-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0442
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:50:17.835117+00:00
-- url     : https://prove2.me/submissions/ad9f5094-ae67-47b6-8851-825749600c38

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 79316548 ≤ n < 79496404 has `n! + 1` a square.
For every such `n` a prime `p > n + 1` (from a per-sub-range list, each prime certified by a
gcd against a product of all primes below its square root) with `j = p - 1 - n`,
`Q = (-1)^j j! mod p` and `N = Q (Q - 1) mod p` has `N ^ ((p - 1) / 2) ≡ -1 (mod p)`; by Wilson
`Q^2 (n! + 1) ≡ N`, so `n! + 1` is not a square mod `p`. Checked by the kernel
(`decide +kernel`) through the frame `BRFrame`. -/

set_option autoImplicit false
set_option linter.all false
set_option Elab.async false

namespace BRFrame

/-! ## 1. The criterion (Wilson + Euler)

For a prime `p = n + j + 1`, Wilson's theorem gives `n! * Q = -1` in `ZMod p` with
`Q = (-1) ^ j * j!`. If `n! + 1 = m ^ 2` then `Q * (Q - 1) = (Q * m) ^ 2` is a square, so its
`(p - 1) / 2`-th power is `0` or `1`, never `-1`. -/

theorem fact_split (p : ℕ) : ∀ j n : ℕ, n + j + 1 = p →
    (((p - 1).factorial : ℕ) : ZMod p) =
      ((n.factorial : ℕ) : ZMod p) * ((-1) ^ j * ((j.factorial : ℕ) : ZMod p)) := by
  intro j
  induction j with
  | zero =>
    intro n h
    have e : p - 1 = n := by omega
    rw [e]
    simp
  | succ j ih =>
    intro n h
    rw [ih (n + 1) (by omega), Nat.factorial_succ n, Nat.factorial_succ j]
    have h0 : ((n + 1 + (j + 1) : ℕ) : ZMod p) = 0 := by
      rw [show n + 1 + (j + 1) = p by omega]
      exact ZMod.natCast_self p
    push_cast at h0 ⊢
    linear_combination ((-1) ^ j * ((j.factorial : ℕ) : ZMod p) * ((n.factorial : ℕ) : ZMod p)) * h0

theorem crit (p n j m : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p) (hj : n + j + 1 = p) (Q N : ℕ)
    (hQ : (Q : ZMod p) = (-1) ^ j * ((j.factorial : ℕ) : ZMod p))
    (hN : (N : ZMod p) = (Q : ZMod p) * ((Q : ZMod p) - 1))
    (he : (N : ZMod p) ^ ((p - 1) / 2) = -1) : Nat.factorial n + 1 ≠ m ^ 2 := by
  intro hm
  haveI := Fact.mk hp
  have hw : ((n.factorial : ℕ) : ZMod p) * (Q : ZMod p) = -1 := by
    rw [hQ, ← fact_split p j n hj]
    exact @ZMod.wilsons_lemma p _
  have hm' : ((n.factorial : ℕ) : ZMod p) + 1 = (m : ZMod p) ^ 2 := by
    have := congrArg (fun x : ℕ => (x : ZMod p)) hm
    push_cast at this
    exact this
  have hsq : (N : ZMod p) = ((Q : ZMod p) * (m : ZMod p)) ^ 2 := by
    rw [hN, mul_pow, ← hm']
    linear_combination (-(Q : ZMod p)) * hw
  have hodd : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · omega
    · exact h
  have h2e : 2 * ((p - 1) / 2) = p - 1 := by omega
  rw [hsq, ← pow_mul, h2e] at he
  by_cases hx : (Q : ZMod p) * (m : ZMod p) = 0
  · rw [hx, zero_pow (by omega)] at he
    have h1 : (1 : ZMod p) = 0 := by linear_combination he
    exact one_ne_zero h1
  · rw [ZMod.pow_card_sub_one_eq_one hx] at he
    have h2 : ((2 : ℕ) : ZMod p) = 0 := by
      push_cast
      linear_combination he
    have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff _ _).1 h2
    have := Nat.le_of_dvd (by norm_num) hd
    omega

/-! ## 2. Modular powering: four windows (8, 7, 7, 7 bits; fast for `e < 2 ^ 29`; exact for all `e`) -/

def w7 (p a e : ℕ) : ℕ :=
  Nat.mod (Nat.mul (Nat.pow (Nat.mod (Nat.mul (Nat.pow (Nat.mod (Nat.mul (Nat.pow
    (Nat.mod (Nat.pow a (Nat.shiftRight e 21)) p) 128)
    (Nat.pow a (Nat.land (Nat.shiftRight e 14) 127))) p) 128)
    (Nat.pow a (Nat.land (Nat.shiftRight e 7) 127))) p) 128)
    (Nat.pow a (Nat.land e 127))) p

theorem win (p a x u d : ℕ) (hx : x ≡ a ^ u [MOD p]) :
    Nat.mod (Nat.mul (Nat.pow x 128) (Nat.pow a d)) p ≡ a ^ (u * 128 + d) [MOD p] := by
  refine (Nat.mod_modEq (x ^ 128 * a ^ d) p).trans ?_
  rw [pow_add, pow_mul]
  exact (hx.pow 128).mul_right _

theorem sh_div (e k : ℕ) : Nat.shiftRight e k = e / 2 ^ k := by
  show e >>> k = e / 2 ^ k
  rw [Nat.shiftRight_eq_div_pow]

theorem w7_spec (p a e : ℕ) : w7 p a e ≡ a ^ e [MOD p] := by
  have d14 : Nat.land (Nat.shiftRight e 14) 127 = e / 2 ^ 14 % 2 ^ 7 := by
    rw [sh_div]; exact Nat.and_two_pow_sub_one_eq_mod _ 7
  have d7 : Nat.land (Nat.shiftRight e 7) 127 = e / 2 ^ 7 % 2 ^ 7 := by
    rw [sh_div]; exact Nat.and_two_pow_sub_one_eq_mod _ 7
  have d0 : Nat.land e 127 = e % 2 ^ 7 := Nat.and_two_pow_sub_one_eq_mod _ 7
  unfold w7
  rw [d14, d7, d0, sh_div e 21]
  have h0 : Nat.mod (Nat.pow a (e / 2 ^ 21)) p ≡ a ^ (e / 2 ^ 21) [MOD p] := Nat.mod_modEq _ _
  have h1 := win p a _ _ (e / 2 ^ 14 % 2 ^ 7) h0
  have h2 := win p a _ _ (e / 2 ^ 7 % 2 ^ 7) h1
  have h3 := win p a _ _ (e % 2 ^ 7) h2
  refine h3.trans ?_
  have ee : ((e / 2 ^ 21 * 128 + e / 2 ^ 14 % 2 ^ 7) * 128 + e / 2 ^ 7 % 2 ^ 7) * 128 + e % 2 ^ 7 = e := by
    norm_num
    omega
  rw [ee]

/-! ## 3. The factorial table

`mkT W k j f acc` appends `f = j!`, `(j+1)!`, ... (`k` entries, `W` bits each) below `acc`, so in
`TB W J = mkT W (J + 1) 0 1 0` the entry `j` sits at bit `W * (J - j)`. Nothing is assumed about it:
`tabOK` checks every entry against a running factorial in the kernel. -/

def mkT (W : ℕ) (k : ℕ) : ℕ → ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ → ℕ) (fun _ _ acc => acc)
    (fun _ ih j f acc => ih (Nat.add j 1) (Nat.mul f (Nat.add j 1)) (Nat.lor (Nat.shiftLeft acc W) f)) k

def ext (T W M J j : ℕ) : ℕ := Nat.land (Nat.shiftRight T (Nat.mul W (Nat.sub J j))) M

/-- `tabOK T W M J k j f`: entries `j, j+1, ..., j+k-1` equal `f, f*(j+1), ...` -/
def tabOK (T W M J : ℕ) (k : ℕ) : ℕ → ℕ → Bool :=
  Nat.rec (motive := fun _ => ℕ → ℕ → Bool) (fun _ _ => true)
    (fun _ ih j f => Nat.beq (ext T W M J j) f && ih (Nat.add j 1) (Nat.mul f (Nat.add j 1))) k

theorem tabOK_sound (T W M J : ℕ) : ∀ k j, tabOK T W M J k j (Nat.factorial j) = true →
    ∀ i, j ≤ i → i < j + k → ext T W M J i = Nat.factorial i := by
  intro k
  induction k with
  | zero => intro j _ i h1 h2; omega
  | succ k ih =>
    intro j h i h1 h2
    have h' : (Nat.beq (ext T W M J j) (Nat.factorial j) &&
        tabOK T W M J k (Nat.add j 1) (Nat.mul (Nat.factorial j) (Nat.add j 1))) = true := h
    rw [Bool.and_eq_true] at h'
    by_cases hij : i = j
    · subst hij
      exact Nat.eq_of_beq_eq_true h'.1
    · have hf : Nat.mul (Nat.factorial j) (Nat.add j 1) = Nat.factorial (j + 1) := by
        show Nat.factorial j * (j + 1) = Nat.factorial (j + 1)
        rw [Nat.factorial_succ, Nat.mul_comm]
      have h2' := h'.2
      rw [hf] at h2'
      exact ih (j + 1) h2' i (by omega) (by omega)

/-! ## 4. Prime pools

`chk6 P T`: `6 ∣ P` and `6t+5`, `6t+7` share a factor with `P` for every `t < T`; then every prime
`q ≤ 6T+1` divides `P`. A number `q < Bd` with `gcd q P = 1` and every prime `r` with `r * r < Bd`
dividing `P` is prime. -/

def chk6 (P : ℕ) (T : ℕ) : Bool :=
  Nat.beq (Nat.mod P 6) 0 &&
  Nat.rec (motive := fun _ => Bool) true
    (fun t ih => !(Nat.beq (Nat.gcd (Nat.add (Nat.mul 6 t) 5) P) 1) &&
      !(Nat.beq (Nat.gcd (Nat.add (Nat.mul 6 t) 7) P) 1) && ih) T

theorem chk6_rec (P : ℕ) : ∀ T, Nat.rec (motive := fun _ => Bool) true
    (fun t ih => !(Nat.beq (Nat.gcd (Nat.add (Nat.mul 6 t) 5) P) 1) &&
      !(Nat.beq (Nat.gcd (Nat.add (Nat.mul 6 t) 7) P) 1) && ih) T = true →
    ∀ t, t < T → Nat.gcd (6 * t + 5) P ≠ 1 ∧ Nat.gcd (6 * t + 7) P ≠ 1 := by
  intro T
  induction T with
  | zero => intro _ t ht; omega
  | succ T ih =>
    intro h t ht
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨⟨h5, h7⟩, hr⟩ := h
    by_cases htT : t = T
    · subst htT
      constructor
      · intro hc
        have : Nat.beq (Nat.gcd (Nat.add (Nat.mul 6 t) 5) P) 1 = true := by
          show Nat.beq (Nat.gcd (6 * t + 5) P) 1 = true
          rw [hc]; rfl
        rw [this] at h5; exact absurd h5 (by decide)
      · intro hc
        have : Nat.beq (Nat.gcd (Nat.add (Nat.mul 6 t) 7) P) 1 = true := by
          show Nat.beq (Nat.gcd (6 * t + 7) P) 1 = true
          rw [hc]; rfl
        rw [this] at h7; exact absurd h7 (by decide)
    · exact ih hr t (by omega)

theorem chk6_sound (P T : ℕ) (h : chk6 P T = true) :
    ∀ q : ℕ, q.Prime → (q ≤ 3 ∨ q ≤ 6 * T + 1) → q ∣ P := by
  unfold chk6 at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h6, hr⟩ := h
  have h6' : P % 6 = 0 := Nat.eq_of_beq_eq_true h6
  have hall := chk6_rec P T hr
  intro q hq hb
  have hq2 := hq.two_le
  have hdvd : ∀ t, (q = 6 * t + 5 ∨ q = 6 * t + 7) → t < T → q ∣ P := by
    intro t ht htT
    rcases Nat.coprime_or_dvd_of_prime hq P with hc | hc
    · rcases ht with ht | ht
      · rw [ht] at hc; exact absurd hc (hall t htT).1
      · rw [ht] at hc; exact absurd hc (hall t htT).2
    · exact hc
  by_cases h23 : q ≤ 3
  · have : q = 2 ∨ q = 3 := by omega
    rcases this with e | e
    · subst e; omega
    · subst e; omega
  · have hb' : q ≤ 6 * T + 1 := by omega
    have hm : q % 6 = 1 ∨ q % 6 = 5 := by
      have h2 : ¬ 2 ∣ q := by
        intro hd
        have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hq).1 hd
        omega
      have h3 : ¬ 3 ∣ q := by
        intro hd
        have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hq).1 hd
        omega
      omega
    rcases hm with hm | hm
    · exact hdvd (q / 6 - 1) (Or.inr (by omega)) (by omega)
    · exact hdvd (q / 6) (Or.inl (by omega)) (by omega)

theorem prime_of_pool (P Bd q : ℕ) (hP : ∀ r : ℕ, r.Prime → r * r < Bd → r ∣ P) (h2 : 2 ≤ q)
    (hq : q < Bd) (hc : Nat.gcd q P = 1) : q.Prime := by
  by_contra hnp
  have hq1 : q ≠ 1 := by omega
  have hmp := Nat.minFac_prime hq1
  have hsq := Nat.minFac_sq_le_self (by omega) hnp
  have hsq' : q.minFac * q.minFac ≤ q := by rw [← pow_two]; exact hsq
  have hdP := hP q.minFac hmp (by omega)
  have hd : q.minFac ∣ Nat.gcd q P := Nat.dvd_gcd (Nat.minFac_dvd q) hdP
  rw [hc] at hd
  have := Nat.le_of_dvd one_pos hd
  have := hmp.two_le
  omega

/-- pools: `6` below `16`, `30030` below `196`, `P3` below `32761`, `P4` below `1024000000` -/
def pOK (P3 P4 p : ℕ) : Bool :=
  Nat.ble 5 p && cond (Nat.blt p 16) (Nat.beq (Nat.gcd p 6) 1)
    (cond (Nat.blt p 196) (Nat.beq (Nat.gcd p 30030) 1)
      (cond (Nat.blt p 32761) (Nat.beq (Nat.gcd p P3) 1)
        (Nat.blt p 1024000000 && Nat.beq (Nat.gcd p P4) 1)))

theorem blt_t {a b : ℕ} (h : a < b) : Nat.blt a b = true := by simpa using h

theorem blt_f {a b : ℕ} (h : ¬ a < b) : Nat.blt a b = false := by
  cases hb : Nat.blt a b
  · rfl
  · exact absurd (by simpa using hb) h

theorem P6_ok : chk6 6 0 = true := by decide +kernel
theorem P30030_ok : chk6 30030 2 = true := by decide +kernel

theorem pOK_sound (P3 P4 : ℕ) (h3 : chk6 P3 30 = true) (h4 : chk6 P4 5333 = true) (p : ℕ)
    (h : pOK P3 P4 p = true) : p.Prime ∧ 5 ≤ p := by
  unfold pOK at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h5, h⟩ := h
  have h5' := Nat.le_of_ble_eq_true h5
  refine ⟨?_, h5'⟩
  by_cases c1 : p < 16
  · rw [blt_t c1, cond_true] at h
    exact prime_of_pool 6 16 p (fun r hr hrr => chk6_sound 6 0 P6_ok r hr (by
      left; by_contra hc; have : 4 * 4 ≤ r * r := Nat.mul_le_mul (by omega) (by omega); omega))
      (by omega) c1 (Nat.eq_of_beq_eq_true h)
  rw [blt_f c1, cond_false] at h
  by_cases c2 : p < 196
  · rw [blt_t c2, cond_true] at h
    exact prime_of_pool 30030 196 p (fun r hr hrr => chk6_sound 30030 2 P30030_ok r hr (by
      right; by_contra hc; have : 14 * 14 ≤ r * r := Nat.mul_le_mul (by omega) (by omega); omega))
      (by omega) c2 (Nat.eq_of_beq_eq_true h)
  rw [blt_f c2, cond_false] at h
  by_cases c3 : p < 32761
  · rw [blt_t c3, cond_true] at h
    exact prime_of_pool P3 32761 p (fun r hr hrr => chk6_sound P3 30 h3 r hr (by
      right; by_contra hc; have : 182 * 182 ≤ r * r := Nat.mul_le_mul (by omega) (by omega); omega))
      (by omega) c3 (Nat.eq_of_beq_eq_true h)
  rw [blt_f c3, cond_false, Bool.and_eq_true] at h
  have c4 := Nat.le_of_ble_eq_true h.1
  exact prime_of_pool P4 1024000000 p (fun r hr hrr => chk6_sound P4 5333 h4 r hr (by
      right; by_contra hc; have : 32000 * 32000 ≤ r * r := Nat.mul_le_mul (by omega) (by omega); omega))
      (by omega) c4 (Nat.eq_of_beq_eq_true h.2)

/-! ## 5. One `n`: the test

`fm`: `j!` from the table for `j ≤ J`, else from entry `J` by the loop `lp` (rare).
`nN = f * (f + s) mod p` with `f ≡ j! (mod p)`, `s = p - 1` (`j` even) or `1` (`j` odd); this is
`Q * (Q - 1)` for `Q = (-1)^j j!`. -/

def lp (p : ℕ) (k : ℕ) : ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ acc => acc)
    (fun _ ih i acc => ih (Nat.add i 1) (Nat.mod (Nat.mul acc (Nat.add i 1)) p)) k

theorem lp_spec (p : ℕ) : ∀ k i acc, acc ≡ Nat.factorial i [MOD p] →
    lp p k i acc ≡ Nat.factorial (i + k) [MOD p] := by
  intro k
  induction k with
  | zero => intro i acc h; exact h
  | succ k ih =>
    intro i acc h
    have e : lp p (k + 1) i acc = lp p k (Nat.add i 1) (Nat.mod (Nat.mul acc (Nat.add i 1)) p) := rfl
    rw [e]
    have h2 : Nat.mod (Nat.mul acc (Nat.add i 1)) p ≡ Nat.factorial (i + 1) [MOD p] := by
      refine (Nat.mod_modEq (acc * (i + 1)) p).trans ?_
      rw [Nat.factorial_succ, Nat.mul_comm (i + 1)]
      exact h.mul_right _
    have := ih (i + 1) _ h2
    rw [show i + 1 + k = i + (k + 1) by omega] at this
    exact this

def fm (T W M J p j : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (lp p (Nat.sub j J) J (Nat.mod (ext T W M J J) p))
    (ext T W M J j) (Nat.ble j J)

theorem fm_spec (T W M J p j : ℕ) (hT : ∀ i, i ≤ J → ext T W M J i = Nat.factorial i) :
    fm T W M J p j ≡ Nat.factorial j [MOD p] := by
  unfold fm
  by_cases hj : j ≤ J
  · have hb : Nat.ble j J = true := by rw [Nat.ble_eq]; exact hj
    rw [hb]; dsimp only; rw [hT j hj]
  · have hb : Nat.ble j J = false := by
      cases h : Nat.ble j J
      · rfl
      · exact absurd (Nat.le_of_ble_eq_true h) hj
    rw [hb]; dsimp only
    have h0 : Nat.mod (ext T W M J J) p ≡ Nat.factorial J [MOD p] := by
      rw [hT J le_rfl]; exact Nat.mod_modEq _ _
    have := lp_spec p (Nat.sub j J) J _ h0
    rw [show J + Nat.sub j J = j by show J + (j - J) = j; omega] at this
    exact this

def nN (T W M J p j : ℕ) : ℕ :=
  Nat.mod (Nat.mul (fm T W M J p j) (Nat.add (fm T W M J p j)
    (Nat.sub p (Nat.add 1 (Nat.mul (Nat.land j 1) (Nat.sub p 2)))))) p

theorem cast_nN (T W M J p j : ℕ) (hT : ∀ i, i ≤ J → ext T W M J i = Nat.factorial i) (hp : 2 ≤ p) :
    ((nN T W M J p j : ℕ) : ZMod p) =
      ((-1) ^ j * ((j.factorial : ℕ) : ZMod p)) * (((-1) ^ j * ((j.factorial : ℕ) : ZMod p)) - 1) := by
  have hm : ((fm T W M J p j : ℕ) : ZMod p) = ((j.factorial : ℕ) : ZMod p) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).2 (fm_spec T W M J p j hT)
  have hl : Nat.land j 1 = j % 2 := Nat.and_one_is_mod j
  unfold nN
  rw [show Nat.mod (Nat.mul (fm T W M J p j) (Nat.add (fm T W M J p j)
    (Nat.sub p (Nat.add 1 (Nat.mul (Nat.land j 1) (Nat.sub p 2)))))) p =
    (fm T W M J p j * (fm T W M J p j + (p - (1 + j % 2 * (p - 2))))) % p by rw [hl]; rfl]
  rw [ZMod.natCast_mod, Nat.cast_mul, Nat.cast_add, hm]
  rcases Nat.mod_two_eq_zero_or_one j with h | h
  · rw [h, zero_mul, add_zero, Nat.cast_sub (by omega), ZMod.natCast_self]
    have : Even j := Nat.even_iff.2 h
    rw [this.neg_one_pow]
    push_cast
    ring
  · rw [h, one_mul, show p - (1 + (p - 2)) = 1 by omega]
    have : Odd j := Nat.odd_iff.2 h
    rw [this.neg_one_pow]
    push_cast
    ring

theorem good_of (T W M J n p : ℕ) (hT : ∀ i, i ≤ J → ext T W M J i = Nat.factorial i)
    (hp : p.Prime) (hp5 : 5 ≤ p) (h1 : Nat.blt (Nat.add n 1) p = true)
    (h3 : Nat.beq (w7 p (nN T W M J p (Nat.sub p (Nat.add n 1))) (Nat.shiftRight p 1)) (Nat.sub p 1) = true)
    (m : ℕ) : Nat.factorial n + 1 ≠ m ^ 2 := by
  have h1' : n + 1 < p := Nat.le_of_ble_eq_true h1
  set j := Nat.sub p (Nat.add n 1) with hj
  have hjv : j = p - (n + 1) := rfl
  have hN := cast_nN T W M J p j hT (by omega)
  have hodd : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with e | e
    · omega
    · exact e
  have hsh : Nat.shiftRight p 1 = (p - 1) / 2 := by
    rw [sh_div]
    omega
  have : NeZero p := ⟨by omega⟩
  have hw := w7_spec p (nN T W M J p j) (Nat.shiftRight p 1)
  rw [Nat.eq_of_beq_eq_true h3, hsh] at hw
  have he : ((nN T W M J p j : ℕ) : ZMod p) ^ ((p - 1) / 2) = -1 := by
    have := (ZMod.natCast_eq_natCast_iff _ _ _).2 hw
    push_cast at this
    rw [← this]
    show ((p - 1 : ℕ) : ZMod p) = -1
    rw [Nat.cast_sub (by omega), ZMod.natCast_self]
    simp
  exact crit p n j m hp (by omega) (by omega) ((-1) ^ j * ((j.factorial : ℕ) : ZMod p)).val
    (nN T W M J p j) (by rw [ZMod.natCast_zmod_val]) (by rw [ZMod.natCast_zmod_val]; exact hN) he

/-! ## 6. The prime stream

A stream is a head prime `ph` and the packed gaps `Gp` (8 bits each, gap / 2, low first).
`sp i ph Gp` is its `i`-th element. Once `Gp = 0` the stream is constant. `sOK` checks every
element against the pools. -/

def sp (i : ℕ) : ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun ph _ => ph)
    (fun _ ih ph Gp => ih (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.shiftRight Gp 8)) i

theorem sp_zero (ph Gp : ℕ) : sp 0 ph Gp = ph := rfl

theorem sp_succ (i ph Gp : ℕ) :
    sp (i + 1) ph Gp = sp i (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.shiftRight Gp 8) := rfl

theorem sp_const : ∀ i ph, sp i ph 0 = ph := by
  intro i
  induction i with
  | zero => intro ph; rfl
  | succ i ih =>
    intro ph
    rw [sp_succ]
    have e1 : Nat.add ph (Nat.mul 2 (Nat.land 0 255)) = ph := by
      show ph + 2 * (0 &&& 255) = ph
      simp
    have e2 : Nat.shiftRight 0 8 = 0 := by show 0 >>> 8 = 0; simp
    rw [e1, e2, ih]

def sOK (P3 P4 : ℕ) (f : ℕ) : ℕ → ℕ → Bool :=
  Nat.rec (motive := fun _ => ℕ → ℕ → Bool) (fun _ _ => false)
    (fun _ ih ph Gp => pOK P3 P4 ph && (Nat.beq Gp 0 ||
      ih (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.shiftRight Gp 8))) f

def SP (ph Gp : ℕ) : Prop := ∀ i, (sp i ph Gp).Prime ∧ 5 ≤ sp i ph Gp

theorem sOK_sound (P3 P4 : ℕ) (h3 : chk6 P3 30 = true) (h4 : chk6 P4 5333 = true) :
    ∀ f ph Gp, sOK P3 P4 f ph Gp = true → SP ph Gp := by
  intro f
  induction f with
  | zero => intro ph Gp h; exact absurd h (by simp [sOK])
  | succ f ih =>
    intro ph Gp h
    have h' : (pOK P3 P4 ph && (Nat.beq Gp 0 ||
      sOK P3 P4 f (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.shiftRight Gp 8))) = true := h
    rw [Bool.and_eq_true, Bool.or_eq_true] at h'
    obtain ⟨hp, hr⟩ := h'
    have hph := pOK_sound P3 P4 h3 h4 ph hp
    intro i
    cases i with
    | zero => exact hph
    | succ i =>
      rw [sp_succ]
      rcases hr with h0 | h1
      · have hG : Gp = 0 := Nat.eq_of_beq_eq_true h0
        subst hG
        have e1 : Nat.add ph (Nat.mul 2 (Nat.land 0 255)) = ph := by
          show ph + 2 * (0 &&& 255) = ph
          simp
        have e2 : Nat.shiftRight 0 8 = 0 := by show 0 >>> 8 = 0; simp
        rw [e1, e2, sp_const]
        exact hph
      · exact ih _ _ h1 i

theorem SP_next (ph Gp : ℕ) (h : SP ph Gp) :
    SP (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.shiftRight Gp 8) := by
  intro i
  have := h (i + 1)
  rw [sp_succ] at this
  exact this

/-! ## 7. The walk

State: `n`, the prime stream `(ph, Gp)` (`ph` = the first prime `≥ n + 2`) and the record codes `R`
(low bits first). The code `t` (see `tsel`) selects the prime `sp t ph Gp` for `n`. The fuel is the
number of `n` still to check; at fuel `0` the walk requires `n = nE`. The body is written flat (lets,
`Bool.rec`) for kernel speed; `walk_succ` gives its meaning. -/

def wr (b : Bool) : Bool := b

/-- the record code: 2 bits `c`; `c < 3` gives `t = c`, else `t = 3 + ` the next 6 bits -/
def tsel (R : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (Nat.add 3 (Nat.land (Nat.shiftRight R 2) 63)) (Nat.land R 3)
    (Nat.blt (Nat.land R 3) 3)

def rnx (R : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight R 8) (Nat.shiftRight R 2) (Nat.blt (Nat.land R 3) 3)

def adP (n ph Gp : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) ph (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.blt ph (Nat.add n 3))

def adG (n ph Gp : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) Gp (Nat.shiftRight Gp 8) (Nat.blt ph (Nat.add n 3))

theorem SP_adv (n ph Gp : ℕ) (h : SP ph Gp) : SP (adP n ph Gp) (adG n ph Gp) := by
  unfold adP adG
  cases hb : Nat.blt ph (Nat.add n 3)
  · dsimp only; exact h
  · dsimp only; exact SP_next ph Gp h

noncomputable def walk (T W M J nE : ℕ) (f : ℕ) : ℕ → ℕ → ℕ → ℕ → Bool :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ → ℕ → Bool) (fun n _ _ _ => Nat.beq n nE)
    (fun _ ih n ph Gp R =>
      let c0 := Nat.land R 3
      let b0 := Nat.blt c0 3
      let t := Bool.rec (motive := fun _ => ℕ) (Nat.add 3 (Nat.land (Nat.shiftRight R 2) 63)) c0 b0
      let p := sp t ph Gp
      let j := Nat.sub p (Nat.add n 1)
      let fj := Bool.rec (motive := fun _ => ℕ) (lp p (Nat.sub j J) J (Nat.mod (ext T W M J J) p))
        (Nat.land (Nat.shiftRight T (Nat.mul W (Nat.sub J j))) M) (Nat.ble j J)
      Bool.rec (motive := fun _ => Bool) false
        (Bool.rec (motive := fun _ => Bool) false
          (wr (ih (Nat.add n 1)
            (Bool.rec (motive := fun _ => ℕ) ph (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.blt ph (Nat.add n 3)))
            (Bool.rec (motive := fun _ => ℕ) Gp (Nat.shiftRight Gp 8) (Nat.blt ph (Nat.add n 3)))
            (Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight R 8) (Nat.shiftRight R 2) b0)))
          (Nat.beq (w7 p (Nat.mod (Nat.mul fj (Nat.add fj (Nat.sub p (Nat.add 1 (Nat.mul (Nat.land j 1)
            (Nat.sub p 2)))))) p) (Nat.shiftRight p 1)) (Nat.sub p 1)))
        (Nat.blt (Nat.add n 1) p)) f

theorem walk_zero (T W M J nE n ph Gp R : ℕ) : walk T W M J nE 0 n ph Gp R = Nat.beq n nE := rfl

theorem walk_succ (T W M J nE f n ph Gp R : ℕ) :
    walk T W M J nE (f + 1) n ph Gp R =
      Bool.rec (motive := fun _ => Bool) false
        (Bool.rec (motive := fun _ => Bool) false
          (wr (walk T W M J nE f (Nat.add n 1) (adP n ph Gp) (adG n ph Gp) (rnx R)))
          (Nat.beq (w7 (sp (tsel R) ph Gp) (nN T W M J (sp (tsel R) ph Gp)
            (Nat.sub (sp (tsel R) ph Gp) (Nat.add n 1))) (Nat.shiftRight (sp (tsel R) ph Gp) 1))
            (Nat.sub (sp (tsel R) ph Gp) 1)))
        (Nat.blt (Nat.add n 1) (sp (tsel R) ph Gp)) := rfl

/-- `Cov A n`: no `x ∈ [A, n)` has `x! + 1` a square -/
def Cov (A n : ℕ) : Prop := ∀ x, A ≤ x → x < n → ∀ m, Nat.factorial x + 1 ≠ m ^ 2

theorem walk_sound (T W M J nE A : ℕ) (hT : ∀ i, i ≤ J → ext T W M J i = Nat.factorial i) :
    ∀ (f n ph Gp R : ℕ), walk T W M J nE f n ph Gp R = true → SP ph Gp → Cov A n → Cov A nE := by
  intro f
  induction f with
  | zero =>
    intro n ph Gp R h _ hC
    rw [walk_zero] at h
    rw [← Nat.eq_of_beq_eq_true h]
    exact hC
  | succ f ih =>
    intro n ph Gp R h hS hC
    rw [walk_succ] at h
    cases h1 : Nat.blt (Nat.add n 1) (sp (tsel R) ph Gp)
    · rw [h1] at h; dsimp only at h; exact absurd h (by decide)
    rw [h1] at h; dsimp only at h
    cases h3 : Nat.beq (w7 (sp (tsel R) ph Gp) (nN T W M J (sp (tsel R) ph Gp)
          (Nat.sub (sp (tsel R) ph Gp) (Nat.add n 1))) (Nat.shiftRight (sp (tsel R) ph Gp) 1))
          (Nat.sub (sp (tsel R) ph Gp) 1)
    · rw [h3] at h; dsimp only at h; exact absurd h (by decide)
    rw [h3] at h; dsimp only at h
    have hw : walk T W M J nE f (Nat.add n 1) (adP n ph Gp) (adG n ph Gp) (rnx R) = true := h
    refine ih _ _ _ _ hw (SP_adv n ph Gp hS) ?_
    intro x hx1 hx2 m
    by_cases hxn : x < n
    · exact hC x hx1 hxn m
    · have hxe : x = n := by
        have : x < n + 1 := hx2
        omega
      subst hxe
      exact good_of T W M J x _ hT (hS _).1 (hS _).2 h1 h3 m

/-- one sub-range: the prime stream passes the pools and the walk reaches `nE` -/
noncomputable def sub (P3 P4 T W M J nE f n ph Gp fs R : ℕ) : Bool :=
  sOK P3 P4 fs ph Gp && walk T W M J nE f n ph Gp R

theorem sub_sound (P3 P4 T W M J nE A f n ph Gp fs R : ℕ)
    (h3 : chk6 P3 30 = true) (h4 : chk6 P4 5333 = true)
    (hT : ∀ i, i ≤ J → ext T W M J i = Nat.factorial i)
    (h : sub P3 P4 T W M J nE f n ph Gp fs R = true) (hC : Cov A n) : Cov A nE := by
  unfold sub at h
  rw [Bool.and_eq_true] at h
  exact walk_sound T W M J nE A hT f n ph Gp R h.2 (sOK_sound P3 P4 h3 h4 fs ph Gp h.1) hC

theorem cov_init (A : ℕ) : Cov A A := fun x h1 h2 => absurd (lt_of_le_of_lt h1 h2) (lt_irrefl _)

theorem tab_all (T W M J : ℕ) (h : tabOK T W M J (J + 1) 0 1 = true) :
    ∀ i, i ≤ J → ext T W M J i = Nat.factorial i := by
  intro i hi
  exact tabOK_sound T W M J (J + 1) 0 (by simpa using h) i (by omega) (by omega)

/-- assemble a big number from 8192-bit groups, low group first -/
def asm (L : List ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ) 0 (fun a _ ih => Nat.lor a (Nat.shiftLeft ih 8192)) L

end BRFrame

namespace BRData

def TB : ℕ := BRFrame.mkT 1680 256 0 1 0

def MM : ℕ := Nat.sub (Nat.shiftLeft 1 1680) 1

theorem TOK : BRFrame.tabOK TB 1680 MM 255 256 0 1 = true := by decide +kernel

theorem TAB : ∀ i, i ≤ 255 → BRFrame.ext TB 1680 MM 255 i = Nat.factorial i :=
  BRFrame.tab_all TB 1680 MM 255 TOK

/-- the product of the primes up to 181 -/
def P3 : ℕ := 0x30e06b35ee39cf75358315a5c3b9b2bdd2e46e25fd10a14382537a2e71312

/-- the product of the primes up to 32000, in 8192-bit groups -/
def P4 : ℕ := BRFrame.asm [
  0xdf0c850baeddb2128ac9d0fd36dd0ec2f329ef90aca3308ae6b7bcedec1424921497fc345111e60cc412113537268a736f809fc9cefc2bcbe959a57ecf6fcdc7dc216df46f82fa5bf3720c4270cf6fb13e1dcf489d98985e4f734ee9fac8505c106eb7b2acdb6bb26b79b9cd02729d2a2b215b45d1ad39b752020674f4f03993d6c7a96c9df2c43cdd5fcdd4a2a82b5082c3e0eab548cededa2cc10cfb2c34e6f98c290160b64fdf83e7d3438e6077c84a97d92b85d47ac7b128a35167b6e0531f91938128b16ed40b0ea8ed276a4a879f7c745e779c2215fa0572e7a15cae72ee309c077cfb5b3d707818405d883f07d24cd50cd5cefb61fd23ae30b49766951623101af6e194dae9d45749c5926504c31b2e31d16b3a1d8d8f628e30e1137c5dd8637ac50c416fb56e780354d53f83146505e0b75b3fd791dfb6d1cccdf46dd3bacd8c80998bafeec517c181f3bb39e1a7ff75b63960e7e4fbfa4ab3cd18f8673b3d211d62f5e0b3e98f4fcf16bc36e8d7000957b714c4798645de1678e06a21c7cc25ca8fd857afcda85428c1cff131cba807766664cd1ef92b24719ad71a1cacc089d80d1baf2446d3f91edab2290690b4fb849083f3506e79ef43443cfe351c5874753757cdb387af230e22804870783e587646125c93d5e22899c55a15ce29a46aa788de770abed396e6fa35fc451018422e12cda42c1968eb0b94f01da5b9943508ea2fe4ba6651d5d47287366890f2cd535e3789780c5933d6df7e974200cef40380b365f780703c6c344beeb37d043d1ef50ebe5b4b1dc45ace9088eb5474968a0e3305d300ae7a40322ab01357e0cffcf44216a95c444ff2a19bac8a80242e5b642615b266fa3b82e4ebec98b03bd5f61703e03d249324888f88edca090f5ed1243e0a4675f6ae3953d13092b10e09246ac59dc44eba77e164dbfe0f4949818965554093616dc9e4d28ec2f4206870ee44b9ad38fba67c42730b4845e2204f42dcb968564cf342d81da1dbbcb2ad1f705abde27272ca6eb434e635441102a00bb1b3837369200971d33813d146a5507c16e5102a5474ae182d25b8f97aee76e787fb717b4826f264800d01b229407e10b46c31d717cace03707e9813842dde7b9c675f84a599ec1ee76abcbcd5643683142b3af9a5e3ba165a9c8a2d3a8d31de317adde8d146dae44c42d3d79b56996c6c55111ea3f81174d232c5ae8bcf0f11585f68cb32a6395e58907339157f0717bc3ea165222c9ec5363162cf78432b92d4ae5025439cbe242ad10e1460f96a3b9257bb1a9075a34866508f80116c20e59d9ef0bcc790262003e760d1d5a97248b955f6cc61eab2893f5cb8e57f2f293c308165efec92b10c382c1a7f4d7b6b32691a1b62141c02811f4b3027674bebab643b34a70f166e082f1a3489b265b5b1fee25e582b1b076210fe9a,
  0xea98014cae2ac4237f4b4213a735cb3415a1380744196e3371ef349273475b1a9a19eea2b2d83e892b4404ffc9ec8f00c804866f9a9ce72904a292c8101dcfff2039576180f44def879add63b1eccb590677693cae9f49dbf554c6ceba32faf6e84616a64ecc2681a2c895e1090378b6222b56e1bd9cb731fa2064f7b7f066b45169170ba0d08741bd1b0820d77238b47918f994c8aced205746fc0ff5ddd8cf95dd8ef62dd050286266519e45e40e5b2950b8b223c07f101ce162963018ecebd501267eaddb02f56ee6b654257d20d3bf13f73db708520ed0117af6564bb8b0a469856a8cc3e2cae84a242db11e2b060f957bfdc5baa0d4c74a319342609401e3be3e2cf7e1993561e8784857ff0965514a4a9f7a10dcbb1fea1c8cf72786bf6e32594aa1d4908db83d4dfb1c3f8cd9d7a4aa673346618dca07b597d1815974f7e7e86e6d40001b0442574f4404912ee91e38bd7d52aa3eb4ba0fbd5446f731b1baa64f5d05d16a29f33c5cf42cf1f8c2f1d0f96b9a325944e8f02b0169806f2efa153ceefd95679ff923ecc80ceafb98996c16305b5e644d2071399cb7883f6b8a85be82455a9824ef5c3288e149fd62ecee29447798e1f5ea7d3919c51b567ea37288bbefe5b6d943b1edeccad5d4a1284aeddf22256e16e5017fe48dda91d4a4172047b9b6ebdbb35f04afab8a3534b41b758159b035c092cc36876c6db744cdc4558288c5ada4a7c4ca4ef963e05eb3b79ee9f2ba92cca910e4fe4419e33cd12dbd87527274732251e53c0c447842cca8504abf89fb2a0fe66269142a99315d9cfd1cb18ff00a8c0cc9b7d21e6b2d9bba36823cae88b84340801e5c81472d1211357bf791b4b9a83cb8f885a19b4d93e68561301fa92d04eac64892047c44106b572731bc2bc586f7d428463bf12880ddf84b9bcb8b75d18f68f07b2d3a4529f33c265efaa9046e94f310aa9a47d70bf8cca38f0a707a6ce8c2756003dc094a30edb3a17ef3aa4894be8e5d72e22421f097677b90ef6274cb0fe493550d58529e9b9331d11bb641d336d163489ce32364bdf6ed4b327e5a56409b1e276f1ed03f5afc4b1f1eb46f50ea2bd818b6ce560fcf4033323b7f46aab313f4bc2688a9e8ccc1545c5c811b34d48d14308a334a169c2016d94e11129100571fa1dd1c841f5a7bfccbabbc545dba69de8cd04f05f4ad32d476559836d35aca9a7381fa618e0c7e7855e9cd829a0cabdbe9e3c01746e3ae03c2e18f4aa76ef419e3de8bfe4b21500785d9b6964477b8a840ec2cdc45f3227e280e2c5f8f6c6a26c3881003f03b9c89575763154d252dc974ecf290538b9105fcea649307d65a15a817627084c27089384b6073f28023d245a2d78437adc9909abf78ae77d00006f6386c40a33acffa01cdf3667bf58b5a38e6502cd21718fca0d04aeabb5d7635e4b4,
  0x1728b345ae1d105890be726995db87cb8d8643422401f2b9d4fd947140af5fdd89523ad14c14787386bde21dc9610b22e07e931ba28009eb69a71e1cfbc0df11d42c4526b66824c91f442c5636d120007e4d24e3bad931045a7365deef650235aae6a3996d4288b7a45118f689202f6eb7631f39ccfe3ed30df63f6dfa1eaea9abcfc0fbb1889d08158387786d5babb4711aeca73bc3b3e7f510660123273125559e32ae86789b3eea846b65e518bd1b82f86a68b6622dee93c66f28b57bb32c66c334eb0e4e18da04a01e1458f10bfb1b91ada31354048151dc2f7b5e1d35cd094790b3a592983b79c98f2002554d6ac0753e09d4c95de4b0a2dc4af58bc18ba1c404b3cf1f6f5e6353388ba00542736dafb6b3890ed4eb1aa021baa0a1027503756833e069161f3b5df47575a40f2ed8ae5cf84444b7fb646bd1ccb521788b5d39ee4e9492f45b5052f2f8d973d0e798ef2bea1edb9884c1f5ad82ff9f2da775d8c1abba03a5c92ff2c3ccc31a8afb22947e1d06745a05cf02d819e21c1b9eeb81560ef0e999cbf56d4bdb20ee9ae7563555bafaaa67efb0cb235529236a4abc3bbed82dcdf54e45470f179f2174157be3c2cad7e76c7b9fa12a3cedcea2a33cdb5facb5327aead5e2ee441ebfe4a944440623d53d4bdb3e5fa4e7f03a0f3ce18b1b2507fe33b65c49534c5ef0e31577cb2e11c80dd4827e40e09ce1cef2aa8a0b6d04973a6431ea0e721a266ed55b1d51682cf24816a6ef7c28d315fd2c4efd94b46caeb7fa54aa9b6e0b0061cbdd73b551b7a80783e8e600f9a9162f2199788c98a444e28ebb46b57043028fe6c474260640a987cbb7babaf34191506f6a669df1064bb5d3a4522f3706dd1a5615ca291b33cdcc418266d52fda48d187a9bd0c40513361bd5652581c1b2ab80879f9b9c802787745e17a9791fe2d94f2bbbf9e8bd08fed5d2fc21b095a1d18135390d99ffac0dba4a55c77a4ccdef9c1b63ab95770f5296498093b9806389530270a161a78b2759215b5156f0b69960117f858d201d20305aac1d8936d3d8c70293ead432613a327abd5d6b7ec767a694bccfceffb2f505bb0e8cf019e8ba6c25ba9c8a66d8ab729be0c889e5c33b9b003a2777b2ee1a7f1ac50a0b600f9df13abc417f92e56a627fec3318cfec09c3ce8ed11cd38beecc9fe62800f28b554bbb032d54ec3265b9510da2763ffbffa465ebba8541e162029eb43803ead99cc036eac2906e2508acfd0b87815960f33f1250c4c93c84772fcf343e319166a963b9438080e93537495f38e222f30b9388f432d57e061f06db832fc76cd7c2246cdbc725791eedbb0f020e4518bb711c9947fd13da39b34eeaa20b783fda7c7fd6bb5a6bfc5ae0aac9be0260efd746edb56cbad7adf1f59b4ef5590ebf5dc901afac752539f95fa616c0121643f4021b923b,
  0x3c458fee709566842171df4fdf91d1866173d1b733c3309816fb19e69ff4d6644f481709bd1680e21b432a184cfcde4bd4f9b43742cb46b2f3ffd58b5ca10366aa342a9454eedf37ffe61d5b7b01c242438d0aa617697b258e4b6e05f86953963e9b1fb21af5ca4ee94189cb1a9899de56581900c1cb81777ee13638ac508ece1dd9c8bf76060130ee98831d9c1fb6548e12387a276ccb9a1faf40a2ee45223252152bd2949b6b5a7ee3ed5c2879d3abcd1a50c7fafe7d7464053500e063887b01e11ff8f5c27000443e192c9ec6511816a4ef4f6c73c364b4b4e11e4b0f6f2bbe6941fc1002d33c2ea0d80d7c2e37e70d298651f344f10070630a47cd0f686b749590c52fe4333d58a21b210eb744d4e7df8a6d79ce7137a4ba9425114e86d112ff16e899cd2041bb3781489ce56232fa4de91c7ae07bd635bf1f0e554e20163b0a43ed81ab1095811abc702564c76b49adcbc3f5264e74823a695e1847b559021d6babbe9d6989a4eb4d5ff4dff6de9169bddcac984a8bf3d9f653c91cd620b187bdf4e086e2cff33827ccf543d72f80d31c0cfa9b0ec3344ac92fd84b3a3671009f4929fca57466981b49b59806ec5b95115c1d11b21099d94bf85ef0b7bdfdcf30ef86cc521e5a4d267c48da55d3b81706d40dd2e26357d7c865da72c94fd723e3cd37aab7bc2e17c9ae1368ca36ae70f1bb5432a861bc0a79709b81f23807835b1bd97dd958f89f546ca0e74a4d91f2231841b97abae7f63d1dfa52d8d2ecbeb25f730e389347efe4030f78f44b1349e216256ce33d6dcbfd14f9b722f85a32cfcc28fb734de661fad78e2c6065b1a970274a9d4c4b238078e5ef2675620ebe8efc5874a7560f17ae9186eba32895c80e9ab5a9367ceaab065805a41b340cf88a6316b15964530bdee05e98635f268eb9aefe7c81d872c1f52d89472c117d4ead5cabd5874110e0a849337c38acfc60a476b55091afdb9c59ea0200bc2c98cb8fafcdb89a5593e6169294a2d7ad79b4d4bd02449d332f5f101f8a95a668b28a9aa5d4ee6f63265932a22b93e6b08c3cb4ce49b2114839ae8d669db30e78886393dfa8e92535a3232ce2d3b388df674137547d46af3ac76aa08a3962b010a924cecef13be7fc1ee1f857c0c1b148c8350206d93cc1c26bdf2f2083e0632187a7170294c132c8c96452ed414567d17115f3d810463dc5845b0e4b2150676860213d04f9e6b1ee1530faab6ee6281c815dc26cd93cc02c8ed58742168b4bcfe102c25dcf152f8c36ededf5c24b756d43201d572e5ec91e785f50244eac7936a17ebe3e80d537492d9ddbfbc53ed3828000ae06dd1478f12304cfaeaf8b594901c5010f524a109d67422dcf2e00b03dddfcb9ee1060b28f0156ff8707686b109c780e98ff3732bd116d2f70c96ca688419b65cdc52070b6929bfff088a3be5f,
  0x33fb30670ccc9d9161ee291159b243d56af86e6c0d29675ffa2c459c998f0c513dd30d097fc73d45684ecd2c87d420a96eddb72894cfb6b134d8599ab23ca2ce27ef0706a741bda8807b24ea39ef3e5da8774e5f2219c3cbb5573bccfa96c4c5f9b3a11dd2cc735f288dc3a82281b63255a99bc8a5e1c55002df7fda7afac36a1d276383158d287c2a4db62276a331b0b14239ceb7b72b9229337e828e76bd3b13316c1bc98279fb890663222d6f91722909d219a67282cad6eed54326f5e3ea9b7aa50d70e0e9caeec704373d0bf36057bfed71c9e794676fcf07be1e1c0ad66e7790c09f157620dfca3e522db1ac9e18ff6aa4f5ee9f682e9b4a56211d5d51aa3fb19b25926b06393d3c4c47ae87ed8c52d4f19f54ba73ad3fa32cc3da4857c98d0fa5363a46671d532322b398f90422bd732d02d272ed70fbfd0cf7be141b677000847b96d192296c900eda94ea4023fdf00bf2e7a6a9381d832e4e1189a35136b481179ba243c5661a527b140c93d9997eb066a8554bb1b07ac04974f076092dfc159a231f26ff9e7fec54a1a4afc94c723cbc812012373c707e0c81c5783247e3416ec84e3a4aa240527a9339adade0e966d9acc3a1867b2e62b4ab1f43d342508113196ac649cf973d1f98067ebe3662022398d0617ba378bc09596a6403112db6adcca330e099daa38cf9f921c1459c9f97d4be291cb38007fc34a018edb5af08589e98b71ab0e99acfda859889c4a0360109261ff6e40c85327af396767fdac713adfe8caaec684bbcab3fea995f660af05b974c5ba6ebf52d1f8e2b31117cb8faf93a0e939836d3b6af25604d7d5b4f6e144a0485d0c5b5400d4713de63a2736fdbbd20ebb835cc9591b48e10764f4744729730117cf94bd42e70f0f2e86b609f59053a2f94f83d2c855f49bc0563edc62683301a6f1af059fbedbfcf1769c0e1fe4ce07b65de8b71ade682636d0abde0bd94cdde2e1cef86e715d495cddfcdf0e420d7fc6c7b523f6cc2a181df5c50d713f7142e22812e9b36d83d5c41a754fe1e2243d67bcc372a7bc1f7b3cd66155a6d68f2d78535f6ead61180b20a9b7345e87ee56618dcbe69453bfb5db4ed7337f698e5b98735b83d30c6b59ca226c04df477bae76bb50da3ba91f4f324c51588c99d2b8258edfe273d77883d519f5059f50178c73612660f88af6f622035e53bb5cb8421128833d0e2963696885b2672976bc22bdef66a3f79a1eeb5745b266abaae035f56d7da1f92773d588519cfb671cf7f840b8c0eece8eaafaa8cdc7bd8e95db47b86de2f99a5c118b3d336c0cf108f8b13199d11f183c61a0e7fe7d42a609536ad880d22ef9acd6e7a26f94aa1aaf1cddea57ca24edf80e18bb54dc9142b3f9de36aa66add5c83fa9a1b3827de04c3ac9a362fe20443937a0dc21250e8d6183c51a530b2ff77d24,
  0x556d7e991792de0f391465729fa66f7cb4cd30e9aeda0d488686bbeaccac9ce166df07cb523e600a3b36496464fd6e277847eea66bbfbbda8d20d01bd4dac96841254b0ff6c61a90385a3239eaab5887ebdd5a6bcf72691ab6644a094162fe467ce8c72e372883ce54ca28eb67362b5b180ca57cfc027037004145ac514e280b4249af145522f74ad3b0f6eb124e1ba8e994e4ddc0dbdd8cf3f80b42f338206e5313438d9856c4af110573fa215009a4a69f506da8f1fc03695d08ba2ea83ba5b5a7e289910d1ded13d31f5810300e41bc97799d709db61c06dd64bac664891f71d68e45800f73cda9d18f19015497d2048b5193e343f89677fa0fc96fac78929ca8a69f8eb195e7705bb820a2c1d044b922b3b6cd5504ff78a3cbededfb7f1ddaa0ed0869a39884c6f13673cd0cf984a8bfdb025a3bb1af56f4031d5d5b37016db05548dedce76724a7fd52bfdec469e49a2080da2082e93fb0e7b8984d7515b69b3237649436f27c00b00035ef33f41f982ea205940153bfc318e858a5987c952474bca14aac913b1b4ab909216ee44902547a558dee848dd30c0c77b4d2794e7b6b4757e9816025934a0ca36430fe238884e8e64fadbb0d3bcaba4a39af73014f4c5e97e70e5de24c3fd9d2783b3a430158d1a672220b22612a92cf52e32121f8a5aa83d3d87fcfed7751c93bad78d5787354ebe4574d159fff7971b47dc3e0bb5c71f97a51f75996eb949d7565f8e6a18beb27aab1db5b87394d2b1525140e3493920f7b50ea878a9be48bb9e59ffc3746855d8bdf084cf0ce93a39f6f14d5b3a7d76372b40e5870bd37b3449fe5689e]

theorem P3OK : BRFrame.chk6 P3 30 = true := by decide +kernel

theorem P4OK : BRFrame.chk6 P4 5333 = true := by decide +kernel

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 79317798 1250 79316548 79316563
    0x31b012c030d110303060d0807060504050606130606020304091104031406061305010506070f110a08160b0a0504060c05150c03090705010302040503030703030b0d0b040c06030f02090a061b06020c1608 87
    0xb50a130b4410f100181080c00d011850700b4519005030305e03140c00c00210359076900136181c0c1203904440c2070708540184629800c03c0c0762543c10300d0840280600c07600e2700b445c0c0002d40da401a4401c0b19645501d5020380c51645400004a5001d9500550740c847d82000c01c0002556440341940d42c2405100e02120103401c401d058403c05050707410040801d46800e42c9a00c45c030380608070900081c6c4400c1d07001400a40640c1d2191541f41c002c3c1500710103000e4940040c405400b01c2c0c04540d00c004121101040b140080c154000103c600303907812810451080c800b1820b005160000d96440a050a1544014414101c6074140554414140c020441d5009a1180c3c011000c4e80928407a164140d8001d001c000b000178000e4002c40000f1a0142c454680307019070381c50b0304080c0c40c42a14203444401c0403c0c003d000c415810b0064a190101c00b80081d072800c21190082040300e000340c4a002c1c100076100b0ba60144c00e400ea014001007007500804c055440d142983e001c15105d90440103a00790390071713400c0b03c00595400d000caa0b00 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 79319048 1250 79317798 79317827
    0x403020a15021207032f1c020c04091101110102040315020405040c0f050301090b190605070210090806010506030c0c1b0f04111204140607030204050406080606031b012c030d 76
    0x1410ba11b508005400c1c6c010600b03a0001a900054800d0a01a510100702007030480081102203e082405004080d0901020480c114040c03800e007100301020030504d0070a0f007039024080c6084600c0d00041d089180c024025500018402410118a1640042250003800030b13128125003c0051400f10310f002c0d9544109840e4207000f10300180010000e02c0c0c0690b02c240c65000019105030960001720514a40b1500c00da00850080350000c250203041d81440f4206e96040512401e2065040703041c14102941c3c0c0b88144500c0e44a184000b00088000408009840c194409101140c44095200c00c80e50b00a804240c7da8a01542d83c0101e10002458a40216000425400000c03443c06d1000d20040c01500d50041041d03803a1814010052195a030800c01070b4483c0d40c09a40050311507003080200016215142d00c52240c90b44801c0911049980218241056014101d000f8100405080040c1d03a107810a44101035880340c0300b01343c4c0403401001e00380c0c0000c1d0740c0124256201550809400e840d2000e950304503 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 79320298 1250 79319048 79319057
    0xa0305060a08151b0d0204151425021f020709050a11030c09030316080d0f0516030b040b0607060203090d110d0e03010b091e0108010b100c080403020a1502120703 71
    0x4180360400c4490031340440c00d074404500d07252032051a02d200c00d99025502421012404041805800307910000f00c01000e601c100010b80740104071f000c0c403410419100c00e1414110a5603d04100310354070410041d00c250b1982120780f45404000c80e0194039501d8500c201081c140c200070010380c0015072841791003079050f9501c0c00c850544d1520780e0440001e400107009107401d8402002070900c0c183d0400e80901c003040c851040c60343d44e548172081d040d00b07482024101040050030402030101e8100f07000048a2140410b14000500c405e9102c002005031091011071a0441800a00304040c072440381c000318807460030002250100c1c249101c1c00c4030702000b0100c540e11245c00044940c10f205100750800502e4007802000410641000710001e44070b140e068810000706c450030600d411200340c114140f14010501d44000f0420b02d038004000c0b540c4c450200a4407400c2002c01e1454104101d9078800ba02c0141d074000d40b003420043d488400b1012042088041d880140c40b507100c8265129804101702c61540d50306549 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 79321548 1250 79320298 79320301
    0x1224020d0f0f0e0c0315100906170d030504170d1407030207030306050a03080a0f0302190507020f030c01080c0c0a0b0405030a140403020604060f11010c020d1d1c080c030a0305060a0815 81
    0x1b400320055801805c1900d20140d070840004100c041d40c001d04003c0c008a2403860b01101e0709060701c034640409064014107141c1040100404542d211031942000a10141d21583c0c60106a441c03c000700100c0c86000b0303c0c030740285c09024031a60b1660203806903034420740302000180d0b112070030820003a5076440700a000c11810450480051720603280e84a0011140c00c016051030080f4084a00000e080049c0ca4000f038400305040c015407070b00942c0041d8a078400d0300500703003642803003000030320000c001840294805800554260014000c11002440a070403440050150500d864440e40342d41c01b1000b0180040c55000c14801054030080403501102e40c0186814509482d15a007a41d0389a4503000010600c00503403840400c0903800c4c055084a00451b502601c0c40034818030015204c1d2076805244400e4010300180851192109808100c83c541e40143c0038071a400c0300d103840000b5100789a0740881501010541003085601504101d000f448103c0c0e203248016110f005555139066044943c5000c1c03401c000 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 79322798 1250 79321548 79321573
    0xf0a050604330c02101d101215051203160605040f120819020f070213110d02030103050c0906030316020303040f0303090503071224020d0f0f0e0c03 65
    0x905200d045075014060b4112485003880228000e403540441e02003400740240500718580082520310000d82030401c0100d001c1542c0030a2100002010100e0091071300c1401100141d00545103035900310500e0105001a408a2031304000c14030709886410300a22402850b0440d450012064807904c0100044820103d40d031500c8080203400054016a01c107099a4601d401041041d002c5c0100e0703c4c19a05c50201904124076081300003500030300c8200d982031060010b90171f00c0300708004659181e50106d4400d800c0c003a0b802c51450040103519050070040300c000451090140ca290041e42c104c90042e0b00351146840305909018941408507422a4141c10030060101065880032742d0100c41c60000e412241000d48403400380b0f0718074420b5001a008030340e18110401c01031a082081c44058a20b001c0c100705512000c0c0d030307500d502a405880c014500818041d0802c3c00c01c58030344c159059000104414031050b01c030400800001c04940d110450f40c2800c040b20450340c02000107101c0100100030700145080c05031003 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 79324048 1250 79322798 79322819
    0x901080703110d05040f0506010504050108030405012d090303030b010e0105120403090806150a12021f260105210319120e0105090f3c070806060f0a050604 68
    0x19094000100c00502040c920810f56202d0b041c881da2003181c0ea02c203040150f00744030780380400c16400700b40709600b00b00060244c8003001c07007541d0444a01f07003008070081c528560101d0321802c0c001603d414004c0c501001d0361080e135005511808a0b8026101000700034100c100458003003004d500400e0100341c04020740c503041000302401a0303000303009103030914009440390180c0781403800958041004007204400b08035949071440f000002001c0307905000c680030a850340800d050381c006868034482ca100520f951048203000d4901c20740c41c0004180300c2648081c2621905407901000c0c043c4500410101013162000e90307003410700d6103072010140f00940c01c01108000740c00c0a0740c10315035500200010754443c55250384540c01001c80254110340041000d2811417000c9151010481010000758040814441c170104001800320b0111103072201c5890a04000001c80d14083c1004961601ea1207680400251303040c0102d10140505070071100c001342c6095035400c00500c02d195000703540e84810b00704010450413280 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 79325298 1250 79324048 79324061
    0x11806120807050f01050c0309070806060907050714060106021f021309021606020c01020301050f1f0f0c0b0f0108010b12120a0c080705101b081603020d1104031202030901080703 78
    0x20700c121402a15413031041030a5920659522044440200034800740d140148840e070041c0154000030000da1a06c1c80000e00140c0003c1c141a0034003000085450a20481ca412101c0300100c40c030490b003155965103802982c64680d100407190b0f40b000b2005001c8160081c0c02242d070090314841843c1c030700714102040c50b4001e52008252090f2014024039020000e80e00780080c04444201000041e242e40c5010b003802800005031f0144c1340314100000f0700f24001003a03040304154665080c0383c40c0d560110000702c25924050b080c2000b41c60319115004100d005c050a41449040e550380200a0024940100c244642442514008800c07900b024800030004003804000d007089015618103503400801c55120901c4caa0b1101c03400340e646403c08686801d03501582d0144c0410480c620118001c011303001034008107544800303070109c1c1000c5c040c6200000c68502c25010780311180ea0f650010032001180c8500e02000380c0c800d100482d1120008a44c1031001c90011060b55070080060f11000095a6a01400ca000700300 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 79326548 1250 79325298 79325303
    0xd020907200d0207031b0f0b03040309120f0c0608090a0602090604090606050d0c170a180209130b06150a050d06150507020f0301090201020c210a0b011806120807 71
    0x11407450881a0070010051012a800c0b00e40241c44c8850035070a1980510250b040d150008a003070590400010050719442022101c600100c203403a42c0780c61408a03400742082e4002c1c01e2683d1840c2048040c040c0e50090314803d98400d45013041c81e40e80d60307001a1a0000c3c1200c2880e425000300c0055004510306400421050700010b0281c0c2c40d050b107034980202114581d03044000000c1c0b01080c8052840c2c03442c03140340a42e6a243c10050100c40c0102204041510000d040c849a04e40380e81d80000c0f80c00c101784408645a07801880a4100e10b8214452017070581080c0e420b032981080d0308040381141c28401404141c40d012000070602d04581d140b070913900d81c5d014100010b106582d03154001001c00e0070007030041c0c41034100c2c0e90b00da81e10402030040050816414840d280b09074580140000181e07000503144602200665508485482090420310b4445002e0310084150042d0090300d4104200210200d041c0c07280180456140100303d440c00c001c8030814040c0c0d00c190480000c10002150100c000740c0342091 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 79327798 1250 79326548 79326587
    0xe060c09040f0e0706030c0917030703030c0309061b020d0503041e05030c100209010305070e090114010507020d0b040201110a0b04030503060402070819090504020a051206040213080f010b0d020907 86
    0xba00c40c1c00f9441c01c00540d103d100040e548103201131050780e102c0e04a100030001908002d000c2d0200350310403034881c85507040040c2070650301d45140071490b0003504441030f02a000303401088a01401e500f0090401e81c0d85110b80010300414000c50b10050295045da40a650010450480380b0b51010030342d60380d0480c0d00001e0301d003484103101c2c2c4a500b090401c24882e00026090000d40c0700c01740000094180d0707501409003014000110000085900c4202103181192030500d4038400000380380c001625903124641021350070903401c0b1442e40900c0000c0d10010300840c400e980b58183d82045406194940b030038810001c0212411401040110348104080d642104000304014685041541d40d2139140e4450200410300c1c041d13100d603820b0b040d504041002c008110076501540381c03000650000b00781d44607001180f0250540c41001c02d00c640c07140d50545450400743c0b000c141c40c03692240240c95403040e950780020425820220340d403d041c20328528020300b0035409407002e245629112025035a0b00c1326803d1410201 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 79329048 1250 79327798 79327811
    0x302040302120c0f0f06191e08060306010f030c03030c0302151302100207080c0402160f051e070f05060313050607050d1a030a0f0311030409050a0e060c09040f 70
    0x698460108028258640d8010001d0fa5104014440c2035401d48040070300c80c40e145d00380c0c21001e0301c03054200c412480c805488035040c030700d107804103447d42502d0b0403001007281c0032500c08a220300d401021081c018042181100c2490703907501903100040d921404003e1024010681c100b0000e40140c1608051b14400d006850460289c6c0006101c4800c1c111078031008900150203020540c00d0000e01c107810a00d1900c0507008031401e000100d5562240380395150b0040340c0c0011480d9030b501c0b482c52558000340d403200d001081d500860605030758542207900028a065651070858a42240000c0c22404607421422240c032803d20302010410a604003c2ca1400c8094481c1d12080004500748030300380c80381205850381611451042084001c4800c4100607a45000154086070034a46e1b0000b84001740e5507200c1d2400b800481c4520341215180c04141901860384008100403810251640040c2d10945500700c0800c60191400349440d5900c4041d5203c80c00b803a010000c10030107040030340103e82c88046011020441 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 79330298 1250 79329048 79329053
    0x60307050f0f0703110a0b06010e03030c03040b0a0809010c0e09150a030b01061403041709130c020303041e030c06111314040b01090305101e0504030c0c061407060b0103020403 77
    0x1c5600444490b00c5000002442d00c0405800071848411407156800520780f00040d40e0b42d90000603000b400c450305122010b030812015581c2042140c0c10000b407101601c1c4c449540717414080e80381d0020982d04001c20050000245c440c0d070140308070707007420710240d5a03090480020002d100e6101b03805005c006543e0000b1450100035220180f10300000c620414112810b0343c5001c80041c0a01c811105c0c05815410810030f20002c0352003800146401c026103009241e41e5212000000c003155200615a02110300f01213200d582144c0100c05148030310b02400d41900b601c0d402c0c038503006906480c0e0348001c02040c1c3c0250040d000c50001d50042c66518406107050703150070040c0741c94906a0103554006840c6100f19130f80380495041038001c00a00c3c100a080c2096283d00b107964558441a11014040f41281d9a50000020700308500c408144800001c1c4100018205030800402e04400d0840603202043e90b114005019441165828550019482401e040075010394900c2c024000000030641055002e0002002 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 79331548 1250 79330298 79330327
    0x311040b07050d0f0302070804050f03010228080a09120c0816050a060f060f03060504020607021002030c0d1404091508030412060605090606030426040f031e050c06030705 75
    0x40301d002e64020240a1581400180496182e00d465003c141c018007008000071001c106a600b40c035003c45004101c15050380c04240240100703008120303400041e40001112040140551340c07503005903a11441c0d00d40d6084030b12005e4555100c0001d1140010400d9010003d10039002161440e100700c4445151480043c03400c0d90076103e00c4001e03105a00070281c10410400240b1804e02c0128540c0020f014591030100c09418500541c0310141050751100005000c56a0300b90481c1c042c10360041480c002007410107002903480d00811200e001c5c910404000c0681d00c0d0041344949548070510f031007146000d0824540c0c4020304001d00c0d241101d088502c40c045840c040501c0944040c1120303036030702c01104407a41400b406030351082c0d0090340524400024000c8540700c1ca8100c0346c0c410b800c5002e05202c2e000c44500e0008034000b41e95070240100c0045804034640010781c00840441e4003513240250042926106000968100100141f042c4c2c40b04160740c03041e04202000d1a0b1004aa08003207090081d18841e105 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 79332798 1250 79331548 79331557
    0xb010207150207060905122509020403030c111e0f0307090e030913060302030c060c0c041103190b060415090806040609020a0801050601200304080a0506010e0c0c0303070311040b 78
    0x2400341c0c0040300d0510904d03070b1044100000306403c1b500300e56007403d080801c1e030b00d808116400810600c400303423900b4503201c030514035213000b45440c0000319915a622304008000c4501103100720b2310900c1002481c034103031030b002212a2a111505400301c101c88151010414641d03081c0c100b190300f5004044000440c00302c68031403a41414001d001459582000c1000c0010100319000c07900c81461401c9070901c0584c40000702c5040e84142501c58544c0c400c54409490f04c1c0003440040c15510234184040d000a203440800a14001d003821000308a4503c02c40c15040c060365180700313225401c0401800200b00c02c0c55250010b124403a030a080140480340c84118241c10080101e5083d070328a912040003030704600b00a0b060500500310704008101710308041000904404000c681f80c418a00400f074810f602c180180110703002007009104403140f4952504c1c00039129a4244076200003d82c05100250135400080101c0311701101c454003075032950341c6280701a00180b100e00202054140180b00c0482e00800c41c60060 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 79334048 1250 79332798 79332839
    0x601020a060203100302100f0e060a03020409050405010c0806101403041e110916050702040f020c01021b0c03060405030f0c0a0b04050a060509031903270c0306060501030c0905040b010207 82
    0x41c804a0171401031085040d9610910020007840002114205910401e8801407181c02c5030319a50343c0000c41421400b0b03005507013000f80d0041c40c00042c4420007405501c88650b0680f251640030560740d0348000c10803191284d00001e0041040c0511507800c0b482c65800540d813140c8a507840141811003c84181034810306581b08440d01c0409042303000446c64148085548068407903109180150f45440c020300354010b600c0002c1c00365448040610003581c070b54060711a2410b118008644590180308104100104000c0418041c0907130003880785541000b00707006d4440c0e078101c402140f520b100042d402c2070075032110320a44040e02074104030400103282920b64900a03030041d0010544c10103541444400c4550142240000da80308101c0310311030310554028803943c3c1c160f038100082e800b0005080700075400d00080c05483c0e51142d01c410302041080080e1005c042d0390040b05e00f00405629540103404450044141401240b81c4500030000c510745500303c0c0a0515040c8165080545d0768002c90903c0b1b480226003 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 79335298 1250 79334048 79334071
    0x30f0408010f0b011b050109140c0a0b09010f230406030e0607020a0b1b040504020a02030a0807090509010302040506010e040504050d0f02070f09020f041d04110103140f0601020a060203 81
    0x2000a01024000c182c800400d19508000b0018018000703410170008030203178281054101d00540c1440f1081d4002d00526070004045a032488a940030b10342c039403c0080030385100c0d07409440003103181138070710082e25101d01d010385400b01303251a4402d003900c40082c00540035074000e000c3e055100c00e03c5115030141000b0003c0d03807004940c0780c120a60260520038010040780855000c48403440102c0c4c80844829004a4003010b01e5240b81000030f82d441da0b42c0f0598000715001800012400c50b4164000000c01c2c664119a0f60050580c070340c031768200d405010718442c842d84500c806e4018409403800d40e00580d00203c0505014482801c100d0201d020303240102c0b0180c6035074000941d024851a004581c1c54840d041e284046c0039011306200c405191030510f03001345840710381e0204080281000142c21200034240152043e1502c111420803003103140000c690884144e100b5840041e2154000d0003010b0b881680d640031000d0aa41d1512142c0401c40f00400840c118810b0600503000300c0e005100131806030141a14 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 79336548 1250 79335298 79335307
    0x20604020a080307050c09131704060801060f0e0f01110604060608010606030603020117070e1f14044a0405011103061c03090b04060509032506081008030f 68
    0x4125401c0115840100150030401c0030800103940490515410442202e10640301d0315003071908100c1d8030380034800402c80003004140c038000401800141c011a042075980000903070300e5079012258202001d1388080414134513051002e103481e048054800f0901c1c10f15101c040c0d0f003860b2210528011040e241a01c0d85a034a40060001000a000381030141c179080c02c0c18440e0500d191b00080c405040d40800d030003981c60304800f045240c1d02c241e0740d424204000421500c0c1d0f0441115140041140a491310004030f049124004143c0c0c0742c40095400711a51041150301482c400f425185501000d04c1c8441c02031148100c0c403030641400e101e0890544d100070f035032003c800e1406182c403e0845e0000c10441340044414820817030380f661402240c0c00824070209184500300f00519003a144100190400c051104000c180410703c5544240070301081c3c14200c08035429007034103c0c0741e10b203050710003074543e42c040304516000c0c01900c0c01100012381024228100000e09980c65501c03500b1a00f0601043c080d2290016 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 79337798 1250 79336548 79336553
    0x13080f160302010b0927010905120c07050d02180a0e060115020105090a0b0103020d03030209060d020a081501090611030c0d0206090d030e030405090403170f0717010b091519020604 79
    0x45a43c1081d5405d8078089094100707400700715070350710441c0b00f9011040d10010403102041001c1d0042c0c01d181d07502804807401211b5010b221030054000b445040e000d40b048c0c9000042c0380c5001201214801c0d0060042a55104030320401c0c10a80f0004002602054440c2c545a840e42001c20909000b07001c1645004440c602840c0700909580018021079400d61102200c080843d500902040c1120f504076520300d46503100e480c3c190302900486c00280e0b40810003240306078100745281c0040554300c01c155140522a0b840130011500103040e19041800101e00902c1804410300071104c0043e0864401c086a041a41c41e03070742240f609403450303a0600183c01c00d4007485104101004110f048030102d0406215411210041c0355481c000d40c030401d4071440c0d5901c00301d810705000794210100c031880a05a00854504800c3c03400042c074050b81c824000540000320341090499840400b4103803110011444c1c540380e172210410000891304c4456070b01140f810030081d106040c0200000303042c40300d19009040c0d945001e0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 79339048 1250 79337798 79337801
    0x409050a050d110c090c130e0c04030c05030a05060a02092202041a0406020a031b080c06010609051206010314071d0a05070507120807110d05090306060103060e13080f16030201 77
    0x50240c1815800188003403210394905c440d855020f4220b041c16500c414407662644000d8001e6444071640c415070ba028040c0900110b00204241c038000c0800f1149a0303514002d05a0303401c400440980306420000c0465103c450f0b64004045001005000501d21124040f4480d1000c00720740e0910310701607000404001001450f10300207005139500b0321140c1001d1a0000207500c481c00070100408220780310303d03950b0401d140e000090704503607040005546c68841291510356204828000e2901040300c042d400202844e003034141580040c5480090300071a441c3da503c2c50394400c545281c40c000c80c0030740b040200341490101d505803454250710070002001e007400a200300c1103034030181071181040b208000140c0810320b481228148458a4940b10f4000e50300c9802c106d41a81aa05003034000740105046c96055540c05005441400811420359a0365201caa0040d03040f100c0ca0f1140004d038404000001da07284911200d500303d2240a0312202d450003000ca0b4049030a980200200c04214504000c11002c1c503909 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 79340298 1250 79339048 79339067
    0x609040e0f0f0a0f030305190203070302270a0306020310080f0601031a060109140111030a02030408120304020d03051b010504060c081605030105100311030a052a030c090409050a050d 80
    0x81c1d0240803112002c3d100d00c4004c1114440290038162600c000c650000c04481041a03030000d4000c003151241030400d4020041e602c21500e0700c00340ca0000400ba184101c503660039840b251401050b089a080c910b80c0c0b2100170350801003e0254201070848001605101802020090103a07040175140a43c15490407181c0d4802a11209480b0003070003040009698100f0f8100040da04c2200755034459038502e02c0100c1e5030507141286e00c0c01900004c10342d0401c0d075400002800580d8659415200901040c00480855010413a0081c0d8441c050720030200c0406c0c0180c0080448409041140030007040d4a941c0b00e007035440a07582180e100741d49038284100d0313550000d80142c001d850b2001ba9403444c22807c00c000c0c603900040c01803910600c3c041c1400d440d5140290310441d0f200b07004262182d102c0c44c1c0084504010201218404c01c6104008408044400b50810419030503400e40740103400d64588000c080c01a401030203803143c20030348d208004000314800700050701000344150010f2124403a22000180181a03 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 79341548 1250 79340298 79340323
    0xe1e01060f141e030a060b0418050d020c01030203060a211b0303030b01020307030c030f0e0d050601050102010617060f04060f0f061809020906090901061d06010f0903030516020609040e0f 82
    0x1080030f4052000d580211303412403000d4000b0700100b02d001c041000140204950f84c04140c91404160307542c4100000450002a00040c9400782d0310040030310b400641c181d1004032816684680c05280620090160366440200c2007605620080f18003029600d45035002d03c007101d40c00390310b070b407150b001c004060b45030080700c3e11207000303101640c1848004c0d600a0140310c0d0000c4020184179000c54505841840740144e40000a00103003a108000c40904046460301400c1c02024015400c00c01d0100b89801c542004008650005001f0001a84c904070341e080c89440240c401c60795143c40d229100f50321030710f5001b02004400e200c0e00c0050824904403507540641c0502ca54202014101007810740542d032506c452603449030003500c031005103a44010078240101015042140700b41203180020010201e0b10008500c190000e032151046a203080ca01130741c1d00303045484000c0001e0341c03c001e83c884561442902c2100341d44041c2c425814050003030005400c0e541001243c505681c84208100720483c4204200b40345d542 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 79342798 1250 79341548 79341589
    0x20a050d020609220f24030b010e0a0b040e0303100905090d03020c010902120717070f0504020d09020a09020715060803030615270102010f0e1e01060f14 67
    0xd940d40450b580e400340000b414802d9a41c2d41c1041d6a040f060100e00d4100d00c07407024200700501c10000124020203224003461503a0908074040200d407242d02c8415000c1e280c12034040001a80b0344603400c0f101c1813004000c3e091304d41e1a10b00307040040d107850144070314143d5010301842e01c2e4075184a00440c40a85940b040350094145014400c0d40c0c5000305107400c04102900d40540c2e20001310851602600c0303140d0000307403c402d4030810010401d0000c01d05005031100410020a02d4800414860351030185009005083d40040410000f6103015402030003a50380c1c0c82404101c240b0150002004c014060303001c09280c0d600082c92104000319500f03240d4038100003200c1000010b04092031241d503404010000c81c0034486e0800300404407050581901c0c04041c0401c0001d40b100c0d84207001641c00301d19803601501542c28050b11408104817070268840d0003002e180104440010540116405146074402403001c0d50f0b25038001c1105001850b41a01400159480ba51048028410301a65420710614200e080 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 79344048 1250 79342798 79342819
    0x60724092405060a15030b0303042606090c0105030a09020f1002010501050a050102031309021b010204120b0f07080718090509030712091d0402130f0507031505060f03181009020a05 79
    0x8117105910a504921103240028906000f4808a8034622540e0810031424484255800e0011003604505000040f030b2400e50303d0603190b44007010f5a818406c507a540c0403e4041c8005018288a54084103079030340001c1c004c031601744500001c140b582c070503182140010303519800188040c0c10440c1e51880142800c1c801180b4100c04480d80c0b5800b01d0003405204800d50700052228003914680090aa102030b44074021592569a0745140e0b400001d0410222003100c2c5c400e0028014140502e0300d24814225a02c1d00300d002d03914907004880e034694800c0c012035241103a403000301e90304080e4418617110341e180704001d50361403c0c203003001c06124203940c58410800490840511456040c5500e072000300c1da019005517016201c0e44000340d2078015490900100902c0d0001070080c506541d00254000c04207524104860326402054401d000001d01401d90003401c104544c1d01c4000122004613803159034003610300300c00c01100441034201070404050451103078540f102082545452a1514020502102c00c201517 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 79345298 1250 79344048 79344059
    0x100201050a0e161701061a040e010509190b010324080c1f1b060c0503040303151a0304020a0801090b0702060c0a08010311030a020301020f0414060724092405060a 71
    0x4041c2640101819800703103800c094050f04c401d402030b002030124032070700e0b074031016108100400580261160200000c00240001114100010302900508039170055581c1c00a15201c5403000d030503030310030841c100f607660030b49030182c00d0500501c080818400a200e0500d40e2400d030300030b4600720041070464031030010400c00d01c6450a009419001455690412415000b81e890240c0c580b03007990300000e070100c4e0a0801038480258428003d510803071180d101086a05400162040da070212030103800201c50000d607140f1401d010510146501a1000b00710415064a5952a41c04d4402c541c90031501c03008408180300c0c0d519014000c1d10b5100c5007103c0c1840c100f6031140c2d0010044541884043c226013051349114040b80c400f84004c8840f070750040d0003591f5070001d0300c0307a590fa00e5205216030400380e1340d00241d007a010b141c114120382070140c0090006000340d03400400d41c0c0b200320030ba40d40c038003400d642c40b0030060008994180d00d41d000b2400e40b007403088141e40c1700c00310025900000e01661140c03002c0030b4107020 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 79346548 1250 79345298 79345333
    0x80102131203020c0405070e01110111031b0403020a09050103030215060f0907020a0b0c0c100605090703051009060e0a0c0201090f03050a03020d020c01020c0f061e060a0302100201050a0e 82
    0x101e810501014140141e80c1c20140e04001100085603005801c140c1008600b54010081c10701401c400e985a64080110161880c2215108500340d16071140400214480740815648034a903030007804407c5160598903800500b8640095011044281e21b0b04010818180c0501401807003e0a040c0d440c1081c0c43c003000096441244900403c0c8142d4090022400c9544200049500254001907150701800c21342064035035904802c0008050740b0450301c0301c52503000725004031011100040c1c40e03001c440c0c40d80e031000da0240400400c000040310070070000103910b85107805610010080f4080b0501c0d0750030080700740e4050316003080101c0103581c1040b04000001340807140001c1e100e0317014a017490312030444640450181c402c1d0b4400040850000ca0940b840c89019401820071807401c80450340520000480e00d5280c8200b217405030780042d0b2040700c0d181940480034060303501020007003080c14a9a165400240c203503c5440034400180c0d555010002e070310322075101c0d0700300b075500c0c1c5001412420a032242000 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 79347798 1250 79346548 79346587
    0x308060a120609031b0309080723040209061c0603150c0f03050402060d15090e0f06010614070b01060e0a0509011401050c0f060106081b0403020d020d170d020a09080102 74
    0x2c0c46566203000b40000d02d84180802e00700c0141c82d5011004000701420000d00441d01e50050381170078042d08100055080400c034040c0310b000d45c900900154070044c081080000d402428070383d41c2240082106140d944070b20260305404900d100700010f001030550030308078050301619052844062802030841406030304030036030611702d030910300c1e0124541d60f40c1d1000c40d83e140540006800e2680c01e00d401e9001c8008119102400c0d0391500e5820481d54040840155992150040c44042904601e006015091160031044008408050903500c0d103407440e59116a2954244e10860000d07411401e14002803074031107542001041c0844584601d0b50600502e100c900c50404c2d0114180800020800b0b40440c0038422508511248010f03101c3c60340c1d4a03e80a04140400c44100400303118515910f2407102d01c240c103503026203401401e035680306d2216600303000c1d15640303404007581e030203000d80c181411049444009100381d01d00d1200141e2107510404000d011815250003500d280e03401406140c1040101e04181c5 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 79349048 1250 79347798 79347803
    0x3030509130b0619110c0a060c0c081f0f05010608070c0f2102060901140c030a0b0a0609080c010219060903050d090b0609060102031201350a0308060a12 67
    0x1c1d18210184041e500c01450000442c030b0304060301250455000c402040031152000641c2c55806021804500490329918000d0b1a540c1c0101c401c401072160611413101041d03602d00c81c0c2402441c03140c0b10005203250100784100f010b0740704244d068405001e05540580981e401355010103101c1c1e941001c9001e0b000d140c2c01401c2c20300b0440160000400c3c0300407a88685a041c0d00524647c0040325403029001110a202d040707400507108600200381162414071076010510750702c1c00d51120b6500d9195a071100d950014010510316500c030200c60546943d4401900000c01007512140001480d140b146414030000c048101d040d500710100304007500e20302d038030040344007a400800001e08102c1e038a001c0e2810b0045031110f4450500c3c0000d0203040102000031a40030780e20840300071034250b4542c0012652032141050300754468503e140100100384280705509092104074025103050640320000d5043e044030381406003103a500c01003509007070680040c5482e411038400d03140c06010034100706091300c3c0d402c03c04800 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 79350298 1250 79349048 79349059
    0x7030c091b050a022e150e0402010806040f0c02150901060e04020d1a07080603150126010b19031b151d0a12020108060303030601090302041d030a020610060903030509 73
    0x11030450b10912071030001d085c496580c031200e0b20400d80c001221a00044070810101d1074011701480e004084010841143c2a580ca804001c1d41d940d8011541c04402070300c181e80140d00c40c03140102c140458050503030794081c183d0040000b440040c1d0103c03040300b005044024103900d040c0007446040d00a12105a1158040e55051001030040c41c1c58a40d1700403c40c2603048008040041c085456489141c503401504101d04403040c41c4d21809582141035000e00c155811a000b000b001d964050048000b00740b0024003400000c1c4611146c0301141100310749982c9c86c02910000c540038010003082c3c0c00ca40000400c40d1079034500c5070b0700b4000f5400c041d1880d602001c060185031a07500e43c0f80c0f03211203400320000b0350203400140380941e5a20400c19600314140224003040003034002401d01e040c0002070744c0c03140c54142e494000741481d640a010040042000f0081485050700f10204141030410081c130b4640300c81c0e401010245030038061100102c40c5904414100103404d002000030030f1b8003000756000d030b4208952 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 79351548 1250 79350298 79350307
    0x181506030612030301060210060b04050607060e01061a07060e0a030203092809090308090a0c17030f0307020609070f0303020d1b0606080318011e0807110106030507030c091b05 77
    0x19042040b0000700c40702d0340720000000c50000c2c2e002c500104071028000b000e000994542004001c41c0c000c0c0c0c05000d4100606104407000300c2c1060308950326007400030000081150300d03401074850503806010000360410b80040c00307504000d610300c6104210b1100c40e0282444400c0f95400940ba80b050010b018814132100e03089030380c0c0301c050100c005401d03840c0020340741099642d550b50384042e00305004140c010412440c005107515902181208101e82d0040c01d0034103090030040d40b036180d100c0020140703036207101c14001680c40182d5440194042c42090300148014500000c1161800c1d40c0c03030f08503080f40c1400300020000070742c000848202c5074015040c015091851601925400003160f08054412030500c0c07000a1000e00100040c4490019410b00c0d0044410060040d501849140e108442c0c0344480080800d00b41e2240c07044a400c041c40e807605a860180140003903080d0340c8550001d84054000300c000704100014510a00003d09000c10b00303000043c003807481840844441100441805400034 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 79352798 1250 79351548 79351561
    0x90e0708060712110a08010302010f020a08130302120a05060c160819020106050a1a160b040b010503010b0114030403080402060f0f04140a05060403150204150201050618150603 77
    0x56201504011080724224546154018a89034030740c0100b480e0705142c6207914000406403421104011816200c00503940d20b07541c011500c06000301e14502c00c502500f01040000f07a411002004c0144c61101130382006400c50042000c80c940600451495600c1420394030001a00842c059a111005800781390f11958541c4e1a81d50321004a00020288480064580c00e41084e04942480d03280559000708002c43d10741050104440039801500c0d00c482c040000c0343d0f0715405140c02000501a145000c1e1086d110399034500030300c547d05440448121200c90014841410b0901c103d96002000b441d000400502118000d2624031002c0c20180802409000090654913060111072450020900580d0303558000290b548181e00030703000b044003100091003060b00c140f800480d0182580c1c0c000f0410340c035082c0b465540e680e6229140ca032058010303400b0b200014a00a454580c081e403890b158001144900c3c100041000180c4050a03100c078080102007441046459400d0300782c450642130307034100c3e620780b00d0b40d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 79354048 1250 79352798 79352803
    0x607050d14010618090b181b03010303021e011103060f0a08060a020702030705030c06040b0d090c2301031515050706050403111204080d050d23060a09050907090e 71
    0x890501400080c5000050030a0b400020010a001000d9613040e5640e107a020420548880c9840300c0d51140000b44d024203070540c805102c1e0342101c0850500300e8086501401c18100350401da00540250b0400e2005602041036072a2a0a00071198030003000480503001e16100d05000280c05140204070030829074030151100c4108002404c6004208d910b60b1034000701c020041c0d444440100d000f4080e5020018207410f00089101a003d8001e200e1400e05081104948042c0c1040c15145001521881040c0200b880140240003070401e01c00d00100807120900d4600025441510306810189401c3c2240b4600c44020b030032009880841103004441401403200b12010300031a0806030446d03240409200825030480400c1080d4080c03c01031f44c2c1d1920600c58a260300b4010741c4102000d58103c1084030344d00e10b1050700103000f088402040025141040440b00003400030284080c106640060188905890066444001000c01c140144454034218a00d251554440c4c0704004050b07440d0740e078900c0e801d40c05 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 79355298 1250 79354048 79354061
    0x80f060a0b07020f03100615110c010e010216030302010c14191103070c0b0c06010b0304080301050d0804081606080a020a020312060409140c010e0406030203060610110f0106081009050607050d 84
    0x60480d46c1c3c400340014a60010004e5101f00c4215200c801c84403590f0b980101101c00650f0415405002001484401541c02080800380c00741140200d07440c0c2d0f00110074804015018500985c000035150751424400340c5071f040c5446000d0140d0380c00b0701160080c64014110b1800ca800306160000c82c8442d140301c1c0500d50300510380c00400400c5640c001113080c0d4030b58030107000301100c000308079080382e6070342c000300c0145200960700601076803003c200600003802d02d51046420588943c450304d01d02652101d03c1420004a04d4500c10450a120020003006901c41c0c000b64204801880442c500120050065600d108140c0380e600c01d03820b1030000801d196140d5000c0c03442c0c3c2c0c0e003000c1004900b0a101c10350a440b01e64007443c10780480d04c0031003800c40f14182845007006881e4054014221910340304100241c142803561802c0403c4405108140e100b03009211003e80c0f12420400801c8035410010143e082c0f138048441c00030028503000c40071001c02c4002454542208840c209950340d18074107070200018005 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 79356548 1250 79355298 79355329
    0xf03020c010e03120a060605030a0c0c08190801050909100b040603050312160c020d0f02280806010806101814010f0501030f0e210d1407080f060a0b0702 67
    0x2806031803221204000c0000d012144c203440203007841d655031580d034004403030b507038010390002440c188005010001242d0021000544c1410b00c44000c6129503203d5029501c4039160741d44240c84104060441034201049601400c400c650a040a2500e9040c0c1341d6280000d0001a80d129151068104030b41c840c0c0c0e024a003c0c42c1c01c001900e680f00307071000c0c002c481c55070143ca8140602502d0101c810a03188102040306950380d00420b00000c0110a403540740541da42454181c2e80a02580d0202c0d00505040c100c09446010000454103100d00e482406070805c001640000b400c0e030001c6040042c01c211200042c426119900080c884026551001c0e900800b52007508844e000900340021070682501c442c1182110000d99080c0301c2140f5228410f0207903841340091741f4259110701c941cbc44600c03094180d40d00d000a0100c01c15401d11403490041c1d010f44190881200c407840031842031050850b130043c0070940c044640f441c1c0c440c80c1d0514101190b030304141c03840745440140002ca42d80046544e01181e2510215 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 79357798 1250 79356548 79356551
    0x3030d02160f03020a03090906060504140402160605100501050304080a0305090708010509100c05070c060e040b0604030602070303051e0c0a0903080c010f1a1c050c030303090d030f0504020306070f03020c01 90
    0xc41c0c40c02945e94000303200300b44c3c00b040703a4000002e6001c484e0f014840581d003007655800c0c00c0a00d0041460000b610310218207074855004d0000c0d1600e11076417140089a68000c0b800410329040c0a0320394044e180190304121b040101c00c200b0000414482411212249018030300000c1958490484c10f08201c9944c005140650800007402145400018070b00041e22458404100054100605a80501c244440100700c0d010b0a1b104108041c041c0012500700d803070160000c0351501840c4002402a401904103c48041c1e003c1002414180c0c513118865015200800c102e00d0b4140047c04400e507180020039002c050800001c8152605109440b1352000b56403040d142c9072110b803a00b8081e80685002d078011102d00307113099808080b00580e600c0684403120060704402201410801b80c54400180d00400c0d6414480c03403510611a8608100861041c80090080d0074990800380004098030010a40c812145042c9010311000d070b5008507031b0a8122508e810810031340d00c1588000e4003c1d009092807041c40d035 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 79359048 1250 79357798 79357823
    0x30c0403120c03080f040f030806030705030a051c052703030904020301060c030e03030a050909060f0a120b090706050301050603040317010602030405120714131e09020405060f03030d0216 82
    0x1900005081d28043c0710f901c4001c1c41da5104500d00400c00d9040320b0240042d4038494013403001c01d01414905d130300010302601313646e180b58998020078546540c5030302c1118184d01031402480440170240304a582a030040c13814a1900c50707410800e1142500007a248001c0f500d103007218600a9400300304407417111201800554032581e44020140100100751804d03030100d50100240400341c80d02008071602c10030107448042c101100c5030300740040700c4001403105030800d501001007140b1303584000d410030081c40c10200700b403c45403040c900f001d50004081d103400340a030f003d040c0510446411500f52415078000707031151a166525828229a15042800d040e03003003060100010641c41e41c048010002e50b10280e03604000c0170400361486903035540520500d40c55501c1041035032030610b080100c2182009041501007540c3d0284107542d490702004031010080c0720303669840201182030500882e5448202140c981d02c540c0c41d181e0120b0380764444c2e4801660707050f5000035003440800440c000c90304042d40156221140 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 79360298 1250 79359048 79359083
    0x3090307021801231c02060d0906020a180501080106050921100e03070209061012020c0102090a0506030f04061d0105011e151b03091e0501030b06120606030c0403 71
    0x81d107000c3c0501d204d401401c0c200440194419110100002c40203401c010403624224072034090b00380c089408036444242084100c440d081140562102580242001a901c16501030060080300400c4181d40c140710b4600c1c820495a030300f00226038110307203041c1032081d52149141c001802060664018007250440f080310340c0c0007840002000c0b100f01d136039103204000e404d005805d140d40c0c0303000300e002c0250302006010018456061441003a188130785942080c2d460001c034810024186d0b008040380030b41c2e682d400310309a01d00b441e20078a5a002810b0070781c1c2d024518202240a00306402c030060014201070385803952012080c1100e62031140c000d03e014002c00595071214200f060f0801d0841e00200c454903110300129089050540d100b5040b5641e4685a01d0341011039850421a030180d4015010b01810303510020300402c59181102e0401d100c0c9201c41600c1c5e00304400941241c001c1d40b69130f402030384144507094903482c58002160700018103e4081d602c990712000c034182a40f041c1c0d04014008840007080e000e1 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 79361548 1250 79360298 79360339
    0x4110c01091b050618030f0d03050f1b0307030c0210020403080301030c0e011d07020102160b06040e0d0c080d0e010c080405070b0708070b040f08030c070501060509010f05060309030702 81
    0x2001e80c455055607078484641c1200e50300007582c60003450f60002040140b01c01a11140300c42140c1d480700942a140242201601c280c01c1c9010050f1160209488a0802808041168100307900502840300f003015070755003101301c060501005080c2c400b410f6031594003241c01402080301c08904102c1ca01c00355640cce602c914019110380c00030701c01141c1d695450742001c241c41030245900d178142e4102a0701c0d2902d001001504c88040f80000d400002555800c00c4104200c0384050410110035006207500c01c1d545c28100148011204104080180358000743e100030780c0c05a000118400d00da4000100c2512000480181c00082c00d540d00c60200a41c0307031046c3c03d0070994003e01e82c3d510880c02801030761754450b039807000c405161207401001009514108002c80001c2e248018080c0c1060040044c010b05004580c1c039011198801e03141c02d0550300d00440d2100400001740580c80c058041a40c502200d5454090415288401400f0b8148545004000502c00b01020000e4a02e002d80051129840c0c00620031203d0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 79362798 1250 79361548 79361561
    0x6080414060709081b010503130602040306050103140f06060307170f01060f03020117040f0b0c0702030a06020d060909150e0f071202270402150d0510050111070b04030b0604110c01 79
    0x31864055917484d80030300c04c4d003081030b0130101806848040c44c0d6500c0c0c0011682040c99140c0481c0c100da424803003c40481c1d10307071246038065480b0701e00da2204007070b10300303c4540781610103d02a00982d014404100e41c0303880c041440300c2143c8891903103c50700d4203225282410700a4070010f00d4529841c4c410b00043c0c0c2e4041e2840d2000f103e0007038958010076151202c41d1508850200c4000d4280e02a40b403404001506074444103074015281c403280784c10b00005a0029003460403685003504ca4a4000c660310120780c2003845150010320310400d04118021548d80c801c0480145103d91001495841884d541021001d10100d5260b2200006542040b0b84480d440105d0382c904020580c0104900c4a520030002050b0138000c5848006000000540da19030b800c102d4601106241900081c2d000e100c0042c024100d4020140260b02c5800703070700f204908241c001000090203400460090380144000c10480c001d5008941c26250840c0c41c0d544c5a55801d00850b01034414884511400100010851120417040d0f00c1031 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 79364048 1250 79362798 79362809
    0x204020d0b1807110a1707140102031009060f03050c0d0303020918041703090a020d060b151b0a0206220302060d020a110c0303040501030209040f0603080d060801020a0906080414060709 81
    0x1080200700d0030704d60320b80d58200b54400915111a482004952080f903074040c240071440341c152015034440c08141c0e2426078200b50b80501249499003401d103d009014011329002c0d00d174512040807058596120943e4804100448902418140f0941000d143c844d40407075401c1840584803182082840d1900050b0201c02c40d42034400303c68140b10101c01240c2001101e0140da001801403600550907001c00458001c0d104048580c80c0d1b80e0b10ba148055100c5da0700c0003002142c103104c819203550000310b05100c4221040981d1980f030700718000c13501c010380d0fa45d01030314294402d210f614204440301e051002c042c1d94894002030340c0248042840d102540880d0018816444183d5030010400e407640200d641d10450303009940d91580041c4400c0c4001c0d4400d501921441c00c5c02480810350501300c0f0007850858555410581701d00d00009140c0d5590380d41030240e04001d2074500c000b1032420010140040400301c1d98003480c0d0401070640080f80602440300c1d0741100d040098000e541e203a00305510050b00c1d8001c0b92003239 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 79365298 1250 79364048 79364057
    0x3130605040f0318032a0306050709030311030901090611190b071d0609040e120d021201060c0b0c070203100507110d080103020607141e010f0605040b0a030204020d0b1807 75
    0xb4020700041c1510300b113040301c3e4466076940350a019107400f0344d40220100c2500341140a201c00c00000f0401d03d0051078040d0043e600c3d980345950450030003c18030141c0311200151903004015801099a1001038130f4201c80302850300f6404500081c0265051074950f00307201c20709130b900c18809801d10410a60940c01600a900c2e80c42d04080c1d05107014440c41c003a0007001c0d42c00f000910604145007850f402003001c0307480410990340f99941d032003203281041c0c120006401d0090740c04075840700c900e94000c103071501418440c1810040c070101c680c0d03914400d0400810062005071701290361011518100700c9004220711980c4103004902c2c100c24010442e401440051043d88610280118590f0044400e54103a90f0050541468020f19803103055510f018248184818494840542c104142050301804c890074030340c00120350441c8004800c81512403d8102c40c1c07086291083c5450180d82e200c01c0308040b681c1c180c602588038641070a128000300380c1c0504042c2c00104400c926410031031800d13052840350049071107 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 79366548 1250 79365298 79365317
    0x60103110103060e091c0215160801080f07060309060908070b06030601051512100b0a0302040e16021b061e040302030709110a080402030703020a08010e0c100e0603130605040f03 78
    0x4e01d08410105449685e4942c20000b075504015502240324140705d096401165140c1a0f51186001e152404458060510315080458420554040f51181c010700b2031000074280e148130f00c4040c3c0e84030382d031501c20300050540d2100c0d0070f4208065a044a40c0e1107401001c00d5855130483e041c00b81d54803604803140e520078040c45002140602c0c284190300100000b03400560704221159a007000c00c8040648000302044010300c00084030195000104090010ba9030050389a5151900d800b103150009002826414800403502c50b00340e03030000e44103e09400da20706801121000b44040f034010322441d0002c0c040074800c46200465101410001d000702d901c00d030129181c441d80d4203003403800c41d114404c0c0d03a001c5540c1080206215480740601d0354106000400b030302c14040d501e900040c90007840c0c3d403007024540d4456807188031014043c01a01420842138a0303030b20003010301c0340006020940c2580020301c15140440401e01c40a0304451074a181c9601c110308200c9820107040c6030145049040040300080c40814 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 79367798 1250 79366548 79366559
    0x12060b0c100c120f060512100e0615040f0e03160302102304030e1e04150501140a02030403060c08040b01120c051215070801080c0103023906010311010306 68
    0x8124030b5400c039190740b0740358080003040044000e010720888121000b6201c0701c02284583d42c062000d1130400900b070051121000170300403501a034403030340c01c40041c0d81c01000400240d0342054406102d03816080300d001416001c82c040703200040c1150540321045100c0403405044170300110310078104082c025021038020385418090402030350205410340c0c403001c1f2001d1200d0841c487ea101100d4001e486030401c240e02c20100004506207507140c1000b4101d01119190030050350406100381a00c040b8005001c4004909007400079000403080030030310f0100c0b6000265031031818070a00a40d0301442d80302909002009038008010810740d402e40b000c0d142149200c00003d011600340620407001d41e840003e501250346048100680780e83c2c00311400d2014001c0700006010f03080302070000c9104160300c0c0c403100c43c0b55041c011110301c0c203240100e48606141c410422100c3c00c4843c0d4400900120b4142c550529408030800d4000c8121842c0c5802d076000e2140b500080b040218103051220945002c0e03030108000c45d40e85 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 79369048 1250 79367798 79367801
    0xc07080601150302090102030705010c0804020f060915090301060e09010204030501061203120b04021b06010e07020a08030604050405120406031a01030204031a1005100e030f01050708150112060b0c10 87
    0x80c814007460302a040b81000345035002e41c014040111050050701d0400d4500c6e00c403182510b841840b480d0000300301d00208070031450155000c0e40111070655680e41000003100104da0b1040b84a002c2d8034285001007041d5200c0d903025000b000290800c80101d02040c2860b00c0c17014082c3d00180001c485c0380d400c0034000300b030291500c030f07588103219003542c0c46000d4103100c1c0b00110000c100e1038068603086030302040b4103191084240c801c4101d0100202c0209072540c506404028903410242c1002d003103402229500700400d0742e0380300307803a0858811200001c41d600c0d00d1416615104a2600d115240c2502250014a90b42c041d48104007a050320880240c4075181100110100d04c40c03404020400a540c104007117900c50f1549141d0f03402040c0400064049484800049013820245500030000306800c141d18003a0905000c030010b800702420080c862400c00c403002078101d450042000007104210904400c0d56841812400502003a260707081143d6500d42c3d110b144964040c1e0283c0d50f40344a141d8a17400141d43c00e = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 79370298 1250 79369048 79369051
    0xa090b0307060c0303110a050a0314010b1b0a05162c0a05070212160614100b0304050312010303080402090f07020705040f0b0405010f06080919030e010c06110c070806 73
    0x14040e00409040a10903501451814004c0d0101940c440c20750141031000300003059154459110742d074840300d072601d00406642c203100c1d2400131000e801c8010130046425909a070204200003000e48600080400103a00e0b002a6190141c041d00c280542e10803405424a00e1109841e8110a119a1010388000c2c0414901400620740c5410a4010000742400c030315602c5141c0201461040e02e820058600c41c0c00c2c01504140b04403001c4281d021210010020315210304034010801032035102483ca014021030f9450b50790340c4180c0c088114000001070420106204440400d00c0c070a01510007940c40b0704004100c02d030229012401044808007107081d00910451840c03003013100e0b6004182d003a0600051002800090503800314080c1c6842a040d0160b65a0103010f0180c114100038000492034108000c0500c0340141c85050130750440c0b481203a040258640b41d00c14a40c041c104040080303540c0d001210218071030309001e40140e203410705040700129068020800e190740d00f01100d25041d21500800d403070301c10 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 79371548 1250 79370298 79370321
    0xc080610021c0c23030a02070807030c0e07091706060f0409020a090e0c0409050d021908090f0a08101d030405010e2403010609030507060318020409080c15060a09 71
    0x38814030074006034412002543d006115100740030311002c58031503c5013035440240c0480340b20f4201141080070907a041040f50000c1c181117004240d034910350703100d102d01d070b20391070140d16003000d80304000504107401a1407510040c07400f00c00345c4800086841510b5114035080c3d8116204901d503044644a40c5400d001c0c080c8026002040b010308903245c4032404004003075400e03100101d0301405130380300104e60721449000300086c0540042d04801c07804003c003e062100d607141c2d42d890b002c0107940d450080b81442041d1140101c091700c811002d1070f0307100c0000300106460341c0001580d12841c00e56a036552000d401c40304800300d0034074103002900c0704420550346a02642c021a400980e11041112040c0750821544200004410303800d450359010160b491203030f40c0b00b43c018501003290440200100141000000b000b001d031803078100801d0014450b4000441100781011b440b403600c0b800d4000a21603c10b0071214150301d11021180c92960701407041d000903404980c032034401e01c9030080c0012480e24038080d0002d140c4 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 79372798 1250 79371548 79371583
    0x30f1104140907030b0d050109060605011704030e19080a0b0c090d0807020d080c070e01080106030b1503100f0b0108060f0105160503071b1e0810020a02010f0c08061002 74
    0x2000c4092102d0307000028841c2d0300705515850102115113031801c6680403140120004101c07506103048c8039080d1001c560101b03040003d100380100750002003280726500103515203042c206011420000800c8aa0111001c0592800000e000194041c0000742c40400b40c0c41041c00411594a40803010741d01d014100b2516080003010316070f01c0000304a4002800382920003040d690324206162206030007038101103040000c6910010040c011220222041801001d1400c000e00134a8216940c4520040014009001d4810300038a014031903641070200701544086890b08001c0703803050303100d032001030883e4201860104003100081181c900700181802503035201a16141d240942c82c1442c801c21812581c401c0d03a490005102038000240c80b020b01180d56440f03200d2082d41c281c20f0402c1801e840c20040482145210b2009040122044c0884d100442e160300b0340c0010b8860180c0407040e805040b1880c3c00c0742180d4688a04400159007021085002e020b09407080c10011030041740590703650400d490b580d84d000 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 79374048 1250 79372798 79372829
    0x4080901030c0302040e130b0f09100e03190905040e01021e280201090209070309051b0a0305060a0f0b011b020405040804080a0f0b100303080109051510030f1104 71
    0x19400380c2c210454002032450014513042d50742c84420740303203102510002c0e1082913000421091090501503660005070030348503000c150403c460070b5a83e9103c5004145010790720b03184a11840c11040c425a200020481003071140300c414000010300007080b43c040e5620503440d002d5042d038240414070a4412801d10b403000c11041400b003d8600056070000ca1034103846200c00c000807450701000c0c0c4040c2c6458200380e00003040035200f92040242402c001804e05040621b08080341010031000258000c002800216600d0300000e207074080f4a400741039401c0030305203118240500a4419107a4402035452264010802140c5000c0004552001c80d9049001103500c4608884000d490300303134403898000e07104002c040d1526985045980c24a00c064001f920100300300c3c1c800e5414000100309142c1d002059a001010560456601421f944418000e200016560f40002025a5180300900d1f4141c0001013817801051051356000b0058000000415903140c02d1170180c2014140c41001c3d00c0c29242d2404100c07003107 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 79375298 1250 79374048 79374067
    0x70803010308090d0c0e09070b07020306060f0118290f03010b0a090909030f0908060105180a0612120f020c010f0e010c0b0c12010807050603070c0f08030c030702150408 74
    0x4030780011402e00e0740904140d2072880000e825040c1e4100401e0706d188085c49a03d003c0c44514200107055000c903600380c400f00441c83c01a540030450b503502c88001c80302240035014001c012945841e294020900c044008500821903880c800c2d05092550805483d041d031251640120800501407103421a800b1481807006001c1c0305038400140c101a012403030300c0c24420b80d0340da081e40c0c2524109507007500482d080e0b01407440280e9000c80c020f0054041940105415450300c4c020411a040c088640060301111a001c100b0740401900210010312455a101c958910a030402d1140c540401088101240c0900c0a424550b400848c8010502e1016140c00d0210090017400b510694214a507050401a00e141d100c00045c1021a04602034400e011203940c9500400745807840e8080107800c0007040303601c40c507000c010580e1900300f207a600c01c40034901841e801c0081e00c0c0c0308403c10b1441070020039110002c07003001700301c45101002d035102d021140d00300c030740e10f901c00da00ba8003001a0594015014000811100c6031 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 79376548 1250 79375298 79375313
    0x1903020904030c05031908060f01081501120e1f090f02120a0b0703020d0b0301050c030103060b06130303020c0906040b01020601051908010608030712020607050418020903030d0603050706050708030103 88
    0x41c014001e08004404040e00e03500c1c94210b9205000081004460b400a1460700764000ca1550341f0120031b8030032070340402e0000e0000e441d440300204640c9007800c4800c0e00b0300440e4030a04500503401111801480074042044110351140b000510200b1005140c00e6192481120b50103404a8150415410300c101403007602401070000f07912100302c0041c490b01c05400001010207820501ca0741181c0c3d030060b180c0303000d589250150350f0a400307e03030b110340e04040c00d00840d20909000c40303046a500c201c0004880c2203071004200f841c0200d03400c2c8203401c4500000001855004071702c4502c40007007207404418076a228001c010442d20855120760060b8010801030040b82001c030300c4038245030075042e42c1c200b0b0b1170754910030582501c0003038101980741c9c5c02c082003030300c204075034000241043d980500241490740b600c031340000e045000c0c51052525000c00200c00d44020040c590442d2200c00000e02900d0340c2c3d4400c410746102601140c4400c40b030354445d5000020b100d511840a40b60030f02ea000c2c23883c51860346580c03500361 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 79377798 1250 79376548 79376551
    0x150a030803060607020d0210020a050c01090803120a09020d0501050f0a050103051011040504090f0203010c020c090703020901090509010e041101050a1205061503070906020d0305160503150402030a0b0f19030209 92
    0xa82006c0c0d606140b80140c0e0b030b855003049148411398014886111103140481c1031401d4014050f061084404050015000200680740c6104802080c560030380d07503403100c0d10080d1001c400d011750000c10314082d40c41800410b410551007254135076154201ea8550485910403a84240f00250180d003002111580c1007001c1d0304003554000c421400c0320b091640398800601210a800341c12240d8602c07455804045003002e001d01b40c6002000d002400c207501502d80071980e50300b002402a000c2560008030394041d680101d46c094003405003d401c01c2415078654401a808100645040c0c400c441d1040c100c20320f40d0700c6841114039004d4541c7d614181e801034101c40c01d019180240a47c0da000d8608032088043d082c1c403002852042c08a80d8030950610302d0714078082d00300b500d515000800c040c103000030003003100300403c2587c120200a2a1582d0b503581c0f00d07a041a1441d4200c4a82a8070a00000078080c0c448200d40003035403035000c100d50740085c010004080011031040c400d80807954110b40707801040949012820513 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 79379048 1250 79377798 79377803
    0xb060d1104061211090f0c0f07080406211109060c070305010f0b01080109090f020d081207091403031c020a090308190e0925020c030312150a030803060607 68
    0x1001405040d00004050741d0460300a01c01010380032a002d0144a901d8203d000c0500f003d882d10b800604110b040c590540304c0040c9050805140083c00c103681141f0b01c0b08807a95250804202038031b40d52282001403595000800704641a40c4a2106111201e0181700301c101c0600c1194500d450059000140b03d0260010f40c0b19a8440c0600000000414028001c04448214885000914040b12000501484810307084542480e2401444900095100300051201070b01210080600b1800b440d10306800d1060b07017103d00300107610700144400035400c14500e5003517580300400703000d0154072202816504c2c000c24240b800f044250200002c91565030b50700822503d295490110100364994942c10300307075400104244c00d44445041010620795001d071100301da2581c21102d46c1d281d030601e207e0424900c1511002c108018040c540400391171402084000310003030024050725155030606021040511007102d0030802c0c1c1a05c50300480300340c41d10036114003c0e00c0e0311507c1c05003103440c1d0500340455600100801c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 79380298 1250 79379048 79379063
    0x7120b0102160807050a0b1801030b040207050a0b01030605151f02030c120309010b090c0d0e1606081806070c030302130306060801020a09080f030a08090307060204081e0a0b060d 78
    0x55242007015801602d0142c140d18004140342c40c42c0106200d1300382c020b0b512000f0400014007640c500a01001110320032600e0034640070a013200c159000034024451284000d0040c03107403020140401031505500d80c1201d000790001c211943d6500c5000d0300c040d0300ba00d01154030828054030420340c000b228114140312101f03407040368103041d01c140ba20740c504401100c4c0e500d4901e4001c41048001542401041e036592001e680c2074a076410f04400c01c2d80320b03010b403404c1e2141003501c50300c00342c40c00b520401400c40344000c0701c1001241d6955450001d0a820001d854841035511210315401e1035440c00170340d050103203080740e842104540498508030000d4105403000d0880349220700c2c00102040b55030140401519005000503621075409030090205480c2d03078804403490f00288050b2860000100549484400504043d00f040c0e03544514a4194031400c0c030000c202034070103d0301045016000803002d494140840c4500d0092003d0350b41c01d03907552346180f401014400034400103402da0800d610000c1103107118124 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 79381548 1250 79380298 79380313
    0xc010f0204080a110d020105040b0c0a06020a030e0114010806010312030b19080c010c150b040603081b150f0103030f0309140606030d0806030604030e011803120e01050307120b0102 79
    0x8040240d07031041d07100d02c0850b03110341101d00a00268120030010388034102e40012901e610b0351700203411030049202e02c1a44a42c04611000c090030188454580c450303101100f10347d01c4001c620041e004004c0254019030540c680701a86081c502403582030b03816100902c0c001c01d110ba03e1665100030060380d01001d103040580f01c0c3c2001d18130f03031a03264446042c25800b2042c1026182030004542c6450fa0f03035807080d41000326100107400407076540e55480625021147c008039420101001213070243c03c4d9684000d20f80c0d03000061400070002c6041c1d80d025048050710941b5080c01c4003151402c140a01030b50006520350204004200190040700001007a0f0405e08021842141d143c60f031010300a1032111048007908450308110503440c06201c03e60203620b0781d0501d8080350500c0c10101e50f035980c00074001804d001405a540a042e80250058490305545d0880034482c01d84910342501e498a1f443c0b0300c42d02107481c0021140540d030140040c0c0748191700f169211a40704400078a42c901809651803480c0c1540a0b400 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 79382798 1250 79381548 79381571
    0xa05040305012c1b040e030c03040306020405090f01060f030504021c0b07080a15030b150a140103060501110c0409170409150602010c0203031b0409020408060a0e210c01 74
    0x243c803c40e1400840030003007054079040300c604000f4150000408580040d0a16200c503030225080560b80d40f0b0070b840000344a801852224614490840030013058880890f0010400c075494000700b040d11010b45101c811511a1001c40070340c0c401c02e0041c00d02140c8107840b000c0e0034a10950100d0360041c0000e150903540e42c01d16801d90500b115424003601c1005040003040261604004600e40083c0c840c00100a810100b600b20300506001d800000c05040044020580b20a0264540c07007102c2e0006110715100c1d9521203807003d15041c100103807808203003400800240c07980140804180d21a0700e201a0402190120070007000b8000300e0811103914400002d900e18480c00c04015201510500300009820710309000c6c00c00c050005680410210381c100303904585106d90110a482d003081151282c1c0c25082d080310507041d8240075075000203414a1020400181c501c000040450113420468030800141110070140c94551703400c055909900a000b0400d110550320030b00061440110600001654080c3e04 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 79384048 1250 79382798 79382801
    0x30c05150a0b010306080c10030e0708030a020703030201050c0a0806130f0e0a0303050f0417160501140a0f0504050607110f0105010e06100f02070b0c031b1f02120c0a0504030501 78
    0x155116080030340d0b500a810100d5030103106903405420144000d0881c9820000003c42c0d410350203a004007019240e1a458811a100b003090f9000381c00d00304252074846050080c000d54980680c071040d4010b40c24103020600780c800324011110400c0302e941ea01c0003a03580701003d000e904002008a207240c4c82d9a4800941403090a129620071060780c04040c11310400d0508008041d10405494407102c010362100344400119460007800c611051850003d07203a0403081702282081644241c058401c1d400e21116894800b20440b01134401c4036030b107200308540030000c640002250011500201a0352040c2c01203100b041c01410b00042c1c15580d50304848014891608150a41c1c100713034400611701d45404144600791400a400c1e440070030051804484258000e0780095440c03c0c0752081c085a81e200194441d1b090905000300d071180003401c402c01c241760310038000032503980c00890340ba0801e0703070313211203805685d0780e000d00864808004404c1c0740026a1614017090803668043c21403030341032000c100000000120207 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 79385298 1250 79384048 79384051
    0xb0a050d0c0e041103160f09030516060305010e0402031b030c1c0303060501020303090604120e030a05070603051e0c09041808040e0604270201090f080c0f010804030804030c0515 78
    0x207035120403400b0104001d00040e202c0362200315000310010f10400215942c41e41e14030708001814540150690381c0c00000781c46804445d08084c3c020b009500b0ba9605007907185030801c003140e0055900300156030342c9003104001c403282640c0c000d40c15001980d035080c903900d8204914170108401026543b250b9401000112102c1c41544281030601141403180141501031060394002d1000380042d601c2c614000c4d0555844042c02000100208050301d00321051500c00e28074445186000b504403245000d0038141140c0c1d03000103110f040d000030704003000101102c060720050b0007009049104030b103c50300d4907084031110740c200e0400c850b00a9a40d20a109200307248650f01402180604402d50b40c0794288400302c04c15a070028a1940035a041010b240301c440040e00154000040f424564600c0e00060703c01280c01980035800483c0040341c07c0c10102d0707403103004203442030050001c8588400a100200040d035186200b210b0107004a4552000074010a010300ba8001d40b50b0b1140341540d40c081510b40d20841c14250 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 79386548 1250 79385298 79385321
    0x110d0204030c03060608121c0207080a031409070b0403031202070515010e07090e0610170108011509050103111c06020d0504020906030f030f0a0c020307060507050d080702070b0a050d 80
    0x212008000b8011603111760800313814000701500c810110803903151144d11681480b004c4500d6001440c1c1c5803818030b82e050b1042c00b5403000042c0d90300c00c0c00340c1004010b4030351888401c0c1042c1c0c074140425016040001d10004413040c101c2c05a0802d450b644058880c44400113a14035201e8003041540001442400b0700c00f8039001c4511801e8041d410030003000411500149960140b0410082c01e2042e9100c5545c00d6a020300b003145c001c0c1d040e0131515812181d650106103000c003d58115400807410715010f400c031481b0100301150f00d1200381c1d034407030020382524800c2c80040d2200c0030112211589042c80c0501c000c03000b10081310494424041d985420807a0b200c2c0169020ba16566414030046142c0f14040c0340d0044000c8004000c58030f01019010744920403040900511503002501100d2640078a00030100c01c0c0d001015145610b80d182000703000e5a205d19000c48050140b61a0070300303018000d104083c00b5004c00e0b030061285504003074a220f11540280d1854040c0131060001c0311043d41c2a02a5808684 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 79387798 1250 79386548 79386563
    0x3050105011b0f080a0c03020714130b030c041a0114031005210601060807030509030c1c0c02031203070201050c0406080105010e0d12020109150c0e06090a050d05030307081608060103110d020403 85
    0x6c517400c1c004e040c00700c00e810115504e43d440900e8449a13991262400354421100e9000814545c40000130b850050b200784c44c281c100d0300f4000b200100d4000b0842e640048a001e88404d4081c040c141c0510595100454404e044031b03181000c10702c054100110300c40c142003c0011008424403c581c4001c0c9000701c264006000206804100b015240e49801041e07084101784005508040d2000c0901d600c80c4441c051642d050321074806242c40c1540300c0d2142d02126030300541030741c12943d48242c90218581c03040310014095800d081c041882c481c0c40360304550450700345079201800c507401c0c0401140c0340368600d07480b60391000003800350002140000210f03509002d0f15800005001005241040c03d1704030074210010b9803440c1c0001c41b01025000b40b941003ca0004841041c1d80303084035000142c003440980c1055402c00d0702220340d507081210010045018440645840f50940e840c215282c1c241c1001c40b4110b4000b0303580c40b000c999594001d801c551000c070b1100891900b42004143c520703040b60480e900507104503 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 79389048 1250 79387798 79387817
    0x4020d050a08040f050f031c09050d0308011e0506030f0402030109080d0b0a06080c04060e12010c080109150528051e011101060e0112170406050d0c03050105011b0f080a 74
    0x110301303800c183e0000302002d0318030184045d0010006522400300c4134111030601011284000903500c10300c0301a0280200810080d14981542001400c0718024082d46c1c0684151394410780c8000c560308075040440314018489031940d500c991000d5052440544200e0b015900c072213040c0300144a220140c4004002d0280029450300000108a0300740c095511140501c4804418454412281380c00c036800d0722803d00381070040f42900c1001c980c00a40300c02c0003020740e5203840e076146481c0703a129070310a048a80d800810300025180e038144400c407003414810f8517840801c82003515100300c804c020920074420f103403418910041d070301c03008214909950061003110f8000343d01401015a040740e0001c803d80c4403d4001c100040c2445140d400704201030060300348014021025104004101c20360316100948250040d0700c43d03a450388050b1194003da08460310b0281000e4421810038401e00c030b280d04a43c0c05943d0000c2031041d0500300744030b2040034030081e17034009001c1c0e008001042c41400140f84032081aa200480c0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 79390298 1250 79389048 79389059
    0x50a05070e010810090e0337050f03040209130507080d02160302090c0f0717040f0504090f1b0902071103010c1e050315040504030c03140a1704020d050a0804 69
    0x49212004800e040c09211001d004e10030f02e1403503003002941e4507100e00280e0295514003007031540c000e40e012000180303a801203041d00b0b0101b84050b0a40c0181c890820240700c06414000d64a50007161840c002d180028000180585031290010390040c682c100070440c580d040307884150501e01c031600083c1036580142d00c1d0307858199041000001c4203071240c00c005181821030f0b0000d1105d030005440c50309102008140d80b115800d8003004c448021380d0080e100111403401c440039036030030382040c80358504a40510200040c5410940100708103640d010003910012011070703031514000c02c004202501b071a6819000820840030510007000d11038010902c007542e410301d1904040c01d442813101034404010100300105c00313580c141246a4481c8105080840e20399558140400044103400c1616600c28184400e000134150032442000250b8000d0341e4108c0031406403034070346041e8424030740c560000440c0c1c907414152040815050b40d41086c07008094458847e07450721040d180801100040d00c0c4032100060800c01c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 79391548 1250 79390298 79390307
    0xe07180b0f1002070f170a0b04060231060309240e0712061119030507020c041a031b0a0306020d02070c0e010806060a030b1504060305070803040609050301050c0712020a06050a0507 79
    0xd041e0b2444011786d80e28640d1107207860b036409140090649502d2404038040055035016038145400242e0441004a81c98400074040c1c5415450004100030079000410864070901400c25081d401c24405d00043e04017015105071000b40140040880e1b503559289002c401050042030002c002c54040341492400c4c505000302201c018a0b10000c54001c201303d03003036564249084000d546485810009400e55903044140d00f0b0011074504950302a103842c080868108da40048400c1d0340300240c040303c8100350086030b000118103c9401103644072000440c2000018581d400824482038071003400744c10030711b5035541c408900c4001e801c001c100c0700804005200400e400c01c100c03680040216503203085145140c607201904400a03102401d83c89080c44041c01c40d03110754210400031540001201c041c01d44d40d01005032a0341050040c0400507414403c00102494140165402410440b0680789851155a1402c09078201051048158040c55011401140ca5481a41d12803c0c0c8a200481d091500210052 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 79392798 1250 79391548 79391579
    0xa0602100b030120030709051005030403020c0d050c100909050106020303090f19061814100c080105030c040207150c050d0c0302031311030309040912030e07180b0f100207 75
    0x40c000d1389400400c14a5840c800c401c3c0c0308110b01e410669542c0d0f11919402ca503040c0c050307004240c111440f011112803282c0e0280c01540704a004c4d0f42a00e03c0d41d100c0000f080307241811640064800d6000d01036081c800c3c5030035041840085000d04102c81c480303649191000030764000342e0007800545c0001c030410031440d8050000c5005040389002606c0b10800494102101c40c08042c006490300c2c0ea00c0220000000c910142c0d101425003149034648562244102c0310343e9100c4101d110356a26080100b0710804c0c07405000d400c0d040c0d91000b03000d0b240942090301400004c1d000548155003880102c011401481e04a00c500da00e0890180c1c2c0301c03580d8020100c4607500b03641280011303a00701841041000310030070201e10b9440c440c0341d21034001d0f01081010030000f0b1840c01841c2c00d040d0300a1074000c90100704200301600070010300c051b80341403250400039600c2030b40b07850042c4541d2030b62036040b0b0340109004030990311071050b0600c0244120710480b8448003042c1a042c0320034610300540e00009041c400b0441124040 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 79394048 1250 79392798 79392821
    0x603020f06030f011a04030213050a0b030c030309270f070221091003022124011202090a030c17011109010509040504080d020309100501080303040308060f030a020a060210 75
    0x10720314100702400700b842400502c1011703402c030042ca02d00e01d003000c2960110b400a5030020400c003441d542c00f40140c002050207440c0c0b20700322490071034241518100800d801d00c210300d0080141d42480769900601074240109000038003544c1016003191880034901e005140100c0a1360b070001e07150310340b0560107864003850301c00301d80f030790495806681d454440200440d500140183d40502d104007070130105401174082d00c40030b440c0c0b040300300385481072403c00d2000721846051010580d5000880e20054a03900f00e0047e24441e00194600345107400300070a90b00140a01c0344050101041e0a50702e4a5004010010381c20003003560710714100641884509004840070150101007061800301b8080000e8014803652039040c0c09903448000050500010200b070b10135800c40b03603009541d207280c040303001c640341ca1000d030b00080c000f40f4141c0041000e09000094030700c2303079506454150076504c603041003002c894407407000030b5072610a40c003042d00180c44135082d9070000c12850f0020320368004103800d104141d0b1186580f9 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 79395298 1250 79394048 79394059
    0x216060c0912020d0f080c0a0203010b040c0f0528030c02060f0705030127050106030902090702030901050706020c03190e12060402030d0e010c08040f0302040f050f010303030f1d010603020f 83
    0x7030040c042140c1007000c07aa0f80c11240c49641e1311103460220070074801011302418118011448854003040404d9902459200f100204a00301001c3c0404c000c50b407100d0b81000c000341009131509541d0303000e1401024810041c100840c0c050001448624402011506c020000303078a504901b540150100229078100a540202c0101458003400042035800140b0401800b003800d40c0965101d0f2505041c1065202058038041c0019a12040080c0c060f107000d0004a015810800c0002c0f005131001c42500c00182d4140d440d2485c0403900d4480002a400554011400e80400c100c001301d0006e007120091a02d6010381c0300c1400003620351082040c0035002c2a40007205400100410006a03400b041c1d07074a19104d5410555242c3c2082c00049074a01001c24000f425000c0000d00881e500100c508000e048903c00c4505221000805000b01e00356041582c01c403a210503000c0c01880064080c0e003000400d501040740000d4001c04d801d200140e000d800c6100c400250f50b5808090042d400c01c524445000c40381a0751 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 79396548 1250 79395298 79395317
    0xc0915020a080d06120b100605030705031902040503160f0801090b0a0906240f09090201020319051c02040e0901021306030c050f030901050a0501050102010b010504060e060705010216060c 82
    0x240603458005080c0001c000d9200024010350030207565110138040e00030b454105800380c0c13203031034030710502001910103441032480c00e040007070310602c100c0c1100d01c9501d09941c1c441c01c54540481c2c1c5280b004520080c02d0840b41c0a000201d9191010804201c01c0a81b050709540205e181290800000b180ca4011a03200e90402c1020400300b07401108a03500300c02581c00001c0c5036082420040001d09404000d00c0b19460620201030860490841c03102c20340344050b00702561180d8038881e0708202d80340307224001c0c0982c00911800110707084079052900c410b201c5041c55031400000640f400c0000e505e5140d141d081c00c0d804102440030f022414202d991000b81c20700214074081a01461a0b01403010388103480800d52210b860b1440c0d14440ca040c0c80c00032602c580340c55280c0c1031070f40503240a03080c200d806164181c940000041c0c10741c0305000b4114030400c10b0310b50701c0c5803506061003225040300411149401078800c0044c580090824030081003c201c0a415000e1a403c9034944002600c1465496200b000321300034 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 79397798 1250 79396548 79396589
    0xa030b10051602031207051605011704081b0601090212100b04051e060307080601180e192406020613120c030c020405180c04020f031f0e0a0c09 63
    0x2220391401c102d40a030b00c0c0044091000a10f00f034101c20b03000d0b41c43d4801049500800c900000c11030210301c0540d8800c0c80c91a01e56004442d10b0718a4108203d949000c0008200408c1410009000340d071000c0d50741803103402c55840154589042a8024900d03181d0002c1c06007800340c602c80c070054000028051603260035191184507240390056005030351140084e03000c132281032100000d10320380c10080a03241e90345030f241540000d05520422600107010411114450030f0584030410444140c075000c03450180075071545465071085000c0b9101d000300566480201005420303030103030341d4034407000c1041481160a080940003800e040c0b01604241c0140301003801a0005042d01045003815546803800e00415845420304665161180303801940061420051180c591495581040b191a220080f540300d41c06102c00e000072440f0b44803900040b25401d01c00300e06000c040750400b01d2802c0301600c0095107517856960750602e0682c140e4030700401581d514a152440d640013b150720061100c09140661102201c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 79399048 1250 79397798 79397807
    0xe06030106030c050705121b030702090406020a0201060e04050f0706110d0c081213021005070b01140f090f0115030c0507061d070306020304060e070305070b03070c080a050a030b10 79
    0x180289000d068071030440f40c403607510030402d840b0b1a0b5000400c840ea40803900201c0203c55016940c11400000810a01045140000304580c0b0503580a484d408040e90380e901c41c180290041300b040404c43d52511030002d100c404003100b16000758011005480d525413504901d502e40161640064280840f01c1c0328100d50400200d48230f0720100003420103108801d0030746441d540c24402c6000341c915010101e01407010321202000c180e10820300c01d0300c078000110410501a40d01e8018444020000c600345001480031700c50561003228003000107810380c000b040c0d2480020302c4210045502c0d4034400000d070b00400000c4829076130300442210302d007010801d0840e0f403c801011485a10000b4000c1c0d41c40d0500e140f440311008002c0f03544290b8642c25111210b031a854003c003c0d40c41640e0070b40e5454101550082c0c4050007190081c01c883d8020010010309103800254906600014807400500010104078000701d0542d0004085001a5a80c1c60383da50000850207412142c11458040c0250040d22030f58503015040b = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 79400298 1250 79399048 79399051
    0x605010c0b07051e0a080702010b0d0807050f0604080d050c03061305100314070503010f0b090106120b04020a0c02100f021f020c030f071703040803130510050c0c0d0e0603 75
    0x1203030250701c0e66900400303554034442c240c48981e9614128002c04111200c20016000d4042140d40b908640d80324004224265500c0045481c0c3c800c043d407410100162480e030003812441d00c540260740041511400031402c040382103c0903118147c0000d6411b031404c001e8886d1650100e40d40a800b400c41c01d1013000f18407070f4010b1504031416a41e07501c0200b0540d02520180780021544240e2015140900c0300b24192503407001e10940b4081e600304440e03030320304281a0058a000d001c01805195a682c64400221000d07a04488454061961245881e1740741c0c4031743c0010503040070a82c40c1c915110016105101080c42c80313040180c204a40c05e140000c0007039005c1a9045404e41d404100044078240c80c001000034460042c007072450340300c0003414404411107a00034056150098000544200400340f01079510302c401c44006103040410000607890500122071402e026000b24215041502900d00c01412101c040e1400c540c00903011449240d616800c2101588049c042c2c0f409502d0b102c00013000c038807240070 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 79401548 1250 79400298 79400303
    0x1d06071b020d05060106120b03011e0c050403060614090f0403020a0605190501030b0106030b030d090506160b0f180120090d080a0309031b05100e010609061e090605010c 74
    0x34000110000e5680781c00c4000901600041920701c1c65940c1e0740082e00e4140c2d0000842c00082c1040041001e502c0c041c45a02010320b68036140e01d14000104120308003e141140c0b4060610005000110100f0740c1031180c14050207020404070990078143c0e080000c5110003d1030304158411110400c4002940491400d42950388440046000d440300c3e5000c5000c407254082c284000e610303190000003440302001d0480c1c100c9030182c07400c004503641c07a000d05440c5d0000540000c045442200c080140342030807001000030640c4841482c2402c2c040e940c1d0100c030514161200b0756401424410b0010309414034111031380c0100000c008004403c490501070030b200e1008840103c81503404284081651a0f000154001d250f0144841d135035440c0030000600103022040042e0001500282c0030160440c450881e00c40064010000340002502d0401001c003070054000d0020b00e075503d5210020b5200365500071680585241d120003002c2d00b11405200e03e413440c45520401c00181826410002642c00055540c403c54 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 79402798 1250 79401548 79401587
    0x4030c020d060e030c01140c0301080303010608060303090d03020c0306010501050306030712060f0903090312080c0f0a091e14190b1303020a0f0510031a0409030201060510031d0607 79
    0x940e40c200740005081e00c004078201d84c04002076034001482c06510010003142c0540d001d4509032111104542280802d0080c10f071264010401400168094903405600c07080050880e45881c0c00903000c110440c0e0200411009a4450950b102c000d15042c032560340034003020710f0aa401d40c901000002d0356029540310b182507105064401e00144001c50b0071055483c54006805d10a9581615006020400c2c034881a00c40a24503104103071003500c1000118000d4440326110781c00c04281c0c1c010f4164940c84241c0103020701400c3c2d58002021081281c0c444d00d0802c0d480035001900340b40c074140b848441c860003080c911881041c1210107840700c140d00d12400342c4d00140d405585401d000004213071220b100e42c002070f501012010001510440c85800c07070081c1c40d4150ba250010501c50380d0154162030b5000781818000b900482003140702e041a501c90000716010344004941596200c0116072070607140c081743c800090b25100e0011209408001030b45146074940028075440c503140a0080c840112032034200d090701c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 79404048 1250 79402798 79402819
    0x1524070203010f02040b030906010b0a12051504060312021e030f090a0f081c020a0b06060f0423180108060106140f1603090501020d1b0812010305010207020a050904030c02 75
    0x40d1400d502040b00c05400e190219a00c2d5205d20100c1b00c00c0e0400c03940c00d0300a12500e00003003030018503d402d49510031802d84529030080203038154000035101c0105402d40b00340e02c480c030b04082070b6920b001d4140154010001e44149900c081070003800d1441014144ea840d91041d5500c0c40d0440000003160045482501d105450308840710014049444552000c5019480343d4004503105201040c13004203c0c0c1442140b080e044400002030340c1b1400b81c481c0c0034100820801c00503407517041000081055070f084080c411b10740f81d04c80c40454045d20038505403404030128030a5030019410070021b4400c80c20b403064442c031419850802c8030b07a0f81d2181409a0002c0045007a000403840c980903043d102c4014070301c0411502c402604140c6100c0d00501401500080c1d129440011b1650003c01d00420400d00c5903501c0034a00341e280080310030407d010108031049082080880400c1002c04e46070380c0614820700015a90b004103004100755500c158200d00e1207401440305100000c2e40000551074065810384022103003 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 79405298 1250 79404048 79404053
    0x50606130303030c1b1a0c0d020409060e0c040315020702060409021617040b04060804020310050412080a05010b030402010c0203070e010b2205010503042315152407 72
    0x180168414003040819602001c410190541c0010b5124040741e070b2142c260a20002220244002c4108054041d11103080402001c40400c2c0036994011600105149040c4030319003008102d0b40241d000b0302034681c2c0e40405102c0640710400c1e42e5080340304400e00c07906103811600c41203450900c1043e42c0b09002d900007000000c41d02e800301903900601080348115120072900d002110749880f084411580e030a00540301d02921151701c0b06440a40e5580302c0814101400c2ca902658020005081607034503101c0e8082c886640d40050003182e100780e210700d1a013600740f4180d00c07001e0302c112400380c05442280e003010010f00044000c40d0581e58441d4091804a0541d41e550010900380700568000300c1e080b2110800104641440310000d050341028440c0410380500f03034a9200d140c0410030301a4038000f07041040441d000c02c2e0b118004901e40000984d00004031880c0c003013441d10f0725071a03000142d04140d00c0e40c00c10013602140e80100100f500c046d80d0194040300740400c4040001c01d0a40031010400300880c14000303 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 79406548 1250 79405298 79405309
    0x309060909040f020d080405090601030c0801120602070803010b071e1101080a14070305010609060201060308120405100f09030801080609060a020a090f031109060316030f03030b0904030e0406050607020d060506 92
    0x803e560003a0203290a41068141042650300034000e0a01440022005c100c5551207849020421016075035a5012a404c00101c0307400c07405501c0c020307603400783c081c0180000310f040c01004600a14281844560352800340ca801078058035a501c0c0311f41003100036524175000c40d460f0f401981c6586401d01e41001960340e41206000280702d06040050074084441c01c0100b81c0fa01580014180e807034544810b03c0050340d036401242a25414000140000b10a01034480d0702c40c6180e82c40c50b00240700e141a50b54220b100420304085a51340c0070400c2040351509126001c0c513402c50311450241100d900946000d141c400a03c1c4e640705c402402c031031140d82c2d000664244251040b0307a0000034210070710000701d520744d0742c0c1000100d102e004c001251103014100042081ca01c0c001a18242c2c0e408002d403280c2440d407454413a90309040b24003000b038080c0354546030480c81603560702c55120700c241c1c1b00c0d48800380800158130034070045481c1074000318060710003044217801503030703690b504880c1403540180e0101e41d035a101d50101740c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 79407798 1250 79406548 79406573
    0x506040f1a0d0f050619030809040b15030702030d0b0f0102031e040801060602150a020306090103030c0512040e1602010608100513051e010b01020309010f0c0f08030112050c03030906090904 83
    0xa2a451a2000074080d00c0c1da01e80101d80101000c9998620744641003090f80000c0700c00b4032005100380c48c00c200b0190300341025007184500ba04005c003800c40d80f0b00701c0b8052500076402150035000682002070381240440d41c0d407040c403207410400d07118042403060b4207002035503a1048043c003108400401c0d0405504090b1503003203030041e004800c000d1240a03501c0c00c000c0d54404070743c18131450911032800041d0f06400700e80b083d07034230402000700f40c0748440e403031500d060341c042a1300b40301990300b0702039500705401002d241c000400091840107071042d11803502603c880100a4201070790011039041c03400401c0ba0b02c0c00020501c03415100701c58002a07a445085100c010840c540f50700418a000d0000c05140518a102030075400b41c0ba628000c1c0140b49203c1d004a88904c41d407207103a408070301c0066003000458454022030f40558801c03210101001002d847e14411900240c8c0135514420801c0000e1003004000d00c0000c0e04a04164000c504041280d8001a5503000f01c07081580a0090200010b0174400c20b1180c84 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 79409048 1250 79407798 79407817
    0x705180105031302040f060e060607051f0e030f0d0e060f0c090d0b040b0f0a06120609030516050309040b04140411010203071203061403060601020703171e030601090506040f1a 77
    0x10032a0881090b075006c0540518814500002241e8002841d2400d016045609840d8000050009080036850a24800e1110700c034a54030695104040e10359100300b003000708101d1184c2e458850701d41088508040c240c824002880c4100d030001410f00c448418100c400302e8104070381c2d00545445007410702c00300b03007407441c01d11000d461804070101303102c18000e00e084414020882d0f134030400307826904c46c0c1d403a00c00d5070144e11880e0b51074a00908600e000c0b441036130042d5542c910078588246004161401c10b03800704c401460544d02500f00080550f0300c3c1c0742600c15058032804c00d880a2007100c2192034010844200140040c003244502c60f902d408a80c030a0003240c1c0c900c0e501051000f280195160000c0c02008540100026035041d0031228a940ca40040d50034480c01c016802011050708541e501d61000400400918404205010254009001030000c06012001044041c0c0b6071510200040c4030010b6640220b0080008000a1164040d5110141b007a102024551400c0d0929010089e80038490394189 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 79410298 1250 79409048 79409051
    0x10b150c06012c0c0901080c03070203030609131410050703060e0a090f0203030a09081501030b0402010f1b080d0c110a0305090f06041403010b040b032a030a0309080105070518010503130204 83
    0x200404c403080b51020380000802a078803040c07199106101900103106c281c64030400350780b092001411610b44020030540c0007400e151008410691030b5034002d100e0180031070002c2141c000d546120020181072007000d45c41062841c041c0102c520303011068440c0d100141200c00802d855581c010305000000c0c08804205a02a0031a5540c041e0044c0040c158000c5003d0200d5601580203d034034155201035500317051300d82250014101d0749a650054a4000340000c00009001107800c0440b1600c0d0040c0c079042145025a806681e58184000c5070411100501d040300c007804901c0c8100c150180300020020300315036050078281d644ac1032650016040c0c50040442a034085800100440c1150520614a040c0d4200f50000d0001280000402080d681424140c80e0541d00404e440307508004413110400c0006403170100c2d9507014034401d010a060115076001540820f41c1c48404010781c980900c12290301c40c4180c41e04134140701d50a041071030550f80720150641001b0011010450380d2450364030b41807146500500 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 79411548 1250 79410298 79410301
    0x30115061b0206120f10050f10050d0603080406110709050408030403052104110f040605060d09030302070b04050c03070b03040b0f07020123060a0f050603010b2208010b150c06012c 79
    0x485c10502e0411580b546001080b10000905402d010381000c0f40808010701402c05003840c110300312815005500c55005c460345401001004c1b80d41000244050704255650081c10b1700c25100c510302d003a80540c0142c007040d29203020071021078409030692741c111354545040da940f91607a40d003c0c81003d02030803907030410207500002d000c00c101e4a00390003110301d2400c0c0d44a204c000c0e910410007044075500c0c850035421020801503076564051950101101074440e050060512009031203642c18520101c40440da00e40c44003070b40003e189000c10817440184094209245185440d0303070781e0644494041c008000d0000c0c0c040118005c00c0c000c0d0071684503411341400c807040c8100324544443c0c2c8403100f030750850b008001000d000324448200c10050000d403500034040038507592901010300d000d903000550342c4401e40c004001003101c11035000b01d070f00000d161403400840c03103600020821007000148242e00308454401c1196180264002ca400d038115000d01e01685a80c80820003000070344008110740c510450360707080 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 79412798 1250 79411548 79411561
    0x30618130204110a091427040209010e0103050d050714061906050616020f040b060708030703110901080a050402031f1505010302070f08130509010603020702030115061b020612 77
    0x4204100041c001c42d001c1c0b140d9410044154194421003000e1400180076002c28091407441e28001a0799500281950800a903136400002580480b100c8880c0540500000d0000b9458800c5040d400350118002260195166075111656021780290910902c800400d400f414803a0140001c40c00c1c0c00c0e5031080d40c00a00d40b403424040405201e000402c00146450004220b60500e08103503280c4601c070705010070101005400b00440d10a01c4100300e40d10540307410600515440b41c5001e03011081c8104111a02ca0a182202a0a9400c00c80150150050074007134210683c2c0c0c05840150044112900041c05032038500100b41408001d001000c17211510411004800007180d014422262418514810407511800114182d108148019050007002201a008602c02c20010440103968804c001212030f80c030800f081c200c01091b40141c001c20341c00b107560030660500303004040920f81e00141c141c0c99107062040160403a90707a08410161048078a00450464540108640301240020403455562500340c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 79414048 1250 79412798 79412821
    0x140901091416060507140d120b0103050403080a0f0603080f0a030b0607050a030f0c0501060f08061308040603180203061006110a0b060d02010201021902010f06080c03070b030618 78
    0x508222000030000810075010030001c0b4004400c0ca0140408440e400e1078002c080750a03400c8098103170f5500500400b81c42e410401080350384082000c80d29448448c2481409140c2105d01015000e0705250130101008000380d0310070482584440c801c000010030800210428005140c036800003000c01d880059040038131075103003028048940705030343c1c107020381c010b040b0500c9042d005000005026030300201f000350009016542942c0081d0891800e05124401c0d512001d0950b00c0f968450384034481500301c10301001c0d10038005a5409501c0140c8040c109060317613107446d8544140d11428080580e105024100c01991000078140560000c0488280d1704140720211408413691240c0e0340420031100069901184c08984211615003081103840e05075900300c02d0005042100204a0440d542088201e50350341c504030b00001e6003000c0b60f0000440c6c0061002c1c410456806401220169001103103580c0566400102d2000703541005000e992a600d070a00826081d8100c80d82c10500f8041c25000c009420104 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 79415298 1250 79414048 79414061
    0x20a180303031b020f030a0c05190c03060b0301020a1d0a030b090606030601120312050601050f0307020c100c080d0209041b050d1505030d081b0a23030622140901 71
    0x5010a08007628403c5050f85d840c5404800c03000c8540082c0004072000e4000d206c0700c64584c0c081c03025148405481010030080322901e040441d15050380c0701c000d0050008a00c52a8039180d13081d80214903001c2800400303807064108418891242d000c11070b1009450f00d400b002c000c021036004950009030b050034500e440c0c40d010103c034002d0091050394000280700011580c940003480c0c250b02c81c4801880c2c102250320180c08000c0c40181400400c0250742c503045450b00013144544d18507400742c40852910030810400c2c250002c454000c00c44160b12640102e4480412501c0510300d01c08016039407410600032030040c094540340c2a80308a505601c810095401000411065040d40c2d0100042c1080d050050554a0940a03442e019800342881c2032205015415040d0440e07041d040c014054042d00031a045140c3c00800010002001c070071200952196282e010501c400300800c10501314a4400082a400d040c03100040119a8001943c440214400da001021008050301c410b4414540792036194040c111 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 79416548 1250 79415298 79415321
    0x5180f01090210030204060c080901020111070b0906010605090312030910020403081305010810030305030a1e090b010b030106020624030a03081503070608010605072102070e18030706020a18030303 86
    0xc0c0f034500354a80a2003442100c06070b41c0035807503071024401c00da00c0c0c42e4460303000720003554159940c034070f60035000b0000d42001d0714106100c3c02c5240d40a180080390141007603010b0344001e0500405100034032142e900072540700c40400701c6c401156280e58650620300d14158004071680b01c5d5920014000c014400c040c0010940f003040c1080c08150700c1c0c1e0f02c40045a0404c02100e0115125800718001c2c80042e200314000e40d001a500003003c40c40f40d100e64040524001807110921250b1f0f9105030719003c020b21044c001c0d00404d4000d80c128103540c90300002a480e00700041041820343e1000484a0003a402c50504214041c800303000c42d161400c242c58007a00303034502512400000402d4000c10116884c00044501c01e9039a103640c1c1e05d200e41d2030140292056007015404456001801c084401d0640e030078890b08920308003a0f030090200d0b901d040805070f17020001500240144182e2011080c45150010850b107603183e100c000180d44086012084072400c840c018441c40707032452454000180342d859080700e04900c0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 79417798 1250 79416548 79416559
    0x220b0408030c0d08060f30070603140c0405090405031306090906090b010c0809010c0203061303080606030f06100302041e030318030302060402090426031f0e060405180f010902 77
    0x1184030101303079000d410456503d584440e032402100150304100001440c02d15190001e0584031802180b2540d41c42d81074203c0807016400341600308061503041c0201c100072003800000800c20700741590303d0802da104034003885000b2a20040810b040107000c104840c0d0750001c0c0740c107152a954071035100800d0803110b441007a425a0a0117408210301c0d215214104003070704143c4800014108030380e2014400d420400640d4188501b003c1d0754400751b203040c0f050500c135126642d03c01c55203070a68a0007078010300380901110b000302d00034070030040c840d000391801039009401103c504e16040c0310b500044001c0d01c1190003d444103601c0040c03000d000c1d042007403441e058038829140c503c250200d404800c01150000d10024005911074000b080140c200843c003e504a4082c85180d54080c00303d60041c146082c18803820300000000104009a000401c0240e041c000c0748840e0040025180008454003410041d0841c0c0c404c5545a0100f1040044400a1001089030a050310000d0f64502c0000780207014031901a0b003c2d2 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 79419048 1250 79417798 79417813
    0x6030203071502030d0506030c1302070b070801050d1707021f08070f02030a111c0c11040c080103020f0d0b0702100f020a080112030c0203070f081e03220b0408030c 72
    0x4800d640041c402c031078640e802541044074414845010304030290440381c26005120203040e003502c43c2c188050400100c8180580d4a04031413400d2085858001c1c402d03403c00c4074030001400190b5905051100040d049692150300c10705000b1066054417511000039440141c1c03020440c80c1401c0404800101c2d2400c3c0c44030ba0896550038005c1c2c64a444c2c0d03001c1c0c000141c0082050b034080c00e00490103019512001e808a0b0300b511075942d0558078110110b02441701040508280504201081d4840c1c40c440a007a00c043c01019900000502050350600001388130700e101590024007615407406c0061f0451700103040a2030303410621000f03912014140015401142046032140c9822000c2c0200c5660307071560755921501e40e181042a19207540400c0b411810003010b0290315026070360400001c4050040b400d403010080307241045291400548800700012091800b540c1e007036100010007602ca1802404030901044005060003032120b03115030704402e150b1340d000b00c0d01142c0d5072070000260901d6030100e0b040300c400 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 79420298 1250 79419048 79419059
    0x90c06020c040e0316030504090e1f0e07090c0507150518030c0a030c14010203010e180a03020c010302180a090207030306050111120708091c020109121112070b0d0603020307 76
    0x141d07200032003c00807542c0100021400601103140d0b9089040c000c0c5001c600380b60310b5240d05030503075400c140b0600b4240e1020000400001d0340c6210107100f01900c1408000c1214410b01658503684c0b184900314400d95251003900b11b1900803000c9884842d440000c40c1e40800303444240c000100303001d035030941c1881403e003085425614000b04503000c10030840001d1213600080c1c5e404589080b070703004c4210344c0e150000d121444220000d002440c0070340803400024070f492400c400700a1319132041402d4000691f106901e4140825008120719003590400e10f009603035109280b841c02c0c0603500700c403a105e0b002491031000160b012800d83c09071012510031354041c00025922001111080001480c9050f160868225000e01c00f0340340009000551140d182d003410700600b6400143c0c06070309054010603800014061408643e4003000d9907016156550441500d400e1680326504a1003101c2503650140b00d00501c02115803404214001c028a00d800103d0f0340c035407a00480001a10f900e200c1203000b441000f1011a9 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 79421548 1250 79420298 79420301
    0x604260d05070b04020f010c0206070f12050a050d05071107030f021809030a030f14010803070b010b030c0f0903190804150801060e060901170907061202030105030706120f090c06020c04 81
    0x8095810004980f40c1e42c42e19001c2124001965160905002040c000080103880303000280404034010318003d0300d601c11900701040040e0465100b13004000040041c800c0e960b812100303440d0000c1110900180ca6940d01c08241c411040d011107180e002d11a40400204020240c0003c0c042e8510076525011010003a1103160302c0100c0940345100583c00600c18001941d100750300880c1d07507482078400403c940d045802c020450007400c0c0c01210f255000024100280311400d0000307801411000145c1f03141d850300c1500c10707800380a41c4102e0f0b000c45000003a03444159404220341070b0a214486003804070354105162031445603002d0b22540f50103105060311705c507440380261951070480f40b01303417200c0b100380c07070400c00700304540e4132000c60281484822600a030030883c080c21280d00ca1000d02009004003811320502034009002601071402aa004100601c86c90700c0c0070074200b003192860b050210a400c403810411020381140c08680040c2c0d03180111640610200907913210445045400762002c40b03082109100 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 79422798 1250 79421548 79421557
    0x1020f010c05070201120b060f0702031504050c220515100c020604050112021b0c0103150f0b0a0912030c020a0602060f040b0c0706020c01020403020307050d200604260d05 75
    0x128409120000c09175008110028292070301d000c0001d0740c03a1004002602e280c10041e07180403c08401300e800003c6040800c0141c082801c0503613007010720700e00769807003d03580c030040d07a0414040e1103013165903040039425100014443c42d040c80203110360301c0c04400040c1c200c00c2c0e440100d48100e03059105441040d000700e0b400a44540c010b40b003585030a0404005541d25a892020f80c20711903400c00105070284400301d8444020700385500900042c1141c0ca00050544041c0c201c424081c07082044100040c410140004d811204556012a15988502c1007540c0152403030703124001c1040703085940001c25074442c0800c20002c0c803c441e40301c000c0d500ca00003240c2d128002c480d00e4244100030808a000b154250580c01d901402c040140e601e45242669070b1016604810000703951743c2e40105040c02146030501411014000c01d8441e500c170148540c45180070048000b00500d04c80d844400000c40350f0300ca075021500541524001801340201c2104801401c00c041d688560315800f0b4141c805084502c80e80846 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 79424048 1250 79422798 79422821
    0x807080105010f09080303100501030e012a0e0a06050d050a02040608070e030304050a0e15030c01050a030c1404030b16080105031015050d080408010b030a020a09090f020405090c01020f01 82
    0x14001a800d200040d07903c1e0420704002d9003889040500000c0420040000394071840002500c00c2d980341c075040c009001d8940361a04140e90f641402003020000185010b119410b80d6a0400d00d480d00758503980a840109040307103001c0d042681b0060215616030408002e1600d9658880100030710340d5007418203c09c0f03000c2ca000b1301c40012041030219101038824010f250028800906403490a681c40700040c0c281600d0b540500c0340752a54100b041a10410598401e0750b00500340c015003820307402400020464800d122108003815940c000303400d6903920500021100d8080c0d010910782d107644070700f00111841310440d01d07078075140401042c40e020305100e9420035040355030150045c14004c03146200f40f009000e03a050403022051050380c0008603503580180d0b00810a0140041315602d80c01c020103a400e45103028100d43c042e900c52565140143ca031071030300e50102c9002c0c100000f0040f04918220103140342c0000b01170f601c142080f05215044502007141c2140280136006c03100a001e0019846091f079035000b0707a0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 79425298 1250 79424048 79424057
    0x604050d08030a06180608010e0705090f040c05030607110d091a0a1e0302070302070806151c050d020303060103060e0112030302031003060e030901030c0c0b060f0f030f0d08070807 79
    0x103500070700699008084410701140d42511082c254a442d40145c0d03020b001d01d5220b1784200000d07502840303454807001180c009400e0312030414003c140361080c050000000c1c030300c0303580c005010320090700749942c0608001820f484a030b003418074000740900e241c0703102d04a0a00407107020480c2c1320b02400a00003122070720200801000340d03403030301080c8940054100c035061145000321001146041d0086e541c0550311501d006840d00c41d14100285000b005400034111540050107104c0ba024021404030001c1c074084403000e00c2c042c0c007142131100b00c02e07100307800030410302c610248a020f440d004005180300702d41c280e0b404c00842c1e69400780204540300a10515641421901d842804284070f900290307400f080d01071100904940e240d031600101c0b0020005102240c00120304800705690500804c0c0412440b031814006000080d181c0d102d00ca41c000e8040392150707081c8003c02405071104840e003200740c03c0c000c0c203940b002107007103101a449081c01c07440340c00021071100000f02864000d442c40ca009020300e0341c8 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 79426548 1250 79425298 79425319
    0xe06030f01170f0106030c06080907140d060f09060f0c05040315051003020901030302070603050c030402030c0111011508060402120109080703080c0403120302090102060a0608030a0c0804080a03050711060405 91
    0x240b4420b1034a5804002c20203000302038030700103a54401d001e6040258424000380000c1490034500030103104c4080d003d11400d4021030000c11002035550000700c1c40c00c004440c00112044207103045001010003482400e6034038101105c07142400b10a0384400b80512243d8020303c4042244401120300e0322071800000d201d40c14242c2c01c0025592a9071040d5801044001e10240b45a2039800288107124268011401a40041400c0c0311865150003440e8115801d01001411800c203503000903120070441c42c0541c10040c00260b20b118108094200250444d861141000d0642c0c1b54600035482d001d086030140e0066103010360050210707005100740d559040d005100c150a08043c0c6c0c2e03046420700c0703001c2c200030813403a01840040040380540c5512402c1c83c03000e450041c0e1701e0300300d8400a401d00e07030b0080441c140c0e1898001d042024000200855942050b6480c2000c509040c0d46481141c0d03000380e4010310118070400054400705074021b0000c0030100d0040703200080b0085098204441c910681c0101c42d0810440318 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 79427798 1250 79426548 79426559
    0x1090906120611191d060f0706060807030c051e100201090203070506070b060613030512090102010507020706080a021b100b15090a060302090105370c0c0b0a021207030903030e06030f01 81
    0x541c2d159041c1425000c3d000a0b4a0350300c0014a0307030b00140d58180c540a00048c4032030801041d071060500030980302d03000e40205461500c95a071482c64900c185809400da5011101501a254144201c3c65a0060040c601001c45101c000c1c000d00040780224080c1c45401c00100f124a005801d4495040e0300091000b40c42c4d8400080c0686034000030307402401d98a581d000800015414849104400207018007541c4400701074000a081d40c4010302040195040820103000c0203501100b69a803103600560050303590b444486001d10140202c10740c1d0301c4140a0404407541c010300b075800981d410801125500000c0d40d0030740b103840e410b02c20400c620382d000c04200400c00c081c0e0b00070340180500550506000d41450035030a04c0c501c901c0c124102030004000c0d4030900051000c41d103024401201407914140703d000030740360750304041810740c0d0140061140d004220101c40d184200400310080140000c020780ba12803a1130041c5c800203c5000407800f00760355841000580c1440006e8911903200301c8003182d41c0380d1926 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 79429048 1250 79427798 79427807
    0x10806130615260a0914030313210c0206030601020a050303010f17070f1401120f0e0601060509031015031406150103020a02060f100b07030806030d08010303020d0503060109090612061119 82
    0x4450440361000c04041c46c201c10401840510721801c202c0490740c40f090060319000c0c004034240000c01c590400101a80d095541c1d0003801c550a050b030685100d40d4079290500107034680800541c00814030300c000000401c410040400d24000c0b59440200c078205d030f15451612946a010b02e0103544592258950100000c00c14004052a401018140041c1c4000b1810880d0250341d40c041303003200c115071074560065900400300640c03070041800c5e240660030014403200003a114107030340c04900071240c0c031181d030b2852038241030b15042d0045034421b070084060929904855142d074401c40340380b2445044209040b400c0c1d4000e000702d402d407902a40c040c00e01641d440060010284010b00340d030550b042000004100e810140000300f207814020349440c003140c540402010320300308008419904000c104401040003980010700c62802d40340030704005480f03503100001221040341c80c0d4880010181000000100b0800159201510a000362411700c0140c0b120184608d82d4400e555500490806004c41d10303540a216 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 79430298 1250 79429048 79429061
    0x20010b031c140a020307020109080c0a05040f0e0a0b040b06091b0307020a0204020c0a0c290a180303081603110307050903070302100203091906020309010806130615260a 74
    0x560801682c0c0d401d0450001000350410809100035900c00940c4800b55a00300c0007013401010075400900941c0884008035412480d50311030903000750744400c0081414049600003002c2c05251a00b103c020403498180611302000c1900c1c2501c01c1c509181c04035180d8200760003800d10030036600e0a561800160804400655400181410118041c80c44903134010703562400149642d9180c80018882c1240074140900700f5041c56104401e6a407880c88200300f200300d8500010300d5004481402612200060001c0d2100220910103465005400d50044201a0055001350140400340c83c2e0b0484100c108100740c0446680714150203000c0024000203001d28414401804a0740001d0195041942c2c0d96004c40c284000880b5044096000800c120003d804c2c2002c04c40740c41700b0280c40b070300c1d1a1854203030065100d1080c01200c0b0304121070f100c0004c81e00e454042d01d00c2d05400740300c0030401606907644120b21456070390f80c03920300002d07039903c4180d8110044d1505461500780e510140c00d000751a1003200c031000703015 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 79431548 1250 79430298 79430353
    0x108181609020a1d0307090c1205010e07030e01021204120e0603090303010816030c06030c09030b090a02010809160e060111070e01030c050409030512061f20010b03 72
    0xc054510040c0c03a0a22a050000c10500304003580b9080b01e01d8000d02043c126811500005070000c1e048051990001124012501c001900003040404090119540c038082c4408a40041c00d00c1b000159508182c0380545c420462a07408200b0b120350440340c18241c2c424410786c000c00100000c00720780400d16210303805030040103504001c000304444c407001c140701d60412900d40340e4176003000c401009400740501903010000c400100b201c003194290b5451000303504480c0900020181d4900075401f1442c0a40c40c04400b41d030300088603104619103100050303901d4180c500e0880c001990703140803911015000a010380702c03d005409980910341040f81c01e068900000740424100904c01710700f01c0f1241d000780b002002070890754901c40b00c0c56040d8100400100269071169004078a000d1408002c264800250f81d141d407490713001143c081d00d81800164560f0215405003001002c4080326040060b040310041141c0d410b030310080c0c0351065505103200d003280d001074080c542507040140722180240c003aa40d002c50001 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 79432798 1250 79431548 79431553
    0x3110607052109030c010e16080606010206010312020109022101060605090d020609040f0203040b1008031e071103030c011d010c0e09040c03060603080a1206050307090e070b030c031e0105010818 85
    0x2050b5403140b5007500c1c00070700c40202031b4105230781030342204200d03070141c60250540500624040c10700344e000035522501403101030440c10a840707083d00d200cad1013034000380d060075001030444550303038201228031200398a8601161030350341c81e1580000e00030b400b4100f41d550081009122002c400000e800344040d60b88000941c640c080d60300c0084041c110700301c1c40618012030041c481154540f802110344520a0f5442e0407009041e8024010940d8010110224900580d1141c010a4032064a032402c40c0781d075003010403460350502001c038150080d003805500c030100c2e000e042042403001c0141004030508031242c2c0b410800006404c00200707129410711f40340e403541240c0b0560325810015900d8031070340219005500112460240081d190044d25480420702c000000030941c100040ba19150009a91b40304a00c250160192503119002c01030b8401e0103030100500b400b001544e624070740180c031200b56034801c4852100d01c0b10090782162010082a10329410703a403040c2c6503800552105040044402c500801aa0551 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 79434048 1250 79432798 79432807
    0x601020615150f1308072102010e0f0a0e060109060c150504150203010b0a110105070f0828050412050307050a0806060d0c0206070201050a0b09010b070614040311060705210903 77
    0x6000c060001d03c280341c12500503c10382420030003502e040080c2e03a806101407511a80005941000e80201c0c0d645103682401c0c96856803944201182501e4020390bd0305a11250070000020500e4038041c01d0fa110f00c900f6a42c001005441d0a801c1d0f0b5400c17946e64002c0c08400020000001040080d405560000e0103602035065090390303203040c1f405036403090704441b814120214a1090391600f1a0442111100c02d20080c0f185240c915030017045000318126201c03c00941c0008a80603200b9441c095a48803201000300c00c1040c01e910000003d8001075400b240c0c0400c0000b0b201503000c0c8a281524020029682c440386810741c5140c0407112000003400c0b41c1d52202007008040c01001c500d200b11440725040e40c0203007100340b40240d40a421151b0041882000c5410a030307a156a6541c0d03441c285054400c6020300744c0d295501030800320000c0c490201075003022250b0070148400e06400c03605c4800c0d91009042183e0007551500c500711414010901340e403200c500070030220000c600701114070f03d50081103082281d080 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 79435298 1250 79434048 79434067
    0xb0d032a14160b0f030609070e0301020412020a0b070b0a0b0406090f2016020d050708060c040305240402060715021305091005012c0603100608060102061515 69
    0x100080d5680014650b440112010a080c0301004000010010078260505184404108912078031000380b44620510b8960b001411280c091010750101c004094000c40d00c0d1901c404101042c1d5490301c0080e071140002c2c141c0000c003091500d04880038590300290000301e54070313100110300c054112315802c2c0340e0081c0c0750341c0c0c081040d92040c1318211a08410f80300100704e4440510b154940740618030030750a01100b04002100605680d10100c503800d47e8103460b01d40d101d5a981c2003c0341030241c160441041c9010312028030007243d0102020304203480c0034106982600c0c80b41410701d1303d14580307803501d024026003440014003d85800c4024118082c000d40c0b00c15004c00c001c40c800800c81c0c1c000c40701074841c03941c1880e0a0165080c11980d881d4400714030342c0c009120070b0500c00040c201070400102c1101c3c4880c101104a6026240062000101070140a103926400c00480305002d0b51047d00508000403080380c00901d49610002e0600e01441c1e030b5008800300b8652410074800e0012038952100d01c1c000040100009 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 79436548 1250 79435298 79435313
    0x11b1e03030b091005030607051303140a030f0315120311010f051006050304050c120f0307030e04050a1b050a09050a030f060b0901230a0e04050c040b0d032a 69
    0x9000e20903580040c01c0c044903410004501da02410050310660074034000c0c00750f614006500d64000300c2e1820401e0b2208811a41c520034181641c0008007503c03e030462480b402c00c00064040d080c0c0c5d119840d100d04075100c4000c02c03400c035030315040a000a06805c51081110071074070810300b085580285000320002c5680841542540d15152100700c0e415662000c00206400210500009d0a52841d016140d400c250310b0305a80c69058034a11351041442c903401e541c103007108201c45000716034a18256a02c50310303103080140001c0c4030503212500031410140019400101e9119010a14a00780550140343d5005041100c1179040340c1424000e011030900301180d01d564200700d039002184558516842e4122074540481540c40c0140114050060320006001d0541900110054035003c0c0d5001e100622a00c000228240c1c00c580c0a002d1010112050105002c004918010030b01c0094405005641403070091244007041000044c0c00100340c2c640401c0400035020340b0024840b4000c80a0888840d191034001 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 79437798 1250 79436548 79436603
    0x4060902120a020109120302060a020c070f060503060a0f0815041415040203010c09050a06050c0c090406360605090109020a0b071b0b0702090403090f181a011b 70
    0x28407648041c044404560348600505d001c0d2020003050310022110f039134041d5450702d000c1c4c021254182c022504003441c4200304410802008000210035106070f42d0b0b00041d000d607000b0784046000d5024224080382141d0400111700c120f4800c1d6004100c1c11404040d0410101d0307001c0c10131664420280002440900304210351030300580d00042403911414a44100350856030855540b00074051105400c10460365804a004111101428859074503040300c08101e0030aa007000f486680310f400320041c0400e2100690140034040c40c80412210341c55198120348c070390ba80415000d40f81d400d1401007000009503294020075000040702d400410040e010303074002060f11030607400c41c1c0b40d085000f10780c01040c002083c0c800b41000c5034030201c0610f00b03410000208224403a002019000b140010301103410944600420340081290200e951480b80c0c644007510031f40c001c8403000384440e0b418822005045000c0c00001d00d441cbe90142c603114988401030a4000344031208543c1583c912403040c8055040710741c402c1c00f15 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 79439048 1250 79437798 79437829
    0x4140d02031b040b040603020114030403171915030809060d0b060403050c09070305010503030a21060b0a03060506030c090409032307020103060e0609010611070f080f0c150706020304060902 83
    0x31061510142c05000032154010300091180b0300f0b000041000d0b0740c03c130b56030304610311108010960301e50307543c00d0075035030b00039084a8021145420010068071484081c800409000d6000e01400113201e0101d4500403130700140800381c1422030411000e82c19180c107000400000016400100d03103403003c0e500240c40e80d0429441510560080c0c004050240351440faa10781c40026802c00b04141e50501002c03d03660700455005005000c0e0b2589044040000307220007620805c0d43d94020702025403194601c4202d45c10105081d40400d05202c0c0200d02031608a00f40c900c9004440d40b034a0600d0354903010003010348100b007000d40038048004c4003403590405070303100000003103141140c140d40e84d1070f03505c00182181c0c00c0741c2c00341312191900f00a1218503518440800c1c11a41945440c4403d2540b2400140c20080e044e0300100007210a14000030301c0b00f00110b160342000072000c0c10703114110003600511280706011108040c0c480c80411803100080c807294040c603042409800c0005c1c0007805031740416203608400000 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 79440298 1250 79439048 79439083
    0x70c050a050c01031b12090c09091104111e0f1309150509060117060114070302010e011104030201020a0303150f0311030105160903030815091f12030504140d0203 71
    0x28103a0558050103811140f01070310b21020000e491124006040e07a0415140f11b41e025160b001c2e03802408203040e042400340059180800182c0c00c1c81c6840f1400303010a40c0350754052403c2405661100d04020141d0352502c0119400118400c0e09a540380d505a0150144481c50344003400801b4032030019403405c0c0060a0248800141c8030050340c0000032000c0f50368881442002c4c44401c00980341d030f208815003a10080e40c810344040e92268001030300c2d03c0640c900351441c0d4a0340442d0341c00a0586c150050138010750010020000109440705000b900c0c412408042e000d688045e050074000380c800d500015070140c3c584a0a0003450300d030b00c05440321403150742c02a610b041c0c3c1e880d480700940c5404e03c50140c102032410010300f01c1043c6c103180030341940c0d91840003905001056000601300200b8550240c00100c006224640526140f0440400d403001040c03905140800400b01003200f064018551514642540b6001d007400d14040c1985c0080d43d00020158205500f40350b0b240050b1400c020f142c080e4080c0d0001d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 79441548 1250 79440298 79440313
    0x8030a020c060313030e031507020a0b090d0207150527030606010c0c0b180607050601061d0a031529030c04051504090f12020a120302130905070c050a05 67
    0x24028074000308806a03a1140e481001800580e44a034940b00c00b81c0c50f8117003061048000c2140009040124070160040805102d03420004120740c00710390b6680d801d109010314011900c4541c0e5183c0d88480500b85440541d000c400c0a1194103502040c5002c5000289806031800013100034108a240c0681c00034003045065079074103a610320307050200aa06c1070b420f10705082c808a0b0b9460b109100740c440e00c81c040740309074000b44602038111070a4140d80482c0c005019155184071528019a80702000d108810006081010000b41c80e184492084400c0400601c544803160454654400c9813071801400d03a80c2ea9942c807040004d4000300c2e011401c00d40174442a100139000d44800741410000c5913401544110300d04810001c00310b1400c140740c8035000c0203a80001d4811050710f8078031000d401c51035010f0550f4041e0340c40d40e2246940081c100d030585101d4000800d56120b02c000640a0740a00d82a00ba01d41d94a40d40510035441c842d8403480d07125002d0300e049803842c28261243c608041d50000240c445400418 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 79442798 1250 79441548 79441567
    0x31807170d08151e0a080304030b010302030d020616031d16060f0c15091a15041107030c03140906040807090b0a05030304062609010203041101110a080c0106030c0803 73
    0x1060f60000d00d00c02030309801008500011801c80910014138130410724640e0fa4100b546524507542c4c040c10700141200d42d1191039040a121511092004a10030f00c00c5140d14840b0307602c049146402110b6091501952070301500064015182c02651101640c100c1c2c6400c040e0040f0400908440c040380740b20341c40d51281803c10040121802d44c0343c900502c040c0c00901800541481e408401c41440c00390002542c200c58940000300307a1044d400146601001403d11040c11b0588030f40d0383c2054001c0b00e04000561400004038000d008507900074003c142c900484401107405800700c0c0c1513155000405c50f1400703001d000012601d800c244c01c00d011a41c8248070a1010700120f01c0380b240c848400300c8000e4465071a00c0002942e0340700c0d9015140800c18007402e034002032a1003400343c01e0a1180f4004450f00c030700e408601d050017500101c070180c410701c036906605800c55008801e0b0300000000103003d0310300c49d0f8541d02c0e409116840014451015941c0750340000221302409180c1c406010254080e581e2920001c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 79444048 1250 79442798 79442807
    0x4061a0402211609030f05190c0602060601080606030109020903071e030b090a081b01020c070603020702010e042912030d0b210c270a020307030e12031807170d 70
    0x61808044008000d41100d240c4d411004110881e80d010400d4800d050303d5107402d17424000403000c2101c174034804142400c1005404c0c5090400e94030703180e00b118200d581d86d00044915003020744510788c201100308014010314409400412031040080d08680d10b2035541e05054101e0348c95a4903403840041c07101024006c00900031f4034150401000c20013071410300c10310f85420b0340c54810f40d2400c100c203009122009010840a4040d14413160012094800c01940ca00000c0c000c0c1d8040c440c01c90015289010071007540ca050303c60110407000e55005c0c585c290a4240380307542107160001000342d0040000a0f07590745110b00b0001051400c58084020506409040502c55101003d0000c40c1c2486405880c1c0c1c0b0139810001500c0c00c244c0000c58008100240045105482202c108800004d0840820421a164956070000c600a0040d075a00f00b00c0088507040050310380c5102c102e0955003000420115400144421040000b10500029140c01c6543d64056511101e40c6800e16240c582015030860300c4103800 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 79445298 1250 79444048 79444051
    0xf0303091506090b1203123408090f10020906070219060212070803150a09020a0905010908030a050403080d0b190302040507050711090a0e010204140a0b1204061a040221 74
    0x1600c502c0b4800185d040c2c083d4482c0541c020320340042c02c010001403081701000e500700103910303450800e0094650380d20820003070741c0340907688100109481101250f240c01c000258100706107400c0f806001c3c1062001400e002070b5201c010760300c0d40316006120940c056903c4045101c4003003441c1403050041072410354083d080144044031107940c17800034814040071410301c0c0100c9a00503065040f03412039200b50750005866104681212520a03c049680c01340303190462002c5c0709a903001d803034084c2621350b501211075070b9215590441c030000d0340900c8104000380740c05002d0044d69a800301c0c0405d40c10000030201b440030061140c90401e482281a040065042612032030703800013458540940340407000d40700c201d101c041c400280317802449070000144041e0017580c4004500d030b07103c2c8001d543d00d0307554200702402e152038802d001d4401c08a03408005503404000d422242c107101076860200040e0f0342d941b0341500500c02c00250316100c20b148404521f2551b114402401d141005400c03413001c10494500861a5007070 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 79446548 1250 79445298 79445321
    0x1b1e0102130b0307140306031002031302010e090105010903062a0504140103020f0306010804060b031c020f010501030b060d060e0610030b090705060315040204030209090604050d080708040f030309150609 89
    0x10804e02140b90b41c40f480c040e000710048916180d0300e46900f80400d1a05c036216000101d031510202c00c0c0000808191840c581c000c0c003da850001c40ca4540c0304101410000b80f003014081176090108100140494004088940394010801141000590340c83c4035021005849400518001005d00020103449203c030751082080c41c0131401d20352544001e91052001400703540c148203d000001c1c0401140350014110b042c03002d416140c000c81244640c0505020f0207500201500503026080aa004148603550490703401501520309a12030009002000800e40d1007a1180744d1544401c0401c80c0d0100311244c000e044600c20403500e0f80c5107003080c0540b80c42c0035003c0b0800d03403c10502003116984000a4941008641100891098084001034000c0c841c99000035001050300f0b0800141d0000071661a100d42d0050702642c003400303009c0b5812075030600102c99000200e044400402c2c00328101321803603070940d4800c0c1030008219510303031a02414103000c1850109140d490f80000d11403290310f40035100b24500c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 79447798 1250 79446548 79446569
    0x60e06040c1d011503050c0d06090608010e01052e08010c0509040c0c020f13020405090406050103050f07030c0e1b0d0504050f0f03030a02030903090d0807120f051b1e010213 76
    0x5040c00d0304c12100b004070400c0f0404250710b07140400c010038041d4080301c0f020310400d20700300500e40d916002c0b04007030141807003102507651800115000c03020042c01200e20441d4454800a1480d030101d0307050400c0070301000d022100100740d0b400410303400c1c024270803018402c00f1a2580b503203895180040200340d402c0e064150080282409505005869000b0070007200c040c201d1b03440241c40044410754000b401554092940b05c030b080000c0c44144800d9a100a069034010790a0f038550241c6414503aa450070a4400206621a002ca04000b02050106800c0d00f005115403000484c2030104605000d5401a18125200e00d95850500c001c01400304491075480c03070300d400a8010032850005c402c5d201c3c0402843d111540350000b00182e442e1105204407141c1d00d400500d8441107980e42c3c108603015401c0007904850031980039400629860040d08403030503070031040d40c41503e464095142d4041d0003d01121103a854402c1d04800c9440e01c0c4d2500c0740448110034200010303166070b5695048091029103038803c1e500c80 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 79449048 1250 79447798 79447801
    0x105041b0503030a0e03032116080412050d150602010c090f08030a0305060a0312090e0a0902090402010c0201020106030b150102060c0307021c02030409060f080d08060f0d060e06040c1d 81
    0x1a00c010094440c135041a0420340310580c520700c0072038214030801446482c1210202c04804d051134070201c1c03980c02549004040309030015803e40c00d4505a10585001d0300820405650307080e12440744004000880c447c003000300c0c1c5084a16541844603200c0c0d00544090b03515220031980c000c0c1d10002c10801010641001381b1100d14003c2143d85074810000c2c1001010b403120001003c6864030310b54000216446100254a108141401000c10255010f00c000c80060240070035a280c105015042c400c91b001840c1030f40d140c0365a070056451800500c0d089065540702c1600001185101103010b01c12481c1c64062120801000002404c0100c010941c10140e8010700a003c40258002050991060803080c080c0f85624005c0c003e925600440d4000d0b944a820030401003600740b800d84000b42161890b0382151740b881504002070710185000c842d41034120210307401000c060300d000c0403449141e601801d800120204414026070900c03100311001c2c0d44004c10020b003044015850003498007201155003040465 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 79450298 1250 79449048 79449059
    0x90f020c1b0901050409141203061f0f0c0618080c01141506070201180909031d030606040f0906060e0711070b07080d0f0524060702010c02060a030b060c0105041b 71
    0xb41060251600440d900ca500004104010780c018004030004002ca860081d03100040321020386c82181c2150240080720703071940050581607030400e034243c860313184e028100121010807510504c8501d0155134440d1100041c0300d00c941a0421403421a004018095840e00c070624503d0a40c1c002c0c001100c8550500350420003101607840c0f150282c01c20458400c3d80e2641c82d800100c400b104160049403540780007041c002070411907070380f1031024603101e078503041c51051611103002d01080748500d019415410030400200c041c5420b6000030914141d1400c001540751454844000315815a00081e00594298060010803904a8102500044180300929040e81400c01d204418020184018100c05000c80d1601200403a900b0403401c03540100010006858080303e034003a81da600360840c8a507211600b800301c08604001d82200d00407074068554110800f04e44c0c3c28031549a106004401c10107a9580400c101c40d41c6040084c07140ae81d20900200b0742e82054209a041c0801480c0144141040100101301 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 79451548 1250 79450298 79450309
    0x50108120913091410050405100203041e1509060b090c0406051801050424030e0115050d02030c040513060509071203050a0c0c060504060801050d0203120309010204090f020c1b 77
    0xc1d08002c0c0c04045120500ba19180c08001100301002e1040e0050b4071003424990703003541c006071203240101c00302e5000300994031502c030480c807041e10050084403541d246258000510080c0c03500d640d204074184840c2d241c45041140441d00380c50000c640031507c0b02d04944552400c4103055802690604203640340a00c0d28001034201e02c0740c025519a0b11003075a100503400c0e130281b81560700030101e440c90400d4108002e170461191004092440300420715011030400c0c000303030500c107285082c20f80c0688002501d00705000c01044d181481c4d42281e02d48580045c820882c8c0752070240b240074071070100c3d41c000038040c1403611500fa07440040c84240b0307640c4072190030000640862500d4030750702d400d41800da07039a031380000c000c6903113003000701014000f40355440c00010070541c002e000f002154807655420b141a40c07035204010f2000074101d40654146d010761841b032641c82c01c5000a540000c2040001450a59030740d00d41c02c191440310100e0884660b0126030b40085560034450071403160240c01030803070449100e2001a0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 79452798 1250 79451548 79451569
    0xf0709150b0c0601050d1401060b0a120506010206072010020c0d050c06070522140307050316091104180b010801051903080c011e0204170304030302030406030b0a05040905010501081209 81
    0x906c500c031403600440c140a50410032142d0300510000030b228464492000101c164022041c3d00700240d801d00b404400c10700e19205290141905902030701080d25656401c43e04929010149825400c4c03600340c0c100712032800c01c841607001d0400304c40581c03030b4140b1040b003509100210040d502800010088983d45038804541594012038904025807204402d1510801088070300758442a524034030100070811130b22144150034003000440c1200c541e140ca41c8141074680030701e002c50b500210302c0040b042c05511100d0704075000d0b0550030440d80c1d08182d5039404511440d032021014051860340d502400c0309035684400c08a01500b0140c03217800100c5451000048248001d2102824203134021800341a04002900400f10040141a51301c0d0b0101c0d13101e02e084001d5009120314141c100840381800c01c07102c2c000c002d441c102c0346c00d9005141010701d84501075020307183c4c126903d46e0004800c40c000c01c0310350307451107a91410f80c00303036000240960500e041e241c6031034980e01914400c1d21003800011125aa00070000 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 79454048 1250 79452798 79452809
    0x10c0302030307030906060503030a081504020405130c050c070e060406090605010507120315031a01050406030308040b22050a0507060306050f040e0304030b01030b0a0f020315010e030f0709150b0c0601 88
    0x81e104170142030420040800c4d403c105c1c0d0602000524000c13155000c16100d000700703403000400300b14400341420041288100c2c0f1071650024500c0f404100750134200c2d84004d40c0f6070b6032401c14a103003000b070f4075440b42003011540084075200160428411181898424035000d02103143c0100071150501001800754001d850300140790b8450b291200f0520b80c860342155018411100581c050b00340c40b46412002d001a00c0b0821140c86802000041e051809004803c103e03601a11078410f151119110344141d42c0c001820740e00d4090040505003006050041038242c081d0250015040c211040e02c1e015052a00690241040609180c4148682e40c4c0303102d6005800c00081300c0008840801c40c502078114061f640c03018042266001c0001700344590140d00d58420b81288000b040a0008080303604128001506d26110103046600400107550103210089102e150003400c5820311307480c683ca075a10340740c21500504030b0240c8401e11a0007024421444501815144940c0f03420540f602000319a601414460b1 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 79455298 1250 79454048 79454051
    0xb0103090201090e100b0a0906030e070e040b09011e1a15093a03021005040b060906030a05010504420b06071506050a06030e0d20030408150105010c030203030703 71
    0x8030340041c9007917030550002c0500c030107070644601010f440030b0860b507881d214490100713087c210143d400103401300e00501911005c85940031151900c4c4c0b00c24200c048001c0000b0159940e601115191282106142641c0b001b60078011802c0580060300e0810300141c132000c140505030b0303407600503105011071085c5c9407001e00c1070b1202084410300502e500c1c24140400e515074100008158922005c0844074a04142e45020f5000c0f00c51310501d0034030300d10456404950140403504004e0116086240c00302a80341c101b40010222021810780381c40301803c4801c142c404548041440980d518500c0140c410280b01e0960b80b403c200540700c0410703402842c809408000224550790300103c102d00e0380c4400a0b50340b0650070201201e414200c000958000346540d000d204d118500d01400011010320038055041004001405428401c058007800e58100e0109062040e40310a43c1104951060007040030340018951400141801030492120086100c01030f08084d0402c0500140300001c04e400004494000000e80340 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 79456548 1250 79455298 79455301
    0x705010e030f0606040c02070504090b040231020f12070809010501090605030319030632041b030c27030b06030609070314070b03040302010c0908032d090907080405010b0103090201090e 81
    0x4030b00300845270b081241d01902d000c80700c100780002101c2c1c0910a5100b61107000d80d580c2c4d0090300842200f415103111840081003009480c410032140c001e0b0a20720012640e96041514180f0031801c00101115013000203150003041140e01c00c0240925801012080810021a400d080c0420b8882c0705020034502e041d200c078400300c030810b0701c0f036480803000f000040c9050008029440c00c82c3e030403513002d0f44600000c100c00b0901200d11300d014460090541040f0010f031410401030f84064000d04489c800400c2444018400c0304020018001400a0200303d4861054000d0844c5080d00e43d080c005800d081c002e0340a641044590140001d4400649030409202c0100300300c008090741c070741502c6821848100740044140810140c05402c0354100550036160103e00d281c03580f400e295a07008004405118490712081004024940c4041c106282e40c000d8000d441c02604401203000e6190550b04000000c1a040401c03051040030301c504010900700340b0301481a010186c00080032440640101c054108001c030 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 79457798 1250 79456548 79456571
    0x60c0a06110409241d060d0312050901060305012004180906020d0f1a03030a120605040c020c13020301051e06070f060606110a2112020304050705010e030f060604 71
    0x101580e0082035a000f050011001c181c03a4400d078001c08207980600f10070b0340c5101040505480034011801150075540c0200c40c4d5074401000702021b40060f06406101c0d451301e09038030100d124000d6074441d1003680c001081680c90f603c1c1003421100e0b140c00303003011211080205052480c80130f00b214210380d000e0700c6481c940d0620041050080440402c001c1c0701b148001241c10702141d0399080b0081c107003615902040078518048001c90a80f10204e003943c0e05400401480783c00e24050059502c181d0800e050005246841e07801050440d0462000d15015074420113001d074441c6050300020400100e04a41941107500d80000302d400c0e0381740c20340b203c0000e11001a43e1345082d15000143e885d10340e0840070904e14011f09040c9400103051600510300000c0090071080d03281140001c0303600441c0c0d4009a4042d5100140440030195042d850300c0c2420440080601f40840c809400914012070240b0040c0603114604400503103203403440000d842c020b401148010b0040900814020780c00041544c01080080da4075 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 79459048 1250 79457798 79457831
    0x705060a02030408070e060901090e0c0103020a20030705070501021603030c06140406060608090307030801091505030304082d0c010c031e0302030a0c020a0b0c0f0f040801020a020c060c0a06 83
    0x141c02024241c403c0c00400540d01e1b07480c070516401000d065896060340e0341c84603021001d89200501e07907080fa511450358020954841e60042048100360302d000245d00c1e24000d14414140000c80c81c00710b030355201050303150620405004a500400090008001c43d00100d4004a0f8082d458440541800130002c085c405010301a00642400508001303d088146424502a4011f100c1e50245d00c0c0040c980c0c030000b03015288000100c94542d034244d284c03030b403c50b842c00d40001c0147c07000302d213824210f8204142c00900b07034600f00060f00181c0056000f4050302040341c10081c01c802d21017404200d0850b0141d101c0045ca03d0003250702000c5040a00c0c5c017458035000b40c00c082d1640c0100508038442081000036440344a82d00d54003840c0074101c180000d000a09034200102da80b11540440900321000706404510001d2094009007165202180c1c190b003040c4000064220b2a0802c0e40305031601c1c2d400050104407194140705020a0044c100c91181c100384406100955a6401280080c0050360f00d0480c02c50074940d0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 79460298 1250 79459048 79459057
    0x603011505031507030612080d0b010f1b02030c0301110307030c050306090a0b0d080a1211030c16050c0301050a06170a11040c020c0603091501080c01120207030e0d2f030705060a0203 80
    0x100c07101c600922101e103481d00b80350b4400140c0c1c489c0e8601e0300c85550240d62089410402e88e0000e40e903084240100b8a070701781525031001c1c0049a04d44100c0e0800401da4030203028606a5000c1c212495459140541006d0300b5035403c40c9c00c0000704901002049815583c0120180d007000140c18000b8029018202150750450b0b903800145c2040d9001c2844801d15504c0002132180c1540701d070040c0150800c0c600b4449150000b0340e2400c0b2510000d10108011600d4644080502c501507030481d6082494900840c1c02c403442944e641c44481d8854038240306c0984a4055069200c2e4000d004200b07032800c68a42d5580902c40d858068421500c0750018000140f00300a05840004001d00d00303980d03410148a0035542d2071001885031080d2010000000c0c0c450000b048c907880c0c1c4901a101e03414003e01440301e4000039030150708102c0610860301d24036103803500c40d0250156064070420741c4000100c0e0880103a00d04103040544e8850584070101c02007041d03200418200f044510544410340c030f075400d034202a4158000c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 79461548 1250 79460298 79460309
    0x12090a0212070602120f091215040507030209010e060a0303032c0c090c0a05090105030a09050d2a11060702030715030207020414060603241806030115050315070306 72
    0x4020a40c0d1020410100300c441c100c83d0b09400f1104003081e807162004050041102d81d18507180140604040b80c24882d144690030201c4070141d030345842003015840700c42c80b8290390648a590000505004508003450158017404440d0041841e82c41c202c0000340d00f0000300d00004041640700c161404605212251242c0c810110010007405030341241d10b01a52003c00d02915441901c0c1200400d901440c40d4003142c0c00b4200030707500c1e40d00d07021829005507290791000c1c0203042c40658441c140c0010034400e0013801d9280d0100d80e620130024102580005070f058002e224201d441c164500c203840080c0020b00c5485103800c3c02d941c144d807a401030f0b000182c108400c80d4030842000c3c114542500e02c0302c0d4103074000c007031136032084604004103004580321002003001102c0c2250480300410100c0c0c40354420030200c082001c5038041c1c504c89080d0080102e00c4c00104500c00001c0e0024090034001700b86028083d10058030011201c40c01c0a5142c940007a41c0d0340d55258130103800752200703c0441c140522907003188000e0308 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 79462798 1250 79461548 79461559
    0x1020d0927020405131505010806090a020a0903020604140906060306030a022707180605070b0f06031006060c02130b06040302010513120b07080a0509070902130905011706070201050106020312090a02 87
    0x1d05e0381d51010f071001d00d8541400201700c05021426600511080d400703500060440b44540c0c1c1c8614501d8000d40c4158a81c40a01412050000042c0c2d50f03000108040e10b05004041c04a07252001446400e24002d03041511996040c810480340d80c800042d28400f06404650200411035000050f010701c081d01e62041629546d90000c000d011038010480d100c0e0070300380ea418200300b0755407104211500d01402d01c000340b60805a00104074040c60702481682c101d03a004081c2c40009100300c0a62084480f40d5020f50301040b000804c00781503241c21b60303000d9050f100004041c8490700c035038400200b1520031400b000b030600c40042a400c11504820b940c010280130320324000007400c2003500f40801e00d40421105180061600310000325807070000d0081c03d004100c02001050010704102e03203500613400c00440c09986140b04000010342c0c6001d070081c2802420003014450482c03207011a01410044003c0c41d03030095a051000410455900008440b0019801e940c14040394480144e070600700f444107480a540003 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 79464048 1250 79462798 79462819
    0x60b0406030809010f02030304021807170103030f12020c060a020f0c0f0109140a0302120c150a05010609060c03052b05040b06040e01140402040c110304030507030201020d0927020405 80
    0x405101d00604401d8005d8840b20490348444004aa60340303c00c4034000e4104071803280c61711094501d0107155402407600d042c41c40b500403981c4050b4400c0c0500360300540004203800030f1079414503003202081510900d4450254a05100d44100c0380d03492102600b030451507940042e400b4022050507003a54424503406043c0d8540c51849090315010300540038040d00c1003c0100e45111078004002402d00c2c203990b25402410320104400310304111a000003d41d082580202c0d00710700d2100141500c001d2090b0041c03d00001d095051103001032191b500750308000240112090900086a0400c2c280c60001d012580c404145040481c20841031200011203020140d00705020b100c20015070441440c0708140c15141004281001c20720301e8262035042210864400e42c40c004200942080e4010211502984c18401d1100041842035403565116034030a603541e17040910b0910071584d0605c15417106143c1840d1110003d4142102c0040b8109503c8100501c10700000305505441026010fa0f07000700001002c5400d00c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 79465298 1250 79464048 79464053
    0x61c0f08250507081204050f04110910030e0607050a02100506031002070317160c0b060a0302030f0307050d140406050901020709021b1005010e0403050703031b260408090d060b040603 80
    0xc40c00c580c004c164141c084d08070400316909828041d82d0807a28000c0124a042c0c401c2006d10008160021b00805d00000c100f00560080d110040719030740808056400181100c201c80c640c0e820b180c00a003048041010401c0560001640003c02411002c9940d40000300b949800c00046d1422043ca80c14541090000c1844403c2c1600b0501e148015080b8000d5085159078860014038051a00c030982c0b800f00e44241303510fa020640b0342c3d80e46a84800003800840c803454480d00002c0ca42000103055440a034000107040080040a000c450b4840f19142048152500a95034903062802580110700c100f00e80030880e000523030710800c8098003c01d6040350840d900d18080f06000d80d1303c0c41070302441041c7c1c846c4803d5001319070201c0c0703e80d504840481c501c080c02600c0d20b035000c4503642c0c040a030507810151994492223240715551001040640781d0b4450241e0507a1140e46100243c003107a254903c0800c4150030000400d04040c2202d4088108442014403070803680743c0392000305803004a0302d41161400e14040304 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 79466548 1250 79465298 79465303
    0xf05062d031e0d02010c0206070509060c06010311010f03020c0a0f020619030501170601030c1a0c070602010b010905030a0f0605180304090905060f01060e100c060e0105061c0f082505 80
    0x2c01c00780c104107880d69456081016403d0369003646001006a110b040020300151060014003034100b0001c0105190000c1e16210f81c1c600002a0401c1c0c0d07a540d00b40c4030a02841d038205281c0103864002d0b040960500200c0075200b52500d5541c81d0252821205010340ca0031961031a0444925201070306c041c10802d24884030080092409000b4094011381700c0030100081000016141e0407a984a40d06c0703150bd50810513140e80b00031442c80d404032a04000d00000e00b003a1810b00000c006409141c0c0002882144000010803400d01503010340e0080e00503889013408251009006051030ba0000b1000c0b0355900c40c040c030700d040d60703100c101e15007480d0001042c0450420041e4100f4001b0a00400072218551910010300b2424002031181d08049440b02d45980c20a0411003a1003821101c24100b51a0800c05600e034102500c0070300c245403503565544c900304080d034a00100041480c0e1a9510ba00003442d046541d03900c0c0f0a82680d6020b051140d02048100e046051608030743c076240450207100700c101a02d49482035 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 79467798 1250 79466548 79466593
    0xd06021603080901150b0703090b070f110609030309040c0e030706080a05010806060108070c0204090b01030b06090108070b0a030b0f03070e090c010e0a1202040603021c0203010f05062d03 82
    0x1000a00c502d0081598420140102054441c010b2003d070001850950040d41941c0444030131414400c66900002d0320b180b4200c060614103014440c40c0a011700e079450a00d00139807085403083d104034414803800c82240c03400400c0d04c0300f04200741c4000905050040f800e480701004684002e40c1f45c86088400300e50b403a4402061030243c3c0c1000000c2c49940d803034580d0700f6213401045683d00d000a40d0f20000510407407140b185448898000707070002510000b00d4648050000090b007044e90450b0f1071030f0500003542403100002e4010100c40000e000140d042080c54002440360035103c00c2015100c80e90200c00340c7d41c0c003841c140404402000c8841c0c240c0c1d20350003820202800c40c0d0ba450a07000e410410750055000b401c0380320302700f003005100715811401c3c0070b007907584032517090410703a009076807000040010b03120544840003d0481001007442c0319410302c1014251400544044009414201803003080d4130340e42d4030280d08031880c071a402420190311101d0340500c0006102281e05210b6840810142445488080e = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 79469048 1250 79467798 79467803
    0x6051810020c1503090a030f051c0221010b09060d060504060311100906020703061e050a02220f090203041401050c04030b011203120509070f03120201050708040f0b04020d060216 78
    0x710f4002a401000802c1c0000c413111401c64011280c428002445a1802c100a0090303040640c00e1540c880d039015110305140c0700070682942d001441803002485030381c880040780d040d0182200298104000000f25005864055008034004100410f101000350041005030901130700c1003100700c0d643c1c280510f01c0c0c102c030641c0c24060a42129268049071240c9201016140d10380c00401d4518503665401008101001002c40600e4030700090407143e10841c01054002c5520307600250701d0b040080d600380c400140306184040122004402006004124030809045550300480140c4a64541c10b09010b003a444800100840d40380c2802c0202001910025000342e9025814251081ea00c0300c0b0f022400c40c0150b040500494064151140c007603102d60460340d4465440ea081c1c90160f80d407806a000e2401c41c1d80c0048990708070780c414108a4990911400340e00c10003903d84505581402c1d19505814054528045d0030020a00c1c0001c0554840114601819600540465588052100e0743c6503441004004 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 79470298 1250 79469048 79469059
    0xb090a020f060c03120601050c0d0c06060801060e01090c0201090c0e010f06080c19210203010e06030d1407020105040512010c11061501080402031005070207140301020f0406051810020c 81
    0x160304860030444143c0d0310380005500150301d00000c8103d00c0f600c445009242038100a000c1001d00341c42601403081c070b24800403d403078003074100d0400d20b0141c0c20348100c1c0d040800140c1c5820000c002c4114124865030440c0c010503000206a0804c601c103d024080401c0b02030f001209444001401c0303525504814100e407075400039490b0260320303214103c803d150156003a001e80b002c04c2c49017601c0080740201800c031000340b900b000c0465842d4810400c4400d04c4541c103090303010741d000c4010440b404000c04955800740e002c4014240340e80410001404000c0200c00d10800044081440302c11a402682250007800d8014101410b2581131031585020f8800c40582100141c40c07240e0600742c91030002215030045003c4103024800c1d154000044408440051003070303074075110308010b40e03041c5a13680c400d46028440399070107400306d603040501c40307843c296100071309a000340c3c410001c50041c12210750542c0c06231030a5251443c0e4449a60a03422240e503982d807042da90203c00d01490741d0490390001000c81030110281e45 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 79471548 1250 79470298 79470319
    0x1e0108061b030610110f06010b0c0f0111071506080604080403060e1f2f04060f02120322020a1514040e010302040b0d050601080a110916030b0604030b090a02 69
    0x1c1d280346000c151070301508030501d0510300004500490840154100340421500c050b03100f082d41903c0c0001c2070b840b807080001c001600c0401b044041c41808108003002c4000d0162a4401070008a0344c4110302e4040c0845924520701c11403080103400070b800405081c0125402c03410103013840f03180c42d13005200403500b042c40c200e400b98407030402003035a00980c130000d0702d06840001031905a0340500300b603107100d4a601c003405120012015120180c100181086401162142d083c07260190541c1c041030404015540050b120603c40880e0704205ca80c041103202c3d0300302c1001c1d1106404500943c40c044000c0d030110100e00301080c44441d0101350040700c806990340c400003603130303181c01e404883c8607134045c1d883d01c603100038018405400c3c507411480d51000c2c041d04501c10499161151801d084082e009059680c201d080c4500c10300640301003401c0d1100080b10b800c005410705641040301a03030b41c0c883d10014507440304c00074140c0d0386d61502568011908008414001c0c54003401c03490311481d03022012440b8054266 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 79472798 1250 79471548 79471591
    0x1606090e09150c0c010905033001080a0303020702010e0d0f0512160f050a0c0315050a020a0203070b0c0c010c0305091902010c030810090609020d050c030601020a0b1e010806 76
    0x10746010b16081c1c1c2c441e100110f40b40c1c000014680d038881c5000302107075900c0b15180000298204002c00d414101400720600d4041001549079407000e101d4070301c40700c424480d0014826072401080c4001c240da4135040040e900c800c584010f8800b0080980d003c0c0d842000230102c0018003921010044c03400c0d02c078400b03031280485442c103000541d004142c2503010440d9030344164000030700000c0701c0c9403605024400b210000113032031340c4144c3e124103c1d80046410070f014581c1902401e89501519410054a400550601000e208025981e00076080003901800711600031031510b50890080701d00c075001c058020700c12200c1c1103c014015003415200661240324004207500c8004001004295082d4146d4801c10000c8030794030225001040075283c840e046015000008542c1101e22515005005440d40584c5030950255034404880000b412110711901c100100443d030383c1d0101c5c0ca50101075101c180e00a580e00c80d81d440c0c6c00c48070880204012612148400401c0c02d0070001107481c8110f050b5440c4004001040 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 79474048 1250 79472798 79472803
    0x1203011503200d0e1e030703030e06010509060420030a2307050f0d23040209061206240310060e0a06181a04140a0b0906090105121606090e09 62
    0x1000740b004000a111030302c29406035802402c4942da00350111107886200c84c0b02980e641c0e0518000340e80c154000207040c800c058045c011280c100803000c000d41015071601008c1441380e00024400c038451a541d8000c2c03030258141c50b50346012008000c80942d00d0b442c2142250004200307000044507410b0414081406081c09501d0481c440d002270f40d2428201244440f4000c0a60094035001c407149440b000b000c4481482c81050100145281450040300c8c01c082c01803081c10403002d0440f0307024540103070690b0f86020f40000c800707810800920000100d40c160303190088600040307103640f540c540500c94940d00c01607440d410641c256000345451200c1506c0d00088036048603d60b00c00c0114403031a41c2441c08040c2d070250710002c0582c013005014a140c18103680001d081304c1c4071608001940b6a001c040c0107e802da6842980c80004007a41c2800311030400c003001a105120503c603031403080004003082101c001c010b20290303007089041401c4100e210385596024010441c940260071075001960001840300600 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 79475298 1250 79474048 79474091
    0x5030c04020304020609060a090e070f030609050403020703020f030a080708130b0c07050409030509030604030f020c030a08030105130b0306010b091003020403030c02010c0501060f0b041404060303090909051203011503 95
    0x2042c0c0e0303250583c6c10052084d00d4000031030b2141403080d00a000107015081000151007540c16a44556041910380c1c401b508403621178100c44034a9152604000000b44c0000c0c990054036011a1140c0c2418042c800203480c18000c02c1c2c2c020300754100418030800b003180120180c64552040d900e1140102c0e255020301d003440c002c601109403294054041089141082d0380507666250003480e0803807801c24828086803500106650441c0003401c5d400c012080700764148405c0700c4124007140034140c805070a40b2482c50030701040c000c0b18031070004002c9003041815180e00801c030220024083e01d15660f503c1c02409000d0308a031110a0089540a041d400384a101c0d00c01c0b10107499260700e80300c0c1a000b2a4004651956450350219080d40d42c0e01c1020410b00a0100c0d520010f00e00341c40130580c0c880c20003201000310590000307128000ca04000741072001940111074036044d5a1101e20000d4144010705006280640b07107042d8003903e8000000207d040041200301d44081e602d02d40f0140140032596104242e959413 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 79476548 1250 79475298 79475303
    0x1a070501141b0c12211005060d02091201110a0f03150905190f0b0102150702150a15030807060b0a06080106050a050d230108010e0601060f121505030c04020304 70
    0x4030600e00000700002001d0f01c815440e40040322488104190303182025400000c60409545803a981003007001c0181541a90241303c40c01144003051400f0041841d5008400060310b441e0780100b0280e0715030301c2c0c8240c1d50150411100003400300b15031021868103d580302650600c0090300c0c41811040e850301a0150384d1a41c50b10072583e40311986016840b40c000c100140c080659104001c0148058895900542c030006c01840f400003a545500c20000e413401451103040100040244200018140c020491070ba8a05414101000c10782d1080d112500400122084208030020030360040248007035140038010341842500c0800c08520f98900700480d030242032003104001a507000041c082c441c8110003428024290b420507e0034180d04d040301c1c0041e100c0700c0230600007082600e000c0d0b9103c000300030078181c01010503100030003410340c0c1c03484015201c4030140a170700140074142c4171482e583c611800c5480d00400006104000f0150581d0107113495000620071503100e0305c0b500c0140c8450749810301c00c0306e0080da03 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 79477798 1250 79476548 79476571
    0x60201060b160503070c090c0207080c1008040206040306150911120c0a090506030a0b030c120a120903050d0201060801240e090c06071208010608130b101a07050114 72
    0x410b0680c072909030300600c2c00102d89902003441044002171b0020583c2025180428020410b44404a002881d100d0f8580c0b00405580c0302d0003c1641036114030314a4150020989002c9180d5aa580003180d001c0c407840c0c0c0000c1200d847d04039629a1840c424140006407503519406210715208184040500d01622201e01c2a01d50040301080f0340c4a030110003000d5440640c1051004203075903200082c655007085400681c43d6481d103401d01600c0c035003401481c9814004807502144c00109910713043c3d943c0c015500040200d1031156842c80010702a0309581c00441e4030070109d40e410f11203003200a000e001c4622070200329600700300c1c4085219001c041c1e846071140c58080d03084c2c0411302d00042c4801e980c002a241d05e0443c010002c0300000b5884a00080c0402d034003c03000c00d00c024030407540040c000c4005074000010030040d84103101c400d102000c00c81d81000d401c4040321029072544609145030151583c031610b141181401d000301484103041c00380c160a03018400821a00c1882e82c6042c06154088072400c003a00b = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 79479048 1250 79477798 79477807
    0x21c08030a0506010e1801031e080d020f07060e0f0d0f0e130603050a05062203080c030a0f05160909060f0611010207020303070b010e07020109030210180c0e040c060201060b 76
    0x4000c15480560f00000516007545a000e142000c51502d008008003003c4410003403006109000001c0d1a00c450080b03e03558100c90f80c0c41544424005000e400014141075400182089514100d942940c1850390041c5042040c90640c611103a034606219030440d20a00800305040b1805001c6c0c0a0200000415120400e422816000300881c1d07480c01d0481024059440c0c0000c4046842001000d4240384600e00800301d0741480b0b40030351a5012a60340c0354038082004d094040c000f03584410300c0340d00304619450340c0d038580d21581e1800000d071840c0d08610106600c0c10041200380101440600d00c0069a0744034031030840c0c3ca0f89031000c1661a540a10700322401000000c00401e4842c6101100b1400c0c645c0005080108940c0002d0860340040c1098820405a600600500c110810302c02d810080743d0008214802032680c1c060349480b4001d28040c000e41e0703180ca201da16162150160002e095020304408219900c070b08584007148010f4500341c0307800e4003040340450f00c070340140314400550f0030103c1c0d040d081 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 79480298 1250 79479048 79479061
    0xa050703050c040510021204030305030f090d0207030f030c1704090b030c0901030b04020a08100605040b0301020c0d030506060706060308030f060a0e0604020f1b01060501120c080f0c0c030703020a021c0803 90
    0x2c070b526421807244c14132140c071f0180498090700282d031180d603801e96281042d440c600c3c5240f00c00b40002200da006580744441160b00000e03c1022070750710500205c21010309003003c2d240880c08001c05017074040340c2e420310440c005000d801801905ca80780c404001c01420a0141a503480d030300300540c1d821280200041c0f0100381c002c10031642c8280f005180031a00c9840e8008039040c600c0c8604200002911620b0900451815000d110403d0b503003580218140208043c00079583c0318010002b000345503079030b000304900761101c90442c1c000c56000502407119076920320780400e503a481200c3d0301c4000c080340c00100c1d05030320f06040100b00b2140100249951900c0304001c11000390711010700d0402e00b07441080f0351b210070070140140040c0240c00310000281c030b81c0307403200242500c81e0b440c6021089038070b010302141e41d80760010429504080c14441c48222540c8a01d1011018840d9031824141d40c40040740c41000c255000450350383c114402d4408106603600800350140750351480d07100505041050000440307 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 79481548 1250 79480298 79480309
    0x1060e09130821101a09010c060e0304060801290a0e04020d0903110d0e030d0c0515040c1502070b16110603180106080d0c020603070201230a050703050c0405 69
    0x202d0080e1100c030b15200c480d410140349098a40288406940d1101c02c1200807451420860010301c1e520015501c0803029842000d0544102d1800e0b5062014180240040c4021640311900b100707400350840c2d89e907a803910400b815100c1d00340b180e007441500d80100780100c1c4ca8100118408281c0207a44582401541e42064803881c0c0020405a001607081c0130641e203502c0036015010f04140a82c8485d400c458851050301d003012480103901c401d0002103511403800c0e03100041d00040240c510324200300411910b2800c1428620442900b0325000c0811084c402441062040181103580358072100000c1510b08200307030f8607040716206110610405010580095035003e28a4000034030135000c98004192610015007990002d4407200071044070804020300c0c01d442403040d031001d0406440100b0040643c274030010300000394070400901031600407001c6944035000350411241c00002d130202c05c003164804c1080416681c0b041751074141075420700003c25403c134000d00c1440d00802c24100703001e00e014140420f014 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 79482798 1250 79481548 79481581
    0x3030905010f1806050316090e1611060a0203011509030201020303070e03030c010c0e03071e0314100507030f0605180604050c0403080f092e21020c060a0501060e09 72
    0x509124512000200008941c0110f00c050310140c2c803441d4817400e0154030002d014000309613030400d0201645003840411102d080080c0e1104e11500e003002300001040040781e140d1a40001440c032449010244142c003407041c3c000e1410b84446d07a00c80c04156090500c1100c607440c1500c0080c0c00740c2c00400200d03184c98030982484200d88030282c100c915008446035410708668081c4840c0380058900d56400c0c0d610300d42482503000400e80c2d000042648105104201940c548900c801400030100300c11103d03000809008402c100d150607d8104403a14103290050301400361466508091803402d500880c00d0324229150340400e07100c546042032144c1c4c90205000007400080c142c1171440720240030000009202d00300820303400d110042080e8552241000740b01c20036005848500980491460f07901d0603250488681c84070709840d240c072042d80c000200c1140004000c40305d030340c44698000101c00c1528180043c680d0b00990850404020980c0d9481c01160042122074401e81d11001c0900814910b400011212 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 79484048 1250 79482798 79482827
    0x312060d02011e0914040213050f03010b0a17240a0e0c0406030f06060f03080304030e0f18070806040c02100504020f04061701050c0306100305040f08031806060a0303090501 76
    0x1070119600180d000c5501c030003c8074050019141410502480056192643c41c15409071010742c00d000903000075100c8a40b117800b4040c0203020720303074801d241c03544c0075084100241c0010300058020764444041c1c03001000d65118520b0107118080320041c0c540c00c007880e0400074007080102941030ba100c0c1c080c900007070010006d00400621a900344450f165440d403083c1c5000354451452041441e03001e1803c02c045d500c83d44c0c40900901300c10340c03040002c1900001141da1080d0705203441c011800385200010001488000041d8100c0e80c000c000b184900d0b0106040790058009459844480d5030748000c20040e9010b2030112001a04242400e2020180540280d81c11510092403c4154050103010804807615a4047c040b15540c290940500c04800c0c843c25070400341051081d8138500e072140104540d41c1c0d003020040109552140040d0502c040040d55088042d800100300703a8a08140341c468190204a00300c03a0010300801005c1522032604590401c116030f40340d2100d038070283c940001560b000264480d82c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 79485298 1250 79484048 79484057
    0xb0d090c0807031403040302031e030c03070b1806040507051509030303090a12050304020a1401030b10110111040807030b06011b030302071112101112011211030312060d0201 76
    0x245000103111060000140003070400400d00315181d420f1404d2501e04d0f40b10740c544260400c000500268401140c44031104414034030258040069026071455841000310400881c040131805008210000000c24020680d00c1501e000e14001082c40e281c582c00c064400900a601480e01005141050038404030302e100b030b094140c2d00303003e00b400c082411903008417000011500f0500c2c5140402c0300342c1d0f06208034a4481d240c040d0662516a0228822200e58001c91a4005650081c001c040e031182d0001c40d403211001d42001e490942c1d500024012001900100e202542031402d0740340303c241c5a00641d01211241c00007000301c03030303c0c64807080308a400241c031309410000d040c4001d18072080c105501d00d561521a80c1c0069490800341803110840030704031b0b0301c24803654401001802d0f10200144840750540d1101000500842c140b107580d034940f00b000000429989003400015130154401c04d9801c4983c02400b074103e802c020202055100d1040071010700c2ca408044020500d24100a40d540c3c3e03000c0c0c8113040 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 79486548 1250 79485298 79485311
    0x15010c150212010e010609080d020c04110408030d14070309020607060506031603030c0b010f1214010222050405090c030a0b0709171f0b010507060207060b0a03050d030c180b0d 77
    0x440e008820b000360462540d5042220042002c0c0b03501a02c0c5000614048019080303100c00a40000d403107050880500e88513940320b55036040c200b030b58201164000d00800302180d544107030460025021700702551445200020b400b0008401c00d01902a0925141e4020900307480c01c0403d039190300050102800e140c2c2c16214100d07240440c922046042070145000c2d03154031440010915111300c1320201600104000c210200c000c202e90044240c03d0351080d81c0c044a01480424a04082c500a000e0808096810a91191074841902c58030125405492080d80c003401165503803c0080e951314002141107400d0b5000501d4000070a42c566121070304010710f89421215242e5034600403154001e400300f4043c0d1600f2006031b40031000e180058903041c5602000003480f401007264006401030183e809d0142c000c5400003401c1c0c0400046030300100f040040101161181901c0341801555101a84030307040200e03103011241d003d090701400001400c844900c1605a500307007403640c0c03040303079410585200408603201c10 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 79487798 1250 79486548 79486567
    0xa060905160303081801140403080925030203010f0218190806040b070206071e1b06090302072d0302040e0a0203010e0d0212120112260304060515010c1502 68
    0x3110000a50091303581d040242020202c50820000d218040503040c1e00d0004c041c00040075903964183d016400d8108040e586c0d44000c1d0407401c0c411028038400c2c00d0900d030040541c0c100000b0015500b41c900a8000b0001802c504250008070310407420000500c05501050103414940002c0c40110700000b400005452560361030154602003042c0d8044aaa01511003040000c641c108105d9510100c0d6290000380da45241c202c810072184000c401a04100c40c04070300b14180140044145005648500100003a540c3c50500079110b4540303010380d1103614000030440101380d03212408200b20000038040400458510f030b003000000c210403001000540280c2c1c980c01d026a50a2040c810501410f4018081c0d58851004c001d040c845081015401c10100307014081034071503c41c40090544481000302000b164403410181c503034194908500c4030140001c5009040106204007450255100780d8060029855000c0c4101080581030a40c80c0020740a5060a000c24a00740e203006246071035050041c608103914 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 79489048 1250 79487798 79487833
    0x603030405270a05061e1807090512150105010f0f050706090602030a0906061707330906020c01050918070306090e0c09100302030703120306180b150c0a060905 70
    0x21225110310f00c2da80c004024881c10045420b0055140c90782c13843c0155211400021028100100300c0030003074112400080c4c9003405030503842c0107408021b00751000380021880859441704102c0c4181c0803040c406000042035405074512050104a82d110002c0e802c1c01c50400b12201e800c6400103890654070340740d441011a0052000b14010b540344c600100c0d0a6400d030038081c054403503d922050350941c1c007101e0341440350004101c1030103a40f031104d54510b020301d42c0508114440b400140e40710300100d45191a15629800c190405d04546040c2c003986c40c51100200150740c103016200c102c2ea08894510300c024001c1d8400000a540540b242c200003400ba603c1c1d07141e600848007684100c41c22a4010201c2c0300c0c20345400f468580d840a00304c00c00d034410300c0c1103901007601c0e401c2c0780c44002c10b502004415012954002c1d0821000761528280e2103103520b2905800f403010345400d000300d0380640c21580010542426000484441c0381c65400203040e016003503992580200400d14003070703855000f20700440d9000100d1 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 79490298 1250 79489048 79489051
    0x50103090b010e2203110d050301051e03100c0807090b090d120327150b0d020904050a020402280804050d0c030509100306050a08010501060813030e030a050f070608060303040527 78
    0x242d548107800c0a964100500c0c0c460b034038080303802340081030004000c03e5442c0301c2c8151039807403079520b5082414014004207103807106e15282c54140b0303402c0c08807070000d16901c904203a1187c51141c0d200960b03650360721a80085807003814455078100448810040204400800184809100d441e00040000801c0b000391881030305003d03058220b000e800c094405210240d100c490105080300700410044890600140400c5e030b00c3d070300003405280342000180034400207200383c40c0c0e043d0700940255507407504034609080c00481d0401c0481d003005891008000301d40701e0602e0a10907540000140701c8070740c0c079000548043e070f40f080084040110401040405880d6004200b0341410a070305c0100710f00b03040c901042a0915150404003651b8549001001060390090b219074100f070070303108200c010a00c0c1e8203048411400c8400059010b1103a601c466040140004609001d0040c40040c0c07000c480c1c0380e40084885440039281145e15a00a01007403007079140c0181100300040c40b0610451031225103e02200003000c0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 79491548 1250 79490298 79490303
    0xd0506010609061709030717040b070f0c060203030702070603050c040308130e01061b02010e0103180c06020105090c0312030705130803030403030b0402040510081b041e050103090b010e22 82
    0x10552410445a504075543e42845110700d01315030303c02d01d401d00c29a82d0ba4042c50601a1110180c140c21040c3c261801007101c01514101100550b22000b6040401e030181240c4402c80d0260b142540010300244044282c0317002c0c01c0301e54081e02d80303d031030000124003426000c3c10208400e5000c0100000188140000740440d010010a9070b41d1715151031a04203400005a00503014480c7c4c07010800c00011002403200794840d42403e11042c0c0c00721070300c0100e005041d02e4094010500003110b80d403042c008400c10f003104803000390f4001e10407070744c60048540d11490880c1d8400d4141d4045504880a002d026001d50303448a01c0b4500603007008000c814030b820365909a80040c00c25040007003808241541401240c413100e0003903609500d054900310105a81e00365a1101340300b08540c000104e818400d20364a409410007103c08419100c035100d540c0540072a00403d43c4840845142c040082c0d554001c2c0192444243c001d01c01d58120f0380b0340314040307030641001813000c100174000042801c5112046403120040c5c50 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 79492798 1250 79491548 79491557
    0x1204110103110d090501050105190315090204020a02011505060906040b161b06090902070b0a02070c2d05090f040f030504051009090e0606030705010e01020a0f08030603061012060b0d05060106 84
    0x1390342c00d00500711001a00010b01404a40038403248450841d807542088992010540c0001142c1000040050001c9040290b00c02d00000f0302c00c0309294150004440e003940b4412600c0d0391540d940030002c80e48a11450385810070010700c81008140304030409440060500c122484000b006a40ca0342e804c2003941d4074100045106820610605601030490740240c100f00e0811031a05600d0303221070058410007040b01c000310740c0000f41c200400000701c0c0c080004100d142480e00e00340c401c500700e1032a100920b00840440300d411442c000f0700384c54400506400341c40c8041940e11107842c0d5843c0c00859210303201040e400d000c001c000c00110b42d01c980d00c01140103d482c0d61006c0b03006083c01100d4041e50400905010581d11400900020780c0d008501d26044803001d0a00038400f01c010300040c1e04110014601801e014244c41c140c105200f1800d00440c400c030001c40c142c50440e40c03695100140300d04030b1300811400000f01c98440b800141c09a01502000d0001400c01542034080d540b4107180003800d800c41300002d13 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 79494048 1250 79492798 79492811
    0x20f0f04031e05031209030c06010b1902150402010e06040b0a031b0f0212030601140301170705090c09091306020d0e0c0a1a0307050405030f07080d03021204110103110d 74
    0x2c101071604000148040e12586096085902c4507a0b40e4000d80558100d405071034408110420300030000c850380016940166401d03580c0d240c540f03000c190000c20118102401d0044501c000c40c2c80450440c0c071079142e0140b840c480b52181d800444010041c501071640010041102182c17002d01040540030090b115600403405601d01e0880c000d007049150403a00911010701c080d044221b80100300c3c10b0b1550903000e00c0d55180d41d58540102d40b1503803401205460000004004100219550246108d1032820421110301c0f0f90b8074414810706640440b00381551a005005201007441c010b501c0f16045041c004000d1162036968850000b264024038811000310356841040c429404140400082d41208030b4050400622f4007610b01c245007100c0c3d260300140203000001071301c154060015140038060150446030f01c00e912101d92942c80c81c0750700511205101da1513088100c2072003030003202d840c485201481314041d00d80790b07150a01c00d40700400c041e0625807515215240d804061001c0e00d40c8072901400071418 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 79495298 1250 79494048 79494053
    0x607050a03020c0f09070309170706060518090319020106030b0a1e0231030b0c030a1103070f03090302011e06140d020d0f110904080d0f05010609090b04020f0f0403 72
    0x2454410500180100301442e138024035030760b808121550201c61410003103220070390340c54078903894a00400301c02880361000c80c0f80302c240120b60b4400c50542e00151038003005642130702054103401d0000c58440343e0690040041c4000a03081016901c0108458000070034025201c0d40c80f0f008001d01150021001d581d07840455227459070310141c1060741c00003140e04500d8080055070204070310300100a101c40c12101d021b000507504030165010707002150040d15004170307428502d0400a980d4030949400c254141480c602005500f0764208682c00740c0300649405041c0d81c3e1013036042e00a0403061030b0907015950707150909829600d0b066248c030000b05090100084a60803c0c0d441000c281c4440215401015071444c0b040041e141c07801c0001d88170340c01c600d0305010034400e440c1c01c070950705480e42141c2d00014804240820450480e0143c194070080d40c4051103900381203400482201d800348210350000c1c80b1107508100548050f4411269910040c02c003625100300104840000c0c2c0c40090480fa651200180800a = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 79496404 1106 79495298 79495303
    0x50607052a0d20030c030705060f070c0b0a0905010e06010602010e010203010b031810020403230c01080402060a050c01090f120206071d0f100906020c0a0803030a0c09050607050a0302 80
    0x64400c0d4a0a45c692030b504401000c0fa103502c2100c2c00b0582e0030755800812445041156203140d5070403201e03241c1070751800002e040400065650410342d00410401c5c099600e54101e864028001035140140083c2180d26111000c40036900c1030006000c50441002100c0d000a002003c811110813030254240c14941c604140348030361f03071000400204005050fa144004442803418139014030030b0740340700540c4603041c02c004907000500b5100000c2c01854a08003810503000d0f5441c1c00360030070481b4a021801c48081e0390043c7c40c07525981d040c0008010340c01c90403001c00055880030300301a040a40025044c0c9515040002030000c141c491044103450316a54040300420041003102d00d00600b410240c000143c81c00361000501400c207501c480760400c0d540c46422a0390440c019459075440501200052075070003178480c1000303c0f120001480341c1e1000040c181d5680600b0150410803440c2c540a413 = true := by decide +kernel

theorem cover : BRFrame.Cov 79316548 79496404 := by
  have h0 := BRFrame.cov_init 79316548
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79316548 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 79316548 ≤ n) (h2 : n < 79496404) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
