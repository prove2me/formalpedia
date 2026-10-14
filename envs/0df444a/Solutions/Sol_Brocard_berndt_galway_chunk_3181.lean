-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3181
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:53:48.604881+00:00
-- url     : https://prove2.me/submissions/780f3f1a-a908-46e0-bbe7-902d07c73151

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 571942446 ≤ n < 572122302 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 571943696 1250 571942446 571942453
    0x4080909070906082208070606030507120b01030609020d080d050105030c090c1603050d0903020604060b040e060705090d0614060a060905150f071a010810051308070f150e061323 78
    0xe0110f1ba0000040240c40d0188001003800351039841d04d01d00c4c105441d40000121100110148002900e60300c0c140c0c1126003201001c40e00a40c24000160804080b140003003400400041e5403c5075810f940209049840072025640c00c0030b201814024802401c8920f10b2450008008090300010091900c8110b1030207850480d0819a10140490465402c44026009a40700c081004100945070059100f0b07280e041e01c080c00741a402200803a40c0f000040d060740306004000c5030419058803045004008103402a01c2070206012111050f0700fa004207441c85400b440d001d031030106075207018800607002c4039070107002c828500000d1907003003202c1e4000d13805048082100700100804151822059400c4000a480800055241440a0b0720b0100b660755448407541c10401008850200055900242c1d40c00400e519a02c924502d481c0c5059840020b0051511040e40810780300c2c450503510130b08070b683c080411180d8645400c0c120306000d03450f10000a100d25000d000c594141d1029a40301e40c800074016084 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 571944946 1250 571943696 571943761
    0x10e040f0f0c030c08160b0a050a0f11120d0b010c02030c060c070305010e0c03150f0a090f050708011a0f03060105010c1b0b0a12021c05070e090408090907090608 71
    0x1306550842e0951102031203511221110f00521a0000c01200928100854034504504000090080c0c06040380d031030b041c444026818900c280c0108108400042d50305d050f0307020f00030392068042d4190030122425000070704c2d026846034654041d04400060b1900140100b001100c0c005c10009158061100034400d40140f100010020701c0034011015103c1e83c00d0f01808409007154181450040c004400c0082e0302204030900007130492640e0000c0c0c11640c0d441c03000c103514041d42452042c1102070340c1d00820030b2080080000308c103041036010f2841e02c00041030407000c900510041005c4050300c4181e55070b241d048200104065800f42c0703848045a4800c9da04985410ba0b05d0011100d68007450307018a0003d44000b810720201a800b9038090f800b002411021400c03d50340380d904442302d004006003011100e0352080402c10482c0290040c0d01c40c0c01c4000c01d09102444c2c68504012183c010401450107400c0c80008107a1140c01096000144e900b02d649070002a5545299488400f021446000003a5103900c407 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 571946196 1250 571944946 571944953
    0x3040f050111060411040b030604060603050c06030c03010e070c050319080a0b0f1002010905120a0f080f1504020c0106120c1202010f1b080f1b060106020c150405040203010e01030b010e040f0f0c03 86
    0x1b0052149024440000d33280d455414198106120040014443c031001c0003045501010042544d044d90086c6e401c441c0c041d03403003003002d458216200710060000d100201d0034101183c0b058503c0d003030303d0505594030b0750b0984841021000740c400380742d45264801c40c0e1060050880c20420740008582d01305100104000700c0c10b40303401e4140b2081c10050401d10800040d82d28000303800c800034808800d42450003480d0b42c5001304680503a0b00c0041c2c41980e00512207011038040d65529015038403020110740c02000629525840304082c40c25400d001c4408460080000603100a114692054560103031203581001141007011113242c1d120000c1159411035101c00c002c003160209003e04010581003020b550340d070b1603103a840a8032403c080400c11160f80810010b00c04d299000c608200300c100203039925484059840a404901e00503038000f0741d005803011000080681c13003038034450b0489003c1c0e140d01c42140d8036254280d201e103000310707000362481b480403020070000342e06040703042400c50003840000140c036240d98 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 571947446 1250 571946196 571946203
    0x12031206050405180105060307152d210c0e060f16140616091a0409050a09120507020a03171209030301230a09020f070c0803040f050111060411040b03 66
    0x20f6130080083c0340109003032040002441010340050044005203d01c615000281c2e04405c01010300101300306080c81030421039040d2080345c08800f2074218070310030f0301c2e00380e0400144000d461a034020a000f246107072448080416204a0075040315a51358488120054000d00410b6440352415504a440401891010090b03400f07200e00d015110b4000007001e0944202c855140035130280c41c15201a95400340e80c00032580100d134250071078040d5080400300000d000140301045c02150f1003606130a00380720422605401c10307800000c3c43c5100f43c0030785801403d030100445e01d030701a440000350807030310465060000c1011700420803e40340c060603445262414508000f400d8510554a4040e1a4804401030000b000110a107100f071107100101c100190b000100014a0b12545100300166550f000810484c10b013404402c4410244d04101d0300183d071655600581e0f81d13640710f80700300c489290750001d000c030385584071b001c1d04040d8840140080c51341342c40716241c4009000d60710320210f9002da5606010b00c10307900d091 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 571948696 1250 571947446 571947451
    0x50607140f030f060906040b09060439020d02031303021c020303181c080f071a01120309151e031503050a060f0c05120c040506040e06011812031206050405 68
    0x9aa60f40604114050102812016041c1e510480c1003400700b110b1500d9001503240e110804540106c0d0520f0480b0107410034240e001a0002d2a440700e03010f202003d842c5d0405000c501c049582225170185241d401203849000380c01402d1556075000d02b00300090300c1e0030603084051000321100b0b01f8140c0c82e40d5000078510390050307004185440b03030740d40c4841d000d18042e5204150383d00842014440e08056136541000b40c400c0d000c3d115210400800d0606c02d10070711942608000c1d140c10b40e07161065031120221b041100c20728404900041801d10301054051126400340605510354468007001041000c1c1d01c1e03040310020020008040e9580d41c2a1441c08400002c0703001540144c014041c084881d0078043c041e41c01100b100082e103420001d08070340f1640d0113803c07034800140c0256100d2140d210500d9046052080d6408581e00680108004c1007009001d80207501500090300c0303040340c01000809000c0e02840320702c94181a070a6a8002c3d0300800c0c040c80306c070181002c11410002e03800c0d0300d6000240803034405 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 571949946 1250 571948696 571948711
    0x60f0e01120c0c110103060b0f180303070302151e01030818091603060e010b041707090c0503071107051302090616030e03120304020603160e09090c0a060309050607140f03 75
    0x540d03d4840500c0346005514400c48000e18081c0942c2e400e240c1c003107109210341c0700316001c4124002185004a009111030211040b00101501c0d540c0350359043c0255180d40100b4840400b401d84030201e1b001464a0584030100b0301240c1061640361f00c2d58441c444c00d03030022030b01c270750030241115030302c1201f5681e40540310320400070000d05030100082c1e00802001c03070322190000a005c400ea080180110f02c9110240c400316405602d50201c49194418440d0801420782c0c0506200e40c1807921060071182c0100c00f0f5031103010141c2d900c2c81030020140d0b4107030303540400c0e2240c190030200400d1a5880940c458004002202020f130043e487c101100d8009200783c00c05040585c0002c44241c1300411502d0188015100c0c0180d115072282107080030f40000b1a24440903110380710b00c045160310041400d00400c4000c1442000400003103880c80c040c1c1c003040e06c42c104440064403900c40480b0100705c090003882207441c05a0001d00900720340e0b031103203c2580d01d91191404801100300510142401e00c41420046104011 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 571951196 1250 571949946 571949957
    0x20d1b0f090e0f0307021504080706120b010c020f01050901030b0a0e07030b06190f200a05071a0301120507030210020c102109170c010204031b060f0e01120c 69
    0x141099000444a1600100442d60400220b64443c1c1d5000001e43d441950111803881207140c9050071154244610741c0310282c58040c0802c002641a0841c0000034400421102803281d4000900110b4410103100303402035000b11160960683c652155001c1d00d554003042c100000c40304140b100085101030b00b54000e842c3c60038120b00b0041c0c5c0c82da040c0160f405400c81680c0c82d070b0406031181e00442c00d242340b0010307600c200b001020341c0c5070000784202441140031140c2165541980a588107142d100d521a8100b556a441421000500140961081d200c04541a00003a00703590030f20481071140350a071601070f54103110f5108044096581d0045031a80203149800070901609540709000030444141043c2e020300c1031101c003d003403103205041d08901500d03a4500000d5058401e18107000c15501110780c01c11040d04c081011114008154002c10503a8000d00e44c810101000b9248500c07090424020000000c1c404d0ba0b442c845c0320b0142d010040025014180104405c1500500d11304580c1d00e08507400003d0f9 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 571952446 1250 571951196 571951199
    0x902130e161206061a03040602031e010b0712051e1803010e0304060206070c0b070e03280201080c0405031509010e0d0309030f0305010e180309180708010e070c020d1b0f 74
    0x221034401c2c0c40080160b085d0080d00000100d00c1d41c511030000a00207041c1940010003e1074640c60300700b078098050204e910342401961110703985189508804001c55844006840c0c0300c09050044003641c4000f0005d03040d84c0801990701c1d01d810010303085540c001107020201d284110183c0d5003030080c00800d0070840001d58580340b40090003490320b00090081da05200502d401e0601041c000da0303603654401d00c241000910401c1c1e200110385000103080784a8607095403404411040103040641150450013661250360607183c076a0800340d5031241c0d1103255071503400034a0703d0070144810380100764031140c0b060001541000e00080503041c40c040c0f05449002a1740e0303585010400d40c120000c45091440b40c03604003c03941c104083d040b40c0e490058080201c1c00c0e1018400c880041c020001c6500f040720142040160848414840c04003420541c0c40c040410403a2001041000080300e00318400c0303100d07503202c0010708111313001c4c0200d440310990140d47c284000d201040841c00584210300040c0070210110310b0b0345 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 571953696 1250 571952446 571952453
    0x81306110d030207050c0f0d0c06030c11011b030504051609020d050f0f072f010c020607022109040f1404020103050901020909061c050708060411040902130e1612 71
    0x10405800c101c00741407050080d200450000102c030b05100409650b214610701607803000035100c01a19000501030401c018010800aa2581200c29240c3c80c03922501082c00960841500b691031103280b9000343d081d080d0712008034512907081243c2050090041e20f40549452028203140300f07441d04514400e98002aa20502c00ba103881002d074415102440130641c0d040c01c1030180000d000140c040800c110344802e0260369003200c40010310036901c5422909403040d200104a5000c0d02d1012403000150181c20009010341d070010a60318001c2c082003440d40000c03114500d03540f21a8004890b01c80c2c00c980c2d62050704012030020720480d07101c0018180c1801181c54184001410b03220018090343e8a0707401800000d0782a22030206030740d000041203a1102c44504a405c5000b4910a0720001070400c0c40b4204000032258004648180903a00840c10f04c12800c03804014001500c1c84020001e410003040d1040040f0030010f94021032900b014082500c00308244c0c0c1000b5001c9103695004002150b00916104041 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 571954946 1250 571953696 571953703
    0x1d070302160c14150706150b18090c030613050c0f210601050418050903070506010e0106020f01060b04050f1212090109050904050322090c120e0c03071208130611 71
    0x203d48003181d805100c502402da00340d0440c00b404c040100583c0d100d9000c81c2d0406c121301020b40c06010a041601c5d2560b104074110340311345000340c0074140144c480350042444108500112441018081e084040041c00f4049003801403e00030480701260740c0034009401602c0900004220b580550701c0b40d112581e910880001d0002d0020780085c0c18040704000401198100c82031000c41c440d1003604c0068242ea8401c6410709600c00c040b80104079004440020401c2c0700340905544c1a90000c0d802c44842c018004505401c0b600d550040440c0cac441d090204100c2403420a954500700301c00604803128003020924a0740c13610012084002c0e4100000c6502c01c0c095911560b210000c110840b42d01030941426241c541e2a4461110740500b41020003980120500c62184400f00601000e034080018038081d80c0001e080399960401c1500c101d0030608652286000051030030760101004016000d400c0c0b820002c00008038500800f2100c3c11030034400b009526070410080b03002040740e034a0b1031416443d850b403140d04 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 571956196 1250 571954946 571954979
    0x70303061707030c090222031a07051602090402010c0204060308180316031205041806060f030506090f0a0e0609010c09060c0b0f0c040306020d140105010201061d070302160c 76
    0x40300c2c0e0040c1c00810110718040754030350456952020050351580d03662000b0210140001c00661900c1c440c6100004001e044030307000503800e464061344407503900c0316001100c0d50b104015900c0048400a80800e0151425010042d0068414100b410102071164041026a0b2582d44182c039400000300f9180904091402301c29403021007180a0000c8440c011405104d591071070101806a00c00b10b046e1840050003003040368081c109a0f202000d007030304118003040c05030a290007102d00013a0210241c420fa07a00a0040502404006224040c26910440c030041c480c80010010b940d140c1d283c101d003c01890041c0325682c0920450400443d1481c883c0310b01601c60b0f400c40c5c0c0316104101040c0040004114100e45003a08514103020109030340d1502c4c084c0c2403441c000c6801c00f620346840041d92645001c5564427181140b0300464404025070781c0c0314016400c8403480d10034244892141e039a40b81c24003490381407c0ba8003c0e01d03820f005080c5030f2240c0582c5210784259004844200a15009200d07515032030075000d0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 571957446 1250 571956196 571956239
    0x50f07030c0207060203070605060a230102070f050f01030c1803032a05030f0304170d02031b0c030f0306030703050111040f080706050910090305010c0e1806010503040b1b07030306 79
    0x88091134804029643e10520f82c6c068600341d80c40d03020030515540d40821038000d094440304002e5184c050280b1074108002603107282d000d4071070b109000071034844881984084803001840c1c2c03222120650015405860a581e0100400a240c0c80f8a143d840780107008030080d5020b0381d02c0110100c00180c03034004280150200d1103402d040c003004000020800411100001201c0316000e4032903e8a18254142040341c800110044101040255044246170701540c416900c50504240100107180807120718401c08189030f0765604200b002c04450001640210340000000d0105d8450355901c1c2c4546003129030900c40c680c82c400c00014200300300e40031110807101402011000c5d0400a181400207000c0b845608480360140746503c0407000c01c180140e18003402990071000038031001441c540c00811807821262020310440d14a40001d40201e070060410380715a0042c2c50383c0c2c1c40c6442d90344034002882e900510000305035030640c0c142c03190030705c5c004050040980701c1c0d00c1c0829814101418604200520110030 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 571958696 1250 571957446 571957453
    0xa2409020915031b0d2003073c060e010509060a050a110d0207030b06130507050c01152108070c06020c040609050411091b0f18090f01030b060a0801050f07030c02 71
    0x1a1500d40d12074580a0b802c69105d424900d4403140c0d6500c2e4199000d000000d01c0d458040d078000003804208001d103a16012000d2782c0329a65141f0502c5668488580300d900c050010031000d02c0500c0000d019041d0f0341445807050600c942840e00d000005545a40400000c0002540c0802c50500d2140c101111010350340001c8040d00191030700000c000d50340d1b412480090300e4408408040358042e2561400a8100c02c0c07941130603c40d87c6025038000d8070940c0010403c0b4030961030b00040c2d085000d44074424509541c0302403400c0f0b60444181c9100000c01240c00d0303043e14070140800081d0006100d409d0407c008005d940c000e480118142010042221100d5000100709070815003004001401c866264965003411980320105403030b540d00e409880300340002c8100140354005258100c0940e60405403442092502d0901f8a150098080c015040d600396182c0d0204820700d80180000781d00050700a60085019042e01c8400e640c07203e50710300f520001d0b07800c03c94400c150410303c442c90f503150060010720103060005 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 571959946 1250 571958696 571958743
    0x2010b0109080c0907110f06070e04060f05090406230403080a06050325050a0b0d15060c03030209062a120a1d030a0b040510050105030a240902091503 66
    0xc941d03c03520300c100c0d103a00c01d01200303001407130050144840342d924004441c00c0340e001041d1944e003146d0f141d40030343e244800b1074020a075070400c40c5414081c40f02601e14414166081c10324200c24801001030241085890685808600c0c481c42d01d15018200b008080615060340c904080c01c02904100001c2c090304002030801400703000e2900e00144003900303084440b0460114031101440301c1040c6206402095207c1076244001451303120200162404441095003040f401d00030580c3c400f20f03548540b00d00b4011900c0881010302180c02030b030181800600191000d4540042a481c028104551012030039040c0441904c445004804100241605070740040c074503d07003d0103c2c00501810302c90580c100718240c080510340003d8800740301a40d0010307400306202030f00341403a18180c1e446001008243c0815460a000021240b9002512203400c5030801c1c00c07802e2078940107100d1440300540030030241c0400d032142d03000c800585802e0082445000e0b1300e1482c56181daa0601003508142d4600102c0f101310381c23003184 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 571961196 1250 571959946 571959959
    0x501150f050307230f090702030403150504020d0b101a0301090c0903230a05100518072103020f07060e03070504060b030a05040507120605010e33030109080403050d02010b0109 77
    0x2c03c510980300a6103150715220040085c1482c918840f0741e903001039044051028031030700000603105480c400c50506000075554102d003011034100302d40103944000c0e041c0021000c9440421240c0c2c100b404012600002501c0300f0301020380016142020560f08000401008101c10a2041c0a102c101504d0240c0f0341c01d01d103840e071100304a01d01642081e07601c0b031140500d02c9804100220070300254031406440e0704034055850000100740849400030f200c0c2400c2602034007808007040450030f84d0883d2a141c1880c0241d03000c082540042514100c00707511500c030050851110400005005219941d078214013031900b07400740340c2020800c0c0e00960141c0e090072014400380400400b41d079841614002c00081556aa0a1452610200303a112259030031002c540001481025000941602d0814080c10200e0301c1e600f8100800e40800803100d04906003002000c0080700010020003402c8200500206600d0071541703a442044d40149d0045490340c0c0400e02c41d0740300d1030302030040380070703441302406e003054032a02e41034 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 571962446 1250 571961196 571961219
    0x423041703071806051e0c10061202040b090903070803040201171f091509020708041e030501061406070f0201031d030408060702060702070e040f08180f0405070c03030504020307030501150f050307 86
    0xc6d00040c090008911010742c1c8200b0403801c11005e82d1000180456651107031880004120360009034080d5081c505000b4550410b0020a40681084402580740087c6901c444078260400b400807410004620382095070f00c07900009090182c40c001c92031403000e190300000340301040c5141e840740e1061410446282d407200109117082e4219000c0e11805a85c0b01030a10f40000c20744540e03000440030b450008200f6180323201040c01802500d100d5802040000d854603407007145a820040000e6110030200300240c0001c80e552446200c2ca4418180800d4156404040074095503000861000e00d900c0481c040004001c20031034140c03c5551400500b0726400c01e644020348400b0705d4010707284072104c0303c40403404001c40c00801103c01d41d00145903c2d1a40d100c554003508280d030b014910340c407500041106016900e06482500c0c01007500d0b071141114900103035029400741000500a0740e0600810f0b0b00000801d4003030142e16941440100390a14450411581d84c51640c00385d00002c4c001d0340f000c1c10504c421804172 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 571963696 1250 571962446 571962487
    0x1701050a030f0501330f050d0f02040f0612021e01051909091a010206070906052b0f0603021005070f03052a1b042304170307180605 58
    0x401c8141d05150107082c03403805000104003121020082000200340c1c1c5d013219240080710312600701c0d9143d0a03a680e500c1035186050a004107540220400381090001d80281601042c2510141000c15450014610141222140c3d400503106124a031300f0502149004a048072804480390200140420001c0000385140902000400f1440510880242403805034080b40010700340a0410300120468540a1131036000a800e06400f41c420b40c408201410301540d0001c0c10b491003962102c4c185048081c044403032480008494041003841c10b8403d8170940540120030060100c1c4c000480c001d4070f50b2050100c10200580d2034020801d0900040340042c4401012440107500f62401545030032a0500c2d0941105c103415400201581072848504102d001169001100a1102c2d86441c030305120020700c0182c030f0341ea10b40004182c0b01a07030002d41c25042d1038905600140a4031240070f05103102007455180394025640d0401049103446822800350740600c0700401780c000361506500b440440c0b0040c100407410b9 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 571964946 1250 571963696 571963703
    0xb0d1e0201090807030807021002032d091c1101050418020d1806090b0901020a05040b0a0c0b0906040b0105040b0105090108180a061b0c02060d090206090901151701050a03 75
    0x4000412080d60711854298003e0a0440e0542e40f000fa502d18105015a20208080f802140b420488070b44a038000300655030411484154036000d420301551840056508906a480c0103006010400c2c540e15014032010300c03070f154203c125100715107030300788626800340c0300c0c0300c0c181084401c10041c0b00a5a0820b0504151041ca040158980086e5a4101e0207440034040c0c1c25860100b031444030040c00b0107500001e5085002d50400c01c001d8555940c000c0c240c1c4181c00c08903001c107104100c1000980c44190007410b00c40ca4910740348480040507552410a001c1c240d03044c901581c0075005010500031038200b45401000100e13030030041c10800b000042e100303000e8030f031801d030500444000140140d602444441400e1070120103542101c26545003c000912209041e024041812035030302c000035014a15560300706400a040f0b508007165224000081d083d101c600300d8000078140001d22191311551002806408041c041c0c820401c0340030b00c02490042c00c2074020110840590042010351148000042902d40 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 571966196 1250 571964946 571964993
    0x2031005040b130f110304050a0201080109060f0b0f04090c0c060f1512020a260f060403090e0702010e0304090207060c0c120e1215040c08070f0b0c0c12060a0b0d 71
    0x4c07000b403001c0249445525600000c03400400c02c001c0010101e51495214400d8035003231510398903a0004000c880d11070154800c0065404005e0110640160203040c14404103c042840c1c079403101c2910050b900c1200038480450854240902080460f02459180714070320b6008120004548480414072000b9200e1800308100d40c03480041035440740329250014045104908030408510703c44020080701d650114407550050a80c041160352000c00c0003802640c06a60341e240e110300f070145510000c880a4140ae080d596203038601076000c0300c24005000144903003000107845840c0c9040c844290751590003090304100380c4129441c0041c9003000e20000d1645130b171500075074000001c004034201c085425008001441340500c40700e0100c111032a160310a40c0b080d50000c0445940301201503070f910190003090350074500070301d05104690141002c1e103c5031031035800b22500c1d80a400b021990204001840b541e0a40140d4204411040a03014020500700d0a50300c001c440003942d1915180b00c04401c1100c3c40861 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 571967446 1250 571966196 571966211
    0x306150f030105010e1f0308033603070b0f0912031009050406060f06021641010219020f09040f051002190903030c0201181802031005040b13 62
    0xc8aa191803280d56a01a00030052542c56150400c884c480c11030351032440d0300c0c250100301c80190302d103880001184d43c0b080045080d40c0f50310f11040c611082074000f081d4459200381401faa4510700202c26400248404007540d601e13001402c0000a400b0010f00f102000018041803141103800006d1101070345003812200c07034694a94580394910003c640e4015036187d4200f0081c8014490a03a0000048030041c14031030a80507903400e004da8840054116008400b5040441040f050844940c1e40d01d141d221260f4964044500c90b000144a24001481800d005800742180390706580400150300242a00020848040b0b800c0d030024221720109602d8078040c040e40b0340420200400980d1030b24105501030255428503000100e50b00094111a140c8130303195445080c480c04250246124405503600750340d842200c46819001980c65040c1f4030f000341c0e42031400c880c0c001560341c0001601000100341c95009a613a04007004495541406900725038480c62400700d01d2801583c2d040041820008104008107929 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 571968696 1250 571967446 571967449
    0x1030f06050702010e030c03041701090803010b251b061404060e12010903050304050c040207080a08130c23031626030703030501050111060405030406121803090503100209030615 78
    0x40011003089200c5d4400070488000c40352000c4080c0c8103442941c445e1981e0704131008940c60a03505030b5030010b40228420801401035070385040c0108100c1c5446004102c0d1011a1700555048141044081d601030311030303001e081003d1560408038001810780c1d1500e4281900c9956651115100358403541007401002e10f0714000350b484540c1c1c40103181043c03d000300015040c9007405040743c0c0c02120115864010488407041c02e25091094411071034104e00c005003070503080340040c0c2d00782c0d00207030500d040840e40504010029507036110500c00783c018801d41c07072198108030391100380c0c507503002412034826000079851f203030850100d10300e0300c04480d948030403514031005000b14001800d07840382e400882800000780d10014181c0540141c0d040784c50071707611901040c500340415615414142c0d0002c102d170704208020040c4622507000d50040360500702001418805030303000c4900c0c51045d010101d001c50340404c001c000d54502440002c1c4114001d480552030f00145000094403290b00030700b1425005001410740d03006 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 571969946 1250 571968696 571968701
    0x629040e07030b01060906020706020607051804240501030e01050f060f060d0c0e01090b1c021e0412060e0303040b2a0a030b0f0609031902041404030512010e01030f0605070201 77
    0x2e540003040d0410550b140e020081c0200c10900039900913124070500016114800506140305100f2583da040c24034402c09880684011424180303030740181c5500303081c0100d9902841119019038025181141a0f26000014043d682490302001d00361f450102005030364800750310095401007003182e40c030700401090400a1800d0040071502c00c280b5280044c10030030076400c900403e00503142622500f482c0790b80c550fa500442d02c030707141e000456880f290344a03550303090080e00a00116280780c420b0342e10440100b001c001e002d8110b43e000b484007101010b40502844010b01c03460703101513240406946145010388802c05418005030410061045109001c0094401180c1c50f4a171b0805a400c45a03551180f1200207014056038500244100702d20809889039240c02e500b110300706c1001a000e48107805100340100c1c0703d240e10884c2030360041e82b502c10034a88a142c1825003489a440703503c0c3e0320384400002d108022030101c1600030380c4800b00e040006201055800c20b000081f07551101c2c0c049869510072200303d01 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 571971196 1250 571969946 571969949
    0x70302061206031c050301090b0907200309031f1103040c140d060212090d030c021b040f0510090e0607080a0c09152006060f10020a1a040629040e07 65
    0x419084d00da260b4026511000171812101c505400b400f581840508000801c807080d00c0b0000861804250449100071f0f08000021194255054a0900c82294003280c00c0c100800301d40e4007072a0709208542012000340c411144031242c90101c280c114a0140d64401900080b40103080c03048851420581007540c0b0f880e1010102d80d84a081507483d5120300035070070032062003545d05503098020f80c0d064171040c44c487c2c8100d0301e102e9002e6004020a44405100c044e0300303031b4a1036407a6041521005007039010782c1c0c240949805040ca803811010030702c0c0391044500858854182c00c80381130308284284044594404042904244038210000c1c82c1524400d0543da0429143d20041200711801c1c403002d6140e8205440500720b01080caa2641c0c07403d550b4100644405080fa1b001e41d00c2084190040300a0a2294210542520500484044240c2d5031100c2040e0039040808411011641040104002c070070f002d40290680500d860020500c01c02d8900c504840385c00300c04502a650703641031041541c004000090 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 571972446 1250 571971196 571971223
    0x1306170a03020c061c0f05180d081602030c0d0503091b102f0d030c020a052d01060e0103020f030f060402150412060c110a08030105060d020f0307030b100207030206120603 75
    0x10f210141d01b40f000140c5401c841c000708101070360006640103800441c54584907100742e5503c1c0c40c3d40e555025404c000c0580d0001d0101148020f109022104000b0002e0418034809515002e8691814984071031802282d44500f650100390303061201d072a030301c8003030101c103140c921400d002c010140f260805800404001248140903031290320a04072224002c18182c11200c80c0d654103000e9108840000d07a650400e40300000c10b1a0b01c6030501c11500340704003580c090f902080140310051303100881c942d03509440c1541c00516003004d01c400104114502080390050100042d000ba203401c141d00d280700350716800c008002900440c4000d0310314150541203421200034200c90040450079480d203041910082c6082c0001c00b01043c030001c0384200300c003000184c0342c000c0365001c1803a900d10382c03d21003440500d402441c903841070b064003030003d22420340c500b05c0558401e0100c2e42c1c00043c0c481401e010030880c82c07004003020301903400c0841c0500c05a21203c04075200d94058002050803520349101083c58540e10781c207401c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 571973696 1250 571972446 571972451
    0xc0507060f061809020306011809150e160b030f0403090504021611030f0607033809010603020f07030315030803040b161b02040903030b1306170a03020c061c 69
    0x1e0400304456405001640c18049240320240440c50f101003c0710b4011001940c55404003004028006c0c81001401640840b0100801d180e6200d07a948030700c6065400f0b1964401c2d48a00c000741c01c4070000c10001d00c040503425841c8a0300c0c0e217484079071402440060500f41044421100050515000301103110046c03c02910856494400000558000c82d080c1b504480b02c118503800405e240c5400525103800d5054a0050080c0d80c841880a4005142034160100c1c2e0704c0140ca41c4805000502015400d6128510504500c4465040801c100b07980140c110405040c0b0510060f00301e5400001900c0310160b05090000301080780d1080c20200c1100d552004248440000800c001c00138050340c0c071402440554075004501c41110425961403810b0582c41503444c3c00b10940300003520303245d007140a800d800b071300b0005141c0e846d0402189e070120325002c1504400b621032504010060800d42c1580c0e0600400001d0f02d480c154958009448040301c0c0d20241c8905004511078149074418200302078a5100003408 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 571974946 1250 571973696 571973711
    0x507030e12030a02010209090108070b0a0f11030307030501051306060e1309080301080f15060f01081801060b0a0207140d0b071103071b12031403090f01051519030b0a0c050706 77
    0x240130394447c0384080d0203001e941e800011200e80004e6400143c03021480b0581c00e058071103800700d8a41016400010804c4111040c0098031002400214002c680076a80440c556062005001d11072180b00507480503145040c03401c003c403541c4002112234801d001c65400811085407030021001d030510500107004020004000940f0000010756181000e010784240c8208030000b03407444069907000c03241e0a03005070101110140ca9803141500366845803a01091000e11400502c0c81400c40b4207581000405610000700041440d0301008040000c0c51090141800b00c104030380850341c010329031140200031080083c0880c0c3d215011300d94907040c10303180c2c4086075160121414980c080301070310081408461810000446c410314a00780503400103070103881c0d80710303000058924240030358001010000300d4050180000385484003800b80718010340d00c3d9009100b4009900c01000316042850500b031680c1c1c80c2e40501040011100810254402d8010310001005120340300151494400c00e140105021f241403103 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 571976196 1250 571974946 571974967
    0x5090312040f05012706200118020114131403031204050607180608180102041a0304020f0427030c14060405010c020d020a02061e070c060206160507030e1203 69
    0x10101c103d4009076950028000302907001d0415901c5140d1007400c100c480301003440700c64054150080d0304a9000520640010001c0000c2d00311403000303004074805450901d043c8259070740001030241402c403c6d11040d01d888030b40401045020000e11a1000040101001c50007a940500c00d503140004a1010030000d4074044c5400b80e03e07207004491000c08107242a1101d00400d012190150540780c858841ca00c8a444009800b0b00c40c1c100c076a04098559001c00000c05c0110f04007600d842c841400101140d104d04043c03040241c080c2101381d480340101d14105513082c0c1000f03140b41642d8544025000384d055420a81012114000c0119010b440c0780c6125000b91a00e00c000034083e40b19030301030b4008200f02694590701b2620740c45040c140e0401070348010003810240c40c1110050650185410101044041c0044c070540c098102d56000d88040b03100040c200a400d80602001e07600c1042c2005002c03c40700c0c1c0400190450068003009000c100b164400c1007a2a00e038906c00880341d03004c900440e0707141d41400c03c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 571977446 1250 571976196 571976219
    0x110403020910150e1503100803180f180c0f090402030c030a0b09040b06041a04051810020306130905101b0e030304053a2906100509031204 61
    0x700d484000c03d070700c41c200740c0300c540b060660031065500185205100c8a542c1d2960b915a0401b03490103c04600c0d002000411400c10801040c0040c40d040c0701da01d00000d40d0301044944030021224a000d25035881c1c04401702c1240380e40440d80000301031020b6480344241001058039009180b05190841d20000030710510b2507401c0003551103030060800a0003107001c5542805815032040d100180b07410b00d40c4001c00e4551030300b80c00101c000f2003240207044802003014002401d071801a1840222002866183c0b46103a6081c441008000e0003041d05500d1403c02c5408944256081c480e00014039030b55451100c104003041c00b40b00f5964051500901c0003010b46910243d4600442c4492400b1a949408030811418040150380813180d004203c44014801400d903105200003519072034180030f407420b2644041103145018408d0b094003c1e80c41d0105000d100c00c4180300503000442034408095080b00f0012559680604110500d0701d0385080c2741c90300e003250082440e220921120a0901c0d0b00428040380514070700 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 571978696 1250 571977446 571977449
    0xf060305090a08040f090b040c0e0103240f0e0711030304080a030608030a180f050303070602070c031202031e04030206181c11090a0902030712030c151505040b13110403020910 77
    0x8001c10124494408000403270303128900840110f440242c0c01c02166000b82d000d40c850001e02c0030006040d4106d2020001c2200d12500506600605182c0c1800444205003885500052600b00a520300c4030102e0075554030f00004000900a400000c2c02c034044078840d03044003001300310500440c0d4681d0b4054402401c01c901c04410084400006000020000100d00d104811100050051490815982c46560280d0b014000594034075480f004000006030180c2040325081c211a8041c540322039080303900100c909400c40941c0008101407100b4005a59a40c003101c21884400100c581d4400c07415011400022007a80700d134484c04d900c40c196400780469030009003e081d0045805005941e100720b0030701b0891780040c03001303034266008503414402040d215143c000c000e8028200a0280c08141c3da400d0040ca40c60030000002079152000c0d0300300c08161843c00e0000d49022102030003a0000100481c2e000b0890f2105144003945480440c0c24010030301088030091900944200d54500e4602030051003034419 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 571979946 1250 571978696 571978709
    0x271514030d030b130f02070f03051801030501060e040507021203090c011715090405100216060e06010e0a0c0c0210050301030302060a09110f180a051b040f060305090a08040f 76
    0x1c402403604076a1092081120b40c201c001c04049014144012500c01005644400000b00c1d82c04c0016001082c03074500101000351080c3e50307031555501105511100d280d000303800a4141070401005001c50780d00050705c107604000a4400003170540d90090220701c0e09008084140030701030000280900340401092418001c42c1c20b8a0740708001d01c00b002c03040a1401b0031a1000b81d8945000020b103520300e00440c419070814040c100301d40c01d1400b814100f008a910241c041d03d82242c1001440c02000018041c04210800c0c506c0902900d626144404030000b0005002010705613031001c4501140d0b0040c0132007541d00350041e00d042d102104076480074080394020b0206a0140c0328001c0010134a28185c014040007541c81000384e03407051010300a03c620660301640701d5074850300a01c003d10710003138645000c40c45620300034008034003420040080c6c9044200300d0450100242e04000610140e8401d94071b000803541c0a1600007600c2d41e41c4083c0078288074850340002c210304030001d00018451419688001640d00 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 571981196 1250 571979946 571979953
    0x20031918080303061809070536100e07080402130e03030f040b09120f0708070b130308060402130e070e031005061302070209150a0503010e240127151403 67
    0x101900c00c041703080c0201d441314040c0e4041a000e01c80750030580b001a8052174941d480d1000300b081c280014a01e22112201080c400854404005820300c40940001c020002081c14280c64145080c00410205004201a002d403100070301071424068240e01401c410b07a41d402c00d80b40c41e810203c0c40b00150003c155020b03100606981c010404000010400c07501c240310043d6514a00303006400010000c0d001401c003a02e58820900070a408a40c00141e014032914695481d11540406440e014103982005010b940c022881400b0030061450041104401ea8440940038041d913507500c40e00301d0708030143c03085064041c00b41c40d090f0440c642464111502032802110711446040003900c12804034040c2c140040e60249240022814240034660340c40e401e0080079210301c6130242c17103d011071b081d40c0503c010681103030701c041d1540c0c0d02c5c07045000751740074244400465603200b07524100c44100c241e05004054003180c4640da103001c0240903036500a031030030450103410f040856074230482500316542041070385000b0300 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 571982446 1250 571981196 571981219
    0x10b09192c030720091305010f06140a06050a0c02040e0f03070803011d0708040803130503130915050f090702010f06030311060906040512090f060711012003191808030306 75
    0x203002010513420b01401a200c04400d58508089800c0941418802c0e1140d540e0765105c0d19456600e809001c020309406210051891114414025194915030040c0c08000301400000d072202d07442041d11200c070b501203401080082e070014416041000090308548103202c0080d98204104920008e14122240b4012130b801c421056524402501400c5511100080c031000000d40026090801b079500112180e029004c002d80329650585598407001070140e02080514040110f0303910b40c0100e9603940c001c01802c005071403a20000c1049100440d546070b104045640004111500c00d41c01603004180c8028244886a500c1c1405442000b8002034000f56008640005025200001d881801168880c6c0103002159408800c88880c2c0c0180b160140d010072a403c00c8145c1d82d6801c0c001e401e082d40110a100720b07101c0c555002612030300035800c110790305083c07825002c0c46042d400b105480c001c59044940c401044e03191141245c507802c00010000f100301080001046030031002018611500094810000c002c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 571983696 1250 571982446 571982483
    0x1003020409030f1206050a151b0623270c13050a0e1209060309150a02040609050306070c030e06040902040305030325020c2205070e15340c06080405010b09192c0307 72
    0x1030011580c100c24514100d03031051103a6410b6331240c12030084001039482c0d2800d2900002c8158429240800185450b030301030140003c518803c16803001501d0006080d40d040c10346100f2400c0c0141c03808a0f106134004000510009020701c59020600c0907007440656030300c2e00d00503180003904140a8040041c81c9081c0208071804c0004649001d040c0648400100140c0e5540444a1030800b4544d00e030000800c0c0070001e1034030818000780c4041c511440166403a4a800d9406100d02c00380508000540e1103080c60400c1403a802082043d6101400d0b9044248423140f940451117044044604450709442d040c100018507030f03c03403a5a4825041142c1c00b0300c1c0c40f40c544004a142d4018810020480ca01024940203001240c0e4074065403802036409030301814000b07480d1079000b40390f03031f0f0300000104503840100300401c00300f803145a9181c02c04903000d020a040c0113290710b10049580541541c1103981b90481c1ca2003030811890040d02444203255074141a0001402e2510f0787c109a00495142c52000030b5080c11 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 571984946 1250 571983696 571983761
    0x70303120c1b1b1e031208060a0902130f03110f0406270e010905150106050418020a0c05030a20030702010203121003020409030f1206050a151b06 64
    0x29204080102614102a4031080380e0084150002c1d243e4111510000030459402e05400d0102c2d5100e042051006145040c0041e284441c0c00715001000050002c001650361025869020340b609070000588503001c80301c080000c2c03402d9800040043c48900400810000d1000909010003401e0300c600c51900040703c240020780700c2a0090481e40e40e80103035104903424908507554020b041900002c5950494113a034282100c0c131084040d40d4a030000c1800c0c070800505194824010443c906c1c0c5249014038000329065118200802c0c528200d40001d000030240d40b00c2e030b90411200307810100740c0303a80d40c03102c02020303041d4401054000010925100181c5080e500403043e505500c0d010f030003840c540142c01d03940c0700307448500514143c0ca42c40804004800350300d4a00c2600c0015101e0748452192a0004d14040c05006030300603044001814040203102030303111007804004551142c80c0144462a100b142555a241003040c8264181c03002882c0b00c0a11565401c00800300d403d00c90401008641895440c00 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 571986196 1250 571984946 571984967
    0x50f07150c0507030f0507052704170d050f060f06070b040803180d02150a0903020d0e01020a0b240105190810080604050610090e1f0e070303120c 64
    0x848001000038003116006400070304110703200300e0a44190980720b03541c14000348050201550181c0c011b08081c0841d04211400d071008160481503080e8180d050b440c090010b40008100030244200050303480025054401621240602c2210501540c41c202010400034001111709510541010069006504183c3d04030b44066400c5088004140d403141c07035114581d0310151076402017a99018000210311001d100b0083c01040c0c039070140072001a80e403a40004c000c0050000310003c0d180134400000203400080160359207000b4101101320000c001c0050317040407460b03040504a052443d00300402015000190800c0c204011445080c0320864001150180161416003800c0300000d82c8102d41c85005161080d44009031140c800e042646900b88a810f04030183d0302219107074032100030f000c40b52250380400c60240443c8901003110004814505980f0350340e0301d061304031000c059481400491507503000501000c86500c103c0d04515968034000b00814042590702c0c0e60740340750908484045204a400700c4 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 571987446 1250 571986196 571986209
    0x3f061d03030a0c0207030c0f030b0f0603030d1a1305100801050412080c091c020a0b03060307170f1912020601050108190f0606031a030d080708070c02031002030103050f07 75
    0x40c11642c1d00c00300d600c02066003490071000d6204140e80000061010401c40c00581451104054aa46586401c604e120805803c041c051210241040323100d4030000b0036240000e0548202094510340c81542084036001d003465039070007407030703080c8604103c0903241c2119000e204010103403103409a452030046e003200c0003658010050850201b00d0b450440c0304594090f0840c41c00c002c01440c100034100003400c40c2c3d050042c550208000c1300c041006515015020800600b406800c0d14558648100082d840308002d000c0c0c1489030300c01c0100b0041c140000c014800c40e240000c0704540b601034103510805c0045130041403c9908440117803002020900c0031405604071a41a11040041d407a90b40c081e0384601c1c035001c00709020726510440310713440b04801e014150041034161000030b1060f6200d8140960ba000c4a8146406507001c40200001161b0254445900503524030f03051440782c446070300480ea41520f884001c8e5043c400d80500c01c880040c01da000b54100c80c170903406c07160310780d50361702e4443d40b00d040030320429 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 571988696 1250 571987446 571987453
    0x801021306180504050406141b030c0f0d09082817091606180503060c030609060a080f01021c090f120216080a06050c070c3f061d 57
    0x300403250080015002c40508100c1000c041901c40e070104044600886060b00c03800d849000c0e5a0418021038a0300b5000813400340e0381030b188401c9003c0c500e0284009400740c0d40e0404000b032180c005102c41c0c000d84074081002001407008480c0c6003003110b1203400480500c900c2010360b903075020303500351550518419040661280c003041030404e40e9040c13258100070011081d80c01030f42210100c9120264070f40e009840c060b10390418a04031080700d14070410341600200d01a6005d40c050008403010001640d61000e41150f000e292903462802164a00380b05902c901824860744031480781c03025042d0054041600150700c4040c041e030751400ca400545843c517401521030001480d040b80868220003611100150900440f05141c1018401c0201d80966920040042e006840c0020400283d4000c0540007041d5490190400ac41e40d1594080b0801d28403c0c05548080312a031241d12001c802c61034002c9100c0d50081780340300801410380d0358080291500483c0c5440c602001c10b90320615175001c240924944034000c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 571989946 1250 571988696 571988699
    0x30606240804083105040c120504230d031b0f110c0a12050d02030a090b0a021c050c1e0a021306050316090b0904080a0c021908011508010213 62
    0x1a10301c5030001d030041c3c90b00c0b0010407549030704030010700840d000075030380c0c0006451422801600580702203140e00700c035129508026800d01d405a0040e5002c400304401140041d5980791440c0840c070210b1500b105800780a5110300106192401141c1c0b0061299079850621000c035400c100908801d00741c2c0132041c0860130508007102031511460307622200f4150003084905081200c80000d07101007059000740108c11051207000c08100041c4241e0f81d043d144c41c0011810031020400c040d0102d0039a0086410411022502660061007004800c46000003042c00700c561070322041d130050a076271100751150028480c1882c450741d104582c443c200705400d10040600311181541c2c1c00c103c5520b04c4402245041a2103100c0820142d50a0100cc0c0100b04503115a80100785800302d08002c1d503800000d09482040364608000101c0e084c9400c40c0d0000d2400c1c81e0550403400d42d40300140b00c42c178004803051080703561031102062041056008601c046000040b503044bc2c3d0303995055509138403404041140e1103d98a50 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 571991196 1250 571989946 571990019
    0x171903050d1a0405090a1104060806041b0b030c071109011a1b070909021e010c17120408130b03060a09020c030f071101030b011e0f031113030606 64
    0x4a82d01030515907000141c4074150340002810f071202034440e034041d0780000079082c0812040c00700e00d4081d0102600d051003028942540941c440ca001000074100c44d1001c60820302d071200498000001e4080403504a4590030210356a2030180c00c03202003251032038000c0701e1144082c40d0508100f412151010541c9060b20301514201800b6044280000c9407400d5204004c0340303540c014401603010384280140007840105600400007011845543c0c0b490031014542c1c0e4107401e903804031002002035002540a0900180c1d514038650600c580d41d40c00001002000a1008202089004249504c0700781c42d0a1100ca0300d0700000542444151840c40e400034815004110b00c58203a0064080300fa00c2d4819203060a8403a0405110760f44501421030340b00c0004a0280095a0140b10351000e220082c40e01030108902c1440d44e584010034001e1100510040e141014121442500031802c143c4100e0300041d00e5244001c5455021f03040c6004c22913580b07081000100706000e0a00c50281c08481c00c5c4004145c1019000 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 571992446 1250 571991196 571991201
    0x271418010b0a030624090e01030812040f120807080127090c0e07030b04061211090a0e0a030816030b01020d1107120f03080601142a0106171903050d 65
    0x70318034010f01d070301c4060010f000d00b5100c801d114802c008042c84101041500c20007072841d15a0b03003201c1c5011b01910700500c08070329024151580844004c41c0206e1a880300d04240c1000070039841d0003022031000c501c1c070395141580951610701030b025a444198060341c0b41e48407000103903a02c01c2c170010b5070f180140c9201c0e0032801c5a0000d481150007401001071441d21002c0c600c00101c0708440d00c2d00070036143c104c0d501260600d80304070f4000f0b0090340b134a61111146541d810102c0202c0102681c851070454001c1520308160703a00000000b030800080ba0411103580c50040c1884c07104a5504803801c440d4900d0345003480c001d018040055005a025004140e51034900741c03075031500034601045501c141c11011910400c8509486002ca0080e9181d0007006c4440c540109144030003441d140c1000091011080e140d4218070a803504022601c094502c07144000c00108454030201c010032065600300040015540180b044030308080d40074a00760380419801d11382c80d01707000c01250001800580104954540c00c1d060750b = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 571993696 1250 571992446 571992457
    0x18060904021b1605091504021309020a0c020306130803040f2402070b0907210602090405070e03071d01030b0a020c07030525080303010308030403271418010b 69
    0x900040c1407a030309160100108a4200d10810b1035804a00010342103407903890103400810007152110701e04c1c60117a9517641c05c42d2010030328600035900828101000c22036070750030001034410190115165044c9942c014255480c00d40140d01a01401004c070f03400704081c05040820a41000f030041c91620703159a5403840291050043c2c51085410882c0c20103655010781d041d04090903120090789410882c1049000064090980070895226120400c5a4043e501c40c0c44030002c50010684c110120600f81000a07214030058194014074120421500c6a0001303025500d0340c0d400d5003215021a104c4040c01e8100704040d1158003414028001040090247c1c1546c03544003410107009401c00c28041010b1345003001940080701c943e0001155010f000f003d8001c0b11180100c5000303414070031403921128030740b40e10040c04040c01d540d00003c0090300741070040c886442074484810351841c01c0440801054940055400303082c0d00c818490100c1e0b201441c0062031000610052120010b07141d107400c480364603030b0b80315 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 571994946 1250 571993696 571993699
    0x2004051207080d05030a1a010c02150c0105040c0e0c0c0a0609140f07090b03030a09210b040f052b08180111040503010c030216060504080f070807020102060c180609 72
    0xd80078042880c41040c0710302e040c4403070180c503201e031a41800762004080e5090b540400000c043c01d40250045681e0000700d00a6040d0180c6542c9209014000000024400c0c0007010030079600309020f100401c41c4458038603044402420601146860b4507060040c2d07440f41e102021510f501c80c01455001c65407550012001034412042c1b80521004503c020741040016010300289030400c01e000c02041d4014000c03040294400c901452600e5088031028008243d030780a081c2d4540304100c840003c104040304024030164100f0341048040ca45882c202c1c4103001c04050886941c09240380c142c0c045001c200c02202e808c071240081c690081039150003107034035000043c030300342d84180044914100e5050a03c00c0d42078103001044003c2ea2103003007200785425500103904000406104205c01c0b0000050401008500b59004001240c1c0d61210700f0a40e90500655034410f030b403500c000234440c00300300c2040000c0051030300c03c0c0c00b55841c5668412141e00540110011440100190b0040c2c8605141500041182c20070 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 571996196 1250 571994946 571994953
    0xf0607080d0609050a090203070f050105040e1506130f0608071704050a1401021b0d020303160509060a030501060210150501030e010e0102040608010e0a0912030f022b20040512 77
    0x142c48081000b070361350580f059042c070380d0344000a10643c10180004c0001d04800f007541003142c2d00c0c21000a049109501c10401025414004a840044901001c001042e80200010b03205c80030f423070348030715020705602c41d19004110b28680010054021280c5ca4410f008581340e81c6c601e2191482003840c00f420060080f113890251465040000d5100510242100c0130b1400040e191952200c03500c0140c1844910039140751301911500107403541c00411694012045112550014a040710548290040c0b1121a51103031011443c260071640c15840390b4100c42c0150300b10380441500200314000c4410315032072207146072444030090083c6d5009401281860340481c1c00001d5000b5107010b07190032030708036422490000e50f00300010461005070f401c5482e0001800d1108110142e00780d500c000d01032801c280a401416140c0c454101c1c445296415913000ca12011440207240000107405101000460021018149012020b0b0290070019000410006119504525290904d402c003e03c0e482e121035034150521 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 571997446 1250 571996196 571996199
    0x3100c030b0a0608100b0c0d05160c06051201090b0a0902130902040b030a1125020d051605010315030c030206090d0c030c032f090a02130e04110f0607080d06 69
    0xc444a02042c010122580c40074000d042c4421041e10380e0312036a120028500c014050300d2104040858003100c0c0c2105410701d80c0e5650003101c8541811000245c010304405015540000d40c81c4d00900107103103807076410092401983c0c0703a0744c0c0981210401021250031807242c220600040c0c00d03960040507200161411500300d81e603528030300700070b0b81e01540000c48011800700511207112141e0080c0c1d06003610400f103040c01e10940050260848104122500c406941c0002e480c056486030110320b1540c13500541966904620724403e402164818403910340040d150100001c0d419613200340e0f00302540d904c0101420618515007c02441c1e0b0001545940d00c400119005000580f0180196001b5480303060342a21582c50340c180408200888203480c0362140003402861300a1115091181110000b110500700540781c200ca070305c0090043c4801030030f10030042034000c110b02c80443d0360540302c0c51084003a00410b90401040c01005031a01201907080b0406001041c0000d0081000d41013002c0307201c1c00024440e = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 571998696 1250 571997446 571997449
    0x50105090c0723391c020105040905070c170405030d080a020417061b191d060c0f0c04110f0a05070519060b10091e0f0303080f09010b03100c030b 64
    0x40070032200c4292140c05a1404800d1101c8110140890b0501507402130010704050049200b805c40c5094051007404540d900c01c1c02c5a014600741c4010f0729403403404115528140d02d01600b92000c3c50381c190340c082c07940c1d044540d0201d0050101c07000d50350064007806c0301d0007000d03030700b994401405032400c50010380030310010a440f80f04100011001000c2c000030f04481c2081540c00d4601d9205030a035651048017003164081c021005c1c2c4036002082003602e800f0040c11441801d81c03219002c000c2c601548210001228040714400090746141c0e04841c0c000da48418041c441003000700c4202c41204041607406200300d21240703030200c024140041090814034501079450b0354280c14600c44081d00d2500042a9020070309108483c8a103034002402030751a51201070002030050025606840380114103542003000e05119507075401014010282c080c0641042c80d00c0f80323005002c0d12011201a02034612800001d511a10140201030800340041c2c06008140000500980a82625280c01c024142c03030f0a0359549a = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 571999946 1250 571998696 571998703
    0x901032013030318081902010203090406090501050a050103021201050409030c0b07092c040206030a090206040e060405071b020904061b020105010810020c2a091306050105090c0723 79
    0x5000034400500c1c040b0705618002c2c002a04811011240b0415000c06010503600080d25050000940621003110419880100c1c40e5201d403808454000b4100300000030020b40540240b41039a1045a0601d0015141c50044040b405400054000c48030039900410007800c2a07400510032900130300d0200c100071040d40310382e42030b00c0f026902c1d0070025291840810401c0e903091112015080800b2050a030080380b0000e920301d805d400b41c8040c0c0310340300020106a0590240c0d0090300705603800b904242d1900d554031405940801b04480311784c00742d800c01e00090129071064001c0165900b9508001c0e44241c1e264091020040009108940690384e8150034107070220301c0c04501200703a9282e0700110303031581850700d50381c200581580e003402224018482c50b020041c010910249420071814880036460f0501d80c1400c3c034105544580f500b10085906000000410341441c120f080c0c0180c40c24003c503683c900900040d14003c4400030210181030250708001031860140300c0401d04000c0550b80d00c0da01040d650303400c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 572001196 1250 571999946 571999957
    0xb0c09060a110118030203180a08010608070e010e040210120207060501081e01110a05070204020403080c0312010f0b030a05040c080105151f0c0f0807061109090a0b0609010320 77
    0x800c40088094600c120240140d41402104030418035001019030745c080d5076405550703c0e800343c5c402c201d141e184840d2201e50060008001b0784000303001741e039501c100c4180c480a0a0040682800c13190717002003204040e8070009030050b0f50290102000f44a03001c3d08480e1198050401c0c0000d0785c003003104e000405e025014903800307440040050480c50040d202ca80c201042e0b270301c011904a03410a40701c3d81c10715500c0c02c10f8410b080351a0602d29030324125440010300900c103e4000428541000c9007007110954008040c19000103640030444030b0340d0302e0f60075402e28004148955030000500700002801c800140d00000d4000c0c0c8245520a541600c6614140c02c0d683c0c101c4000e070220700c2c40804d480c024a0008140d00a801558200b0f101d0b0314001038004081d034a0f480005840d21007060180002c0100302012940d02581100b801c10500f040d1400b2446d19034021800c4501c5002d892011803c1311400380b1a038001c14070000d003c1071400b4040e000641c003a26105500d064094203030f400540040809400030003 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 572002446 1250 572001196 572001217
    0x10504061d27090604200f13062c040305091807120b09010e0411060d0c0207031202010e1b030703020a0b1315080126030a0c0b010801090b01030b0c0906 67
    0x8000b944240e034464207036070300240000340540c409010702001c940000c5040d8880415004482107140440010a405040c0c806961b500009a1003d078101110154088415202c2440218100190712407450181441c649400d1003c51400c00c0841d0009005800a0a07102d2014100c02c003801000306d4040d400c50000c072071600106040101745c40c0320300b60900c9040005101102c03504000d505200c060b20360400c0080c002801d4040707180b44052745954580640312840008d0707006114210690700c0094440e90349101c101d030b1012020401003040c038010b010398a05000c03080001c1c0840700150700c05c248490b92000800c0c0d0903001780750001c0056150284500e0241070f9000b60b40d951400c020b0440c0c0200a0140c4c842006e60304891134240c0c050744d008900b24111a01d9007250540100c1c00c41c14501040b100701040c0000c0d110000b0048000c0d5001380360200102e0140a500919a0381d0315181403c0e03c400c0d05000b08107507510001400005c400052294100a03150003090600a6842c04075946038014450075 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 572003696 1250 572002446 572002489
    0x106080622050a2007150905060103050c030c011d10090b040b130f0803030408090406090615120509032a010c0503040c050a0b09061e190e04020405010504061d 70
    0x4550710f607050094182030310304100001804c036208001e0048601030f10b413009146400c3c90030b400c0c404070380d941c01070801e554200303040c0c1c4c5413543e507440c0282d995040a0980c80c003034020303e04040321541c061300c84694407603480000300348080002810420b90780c1036003c1c1003080c00002200418041e1581000d800035028011403140e4907200360501100c068a80d9126200782d9040c41401e1105500c007100340c0b504103900c10b280c1e5407510320030000280901042e810294141d450401c002600722040c2c100400000300c1c0c3e84404051040b48070b6800d06480c0c080358203040f9036108004070080b141c40500c2030700394402c500e41d85005d404900704902e03080d0394102d42c03c0d1f0001000407040c0414400d8120f111402403908940220800e4905084a1141c0c003030032850521807007011441c0d1001d00003448030700a0303102404185076540d24130045101c1010258510350b800042465002691a050910882d025180161640ca040501d030040448610300300d00d56090380f015100d410074460b5122981d0b01c1004268910b2076 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 572004946 1250 572003696 572003701
    0x16090b010806120d0503150913030305150a05150d060905011707030c090209030a0609140f06041509050f160314011404081b0609010b010f02060c03010608062205 71
    0x103010340e101420b128810358440d644042195000160102e0343c070342c41d080070760310384c0d4412450a0041a1070301c070a5401450750820081d0307020340e064108000500c01d45003006103440d58250f8010084d02c419002d030700050340c82c00912203403a20301501c3c07800ca515002d1161501303030810805c4094034941c0d400440029112001880007445102c0b10b241050b2440008042203851522401c194407014400c0083c002e9002400103082c0c2c0307081c0880040d19422001c1800300b04080c0c035007140c00601860445050f0f020310707800307800e540b00e001c00c3d001e004540100310140501c40c076596050003001e18510444051003102902804010103102920090840301408103080c0c0c034500740010903481c040e184d881141d140038a5411000b10034030307040d60480e03045040c061300d901141805020150f000d00d80e0403218424a01000b40840054018540280082e41d4034003c0002c400c0040e07079150026208281d50030790600c01480054407881003951f0112000b002000b05d4841049500281405244440c0429465108 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 572006196 1250 572004946 572004949
    0x90a2004080601032906010f170f07080109090b0a02090d171c020405130902030f2a06090108042015030a060e0907030609020d0c1e0504181416090b 65
    0x101760b083c00402a81d0103a6140b58500c092400c02c400400107030601403404410a1300a21640301ca6004240c0d03591000c2150502810b00c8034100d10442d821400102180d002041a562a004095400e903019013079144c941c0301d600001000e034212500f1030f46c02c64807190620340411480d0581c2c900750100d2581c5642c0c1c0d811020002e2200f010380c00c0c1c851034100d00400040041d622042c00c0e108984001c90302c0020040d00510020b4140301034a12001d40510825100118034030245076180c0b08407030345c0382c4a80b40c0d1150007000e0203524020108918045042c4000140206441c48103a000030135060b150402d549a40d800020721100b03500f5001d100113040402040301c0c06205204032009888100d880102030714042104658035401404000c01d259220500803045484410030003c9140e4020b5400f64213544650244a009401c8141042da903000000c0000701810140700740c07081003140441c2c2c0d002c0030f8a542c403222110b041030000c10256102e8065506410380580b0340f9000540300400011071141c05040 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 572007446 1250 572006196 572006213
    0x90f020a0608070318021507020a2d050d03080f0a060b030103140c09010e010501140408010f0902030d050703120b1c03082e030b070219050313060c02090a200408060103 74
    0x1141c0000d03042c2c24171103000980e9907503100c148110720701c810040c0e0320b00c110320220b074513030701c40b81d0008594809c840307000d1201e9081c20180c454030750f17468900040b01560342c1080000380700140d000500440c002102250100020708030840e40b058840313901081e0b903036a49450b00d5042c0c0c8240e00c143d50a0503018590344031004107200c144007aa5044410305644d504001c0c01c2581c1e08010311a45040c000d4070441c504201c140030301560002c2400200800c1251105a080e4000c0c01803800100d1003070086103038031400580034100390b8510356059940d25411070403260f1080000c0803d205120780c010507103241281c1503050181101c1100744039070b0319a030190405000e00d907150038240c509448182989040044d9411012104800312600650306660580300c1560607801c01141000403120304144108032018454004003e00c104898501c240001131780d40da030115a911109400254030108210204070514000e03000b0400224110020542c0300c2451941c00c443e42d440390303010300900e4006000420911400c0d1 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 572008696 1250 572007446 572007461
    0xc03081303030324091802030a0f0605161202090a05130b04150605070803180604060615050901020d0e0411070f0203070b030402061902330106021204030204090f020a06080703 77
    0x800c0280c00b0102c02c0745460342e8400c49014030282c15030b9580981081d0745017081d101b245a40c0203410748844502c541801c2844940f4183c0c00e451440c1480041000180c01c5082e2110400c480c0c0e403801d00141111380f01c00f0283d80440101c5500018001d40410f5541d585190b25400118a190000d840c081c1e81c81030006440d0070a060300031030103404c4030800c0f40f03940181c100e40500e0340c4486540c0c1e0f6a96210309440d2640400c9141c0921407240c60b08100401c103c0d507110409440c03800c2c550350420418018100d0705803107074819603030050b0032507003407044610f01440d10310b18100402000429030440301d0000c2511070b080050265800c900e450a01b10035400c1c24884c45014144020030903146203040e0300454070034030545000035050506440c00c80c580c0d07882801940140c4000c032000044240241c1c00907408041031815000c1c2c080b48039000047d440740000f440030b03c58401ca2640038140303441c5030200300c010588100140d465002a0041743c006945012501001d4441d9072292a40380c10316050081c01c94088 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 572009946 1250 572008696 572008721
    0x60e010b040b10052506020c0d090801050606120403020c0301110a18050132070f210206012601020c031c020301050a270507081605180402070c030813030303 69
    0x4440302403403c03991000445000c50200001d2400c3d00c0f00ba05001025105d2001003d00098800f01d484000c0341c602241490650038107039a056180e6440721415402c84409480c000e600c442e0070000f001002c626403030b00c181c0c454083c2c0141e810b048803020109007560351031645100d41c20303400240f10036000d411007030303400027015486c0c2801449410040040c01180380c1c2002c131080b0b00c40c86250503400500b900140340d00d509450518580304c46040c5028003000034146400c4407040b500e01c840040c1d0b9014901000e28070b0401e58001e003582d034a40707184207c255a003640d15403401d250301044c02c0022207090005103400032102000355500c5140c150346d4a0302c0c1394084440742029004200400507562800088002d80392841080c07107401c3c0314030903c50512203502d8454003525040c0402c2040f07054002d4500d41c4240da03511900d0380300b02020b240403a403900c600320343c1da806c90300100c84520342800c3c683d000d410aa0321408241c0e0f021038603900c5548440e00503002910461071219002e1013016414066907014498 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 572011196 1250 572009946 572009959
    0x11210f070603051504111e071502120402010513030c23100e010e010c060e010603021c02090412020f030403080c0106050f090f0703110d0e1605150a0c060e010b040b 72
    0x10314414000040300c000340d2240c03066032030314030902441b00050200d9500c041b845503030320074415011440702440d4001900030380f2201803943c500d00e80045180200c5070240035140c0100f445680f84c2c0e0064070390303411484009114490020001c4001907030403030200302400810180003175000309400d00c000c0110b250189a8002c00b02c4021300210f02d90000f03042c2c00001004d0030300c04009902080125038a10130780c04080d100604051490712599070652001d400d50f07000740c03502c0c0410040800014035000c001007000350844114070015000c503452043c3c080c45d051a80c41521040b80303206240d40e140d604160820b507503207900090f442c9a49c0700d003449400000e15095502d6001c04001074002090828014803865400d07615000192049102c1c2d03100d0398425266841e683d071940ba0038480440105500c1c5c196500611030b203161310488000c0d009105044400c010700c042c004800d00c6c0c1041c5402d401125200042c00362912010000901c140550b281800214000084680c40744c400c20041c0c861107000c1038000e10 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 572012446 1250 572011196 572011201
    0x1e02180319021c060f110a02100b01203306090c03040b1801060f050108010b040b04032009070314070c120f0e090403020102070c0801020f030411210f07060305 70
    0x71204200746001ca10414110385100849084c208040c0c852620f0000855103091050a5002d1103403000c1c00420007203a003103c1d030032503004044104031600e40d00d8180c081140300d502801e85090402c40b0b40c5007007074028241d601c80d84d5613140c80d84040b01423050200107040070440d04040b80504805540e40800c0480b8001c11038140054011500d100151000c0c1c4103806000020301c006074510403e4405001000003002242d40e0368003410a84455402041d0008410200004003079162005079000c5e204080c401500d010701d076075100352880902090900c50042690950509a51148030140c442c1243e45c5001c6410150001c10030306840008004800b440f84079460000414060b6005103076910a07418040303929144942d0540d91403c0f011669a8031801d0841000209036040d00078028003803040c1d15400100c2e072075003085401d038014211a00b488600c140002004924450882c982406c80602a1154540030740703614100311001c03482002032507101070032004422604118503402020031780b81c2003105d030 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 572013696 1250 572012446 572012449
    0x1502060408091c050f0d02010605030303060a050f15040b09100302070507090c180f09150e04060f14150907030e12070201140301090c0f0f02030703031e0218031902 72
    0x90041c0d44840c0d0103503c1424007803034240343e14142c1540c015000000ca80d041c0c0300c400c985035990441504171000650a1410000f4241400001c0e20b000d40d4004200c109000d0800303040c040c45c80c0844144683c401080348082c074102001c0c0700108041c0603445c3d080d50f0b4a14040c014409924110002413081600c10418100410703004600c00040d66009140070881c685d58990031642003041510b1100c08000c440c000044a654800041d81101e441d50400d00c410581030380c804144203164440c80c0c400a000300b00040014950b07501031444640e1240700010a5008505500280031003110381030b1420300010800059850301045540e407104852030248445080c008249403280182001c4007040c1c2408101c40d42160300401350344422200350803000e51290b956101c82c1002d044000f8040000c56410081c0c480c0c240d01c50300b200c0c8015070b103680080d032425046950440c01000702410401c03008290301844110300300725000900c2c5c0301502c80001143c4400060405d410302901c500b010248488203d42ca0005 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 572014946 1250 572013696 572013713
    0x605090f1603061814220813030609050c0301050c0c1506031516090602150c09221e1506052515050a05010608060f01020102120c0415020604 62
    0x105400c04040000201c10142c02401c419045015000702e00070702e11070700c07910766400341001804030107510b616900c94a2004c03c0c200c250030040c1544040911240300400c0308040140b5056071103e1544220a95279100c07242100c0d04070904840a07008440d00c0e00042c6400d010781768000f29500d4419141885004445540e5120003503003400c0143c610001400c1c0d42d034248030ba00c4030a600300c00100034a1803d083d2603407040006486580120b8804000850540d10010304290001001e140b50941e03610b910f08400000c2e008404150343c025031010128504500003984486030035803885010450308240c01d41862032007440c0d0816100702e480c141d00038141d81d0781564010101ca815050565440d144001c801c280d07400b404c0d0003514181c200b00b003000100300c600d074014030038030a01c0501044162210355100c1e081c0d4500303200368000115100c0c0402d90303500d024002c2040520050000602d401c80c020702880340c10314125400420700c2c101007020403410540c070480d00c2004005101501e00b41ca01a510b1101 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 572016196 1250 572014946 572014951
    0x60e120a03090809040e0601050a0e0c0714030706090606093233010e06031513091a04030f020307050307110a0b030a051005030705031908120c0703030605090f 70
    0xc041d02c50b80e01c00140990141190350301c0c03002402c1031101008034040c1d41e85c0e40f40700380301d01070286510031000980070282441c0e003401400008451890032000c1c1d2100c522060b00d10011045030b0100300440300004030203200d4005160700c603e03004550355140c01c8046080b582c0e018042c04030400b040b000c404560941d1060842c801043c041a51001c0d1103002d58400508101b070014a1004203101244803a018480740345003212200341c0c0c48410741e10202081c851749010507102c81000800303c040c0c0d2103c1e440d002e4400300400e5003e150000d03641c07180c2d8607150742c5413000c0f090320149c2c60618414032042c0740d880b54060202901a000131403500d8055540c1d00e94a10892a0280103030b942c0007140e0410b030396040f600070b00805084060710303164185020140010031003540c1205420820800005513814089041022240004e010300a042c808141c49155180040003c6035840410861030503164034036424a030040c800c28080d607880d043c2514024080740c1721034015500c00e50521781089003205800380c6095 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 572017446 1250 572016196 572016217
    0x1506171005090304031b05090c04030f030c020f032a0301050108030d0b2202090f220906060e010b040f09021c02070f060f0b040615050a0f0903021003020304060e12 72
    0x2542d40c0d07864120b42c110701072904000d017411040c407003041005a90141d4081507a404540c1d200c031a4680d410a40f00f64130944c13200600a0107031144203804a40603002078070000b4000740290b120010082e000a0900c620340d14102c258101080c80019640ca034440301035004003041d0002c01003941400030482d528003c002d01d0b10b00003510744403183e0160b21540c4030b85007082d089000540b103160480d600e4801a4201b0282c0600940814000c0110303840c000028a521001920071548804841e1041c90040c0030392345070542c1c05ca07880d10741c006040508038072120300a000c17006440b62114106007001800c20301ea5406900001d00500074182c41081244070b02060925101005a40e000c080c508040c40c44a011400350806241410940b0404425040300000384005c680c10820962142e1401510304c200250000c00100c0078041400001d006a18111609819050000d0055500e034006519104050000c2d00020f07004414001001180c1c045c26031900a000b003c1c0c00141203011036044e460040c0305499 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 572018696 1250 572017446 572017451
    0xd1103151005071203060e090714100302160822060e010c03020f0f01050105010f030501150309052b0813020f06030a150f06080601020d1b0309090915061710 69
    0x84614000c0c1c00f1148040da00806041072281211005001420301c0d100b980c0504400c80005007039075001042410554000c000c20310240d2141c0400d10080c2006480b0450a041d0708100c410300705030060b00048425442a01e0b95507032101c226050000040c00700340c1e10741080c00400300a001c8146c02180c1c0c0702c95401c080c82c3c82c891100150030228a014070f4408001554007072525441295801034002a043c3c41c400c0c0c0381c181040380e400c00c0440c00c55100341700b401c81c082641511120102e00c26048414a40c1c0140102d507582100c0224003101804d0f20b5400b111510002c0383c8050038907400c01840c55021050364010310840030290085201500c0b515000340c031030f800000016030410001d5110300c4100c008003145115131600c41c08080d901110034040d900100d0f201e040090010b610004508054280e40d95654450f80c206112103800c4e580d920104800380120800b011881d034155204140259008c1c2c502d24945050b003c901c0001c54000c0e070004086100b08200c5440c041000154841c1c0d40501101c00 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 572019946 1250 572018696 572018719
    0x3100b03161d060a02070807300302010b061603170f0a0c05160503090301050c0301080a060b04060b0324030111121302100f17070e060304051f020d110315 68
    0x61480c08040d5125443d409803000c124010460b80c006944d02c299110346003150a41c03a242c0303110300c0e150410000c0d02107160320b0425880307608038080c62000e000da03442800082030f000d4003103002812a4104624580d0f000401000c20f03424503074081c8810381d1250b03080380710b244141880c3d170003945800d40003012418000d0701c1d0301c562481c181c419021103081400300d00c03195565840903e8070302d80701c2d880302449900c21340c02c2c640454102c181c441d0449040758a408010300c154502da80e100b01c040c007141d8404c0c42c0d01554600380014034400030350003503103c4d4031040b0049030407042d401c943e102001a4444500d01aa15010382143c143c422502210202c0c41c030b130410303915142c0d90a0b1503001540083c203c0250405d01031a005030302c164200c01c0344140840d0607111100840c00c090403900c0504400c841502c00500c007041010680e042c85401035401030300603025149402040524070040071f81c0c0a68400035550b00040d0510068030300d20070101000004c2a6141c514103003d04141080c1c00c0c08600c0c00c1c81984010b44 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 572021196 1250 572019946 572019977
    0x206070f052203080d0212060906012003040902120a0c0806010207120c0510110609010c0c0f060b0d080414030a1518120206040b06030c09040b060a030602070803100b0316 75
    0x1e48500841c4d02010309507603803a1641d400400b9400024035400f5099840700401c410b482c5ca0402544100810b079601000c0c11030810a101c1b0011500d40d561000380000c00c004140441c15000408880080440c90007083c1400400c0100b21802e900600040083c40303c00d11456a9012828408864150b1810342040c0c5c1c2e1410500c06090313190348502e90220810655880540d0070182c400544e8400b1310a48800303a07101108503081e100030500c42000500420350030000100e41c008240c2e0074a01640c4001103061040001c5070b400050100207452940001c14200f2030171140000440405009801400d103020440e80d40c0308a880070141c0c400d14886c0c603400e1324042030b01d003480c083e90803e400c210b03244c8100c214044040c1d200c4400f614142e0b452540d80380002c01c1820002100c042481b80035080c0b9815980d01d41340c1a0032564058280781c5c0c0118102c000101085030f5001901c0d1150245000079682c0c1060410a0780d44070300f5510400340c03032100340200080d044403400e009070542800e00b400000b4014404 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 572022446 1250 572021196 572021257
    0x1d01050a050405030a05010609150608131e03080109060801022b090f08040f050603040b07030c02190c0e090c0102030403110301020403020d11030c0613050111031e0a0206070f05 78
    0x300502d41603c10048901d041c41b2054011004840f2925020020440d1070f41da41c64810000e40611008540c403103000ca074520049204d80d10005000d10135106101c054080103400a0003d00c034181d0009803a11300522040405205503001000340304000c51910a05605105c080d250100c3e039013441c500032004403900420203401c419001517121158010011132071900c00b2a940048c041e60051010001002c034040c00c20704100e90003030b900084680d01070390b0358600441c0644100040c120440c040c400204034891014204407140038031800c000c00146082c2203501314013080c001d004101950103a4003001550340c000c41283e050701d4209002002d41c02182c40402e0180c80760b58002900059031707071003000620209034100412201d003107003034501c404035450820405009540d81d000541c00c07009002c12a5600400101d192500d80320180c038204140d5040340c800200c8180345103001980c000900044041e1b05028182c0c0c0142907080c45840000c4002c07009003075000301500c60724116118803800b02c9990284 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 572023696 1250 572022446 572022449
    0x110303160c06150e100e1b070f020303040b07050f0a020906010c050f0d031a04141f0e040303020901020607020304240c151e09080f3105101d01050a0504 67
    0x3e04034940a07642e07070000e0307800c2010304507000303040d882d2500004070707541248481060107940081019003112140580c181025072248208070b941041d0944041d0058900384054001040a071190036107541c494113101303041000c0c25400da1865040301c5d0007000140d541650b4241c00c8802841e0040364003005280c0b261400b1f0041c01c2a9289202e004002d5600650580003690950f480ba010303800c902c0340c507600f480291024007180c180300d00c5515000a00d2080030102c1c054840e002001d400211556032000c441d010181a20103800086e00080c41c548a56010043e1580080032407000b180b41616182807040440410a074000050301c03808001a4003d101e0203400201c6c1e070304120b20007512146801140d004158a902d040c1d4030300100c0c00d06e241403026034412050082d41011015103064440c4055140b40d52040c0e85503542c3c00d500955104a02283d8000102610401e8007100c10750380c1848100912047d40044190411003140c1c20828208071121904036410401e007481511441c8004d03007a9030074000c9 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 572024946 1250 572023696 572023721
    0x504080106080616020d02070501030f02040f031b2403050414030c0115060203040b0f0705160308090a051e040902010e151905040f120c0e070c03110303160c06 70
    0x2804000b180d299400300e0722a00500025150040d078400d0b80b0401d0343c980c2d0841c1501e03005a04420800c001550107908407004061032418010320786619403c0171650404241c00541e0351007407005c4550302c200309014289014007101090b10b0300850304400764030080e079202c56990341010745410204041000004580d06040c030054250384c2c03a0001280038500038071140c80300810380d0f14000e0f400a00350303002000301c40590b1101c0644518104818602152903801048115001d210307241e640801c0d0421004107002841c4a44c0301c0650f140502d101300100d400090b085a881101081c00c217911394050200c240d90042000c0e10045207828050005840401550901903007104000074403484120440e0028504001c542c8035100c010540b058088800d030281c0d0050003000b200c0d07114240100f401c2c004110708001d00c1144824241030b2151400311741c4c2002074034590301144c03961035a00c04150300320401070840500000150f08610780603518044500341046e84005200400603400d00307202d0690071201800c1750 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 572026196 1250 572024946 572024951
    0x91302030408030a0b011e03150e070c060501060f0c11030a1e02150a090b0c010906150801050612120a020307021009080d030501060f0809030922110f0d0c05040801 72
    0x103042c00c14a4141d401180d10258903440e100f6280c80640c064000724100c40340c00c020301010b150700a00306500401c1d41100481e40072525100000d040d8000010285c85442c083e0b031884500c0c0210303d0210256101a001301c0d050124540d01605070584c0000c50f80c480ca500310741c2403001e1500c5540845e044c03580d11003003e00440c40c1403000040b21440040c102074000c3c03090710510701202d04100b00100d503000e40403806000070444034041000b94603500107850307501d1080e00005001a40c40e51200c045546400c803841c2c00407081d820400603020280300d069440a0256241400c58200742c51054980404c0c02080c83c0514000c902c0f80b150601c00c20503203403143e601500c0c1008601c082200540884402d00c54050070703124440b40f1103415807190069074102e4489480b80321085079880310603a0130a400400320412071100b030000031a65076469448a0014048052640312040540250429141c82e4034211049040030017400c141d2501080450314010518640013403040d945500880c0c4910603940030200ba5070 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 572027446 1250 572026196 572026201
    0xf0803030714070b07090503070504021c2d0f2d020a0302071406040b071409151c06150207050d0803070c020a171e060403080c0c0d02070f1202130209130203 69
    0x15002401e802c01c0d01c8048040700d035a15170b500204000e91041243c2c048011201040004040371240c0100b40c43d00310141c0c402e00503440340510310312448841e0701e90018030b40c0c03541640521048a4071071540100c400500412984281d00151070101c224108032500d0303140e0029411004074420f0341a00c0780c281d440141c50307082c0f500c5862410ba89400c20b070740a482060300c1c2c1000c1500103016856100c0d1030142c1003100c1e0701304440c0d401000001d2420302400200c1c0ba104003da01c480f80c0d6038408584109691744030000c0c045d4200a004031003000c0c1c090346602998420002800903940f01610182e9540c0c1c0907900554175524030004549a01050000039002008141c000c6a0f1800c4c07002d41c1c1d507403040c040c800c41d041144074101400750b5117a902e1828206411400101d400319105190140e40452110001c80c5071511014141d4074002c0c40c031401c200142c000007802d0003805561130244000384409403d00d0516035050700001d00a03c194140d0014a981c0054640e486440d0b034115128210003408085441e40b = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 572028696 1250 572027446 572027461
    0x70c081920031c05070306030614070207140105040b0904060f080f060a180305071a2e080c01050c011503032001141306020d06030f0c0f0803030714070b 67
    0x11044005101d00d1a0404040819900e5000080e03601c0c1c4101d43e000601031405140c00305005140203000c8108258072000c005c000b08030345018104400d01207122903029445c2045000341041d819801500e030303829415001d40c1d10382c0e0707002098400740c0e01b0041c903090761011000000340c01000190700022940010300c00c0081d9080700400c80b4295441c403041501c81554400034404100c42b03001c503003250543d0b4170380c00c1e43c00428415800761034514810700e01282c00d0a4584110040501b00300d81140e185100040064680050145c00c1c54070f12130b00703102d83c0c04030340d04140e00712b40c69906c0c25191030704000012902140001c0d09411641e4021000421140001d40702d0500400081003414070101200c803a03107000f921200c05203d644100c00b20081204069254141d029592500181e4191034080c2c080c00102680105841440021885541c9100c00320300f40d0314000c0c2c0c5c00045a4040c0c1c0404091880401180e1001700449502203660f2411041d44170404224034182d0040102c0038241c04498410080c10 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 572029946 1250 572028696 572028707
    0x40e0a0b09070e0705040b2214121609150b0a0201020d0506030c100807111b0306100e070507030c12020f01290f0a0e0a0218041103070c0819 62
    0x640044401c0e10541902e03800200f1485505440307880000d030303040004104045076500034003601d00c000200004400c800c43e003440e808800580080e0031003d083e8808641501c1c106002000c041903640191924103038412071b01d005c1682c03a104855a00b03440d200340c2820341030007124420182c449020ba40b130b110860703078500074000c0d0400f184000b01140340c000422060b15001408120100000305101e5041c0b8000500720342010003c1d00e404240000b4242c1c52464040c1030020b4071100d1001d08158520031000406c043c64004050201120480c0381d40c0c05010316803003c6c0207160b004807a4100b85a4034942490215801b00ca0bd610140c4000c540300c000742c01155000c01c1c600c8400a80c3d400a0240c05049540040c00c200000440c941046694008200d50f040c0461201c078000002011160440d54507100124651004c41d1520b102950000c0c0c20182d0512032140f00400e00015070b070800905e044100740201c00e100242460741440441c20000c81084138400032601010118407200e0100d0b6608031000c0d16 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 572031196 1250 572029946 572029951
    0x1c0b1801261f0b090f0a0e121b06010b07120e011404260d0905040e0109050312012102180a0e16030302070b120601050f07061503050c0f03100b040e0a0b 67
    0xb81c0f820525044110315003010518003904200b2408409619181c042400a2550075a030a845010b1212422500c0d5086405091860404130340030000100d48402d450403c507050300b10401060b010301801012444890801d4044015400c244001081d003000584002c4100c0071740c0d0941540004011404100ca45051941c10840446001c4455180d2616584600150010900107030b20004200705514240e0014000606410000101d600c015240d00b82140e104444d81c0303051940e0440100450000150036804045e9091041c940c10781c2568009030740454140501c01d03107104000081044009c0981c40ba40707054400a08232024545010300781514408944010b80c054003134811b0018540c043e400468802110300c80c2114103941e10503005560b6608060198000030500b484074000260207442105440420038001040d02481c1d450118942407005c04903d01a117000070700c190321600d00041481103500c002c0f0307010915941c0140071500400447c8c607a0416481a0600c2c1000e20010076505070 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 572032446 1250 572031196 572031253
    0xc120406020703390f0209040303050f07020a0201050307030203180703050606030d0806090c0705031b010614040e0a02090a020904060b090420040b0703090b1c0b180126 74
    0x200400c2c0c40c03000c02c440d5186034107020f00c0c001c0c240401c401881081130b030001c0402c6110380c40303002c4908002d40106034007aa00315004c4010a91f26014445810310309001c070795004900f0f1005001132211680002c110703000180c00602850b40200c0403d20348550010142076a00d146801c0b10300890ba41d09180e540d480341070750041d0080c029200c4d20301074144504011441070710003904000040d1140070a01c101c56109010980b81070006221440d56001c2d072480b21401c604490b400400c109042054084022800d03400d100d20407403a00c0602c030490340b004102aa00190100c64500d0340d03554510350700000e03114000c08954014a07089000c540c004c988005082c03600c40c01c2e02d080003084042002840030448030031156145030401c0c40700300300750702e8039030000c14585100b840c14001c0341c1c0c2d0f2512a244e143d004102280e01004003242d2050f8041c0c800d106094400c2401c40b00000a01c141e92407d81c030001040c0034040c0281703200c04503407001c461160781c142c80850700310048494201441c1d01e0700c03161444d40744004 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 572033696 1250 572032446 572032457
    0x40b0306210c27310302060f01060503191e0903030603061401060504030b0601090f030b04020306101215110301121106031b0d1d0a0605010e1303080c120406020703 72
    0x405000201a0014010408403c0c01100c03e490740881c010050b02c45000b041c8800a01e010300c1c9803a401030100e81001c041c400d0700100840e080402c500304121405130000010007a05104000000c068412028417241c8030394000a407900e003104850244c01c008076828807400d8100804c07407041649c5640040c1c100d0f07001c3c46040019501800305801106003c0c865100016001c0c402440407442442510f42c03c81014100b260ba01603880030420039000460340b00351413030841c2c40300308815402c0a0103240d80c4480e40b9158107884a0806101c2203c0950f01c00c0c000d041c0119203807036084141070580c0f101203040204030301e09450350fa5401e80f00800200d9180102d9003481503902201e4075081041c2628020800080402095140307903c0000c000d170402c1c51641c0180d9141c0522480141400c2c120390340d454207242c041e20354001c407820203409803201a4003c2c13140c4400c050810503920007034449800201d0341450229040c1c0c880c03865100d401d00500c0c0340820005a0107007480108403050b4002c21300a03220343c540 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 572034946 1250 572033696 572033719
    0x803011e0b0f071b0317030a0b010e03120a03140f04050d0203070b060906061b0d090e10050d080f04060c060b040b1f090b07080c070515040b0306210c 66
    0x820b010b0103490740103550042c03042c20b00098603407280880c814011031030002110b5490301c0b00a186042c1c8806000c00340400000d01a18640602421000e81401e09006245140d6107001c01d9440c00c00c0719040384260804108040001d0ac01d03004442c0714040d2144500c41030412410281c4c0001c4240d0b1308581620640301c4006a4a00100c07d45960903085921709006681755001d2040b002801084182d01440800520303007c3d00300d00310072012030240d40e401004a0306444602a05445542c0c014180f0380401d0403c21a90100755207000041d600c0c03d403803c00581c0c4403845e040e0270314080c4e41c41c0d01040711404200442e2541c0c0c07100384040313580c1c0251001d101402c0c005091000706d88c2c2d54203520390007507201120540014208400384038280300c01d00d4041c01e110307130340d220032011600005401c4510350030005032101101802c01500c005018111800f00324031000203d044101d00c100e00c83d04c680034901000058081c2c0e02d0507018400f4040c508a0f02004a030240b051644880c64261806e00c00c41300d142d071 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 572036196 1250 572034946 572034959
    0x212150105090705041202011205150108090c0906040b0613080a02090709080604060c120f1d01050606070605150604031a1513050925060306081c0f0c0803011e 70
    0x502d50180742c2d9038440031320b0300d0f003402d080090b0030360301031001e03418400c15566040304030205124140c41264910550328280c40c94000042031140c000e4a03103c41da40c020903e000559542130400d6030007000840d0300040084800c030108404d03004030004603000010100c1c0000c0e00100215000092a100301e4040c078080c0d0350500140c884840500600d00584e000000190008559610421000001e8101105d21030b09100b13106054a18500395800a81c0d00d95200e00b030302c04030042c000d204a1103460000e0201d8038008001c034003507014460000d4070341c50321040828000899040383c1d50f9012001343c00c0e40d41c0c56840e03051000350312005100c2a90305a00100008441890559244842a10040a1400e07601181403920080e140c0542000200d0003440284030820075403541c45a25120319101542c000352a144c4013500b11602130340000c2540d0080d51f5241242070003840c2d851401e9109007090201c00040345811507840b060306100900e8400e0000c008a02c2d9040d50040205ca03d04ca10180e080c00340c4c5984 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 572037446 1250 572036196 572036209
    0x2b110c0615041829070315051503071404030b04032604020a06030f060509180d0c020a05130b21010c0c020d03050a260a0609021201060305090a0212150105 68
    0x4101e03080303c03c1210306400010b80800143d150840800c82020240c0d48140410043c12015981140442c1d601c603c4000011820f0b80c040d0002d1004440300840074400e201d951a4a20009010340304004c03ca54003034500c2078802e01a5400307580c1140c45031f8280d162070302c2d028081c0031580f5030f0200b03441c40c02c08084031203488869004e8411603020b40301481c840d151413020b80c0542201074204c030b10181c5421012440d521b074400341c030740b107404d40c0d41410f0a03039240048200d003081f070f4094043e02000086007032031015844000c11001203542c2911150300313450031000d034400204003a29103194032181c0e0800720310110010071046c810110030312000700b003000824007040c0d03012110134034000c0d08040250703080008a4040c0e40580704c109154100041d10b04a4406040c1041180c02080c0303484502500602c11a114144183d00c040d00095004603d4520310381442c25100740140300381402c058a800c001070281c0810320512450ba0f078080c051014030881d003600c052b00c03100c207004842c0c01001ca0760000590b914010 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 572038696 1250 572037446 572037461
    0x3020418051005010e01030b0d12080c0c1f090203030d0501031101020c1c0c0803120a0c050f162f130b010c0f050a080408060702060106052b110c061504 67
    0xc000d850b0b80d891403c00107441458462441350b06041e43c420451469480d0b02c4140c1007014413400060211041d0310700c1c0600108400780c22a00400d80c24001c686c3c40010001303220101c0380074010501c0c6418619001a800391004400086d014000407072564004070041d0006410703280f0a001401d18003c4550049076500401d00c2c2d0280d0040964400900d441a5484641c5100b40140b0411300305603100c1d03404900e184c0c00200b400070301c5140482000f404c141c040c0b00c2c000542c55030745040347c40e0200030074110580b0301800300c2e520a020002c264000030000480c030246000b54843c0da500c921821101525250307182c6010045008240ca07544021303d40e14a0320545100c1c00c0305840d0407020705095240c5102030566800121201c1c880c414070300700032611403400703800140b04180050985140240c0c00130304180301a800030050003014498019961040800300c243d40c3c5400404a08440060b501d0350044c210581d008114800c0003d1582079110000c140d4900c1180807688038a08001c018052100700c0301030 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 572039946 1250 572038696 572038711
    0x13080a11031902060c0a05030c0a051014040b1e0c07060513021c05150408040305011d0304171606050703022119050712270b04120f120302041805 64
    0xb20a0010041c0350a0000d4041c0b42c1c410000c842c032034480f40d60b0b0503156a000606184c21170b8807148113007003003041c100a101841d1000410a02c40d00c085083e044070301544c050402400305c4441e00005040003081249143c086030b0b04c00d50000581008102c0030120b51064406072407040c01c00c3c00260501001c3e0b0804401d480c0d0181107000c1141c001c511180c0c80c504100c1c81203e80f8051001d28850404010301d00301e000300e0240500590300c610303500d016821070301300c1c090403402c40b000914590031405010081d901210001ca02d4042180103030403086040203007801c5100ba01d04906070010510680c0701c0044c114241c0309030201c0d0598454070200c4841441a00e100d040d00d100100024403054103504012506103000b410072b182401d0142e80e0b042d00f9014451344810010320154800a2800c50130301554525100d0300003050072450824040c800581310320b000d565901c0c1100c4c0099030400a5441c0d07a0003c0c5500031031801c110a48403080100a0b610910804031241588030188080d5421403040300d001e03880c03 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 572041196 1250 572039946 572039983
    0x10050c04141201020a0503060906030619020a020106050a0b040801140c07033e011b08040b0601090f150207050a08030a0e01030204091a181e09010213080a1103 70
    0x350041034441c0088a81c0c1181d04406061106600749200740090003004200f5203a0503180e10340701c1c0a0101d8804003d00041c0700707900c40e60501100c040c032102e04002002500f030300540d9035441c81105034050311395580038070781007424000c000907074138546005001503034801002030118210201c0428000002035482d8035600c2d1040118000007401104603681ca0070350f074803142405000c001c00c5a07100f240031016261050b0144800c40c425003400f032245415860800c0c03003003c040790345000000d00088000300001c00c100700d85400314010fa0b00030750012000b8064030300350030307281500c43c2c030200304000c030702e80205003d032207130b8000440c3c20b14090481d4000e80b1583d10045003810f51000e81120266800040789052660801c40840c054050f80140002403030080c08981c1c54281c000c052001805018488400c208040000e21040c502d15014564082045050910461710741c00169802446200c1a00c002e035044940001101c010218076104010f01850140d181c18510070107040c1c07102440c1d1540f07104040c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 572042446 1250 572041196 572041199
    0xf010903080d0510050d031214010b0f0309070801020304031e091d060120031c060e06060d152303070303080c0708090406141203090a0b070f0204150810050c04 70
    0x6205074032481c1d02800000c04c088055542c0c60204800d0074800d202a4000390018001c00481d07100b50186420100781e8204031402503150a158018600405c003110080304000030104452040402011001e85400d000866507400e092030050040384001000301c0c10890020303c50711b0818024100c0400b11280d8946184561081d1080d0508031302c401081030341484280c0201c00043e48400001e9100002c40c1d40003142d8410718440e200e2403c946040c003000009051120500c102c2540522050b0400360a41d145610b88011800e070b00c003d421039803a02c0800b10480d08002840140706203035070400070031034001031a0480315481496110b0419000c00750121303800c0e501080300990707030000a04180740035480c403508109400001400380d81c86980b00e0204843e401c024600d161034484849258868080e000b10302c0d001c3d800000c01e29041c018030801603400c00100d49803080c404035205405a842d80200f040100341820a06d4000da6440c03401400154132a82a0100200340d40380f080a009801c60407416042071f = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 572043696 1250 572042446 572042467
    0xc03060f0f010318080a0e0420030709030f0c030b180d0e0609031b010318050a030c060207080c1c090608010b0a03110c0102030402031006030f0b100b0c0c0f01090308 73
    0x14100c07020a0406545500c071030080c0304140c0f054502184180000b41d0748a03110f8600400013142140624855454814540c07512006a441044192003500200b6103c0e40c0c0d00e14117694150140d0f10203040180800e06810410000e0350300c1d58180da00c54400d0304e080c0e45600c824690840b1a15100c002545d01c030942071101c05001d6038441039800f100520700ba14240301000400d0800b0100420020801101030750386500f5a0940581801c500e03051085079144001621515655810f014014080c0013540175035000b4003070b050f01116201600a11101c2d0703101c00034210555600310310a400103404241e005500c3d54140310303035200d000701c0740c5c1030744c4100282c0d0810300890f04a80c8070010700c1d402e05903518014040b03416070002614050844200040e200c0c139041c010b06040868a80300741209510317150041c00011504a07180f151aa000034951405907920b10488a83d24820307007114804010128042c0818680003886282009040d41c107002050b21034001518104541e000042c400e500501c42081e04 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 572044946 1250 572043696 572043709
    0x603060f02030621010e0d021b010806030303190b1002151810020d0905190b0603012c0106080f011d06040201210917040e24010509060c1e060c03060f 66
    0x13908550800000d5a6038603580d80c41c078246241402d031000d82c00c4280c000025010020548402d280c00b82425949444c10100282c1c0320300c0002d10194000d44032180c14507940b2460303071018103401c02c0500403a945101040d0302944d554084451030000044040015440124951003039206d54071240c001e021480124190b14007a42252081100840c0d0b541c641300003184042007122154005083c089042008508055145a4000740014000da050500c403040b4003842010301d000110400044219046410711503034050511360703002c20090700c0360700940d42c074404040d0b100c0005d40188526100c80306114541c480e1311841d044501a020a07445540d400c0041c40601c83c180e11620758040004442100f681d410120201c40c9850290074000842c0070b1050040400303500cae07000030850180da0000c0c0d11001b480a400c01500580740c2c108032000c603105245845800507945000c40c0b1905842c030300740c254205d848621046051250a0744254004584042615405c4a01444028004011a00a01d002e004c40c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 572046196 1250 572044946 572044999
    0xf133011280218040c150c0b190507020303101406040e13140a020f0d171608040b030a060e0f06041806022b0b010c0611120103060603060f020306 64
    0x1c844000c6001a550442119483c0810003001800350034a420007068031031154002e400e40d060441131184407143c01c40002411a40c0c008204086a514061040546a0b0303005424245070b081c1003c0c0448240c010003d507110b0007004030b8030707040541d507003030358440002c01c550405812920030841402080c03440101c040d44000c040e444007180e40107542c3c0301011600c00a500322256006004003004624240840c40041c0d90100c4220004d42507039211650740d440c00180501e0441d000003802031085402810071641a608050f0043d141e82c0d840000b090150f00c00c56292103414070305100403541c40a00d604050060f000407000e14400e40c1d070101840000c02d800e003c00c08046003c6021500000e100d400205070003500030411504071986c6026440c40790b030032803810174415402c082c407220181c0d0307020003108201504048045000000020500000d03ca46918107840c688200004824000300d9001281100e11515081000c101075113000b034101d00054803401d6221003150100110030440e0a2641c0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 572047446 1250 572046196 572046253
    0x105072a03050f06060915090411120705031507050f0708090d230d1b0f0209040503040317030c0a0e1801060c0b0604060b030f133011 59
    0x15804580884a410540301e52044400d030b4004418211407000074000c0c1500250140e800d42c80c1070800c2c140700d02e00c4070041c621142c092030100e00010244260307507e954021403005402411342d1018020b0780c648845043c02124007902c034194500364044540c6c0d40c024860341072962610300b00079000c8612200d0794849030b0142d4104030280f0501c0072a66503001c03005d581034448c295400102039510f0055078103e03075880016000ba0020f1580c241c0c1c13950001d0700101109010a45000001c5c0750740380031a1071348a2903502940043c0041e0400c010840700000500c1680d014840d8284200c40090403070400d44404c40b44000800d070280410702e141d0340505088020a1401800316a0a99110441e000c003d442640710300001a60502c020040c8801008850b40004007950306000b40e5082100c809400c0c84082d040c2c3c4480a50000020344070200c1d103502c211080d50018403414040c03200050440c00c2e45104414090b40c10035041040300c1103000c0c5024107941005074018150340408042c2d4007010520844404 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 572048696 1250 572047446 572047493
    0x606090f0c09040510060f0f020d12110f03090f030414120a05010507180f030b06010e0a090908090f040e070314010b06030a062133020703030902010e0d02010507 71
    0x440c0d0300c13400b58034824850840a840700c245011001071030700a101e4036190a02c0b140019201142d40d000c1462142030640e400c00c402150101c6010360000c11507000a54071800e8003081c2c040541400000a5018600b0761045a844c611001200c58803442240b10b00c1c5480040e4161401060804514018510001109454460035261503041c00d40340c00301c0c4ca090000b038006000070170f080c01d08100c88000c0c1400c00c64902d40b1305d05640c0c8559158401400042c18840d040064070314a6640d40e4011000e0103541c4818043e030601c03464005469000307861094803416000381c41507124185482481400f0fa917590080003002c0c5180c40f84210080451107403003a035522190008410740b0303814002c50056030600e20000d5142d140c074030300d5100c8500c1c40414603031043c2d00c1c4890a000c1290756401000c524001004040c0080c0c060401c0c4032200e41d040f14404005002080480905400d648010109070003a2204101d2030144401c05c800c540800800030301042d03060202c0804500c0164000c00e50300100300e8034 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 572049946 1250 572048696 572048707
    0x706060b04080604060f11070b040b24040e0f0d0215010e0609040605060a17030316020106060c0816060c0e0907020304182301031b050a03030504050136080106080606090f0c 76
    0xc0300c4603803007098155070b141d200d00b007400108a07005c21a41d9000201b25030756281833440301200b030f1906520352880b610403500c0c1d182d030f1440340f0300c1401030000b81078040007101d620400350134019481e079841410b03008045031640c000040c1c1001c11b6445500c2103e008000a8256035581e5810004010260100e9000000e5483c086810380100c10b0f0110080f0384400116140e2400401401031001c0c940b03016000c690510404100315504030001c14052540400744ca030304c1c3c084c4220b09014182e989840940003d080c007900c02c3c09a504070b0901300500e1340a03500046280d5071000146c3e6603119500c80d054150604081c240080c224a6010741c5000c203503110103011441d040340003405081c0e000c1e00103441d1084284142e410700050450903c00500c03007070707465141e05450340e1000f40c198006e61051030b050080c1c0052900e500f9801c0b480841d038045145290300f110843e140c400460341d040901444034150718010340030884100019400b80309030402080301c16181e465500c3d443c090701c4080c03c00414210b00340714 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 572051196 1250 572049946 572049971
    0x30803070e03010c050c0c0d1e060f050c030105101806110c1e0901081c0302180a03030306080f01020f030112020a120b04031e080a111605030706060b04080604060f 72
    0x800498100d90360b219500c41c1c6c40441c803d8203001010091920910341d110304a0300280081c4c03a614204c18800100d030841d01d0031820014040e100d892000111580f400c4100200e000f25800034506030348087d80c4074100c070700040c0002e46200b406440d1006945020900c2003055910900809100e424004c0a0356600e254401c01328032642c443c2c200d90a000c2403007400c0356200e4140000c1c46030040c000d54000b8000c12052500c007280007000360454400301600007411080d210a50400c0240400c4045c080410455490500034020709190240460600480e40c11007144a01402500c80c44011010041d2441e4601400c0c0310700001c0e007400490700a94a21000030324081e00c00759680c8603038018080c038041454a031800808031321103a00380040c4110100060a00c0b15072082084ea4801052080028a80203c0f100b8120724001da41020100740d00d038000c59400c005001c400b4003880d600c9560180034041e00c440c501c092901450045489981c800d00005021941c25000302001d807443c41c0e40090003011006 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 572052446 1250 572051196 572051201
    0x5100c0b0c040302010806240a050c0a0b040314040506030a150b040905090d090e0a0b0a2c01050409050312070e04050a0c1d030a0609051204060207080c040b0901030803070e0301 78
    0xe45001c01c0c041d021800300709558100c02d95580c40141141c50960300b120a040302209541c4e080c0f4841003544007c02c0d02105103008500701c9036003100321001c841c0c5036907285c03030000d0020800710340880019a410307a0450079020504140d07819034000130495811079940d1001c2c20f0041023044044240200540c500090158000005102809100c00c0c0402e091401001007071510074800c821a0420101480030409000880c00b05074000c2d9022101003000110040040c03e0f0101c290420500003020807012190014040e0004044131108040b00656030703610b608101c1140c00400c00035029400400c07122124511a10009900c0410350900000b00340c20380c404603049910480f0040701c2d0603903400d0380100840e00100c403d0312080c5181c0c4901e060a44940110340ca50751803810080280d03442d8444481000341c00d01626100140056050761aa903640000954800152080c141e041c001c00c00b5094a03402d26020300301c0d01c190040e02d8038003941d00c0c59035034140980c0b000f45600100007038041c8c81c0c0311030360f02030 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 572053696 1250 572052446 572052451
    0x16120c0f050c1c020a050d0912020603060a15020f06060301063803181005190903090302030a0602040f3201030f090303020309100504020d0f03051308061008011505100c0b 75
    0x41c4d00400c400c40e254a0302a151118000b590818092200700400c41070741b82078412240035a050302c200340c0341c0e00d03081c0c0819401e1655400c0301075951924000c07010003990001c1c1d02400c2a00b250115101a1a29401e0500300e80840c0a41c0d403405441080c1c02a08448088801d10400b24448020640f910b0300c0384c601d2916001615010100603144940b41ca404004005503021341103610030400071030070442003040d00d400b454260007425a403140d043c0001d042c01800204004c41d005026145904240e150500082d8018058001d042c032000c140841c3c1c268980001e898080c3c0000300e0011117004c001c260906803415100d10a04241e10b442c4a5100c54205c0e00a401405100303442c00358483c10009205c1d814206441805010645000c0400015907141681028125003043e42c04075444110306085469202d100c079844840710710350a00064501d80000c449106280c030580200c43c581d1906045400d0f0345511460cd002c101000100380001d10307100c81d00080720005800c0407585200159682000003008 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 572054946 1250 572053696 572053753
    0x10216030b072c190509010e040c0819030302032e060e0f0d02060904090c1502012904110d0c02100b010302130e100e16120c0f050c 58
    0x20380510000580050303002501014068021110711250b04030f161942e0320403409240700305003054202c00071054501e101800340001600402c55917844840200304900c040d602140d000194841c00200094007044668103030b03862000c0c60a0700369031030724100d01940010f001052071040d0340c030b1501c001150600300240c01e00901c050300c1034801c3c0340840180128040d41d2456000700031a100d01c0d10960703039042c04a44943e50450303055803a00700d50004a402032060f41d030002c208514000d4086038484c58020fa0041c8901d0550003413200c0000045144100c0348041118a0303021200602840c0c185015000b845d402d0034078025190410032010292820340314015000f0015070000e010110001d00300d4010300c0031500003800c05629105046040c052900c90ba0301c200002c121111004c50401e003550351041000b4036200413461250708283c1c050381c08600359014264040f850202d0b21440000241c042c072800c260041d1941e20b554071401d0f030180c503180d010303803100116800f811b8107030070080040d4950400d10b4803d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 572056196 1250 572054946 572054963
    0x503151f020105040510231f03140c0a0b03040f0245070504031401020705010c090e07140306100c05030705150708040b060d050c0411180f0907080601021603 69
    0x1054180107041c62240f904605043d0f04094103207454247d000c01b1031400d041d605540c44525920884604001400c4a00c05446055006000001d0280d071208041280240406860010b0310072010081e4841d114071030020107007024000140404c100307064251000307001a1030f1717401d441210b0466242e2104169000b50079003003420552241070320351100c819400000c130041222503041c030b410b02901078040e07440010019800c0c13038100202075800b07406482e18964400000e01035060030002c080c010401a0003294101d40001001528091140e06045140490b8541c458a16100d400c188003869114080b214140000c0d50074200000d4010401810f440c0c0c003420280101d24809116107510320006031003c010442003000340000b01e99646940b0781c01030011a0b40d02c030000d08510b4103608084a0b0f4160542c0145482c40900a20300c0c0039008100301c14904041e413030360040640030410148840b06145400c10b400c80009200700d07014690141d08204140102d5404a08510320a070f10000f058004664401 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 572057446 1250 572056196 572056201
    0x18030706090c090e01050108060c031308030a09060513200303040b37080720031c0f09030e0f0d020607060e120702100c060f1109030c100503151f020105 67
    0xa18520400d0343c201113850090240c0d524060300306a4801c3d0281030850080340010229100b41c10803800e414805030b01c90151034580c0760141c41f510003408000e4003520000d080c01d000a240091001d82400da1940c441c1900c0e401d00c105140140350f01090603402c6030180700800004c10001035180c040d0079102d01002d8084140c06042b003444904c212131402c146040c08007060803048440d045901c190b44407060f4500301c000d62528800c00e4940f2500108000307140e0100040b601c1000510715a14074110300800401e0005141c240c0303609007180c56008028000440c00c54111aa92400046000c4000f03002000b280d1194056000620150f0201e5402c45c3c07101c0e550705c40b41e0940c0c041801000c1000d0b40a40100d07091052a0300410078560140d103581041000c0d0f8400e03a01003001b07540c407042c800380d0310b040c0410500c2094500e44001d6402515071500c2481150b4504106180413800c0791805030060f41e80a05644440100c0c0360002c40001581760311074000c003400100212103441d488250301d0258004034050 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 572058696 1250 572057446 572057459
    0x5090426160c080d181707170a0201031103060d0b0a09020a0609031208010b04090902030f010614010e03030a0e01080403030b10030902130902011d060c121b01021218030706090c 78
    0x1400d02038200b424850318040260b002000c10314030701c00b1290420081554040d0341b008a030306121168014032080014824000c01c943c00005405540500c03c0c4c0b401c00840c00c090080080d070303010031103c050707200c99002c1c0404002005000314903044404040041864404c5600242070316585030082c10014102d401c00b0400d01548250740c2c2000c80c1642480a410750600e080554140714500a8010b00c0ea182d5155008540b000c020719895007594500810a0980b141595500b041c0aa0031080c001404420fa425481c5004012a10911b8441e150034607605603000054a000000030001c1c2c05250751600fa0491a459400f08052602c4540da00000c0304940b80c41044040c45e4121150450741f840c010380c900050342c0240c01402c18043c3e0002522500c0f141c41c2c005441403003000c84009a03400307410101c5610102881c058862418030f00b6040c1d0b82100c00c10304043c202e00921f80c21170b03000402030313010030081c500035241840340384020710581e450801c060316203500b85d41d60844100c2d0b2001c003510080214 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 572059946 1250 572058696 572058703
    0x201110709140114031203040f02130b03010b01031b080726010501031107050c1504080f070e0c19050a03091b08190201020c04151203030b01020705090426160c08 71
    0x1500d480f01004ea070501a49000c0ba50302e440c030742044204450000049000d00c10031a00405480350300804d004901224058064064501512000d00075800c001c81c0380415030003030041c000c0c1c14060402c500c03d8600c8400d801ca680000103081c41082c450050070000f940031600d0802d0364130600316111003060b54504400102111600454843d890000b400520000380d004516002c090740210f035039130000070f91411040d00500c1698460101d922800c0d070543d41850010400000301c552030b03094441d07540d8610100c4841845040031450032a0044130001d160103000d9406042000768920f40000c042405a840380d004020290748407058114000c0200000c0c0000c02c07201d0912402c00000c0360700c1c08860341c0040c0d680d181101d8441c0c401c035181c4c5206c070030645091200000134040451181c00151083c00e01400a20a800281c0d0040c02080c10106131818607008450003141c0c40100280104901e503403024203202e000320b11912105041001a01c2c0e00c02240d000e0003030501a000001604e072421611314035 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 572061196 1250 572059946 572059949
    0x405150f070303112a060f0405030f210106020a0203060c13060e1c0c0e16050304020f0a081b0a15050406051810030e060703052202011107091401 64
    0x8a00108011100c2495244029110429814180880d48a012440c910741501512120000784040c82c00001d6a1221401200000b00070000035204e05071500304005400d03940444019110345d004000740006c40c5904402406103010019080c00800006030184100c01030a03403126006070304c500c00c00410751800381300305d42c5c0100344d55203001d203407641c0031050b408861050f105076000e0014007074140c040c075141d04100c06444181d1994040d21120245021044029140912000030b400710001403010300c51400d003940701d41d0305616601e081d80d440760300308442800b029440e180c10849251000415090400007906072101154080507003401000034084020b000343e210742480720700b21000c4220310350400c080b502941d11515207580d5a203441d00071044445000c2d02082d8008012032000048d0b5503155200168042c4030805980454841d1803045040d640c041d142d00d95010b10b003407140c017001c54080082e43c041520605014580c04640c41200e41011415401902483d445441c1b494990100c0d103030850 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 572062446 1250 572061196 572061229
    0x90605070c020f010f050403080417071403060c0702010e090106020f010f0209100804020102070b03070f030c08190e01060f03080d060e09121b010f14010f1206091113020405 76
    0x2050311080740c001510f81201000018180510403a455a596101d070089070003640c1c12070180d40d6129a02c980362007112602401a2405000f07220303012840c08a01d860040140e00008d00401d8176445504030b07803074140d200703c03422410302030711a2003054140c0300e08505500818158001c7c0c5040010807000782d082d99161200c15601c0d80c4100803050281d03a43c400c0f400261034179450421140e646510040c0c0c0740c00c4031074204c15074609001c01040750956000c0c040d100100000c0d5814810380b07140c01400d441180040c0d600f221104004e070400b00c2c0400407a03100c0b41c2e800b041c030000400d11aa03034010f26403e543d0704d904240e0ba40280000d05086d500322900520000b03180503030b5001381b80e2502e80c2920791035101c2c98041c2c0801078000203121a5048005501501d800314181c020070560004410201c0200041144005107104403030000605000a01e10302c01141c40c44c1c0710708203034054903507110001026044003c44146003038120b0030f44113440d0070300003051008000100590b0381d81030508001c00c6940c40030190 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 572063696 1250 572062446 572062457
    0xb1f0e010306060e0306160c0b09010c090f0605160804121104110c070b030403020304031a0f090c030d0e06251b0308070807020406080d05130b0a02070608090111070609060507 77
    0x2070302d1079180000c035503902511f0620340d6000c000c100c0c44e00320343c2d1346041000035000c2d107140300500c682c4401c19841a212142e4a841c1e000752142d139406520303220b44407845410701240301440b1040c1030440e43c0400341a0305100e0000146007d45402c04483e1420031414188c1d00403982a01141450500d88140142d090721404114100207812140c295905000c0c002c170b01c000e1710044042000c0500800c203a03000395503c000498420000d0b454000e5107480200c4802c420340d00441d000c55a03c0401181c4641f0284001d0040c2424240045040e0b51084140308004c0e0401020040e40440e43d10300c030004052003141d0840c0b51548909400e1034400030302000446403000340d881d00c081001402103400c54801d1a4014255521414580001001003249500602c2e69015014131880c075a907200c002085080000f01500506030b0b2600296280c2d4000d030052807000d82e1221702c05100c2130780a960782c4c940c4245036000119030340051501e0204150014030b0b04407583ea8071071500008000d9a40140366000c001803909 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 572064946 1250 572063696 572063717
    0x120507030618151505130e0403320f07060c0201050403021005010503070e1302120c041505030d180909060b0109140a031b0812071a07020607030b1f0e01030606 70
    0x40f106860035100d41610b4a4440307588504d4680140e041d80c203480e1000f0580c08000d9a608070864411608440890020b02d1151462210007220f10741613081745110380c000d0307116800c20856048903034040340c016000090184921000980740380520070b5502115030000c40d40303052519010b4a001d03c18114098030034180750042c015503c00003500350489121002140e003e4a544040b424001d0600201070341086010004d0504154001f5407921903c1055401b080201c290517183d011003090307401580d91542012030b054001c00d2107407082d01203480d54804802c00f03403945c40010104660b001c0704210b83c601c4e2030f0340c400c0000b5a000724030031000382036030784909000c10380c0c2d600000c02c081c030075001c02420800c0e4454050381c00410940d0a8000d0092101103588000011401c824107804c0388804a400b4003401410000200d02808014020030741c40e0010f09058071510300540c0500303040c1010b2034001d009090350510306041c119540440609580360f04101c0481c40c4001030075210305411040600c03900098 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 572066196 1250 572064946 572064971
    0x30307050d0b0f060a02071e0803120a0e0a050a02041103060319060608191707150b150a051b01020901090303031e02210708160f120507030618 63
    0x45620501001c0400a4074008000000c0c450098042030143c00940208100039406c0d00001c20030251410b034403041a8484100f60188642141e5018140103138100784426451882c0c030f00d0129400000b0400702082e50654040907a107403846051081d40c640c0c0c4040c600c001503041503c80e922840c41204119442c51400300c0209644160215000d440c111144c4480f2043c0500c0d50f10503400303405104169400f000302c0501075a188141c0aa0075103c1e0084c07800c07000c030420407000844019a600042007030740306c2c0407a01050010801c40c0400c81e0030140c01180e24440030841c0700101406074640d01e50b6600c940c0c0c19243c04074070180d81200303030b1034581c030400c020481d43e0b80050044049a0b894070300850b03610034100401d00e0340307610460310784142400861000c600e10040c00c0c103010b01240303068041c0e1240d03460030000c0b518108107030f0742c1c81c1c9582040100222602e00c6030017140081d500d14103203005010201807079032046440c01c850202c002a51007405002ca030358030481405107d900ca06080c41070001542 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 572067446 1250 572066196 572066207
    0x2090103020d060618060f0b070b04080c0111120415060b09060f0f0c03070201111204120f021002030301050a0b041518080703061a01050304120302090301090606120c0602030307 78
    0x7a2080240b00400c0040288039049070010341000c16803107140c1a0405891320150038240591070002080b8000803450581060a603140103030006050205a103070354643c41519440001050307915500d4000c4144641d882c18010310044141d440b0810b5540742a0400500c001074100a210042c0d04040040103003c5501c0141d5607002070456074255120340c46941c0a009200f102d003010203410010030184012034011025088480c001e80f500340c0c0c07840001ca0803644810320440811030b550300500040c031014903a070204500c00303841b90019070840e07002900007403401e60305100c6d50720040e4400001031005051040c41d03400208109045c1d2400e00781440c9101d0240c1c80044807400420080800d41202c500c0b0307800d00d40f0010060b0805942e481500c0381013030409456800b040203441c00440040103d5035100b032044a00c40c9401070110115807040001c1200658008403000b541503407106035840c007040b40c5109030b02c010900c800384010f0002e8149802d0740c41d1103040e40b04105640051040100294009 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 572068696 1250 572067446 572067449
    0xf060a1715060111120408071d0c090f0301020706240e0a090515090a030e2709120d02130503010e0a290108010e100e0307150b1215070c020901 63
    0x180d150340307080d91200012500d4008644141486120b400c4031881c00e4600700c0000c2007524641400e541c3e41c161a0458440b0350001e0b02503100c00d5080280c0051104030b0781d50081c04021000518a02d4100f0710840001d00b660400e40c130607640ca03a50b07070181024004000813440686040c16032090030040c82c1800c06441d00d01c00078980100e8030b89030304410013009402c2c064a42c248420950001e171a0412290059544120b140110081810085e040c10b10380f510130340b100c518011400000340e04002c080f20000d04600040c00110040c07107624648100b035510f400c081d00403400b80000041e19200740840e104602941c550000303010364513001c18210404030100e041d0760043d42020302f01c42a41488034085412280325603902100040840003c9941503043d040f0701e01d800207201c221010b01101e07100c40400c542026002d4046640300704400d2000030364070010140707903004040c400141d0861550104400412090000300301e0f0300080c51041070450003c04041c0c1050380d070b01d0008501c0809901003410004113 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 572069946 1250 572068696 572068723
    0x5040b0d03030e07030b0c03070216030809100201141806010902030105091810020708090315060a1401020a05100b011b020901090e0a0203070608060f0d052d01050f060a17 75
    0x43d040e040b40381e80c0c020044d1400940e40035480c0000d914040035501010741050b01c1c104014040e0000442c103400100c0000c8061303035040410f0b503151680b00c03010004a99107181c002c00655481c0c41c2d2503148088001607240c0300d811069200c170031a118201005007410310507041401403900c184018040c03038441100c460341c40f400c0303515110313580344200c441c032441d007031502e070030302919a00004130074041020440150108801c00c0c0c0442d40110030344503686080d00710440d141074006150b103400304039299844050119000d018010b07504ca810164441c241007046410700103003c50f0701d0307107400501960312490710190481c4c5e01c503a071082058198001510110188a5241056141e10701e48190020a002c41c4040d06e034028101c0314100d80d40c101c043c02c3c60034100c4550b40306201c911000364880c01c0c2171a4800080364024064994902600e2010400500004440d05101401c401241e0740b064244203060255064031611503543c074200d000c000b5007145641001c143d410300004070f0111101c1c00180020365030306 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 572071196 1250 572069946 572069951
    0x90604080702180a090606090e0a020f010315170f0303040507030b041e150501090207020303070b07050403021806040b010906050306040f11070b16020a0f080717180a05040b0d0303 79
    0x80d2400080c08519003583d4030310b500c400c0c15084c010915a81d5210705006489003c1c02d104082e51601e04e54200c0c0c01d142105403140c4c01031780000d801803822400e101c0701484c05040004005a0003521003030b80701c940c0d4002c036841050300741241c007511f9810002d000d0b04140440080d451440e081d5201c50b207951151000920040120307011400300101846032900c0b4096010b2822800c40490401b0031107d0150b034510083c0c18a880000f242304c1800c0d0003211001500030b4021032408403542d89401312610010080d50802905120100c0107a540252242048411000b0721185007032881c1000111a40c0040e82e07410300507030075800c00000ba040345c281e0b540b01d481110006030590000c8a81005461441e190140306600000c0090401490f000203a00a80149482110100c65188140d903a682c0c000c6020380711507041203040002031041002402e80030700c00c01000c010200060b2240e01c040d0404028491100c8203040c00c01c0550421030744140040c10100c0e000d02c0005004008030300d43c1000d07818080d04258 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 572072446 1250 572071196 572071207
    0xe0d050a0c26070c061d06031e0705030f09070303080109050603011b030c020c0402180d1119081903051804140906010303081f260604050c010f020609060408 69
    0x140c1440c5071031450004a101e402c0700c100c25000c40b009a02002c01261060203a040c0828040e200d002030608490790807280750140c0000b03004012440d04020040907400f6040d1040315500c0e08100d8816005031500e840301600c03800c103c1d02c581100c078002001c005143c3d01440d020000300c0d6000c420207044078120070000070140c4a00d8082409445407060080300c1e690701940c3c84035a5075155001c241d2010060303080d104201c804e6010042070b03115a000007155a01843d03a00000b5140611505a915224101008440305036002040d8161003a6000038a040200c84040115410078040f94100005840880810005c690b0b0040e0041c0280e10b0000b590f02044486200c1c240c07656070003c1c8201024221810252404c41c99159a5110034041200000c51200108030b03000d0098400300b2100f4040740d403040782103050200d68031140c600c840d0325810b205030100c031084580b002480890701450050300a03043c041d20040024125040107502d001c21036020038100520414049002c2d60410742c40014550740c0e0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 572073696 1250 572072446 572072453
    0x4030507021c050304090c080603031b24070f0c03170c0904050f0108071a030c0304021c14010509150c0c160906050406090b0105070b060a08010f050405010e0d050a0c 73
    0x2221040707032400b00381c40425105200000010344115142240c040c48910107504089910341410340d507880c0c05034014000400d40314000c04141d40d159500d0402c69103104403080818008100038079050300b003c041302040c021003d512201d0000c050b545803e0002d14240309590040076440801a60340c0858613000100c3d9951894904450242500520500003410070103c0303120070302c0d02803250708480d1080c80c100181511003170208086448400b20458256561900d49021503400240100e90003400340001c80051219181d44500c0540990000a041241c03400c006086450252100006500c032110482905541e620b110b0382c085071151540c1d4490400e91119172400d030049205481800e0010408a0915030f030340e10160445404660511a465541e4981e00454205011391070001343e007000301d5000f040354140e05940003840608240c201e0b1b561241c120b801c48072615100780c8c115484806000c18440c007400b034220b84442c01400b400c80240000340c043c2051007845039010034840b80b42d0082050 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 572074946 1250 572073696 572073709
    0x91a0a0b09221401050f12070b09030a0210032309030702010302090f1017160806060702030705060c030703030510140904030512010f180b01050a180803210a0203040206030403050702 80
    0x1e400c01d81031180c3c0c10420319814501c4400d0280070f009200b61042d41505242640d40101d94082640c0a45142e601380300306400964020f5001e40e80522070044e1510050b20b03200c00558020001c0d07940040c40144d25940c2d0602c0c0c405030f0712000703a00f03103040e0280080b14201200b102c40140d424200141d0703a403901070200d4843c1e0002580141d01900e22540180521b4000c1021040d1110b812800703031042e42e858070300d103504a0701c0507802e40008504400041160034004010309059000a08580c034542d61940041c802d40c2c40038801d692541c101003078420406805014440d00048160140d41c020f90820354407001100e10342d003615110b811010042410b15001d1001c981c2114102c0088910315a160f00582c0707000f14061140300300750a0105201082c0c80031034404c08114480503516549040d0310000d080700c03005c1da200524801c80c403200c08001141d0204000a080d14408080286001851805540004100281040c0d103540c010000c003c01a640c60003240e51003941420541d844003c07034008030b00f0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 572076196 1250 572074946 572074999
    0xf0c02100b130f0c0909020f07020904030e0907030b0a0b162d08040501140a08041101021212060f01020604030c0605130b0a0e06070e090c031b04091a0a0b09 69
    0x1d207903d4000069000010b541240faa2543c0700d40b2a0b59400d65103208160480c89075070000c8910b603074103102c01001407034a41c00c0542c00c40c2c060b20b04080c0b441c4420000030285d0f80d050701c880c0042030382c80040403485d0800030549030080600b84c4000f070070180a901048403000200000900c2500c800a50142c0e00307000c0410a84c82d140d075547e0703070160089a0325007105d0551050080e00d001c150320350340681c800b00c0904102c402c3c0543c51765409440342c07916a5211000800c94a00c0380c150700916100e001d1181c200000380040d1604c5e41001142400e041c020700c11001c640303100301070440d0032150030000800c3d000400d5003000c0d0781c00300c0001407996403074a0888101000682c0241500300c1030060005a02e07103a006100342c03100d004160f80145e00c03021000c0d03c901011000c1150085000d0340002c1e00e84c10591301075513101100a010381400300700d00c26481580e138016081049860b584a5402e14282c12141c4000501c00d4141da4480390a402d02441c0c4080d405403075051b600c41c3d2070071140340a440100022012 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 572077446 1250 572076196 572076229
    0x6110c15030702121206040b04060312032012010f05060a08070c050703142104080a0f111011250504020d060f120203100c08041e0206030a0f0f0c02100b 67
    0x985030070b16840140d410f6a000d803000b0b44192304008606401d85080c0c40707a64120303540107114900840540c0c0c010f174041c0c031043c2d000e103030b607941c04050300c496001d00c0100400e4000204882d1020710343c10618280b03200d00340c5402003406101c0c10700401c5031060300240b11a40206190820003040d8a0038070340545040c07901c0d00014411000e102c07444a4151001440311101040d521031a1042030300d41d84204014000c0e803040301e9040e8044001c490224140c0d1418000c400d0050703507840040700310000418000000302d51904005410f84038501f04443c4e00b8003c80d45480c01503030303901516040340c00004030021114081c6500c190360015100d00141c1181e884030700201101e44100b440b890703565100341014410070b0803da000e400380300041c40400e04107124801400946403500c58881c2c4607515040081c03125007450507400182c5a4440c80560703070341c0c03000c0c40c4901c50002c0046a4904002029015100c00da83c0d100c101700d0804150300d0041d07030003180c0c684204148500010301c0c00342d55000110440220703407100303 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 572078696 1250 572077446 572077483
    0x13120c0f060914010e0d0509010e06040e0403022401030c05120f07090203011a040807090b121b0a061106010b0307210903090605130b0a05070503120106110c15030702 73
    0x22410440071090151a003ca20780003001a141140704c4ca58940c900024102c001031420000301d5503e6000e0b002246428101802c51410140c650503c0c50401da0244c5003030f00541d102031010708120cc7d001c1e4083c13000c0d45580100001d43d5140d03a0303415070484010300406204041072500c24420100400201c0d00c0902e40908031091a81c1e11004030000b50700038050044024240544a0041c58100c411601207455a000600c101468203030184024400c002d81103a00c00d40c00d1b0b800500403e010030030800580c0700c442444032880e103080c04101c3c4041070303540601c003880046000c420080c00080360181c11070750081c035099034076a1881002c484c0750300c4081040034a1140c11090002c0704480741c1c0a0a000d038802e448422007180c440710180c5160203888000304000e40c0d035200c24804170554402070210b80c41142070090030000c091341c48a040d5001000303030303200401d814801000015441070403c1000100d60010303000501c805800310701000200540d21003e6907001000c0b500d003030700c00c11600c00400100d01d002c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 572079946 1250 572078696 572078711
    0x6050f0a051803060a0c0210140f0606070f0309060e040b0f010c061d0c09100e040609050118291b180a06051201080d050a0c05100608030d0513120c0f06 67
    0x7100520850500700014824443d02d000ea00100d4811400c460740341d062000d680c3d94400ac069019020024511900020b0a00000d00040c940000021100d40300e03403a280d200509010000b80b10b01c2d806684644600d062500380313085500c4192040c80c0003082803030700d58048150390501c0c6024005d83c3c1e080c154281c0c507041500070512000700d00780d18041022102101c42c0d07211001c00c0802184140201d00941e80002d001c907000070450b1f84840c0a8030711440003c031b1a4840100c2024030451110f005480d000a064020b040406c0c4040c20707100c0081046a281c412401d100821480b9100300b5101c8038040c503c0050074003103401c1d40002c42c03804024001e00105401ea00c90303c008003190851543d551a4100307001c000f24031010045401c00d10040f0980d1600d041c101d100c00100d8032650300c61030544031800356001c0c000b05040304c1c0c09403802400c01400119034402c08222000200d6000800400130301c407002d04800c0018036040c0340003503111f0306440c04128400590425803150310005000400b810702e001032 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 572081196 1250 572079946 572079961
    0x2010915030603150905062a120603010f050f130501020405030102030405030715090206032415040825120302100e0706030c1e0f050c120d0606050f0a05180306 70
    0x10030741c1e204040c00905102404c201c1c9099840800c4001d1480c1c0121000588030304118452112903940380401152546680c00861100da01000811000c1c100600400c80542024003610300c80c10f8414104000c2031615074220150744c080545410034194100c40c400082c4032003501501d000e0000200210350303174101498610781d00d0b4044441251b07005202c50011003060f62501c1801c04054016003402c5c030790b03503810200c1c0c480098a12105001d814034003074215000c1e10b4000d0190100c500217405282d8481c100102d21b4902800c03900080050340f01e400d00000b03055840c41c420350460b642c4517030b080442542803809078100304500101c644418070707100e0300c8040704e4400a1800c04988017034030100200502d2480441d01c10071003985103a4904160381c2c95140240c030074284000502440d1511508040420750300c01e080c88246201365078280d0010070000c51140d018466400104868140310b07192207541d004030001802440c0c0310f81c007440008220030681c030f81c03103900301d03164140000e042c0c4645142480 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 572082446 1250 572081196 572081201
    0x30c070b0f0a0e0a03020307030305061c050a0303111810050708161109010501080f041727010e1c02060f040e091005070512190608030d0b0301061d040201091503 71
    0x441195000c0d08090a81e0624030f408210044425055406146084510b480c264041c0034040c0440f034000c030510340c4400380b0088010049000c0ca2103179010340b840341e200341401015201010001b03841e640c003c1000b40c012255410307020f03003884020b5818444030145420705442900900b00040c24481c000a40302e4200740042d8603188841d48a00c280c111080c03980790900000f8042402a6401b051041d0049500d05030241c181d2540103102d43d1090003140c01454920703030701e50007601200c1a48804142107040b07007845070f600d02c0c0b0b0b03403c002e20701a002852840009204640b01405c0068001c0300303d0314050a6484003012a065850103420b4156255076503d24200003043c1100d0300754a40c0905550b040f0310400502a0342c2c016900c9a0364182881e0101d6092002d00b10f0103484541c103580720340044d42c0c0204407401040b009101c00d002442c2c131102d803ca140800c0e507000b0a03000780720340d14090090180f004101c81c4d1140c1c50040846c59040766859100598241a0a400076010b4150030700860600d00c0c0d064 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 572083696 1250 572082446 572082451
    0xb100b0316120b06030403030e010e0f010c080a0b0120010608120d0f05190e0c1801051207240210111818010501050c100213030c05010804110402030c070b0f 69
    0x20b40c2c400304000404140710045600d099046640042c080001c9070104e84607800081403803001000016103400039207141440c00032501683d00c000d9440c3c0354034918168000741a560b0007103410324107126854a40780020030310b054041c61141a80e000d4400804010f500354403400161103c2012070700031090040a9038101d80200500d07401c5941403501d2140c42c41c621340240d600416842c1c0101e421100508188070242010f410644514400c0819005d910350f02c4151580e238031519060305d2007465052800b84285000041148081030b0b01914003041680096914642d21000602111030203134180c0070100e0820f61014900c4c000241402d05911034000c001c03008010f24500c8040c0d10004417803140910a00c2c40b980c01e501a440000c203001008294082c10082c14420729582c00e44030240e4007209010100d030051109002c945140400600420104070b1a20004c0c00090a240d1050315103030703444215a00241341218052500800460b0f1501d0491040d6000b4951007580b221961a0025203561800000c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 572084946 1250 572083696 572083741
    0x81902160b0702121615032c0d0f0203220b0a2a11060f040b0c07030b062b03120c02210702090a050402061903020915160b100b03 57
    0x141c03013a0074400c04001540710000401d22400e80c182d00e00e0b20701107020b94002e030070035507081c907866140800b00080b00079249610862a00014504a18070420305441c00507154400000d000c400704c400410160000161201c40405035107291610036600c1740190908030503486802403030808501e0f04a1b160300400003498040e061018019889880002840603162154021b003103000340e54502c443d0390070202c0007042040112240d940c40c0582d90005c20115910001100020b078000c1070041c410480300c2c0c240c0f03640203042154028282c000da0150350912410507202d441c0c1c051300d0034540604240c000d0215845881e01d0040400203a0562503000c0e40307503400b95403202d80c103103000c10710b81c211803120505550345540c02a00f034281c0c1d40e40d1039540030010700001d8001c1ea400b000c280a4156410050004110300301c0180e50090b848104003418041503e10880c1014641c20003880785028050500840588aa0700541640302d9520342c02d00702a41101107810040200e00d0000030085449003c20040c50803141 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 572086196 1250 572084946 572084959
    0x70f080a080f011d1509040804090e070b030606030a1e0b0f120a1407080102070f020306070e150702130e060f01060c03021203071701062604081902160b0702 69
    0x440624200b0300180900646590030241c0d00820310313180341500a40d50051000c2c02c0d201181c20500c0000d401c90800312000c680c1d000c0700182c2801281c0c001d00071410300c2c07075040000704030041c10311001c82003a01005250b18004c400200014950406580103115a01c0c000c1c0c910099680000900c5009030114000031801540560460121420564140314283e00e46201070400300680e941d80701a01d804140100419110781307040410011380a20082c90035038031400c10343d44c00a9440c070506003042c800800c0c1c1c00501c00d100180d4142a11079016407444140c01d02c1c1525a65001c40c4009020002000761140c40207140c2a10700008590000d2110b02908885246903000e03a6038103012243c2e02c040d0b101c0240141c000311114070072401610065608429582400303065000782c12020300a0400903804900004c41e0b20500c140c4819421010a4019240c01442c00a83c54280c48410441c8603144100303603d1200825059101d505c24000501110550001c0e201300f0740d070b590640c3c58650807042040e0321542c0e = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 572087446 1250 572086196 572086201
    0x5040c1103070303091a07210b0d140a140c03070e04110f0d060f27030207050609010311030403050403050114040f0212011b02060109110f1608070f080a08 68
    0x60003012a041880c414000962800b0880e550480240c1424041103a00c01120748942c00500c00d0030711110301c10b945c1c9588440d80a03010360b04103d0641c40401d511301c3c1492804c030b1040c0c120340321138880b40781c01c58100484041c00c0da41d18040d41e25201d20800007403c0a00d003c10700111200010400b80c2030500100e00f101d120f1034484034002c20998042e28001d0084641000440541c1021141d01b250010000c042144044080d102c00003924040d043c2403003140c2d80d81410400148424200c0e59105030030900c4104240d01d82e5402075901c0085029841c42890042142c4055a1003031300110200000c0420b1140c6a0425140140003900070b40000c48855080815518074038030490601c42c8215000b98000c610000b090f000d000e00e8107030004003d50f0139500c6090000d0300034003103421200700528942c0107103501d6141000c00000c80749848810050b18000300001103844503008140c1e030000000220b400c0f2164014170300700304180315a040082503555991600000c1c080401d0140400c07484039201c07414ac0c1c0c2e = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 572088696 1250 572087446 572087471
    0x3090a080708070b25020d020d0803070305090f12090f0a12060b0f060a201c0210111b03130f0509060307050a17010b09012402010c020307110103020d150504 69
    0x1d0084888543d044100440d13401c0c005e98040084110040c0041c0400c0245030381034020800e050000c01741524500000418803035a01d80c140704142d4041060400341012440742c2c880340d03032510b11104005c0c007040700102d4503010f640c0d40c03003207c500d542c1d00040941403030581c0c80e03001d0f001c3c28a220710f00b65105072629a10b00042c1c103000244082e419001000d00f817400380c00020640d40030210107205400000761002189140c0c5c0c1c1006000c2203205104403940d820300803410002d10f0007100201000f80c07a402c1102450b08035070504140c8990401c0c101c07540343c0c99003800700310510b180a690380e41d861540c081c12000412000c1c50070a582920b800341c60445807503031740b01d0504d03603161039038880c0940101114404014980d04030a594100410401c004680e10900c2000510b80c8c51080e00b041d48119510f07200e107418442c070044c540c800c05100d40003c2c881e905111202075103034000d108000c1c00301403000b48a2035640c1c0c0b00c6c8d4100c0b00410740c10081080720040c0980190811141409030301c2c02985400e0010500c0c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 572089946 1250 572088696 572088719
    0x18010f080d05040e0a090f08041a120403030e15010e0106120e2509021b010c090e220503030a06030c0f050d0f0807020d06020d0b0d022103090a08070807 67
    0x12a40e03521603e1515141c007945140c084c0c4001e04610070107aa4000381030020301501a0700c0d607402d002e440b1884c0c846007481120140da07120121302c031140c040e0400a400300207500b40b0701158003e406040001c0c00c658080d107101e0800d10040d18085201c2030744030001c110002d01528803070607a0b40d50b03580c1c075440c840007502e000c08407039101c082955603510251103007040c801c0c0d5103101e508481e422500c40c41e02581c0e0b030350094145d81098400707010302050500c40d042c1c403020910071401210322a10b00705e4200361408049802441c000345c02070aa000380000c42e22440908a5901081c280e48881126070740d1404490800092030f4a00048031400704200c800148088040c0a5909595001346201c8c10410140d80303846001d40302140455030f0110611200340940d644040340070150703000e9080035a543c07451031035940031907440c00700003482100c2031010840540c680d450450b10700640c8040b400c0d0804443c0b042186180990404941e02103120100441c04450100b112821a00301404858801d926007490510 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 572091196 1250 572089946 572089963
    0x1050709030f060b010302090301113a0507020c0915090105030304150c05070807061706040510030308090a020a290301050102030703050706110417060f06031009030e18010f08 77
    0x38080d02c204907100403501603403001c500da00050400526144482d404607080d01c1c0144801e5540f1440030440c2095250b002c0c811003800b100360342150307030900c107046142001d0320109101c210005a96500040d01940200013001340d80c0740c001d00280c034501e042c2d1100c0e8028410401014000c031481400080d0703900f400021388065074904411441144481ca404581840806800782c80c03c1c80b8448000403020f60030301210b0040c14540c3d03129003072004903d1200001e034001500040c0140e2601d010450a00030101019060f658149440341007919074080c101c4c9001c60b403c0700a5803040480500141c81c440d055000c00c1d05407002c1c0c51030b0b030803c42c08030b0004580740000d20607940960006c00802d030000744900000d1030703214460100000e560b5041040c624a0350003582107019039803a21070142c03440010401100d41d00102c0b0b40c0600d403191070304502181d21400701d40000f2801c0380d01c0c1c0e212002050301620303140d075000c0409001890000c403070030348071081d0b900f0038451130f04010200c0f2804160f0741e40c0410580b5 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 572092446 1250 572091196 572091203
    0x2103050411010309150e010e07080c010203030c090f130e10051e100306050709030c0803130504050c04090203091b012a0303140411010908010c09031220030406020105070903 76
    0x200030182400643c0a007055000485c0c03100101088103800810a02c15a040e100186000203088405075416a190442e00d030410801c1d0b0b4880741c02654183ea001003160781c00090081c0d2507031903007540000b0070b50180f41003101d0303035100140c100d11000e810351690018070300b60040c1e800c95005544180e2000101d410607240c1e0162303158214100102408800100ca420041a003018804641e894642d0011100161485000038050060070824000038440d1680900710901c0514548810494440544441407007014010703601c50780054000483e11065800404120344259901e24040b0441521814503540541d01c0c040300b9000720841e5481052186e0400c1c56000500310940c11140864410601c540011020903844500d0138944d440000800ca007e24070901601ca00c08006000140000315990400c0c14945c1c507110066003425480781c4407008481d04002030032118007140070211400240364203407541118042d03402c030b08100c0000009100b01d4401d6802084035880302d040458007011700d440042c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 572093696 1250 572092446 572092463
    0x140f130c050f010c0f0b040201080604110306090907080a05010f0f051006030207051c05030403140c12071a041b08150601050912161d091c0e06030421030504 69
    0x1d00090526480c0b148004030141866602c1d584983d85041ca42e02c0c12480c2201c40c074680400f4003003156040f4150b1500540200c800b840840c642c0c0c200d584542c000101800e00c80c100b0fa1000c41c0118006100c060040c00810003580c40d007020a0400c10b0203801101101e00f2040d2402001f0135140c0228452540980306100c64910185c1c0f4040c0210041e40006205030f4490040015818a1800100c2040003031900b9490b15910ba10701410702030600450410b1000c2e9014042041c006081c801003400385a4004045205856201c941445120745914800309420940b004081c801402a001c149030700500600346510b40158407000080d480394007903c0d010310748003080700114a0075802000a0725010201910109031910030482c054904144166498190606241c00340045140c84030346140345001d44101c1c250501b01a90340d565075501c0c0016404000207006400c0301c09a00c075100c01e00e881d4000030f20790307500c90805003448001d18080d0540c2195050a41448001e01d80c040d009262040d504a00e80 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 572094946 1250 572093696 572093699
    0x19150801080c1f0e061b0d090f060c2906030d051804020c16060e13060806040b0912032d1504020318011104050406060504080a150e01140f130c 63
    0x341c1c000303003d08000010710144a08001c85034960502509918598500c0b0b03d41e007403000d10700d4508200001d070300b000810440000174012040905546e1080f202a4600b820300d00210b81059403288024040d0070080781d50840ca241020700b807080d41140598403c500303566803d5041c1401761800d100c2c0500e403000d180c80042000780c0317600d032950103800c143d4840404d4614640c03110700030520188007608020301045c1444000c1409040c9006444500c001c81c64080011900b4030500c036035201e0340100000d0441d402d007000100c545c00d040c4000070303228a00d622240e88074145040c21641c0d010600d0b003658507005118090462145409074102d010703800c91901e00e42c40c640300000b48006940011701e0720101c0504040540e40b884801d118103403000030540405601c2e54248410001036500303942c800c1040040911003803001c10000b28075107030301d151b200f44280c80c0805554071000280a01030079807045540b8000c00300e200174400a100305d10441c2c5118544507150750301e00001010b5450643c0250000142c03074030 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 572096196 1250 572094946 572094979
    0x303020607080709030501050f0a05060402180603060105070f0503120a1b0c050c060d14060301061805040f082706250c0e090a03030c0804020f0d0219150801080c 71
    0xc000d5003080f041d14004561940303a032070f40e90035590151034010382015200d04104040249228464100700100e40640ca016440b940d00ba1460748001c01c0184582030000204056a021380c0450312007581c4451062414925030030441d1322500b24a23014064040050700040c41e102440c030031000c0071003425401d02d2403020301031001c80b40064404401c503824464614160110b540322405414044a0b070707a004107503241003c50b411844200608554000e03810184240104d03d10750350704000c0b000980d4400503240d82c0d00d042800c49024198000307010420000340c4082402c43c3d02903801002812000c00700288500c03030060050f60310642080a24109c3d0b5001c03000700044011406410960092001d405a40c2e150700c903c454006042e140d246099009112030003c00d07406000340080b154032401c0102da02c0c580340d0082042082c0d0500e080d441202c414462500b190307070713240c42031030a0001d030004140c21a0b150b0301c40713095500c041d2a5060101c0ca800000169621300054845905040682050801c0745045c0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 572097446 1250 572096196 572096207
    0xb1908071e020708030c1b0609030d0c11060d05070e0d120c2103090314031b070302031603030e0c03032d07060e2a030703080a11030c0115050a0303020607 68
    0x100380790218000e41d04009860724040001c4c1c0843e07401100a00030103400d4558111500b41d501030341a002d0041404413049980e00420302410750740803410880064149840c00c0c1110f045003826007a4090004a81c1c00c02c05210782d400355100d101e5035107034102140f807001f003000b2050fa241140204140c0e83e0091800d00584110160381c0c02c1845800c142e85010302001011a4044e108440ba01c0081d545030102424154007001540410743c00703500720303440e50400c50760003207100400030000c003a0090000b542004152081088891491003003034150300351002848c004015204041207c1503c3c803a800313110ba01d500d008022111045518129130940c0c035484080700746031a181e644101645242400000007066070340c0600e4948a0601001d48030100c4500c0626090440d12403290403040c1b540c60f41c04610b42c40c0042d104054a40200080d600c800e20b4080441c0c129445c6004540107010101c2d91000d41da02c1500309054148c40004c280d16642e45942c00d02c404c62845100180c0142d0021001c80c5e20755010700b = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 572098696 1250 572097446 572097497
    0x6070f030b031f0c0503010b0a0509150a0305011404021819030506040302061014100806040b040204080307050f0102090307090c140a020c010905100c08030c040905010b190807 77
    0x909010400d860312400107420145843d04281660740c1080b11581c0803000d9100d400c49410050030540e081d9410a1070000160103003500e1070701030050001c0c84200d165155034034103804030900681141d48268842000b0050300d401e120300244030810701d0610259160034001d41d14489c9046008299a072550401c10214004440c0b00581403108a20040045003041c4a0075225502a400a013010700745540d4200b6121800d6000211000e00c01c0c410b0655a42c404008003c00140c0340703481036651300d4000000c0c0041c480d0710030540d0b1003803001030001500c40000c40a00405800b80003662404400868054280d2007a181159859040040140440c6850b40e04c100502401c62901608090291008800c1a03018a8000001da2300c20003032100c103580d00c4100d84000e07080640701e901d00c041c425800684500781042c0001e025500100000300c600310124146c8004110b205010b0013203594960825800351300400ea148059040500c2601e00780b4090505540034005c0c070380d80e0710300351070b00d080c000c40440c8402d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 572099946 1250 572098696 572098727
    0x302090a08030a0c0b22150609020c01140109090201082a070b0f07111e0f070b070201020607080606030c0d0e06070801181b050f04170a140109050607 66
    0x588404907141d032080020300000203454031403011000c0b00e800d201e400000000c1c10000b4040001c0010b899042da00c00c1e0000c1c04561280e504001c408841881a02800752500688a43d40c8086002640301005410640801d42c145090103002e9072110703880b070300359031080702c001c0e011461202c0400c48008860901a15041c0348000c2c40e5020b102d803060720307030140d44820020340310350031003800740544c026035405156084003646c2051460322407070894080e210200079025842010a20f42e401d03014840c02d102200380c4144100c11f903011151218000e07401504a41400c2e0b00600c14600010380f2240101c0c002d9002d02001000203007982d9034100c58245551100c1295508070351070710040c000340e6208120b080e0080744940c40300c04e103d40c10311108140c0020a4204060b5a9090116201076420a60304841c1ca2070b94919000e99242400c8040c0c020078455035000e8044680d5100c046100001c011540d1405135109210221282289000890a0f91942000a0329582206002c50301c00c6000340c40f801d46160340c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 572101196 1250 572099946 572099959
    0xf030e120c1006030312141e220507030303060e0420210a1502071a060109080d11120a0509010e0a180509011d15040609060606020d090602011b030209 66
    0x6065842e1040d203110340e1040b0003140c1000a40c0c08095454000c0d0394207041c580c9025545071400c01d061115a0700d15800b000301d10104c41c001710b009641c0c134130900c08040b02e0750420b482c25818a460419503d8005200680000f840c0080100e07410240300780d614011030700312640c011010054603841940d1100320b81c0701382d44a021360710002401c4d48190080e144d240d10321000390101e140b140c2401603d0a541500b03041002c3d204000850016801071907040621110310032500d01130b0354601c0142c2d5904241d070042d442c50310807195503842d10703940007890101c102c400c401a60807581a6010a02c150702484a0410100e00c0520003024113503c0340101c1c3d8039004005058111051380d5507640907108100040ca0207101c0d0300e0700304002014809019040c807501c040c0702e20748000000c60b10943c1c1c0b1003e155080708260007558001c02c080c05042c0e003103500e54540041007007040f50f070b850001a42e11900d15140b0350205020000c0090114010310440d02290541c060f604400104d0440c104c1c000c0d802904110b07803006 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 572102446 1250 572101196 572101213
    0x20a051014180d0f0b09010c1706040b1203070606060504050d1e120f03140108030318011b08072003041202040905030309030a141303080a020a1b060f030e120c 70
    0x780e45403e80e00c3c50070300540c224094030314a410302c01c0e084540280081c21513810020041700150748110380243d80c000c4007109000580760140014080d01c030300e9040c2079102c41d1024039500e00040110050041e41d12075941044016565001600c250240d44511f0360f000d8400c1d14a0030100d0503a2040c58140914036680300000c100030341e0348062000d107500000700002d0045900e0002a9010320031428083c031a54003ca450f036140880c11030b540c4c8402044041c04c01000765200032f198209412081d00700c00c1c4004100140307820140010003a1404680c0d101c00510b15198039a41005800b607503d04a688030700c01b841c60f09007401c81c0e4035281504054100d070060713a04c00c480004590240003a46c000c0c1c0f421406503a0b58100088002c1c05610040c1114000410800c124013420b00140b0b41d403000c80303a000c1040354446884440c242c0c200422440080d013400f100001150301c058500700c140c1d042d1044c984451880d4803640c0000c40441d420306040b2041f40d4044070341c3c010346401d040064101201e8a01c00c1701e0884 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 572103696 1250 572102446 572102449
    0xa0209070806211606050f091023030402010f031e240b030604060f150804030309050f061807080c240a020328020c150408030a020a020a05101418 64
    0x40f80310540c50f0000d030004507800c412040e026000d180140894505030b03040030072849802e0b120b4802e4510341403265110580c81d5080720b01440c1503903a040e180b042036001031034115590807800d910859003240040d19650501107228042c0c1308031440c20b00c000700e010600e41c00b108221002440c840c500500d042d04080c1c4070b041e00c00d00c450031160140c00c40100203a102d04024051200f5030b00305800020f0150f01001c018000b0006a040051400740b862910b00b000e80c44c0d078101500208900300015050340100341c0260f04094000404c5400303413010604981105c2c01d01120300b0380b60801c50041c202d00c2d40200b03a9012140c40c19010718140d1071f00354400c4007004450700e00c0300246580548000d00150b007000c0346c2c8061100284140d100003412024001c1014121001d0094680c8403503107109200c1c6004030491031034910f400701544c015182c0c10003101d58800707040724080d55882c3c02140c1240325034008807000c00c503410709021900445025880340c001d00d500c110b07038000d0142c005913603c8180c8011240050907a = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 572104946 1250 572103696 572103739
    0x10305071b140d1805060901230d020711012a020d060212040c06090e0415020307020c0603150a080715080c130b03040312050c040515130b1b0a0209070806 68
    0x81c40f50b80c1d01c800d40000780000d0030034458072040d4001441001d042c40108005d980115060081d5903400303000054107644007800e200c03103004010441d4106840403807000c0800a480300120080d4109880e44240f00941f420450181841150450442203003e10180014200039a185c01203520803d00035090000780c1000310358440d0f0460302600c0100c8250810422182c10803208400f8207658182015149030035118204200345440d401407505a0010004405520a2099168403a00180030b07540d00e0408400c04c94549160840c8c1a1003940a00310004645600107400d404540c2d4500c61200004080442918500c8004100e41d0440f40100800320220100b444080040c144020b1100c1d124106070800500c5101940700806e40e50b4600814030030f40024201c280d0f4200d171000c542840c030015200707107105e159020310709000c5040311003000003141041249014140c8009120341e80310071401500f0f603844e6200740725807021b508100c8000100d010301e0b200ea13000b958060b2001c1c100100c4509034100fa5040c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 572106196 1250 572104946 572104963
    0x34b090319210606090b030f0105010c031b0b0702100612020f0a18090308060d051c111603060b030a0804050409080702060d0b120a0c09020c012408010605010305071b14 74
    0x1a070070b0b5155003c0c048640c05c00c0c000006801034944090452600c280c844040d15410300885041c04540c12030030003058401c071040d003128081d1b01861105905245402562540306440c4c0a01600a190350b18910030301c1c901c160305c1110b80c0c5d041c00c114041081c5d000e0085804096814940201c200d0710045003658540c50114240c1e040d100c800a581d010509000344000c00c083c1c045032040d0719204a00c4046a800031364050501ca003910b46503401207408d40241c2c1d0616040303c20342c2d0b0600440500b4000c02c1c4a840c41c2c001160b0069009000c01e50074001019218003420b040246104c005010034021411305030300040d030107403044442901e402e0180d00000c489800000d4158402c0b0380b00c0d40b4400c9981411940804100b010701d00400180216135910241c5090714022507510380d60116200c004000c00b500306604640c1c2800484640860701620b4280114007401400700b6076003080c10010f0554886c1c803c0902c2081c007a541c154110310b102c807111301594881c083c150b40f90000d0010101d21990240007101 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 572107446 1250 572106196 572106257
    0xe0a1203080f04121215030615080a0b0a0203090a080408010c0e09060609041512030c1b120311010906050a140c030403020a0206034b090319 62
    0x4118104a15005206540c000c20b01c602d40c040c020240000a1000d800c000784071660750a03c0b8010303000b112091070082042175004854030803007030f40000032300500398402d03410b0010031000b071840036072601100d80e9501c2c00210010801a9000005a60505203a000d0b5030003c0e032002c25510400b24544411556400542101c0c0669648214100146800c04c120f14041c030002e4840da10319103021000030782640208071825000c5e07500c41c010007500c103031030f81850030240c082c5482e0305001d003107242402010b900140b1000c40766002410b4800c3c06455220484604441e0400500b0080d000d15a03811104003488842e440c05a40d00e4251781c1c0c0c000b4031640500c51003054000d40c002010b103071101600001c5100078000b5400f8100030000d001c0420340c04150390200980603903150743c1c1c0351618054031305079804a2100103400f00d141d4803800c14400d0542e601110145c0b4616003500c0f00194180c00c502c0c0c80310141d0b1012a60b610401200c0b030189007131700e07640e43c0340e401505144507032a030200000b205107000c008500 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 572108696 1250 572107446 572107469
    0x5070504110a030507020f030a03090f050604060b0102152526091b0a050d0212060405060a0b090f0f07020c04060902280909020f040302040c030c03060501050f04150e0a 74
    0x10301802c0e60600c181d90b032040305c0d48000d01140c0718140880307443c1c0c400e404c00d12013055141e41c5504c05002c02c90200302c01d210361050444d943ca10302410b1090080070404580e6005024403249080c2e100910343c002809100d004040860705580128032241038451100d01c403051081d00041d10784128500c80c045542c40240030a0101140790040c441410845aa4090000c00c0c01d0701c0c160b00c05c03548883d055001610015603c990381e599150000400c0d031310203010007000a1281401704000c015001c24800d008a01d004001c0c40b20030a110200f000c01007040f99400452a002c3c030002c0c8445c42162100d82e0044200e0060b1703480700b0300003000300701540e0107500403192980d000112070300380c020303007000c85402ea40d5030022100d42440001d2009221802074400c0c601019004900b00c40002914000c0760025540104104400c2e5501207018004d811024460408240780010000d003d5024401305ca04c26040400a20314080c10905c0d14043d0304100c5503010204600d06484180760380303402141030060882100c40 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 572109946 1250 572108696 572108707
    0x10e010e0d0207061706180a020d1d06060910170c030601060201050702060a0e1603060506040c020601141c0b010609030c1208040905151507060b041109010c0507050411 74
    0x8851030900d000781c0000c02c660000500f007118951111440c000543c0c60303540100c40751a540e00107a83c0c00c007900304d4100d8414211080c068205e1159001340260f1402c941c0602c080e400658180c50140080c800c0162950030180004d5614a07158903040d61241d0922213202c10507840b11422009080c298a050019030700c580d2a580b801c2c40c0800c080d50061400c0d100030b00851804842c000e4540b00060060708aa42c1c841d150304011000c1448003413800c40c440080901c03000d5503410100302801c0d09031034150060307142c480342480c2c1c684041940d505035851007041869045940307040c802c41c600c805940c598010041802c100c0003800000360310b03000f07103065500c10501c5c5045041c0005004d4842e44a5184a0040803249001545420507102141e8109900181c0c1d583c4600e151408038030840c58003584800001c00007211502c00e40007800c07080d402a0070800c080d02d480b6050000b103550b80041c156160070207002412803076101c0c0c00c03541e035000c4c0b091042e200c516030750740e01040a50b030700e44211130003604c40400c0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 572111196 1250 572109946 572109971
    0x90c08070617040f030c140d0519030b0319020303160b1f060e21010606110d020115140307091802040b1c15060f0305100606090e060904060b03010e01 66
    0x4541c08a28a095660304050820390b495002c01408040c00a003841b0150003032000380b111118801110005401c2a201c514680c0d6900070113079404900040c00162072010204d88503032007440340300440003010300203103031860804810143e140c68006080f41d05200800503d00c95840b000b0300b4111613032140341407002c182050107080c5501035440c5448a662811f0910070489140e1000d10381e1400300042d162181104450413507001c0e401ca9641c1803032981c3d82064000220140d110700c050072001c0d2010f060710380c10403503010100c1c242d8021039601400019440024044204070f01c84450401c40300070104d40c55140c0d51448601510201000c40000d403080414900560515000301d02c00321100316000d4944295000a01654000044000c0c000c040003110301c0a01981981c008006030401e4100180050303601c0c5002a07413030721b002e0340700700540b030400600042c010b010741e40d4a42900e112031030340003807035981d0700610000300c40c0144107581d074a803100d18910b4607031004e110340600c0c415100f0000c54585281d52 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 572112446 1250 572111196 572111207
    0x70906181a040e0c0309150606040305011e0c0504060206150301090209010303030506030d0507021c020114040b0c0c0d0807110402040b0d02070c14010906031e0227040c05030106050d090c080706 85
    0x42c4000c20301360040003007000040010881003c0d00c0c421196000c82d640b10600403403c1d501841e040281298601000301640d1041c59428510200c8840001d100280b1100011074407400b0311310983c0013503804035000c2024045a41f04000c10940c010b000018802d00d29000504004420b90013074010070b90340c205100d003a08042c80004c43c0f0200a0802c9403600e1f107268007050100d49a50b10304007403800088900400c6a101d04140c100a0814070b1180b5101c9851b80d4124600f40d00140c1307000224480c01c040684981448050740300801d4020032038074200210740c0c41344000d182c46402650b074059404c12011801c5a0440090085201225401a106c00040c80c1018100c0c00c43c1c2c11000000c00054079202c02030382d112130b15106642142c44c011800307144d100340050700811040035194100c0c1c0003040314031209100b58044035031403034030212011000c11044d060200712403015034031705d00046040005000d8580954002d10455044400002e401c1034a030b2601010010550003801982c1c11030300c070411440b607204 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 572113696 1250 572112446 572112451
    0x603062e020d080f06010e0406030b070e041b02060408071e06331e03023703030507060c020c0a03050c0a05040b030d03110d0f050106090806070906181a040e 69
    0x181000f01150a01020141c0301c018024400360403c4054140000c4907200c0d074000f84015075124101811a04044030068140c0355010380d01401240351034940e040c12880308120a02140154000e0089a1695210111b0550002c101039400411034240003040c041c074042101542d0380038101c0040d0808c2428a40d44003102c001c05020f07c01146084030804d024500b0180c102200e20b1440400600e1205001c2d0045084541d48069480b503c9080d540000c02d80c1e0000d40d00807200c443d012800200103410107299880742d2408040c0025205116400021300079038000844020343d40110f0750341c444886c00007084001240c1045a40d60407441b0b80490303600b0451003841c042c00301124184a1441480e0200b95580c1c9001c402400b015120703007400c2884402c41c8101e1b25098040d4100780461003482500c0e030054030f02885040c0c00155445000105c400005c5021405050030b652401001c03071502c0c800312020740b2002e924500b50380c3c1c014400510001443e21404084400d01036040e2039034a800302108000400 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 572114946 1250 572113696 572113723
    0x109050906070806040c0c2312040305030711010e09130605161202130302090a09030210021c1104150908190c03030f0909020309030c010b040b0f0603062e02 69
    0x181e028001e2103a08441041d500210a80300000c0d02441b15008644140001d003015101c20070103600d0408d16410b20305182e04140010b002c0720a400d08810020b81244180c0c0f00140540c0c1090010030b002400301e0082c11034082c0149042c1e0745002071840080c1c1492070964070480004a80c2d4890003c01542d40101e950100c08107803000c8005000140c0a80390710155426189050750000e41c059001031010103200265401030000d50203450400ca81400828402d071066000d4482c51001034549811402203402541e0080d00315011884042040800307400038503800c0303944040500c0081003140c4a5400c40c2410990f40e40c4a20380c80d85082c00c0305060012844481c2d40940040d5188800b10322110365080440354103282880c00040110002c4079000c07a581c01c51342031240000240f095424001001d00900c03050390008116200c031040070882100d0189101913002102c0381c0e0407040300d24258020310b60018010305104043e001a010b249900c0a0100410704405404d072038007034081d0303030400c0701e950719420 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 572116196 1250 572114946 572114953
    0x150609042415050901030509010608060c070b0901090f1b0308210c091011010204050a090903080703090b1506091009030b0f010807091a030601180b0a03020f091e07050301090509 78
    0x102c108014214403130003010701d0616480d0f2021925400c000d42c0300c1c0008000c0030040da6114205407191610660004509450000080c0c02194000406100700980154000284400c03800b0541e607543d40140071010b0880d00c0c0103419000400308a0300d00062015000b9500000744210f24008000e81660000e0040652114280013185050b10348940b0300ca04280c113030520401c00c4003054511806840b60b40c0081e81c0001070036100041e60300050f0400c560f810b10a403955003042c1e030b52035811011905030900180291000308041600d280f01c0b00c1403002e2a03000030b0101840c040c80c0101003035414114a061000080c0030312410000d020b0005801764000c6214540000503502d0070030001c4c0e46080a000d00041f0698942840380d1941104545985240028040e20b8156941ba416406030f203285842c1e1600301400c14a8000451814215a4003941e60041c000f00e03400c0c00c0e01c010301c0074015004000f02005500d140d505140e4100c003c660301c2c411503c0340d607401d99030340c103000445040c0d441c05004074015a0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 572117446 1250 572116196 572116229
    0xa0c24110309040e1603081c09050a030f0c081b010509030a0804060b0d0501050403080703110a05030118060b03040c03060b0d11010807090b310b031506090424 70
    0x6004421a20020421180840e010368261004d5052250b030f6516884444007400e000000c00002201400070045443c851458416104401800755044034400511580147d0007040010740504207a0307000000740d24010f00e000403603a84101c0d0300c0e03022442255440013000c060041241003402130b50340c802108030285082458040000d00b8a4001400050801c0e4450346140750684804d2000840700341c1100090045040605002c2c061500903526100000c0c02c202030b0300c810385070306411542ca0308140c0c0e945a1441e03282001030085400e840c50303a0140103865403800a0201c440001550140740240342c5130400b10b00c0e514004c000c9444050045000c1c02c440030700300c40441d040700100701042d0701c01c1c2421b008944c0c60550840e450382003908400005280403502e040c21403140f1b045910302070400c01b111b082e000840300c40c4e900340c8030301072141312001041000020800c440a00c81c11880b20701c090021420300c40740c0000034007a02c03403c6d201c1c0c0065025a54501000b014202c01c01c40060003406108602403 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 572118696 1250 572117446 572117477
    0x6120501151a09030309100302070b0906010b040324060609080624040207020d06050702071d01080309060f190507200603161710150305060306010303030e0a0c24 71
    0x1058040d501074424440810640c0184e1401c2c8200c0d045420300030480301e5400d07541d03100030300250084901510342440220001c0c90382c040c00103d650580720540c0b051414145160b890001c2c071690312005048400403268480c0d440c030741c0d501440c40a050107464151455040c41417a0f46498070050000b503001981c070041c480c566690b0408100c1e6000150303405660b5403903134008150003640a1400420007482d00040042141c0e01080020548500700e050b100070705818401152480380a0041c101c1c5034100f040707105424038044000f050120b0318841c4503814107d484010f12007218101641a010230b1002507454200300000551513041d6035861550346501c80c455000c5032881c0002070904d1200d010a2105000c064041c040b84680c0c013022800e80d82c0c580c41c15060700c001000c1c4a1048243c48a9005403480501e400303030068070300c1200081c00418890b031179510b084000e0014890749070514055140740c0000f141f500c41c00740700500001001d02240e04103014030581d40101900510080110a00c171a01c0c07038 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 572119946 1250 572118696 572118719
    0x10b1e18040b0303070218220b010501030915150609080a0c03150906020403050106140306090d1b050d0f1b08070b0402060c0d08073f06090612050115 66
    0x1030340c040d1400589114400007207442c5100740280a58012040208028003000a1240a20594951441084020403036039400109480800001d0900124200500c200d5110354082d140301ca010304c0403403040e0101440740310700300d8086455044441003101c1080c40301c03d4120201e03200130302145c802040311460903211070000302e056003c001c11a45101c0e8014501c810541c01480700741d50410800c56030f5903600e10b0064020701d42840395140c3c442142074508241e00e00030907551b125a00b59006040001c8000070100d03807007110840041020001c0c0701180c40400c1040107150695401c82d00c1d0010207403403401d40502818200e80460680291400e00c900c0001d40712030580707a20b1640312442c084a601c4501c0021418090403900d299148079004075100c4065003e0348450055003540c6400700340e212260300d6900e4202d44004110282c2189221810000c03101c0800411041400c18001410b262160f42103000e9840d40c0d40b004089000118500707040c80703000c1c8145801c40260460303903c062441d10055245 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 572121196 1250 572119946 572119987
    0x13141b1206071d031015050d0c0303030b010c0812191512060e0105130303050a0b0a0b0306010c14030a0915080105060a0311040f091505010203250b010b1e 68
    0x1080f504240c2d07142c2211920000101410009003070311701c40a400d900080003440c0400010400c0344800d1800503d5080c0400c0d134081c07084d0880449c10307200b1b0540d1030580c0a0400204843d04000c02502c1c0d240110b00c065000e42044a00d101c100e440604002c904c40041c0c00d441e246e400c0c1180e141c0010800321000403c4100c04446071380b206c000400300723a404d08100420f102014129207500341810012a84400c1c0100c096803486500d00b000184c40d9191007070201d444500310503800c110800c00900880030a280550750201c0705140007144101980c4d6803042c030080c0515103400030303840400d4003020380b038200320007801034594442100c03034002d40f2260007401d9643c10311445004105c00a06480000c1c4290031041c0c02c0100d8400c02c07a52603564011f08032042285104412216103000420010440008081022100164019400c1c94040c1812400307254a8174000039892180c60041d41c002284505420300820002114613252140d000090b00703040f51542c009250490308119004418158600b41403 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 572122302 1106 572121196 572121211
    0x42408070c0b070c1b0b03090c0303071101111002040e191505010302090a170105090d080f0a0207060204090912140403150513141b1206 60
    0x11040641d000004015800840124502900c1018242c4041d4010004c000c803806001c1007000c030302c403065032000180450100c10840b440341c041c4485100e080c002e5000e07601c1e089659484030b5402420810040c1480a00c00000a51810400c41401d0740038418108540d0343e03442c0c0065020041c0202d030008070401240fa21240c080849000b14001241154076184000741460010340c00f0f5017049103581c1d080b4080640c005000080030410b42000500c4c4800014682017000300c80c0e081c0044a44054180010306090040424070384141c10382c0956144001a1250076034900300c8043e2140740e01560b0382504101001302171114081080000c0300e800d80b603600c4150240c0344001160f001d184005003049010084010481710160000ca9000840c400d00700c601590980d210428290711644100d05948000c406076101da1710a861004040800c0342c840d5114492800007507a900c00040c03c13403 = true := by decide +kernel

theorem cover : BRFrame.Cov 571942446 572122302 := by
  have h0 := BRFrame.cov_init 571942446
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571942446 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 571942446 ≤ n) (h2 : n < 572122302) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
