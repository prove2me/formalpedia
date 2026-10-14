-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2683
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:25:38.68361+00:00
-- url     : https://prove2.me/submissions/80d17b5f-391a-4d9b-b263-83fe0f9c1149

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 482374100 ≤ n < 482553956 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 482375350 1250 482374100 482374103
    0xa0512072321061c0b04060e0a08040612020d060306022703030405011b02040c0801080c091603020a0c120906030510080d2a12031401050325050402041410020a0b0c07 73
    0x1800c050030b418900c4c00c03d01100071820b025442e00090b5003864070382501124402004004030781c00607210384001c100020250f904461403400c2420a0020b1218007000174840d0f01c525450719442c081c1c1c0401401200c8e8003a180c2e0200950841600307858950700c03905610b042101180d415402000705000b9548944810080c407400b4100e100c0c00407807158005000d46940844c02c0c0001403801d00100302c0301004020041c02c5980a03940203880b401e1600d64081820031284808c418986c0000382c0043c070620900d0503210054000b600300c0d021410800b0010b02d292114412140024186000329211a4000c140d507001c8565840080c1500e80e0103400980e41c403030032101215000034805031100300038540024080407480c400d009801c1403008000c2d000e421107804da1241c0c24504501c1005000030380340000c0c80b04001054005001c421100009004840f0b0445d0b04503076042030002c00d000507032032204000c03e564084115642e900240d40000100d1356a82800c01c06010f2089040100310030002c010005e20700035 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 482376600 1250 482375350 482375359
    0xb0a082a09041d0109150207080d0b06090414060406090204080a02090403091505040e0f0f040206030a020c0f1e0d0e010813061b0207080d080103080a051207232106 72
    0x2200c0708061000300f01070b000b4540405945805c844001c1082281d40d01d0b10141040364218101031698075102c4440c00391038102d50a00b944c4880d005480d076a0341c001d0301c481400044c0107102c61070303121943c0804290b0039a0024013403810304401050144c0380d4001d41d07058510510050080c00c58980030030102345400b40055060186021010458003a01300101a4035a400d0310307240e0343d079450919a087c0700c500090800320760000c2181401700002c041904240c01c250101d8940b500c90b00d585d045000240305481e0100c1d151300c5400c048440c9003002140d00820811040d5000005034603000005403203400400342d00c00000d503210072100ca15809080d0740b681007214070752034124660a41c1d0700d84088402001060b15009502003007070308016030401c02e10300a400c03a400542078400745200007408860060200401c05100401c40003034151284040d5000140c4641403c07030745050055018214940e015681e2400e2003c0c2429025a501e070001269590b000c40d013542c8032a011130b11400710005001410042c4d01 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 482377850 1250 482376600 482376611
    0xa02090604031208060102190b06010c15020a18090917221206050a11070f02031612170414040e2a03150610050c0f070b0a082a0904 58
    0x8030f034a07540038035188461034680040c0c6003015400640b404c001c0d4081d040c5e010a071040081b0008040048c00b6411507401c6c00e00c80d44000951410b42d000580c1c0d02c90301d4080340c2c4041001d40d40590f112415281d03aa07000c407a05540c5a0b1503919420a135044010060003425a440000b0101c10981e40105211a40001c0c07168954010019418043c41158480202e042d50400b050003800034512500c1d03041a1010b00401c5910480400e1800794080c0f403502509030740103d05020107645050100000c8540490f030351242c0c0580303610350602000c07804441540d0205a480f40722030310050180403a0195481f454030340c03030000420340401018000a00710070303400340124042030002200c0500b614110301d181ea07000b55900748020f130506250801d1551041c0d04d006c0a44280b0000c4d0702c401c51070b041e25071401e1034100c1e41c60880010351843c029407100307503540900c182140055800109405440c3d0301d00d0701e48c1c0e03841080c3c4962058555070030411111920004003541c000200c5240f4900410360010090b1002c500c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 482379100 1250 482377850 482377853
    0x140615010f170a0606020d0c05060a181505180316121211090310090b07050f0f040303020c0901050907021c02011e06050301050705180906040b03010c1701051005030a0209060403 78
    0x2403030805a8480580b01e41340c51080c00519014000604041c0c500c0c80c1c4102c80c6406034403219900d00d00900400805035480541a0440303207000115100c0d00e4000c0c180d10400003000c078003c001031508030703009007005031903000040c520790000c001c488a120514108288195881c0c030390fa8021503e1091007402c0c400b42005034007042103180254401c0d0701e2054034040c0c4424880742458100350014031038101880c07501803003800043c5983d605a4008003a444c0c056181c0781401e08441c160300c1644c408103c000c002203000020180d0001c4c0c1d0750b810100c15102c02c40c0590340ca5043c0610707204140d031400d000d0703081a103100d030550f03226844402c048011b510000c140190b02d00781007429003004111080080b900c4060600160a09010b6540c01828078503049151500c40e104c2600807180302c544052084060101044159a4a400116140302c008000f00450000c8031005070098004600300c1610101c0400001502e150003c0c0d030750380918640d1242c503d50754038100041c000750301810b41c8980c046000d100100 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 482380350 1250 482379100 482379137
    0x7050607030b24030c0703021e0703020a0504050609040f0507051519020c0d110a210515091902120601060503090c0603010303090b03090c04020d0603140615010f 71
    0x24020880364800248603490718042c0302c0d400005107001c0000f8400b84078801c40820700b00c0101c9501c03006240030703180c8592062408078200071105220081000c202c0703400041c0c1c1c0d500841c000c0c08480c803c0b0b8070700044c943c2e24030a20043d19000c07143c0e954044e888c0740c000340104915482003034103140300c3c00540e40403603100d000080a1000d1300f880c1c1030303000c1c0011403040c00d1455200401c3c401402c0c10f000400c003141003000000c4100c00e6018005143d0b100000b07403242c1c1c50301d5900c0000d0241654108510000d0b102c0880160101c095420540300f610450501c1800c01c00070034412801000e00002501c07070701c59030b0003200754a40b5080d841240c0081c0c140c0020440200140a081c0c080d10341641c6496880c18442d034400e19200240039514401c4004000400000350410050001c41b035002c40c16076204e0341d42c42c0310542001101030f140c98020b40005030003031031a4815072014095a118040304071600100c046020b0f5a00411124540e401c00c98100205075503005503000804100107162220300d08105e00c0101 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 482381600 1250 482380350 482380363
    0xc151305031f0e0c150708070804091b0c0804120f020904080306010f14030a0e03120c090114160f1401020a0f140304030903110d05030c0d020106050a080d030f020705 73
    0x20900c0045080107010007a480c0c0c0030f40980050034400070b11403501000001403240c51084060315051000040030402c00003590300741d684080c0c2245007030b40c071142d55030300b4000a404642240400c078030b19040144107650060841c5071003550010000c80c01d080c103003800c8401120b89540159100d41017050780600507603841041c144218860183d46840e8202080091320f4182c082c100c40e030500800a10803042039040406803640702c450b14401182500f003c3d0319035411440f806400c100044415020010761b10356010090855034002c0e614161248122502030306c1d207010314041958111803032025240403448407400080428042c1c89010350341c0c07404102503402c9910844030940818481308500140030342002e08400c280141d80740c0380d861880c01d03540041070100305002c020000c6003a500150501e480e003102010a06600104599071640070400259944c4450f0700124015801c0110115075802c1002d81c0368102c5001000510325840421790550103010b01c8440703840720726403c3c400c00d0302003401000340 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 482382850 1250 482381600 482381623
    0x307080c0a03030608030c0303040605060127150509030c12150f0a15060e130e0307050f16180b18180d030209030a060e10020403080307020601080c15130503 69
    0x1040c9107070542c030b0050107890860744031170045d410a00140b0119000441200d138090b07880400081c45c0d40d40c800042e1001c40c040c10212104c0c00048644407042140708a40c1c0c4282d07403441109403c2d8065070241141c1c2c5109490070190940c00420741c40005040081b12040ca0503402401e46901d6009501c030b0348004e100c04ca6010110f400b0900920411003568401c0d20603400b0003c1c0d0a0800b41e08201e0040e25109004a85500035010440003d8412510354070001c4440d616106881e82c602c0710707081203650b9541803043c0050a00480160b03d03410700c0d004003490101d90a65048034803818401040d100104081f07801241c101800b0071294004103d0341e00003d204005040d500c046032075420986600e00407108003c4018180304000e144199640010810240c5d9840400843e1107500200c4050400900940131003840f800440e01004105607880554420030b8190700f01e490580e47d5144065480305007668968010b17460307845800513124030000814007600c10002840070b040d03031030000c01e20b0710011001c0c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 482384100 1250 482382850 482382853
    0x240c03031b040b07031803020405150102010609061d070203190c050d030911060f09040504230a0c06050a180806011a0301030c0b16080a031a090708070305090307080c 73
    0x40141c24091103100100c5100d10815071410141000340c001c003140300e180c0000d0f06112045c030400d00c40d0045207075840c016542c094814005070a080c904200128140524207000d0350800102048071002132203450200c90b04448881211445a081c00c0302c8a00042c11103021400100084196408100b194039040c420750b0741c1309400001c0354140301d820a0300c00503207007042500b00304141c004180d1041c80c0b2004201c1c00c4900f80c1d9180241164940c0780e109940a0503082400d12003004240700c04010034800302c28100e1381d02103a01e00d0151225485140b8140f000700804481b1105100a80c49034015000d04981c0741800100d41c254040d00c500c01443c0360344030000da540f00c6401440b2100f0a0030041d803110a0042080e811541965a04000c2c1c0d00d40740654540d9200c0856420200c5104403001c0480903000351905a88807100d20008002e0b05c041051020101004910500c5604150385284c0c8500101d03030b200543e030f4403a03003802c8002e0030010307240d0303555440180000408030300e40c0c0c0000c01c201a0f4180 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 482385350 1250 482384100 482384107
    0x151c0e0c100c1410051602070303050a09050a090203040c0605040605030f0402120f011b03150509070315080609070e09030711060c010608031902010c080703230a09061d0c240c03 78
    0x4c400c2c0342650ba0050405c00f03400b406040c0740d0f0075181c00103806401d0341d905003000c50311900400c600301c4400020354440d42c0c0c4030079240d4001070000195070085015900505a08000c0d80d161a41503034148a01c1c03180704005407081001500702c010703407468181c116100400c000c0c0181c02c545141450a65030307108001e1182d66400820329400c2851800d02c88169a0741800c1c404603113442290090507003a44204e038000c865480001c1c00e4688a540141d2052094840140ca61516214842e90b556000c861140b1980f15003400407030480c01400c02c1501c0340c131200c0011450900f1a913201410209110303900d64015000f40000d5901000a004240242c460b1400464480080507000e000d8508182e0081055914114000141540c08000d00754446291305020482440000c603286000d4540c1e00081e940300c0850301070110400840d044140310314050300042c0421010718514040c1c046000342d500081340e01590780d00100d03007000c2c441e90040460744112410515800b056100c025805025080d02a81000 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 482386600 1250 482385350 482385373
    0x3110705041a040e010204090905030a0201060b0f0f0a20031215012703201e100e150403050f0f0d0203040b0d0b151c0e0c100c14 57
    0x4200400040808a03018011100840c101c06005098a440c66008a4496022807000701094044800030240000200451415030600680b2601718804000065080c03078000225454400e0a03520640c4078400002d140002d031607008900ea600c0740704940c0034051610010029203030034900c0110300b8240c0401540c1d403011442031000100750002c0800700f0102d03d02c0a400c0c0641d038015034141080c100c0c1c121102d80420b0341681c2c000700a2080e840240150002e4048800011461001b001403440a80c1c1c141040051041e21703104002c1e10240c2a60002c1852080d07403806c0c0c1c8180c026003071020004e032000c2a007171182441303240c090313119410680c0d8030b600800b814207000c003041204020304101900034200241140c1002512841303240b0405070b0012002c10007004080165008903680740c0f004043c0c1d5446c0d9041c00c403001c1d80782c2085403a145442864004103c40c14400d02440300115205000740008070700d080304000e030341100c42c2c3c002e20401295585000000c0c0c500321040f0081240f08004001c9140c20707 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 482387850 1250 482386600 482386603
    0x1060f150e0901180b15160c1a04030303050601110c0603130606080a0c0e090d0f090e070f020111120a110903060703020304050606010e100f020f150105040b0609010c0b06030a020d0311 81
    0x908945500480c07030408600400c480c0720081c1c4502041f24010140d011082d420108030798561900000ea0f040052100b1400d1060240001c3c821203100b510140b0180e07450000541d05d6581c1241c3c415565006403958101c43d00d4840000c580c0b06c0d0310307507040d10024101c1352516000c071a5150403074074842e0f20050343c90017440203800c5034400605541211415500d04060059150516041d00744140a280343c11980154001c0c411030001d007140c00845172003860a140010281002e0304020800765282000e0886c20010941c112410072582c4185403065031180400743c1e0007004010786c8010100d5050140b20301c0c650303060240c80e000706855900941c6034101410002d06000010340640d042c4107075082040440d4545081900c110009400c20400070003c5100c241d041075180300c000319003070185031501c0041d80700080d40300341640e505071000c000031a005401e024141c403030700038003a0104040403210701c0003503040c007011940703d000501660544842a0b01107000e81903400000c17030210b0b9540311103a404910 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 482389100 1250 482387850 482387861
    0x131110140403080d0b060f12040204021204060f06060e150d0e190b011d0112110306011e0e100e0405030d090f02010e0a0e06010f050c060f1801060f150e090118 70
    0x10b0846d2041c0c0341564141c8220310750320484c881045070310905e100003800c1d03541d01d0341956100980c1c21200000b61405240c40c6002301345165a50300f10714036241c00801c14611074217045084e544040e268802c84003507041030860507042000484036983d21000d000e250b11a080c0039000348201d06660015400c202e5141c001c01c28201600007004501c0c854100104100148108a0444e02c079985900090a02420900c0320402407266454151041000010b42802c02c0040d070303801800e501481d00b4a1a4541d107903010020001d890042d0844e03142e080900c51540d1224141e90014440d0301101e251102d44e00781b42050302c1e0716000585003070040000750000d42d6001165000d08800032140e2a80c00d0703081071500b0b450b558000e0a4641001040c4d828504060300440407501418012001c40702e4900d40350b11550511003084a04890010b6403111103ca1b440050164406907803c0c0314081089500b800c0340d11104d00c101007544801c0141e20b40303051404d911804981c41c040c0c840e00580c580450006032401080e00c0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 482390350 1250 482389100 482389121
    0x192109031a06010915030b120d0e0405061020100c090929010c02031b1c0b040813090516030b12070b0f12011409131110140403080d 58
    0x2030030390040102c00e0381d0000102080d10700a0f00f8010315014400c9089004100640580303410070400f03103011410700c00004601100c03900d0f903900c202407607040720284802e480c01075503520307086440300da81500c003d405a03041d02480d18003850100a500d0808001c1890300e200b0203000f00040342d40b54211803440354014100d5010b020481c1051162003042d8406640140722030701e034001d685080c20814100c0d40c1c801c0141030400c58004084032007034400d1140da201c00d56500c5d503400d0b00c50000c0b0300070400a00c0d980c1c01076202d0260000c2c10484680e0302d40e100d845080d80903da00d130007502440c1c840401c86049610603a03002d204880d0080303041d04c0c0303502d5000d170407112000d0707045104600065242c50b50000001e070107819254094845620340528884840c0640500760040802e0110000081082c2d00c01e001c281045d070500311100c1d9110303110301c80e0f28284d00344500c07005040b091142d4041d41141c00c01005200340741c441303807030441c5100e040504008110f8020380c100300c407441d10014002060b280c10380a01030010 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 482391600 1250 482390350 482390393
    0x30b0d0b151c170f0a050c010c090f03031b08030f0609071809090204020702030304031b0b0a1707020724030e030901092702070809100f0219210903 65
    0x1280b035012405035408900c10014095500c0c06a828603e000241c29101e00f01c001403800f42c0c551411403006000354019800c0b0404561a001c100c2c418a4032584203442120142ca0072051103034190f80301183c0e03218203a299407030501c801402c5600003841c404002c0d48903010005007549941402e000f0820305d1b0300081c1540c4100304081d10982824807900401c4002c0301c80300e00b0001605034003840890064012260084d6240c000802e000007440f496100f007441030341c1c10380150050162906145101c0c2c2c000d400490000442aa03007401c0da1584d0308041c00c0d00a01c5a00407903048694445408589518031002c0300f13070280c00d03040e100035125014040e4991041c2c240c0c1c00f841c203100c01440020289086881030700346105080e10400903104030326031805179080601005540d0f400090a01e40380c03039480b0100f418041c03185c0c2180b84100038031502030078901803410b90181640440c8883d01124816035141d095560307014419a9007400780001200440c5090b071030301c40d0b03001039155040943c04100603040d0780340903 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 482392850 1250 482391600 482391619
    0x130b0c0c0f060a0309021513180c0503071202070c03050c0310060819020d080a020a03090801050603150a060503031216080c0306061806030907050901080a1502030601030b0d0b15 78
    0x742e90340c010a65080d000c0e685000901c80c5440d000141c000340000d81c049100036400a001d66102c1c01c86903580c01074a40e01e201c8030501800e0101d0a4040304c031007d00c0200051414804035548070f100b00340c5407007648014100541000c01d551251040039555078012500740c0d100d04041d030301505040c000c0303a0042403250001c0000c0392401300001d0301d43c02e0b081c02000c03084250300d0f4175804542d14000358440994210701241d481d4034040c10701039980e514030f0406a004c100640d400040170b0754140070302403054001030050880c250359800c1c840224403000c1d18150b81c050300d41101280301d0710104080c0000103242c0c840c400242c2041c480300e0407001154801e0394204100d59041100751208070080700e800c54801d031415641c0390355010352000c06929541810f0f0340b164001082c004044000034042c410b54501300c64030300303050743c2c0c0d0244140d942e1000e04009010701d6003002003030302e00c0d12103601845d032001e01810040b031515101e5000402d088810360046541c1d200c0308080c45021006440e41c6611a0010b0342d10006 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 482394100 1250 482392850 482392879
    0x10060503300714070909020315090d030b1203070b1008060601050403150f0c0e090106020610090b0a12030504091b050d0e0a020a080a11040c17070203130b0c0c 70
    0xd800c0765a032456107103280001c0352020041d2403035111004001c40c0050350340068031101c141d0050903200405030702ca485280c10300c070304c140035802e4200d000b02800030003003100c1d03411100107401600c05684803541c03000245040228492091008141851003198030a0b10307480d03e00c80780d94081e011038000290b268403500412856036084800c40b001d40e0b402c180041e0b508800ca0448402410082902595032410003403081c3c2d200e41c0003440300e80e164804135070101143c0c0c0c0b46d50040366592401c85009a2a4000907001c001d082c810707a0000c0c0f003500380a09500e8200391104040011194110380440001c2c40008042012185511803061443d241c48010b640036902c0c41c000810318020746a6112041d0342c1d5210030724540e0010003050603840e90181011540c1ca6031181c40301e0f1039030031449094403107811507000c1503003d180502c07034400510019159003820030010882c40c0e07941c4200400990640c8010003104030302164a1104200034240800d040b0fa60f001900f4041d8104402c0c0c0040b01d0203220380c60309440 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 482395350 1250 482394100 482394163
    0x50a06121707061416020d020d050d090803070c030906020a0209060111010b100201050a0608010b03251e0303030609051b0c070b12010801060501020f06190e10060503 73
    0x102041c0d00455008140c10410101c42480d104107040240401e14003035182240e800e081405034802c40e0070444041d0b82c960380c01003c0e80c58021720281d010040c0c0140c503a030b40406004c0d8001c1c2840c5041c1440005102c0c48983e6010b0f515441907880c4004140b440021700200340c0d1000b0248080e04003480070b010706d0b020560100b80325040151405041c0403484050520f8104254840302860750000d2900c0342045c072510300030340288010b40b4000d143ca42001c04c049254441400351409a05016004029400040340d42d6101404001482250003205c0d000019200b8100e2039840010180e11241900c0185140350103021a0a25400444070504003c1041142144076020400464890050070740c0c401c60613200c1400c1c800c0a8100303c80d204404148080c5c0392802075041d80c140c40c0c8890080008588510059a4450000d4001c1445a004c00005914040c8d400e0100103444081c060114080e400b0310341041c01c0c4800e20b8004803030241c0e00c9104200700e00d02080307481038200f480c03040c5684036145004540b = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 482396600 1250 482395350 482395379
    0x2030a1424012006162006010e0c07020a08070905100b160c0b0a090f06020102030103120f020c180702100e210706060f03030e090f1f0b1b01050a06 65
    0xa074180040741243c50812400d80c61480c0c01c3c80140e41c00e0b1041c0740741c200419048211092070a80000e0030500803810005000345807550101c0da0310000f410140e117001350701600d17094010402c1d00e000030103012410040c0ca6420403400a800d03828080c00c8454140015002100c6004190300c03032221481c0800c129444042d0201c402c1c2414880c0410415012414802004145a4002c040302c00c0002050340d03a4030740c41580c040c141c941d0003005552059884004909030b0100780006409001c100000d01c0c0d1950040d01c000c10410030398010f94840d081e05500090b07400340c004a000d400311078800100142e5550503c903100c2c44240c4008108810701d0842801f6940e0520350070101030400d4a0a400c078a400c250809890740d940e40004188110f035216030394090354400520048020460b103040328001c03460070444051183d402c0c20907214143c1c0c1d40703000c034400d00d42e0b005683c601091109100450b131448440000d2080c000903054540b4581c1c03001e0811802c44034002c2a04012501c5e02030240300360030b11034080 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 482397850 1250 482396600 482396671
    0x80c07030f0c0201091a090f04110a180f061d180106050a1202070302010212010b0909040f0609062a17010603050c0d1802010806011805040f0b0402030a14 68
    0x82d000980d0328801601d0b607600c19041061401110800079860004142c020014402c00307440251003e40d00c4400d0100b91181d45201c07524440b410b102c100e414a21885100e90462016212081d00030360301c1c403964034240503540001e40020811154190341c0178803045942c2030314005075040705850804807a070080940307042c007030b41041090018440c281c1601c40c407018a150340c20484219542c1200f850003900035400120391100303085d8a90000039441255200b6145020405010344095594a81c2c030080b008100100c111480c42d40c503d840408980300d8450f885400840f42455000c00c2d0347d0003c0c40349411403801641d81040801207900c034864400c900c0c0641100c10504010079940c0b500c0d180c540090084c4007202000030f04d0301481c90160825240ea9400c018002c0e01c50440e99103c9800441d4882d15000305d00c03a0300d0020303081c208100c1c14280c0c80868040c0d404d55001841c1c0901c4000501a60f00a07a501205561504660f03031a4401e1a10f00c6d5800c1143c0000070135251201303200b0380c048900030244 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 482399100 1250 482397850 482397857
    0x30903120f0921280f02060708072006161217070203030a050604050105010c142a090a020c060f07090b0c011406100c15091e03080c07030f 61
    0xc190031481c15000940e03030070318401020460301c41c2d2003680c40c10f10465501e101200e14400c0150001d0b8910240d000054030005508068814040f203446940b01541c03081ca040360022001c008500205400202800c0d01e80d2040b1080c440c02c54091422407400140540340b20302c5214200840303c48400c0d802648440c4c43d50000c00040b01320117079038041e10f1500c40c40c00d040c42c030940c0f85010040547e5000c8002c52043c0341c015420000c0d62587d01c00d010131a902405254007050343c20401070080b94944240701102007101089800020180c4c110b1201680702c0707442070407440c180035010101c0b40703840345401e6404500c25904608103680d0b51300300351b40c508016115010341c800040120341e42d203200d40070440c081c0502520b5665034644490b03415000700351031224044006e4051010400914089503000300c0e0300f865070355000c1d441c1c41540310416951140c800c0a5965a5200341c2c4400054110000c00035840030742120f0301a14449003005019003030000c1c81054005c0c41046080c00103500424189942c440301d18 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 482400350 1250 482399100 482399107
    0xc120e0705010c080d0e0607034a0304060e01080105090423010b03060c190801230f0d03020c0306010905010b030f0405010e2e1e11041d1803090312 65
    0x4100213248905c0c0401a5660f0403c1d0302c020300400006041401441503039000c1003482104051705410540c1c50700249030030241501d280c040407a00742c84040364a50110305181185049010f80c603d164000c6e48544085160100c8442d455a0010711650061a058135107162520b0281c1d03c0d4500089400064801401040560640040d00b54006103100c40c0141c111000350411103040b5900f5000015401b0100d071790101c60508180c491a00c0c98129500c1d51550b81e030b1803003a01118089554444005a00703e08840c840d10040d0f41d500304090503003400f0750003508418401c001454107008c416000811840c0c18180100310070700d030340300480394007201d40c1e00200700d503880b2440c0190151800318031650580c8200680d0501071b030380591010b146100d4425410004c201c100c0812403d4400041104040030410108a0709500907604001c4a00464801c124646500c036851410040c641148031700b00420003104000003400d20741d0b007403a40144040700940c10419100002039607060340c1c0207210100b50012 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 482401600 1250 482400350 482400353
    0x12714070f090b18040506011d061803150103050d0f0f081905090615011119030c02030706050a031104050d061d0304121a09070b07050703150c120e0705010c 69
    0x242d400c0c50140031483d400d076503507440d044004481d0366024080a80301d00e1624010a080c0e60040c041840400140c40e1022150130400040010035000b48072011404041043d6422450341c081c012180b991410215102c40c0703505604102c2d00e0001090b400c0d4007800f2214201003105500b040303c3c84192100c0d0f141031401641e480d41c91000c1c010040350101107044c102014006200740118103580318821402508201c849201c00460720042c0507a251a03245d00a501c0502080b6040380d140d0034554003034200102c4411460740440e01c0e101003907001a000640c007143c40310201d07904d4080c40c0400f48030b103107095003410b0412002689110b402070004001c2655040d4514140b0200e00100c280e406514080c2c90b100c550781c118201c0200e801c40022107804241c903103c516110641400c8070b0240492000504c6031508141c9800300c1c03544060000d640601c6022800400500e1030b12218079044040700c004900320100f51009040d2416480d55070503100d042203e41580d0000c0042c3e09002c689007413a00b200300c000c0da03 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 482402850 1250 482401600 482401607
    0x3010315020d020705030a031103060a1806050904080a0e06070b0f07030e2e0207050723041b020c04050412030902010302040506030a06180b0904060c0e0306012714070f 74
    0x4550580b4011400407826005010b4040040d2002200c2d5031014042c0c054481000705c040d00c0110f400c0ca90002002c00280540c15480c1244400c00702c5040740060390f03540300d00001c0c040800c11a411544040c0004210800c10740c4100b80701c503c114142c40940c02c00b5545c0d9100106108020451021504800e0019418038403070380080111200c0442901d450390105c441c080d501008118007418a0709a02a40b03000c0209548200c601490300080500542410000b09011700e80c4240c0100f816034007400c284903070903510381c410b0440011103050b140c85005d40d018000390801c0c500c0b8210503c120f18180820020030004a003c0a020030f84d482d0000d0381d0320003031005030700901990b0000758000c14044104100d008030703039101c6402e40e2543c20004000001018140c4252440c4c042e420b60003071a050040f42c00600e40350400d038402e00250511640d40c2c140200480d141502c264001d900740e581c06070107490f145652290390410000e054400307000500300041880c040c060090102c01c1000014181041070b03512 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 482404100 1250 482402850 482402857
    0x3040e0f13150c030c020309030c060309030f030a05040b091506191205010b03070f030c12110910050f06070507140a0b03010e2203020a02090a150602010f0606140301031502 76
    0x1d1004034001c0702c91148040100802041522201080c540740d6003682c070320b00001c1038804505000780100424080d003018041142c0010740b0b03032942403005000c2c980340031003010041c610544004100044520300350420064000014080c0301e010b0b00407002c0c191411440d40d0360643d006800744c45034007444200c4041d44140402c1c9502110701710a00700d40c01001c122064020300f00c40c0504a0894107241d40350300880c5690713402c0c0c0c48010906207540404010200c0003280c1808840e004035090340c11030314000c01040000d0000c07501c807440c0c180c9100741400a0320f00070110158805040d90424104440c99950540d14105401a090f00030721042260000d0350f5600300c0c01018090881e40d00d0f8580d42c1da6041c40f0880c0304103803100b4010114001c2c03881c5451242c07101c05d8520903010307401084403013242c1d024420841d4000c0c20000015032202c00780c2e0942c03005101070900608141d4000200001644035450407229aa0080360403c09180c2850390320101c03801c103880c1500d400100410001b01d2040442c0020b10 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 482405350 1250 482404100 482404103
    0xa050f0a09080d0e150705192a0b04050723041107061b020c0102030a050901050c0106090e030702120303040302120309010b041e050f06011b05030c07091d03040e0f13 73
    0x500f00f01000c03100c3c6001160341310000d0303c2e010310840b251b15196415511030003030502c1280e403245ca074044a00740502c01d1885c401011034241c14858a6200f902c0c83c2d5104400070f4206880d1954000203000030404200002402040d07500d03a0b0100d007000743c0b586076001c8801610320383d20a6480c0e8032020b09020424048070704055211804204604c0500e118002a440d0008036402500401168841550020040700c890b2000d6595040c43c01c00d040d40191080d4101e0710114545659512000c105100203106880700448000011b5845040d40d204000c0ca803452180d080e1402c0c0c00a0040c00002900060a041444102c4071510b45a90b10b0b0f802c0e40b80104509803486a20506249002030400c01100c0c042c0c082007031440007408156191807040103100c00035102c0c0740c0090064488010f01c40d445a610100c4680700d02c0540340b034000425025840d11140f86c10810742c180d5a2107070043e1650300c074060070041c0c00c81040690f00b442e01c1c02d01100c41191004141411320048200002c00306c2d0b0155042b103114a = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 482406600 1250 482405350 482405377
    0x1a07020312030a090c0b0c21070b010303050408010e031c0504030c0f110f040b091512030d231306150503030a020a03110705061c020f0d020c060a050f0a0908 69
    0x2443c082c001c3c503019129801e000d46801c61005800b1440da0070510441c0c54600d5118002c18a4840d1007c44181071850b5080042c40381d0400d109900001e03206908050007540256107040d10340d0b00b0010b0050031941140d02c9201250300811000300400702d8403042120002d803214000420346e032030342002c0c6d40700320032900018810840c400c0d07400c08101000c511480300400607207141e201a610f42c014442140c0d02c9520300d5900c0000e500c00200b04c803c0400d1071001c60400503200d880c0c4004c201e000589160000f025518645444000142d9034145c20a60340d20a020810502a15400d103542100e0400c628114054401e82e1501010600c02c1c0382100c05200500380641141d54418940c88000d44031036400000710002540b8403220a018400000c1c44001d44800816052501c040303988222107011021f40119402a001d0020000010305c610242511001c80d40c409652010cc8a00302030a1603401010b409400c0e10741400e200320300351105c4405901a5065000059060440c100764a480c020b040810005 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 482407850 1250 482406600 482406607
    0x60b030a02120d0e2e120e06060312032e0b04060c060f020c070504020309160303112b1101140a09051504030c0305070c08030d020c161a07020312 64
    0xe65400101c0b005666096540d0b40c207161016410405503200e2584210101000200040c0340092503d5044040e20410300341001c10300041c3c9042c4055501404a41c01c07e074105a042040c5411305104c10110640382fa02c18a1441c41c1c50704003c20650310b64000d4803e00d60302d030380c0e420922442d1034080300043c00c031240c2e01d01e455a079030b0322000305140c118034400c991a03810505109100c29140c0203880d81610a0b41c042c28142d400c001c1404021b410050a00c18640300c0c1c080b0000e03141305840c001c200950700aaa45071242c41144100b1464140d0a05240c80b420a2141d6031070741035413a56441c0c0c03c0e035403482e00d0030607000318403050030f203000d8001da20780c030398071402c09800f40000348071300780d201c03510940c81241641e520b10700c01915038900c84011034000e0041108039074807000180c42180100360040c4181d1000e8801500c403080d591a541080c0c1150750340c00c0c0e002404540809080141e203d4202407442160159403c04070000d25805e00040711144041c80424508115036007403040d00c03110f214120490741c6 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 482409100 1250 482407850 482407879
    0x5070302090a290609040f0207020a0311010212040e040803040807050d08010501020c061207081305100b011b051515060705011409070e01030f1103060f09010b0f0d060b030a02 77
    0xc0144100e04054000380ea00034441d0003121620b4010101e000800e80c5007005c2d03c41007444041c1c0030080006464640c20410400103a45160711000618051040f0f2210080503238006440c0000560a41c40107650611003000210789403000300d640b042c5d004014545a446e5480d091103a80243d0340001c1184c001c001200701c06650000103141250340c240d0840d05003071702c0740083c00802c2c4200400b5628460b00c01d03000911042c01aa403c581014020034400c0d00c4600300e0701c607035080c98011020818207548800400c00d007580c1c0803c0f01e001038034140d5910490350138543e94050795804290a910000555240040d40494104040125860700640803960350519480c04a0081c0114074041c0c0d54180500e001c200e08e50f40014406042d00d04890140c00030743d00755164441010000501100c5008101c1c0302114942c500f1b008040c020700b01089078281c24280311141d203080d41c03d18045103000e4540d030115034507541e850782052416250020400140c4602041c0130a0922550310406900011403841c202ca = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 482410350 1250 482409100 482409121
    0x1302060c0d020f0601060f090e06010212040b1c021821010c0503090d020c1c0510060e0f0108011a1215090d0f0804020d020103020901090504061d0901020c06010e040507030209 77
    0x402480065044d500c01c0e0780c8502080e00e242c0c1c41a07012400007145070070180700045a20f4641d9800c00c405004445031407001d917107102c44690154004003080c84000c1125042c1c240c0d040003034520410014020741c100400c20082030608801080094481c035103001c500c0d803001020300003883c0010200e000906c5800c601d0000604640e00aa803ea400ca21488503d450f03094408a40c14120410050800f0751100301c41040c140e40da0414030041d074041c0140d8500948400f500e105120045c450300c03810b00001c0c5000180707210300d280141d1085071503904101d00224030082d1000e440c82c0400c1d049034408048507045011615020340552114001100c120a00140700000142c031050302d0743c1035443c61f0b40b0a90483c001c6030708150503540250400080c402d00d05c0198003e070041d00300d228040c5419603016559a0002c0e055031b40c42e0340083d840b11100d1504a0401004a002960000d9044001d500d043c02a000a0b41e4888052160f07251481003203010904002e424400c0c4002581c004000303088a04095841c0d8 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 482411600 1250 482410350 482410363
    0x130c0c020906060711010c03020123090114040c061103161103061003030503010501210603080a090b0702210708030d060f170d0305071413030b18061302060c0d02 71
    0x303900c6424040c00081c080d03e40b003001c44003566407000042c170f4500c044000544a810304d0030340c202d0a45d500c8060703c980c41a1b5a165141c1303c44a10b00740c005081c102411510f007145e0100036540c08030a4160104008900000c83c11030407070704a481d0185100c06c0c0001d4450035030042a11751100c840c07400031a03000340400c92007183c0302040224140c0341c1c262150107400581d41c1c002c1c40f001300070403000d07c010041c640c0188a140e03130060701c0206200d408032040124804a03806908122040788010a51000683d444400603001d8902003504070300c1c0940c20740010782c0c00d40003000c0c5a0344c14110001c3d089071540003400030b0001000e031034040b0381c0c580ca039060540000d0001401140000307001e03000c00041c510390000075000780c4210040a40f580c1c0c50001012009000002d10120900c003000d254082c6a9561000509040d8600b07500e90b007469041d403400300000080680058103042074105040401a0007142c400c4d04061100004440300300c0520109840d0f0080040e80446030141c000300d400d4007500031901 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 482412850 1250 482411600 482411603
    0x1f0506090618280f021308070f0504110c2b09050a0314010e1e010c0f0516021f1d01020c0315070c0b0109020a1403090c0906130c02151023130c0c 64
    0x40c001d1240e2960070a523624240703031040b82c04c0b502c18840d08020310f0410764040318031030041520480c500b4809911143ca4080034403018100b910318104411955000901d5030000801d542c58020034803445e01d0001101e298441c000075100a44a101e401c4441c80c003503002e031100003940c0003528820b58488204100c031403801804c0f80019400c04030610303c000d10500036102c0015103620b41505040c9450403406c1c0100b4501402c0b6044018214802e01c8840e0141b041c021416469551041c04500b9600403c07030300707140d2050310f41554000c0b02440080d070f8010483c0c51020b44540408103a96484420480b50006650b00c09001400ba0300004140c0d5205034005110300c000d19225020b501081000441035440b0456440e581ea800c010381400c61440c1c480d85141c1c1001c001801d030341e20044100b18030405c5840d4401380201507440414070400701039041c400f2951102c2860542d00040f0b1408403800c4c80e022400811850f00403180d035441e039455841180c2000381600000d81004855126403002d81503000c200740 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 482414100 1250 482412850 482412877
    0xa11040204171b04140c0d0e030301090f060906080a140c0603070c051515061803060f04020307061103030109050a1b21110901080403021f0506090618280f02 69
    0x101c0e070f60203050502a42c02800c00780d0202000340e64070a244071020b600001404001c094071664460604c0720100055030103442e01c00000103c4841006440c01200c6880e0701c954241400c0c028200017000c400301c0c030410440e4100107038442000c00381a0017418460b001e060180e01c0707000403060000b142c1e40010b4510845110f581112100245840501180041280c1c20b400410f0415110b030340d00d0800c07030050801c68007004180005860f121002a040280c103c1b40b00070148110301c10401075240801c952801000349043c00c00c558069448404d440e8070050003184801510340c0c000ca0103020055100d200c0d08030002036032100c640c480800c000c0c4401034841c2d80c1420643c03a10060384500203a80720b03c001840c08120300310318100100005503400355000304240e05500030140c0f401464200b411900c4034811031413100185c0740c6450746c200448680080c028600402a030032404140310a2440341c1500300081c11480d20010361610721146080c6010981c04500608240c0c1d02d950f0240c545d00909a018034401 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 482415350 1250 482414100 482414143
    0xa0b07050412291009020a050d140a1104350a03030e070819060c05090d050109150b0108130c050d03020102030f010b120106050319090b06010e030f0a1104020417 71
    0x40e100c494241501c45840702d50013101c0400c0324100703079070081980e10000d0800c41d0503c4400b0070120110b0704280306610000f001e9604004c4820403e1183d0f41001080700c00c59400c2504041d500b00f075030a1008080e80c00303641c0300401a00c16200c200c4011400100b41c0703044039a08141454014050600001b01702c119200300b00d0041110840031428047c0c600c2400d80302058041305840d514054100e01c080e0f1b90602c01d041140c4d68954541120040149018000201b140c1c611072506100e07c2d164882072481c01860710104141d140c0e4000100c9030001c21103800d0360b001200b01e0030503a166101540c4103607405043c00702044105a01900030b1740c07040c42c2820824146a90b00d0450a5a920a003001d1015440d014001480000d014201171600082c22201006231030410944c801d040b104070080603140c0c8003840003000001d40c0e201004071035549003980980307980c628500074650f0f1220400300c010403107001c0c003d0148140c0c440c0d9042c0c6006007251581c1099810107a007106840d0404d00e04000040d01110 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 482416600 1250 482415350 482415413
    0xe01020d060b19020607020a200a080703030e09060904060504020f041a0108010b0309070e180304231801062025150203180f100513050a080a0b07050412 67
    0x412a50312404084d00540740c40307002549c8800d84c850b60410040307031800000c084a459901c8070a4002d000c2c0c0b240302d006204240c01d40c20041c0c2003a49001445108041c0740041000c2a280d91300d4050304103500a4010805813124400240d000c034003c9400781d04580b50140700c0e1918a2b0b103541c6000e4051081e2030756107080e62103c0d00c0d0406440304455140c00e42e030147c00208501e69041849030341c002c0d441c0001c9545c4030341c0c6802c01d0341940d100e035004680c0c0080250b1050030181ca4443d03446820b900480d40c92082da0581c00d024019003105100c0d800c02d04c43ea50036440c0300002d000c4204640302c95803409403800c4a1540d00680d019140b61a60348980b6a2303100c0021609036040d11018180100c907400441c281070b50407240e0780700405500c10003a00050140103441e5540c892400a440300900d6840d002c1d1a02c4415101000101533a44441e101d01e0031410100a41000421017a00b01d83d0800308400071940c0c1c40405560b00e10441d88001c1c800c0b03949901c80700900511a09480c501d5103000b10301c0d080741040 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 482417850 1250 482416600 482416603
    0x60615030902061603022509241a040906030507060306120308010522090308090d0e0108010b031e04060e0d03020723015a0e01020d060b1902 62
    0x84a07009400c0b10b0708016900407a0121503400e0382403842441182c00b41d006220454810000c0c3d101c286018400048040c80a1a42070240c0300344407220221543c0328204c080c04544902c00e00b40b242c041c401c0c01e11032520010f00c11700300031600607002d4290140041992860096a10b041911802c00020710b02800031404048103081d0403903103600f6960360002a400c2038104600704607142691804100e1402200d0440c1182c0e026100d0554021f844100f40da107090040181400c8003007070688200802c00613518000c7e84c00c000b44034151505005240d880c0e5888100403144440e07010413446041c5203400800080110680000c11420205c200b48d642e1075032041e609905900800800030144140d10b501e24012100802c48500901d00c001d0011944007410384610306903c142c500e900d0901202c06048007400202d10030a2800588800c0062500740c02d0060900b441c0717229004551480c45c0c50340190740380441e09405844600c40e90100405c501540d8000851203540401b50000c034580d079000041c6402c070300 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 482419100 1250 482417850 482417861
    0xe062b060f031406070c0b0603030405040f090317060114030c0f2b02090906010e030c04020c0d18030302030a080910110318010e06010b07050106120b010609090b0a051201140406061503 81
    0x1207922280301200d42596049541f81004003101c3d0944400d11000400366128015410050b0400c440002c0c44111810002e02e00c607250600750f01404001c3c0140842c0366801144842d580810011007134a80d140e040004510303104001600482c124003040002c0402d030840340f00013001409040040c130080c80500d0110603809218100d07640072043c2000a0002d50041c04003000600d030050655500740ca0307500011701280c1190350a9540c0f54400301440c006542c1200c41c554624400c004002412855650001e40c0ca01c229400c01e0b04010440e030218104640820500801410310700080c01001d6540203440a01d070821161990a8510f03007030010b400070b0041c1306004010b583d640203030025030b00300502640350394460341049485641e10107000500d0342d500116043c0082c0f26012961003545003d4000348248169080110141d2601101c0c511640d5a080403004803801607549020080c500094140107002c1e12101a812083c038008110030411654020019120315584412898440c80e400b1001c03282e = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 482420350 1250 482419100 482419111
    0x6050303070609020607060f0f06060e0d0210020724260402100905130b0906011115040303020403082a0106081e030403080a02010504060b010e062b060f031406 70
    0x1002080141c0c00304406070844502240041c0a403440c20800d0341c1d442c07045850340c40b004021960341c1c039000c1703110240c40d000b980f009051b03030b10f4078102c070030100400111540d01524000f40b10b601101c4088480c9070080c03000000034009003400c0451024600c03d01d07028481c10380c600342c00284151032140140440100c0c07196154a02c40011020380c0d80d59401d00190103d80c121100611001d988001902d0362032034100c5412030424a00410802420400c1c061540d0340500001d041c0504207204c4485048002660315044500480b414030725103660505800030709c40d6070405880d4660008600302d0507a83e2011944680b02c9484201c503001c0711541c40b880c00c9a40714061040541c01c15042c001784410011a00303441031050b9400d40745090b540b90b890340d1040e8444014000585d454400300000d1120714801d001440c80c0c00e08102c6c0c5001043c1300042c3c2603100c3d450060300021141500e1603510782c030782411000c90480d4400204565600c50035044240c0366a48411646d000d20040e5682c80808003113a028000c0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 482421600 1250 482420350 482420353
    0x2130203093313122f030909060d0503030a050c09061206030d03020f040501122d0509030a1e020a060e031201210f1a040308061305090d050c01140127060503 69
    0x101110b801c2121031100201c985601d04801c584445c04800031503e070b030440e014001c801907548103200d40034019282c900034200751003000c41d0207003103000c14008402c40e54014100c3c1800242d6603100200070074280100b070f5426801090210300150009c00b0180410f005035000c40448081682e0341c1c0040302a40b1609a1146400c00c080c0800c208950140340e01c84075070035903c0070110f80c05c1040c00c014084086d50606400c448940900c440da11080c5034816690001c0340e0a000d103290104100d40582441c28030282c2151443d200320058500e10b10034008400217035406030781400000b5880c8081a0740340c0001c030881d0501d020b50000041c188481c10424101c40008505020303500d002501e640461a10850341170f103a01003031314001458000c0e120404c40c45139100791902c2076a82881400d1080f051070680c0c40203c3c0a1420042c003400e03040c00a0203462260441c41e29a41d00e0510316406409424420495001e115241c00049121040e4620800001c00b0442c040103082000c83c900e2070031f85400c2e10a082d0035 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 482422850 1250 482421600 482421623
    0x30815031009030e090705091306051e1c05030307020c01230306030a080415030e0c0901030803061309061a0901120303111603030b03010507090302130203093313 71
    0x5400c11034205039502c40c001d0402c0010342003e03002182c04454100c4200c1d0000f100065050306500d070405010181c4071052504010103070034a404102c0d05200100d02c061082c6c031141300a100c07641c4559080a00510380d8400070b4000d65149040c80c0e0f00e80090750b00b50054026400004c440d0b512071496440d0b44040041d0595442e01c100c40c0c000601e6001400d006d4040c0a02110b900c086842c0d000103000801c0c2008100b48441c1e01d490000f002c444110368604078a070031154442e0b00683e140040c65041d20b4004010301c1e079a8813044002a40d040009a03898074442c206400f101c10700810758072540d0316003402140c64042030360710020846505024010004c100c1c0000d5030324001304c0d20a0384018181e010703183c1003900d41102d041d520200301034030176070460000e500d480035040303e03080c28017078243c200e40541440341429007543e00159941c46081c01f0400c4160307002c0001380c01010200400c0d81d40c0461002e1481c0b401c1d4a541100180600419110300320b40402d00100d02e40500311616202c03059041081c5008 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 482424100 1250 482422850 482422873
    0x402040b310b1008070212040e070f050d2309010e06040809010c140a0c0915030f0c050d0803040b070504050d11010215010f081608030f0d0204030c0e0403081503 71
    0x10a1050103001055a48480c0b09009842d1190310150795411038031118954585010000d04e846002100751100c40030521040001642040055410100301c0c01c050708040718802e0b0442e0340303002d40d02c034240c0302c1814922400141540307845210034900c2d24450750b40280e03072105256820782d01c5a00c840629076100c03c2c00900815070308d901030840318205140040b41c5446a4450b0541c042070707a80003064581040c04c041c2d00b0000c040102200030700702084240401d14610000380d01c04941484003508070040314414100700303c580782d40e0354043c210050800c01c1402481c20400620b400031a01221004031400214035024040c10a5030221103004020b58113076400d030b0790f5445541d108402c0b42410f51082003200d4644851f00003116010300103201030400036034035200741c82e4580351010001940d1810300003c24002c0c5034011085413042b2880b18911660b402c401c0e0302510080c4102d40c000307001c1e00e460180104c1c5c0716a00040c440d00403070182c0d4694442d51100c19152601441c1b103170015070f041d40b00090804 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 482425350 1250 482424100 482424169
    0x70807080d060308070b07020607030605030c0118030b0f06030f070807050f030a06050901150914010b03070908010c02030405014806020706020a0f0f090e06060f0a080402040b 77
    0x441d46000000104140d903503540c030300c843e03600078030021030302030903003004004126a04001c0360340e00c03580c0c40c5802c0c07140903d400d01080d1210303180e650803410814640b85048407009032040c840019584035200740b58524060100b028400d0741540c44500c40d001d40950442d04000005007001941e03180070142c1900c0d071810040155a01b02d003040207416000e80c9180e072001c140f0758030410f172080001000218142a540e040d03a04e01503c0b90b001620518940703400d40741e417004ac4040c0c641c195200600c07956034a860342901900e00c59055403011425608100010b8606540400500110741003070b2290710708420b24007250300d1411340c0d030340c1d0f88030f400403840841c0c1c4507924851011888108050074070b40441c4105440e01c40691313001d14000e0326100d40000d00d909807513a000040c0144947d051038015448041110024013000e00c501c04d240d0460242000700702550f5880d811500c3c900049a503882d0f036120703284009490b0744400c9505910852a110344000d05051001400048ac12501554617102c8803107000704 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 482426600 1250 482425350 482425357
    0x150e0603010b2218050601230301050904050a24060f0605090f01030f0c0e09010503070303022a0d140601080c060a031104030f0f2607061e0507030c021207080708 71
    0x20280200303c1c2c4002500f0440240072010001a82030200e8145407090001d40410702c00101703164280821101601c00c0306042c819641075500c00c4070300c21555115810914589a2000310241480c003414820020603148005000004400c6503400d120541e03981d442140d24902611600c0c3c00305070100018112803500d14a4140451814100007507010340c1d10750503c0403540c40d00c2c000f40108040c0440f104d03207450491892801008100e00400403d815079034020b455050f800d2901d8000c55020040350800c0c4041e8071800c42200002d025200205414104820420001c0c0d000b03071041e004038000818101d1001c100b40c003000c0005040d551800b4800e60046000701711b4940f00000c0003806010100c0041c0a602120345654010001024212154200000c041040d00f00c1f103948880e6400307090010705021016140e055800c6000012011005044407403c0da1061041400040c6803908000d40150564400b502054056003101c40c6008000c8410310148107005001c1d180c070105010701c10004a107a0000c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 482427850 1250 482426600 482426647
    0x302090126030415170606090d0503160807120305041128081e01020406231b0714030601080601170304031b06030507051303030806010c0507150e0603010b 68
    0x99011a581c0c0914590031074116410060b0304804e140c21048500e0b13805801c54680700c5000b01c59803998200100056658451502c025008506000f0b62005101e014000d40d8480e9030080c801d0790001c0c9091400455541c040700341210420600a1491215482803162a206070b17130012030341070f810030241d0070494000d01c1074018503111b480c0c005c11076040900b0300c0c11280060007164020100e0a031003444a03000300e041d03081d040d9002e80c810f00c020040c40350b00c140c0a443c0c00c0140020064111001e145841e42e0f4030074511a020100703081040c10882010003d01c0d00f04440c0a880e4125440c12280101925081d00b88a0509290700180060000e2011314040040d000390b60800c4038945662503940c4030302c101c42e81c0000d00c03203400c80725000c20000381c140c0a480e0f030044203840c18a00d01804420000408003d9000203010003210b000000d00301d034041c80b03240511641050849403840da440c4081c84040c55200c03407800009001940254a9040c4401502e06840340c0811b003600709440002c466080f107401886 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 482429100 1250 482427850 482427899
    0x10806030a0c0b0c01110a020309011805040c08060915010c021003063f03050d0908041e05040c0c120f050d0f1d030a0c080d0603022707080103020901 66
    0x400002120794034840003c10400f00066101c01220030f516003102c04101c050030109404018041e40241d003c000c42c1c4440c2c409003404011640f908031040156419a040203030898a04246400015004181184504011038100e00c0035a50074640c1c3d069031013030b207154901294010050800600e0b01d8182c040d424651407800150060b40d8003c002040620300d200b0011004c030440c541140d01c148141c090003c000c1d80c51513031081404c00d030380c0109684910718480d0f24803552443d00204124049046a00514000c20440b029010b13078200300106007003034880c0a03c241d1405000c020003a008695085002d81c001074030640e444074200043d10307440e07200c280e02c1040260800c18400c42000c60f1080c002d1343e41d520f070000203801040031000005440000d00200241d070040c01543d10580d44406100346055200c0c61158481003003909c90f0f0080e05440e00001c3d8011061440f403200300d40d0003200d500c00e1207841c80f105035280e184c501e025a41810b0a01000c0d40100b01200144091086405501400c404150 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 482430350 1250 482429100 482429113
    0x10b1534030513050906010c060203041103030c071d040b060904050a05190204050711071502030c0d0203031e010e07031e14011a0346020d0f0c09030201080603 70
    0x15840015109181100468004650441d4540428602101410003502c0301703103840c01c2034030000e451110300c8100105040c0e0000b00050402806100c4034040c10b0700907080725154580d80b21020744071900c80c0203071544071744400d030000d048540215a440c0200d07000b001c6509652103031001c0c003110700e10041041d01c0a10441d004540050b0041200380c0404024451151460545204000654030064100300c1000722941201006010204e1840f0484a11400c0c409000c2000301d810383c10340c0128444420341d030044004280c41300e80c011000314421400e1581410450781d0076180c2504546080c0248010400c0520004002a0090b8000846120024a09849405605100400d54a01503015039403600311000420400080103441c00b68000c2c207507450b03411403401005011404140302e4100040d207803850024041404110380c00c40700b42502000d10300040b4144007036100a507000d030441d98440c610705015400c0480b442d11a40d10040695601c0b88005441d58004546280e406069a40e2500610 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 482431600 1250 482430350 482430427
    0x91a10050702011b0f020a051002120d0b120102041403120d15050402070c05040507020a050a02041d03030a0c090f1212031104081f05011d0a090b070c0203010b15 71
    0x30000c90310085d201e08501d0194410038030500815094951145000d08010b296000e091a00400c0d50005140d9240b0880d45980d0f01d00003020140030000c1c102e540106c05036661924515041d00104195881b80309525140f882c0801415910720398009000b40d280003d11180729088030b96042020002860144000c4998490f03000034100ea100f9642101c03851202d510400c5581414050182e01c20f803140082d10100096031140c0b9214108018028400d980c0c441003403c803104990503c501030408a022a5100c1c5000c00321140202038466295000c41c007040400942c0e070080c0c40c40881514a1a007260400c992140c1e40d4000a040154810043c140c0341c104020044405078050001852072030700030280c10030504054039104040041e108032240c1850014030010780011200b81d140310f4405003101c03040d0390700e551840041a40c0c600003800803406600340010303030b50f004400d52141170080b80200103090980301045803964810107505000c031400e00c82009949054061000044d00114044002c80d620 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 482432850 1250 482431600 482431637
    0x309080904060b07020109090c09090b030f010e0d180303140315120c0f0a030b070f0219030801031a0f06010f020a0c0305160902070503031b090306010807091a1005070201 75
    0xb0b6004211012804610341040d5a401501440107100020f0200b100440301003004018000030300412003401d4440401d403a203524200184c1600c0c3c0c80c8440200300b19502005000e481d491703114500000514524450074072200d4035910b030700c00c490745070b00c03038903808403c18036401f440d40c1000701004519401c82e0032185041e1113441100c03030280c04102c054090b000005040000c00c0c540340c0080c42c05000f05400510001e2845142c868000740c01d03090040c2d500c04c03a03c8049107011400451082c5d040c00544540b001c164000100e24141c9204801508008140c1a851100408220750000301c540c02d4001040803035010383c0d1108030500c5a44180c501e15450354032034950514040d8000c9525502040c802851001c101c0c8400c1701400391548254a41151512059524003014010103840f1480300744a9904000c444100c07a80100c010702035559035a50340304821380381c400c584603054003641001c9003940c00c3c26100c5c0840c1d109100c0103011081c0d800c40f88038229041d81090700102c0c18411070403801c5038882d60 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 482434100 1250 482432850 482432861
    0x30a0b042901061101060f03020402070228030605070519081803070b0906010b0a050d2313030e010e0a0308030601171602010c0504050f01030b061606022205100309080904 75
    0xc2070454585503d0301e0070061180100c0340100c1d800d6403401d5024002603c0d4071942c0e90480703404460158468620340000707406003040640c440c8003118201031114070040b503092540c08403409414100300c190344102094404e84507040a0512611040000266003405003081d0358220850304074282816848018203484e5501000042c2e4603140c3e03800401500d20700400c00c460250050854441c1003812031400680345024ac3c00c02c108549480e03000312024510000e541410141800381d00e100396040060480c0c0070815031001c1540085d18403611034400d035025a180788220300b8058035409100d45140c9401f804d640000e04075904000c455441c03601a01842035559024030140b1070403e12408048a0280c00c5820411a0509010b414402081603940307000340c03400b40c650b082c21b01050380002c400c0081e0032031040c0d21071094084002008901400340e180d0140c00390340da070070f007444500d14441e041c00328a600305403262a600160039032601a400d4440e40022450a100b16002410141688009001e440 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 482435350 1250 482434100 482434163
    0x102040909050f210f03070309020406061d010809101a04060e01150206040c050d05070f0605091201020315060d06051f120c0203030a090c0806010e01030b01090b030a0b04 75
    0xa0240341d10326880031090004030f40d03008403441c1325000c2c0110340d496102c9034010325003103050b0f000020000401d060701a0304050040c0e07500610400c41951684406040b04d5510011030090540c8500101442e500031900ca50044491714002c04186461a00c200003619205800840500040701144030356110350003944040c28150041c5041903061440c48241110410b55000855011006220100e25240300a0003039441c1940e400c00c00d4007441c18028a0303c80a9845a11b0000b0010000600664440e003c1d040034801262041d5104081500e140d00341d0005898141c4400300c0c2c050100014641440100f28149031a44045511559080050301d80742200503851180c220f05800e07640035a52000d401420182d15135010409662078100007950703408003d02c1c10300166038411606042c040c01410340d40c002c2c1148002c84646684035059840d0504080c40200c1c1c10020890021074400e10038010030440c00c20190042060b10200e4545059211020700107031824040ea000441129024030f20807070405 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 482436600 1250 482435350 482435353
    0x90112020301120203150f0703110702030d02010f0b010207080d03051329060103021e030a06032001091a0304242901020c0d020d1109010f05040b061204020909010204090905 76
    0x250f00301e00516090100a84400a4580c5081e04002c0580c0405007140c1c1c01098611380022400f5001e0018009885102001303585842400c00c960040d5505411599451284040621415288900580c0d07216154001e280c2d854100c03ca4240c1014070a50002d84c1c0310039110340c4402c0c29020381c2c441c0f041186074680c40e0005020704400305496201000031a5030010400e1a0861030800300000b0003601c8031001d891844090000804a65402e00c80d0f0403000285800170902d046003440c102040340c400c1f14443c1c2c0c0c1804106800380000f090f2103412110803d650048207801c2c9560740700c0d0b9611004010113074000d10a130b59061886140c00000d8405c41c14190110401c8030000003800c52050800310341543c0860455018440c624800c2d00c1c1c2e505039180c41503040d1100664440ca40ca0507030006c184031441182c008101100004101650035045000c580050300c040141c02c4070482408440d05c60118401c1518403201d0115006007000321415500c119a240014106512000c860381590328000c01a80d85 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 482437850 1250 482436600 482436629
    0x50a080709020a022b02120f0711012a050609071a07021c0f06110a0c03031515120e1902130608030d020705120901140a02010e0d0f0e09100b090112020301 68
    0x9603404024000d055445201f105060000c4101c0f9400d0394824032a00821404603080035240f20b900071510307419800d03402c4401c61150380404010303208802800006540c20f108000c0071415140005c9032907070035905149004403500122003104401980304e11022130b042500801c1e0300240031551703070a8080b00b07880383c116154044000e00307009044d100c62826510200008100760b03813060f9080443e40d00000d61504001c1040d90b500700850841d01c17a154800342002c000b0400705112541c2c0400014864403400c0400c0020782c0c0072400c680c1d80c0d5050b1034540c00000c2101150240503141403a5801500042d010003c6400d42d203c02c18681150012000c00810700d40101d005400c001d028032031459210880c0700c0c0d850402c405000003c06100b00c1d54840d0111080c00500c0380c00c128130030341100c08101042012507080c41d1200c0030007132205120b41220030000b40c000014505c1842c020350f41c9405590901e8500c4041410f144103102282d00c0024400c1c18072a141548603a240300f50700143d40208800d1191031312 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 482439100 1250 482437850 482437933
    0x215070305151210090305070203010501030602121302090c0705160605191404033e0a090b0f01030c03020c010504050a0203010606090e0c0306040b0612060406050a080709020a02 78
    0x660904050716540300352988000300100e0200002c154242e90241311001c41c9803026410140c4407807191071700c06901542400b0002c010b1000d9a0002c00a07444d00d58100201959201c2d40606030801c1020300940c05940c00f408152000078240103400c02e0307401101519180d20300303451005590042d55104001282020880c91070601d405c070301800c02e081c03241c1480016013412100300540c9204e5030000403c1c807041d0301d0106406a901e081034070a501c0b52000310b0380792181071040302d40c980d10101c17186a124828454010a00360083d018600660360f01a155402110303001c070064015040c510041e5042560900004200080c240240c50089000700050200e401c1180107250a40b03c95401000c01e00c0b14100080111083d840c6a10b070b8420b0010703c0301a01c98441e1400503000e0020700d03000b180e2000000c241c01c2500010100564041d01003180d040040f19a01c03014040c00454a00c24035505400c60501040f0901e40e60300100281841e900c1030306c2a691420124169a50303444103c0b02c45140c500f1803542 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 482440350 1250 482439100 482439121
    0x506070824150324030a15051f0807031e081204060b0d0f0501050f0112140709290306090d0309020d0209070906020105060316210606170705040b0604030209070215070305 75
    0x910384c1d03409401500f071030100390320380030380c1401d454412007013850703860f0300007401c4205800104403440c0c00c001030200385603501c4503525a00c40c40d50000391a003071080c11042d007102030221902c00c44250f211520703500b400d00d98014944d030201d0052041c0d40070340e12448820f0b1b403541c650054040b03061090115007070855407410a542180d2001f40300325024001c260061048045201300c640d103403035100400c40c6403c14210545410051180d21200c41a428181d10070507402c40d02100345080c50444000078600007000e006c1503a6541c6c140d0382003882e41c001c19507042005209400100040780050110200c059159020510600e0122440000074241f49424042968203020340c0745c000e81e0480045c00c0c0030003660707502c400c059402e100c1d014000d84141c4440340440400b00199407145d40001040001a550308001c2d40d04007040c80100b034180c016500045000d14040c41600440b180180099042070304660a03c007004001070485c1080d4403d441c0340c80c800c0205042c94510a101650700483d003030a00c8560903 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 482441600 1250 482440350 482440411
    0x1a130b130618021c030306150c05010b09040b1b070203030705030304050613110103050702010f0e010209030c03071809030219051509150406021b0a0b0405060708241503 74
    0x401024075a040c600540d864204ca0baa0503c0349400321600c0c3c10313880c602503000b040b5682c000c1550340115030282c0207403500802e1108072640982d00a00070307007040302d0401c0301840044900030010205031021541d0180103280c103400c00b05100700c40e00c0c0340c12101d400091460300240f204452350341c400010401001801d02c07104d6005101c411068070300749415501e002030020080c04103070405544a0000d80017901c04d4019280140c20424208060110f442101e80030b5403140c5803c5000740311740c006212450800040102c11039100800820700c41143c1010800540503c0c0000c0c5c0840c0308045141d070000050008044595210744020032002c09005d002c003655140041c0a05403e0f04115442c801589136103803200e50040d44414010ba90306065841016840300d480b0315800f992040307121020800803d4020207010301c0c043c0c03040b591196a552412689078030119a00c2c240924075410040030381e05800300e00341001100400301e81684003201d202d0b1134140c0044605208400c00741c000d0102941c3c494110 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 482442850 1250 482441600 482441621
    0x11403100611060c0d052706101a0d0c030e06072d0206040201180b0c06090709020a02030d020a050706020c030d0c030b0f15040305010c080106080705071a130b1306 72
    0x5015103141c20111300c0359a00900038265165a144e030f002900720345094617007100040c80440c1c01c00c41d00b1140791060356a42811207040300c58044100c0081085440080c00159211480d20481d240c09100960743d4098132825000340141030f241c09618689181c1030104a100d07080c15941c1440c8229490290041c003c0b0b14420414100040420380034000d0703001c110294040d4081c20820742c0011402640756151015900445030404007003095001c0400c0481c0e924014403905007112030058540104e2001ca00c6a00700510140c1c0c4100311800b205880c80d005414224a00d052480c14509075480d01c0050340c3c443d08104030960000075013000491058420080307031030598a800c201d00412800410f00b101c045c9101d04c0c0c4181c1c000d009080c100c2c040300d811140034591280003400520a0458081c01c070744d0342800b4550204178001c0000b075401e4810382c240c1d0342064000255144260340c00c00500305c01d8001400f50f0090000b030b2100d80011a031036490035402031a20380b140180d81143c80c18003104803070386e1111 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 482444100 1250 482442850 482442853
    0xc0f0d260a05030a0c0318062309031803190b04032307151a0402130b070f0203070611030a050307050c0d080105030129040209030a0c03060b0120070b09011403100611 73
    0x921f80d5010840705031260300b461f88800001824107030800282c020303421003150041082c91550800c41b1340315000c005406400036803110380002c0118401010384404440b00741c8809000300b5612200825112003410b6000b81c02800d201c9030b80180741c00070f51004251141030500e4650b0000d030000c1080b41e00003502e00200b515580c00c01085020b603040b03180d40f00c1c01024061050f6008580000140c001010b9500100100c600d215a10340441c60600c0d0203180381441a44680039010001480c180245d80e180e51075410107001c3d514182e4100d005403030f19000078081000300902405001c007040020007410244183d152500046985403400705800d4400d03070f0707040c202d0b01d40704c00440c400742c0200310320700801144080381c0268540104c01c000c03d00d040c2d40d40c140541080c0c9040320000030f001c8203034407413100c1c1103003a030f91040304803083d401103201014100b4062080d5408420308000003d004006007a007503905141110481001c7c62654142d508117581860342e4190a100400440ea00540000c1c10712000c40c0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 482445350 1250 482444100 482444111
    0x3030c0317072708060f04210206070f0e06030910060906180b0d02280506090d061d031824070602130302090702010902030c0f0d260a05030a0c03 64
    0x40000f00310f569105a0321003190800e021001d1002d07146114080540320320700440b041c81c50f050070240d07240002520140d031206441c1d030540c886251504101e60741c0440b242c004050589030310b14111031001001c407040d010003540481c0c651250399401c0c021400f4404404c0148000c1c0c0c00401a40d040703940d01d40c41600904d25000b420001c0050b43d5440c1400e005590200142030032010002c43c08050900800952214250301aa403460250641c500c0000c4051011084620b480d4020b224807840340c0808140d11004c4465400d0008155400407040c50500d40c1000705503400002d180b5186400201e07451000c10351403048000c01e410180081100f095100c0c1045500410780c0f12811010b22594401402031900060100b040c64034000c0304c0002181d010704002a14035100100078000c10039540c080b4401e001e5a07140040b549804132480001038802004e071261000341d0f941d560302c01d0124500c000912161070812034400e01c900307030140c488900035840311540c0c1d1400705c44040454115088680c14140b404 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 482446600 1250 482445350 482445361
    0x4091b0611102003071d01091a031312050c01150302010503011e03050703030e2106010b0a14030403080405250905060111060901060603060803030f0c0f1303030c0317 73
    0x15400c01e040581c00c2c00045242d00300c00d50502d070000e0040890001c0c900002032140c0b050b40b0140101c08442070804214690400800444815600f4410b500904a4225034003049203070700350041d45c0100341a011006100c08079034484844003030a19809000c03820104054403164020301980c00f907141500510016031b030850f400a4880c1c003044c0079965004d200c1740050040c04214130005d00185400200326600a550b83c81c005081c05414420103000b40014a030b0b0307082491030b501088000007000d0015100681c02c003035130640d080e04155925000c0000145441c0c1581c0b4012004502450080d6100d000514190408a16082d03050342c56109009105103c1c1c494842c2c1510300700c042d15003100c80420b80c0d40303c2e01300403515a107040864a03a9405010b05210174020154411400c5561503141400900da5600201d6124042111061b1400e0001000142d0842500b001046d0f00421254410304248540340c600318032400a4004030082108218190241600300340da01c03000800103c0317100101d2600 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 482447850 1250 482446600 482446603
    0x406052110140405220f0c0e04120c110f030106180510150837060f0503030702060f0f0f04060c0302100608150c041701051b04051005070c0504091b0611 67
    0x584500d0b285c60450302c05c41c0410810107090101459030054a103060719516051011800b100c2502e0403140d00c0100548003400b140541404210260082c42428003d03481d070b020b003d0082c41d1000e005906558411002ca0040f00c00484550341440f07480340003955150444a2010382140c54109884c0500d0101098000a500c4844180d0059a1600c00c4041e16111500d035103201c1031907101039a480380d14103024903807540698005411100650b005c00a41c0d95590281601d03031280900182d003240b4108a407540880c014030042800c1180d00400c0fa19004020840c440560015000400020f0307040c6120000d0650410a90038a6401410304005907850107040c10355902d20b02c01e2a1045081220008110072054010740e40109214040852a01180700134a4000d1204880f008114012802140802c0c65001c0641d0113440b070103403a900c1134441840c025201500030b554111509001560040303410b8031741c0e00400d4202c1d8800c408980d0388100809040c01701d1a055007114003041900030b02d214003000c0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 482449100 1250 482447850 482447881
    0x4080d181a04120309261b0102210702030f030703030f0513060c020a050f010c11010501080619060308071a132f0301060b121b0406052110140405 64
    0x2c3c4408101e500074001d141c01e48102135141d2000c1542242108040c051603560362542c20315200340c0702030343c0c5440700e40303455612a10040c007451030041e80701c8032400403500910368140302410b0000c62421b062441c80d0340041e1402c07104031300d1440310307800111320001055054050020030204a200c02d0009140a240e000c104881c0500081c060075200c144050640b4020b10800b054542c002042d1040c0c800503103481400b0b80f0300216080b002803151602e00301007900601c80c9174103803031900d40584071a0319840d030368214440410200304003090782c4150020001d0701c02c000130580280305145203000480b020a503d1036010008001c900b00c12261080c0200007a1580459103201090140c208802803001075000b00141d282c421241d0107610703003500800c2c81c003000f00240c0030f05400481c5881a95481281e030100715003004112004000e010302081c4806030080016043c0040b80805081060200c0c44031440d40b20b4080c6e0b18500d046001040600843d41c0603c2a58035080c425039091080703040880c9119440035 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 482450350 1250 482449100 482449109
    0xe1c0203090d02131d070501030e151012030e09180604080307210902090c0408060c031b18011b03080103081803060c09030d0305040519060204080d181a04 68
    0x8020349156800c650b580111004e00f075000310004c103d64410302d000b03641903620045003001c4502c24407000041e1580300c4c0c0a0425015012000b42071403a00445410440220107003108628001c40c1d1000f00e001d01d07112035955400c50083d170b240016171221906100d80d614019010384944520001c01089048001541c103400580c4201040e03a41d070f0f1094812184603042c0012185030341400d18444448411030741082c120345000711071000e140d44034000594014401c911825419800c2000001c9282c0341d19800f655100d00017510030401140761550752040347d4800880941d409074034422451042d68048507008090a0f0798150142c2140180c0b80540001414480201002c6d400544185c4028801e50164410f000140c05c868842c00d0880e207600c400d811580c02503000e4450800204c001c0343c46405824000c5e50850060a1003829017200c46126480c80744055a103035400300000150454208032211401c0c0c03880d0f0701e020301c0c02400d80781c0c031103400000d601c035407503100c02d4240300c140e800019811101100c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 482451600 1250 482450350 482450359
    0xa05060c0a0905090c190201021303260c0a03050c0c0a030303051812120619060f14090a09090201022112010b0f0a050d0e01020d0509010f0c02190201090e07030e1c020309 75
    0xf00321a01b0132406441840140d42400069807000010891008020410300701c0303c0c50f80c0b15041100d4100760006000b01c581ca080c060340301d4410480401e02400c010541103884a06494800c403613040464928000d560003140003c0d903500c100f00c1c0083ca401d84442d003041c070003405000800356a40100701503006480c41780b100460808046042e50359500c3ea1b071078500c414030b00d025200c150744080c05050388082c0000b0b400807a02441180000c02000011a41e12803001008420180c0c2001c0021000b411840000c1f070542c03040044644021456206000242d948000415030700c0c07880b95a40f401741c0700103074800707a111001403007120100c00c541010ba51810081d0300e0426100d50324407c00748007424444107000095480005c0c10f44540500d40c00c094451046a002032200c140c95060403021604103030001401a00640050640c10401841606400d401490b01d00403568840c2c242038264403056641c0c5010956485010030340485c01e2207080d00349200c1d199201c1e4460f829140103900c1c1d21403202c01c03134801c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 482452850 1250 482451600 482451637
    0x60601030b130c12050c030912070b0f0703020d050c090f0402030f040b062e090b090102060123060d020315030604030207060c171309060504090c0302040b030a05060c0a0905090c 78
    0x4144034410141311501800710a0160342400003a500c0a540103a8058100d4041d070302e81065201c09010441300c00726480607202100ba0348000c6103448840c8050214420180c08102420388040c1901409002d80302d0800031681d103041c0d4000b08400000014035a90040340148208509150049e90496215402c5420381205640c2c1c2d400060075107002802c0c01801c141000c104084925030700a100500503c00d0300c84040c010340705c05140210b8007a00020a00507806813005101840501e01d4070032010159090400d10003d005000030030350303045410007100055000c010050a00380d030b1302000202c0181a1f0280100d800c05407402074542403903000309010302c542c150710002004812083c08408010b081c4100d81c6965104501d03100200c1c080c410400c400341049008075651600303220790341489a0000b5001c3d074251039030f4288006800700414060703043c085c01c41c400b4003145050103400c0c0b24504040802c0c0c0d8600d01c490024003091426002240203070105020821104002c3c0101c50b96100b2820b4139008 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 482454100 1250 482452850 482452871
    0x30908090d081303030e100302070519050120070c090606050a050306010c0b0103050303180601180e1c05030a0612030f08062206061b0507150903020a0b0c060601030b13 74
    0xc451045090380c8950f4500d020700002415440300107079007541c0b03089405070002281c0c1d0f641281039015052010701190404083e514281100340c0c2401841442040003040c540101c06103483c002105048680508000043d01800c01803200304800c05003002c2c2a04020807030506070000e1442c0651400e0b1340900000001007030311a809424600011980030014080320348e12403500075140e03017007a90b00704800b02d182c40c103c0c2d4503450080781c2c40d41a10050300006100c00814854980903248122441c90303036002d440c1c40b01108801c1c103860040d14440a4840b1903903800c1c000801012103c0d117500480040440050010010fa48086c1c140c80301400c501e001c92007504d5400c0018106481c82a040d02102e11000b04100e2480b507540058040f14200c1d01d030800682d012034185464018803040040098008503000d0000610707002c4881d13250b46462a002c0300071612940880c020802c1600120900000032490400307099040210540c0701c0b500703290a00500751484081a12440e1034602c0140407900e07140c6415 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 482455350 1250 482454100 482454113
    0x10f0221101e0915060f0521010909050f06060d060b061204140f06060604260304180605060909180c13062c0a0c0c0807150c030908090d 60
    0x20701a014103001c2c1448401c1a403402103142441581c0d081803d01c40100404110315002c04200c4029848805070400c00e018100d13215486005480c01e550340d06103d60039030700e40c45190070b40030705140800000c80210904025181c800e81e102421480e901000c10000035032520494200c141e903005201103030004043c00003d10900401c42100803030003070b0f10104010b1040c0d000101e5401da240b8070540d400480040905900c035141204e08036041401084100100092164404030b54050480e5403405520030495590840d40181e000940e0701444946841e0b4450451040e41c00902048400514009040000c100783e607200034030010306850401070303003001c540081c1310340e5081c20401030840048260798082d0300300610642c007403090309650a40c240b45000c4c400740761004240341d40703860154880e500d43c06c0303c2c0c0180200f607030b4070b004210304400f040e400182d4503c0a045038501c2112400d98801c80105c28030f044039030485400c81094140038070310380408d0504040700e0448100341d8105c2b110424508024 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 482456600 1250 482455350 482455381
    0x150e33030303070c0308010909020901051302121009060b03010e070f02010b221a03100507021204081f0204050607080702030102040b1201030c060c0201080f040c051e03010f0221 78
    0xc0c0c25000010402c030680d41e204114400301c51094643d8040b907601d40640c50308580c0c402e50000c1d001170b40c400051003c1d2901c40c11075140004010000740c42d02d070400c24148244c1005031000e102c100d6144000f0f000002140c000c0c04050050250030341d08542c9810140c80014902803d01c40501c444014800c080038400c1d00000181345003d0080d800f08a18401d080311020f04440175030203494900f8070085142100d45440ca00707407038001001411030304820013050f00100000740202d400e500c00ca02034003441e0700d0754401400c010048940640300000500c103004521f13090002200702c1c41072040109118a0365001d0a483d00f8540107103225443d08103501c01300740203200d030b5013244641a00200304036072080c04405017a8140ca214055070200030341e88000507502e060b200e490003404245a00e0001c0c3d0b02801d02c28207194028003446592505a6907000031440644024005c4089607911001c00085401d0034052401140c0094200310301e0050031104103000005d02c0401c410180c030340800802c0124404000c40c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 482457850 1250 482456600 482456701
    0x30e030106030c06050901030605040c0c03210603030507060506150a0c060b040504052808030105040b0112050a0b01171620010f151202030d081806040501150e 70
    0x210200540c4038040909690001b401c2d0b1070000381000004141400c040c001e059441c403450300d507100342000070740c0d054540c0e94400340b018bd421510540304010303040040c0603401c0254001d480f8141d8a2149050150613980f00825690003000d03541503520300380706410101d032698901c0d4500103100c1f14991a01c80e000e00850710025501c1030812062205014010403080001821a605682851400d0364001c0c082070100750017409008013400100010f00302504845065201450912070100f800c0c0d5125049441c00d4820845c2c01e5940c43e491556540c001110800a010103c0c80b803115103005100c000308a481e0b240d030342c0c040100c2901c440c200240544800c400c0f10f08241700900c0307070709100000e03100180020754600700c40040e480300c00204181c401c5000f01c3c010390040c0c0641010314201c402a00c400a015107020307044400b40520a104140510503640507510070000401c0b42c800c0081c141010078000d4000141040200080c09a000c04050750102074048006940055501c0e150134000b03804080d410 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 482459100 1250 482457850 482457863
    0x9090b0102010b1807180f050118030f1b0611060a0c020f0f0a05010c0305060d030806240304051005061c0507090504030e01022e1109030102040803030928030e03010603 74
    0x56000030482c116102c0d1700c10061540c0d01d20108052094809580d00607210b19161201080800d20095214108404040140301540c806003a60303a500c0054840d140300007134070744203c4040c401400301d00840c08030000346000e250042d400785121034040c0d100c141c0985121303421135030b4101d032424450007070020960298015065902064500920a8440c00d12900840c0c280d480d24105680e1a030291040740e0081901030681421039000d6078041d80c03500400751003950f10600d150007038400b840510b0100c560780e84040f65086d40768101407034001d10305110392440c0c5040c03505000400a2584a540c151508503c0d45018850f182c402c500300142468580d4004030480703420401040305064000551480740042a070031103800010702c200031a19185907a250807078440d01c0300000144c7d01c84a4000c002420b00d0281d9803450103040000181c22030780300354001c0106400100800cc7c41040610401d00c207203890704a0002030840c01841c0a036840d0700c0340030060500000746400c00a81c1c07400d5114a015640c0100c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 482460350 1250 482459100 482459119
    0x207061b020301061502070e0403080105011101150b090405010806040f0b100302061204020f1807030c0201020415021c03050402030309091e040b150312031b070501140f09060709090b0102010b 84
    0x2d05c1e415045075000403840242c03184280000710000302c040568415501640c4800c5640d00b02401100d2500425400d51400c1d900c4281744058140281c0c0400002d24060019a0341c40c100c0000748002d0b01c8050f070082610782c014000300400310302081e80c1c00a600381d001e180c0702010f540c0c8011880c1342044036000070350007601c08500200e28140522015004600883c0c8600d2610381600401c44a0b9481005071080c4d413901c0e80120703400c24025040204820300030300003d8101034503018001040c0c203072803128000507403000b80241841300c18042212220103440c40d05014524240c1c000c05e03600d1188070741c100e015425000004d8130019407155000110035001015800340d0034142000c200800040c0c1e045034000d00f2483c2d080754189000500103880c0e00c000c850b1181196200035003064603080180800407241c00030844180064001c1c815900e03c42e21b4444102000e0403c0c40801300e5040c0000c100c0f050300da0201003803100d030b070790081803081c01c803034102002003920504040100c2c05808000d254a030800c1c2c914 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 482461600 1250 482460350 482460359
    0xd05010f0311040506010c0204020d0e0a05030307030507050c0a1704090504051c020d0c060917030a0608060601030b030c041d0d02010212061f181d1e01060207061b02030106 76
    0x54808808a0b8054081c681848020a0070803084a5003a034115010558060035034005003015000b600e950501410009051102501c00c9418505201c42c11030f82600300004009540360548181030b005400c600d400c9061140c2c0d420310360303a500c1c010000940141c600c41e48000b00d00074107504440190000c514284142c3c03c2c80e02e8080c4d41c918112843c04a0000481f00324441c03648001a04074401d1032035594400310400c40d490381401010051820740b003180154000f000d80b501c2883c01540a100750500019101d843c084040e4108040902880e040505001110340a6500061900c5000c201160700240803030220900751401ca2481c0d139102e400e40142ca06050039a6010348c00b4120300701201c09860119940e6901700440540440900403240300b651405076207a03441000d11840c40102200f0b0035043c1620781a4240d1140c8040720603800c585980d104101101014450100410701510481d10316541801001b9403a08000d010b61000c01109001d81c0132030803004a030081e00650013500230050203403038 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 482462850 1250 482461600 482461619
    0xf1103041802070c050102030319050a020909130317060d08090a170102042c0f0406091b050f0306240109090c081807080703060c020f0d050405010201150503070b0c030d0501 76
    0x981039035259070061001606500200481e4070950340600c04540401100241000a00001c2c11144c0b03007030385c207000d409407645948fc2401d004512030b01c49466841c045250003032011480702c0d0000050420241800740540b070390300b81c000516a00400d00d58660b00c40d0404035402c0c8106622201100000c140070080b849010342c014403e80b02551085005004080010600c050f042078100e03071040e001900040401481031400f64106114080200c1d1400258458090540580b910000c80c0c0c40000340400aa00d0011440c0410b00000e5026249031324201211605544188011000010490360018802d86c0300e14905000380800d0310081020381c1d40d480e401040c0ba0340454107440901d000b0501d5400e8050700103400011580e0480050000c070741155564009407458021407410343c400c0300100040c2e0030040c819940d401340540c0c0d403151150300c0c00d4002402e40e59036010015a9000c0382c1d1080c03180c5d03180840c2000540e01e255413070b90781d5080d2180f400c9185104000582010758a0702e400461403541 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 482464100 1250 482462850 482462857
    0xc030a0818040905030d0203090304031514092418011e060f030807060b0f0d0605070210020a080606130b0a0c1106210c0f0705012405010f1103041802 66
    0x26408107600c10000700501049038071464024040364000d000201c02000719800440c0e10101100581e82819580d03074884c6000c03402200082c0c4441e841b460004ca94803100841107601025120040540c0091003180a000f201907220075003c8400ba40c001414030903e0800c003456121901c0001c001900038090780340e040107019a1048242400d0140c0003c8400c10b260f03004003665040107640f031610105640d00b00c010180000040d810040303900086002d60354400c200d000407801610301041c1407400c0c15000381445403406080398414810301030203141c541d1282c840c9030310080541d016030741c442c1c0541c0700a01c0b00c40107074401c9a003500006400b840c0c6079408a000c142e080e1060b00c0103a05590705c0b904001c800c0c0589521034080704132200100a00c02690f209582d0005001409103207002e60000702ca031429841040203a038182e460750740c0304450010002007a030408401c401c0c0c0407090b604002c0003d008400b10306109040007680304c00c803100310320140211401131142040b591213034240c61520030060340 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 482465350 1250 482464100 482464117
    0xf0c01090c1203080703050a09020a060c03080a05100308030a0e010204080d0207090c0806310911150f0c0c0d030804140d02060a150806070c140f0d0f020c030a08 71
    0x6494400c0000d40d0300c0d8455031502c54a80c1902c0c0c088450707071a0700c0100c0080c80e004282004072900c9420032409030b00c0d0350303940f207009d004280c3d43d514180005045c05004510301900710300c222460202082504400040070000f5260b10095065490312010842405400d0403a00701040d544005000544d1900010b80c0c43c042480035001c0d90b0089503078910399011034084244030000f05440c040010400e1607c82240407803110349030707002801480c44104410442070184290001e90b50f480d132202c3d00b80143d4039141c040d488002c80700c0580c40c1c4c003902d044040342d00807100c64000504010419904c803150a1000c1c0010010241110341c100c14179040050881c0410740f03042d105c1c641d0440c0300049000000c40c24042855168004007010b8881010b00d10003003518000020701d6450310180418604801d000040c028001c41d540c04001031074074200814002c00400c0d000c0c110341d0040080410038031011510005c0b120150030241c501700002c0c1004d905069144590750380c1402664025410408a44d01400586 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 482466600 1250 482465350 482465363
    0x3092d03090806150f1809010f061a070f0201120c020303011401020609060105060901020102070c08031e0c12300403020106080a0b040b0c12041101080606070206180102030f0c0109 79
    0x3903036104003094442d4010f031848078030054004100952400d050341c0e000210b09021b00400d2004240801c01803d001b01503e03d165240d444550101100c02c840c081c1002401402040c07801c1c0d00420000380c900ca105440b00106014111003000302960302030300900da5524080c0384244011807940710000d4981d48240078882118030480b81c481815440001d01c2440340340400020a9107074249000c00107035030010380c0c0e40c504540d000c010110002e090040c55000400c1c003c4000e644605612160785c6c002e00314500c03904404242801405084c203000103141810510804c0096603804600910074180700f200c4140100228000c041760a10650401c480e0348514000d40c0200025511600311549a10aa880241c00d00c503000000c140400d107070002d910f41180d0329121042c608071400c1c0100000c03040440b000e071200d2046400d242d0713695811000440e40024101c4909203041c001da8001840e9000d10f1728404a41e03107044605038036a900820481d03030164001c44a0f9512458009403440c007070200e140c02200e02 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 482467850 1250 482466600 482466617
    0x60224072f0d03090515150307090b09071403160203040306051e09010c020a150e07180f0204050a031509053c060c0c0705060403080406080f09030a03092d03 69
    0x10352003440f8009031300d9170140142c01c1c181c20004081c0041c1c2c1b8054880b0000140c4c0102110040c1d908100000081c44054004031342c88004608012030440300402d40e400740400c014658003107039003000407242d02c17001504212aa901881d0702c202d00e14000c2c0d820040c82186410140704401c41242038a02d4581b5a030324404c80560340b103498050070f17291038180040250f40562015000a0301d070020041c4235041c820000640705c0c00e41c2c580300e860401146c0c00054400820302680b04215824010b0744100c2d45450015450310340303041e022549040c14ad20014204400700561500e00c0d0100d50011105190408200c401c4246a0070181c03080000c4616000d02c0c009104000e508a1f00300c10f135540d0462201c40e0054030f034903500c129002c081903010f0020900709000d07020340402c256990740041d10143d801500c42070348030350400c50060070703184000e010250030f5405101044880e02001080b24840242860007140b07410445c80c0041c5046a5131a41c05080380c2108010300003040c006915400e002d0195803400714 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 482469100 1250 482467850 482467873
    0xd09090507031509091a0411100507030906050c030c0706030f0e010b0d0f02130603050a030e01170414070e01090f050601080106050d050c09090a15060224072f 70
    0x8440d404007015111903c0c0000402516880380d000d01e101074050b401a80042100340001844502c048408483d02802e1081c8038072181003d00d00042c0341009410002e00d004250f850107489000240704917402c01c00d000a031801004000d109480469103040c0c21265143d80340d80001e0301400c8600e40c2409213a141841c646030351101402000301c03c00c801303421707030000e0385107070b25030170f1030088040014cd8006125049010340040c161103200000c5018102414011b095450020410841186100d040103444086c0020029400600c940c015034480a01500044082c1c0b078203007061401d52100b03c10303180002c00042d0007240d03a041304824400c5800108100c1d1340e0200150740d000700a0194600080c020301030041d0f07902d03c99115175007040c04540d4890034483c0740000604e600008490550481d0b49490110040c03050403420040a411280054810003100000752400c4144012801d541c428030350700810300c4130740500503448040c030b00700e00828550074a80c0328944e007254461200032044e110320070780500c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 482470350 1250 482469100 482469107
    0x14070207050108100b1b01060f031115030408090409020f030d05040e0702061303211a030d090b07060203061807020708120f070f0c0f14011b030206071407050d09090507 74
    0x3020b554241603240e01b02101e00d4606040ca54254682d03a18a41d40c42c03501103004030506074504001c0d07120728000507060f000c041c203104001c15281d001c5440ca0106105100000e04002c09a07400c3c4101914002400d1041c2c0c0001003486268044164240c010124a44c580a6210000f801502c00c0d103082401d03140c456801c12a40c401044848a1201c1c0203e8041300c0001d00c52a21007208600d407828040803101c0142007542120300c50b60078421950f6020034940031609041c03101801041c4181040801c15140149024013441075400003016a68008000750a640d5004581d00e05000c1000c0c04506510302024041c0d41d03481103010b40000b0303115484c0b00d141e034000c0e44002c9a0b58501c0d4161103500306420365548a1210190700c00c103e425152100001c682440c100c0a0b0400608056403055030600020002415080a08014140440e85003440d00046600064519007100480c50192a05000c01034038000c030b030181c0390b802000c500071403c00b400ca40781e00c4506201920744d41c100030440f60700c0d14036098 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 482471600 1250 482470350 482470381
    0x11041220010212030703090b0a0506030d021c0c0f050703051609050c07060c030f1505100504050f09040c080109030807091403060a0209010504050301060807030c171f14070207050108 80
    0x50740181d114002e00b0003981c4100c00a0340e0400c28604000c00c002c03072159100c1518510842c0c8403859155200b040000d0791030308020102c10345800f80050402210030b0003015095046002ca05000d12511100c100c0402c00070031040720321aa04201915090b43d10391038040e0700c8919041c080d45900c11600c0c2c011603909100d103d807d000e04034018090340341820550321000a000c00c01c10b01d0003410f40d2061005000d0409001b00b4000c1e0101d0282900d5641c1030100300400c603240e0040307a40c100a03040c0824800c13911054002c158014040b590000e840c1c1e5a031030040c00c44102a00107048c05d50a0080c00000c041e0800076541c0101416143e000240740c5501c0c0500c166022000031680c142e002501048140c005035008204503d41807501c145456203800109081d45c038203074058007040d401f10380200144954688910050042200318000c96014440035a40d1100141400c2041d1107058401c500c0c000380e41d91280388003400c41d84610210b4503242c08082c0d01c907e000d1186501003180c100c0010503161a06554 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 482472850 1250 482471600 482471663
    0x803010f0e330a030f0f0b090d1b0615030305030f060609030a200a060504081603030c0605070302090d050313050108101e03240f0212040b0a110412 65
    0xb02003500110b198080491052005290010b845450200102d941e1078540554180031310600e2000c000d041c6440b554510000b0710780040c07a040900d604400c180c1c000701a9086036503000800204880303d080442c002e24100003a0140403107903100c0001015004800341d03100c0c030f821002c03444036075580c3d00c04d1105622402000641c582c124100d00000141041c0c548008142c0c007900f09040070341240c0204101119941000000c00c0c00401d003042118410000d0761000050980d9a1a080303255a4001d000c0481c00301c8000e1040d601c840009420610aa0644200d03440040c00c40741c0d0100c1318100b140c0c40f680302c1442c0c181800101d10021074a075000d0b0306080c2c05a00d0280f03941c3c200e90311713103104185600c9960050004c1451031000000118560b40c070f201030308650f80f0000040202051151b101200c210514448915006000f00700781c0c0c1c00c0d0f002145500c180c0020039034141da603070f64411800078004105030a462200118001c03804803a5060090110791280d2000b4442d604618140d10680158498 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 482474100 1250 482472850 482472901
    0x100b06070c050d05010b1011010e010c0c0209040809030a0c05010806040b01051e0c0105071107241101020d1e0f1509090215030411132310030803010f0e 67
    0x30050b81c00d00c003200107242805603000003250f580032400504070b12403464039100013800d80d506450003d0004e2143c6110b07800c40c0c0c0000c1010031503003130b00071b80082990000030f0b20074000da00000c1c0a11515004442c21288020143c0b4030bc0341091500d140004a24041c1030300003500240054041d041c14400c0300d001a030140c540707500303108050302d0304000980d109000c030443c20f50511001c1d0f42c280003400303564010401c545038096120b07900f03d0320030320b003514691201444d04c01110080281085d110300304240082c6500c0d05540e00d0a10030f15041c0a4468590f441d5000b80c50081d08680b180500d03906090b100d50034000038008010241080001e4401c081e50300c1c0100042d44008110600c803a91164801e54400340c81c1030541c0358602242604c80d0000c403020b4540c0c0382012107084e200d24010032410100100b00340304000710140740a141d01c014413460003201c10010300c840851082d1591400001c021507110850995940e1103408413440540f05d8030403200d41050318800318a82c119685c00c41c6c541d4688041 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 482475350 1250 482474100 482474123
    0x20c0a14030d061d22020f0a0803070f14010c09050f010e0d06091211031801180602100e0f0604031b120c0302060f07140f1902100b0607 60
    0x11a1044020394029201440d444100204600003000f406a40c004000f41c0c2d41510402d04007190484203030340000d1030324072150b10201440103c4540c0c0d1284004058042d070740704401e80800c5011620500c401c1d000352901744004960b1208000309001c84100d12131040a86245003409800482e00362000c6102ca1380c04500780348001c0c0f103982800c65012086e004145059103010040801081e030140d400c41c8280c1c0e8081e02c030014501400580000441d00e1415807a00b0420104030380b0203191079018000100b240310088481c240361030b81c441e610f2080b12260504034944e005e550307140d0103542c44030000c407d00034041c10f00840c02d05140707000c112101d08410f0300c005454256220b90301124042d000664030541d0303480c46d03299180401d107005031584100740d003a1201403003c14a401d02a10b0944010403440c4e01340e0102e03040040c20b41d0311501103140b81c40d2085440d61a00c1480811906034044d519114800c480d0800013400305550001740c14030a60408941004050071550902103944a004006002c04c403420 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 482476600 1250 482475350 482475353
    0x309030705091902071109130302061b04050d1a0709050406121a311a090d1209140750030714040605041407080c12010308071401020c0a 60
    0x13500180003d51144c07030254a00b010030381c000303a5002e80903100011a04902c0600004141d0100800d5400a41036045c981041d02d5030320300e66100b48902c3c080c050103a466580554108041465480c04004025a0001452401040c0105002d445100d41e51050b4204103002501103444543c80b4846500b160039440807455170346607000035070801740c180840c0080303100749a8250001d001050803c40303080c20ba186900e04890600301c00b14005e0206007903190107101c0500c0725030200003a400300c41441c1d6040006074000011800c100511031a00003500203084c002c00b41da0340b07500114004003a100c100959000c0d00030110001400042c25034800805000c0301c103080d80045001800400150109556040c46007208101003030030b221255001d241903000e405450f03441c0780741500641000e841c068604000e00c9440c001c0c08694164094050b005000040002c00c00038184035007100c86134450391038200e0055035a40341c259090b60101c1800c0d10201441c9070a90000305040c02140c629803030460040240e02c079103 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 482477850 1250 482476600 482476651
    0xf021e03190506010c050706030903030b01030e0d141b0703060e0a0809150405120106151d0613030503040825061707051e1c0204080601060c020a0314030903070509 72
    0x80c0042d13040c40011030301803001030810044003002e403600382d5011450004a180c040c0643c0d011601c0103050505000b821701c941c510000c3e01d40342459072441d00381008006100c0710b07001072054840707118540c101c5141018100d5400592003084900c240010000741e903100388032940310494a517004040001c1006401540e14180104410180c14040c4203458a81c1d5607001a0000b0400041e0400d01d0f5120001008851070b0240c400300120b09600301149903500e001038516035601156080391180401240410f4040d1010780840007942e4000205d80e541d940f101002940c80c0c130a4616000720708041e0907501520b60302c100d05e02046031030584a000f04102407488441c070b80b000007031043d030400400f4065601340c80c5440102c600003c800702c0c8802e655003940c10000d11001407680c03032420502d004000800c0700100003c0c52504554461900920402151000800c00802c6038030203844440035a920320010031000c8010721449108030200e446140e580d0043c028040d40403580d414400d817040916071985d001 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 482479100 1250 482477850 482477861
    0x609140a0f150e10023409020319060b030405061308032e061d0405072a0614150906010f0302090103091a100605120103080702010c060f021e0319 64
    0x3003420214060300210004c030700300f200c00b40c2c0c5000050740516450029001c00400c5180d5030411034900e10609908240040024001031180480055001001030740082e040b0425580103945a1028019195100718401040c0c005440c250703060b0203844049015103040c0406807480941c01004a0f040d5540c0540380309180048403a50700304007082e1030300281104c4032080070001600d4291510060100c021100d403040320a581d140c54000c3e45000184513001d600f05021954032041d0030800480408040e2421030400300000000f01820b080c03d0441800c403209000c4684142d22068400c03928408490401849039000d54426001c81d1410a642d031000e8400d070010521800c040c140424500880d5403801c24881d40105249405e81ea000140001480307003011480c0103000a281242c1842001110013071601c00610005107080c1000540508590040c8840d04400d80c10040400ca0038413510064800f035800940d600d071400009404564100001800b50303030080b002200316440100149074004003c14 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 482480350 1250 482479100 482479139
    0xc0a05010c0516090f0e0f0304140303070c080d0f03021303020108070908060420010203030405190212031c0b0a12060203041a01090209190b120406060f0609140a0f 72
    0x1980e0f182056600c032409a100060a1601c1c0004020554103580c07001c4620103014015141c1000c80c220000e13400000544064446080c1945040361900e0006450f40c07207003507001400d4020700800018074000201d26034a2041080d115040c0000000100301c0882c4204a8000c0c800030280324140095485840c3c0b0aa103c07506040441c0002c0c1c031104003514080e01103804650300c1d46c00e07a002401c1d44dd98849403203d0014280001c1d0b00703500300b6551705034940034041c00c880721141c2c10f072220078203541d540358001450402d45010b607550785180d00c1c0010351880b1401000700301d0a08000d0300080070706007150400c0858640919038590074005542d050f01a50020708141d50400e110b4211a10a0307042c899900c0c02003980890050350b950081081c020b54505588084c0c42d4101e0440080200c99031240460b0b1180d0411404a01e00741e48034a842e40007810700390420190004000404103001d034101c0c2d61282035503828a40880418254010014104018012070705141030b170400801c10201030340c10802601 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 482481600 1250 482480350 482480353
    0x70e061e0109090e0a05010b1813060219320a1d09101d0c03190603061e0e010b0303091306210b0a090803061311070b07080106020c0a05010c05 63
    0xb960707201c2010003640c841c1984505260420208941080707024847e00c192200b00b6103240c00c0c0d0050780300001017501e02c0204000d0211a4000d030480402051343e0444807411020450505d540c4840c540040020002c0c8045070b83c1417048240858440c0c80840c128080d03620103c0131249018054101200c4003900300f4488010640003014598a60b134030407901510618001c24000212032905101c4001105040545014191b07260140000d090050048030380c07101002d03000318130410b0802c4100c40201015072010305620700c0c04c1c5059101c9107142c48409001394010f0340611104051144407800ca078101b0ba4040d13815882003105680b20704010002011301041070700c00040c07881d60707035400f181d40180c070b40040c02071118010011001c210140314100c0c0c00aa00c400c04000340c61299948294074400980051b200c1c60b0710118004800c100e6400125080f04520807aa4560290b8a0040b034801000e980307903030100f6015000460407510028400c640c49070000e00c04081c5501d00001911410800d01080d10305 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 482482850 1250 482481600 482481617
    0x527062203050d02040806071e0e0108060d02040504030e040b060301080601030f020d06051504060605130302120a06320f0412030209030a1b0504150b09010201090f14070e061e01 78
    0x803c011071015000500184001e0105031500308002000f80200b0004112000c40c1e0344194130040d688040301e0800340000b070030f0491098440100048a6030081500250300906003410070081580c041c00882684506a50a00c0200c2d00d1100300540c9001c00d0284d481d031548410010808501d00410200807240041d0510b1081e18441c2c507081d09489045a244890f04003109510101d0700b424810034000b00105d14000e400c0c02d08103600500e00600a1001a110b20415030170b80e03030b80000910a0f42412944800c04002412142e0405419800c072222070070720590112201900368172035074040c54825410740301c00180583d41d07645c0d800c0c2841c00710b100101c1059820305c0030400c46c0c0c07000c100c0d1100150094913a400c4051908540024410040e00820b018a082c8402030288103086102071040c1d8890240003030300c803c0c901c1c0040b80100300c07201016082c81114142401070020044410141d50820010780b0900d60700c561403c8140d0f102500c1c0660001080384840d841d51403043e080158500c414903041d6103 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 482484100 1250 482482850 482482867
    0x31b0d0309021c03051908040c0504141801060513090b01050406080619020405100206060a080c010c030c02040207020405040308090d02060106051206191e081603080c10052706220305 80
    0x5203110b86c03d092902081c07241092005002054070414018902103c05001c0c8441d02560700c50750241c083d201a01144460b4542c0305414400e4010401502d80a032817144064042081100a04040300d026610480c1040c00841e260070180946005d84e44503000803c000e4585c203600300000c0c0c20f5072055150496003440041010341e03407094001c06c0c01241ea4018960b9041203030030070450703038041c1d4004c091580c002c02040903d030340c0001036648116050304015a11280c240041006031240d504025801440c0a0401c8100758000d600113000d8903070b8070121140542d02d020b080e65600b4080c00b0700b401140e014480903680d0000442e8613540020090035040303940b00701c0c5000c0f54620029800200f04c050018401c80346841031107079604010003101006003000d40316403003030101d40e081c2404003411441c800154002c11032410402244200c0e0380c5101089a403600034007144c6c00c86441d03400b0202c009075265045880d403200090240c056007208004d404c158110b10310601c0c481c0481c450490500400f44102c03079 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 482485350 1250 482484100 482484127
    0x2101413030303050601030c080601090519031403071707020a05060f0c010906050a0b04061a0a050408190b060108060924032505060301030f0320031b0d0309021c0305 73
    0x1000714420346001c80c00e0704000b03001405603184103043e0320810003e00c081003c941e902204103811a032069030024000482c088081c42040500e4002811104d1840b05101030101d000004065842c02000300b5100c1c01d070054400512407045207006940b0400b401414400c40c9818001070210038100441180340594880c079a5003501c241c11420340b00c4c141d40e0010058085640d0281c0b070b0071190205c0e0200089800c0ca1180001c041460b9200352210001080c1072003224016030417200035003124812500702034080c1d01d4442c2031b2058660200c1e0640440400309000354003031070020b0700484005011420781e583d40c0c0340803064103443c9541700c019820341d42480e0901c0e4606004c0240c038841c2c040301c4112120410800b812940c440b5070f000b217004240c01c200402c0801d5174030500c003405942c1450f1850711041010184200c0f00e404e0440b864985c0030004980d80c3c01000601003080199015080c0d8488102c0454150201ca100c050041d400c070707501210701d050341c00c584080307001118840d0810a0800e80380305002d8 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 482486600 1250 482485350 482485387
    0x7030f0504030e041a0a09020d090515090106091b032f0d0b030312040b040c0b12070f0201020a0221040b0301030b0103300806010c020603070504090b0607021014 71
    0x50b00400c001d051500101c1c20315004248600510007040d010214a000100d0003200481c4240c40781c4d0b039801f0440c1407905525030007c1001c1900300044659902c03501803008074541090b21165400e41c80c0c8040041e880e4094051310756801d000c0307180001c03100c442d040140c01034151004030090017a030411465400340510b0303654546c0c0c40801d08409458004140907070045070020001280300754018040044200541c03902d055100354040050f201036141c0340341900100d811794010040809000c104208100c1c096031202c0d101d4049d587d41d500310454914800d074201e1142c0450800140c215025054141c40200f5003800c0b483c05c55040b03586000e07924850500035800a0308201c0b1441d040500400034000b0130f903c2501181c1e403101c000700840001c40415290340f16030409140600c040400016a560700a00361121450340183c26660b50b842c040b0740041070380e4010700960320600d2070100300c58140c1c20050181e501060740548920300e1540040070070389101c4030141403064880020800541c2004030007020 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 482487850 1250 482486600 482486603
    0x30b04141f0e0c0402070503042102060d020a0e120d030c0e0604240305010b03180c0d0302062a180d0501090b0a0b090610050c2b080f040b0f07030f0504 67
    0x80da040d9500ba030604000030240041e2203140103001034408140080100c40498031084c084205036200301003118060007251030003070351010011910740c001c15800e40050801600790396511448100c03000411185401859241c080c59100101c42201c00b400303a40111824040313402c100c21280030400014195502680159103c280010000020000c0a00880c3d1025219080903c070560400c40f2500103404010150711800b440440d41410007a002d0201000c0d0490141c5074030001681810060f503a030f83c054880c4e41c0c0c450001d51040c0d4103c28400c2c00d0070b05513200621510302d8001e08020b0740203c01d0070051038a40c0300b12003d105a0026100744655103032148103450b120801d181c802080c0d4101c400c0348a42d00c1c0a442280200185642d070120f00d0f6a0402d03036401e01907103682d210203c2900c2c0030404080c030300c5881c110980c0960303200304400ac201448203c03aa1548055661010b007450b48440589008205101c800c1c0400c002001c14440c1503070102d483d290008800d90402d40e01d2054507016030b0b0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 482489100 1250 482487850 482487913
    0x1091505010f08060403050a050c010911030712051903020106120f0506071b1b0f0f080d030c05121e01140405060f01020c0103050a0b0301020c150709030b0414 70
    0x422016042140262401011102c0039009038074030345125607485410040c0010100240001c05500050240301a1a031148072000204106411032501102440030410060720034481c450002038814404040070360aa54000c0140c2400d4003071390044294400c070180102c0665485400c003140b440300d9411207402090080d40350101840c0d003070800ba0b05200010380b07010204110503085160907811a00b8400d000c2e13501000c4500010a60300800d180644160020080240d16010000f207d42c050144501981c403a82d05440305d80313699201c1a02101c01112140d07000ca80c06200c00e144c041815111141c1c010520f5216a80030060341d4900301035204242c022205014112044804c80c0c00c1a00c91294043c0e0142c0d03400d03068010078000030390740f1381c1c0c000c035031030b040544440001c0e0541246410801d00e103038000d0000e44d00d40300310000b1152207842c01042e8003100d51040c00040e1400c2d01c60206002107a80220f00f2502e140c68546680a0080f14100c0030083c0f8400c42c1c803103e60280c0065150700b0400800035 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 482490350 1250 482489100 482489123
    0x711030f100c0806010c0803090f010501080d02010515090c030a091b0e1e0a0c09030c06030c140304150e0a021f020c0303040b0f0a200309011e0f031505030109 70
    0xd952088410ba0000001001088020012030b40d80160b4003000c0d141d0850070882e101c2d030303c10341c0c42d51508400003a018281d500301000001c240307100140c69203140c00d240c2c00074092551241481d42021041d0203a46901405010200e5110302e007602c011074000489200c0800d003001c113512184210a0180c500403003080c0001c1e82009540030304010150403c0c1001204845030300c655410b407000f240c0103001c81030465524500c0f604110b0140445c00020b65000d076000307801c02e540d240e0140003088003a113035802041c002c440c401442c840d000e08491245034049400f00c40c8055804800000b0102c0701c0100c0c005201d8000c620000d603036106000900a40c018051040940740003030002c0c1044c0b0070b42603550180d4001c1c8000d01100d0000400c0d03502d03903034020741e00c96100c01030103c00700c40b0310116107118041c62004914014132040c000c4011b080b01e200a07203132081c0b1102070300603805807200030a07440f00c00954020600180b0b584603400594200c02c0da0690303482c2450f2a04006400c613250341404075460500b06 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 482491600 1250 482490350 482490373
    0x30207050708120d05060906010c1b05120607020c101b0206071407030c050d0503041a2703010528200406030e06070806091609090f020702010306050a080c060711030f 73
    0x1809000c2e07118a06a4000002c8d0030b10800280c42c2c0c1d207110000800503111500c002da2054500070a03040140b44c001e010004100a0f069080e4a17a030081c0c0c1c5000041c050340305511010704000b81030030a0458035594900744203030302441c8000c6101580b02e00b02e074019000c00c002408038403003d89104243d400b050190049901e546041240c0d0055980091b008410f04070510b00464800700607103040320b0920b40017036604846121466082d206e801c034801d807180ca5a080f07140220410724200320302c81406800810060300d9a92040c0c1040d00d4007145036240e0442403641c01d0203103546400a07d41140032408d00000550804c80504064205400c01c600203580d0300281020480e042103030b140c02001e1410524041d00f05840407481d1072200800810250b420794803202c4c00321303200d040c41400922544004115040340c6200d5103010b54402982030380060b050010228a51601110035000c90ba0040300a00d0025280401d104a642102c8800d450883c080c040320780480d01c082c0312580050744c95070090240c101d1034 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 482492850 1250 482491600 482491627
    0x30103081b070f050d0c080d050705010b0109050d1101140406030213291c020414030c0405010e1605090d0803010f0b0301050312030c210703060e06030d03020705070812 74
    0x400035a0510740d11840082001043c0c80d00c81d0400d403501542c400e520041c203810000341072425580165002d205500c0500c000a074840041c0c001d4a10441c005e211762800c2c0ca004407100355050041d00d511041c2186c0030000140e0003041d2208805060400080d580350445c40d4621981003940542e004c40e40004444110042403100d8502503c0e01c500e5415090402c90501280c03030510004030325201c0300c00100c0b00f240710b6403407108203003000c7e0040040d5035450700e802c24240940070030250180684244010900035142034050281a81c50424070240596560400303000444c0030b142516046c00001c20000790b054540c0c900700c01226000d5060a0382d20352421140706004e85440e403000c0c0e484030042c030040c007860381d010940b0410070b80a2415603482c3d4590458403503039845510041c0301c1ca051f41c4e030180d00300a8180c02c0d000303110307400741e40f0b0401446584603140c40034208222842e95050300818500d500d518026809048424014811650350b01e40354000586413425020030050400004528045d51024 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 482494100 1250 482492850 482492887
    0x7030216170f060405071e0f081606020303090a2006040306200a050f03040809040f141008060610021c03020315010c1a150d03030f0f06050306010e07120203010308 72
    0x500700001c00f01807406403613250311a00c6a0007580c0c02c0354a034500070074150004101580c068440c84030602200d0703a07652002561019260303400e41c40c4240e001c000042190000c401d5074130070500b4201600f400000c0f940c1d405c41900400701e14844c0c00040d1201080c1c1500e400c4040d001862080300e002550100301c607806015188052034500460b00200003180001e82d0140540302c3c4408804c440d680c03030b40c40714034204156011302618250010719295003611a207165411500e6401002540d00c5415290000248040d40407405444140e40c480f10129829003004c4c1d0352903903990750318410717141006461403a80204191a410b80000a5004803c1c050529041001d800c4802800d09107401c2582e2582c0c0c41c10701c02d04070700303001e1007044c82213000040c1c1c00f16950211902c00386008201c004107401c1c900c0c2c068001e00c840c0e000043c51601d4442c24090400152240b101038400c000c0043c42c560b841c0010014545ca0000c000e4010080c40f5407110081d40c0036800510b01a47c070441ea6540ca0700c03544c54150741c1202 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 482495350 1250 482494100 482494123
    0x60f091b0c03070b3d170a060c05390304170d08010f140d080c1e0c15030411030703230105010b041701110a091809020f01050703021617 60
    0x1032408102c07801e80131040182e1a40101c071000030b1503956000000d05c40340c80903801001640303908007100c043d00b840880c108601c20300c5a04d0801041c01418421100c500403030340201440e82510640070040300e0b075205c0a000991402079441c103c06003074481d0a013942c009074000140f01604145420780740303500388030000c6008082d00c0c1a00c902d624104640d001682d8621801189402424040300d05444086a00e038409821414a982d200c05407138140f9680c0817244000ca56a0660303030100c50b0201d4001c281d0802992009045020503511024020810390021700b040f2100029842400e10b5600d043c040c1c0d8004600070300945440c003220090120a0080c0300c100401d050345004014440c044a960640b002c0c0c584111048a04180c296502c0340180341c0704041c07143d0340c540403841c0b108050384100044140d0320101e0a81025412004108041e945880002540300801c0510308511354400c1c409031816a000344104e03007000c01c003420944018070f500c1c2c0000d0352800340400f4000c40e4074001c0160301d041c2d2 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 482496600 1250 482495350 482495371
    0x90a090b10082d191103060402030613050a1a1914030a06050c090117041109100b0a08060111070e0a091407060309030215060f091b0c03070b 62
    0x5088100001d42260207a402090038000b004011401c010000c410b0810b0007402c00c0350011a011450044030794407107049400301101d20101d09941844441405056080c081d1000000e045446050400020350401050340350400301c0000d070605100c146010341400340d840102c0010352100e2035154010070fa9000c11a6030300404121298408142d0011741010480f2180f021300c1169258200020b0700309461941c019000b01d0170001448019580c040041010120980b03503070001404480722420307624011100900882c01801030a041810640201907100c240840945015a120004108190050410b00b00080c0101040100558102c45651464a4900005c0c44104e2800c60480884035000f40034900f20382e29012200108080b02d814000c01070300d040203880032a501c1c3c800040050200c90020746c0140b040400c83c0c00c81200094030a80141c07000380c05144504583c0d0f05008441d18080c1c06410760903130b400a548041904030001e03140451080d009195603000c40e0806214103000070703081c503ca8 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 482497850 1250 482496600 482496611
    0xa03091a0f010b180f01030219031b08091903022a0103150f03080c030c060c030403030f11030703091401020a0302040302130203010b1b1f0e0f0c060901050708091302090a09 76
    0x605503854140050070300446517904811140001200640100c02401020240da03001c0c444081d82c15421034200e01018982c0d112040d0032107141200d114409a40c116040d0f003002202e12211001d00712586010741c000e0044486800d40307200100c0140401207010b201d136002c00c1d060f03210550390600074060380c81102d00e04200e40d1b0f810b100003040e00a0003441f00403c0b0941c00a100c1080c81803c2c0203540d80d892400054910710b144c010841060f580c0203c601310002842c000b811566025644118038540c68a15000c41c11030307564204c01d5009001004003600d5624007407405451030030090000341494401642c015031580d286206004807051000740c04245240144010b000c4c061107141600c035504190040d8000711400c0304021801c3c602038103495015a40d44a20a0881d20719070b07003208002c10001e0045400e084c02901c90b0503100c02c00c1075016a403041b0104801e850962044001d42a00d80c00303541124a442000c41c00110340c008070011440c1b6403034010450507102c0c5801054140141051074040c0300 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 482499100 1250 482497850 482497867
    0x803070306090b01110d120902060a0807020d1106070c15050109021801140d151701051503010b030607030509010e192603010918060504150b0102070501140a03091a0f010b 75
    0x81719000c0b0701c00072007040240181c407c4041920340042082940180c203042d9226020310000704120b0007110880c1c00740c0b203903114582c6118414800088003207a2000545107036103440d403040b606124070080c1651090075211000716280c086200f001d00816103507000503030b0340b059411104c90456019200e14144001040b044280c04400800c079120020741e4100014401c2d075400c40221031003010740061402050399101d940c600f400550246c0c0c094001000c00f41c2e41c40144004140c2603426080c0d2030380d0142c000f40c02040070300b4041d400c040e4226140d1b60011605801200d002440d04191020940218410907c844103010700054010402080d9660380703145400700a00b154403070711045c0305401000e03913100b2002000d04900c0351010011503004d48280070b103080500300301d21481c0c98240c20f501c401d803502402d0245980000745800441e5810385542050b1180c0319000d0745950040c000420a054035103030440001041814075140f01105440110010300382080c80d09030744a0140c01062150004001d02c00 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 482500350 1250 482499100 482499103
    0x11503090305041a070f08070201031a0102030706052203080609010e010b0a0c0305130914150d11030c060c030c060f040f0f03032901110312040b130803070306090b0111 74
    0x60071380d115a100035021100c150300038105481202c401900344c03400e0f0b051000810003010b005040140c001da03018001148814103600016034891403182c00350740104520800280a90856503010350628400d040e58240070b480003c6240002e1422000503c2d4141000003602d0111011809000d0500010388690306001084c21184928103010003402050100c180400d8424000c8031505400030321a00091940c1c2c800850140c0310b0006603245007030700ca0f400038403d0845c4048915005c80000d000a5104069880d800c1c690300c1450340080d05801110001e95294031007600511103500030300011540d61010614141c2803000103051007020210b400c0620010500c100440c1c0e41c0960049240c079141c144600d415801040d0001607408013140740410821909100707421901420820f072500058910041c0899450340b04034011281321b0f40382013000c1400b00e60f0001509034402d040c14002d541103030098844074020741088444400003074445109101240c1c0038024080e02c8071003030030880d0b0200c9840304d505 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 482501600 1250 482500350 482500357
    0xf09051212011e0b040e0702100b0112090c1505070b011202030c010518030708030d15032d0b040804090b0d0c17030d090602030a060b070b070509010c0b0906011503090305 75
    0x9002e40b43c0c01005143e0302401e12043c028038220140c1c81d6900c2d622201c00b92200c0040302c1e50000360180c0780007840e25107054080c5490315001659003140c0c0a01060040b0000e00c0b1002042c0c9800e180d080022441940c1040340b040b55034a241c1310309440300e602d898407040f000c5050b040f07104500320003400ca4006850000d0043c0d44e240c001d0038002e07214541100240824010807000960603c52664001a000008401080801c960110a0002d9440c0194041c900860351200411200d451629005e15003840c0e02d0040d00404040410824045030340c80340450f2510603a000e480c0c1c0d000004040054001610900d00305200070342c0d2041c4241095111240c40455a202d101c0040849125080e40440c3c140111404c03c054400d04000e603804600b000802500300f140c1c01300f095498000d0110725503c2c0401038942c8507a00002004160342da007001151141c0080110300c2c1070040803628000000e80d40e280c1c0300d200b07041c218014003596242401c54030012103041401000e0515001441003c00d9000045 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 482502850 1250 482501600 482501609
    0x20405010806040b1f1511060f01031b08060109090f050a08091e0102100506030106082a092403070314030307030c080c12060d170406080603070e01030204050601120f0905121201 78
    0x60001e41e06d80220944202e84030403500f03481401100304000c1040505441c0c0ca042c1e9004448080006c20031740040c514241da28000c500069100d0801005102480d801c120741c264800d00c0d480501415030355605281c4072384683d080702c1041010464120782d060030801c04c80f00b039581d00d541401043c6a100007039240c01d00b401149030781584400006440740c5094210030000d1405030111001140f250081ca52003189032801e01d11180d81e0300303403021100d10341a1031487c02034410001d2041c40002c0954505010042c0500341e9400d0f001c0c54070004003048000701d00c07892040c0b94401031580d030f1612420050445861040903424040220b0500076403000c05015907840c00c20524503a84e0503160301000590303940308031a00403c00d00c82051211030f0384000c00c0103802260354580341c0c40490b440b01c0701099101c4800d4080c0344240c41d514001000075241540025411850604184141c0f42c1e100f1408000c0d240b100c1d81c0c0e062056110030385001008010400030300503094100195052004e0260740008204d0b06118 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 482504100 1250 482502850 482502869
    0x7030305040918120c1a0708010501051e07060b09060d23030d0f0605011707021b0f0a0305010b0a0605030c0703050903030c0a030201062d0b0d0603020405010806040b1f 74
    0xc43c8800b1a09100641c4440b600030351a41340d8420a450010003085415a04481c03210002e4000060145c01c01a264040c56064407a5001a0f080c01c0045403950064506018110004561110168078010041c800c0c14000d40010401401403030900c2145d0304060b000c00e0151360240d8404011410f12580d003042080c40e5246000c00d460403000d000e1460013503840c80c0420b03a1030300c40c8401244480e075100000300d8000ba200c8420f140d403000d07030701c100703b02d000c07a45007015802402c0f4020801d4040009000c502d640241510b1034103c0c5e41c00468149403a5800c1210169550110001d83e0b1070f152481d0002011245022031861414000c076072564001c4550080510001007400eaa26960600584401510301b50407200c0e02204d6040c001d019004c180b290100b112081045507000603900484650402c10303665082103031714603151003040103a1114038022110340c0e681d0300110060f555402082d00070700004c80200518181402c201c20311980113081c1d20000c0d040801054441104106001c04441c0d8409 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 482505350 1250 482504100 482504111
    0xf03060b090f1306050a090b240a0c020d0b07020f010608010e0a0b07030b090a020d32060a090903030b040e2802010e04020c030715150b09030708190302010e070303050409 75
    0x3082030f0080d10311600229480020480c020480003c039074041000780104403000c02c07840500500411103c0314816240500700070400c403581000c0e000b40b541414a82c8064800c00902c4000d4031004031007102038400800603084080d80d440c0d0350000b40904000307441450020000c04460009951755080640030051606070080c0018100130f0003a44481c0d0035800c0a4041078091500901c000700a51103a1803c01030586004650704003100d0407607d44001a6050030a1281000700c412030407003010006000325840201c0300e10100b1355419a0080c500c403988079407000300380c2400e0541000700351080c00403401c4440e440086e0508a0200c0b00609034500d4000754044917580c40d4900040b90840b50b00907a03580c00070300000c0d11a001d085c0c004010604a400b40c0c04c0c005c902202c04901c44103550501074115a0307120038850078030400d034510004080081005046410b51a40e034241a07041542c0a24102c0c40180d181700c0f007106241d02802070580303200c40c840c090070303c05045a9014040b03000d140114bd602640c4d9a = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 482506600 1250 482505350 482505379
    0x3120406060510111002030c040b1b030d060518061f1209030905010e0d0206030a0218040f0c080f0f070f030902031002041409010e0a050907030609030f03060b090f 72
    0x240d200e0409008040c04440c540002904054040c205940e00f44103641702c0c0c0c1107132907580b030114800d8a01400950440d14507261504c0040312160704800a84407920b01250040003c0620810090092551800000c60118a000100544034402e0b00a1142c105255003c0001d25655141c03002c1c00c074075640c0600d01000c0040c0b6030484a0080c1040c0074112185008075000a045c1c2041c541c00444800345d84500a0008039418020075001c5144000c0d0800001d00c04141000080d402400c00ca80900a1810000102c600040c05079000110801105a640e0485c4007050360f02503003030395009440c014040b405050010000608a800402c03001c00c00c1204000e131040644a6000040030340d0b00141125203003181c1c0781ea02c0d0004d5100b44108036045459403000c03405070504450090494492100e000712a0740c40302000000343c80000c00c00c610a025520000c00021024812080814001c2da1580b00c0042030310701c0a0219079484c0c02c800d2180c0c42c1402071072196920034204403001001543c40b00713020401d0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 482507850 1250 482506600 482506613
    0x403030e070b040605030114041509020906070b0112140a08090906060f0d0515042d020c070e0402030c040e0a120201110a0e030d110a0b090c060301180617031204 71
    0x1076041040c400c0400a80028030700e901002840c180c230034803010100508a606e08000c1100c04403254031081240900d4200721048d0b10f03038083c1c4100382018102600d019090b9039114500d42c800d8100704441d046815801060185420b81016100c0c09207000f002000c2c102c0d02c40c0034582c003903110352a100314a6540094100e49a1400399410707082080c03500d075183c2d081200c03450003400040b548402c520319142c0100201307107031600038404012901038132603542424074100544501c0300a40051038281d02000102c000440030041c02d0001c0401c1c80c10303081c80c3e0405104050800204c0b00f4958441c9060100803c10705034042514043ea5601c003d0408a4a11100041c0c3c054450140903001114002c1425904d540d044040c520718801c2c22070540741c50000c0c81400340c41100f07884a07010304903803001e04070301c000403030750700703040c3e80204401d400c8912140c910800101e8aa00036045500a549003015031107240b8000d00985020f0300907000c801d40e08454650580e540c900034a0141846420603c0c04101030041 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 482509100 1250 482507850 482507863
    0x7060305191e0507030902181303120612080a030605220b19060f140a090b0c0c0d03090e0a06060f20060403020d020609060f040311030c071418010b030403030e 70
    0x61480081c400d914140401600a100100d0f040c2c6c0102c80c06c1c400c07061423543c0141c10511501c05041da640780c940c800d071402c542101155108008860b82c503400420400c1c2e100210311100c512600c01c0a07500c0502d00e40003401d41e4a5540014010b02802c2e05c082a40400018048041d2008160000b1000c0480002030140740c003588607040c402c2c0c0c002e98007107060b55000403842044015900e4403480f030441b50080700302600c600d9004c0c0b000910020710900000c000301e40140804444e5004072500c81c40210002000c440b440d0b08100c011510000040103005034840c1c04036030202c5110401c001240c509072000d03150031142681a410807001e4650825110354980034502c8000060b8204c44e030038a07240ca4013964407002a600480507120383d4000a0002e0000120f4500c9032020465841c0241c07900e640a6034011201c00f8101c0f0340f4082030180300c0c580c05040181c01d00800540310743c54900d807580070074802c4440015803080010011003006019100e00c0e902129005585443d00003080c0c0d2040108600317000 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 482510350 1250 482509100 482509151
    0x702010e0d080301061b0b041e050304140a05030f0604060c2321250c050d0e0109050f03062a0412020a05120d0c050c040e0a050706030519 61
    0x58080400c4424811002d001d075050f2005600c03a06130710b884440d01c0c1644005172200082c0300300f03191000200000e1841071040da26081048400c000340020340e80e818191782043e08040c030103a0300d105501c203851030206131110013481c00398041d04807103400003242c5485c0c61006201801a9071994170200d1210710450b801c40006d0701c580c02c1d08414051550281805600901015410130b0941600c3c41140036002a102e0060a8140410510924101c00b059580240504400a0004d21034880c4086181800000c5000d507540c0e5407070650ba09600009042c0c1d003426088180203030b030030701c0000940ea00c00040c1941c0003c203001f40c08207600500d240010b002d0100301c035103004d0440c02190000342420300300c03103907460144200c850226054a60003402541c1c40c0359a044c00c1e0540c86581180162401503c1c4405102d01403000d0380c2c03030641004e01080035038460703850b4082d103a800300500e001400340a101000280115180511072400c0406080700a40010300301542103545e80c210720300310956a424400c03501c0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 482511600 1250 482510350 482510359
    0x8131a250302030a14240f040f0506010807050f040e060a0f030302031b160302090a0b0916020105100b07140f01110c0607020a03021015030b0a0203040c06050406090302060702010e 79
    0xc0303a461002000381d0016241c1c44091401e280c01134004203c0741160a210351406200403044000742d00e5000c030315504030400250000c5041c2c0c001c1400752103d020348812624415404520360811600042841300b009003590100300e01407002c0383e0034002aa04881c100e5100d4241d0741056120800001d04508040d480781c3c09586600b4000810141c010014120f440d1030018840c00302c03002ca004041d1101d0340074080250802031007001b13000614108031210b81201100d14001100340f0f000c40891070060060f26054004c040c4000b190040c25424094150310120034049071614514001c240070701c40c00707602e0f4001e101e02000d84142a41480030090150f46010342d0300207205080d03100a02c0e4920744e002c122802243d0185800140fa600e000041070780e001985035000745a00d04176800ca040041c00c1c40d14024040e441c1007000000882d403807541d0b841c05280310040050350f90a1602d403820400c0c0483d80f018048c01801e0008100c1c0c550805400000c894040d40c03c0c03503443d8500d20048802e0b0001d1100a90300 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 482512850 1250 482511600 482511661
    0x91902060d0e06090d02030f03060418060c020105090d02010b09221509120f020717032a1504050d1d06030703090c08030405150d021e030708131a 64
    0x20b00c40c00200d59001d100c581054486003100c0420072a01c0f0f1140300150032600303904001044403400e05601030603d2404030a030311412850240d4402050740e240d83c2520300180e4542c07060120324401444500352010150008121100301c01012407101c240013009203c02503801000d40c00564900301c450f803102c0c0d0f4808400000c2003110301060000b44003000b03043e10a00c0482d5805c908460050b82c00c8800786405400400e00c0a25080700102810080d903c45002d80c00180800060140310800d02e198070b21a04010101040505500d00d20303020100c100861140582028800410004280030000402607d032202d100441c444107490b0b41c0071500d4580703401100000030401c0e002c0c1d1651001c01072602c203850896a50740d48a056070303582e009600030b6582c040292400c2d40c3e0015403503c020182d111000e240942841c2400302620312402c0803113821402c00b10008100800a0b030f03c50640340d0b1040820400ba0350b9440c19031145002d40c1c101c07508068207480f040011528251045225280000544410544 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 482514100 1250 482512850 482512871
    0x2e02091809160b03070e091803120f0f0103030c0b04050c1806040516052b06030807050114010b0906070c05060f0a08090316030c0c0308031608070206091902060d 71
    0x54880c00d42e11002c20341c1c00042400b14100d408030080381d0003456136035900811102c50004121070820042c042c45030445131101821500c00080c0041d228450b601e40764043e151404004005d141c00009000c205a0844030380184002900032858409507074000f20049a5951141307849460402007a0845030f000d00010030300c802c0c0c0e04116004900c035541c280c900344201c2e1039140fa0500d80020351111540441e0081c03000603603800e0080b0380520501c02c084044045103605410140c00c40318150829106901c000a1400500c00240580e4201e1402c0290301442ca40c580134280c015400762001407031142000080550030f201c420891a0040c00000b4015699070100821240c4540e102ca02ca00012980c0440010410f01020050326441c402030038522001d0422950102d4200c03800c0e0800b1143e0b901c99000c003002151120001d948114210514000e051078082d0001e0320440f4010144011580100c00b000500303400829000483c1c610f1041503056841c15100180c114000d03210031152031441e1104050 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 482515350 1250 482514100 482514103
    0x2040f0311031b1215151c02061c0902040c08190501030b0604050c1b101b170a1805061503030a08010e06010908030a030902032e02091809 61
    0x8040300e00c51030007030040640300028161a03418450500054400103203641c0c0860402d581000100c40b0f01d14140c542001ca800242000d190040e90300c0f019143d0008862601c50506800c461904469002c0315800e14a240c0c1c0062003034458001200301c40c8203641d030003055440c400e0300002a81d83d0700030300900c000591050001e0120008541c0701e440203c0007aa40c0120102500c03070281178a821200407001175507030800344000781c90084c2480f01300200030000130313a2803021000c3c50b4521103000b5000c0c0c580c82038011098001c0e1492186400405819124210b8010b90000c6840c14404441e4a5081541c1c0d11a56444010040308064654180e25800b0300c0c0c04012020a140380320f10510081020707041c0003401859074030700415000308007040c070311001440031200300e982c131a0780464149070090070726841d0441142990010120301011039142c1407200708506d003c1c03001d10b010554100c40c80f1802c1c0302c0b20008010302001124001441a40000d40320200d841349020a400c07603030440c079032001341e0a2100b10700c0d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 482516600 1250 482515350 482515379
    0xd0e0102211c0912031802090a0b01051207050316030c020a02040b04020d020f0c0f0105130f0f080a0201090b0a0b0a0603150b0c1f0504020a060e0d0b070e0901050d03050a1409040204 80
    0xc1300041c0c40c11180244540c020b050000e84d86030090601001d540c0c8052069001785844103250b818000300703228071482d0004084c4014481e030b00310703650b40392641000b07041003c00f2210704034002c0c241400c0907034910400b40c4c00101398000d0303a0100c5000c9910795040c000f0500900c281c20740341109a000213484840c40300c0540c024900315070f0120450704803c0014403450b0807514280d40708117031001800780c2080404d02a904103545180a0394050382c89484c2540c601e05035a00462a080150351142c41f00c00a201d402000e25030f0020320400140001401200094440d0b1498014041415516000703040a88131000204000c1d14040800382d80d1400f0140c0b0903517440840000d00c5070700058148100e022301885000c0d69028030350207840281c24500304a815191a5080500075030000070040305030020a080680351402480a0340fa00718402141c4c3c803d104180704140c002e40d01851502c0d03c25400a58428120703603c00e82c0030300d0000b41002100041c00614031400a0050b80701e0b0010401242c4a030303502c1da04 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 482517850 1250 482516600 482516633
    0x180a060305010f0c2006040b04062d0b0906131a0d2a0b0318010b0915030f0307020607080a09030804030507361a030307050d0e0102211c09 61
    0x2000c00e0002d6030481c40c2176820902400603540c2d000324002c00c0c00100c82010068110b4030400340131809080320309051503a091032200c003404c0c0c010745e40c042507205140b074890001a12000e58414030750f4640703840810b4501039150051488640d50302104001c901c6070002c2c4403160b22b0000c0c4240000505820040e0000202e4040d08501c0c8844140c040031460406c200d160443e41021503003400c0d07551700c0a211070036002c1c4000e0f0341c1c2195210490317841c041e504c11505520074000c0d140d2040e814413546c8140f41c6032040494108150b07a20070000c1d10096a658010b542c4c15070384c06184140c0d035052036402141d00c1945540010030a12001c6404020401c0115200c0c0540d25180d5032500f14800300c081c16000da111103480b0024042d000017007040b5000d00ca4012150100440d20729612000140700403902c0d607031084c5000c1d07a903070304000c0310002c0b0103500039003e000c200d50900c0100301c04da03526490b060008007060746652444800159014000e03012541c810031a41c02008200034580303603801e00880e010310078880e = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 482519100 1250 482517850 482517857
    0x1050a02070806010e0a14070e060a03020909180c0a08100903110d0503250f0c030522030203070801020a0504150207090509010509101a010302250c0e09070302180a060305010f0c 78
    0xc40000c41f040420a82d44540c50640c1d4910241c42d00a090013540da001c0c9030803008150f000c109040d0203403a000c1145004080c0310722281543c103910540142451603d840240c0f2866200600f002000030011f0909400c2418000010741e40d0320914080e202c00041e014690700c5802115a42e030002500800958850a801a0002440f072021054034000c0ca00d4035140c48003003040f07042c102c00107901c592260b030f41d072901c24141507203442408140e0a01c01c250741c104c403042c40641031400344218241400400c00400e070410089d410400d0094010b400c80c0a035006081c2e0b2802424001712000788200b041070000d10866500700301302c2c01c1209503079000c0c0c01c08540d514624812142103188010382840381c4985090a6181d111203021401e004502941c42500b4101d00b045064480c1c07407003455440b0301c50710618410180c84004626001c0a00c103002c000410f084540d40000d5030402c056110740e07030200c6000303802d0040d40c284c903a2030420840c010299034102921562a04803000d1030001c03d9480824101c0d8942c9 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 482520350 1250 482519100 482519111
    0x3040506010602010c140304150e010605040b03150105150f0a05030103030f0c0b370c080a0e07060e030f0105090d020708011e11041203020c040f09050c01050a02070806010e0a 77
    0x30784c20303582d140300300100144041c041d44142003140310186400520900018100340122000f050980d1810683c10f90580d54610342044145054401c0400c01c4c40c0c03d9029140852820200840ca110140b14581c000d029000700300042e00320708c0045400c0c001c0c40200d405e4403107095200081c45900240400c074040b80d07941040c0c480c901c2c080c1401c4560281e20108241165407004010741d000000b4020303090800c54109001c40c3c3d403101882c0340300b032131941d5030704c000488100050008050b0f40000c0c2c21203000c1440c014124003914070108000003500e5090400d2072200c104040468509010362021448552a000c240500c0c1240400d8290004c0303e2903003190551a180e023141422601e202c0c604010346c540070f0824100410090b00410850400f502d021802d01e555074032a041c4102c5d80210441c01078002c4c910800f03d9152602c40c0c40c816080c080ba0400421007260b5803545e5541c03411200e80c0c14840045200408540700700900b1001d0264201640c0d00e0f540c3d11070048810580569450311b5103401d00d03 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 482521600 1250 482520350 482520359
    0x61103071b030b07110607111905060709120302030f0a050d0207140105150604090b0a030c03060209040606051908040606080a110301050717010e0a090b0705031902030105010e21070303050304050601 87
    0x51742194041000b040142081c1e4440d060117403140b0002004004d8180180c50a40300150840d0140c4000e0500500242c4468688000e000308000e805030012036840760804c1e2071101003680002900c4803c500754080c0c1d6030703070b01010700103803114001c00e00489519400084d02008101c5543c40565a0b54802002800390340c40f810000622140120182070300040140420450b61100d50000c00714444054003102440340c0b0780c2c9449850140c0c641058588540008951b14141003610440c8020052403030300c1401c107032014503400c0314402c5040103901082200350215003484810b500c12002000c5010403141401e0181c81c040610144d18029123109500e0100041c00ca80d001d44038000c603046001c0040d460507800e02c0924500944041c1c100d4500d91764482a103c002000003041c01c0c01034006131905900c03894415460301207190b244203402d0b04280184010032451360004d40708808040b04584440307442d0240c5511400a114056600c5868401d8010020605401c0001140114001c00544003c2d03a2075 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 482522850 1250 482521600 482521607
    0x5060705090112020304060e0a0c030b010b13140a090204060c030905061206060c0a0f0b01050f0a350102071208160509041e1409010c020105010e01061103071b030b07 73
    0x280c1040310b010030121200a5203040141d4000d55000b4416400020f80c074030501c00f407a1600c038611804469100c001a01402407082e441405d5006000010446203400968000070213046240d01c104940991000712502c0d40b5628030310310401a010100c130840d150340da200300052449440c0c580c140d0116800100200712818944215009102803840c241d04980340c04040c0040c59018051140d03031402100080c40000d400c0092520b0301900880e003012541d4149010405c2c01e96000180a04c203422600d010040c9080f04420041d10014945542e00d41d44050000c65002d01d003000041c107181d52001440710100310400441040c40c2640d40c1c0d03512100e40d90688941902c0312400700c2c44010400500103a00d007841d00c5d030000d2200340383c4c5031490090341e058008150180c4042580308000c03192168200b0410003000d00ca05649100f0910003030041d54900440d28203034070740c1800740ca810480e0040d54240c0c00e03101041200c0b41e0a0b8072200e88500c111000b256917900030359a01040394020081004038084610 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 482524100 1250 482522850 482522857
    0x80414030703210215010b0a0807030c0806120307081c0e0718020d060503011503030f0c0f021002030f0309030307120603110d05010b0409080d060f060f030c0201060f060c05060705 79
    0x240081d40151808070f90035448601240315000008504c2000031880300350710351091440c020030300c605489440d4550800d000c0c0860000407d10704c1094906080200c500d81e21038240f0313820050540f103000d6000b290030f0056086125120002d0700240c00020301c54011010900340c0c9400c00c410500400c295810b181c00b180d16900e4510036650f050403040301603a4034119503801002c002e03040900c0015180d03640c0c004282910052000c034411a908600d0800a154000750080400c0d15030707160a165100599448810078000030030064001c40c641050050268000c000700d92000c1a13044425403680f421140540d9250b00848100000505607040c012100f4aa4051f1a040d26840b28ae003440541d00795084c014a151000d42c00c3c1c90940d2500c094645503181c6100cbc40d102c80740100d0b0b125580e42c100a0041007a150140d00c940f40d1000e84603401c0141ca64042c40b00f218000e40380c940418281e50f4004100d01600c01608140d013400d00e006000580036070084c0001800360b12443c00d40342203542c0c4880c103a50601 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 482525350 1250 482524100 482524103
    0x30521010515120403181505030906180a031214040f050706090b0405040905250306050105060a020601050d050109020301051810061a09030a060507030203041403030103170702040b0d080414030703 86
    0x80f103560200700042c1c06030045804907100040d400701c0b07990b92030ba00e907881c064409a102d808900c0010030302c10360b22014071400e03500154038035902c0b000e000c9070156a580d81c815400050100042051500071030385040e04400401c8503240030021440c103050900003008200c510b000c480f00d00c24a540010340c54040c04c510800c83d040e60301410f060901d40014000039143c000c500701c0709401202c0d40c510090017410969988007281da43c80c0c0000c2030540c030b0a901100c0c03040e04194403511040c070103000c2040e8001100c90550750282e8060056083c5031078446d0251003071140080d8194203203c03c11051702c0782d0701c00780103064203540102c6a4100c0b40e60019002c440300c60040942d220034803205081c0c184000c100a180c2d0100140c220350100c1955103660301110f0040e078403000040d800000f44811310061420003042c03100c418025501e1945141d0340e03c194620003e0400300b0900d00407070902d056680c1da910000c84028050070104042c4030500d455505503000d4020328042c3d4642104544190800080311020f0b81e = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 482526600 1250 482525350 482525377
    0x15070e01020a0b130210030608010e0111072402030a0f05061009050123160c0509010609030b060d0f240b0d02062b02090a090c050313030521010515 65
    0x1c00342030b03e0301d007181c10f0024440d010f0040e00c0c19880b0016282d007074502040d1120765900041080c01c00001074252030228403007501d0341c0c1c10010304101c0011050221019680e100b03184017186401111040c00c440100003007546c450f4804802c01481d80e40c55044204101ca0110b0700304040e0b03403102c0802c10b02d0070b80300c1003407070000c0d03501c100030321541d40901504c0300201000300303a015286482c440c00104592012800540b9503040121304420050390403950030203804115480503080d030618200a05001061101070315003410940413070b24984406c00c508400f01d4029070042550940307030a0175100d1203000305540b01c2564030004458402880b40c45058503a0000800c07060385154140c003040321603007128040081650b00c0d40f2001c80e0140d4542d041d54001c0c6d40301e074009600c1c0c40100e410880c04c809a41d000c040740c1c60411400598042e40502200d5201411440d85540c2d02e6240c02d0481e558021482800154420520100413101c841c0540c0c5048480490f031984069540501c4002c0600030140303600000d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 482527850 1250 482526600 482526613
    0x80c070f031e020703170304080a1b06060e150a0612020708040e0f0412050a08220c0f0906050409050a2603070f02060604090c05010c030c020604030515070e0102 71
    0x80c0300030a5030352594040d1a084914000310b0122801c21241210741d800580d0142ca010400c0000c0920665000c00701ca501260071440d19880300002485040c440c80c04201713801c0701d84079245040b030002305003154022000b006000d8651910860068003901c2000080465424001051600760466429501c15039074605030624010094800f1f90401c540466400f1401e00c000309000c4c806440b4948552078039041c8103a903041a040c84818003150003440c07400c00200700640301480790040c1c990b03900718480060b0441049076003071201071412200d240040290790400c20000d4a040c0444070001a40c0c040901080340c9584c0744200000c496090320003c4c12604044201c1010032000c100c054510b880c200c514401e45c1800c1c2d0305400c000e61048400401155008103a804515030402510ba445172055034104034000e981d40319140100140c0c42050704005004045030201881500340810381a809000b00b904d45841e4174140b512040c0e070742e03500038281c014480060b2035240b0911a03c6040d00d010380240c20b1 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 482529100 1250 482527850 482527853
    0xc0402090f0d0c265b0c0f020312040b0402190b0301090b041401090213090c051803011a13060b040305070e0c1206040f0209031e061602031b120f120106080c07 70
    0x10840100c902d821407401c1551010920301e03405040c014000035110305c0000d00901d1211002d0500d410b42980c041c1154024010305090402c001e444070741040e000606003846a55620001d80344040305ca0f0355440500031244001554041e18010b541170315034401d0140007205403042404215114444290980740318880100801e00b560307402006100305407151020459210300c501c1c030a0390b40c41c0d84e56000090000401840000002c0002d450590b0110f0003404001c1061a01a542c0300e22000410720404400010020740d64032a0710120041c0418403005403556030b01d082c12500d0380340b03521501c031260205400060040001800312135150f00c900e00d0a81041d00d481c0c0a0100818250701131240341542081410740594082010082d02483d50704800382204c008400c6c18100b8001608850b4038000824840f1b060f00d4010055a04a000c0f00005220242c40d59010300d10b81002e07041407045014000626610301e118a10040422200103d00c9a10030b0b42d0300d002c21114071608481c8402c00f09810b109050 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 482530350 1250 482529100 482529193
    0x105101703090f0a050603100504050c03010e0403030e160602100606050306010c20130b04062304021e040303090305120403120e030a08040b07050c0402090f0d0c26 72
    0x103c00700162140140c1c03500c420202e2101e40c0141d50504070b1000f40d490800a6243c84d0050b261321400f00200c10342154076284ea10801c681018000030140340e00d541c5907080214040040c0c0301d010840d084091031240d95048045d45680710000400c804906040c1301042403402031040764051401a5511a4008643d46a04031000c03001c15107808408859442c150032030340c0e4881c509000106010700001c001041c10200401c40d0100d0b80701000381c15100d01d04241c4003401600d84009114142c90150f0b0700e107841036107141e0040b00491801f900e00300c003044c084141640206d40d02c0a8901c1401240d02c400c80120b400c038058021440002d00050041041a0300c01e80700304030189003648c0250481d0b2400c2540e40d2601c1d4141c004d40c1040c8030f00c480210301138007404810001e50b09000001d030b4045143c044090f0120342100140c020030390250780c0300066441009100041c3c6002002c00700f00386000120040c0d041034400030f41544d40d41091040c130145c0c10301c2c14100b41c200c400b51105000c3c20034100408940d2031 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 482531600 1250 482530350 482530369
    0xa031202010609111b0a050322030f1211120f07110301110c21190c05150103030e010806030a060b04020d181209030b0f040f021002010510170309 64
    0x4554031800001100c00840c004c2d48500740310001140d03255001080b41036142c0c1c8528004c0d0b51940d000c1e9100d680464404011915800032422180c000388801d15650030210103d58030083c03007c014400b062081c00318090300c03411003c04a68403122402d0643e1a40b40e80c40725800319140c1454420401203816840c04401800f40c2d82c454400c07819140d10070030000e421580d03182606203000c503000901d003039000014446d480103001072041400400082075000d200b540136100295140641c0303050060002130140f41105201d50784602112240d0b444840308864543c4280b208030003040c6545951340d842e42c003601041e8861400030713000b0820707100342c1c0e00c4010141500d02c11094001d0760070401e0b010000303110300840f00700904d000e0030984401101e141c0f659043e1001d60a6100b0040301032414000200c001100d1074202c0741180280322251101d0a10151500036404000d611040402e03188014580641010b4030403555003003281801c658803008101060140d07080100320790410440000c0b28030303004201 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 482532850 1250 482531600 482531633
    0xf0b04140a0801090b07030c0f0504150207030b01060e100302090108040312060f0602030711010c02010f1416060b012307030c05030f041e0f03020a0504091a0109021b07050a03 77
    0x816000030b5031407510034211411284180c03101c0d00d02500b040034003034250050180c0c000403460030b000d601c3d002d61001050f50085008801d0142c020f1110084454820003105001c0d40c1c000040e070046594540c40075040d100c1d080d8026004151011103c01554004d109031555040180c4034840c01d40d485641c1281c54840390b107104004240e4074003000c1800d1170080554005061180c0042d541c030402401c00d40c5001e1290401c036810402522695401030340e000100d4000d629142c1440c8044c02e50074802d082a42c0035100513180040b0f1900c02140500046801941c20800282c880c4502c9070301c01000c0001301c00b03502408441c4440208403640001c2d2265544111190165050742e041100ca240d50f090107030301c65804a090411010311010300515554514030052003c1c8420245947c555401709034003520910403580b03d42e5540724998240081d00350040050303412026081c507103607124020000290007020030300104c1c1090b07048040085000050b4181501c10061000d18286c0c0385580c1c103031160800c03450 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 482534100 1250 482532850 482532859
    0x706200403021c141509060c0415051603030f15050901142808120304021e03030c01141e0606040b1e180108060d030905041a0a1e0f0b0414 61
    0xc0d540045050306841d02e401030100d802070422481d00300e000350249800604140f506400103401d001c58000d010003227038115011107a0100b0b2400004100b9911400350285200105028980440426625501151507044c1c3c0460411803a246041141c0301d41d0400c2c05455040f80e1440c0040c48076079480e200b6151468001001c00d810300c20342004000003109800d61021318400c0200341806440014030683c1440c5c5e00c5010324906500d0141c0005041c1c403401024405d143d4850038800c00f40780c60900c212500c0b003c0200c020310082083c07503c3c904160404454946a8140ca410b14070b1178424080c800c1340c05203000404650416003020911348070350b802000041100d070700440c910240c8109510107070081c040020b1071000701d48da21600150029200030000e6105424800007500020341100c0d02c0001c0e200d05035800503840107542040260401c0400301158818100b05001400d045e905e0100c00344a0444020451b01c40d80c0c60900c03407103200c2d131070242d503030906400c0c0400d20210b40d01281030840c400000f003 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 482535350 1250 482534100 482534149
    0xf0f040618061103010905090316030e0d1e0b01050a0308040302091e0907140d05150405391507080a0c1523150d02030a0503030903070620040302 64
    0x50380d290464240306a503c11518000c4010803420b906485a145e1217640740016600d4800541c04881c6000c00d1200c00500348200303243c8070669601ca9120100c075465000c2c2c082c420440c1820241c044144014204a0300580c070f5100208031800d0a040c0e610469a01220791400c140c1590f08105030301134000d141d0044081c1e4001d01e5078810303007140e00c210700a0350300f00e024003a218280060507486101d04481d050140d0001c0d514000000c500150302c0c4c8200001c0000502a42c68074604541401c03800000340404051035280440e96640c0422555011a10580038250040d401414003900080303400280510240c280701c040c2c0410319450040c00c01d045540b6000203c0041a070365480c155142252034210281d95942c0120700b11841902c2040400041380f4401c44d600d000d035101c2d4104e03661030b00024015100c0440100454408111070b100c0598070805491301ca18151b41c0107a034a4020310410b42d04c0d40c3c1020100740b0b03500320184030003c0c0222030b010810301d818115024001d5a1020b41c050400e00030064 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 482536600 1250 482535350 482535353
    0x210b04060612110a090b03100302030f010606020613081210050d080406020118052e0903030504020a0f060212030c28110c09041101050415170f0f040618 67
    0x52092501070301e0940c4414900804264070034048860071225802c0a250402508045a0b04002101d00311881c5034281a41c0e40d889030005607040207194002501840f070807110902613901904204d05030b40540c0d088809070368500040790780c14142c41f100a00107000800a9003088071040309480d602001810480d0240759072000820300e0120020000d4854800111301030006950a0150440c90346990702d0003104088140c45043c0c40e890107140c00d40090b441d840020741070141a032811040982d440c08104681078007410050041c10084500701e12a05050b00d01240c032000a206400c26144c8984c0101556603030468001a242d01c080c10360600c80ba010300c000307901c40825203011803c01d02400024205201d0502c80542400c00302c07140c0400b90f8100c200007082030340310610b280707902507040482040d001079000d00684051185812045021058001c1c1701000c40c0c01030fa80380e49010403229140241c0e41c46000f0080c03422010b58040302140f910402040c04940103030414680240041c0304803a0501c248d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 482537850 1250 482536600 482536609
    0x60308070219080d05280e190b1204030f110d030c0c020910081605010c060902061306030b03060703020c0606130623040e0708030406030e10020c03190e01210b 70
    0x4455040000850000d4413245640c6139050200c4000c00c060084002c20040c1440548002961400e8a0148c002c00191072001501101c001c001428104ca6140e41e0303081842d00d41c1d4120500300c4042c3d01003222003401201144c0300c1e850596400d025480901455070380d5078002c9000d40550825002000014070f10701d0056a40c00300c105015801030302107841c1036407411480b1810900f035040c1d0000351001c8080c0030070490340c1240e01d40400075072204000900000b030f44001a041d02170303030728028402040d900380402c1c825090750020348203100032000c881c040d60380c0c1103044082e4480e4000b00b0345039411541c08100c036400c005800071450110740c2d8002c100d968171580b0085014902091242c030042212040760500e081602c50203601c0140c4102a0218500303011406550744070710301c206000c240e945c12210201c5c00f014030140502d1a03007801d040d5611002141100c0d941e4001c444d52082200343c420459249a0150714001101c00041c0c54000c0110740c285616861a032542400c40c0020340c540d904038055668 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 482539100 1250 482537850 482537863
    0x80f040b070c02180a0c0f0507110303040308130929010e130e01150b0301060509100c05070b030103110907091206060503060c130608061c080c15061306030807021908 73
    0x4c90a807a0080341c94010f000b80c056803007a1108009000030a600f10f1802a40641121015504010040c00f00751540340440c1c0786100740d500c098800320012842e0341510900d26a6481216020b40091241c206011081c800d0080490242d014903030740d07810303900c1c0c40d9402580568807a14004051040040c1c004049005403041001d5004080c0d548007a850100300d01d007100d074000760010a151a09541c10210301425030301c5400301c1540b082404541d508030b43c61040201030800c83e400300942c0c00d402e588480c041200d401c0be001c1101c0407180e60303182c030a10781403210206210710015940c0340041440c1940131480340c1c01d107440036601991200d00116070b0b03440030003c0c140512042e2084a60ba803010200312085258590042c8041189084c10712105580e1a1400c092240c200c641e603e04804941c40c140d0b26a12400c00314443c1406a10782d4501c919219803c103502c82c0500340d9010400c1d080b4620200101c40890000511030328050225001500300301d4014000001601d0f82905a540c58100381443c100 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 482540350 1250 482539100 482539129
    0x1030216060501150e030a02012a110901080a020d060b0411040e0103230a080313050d02060405010b01030e12180a240c051c050418060e07080f040b070c02 68
    0x40e10b4000400500c9a402d038203032801065440d01c4006045400006901c1f48290784000c3d0400480c180406070340e81c4800e282c4254407114000c0c91b00c803800c6038984125039000108500388180c90300d0000284408022512100d071650040040110552513651000180300c07000400760040e6031140c04c217200400540041028140c0510104099851481c0c0528801c08141d40c42d00101001e5060020041300080d80b4030b9660760201810341c8958035102d80681c001500320300942240300d00c045010705960007040c1d8a00a600078002071040c12030920064044e1203d1b22002d0096500164500d03500c071a10002406c217002c641d41c1e00890031505e40000840004458005041400081c0b40211000340c1d04043c60b14013001030b050400182c1540d8403100d45542d144040000860b000c00410000f4a2040040310003826024140704002c1c660311440e00003c082c14020b030140122000e001c00d5020703000d100708500c0381d00741c010780522a03030f030701c0d40d8507070b00d00d00d02828420074403c5104048006a40f10181041e149 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 482541600 1250 482540350 482540363
    0xe0607060501090606030e030706020703020c0603160206100f05121c081915050d031e0203120903030108070303050a02030c1e011a090a020a111e0d031a090601030216 73
    0x1035042503042000c64940c0d17030000c003c0c1840d101d0419400320b000300c02e030798940350004801a00d4510030704041c1e042940e601813095210310000104442c0d0f500300380c0e0b140c01001a99003145c1282d0307100046003c80890900407501c80c06e2025408100c189400a031201c120300241007980c2000c003500d01c03030700024241c28801c0404900303071004104880c82220510141088000c5040c80766084000c0c2d00c00072012a402480d001e1b103024203016040c1405411460b103040420208101092070b4410003d40b01e03004130b450a826808030a004c111407000001c01e803410303544d070000905074052441c0e4040d544c583c420298030044d800144200103a004081c424011a4201081c240181d94040c84003a8216400000d00147c000f0b90406541401c5c3c45154500758441e4440d02d005940d28002c0809840e1003003615104c07a4244200c0ca20301c043c1c440b082c1440c1c28000040310450340c81d40214031341034064800009007070082c00800300880c0081d10b00702d4030b40c0750000e006040052400c990150b20009841c82801d099405 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 482542850 1250 482541600 482541611
    0x6020415080901140606160b07091e032024040f0b0c06040803090f1c02010b090f04023d120605150c072d0b040e160e060706 55
    0x1036074200c1036007a800051980201300000d0130039203080d00c991015105030300640d00450500768801000d006040c0e03054005c00b140f202da1030302000c0100f001003180200c510041c0401600140d8034249400f085c04e40703500c540000c2c600040c10010a00d8001600e90b0f00343e00500c1f80c0e146100d0014451400c00c0c944e1007914072103560350b05261410081840303d0b40600441081000010f04107200400d150f60040d40c0b00d40745a0303983d00ca54001e1440c207003001d0070750300d803d005040000409035140c01542c409200a500284205003481d400c0101025013100c0382114082c1d0240094014135084e00700c0c2c3c0070f2021034081c46840102101c2c030783d81034072a00d401d03001586844c035400040e15500700d101d0300c1c090148544203211140c10400414070000d400928000c00300008551014201c0c81030200a0290020310340c035030181604c0340350500c100701000d00c2558a0031006240410360f000020b040f2010b1f111070680140040d11103416002c018420151000200722100403198026551940100143d6005003000304d203 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 482544100 1250 482542850 482542889
    0x902060d0e0d080c0a03051801020f040906050609010215070c12080702010e0721170f0706050609160804050a140321160c0c0b040b03010806070f0e0f030a060204 71
    0x540280303424048140404182001902c05200c000c5440e040c030305e4540401c09841d01c10449450303881d004184483c0b540080f40d40d41008204a010308115008500e00b4002c0750740d500c042c00f84a1041d1003c0b01d0050700701041c7e00d050b5400e02200c82d50401d0701da02d00303008502002c1c0c41d1002400340002ea0f0714000b8140c01c0c02c1c031001e5582401039070034003501e400280803080e140101e024000410543c0c10600a10141c200005018070201c04a010b41144012196550340c01c1e58180c40c0c903486443c0c1190242d140c200402c1301428070f10f640700d1041c51010404615903021000c00c2e01c0210004108a03954440c002c004000150000743c0845151003030402191510b0b00315400c4c0000c031150000d0000c1010b0302c2c60410140c60442c22114007a0034840c20302d40d1a039421418007c401c283c03c0c1e004503c4082002800107203041d24500194100ca20b4481910342c191107412044408100c1c1e00d4010b0009513880c9101e5481e440d002000e42d48800c0c00074110760b1030399070560f14001642c006030302800300240d041158030b0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 482545350 1250 482544100 482544103
    0xa1e0302060f0a110607020c1203040b0f031611060705070f061409240103060527030a0f0c02091603090f08070b090d080a0c0306051f0207060c020918010902060d0e 72
    0x5012000132000381c00c2c07910702224005d40d5003580901c2644100c0c209501c0b040451001d004844c090558800d58035940c1807890084a10340e4030959090035903104c00c0b0342000b04180300e48195507400076401d003c0e040030380f42c02c0300880b450f403c0500e0030b9910200000b034100000e900c61168100d500f101654628892511100140c1042c140300004100009020314544e4030100f000003050550768440000201a15030014070300500071030a00e464407442454408010702800000074000b0b40580340d070b45c150143e240c11401c80d640c004801c402034001e4006808111241c44101b01400e2141c000d160000d0508440e4031500610b554280c800c1d1100074000600750240100b0503140e9601c000414010005845514001000c0c0140105002800c5990384100e00d0711a02c640c0040b802444014010300314045851a40c2c0d603c40442c3c410600584240240000d50702c5c0601e01c0c500199800030400c06c01c030741c0d60301814220203052140d0003915560300c0381d070180103a650340017030082d1500c80c000c00580f4044048016 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 482546600 1250 482545350 482545367
    0x60a0506061309050a1b05091306050f010c03020c06070b0105040f0e0d0806030703170d060e01051e0f0a081f0b130b0d020306011502070b090a1e0302060f0a 69
    0x6000e107000704510110b1a407042d41c044116038030002c0010f92580c910b60804010840803a4001175007145606162030268440c014289018084400708009950120a40100c80c481e01c05c440d0001d1000c4050707030080d802102401841c50085c01655910010707a00021003e50041c20206c9181019500620040c00c0c80d200303249158400d410104589040342c00720a071390782c4205181c0360070054014000f48080d2410700c2018029540440d0800511015a40c1d60701c4030f404c1170100c81c1040303151000c0001c4070072803002424100c52001e41700819483c00c20700d64050800d20041e00a42159a41d04820403940310704404800401500c00603110158850315000d071040c621244003000e040c10404107074240e64072001c5d162079401201d10005032122000011404e101c010080195041c00342c2d2000046100a40d02440902e10750b690a0b10704054503014038110310700541d5003c94201460000030310031200742221401b285a100c40603188010f07034030f034009062076210341342104951401040360842c4a4110303054 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 482547850 1250 482546600 482546611
    0x11e091409040c0509041e0305270f060d0e060106110d0c03080c0304031e02010b0a0803120f09030c01020a0302040f090e0a11120604060e2a04110417060a05 69
    0x14103818286615456000c110f01d0044600c00e644181c04241000265405030001906000c0700ca02c6c800020b08010304950428003030854041c08240000c00c01921144d5480c0032404010075111010340d02c601406220b400900c00154030a90304c4105c01c071010000c2046500904c885c1d80d41d00741882103400307800d00b08000c0740040000e004141c501d5400103a00030304025403094401ca80140c03a50703910300741200c000200610180412400c02e0f18110500d9046d004450a801c1c01c0d60780c21040c0342c0d100d885a81d01c0c0f04201d6501e4000c0e04e605c0c040340b1660450004103030000940011a402d158441340c0050032a0b00c602015400b00342d001030104003000c026004000203140840d0200224811223900d5922903021030710040447d61a00108803e40d603448060785e6001d01c14000700d40c2c0ea0320301458084020100209009110300c100e40c0300300000d030034860303018480d0041c224031000850100c0f000c0c0000f03030403c0308092118020511002c180461103034064100701c2e0010004100c00c0c28020014822140040c24 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 482549100 1250 482547850 482547859
    0x9050903030105150c0c01030903030b06070f0c080304050112020a020703020a0b071704083c010510090902011d010c0b0406021306050903030703050d06050910140f1e011e0914 77
    0x30a440405c000309106000e80f1007030070049081c13403103841e044005107842404107900200105003038041c0000c282034142424840d60300200c40944991000ba42e80c021441014006081ca03070220050101e190003600c002522030040350001c40e02c80d80083e0712444150170181c140c0c40045030520a102e800c2d500249100d03c041c041c00e25060800c01c045403a12054090403074800e462111002c0444501c0000081c80348241000b51002115021028081c000c1a1440d141c20340c980c1d007001c01c0b58662403103221120340d03058507541000c4800c14040b031104603810309080d05011102036010f0106403a91882c5120300d01c9803100603070b40c15540070f10041141d06600903000308101440007081e41c0d28008211202e458145c10703c3c2d42c0b10b0084d605c0d4003005e4101c80c0c03c216007250906041c000d402500c000e29000f5255811410b803039540c00e0318140b02d1540000071103240d10030004080031a014042d610071031940001032500551104003074025801714201800d182c0c2c0040c80f110030400c07421410300704112690000f190b = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 482550350 1250 482549100 482549107
    0x61e09050108010b03092d010615094406070918020d020904380907050901020c0406030c0609060203040321110609010902130903081f0905090303010515 67
    0xc000800d2074405004440402d0400008101005020040c4e0340504189019140e08002201c0c000301c00c04201050315001d81d800c10350f001c550000741050030b4043c1510b42d6640c4848a2510300819009000800050100c82e80c3c1c085501e603005900000002c11440c01c54040c1d004c0c90002c40107442d01030000c03d1913042007201e00d024082400042040c4224044001c03016842d0b8030382840c04802445400340c4194402d213812103800c0708020000c04d0f84051304155210b0070303140c0c02e46a50310800e1b07128500350541c00802640010300140c060130280c02520410b2040b6540301c0e01c810041402c480060f04166400b000048081240660110019010304041d00c0518145840c543e07404044850b489140640b20f00c0c40006401e10038490541000c00c070030100111401401c020354918003c19200c0002c3c1c0c0103140d44601602201c40c94010018081c2e0716590340e01d603964803116046e030b00e400c503004184012605030703200240210f502e0260078024100c0b81b01455503035161000704415110410385e0b9062032403092 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 482551600 1250 482550350 482550359
    0x80601091b0e030a4701081f020d090b10210302070302090612030a0924020d0f050c030703080105091e07050c011d010504060606020f0304030f08090a061e09 69
    0x2c100b002e640355001c0141d145c0b00010380449440d00c416201140b01c01301004c004010100c05282d100c5042c84005072003805a41d8a035161140c58400d48074204c2c4001c0c001c03000c1d0f0941d102159004200c44100881c001400c241c85554440b4024406d5540320f114480c040428130031820880b00300300000d6005800c0c2c0880900540e4003940f2a4400d2002a104100700f40008001d61076100d82640803243e000c0544c0d50384c4103c404060034818190003494201a000c002c030f81e030020b196452841c0f002d02550002e05900f00b656404443d100d40c080102800c11005000c0546036a0042000e00320715840713929249003a6040c001403184c1c02000070040f10b0a02c0711000800f040141d010700d016008562403900a640d001ca004103140900740c07150b1a196001c810096224048006502990099100d410203002483e50b820741203030788030081d03500c070071194004100400014188510590109118000640c2811050b800161481d80140e101d0b40c04200c1c50107444003140c80006d025200300a080c1881da58450a0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 482552850 1250 482551600 482551603
    0x703020d1415040b0d0816030f05040e16120c0e0112020405060909070e0303040e180607080a02070c08070906030b1b0403020f121b0111061519080601091b0e03 70
    0x44200482c0901c0d07890840001390345a982c0c02070803a6400a908540d02c200d910396020303d0021a82c41540016080402e1100c040c0c45030080303508031034240c080d5034401e4a840101d075a1842c00b50f825a4240800080b608868000754007460019011640b1129910740d8000d00142903200d224001003040d0f407041005008031350303e078030a442002809030750001e00e0790789400c01604c080b001810269807522000c180000c0c0c3c856840032151181c0c0884180d03d04400d010150142d0b1000261400400b007607120b000158421120b5000d4400580030341d94200e41c0741d41d40c6201a0501106811588809844200c1442840380014407141c200c085a03001c01c1103021103403d507171220300590100a05c01c03008410148455514110302c450040424025104a8030000701741c031081c1c07404200301c2070104000801407000c1c03000104d0098401c0e81105051546c54003200200481a560381d4000c000c042c00b18600031840700e900b00314240c0605884040050300b9120ba04406002003c201408001c00c2900300000c140c07501c0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 482553956 1106 482552850 482552881
    0xf03050604060c02150424060f0501020105090319031d03210604091e03110312060415050f0d140a030e10030b010f0804030e090703020d14 61
    0x2c50010990700c03900d050078480d50b0b503221800040c0206c0c150301c008051b01042c00d9210007c2c4c02c1c00f44101022074009400c408444040c82505108958091245a4008601e04001d60512041d45100640008490304180c10141c448921800e10406c0d0304c0104a00080001503030381b180039034000c0b551b5072441a003d4910044500c1d003c100c650070b040c070440500d190031403a06105004114106490300c000ea8a0480800034030b241c0034084044188094032200c42800845041b5040032820001520808082c1c07100140d03902d481041135a403031400a50b07080500340c4a0a000c03000e01d08204e1030781c0c0e29545244076940600c0718001d00301540302d04c1340254540b040ba6040307050300c0350440403011a0034803001240401c025500d5000f070a4010000300e42e00c240700b0f2030000c200d21075020100d1010308040e105032001c650040390f200302e490118001c0e00341c01105104010b00314900b900b4003055503007 = true := by decide +kernel

theorem cover : BRFrame.Cov 482374100 482553956 := by
  have h0 := BRFrame.cov_init 482374100
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482374100 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 482374100 ≤ n) (h2 : n < 482553956) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
