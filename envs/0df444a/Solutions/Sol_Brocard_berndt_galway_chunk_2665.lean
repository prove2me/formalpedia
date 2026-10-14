-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2665
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:22:56.436525+00:00
-- url     : https://prove2.me/submissions/eba7a272-3c35-49d6-914d-49bc9390f165

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 479136690 ≤ n < 479316546 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 479137940 1250 479136690 479136703
    0x30c030a0503070207080d0804060207050c040f06051810030803060619030605120303060117060a030f050a0203071a030105010f12090f031e0806040207140a06050f130b061908 77
    0x211581c0391a81c0f850032032002402e000c4a50001c0c00180c015005e040c02a41d88004011741098020400590b9205140b4006140260212005030000d00700301c0c8041d4280c0c0d45600c010222042921001e201024405402244000c00c07680311684110210702400440d050b070018540c01a409041a86440c2c41400c0b04114621034001400000e6100c1000740300d1400c0c615011064006014021811414a0350018290094441c800d60144c507540c800281c0d10341d03070415558015030f0010b240e100011828104551101e030a6a4142d01074856150f00241c034005440c081090581940fa45074250390a0400464405142c07001c500e040080554079a07980c11030300e201d01404184204005540c0000614020748030080400490368508000c00c0c5450032181c001d17242c00e0b444a000c03100181d43d4903040c035100440c0d2241900c29002e51280122140c2008031a5010354081d480240140b40d09903a00c401101400006100007032a1440c45000f103440303401c0440c038540519a01c095a0601d0a40382d5004034501038 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 479139190 1250 479137940 479137957
    0x121803060f0b0628080105010c06050402010e10020f01060501080907030b1003080d020703030f0203071d033309010921030f1b12021306081806010609060e030c1c05030c03 75
    0x600742646203081800d000071080e04d0280d941000c0c2d0a544c07502c00040c001506c4000c003d0009510f4000050071a8890740e45400481002000007909003482e0300e000b941e541115298660035807800e4008030f990340c043c4542610525442d0000c001141c2141e03140740d181c0307601902100945403146400320015200f41c01900300c1c44d070103450068072010241002001e40300d4601d9605c0c1c40e81d104100344110588d004805e420f45c40071050440c0140300136200842c2c5480e25405085a011400c01107410712070039550f0305ca1500200c0c0e04030079056038807020328141c202d48840c1e6008181d507400040000b5a02c50f080c5c8280d00056a44c2000160300c2600b40f146015254004807074010362444040054a00e078025080d6441080b0300e160442c10001e182005ca00c42d410303140500820b02002c5c0f00040c1c03101c0079118030030b034200035640d0a0b21071550f03680700090114500740c05441c0c0800c40850030410681800603149111039001095885115035002c4103511404200d502614603010400441ba0003400800041c44900d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 479140440 1250 479139190 479139217
    0x301052206060e090601080f22050303091c0206010b0316180801020901090914040807080706060305010b120f150a0e030c03030411090c0906181804121803060f0b06 72
    0x21141c03d04015081000410741410b02c03005905004d10030410020740d980c00003079010704056220060f1042081001c05d40d40040c414800042005261100880d0b503140000c2030300c1d151500c80c502000c0683e2179910034040e520342010f0a00005121070320142401006440b10b06101e0040003a203100302101500c55000703514581c0d000240b901c0203583c042c9440009140c035150400c80d000000700308082103036002c0c0000e404560080356a4080c00361201c101c0714000d6218800304499030b82d23841c11a01a105410b11240b113051400000896894007140300c8003840050406040b1134030301900740d103c8802001d06082940c5650704020082c0c074000308028a00019000001d58482c6014506110781c80015103906000728030170001d01c00c070b4500c50f0082e1454440100c84003600c82040056903124441501c400c660310140c1d46800340843e20744081c44a000d00e009500b58000c04290090544043c1e0480f24824041282d0000810100c1c42d690700141030126640d10107d264040d2400050a9030031104050419 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 479141690 1250 479140440 479140457
    0x1030309050f15210907030b01120b0f1522110703080c0906070605010303030b1e0a0e04080f03240f220e010e010e06090105040206030105220606 64
    0x14140c2100300a0010034080300c20001001400011510116079040985082000802c80150713203d204040b200701c007412800906902d1610301403065035210588015251070164a0000c20360848250b041a5a1500030704445070545529004442d20640102600090545040710f004242c1d80e081c05003800807264074425582c442d5a20207001220703075940d40f8485160003004402c0009401c498055408030034039160079111044c80d004140c03a4400c10350700510403860708001208142d0564070105240f10242c0e664003040300c0b60501082c9820b804c0c21080d50004186078200042032580c070a2070350040c4541d440c2410800790040002c03460f0000c0d101002e0a81c007451840c1c034103000100480ca1119821a002c0401d210600045104038030300701c0c00b207503400c001031203941c030700b19801d800001404046030300801540902c80f40d118000e000321000000c150280740081019280e0500a0328040c0740c00600303d6255910300800c0144410204060300d038417180d0905400d40300c1859104400080007103448000c1e1 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 479142940 1250 479141690 479141693
    0x1803120c0d1e0f0f0e03030a0302030103061d030d09021219020907020a0b06060705011805030d0f15060804020118060819020307020a1101050c0102041d060a03030f0f140a03050103 79
    0x564080034034001246400b07098118440e81c0008840300a00c0300b03040c8644850104001210900d4041061580500c40060580402949a4015412203000700704c10004000401003001d203051042268001030743c000d101c0b45095032415400081ca040c0300810f030f8899a0302c4070f280282028035012403248007195801c150820750621801e51540070205201405c0b400340d180c1c4e030b14032889001501040c0100804601801040000d600000568100240c40c81c40180d417407910313690760b07030046034051101c5050000c0c581d84a440c5010340a241ca0080559412450602e61700326005803006100340d042000060307d041e00420084096005468075641e10700541c54070800d21010b0410020b03070360301c8070b0b4130400804c10059400b10f0041d03d00c560280403101c24414441c01210140140e078045c1049502c0014001110707183c1810600c0741480c0290b410b1706607542c1904000f5420036501c40079000c81e41e80c2c40440c030329600c258400b448880840c01c10f4042003440c41334120b41d50f0000c40301c080109a40380014030 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 479144190 1250 479142940 479142947
    0x60307092d1d0406110d020d1e0905061f050907020c01180617100906090902030d0c051b0a0b180f0a051c2a17030f1803120c0d 56
    0x50103070036006030340b002154815000d03184260004002521056440032030209060240f4122500c04168000c00c3d504c4e14441c0782480c0041040d01800003e406000e204042d40c80400d00403032801a030440c000c6d0070076a48800580c84a6840300306d030790001c101c1510000c40c4660b11030f82464003e00540e40105a9180d0400c0094900c00504015200082c01a00f0401c0103640c01251155410a100390308901ca460310140b040d0400b4217500140b80850501a002c22000b655070300040607903000302c041321444600c0f0030040d1101100c03240e0103016900f08807518054400102080700042d40d015000103071036a034032584404207030000d200c4103c0c18100007029400c5440d1041c00707160003050481d624080c0c58900400200710040300c0020500e11b502103800fa50034030032400345021240b650f0441d03409000001c3e01020b8481440c07802030880ca6020304c2c1c1000c4601000000f558070303889200e40c1251510107000b121102c5c8404e8260419411300c0382ea12000d940340407210103050303000c843d0402800044d2041e103018 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 479145440 1250 479144190 479144279
    0xb0a0c0c080403030c0302161719050c0603130203010f0f0f0c0503070c020102100e150c0f09041e090606050f01080f15030a0c080714030a0201020c06030709 69
    0x118100200d4544035408a10110115800c481e07060419a4000b502e41c030b03041e401c5c0b5203000c044040714101420001280340000301e0072003000c03189000780c030f80c42d25103945103111a1800140c05441c070707842580c0803034060414000454001c202100d84c4800c120030f55001a0030340c4c480c00c11001c446500da191405227400d00340913031000f482103000280003a540d04e901c020141c1c00010704c0d031801c00211039511401d5900a1020318108408280c080c01041d01000c01c00d9902d0b2806024003150b000c1c80741c0000d004011020540311303014440195203181600943c108006041900c0e071003000610720304002441d483d501d00c12007817414417900e8081003483c0b4000c100a2812507402c8a1410300511b402040720b06c2004144003079000703015010100e1800c401c3c00109103840c2039a03d0042c80c904c296600415480c20010303541c421543c030102c003510019406000c0c19120448d265009003d64008100c80b041803406030003865016090349009144581e0310b16084580c82c2d02043d811050311a10020881031381c032000c809 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 479146690 1250 479145440 479145461
    0x524070c03080f06061e030609100602060c0a03020d0e16090e0c040e01020915180d08120414010204031410060f1203260f2512020d090b0a 61
    0xc00c80c52a40c5031000b4081000080840340411400f400080d0650345240982c1e800030100800040085610344038000254801e45421b4420ba90381d90010f0000b031095060701050303403c603a004c2d003103a44815881c0501608080000000d1540910424480103680c1c8030343d2550311610001032640c4030b1041c0e2003000865a076003121002070305001301800002000200310700311442c191400a40c03007849007130780c40c0240280e61040f94041903068101d0340400c2e00a001e05441500300b10003900c41e2540c0d008120f901130110000815404040c4103011183c41103c0750503900c1030007200c04080307030000f09402608a80c03054100300c1d8103414000d85503e04807030800200d82c082500d041c1c1044020306240c0d864000520620410320f0000f040c103504001c0510031102180350100011604030b4800341d11411400415040f100030b2017040020000460100a05411000d40a03c54606d041101c1503214119001d0415107103118840390200907003203203640144928030320540141d44101941c108124514240ca800445 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 479147940 1250 479146690 479146697
    0x90f060a05030d270e0702030406080f0106080c0309010f0c0203120a021305061b030a030501080d031a011b0f0506041406060a091e050c0903010f050c030a09030c052407 74
    0x61803045903001075054044510f08480d000c00821312103259205200c07107030004002e40c0c0100003070144494001010348265062038a40760225502c41c100150150401d114100000c0c060101059036182840011901700c0420301c000715001000007031a0050702d00350014800141c2c000108440d20400811840f03820000003841903143c1050010f140d840e1034400c1c0944c501c60000001c41c418103240c10460f0910b84d80c1c0100503240c841c1c0c10814040c1c0103003824030428803d402007625a03409244248218080c180001c3e9081c070221107040c3c0110b46d00c9900c1d14500c03401103440300203036010070240181414400c1c4118000c1030f251400c2c1c90080112201d00c2805890b81d40482c06114003a80c507000708000f62806084c0004103003a0441c0030304034074030200711400402490b00040c4075180754058010001004194000d000b5850f1049a141c201c8800302e035107c140e110f0901c0800c4048400d9086105802d0080ca07082072541c0303580c2c841c10700384012804010700c240c005600c050070340300c55420a1940401d117400c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 479149190 1250 479147940 479147953
    0x1b090c020c030c101701140103060605161401060b16020a0501021902012d09030204060f030804030b0a0e1f0c05030705030403030c110a051f020c07140d02090f060a0503 74
    0x50100703503181c0310300b40703201d120f44a141110314400e8170941403a880726000c2d07100c150381940d450036102c0e40c04109800b42800030381040804074441d8090320894411314035590304841c0b040c1081e21003001c44840b000c03205580395200c40d0006407581a0380050041100d070b181c14194944a640304200300348865038003240c155000b1311030030140440562454000f040e028209160004040418843d007828010b404d00d182407030390010328041c03607880682c500070303a842070f00d003000000e403902d844042d82c0005110080180c0c20400090001403070004005420161401c40800d41e100f601101c541414584261705000c4c01115001c120000614010000b030b001440c00e00c2031035810318980c0100030b0f1100400160916440744508403105120b0702110000041c44021780700f003104940b8040d03071100240d1040c0b4045114030048001c440701c0c0741c4229034285180c4c000030400185085140c00341d40c0100242d0541c003d0400c1380d06805a107403a40340c0b51182010180625040c13802c03000f08038512a03a5044280030f80e02c0038 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 479150440 1250 479149190 479149213
    0x12060603031204060209121f050112030c0c030501051f06080118020a1713030908030c070302130b09040f02090714031f031202010e071e0303050d091b090c02 69
    0x100484042201c2c4034880006582c5600345100644100340c91942c22001881100440d681e020a800404405000001d220340e119200524240c43c4207000d51000c2c00c2d0354612120010b03005410028695104107004004165261600d500f110030444842210b00c80c40c4149041d643c048040d594060b120904110041e5414030280aa504207601046803802c0d500017000c411781030054101c040a1018245400346619240d041205015001c0004038045201800d000c103e4030740c08030075a4411000c8800600b416880c40e003c2281c0140004601c0090b2944c42442c1c0c1882c0d100c50860307a119030b004100726981342c0107a05c18429600c030000d000508020000741108c030120703030000440e90170240c00149a54007980b000005a49160541d01c02403003000c050340c1d060900c1c0d070107401000300c40d20f02d00c082e60382c40d5030f42d41100396112800c41902e20f01680034500520000b809980a024504218a400112501d00c0d5035040c04e110862030034854000941c00c000c00c0f02d01f015000c0e00010031101c0c4040d02d0200c441c2d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 479151690 1250 479150440 479150443
    0x608160203040f0e041104060602100b04060503250f23030a020109092304060501030c05091303080a09021e030d030b030307020f181f3309090c0206010512060603 71
    0x2503004a001d42203111000c18107210200900129106c4001c008000441c0d844101a40d106901030460050030b0030800c0c40700300c0345060320a10080f5600640a04800c084a50580b40440900c000b602c450110805000c140c00304d801d4117840c090182081010820b010b400d00c1360780e2000d400f001051090f400140c6020061740d010360103808880d40d10340301140720803404a00c4400c00d00c00a030343c1154280303a40c0412080c00003942215040300e028058007410b02d51501c3c01c4c41300080b8101c4080c03090395814088800080c0c850340000d030740660300d01c10005003c00030b9400941201d4200300f5900303800b50005c0e040c6441d0b01c0c042c00307180d8214084c1c0c20304200e40f58604010940324042d60b10f0291242d82e0801104038646c6443ea076040003072102007030b494458a0444d101480b44941101c07081710740302800b00045814200c40a03000c25070040d0100706085280f82c0107a602003461403032540c1c0d08201c00d4250005001c42c0a001d000c296803101e40207012190305100510042d02c0328800340302d44590205080c08001c1c0c40 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 479152940 1250 479151690 479151719
    0x50a0201060e0720010605060a080411040c0f110a0b0717060618270103050303040b010509041a04050a02090115110319181a030106021006031e02011206060816020304 73
    0x1004051511349420320300e80350b004000303642c0302c40d420940018641a500364000480f5224a200300d0300c01d190301c0d101006000c1201e50910151001c00c0b6180c100d071a00c10700848110385146030901c202d9440c00c40030303a110108000d05a810741d0106440f1780344004a50109000213900001c10350352241400188602c038840e41049541d564040c0d4030790f08658000407500e55054461031358100189a0317550307481c9011a901c0c0e0084a0540e03000700e80000115051407c1000140141d40028802001c402500f241010000000e001155640328007202000141c0758611094001c02204568000410441c00054500e600c20103100c4401d810030130401d000110100f00c001c11150b5a440d0421340014030912081d4021085c0e00455a1002d40b00070b054511038080c4011070581d81c095003591030300800740c4a0132041d120180030040c0b94114401c18142c04981c4a2413100c80d8070700501d000c0f01c00344c902c00c615400f00c0d58250003400024141c0300030050703110410110301c084502d06100a520f03007868400790100098 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 479154190 1250 479152940 479152967
    0x603122a050c04021308030403120f03060b030a020a0509030d021e030301081b031207051b04050f070f1403010e1806071e03020f030901051902090a050f0a1203050a0201060e07 77
    0x16030102c2c45d0945003040e25000d42c040d044040840340c0c1c550712800c00c2e1a40d01c2d080414500090f00724000701000174464000e50300ac680b04c03000544d0441e103d107681c1d0006508083c83d0b102c200310007448206411798042044114488007030300504211002c0e80d540000c40011410000c0c9142d00810042004502c00209c0442c1d42e294209942084403035000000e003040c4205145034510301020501c0014400302084403c6e80080c0c004416040c25588020300c816034004440c0c034038064202000080c5241d00500281d031070254a8074080d2841060712a00e440c00d40c1080c4c0001090840020400000c0110309250422041c4100c00420103890a101c00500c1c3e2803064504003482e14443c000105840c0c02501a80d01607949170b2107007520392922591b110700805041b10803082102920b5542064245127100f201d01c14540906a0b094040c142000d1002c020f1085c0456500201001e0340066205402407810f00003034448d031b454982d5141e039403000031b094880c1c1d03810242d144e6a500052000d05900840b02d140ea02 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 479155440 1250 479154190 479154199
    0x7110a06020c0a050607021c0f0c030c05030d0e031b120415050f0c1605010f0207060e0a080303040f060b010e0f0d02041416020708030906030105130603122a050c 71
    0x4048a40d2000d081c40d000f41c00c000c12074840c4c401071240342ca4010038000403603140b440710a0402c400403882203e64503180a1664042172078020000040ba1081b032983c9880c5001d4070890307240800c100455011188182184000b0b50404a04244d0a4500c48403022445024800501202d0200d102c030115610540c89503903852190300703950b4920300b4050710984074071051341d0888640300e49103ea00c468075a07044a2201a030b06100400205c0c640d801014568510022540102541030a040040d128441c0340d0b0300c0390398003102800002071000c02c1000107510881c411031030065000c1c018a4540140c0306205807050500583c201d428010380c54100c01d0114030681150060300410840c00402d00611860700440403401d00002000090070b544143d948140d4802d9003140c01c41540c0c1c84520303407a401480d42169100400b0401000742e464600400481803140e20780000ba00c0355130f41e580f5802c01c1141c404540c00f2413518007101d034403014403c00003042441c00101d045031428071595440d031902d2038800210f118 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 479156690 1250 479155440 479155447
    0x3070503060c090603090a0204180614091f0e03161a04050303040314190915020a080a030203040c091b170622090209010e0912040e070e040209040f060e07110a0602 72
    0x30b86c040010150640e000340c800c21601c0c1c42080c401e082c0d1080804c2c2a1034044c18089860270a00341c540009110384184009862200d10500441810300d102c3e40b02c20810a440301c045d1500c00c01c0500007081800c6540300d0031845140300d4600420b24010850700c503440030340740c2005c20001c648084100d070390080d0715180494048040000c0c64010f8010441d294007034440540d1509280c43d04809044140d030035415003007034800005034080ba541c2c404440c004100c048103008181c58280681c0140d038019115250880459448480c80303401c48103090301e4241f6107031130b41e8012051aa00480182600078051035481e1040c0b42035030200d41941701010720040241c00c105e11800410070164410706120303a0040101c401c0b035a5603043c48555a4050f07842c3d0307186002d42000401070301180000c0364110740e02c0c07044101e45a59040c809698a003502d40b0000d401940821000c900741c1d40d54412040c900403041400110740c0d04201c204002404001c03c2e4500340595280d1503142c81c00000303900c00006038000c5002d80da = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 479157940 1250 479156690 479156701
    0x2d0e07032a0b070506090f0309010903120504051503061f0e1908010e0a02041103130803060315010b03250e0f03010225030809010c09030204051b030709030203070503060c090603 78
    0x4411220b60001c01c00c000003148002c10030501160700ca0050104204403109603640705c8145441c0c0c03150005041c0030400302c000400014003445c49160702c1c41285c0c18130034145030760303800070500c000000710410135800b800100704242850210020b45290f0034000c1075000340e161084026205038a1000303441e100d948110b000010000149100390098610b010091002c201c60164099503525080c0c4100e10a03801c00e12048412069401544d11030007d25010254441c407a45906c1c80d9038cc4058205034040c0510610403020101820445008040000c0403d550f0301c0c001e00c5101080b0713100d0180313200300d80422840c401d00980c4040307440c802810032524030b102d4030300c1c000c0002e0091103055000000012000100c20180c000d524108081302e010747c43d007005550350b40b2142402c03140780f54500e10115000304018005420141c0c40030b179102d4403810101c0c00c00d40e001104004640c10456021001401004041c0110304003844008010b20702074000f080141030104070340485001d50101c2d18001d1402100181c07 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 479159190 1250 479157940 479158013
    0xc0d060e0a05070611011107120c0f020a23030105010b04060528050a090b07020d12020f15060a09060f090c05070812240f01030c032d0e0703 62
    0x3040c1c03a800070444400c2544d900e8060509680468259040d519100480000801417421511840c1c1c4c08a40700082c1e000700711081c1c13110484c0c008281c0d280c081607002c0ca80142c541030303103002c0035000084850020101403500c1e603040e034152039402d502a13410540100481d00040c0151004e07144141443ea845154034406011040d18503c00e40400a100207040e100d001d41240041803c40200e90304d81d0007907030302e403140700080d0300c11054020f420204440c0140003143c1d2510800e03134120b210348141d81c40c0101203c0c01c80e107815141c821035030f00c030402c100600c00c0604d008404d250050460110501c0918a0000b420380111243d104110303c59881d0355075011454030600480d414144e20146140c0c4543c11b000f9407049858049480c500c801c034510b40c080380011212140c0148104e001404001d080080707200440c0038204245064060648900c1c0180442d2000c203542e42d41038200e1006450340c6150080b40d4020385e103007441d40c400283c111071014400300d41c0002e04078011241549051403107960155520 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 479160440 1250 479159190 479159203
    0x901080115050705010203040b0f10080a020d03090b0d0e06060301140c09040608030a0207051011060402040905011127010306060203040b03040302070b0a0507020a0e060109270e0d02010e0c0d060e 86
    0x43c200c5d4800010001085410300349140030382c071400c01d01e00c3c00307035140c1d0b550880302000b6025100da15031140200340f0042c50203010b214089482490705500342c95031981c140c400c40d00446450813075261500c01c1c03200c0410041203001d50289007180244000601c1c640d4142c40640041d080440c0e250b8002448041501c0b245c000000900e1403a08580d07036206200c0b4001e4845500740201c0f8402c407100c5204108251003540c11074561000c10015000948a6a00704030080403a200112095500c48500c1c880c84403a21002d0240111034012003281540c10210004050b500300310f09c0c0e41403602c0d0040c1404410343c00810350302074914195031160342c0d4840d070030242c2c40e001d045d40c0804440c3e0000070342e06c5509135015015004851007941d800280c1515000244160308045400034006030146200f08103d01d0b00e00d02d04d0500c6568408114100c02d14580f81205130356070b0320105259a03200203240c600040d82445404007400741d01001e081e0a6140f0300001d0140560342c0c070041c0aa40d124030458206413411b0020 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 479161690 1250 479160440 479160443
    0x609121212180610050603150a060509090a11030105150408120712021b0d031803111c03053f180714041e02160c0501020309010801150507 61
    0x80c944985103441d075034900c41021030307812071081c1042055003410702c80007407528002c44844142222103420042402840d82000301201c07103001071034620741561748801c0c100e1009000c2c20764400b541d0745040c6080c4480c007140a4582c00016140803034815040354041c0550341507034030803120510045241c00a0780400d01481e00003101c1c50042c0c0c41c00c40e010f0385840e00101b00440c440c842242c41ca40c03000d401a82c07203c04c6030300d68883e070000c034441040c4680341c05800c1445407440303030030aa006104c101c00e07108402e4441d81c104035811004010760781510302c2c264202c5503161102c1c602941006050f03560080c100d00804441410b07102c0000c8203022501071a0980607060601d01d8040340c241c040c0980d94002907901901e9100d00c0300c401825081c034010020a00c802039035000f544030180d00e01c9880502c40104100316103094089000c003121103d20f85140010980aa606001420300441070700380b218100c0c102d030b80030720706542c001c202c0382c58581d03000026181125410140345909810480d01504c291096000 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 479162940 1250 479161690 479161723
    0x207020607060f06090e01050f01060e0a08100b150310060c0816030e01030f0b09010315060b04080d120902090604052203110f0a0807140c04090510050a0b060912 71
    0x243c441c05003040c0e01401c00c80b030350042d051000440d600f05072030881f00203441d0b83d64500c04480042c0300c041d00800004100c0d040142c800f80b02da565494105042807048203000300d0441d101c0c0300304220b500e02500c840d400100d0810304645903040607054841c0219461080c60b040c854058030000500000f0025074442556280003003008161a01d0000c2c26021002540c0d0301003440c000164010055510405108371406413255901e6420743d01e0b060000c1401400207034125865980c080ba60100740c20180005141d20002095950100d0070301500d50395114280c4c1e5505440c00014001507903d01c400d642d0494801d840000c1c45444003511244604103000b42503084451416050781015401600e003405c0c01501c5007600d1049403646d41564444002e414050601042401034102040804c0034041e49100081d0484c0c2c00c1002c0a4045416607151070070580d902d0304560348040401c060340c000d050b4846e46007101040f51200f448001142070060a4410340100c040102140002c0010004020980b08906 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 479164190 1250 479162940 479162951
    0x150e071e140d02130e13060b0301020c010e0604050709140403030b010309020a062102040b03180f06040609050105060d03050a05090607020a0e041208100504050702100507020615010905090703020702060706 90
    0x6440b8040d41c082103420b4144040d06100040304036910b00304034018803e41e0001e40000d001925070310050040800c100c0c0d4103550801a11035154001d1291403510769100c005007405180c0750411a00340031060f8410201c440c1440740341c01200b11a0a091a44190b05080c0004c407182e506004030002d018880000b900301d445e045000c00e03da90001030001183c80102d070009044843c0d505148180c1c0070714400c00f0361601c000d00100c1c96015070844503a40c0385140100311122184210120b0b494000103407000c0e10901d555816400500000380038041e4031000568075a4010301450754010070512440406800b0444080f6031442c450740c03500200c45400307070010907000b8000d885113a1414140300039501210303190842c2c0e56030f074542405580c070a84a04088014200814984002e10004d010001d1a4008501030342660001442031882014018516980240014500104040103200b581d40016040c4221400204060b586058a255001405180150b114800b13880806c12900a85500510290400 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 479165440 1250 479164190 479164207
    0x8070f03021308030d150e0408070f06112701081801140405011508060106050f0a11010905010504030e011110020d0b0a0b22080a0f050f10150e071e14 66
    0x40641703a9844400030800441601d402c2e450b05d020001e11580310f0001c210750000d00800c0e85c0101906511380140d40c050206903050782c0c0c0d00c0440d01640b81030100c00801040c51452001e41a8a4520341e482c00500302c0c0700d20407194000303040050014503120300e002902c031800446c00000e41003544005088448056141420726003180030b0700c0c800c00b07054207242c850b51001071102000150313030b4121482d503180d240c130b021080140c2035030542c0202d580d0018030224800d1103408a00034410024040e00607000001c842c105442c0040061966020040c1004011b1104c030403801c0b408100e010180364071070001691401807100c3e0390090655032011550061032482c001030a00c01e60030042048009800c400041152010242190002c5a0103841400d60010b18420001008072103c903140c94022411980c0c2c1c0e0300100a040c0c90a0f1040c0300fa40074a64030380e800300c019660003000300405040e24044d00100352618800047c41c1100c001c5403071200010714010041b409005901c5c0280b00c110208010b03a03145800e = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 479166690 1250 479165440 479165443
    0x708010c02070317040e0a11070c03030e04050a050c0d020309010b030307050607030b011803060c020a0b0c04030b090a2d06021306020610050603070f090e0403021f0b0108070f03021308 81
    0x1207100c16901d610f2000f413a800382d0f500c0c580c115010740e00e41903040c5102d070b01d0303201540e4020b040c1d4991321503c103d0100f19460101e4442c0d002c0b040214465070b25101404440d40c2800240e5102130581803601c5d092409200104005400351070010401550051b140d80d90f0a0b105405071201514440e010301001450308148080400d0321352050406403014400c1c100440c0045400741c070342e5802c06d0078419541400384006442e50300041113451451048901c0e840c1c141d1a0404034020503141c0c40710741c00e000901001005038010540303a02c10300c000090503000e4105e445a031940311a542d15030101003d000000180016544411821946c00c21021900e43c4030b9040060340c900c02501865003d8822040014a030300d0080920500b61000a00094115107a070300b025079940d410254100300b404260304010541c004410301403445240030f5802003190350089041d030010380714440340e441c50b030703900b4007044405170303604100e04540143c42450403130249925008114020301840303400c1e0200c48030f103d8001800310340 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 479167940 1250 479166690 479166703
    0x40209040614120c03190501140c0a09090935030c031005030a0507090b2e030507090f0e07030b06071208070c050705060901050f0406120f05190b01020708010c02 71
    0xc007030301c40f892941c04803207526940301044000141d143c1e00a03e0045102d07520356840e00c0c00782d48600c002103403000c507040c141544103c0403170b82e0000000c000f18801603070591045c505801403100b80c0c0c04114804054450513840803441d900c803280790181009420f030b481c040301d00784240010b40480c8a9240d04051001c014140d03c01d941d182915050004042424030340800e8014201b58004014004240b900d080e4101402c1c1111a0950044804030030b82c5070103000340000f00c00341140541580b030f00783c03c1d01005012240090940410050040400d10003000550241801c0d629072101d441001e82d00d0341c0003140648860100b194209130301141150811080c103400c1c1050040e6a11902c043c1d0f40c410b84102d8800c142c0c80c00181955100b00c4082109041c060000c042e40300d018503106240100c0070345168500e40c42035000f8800680c00c2070045251071280d1140240030b034400381c03013448035041014099942440f0b0090354242c01d903803540c413078080c1d0303008018460080000134000c1c040b690084002944030714 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 479169190 1250 479167940 479167979
    0xf1504140f040e10240303030e060f0c070b060a090f0e06090105150d020a0305010204080d090b0703050415180603061802040302010f11030f1201031b140f0402090406 73
    0x15000080446180340500602e0603420703c40b0b00030030084101038007100c050001c0b0b40079014840c1c000409101422505103409002c0e41c001e031401726083d0100b20b5450b140ca040102082d594040400a01105282c903004035451990070544640f0790f03444c0d010002c4c1c1406020f52265003864681305c221080c00c490340e000402003a114006a41455a8400b0503c0c04c1e1101143c2640000b62186070240a03858414a4100d14600140c10350322500d03280c2d07075101d0072a4400d8100032016130221441d0300c0281e51000d40d46001d00511480c09d400d009c1c440d030b00a0042c0c0228000c00e4403100b00703810300c000c8172807244031b50401b50040d86110408e201d0751020081c008141c14003841046050b5492083d03201c00307450085030203c0f90b044e5503075458455442e5040b600507049a1644038140000c10082503840c500602620b2600d50450601c030440d4510b00e84511030000c1c40e000c04032400d404081c104205452240386000844080e90080f00d2001c050000500034840c5412445e401482c14401281444a40c0712040044 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 479170440 1250 479169190 479169199
    0x1e1b160606120c15022805010e0109060b0a150212090402090d15060f1d040206070827040504050601090e0c1503040303141009021305180402030105010605120103020f150414 76
    0x3484550040362991260441410400414006d0002550303510200c1c00c2018041c000000da9240302c4003a4500f92183c0590556146448490303054041c50881c920100505402010000340d9421480181d00c03922403884440082102141f070f602c264545404989200c02c2c0103200b64501801407811814140300300c0e0f0f5600040e445c100000c1841c80800201c5402d50f03500c2070024081050258101d0b00e80e10000700100d82141060041400060484000d00340380c0340d8801134841103800c0d503000c0742040210301462511550070541440089900441c0d0181940d00b84400420710032240c0098500d072400316014960400046254081c489071707e603004c2d5010f50300c01c0ea42445415640000c1e0312a0f00360039550415030074400c08003001b2001440c1c0c01820501c40c20f0b0003802daa41e50341d00001d554414850350311419038040b041003008524080c804c080c0909001c0c01c0580c10202c2415581d200041c05000081c0100c1d041120f491896548200c1e813120304c0c050481c5544d56644465000c110007aa0301c2016004 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 479171690 1250 479170440 479170469
    0x1006020c060a1d030102041a0403060b010509010f030b36100503030301060804020d170307030507050309120d021905040603060602010c140714061e1b160606120c 71
    0x241c90300d0780490382e4424055440e08a100c007168000b8009010315240e00d80c4c150350030000005c0c0490296801500c070903481010740c1d1030310700c2e504041041e07a00440540e81041003c0010b202c0503a00a818110140c82a10f00015040345c0c0e600031a160148202c0c4000709005a10301244008000c0e0010800c415106401600e09d5110354030860300083d41c0340107a030342c144c1051005010035031182d99101d60203800101948204102c43c0c032102640200082208450000041009003054244c09410741014992804038910700d482442292205001c00104039a1680080c800c1c001c1c0107180c041e0f17002c03a102c00d140800c5c0c61892510182c8554824450b0001090500500056275401845800700180c001c1d2220f80300c071611524504680c0d031003800c0031514001c5281e82460444002c1205510420030082e03400e8124007210301000022400601c5000441da104800f140d003104404140d6032074a9091030541811019860321001605060300302c00c0f441c0940c20000014465002131587c100c40110401d150f2 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 479172940 1250 479171690 479171713
    0x20a0504050a151a03010b0d0204030c090e16050915040b031b03160303120906090507261219020a0b0f060a081b130608070f141f080709030209100602 66
    0x22004c00c02101040761020310040100c952120010000c280a100b00146041d13140c1d40c1e41c0c2c00b07801c0281c00482103a5500c03520a10342c11810040014614604841da6103c6440e101c009070030342c90006c103e8841e600b02c080520005403116040740d114490010309403103c4076040b0142c0c420f807840c14440140700784100c0d09090700c42c1b641244400d00303494051740d448040024807448a0042c0120040488440ba5110700007800320f0340034404000a014050980b42518814101d403840429403c00180c207290005482d9200110f6220125524490050a0994043d070550000d0742001d00c100700141c2143c80c04403c0261411140c2081440b0342d02c110b80c08030740305032104035556031b0b168158081800d1801c00042d000c00f034602620100c008000381140490001d403512403080c05d00820f03034011140508042418850049004002c1400110039548a0381c000890701071240050420715018003408001408103610070711600505010310303009004507016007020881c0d41c0248000344074250060040740d03040d4a = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 479174190 1250 479172940 479172959
    0x20618010e100c110f04090c0f05040b0102070311010e18040b0f01030506180f0d0806130b0603070e0d0204060311190602030921070b0d1503021507020a0504050a15 72
    0x118030036402d584141e5803c11640c0c3d07040840d865a801a50700c00649601421141d032607002d02c0710b071284a02094600316241071698107211415404c80d0380700e10301705204402a660b001405000302c0303400400c0744820320603035001031f2410440c002686800130000b207003204942c1960798156002d184a0300c24414159070366078901840705020b000003040b54020402040e45240700c209001c2c419810541a22000a900441c0500d0301c510f5100d600301041c2c140302000349900d4151513403002d40c03400410501c090640840001d8a502c0700418240900400d07451420340e07034030b0340e808410441c0d5016004100403502c03400d002d042103000c6018036200700c6115150750100100380d07502d041280d8180d0001c1d420f148219003000203191030860710150244003100d500100b05002c1284000402c59084016a02c00c42000100141e9408400f03254101005c50700400060302c40700900322a141140c1d4032941c4030403503440020494a030781d90005901504040070f00c19460069440391b06018400c0040084080d80d514040b03 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 479175440 1250 479174190 479174209
    0xa120c0b04140108090f0610080c030109240e010203040825030806010507060906060b0a02160609260111090a05040b030d0e1c03021f0b0a03140307020618010e 70
    0x2d90720022007281a00d6075010342003240d0400804006e54510719424011286040c004a030003041030802420f080180b10020f01c06c03404164402d40003030144554507160008011a4210101480145105d420050b81c4042d401200036995440003950b41e41400e050043c5c0302e8101c100404408803202c8410244281c080046804d40340c1d040e11240000c0e51684010f4509400c0340130141c0c1c050744c0712040300300010001d20425000c2c000e4402c4840e11800b0220009242c0305502d42e000d1410390519205000140d000101201120403600040d0f41c01c2c8840f4403181403d09000300540f40030360070419181021000d00c00508848041550780c02c8281e50b5410401050380c80c0c0c002030030303050303044041190f10340c071b100324500d40044501a004141c0c000e10354840d001414070500701500140c004241c2001583c2801c1c2c10030030700640c201b006100c44410300d00042d180007280c2c800104001c103c040340d012240b206005031004950024015a00c4d0520020186a0000c8107a11980082c00f881940b4000745000402c1 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 479176690 1250 479175440 479175449
    0x20c12011e0f150807060810060c0b2e21030903060207050106050303030a050a0c0c05030a0c0302420f1303120c050703080106050406051206040b0a120c0b04 69
    0x20706110070305084503800901800a03003240003516036010000b007007006401d803401042d40b5401042614038010300140081e2000d4242170503240380742020031180d03500c80e550a05803a04010f034081584c4490004030848aa00b08102d400402e50b100001d240300c040d40b0078142201c00d40701050554188481c010a40001c410500802207144041d090012070115030142012301d2280000164403500c0f200000d2460300100c03032003484541c4560400c210304c01c0502038043d41d40c945003410031424000f56607075500c03401007102c04010400890008030a044c800c1000d80703401c801840d810074403015050150b1140b44140c2004075100c90101c2c001c10100c1940f180701601c540c041040005203500d8500351885900a03040054041000c0005446c0c0c00203032520550440c6d404079180c3caa5680c2c010300c0c014001020591040703052040610081150a03004011100c0703110320400c00901a07940c110024000b0403640c41035070b4028064640203c1d2146c81926100b81e418020407460904a03036400d198200c034400ea018 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 479177940 1250 479176690 479176721
    0x609110102030319020c07030506010e180c010c060207020109230109080c1513080102040e060910060806010c050a0807060212010f140603060f0d080a0e04091208091903020c1201 78
    0x245000d82503000c5d40905a540e107000c054a1100342c0d60344885103001001c0c0c02021502e4801002e0200e90684903540d2803029072201e0143c402e5042d0300c00060041500084040c00941d0001003110440e03120303000f0711020300010310385c265507401c1003003044e00c1e10801000b01e030740441c02d414004240ca480c0003039200311094004180300548421900d511503907402420340512219030f070820102d0028405e002600180040c1d901d45006480c14000304070720500701400304a4181044034040c4100303644020041da00181c02e090170102c01c02107280c42468040e0500c00982824400f003055401c0140360380081168540036004581d83d40d032615880080c1780c0c0f05110700700c1405003d0140c4249802c20314069580001c7c0107000209218941700420170300c4580c0345c0d003220503460000c0d0502059070069203150010905072010001c2208603035603030f80858208024082440903640000d1110300042204d4503001528030341c10f011704905da113000b030341d25203c14410522903420300c0122107180d0414482c0d080d00410942 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 479179190 1250 479177940 479177971
    0x1b0a051c0503150d030908030a0309170a0e060318030f0c1c020c100e030a0f02100903150905240108010c0c081b010b0d15060f050d0311011806091101020303 69
    0xc0800030344510f0040105d00303000b00020300042c000018406801008450f841c082a550100e00e4615800006080b00d504850014881c416406501407040c1915901c02c0d50101d54a40b100c140d0800c0d147d4003d140501c1c3c500c80010721541d18180c1c4000703403040c81080f10440d00c03040307070300c804011261032988110030040e41302c28614005894090744161502c1c11034105421001007000100307080c904020b01c2a2403524944070b400d011402c2450101c04075018628080b0212030940ea20580c2ea500c0a492084440c0d898452000c24400113005000e90003c60b00c0c218407907002d065041064032502445141055480c2962205126005a1702859101c0c1d00100071860304198410301c000200a96680400035036840038000142e031030306103008840360f0007040004441958200804245c03042d41e0008031030b41802090401c09a02c400400551003a8142000103d00300780d6083c1c1d900401c0c801c00f8408074000b60310070714400e10600764804032103e8061030811060801c00401607070b030f910003981d030101881100c9 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 479180440 1250 479179190 479179231
    0x11d0714031c0e2b0210020705060d091b030c0e0903040e0f281a03010911120c060f25080405010e0609040203180706020a030507081b0a051c0503 64
    0x100207207030442e94014841455100212004813100320007401940c2c1e00010140700f032042d881c1ca550406070420070340c401014541d043c0300100d4010702502060009142d255114201000010b150340882c0e0214035241c01e241030741e20705040b03842c0c505501c544040d4024140105480110200846056030114110a011900d035880c081c2c9000c0340003840b0b2080c8491030050300b10064007410f4030f51203986000c80d010811310841d8001010038403c424803a4880da142c00790640c0061060300012102d03e50844020706100407603545d15003010081030280e50301550000e003411140c041130001d060034030300e0074842a4501684040c41e0500d0002000c1c0600621002e010400443d8415007142d0203158016007014208114200850182d07001078800c5810702c0001d1145039889901000224000c0c003031403004000040841c1c602405c0c5110b40d00d070243c004000020034101c01d00d20103810300440d4101400b00d0705090b4003410901d0701c2d6a60300130314494024220407229102d500c070b01c0a4a000f075185c100c4154116000 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 479181690 1250 479180440 479180447
    0x1b05030f091903060b040605013e07091407030b0112110c160312180603050a0e0f0d020105060d0b220f0f05191a0603011d0714031c 58
    0x21031401035200e81034014014400b8070021098000358802d840120300e0340302c19010841610043e400250402054021007280da9402c5001c0c84942c8501d800c04040641c072061105010144d400300c4c3c40131a00c02d010303000681040c25171005a43c0c01c4030900b4441d00d51900d079000c40540d05844105800940d032941062070503081d0354041c0107100200e08416103044001c400250504001481c7d5160740300c03840034108140a42c003807800440d180e452038003522000c88080040c926001c2402418201555940021114019607010084000c454000c845a401e5904101035440c103c03500144c00550806000c9070340c03030400d41e486814007a400140341d911641c0c0c0031004650307960b01d1100380407515100040c00c00443c622044c06010107000b40d0162140b41c026090a034070f0711403403100e04071040340b9291000c008a031070032404801c400a0300e045c201c1e142e116240041c1c050b20104200c01584400001e000f0404da1001031410103c420140000e11000301c1c02c02059201c3d500040c11500e0211441c603800f000521 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 479182940 1250 479181690 479181697
    0x6041101090f14100503010605030a0504061e0203240a06030e031b0d0219030509042c03120a150b0706091b03030210050103050d0e220209011b05030f 66
    0x80600d000368105986950a588103003003a07001070051103d42d490b0101c40c0c02c10400303020100c2c0c007038100701e407a6514045001b0294440140b260034031641d1000818100011030300201c0c6424035500810500c0514041c41303038001c0d801a0f0b000c0c1484420207212082c0741c8082c0070342c02d044100040c101c103e16440d0540a4000e0400d04c401c40c1001c2c00304210301d10803480c0030340c034901000203542d0040c148041d04210291409a0300207408248101c0c0e61840700029500108540a100e000d82d0040b6980800c140e603004002502c1002810500c0d5203040840b81d64400400341110b01c080501d400da05480350092740c8100c0c0c0c501080441440c03907900c4107105855150307000300000303413098000040307100040d01c51031000c40300402240386070800740c0000c000381a810041914a900011010082945503a03134071640c4800201d00c4006110070b00b03c010b40340303542d4400d00c11050040000900180b40c40c10014500a5001c03005a6020501000c0c03074086e04001001c02107043d55004d801140342115400000302c0310b41 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 479184190 1250 479182940 479182973
    0x5030703090809030f0c0901080a2120030a0327060b03100f0b090106110604020108060103090803100302101409041a03030d0906050c0a170604021204050303100e090604 74
    0x2c020804076200780c5040000701c0c1900c245101820342c444000003000014001a409102c8903401038045030301051800c49900314800004072500700203000010141e40700003101001454900896510940744140070009151003862550304100d04003541c074900e81c260310407408000105840c181d030007001070841d41c0300001d4104010b08030b41c0c03170fa0b00c482404c0c0e0540751840c0d5000c030f0558982c2c103810380071f080a8200b203000d8503013824043d44c0351196008440d03552000400103410051410301103030381d5034001ea202000203508008d003180c0e03030b1402d5450500c1d100024441203005444040041003881e120750312000800c10002640c5241c286280c04110103003000c0384420000021500080010360fa082004100c40c002d016008204901e05040c48011604020450110382c0d4040110490aaa105038102501701001007099559140c1e000403500038001c0800310460000500240300520500101035882488441803804134241c40d0702c1d5285415a00385c4180540707901c107002040c0021341080a000060 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 479185440 1250 479184190 479184203
    0x4020d061103090d0f03110702010320270103020918220501140a0b0a18090b01030317060a0609030b06121204050109050a030b0103030809010b060406080f09010605010503070309 78
    0x40c0140d010348441e0782c0c4240d0310b81c030701903018490116405410101d4449019018142040f12544400a618082c813402d000281055500c0c81c42400030740710a40d0f0045c0d940c000d420030340d88810704c6080400401302d203945a40c1d07040348010100822980b080c000c80703900d42d001920b40140b60410102000000b00c1c0908020003c80b05420000f8071002c603605401d8426002c3e20001c0307010001d004466083c550040c04143e407032070500e481190343ea2540300d000c00440321840e41000c00001b030f900f02c03003005046800b40180140d40550000080c55413003000c501d00c1000013000001079858080400840704958803803640031404605042011614620034541d01000190900c0000c0500784411400c0c04c0c04103505010100f8049024041d6591240347c9d000507102c244c4c2c418001d00e0079a00c8038800028140b20041c10040c0620020f0b141d004203400044d0080e070007030f01c01600c0742e44540002c0e007400003c840f610396100400c0e001070610b0005010394030456606848140c0782d602c9181c421809071103020f000b582e20 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 479186690 1250 479185440 479185451
    0xb150c07050d030305061f20070b12100f03050a0204180606080f0d17060603090a0c14040506091608151203030406050f0c04120c2d0602031204020d06 66
    0x12900c49142d24030407148203a90004180c038000c800c200c440031104048045500030303040c1c0d1054241e04001c8420300500c41e02c0c00b81500c00400c480700c0b803078403031190441d00700000049040300461402c4690940100340713022144504a07241e14203d030040740d103848094455400141841c0150603e82c0c001e00c1e2195140032460205c030002c0c1c6a80d025503a00d540849842d5210082142c0c10500034407200c0f000100358a84507600c1c0004d4884003081160141005125203000808900321003020400d444200f6880f514085144d07903103560041e00301c80f6404c4071900035418500061241c0c602402c03868890008908200820110302604503041a002041d900e401458002032003860369403c50b1400201e080a4011956482c2520b00001a1103000e00000d969092040c10b00500c0480001035400350b0795015941055100745041043c00c84111b6030041000d00c40070340000070750f102c540d00c180070b10b015004400703449143d032000c049a903441030031104041c00782e180000c640181307880144405614041c0e840440c8 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 479187940 1250 479186690 479186699
    0x1030f020310090b15070b0916030b06040b0414070e060408070b07050d02012c1507030e0f0f0304060302090315070507030e010e060901080a06170a150b150c07 70
    0x2280e00540705400c0301c0702d1500040000c00030a0040d901a55001d840842101881c40c6a001c03c41c0502200240b6100c80c000c00141c909004100c000209200c42d0713114090039649040c25140083d0546216000b07a0500792000f030b031401c0074003880590b0302c062584451996200070048076000d505245650b40244d04101c002071003007040203060080c00e49149802d65821040c90100d2500c4001c0310404256410b001d010307001000c2c0c00480e102003203800e842c1168804000341d44a4105002c0c3c5a5100c0c9844540c001d000c0e0340e651583c44440740c0030052007241e070310540045c49140d03a4003260300144059070041200b4070200e48690041c10200b40080c08072000c083c0840f0982d603100750101d40c400d0000b0b5003c03d041d42030552126000c805503900b03003000500c180541020401c0c038811254803505022104000c28142c100039403000b4001e0000f003400c0341040e11807046450300c0d00a091800d1314906403004142c143c001e141d1003aa405054000c2c902c4101685030148204103410104d000c00340e50007101e90004 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 479189190 1250 479187940 479187971
    0x306080304080132160210140402010e0307030c090902040f020c010b090c03070507030503180615040c030b061e0c060106090e0702030c150a0e160303030c02030717090103 75
    0x406880300c40001304680c015000c641032241c2c188405105202c0d89840c0d000441e0aa40380c2e0103810200e0240110b2580ba065030081e4600302c1101c0c5a0f50310f9900c1c1c85a000c501c2003590700024003032807007640c2d0034403041e4072241019038503500e9010150030a0b440341c40c03c10503600c0a0b48110101440a00007148018021030005c04076040704150280c4c594403030907905260f1408001d002c3e4031040310b0304014114204000001c0c002c0c042c0100c000c05004000010404c82c01c1c041a004445502e003c01f240c0b5240340c052011220341101191003070140b414194000d14050080c000c585c4460006001541402c4040b040358481c180502800303144c2d1401080062403951051214030301038141c681b103403040540ba114000030401c1004201c20119041840525035070080450514041c0201c1e019003c102d49400c00c01c240148034009005516224140c0d00e210b003100d80780016400c480c000d40301086080c0321030742c050781c9910490b900203001d55017241c0c283e03504074a010054042c618043c5000600c0188132410403 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 479190440 1250 479189190 479189197
    0x601091e030c0e0a05070c171605010c022b2a05030a0e031506010804110f220b04050115110705040524060f180d0813030b010803030106050a0f03060803 67
    0x1003c07941810070821800d11403500906401003e10714220f0344050303894441c1746e80c602410040486040000840104030340c6002d401c500b116410400810140142c000c2c0695038400165106e000100c80307142c1846805a40c00312303003083c1660360b00c4101004a00d0b118201c0d002c1c00804401e0701a0200b40b000c1000300700704201038001001c05444542458840e5003c1500e030244c14061040c02c04c0c24134003040a1039070301095440d044bea2161a00c000e880d00c0000180e0041c81e070030354842d0404c64411324041d492002404258040890610412001c2410424001520824003800b4140781d070842840030810303c915026640e035503101c019540103d845100050a0354000d035041c0000072801d54001213411484868900c0cdd0400841c2c03024035150031034203210010300802000310101070030301c2010070307840d00c0b8503503581c40403680801c4103540c403404d8019905540c3c183d80030030790f52081d03080700124848800004480c1619275503202c0504042a880c1c0c1100c407440050020300c04c040c0c40764030029600d541040503 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 479191690 1250 479190440 479190449
    0xf0705060f06030d0e0904060f0c031508120708032e061e08060f01111024120b0604090c151805060409020c07030b09010203070f080601091e030c 64
    0x506000c0c1040740102858140150603248240c0264000e44c80c4160013120f44c04070380506036000001eaa603a410720000030481a450440e485041940200209030306501c40030301c0250540c0d92441c40742c0c41c1da851039920030950344165201c210400610000c1180c8a0241d80c1c08041281c25551456981d442c1e50020f0740c0082001842d4000d840f028080c0c0ca411134065400880c01c80c90810350721071049402049418040d100301e01840c0b0f541d40030f074841e9205140c50f0308066503460032070362413154217030050000304050107001034031110039501d400c0a011041282401c8850700500600701244139210942d0307030b001c0030b40360b00d90291ba07a010001c0000c0c4180100c600512070a84121801d450344d1001800b4140c010f204d0181c000c0131560f0900ca6980e81c5801d6805580c086240180c0710740300560b00d1881d2698035000a44074035844d0081284043c01500214403400203561518102c49013918151450001a0ba01c580818003024091200003c041e00c8400f42410004c0c481111540da900c8a10580515811 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 479192940 1250 479191690 479191693
    0x809011b0c030b0411061207050a02120c0304140a0b22050306180706090e04151e091104020a320d140c0910110703020604060806010921080702060f0705 67
    0x100024400c0030f82d021666185c040c0c030018a0100c20f0f550301400050f0090040c0144007000c2501000303e03100700400036003100404889984e400e0021201035484c0c200707210740e250366800032450071b126080c140b09200443c1c06c440c451904101070102c49800c180d1900380005d4a044074040d0003e456901040701c41d0150160104200c06200342d12011400e0900701e4000406004090404000f0300c64800607030ba41c000c0d00407607030f200c5201c115601c80000e40030300850f501851102190604403034039540c0c07280c04907502c900f2512031444c000a00f440207a0142c620703040c000c0b8041c000000c0a0501441202e04910095451084100b1500b030501d4916044003200c501519515500d100801081d5012944c11139148820181030080c40c500040c184000031000c54108800101c00c460f40c0d160800607a000b03103070b000f05002d03200c0d511681c0c014280d2a049070301074001080108002003903e501e8007440100c030840c0801c030480b0009616442d078150b0101404980100080040e039001ca9a440042c1021510071030 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 479194190 1250 479192940 479192963
    0x1020f040618050a060f1d031f0507080c070609171c0501230d03140307080901050a11181804060b01021e03090d1a04050304050a120809011b0c03 64
    0x41c50145000150b000b89004461380c0c4424050250401c920b0a05221289000702c10401000161201e9252006085400d0300c030f24031030030702c081d030345d615410040340d5448000308440d81e20b80c030040324102800d58070240003000800000d00030445030303008050500d00500a103011612002e004030613592115111001c10400d00080d03d4030000b050007254010440d858000f181d880b030b801520200e0034103d4600a1041d069900180205400303000744102c200040f0004680301c0c500b124001d00030503000c4920f84240d51800000a514011520034203200c17241c0b0480540c20400d0685d94544070850240149901c100200c3d500050017024003101445244607082c003044d500300200000e480c05d00c030a07000c600c003030703070464000c0c100c450001081d0f620700001100e1154441107242403209001c1c0c0c1e81c02041c060350000c01c040005210002000380110f80d0240c0320340455903036500c14104d50340a00c0c0c0c4c0090071104104004610307588109a02c1442001021049408004a80d5085524411948102c81846100 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 479195440 1250 479194190 479194217
    0xe0103091b090c050906090108100806090d03180b0402210105010902040905011d1302060f0c07050f06040e0a0b2206030b0c070b040f3810060206010e0901020f0406 72
    0x18026143c81c1c42060a000d4104643c4400103200c074041e5002960412104170006140c803051b01607024010000038040d03450b00d041000a1a407a064103000d21008682401c604842140004031340004103908152021180e88542e8204881c860701d20340b500c0c41070101c80010a11301d403403e2080500034031010b07000599940ca81071201c0300b6208160b201c02c4000000581c0b40c9011f502c01c0440e16408a00d500e00441070008510000e0103600403902c085001d50404654603468000000d0b000d8161082114048010f0b0001e50822125215070b00404682061b0070003c100300e04030301c0d041020280001030800020b401205409032890041c400810207094a9403410818000c01001060b00014803607102440d0a4440c0c98141300c140010300001c1041034052030507018080030a0011450441c003803e51000e503552403031b4501c448500203c503240b41c1c1441074007140804994030b08083c1101c42540241c08242c4ca08044502c240c01c0c0180304502c1550204003841000c804c4800030805011710f5120002d050204 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 479196690 1250 479195440 479195459
    0x31501180f14030706090b070f170403061e05060d02040b040912050301030c0b040501170709030b090703020109080105040506130305040504111c140c070201090b19020d1e0e0103091b 80
    0xe45c0c0808140402910140860b600d540d0403580da441c0c2100c2021184441880e10030100c0100c0320641191000104010040013001e4102a406c0014120047e02d1915907113254000c50704195206640003001c0110480142015000603503400002000090b0b0030080740c94076103510741d90044000011750300100501c20084020495005400c1c01042c0070b0a050034076001a10807190340c0118180c10104000050a1138450130592001e0341d8422080805803e080c548984d503680a40022070129054400c08620b0f81814800c0c1c07841960490000c244035120842c0c4030415107461f101c20f8040001c1003001160644450041c0300300109a411440c0d03a41d0b101070040074078030366000000c6415900713001031412041480a0300541040081e2605a80c1c0d4034a0b10045c0d40e1040b8503401a07030008800b144800d00d4443d0908240300840c09070f020b8030000f0105900444a8000f64400032411551a42c401c02c202485030708202416101810002580b1581d619810068040c01010300d041481e580c20a0011105 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 479197940 1250 479196690 479196703
    0x80702010b030709110c010912110a02060d022508031506030405101a031b091b040b03060d050f0f070510020601120f0c08010917031501180f1403 64
    0x1a20080108010660020b611a1120b2081842c4079448411807151908001e0885511454840003040034500900d00040784070460401d040c04140c0c100c105240c6014003068200700d4583c01490a86070840c100f6070030000750444101c8901c400815030070108120a1440748440f814041c0c4c070010b85900d0031694003d1821103080509016407010300038000080c07000aa89900f94010b050003056000c60f80703056080d00300c00c40704041d82c0340c0310f40205841c00442408046d04800c0040e83e00c5040c81d52600030304020000c0c100a17503212000c1c00c0204006500c035180c06107420402c01024040e441da80e507140c2614060512840c004250403000c490a030b4050200b000c200104000e50707580784260403160b0040c0d03c0d040140b00726100c06030080d40080800201e4001070140d558441c4003074250716180c900d030741c2c000d1400201c112404030507800e00e4002c2d13039400c2c0180c80c81241805c082c030940140c001c00440e419945142e00200c007401000c0042000c0c80303aa241880034046e48010703019100302e0b0a01b003518092 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 479199190 1250 479197940 479197951
    0x2070c060305150402190309030e0a030309080708030304030f0c051509030d06050f0d0201030b0d050a031d0402040e010506090103060807182316180b09040e010615110705040f0c08 79
    0x748100046c041d8504050122020300c0320606001503446130906090725040ca152400c20380c0902c1c8550084201504140c401d0203454005c811070754447d840d40d031072664920081d80c004d404030301c0104441031030511a005410080d0710901c143d230481012007450341854001900d00d41380c130303400206035202c0003140c0e403154500401c404c88110034000281400700e52041b500400290402d6100c90541d185030710760446a00515502400721641e107003060070001e20030400408203031801c20400303070740240741c1c94107009031030540c1d104c86160810341c0d00c0c010411050354083c0ca41641459110040012109024440c0400500b01c01080021114009102e4030845900c41c484402c902103004036608010015200c440c0d1100c0410b1850800344441a03040d90020030703102c03000381040200c490200d071108100307002d0104441d040d0340c140581c1c0d00c04000c00e03080e2880c13800351700b4003920000401c102d140d200c1c40c0c0345080e20304040c0583d4105600e8001040c255143ea610690085403150840302045a02000c02c03544070 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 479200440 1250 479199190 479199199
    0xc02010902010801120611130e07020a0201050d0507030b0d0b06010e010516020f1801080a14060f1501030204171e210a110604050f1b0604150302070c06030515 70
    0x100c00c0d5500281c03400c14103008000c207030010309000300c0411065500c01485070714007984568075001807180d999580c504074050f0011010900d00490040ba000040380c0351401c0d8142c4500f820401106488801020010081d900705a00c0b00c41c41042615013441003191030b401034140034554030f401d00014184442e09210a410031500700003a940d4044410a981e44c0f417941102e210310203a046100058a00012060368810961428000160154001080300c40ce61144c0e1181d41c1034141d20041c5500c940d01140c20b1107118035090001210f203125210722210b1100141001800c02d51a0860b0b0034240856002081143e84400300511810040302d5400c1c0341603120360700a2151014052508000844406449031642c0001c03540880c4140103e052569502d0800c0c22100c5615080c02d040d079a46000010b10342c1e0a014551000002007485601c0c40300444014001d940b403d0310380f044031002495980750130303001c1642c00c0c8103040000d418400c820006143d47c2d9008130315410324283c1c6141e0583c0702620944034 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 479201690 1250 479200440 479200451
    0x25020f0c12030f07052521021021020d0203010509100503030f1303080315041a010207060e03071d09070801020901091202030a0836060906210403120c0201 68
    0x9081c40041101c2d0640400450240c58000c41e1900e5480c00d003c1c940540007600f01000a0034107281403481d00b508441c1e44ca01c807034448580d005806607484101440280d08400d101d00080341040c01181c00461450000e0680c0d07107a0681110039004a1b00500c1032181c0007030700080100058544000f846800c0078404000c4006140b030140025500c0c480c5d0801e0060040000c02c004042c40200f442c1400103581010b0483c1d44d0380b402c41c80e06c5608130112000e00303200b54942064a41507440c00d080004041406030000c0c40c2540c20118180c0792480c41340c7c8002e50510075140d0101d052502c1c200c0c0910f055440e80050711090600c0d030004d5080100d207821031412a03105100c00c4d403050ba407002d811012225202004004901d003400400c0c1441b03840344c006081d034040043c52482c00c03440091407440c603e6400b603000c1901071102051000c502d04c0903c6203a409034050007815403e2800000030484c030031070310041070000e901c0380300c620301d0300081184c0c1500420300d41a008514414140590b410205051008100 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 479202940 1250 479201690 479201719
    0x2100b030705031528050106030f15050f2b0213050403020712020315012909031c021c02030307032f09060d0216060c020a0506070825020f0c 62
    0x1622841070500c0e042c1d407613031100892242d01d481c03a420101d039804184c01000c05048545c045003c0c01003842001c0c00640f92580140404900340b081140c43c01c07980100052040ca00020049145960045030b5844807a8908002d2180d21a01c04044c030600c03403450b451a1070649004000b0b034180314040c6445210304240400001960204009094803040c3d9000c6e140408540080703031803d0840200c040c000c804120011442c100d83c603050024142912010b1028002c00e81c80c646082c2c045d510400780c0550220414184c401c0000e4030303141440d038240c4111000e8850004410480740041245100581c200205100940c0da060090000184000400c1e45410040020a903008402c0307180700c912840c0007061220507561490708589a13401c10447c00d5403180010008002064038601e07080b60041e00d40381180e68410f00106d6148442c42c0c02402910142da5808004e03030390048000d001895000d2182c1d50a020001e82c6001004c0c03880700b0342d0040528080450300b01c1c1c03030050720581480c45000e00790420392 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 479204190 1250 479202940 479202943
    0xa0f111c0b070906020f0c0910050d060e1006081f02070803010b070209060f010c170435060f370203041b0b0d110d05182413020a09020a02100b03070503 67
    0x800b01e01054605148c160740d214500c1c5031100081e000340d81d00000c2c2d05c0582040c0301c66500036159180c1030009650003a40c0040000086407010300c02c100c1035400c001410ba02c000880501c4047d00300340d98802604d0002141d031703100020392098100078800d141c045030000c03c0d800e058030190350001040d9036244d80c9600b080e00181425903d800c0040440d01001c100c0000d180440040c0c400408040650300081c2e114072030351400842480540703040100191001e40c65140c40068198061054505000c425403112511030319280c7d06100c1d070380c01e400044814850500700c4620042254590540c0041c0c5906080c513107450854041a401c69a0400c0c58209001c021050380071240c82c5c070f040140010b925121146009180e014540000344281c1c82d017800c10601c1045810220300107030341142505c2c4a2100284480305c1c00d8214040c0c960004808000100300501e400382502009000800015070580e0710300741c45061340c0c40001c0980068129424542081c1c170540140c0c5000c00c42113000e803061900b0400440d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 479205440 1250 479204190 479204203
    0xc080403060203072a021c080a050f13030b061c022b06050c0a02070603060f06031107060510050310020c0312040f290106020a0f111c0b070906020f 65
    0x1d003966a001000c540c3d8030340038007400c0101025100c036002d120884140180304003000707254260300410344102125a4081c0d003107288103006610801d6281480303a4100b007200c0e9908440b0202c000c0200030401d0b40f40b2207494619640080d84203490545007890f00754213008040c01da408a1480ba03c0d003524141c001656200c201c0310440211010609082c0711829501d600004003810160030245031030706000841c00c1c0c480082804101d03039000c844c0b203181c1d240003c4007203641500c5403003c092205c174801c1c001188250858580ac00400b010b1f542088441d8031050102d640c103407154030400700d4030701d001c000600f0140a1040003003502c200450800407240700301a22032082c880d0381c901d80303603c402c0040d04010130100303d0170045821501d03080c0380205240300e0942c129000b0414010000c4010000550700788005182030703819901c40791100c0c046100e59181e07140c100004440c1c07540100c40400c1c030320800e01c10349203d69040f40a1200240c0c0c81c00e00d4100505009500d422440454024501d103800442002524 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 479206690 1250 479205440 479205443
    0x20c070501031a040203040609170c0a03350108010f0b060304061503120e01030515010f0f020f0a0f020405070c0308010e060310020c06060915010f1409100f020d0c080403 75
    0x40f0780c0c1c01401d240d82d42c4010300c0c0071059a2080c804810311043c809281d000c844082e101c1c581c8400259230062034100d10303004003e18180c840e0f0000032100002846259880e0001044920910740700f0903403071840c40d41108044003a5038a01d907100c01045959000d000704110b030b402ca02c400f000800a16130100382c03240b100400c0505001d85503960500309040d400d04160045800500034840b6080b90440181300002c00c055481c002420000420f1070781e501e10500c5510720105844150b0f10a00440040c2c5400c10003c5510040d030141c00c1c1c00100d9454244985000c10b84070344c000b000f074042503104000440c2d40150035402000091048080003e0708038103106e054550100800c010390b0f81d042c00081c40e2404540c0c0343c07261280049858820f86000055850040c241110300445544d544511000b081c4000710003580042c2c1e00b94800c1c0710007400f50065640c1c3c9070211492529003154100400c41c0b49a404890000056108882105159052000390b1701c40c40ca910700500c4c0909180c17611800d6000b070303010 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 479207940 1250 479206690 479206697
    0x6050309070e06030705040608030a1701060503061009030209130302010f1109060d02131202030105160210020903071e170105070906030b040212090706020f06060618030a0b040b07090801020c070501 87
    0x100f1840d139801c2086034010030f801042880080d4035241c8141e102c0d003000d00309001187c0b0711280000b0126081c0c0c0b03124107032040b51b80c545013142c1d48c030020445a03d038807034218000e12040c2c85000c405601c030660168420070f040d028072941d0041d240b030000d00b154440d100d610300c060f18003031030001403841000868908030401c0f503440c2d03103410340340603454028030881c81c40d42c020703214003500052380307c2a0707100403446035000700c00030083d0750381d130242703103107200014451520060700400320451480d000c9074040c090101014003117694240e00c403008507164840d814001d202c0100070b00003c1001035001e0184500c8071034083e000344441c0c1015000540750102c40d000d050149900c2c2c005c43c1d52151a154103032251040d8402c3c4204a41c1840030950f503c8144900030300d0300602440548510810001800324040c0c2800351549140c0a562120020402e40d400d2200707600d8050616002c0c0400c10b40b0440c05c0c003ea0054443c0c1ca510305015101429203080c544c00b01c004d03070b4014882c0f499074500214943e0104c40003800e = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 479209190 1250 479207940 479207969
    0x90403021f0902010e04200f041a070b090d0503040602070614040614072c03030c0604051b0a0503030d0507030b0406030507051c0f06020c0c09090c0306010605030907 73
    0xa026030070008481101c8140341c40101c100380e00c18003140c0194003464000c1e00c440c1402e0f1108028042510030819036402c80c050030b5806034200c2ca5009005140d110303190200c40c2c4c1429140c0240250340c008034041510240404280c001c10321010040450304072102000502c03240b0044031026046000081c0040d00e20790340803410005220568100c0c3d09030038034035900040f0310300c1c1a207031000040c09201801c0319880d0343c0741d0000703042c0d038040c002411b921a4410a0801090680c1d18400a410152a02c15070580401d102d04e82c1c0ea010204181d40c080c07440b1344044c060700b201400800c002ca079208860307a4860380490740104500e8401008a0380d040383c100c1c00c080b425640c2d803801a0081c08a2048258103c0d141c074000100f842004642745040e5002280c0b01844080d00c002da034a280541810094017911410a649001412590060014400510580d0074204130000068075140b01210520041d8000e4600c1120514051141a01512413824818190b0502c400803d40c0c0301c001d401845016072842 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 479210440 1250 479209190 479209193
    0xc0c06011a0d140907090204050a05060f04080d11010b0108011d0a09020303220b0a1e180b0a030b031605042003010b04050a21080702120a0501060501141204020904 72
    0x1c03078004034108407081c000c2c80200708010030000800c41e007410041c005e95a020503e507079940211812288001c2c14041410300b00340400c12140d101e40d00c1122040400c01001524010a00c0f0610280109807234550004006041050942d10940219030402c0080700061000201d9840480c000510b40c0c10411529510346103218001d00b241d00c40a9403603c4003003030280070444d44480d6000b401d554900c40300642d558540b41420f29001c1d0308111000720b074522040902d180700e42c9a460754880c034180341242201301491080d000a1049411611007c00c001680360107054140c0a40000d490040c0d000708404e40740ca816494481c41e480c02014815604d60040c281841e500c01b01d12011142402240341d92541e4030400244030350f00074271400f4000c807003c0f880003420f0815001300c400d100440c0800409401c02e40d40d03401d0510761254000b2a848441480741400482042068032941032052000040300c2e400e00001610000942d0300c40c03000a04100b00802c45214030310901c42e00142c1c10f54400026895a = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 479211690 1250 479210440 479210489
    0x8010803030f040f0c031101030606110a0201300212060d020a03110103020c010e070521030f030a0e030a0906021209060d02090d02090a090c23010c02030f0f01060e0c0c0601 76
    0x103841c0090820030107071741c0210900001903040640660240c80421036140d4512042c1c1e0f01c2c0700100b0011307040c3e8006201c0080594020000710450f46c8400c0c11340c1e00c10701e0035000103c41c102e00c0e42d071158881a6003c07a11000f0815203030012a0081e00440307400b41040415400942d9111103400010030000915143c400315900a406480d410303650f000003801008901003100755210a94441d03540b10302d124483c884c04a505682c0c01da140115004080e40c80c00d02600403003141c0d640003918a41c00a039071103810b08914501800600a000440c1c4c1d5510001c51406500070b1402ca01010221440c1c0bd007080310708916035400d01201c079108141c00016841e420007200158403201d01ea880030f504501c07800c04005a2074140d91042814506c1860300c5605c45032111420403820450880204103030300f419440301041e60160318081701440c4000c00704c42c420090948454101025201000d1050303445031411f10904801c403002c0c41e409060100310905049c40d1740d07a11079840c0c4040c410144052020035150760701045 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 479212940 1250 479211690 479211713
    0x40b01060905100e011b060509070b0307080408130b04080313050a08071202061b0f0d0302090108070c050a0210050406081303140a03020403080a0806030c0102011a10200604020a0608010803030f04 86
    0x72414440e84880051f0706140d0050300c012034501640340502400810060304405c02c0d28010584d59031900843d42d0340e503440d041c0070f5100004644030780014000c009440490391000f07201400c5014042c5803905417402c228400260705400c094403c403811801803228080c0090124212081405c0340c0c0c0650302c96001054442c0700e10701030402c0450305050b0400f070580000540411000d2207900300c445840e0201011000c902450b4040744c00a0146804200182d21030310b48600514040c40a592995041c0c1e40010756840ca01014040468008181040065040220694001c01e050f0039100000310356a401072120041a00c014003c030000f081891413603200c0d9060790051039011020a0f942c029040c005030008008443c2a0301c20b01c41d00e410040c0320b52060082403600e80e280c4205403100100315040006008107004003d00304015040c2c02102c507160700420400c484084006805076040c24014801101d941e50052402d0184880042050050000c00c40c0d5220301504040c1450f0340303407890400c20501 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 479214190 1250 479212940 479212967
    0x91103070602071701020a0e04090201050d0c080603070f0b040603050910020d0207060b180106120b0303040f0e01050111030a0c02131401170106030c030609020316030803040b01060905100e01 84
    0x4911040858602c1d0001000015148000322010303c403820307241203600b40d120b00d01030b501c00240307140681030003814240c114401040c4141001800e00c080000c0b5030f01103030f4110041000068294040c442e1078102800294040c21240000404d03860410901140c144030700d1050104166440c0d0011750814414003580c2c000d945800350079982c54000300c8400001c1e42040b80240c40242c6068005402860310401201c01d200d082151209160b1078103c0c140c034a6408071108034010380d12201200041e6070184000e00142c501001003588450500c0c8680030910416084603040c0903560001c031126140006c1940c60b2080c180c40d0441c61262940b0100b40e4410810009210340c505019181401c941040c0d01d1606861000007507081d051510414182030750300511000d0801b9031b800e0700900c04201c942e0030000c000d90001d070444099000c48007180c0c60280080c1d101b0703186c10702c0202c2403104018410760504e00600841c94100f2789503043c04009400d0028111110082c080b81c1d80488505901035081d010009 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 479215440 1250 479214190 479214193
    0xf010c0b0c030411041a10260f090a08070f03020703060c200d050904020711090f01140103021213050124030c050406030314030903120103081804110d091103 69
    0x904025044003000d410907142240c0c000b188083e01901c6042510035410154400b4606030342400108040c000014003080c03542023000f101280504000000c0a0402880014403588035903500d402e0101c1d080c9888094180c140b01c0c0c00c0750b0f041901003903000d81954038a0360005540f1040301010b00d0140d287c01e40070742c4010301003410610041c00c9560040150113034a13100040e61007101c0c11252510f40c642d9050f40d600344c04540705015140560401d54003901c12184100030300c4000c1c1c0402c40014288190484172825088003001c0107008203081059401b030161002c0c2000d5007001d000030324041c0d040c01c1c0200500405c0d0344041101090200c01d4102810320380883c1003070078006180400724000f49106010035150711050540006503030134030384644c2d011660140e40d5180322210801d018121a44080c024920620003845000c00c021000040503008600c21030215a0b0350a02c1c04c41600707030360510040b0030b03c11481d02c0300341201142900200c41218000c0e040008003199245000507030039400e0320300d03a40c26 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 479216690 1250 479215440 479215463
    0x5040b0309010204050310060314070620010b0402160312110a0f0c141c02070e06090c04080607020604031b020312090d0b010b090306010f1202100507060f05040b01170303060f010c 79
    0x30411f50f4440b0b010340e8000c02d0280d00c1c071005000d4143d0f8510240c41000000342c854070503030086286084459280003180c0d4000304030381780250001400c0e0b80010202c5140080d91840f04030825070052101140d4560303059043c000c5c00d24051030416070303004602460090042a21050010300e00c100030101840390300c03010b41c0291001100460350f8940e601c250030ad00305172090350290882400080c1c808121a2a03500d601c0c0d040ea991418009800000f501c100303146d880c01d10011662a001340165480744006a0092200d407625041c0207043d620b68200850444801c81c0551026807404111500d00e504860302e0f20750341c0c01845002c0382051055680103841c4542c0302c800466002d04c0d42c2c0040590200c1102120840e9072030300c2041c264480c0c5440f41070b44043c81061a0001810300d180e038418400034508140707061100d01d848540698100c10001c071211669101000100081c00c800b10b4058200f9036100125000c460f1069681d030312002e8001e601c200402094240c95a119107503200c980c0ba8455401c242 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 479217940 1250 479216690 479216713
    0x80c0d170306180a1b110601120503070b0a020c16030803060f2202180612070e18011502121306030b0f030f0d0905010e0906090a1418010b03070605040b03090102040503 74
    0xc1030700740880788245c0000105024210710a40a142c0800d0800340070700916413030450700750083c0300f4101c0110f400c1d02050080801003650a012980308d0480702c00c0240c0c0d1a11420252420400500c00881694900100c00c3c404280500b0a0340c0e441a4150340540c2d540804500003503806403103021200d6040c01015180c0010311098000d04040b480032090314486810050402c4028022801001000f2800400141c29248030300f01505400c103000e80202c2480b0103000360134210403000d03046820f5207038440e6540e400d0550304002001907413601c06001410000c0c440109406005039108550070075440395040215541c0d0310080e954104001401c540500c03071004003494541c002001c0c0740002c580c4c0e6840020f02ca5008410001c2c21960003042003c0035660401040040c15000d89170030402c81d41d4001f418000140c507024a40100d40780d412142448921407a11425140d800f00c4050180d00910000c012580d004000d540607680d002001589960b1081d1300c680c024010b40d40540d41c1031241d851940d0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 479219190 1250 479217940 479217961
    0x306032009060901030f0803192a0810090c11010615111506010f0c12020f1e070308070f05031c060506090f131107050601080c0d17030618 61
    0xa59580c81516030366050b980307010030042000d00901c8040c2c4104292111000000c03842c1c801568844400c00516800542030903020703081754200d141403540700410b186410000c2a060300e900c80000d6451074490158078210881d41c0d881d070110f206001106803100d540d448098026181500500401d80c001c10007a41d80c1c0c1c908228a034000b80d481d801088142040c10000c1c8000f00ba002d07a1800e114228003e2031b154140111140451a0702060400140c4070f40a030000700d04210302c04040020f41d00810a0207808601c050a05e05100300071010114403001c07082941c4d4003c140d010807280c01800107a180c07a414180404800c80022000300140400644803da20110320040200004203500800806480e2002c0c00f0061103241455503000907209050a00e5290012001d080c0c07800c0d02c2400b0910b4465861914400c1d002900100c8440c0c00030700050009550400c00070034020380481d04000304090030340710300c001507400390380300a0b84000000004007076490b456440801400c031200046001e1500d0207955 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 479220440 1250 479219190 479219243
    0x507090b03031204120f050f0a0c080d0510050f0a03030c08030a1b0903030909021c05060a21060c02060705120c090d03120b3106030b090f060c0403150507030603 71
    0x364049011050303081ba10714800d2080d503034015100309040e440c0503164078003510700ca04c0305202100d0212041112825121250242e00d008003031890300706041600b8441002002008844818084d0061403403c001203988401c43e4540c00360040c0049682e601d6004250b00030b4652011104000c825118405000e943d00511400c1180d02a6640000d00764440340124168400c0010b1031a603080701d20361025854050b5800907810200040c6000f0400ba034400d100720030b10a082020380b403407400e01c0503600103010b2180030303410243c600c03880500f207545021080500240074400d440d03a0910800c0c00000c081c48481c0c01140e036500002481c580c40c03176030b540c0ba00915541d0019403500255041640c1c6920354148074502422592113079091681c0c01e07030788150781104007084200d81411147c50309000070200d03400e911480c0c0566000000750000310b074042820f61808402138a00380110800f0001000070606e00544109003001494020540c0d4544260490152502d0303000504850f020403a000281c1d034004040 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 479221690 1250 479220440 479220473
    0x150c04091a0d0c030519200a21030e1c12090504051602010c030509030d180812040c12170a020f0607030c09050603060a0902090303070c0914060301090507090b03031204 74
    0x311b030005500000c072800034021110f002420380c070070601c007415030030985c19048614003006480c01c041581c0e180d9203601c0907858092520098960105481c050591100e2612010300f0180c688a440d583c402444e1081c2c4620840c0181005e40030694040d50303a442294507900402c4011720501c05030074000940810001404201409586000c07071006503d0300070f000307d501c1211b110000d50f040c100722010100141c46440800520a118054071400017414500500034010012100000902c1d06160040d10074286070060403410080d20b000d4000241e40720a410303c2c0c2c07180c03e14000d072503514400c0d0980c9072480c00171149405010303140812045690603031003201d1400c455600c803c0a56a1503060128034403003624482d41046a0010901c964a0a40c00922510001404981c0ba003d120b880c2d0580102c41074000c3c01d44103888500325000c40500141039030300300340c0440080001080d142e403955a25111482502000d0b9210806400c2560381401074640d900d0040c41c0e00e161901c0c040c540301001103502e100 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 479222940 1250 479221690 479221693
    0x7052208011109031b0a03080d1a030c01091707030503040806040201091703030403050706060b032e0506030f07051603050a02011b170612030703120e0c03060c0d020904020412020102150c04091a0d0c0305 89
    0xf2f480c00090083c112441038403014045801c0001c516041c0202030080c450314440c0e8400040000c0041009100820100000d801c56082ca0710004103c0071056020180d190300c125555191880048200c90700264541001a40c41c0d07154030340000900a140e01c0708030103010100421482810306401048101000c003440345c00100c260072041c070882003030b000c1c60380c00450503c0051a00d9212074422608281d6074100f0300d082c6100964942042c41460a0840025901003000312009409006070a840c0361b124102050f68007001500424504040d80407071078a440e080b02140c850f4aa480c40d2241c0b0f907040d00c064a65586a504001c0c01600b40000505003c5141441c13030540002c002c140c0c4980204001c015010303544a94030804000e421104c4010040c1d80e0810100250740d03564801080282030103008010700300e04c18000a806c009410502c0703220040b040d802c20480261190480703060742c070361f034400140405180c8000740510a440e400c40760000c9500319100705001c0d405209800b164440d00 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 479224190 1250 479222940 479222981
    0x6040b01050301020c0304050d06140c0d0c080c0703120b03070906030b150f120c09010f080118030f0c0f06090b090f0a03050406030507052208011109031b0a03080d 72
    0x1c103040c204d200c1e100d4195503503002440705006524002c07172130702e42c1c540c01100042005410040c60414103c03050b581020300010002e034003246a08207014072000d044507420100d506180011020050b449245001001c002c880619064030115651000c003403c0f50140482d26080d848a0f0101300801d2140825140c000e400b00000b044c000d402617200b0240800036090300140c3d5244028008591034400f038030000b500078050645001c2d01e4000025000313180ca00f4242010b01e00d403048041c21074400320340c07582d45241c007a4040804260000d107100d00362410341c60000210071890034500c280e0030701543c006001e9428008400280580c80c00094043d91104080e2080f28103074184440d0f990324600001004030b80300b8082000b507a4006d1b032100f80d1000141c18443e242c0661046c07900070b5800c1e03443c5504103404101c1d1003800160400d108800d0200712503600b40d45400c6900c00000c1e1380c1e14040d54080300103480000740300ea03540c07207004500380199408540181c030740000d03003c102c010b01450315074590850a0340 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 479225440 1250 479224190 479224199
    0x411010302131401270504110d230a1404080309010f05040507061407030905040908041716151710171510051305090f0d030b09061219020301090b0906040b01 69
    0x514101170030996a0800c540c0c040e240c281800068041501d0451034403000b4854040581c0e02400340382c904d00d0305c296002500a9a101d030048048601038106c41c0400d00d0850050101c908218a282e00986c000c8004c50b203035501d00717407024054070740081d0700301d100d5040409010812000050030b100359103d40c0c03501410b010a401e00030446004134031010700040c042e00720070402d07420142e00c105c0c0c00d14001c60b060340c541a01c41444c01460501610800415070145014008800c02400c0c010050105201400600407210700c008000400e40c0c5c040880c00003661002c114100903845081008040300034081e11010149401140c6034409224840341001061001494030310b900f090308401e4800c01003403982c9116205548800500005000364003a2240d11000c948101c0200034032103001500343d82c0814005408014800382510103040f5902030072812042050302000440c4090801c1d1506d91020380304c10f414000070b800f41c401510301800d070083d020203001581c0300100f071807032169000361002c44469903103 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 479226690 1250 479225440 479225477
    0x8190503010314150c0d0902040221160f1206030c03030f0801090b13020304020102010f02040f180507021c020703060603121b2a15030207021906080411010302131401 73
    0x144d08218a160f0302c00c001440c3d40006005080c03040c1c014180016658960f9011074226800552004d0b0141c028041c8002c16009003010140c0c80341150503000320700302c0030480284c4542c44102e806001d10200421759004035696074801401903401050010119960707040191500025804100c0007a001d0000030a07041d5841c0644c071071001c0041e01c21352080c100c400301c09000703420241040381107548556000107200a94009000601260a00800c15500d1f0150500c0e94162020307003000c1c50781c104020814415000700c1c00500d5290001e02d452110960b210049081c0002500000c2c90305160080c00700a00816250190302c040840d21071605000750341a4404166001c44002405119454032000c440008036a501c0e48000b151656010020388a550780385c811120100400e002035400300307070341c4258544080d098410890a620b03070034003d41410402041c001c030050014011403c3c2224200d02e6900c203074125941444000c4200e20141d880f06e4690b030322911000361407400104500c0740007051404 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 479227940 1250 479226690 479226703
    0xb0907150305040305090a0f060f0215040605040c21020f300f0703200604120206280905031c09180213090f23040201080408190503010314 61
    0x140c4644003000c8044500450281c20700600c201d042240c14003003644a0f0b1160034050020b0311015084600c0142402802000e02c440c03020301d00e045602400c002010048440c020f25007194000e080442c2956a41c10030f64075125644d42700108134001c4034415039442e0303c2e1a0a8203040342c4211688003402a140013008050b01440130703c2c0c001750301e2141c40c943c101101c414510b901030072001c1c2507030b510701c2224080ea810801030f03510655114042d10080000203061030355624481c403003180c0030350074a81800c0c200000b40c959918000e004010008a582d526416089150701d1095010749084888034030103002402440c0c28441d09001c9c0c49140311f00144039030403207140700e00d8117038a940d000300440c5014421907502c7c900c3e6200400507a8204602903e0f1050340d100240503040b1868003058210442e03920070304035007200c0c0e019a00030070340901506100100c006040e812070740928000312541c4544c1040450f5104010501081015845010151ba508035021314100ca006025010001003030700c041c66141e10 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 479229190 1250 479227940 479227949
    0x110601090e0c130e1006031214160c0302120c030d053c040305210403021c0606050603090a0519030903230624120c04090f02060d090b0907 61
    0x402c01280c0c075406003000201254000c0355500d022407808202582c06040c5601680e91181c4d1684500051050003420300c00454003501900e0480200903a440c0d250501d4010700904090549505c04002c080c000482c50010180d0f4000f02050b203c030140519440d600d00811444034024002c0c0e1240201c40b9000e04103942440c0c500c07080103d4041d00011064900786000d10008115000602c0300c40d0444510714081c0001d50703c600700404180000040001c801d2904818107801c80a080000f440107844a44001c8800a0000d4980301c0000301450410b02812243d0030503178210702c002c0f08105854200003485030003a405002130b0f4018203d01c89044122074041e0201801150130300705c0410008482c25801124201c0c11031710074018540207000c6500f050001c1e505010003500020310464001c1e50500032180d0a1021942c881c81c1c2111008200d80fa04500c4140622856690245100b48600e40d0449000e16a006180ca03640c1c4089005110003000ca058090300c8441c604c600003110b2090000d00315041d01c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 479230440 1250 479229190 479229193
    0xd09030f1d061b060f09060c040b04091e0c0915031503030806010c0b01030303090b0f190c0e030114100b03010f03060209010e0d0c1703090607260406110601090e 71
    0x112041e024030060b81c0c8914960503c00092408100c0701640510045014805000081e0b0641c102030f01442c0c90401c0260520804c90410002000508050812182142d40b010004101d5a11310040c050414400481c0301406a060603d0251010781c400016000d98804c02105041c03d2005281241282c03569940d003c2d52007020b030828404a401801c01a90041c0d0500d481c00c04102c00d0b55402c0510704080e4012400302c2d89544481c020801c00c000140d51089200e181c0050503c0c20145040381c072107000c18090000c80e500c074112948503100360305c00e1000020190007400a04441e07001c0e10000c5130100c481180701088040007140070001c08089034103d400240ca5500c1090442d154800294002d0031024148424241c0650103915101c403031101460180c80d4a810480c07600c00440b41c21345c02500781a03160342080140c09070781d1b41c1c0c102c1940d10a5400c45e01d000701010000d0000200a101d00c0700c6102c0b40c3e0b00c04a17000030324584c00641d580004102c1c80942d040c0d40d07a01d184443c182c0d911440c035071900c0e = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 479231690 1250 479230440 479230487
    0x1150e2b0537061e020c010c08270f1b0a08010b01050d0b0f09040b0609090102160b0603030f04080d030c0203070201080105040e10020d09020315012105010608030d09030f 75
    0x1940d19034480c00c03080780110f02c00a000034080c8400103c119034100d1a000d00c03900803486a02d603943c00e1003123400c0031656042040003403820012141a080720203441180d081041440304c0003076103040015115009800d0200c0d4464041c150400c88042d880040d1070b07120f0031503079402007401101809143c06400d01a100c250a00e640e000c3c007507014254480b8010f41080410581c00c11940c1e5554243d030040d4050036800040b03040c2101070019188004054070010707030042100c40c882001001c2c090102ca500092002d10175203d140010f07003180b05a007400300c0030030310104012a022601040130070408500340c070100004411801d00340c7c9c607400f9042c40640801c49960040010341440c3c2c0180404036021401d40d00c01c0c0b10848a11812a0004510b0b00d0980e40d503080024114101080721801c805096043c061564bc5050f4180b00904110140c03440328001c0c403c101c004000094010001400004040e1703070300c8828044603a001803140d8282a8001482500f8000b001400f0f064007400c102c2488651480 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 479232940 1250 479231690 479231773
    0x503030106080a1b050a021005040804051003090804060e01020d03050f0a0e03090a0308041706041115070b01080606090708070c060e0a0b0a0510050901150e2b05 71
    0x100000c008005003c055290381d035002c1c07649488407001c1400c60300c1e0f4940745c1c0c54030404003000780f41a04510007002280e20740010f00c00458064020740d41158003c69100c01c404c60500d208030094000701000030f1520101240c0415440e8101c0c040c101010020382c00c5a107882841c00e07088083d20025100c1d803174000002d0f0003098000055402008041c02e80508170f919160305280820390522059000f03075000761307000c14140000c07600031403446003a4200c04018443d509241e02e81c00c1c1c0c0400c18603a11881600c0030100202d240bd4814291905660010030421066035100121515048226511807003000c1d91307000180410300900c03506000b403106544180d4074011695900c0010141c4650b941d41c90711a030411040001c59034000c1ca44a175a0b0b03e2008502c50a00440700c846500c25600100e1050541e400140038040244018101061240c9003c40381981e0307030404111301d01d40c3c42000c00000308200d0915911401c5142100d03151038414001c46000182801240c4190451420401988001c0f1400c040 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 479234190 1250 479232940 479232947
    0x31401200d051005121c03090c140118060f1214041106040b0c0705030c060f310602010203040b150f0904080c0106061205011e03021003110309031b07030503030106 72
    0x15032003c000c1070018109500c0d14000380d12074165130301050107507001405258001e00c0c0317014940d22200041c1400d01c0542403da44050003042980610394240b40c3d103014a103150303031040503e00300942c08080e0141450f40c5910000700f80c3e03284100e600c4003040e20a82602c40710100b903c64000c820f149005843c08035103035665501140d480786505275500c01d0050001041c02044134000740000c02442008101c01403601042c035007454040c504040c03090304e0900656203204805011034172000180141c00c44180b04503114508584071250803c05e00c0c1503112008220241c0550055004a00070803002c07a10742e85152005601d00f982e04070498008185a035010320038104407200d00d07003040c800e00809041490500c4003508442295018100084000052032100da04910840340901a08504140034418800d2001100c11443c0310007030155441d608401d0342c00c0d00c2780d0310803680180f104520301d90ba41072a0f90f00d650340c0d400407001c00440e003503042c1e81d80150000000c3d01c00c084030b0340f0201840c1035a00c4c2c141d094 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 479235440 1250 479234190 479234201
    0x50619080612031803060a061a1c0207291605310e071103160510050414010b010203041a070c120c090b06070203070902031b0301031401200d 62
    0x45810a4542044115162061004e03040d954000e00805081000b80010503150200203090060400e02c0c042051000c0040d401800c4d03034100003850500d03540c100303007080c458034110101c80c4104c1e81440462038204000038880702100c610b8807a0f290200040083c803050400001c10b8840648031400710011012450191018011a04200d0f070b44072503000504a0000e02c40d2440d0300c140c0251618644c0501007681090034094000c401444c20001041c0b508643c1030b0f592046240800c2804640c0070100c042040402c0b00c010441e01000c01030040c3d040501d030410443c08011a07100c0c007542000a0180c4030352002043e10304480b500307201c3c41030031160710001c1d812940c80b03244140c0ea2848000c0001c9a481014004102007501c9035140300361162410385600d04994104a190b44102c40c208862809070390300041d41c50903580d110100507580c2c0ca44039600a00041c440110340a9a00040000070a2016210f24480c2900d500e4000f03101c00300740c00080005245503220717500001031040c0480750003007036030794000c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 479236690 1250 479235440 479235451
    0xf0a083109051e0405010203070215100513110c0109020f03010c09260d052107051207031506050c0f06010e040f080d1109010f021c14041a0a02010605061908 69
    0xa102402c0c24800f041d1124203c1e0705a40300d071b400000340b01a0950401950591800c1d8124444072800c00d042c5a120b04005407148911448034001c1961458103640d01960400000001d40c0d5500e0901c612003a002e0102410164401c1c22a207040c903a6505042c0210980c903034840c2d03150b04289003070100f101076070b071660a02c40c0001100401d0b06288550308101d42d40160400d40c131401d031500706205030300034004013007507100c00e0320a40c02d03050088807508001076403000c0c0344000c003c809940c0c488404800400c4204441c4c01e0f6411824000a42c0c1c2d500440202400c02c06d003070a036440050462101036803041c0a21900c0080e208910026002c260500c85a000d5a4861084c0529000c00c004007a07050703a2030080301e500000c0000035a10700c1e96800c482c80329480101400507102906081c600048942c035002c418200f4840000b00042c180301c403001c00c0714050003095810001403c24500c1d04190b5800843d40b100c050340ca0000046080c1c6003110035209202030039007001800011442c1c0032528018007508 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 479237940 1250 479236690 479236711
    0x102070f050121150e010902070206070609021f0c020103050f07020a030c0c05031501080c0d200f06030405070e070527131b020709090b15030f0a08310905 68
    0xc10b0b00100e00f841c010b00c43d4640d04e00a81000719410610b80300108441039100c420803c4c0704104250058807444259000960041000038086901d8004903207120074860100c1d62000100880046050f00011075200c1d85000b81d81c1040107075148007400b5a04001901c04c0405640400142800039100b000920310300341c41012041c0070180d44e08082440c01445001032800529803c0042c00720200800c00c03541d0843d02101c521003154016110041c103400704610306001b0400f070178010000d54403020340350759411001801151781c0c0c0c580350a10365244ea68600400c2402c03504d03030020600440c400c106544d40703400ea02d41002c030622004000c0d003410802041c405a04030318444281c2c50041c102c0d100d100403104036200075051960015000900303000d6107410440040b0f26018140e00414841e0b00510b5001e085000180a200c80303140c00a460013001c26200340c454071801114508111100026250098800e01c41a0990071600e000703200d03001003103004440120b24403008209036506500410740000d034000 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 479239190 1250 479237940 479237987
    0xb04051003020f0d0c08011a03060f06040b0418080a18140919150303030f0c0c150b12010b091503100507030e0a080702030d0302030118090203011503060e07050102070f0501 76
    0x10396002d02c00c4586d900c11855030b551000820001216200f440341480c1d8110050040e91916a03514010700c0d80c05410703103000702d5881c0600400703503c480c1d1040100c03504004408a0205d409c1c9011903041d031141d42c90314001040360303c40c5150481285440710585051800003030055400e40240000703010014032809203201e6800c04110359202d01c1c4615481d000da0003030181541411800c000d0f06a036403001940c00c046103004c0c0200101540224003a00003580824868180c09251a0100203049106c0002c0e60180c0540d04030341030010150f00506d058001542c241159585e10f80c01d00b60307003554040c01c064140e08a01e0001e60008604e620150744107250307090000e0800d0707400c2012854030107050740450f0045030020300c400561504001010f41400245000e51856040269000c2040c007a4100e400c0001e8842c0c64036005c540e001c0d00004168001c1d01010340c661030b0343c1d081420160a241c009480b560144100106241d4808140201951000050010b070b0f985408011140fa01c10305845105240440 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 479240440 1250 479239190 479239193
    0x5090d050304080910020a050601140f130e0102030709150311070308040f05060106050a080a0501030c0509040c03080d050103060f0b011b08040b0309070509090f0a022215090b04051003020f0d 84
    0xc842c81780d0001c0c6aa008045541c0b107450458903207141a00071900300001c1d020690340c0c0e95a0f041c1c511104c044140c8020520700b4141032508050000050f000242c0e500100c104050143c1c8001c40303c04461100001d4034001504003400c0c2c04480809801010b5103004101090119005100301e0740c10030710848103a100d43c01e1946900342000d000380c01c04000100001650469681e1007289031350082400b01c010000c651440d610611040c000e8406e107400b07401540001410302c80113400752001103402022036070f6140110781a2100900003400216045442c043d41d403110f81d00c0c4c6200356a200307070301a16100c0c03625082c01101c510611496904a500005c108000300d42d403c22080554080d1038480e008106031807c21040250356080101101415441a40103c0d038281000440c19104c4e60151841e024504495500aa1007400d04806503091400c041c45540344c04001400042111111101000001d040c40e08000544002b95000010700807820400e1015142040324924000401026120306604e207 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 479241690 1250 479240440 479240449
    0x403031d0904050f0f300d020703090e0c03060f040b2706010f0f020a030e0f030a0c0509070306050337050d0909021218070803040b13050405090d0503040809 69
    0x80314122060f42001c0011000204100410503c903448417001d00840c00744148072105c1c50095040341403005a0807096800c4c44c170541802c0303850200e00680150350312501810007070031002c0030b0701c698000c1e001340800041c107505030801a0ba000c0c144c010302c00e020810550702008090190008240c1d80b02d8004402000c0c184000f544909039103140c3c052907020752030400005443c519840807801c0900440c0003500c1904c6034041040540703154582000d0000c018844042020b2004030594640c06218100d6040309101d0340e010f580007100c0e400c56484a02d81e4a0380b5044094500c1880307541d8056200418941e01600c0d030866050780d425040700c40f040020300704442042540c1070f0328010340d00ba0304816040c008a6a0041d50b1310003a1112100c107501c0d0035614031280c040d0020044c04000554030646021003082c02c1803162030014500141180c3c0c4407500e5244c075507001c0c0d0000c1c07811403050342c0983c030000c0d103401c090054070f204400400c041c1c480d1050302e00f420f0724141d1009208854020b070403c00800303179545 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 479242940 1250 479241690 479241709
    0x5061602040209330306030d03090c031703040507051c060e010906050c040e06011e0305060102070b0a0e190602060f04111f020c01030e2104090609090203120f0403031d 74
    0x4c1e0031039020f54501c440d031960b03c140c1c128003007a1060326000300100819510006045514a5014a8005500e2055061100d4010b030799400040500c10b0083c0380c1480310941e07030f014500540c06102a1030589560704100404e00d10010804075501c2d6103455140040f410a5004000f80003009002041103007196803000c2c119002150409414100800c0c184482e880c024441607001c1c0c820700703101d8805220b240380e50502400c410901e1040640382c40000c0d10591083c440c102c0104000310b0703e01d4403240499005005134038003502a40c092801e10300c01048804c0c207c407140044804030f4002d00038603100c21903841002030b8010001d95498050181001950304e5848204c001d07030344203520b8482691800100281442c41101c0400e040500300b5048025482d0041207040500704503503000041038071001070304030288c0034a50041c1e0200d4a080000550864280c000d03111080c4210b01349c58140b4800c0f8403a0310075014400c02440600310a0005200090186603051440c00c3c2850600c1c00303030110314001440c140d1 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 479244190 1250 479242940 479242969
    0xf081b0c06090d0f0201092424050f01050708030408030603120a02060f0f040b0f19061e060203070c050d031b262805092e0905061602040209 62
    0x6100180c990f510760780c0a00c6114611000c3e1009010424140e01c84180015040c0100b02c03c8840000c440013000300144d01c030a00301d40c105d50110007082d5100080c1d48403000c07144200ba0054031b0b00b0806088561080c1c0468207411307400049a403d545403070322644c54541005000541500c00e80c600740750440400d030301900b42145140e0082543e4681142e2113170300b503040070703145a1280c0308003400d1000103500004401e501c0403001d9000700722956a80d41761540c600680c01d41d60034151621300041040080740e060b1510130050030030140301c003a5031410126503e00c15544003a010000c004424090f51170003110000a09002c1c0c9880c2c01482002c000e90310784041c00340003c5922501250341e64082d80381036006c0503105810014120b04002012802410611007072a00440818010030103d0407507000360b05680b5001e0018103080d80c06100341c141c008169040342c101703401071889820f442c45020b1103011303440183d402c05080181080c0704e0008a04103108001d5040381d0042d001d00c4030103016106d084030001c103803 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 479245440 1250 479244190 479244193
    0x80105040b0d230c1f0912020f0f0114070605040606080a0c0e061302030108060711011a010302030c0d06180e0d09060f12152301170903121602010b010f081b0c0609 72
    0x140300642018103086280e07844031081c0800042e54502680d2272040e103010302c0006407121021058a0070040304c1c0d40c220321861207005800400d025060003102e034800e6225511450040240c55202c4000c2540c4102100006040c141c20041c10f004046600c0c44241e0455009484900d080c00c020744050180d800980100741c5c0f41d4800c0b4108200130354411400c295440c500d0000f00000401011480322204610310300720b06054001011a407171604180c1207402c0d0785200ca00400001d601c0f11015042c810584c5c0c103070402030303041401202c8045000705029901106980700c1103c46c0d850071005940e02449412200b05021211070316402c0c210540c080c86005510780c00002d10f000e8200001c48800110b070090b4103e03140c2c0d06034510780182c2d80029085004180343e80d00c0801603990302681c00c8c1385104203003080343d031810000c041c46420101031142ca030034408107400074040540008011180004080e81050002c1e41d400c020a0001d10799a4852a2000d01100c0c1585032020006031507151040a54504406 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 479246690 1250 479245440 479245489
    0xa020102040b1612080f0a200d0209011206050609040902040e0f061009060b09190b12010e0a0e0705040b0d0b0112031106010810111207080105040b0d230c 68
    0x30800d0710703510b541c140800c50070030781031700e04100402c2e5182c40801010040220340e511307401c88007031a14004548540028001c42030755940c1c0f4030f03600e20183d0080405140410014065501841c8407030241d031082c2c40020307001ca410540c3d01c000b0000540400070050f41c010382d0720103a886d20060140301c0c41449001c5070005201c07a041175003d07882c52a402e80d001008880c83c0c08024020140500d003290070060301100c13260207005002c110081405499840000b00a90000d00142003070038090301d40d8126a24001d60741c265564004242080c1d4550700d40790940da4100c0f8106000600d0598040031800c0d0001d0004105a0303410383d284002c10b4030a802811811030030100c07031030400d5400340c4c1d65040e00307a003039026040951500710456a1175141c1012040d40703a80743d680000f00524001c0588180c6031a80344a51541d0230200c1d030150140200303000340d07400f0780e0a14070021290700780300aa00305040d03440441005400302c800d51184c0101143c6001c0c42441c02601c03070000c43e41d80c902c0d410180c1c01d00000f003100711 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 479247940 1250 479246690 479246693
    0x2120412110f0615011404091a0d02060d27050c0310060305061305210309010608070b040303080a090609120806090f060d060b04050c0c1218060a020102040b16 70
    0x514400c0c00c040702865400710380300d00d05005011038460b800011501c10401c1031006400140c072800034411a04070074190100300001d02c1a00380e040b0784402d07845045098082d002d4241071003519101d0f402c0c0030303412103020030000147c004280d110198900c1b0110305001c49941110b2010058458038005643c07990004040c40207a16082c00071039040030034140d041001900d1552450b40311080140f0315803410694241800a012040c00715194254400d02d00100d80c2d00d00180a0140e9081a0340c140d0b01503180003404215103600062043c15104200710850500349503550803a5003010080080242c60303200e418480014115000d0640c005100301080c420080d01080c0042050800400c1140704e049140140074035500e032420801c1c1c01030f005030f49003403902d0118141000a003002e04d0f80fa98120386000100b02140300c565028282100c0303200e017036541004020501184500400d07001440f245101c0b60180c1c11450203c000307010029941c000903080030340d100003250083d00007641611800445044050 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 479249190 1250 479247940 479247947
    0x30e19020102010f0e15070c020303070609050f1605120c0405010803120f04020109090b03011409070f091109010c05070305070f050a050108070806092206021e0a0210090602120412 79
    0x1100854607413410810415035203451a50740c20b05110110384041040045100640304510021041d90007030300f16940c98402e40b4082000748000c2009807801c0c0a154580d82e01c42d0b1000c0340c01140642c40072004181035042c2002c004034036040c02c00e0142c0ea4451014018000d407514001e0364028245074002e5a100c5025001758800c00b48010552680d10740c00d8010440140c3e0001c0c5543c041d80d950705400651080d0a00c04240100004105406004803175001c200001100081d60030a86d0306240000a81d65620140c41040c3d89014150520b80d0605021110301c951007195401642406a01200d520315900e0300c0c0c035400d1040c0b80d0800b400c03502c400c80d0140241c3c02c00984150007001c080c0781000e60b41c42d1005e8014012180070b00860722440e0a5030116855500302c040d11001c0203210100b5486140c02c07440c01034008c2d4071060205206028040c0c001c0308420074481070301c160811603005040390303040380341401e4024601e0010403540e10341d0a1002c806020b00016540d4455882000d40d800b00300710948018 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 479250440 1250 479249190 479249201
    0x804050102070510020706050a0309060e101a01080c09063709030209070c080c12030a0507020607091208190201090507090203060607060209040e0f21031308030601030e1902010201 79
    0x304d00664070031000c0c1310034550001c2c0c1081114075900d0116110707001040100c01802d0f5411001d022036082c800845481240810a500b240694040410220072110140b076030403041c0e00c0c2620301041c2c0340f60000d503107540468000d0088450040c84a490944003039020245035040a1131218010a6400d554030008142384820304075088608061540d5840c5034002207003a20000c10510070003191041007010400c0c800c0507625454241c2050324400288115110b489410480b0920400390030700010510040c00421000c0c0940980d40c0e98007000b604194030410036010400c1e0440c2c800070204480807641040c010540242071039503001203030040e05410024504561130300000c401d01e10400c14040b055449208480c00d0f82e900c80409611580844009001080c03812820310715030240800825104102040c0c0011202680c16a10390314901c11100c0c0b0b40354001211140c00b5881400f480a0114900c48003031580440c0524010031400100d11000f410041c0c069420170346100c183c504036085680a0042 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 479251690 1250 479250440 479250449
    0x9151e131b0312050d1b020c011e050a080921030f0a0b010e01110f0312010e100305060c0334110307020604140a03200a05010e01021b01120504080405010207 69
    0x141d00d00a811610f420f5003e10701d00002d08140000040c410500403075a8004a1383c030014015201c9102c0030701e11000c1d444800920702c041c00680c50701d880342031190340c44210001d030f454250796141c10075511003c113407207183c00030f8098030403440780408041e001d503240610401190249644c0603124103100200328011130000d050809610300f4203403010542e0f41c1c00345d045d485014091910710902040490b400e400c1c5203d406d20119030f4080041c3c101c07a03880024903424122489881c001203940e07181182e0012441c06800024029004a00800c001082d044050768010701e0107060807d40209912407459240c0c2c400d02d0202e00c180038140f007240f0b51a0004e88801c10004104086e508d46185540000c038240700740e0281c060442003001222480382c9940c0030309405035900124101d2034240504510083d10f01b00800303288658500540411254030402a6100582c811b8004141035048200300041c412a0f48802c241040707503a0751203101e11005801400c0c06140907010150740c46042000080c02d01e462a0807 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 479252940 1250 479251690 479251733
    0xc080f09150f04092f030a021c0b030f0a0c09050a0227030d0311040509220302030403050d0c02130e1207030e09061009150311040306020306010906030509151e13 71
    0x541c4e585201800300703198900000700405c143d41c0d999130311070300e0028001c11000820032001c01c1004000751090b6801001d42c21011000c48004034519501140d840b03004000052540404801c1004080d8454009a820200446015007803100312900741624801201c580508107260346030b0307004142400d002d4810743e0f81d003e1400303110b034403007818800d2000c0c0316501c51b15020f45d220380c001032144001c0250700d07054054541c8144e24a10100e0038001c2d40c0303401c1800242d030140101ea0000040c035010350040c40b80c0a902600b0410b101015600901c01044101c02c0302083e0f0168480440070342500b02e0040a006110380c9603c420b210f900024088041c00c010b040b14020701a018089214a4100d0002d00c211600326a04026041584030110b018051000c1c08002240c804180801000441c4e00514861842031360b54000d1f460b52084201d0680d08140d03003a070181e81120688a40c1a504488219808000041c1c01408540c0200d803804d854042191107665641c6000001b0003002103113071806902d030f403083d00c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 479254190 1250 479252940 479252981
    0x2031b0d02070b0d0b030a0b2e18200c070e041703040f0506040605010608060f0a05010e010522150c0b010608070e0d060605040c0c080f09150f0409 65
    0x4080d640b0b070024040c041801c00e020036840d00b40c0c001d54028510b485c030301500750780400d500c91808011190702590b48541180c2d0310f040481c4511030780c1800c01c5428410900000d552450081c000b5140890002d181c00e440d91114504042c2280a070b848188010503001c01c03540ea002103d00143c14010190441c4138100f041d1000d00010500b06e4185042601030032507110740d2525a40740500600880c05401040790160340200000c0c854a42e2000e0304842041e01e5010b0541d4901c02000141500c44440da9808002c2d102c1c1817140d54881c008008940c9018100246000611390340d29014a80060000000801c051010302140084080d90300107040c140c1045001550640d682c01070008050049030104000e050000e0202445074042000d07030080074000540d03980281c03e00030043c1171940140c034040c0d030508580034002c0c0d201e00104600103400c148441d040807031200316a0b20cc1ea000c0100c00ea4419800c007080c0340b554450030000c0c09081c0200f000203540e50300d08010b02e01a10344003c000c0c1c0b410758106 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 479255440 1250 479254190 479254213
    0x9140f0f01090c05010e060c010507080a0b030d0c03111e010b0f011407080d110313121107030b09070510030b0301110415080405120a0305061c03090e1b030702031b 72
    0x1414004d0f62802d003840302404102d0000b25a043c012010301c003490f9070803c0305009001342c100741d805010700c0315030074188048000e160505030383e1200b504001c800104040000c50103e4032500540c004006000d040d5054082c825808022518440224208a956802c41c40ca60f600c0c04c0c006c00c4030550f4007824080c5840200083c1072806024005016148441c009801003003002c0c40c1d4001030740400c038080b03640d4a03410a044140c10558282e182240c05c11a560f1000030303488d01803a0380d10351540080006100007415a034031024003d6000d04065114820088042116a28031041c1e4240315104c4d600000d50180100416003900c0c51085072082c819000c100030b10001c0b4903207026500380c0050b424400709685641c41c11a290140090384c00340707010000310b0748480080e40b5030000c9025410440c1d0441c481000f03030302d0b03103070705120f1044008010a0101340100f100d94031181d000340d030104079803440b1036800550040c400d0450344103d0790710006030400110340220644100c411041d90310000018030001605 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 479256690 1250 479255440 479255453
    0xe01022106040e0106150c0201020307020a0b0c070902030603031c0e0703030f02060c09130b0d1b05090105040e0d0f090803040611191e02040b0a090902090a0c1409030109140f0f0109 80
    0x184000c506c20041e02d8581c1005590003003007207444066010b4401909a40d46054002c0c03581c11540007090309010307130040010640b07c0340c0292401803000801a500c1e02541c240d2103400260154070410741705850340b620480603142132040400550007900c1c2c0115a80030308000900784100280084c00c0c01006000b00300b21601c81d813220007800d0401703040c0090208400b50000715242c02c080401003512400c0050702c901c401540315040c08491095600c020300d640c80d00308000541c0c6124042c1c54107030f440001000249445081c403980c4110780e90400500003030703c03812201c0c1035a00a41110703000c129200040c08000b003003040b012861900303204080300d5029069907000b1149580640300704900d601c00c40418103641d01c83c1d000303054040d401081201c0c41a940c034046409000c245906a1040030498000f44101103940100c09400649a4480301d9120004806c001e45401911041e6015962030036454000703000404540c40504451000b00300284021980604d0100c10200c0c101c10b0764140000c42001420 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 479257940 1250 479256690 479256719
    0xc0801030212210a020c030a1a0402152205030a02150d0b031b01140c060f04141005010f0b040f0b0a0509060f03010e160509040e01022106040e0106 65
    0x18100c03281020200008081c81c601101c082806246a0709140c109094007a0000203042c0049560240c903a2890000101900c6010400003e0090009c880605010050720b200c2c2c19032191005081c6400358101038481412900440f01d2005084988907101070b0010343e260440d0004c1204900400844020340c1c0401c401019400f2401a44800490510002c0101ea0844004c126024046602108007d00b102e1030500d00e240485011640700d07065545030041c0328040303034801e00b50340000341f00d1601e4200c4c1c44644460020001d56030b04107420485075001c8014001042142c003070100c045415410309442400c011a29880029500000c1100700500c0e2000420601100c0403003034100c0d25202946001c1d640d41c454522800d40c8031400060038246541b070b840c0650b05031500d04219248070b0383d583d4061080c901181c540c0d03c1c0818010700203100f661506801c078075400d498490001d41000c44010b0396581c140304109902440c1e0002c5010010356040600c03810100c0d10b8070000900809141c50300728811f110 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 479259190 1250 479257940 479257943
    0x100b0906040603020f010f03230411040510061b020a170f0c0a030314090a24020d05030a05060409170403150c0801030f05070b030c18090405030d0209030106030501060e07080a0c080103 81
    0x80d126080d0301f01d003800f07130b4806c028a07010120503180400d21503441e85070747e1320222011100160242d040c90141e051612600e07100b10301140158819509080068030743d1403003d02d0b66450304081e10120070041c0c0710305981e180140798024420303e8070400e10018a08088110703007104800d07070110521312420359440304902d044a805007070207408508200702c4031a540c883c6c011140d42051449000144118983c2120124840230100202d01201202012a00c400d0340003010800505d050010402d11b0301a0b074011600a0350007040000c072000b0796030300c44075002c800148811a1302e40c0403508105000740034005540001d030320700f010012000600406031a0318030600001d002c03d101d07030482c1b80400c0020032044014045c1100b900e80c9a01e801442c0c0302540d0b200403401504064800d14030f081c00c0c10803669540c0100c0c1e01c40c01030350403c071241e9100d000039000400e900f13030b1564035040d000010803400c2c031400d805040e150120003114604600080d0456101401c0078200030301d8a4401d1540c3d0b41e000a000381545e = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 479260440 1250 479259190 479259197
    0x2060313050c1f08011703070b09030d0903051e120403081b03010e010302010e0d170c250509010e130308070302121611151512100b0906040603020f01 66
    0xc1060070714500d01400189500d0b0818412031000e220005084100e600c0310300340d07958090b003c1c0e032160007221048124490a6030140c0c0b06101c005d00040a402d6556072140040040720f081065400c50072064403905102600851400a030503000e45150a100914508150800d01d02d0080e403610070940220380100050100807240c00402c00c031714041c64101040f12498500c0e1030f00c0e561124941c5040350300a1100702d01051164520800d0b0b03084c003000340c06005400004074030007030b109040041110751160a0802c104c4c02802442c00c0400d4094035001031031402c244c82050720078100414026100d1043c1c0201814114000030800414881e0740d0b03910616a141c1b078a401e9a0300c0300703102500680121600d044100c2c4005042280740350303c50615441c1140d0781d588401240303e2030b5203501d440c3c1c942d121500c0c20b041a003500241180e14040c25043c00741c8005483c0d0320f10500c080703600d5414420301c0c210200c201f0342c85540605261425918907508000129030402100385550300241d9a040740d41c42b0141030 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 479261690 1250 479260440 479260471
    0x201050d090512030f010f1a07021009090c03050f090309090a0b0a0b0406050d1d0c01230c0615030c01050d090f0507090209120a0323041a19020a020603 67
    0x700481880003000c0d03c0034404a0742c1d100e007096440101c024109006403110403090401c00201c84030410000100708142d440c14900d42071030f076024032840c1100942d0b0f910a10448500014580b0200c0c41040c1a44404d940d0004880c03e02c48441901118050301e024007aa105001d01b00c40c50355a0210306421100700000003410121030408030f42440f070b459200f66052200494009041070b048001004010701c81101008605070340312286400200742000c000d1540c3c400c180002c46035004446841510f00c94608003080d000030780c80402c0165002007840d00e400d800078803e11125200410000946c00c40c128094460200600d000074828000e5828074889192074a14030300600400d400c07000d00030b03508030064880140c0c175003030200081e40c03242c0005070150040381140c420b50403001c0303501803003540e15541d1049800004880c00c858a0700300c03500c0c041300c8482007000007002c0500b0085600341c3c2d00b10f80f40003602e50401103d402e1252a00046020541d0480340b503903001a51040d0480303500070045071000341d6 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 479262940 1250 479261690 479261693
    0x6030715020a0501090b150d150e031b0708070608010605090f010c0210022802060307030531020907111c0201061208040e0603070608060913020d0614130201050d09 72
    0x2e000310481015186510340000c00c003d0156183e1103030302c9000d0740c0d48142000104c0e003040c030081403a0220054114025003824641241c0700342c010702d034602020000c581c100031403401110750f800c2c0c640c90720100035808258104030032070041c002803004003044d0428400940c03519801034164400c0b15891441800510604c0d01581e0113080e44094140d0050140c0c480c2d005442d2004e0364840032a00540310001440040728a09600300781c1c2030700d113140d026004c10300f1921110740c00d802a0201500803021120722800b000c650895440f4036560301d82005410350540d502e0703801800303030302e04000c1c0c003580800c80800c9816407000320025071001003e1451090380b2007001c212404a0040c807050b0403c581c8040d10b07611030000d100c990b0010700142c0301010715005498480c1da04040e980c104511910012400d070700300050301443c3c4000e01c55442001502c206803070044540c00903c02204107541120020340e940c980701c8600500c012226801441110035074808001c030b400180c92070042c041400c148a450707050080 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 479264190 1250 479262940 479262943
    0x13093b0a060c0c150518070609030b100803070b01030b0f01121202031c060807090b1014160f060b240d0b030316060c030209060405040c0306080d020a0b0c030603071502 74
    0x604480d00250b41c2c490281120603254080c4c80146d03840003040702e85040c81814500c0103c1d40c0011180c441c1c40f0120031910315924404c181400070140c6844011840000803955028002031191a103d50621103480d03043d4608045882c41c05000741080101c07040040c02111300e0707844040100d94012a0b00d071019072040c80304a15600c11501d4410b41d1002ea5030000b030144859801c81c4064030b00c12410313a0031103a1074200400840300032240e0b00780e04c034541e4084d800c0c00501a440225a000c000000c003403030054206401d1141808201d811600000181e0000042c0011849070303c1d40d0410440324104555600e0030703145c0f035000258540c0101d43c403000a40d280c0d02842548031500d08103001c2d0980f5240c52440d10910b0b500c0c151980c050700c9242c1040640f51030240709200312008058010503507814107061030240b00040c500c512561003455500c06010640038010800a0310304400b40d8000e00450300c2c607241101601c000949410700700700c8140140812981c0c00b00310384098440803840201104800001207 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 479265440 1250 479264190 479264207
    0x70e0c030a1d0304270c05092e091d0105150a030609090f0312020408190303020702041a0f060405211501080a0b0105030a020d0813093b0a060c 63
    0x1040144400240000c40303004030000350000302801c0d401054a080a10740e1201610840201b5400051081081d6040ba1600300b14117900c14210380c82c0803000350081100107001c203040c1421140811007540c01001281d00d2404c80b01c07008035402110340ba042d4540b03400310702140342d0551107c000507008940c50310424460ba0200e002403c030034101b4070007842d190800c40703904a80e9010640006d034a08603480d030442d040c0d008a40071a480f82c001072140490f5010111352502e0195400c40c1010303000c0000d04090390340d03409840c8d80c58589030107800140302d4040411101c01440c42c01c46000c3c00060004002c00e65480b400c0b0381c0090101c480c03005860f11343d03c102c1402e080d03503040e0800e080d0075914008100d01400140070548113200f0b0074003140c82e907260801c0680e5052040402035101074942c2c221320001d401100a403850001980600e0300316900e0307030a10019100c005010803d07011000c02d5050142c4804000801030301300036010109001142c1e52484d407038100c8008094800c944541006003d03e214203000c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 479266690 1250 479265440 479265491
    0x80904020f0f0405010f0516030c03030912030e0c040c0e04020c030c12070b010509040816140a03030f050f0f04111f08090706020304050a0303210e030408070e0c030a 73
    0x1c0a40c1da200145141d402034105010b1a0700040d5001c42d50b1440ba80902c0489509004501c2c0d08208014155011901380f05510011010992901c0315440012052280807074a40d1040c0c50200348209619100d81c9001c00b01d420980c0304030700740744604150341d4000d1000000341006030387c09a9180c0041149900e140b04035901030390540300c0c080301c082440c0300180180089511072014000c84da6a500100050b07102e05070b601810f415020480401a0140c120203101c0581c031441c041005120001c114034200103111906501003500d90146030704140151180c945d0016481d20418840c2c1001030031074264040080c402065042140300c8409550b40b10b00b200c0d054052280290520720104a800030a2140c040c0c50100d0a8420310f80085140b038004015181641c4000c1c4c1035101d80d510319241202d4826415102c60500c00b641644205070125501031075948010050041d5980d524180c4000c0c41d203031595004001548070007042c0b001030203540003100d8020750403800c045548425420301c0c0c480410407018 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 479267940 1250 479266690 479266717
    0x1d0114090915030321010803030c1813240807060e12121b0c01080c09100309020613031b050a06121409060108010b150301150210050109020d05010b1608090402 70
    0x91850001100c004510404510644418906d0f644c0f9150203680340015610018050710038080c1d081c183c2420b0a88401000c0000c1501001c5036080d101c0108440032800506456031600344400ba604030404001402450b150009003010361804100800070b8200032250341c4112042d0f5420039440d07008010a8000f083c1c041c860f55503c0f90709020204200c06450101c02e070300d00800078a000258000d0004601c2030100d4030800345069201c40c10088650184440390342415560310703103600561100406030010a242d00c486403092400c41c20105802d800d92800460000f051040c18803041d201e1201d100704841260506241640142e08080098443c2d07402d0801c050035104100003030604005000f50494150000802c0184082ca007031081400302c055032011905800c20040040b071144603074548100c0c2403841a150140d40600c10082941d900b1b0340b00c44078043c7c020494003203405041c4501e6004101c8030b00c0c601e140a04111001d40007100c1c180014203010008200018103844a4040b41c2ca600c60394a03 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 479269190 1250 479267940 479267947
    0x70b070306300201030b0a0b0c011a0d0521091e1c0201050304080d090f0501150e010e04200a0f030c090e100504080d06061d01140909150303 62
    0x18006000705003030710440c80c0c0003816100e01062810700c02400212651510461040d81400e6001034018060050300e82e40c1140a03504001541c0702e01e4000b03410030850311800803c4540016105920201c00307803000034401d20200764104001000040d400c084444600580414841800141c001d1402150003698208001c02c074805202c4540303144c001407810342280d6200802c04415401d0480031014a0005d0114408001180c089103010b800751a410490607000f1982030460765450280c9035134403004440716074503810b07000240d13142090a8000b8010b0400b0b52901076150482d02040d690002d44050240403103000f01150721010190010301420b00030f4a1502c4141d07680c007540b140f00403140b100341c42501c03802c0d0010408039458041e101006903060024180342042035081c2008150103402103411090800101c0043e1484e40200c500509054035903c010b01401407662506e04003001920f41002a2072640180e9443e4290a9403a1403505035000c4c4160b594940d080c44141d245140c40075458403011 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 479270440 1250 479269190 479269201
    0xc0507120b0702010c03060501050405060904150303080108010b09070e09060d080f0c06130231060e0604050702010c0f1812050706230304020105280305180a0c0506090105070b 77
    0x502a803801091554000c111000140d17600300c049031100e0081d1800100200010409031600c60050500e11070010b00021721400a144542039003100c903401200071a80030401000304810038400c00404a40a940c0700c1d41a18102000074840d00a013421036210b088403201095480d00d0391100051171591080409503a00088c0712025842d8010404038a050b208100008101401094107030b43c40c00e501511102d000030040031200c4401d0503c041e6003c81c40d0281c1d8080d0040b480c140681d500418040d4842c10785810040103000a45100070841010f580c102508059281d0340b100d5008065405440e07c1d01d0165072284000a00ba807442e4094280c1005040110007030150228410003151081c0d1603102c01c003502082d140b08030524410a20100c070501380002400355010302c0c001d0030303030514080000200c40000c01443c3c410400078100700e40003a82c0e840400c130440d07203a01444098030305000003d2582651039901d0701713420009401200d0003100041074040451340504140c9a006512a074081c00d140b034907 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 479271690 1250 479270440 479270453
    0x30705060705130504060e07050a12090c030201030c03150506131706010f06020f07090515220f2016080730120b03120c01200a080103030c050712 64
    0x14800d01d90103d01403090001d0585001d00c04e000460359150355071a641d907540701060f40e058124449180500c482c20180720b0804000e84502056a403054841ca00c20b542075000050441c0d58075403220061500c8c085108242e800c0105811044038422034040755281102051480c82844540c401d0841d091000a200001c40300482c0040c113a4002070018409036503a14400c036650f60800c041c0801c113400c04217080c40300c004280c00082e407103004004a1411441c038400801d821000c4108516401c403040380910600300081d000d6110800d040040612071510f60b000807100c02e03907180c826542d96080000d9015074115140d40d41c1c006c0700d6001580241c5440031400d143c040c1140d4941105a0103000503007001c1208914040b50100a84642d501864019840c501d40b00408000c92055410701c203103141e11031091203101c014848041c1000c00030550011402e081030200366000f07441c0f2100702c0240002c1c01c80580c0401024116509403030144440100c90520320704001c1640c00003084c8c3c05584000d00184240c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 479272940 1250 479271690 479271697
    0x61329040f020f030a020d1e02070c23040504060f061d0f19091a0108030919050306070c030e040c05030601170103050634030e1b060f0c030705060705 66
    0x5040d102806072241007a444000c030311400c541280411400c0c00803449807003c550107003007110f4412600294a03100f20001880d1100800c45102090b070f0000348040400c100d500c0500c008149048040c030000700c04a801060178402d41030400d004640e90000541030003102d03000121000c041d031200700521919012200038940c1020b20803041c0c6000100826800c5556001d000d1040081c03003c1001c442c9038460b416406009a8203059500c4081410103884565aa070b52041c028180c903801547d6400c500800d02806208142c2070711044110490100030a44000c607000754410803910345000c1203c40c503e02591060364000c04540c0080c6003c010040003038010000b10300408090307c4e501401e42c411142044901c0c001d02004045400000c0402d04808a1524100c2c62048070030600070038250440c2400c41c000601c455003000692a130500e881000c0d014440a42e410322801c206104000c01000843c00920694424154695001a4007038446105100340c80c98032b03a10030700b43d40060400c03040082580d003 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 479274190 1250 479272940 479273021
    0xa03020f0a0317040819050414010504050a060e12011121060a0303030e10050405011410030305091e0d0506040618030e190302090414060f0702060613 66
    0x1240d211603026640000588039030030355040c0c0d102410000d0701003200c071640801800c11503000c1c90030b010241c0710401090407180c0321190b545c6c603503072030b0341ca00311042403c0485030000505001080100317101c23a84611030b080c0c2c21b0350300d641000c00740c0044610104519030150000d520321035280c815007110729000c0794020812b2581c19203240701008040c5840107800d42e0300b610030701e5102101c05805c00019000740c200300000081401940d07620310070300701500f007556400c44003100c01d65542e4800c0000d000f44038800c1600000840d10803a000b41c1036a401400f94410300e04200d109010042d955506110054900c0049000c05000146c0b4041e481c03808940e80c1748107079000c90381c10342000284200e9602d40c0c0083c450070390f09a500d1159448002c814080310001020050018000711200800540c41d40d038003a60040384a0850030241c01e00c80c500003414000c000d00a80210b9002d1400d1210240d400642c1ca900048101d070300c07006000c200c04000008100307800c000f00540c030070070329000c51040c6215a150100d6 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 479275440 1250 479274190 479274193
    0x13020d05100b010f0f1101020f0c0601030507090203190b030a020d0b0a0506010f1211040305070b071208040309270e0d090503030910080901060e0c0903210d020d11030103050a0302 79
    0x515000c0055130344043c2541c4100c00108681143d10b042407040840c1d0101d00ca410740018604070041900e0b000c00d9100060520030b0f035100d40010420818100183c0380202503401085003503090400001c2d03440c2521511440401d910ba0401414960341801010500d90f4000c2440e50212820700d450f02c0d080070100c0c0c0c2412070070314000001e00d55502502022004070300d9961442a442c2448480380d0013421410b602d040e4280040c000440080c0007000484050600b206840c3d40307600c841e15007002070240031201201000700000c10b210001e500600c000080d103820340c21811080342085034640d884074024882c8a0010704000c01c0c021401d50100d10050700b0409503440d0810162504107065803481420440ea4100700411600007a15102c0c4000c1604031036004008a94070780e403013081c0c0c040f0f0001502c0c950042000051142014601003044124211110446183c1c00b0ac03046400c2080d8011a040788007030540019840c00600015070055020140101c4115181e503120300380707240d40300f041b01001c4016 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 479276690 1250 479275440 479275451
    0x2a010506030607090603150b040e0417160209060409050d0e0f010305241c0303060e0a05090c01050f12010e070807020601120809040b09070e0f010c11040513020d0510 73
    0x9007000b1030003900c102040d480b40c14142d4a000750440081904900000c0170011003440400e11207039200c001c200030300d84800c06814500303003414540f2040319145e41c580b420142c01c01a11081030002e42c4c0c9125001e0b0101c8400000341d03a05804503000c1c10745101c0003405402002075501150b0782211410658002c1070740c81900080d607000c010742c1140e40c207071b805031000c039150055100c2c610240458201d0485014002c108810210007401d00720560b00384085001c01c1d00c61a05110001210341240e86c08010001d00740b1142c1000d0340c0403512172030a464918104500058030a41e207001600880d0290313009560703154101c0da916800c0640020003592034400080c42a0b010409442c400181281a2003c10f440e004681084c0c2c0d540e8250341d4021b0780c05607042601d03001020303c1580c0b02c1e5943c500c103141540700c900e05e050904080100f03043c10b189815052028030760b40540401e0f0120045020184181c60000e40d40d16000041454204030b910000c4d8000c100c1484001081008500000800d1440009004 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 479277940 1250 479276690 479276701
    0x60c03040c2709260a02060a0b0d02060703031b031b08040c120f0209060a06020d05070510110304050c030303130305070807020a0312020f0a020d0818040615020f01060605030117032a0105 82
    0x8a1185c80120401a4080e00104600041991061158000c0181105286034041d03001c40e82c076400440c01540840d640b44d8a190400014614209203008240781c10048010400d10309005941c840c101401000200000142001215012a0b02400120f17004423405502e500c0d02515451100000300c1c0074181002c0850500d0401d400c4050079030b10a07401800c0291001001100e01d5000200d00752082d11823110703000000105441074203500d00c4503045040d07492400382002450020314241f503d0080e0300801c2003008095040505200c1b0541c549030039561108070341069102c0e800b603420040d5001004d16400402c01151300c2c1d4401c060010368080d00c020000c40d00320952503000c1d00703401a4210311045a50000240c80380c3c0282002404003481440d104036600c00705d0101e0715640c0044080482204500f84469010400d8052540119000f4800b250400308010a580410720800707984030f0b5800c4007860704000030b1007511078040b540c455000e5065900020324603c1d1455010580c16035292001240b0b = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 479279190 1250 479277940 479278013
    0x15050603060d02060a05120703091202070608010603020a1106072d05070204020306182802090f040b01020a2f0f030d1b05060906010305060c03040c2709 67
    0x303101e41002014481814090340a0200d164041301030101007041c100001020711941c20303e0540a404155000256545180f8140f02140b2908905000799800741c1820001c666001007000d041d41c1152030056100d0205040940c0d1818000b840500300d400750008100416a11410041081082c42aa20000444900c168008a60486103800001c00070000c2202600b0150000c540104020b00512000340c0004110f134164082500d0300849040d10100c1400e00c040040c227a03500700b803181c090451810311190009403980b8452072815004a46035207210411340c2c000d10000c8020b40d00304a40e007442480b007004441e20310400c2141c0d05c3c04655085002202410036244004c0d4010000e0700901810284100c207480300301c840c00a81c0c40d0b10000c5101d600000c1c0090203103d00481d0000c2c0200700a504514203582041e000a10203003082c0b00a004101c0824605100d90003141c1c0802c4448840003c120002d02410000702400f0002c1403c10015504015540032160403071101b501142041c0161000d011 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 479280440 1250 479279190 479279197
    0x40515030714070503090904020d05011515020106050109050f0d1505010f24080c1b030913150303030906020d05090a020901050423090a0f121b03051c09080409150506 73
    0x24080d80d1041c4000c40306c41c1440700e04603800600082450b16221182da0b642d500352031048405111020001d001001105420031900021290600003440081c0c207060008200c4141486801d00c918a455800041030b2078415911592540091901c0741c1c0480318400f0f000540f50030311500b24039065000000038050440081058002a400204940c50350441000c81c0d91071000b828241505004000144029204001504a2a05100145445091400c1001214a501034520114031308011021541c601e030004a401a00d1f49806d0002e02c510710760411400a01406441c40003492404060142100001a01c1c5c44590300c03c9803540203580c3c030356003880152100e00704441c0a004200d105c140290b1900040680c1c014410b43c102c45041c00f894941c2001251326842c1580d2405001402c4441964441c40010b0440503404802c072040e9810381d00100707244140025080e03213500c42214070100102c1e0380c111405050b085105161290380300c0c5d1039007000b45010040403c0c2450016400240380c1841c1e01503 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 479281690 1250 479280440 479280443
    0xc1615180608061f0309020906060a0818031201030f0b07031b0e06070f030509031b10030c0315231905010503130b0c120603150105010f020304051503071407 69
    0xc0c511018a410400d075120740028000d40e40c81242d190001207480901044042e08041a03500440e004601d8014004400303800341c00c0500815040103084081904402c03000d1700302c010101c4001302e000d442840303103013107005090711011882d0414000005110302510702101e902e0240000d0030150b100c0c04000e800700c41c0a44031403207099915291000620b0f0040500c4045054040c0c007903071500800341d4412411641002c821004a0800725604516040421800501c1074104040f0718840c80e180c800603881e1402201300070f0425845600c41000a440381d0440f803078440d0000080b0034481d40726450541d60305c0f6061440c60020450f910090818942079100e060300b405408410805182060011205540000c101a1280c10301d1030303086000400c8048101d101b290440ea01a883d41c07003043d082440f105020b09681e2082d489868a45900d410407901281110000d0804001070b442d584026400c0d0b000326804180c0c0034a82015000d550031480c1c6c003c520030b035a030b0303a186210030707803501c5d03d0902e1381c02100ca0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 479282940 1250 479281690 479281727
    0x30703090e0709091e06051518060408030a0807110c0a05120f120a0206011505120a0f0e0a11060a0207150306050a080f0c040605030a0f02060c1615 65
    0x1010020404400c01e8070750403100500d083c2c1d20040d00d030103c00080d125408407603400740c01c02032403071401900c6902c070740009060110b031505040300702044500c102c0c2c0595580d550081c51741c00121002d95891400b2500140000c01c02d680d01c615590401510410003114200c0100e40c0c05411003159103004581210070607030080009044500748130500512700101d5040d15014414804224485602004400b810316a0360400c80d98819800b20000d0038000c0c184d0166040072640c0101007540e035080700540305101c0340b1549041c2a030351101108009040001c0048040910780750078451503043c04161707481c0090107203070040001d1403210305000842c800c003546c0388016040b0410502502450b6400b01e144180d01e4900840d01540b06c4001074001c4025600550203a44010003040e4110401d004541c1c0c2e40e10200d4040040c54640310120342c0b40d03000d4a60040c413515080920504554400c4180c60003090040c0840790300c80480140404900414000c0841990000b031020681510884541064450149 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 479284190 1250 479282940 479282957
    0xd11071419110d02030115090c090e0a0207051f020405030111030610080406140a06080c150a110106030f050a020102060a05150108040812040506060f010c020a030b06211509030703 79
    0x11920651005078109066100d074003001c0d00009031760709000b840741c48040c15525044461416071400c044813150314801c03060210071f01d8104040101c80e80d200b42d00a111020150750780000e840c2c228148a2030500d2021a5050110605103281030356014105443c0b060340200f103402032040240265010495401b50b210b0004541402018800da82651304684074ac0300105179460b100c00d003800a0740c41112110002a13031654100469901040f00c054028400c0d54512b5914040580410807071061018a8003072082480c800f2007050380075070004004582004031040c050f2058a400c54484001c808140e006201d0b10002c07c0d80b4001c10300c1005d0041c0e4600b0032808a00105030015591070301c000340103540c221000e11440e1800b01641e07820303510403486840600f09a240050400104220036a1101d04002590b21301c100180c85200c112029690004c80a070031541d201d10000c7ca0074000c2501e400f00a902c4022015034001c0d0008064a101e4000001c031111a91080c684994900503207602800041c0c3c485c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 479285440 1250 479284190 479284193
    0x80f1603030315180902090f090705090c040b041202040e0d0c0b0705040e0f16110709020c0a020307060c0215030c0714010b03070303080912041a0f0d11071419 70
    0x394000603100e07000b012008290ba582c1e51301c80b400f59090444d8444110b881e501180c045141c054180f50b40001d45440e89029814030158155132400791f4002c3d14014640320300840c80205201c1c0982e8000c140b00f0030030300e9590f07440c2d4407500e0101c3c01d844002c902440c1130188040c5030540108280401501e80d50b03482d07050449540b500003140402901c90700901c0410003010a105d40414606c81c810501e5078881003450030729030f0403440d842d81d00c01846420000d2a41da0807114003c089904003c54240c2d40b070158a40e40042c0303400d0704003c00d00714000d60500c28018001400e0741c02070a1080a5030084540e64560600421002074a1204a400d80f010081c2000110001040007030904083c000c50000015a01044000301e40f034800144c1040d80418915410080119000c101000441858450310350400c1c0c48e000088034420f004008035151410003083d180b4106180c0c0c0155240307a2805031080c4000561202c00304c1581c2d100b01010364070703990340d4800c1d0310402800150700c8505c12520701e01d143d403203c042e = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 479286690 1250 479285440 479285447
    0x5040b030a0f06030b041b08030901020c0108060f09090a05123406150513091a0705090301061401030c020a0201080a02090a08010510052701210c08010501080f160303 73
    0x4080300c0142d8036039a004003001280b01e529085100300d1140c080c40740a015882c03060250180329920640c207580c010031012401c3e99010454613400002070804020300d480d0b100000d001015035418640d00904004108200d460b000107000f101030707005000f90341ea01182c02610182c140301e0600131982032505070011000215465407e101d51105150758042d0021680c0d90704420b803199440503a04000d0000010700183c41d00722032802d100550032601300200b44913555260711030743d0340300600c0c600f00d00c80c0d200082c200d034011811158a014004d00800c0b40e00c5c1c5403d66003110340442011140083d00e4450045c07800350000a0201149405842c3c41a159580c0203542c8041c0d0301840340c0076044002c0c0200007900200034065140120207046904034007d00340307014002c0b10f09510081180001050740020011104103c025041d151181c0070041c0c2075448411011030003a10b80d030000c0c0703089201c40f80003801000660050f816a00d096081d034052165402a031960782c0341450380ca0001340c2d445001000080d00 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 479287940 1250 479286690 479286701
    0x209030105070e180f1b0c0a11040e07030b0c1c0c030207030e090712021804140a05071704030507081b010501031416150201150602242503060503250605040b030a 71
    0x6c0d02507424039041d48080c24a080140c1000101d4007504101480042c83c44c26004544100b60b84500404d01240746484a0710190f002030914400d03007500040c0c0710012003100084161685484d5024850203500c6c01e4001c0003907001402c140c0001300724018421a0340b905500c0c41740516115074402041d40101e81e2110001d6204030b5410420000304c03826003c6903269070180c0c2e00310100703054006010b403400ba45000150382004040c40d00304440c41201c42c0b41c9480ea2221260440c0d0145000d9895102e43d1509a1035071107001c1c42e04c0000e40c0880c05403034944405400c5613040e40e10a4044603001d0208845c072350364a48032010084090000e0980903c441c0301101400541e40a5070710000c15540c1309800c00c03a4068002c0c2c0c04c602c0040e000b444503455045c50300c0311400700c145442043c480151070020030782d0f0a50a59003001081c00004001209169840303500480080d02000301901d051007041a5119522100c4d1252684050040500051140e000d01d0550b030856840b070090344c1c81c503920201c0c050010030 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 479289190 1250 479287940 479287981
    0x10090203061f031d0a1202010e1f0209060706020702040b030c18060d02100f031b0c0f0309080d0215090c0f061b0102030109060303030e0c01050412060209030105070e180f 75
    0x6030f40381540d040c41030513800824006030140e0040d11681c1c019080207103820200719002415a8185610307a40c480d0400078400a1443d02c0c404ea400e00c1044c400b4144010744904682507a10100c007060707400512905074018054035208030b50800c04290580141a196800e428500d5803140c2d0b050040245800700112803a0f018000604070140c1101913400076855422800c4030718001001c00709100341c82030b00f44c85000da00e1744c40515544402c02070340c640144651340120008004229103440082050700030b600c440041d1420505440d00100d0a01c0025981c1c0710018510200c00c00724404510042c5d002300c0c08420901015014407560245503003440b90070b030310603000d0700c003004002ea55000140c01c007031000d94060681a000400e00030302e1428010151074000e00313100c00c180c0203031000044aa03040b1084404490f40700700c600041c40c1203420118024003c0c0c4241d00e07019404c003010001000d501034514aa0030708120340030101f01c0850075078410b82000444241082c1d070b080c80c02040742507425072a42c64546 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 479290440 1250 479289190 479289197
    0xf0e151803030708071a0112030f030f110c010606081005090910090b06120d0905040b0109030c18060b2d0d0c0905031b030606060706020c03030c0310090203061f 71
    0x360a090301092859104000540f030b02e110110f031150810480c41e1000c48880c250002d00c582c594104070a07884102d02c60703400102442011034100002500903000f440c0046420702c010880c1d111001c00c1c60806622401c010106540782500100e9194082c03003505000310000484040c03085c0c144400c1c08000c0d20041d200141612038102201081000c500035407c50610803d4240b085041a0047c0554040307048003502c03e40c1c01c510950b1840981c0009400100d44c1e0445001c00c80c241d81c40016900903210741c0001d0074030245e2080208001e1142403032810061500541003010950704c0099103c4d500800025010915213000c91031703050381c491000380c00e041100c030341c14501c0c0410480c2024115868000d514020980c001700400c1249000d0008103030201c03100603c1e14521203001c00003a162032009049601c22607000c98020240411581941c230040a450112940d9003840032004c03209401c00c403481900b0302200c6101144032001ea0080e43c1c09900c1c041c0c14031000c496072814140389103144002e482c042 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 479291690 1250 479290440 479290477
    0xf070215091e04180f0201030b150d05060a0f0f1401120606080f07030606020706260702060108010e0102040b0306040207050a020402030a09031803030203120c13150f0e15 75
    0x10341d84010380c4082d01524000710540040644040c0400e489414400c0c6a158a001e0000808580380341003000c02c2c641d0900c4c0c0010444c0d030010008a040c0e042000c440501c03100482d05240c080000e0f8400ca00512080f1781c41d0b840c1e1950389220880440160240381107498194404024110b14800c00b5000d40174141000b000c020300d41d04821040302e070180c2c00240041d00c0034041c0980364000030003841e0041070750f2409104803802c06901964a0070a40300d040c0412090a2004613038107901c4400c07c80000048640c4201c40c00c1035a402580c9c0c0000380601c3c0c200d9441c1061510050005108540c112001004943e0450351358004010083d00004401d684038081c07081004016680c61000b5480b55070b4110000440001c103040060081100441410942c00c01c00424800f09800105070b5000d880d1040102240d60350307034400d0708820b00807049a0482c0007141e1b100400c1d41c0300305816828132451169140d03410340b017190908450660001081c5034109030070b03080c02600309200400902042c107a51501e10038 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 479292940 1250 479291690 479291707
    0xc040803130e1b04140d02030d020f060106030203010e060d0201200610090510030204050402120601080a171201140f191703030411090406060b030709090c050f070215 73
    0x86a110024041407100160002e0200c1032019075655000342402903c404002c0d200c07a84019140b040b03008101403029070414070611a5206c841070800c00c0d50180655404129102010f0759600600c4507601c1c1a0058100110700d0504c00c0c07099a0403500840010f032140c0c0c4038642400151528031500703904009203420b503488501c06400d80c03605c0c450202e030000c01075031500e00d10351091440250842001a0304010500014441c4a601c00d4190307501183c0000302920340e48002601d241030701401c0c4089001c1c203800020600c2011641076121400380200000c40aa005590440d51240d5201e507090002c1c070300c00600c40140f2686070340e2195100503280c0c085504a250000348624190042c0b44440e1018000c144120744020b00e040800c6031003100158114103055071000707070144c0d0046805000d0080d00b4005428042aa08404000c240440350305682c0d09244034000c11014503405003c21490034400c2101c0031510440c2107803409134160008500705007041e0700f005a800c01c01d040b107502500c428418142d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 479294190 1250 479292940 479292943
    0x30b010909021206010e01092921060f041b180f09050a11070201020d1b120e0906030c03032715040f0504051b071a070207030204050f070203120c0408 66
    0x80f9500d01a50340c501c513181240c001050520201c0400d41080000b0200704518501030700c1c101068904480c00c0b001102c529a0400c500380210f210000702042d8100c0021560000048810300544040d118106944824020302c010350f1041c80b102c4034590103080654445910404141011039194852801d0041e0b807050410581502d40e00010302640e903420500c0900c0703400e0300c51500c16041484059091400366000070351034500249043c000c0c0310800b01c68080381c1d00000340901d50303954408100c4103003c00105004060000d0300383c1e800e0003140d40710049507040c640050104a2070200400840c50084a4090b0a0551180300e961244203024028881191b0381d0300350041840400d0159210789076881c00d00b44100030074044e030125000d1440c0806000040d10140042c607110244200c00b42da54291501e44043c440b841e004100d610701d1106c9050007601da60205003142100d0089800380101e4907450a09400602c083d1499405640104080c2c1e2259803022203441c0c0c007050b60362403941801c0d951030115 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 479295440 1250 479294190 479294197
    0x5120a0906020c0d03020312090c13050604052401030e03120708071707050a030b0102030d2405091905100f0803030a0c03150e0603071a0406031808070201030b01090902 74
    0x15404a00c2400e400c0c044107a040001e041d00c10b00498140c5000b10040d14069203038030500d82000704609104002892215080002005503480905840d400580c10110280200b40c03d407102c1d44101e08017404070343c801070b520b2140801c1c145001503d01c0326091510065000b070100301d912064900091003185818048802c00038807400c3c413500c0782025850248402400c0c40c2805484400c3e000c3c1c20024000302035071010941d00e00800c18100005c071001c1110040c0c3c40d6002c0c1031b843e01d41303080c10000f0f50200403039155003520f40316001c00480039045444034104000703c4000c41c1d201d00d00b480b180d5110b0000500c00d420080c3c000f24080c1c014030186880e000b0340c5208103840c0e0441d140d1030707000006000300c2c0c0d406881600a80004c40c03904110044c0d0607005a6001031030b6104e9203400440220201c0c00c5987c040c4880b01c02880c2c40702142506000c03110301c45801d03402c20310130031001c079207044a860030507101810108042603001046619000003540103400400fa090101c50401102001c041000782892008 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 479296690 1250 479295440 479295457
    0x18030611030906060306040b040209070504030618030e1c0f021906050c070509040b04060504030e0d050a0611070c0315110c0c100504150e150a0c0c091808070512 71
    0xc140d4034a4809181850200c0280c03d0314020380c054020000400da840e5000341d0000e6040f43c0b900c0c10340d1204030b000c903903e0203540c0010745040d10300202e400d0780c03c17082c0220341c005038070039264103103003400c56410031000401c4011780c40703c150310324420b000000e5580d00300300881c2480148407008442e044400c48a22a00c0d6420100101e0000148903075610000c00c42c41e0f00402d001c90700001c05141c19a19030642410151005190700c1c2c4980114041600540b041c0020003405044400c0903001418003641d01c0860703d0050f5040e510301a07541c0361031900131048844103a0445216000a480d40e81c0c0c1c942541c03104954801070903a40c1c00401d90a00c640b1004107981c52000c00203144000424041080035849a08083c060050811041100354080f01e01134841c14001e00345900d91550035008074210032003c04441d24012000101c128149801c03042c030002413070007000d4401d001619071070030000300c030340900500740c0c002d80c4440000000380d4200024094a80302c0c4058480c0f444101140000d10707040340c0344 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 479297940 1250 479296690 479296721
    0x41a0301061206060f08072a03080f09030a0518030d08040b131502180303070602040e0708071416060e0d020111160b06060c0a0804050f030309010f180306 68
    0x1003184507030015851540c01c1030b00100f0802d1501e0014045d1101801c40756440c00d0102c4000018611801040900c4415101042030765129020008900407540d40b40c904901190569001c52007030000220703c02c0c4110440001185032410000040d50250860f6502512180c030f03a042040c134644080c02071503040c058503102c0207040e05240c038080c2550100101422030030305c4c0068130b40c404207129012102c181e480c00c500050fa01c2424004545448505505194052100150381740405c505940100b00720f070010340d58000c60740c40d17000d01250818011f42da0f420004060704c414820706103002c5c008012300e03e01d060012032080400e079280820348504808c00c0740d5980114030101d8203540c0a02414500c0c02e003000348603180603c00c0e2007038012002400310241406d000c22000401940b684811503222030380319800c0320100c030328a2824180030361190003001e000d48001218503206007070000540781455816164401c503048035440c02c8070086140d441408d200500b4000c000081411032081e0613203240c5030030 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 479299190 1250 479297940 479297947
    0x1e05070e06040f05040302070302011b0501090b090f06010810020315040903020106080d05120c03060d080708090a050f130f1b020303040209060a1203030b210a1b0f0e040602041a 78
    0x1c1080201d441c22407101d050740b401c103802c22000130f0340850140180c1c0e50901f09010882420038002104202e10240100950302c2e004001040c4104950818450307007030703142100c20404410100648641d020322540000c0d920428640e0421f15094010319030165040034454114a882070005040e100020020740c0541d5581406001c0140240000d100c4c404884c14414900040b9000101c200c071401800c28000940101c04140176989041c40034662507003001602c4e440f5081414020210340c88940c9680c03040c0342c1e003000064182820031810400600051090304c004003004080b00103044854414481c9550703030b41c0c4a88129900c80c40b881ea640070a640215164900303403041c03020100e40505414800c0440303e40c00c02150311115248100325a1601c2c0101da80d52260020a007018100d1109415000c544003044404000000d10b44c440da502400c90154402c2c00e07031191900c60603940c01514281100d40c0000d02c0700b020500040c50f0401c0c8664030040c942503a540d0310030484035100845c20f042d4030002 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 479300440 1250 479299190 479299201
    0x4022b030f030c0f120b03030a110f010c08040b090c0a1511011104031401090b0a0c12090b070309020f030f1c0201180f0822080d1701031e05070e 64
    0x8581080710880c0d608080001c0d03110810050080c0d00132120003c2000701030b0f1240302070103e040e04900c1c000300001c1e045036181c000b070200141483c0310100000d440c0e4418005004180941401900346d5003000303486001951311542c8504200d48001000700055100300201090b15440d11410301e4014140d18100c00346114480314010249041800f0001c4a6810000c00e0b1482410305400c48085981c81402c01c40e150608106840c0540710201000e071a00c032500c000c2110f01e001a0f00701c000c2003802540c0391320240406159610483e094550003501c2000c80000084001f070295000d41034490000b444403070907900b41e100003440c01c2d45000d84884071750404a0150b0302e080102a00961000c000c0c0024400740005000502d0085400100502098a81225882070060040407190300c103500d2420210200062070900300c40001e507100e419414418414408807a52042c00f66200c6040e005049908a902e036441301e908008517090f1000300c180702c0e924420b00092007003101c0030050801c0750b2101c0081c9800c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 479301690 1250 479300440 479300447
    0x303070c14040f092a0b0a0c0c051008150310110901091203080c0a050d0c090302100c02060702040905120d1e060b03060909011d210a05030f04022b03 66
    0x80900f00e0351582c1045030900000f0741c43c461119600905040c0f03e00c4030010941c1900501c16181c0c44900d0b49000000c01c203554561144c500b8a409006503807004049540380d00b800b5110411420701c80000c0d0040000c900c0108144840e800940c000504864071075080c07a12070011149021011031000310001811603680d6008450307034000702484011075010b800d00761005440ca0200a1201420010008a03190700380c1c0500c1c2503070780103000940100f160600300d40340900420fa0601040e4030400d40480b6141c10f1604c40c130403640f032190f400f8081c40c2c10001c0c1a07082c440070380800d0004580794010f10700c12480d8961280090540d0544589010078440070301d95200014400c18041440104c0c20107405000c50490001100d410600c1515042c05a0303031003d00c6280103040101d440ca2070f442e159145400c614100003146001036503c141d841d00c0c42c000c9806451000c0c41200c0aa201084040c00010740e01046a2134456001d13002030000d1a040d4107201c00409402c91281c40c0304036200c6588880014141d0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 479302940 1250 479301690 479301701
    0x20c06210903040e0406091a090105101517040c0e1f05031924020d020903120702010f08070302120c071401090b0105060a030219030b01020d05031012020303070c1404 73
    0x1018014602c1c0a00700f441d20403031303031100500c0039103c16245c03c4807000f0401c80b10020001248141090102405e019401501902c015940d8801d00d200e25403000c10301180f00b0020446a04d02619200340514900c940c250703104e14018000d0301c3c401038210001501d244e440c14414480d032082011548441c100003031101040e551030b00b01c079012341d0140003499868070041648031079140e0840c090401041c0401c4440308401c05650000900900120b2151090006a0040c12050000b02c0c00d50341012048643c1b41e20768015504040d001440109580184501070041150005400c2c0303009481e08514a012601440d810b4a6006000ca00040c08101b800000b01d0fa0005120411000348138180311078503a03182010060280c144a6140056002d4885000c0c0c0d048410346071f044280c0c0003000547c01e00160044c1925603409000d80074245440c82d040340300b107007164410703d0810314180c115818100c502c009507520340d008031b8041c8420001c10300410500595400180300d00b0a020031201c8038002484181c44 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 479304190 1250 479302940 479302951
    0x60212070e060403170912010605010906050f030a0c1e02060a06060302030603060c09130f0606090f0305060a090303112a0106030b0103020f060405121c09080319020c0621 75
    0x20740e00300c000c8440c0c0c2d40b24100c5044a400c41e051a0242c0550200a01d1170302c1034151482c1e1020114001002000040d00b10b44101ca00c01d80310624556915541074449203d04010020307850390400001d088410303590310186041500345081507840002c1da1812910000c0c4203003401c09a8444020000703110400d00600014201d145419819410010003103a40ca40015008000c0c5620224801c03040b034031025140220088003180510030305105046200080816020740030004100000c08680241d900d07850108990b40b00005006560721003080c1c60050001c001c04504140e111859035400c9484000078006104901176001d44280c00d000c0e04949690480c1c00e4554241d05014007040851008112541103a4041c3c90111380c89103c040080e58503c61600400d80c000660711200c9121400054903458000c001c4110b02551168000181c1d00541541b203842141ea000700b003414489811202e4002c0c102d94540101c42c0c009207900005040e54000520510300c2c01c100c0e03508281c3c00791058200b81c0c0c010 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 479305440 1250 479304190 479304197
    0x280f0521030a0b1e150904180b0a09050a06110f030405010509160f050f0411131e0e070509010c12020c0f0402030c1b03040b1810020c21010b0d06021207 67
    0x9544e5422941154050000742e2064050310807622400c030242c400c03680c0194000708200801608001001d1460884400a484540582c800915408410311880c0c24450f00000200300038101c5696142c00780401413000030441070103200030703a16810f07040b02543c005d9214200100c3e0a14005141d146802034152042c00386850700001000a144030307004001c01d40f801615068141842d03000403c020346010740248210346030004206131445401c0d8821401da81c1502003c541f404110340746134880200c0b500507400c0318040180402c07412806003005150310701040c104151724084545441c41c02020800404015821450f006080351601c0300c0900c9803858212011400c50501280860043c040d400155410404401e50740c480c0e440100181e40080c411100c00300d0b600e90480307030f801000c00a65030740729000e1401e801440b00041d00129182c45802d401611217000b102e0940041c0b11104400300706511a0b568408000308182c035840c6103082c425029400140c0d4407041000e400c0007200000300500f040 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 479306690 1250 479305440 479305459
    0x50706020a08010806360313090606180f0e070215090708070501030e0705010c02030f25050f031b0609030a0803061f02060a0b0f18010503280f0521030a0b 68
    0x241986d11044050400d8885054607080c3e442c004100e140d80300b40c00000030401741c50b250014140c10307590803010640d040d0b0307589c0c0b00c41d0300302110340c1050540c1c060085611040d5040401d0016020200c207040d800030703a42c4100c0701d900200d0b55910780d0054041d104e942c00354104030301c2888a44070030808000282000e182c2000700c01c4084c01480e07162135450040d24100b1601100303082c11b5640270088103140c40c40e001d00f0355210030001c0c2103a54002e521040d98008441202000003142c0c500f44800c0b0240980144c00341000c00203031a103609816840418070f551102c0140300c8540703162410081280360342d02c0f442d02d03643d0300c0c141303035041003020f190390030903100d10b02c0210f40380703108aa6012440030b41101c071501000c00e00d580000005006024131070100e41d000010007410b00c0060405441c454100e41080d01035880258220b210300102c140d200c06419050150751952200045011403040314640c0101d0641c0c07000da0201e141c1d0358051500c405021840c00000c01400752030341a0340300e98890100c080300e01105 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 479307940 1250 479306690 479306731
    0xc08070f11240412031709010f1107080d051008010e0304031b03031b0c0306020c06040c21020d020a031703100f0312050c0c06030117100606050712050706020a08010806 74
    0x1c0ba44201d02400025480748207001d020580203021603600c1c2c541c0640031a1701413030940c025074000c04000030540c074028103019555002010b0442143c1c40240c00c200c1d403618000d82100c503030001e40005000000c18149000300083c83c200288140080c4019107000785032b6031490b600384924190200e280742d100c2c3c3c50104c5030820020703801204003401c03408040d641c640e42090b00d00340060264403c0d4005801c01d8000501143c1b507040100d00705119034131540c48150481d807202003180410314000c488070a83c0300442c0004000d4600380100c500000d02c01004180440d490707a441d1088810744503c204405031001c420f01c8110301d9104650b60142078000ea50860252454543d0800d003034000c2c00000a0100005510301050f009001000100784060030082c2d6951707440300c11407000500000b0300d82c114000d0114000c0089098000c08044400554409042500342e0301c60380c00b41000405240c05000c000c200d0f00000a04a00240480c242240c440000079131601e49000d08148008001d96201c40e00c000d42c60f032 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 479309190 1250 479307940 479308009
    0x30308010504021213060906090c06020609070b16020f122a010504050405130f0b07020f01060b0301060e0102070f0308031e0402090f0a0e0a050307050106050105040f0302010c08070f11 81
    0x50307002c0c582d245e150442c0c0400d41007001c024840540e0241070785040c840b1090a01040c40c90000131241e51782c0c2240d03000d80d030b8440c43c075440740028004d036610342c8010084114401c078821107180b45507000400710b00c08541d5000000e0760003040803014032015004295426491104600d504c1c010400c1d28817000130013115040000c0c0a8840d5010381807083e42d8032400b02d039410181811402000d0742c4880a80c005481e5400e111100f00740440703001006108912511446141c107008100440d020048102e04503420120181c80e06107941c8a00e50442c4100d1000051009541c070b9030f400154000c9455a959040590405402c00b80c0700c4204011041518180001030300c40d52a0507078001d000f01d1300d010031602c40308013910107080308050503801c5100e07040041c800d210021000f007904500c00c200070099565510019640390040c1d22400346111618034003000554004c41c16103103080d1041602c1480c00d5095030b142018084c5501003507401e910303000c00408040c18412041000050a02d20311030001016040300c4 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 479310440 1250 479309190 479309227
    0x1e0d08010302041518052e05091803031005030c040c05160516230f13020c010b0918060f0630030c0a05060c07030909021803030c0703030801050402 65
    0x1d014994600f100305030008012000c101502d0400301c01e0024200e045c04050140905a4106056100310f04414a0103106540180340061445c6072a6018510b404200007400e50000c0c43c918010f20400d40004500320184021403040d100c000080822604140a26240c011420b202a0141703282040700072483d500001070301c41d40388902580c1420f000b150f2030001d040c4600c95404031400c00d94454003040300d016900c1e00b041e000611080213040002c40504005803c4500500075411244000c400902d05000d60014810380c41c020001180c1034900c41d0100c4d01ea002c0c01c840302140300c66804001d040850040c00310340d0708190103c264251505211000070100c142d44640c94001031a1091040c2141c2c10b800101c04024100b641503c1d2900c2e040c0b484107880b10080c2c02d08072194050b41d0005088402e800007a14103940e090ba4404803001e0a00d4040e000940c0a41c18420401880d443c120103e036804200900c10503140703102411455155140c003520f0400706800c1148150b00600c070310421041c403040318 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 479311690 1250 479310440 479310443
    0x1b0108041e05010b0402030109361407030f08070510050907150c0203030f04150305090c10030e060412031424062511030a0308070e060409020301081e0d080103 70
    0x38001214078034504a80144800784100b03810900110002070040c0141d40324044003107015101d00d1040722061a00c0c01880c0800c00300074802505490000c0100b05000d1025500740008401c444040744c403611806505844004200c80c2c0300c0b40041c4c030400f0444280600500d10a0f018030078891420320f4013409446803214085d9010540e80c42c2c460071326003882806065116038000d815240d0760b05004086448a82c0715010f000446000d0300449143c151103841241c0c400e8181c040903200c1006007104220f1301c4080c800b480010144c81c4c1340c0c881101c0c80c060100d540524844d00d505404025880c2019098405881608034200d00d44002c205c1480b1042034144d01c64411504190f83d003062070340000301640102003200c410806042d201c25004840d000e0030300151801515400c1d11512210109542c40d0070096006000464100125200f6070040f04070b605c0d644001010203050a456050315002c03a0000d911000c041d61007440031540502500c0d10101003001d017180640315412070000041c01d2203406100 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 479312940 1250 479311690 479311733
    0x3040201140940020301050406151b02120d03050a0509120d0507050c0613020315010b12060301020f18040b01050702010203041a16060b091f061d121b010804 69
    0x4007881e8800c1020b20403090f0009030304096541034041c10408000750002d000780350080380b9010300891500a5981550841c52030380e942c0d4070409001d96041c00402038864000c0f1782003410300312145101c0c00c0501060040701c6642d41d0000340380c500646502c099610160580506070080c908410040051000311030100c078170702101143c01e07103408400701c2c0d45101d07104641c0000e002c3c1c0c0701809021211060a0a56039000f1022500c4e65403005851100c449003e03c540c8002b69000c0003110200800d02c8001544000002c000500b05542c411902c0c40c0e42d8031500c500301c1c140d03504c8034018400d45482e10031101d5501e004e20f001400c0100703070f40c0042c1d980e01c40c0b40602d500180c10304545c5100101c88000321105103103800503070075801c0c003186084006801c0689a15114200704c400141c0c869440710b0861120102c03044c000d9100c00c0c42e194003610041c1c00e040000028084002c4042626141c2440041c4001d40c0c13080108002070004191856108000075121304001d503a80601c8049101001c021f401c0210201 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 479314190 1250 479312940 479312989
    0x7031104180b210a1401060f1401210b09010905131509150204060e04050702030a0e030a0804140a080d0804060b1c080309010b030c0a06050304020123030402011409 72
    0x140040c010f10040840129001c0b0a040c00024802010880801e0144500c020301034444030401c0f00c50a0b07400303078002ea406200004030100a1401950604544ca14042c14200d07810b0703404c00c0381102030142707400340c1000c038075150420b0501c07502340b0b207143c05c3c014038030310300100b205040c0200710072982c451400380035107000c075018210f0001c07080a521032040e1552017070070949414031900f0218041e401600c80e00e40410410411400e1509141c056548507a00550144d4680340003205d00303842c602d100c202065010b01c1042c40002c00507000303000500140106100e0803001c4206141040810034007508001510342051a15202c40c50708900c2403a04258000400f15100f4450302c0450b00c01403045c000c04000d060064491700a00c0310a40c021030003094504000d0180c02170280a15503508150780d40303103410035124101006214400c40c06160071520500d0141c04101220b48040c84e80722110070440300c5040000103120856810640103c4850070305c040351401c111070300d000101181c80c0e02e8040900a858034 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 479315440 1250 479314190 479314211
    0x603190f0204022a0604020a0501111f020c030c070f08210a03140403030b03160f0905060604030c062f03121512060910050108030307050715020d02030703110418 71
    0x2651000c06044071041a00c1140020703021399a403001994180e000309100395000c90b155215649403d55030700c504c001490814528000c07a005030342466445070440da0309110601d440f4a042c402804c100441c000200411030400412400d0f00c149644128000d07401101c114014900b090341c2e465814040b10b07016501d44004440580c040c211949240710300c0e400794000c010400d170301540102c1e030860007a0103c03036904104010741d990074500c074043d24030391903010102040403d040d6003010394460030282c0045c0c01c203643d950300c039204c040c0b20760031190120b0024007003d01012602445240040e200d6103402010758001d1000503120f218010b0013810b100d20f10030000c0c170094500b92040100c0d80f80646612540012034040903126002981d000085014501c0a203030101c1d0a4041d20b030596000324061403840c3c55030b036419101e03030380020021541d4040d540e040e81a4009688080c2c00c640c500490050b0b80ea141035840142121502d100400c030b40031040c84140310103049203a660003400215500042d440000 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 479316546 1106 479315440 479315467
    0x60e0d02040203090a020a08030408060f01050a03020405060a0b0d060806010b0304030503220501140f0a090c0504090c030f030c03082505030c070c08060603190f020402 74
    0x21041200546007950086800c0340c1d2200403600021200e41c04200c24030300030340c09034000780c0020500304040d040c24040c661b801840d0480a0178a5810140003590b606494080a8020f42d41c1c0c1000a4064840d8201140074102030282540c40740d26030340c0c200e0041c1105009881e02c03400341d034000044015a250a69000e41c0d810307180d580c10742da00c007103c0d0071924007070f01488181d81c541c240b180d8000c101c017845480c19003040032010048070301c1e140b041051400310107007400e01210710780803401000c902a030960b0700a0740d204560104201d480c42c1881220741e00b11760005800400042400f10801d41c12030009400644640c9501003142d694000d00070315032428111206010a80c0d030f6000081c03500c2400190342c440c032004100c80c2481000e4841048089207900100c00540c41002071101c20310b000c00455401c0124120041842c1000741d07241c00c403029900c58028001e9402143d0440482c48 = true := by decide +kernel

theorem cover : BRFrame.Cov 479136690 479316546 := by
  have h0 := BRFrame.cov_init 479136690
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479136690 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 479136690 ≤ n) (h2 : n < 479316546) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
