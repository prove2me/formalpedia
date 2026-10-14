-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2319
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:21:04.849007+00:00
-- url     : https://prove2.me/submissions/7909ff2e-1955-4ff5-884c-e55d474340ac

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 416906474 ≤ n < 417086330 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 416907724 1250 416906474 416906489
    0x903010b040c020c0d1103030c0109020a0503011b03110d02030112020f1c1b08010203040b0f01050609010c1103070b0d06140910030209070c0506040606051306030503031617070e0a 79
    0x2070640c0c0035002139160303446105581e000310400415001445150362541c0010080681500d0b81c2d00c141c020054060b00143c401640601000306000500d42414070a8600042e080d180800351606005002c03405000300c0b24820380110b4041c4494100e4030028401140202a14174071514a2207051061103c06540311902c103100d040240340520005d5a50000d00442607401241801c2c20030117401003041c1020142c008001542c030110404c07040104100032140030300b2003140b40281d180c1c2e0310f9003004060700c54070012a0014007100800000a100ca0300c0720502e5210050a42d844646c940da0198a190414120f018005494541c100041901020001d0b00c0d003070f0a407943c2c6028500742c18101170120381444024028480080001c03040ca10511801c5e4030300e076010041d10050f09103414400301038902405000c2c800e4440038030641c20295a0721800c411254042c000e5030035640d0ba03400c181c00c03c03200c0c05a40c4003480120035060a00700407030400c51b4480d0582e610f0f2645a11410010301c08246d486800c03480 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 416908974 1250 416907724 416907731
    0xc13060e120d09060e06070605040804320f1819060b040f0e090307060e0601060e0906030a121b06060f0515030f04061d070e0a06230a0b0c030903010b04 67
    0xc4400e07031043e403200c00d4482c14101100700c035000f200131420038444c2d00400b0f00b0075403504040c08100403141005100301d80e00256001c940000c0a1960025107283c0640c10442c4c0300c0000001c04142458640c1c00d04070384004212425150581c5a901000d00007110b1180990104500d80d5944c0d07141c600c264009020303c0e00409003030900f0000340c0640d8003860b00408407080403801c0010000041001207551306948900c0c14482003142c0c8200c1387e41d411007800342102050000c05400814100083d41d0352003250000d00900c0080d0032615a0311095951080700404c004c81c0000c0644918800300300c141000344241000102140703004c011800c0249242c112910442c04190300d0003240491005032604040d2414036042c1545032450b1a60060152200c0024610030701c0700200d508400210f629000c0f00c2c1c084041d54031581d074042001c0119480c1e80070341d90b84040500c0c00c1064002c4855075400045c034000c0d203100d5240362141c5800910390004018460290f0000030201c440e82428011106010400d0f01c051 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 416910224 1250 416908974 416908993
    0xd03050907050a1a040b0d06080c0f090a0c021e07090b0d05030f09040213091b0503091005150a0e01060f08040b0708090c120309011806050a080c13060e12 68
    0xfa03440605840342040d80d11503000a901c0c0c1030207942c1298018840b091040b65180301c291607400251665101c2c40c0042e0090752981d1809043c026016081003400401c5950181d81d21407580f002040e90641d03920840c840c0000601480821030704001c91410110000d004a5280a00801c01d558007002110300400c8424800f00000d6400429645100c0c1c50442964841800401060090203401c84006010381481c00002d40b5840c0b0b5400183e0302ea03124403082d0000f10402c04240c030075100554140086a111880080c581012035000d1500150401d01c41048040ca9100080e03a84415801009080303400100401140e41c0201500c02240941e0a0a04081c41c00741c03900d030071250006284030f003030003a40b02c0004c10b28107062180c003600a80080090040c070840b650340319641e40024526a000c03444c08140c1d500d0000d2000d120740c04540d01c42e51040c1c60082241d80c00c40c2c10300c0000d040c1e181c012074140201450142d12070024070280c800307590385e002032050f0320080141d500710028500c0b079540c2013190304 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 416911474 1250 416910224 416910229
    0x50307170f03040620240f0601090605041e0b0f0c0d0206070e0d08070c1712090f0d1a090d081305070519090509100e0f1504020a09020c0d0305090705 66
    0xe03500c00c0482031896100c00c012152690801240708203010340300f001800e182a07034489a4034414047d51001100e10b40030780c1d82e0001520384c64002c0c051031001c205e09100402818400c00d28940755003081c40b049501550399100c00d000b042c0c0040c102c4151207607000c542011298030400c040040e4040c20710007411300e030404100241024250100450141000031801e50034883c0c4442140e05841d400303062801031640e039030040c3d01d10364800d500d002c202c0d02031166003840b440800340070342d80141c00040814a407200707000204030720700c20154012038490110314041441c00304010f001c43d10600140010300142003211600410917400145400084090a40c4040120390005585410740f28207980d200755140c803440c00e04120034003e40c072000d03501c0e08000800c2494400414094401aa01201806040c655a040b1030303c42a0035424120750754412221001c0d02d900a402954202c2e001078854081c05071181e902d4000d80c0d220f080d16070695030040b002489441d9140c40340581c48030280c4040c004a50a1000 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 416912724 1250 416911474 416911487
    0x11803030509150c030c0a120f121a0316060807031406011d060c01090b0109060e2802030106030203040b090d1d030102041d0f0c0310030f0606050307170f030406 71
    0x2a4240501c0000c9400000b1150a80c11603c1c24091401140d844982c010303180f40c1da0340c00000045544480444401c040701d80100942c0301d4009c81602e86c2c4221200076545440103001e0381800d1620607210741c15485840d10284500b4950000c0160b907175803001d00b0044060078481000e400301d001c2600d0310301d0303000003500502d55a94106009181900c42e00106078803c000d000c5212503800d41c8105c00040d00c40b181d10b415401004002c0c4151402540c903a41c480e9103200700c841520038a2000c030711900005501c20b44403e1120886400c0c40e00c44910000105030701422a00241c1006001c00d0f80002030000b44000141041c0d4010039950052807840300e03010004110306d400e0208640c1c02c105408034458135a0382134058034042c240e010550003c0405500c00c03241c3e00542070351816441004007000c40c0103a1044000c9034030514078411000402c92441ea14400c01c1052580c0580781182c0d160004502580c01740468401045ea404100100080000007542841254100c141a0f030388100030400c403040d040103 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 416913974 1250 416912724 416912737
    0xe011203180e13020913051c170a060e1602071208090303190f0503070818030c06011404060f03020307060e03100f05041109061807110105040c03020118030305 70
    0x2810104454100400300400c2480340c01003070002640200b0009504180c8070070041603402291424170b29142c201c03915909a600b1003024007140c1050703c0f40f8035020004072010001590514017030303001003e0254844403207142030700c142e421140c80b030400b003120402c4a40f860f6040802074103000001c04140c3c2c0c02964030000c0c1d100d41031040401c03001017414083d088003611800700000d000d4035594090841135102c04103047c204040403031041c005140c0c1c0d1520880c02d0f40c0c0304141d82e460364103082c5c0304c82c50340c0180501800d40c22059480200101e0b82042014081e113030080c021115040c100e043d10400700b006485d041d400001c12480381140400240c0c1e070026000d002ca6040341400031075000140301182c00d01c00300500c00c01034a403d141c5a900d00113807540c0624410b0b40218152880b0300c15660400c107402d04103603119603002c620010b07045061044410403030b801600508040001c030145450302c1d07094509c01c5405031801401414104250b5801009a400280040700c812240508680e4050487d000341d8 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 416915224 1250 416913974 416913977
    0x150604230f0606090411030108071a0406050319091b0b18100c0803131502121915030b0a11030624090d230606030a0206130515030106090e011203 64
    0x20340110390b440d20b400c030490340300340e001600600005080080000045e4001e11901d00d07144203611340040c030354860340408240c001003800528075043c80c0440880d056040580034020b001c0322101c103400d0105062040e5240684104805d01402c180700c00030002000a41e0b0040e2640e07201042000c80216542001c80d01c442d80c1210031042d04183c152046400f1200e00000408040e00002440710400c103401d20095420f00c100445050200d122461034168004c4080c44016501a4004262b004400c201e4407151006074910004d07591007203880180e20b51a40c5c2c0e205580840c48003082c01038009090103510f40340c407940c0507560311b5820484040b60040c25010b0780c1b12031a62944803d0740c282d408500031140319140003002110316051382e04000031019412005500d6081c410064190340110104510b403040400030042c0001c4002d640131300119611a5090702c1d1980140c41011603144d40c0c1d0f0130901440f01c1031206440d20f1307604001000d050b003003440e00704001c00c4018400400c54400a183d4039400507906 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 416916474 1250 416915224 416915251
    0x30601020a140a06290f060a0f030b100c1703090a020904050f01060e010501030b03070302030d1103040302100503220c170319031a0a0b0d11070515060423 68
    0x780b0700c0039030418881c1d08004001c1d070b0030802038178801c1000700d50080300ca522114401d501c82c40c00350100300c0d01c2c40c5183e2005407c490f0900c40144201d000301030940c0b00c8005410041401c40c411b00000e0604180032040ad40401d0038144c1100038044224055484031440001c120300c1c1d0b0070000304c2160386151500e80203105400000c00101084000d00c41803d00800e0300e0028031140e91078962442d0204401d024a5001a10705981c2551070b140000700e0030200c03070b0080e01400e5058041c8804a4601e141d02c090902c950ac410080000103895400740c031005202d03207a441640301d050401400c1c1d100000c68810740414046030500c1c60124090445030307412030b401641030414500c0394440c1c050442c040c2503101c0c070b00c225452a20b50f141d140c16030440300d80340015071a141000e0700014100a80c800ca14022500143d50a20030144529559480703c0118031142c4180d504003103442d0740f003d18244440c010103030103804000a02c03600381040d002d000c1c0002d42144608240801803a01240360450080100681d61034 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 416917724 1250 416916474 416916503
    0x3130f080a120b03120a12020409060e1f1e0b070c030b131a06040f1a13021213020402191d060712120b0a09020705070503120f1c09060e010b06030601020a 68
    0x2198800820007040318150340307441e5180c0040d070007000b00780b080307103810703051040001c40320903651154105462000c098378500c207040c18101a42d429031124005a408000c540125035020703404040c1452900c40d50040c4e907030f0b41c1189040145454050f184002d454241c41c0003000113a41c100003171201d010000051001c80d610789002030081d011049031002c4462038039540c01c981d524071318404403101a058980400218154494208034480c0000b11421071020b14081580006041c1e074400074580001e00250400002c01c030344002140314840c40300c0c0821f41c440c44800b40e000c4000c0081c00b40c0d45040724640d0404c1c50750b031141c0080006908004003000201c1d0418505110030703034040c1c1d0044401900014005486001d2040254030201c07099403603101c0e202000038280742c00124400520f001440881c14612642c1e03514007980c01c149104001180f4144801c2002d202c02d02c41c2007c1103008000200700e045030b8028860841c0c104064a90144900704100400c40c0d8001802180e2540d01c1200101d0694 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 416918974 1250 416917724 416917727
    0x203180a1a060411040b0d0c11120d0f1b1701030b01050904050a140a0c08060402010c0807030e040f0b040f06050109051e03120a080c04051503130f080a120b03120a 72
    0x3000c0107100303001000c00301d00469503070709007806004c01005d0b0078002c00034808001d4060309c02c001441203030b40b210b0b0311413403421910352140c0000c4c0c48036905001001c189c18010f50324a03000c0c5d4103000b04000d1810809600701940c02d50103111200c1011031488104015411621641810401401158001d01346400420100721003000701910381c540142c540780110180d102e5098480303e2151081d9529404504003103a02000407a045004582c161204000c0d210642e1301e20a407a0071042e81903060000080b9410306980b07a0303005800004800c2c07100005c1030030042c002c00c000c45000200c95000189401400e0203c0d9801ca007141c001c1c0c680c01c46201802e824603548031454003407601600b9405000301d0854403580040d0f440a08040005c80d110104165141000c88105004c4c5103d496480b10461081000741d141c598010f42d0041541503021101c0c0210b03481d0451441d44140c811a00000001000031046500c8194000141501c039014415582c444000039980d0000f80c01641d004c2900090541645 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 416920224 1250 416918974 416918981
    0x8040305090901030b070e030303010e04031b0506150909011a1315030c030b010515090f0a03120207030b06010309110f0a050915011409010f0305060111030d0203180a1a0604 76
    0x2000010800b0310340750703100c0c94511000b282c1910120082020303100d9541c2c507460b01100b506d05031b07400340b00d11402c1940c036a2021560240c0e4082039003002d125103080c2c10041001404542d00c25041101e541070101040b0701480b81c941c00052244006915182d141c6203601c10044502d040740004691400c0c22580c0f8080000c000d2150810641d0301c02d0319a900081001500e840d1001124040d0210201c181e98420034002c0504520740e42e000c040c982000222498a400c40b54091207800241020001c2e948940c0c07070f40255000c142c085009644280401c10800c0301c00001241e1024080ca400d02035003410b96641e0812070041d410031449024000b2002a943d212040300350024080108410a2401d08001d06051602c1d0309480d54001410450707000c2e07803048003100b00d84003a4010f030750710802983d20800440060101401460400002500d400c0ca00340040025100300d0075540c500680d40d0500024980d1080c6030201c0c041f48a4002d2620f01d800704600007440c15184d24a4401082c80e40d40b2040010010b = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 416921474 1250 416920224 416920237
    0x2031c210f02040e1b0702030304120c0513021201051504090914010c0f090506030402060403080a140a03060806010e0f010e09010e0a030e03010c1805040914030a030b191508040305 79
    0x5852001c100001c007211130240c482e00500207200e441c0e880154000060101c0d101d8a00c010303406a00c1000100001e1000b21a40610203024045142119231158009400c0c89004862403107490340100300000041e14400480f8014442125925442e0019002c4801c81c6d0155220b03031080715075100c031800c042c0109003100001100e681c01c02008005c1003a0005482140c04414420000d03c00c02404030b2541880c50827a405650010708481c06c1c180380d9501c0e03021a07880003083c802007202008080b140102d19070007800260044d9100468618100304c40e4a282c00814be00905080d08070006010f60034540068082c1580e070700062841c06541d542001d1030241240c0d0382003c10321311031600a001410380c070407a0010410340c1100240450004804115030042e0349540f840c17800c03800b480d000c10051130a64442c9804500c20411180d10009003588541940c10200198020988946850b038142c94a0000110408c902500100340141003004290340b081c500b080c2801844801d8005c102490300030b0b01550407 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 416922724 1250 416921474 416921501
    0x60f04060306090b07080a0e0604060e0a1b08010f1415030a1b060f0206041101050309070e0103140705010c03020303040b04080d09060e0118080f070303020c030c070302031c21 77
    0x4000b00f20310b4440d1190001300d071600e0000701c868010030102c03851802480c410400038002014142c032161215002041c0c05c11050005102e00c0c810800001d48005a0301484614043d212050624200081e82550070408010b03c10519280719070100e614a840155004086003030214441e08031000070030301d007e945200290901010398824200a07034200d0340c0f82c0c10340780790780d941e0390300c40c02c104a01b80d0344d1700740554000b0401c10040c90540350b254030a4000c0c0d0352100410b801c6584541c1d8072102d0301d030200402e070030039a000ba200c424a800030510821036000100030a18140444d00c40319100207440c0d0001510080042d070b0444c0200c4d00303221b040c0c1d0940300040006001089035040900e80a0002d0a841020310b1881d42000036400700c1240c942c500c810640c1d00110039a1a150720040c100005600841040b03051550034801070280308030030030107024030a00340e0004150141c00d6004051a24162107418100581000028460503a2040320003000c450100714540444036082800c1e00a030205195006 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 416923974 1250 416922724 416922731
    0x40807060e100903090909020d02040507091211030f03040303170601020309060309010203042604170a080a090e0604020f12060d050d0309031103070b1b04120303060501031a09060f04060306 83
    0x6a01c2e1019402155a28481d40320020940d9650103204162500072002035408400e00d1882c0d1b0140c107003904115800507a0f0724203100310a48031102c465118000d010282c480700d480e420030081e281030801001390041c0358ae2000b1410a407465600903d0341000d020f009003001880c1c004928242d0082082d1030607040c0040c0035584070714004902c64001d402c1100e0a98440034483c040e0f02c80040c103519003146e103484d071030301d020b1a1500b00081c9000c1040160a8060b86200c0c0481c10808a0b010001400e298041d03503644140f6240307000c3e40130b560100042d00c0203118a20400c07000c10042c40b01d00c11169524061320000c05281e4500c0c000030a901e06284004d00103000d510802e411140c0c2c994400c1b00401c0c40780d12146291201ca04d441503603401600d400502c2c1423450b0340801d03c501d4003d0181d407414505401d0503860b00c0d480394010400c1006000c030480102e9141c000501c090740e010300544203041400000c080540c80d403100080c20222002d03248a000b111408031803851a22950003100107142c0100090 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 416925224 1250 416923974 416923993
    0x306011b0503071505070f02030f0c15011d160e010c051e070f06020325050f0d090e0618041502090303030c22080a080d02042103020c010c020306040807060e 69
    0x3400041e034039244c1104958036000004081038013410303403000407030307080d9009505201d041e81170184036178000c0c018030782c05105001000301561110340310540a045118510254040d0ac0c101c0c850f00781c20050300d080b420b6290030b003560f050aa0b1100d010400c0803030910785203440484a04100342070117015403070340044c00e00e14401400c07843c8000a00008940c00700c0c0c1c001405c113980c1c2d103040380c6a008124810340c0c0c60390107240000b85842a03d41e120442c0307019805842e15840d06660440c0351024120f102c0c070105200c1541004025411030340d10360321841c00e407041c03c181f03030264401098003800100000c240c19850417103a00c51010079070507103045050180c2202d98034103009140303d80d5900000c0c003081d82d1080713200c0c08111680074406c2e0141100c28600081c2458200c5555901c8140c1207201c03c10405a400d00c400280744c20049134000c1d0501c40c030f4000c1c02006000307040090074001e1100d54141486000d048a80c01038600003004d80e4841e401194680c2c0310200c41c608600540200103000307400c0d1080b005c01 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 416926474 1250 416925224 416925233
    0xa020d0203041b060c0f08030601111c090e060121020409240504140106030207080904050106110f06160c1b0803030a240302090a0902040518120408030306011b050307 73
    0x20310760440703115144081d441340e030b800c02210000c40c5410300030702d21080f03891805c1c002102403010f190090014100003946250300000246002c0002d10060310f000040316003428283d801003800d1000d030004200c0f613203062601ca000a0200610800c214500c038030f080008004c840041d505a4015024650040c0500c0d403074528030340010240c100840321010b80901300001c0c580740920481203401e0b40e580b088190350303203000c2c0c00b5002034000000540e840e8404108158041e6610311444c6e0103071115459144271240302001301031605101e0a030050043d0320200500405d585100c1d02ca02c0da00c00a49440e102140c06454100000300009100301c4a004091401045260010010f540310314a036560030071000b80700210402c0c95000b500c1d14049980010041400941400001c2952042c1030780c0002c50200c601d036011804071041242da4000080e00d6101d40b043c0d00c00e0074880807405075401020142014141291a07031207100240c691414000205500450184600380c0c06d00816000426a81c540c002c5d03090 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 416927724 1250 416926474 416926493
    0x302060c0a03110a03020703020915040216050615031c0210020309010b1216050603151305181b1207091109010e011b0803060a0305060411360a020d020304 68
    0xd0440200324400d2489000000016181c29044c5d0103038020300d00300c0e1440e0240400080d0140110554801440e45000180c54500052400d485040750908400300e0905019042a07005040d078010003220f00c40c41c140503503000802d00340304d0081d9a00c03039200c2011140c0603440c1a00340001c40408500110802000002c19840401c026400361103814507260503039076190300d07484214000d540003c00d0a009100d2410184007641d803050003e120403401c59240800246404906840b503030040361268200061a0940c00c5c03486500d90095009080a010b81904080322014070400180561523000c0c0d0020a038400700b02c154010024003400f0054560407086910099003d20700183c0850030201603242c565110b040c5015100f24075080f4183c91240340c0d40c900d107080d8800707000b0581c412141080800420000e001d030500031442900c0601d040510501800036005140311408034550040d07140038219595240306807180032030bd03003d000890350380e00d000400900070880860802c0d440481000100718100c80c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 416928974 1250 416927724 416927743
    0xa0e1e0f04030f0207290c1501030302670f0804152d021c060506031305150f100f0503070512010603020402031306060f120b040c0302060c 61
    0x5849803120031240909a035540313030600c0303403246e041c0100b4095a488125000c20000284070040264a401003264020785005205140010060405001042003580401501d42d2540e02c0300103a2103204012141c551540c5d00004400c40305910440801aa00003400000541d10807102480c5280c012030064080481c0e81000116000c94010b101c6602c1081c000e4203440e00c242e500c01400d82040b0f480c864500c014224142110317442d00412115a420740340310248848150f8403110300143c407031500503100d101104110f86044492171405a0130f00503030311b40c44100c0b40d20440300c2d0380a2a0f059214035080d4600f91100040703001c0b490301d50060142c1d030006050076600031548903030703004041c40d112285161448221701c541c0c0c1d0306a0042504000c00e0a200f03100e458a050000000544556241c012605a900440b1508010528030701c40804101140c803079100078141d683d0480306c3c032031b00b04140c00c1180e0f0782e1a400a0088500440001d042100b500c180030085e5501031b042c070340c030f441c41d001d4066034850a46 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 416930224 1250 416928974 416928977
    0x415090e030415020c0f010e0a0302041112131a13050102040f140a0807181103010603060503070b030403121d0706110706021501050603090f01050112030e0303090a0e1e0f0403 77
    0x3009050f007034400620300700d061500821b402c21035101000191090b020700c6110310307041020a02e0000c09a9154407520000c401000041652200280d41c41c2e0900320004003610a9540c20300c00740c3c8042101030705d0031076081d03411010420325601d03603502c50001d00b015400010025800007501040e92203071009458202c138800c621486000b500c0d48200502e02901e4040c902d8107a209510402000040304e0015424a088950000e01485400407003070311944241c203c0008a83c071410301304403d06080000c1070050480c8a0820704505007030b500209025000a14405001d44442c1c13082002d013a19401c001e0030a401c901181c1300b40380d50720b201a000400000d004c00f2140a5003500140007800480c13040b1114008034019961603003440108207481d0005014a42c0b18401c009030f01c60003000c2445a68082c103a49000d034400580720b460001c0c4040540004c0314000d070404c0c044030b0b1407521040e03c44015902070440d00c206a5480341e8150b5010f20008029000e010300d0340062101126003250400d0186029 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 416931474 1250 416930224 416930249
    0xe040605040e2a0d0b0103030206090d09050402090a12060c0e0a03050c04050a021306050408010614030a12030b06210604020301060f08060d0f050f010608011a0415090e0304 76
    0x19801044126a40c2d28502c822a82060081089140000c609900c0b40060036a099420800800c0400c0c1c443c901a14121401003c01006005258040000b07540c0080058010f203090310a00303000400410547c81540c1c0503540109c2d624606a82d03450165001d4032040590544070101420b008000d030441051160218040891a184c0303410842c4150003030fa40c002008000b181028400e12000346001405189015800c0c810031f01003c03d001030700c82c014981a07a40c0c603100c908050449007102c0300c82c3c1c07240c040043d0b0720344401c03429100858220500c1d034000c102c5103520a00080140d02030a821000c2d19803090000071548108500f452169003646107040300640309980384c00c20b2100301e00c401e0140c03e0104508004a11307a1030710681a0719840710b00581000c200c140150b6400d502450799007000c88098001c0c120f580001d000134415400100701c41c2009118105110344404402c800604286006a41314242c2c2c500303a800c1c0d89100c070010028407008022820340030b00c10648030b130854007405400094 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 416932724 1250 416931474 416931479
    0xa0806010302130308090402190c050f0a0c05010c03031d1b0406050105120901090807080d050604050c04060c03020111041214010b010503180a1a01150809060103080306011206060e0406 81
    0x700744261504240100034442d101d500b1900c400300f043c1c0180580c0c0b503125400300040001d160190701051507980598840341351000720342c0381c200e06280c0403951203c40342c1d05c01070b440c50100f010007000800320b49081c05c05030019161401c045014226151504414100302c0d124480428400075000003070305c000601361003c100880c400c00c0240c5580d445003034000381042c00143d8480a4401d0800e400401c2c80000060180c6075a480004d17981061405070744ca40008280b0482c06040d0b4050180d004400b01d608103c0c52030714091421a5019601a0904110700300d4030b00001c05000354028000a0034900c03900c2c3d11030390b56040386a001106440c04560742c3c0520482800920414025035a9081050312028110364414850054003d5882800c242070301c074503480d907800b003084441c600a1081c0c0c04003484131158100b003407100c403100b8001072110130407001da0b04128014202190080c192988041d202c3d6880d00c4020041703604c042c4528a0001c10f610380180081c501d0340017184d54261440030b5500384403055 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 416933974 1250 416932724 416932727
    0x615090509010e0a0e0a050a030905011d01120e03120c070203120a05180604180b030d2a020f090f100605090f1513080c04054807080a080601 62
    0x850a21a0f26060075030722010803046046a001100c00d10750007003c81d000309503141c54a600d000c0003180c041d0041100c022080c4013035648405046284141003403402c070300c40035100009011980031000c40038603c0e039a40e45295603c0d41801110355200d82218158502d00345502d268044e82d2224100724445c2c81442c0c0d02c00100c00308402507400100243c3c0780e9134245900c00303e41c0c1e010000035608203988540100008a40310b11091005109040b03151800910708110344141032074480c65007101c105100090b580210019a140d0348020416005001258100d856101007001051400780c450341c40800c41c0100420b0360ba01508580c0300da030030108105203030f40c0d40c1d001c180c543e4851128072a4000a84851034219820900d584426159151002500d02082c030300c009400c5801c5508400c003581c1010b000845a4901402076070b41101210341c0344200381c001071070642d4401185152050764040452001c0c14102c500d00d52000c00b40740c11101c19031307941030076103460798041d4880c50125001c0303626000814a0f95 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 416935224 1250 416933974 416933989
    0x1401030c060c0201050723160f0308071407030b0a0615140a020c2112030c120703110f0406031a030601090b04090f03030b09010b09090c160606150905 66
    0x2203811010100e52181400e60031075220420720340c1a81440320030442040040c1d04007000c1e40082c422880b0f0500c4016800c2c0040b404d011850100300c40030541c5a40c10301100c0061100c4000301c81d404244285d0f01c010520301140c403d1541100c181e450301030f40c04004140150012070703500c02c2e03601d040200500c640b222640450311002100c4013001415918000707203000e0025009001c01c1c061401100d860021b0b010000d140550280b10b900d405076800e041d40d0401e02e000300000c0c00d5400024a2140c2907251518041d10309000c0c05688540140036000426512402540500071040c802d041d101d56508002d40440f00300c0d4024880c0800103071902d4220700d0210481c0c030781c1c0c80c030004c001806020180d10b4142d00070041c04840e1601c1b0361107555550301c40002081b50340f5a600c0b541c0710352400f040700e40da2042004040801640300b0288a05d040122003003950b10808141c4c6d115042040441d02c80c585005aa2000d03400c05d900185558030301040814100920000f0030040141550350500031a100d8040c000c82 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 416936474 1250 416935224 416935229
    0x3100e012f0a0c030210050115030e010b031018051203180c0f040e0c120a0605010e010b0a03020a090518040c05030f031602060f040b180f032d0d020c041401 69
    0x81c40061101c00e40843c415082403a425004e0700c101e510102c14829842c0482d42c083e808083d1100008110700ca83c01c1d0540511060750f541c8100800c0100d0311300b0702284d1114024551010340958403007152807803442125010b45c030f16400000300c40714402c0d840c511681a078004c0e41d40e004640700080038660440d40002d0040c0c040000a02400402e52904040c040036140c00b5220408a00502c2c8814040c1d8440410012032880304000800f16040d031410a4811508103030803030080c0a40c100700521002446004540b038000c201c3ca40169240200c107002c0301c54040070b40205a101c19480c0000640303030580304203203019600070266180f016036200201030b42c480b5244406401c1e900f0078000c0000d015092803a003001c117030010340300c0d45c0341809079500310700c140d80142c0003050480d0000c20b441201840100da01003402c42c05070b60041c1c0e42014680000c0d600c01c200c06c1214566000c11440e1804a00044a1141344c0c4564a003100e815100d0302c1c202a40340c1501d21660350059240030701d40c0d000c085034416100d04 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 416937724 1250 416936474 416936561
    0xe010311040905010605060a02030d0b01030c02150408120103152d15030204020f0d051003150b04270b10050a050d080f030f19060b09040b03100e01 65
    0x49000c28041408090840311400340c0360f65617540f40024042e1034240041c010fa041c02e40c00f4550302d4190100c1c81e0b044a82c02500103040600e081d001c00c06140d00090510070310700ca501d00410003945d840c03615051502c03a8040d124502c405600000003004904520000e411074214000c1c001a45440b900304491580c1600980c03607490246840d6100c440c46501c042854070311135403031a00450301c035004034041ea481003d0618401c4000113500910310341c1845404e4000c40f02070103001105156485550180345583e1840040507a90281011141e0391a4000d201c000c0100c92a821500300640303003500c2c203140044050760100c41c1038000600201e554065102070320701c006c1c039402c5124109000d00c41c0700e0b11804001c4800050400840740402000d2000d58400c0e01e40d80240ca590345040e42c41080d400c0e40045c0d60740c0700b6609106050082c207540c00c0548440c000291070002e03100c1e041200081c9482c2c0c81e4a1681000342c50b00c0e049206811041d00003458110b42c58110341d1050724425117584010002041901 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 416938974 1250 416937724 416937743
    0xe160806090c0303030a0c0903062a0813062a050a0e0a0f1401020a1a100608040b01031403041e15050c070b28030c0f0f08011a0c150a060e0103 63
    0x81b001c00c090351200b50ba4000a250512035541c40755141c41c210f0785103024a02c07480300d4000d2640f8402560300c02c40740030003c0030b141161183c01d04c00c060000d1032130182c030300130b02e100d8581d0900026217128803404450840106600282c0c000e10130000b42c0349a100280c40000030354030403889206810145601030407a0401d0a000480303505d00b44441c000010814003190445c0a90f601c0310012070b4112410f0b0b888603901c1050802c2a007052111100d80c001558888004d003e1600308010200340c4080d80541103a070440d003000c002c0b06410a02604601c100e0700400c418407840000310079180c0c540003264050350410304940c19403d0480c2000c1c1c810740500e08403000039a00c406002d01094101e8006040420180140b0240501c0200d48101a1503000c480d12000241e65802140c819a8000d540d04401c140c9800c024035040540705004088034014019926002d03a0050000c24401e440400c4491490040c4190391440d4a110161a421403058800851590504a0104244040c0401141203942c8094807c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 416940224 1250 416938974 416938981
    0x111030405064e0c030f0a0e100b030c09011a090406090603080904111305150c060103030c11010201021801110709021911010204030c0512010e160806090c030303 71
    0x8129802414108a525103854000381d02e6051101e40c10307400e100f840f0a42e0307000c5844000d041050b40c0040d403440000c00240003808120344032001202e411440548418400382c2ea01640007020b091034051b100040c3c800d00280c0c070500d5003254004843c49008800765982030313010000700306a000c401e001c2c400380c0a0450070040f40000342c210040092940240c0040f8807a41c0c1e4410010480b42e441e442610800b5000a44440c0f52515120301d11680707035241d04007401e0000740070119404050030b000e00c50180103d4420007000306c4021742903407140d0607040b040720300d99a10392030f00511855818001312109038001700100788941c010700950309843eaa1305030700300e42c52304100300450b002901d003040c40000d402802e4002c20788c84028001400c05d01c0070b464100c14034204d5420005c2ca111100704041c02540d10600091001528102c840022124210380c0004008001c1180034010907910040280901c200070f10118441c1c021600c01040310090703821b442c141c3d56040744040e164101c589840e07a150b0000c1000 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 416941474 1250 416940224 416940229
    0x6030c010806101b0303020c0f01050106050f0702011812031418150c0d08060f04090b040b041e060b090c130302090a0906050c180d0308040f060b0d0b04020f0111030405 74
    0x7143c00498514080d500401c40f486003503d9032103581d506030006500000c881a0404d800c2024902201242008100c0c0b50326009005095025a0070040b580302000204103095a2050001c0041800e038260110050741c0c1d110200d42d000c4900d260b045021400c41d441d1400d2401c007507402d41d40d440c00c10b500d0406d0b46441110030040001180b00400e0300032003041c401242214010807100c12111b506450394002401c014003041003880980300750070310541c01c0406e907800059015103803603003281e44600c00102a858600d0a209592150105540c4106c15484814144102a0081084040140c80c100e2003a02c40d001e00310203c1c8124014000e50007a540340c10001030030148110b991100b894100000c0e00301042d81c0d00410ba0300203590101d010340c404103003c4003110700740f031806841c1b0030304907a5595106003c1e44c0c082c042c050020000307441c0121807030303200301030014030703044624088402808150759802a107003130301d9910410b450503402903410104c80590395029a1050510520250045082c07520b040d04 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 416942724 1250 416941474 416941489
    0x1a010f090b04090501051306110a020a0b0601110a080a03050606070b180c040c1701050121020a0c0803070c1403090303071106041d0a0e0601140d050c03030f0d0506030c010806 77
    0x1c025410a9482c0c2648022031001e101e0140103070016400e00c40b25072140d00b03003c1c00381c3d52640d101d082280420081910350300c1d0001103e003840c0e5881b0185003603e5442000584940c9043d0041641600480b0b07044000c022a45000346203822260314100140d807106814094103000303407030005001100340800300304c4095006082200c44112401100c20068180d00454180c4690103e04400b2442810425102040a0720414050b21081c85c1111030501e9580d01d60800224411070030f58410743c00114000024814080070003260b170401e8840c0d947c1c2c184003d0003000900720319411307580b5002c48200454070303800101c220b40718a0300040056040c000c2503203480500c20351410185500080c10000060550002d034402c1d10740034658040c124183c5000324441c7d00741c0b80700402e00c0303010390021b500604c0840b801100344011580241ca124444210501c2c2c428030f008600310003c3da0620000c01d03500091001234000b4040d014620405100d12349910b0141070f0b9544000c4111804521b66000082950801c0750 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 416943974 1250 416942724 416942741
    0x6090a08180406051201060e060d030206040f05120f04082506050918012607050312030606130905190e030a03110d0203130605090c130c1701080304031a010f09 70
    0x6200040c3c40303640d0800580c401001c0135458406944030f0900300206003210140a92050302542c400c0d45040c588d80e402510f54400403c01005183c0301d0402c05e0030320800b003080a0034409040281a0b451981d01c280c040c660300288035200d0355110310421803c01c807543c0b6250034030304615010601009401e16409564542107030350b0460300b210124031481042c00010082078000c00740d000790303081e1042c1c180c840140004039103244200b5590112100700300780d440000e40c840440c07106400c07071030310303a00d43d040001c1c540d00c00c80502c0c01051b41500e1000c02c0c03503071407030b84624042c0d140b840d014001d0300c10074007a403c1510b8618503025126002444000342ca2070198000039013941c0c00e078403100d180c100c1c00c0c0c1c1404202d80084d11100045002c0813002000c2002030310965030030001400084c80c00481483c00101012503034414011415154100301d04a6030007000e441040c0303118041c044036150303110030131156a608188400d0310400b0908100c0450101503152a90595580d210588000e508000d0b0700707400b826041 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 416945224 1250 416943974 416943979
    0x9030909022d070c090f02130e010618081b1c03030509100c090b0d0b03030a02060129070204090206090d030c021e10140904020a0804060b0301020c031c0e0d080906090a0818 76
    0x70070248010b90700d0400d02354080c142d0215504559418044028500c840c6a000b8a0040b16552010301c01c01c000090540407101044405855015420700030408020180304d0742014000103440c80000c041e01900514403032841c103011103a21660440c2000151040703400e640010840d21801405402980001041c41012119001c034442c2c083c0e00200745158810001080140c0100d80107020141c3d118589902800c68030383c83c1c0c01d0540b61402e0080180c40f460394002d110700e90f03c007512021510b03460b00359070209100809000280804d410041e02d0100d403c01c00728410429064817000c8001d8070f00d26856018000340000c80c610001540c2074440344194040d40618080500500c01c841c1e80e180004c1c0712507080d07076941000038142407a1407404e5038580200c040c46030b40140f00300969031100100781c41c100000c000074a0381c1c11202c1d070210030082482020311403181c01000040300c4103c0e00081c191340140074010881da80c030303030b624011261030341e0000500a0034400101708020034070b09100f22030558440300 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 416946474 1250 416945224 416945227
    0xb04060c2c120a2402040501052209020406020d2a0b040503070b0a0c030b040e060c07020609120a02030610060503043315080102160609030909022d070c090f02 70
    0x560312031a0543c2c845049a240c1c00140c400700f030841c048070b1394080e101c107066015400c0070304140028120303003e007240c4803040450364540d000201c0c106644072801410200300c11982c03240c8a0000946135086416140086400e50030308000d80c1070001c4002c040501110740ca9420300074160780c5c102803124040c20545d9544000e20203440850341c8258140d010311354140300080e420fa0049005005d407800040342c54403d03440c03c41080e09101c0042080d6620141c00200156201d44500c00103801d0300802450700c0e0070015004201451110000b5550004d500880444800340c2e00c08203201260192801024000307017040c0081000a03850600f9600c0000c03209007810215220036000424900603035084038401380d22040040c00104402d06610094410400250b103090000d50301c0d41a05003076264014107041d5a02d010304e0070301d0302c02c03611070001c0c04480340203542d40c1400000c50803621a00e000129002c0d62403200144207c0d10740001c880d5515070000c100e200c1503160800c02030003440c0e000108003000c4e40 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 416947724 1250 416946474 416946499
    0x90102030d050a0504030f0f09140607060203100f1e0603050a0b0d2102030906031f0503030703170c0702030a2d0c0f05010f120e01060506070b04060c2c 67
    0x11a000b01ca00c90344041c0000221403500307090081108403e200028140048008244401c55100e04254144d0307004c100c001e4a00e1050b100803820b1441040000381140d032012091290008074610f80c03c08441c2010782c610400c0b611007028440c5504070100c80075260904243c1081090300a130000d540c8642d001340c001803802428404110b039113048880488040707101c10501181d844d44060b000c00740355034a100650802e2100004222103100242c07110301d10a0103000341d90f005100c061440380c080c0c00f024060760744906192401a0010b003030403c03010800d0540d080000e240017103650668010395002001004203e107140c940b05011030101c1c85118055090840a040d0b48101d0003181916a00c00c0341000302c4549042800030169042d034200c1410004005460038010f50300c10000c400d5117549100010b175141d080700c403441c0103190641c80181c00c07032000b04e12201031100c1d0081040c480c034002e9200707024403d40340400300c808440c4528106042d0f80036001880c0f6400c0204c400607911711b401707800c4848883c03 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 416948974 1250 416947724 416947747
    0x10302040932070c0b041b080a120e010c0308090c0a060203070c08010507230c011a10020601030c15020f060411011107050a09020c01091406011509080a020609010203 73
    0x40d0342001c6040420400d074500c2003030030101640300c0341e10642a8441012401d00b1030f030040c500002080042c0c41c1d2070f2060045018443c0400d0081e00e2480746e610614500c0d5640c000c040d131954400c64040d20141d064031041d00d101b1b07002e44450420000160756103111481d455900791030031103020b810034040c1c1c8580c003150036290300c0b01c4081101414443c1c00841d2070790a03a1070890680030f0203810403c0d480c1d0620b0244051a82c01034080c1c0c1c529003140382150810340d03110101b900240100f61050300a5030900240404502d0711513980d0019083c2550a03c2609203039070416030743c1d09400e100c02009242e020404100d94052465241803252140c41030b41c001c44905c000051803c6402c0c5c8084d203030307490404d030581440e40e0000d03101448046048080c111355458440041c01860085c410035075240e4000500302d01003034003135104507200c9a100c060300380340752048090745590301d0090050380034040c6040c20500e0140d008411140c1140c941100408414070039078240441c58205400a605600c0140b0802d5140b0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 416950224 1250 416948974 416948981
    0xc05060313050a050601090b0d0b040305070f0b0c07030f21020c070f0f090501050a030503030402010309140307050105041103121e0708040305030c0105250e0102030f041e080312150103020409 84
    0x140600300804240d414400f01310300308e460049019100c3c001c58254407001038000b0842c554000e401d070500603103a41c4d0504200300e02c80e5400390020421813401c82000a15000ba4001d0b18040d8020b5a40d011002d5030001c00761150039069130380c40c0407291200c1403040100d446800405500d0302d050151000b650390340b6500101d1000380d070000c40c410ba05d01c50060140285a02c1100e0051404a4240c0e44072032850312215101d1101038006030400d9160200081480030a6501000e41418502201e640b1500e5043c42802009c09a400319644032600b40310340c0c024500020041090005214203611f802c1059610b0700c0f07400d01c0c880c1c040d10804014041e950214000c0c0001d00011801940038503607402840ea002c41c03c41c1c3c401001e241241043c0030139810481c0f00d00c05142003075191414840c810b00030700c4005074914080c0c0c202c1101e00b4840010082040120090b5004070302e4603417000100515200e010b4503071240500442341c00f1002c02c440019460380301c3c0440420300b201c41814014a02500c480032542071707 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 416951474 1250 416950224 416950243
    0x109060c02090408210919020105180a03210f090503030d02030a11040b1207050f04150c060e0f010e07050108040312060305030d0b0906090906010504020f0c0f0c0a080303040c0506031305 82
    0x171300f0a880304020510006008240d154042131030380ca50f103482d40f0360000e8030b14001c1500440c19070103008101c41e240d803282c140c0c8038059a0000f03500081420f4407903045002d908050586d400007800942440030150064947c18280c640040165041c4811001004003d4200030181e9900c40d40304c0b11214143c110000081c0b001d840c080e1050b43c0e4409401d0803160724100e02070143c40c1002003c006c140d1100c00c0e203c061b01c00f520541f484c07403a007814403910110741c0c0e29800fa501420b62840c0c0903078514840b50014003889501c1100000780018004450056107070202e5100d661b02040d400000500068400c0c251642e120104030310000f00f20307440780c440510395000641b0740360807d662002001024a00440010380c0644100d8a00c0d0044c07812074400c9840740c0061007580d01407a00481d10641c0402a00155400f601d054002c0311076248070030b088180d54096201ca654082c1d410a28003003500c18000c02200c4c840d81d00140b01d40c004d00d242209114030b96000078451044036400710840c2c030010740280101c408 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 416952724 1250 416951474 416951527
    0x10b0f090109051e030d0e010503040201050c010b040606030618091e0314030907090509190312020f030a06050445140d02010501170a060902010504030b011d060109060c02090408 78
    0x1304808450030315140c41c0c80a40f500c014000c40c030317800c036046030303408802c99a0096080c07802548907800e141000340075050f04030034141d0203810001c020580b6607142c0c1c488021140200d00c180f807204c049920407000c4511401002e031041d1480750300c1d101c0c000c14034024400d0750707072081c98580c20042c60500300340426001550f042d403240d00020700400841106000d4203801800020140000c180c510041c14825148100c008091200f142894a2082d10f0340d03042c2d550342a030311402c0c203690349040d03c0c540009100d00e004031482945400040505401c0110a110006103ca842002184840c0d10007000004080342c100700f54400b014030030b2001409040c034402000b1030341c000034101d0701c01000740a4290360050300140d41c0081115484900c1581c00030f200124540c0002001501d5501400100d8030ba2003103070005444140518000264104040c8403c1c00b039020440500c0495110307140111707014041d6203d00c03000501c0505150b030146c9000414150807a01c55501c007841c18061032805011500034000504 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 416953974 1250 416952724 416952769
    0x31d250308030106050c071a0307080403140c15011409040609051009081e0a09060509040f0c0c03030c0305151011010527070e0f0a0204270f05010b0f09010905 70
    0x10301e062030411a0001810140e0308c072078102c41c1100e801e0483c80c00010082410000540d000c07a0030305004040b02e010704490040e1140c6c0e1400c442501035960f142c00060700d507034040c0039400042d46c4110444040c0c64643c0041800480303481c0c580b2114080c04809806071554000e9050144950707035a03125801c8020304c90742d9403945543c090380300d04071200720030104400c41c08020070070440100c0d132021243c0c080d90319070304020344c0714905840890004d040e0311404c62600d600d404581c4506035040f55071056054481da505100603921500101d09a4209039210051070304174401042c200e00e4550003a220882032441c068920314204411942950310645d4111001580c54121623a140300d54041c9010315800f0f0070082c0005403629020907050400100343c803680c10102c4000c01c2c403150240c1c040b140105144420b50115402150442c80c0c5442030480c1c203048145410000140c041c03080c01080d049510648055040c03c2c1c540c00c00c2c545550110310294100b0148100201c0d443e070319800c12100c0c0d000c200300d42e80c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 416955224 1250 416953974 416953987
    0x306090501051803031f030b010f080f1c0302030a090b010b0307020d0305060901031101021903021b041404060f090c080309031e3c010c031d25030803010605 69
    0x64210781e0007030030010710b058404220b003000c12800804c1700d800000c182c0c9504802800c1c0d101200c1202140d41001b801402800d00008101c207125040b60b0a8602203000c0c1e074031021001065075964a41800d00b18804181600d0320f010090081c1d015542c0b041003407101054a00c043e6403000d10044003600500c44d0000040706200c0d040e03504100c8400d07810f00b181004c02841c1000c0000403d07100051000409210401c07407540e005902c00d100254100c80800003a040f000c21624020307480c0c02d501040c400400200c5288c81e1680e14240c000c140c2c1d610100301c10409030b0b803225140c803c041c00301034031160182a01d0b030051100154011480100038174581001c2c64aa008850805060140d8005110800600e4445d144031a0001041c0b00104203100f850002c0140038251100c4656070b02180da00701148a541504208101c064014242441242c2e404111040b0420114040800b02c0751014495500003840a80c01c40174034800441100c00742c07100d0014a513600c0c1d03252207840d0300c241c0281000034000302e40c1 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 416956474 1250 416955224 416955233
    0x21314091c0f0912020f0907120506150316050f0721081e07020c090f090c0a14010e0f0a060c03111506090604060812040e340513030609 60
    0x1c80a400c1a42c50011500c0e104000000c2c006100f40c0595070306900070754003503401c5507a040c00c4001c40c800c026000d04420b1030b040101901141d204980020300a040c40300107000c6280c640e104642c0c84440498140c1162504407620804540021815060100c100294400c03819132401070115148190554459501c0c0c1c101010f50440089018005011410051018080400300d00104034200d074081410903907103882e41249403148103001c00717420a080700280011820b18851003441220004100d840c1240c8240902943d1111407049c020910b041c0d40c0310490540c420050121001c0c0c4c024030140302c07021803200040003901d0944c0503c01140c0140451341c10150001104e40c120f0304c802c0c014042c1d80740c2d0071815a010903401002c03544958505800110700703035240d6000310041c10b0010211180040920a8640c00350b000307000b45481028603a00060709074000704000041210507424500e403800c2c1400c880015204000c8078481400024000c1405007421111410000c50064001140c0c80c102403c1 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 416957724 1250 416956474 416956513
    0x809121c020709090c2d09020a110609031e0409020c06100914040f1407030b150d11010e0a0801050c0a27030219030b0a05100e01030c0302131409 64
    0xe8181824042280c005c40c1815180340c040b40c94600900160b9038054114007170307504c1140c41c000314140f01440045400100741c2c1c054441c21132503444800f102d00b0359040e401c0d075411046030540010342c02003091240030000c1341c1950b480c0e075203001420740c01c080c1c40e80c10b22005c1ea0401640c540342c0340c0c0041c0404c10003400c0b040400c4020f21900000300711298505442c209001c0c0003c1c400786c1034818080070b0741d0406c49a4408201583d03031351803e9900321516461300c61915003060702c94400b59420300c0d4051440b03140c007002d145401c0d503000e8000a070784d42840c0015265400360301129584504914800138100350203004040c441c01d41d100c074048e03444402c44000780001c0071540a404c90800c0081001c0c4018505403a00000e894040b200b5441c1c1349107164007683e23050380b42d4000a059020703031418400e4020705a00100d0007003c464001e0340116498207495960500244030203444c44a9403c002c0015091550a45000c041140d0020440341049009149004400d451284841c1c0c005112004454107480 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 416958974 1250 416957724 416957729
    0x80111130b031e130f030c050d05090a0e28050603070b0a08060906040204091517010e0604062408060603070608190e0c2106010803070209040809121c0207 68
    0x880c528114100014407080f0700059011180c3c241c0d04603c0881c0e11440044098549260711050a000e80401890700808420414408550340d00c10810741c038440600500565089803005014054501c0c58007400d03505604d0701404507007101c0030000e0b02251420b0100020807004000207004942818880181841c00700d050380f26480d041420702403d44516480a030654219508449800403900e17400002070007886681d01c0984010b16003140e25000b45e40c1c0c8401c0c40122800d02c1d0340441000c41401c021070a0340e429104400701c0707400050001e00091240d0380546e0075841120710101c4070200d405c1114644103007540000d58158061400c10080f0301d030800200d00076240e01c3c13600d20700c80e017011050540c100c0300c840030310794805448642250003c83c042000c0854840c0c005d1244d24810024503c0302a0702100e003441d41054005c10001140d03a040000031075852640c05024100c0391707941c5480d00c204a410070445140e00207426540440b92040c20000c403494160030918401498101540180c580314196 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 416960224 1250 416958974 416958989
    0x8010503060c1209160603060509011a04031e0b0a05010311010e100c1703010f0f0b030108031204060f422702160b060301020304020a1502010608011113 67
    0x4008202901101c1803d9030b08041011074403540d01e44840c0030f036904040203445400c003412078017800052030aa054014208540058401c0541d690321070100760f1890042011000800000700401c00001e1485000481f443c00c00401d0342c42845010b0342c0b2940c2e00036090784c07103890b5103440e58010f209002c1d000d10040030750032003428000c205101005c086001d50504404090521582e150796000384603030111408400e072480020280d130b0750f131200c16004500303a09015400e00d064a08102091740c480060859041c0ca103440015801c255501d410400f900c44000c0084840c103482e0205c4070848101d6018048607144680042404501044108500400301020740d8510001c80c00315448442d0b69020300c902640c2d90398081c5031848550503030419814802c8414245020b00c0081e80030341c038900748a840120140702c0c000050071601c900b0101401e030b01007a50007960108000d00d0401c5400e40b544200402d0031014000400c0031982c0e0206a0300f1100c0750030001c001c0d42c000080300460b600003000140040d02d0399 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 416961474 1250 416960224 416960233
    0x14040b120a050f061813020405010305061605040e0a05061336150c0504032301060e06090a0f0f021812190f02030c0a090f1a0607031b0f0803010608010503 68
    0x1000040c021403403064500c0d40c05c2c1070322400716040c0c4020318800480c198003d401444956520310b0400e1b5202011100c98501c0840d4210030300c2084e202d041203508554000440500a84881c9000c100402c0c01408840e40305d4190040c10b44070049600030204091800515104415a0b07000a0b00707540724000c940350080490124400c1c000340341100d01c0c0c841ca0700c2102002402052382c076804d0b51180b280740c00c080d1044079615103007401d0302c0309032000800f0010900001e00c40c02d075648034800c1c0e00769010340e05582d103c0d0300c441c009141039105501102281460740b0002c1440c1c42c09446002c02ca031b1000e6105c171441c0c02900c90208490901007210140340c550000241003031004102d80d0085158a44001429802c0303541c0c01205554042010202170b4074010494160319a031500840020982d138a660302c562030818699246510400355940e040e500e02800b8140390031400c0e41c00b154601c2c100300524038068204e8003803201003118514881007880c4180c0c0000e5480d41043c00182480c28140c5c05070784664170 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 416962724 1250 416961474 416961481
    0x2d02030a0605030c011d151201090b06030411060901090314071d06030303180703080418150e07110709060312080112080412030c0209071814060a14040b120a050f 71
    0x4e00011200e004404039501000403200600090380700e00861402000700740008c603074580204503521809040b207480020400041c40b0701d005004090104076070103003494540e030301c140702541030450040c84d9101c014900b020f0002d440b50703103444002901004400e800c1e440400c06000c0d18180b5004144280d8041141c80000c3c6827030b01c0060f5480c840140722015101d4010200f113003080c8100b00200c003541d0b00151403500c55071500905650122216507407000f1508286080034868002c1607000b041c6d4404080258559a035400113482c0c5180642c41894140702e50040040c1752209171242d000614031401148064602c1c010000b40400c0042c0c20130802c1c0c8840400d00800600803030b0440b0102e074400d5800c0c0310340303440d81d00b000e8031303180358203600030303401c5091002040b68065109524002e1041c0075240d100119403035014699850300c09210883d00071104100795224940542d4502c2c0900e42c10102191606442d0742c001015900801c0e0407200311012101880a514054003e555114000320440c203920314 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 416963974 1250 416962724 416962727
    0xc0309010c02060705060a050a050f06090604020a0e04061202010f020d05160206041d0603010c02030a020c3609100209030c01030c03020918010e0601020604030801092d02030a0605030c01 82
    0x105a055450601024008600454440509580d0b00640080540d04585010445e0038090700044401200c01031610001920070140d80d4400b500803180600103143e01d90762207090000951244080d441400384d21444910303107603600d028800c013410300c081b07031002c80300c40c01e20016081c10700b0354041034199086108200b4840e540242660000c1c14418505241401107001160681c820754100e01e45518000003c0c827002d00f420850240115030950082001d510700d640708903124054040f00c5401a086814040e03014a8104505940001c1d0003605016000440701070401344075807a21240680b03007019040181d406000d105103104130458400a61804030740c980004e88400300311001d41e0606580741014142c2c80d200341e0560340d1056010341120000318010718441007458017440b40d404a070000c03900190300c5500c04102940541d0b81a11410100c2c4d090000c00805046941d5070110008014035000505481e03d000c3d05080943c05900140c0e2400d00e01c40e888203407686504801d000b43d0008000e0740c541c0c0d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 416965224 1250 416963974 416963977
    0x150603030c1b05030a1e0c2603040f06080604060819030906080705030604050a0b09012303010b1c1104090f122d0c020409051606030e06012102130c0f050c03 69
    0x3154400001c80d007206c0f98951020f140101160060710820f2070000201e0ba0340003466084a182c0c018101411015201c0c010090b0349200707601512030320525a9004000082c0030360103440e00080001c0c4007003561610382580c1c503c0c00074209046080018083d5030801070542140908026040d04d103445030f81e5141038038024225100140502e801030f80d03900c0c00640440f44541c818060004000c1c01c2d05103d5070f503240d0070003000c001d00d03003160b5108120310b0348000245414880d200c0b4901000c0c0c111004402003031100203055003034030025218010005e03020740c16603489104440e100b601ca20414a403041490070001d02c0008104020000e2080001d2031003443c1d0302d00300303540f20789140d540d08103802040c0000c81101c00b0007030050000e400a0505440c0820000042220401004c54508101d065039851504078151004d5074014070007a00b2240041c055043e00c115034180c102d50703000300c440c0c0d494019404500010110743c1034080082c0d60308801c5d080e4941c0048943d1044401d4680713141040219110262079 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 416966474 1250 416965224 416965243
    0x3090e06010c030c1a0708010f082802030f010221060102011a04150806190c080705120c120907050109051801050f0319060c020c040c1209150603030c1b0503 69
    0x80c4040300750148200204c0171100300842c0d02e007038850040e5080c501e02c01741c071481c0c0c203010704842c03161003060200c0c0e105c10010304140c0d6415008100106c000c88561000d103a19842103086e178250148507000e01446000340020075000c00184032040d0103003035410752145205c5003e00b0349811641040012110204115640004204110340c000781c2d08440904044071000c1d250300c06d01c4c05000b600c0030440540801086d0072061050b40c1c005203c0e90f129280c0488003e281100c142020840c2800022080e2200c002e415521040d00f0008503e412001c60600020600449207645a50300802c01441556030091010008001c1a00c1004030000200310801180070305014081c0103808d035188049141d0350400007400c1c0003901c1190281c0f5562903081c541d019181640c905400740c495030a001d4902d0405115080045a20756a51003007110f80001030805401202000c0e1020240c0448074900a241840360100071403098032200814001860440c071661f610081d0001c2803640003408000e5610081002d200 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 416967724 1250 416966474 416966477
    0x601180b09060f120309040c0201090b0f0103030f1107120807110306190e01090609030207080f03040609060f0c023a051c0203160b0129040504021c0f0903090e06010c03 74
    0x103c04901380d451441c044e04070780076800f0b401d1001d00b2420780e40661050310880c0c01200900000e40d105008615003e400f84801400905950200241c40d40324045901181540c901940c49141c0e840700c8003a110002500d0544000c440050740004114180e0f51103a5421030503005800f1b585072100d40e194040c40d1090000b00c0f855100c40450034410f00170343c0000c840c20781c0107004000c0042e80e400c2c000c0d912010b9000e82e100d24440e5401e03d0a44040000640302202d00301e9486148035030400d2812105100c140c1030071400c0c00036100c1e090740165215060400b0280803558151940304401106018505c01541c1e0807034201954107446d004a00302080b42c0c1000c80c502d602c3d0b02c10a46400e4022481c610400940d481881c04070710b034072800c1140f000e030300d18121610818a4800010362140d05204001031b5144804841802c001c10045400c060b0041d01807210b81000d40e980050001042c0f00a135090000c041044030355030005101019009500c200240035442d203458441d10701000013070301c0e000c0701a80180 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 416968974 1250 416967724 416967739
    0x8060103020904330605160f060e150718050a210c0b0a030e0102121b0d020f03070f021b01050334031112040b04020307080601180b09060f 61
    0x82d42c0b80c0d40c110f4400d540c440c0000a40c00b040c41800c07442c401010f860401015a5070b0f4a00068082c400c1044e06e81c650a00509030110300655501c04200b40254003040741c489464a8900300f800a06200340c2103020000510a4a20706d004e603001031062080300042598203810300000d2101b516101180e005448801400303803030104e0081e2281d00c1c44550b2900082501c404541d011901c041c0060207011049610340301807141081c0d80400718282e0081c40200b00341c110300364001072400c2c0130721207980440c8200c0d06552460012202c40640603607010342c4080d881d4a100100f44181d46511007005c401d4000288003801d2000c071030111905002090307a8014ec1081004400b050000c82d90540c0c20f202c0c0050240c000461240705000254040b10310511030011070f01c0c003400c22110680d48021204e07003425281055803250754a6503041c00c03054028000b41d805204070740c0040b4080d4010401140a0002408401c2e0740c2e41c0c0410100301500e8162000d58064144101400907540f44c0d5030f01082651030445610 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 416970224 1250 416968974 416968987
    0x51509010204050d38040b060f04020a1d030705010503010b0a020304090f050f01091503230607020a150c1403062d1e0a1502011401170609010c0806010302 68
    0x5019004a80110f54024a042e10030700411000a02509100310f40850079841205005c2501c080f1800c0b5006010004540ba000500041e0180010940c000c000505c00012642010301040803a08015200000b1481004094003004a0100d488480190840c021701065080800080117400103104440080c000400e40907401e50080c01540c01410403440d0400c10524035803180d0f40600016102c41910300c07044400030030b090b000390082940b03080720300804030400c0c1c6c03642c0c4d550b140c80c3c1c10354aa61a800b00341084403d00d02c00050190600883e110350043c603080c80c89081613001485001c5000b489130b4501810602506c1d044100d030b041003e00e45840a80300c1c0d68140104030002c12001c490042d00403000c000c0c1c881010710721408803881e4010384501d20000c500c01940008824480c40003540284907010400c03620740680c0c1e003202d05140d01d10011403601400c1001c01010042038000701d810b85071420300c02070308080400205a01400f104002c0c00b9619400030043c00b042d070301401c02c504164001401 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 416971474 1250 416970224 416970241
    0x204050a051b0a03111218010903050a0e0a170607022803030c02030903010509030307091a2203050601032102030306010804120207030b0906102301030f06080a0b06010306060c0515 79
    0x11180002030103005c1d554100460310f0320f4030110110350788652110084480090040c05114a82d5060340c1a02c0c0c0300e00d000104001516030040960381164400c020380c0c0c0100344040507400d041e1881041c0e034001c00040c144800f02909028103504040790800e41e040c001548855440c04c212440c0f034060800042d010848940cc80c21031042115090301903003010309010030010000002d6200e034100d544c8003050240c6900c00140d00244118031410b54460510100c040c0c45507940d00f21a1521400451002142d500da480e107040c07039000d034130a0320108c000b04000d40404415410621280c0c94900c0035502c2d5161100028007170100203003015120f0b04429020180700d03402000040080d50304208000620f02e054510299241d03c01c072081c181e442d40c51400003c05041644100344001551140c80340076000a90045009010000c3d085c031115444032400203a6400a110341c01046004400300700103481c00c40005000e4440c00d030302410410840400350300c0403034004906510b48031040c080344034142c0c841d03410 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 416972724 1250 416971474 416971481
    0xa020d0c111909090b01030209130b18160b07020a0e090303040b09010b0d05010605100306060516060605090c090f0f0a260708032107122a05070204050a051b0a03 71
    0x81031030f540d4a41005101404032910714203040320b208441c090400e0703841c9120650140400b10780100306050701408500c0c00c82402c11070311000381c5800c0407a01c0404075030800c16150b16499120640c0039200240a10541c01d2051b01d40001c2c00016a10900c01d003082102c140c2e27248802440034000010135404904401801c1d00070a859043c001c0069a8805050078058000d200911905204507081c0c01402d10b40c3c2d00901a510440d4a10b803151410040018100002c82d101c00c0003c551865540c0c00c049000d03900c5c040c0440c0210120390001e80c44180000500803000e208001c2d4503ca1480310990482030782d00c0000003400d07903d603004d036821a002071510340c4510b06d0b007075883c050483c0510400801c1100e00003001d001010b0400b51070340d80482c05002c0041070701c4000d40d009000074802d4003000d42000f4144e04518200e2145c090640034003007002840c00c8a91080d140c0740000200b0006245003903140c2401072a400c03002c0100704200509000361910090b60300a110000710000204440810901992 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 416973974 1250 416972724 416972729
    0x50a0c0c030503041a1f050906031c0203160b010905310311030703020607140909040b04030507062d1401060305060319050a20030706110c0d080a020d0c1119 69
    0x54800d0b04506103905c04401b80d90308004111018074030300000003450700e412114a0301640e0f0103409040008401480f601845000180201c25840708200c0d00007002401c0c220f6030032040c000c6a0b01201541001010390503140c0140c040124104c040d0511302d9144a01e90301ca10000c11031501c1c00345107002c1481d0584138501000c00600b681e0001040500502d0340105060748500038694070007288521846c3c101c1100e0080341742d90398000a5100000c0c00055000b0718aa4000c2d0103410424200300c119540c40342505c1700055540c8000c1b88401c004812011610300769903d88901c3c200c188205c0388480495660aa014811441015141c10208103039440504c600c10060419009208000e03869040903562607040718021180540c440034035002c145040c0e0f000c1c44001e14020080d0800500d010401c40c0c0310040307010341d89824080c070f0111843d07507501c07012403003d214820031050351100c02404000c1c0c140180b50594100b88007940c5009800903a4099445038041c00890705041c500000c181c1392404071010384c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 416975224 1250 416973974 416974013
    0x110c04060f03020319080a030504020f12011a0105040b0d11130602160506040b09040506040b030d12060902030c19120c05070204060503030405010c0605060f22050a0c0c03050304 78
    0xd004941c1c007444001c10801c0c0e0340280e085070701015003904c43c0807a55135800c501078105c40090180c1041c2a229422480e04a0700003480200d9000380c0740300246002d000700505401e140e54600b44200308048071070011940c1002420101d007400d103048655500e500c42d1000404145a403040d440b031180007940c0c15075140358401c81d230001c0615100d000c00303036652000e20462181060188000225071034114111015a0b626041c080d003001008014031028140243c21503034481e854492007030311910b040010740d0350340d00303199601c045444100b281c2900311161a0000d00d50036004000f00304402d011841142c810b210a040e01c005800885401190807810440c1521052070a002503c6400c41d4003c0103000c505008a40400c030a541e0340081540c1c0344910300c601030104001540c06400715155520290b80300c0000780c2000408810b280001b6076411520310800d54401007815584803401c001d220301030f8032040b0704a0400012154100c05800c0240082e0000d0410100000203010000c0304524036079801d0f00c8 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 416976474 1250 416975224 416975231
    0x12120318170f1c15060903060f11030a02071e020f060a05040b03010f03020423060609030a060507030c080a0b0105090922030e030d0203031b1e0d0203041208040210110c04 75
    0x1103680c80403444200f41481d12400c0c1003070340f40601c0c003880021410450340c10707480b0b00640780d29595030780000c7d00720a482a902165581c1c084a4505200310044d4070489401c01c00680d1020641350103910f540202c4940c940940040c80c80c8d40058503020310744400c1300d00c1160417640312108600300305d64510860f000710280324800b000004500c0108881c2005480c42150244440714203480d01c011100b100d04800c1009160274400b040550034100300501008501a040e82e159003a00c2d1106010307260140d8581000036540c1c0380d40c1e510207900042d010707003000a200041c8085020070000030310714014054241d00c650204004656041d080542150141d0010055030b400b501c980e00300074000254412503d4000d014412041c2c120764400700841348601076003404c0702424201c0c0e10341c01c1c003641c001400c0c1c03510b02c0c04c140400b01401000303040a012038151003500540d40b440c051034804d1000408000709001e1040d04d00502005070784451244079040451703c0e1003040710400e0108140b9004d55418010f400c03525 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 416977724 1250 416976474 416976487
    0x50c070c0e0106110f0706051c0603080d0501051504060e040612050607030501171b0303120f1b09090a05091c0309051213060509030c0a12120318170f 66
    0x16201d0601d040368025210346012003003406045440d0350000c060060300c0d8020b10000e0000d03d02a80141084038000c000f90f22403003132050040c0c401c075402a0025100d8071750100b02d943e420146030003900d0250405a0f1403156103160146694001e000d1400341c1d006101040d1040c20090300c840d48404020708508196410254071400c010f42c035010169046400603080800201e08010045081199041c58000500d21182d0345940742161000144060740c0c075000800a80314817501c4694090301821480308a1503403810030603151003440807101901820510107210001140e540c0740941588144004004195507491400d1036042c890003c41403075408030b205104c402c40d968580d1200d240380e8450400c07a1085034510306050310714003c460b500c2c0180a0140e100b071161354420b102074000d000000e03084805034401040011045145a0800e0800f101c62002c80e40a01a82c00100c4a15418900b81007001440c0c408202d500c0c101c8214000c1c0c4a84040201c41c081d504c5036030200e9074540c1d00740c21695101c48 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 416978974 1250 416977724 416977739
    0x215040b07060b09011505031911030709060207060507020f0a0801050a1a09040503031614041215060308090d050a1205040503070611071503150b0405010216050a09050c070c 76
    0x4121800030b44041e4900051010181442c1d50001d058501c002d220035014450150211400c1e0f100603c5100341005076442c003400c1150f20b0003851091041c00b00c3c205e440f4904250010041c5407250301100440d8011101001469085011140b64640540b00180610045000301d03206111640c4000d04a41c6004100f10510425a1142e04589801c440c4060380c41501010805100e0055070058603a030010404900c0b200c0c840040c1c0084d8100c0c5007480302c08510856030050740c642042e07000d5500f4241d00003a02c000c0220102078440241c0c1500010030000e421134541c11002c8c02102107040c05a02d025502e038080c013004125020446602c03194540d1500e82c42c0c0d4004199402602c225402489450004100d5500a50031400b49030f58140c002e05482d0720b4507080b030740581171410b40c0c0000c1c1603851260051910311a84100098125200b549985c0c4c0c1c9450002464110030b4a40759041c4640d0610038011039035203a000e0002c40c0e00050003c10191921440100ca6100ea007400422200b07014400040c0340 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 416980224 1250 416978974 416978977
    0x71d090c1c05010b03010b071b06020718150302060f0d060f15020d0e0105070204090206030f090709020a0507021e0d061e0209010f0810090905010b2b0f0215040b 71
    0xc01c007049022001d0300c0c803041e81000340c803003c1c09000c0402000b440180401c06030f410161600754043c0281c012401600b4455001c07404d4242c00640040c0c2001d0030034080c00040718080c4035002900841003000345c22510f49059041000c1c00000e20580c1c0004111030a0a4018150ba9005021020410009544290200c040300711807050b0407520444100880d042030000c6042042d2401c0e0340c03242c1d0120412030340111500d510004040380d00540e540c01300c07405a220403000e1486444a10010f0b01c40b408c258959030315103e51036000780d000c54010060b071020700f41c0c042c00380c440c100d40c10344189400c1c00c20821403414045c110340d030040d00441c0154001d01071106503081031025400000d8a01c44202d5540c20340c100f68415401010b0100300003501c9600040d200c1c4508075846940500422030081d102c545010a4030803440c0140c1d4140c4d1240040146480c01240010480d45d0700000d1119554501101400070004004041c102c490401f0010007035440d2194280024040c80c004956119280c50902c0c416 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 416981474 1250 416980224 416980237
    0x20415090b10050310181103011202090115020c090408040b130611160e1008010c0221070c0b0f071203060303021504020a050f0427050f0312071d090c 66
    0x10380c05550400c0c0b40034003480c21280102d1815004013100350410840b030145c2007240381035a4000d0b40d01c80609101c0107551000e0b42c0603050800d030011001c03003c0e004000c400701042e0810311142c802c003045004e80940010f40d00c03a800b030058811103503d0391541440c0401e4099940003140c0c643c000540024021045001c3c0d00580301c10780c550340c11800c03882c1d162a5440c0281102c2120050500c08103204000702407991a501141e140003404041d0382310a20142074481c07400c0003a01507030080c07490020340491400c03140c1d95031041b0000325040070110b0300c03a640e80700c1e024400c00b00400c00000716000c1c0d141841b412070b5442d98201002c0e41c624080040c0c020000c0c80c1d00d10042e00140a0480310084010b10b05410501950b0010101010a400c01c01001402000c030401590b026a8405500d11040000124a840c414400c4440102c207071072820010704007110b44280f29415003041010a2141451481e02504a141850714801103201051450500010810910f900001e08000c110000c0c8078a0700030044c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 416982724 1250 416981474 416981479
    0x6080a1b0f3e07090203090304051c02100908010b04020c060703050403020f0703051609020a170a090213020a031b1d0d0203060a050a0b010302250c0b07030905180f070c020415090b 79
    0x3c1e1a941c07a0740c06001c9010a5030200d0040c0c004001c01c101610344442d4258901580d038201c01901078281d07002a440304004000e403030204a80030f0301000323420000e20410994035015a0258900602c00354902c0c1c480c00c1c0101000d091555a501007810b06108015a40f80d0744200000c40b9001c13a20703030130720030707640c048501c8030a40300110072801082900c0c0500a460016080c1e841710540640010031600070448010f102c1da81007a518102400035940b0020f100c59200c09080c401a0b0b904d140c000001d05030340316005203005040c500b00b40740b040030380d0010488011707640c206075030001e10512100241d94041d90840c0a0761620a075420702c843c07500990320841c0100341400301045a02400700054069024020300803410321414648401007107156140000300e20311454109440d26200e10220403140c02c0302400b5400200070400a000307a0905507201501c0603501000160546004e0072860f51900c4001c120b042042005210350b000c640322a006000c3d00420324026484e640e403a81d200400400c403541e503880c03 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 416983974 1250 416982724 416982733
    0x90309130f061a0a1d03012a020a1a06060708120609010f1d090a06090b010806100b09130f180219031e14060106080a1b0f3e 55
    0x601007140590b02021503c14540107050421661080e03034802116450300c0301422545030b44d40c1084da420720600c1040a001e0310b41c60241c80300c0e504807058900e49024080150744c0030f40b42000100e85840d13640c050010a81c0300e510b1207655500045000d600900100034201704004c603505000b9004403904502c00d801c20f40361001c00360b980e140d010340410701c18418840b0210301d207242d03030b0b68000c46c0c0e26010ba4080078403411292241c090703980e69130807515650340665040d034804006000c101d105104440d00004003081000c00c680c18520503900700d2046540d40c6100d01c49241da20384103a24690080c1c4003000501900f08802c10b44000d400400c40001d01040344121204001d103102454001681000c1d00c0d00b00e045000031080004102c0e4881e80b1220083e2070344005880b0f0906040d4042107124060300e11030b66000c20750300b0120f1100080c1c941c4000f00c0e007241c415000c05803a0f00d640c0415460b101c1d803424601000007289803100c0300f070910001495802c890a00d05164001558042c000388408000b84041301e = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 416985224 1250 416983974 416983979
    0x40918140106050907030f1401030501020705060901020c0706030504033605061303030809100c05040f0501050903100506041103040c1a0705060403120e15040c050a06120203090309130f06 82
    0x4a0890303405005180d13204040001259040b03109a00c0022100358880000651014100360305100070710036031080300c0301c0c1e40000e0000c0820000341302494112038200000d5003003003104900c1c5a150481406400105580c40d4001010300d03204000980c60084003180c540c0940219817030050020187c804210f03080781e1252000217040c103020702120b8070440505560f184290a50b0b038120f4201e130b80500301d40c80074441c04d8941046808144608080d1040726180d40d940ca5241c00da01141c0014690b0040781400010b000c0b120040d100801c807101c2c190100c0700002055603d0200040040c1141c1ca6100d4905e403010041008000380d0400c884266100008030011480c030aa40d094203900c80c88400400c540c21040200b40021301500001466040d541c002066140124024a141080071003140411400002c280024043ca01039160040c003010755405480900344200038021b80200d00380140300342c0e40000011002c0c8002d005858500800400045060305407600c000d02400124420508103032504100 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 416986474 1250 416985224 416985263
    0x19050d1518020d08130b12060a05060301080a060519090524101503290a0b19050f0d02040b1b01050106080103060e1005101a09010c0f030302040918 65
    0x10080542d401064144a202e0741e03074407030000f5000807501c00b062841009000ca00840f011000d0030035402180940480c80c0340070010060082030541c0071758010b180810040c003d650703021039180c182d035802c2200814952118480d005200b03625003103d1145900d0704440c4001c00c81d0206140520b0032080429850302c1c01482a4141c0b010000d580c0c2d040700c280449001c002c54000c8a5018103283c81a003000950f426600d980b1080022056111070302c00888411081d1061503c0055100900400740030700341042441c0507801030036184110300c80c0c14000013049802010035460120f0780201300d0075070309544851340d8650144680d00400c00020764091034400c40b4424460520440d41203c2c002e0ba5005216407071a11030320001d000001c0d051100380100300402106001074007c945c060759182c000382c0382d40307450300340d980241e5400e8442c01d101d502030401030181c0700c0c0c1e13000d2541d00200307030007918410508000e8030f0f06a00334451984a140f07024140f10041070420f01c15201020990300a40d18107050b54800309a = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 416987724 1250 416986474 416986511
    0x30c11180426032d06010507020d05012304030f030923031c0501081009122a03020706030b0315010e100807060203041502060603061f081002070c05011404030219050d15 74
    0x1440b50005105104230409480c007901c500c802c0d02e01071000020080702e40a00000d854242c80800c0d041e0f0380c140c0c0c0c1030000b00369015540a004411910342005103504541e2407103042e162201d039180490341150380202c40b25005208030b80413562a40d100c0b030359183c0403042d4180a400241b04e904024000e40f10b190505128500880c034840394802000c290b801d0207648142c60002c0c1c84100e03040041c503c02d4a1107146400751201824144c042e400078231032245400c0300201612200d4081d540a50000070034030b805403000c00e842d607054a42a808103080d50b510300700380c030b5070b416415841009548510400050740036004030040054800d540f9400b4103910300040300b60ba41e414183d0300709405038080030005491500070b42910400c84207a500304c02c2c0aa0392082d08038a828508420200c5507a800500310b420000c0c000740072001000700382000c8030140b06080403090140103600c0040d0058102c00c50409420f00d04d5100c120180c00000c040c004c0d144981d041c0980c030040c42c0044941050f00d400340c0c00d500c1e5103607600e = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 416988974 1250 416987724 416987731
    0x1508031207030e0d021c050d0c0c05010501050f060405060f0921060f0f07080c090d030215220303090201021009030804021e0a060c11030703030c11180426032d 70
    0x40081100c03001303081030380b4814219446c807101003140500c81c1100300e5444e400b464880e41200e43ea45c0342d0600316801d00900b1a001a40220f02c184058213041d0010307154101036a044030790489415486c2d40408020b03101c18410003218550140e040d00c1a4502d4800c076400c4001003160110803181295140c03c45548545825580b41070469542800903507090721034040b20b179001c0b8644054070b0800c6002c10100e03103404c2120100f01c000da04101e02c1d0716010802448110307405001803036a14101500041315220040c44010094101030b21403400c0c8055900070011030360000c07000001080000800c2c20000c20889094404a2043d481e0110f903100c0084504c038140c680b42d4005241e018840d103800b41c01d0301d10140c8004211944580e07090500420368050040303e005501a84405916500c20b10306590f0540072118003e101e011b8045000c40600b148a004540c85940403000f0000d17002c420460005494003510343c001010310000c20015041c9114842500390a03a05000c0d01400c1034022400785500000c9 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 416990224 1250 416988974 416988977
    0xa09030e040506030f07060f080c04030f0201180e0a14070905091f08150108100203070807050d020c01091202010f0b090408071401050408070201260103061508031207030e0d 76
    0x1552003200c0d8900741c0c2c059900070000400300e41185809200e280d041071030030b502400100b91481f00c00145242c000700c00540c805103a6109a2525056540d44007046910b120301034100601c1c5010a003149a48403580310183c050505400018038181c0480006002034000c1e1050800d8401301248420b4080e5048e0705c16500d006102c901c143da10758542d43c41c0c100c0d00303c20814014050650001c4c134220188030079045d0589502e072484107981001000d5261091007220100320510400030005102d500540041e00702185181c02503580103c0550030f4047d0050521103031080d407030289403004100b11030f8055014140325400912280c2090701941080350380b07070154030750400301010016000a5003c0c00403c0000d101d54401c80400c0310f00c048039800c40b4002c03202141c4e00540003c14105643e0040036a0004803a200e50980c06450b081c0380310350103600d045c80001e0015440e140440c8455400c0c80510300030f072100108403070b01c0d511120052148400255080f10200346410700400555802041e01c03030030507215 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 416991474 1250 416990224 416990237
    0x4231c1110030f06030c031406040c0e0c0c1603151107170c0a03090623090415050d0605060a08070815090a080d0e0d0305070207140a030c0806010e0a0903 68
    0x5030340c24000601450400d94081581d1110f01070140209481004003035402a102c0a00040c01d502c0c00d500303240085421040075900c61010407001035030001400c1c05940034132600e0941610b819640740103070f00421800c24040e0042944207140400880b98000849000c0e880c0d540003c440c035400d03041151100340c000c0554080805c5800045800c0340c0841c00c512000301000b91034046203220550400030008000c40010f51400010046036612008407089182603006130b18040108103102000343c811780d030703440740601d440b40300001c005038102410300d0042002910f010030f4004585000c20007080c1c01c0324401c1c4554000f0601180e4450000b03000819a9421801440f4803204181862022800205415014030854501d000000d10318406060f10b40c0c82d00d03202042705501321207050304140840c41003008040c90b00c02000609540014101d0854a03a4840302d01d090a4100114a01038895003000e800e81103010b00c00a80080005061030490725140c060b84582d03200c950707850701901c01d8150080e000401 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 416992724 1250 416991474 416991503
    0x309331c09020f040623101d030106090203130303060e060918010f0f020a080a2c150106020a03021b060304020609040b090c040f060804050d030e0304231c 68
    0x1415800304207041e0008098488801038000010306540558011810340030210b20241d0394604030720904000c9140807100311019880c100d80050621600c0d17081d00012929900046074261000e501c100c01401d0302e02d0056541c0d1924840e11010b1402d41c0c00704034000382c504400000d0030f01d50600343e035005800080c0090125142d0280c2d1403c018801c480e4603016560b25500458081803d100b19084031201c454096103401d003196018260610040c140340301c0a08011007540c0c82030045004413004800500220007542d214072105140c01040101c0074605940d48002080098000500e201050711075802c80307800e1400f543d041c05240341c01c40d100c40d410002c140007040051406401800d5108400303400003075041d100900089800406650b01010080300150030b120b80e006007100000a000203061010003411702c0c6d61940d64900b0300541030010107564900c4010032010500c111401401c51411203c084040254100c002010102940b44550707204145d0f40b11a1040070760303012070316410400101c00300a = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 416993974 1250 416992724 416992777
    0x503070f1509080105241f0516020307030b0f091207080a030b03100e0706170604050406110301091e050c1b0c0a03050a061d1b03030933 60
    0x10500c1c1619014050b01c08004626004240304142c424800b1441c0000300c0041d5240744510045920400c034003a1050740701c000c1c250701a000450115030380500d0b03d180e070b40030150600340841c0e18007007000390f1601038a5000000e004100503c0340c01409079001c4055180c40c0c0201d003941c0c1e600e0b1401000c440034000d0103000040b0308284080c183c0c0400504011800d2142030001a007040b00418100200507600c062045061200300001009070050b41004c042c030f0b410441c42c40c00d564400034000c038030030b54407980010100b0107940c00c011500620180d0064995865a81c0d84d8064108001c4081180300a080c1040c010380103401081e024035295030302c9601d40140555003c0302c001c500840711410388107030a4800d103d600c0d2141000b000354000d0000e080e402800d031030300703906580841041401a0000e040146905400410040102260020840345103c1c010010a0550141603036955210034505554200400d60f02280540c0d92010302200701921f12500c070f50709407400307141d210ba8039245844840303d01b400c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 416995224 1250 416993974 416993999
    0x150218130b031e1204090f0b0108091f020f030412171b0315280503070e010e040c08060f0919080328020a05130906120602090d2003070503070f 63
    0x64107241c0c1514132024214101c0c0d46240d21030391102c07003120b44e620041400021a442040c801000c01d05e4214194200341c04807030368070201c296044100c081c10b0f0040861100e500d41c11200c07003400402c0e88540301d15181c01c04d03180d03000c0440d2000c00494501d0030a034403015a1138503024400c003680c4030f000c2c0000f40b00c04211003003504000d0003c0b2410303041c40101191075961580300920b10880b0f1038000341000980000751010b501c03551040303003e0f61083c1c03800d00500c080c0041242c151049414141c2c969915401c2c001d513910740300da2210b0010300408040c08000c280f200001403280840008840080e2282040407000154003203000d000150140b0214012a64000c004074412085402e00540842038455190484c0d03c03502e072010101e07000207a1011402e081303640840c01000821020000e0510780002d1142c000500d0800a0100794001189243d5036200c00194100c3c58202d210702c807464840d0f0214010b12202040300611910502038001100e188c000b401e20f050312070102117001121726040c1d001140 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 416996474 1250 416995224 416995273
    0x609090609060c0306040e1b01030609020c070302011b150f0b0303070f03030f0905120309070803180904030903080d0603020102011d210f12100b0a0e0904150218130b03 74
    0x1940790792070b403010b810341000140b006040342c13440c0706c810235032030400901162a25884450082d0061042249040001c0342d0342c0126270302800c1144000b040b401e001e095100303c2c3c1c03000403c44d0360100d180c0310101803d540149091204444c040103485c0d040410140d4074020500020218540c0c05200c6d000640300b0303000344943c0544800e0110341302c4180d5503040d08194960a07500b0403400007104120b0034520400600b4000c0201602031458200701e003030407a065110040c804d41c012107006010a0800d8480e0211100450b0000300094640b004201980013504142c070003030380150700f880040003048031340d03e408500040d026170042c101040150240c0000d401c421000c26040b14050296100c891039200041c410926004006011403510499143c206e051540040214032014804140c40d26048030500c540b880040301c4d0305c0035a40d12441d041c90864540e900c464002c500104803a4003a500540360f0220007d0100c035050f8084918068141c1120710740c0307406c12350652001065441d090144518220b6 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 416997724 1250 416996474 416996479
    0x3120f151f1809060305010506091b030112080f210f07050d0b0a17032d07080919090c0201060506090303120a0f0513031e200a05070e0609090609060c0306 68
    0xc1c039503484143c58201c8003a98400d4030540d45a40400031140740000714107520200079058070100b00f1280ba405941800140900301070362090054080074003800d001505c2c40039030301c1020940d440007510038010348140c4100c000480d0300445404105105045869940b10b86025582d460a002c46007030868080c246d81841d882d0403021502c00441d03690b1102c0150208507850800440c4c0d203030703884520551780c94803644124442445950041c200900d04000710f442e29504003000c1d5482d801080d0000d101c0e0752014610540640da40c0c60000384030480c076081003015400e40d400820007107544006000b05480b0724019540d05030400c00212403112030000200d904a0245180016021003c0b54080e04941054903650500c61030b0508000c01c0541c003c0600c1c8580c6000c0d00201f2120a0100c0003420394040ba05071111414004110302d040c4401c20042c0d0b1004079003200032500081d545040311440e102c0292107081c010300740040002c061240001c1d1090140041c0d40040110784d6518101415580001d0302e00ca9 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 416998974 1250 416997724 416997767
    0x21f0e060a0e09040602030f0702123109150503060907031421071104020a091415070b100f140906010e040f0b010e01020114041403120f151f 62
    0x7040d0380f11418280e205901c1000c0050b501d05000b440c0070340108000306110115030004800200708a0141e0647c2e00f070f1809100c4544030240003030a044504104c006503040062603003800011400c1041d004030a8040540031884c900c25100c8041c16101e2104640048203580030b0001000001e01200303402d82c05100c49001d650703241d4004c840c540403030310504034030346440c0002086c204140001034040181c2c030301080310114a003209a4030050a0180c50384203140c880016059600120348410007111041103504855694030100d6252207191018280c030308281610301450082a5480d00e048900107a4440c07203110400804110b04019110a00900160401c5007038144500070f9107a07401500025821300401140300c054810004008400c3c5184940c1160304040b0340452034822407005a0300103401078003828001c2e1b00840d80070b240d84200d582c850092080041000a07002058000e2402180070390040d00341d6064000c1082442552102c0c01350701c0b03002d40795036074040c1d6001d85900795042e008502d024 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 417000224 1250 416998974 416998997
    0xb10171806040c060801060f0c0605070302041701290916020705060c010903030c0921020303120403021510030b010509070c0b0c04050a0e0903220302030d0c021f0e060a 74
    0x8038108902510b040300e118030a1503060140c41e0300545802d01605803807500c030013000d2100700001c1009aa00d800600016034890109a035a4820340485024100140c50805800d1a030f0090b1402808200b039040c0c42100920060507414001600c018015200205803652a4540e0ba900c083c03c244001022419807254940c005101e8492801070032080714642c0000030071040030f00f0050156800c5005810801c41c04a0081c03102e08100d00b03904018003032441c2003410707600c107920100c2d00d14400e41c2404000d00074418100300c1056800210420111000b107a019000d40b0360301030405413503040780001841280c480c00180001e060540e0150303440415480d02c0d281c4103000d503c80009014042c1c98000550b00e00060600c42d6080c00c2290380001d01046041200910301019243c1c0c4a0040000e072044440c964600709031083d1100c0d00c50300247d9001020386811018210024200058612089000d400707211420320499094040c0c1a04055142d1103450b240c2901c02c040100f0707580141d075441c09002514022 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 417001474 1250 417000224 417000271
    0x2120601050d1803030e0f120a0e1c0605070f020f0a120c0b0a0501050301180b07050f0d060e071d100f0207080316050708070b0d0506150304060f0b1017 67
    0x340905600175200011032141c3e410415082c00c03280310003444c00783e000d0041c110304407520101310707881002c0d40d24100c2407131840711002894421400f9080808080381d6030045085c080c403580441d01030301403512540d200c2c6d452800c050b1307156001b160f00d203d10ba80060311441c000c00e0700500c0342120f0141e10300e0722125a00082d510310075030b11030544405e50504d54960042c0103d042c02d2048102d0308100581561001040345c0c1c07280b0b1410001404841041404660003003101005c9042d102d00c4146542c0920101e030b00c50981d074400700d608032040700000302c1007640010201c649880c210350402d000342c003440304072050100550762801c807014030307800714841c0d0320000a21560610103001004020200e1040c4a120f900b0003d2402086402605894000150410400344200c0c201d601c1c40b5004100460030340e0b6107400040700c0b034002000c03d0345003080000070002003145030b5000003a0328030702d040204050b0b2045030510480030345409540012445140c41030501040d10382c0300f69804545000100c0d49808035044 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 417002724 1250 417001474 417001511
    0x20041a1605070521060103060f0b031203100501090506070201081b04080703020307060203121803070f061409060105010c03030f02130308030103030201360c0f060509031002120601050d 81
    0x1500d16401c6030780103100c3d03480d0440030000356113041c6081e00c040420440d102a120007040c400185442d5407901e90441958168000d44441e000040582d0340280d0400340d84e141590080f910f40000200050001c105580a040e06809450025000b01c1c20b003c440c1e4010340d100c103c0548288510741c104001d031044106100001e2018110010207842401d140d4818540b400d00540c11010030b64005000240e200c11140da401303540070031103a406120604040010609500c1152005072441004800300c4040c44103903040b20034242e11086401c0e01c550380d104001030302c071b078028001d1742d0010700e0b09800d40d00440e20980191b0910b07201038a0051400400240c0302490104940c400c41d04003030084010418190284950a01c80340a08035404407000c1e09140a9401044030101959140041000c43c0a004041000700094104150141c40d513544030781000d4441d07000b15081510038840ca400c0004a15100d000741d07103440c24076500802b450707200c4d1401036441c0c0d041083c0c125034141c1c0d9401c030180307003e00903070 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 417003974 1250 417002724 417002767
    0x1030f1209170f010b09090309010f170c0a0e2b031202030f01061404030f03050a050c06070203031b0c03040e06060706090f1e0b0109020c01060803070c0920041a 71
    0x7030080c103942e04983c00d0282910480200188135018800c10065280070220490382c4808007480e1540d0390213203c003400d99481025031146002c40e01907004003c1c900c1950f0004000280403034440300c41440612040048501c040348a01d01c41550145101d01c2a000240c0348881140c460300b484501c14a09000e01022a041110202e1064289174010440c450308007020007c200c03403080c40c8904d0b00d41107484600308114140c000404200c0001405026684100c05868001250384140d4800c1d05007200300950301d0300706803015070800a04103100b1040c0354981040b03420f22130408010b90708291901141100f00740c4014680c94000300204488000640c3d180700303110714603100701d0803464181d070340717051059500035074a00d90305072003104041c0c50380404c80400b46c860440b11b902d48050398ad1000c0e5500c0e14050045039118008d54030001c581e16003004403e00070602525500d4038100141e0a0300350181e0321941c086200e04141040421060180c0042c1003212034464070511b4009180240c21040020701c2c05015 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 417005224 1250 417003974 417004019
    0xb060417060604050705072636101e0c0b0702061012020d0b0405190c0e0c0a0c030c0203030405060d0f0c0203180123040303021006050901030f1209 65
    0x5108100326490544a001d0700101e251500d2070400d885607464001506100e1082c0e280c403035542d0010042239203003804503511001128149041694541c06140215000d003000b00d8040d1841c1c1003650150815503800c2820150036a2003110206882c0701e281c4c40013038030011100411000100794000303c0e5070745030240d01480c00b503030003025580781024030100c0038261604400307000c260586000d00903a56103c882c400080d0441d4003080c3d1a03d540c600503140c0803e000c440c0f1103103005032191000f8131407260104800c84008800c00e003404e950300710001100c0d120340e8200201140031080c003c0e020902c07490001402c5d9102408581c5001d440301d0000740036811424100c1c548c2c40c2c481c81c01da44082d0303c40c01281ca147e0001e000031420700d0320300012038150503650000036042200d1030462410320400c0c00d000940802d0411303403d5665980741d0038001c1d143c082d12000d500c0c02c241030401c001140e0030b00f041c1150481c1e0f00b2041000281c1082d0351840e181b40c1403e202c89e0108070b02c01e2404a020f008017036880c80c0c2400c00b17 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 417006474 1250 417005224 417005233
    0x110a022e052203050a0f0509010f08100e1e06030c24070516170106050307090f02040f1202010219020102070605071104110c010b03070f0504110c0a0602070303060b0c0d030b060417 79
    0x400701c02480138800106c1c0408000090112080a0741c011400d00010410742c1030420341036441c08500c96401700290b00484812060340140710001c01c1d01084140c00000901001116036152001e03d55141d86070050190412805000d0340ca00c0c004c0b40c102403001282d503030300b114680000750300d46914001003a40405c0000d030040380c1c00c00c1020351b6525440343d6050601c0c000c0c00018500000251a404144104010300792140f4103007203a040300794110b902500740501084c0500e0f0300c419416240d000a01c404902500c0303200f56184801c082d848802080d9641607006040003828a242114075400a42080f41e0071141e07408910b40c0d40c0e80702d01aa0f981e8245981030192a144070b0032040d400e44c2c01c0744030498003a0708801d03c207000c2174110205d11001da600594001c216444449401c0c40e42e0701c1008100e0120703000d442500c00803c41590010f16615010782d0b410320a03191224000130841c0715004001c007943d0b0101c440d0000c0940241c1020035000401400c25040130741c0c9a010740002e192100003240d40742c00 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 417007724 1250 417006474 417006487
    0x30402131a011b050c090703060e040602071b0e19090210021f06060c08130b0d0b090708010b0a030f0b060a030212010b0306010c110d06110a022e05220305 68
    0x2d010200d09007142458030308101141d4151134098036501806400d6006940d40740008080d0b0740660072160060203e64030405162801e4240350313009401c100411940d000c0c44c0180c00707108050300840c0a080c2d071400342c441030060322040d104c0b500300301040207980c44443d125010701c2c0150f030b9001c0da500e00a010316000303030000003800d00c112000c0690341c91440c622645481410300c0342e5907100368420107556000c0c03000c5a42c0c2091211204107155168070108589100064410503031145410413994208150f494040c1511003002c207580200c0240100c032042103041c001c00c0c200503c070343c1259490010440e00052785860b00c0b004a0615840640540007003900028950705502d03020324000e004005141d01d480c2141000000241304640c4801c010740f804403280c4480e02150340301820300d034803d680020100000f200903441c50809800c04040640940190301000c1d100302c1d52580100d840e030300100c070080400c00c1c0d80c1200900904028001565524900c403208182c420300525186885009403a1aa107800 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 417008974 1250 417007724 417007727
    0x3050309030f030a0f050f07140a14010612030509150a0203120114030a0b18010f0b030607141b0309090708010f0f0602070e070309021032040b030402131a01 69
    0x400d218940301c60340108140012141d002c0001c5c1d840e07400340e242155a4141403002c800c05801401800b81038a00d81d1040d424440400041c4020310920940d685203030340c50b0744400c1c0340c2241c81c9481660100d559140c031440020388a0b50040000041c010414544041e03421000050b6030059008100583e10024040c0c5c01070300a509614010a18040c0f000c1d524000d10700441e45038950072034000c05100f244404207100010746604c840c0e0502d6810003c01018403880800c0380503200b0032000c54086d00490000c21000ba01c00c061030f0b02c0000003940414504441502c0c41240d07108000c2e07049035035000c18070160b5000d95a0b400800d01402041c0e44012007941081b0700c4011420b01513014056110340c10104110058010800c074044801a5a4201c01035440702029400b40c4580c0400a5003c481c01800d03010168002b1a900c90b100c042d00600710581d40301401c0c20f0158010818402903901003880100303e024506001154000d00c050002d411003074080c242c400c280d0b102c8401d01a04503108580788519035 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 417010224 1250 417008974 417008983
    0x190305030601030b22090f12090501030e160611070b0706051815131403030f01030c0b07030207031502090d05010504021e0d061d0f01061a040b0301060804020a0902040305030903 78
    0x648100e850150f400c0d01010150507000e00f0082c070500883e224040001448812105106110b421420888203040c8c4004010500c1401d4001c150101380380c039040078a004800211003081030300b071810417500b05040940560300000c8815100000e803168035004a00e03110700300040c25051340b02d2100851035080558002c0c800751100f01c0001007036400002030710703405001e0212007500305158a441c4c0c100c048050800c0202016054040b000c140301c00420b01800710304800501d81200d00544010000e0741d100c0c50107075028401c58401a0060740010710a00218450b940041c282036004040189051144000300324260004c42c0c068600380d40d2282040b0640c00c0030840368074030060b0008071191842610000070800641030340003031f080701e0751407617201c0260f1400c041c49400d489001080b607440b0480202800d004c0d01d075900582500780201440e010710304522106603000d44d66104c9a080c20b581c00d0800071103400000034000c0c0c0e40000c40340000035180841d0b10003000070b1030041c8051680c07011088281840c0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 417011474 1250 417010224 417010241
    0x80424051e040302061317030c09030c010801060522080105250e0901090e07050613140f03060f100308040f1401170a0903030f020307080f010902030709090c0219030503060103 77
    0x41c0c0241e004000009a001c10140d0780550880100b9030a1611805c1080c07000c0252240c80d06441c800005000d041e00060700a01207400e4100c00711079003104c04c400111900f000a2144501181781030080300e4000d2a0403003220751254900800700b85442d52460003e0a6503010b56a101041001075580604907252465442c0000118248104146169004100ca00d2014810320b40c150340e48030316071558514144061b4000f03020051aa9461745120503109030304a07c0c9204e904159898180c2c0300c1c0c0a410f0000f011050701000030003402403550f40c0004d80c17140c41c07002041c1c42c40a4016901c084001440140034002078444840103410541c204904500c09400c44180b10341803018900038005000d080b03a2540741d11149080020540f01c10915082d1f0180070014610f0010714000b10401c0010744c1e021155a00c03503401445840d4030b50340e1f60341c8032900301d1105a0354080051070140c018808544035800c411074004081c4110340503900c2600300f500d460b00c03140208400045002081c0404d035a81801034014 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 417012724 1250 417011474 417011521
    0x30f1124040213140105040c02010f0c050c070f0b07030309020325060f0809100b030a0807080a08010b0a05030402040c0912060c1d220e0706020303041b0608060108042405 75
    0x101c0c1804d0303044c409403081441140e1040340c40b940d50b0758120780300307402104039103c1c0c055042c002922400c0340942070f600180741d9044103128142d000284440301a0842d4202d450307081e0307828904002500c00310082c3c02800020303601485101112440040e134002c4950110000c0100c4807075050500500a1030f141d54070400204000400c2c00b4448110030101c3c89101c1c001c1e48020000780001c6510100303080000c4100701a050002c089140300c188507440e002070509040d69543c0c104641e80301d0704011418015860382c1c90000d0b1041c00000d005080990121345120801d040c0740e03800c41c1d603c10703403220f00c01140041203d8160302c0e07200317100070540c100e04642209007640710756441600740e06001c210711030300f4001000440c588403603d142080f0b040d940111140050501510091600e419001e9034039841075904a5940e0b0404200e40201510b000c0c0c200151496595140e0050321001c0044604c00c0c2d02600985860b07404084a0b560040030030030340c60081d060703181e0101c0c007842c1c507081622000700c03022400301 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 417013974 1250 417012724 417012731
    0xe0c090106120c030b1e040e07031e08040302040e0c01140903100b040e070e0103120e0d020105071518020909070807050618090a020405120a030f1124040213 69
    0x92507000709003030300014030000c070000e0f6540c1c2d045011030151456048950700607480c4040c425055810500e1000b40b40d009450500c4905e580300300c041d5803035406201c040d0908201d64003201d011312008240d419954081d02200b410a42c0320707000582111003081c900b080f1039001c3c00d0340300070b25600f145011110091101e8000d04151105000c641c40d1007248014a01d103a40d54881107031196100e9001740d003c0c4140c0d0b42101c0c030154944612100c048000c0c001505e01c443c0401054610074810b1200c082212009040c007030b4503c54580c01924140c10142c002c58002805036500700c2105114800c5604001e0012030816100109006204031408040c0401c21250080c01c4248401c0c1c00009490088a4058604513070350700e00c0b40300e5000c9555403074aa00b81d210b002802440300e01907150700504180c03041100c60151100d03058903c0c1d55240a032203c0180400c103100d6880381124014003404807120308440598032912114a1358078806d5800100c034141c0c91080d601400250b05105c014028004151071080 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 417015224 1250 417013974 417013979
    0x9100501030312150806040501060e0906040201020703120201140f180f1c0c0c0609090605030f060604051506031602060f22021216031b0f050f0a15030e0c0901 70
    0x2442080441c42022106845484000204440384145401172060788140c03001c60825140c054041c004034480c001403001c2d400c0105880e0f400208080c0e0003143c1c16002811010324558411a40501c0e009803841076560303800009044840102e421071103030000b2640e00c40c0342d00c0d00d0311030b03900400c00240780201e050380100e0702e40741c00356030020b076151140c041d40341c10b190045022641103036048424030b4000c1200c0c034045000100700da00864240252624160103001a5440b00b0a041e607440c10080c0808241d031220011500e24140359010f03982105010059651040758080071407080e034006e4920402d848070482e01c0d000d00e0b41d81440101d800040e032103414500c1e4105040b0703114030b11050380540c04010110342a00c000b10342d6503c0d1040781228000701a21050881020200d01c403408612058495441070300c0c4d0a0031100c518401c58040d00d52002d40c20300e5940c20502441800d15a90031200e8000c40da075140071403003000520002d01c00c0f540035540400d1001150380c0c22810961075003800f80c06507001e500103 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 417016474 1250 417015224 417015227
    0x3030f020c21010207080703020c010332180a0b01030b070504080601231c11030105011a031017031b070501050a08071e09062003070201050a0c0c0b03091005010303 72
    0x7400c0010b5020000356020811070044030340280f0890000400c401000114a0308164000c1a52040040c7c00d880412660f19203441c10300068520765800c42c031485180304180340c118140010180c00c940e1100d500e0104a800c0d0600620b040082d030001c0d00c5179a6610010002c02503c4805141d00c90024030701281400c0c03501c00700680c0d03000f06000d140c081528801c201c0340311000c08444e048255000400014190198540d0540b032256041b8050b103501114107503071846401d05010f01c0741260002c0e203102c0304d41040c0d0341080040b508090800030004501540008044803c03207007042c0700c0d10550020790390714040c079000d910510340c07030107104002074109142c204000c2e2b0300601541c0e00e041c65401c0010942c0d40d0b4807421034001a405820564006281643d101600d5100980500351030080d26012030802034941c4210030b2a00ea100101d407150301c20001c030001944214042d0580c0780c0e460a110082c06410b5a80d007138440041d1f044004198008001c01c100703032204000c08101194032040030070041d41941ca0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 417017724 1250 417016474 417016489
    0x9051305030406050a0c0b1314010911040b06040509040b06030609010911040222092306030a0320030c0c0a090209010f0e030a0c120b0106080c19120203090703030f020c 74
    0x40c8605220b00480d99000d844d0064003911986a80001920810f25103250100232500800c00e064035184007074980b031407050405100e0542a0382c2c0107610301c015002104200070280c0038030600160030040610001030781b40c47d21805a80500c1c0b0894483c0010310b44038081c1494040300910700c0020307a040101801c0401d104214200d01400241c501580e60f100302080d401f810300000742e003004c0500c1d00000010702c010795070340544400145002910309881c0350002e0080419800c3d10b07029895000740c1515800a4010841ea040c08000070400c2201712808203030160942d003206091070680e80142c002000c0b24501095103c006d0904038104500b40b03d0290002044600111000024042d00c0c0000c03030f034a070350300b004010404c0b58403e1080c44a1034a58290100d090175070401112035000140000c11810300450070713203114100c1b40f24803600b0816600e919054003140c0105050601041d450714082c0c060413030000b14401d25000004010b00d900d940307002080c42e0389490341841150040c41007002035540d40381 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 417018974 1250 417017724 417017729
    0x5040605060909070e040b15060a020a0b01050607050705040b040b120c1306150e03100f2f07080a050d05090604150c0212070819110606102001090813090513050304 72
    0x5001f036200d6600d00400304203600d03c102c0c4455110b6400b00380f0721845540040c00240051081d00980d146980e00e81c1802064043c90000074100e810020040c0054100744d408440b1262004101042a05084c8003185801e601d4102540c1150000c000640c5541480b4a50bd14120301d0320404000c428505010150701c5617440000804101480801021b9680d04008441200210301001c0120407041e002c0c0900038002c05400014008032030044c158281501e6200c4031607080d81d021082d02d01101030f90b99031855440f40740d01509100d010311403880010356602c00c2500c10070310000180102c0c10603041400c00402c8d140a0b2890b0b0074100070041d100e41d90b0100c0c070190f0130f440642002e600c9106a14000c1032602594803015138031490320301c0b1004455404134052500e40c2041040c2c2d005512800180440514220f4180011139803590f1000ca1008611040e46400200c03c80002031040b880c1c0c0d120302c2144c1c00800e14850940001206200281e520b10030680c102c0002d148292011300c030765545c2503c0f4011032 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 417020224 1250 417018974 417018983
    0x9150903021e0402040f0e161b03050f0a0306051c12050c030c1b0a290c1f0515030118030c08040b22060e1f03020d05040605060909070e04 61
    0x2d148912a0089000c09080d0120000b842592900d031039090200d158882c510030300c4110001d190106003000c2e41d6001d10ba402101580e80e1518a43c4007040c1d1071401c0707038500300c1142013243c10040140546007070b00181400c241039641c0130074028a4407040108004142d0084c65403100c1c2c80c0520030016104202003042c401107400e0580d10399583c445668214025203460641038020b0b0036020076a825800d210100d901e8003103d001c0c00301d5331035070000c2c841c00703a01c4c0700015a00c2e41c04051618006020602521802101c1c008a43e41c8507007404204641481504806049036151810b014031a03c4080c041e40c1754080560007089039140307295021001102c1054060f0034014541c07001d0091141810495000c0c24109650780d90718600f40100c055468810803083c810701e41c104c10302081491146062081e03154006064609283ca5101c0e2220308510942c449814903600f08400c1c0510b8440340102072045010b802c000509241080510410560080550420b90031900050014840c10016242c2040c0c01 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 417021474 1250 417020224 417020239
    0xf02090306040321020c07051c1104021602060a0c03091202060301120807140619021801120b280f05060307030203040317091c050c07090b030a0c0b07030915090302 72
    0x102d403007590013120f14034801821800065030b441032a80004500048a0003035441060f035103c0310405461580c41001e0003803113122103c20b603034201e107050b402400000c040f90042454040c3c40d41d000074036a600050651001c03400b00c0c1c182c081819088452031380105000081c20f40041950b5001400301d1005002c1d0691003180d16a806e000d0000c01070664003800d034001c0c41114a00340810502c0d64400303017210703030010415190640c40d128070350301d000703580100007002c0ca40d02c0110380b414010b640d83d2a410404403880795445690701610796610710403e40079080c4000c4213444596000982c000789000f504281a40c01641c1c10070410ba40720602265480301c0d540c0707030058807600c45280031690030b03691555004c0c00030f050005200d044070000c1000c045008040e6080380c09241940410742d00760141c05600350042d00410000c20481f050350304001d20a40c0018240c41c00410745994185040c41302e50007010480ea40810218201900144213001500035000d8400c11a006688002c02d580380c18040203001d81c25 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 417022724 1250 417021474 417021497
    0x1b0403032c010504051507081225090b0901021c030b0a120201080609130c060e090702011104180b0d050d0801060903020d060911090f0603010c0c081911030f09040f020903060403 78
    0x180f200303891f24550300c41c0c44d80f40d4605d8680443d00d03c0e00026502d03034071240c1820f48911016803900f982000101800e4071410100c0e40350200605094100d240528154059440c103d24a001500351002e10201161000180001141e090120740c04080c0c100b010702c0300e400e000d0400540e0b08001d0a0b984108100c0380582a03a0300c0c082e101c011030880040090445030030340808569541c100c4000100d07002c0075104242a50386000c0222700b030f54040e410001300000100400c4c40008201100d040e4640e0300d12a010030050046004a10410002441a9010381180c81c0310040558080c0c0c4050040041d032901801e100e0071500010203481640034000c055030303501c812a030200614104450030303140000780b04252500e8001040b448165040300c840e48294a45003038118440c0c0110f0203a110144c1180c0715505003213412441590101c51501000700740b00c1c40d02d025480c09003003000145142c06400312100d4a800d0000d0911051302c01100202040038014000c04031a80c40c0020010751068151412010481 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 417023974 1250 417022724 417022759
    0x309031209070b0f04060305060d0f030e0414011202040e1c0309060902040c1709070e161803051005010605180f0f04090c0302030c0402090306010e1b0403032c01050405 74
    0x2800d9841003203140404110364a00d5200500644100c03851a101400156100c9c000c1001e8040b4003007005100d00511203a603000300e441001100a441c0e0301901c005004000f903189607680c0e500c01d83c06026407402d08404001141028021404900d64030310040040218200b0300281380100003001e8410180d41d10080410700100350030036810f07660094003c2140240e02c0d400103110b8844d0014200c040403044c0c000c80c4030041d002540e81c0480b0110b80e031950301c43c1c079200421903034024050308803c00c00050b50328800f010021650908001e5100c4c4000340b0344403c89100040c25120141d104a050010034440c240b0710801550402115041c00c40d8803081d124880c400107501440f8a61949800601e07014488040100044100c01624000c80807100c6007804001004145c0c4a405074654158000c0c0c0b00400800d075000c0d011603000310403607141d03902d00741d00d0304c060941c250000d81c4140d00040410400510b0111280546180c0c6040b11131100d51030540080040d00b944103910546002c1c0e0f4428ee24031f190031 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 417025224 1250 417023974 417023983
    0x15111303141516140c030c16120206160b240103090206040603020d0f05070201020c122a0a0204020f0a180308030c0f0d020d0b0126070804081306020717030309031209 73
    0x800501820076150101c0700c074810baa0b50020807c64041d442403882c0c0e84001c841e88284c08048450b100c0a1038103d003101e0303007880320580000e09807044e049100c10240300045c5003a0110b41c4500d100c035a8039507d01d2100b000031201e0640d0140d0355030501d4607103803145004d80c848400716130503030301036040160741c4a443c001d800009140859080c001285030009004545506400411082c2e154100710381010145100107030861180015665a030480c1c01103110703030b038441003058007103a031020803d54429407102d4004c05e0a0346c0c0001110310301c2010000b00300482a8019050000e01940f541b02c1c0134815003075a0340d084141c44003801d5814030007804038180f2498144107044640b9500c4002007991180fa60104400c050721804c0c2c0c40501080742c24402c00400300614284898108060780c501c0a0b50720340e4142621002d0020b841600c80c680c0030442d4520414148120300001e16003070b4010b0015500c0c1c0280060808050b00004406810030818041107400010942d41411441c0d0103c2e011510b4256a03540380 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 417026474 1250 417025224 417025247
    0x30705090d170a180f0302010e060c03030103240c080a020912070b031005010c030e0603060f0603040c0f060f021e070302030715021903050715111303141516 69
    0x60305080a0340e607280e020341d8024000796042600d41c0055103034124204922450a40070716550205104010005580f080c3c0327000c040c1c0c01024103824644000d0022150450340300b60011341d040052000c4c010a001007d00c00803a241e100349400b003050f2081000001c107a103001400d207030500d6801080210b000d6446107292150b00e00321100300c0c1c0800e03581d80c80e03054580c1c1088a03918100900603e0004481d40180c03c440106949540c4507104450711030b04010700c9400107408280c108401e0154000075449030002940640e00407490f83c02d01c24542408032000241640144040100114a04e05000d0300010801c40c03103164218a0192140c5800c0054a42940c40d400a07600d8070a0f50030000740c2406103a981c19500c5c210340d0035151220303442e00c0c80000d5034007010710042c0010b60800205000c80e00c10740d21940d24600d0f000000c00c400b00d1043c00f420440e0000c4140a1304801c00c52030030410420503010040c40c07446400060200c00511756015200b040d0001d00c89111088281c06885410f440b85070103241 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 417027724 1250 417026474 417026483
    0x10c02070b46030b03010c02010905190507050a120c09021e1c050f090d0e0a06050327011a0a0b0301060c050c030102210f01080705010e010e04050c1c050903030705090d 74
    0x39200c02c0c0000d01403d44e0700b421038000c3d4a090088171030548180548150303e90440c009003650300c0800f60040e4414200b40083c0d8aa000798078000ca03499a0fa1602003004108404001417525268100600c00c40300945c400c5031180d00c100124038010040e00f40f4114803100c296152600e40d1800e06000d121040b169100c203040c54600030421071000607881c0401d000720195401c4406190a00c0030030340d0800c440f00c0703c03240d004e102100100002846900111751181d010403036440000e058034502c2c05140b105010115050751111200340c0e100504028240300c1d074030202c5100d8856071a2404000c4280300601030034080050241e450803d00c1400c01c40040703140b0000e00215660720052154518240321200e174441ca090050303021030700031070b041030485058502c6c0c5009041c00030301c1c217801510784011109c002c50500c4852100746050741e0f10b502c5442d108011101140c0c1e0344035442c001d101c0080318017090900d9198034040c00d0003d40100002960790102c0981402ea0760703144030100003440340404420091 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 417028974 1250 417027724 417027847
    0xe011e03090807210507110d0f2102010b03010504020609040b1c0c0f0b0910110a05010501080f06010614040515120a060311010c0b040b040303060b0c010c02070b 71
    0x34200b0291405614501d110706080f100c0d00d1a05100803a051b2203480c1000c1c02c001c590801d1004140307003229001b14021f101d207140e4182000c90342d40d408180e4256180c202500364454000c80c14a80d02809411003041c4200d008008a10701540001c00f980210304516001e07035a00c1480711102d0311303882985c403102000c18446041c034005510f42501c1c1c0c18200c0c0a07d01d800b0300c001d0030004485907900103035900104010300b803055064801071b003150700300c030000c6002a03984250208040810001e00c50180a001160054076101900759481c82ca0483e042c1d000c5004c220384044500072040d10b000035a0155001121101d04100620f850810303140a030103a02072121040ca400d100f2680b00755805641140c2c0304002c80031244011000646100141c01400f820404d640300c0050002035103c0065a48540320b8240000c0035a114400c1031001c2c3c0000c00e014045d82c0d5100c5a044d941901001040001c280d2803c500b880c10807041407403914210f54a50060110554918004100a80c4003101c2d8030003c010003843e = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 417030224 1250 417028974 417028987
    0x5120405030405030115061211091005220509180a17030402190503070603020304020d0501291f050a0306092301150e0d060603060c0c020108070e011e030908 69
    0x3501c82d030080c401c00d80719600c1c0401e41d00040603803880590850f0301c10786a509104200b0b41c0300701d020745080f0b0020304001d403041003070348a00e030741c0d000d82ca04002409654158440d1901da01200c255a11449588080310007401308003ea981c03034040c1e00e60321464102080d1510107002095614181903400c00501f1900400d0313048403050b074040701441c030860084480d090050480d0213840c0080f04907000e0303181c050b002003109210543c020340003560010302c080c0a030701c1c9a0045071a1282103419154041c2c2001c130003541c035101a2070150702082900070b0112581b01c0390b4400c0c5030b440ca000c080300820180c103000002c83d0a200c402e029500400c000c05d41c2034001d01441c10004509074001c440d802d0103c1d4101c0c0343310300120350507a40041c1340351940815107682e20712500050400040381546482205ca02d41c64050200c0000e25a01070042c10348926100c001c0b060105100241080c44003c0c504801c011404040640e140e030300100756030540001c4012000000381702da000b200030f0404a03102074a200b5000421 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 417031474 1250 417030224 417030233
    0x1212161e03020115150507050313090912031817070c090b040f0603051914010903030518030c1c0c0503130501030608060c04050402030a06121101030c2d051204 70
    0x1452106110b0b5000f00003640c40704074195000b032000e02490380071483c90803211055034000c000600039680908106c80c20101400100010001d4035084003946a446551a400b0080c8880e0701c60b104000ca403c0a10a140090404440e40024640d001d8400c00319011403e4000c200042220b51305a00811450859600c960300280070304001c8a100d40034a241c080104a003216034032030702042d281c0c00f401609111802c203400c0c421300e2401410688031480000401c520b650001d00c2341d010502d00ca030f10049014a4480000380c0072100f4141c084195800030800081403100103c1d175000114810308107005055400ea2040302c200c074040d240140745102c0001d00c0d40307118096880d410100c402c2680c1c244203641d282c00c05c03207440e8481580c10200d400c505101c01d020f1841c00740c02840d84480c20900002d400343c0d450700c00000d1400c01030710550304002202811442c650303043c0100f64440b844c900b081013111810803900c1010013600c0c0c02c0483d22540c60003024403402e00c1a42102c0155a0001140b0181d041ca07080 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 417032724 1250 417031474 417031523
    0xd1a07030e061f030602090109050a060306050310060b031b09060a2319031e230c0301080d11070510021e07120212070b0a09050f121216 60
    0x10100194070500340000c03030f0f042808186860b01031002e150507900c0342c034542c2d491010750840540c49040c00f000003400b00d03090f120184103a00034640d9076404500e02c0d00e000c0906050851080c98062910f0414406004102c0d8500c02c4a0f000315242b00d100c6414941260204a1400707814481f039844030f000a11003100070340c81448025859100d80b44203094030000d55603081c9611401080a41d4400351804548a8034001d91200c075900c5900c9402c0c80c040c0004d20b5111040341c01d150320101610009131907650958214440741580201c9051a0901c2e65040408180c0d48403803c040361000c1045081c800c00c1c02070f009010100040101030109138400c203844101070340300e61030541000351076000540c0d034500041c00041e6001c04c80d481e4000c2c1181c0b56403540c00f80020001522100c010601c2517401c0051001902c2d0000c0c450441c49541d2441caa50400c8100661280081d42e40c0f40f0031100008251400140410708501d032a055400ea1a46e03000010101011510b0b0050040c210390341d5000d0b160341c810311190 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 417033974 1250 417032724 417032741
    0x80f04090f0207050712050c0a15081e010b090a180e0f030a0f05091212090f01020a170304150f020306040f090b0c0f0903011a0306090a0b060d1a0703 66
    0x900501906124a190008a0190f00405040e50380901000c204800c2e9807000716020500070020349488103c40c4012400c40b9036654801c9e01e45450f484100c03526264040300c0c09800030a482c0b01c0380c07000f810b9800c0a0041c603606014481c0604400030b000c5109580304550400101421092010030180240a080c0101410840003946000d4061001c034000c601204607003006195884070310041c441c0050460b0b031900a03e1080b5040050840343c00d48401d41042025507e041c94482d107541c0b401c810050100702c0100d402540d05551000d008000000c42e130059005810713000e01343d69a1a640c607400d21500001c100030f9000841440c1a185080150703258009610558007550f0034010552445100c400f11100c511014080c00c64030b50200f2841d0700c4050051158044083c045428240c01c4000282182d041c824549003031000285141d6550406220003a1f1028003400a0700382ca4a00b41c80348691903c006022074031881e09409060100401d100e01c446507602c401400d0038a624240402400500c46070 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 417035224 1250 417033974 417033989
    0x1b0f030f071401051608030601110115080c040c2307140601030c0b03150103050901150608100b030108120c07090906020904111c0504021804050d0e06040b16020409080f04 75
    0x3000d00350382d94042c2d800c884042d200507040c40d40c0c41c4040d445003080d0b6080901114100503c0c8600741d40120801d000b00c46409c03031011028400c0c41e150215003407600d96000d00c0305002d40e09000c03081013000d4200070240d1b105407004140750302c401c0e01e0880203640c500c18200010004036008154042d00600020070170b058a104e0212550741a41b40c01e0750300c2003400212801c85400a840c0101c40c0385510030340165400407902c0c4002700b840d41021815920320005600034600043c84801013200d84196a9981002407000c4a0f0851541d41031070036503519660400303842c079060b050000301241640c00421144008084c0b403002003000c1744580c03030b020b40a54000c840c003511960525800100c50381541c2d040300d21865040101c00165220030304103402610004000340c0c2d0000298003620344566031480180e22480c8500d0242c108010300070800750042620251190060400b84018441c1d54107110464540341c60300408898032a441d4400240039100c2c2140051540101262660380e0702d401c2d00141082d2100c2 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 417036474 1250 417035224 417035249
    0x40b09070b04050f1c0804080a200102191a07030219020c0a17030c0703030206040b0a051302041d0f0d030c1409040e0709050f010e090d021b0f030f07 66
    0x41c1c0810322014041d901a040d031000110881c04510700e069505421300f059541101c8107002142e403280305044d0826030200d4102d41100c50300c101003042400d40890140303503986c0c42000c800e41c4140003d5a901c0c024042080061981e0310145c14804142004d02100000044c002e01600d00103000501031740165494940c0c0c2501a046504060b00103c3e90f00c408030307000752070b4200d010714100b4100554040d0f000303089494001004054091042031115a01a6000360020089400d041c94800028100140404425807414051000c206180c2c4482081c80340c0465000c28034501743c11151181000000e05840326115444d9010f00160020940c2d070302825141e01c0801c5100c00700b020030b44010300e02c481d044601b088104034101252820b540016002180e84088521780303600c95552034101c8000391280001e5007010801000401e0b0b0158944d60700000d90006401501d007802c5003c1e54a1100c09201c0e0000106040c0300ca40d60303100d899032020681c00c01012601c07400790b642c0600783c80700d2040c0130305220000d4 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 417037724 1250 417036474 417036479
    0x20f06040c031109070f30060e0c070c0b0a090e130210020d05031b09090a090605070f050304231006030b01090902010512060303040906170601061409041107050105040b0907 76
    0x1e245007130364801c903565200c144e80c094126100f01d0303022480310028081140b00042d4007406c02035502c210f010310f040300070000070f40c14140722a540400f03100605107103c0c0341c01000642c0010f4010642c03070048514003240c0c00c0d2a1041c2d000c5c151012440c9401071904420480108425101c41400041d2010700907106103a03400b00c0c4110490311001d035542c02c400030650400102e0505507101910b180803440015480e03040191030000074241040503107581150f19182c040700c1e403e005061040300d420414604014445158101001d091400020805400200a0380782d90480d0135100c09000300580d031003400e5400001e0702c003081d03800400385404151800050200003045e0601e2500c201c0100300e03016101c20b41800160703850728041c004000c00140d0907000a01c00000d00082501408001c0c01d05400c02d0400c02107480c1c00e480c82e21505a0080040144c0a0803403851200303807208842400d10180d402003240c00301c11000600c64030909500521541c46c020401c01031046c1480018003504002098031600b03603 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 417038974 1250 417037724 417037729
    0x905040227101d130203160e011d010c020a050405241002030403081305100306051c02150a030905030304030905010207080c01120b01031d030315060315090601020f06040c0311 77
    0x2101c0d1403042c00708010105100e07682801c1c00303401210102c0140241c80180b00d401c041016038005960038001904264940011709402c8584669039000030b20b0094010311031010030034070300740443c80010305200d1181d08942c20341d120a51aa00a010060710500040c14000031783c01c2c130204540403442c000c4002143c00400c40c038100018409003880c03a401142010700307503240e044042c1e018121004143d0040c15000a40740c80707028002d01d07509069240050541e01e8081400b0040c5040d0819180b9811a0074812006942d040031113581c46070200e481079250f080c9885c040d0001c0040d1030020b015880301104000400d54070085000503540e00ba070a64200c96075641c10551768508041c2c1d800e0118501003000516103019500202418205160101c0c0310345c01301441420000000b00214107070340002041245801c44214003c0040c581555400d1451408917619015502c6082c0d00c244984501404642242c0c420480c403120740108100341d425034101403500c1480440c1c1d0788001c945182d4001032218451 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 417040224 1250 417038974 417038989
    0x90129040b09100c0b100608070f0801032a0b0c0d050c03031311210106050f18131a0609010b07080318030c030724150311010905040227 60
    0x8030030031610a400e00311901c08001c0844a00940f00c010041d440d4031000c0414450350300f29000e8409281c00380d900c0c904140008101c00307001031450701070004c41d6102401a030350200409045079002021044131801d100c04201d0107002c01c4c9542401c654058001003564030a01d030041058006040403a00c003114044010b8446014400000c0b000d60420702c00140456100441071013041d1007102c030702e01d80c4190740001504800540e00820114210185400c44044c1c1c01d1040c440549000c03109951510410340000319415100c042c0c0380c80301d81d141303404135510700706205401602c180d20110811404c1503c011401600c581240c1340c3c1d2003110700c00000104045003c0c00c80d00095002007035645569103900715660324080e4400d003903089202c10400c0f081030000038005010070034814600301c840803016040380303116401140940104c952a00b04031840240400ba040070445c0d5000100e07410000c12100107a8928a40e0750041c0d41190001031550410103d607100e010100303442d2114410006c0307500e014403c1c00f = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 417041474 1250 417040224 417040229
    0x40f1707080a02030a03050c01140a020a320708091002030a02070e0103030c020d020d050f0109050f0d050423210607030b060f0d020c0313290d0e0c09012904 69
    0x13503000003464001182c4908004c01c0d0003c5c00b003001080f5a24203849108408404481c003000c00c960101d05500c9484e40640f00708107080300d030a140181101808004c0315030010810760f01c54030550008801e010040ca00f02940c070b150304014110305400c85100b40280d100e0b840950514018090721001083c42e1130014091410b0b00c1e016500d00c00020344a5082c0100b101384114141d0780884a03e2844000510401c9010880002d603400800d242e015440c10b01d02d495082c21a040d0144c1240c2401c00015a004c0b051f0760465601c00811b4406002c9600da0282d421018601c0700e030005100c1e0103207242d101044d40003c41003000042210f6090365903403021400c80d00d002034807990001080004400800000e000f0300090804d07054010701c1d2041c0551810b1a55022034800e03078ac844030b8210704001115100300c62405500d030350603100c0603988109406c51014844c0d6100610859611a0041c1548004000da0b10070104003a15903030243d40c49003541b248081007c042b507066100c6980f8043da03940380807000d8508 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 417042724 1250 417041474 417041479
    0xc0e010609050d0201030f050106050408010c02010501080303150109031202010501030317041a070504090207050a0210080c1207140a02060f01050415090f090503130305060633040f1707080a02 84
    0x595828802044030070010800c3c140d04141d1201ca0b00280d01d4054803e00c0d008003010340382e00380d803145040d14103420b450360b00303000f00c0543e4075003001002802404812a980103552201015080b003030100181c501010036040034203040c0c10401e05601240c0c055101e0703810380e4001e0315410405ca140407082c040500c01110020003941045981e4502050120302498200240d0706045080640351800c80c4100c1e04913040580c2d440e84070a40300b00943c1008410f1034a000d1491800784640c0c42c1803005440c40b8840e80042a0360745000c100081c0c80144150140000c10506200c09a6910070040c4000d60b0ba842c1510f51940e4082d0250001a02e4a0184544032100a0905030604200e1802010034003c0a2000c0c0c2100015100d082c84400110203000030004105003c21043c03075141107082039450807000a00050090385039240d41c244c00c4011184a0614200302848100004800c3c4001112406507a21800692060040c081600c55000101c01c515404500c01c0703034405d5079121900c1f590350707060000194 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 417043974 1250 417042724 417042737
    0x503090a0909020f12030f13030213110f0721050901020f0f0a0b1b04060c0b0c030417071506060c0212030703050405060d0e030403030c02010e0307030210030c180f030c0e0106 77
    0x12507801c0c000c0c4440e042651000649050038003003c00c41ca0540e100d01032002c0d06000d408812701c01c5161990a61150004015003000035413200002656140b040c0000020341250100c6c00038100603080d0031601c040c0104110714400c8401000014003140c01c005a554050300a007040076030b90601c0010820324030507640004180c071282c0d0f40c039002c01c0860007900c0d144458034040380e92661403a04000600081c42c582e0b640d40510307003460515102c0701c9809090000441030070814800496044007900200350750700420340d03540381000c1c905903890400e840702500c0900d007002400581c0c940c0040300030804900030303210008190103c503001030300d920450314000e010440900041c032407800d0806c05803901e144140d000084240798000c3c05440c58015500072400245074411035411542c0c09090b02d01030034001c0d030040c50141c2c1958002402c1012035407525041658400d207010700c0078420025901c04800c4c00111410241e11b0300703c9000492000c2c041642d000600010000301e0070f4039001e40d00d040720120358900 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 417045224 1250 417043974 417043999
    0x804030b0615180126040302120306010f0f1803060b030c0d0804090b011206090203060a120b06010525050a0203060609010303020d12021207030b0102011d07050405061c0503090a090902 81
    0x361038034401c070303c0c024100844d05101c2c452580c0e1002c50340d0301d499040d603e83c4060380341c81c1c940245020100700341d41118560034020b00842e40d030003a2140001c00c44034203080401034101c050464400d051481e00038525003c40000105110159000d550300340025000c0d151984c4030343e003d011119044910003800b8040c2000100a1203030558005031408505140140540482c2192401507941e030307803c001d14150f80003040c0807852a185187c14010072031100d410840b8901512044140308009110310f042c09400100781d610085504c2c05c5d0402a5050584040b00c0c01d0030342815035440390400422806841454045009440d285005504a9034554000c040580d11210111110402c0c000861102c0d074007440501c42c10088604124450500c41e5400034040040c2b000080c251664040ca00000c002c180d0342c1e03151218404201582510030945004c02e143e02d8200201c2c0101d90054440101c081001400104014020000b00805841214203050341500c52620604589400a00075841040042c11 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 417046474 1250 417045224 417045247
    0x914030106180c110f1b01090501050315120f030301030b010b0408100c1407142b0503060d02030a08040f150504030605100510020a02120d0807050708160804030b0615 73
    0x500c01c2c3c40441c0303004072034071212403101882c00385011000c1d81070b03800c20107038403a0f0741c00f006a030b0741040d070400d181600c01c42e46004e0018040f440043d102c2c41482c210006901126110070a9281d00c003029181181e1140e4041c40d2400e44940007070008a80180e04040005810300c0e08900360b405a0f40040040c20400f02d0a85014000340f01c00f2107500144020340b0074800712042d4207405040c1c00c5000f80501034070f1820115009042c515941490100d21140c0c42c14402a0801d203801c0c020001c8107818070a940307895072000580d8054050380000d41c184540700c003c4041010034405042101c00485901601503200d50031280c18040000348800000d030107000800c0401c0c04c40d00200d8102400060441c001038842c000306540301c480c005c08502591081d01c1b0142181031501090341c01065500240c040d0b2a03014500504000025224030b0410002040d01d905010203d0b01b100c80c0b82c2003c0c50090310450143c5850303040c941040c40240c880b41804800100d580c10700c400c280c5945c403c10392240c0d182030110b010 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 417047724 1250 417046474 417046481
    0x62c070503034e061f1d011b0303021c06030f0b04081201080601181505091b0c01050a0e0114010e0c0403080f03090c0109031110050910091403010618 66
    0x54400184180581c0c141056444070007071034421154a0f80c01d00d624044041c002484400250800d80d2000c001002d00c605510203c105804081810301c07104c400540001240d07801a0f41a4032041c81d0814400142007542650060801e044ccc3d83c0c0106582010640c4808210345181c80040c0100038140369000010b484940a954024484c1c500d071401c1500141d004060b00e04240c01c00602940124011b10150b0303000c20580b0741c0c206a0110903c05620030b411301d05820320a52182d503002d819400e01240e8822095050101c4448a100416442d5100e484600e8080c0c0016a84152450300d4a42c0d2001c400506000f000803400c6070750f42e4007900b646400100010180001c01c00072041d002408003000050441c00202140e800c07450041d030b200d0821003c1306082c60700c41030b41a4148103400f1070410000741141c0d032201e0085011214a4015200c0d40d800b42d84030f106a0024940c06503900803030071070080c1c20004040644080d0220781116405003030a0600700c8007180101d002c0b01000c009032014882040c0c0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 417048974 1250 417047724 417047797
    0x40309150507050a06050108160302130c1125060914100219060b0f04020a1202070c03120c0b0a1503060911101d010302030403050304020409062c07050303 68
    0xd001842c08480d5151581400c1c41140c04940458455004101c0201e04004101210140c01c1540041030300d59400160101e100725401d50089440b8070301052910701072580d10040c0f0b41c403e0107940c0c85496052050004804032a1140030f00404280082405481117401c1da041d5601c5105080b40d0101c148100702031007250a40c0e07007046100707076130104141040c80580d420405100740004148008203e0410041e2104c0c8501c15002e5031050200504640d449840c2122072040300c44011382d81c140a0400c0350380381049070806013255107034a40003900b00754021b101c1102107029004000154903901c00d05010342d1702ca20b8078031455030980d170420320200e406948484c00592003044000c286c0c5200307002050341c10741000400f60104405c18103e00e00c01c05840c00d1801e4040c02460308600c0c0d4a00f42d54050154040980064021035a640c0d80740f0401c54140d001c081303d2102491264898054000e103000080754810004903d0301a4080003d950300b0000f040d0b43c158101141103607483c642d0306040007603c100f1007 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 417050224 1250 417048974 417048977
    0x90201120509120f28020a0209070c0f111f02071a120c190207350a2301060b03060d03051905120106020c0112020f0c0303090106061704030915 63
    0x80345422080120f40006084100c1c4090302251200030348130108040041840100c4105050402010600b95001c5401c1c030120754100c0f031006072515004811540d40d26000300041041404048510034031004041190310080200d4246014050038028541c05118420007400983c0c80500c4c00d110140c0b418030034121041001c0403140c10030031201d032540e20980003542ca07441a02c200061400341d1819501a48018840f24001040440e2405a04100710201c0c80720b1290318080c0031011414071352a001c071803645420302e107045a20301c0103103040840b44070413a403a10b2860720f03504940f020100b0304180030300b500f102c0702c2c044410308656826007030020080103404214100101080480c585c10701c40b146140300c1411642c0c610b80c075444207a00200020748103800c0841554442041c28155aa0000c2442a4081c082402586a1851040368080c03409004605501070101000300005160158400000c0300e500d0b030390b050814031156189002084042c1d0f400b500080381d1a0307060010040c03201010750343c203406 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 417051474 1250 417050224 417050233
    0x3020903150406050f060a0602120306010908010c0e09060d0302120904022502100e09070c02030106180f0c050c060f150901150e040e150a06170d02070603090201120509 74
    0xc074505031580307000c216000c6500580d00d00602c150100c1d040603040c2e101c2c0701039800891203414242c02950715159840384903071110002001a250b85d21440c010790080180300002d0000e00207002c0040d0403940c150100a026800303a2000400c01c0c5400c2d4041ca1000e9003580240418403150b40b007901103607000d801c98a4005070204240e001c00d80c4038810080c00d140390407004000d0f4000d02e1041180424036400c54404000c0b194080c04107079960460602d402c480d890a2003403c4650900c0802c0c0500950b902c54034805080c00012400703543e060700036510707081014008000c41c2c14140801c1e901409400300410301d95010500060b00d0400e0f03040595000000088400440c4c010100000c4540701c01741c111842c0c17034003054440d200341794000c13501e404001d50031a03083c06284040035101d6030b946200041c00b17021007040c00120301200b2060b44044042c05282c4001c02a000a07030511507a528035007414800184107030b82001500038800c0c828a40b40d240c1c160b60303a1a102000c2440c0c030340030703050141c1600c03a90b008 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 417052724 1250 417051474 417051493
    0xd050a050a14070c080f1002092101060f0b0a0e0306480a020d02060114010f030209040218150a050909040302010b12010b0a0f080304030318031e0605220303020903 72
    0x100014132000a284100080030a0001040c40da407c0114442d24501018014000302c8641d2742c90b9114400b12001203240e20f0307800400c000511380544447e51200c0c00088400c040800d4840d1200700400b1000e140d500e0300580c0711060024075036100c1044468a519449400c402d12a45490707901040c0c10701e4862107202d0419058410440031000b80040302000f00500158000105806002c0c1ca400c051240c0060581503241c50354203c1114144400c0c14100079003800b441c0e5240340039a05072448060041e104545032042c04410288903151114010f03c10b2404011441c030406c002001c4890500b415a6068240045402804015600600100c05554031f40d5850700140d2904107086103a0201e2000120300447c10100b4048024081d801107581c40044000a00c00d10a00004450859070702d4079040c0b0000300c50500034207005540b03400080120006140d810352000b00741503400c6140e802500b04208644443e0340380d20b16400e01da48000c101803090072030341c000b181c06035000e004403160103030a851402a = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 417053974 1250 417052724 417052733
    0x10509100b04290c060105010807030603050a0f0c08120d020a0c0827030304080a143f030411090c1c05010f060c0804140f0402030a020901020d050a050a1407 69
    0x1041500a0f0b04600d011001003014140070342c5000845115055400b841c1050544615440e000d05000c0c40e4180304880c008a40214071030f51101004640020585c1d040c81c0d03291905600c02c001a80040c1c88101e207402d401b08140d400403a100307811102c030300710140c80d00400c890100d003c0e401002410003881500c003803400c04140102d00a00c540c110200b1032103100e42220550311004092441c1c1a4020342c81070005210038500014081d54164002512403145401411020315050700724002c0e54808500410500c907014121401c2d03d03d008948900c5141e84441d1020264a80000c07200580103c140c4c41d0011070906103820081d4004107160901c03441d01c6100c407099403400d1581040314007810781d201c004000034264070801c200134106524081000a95540b2030443c1c40c020350040107050b21544440ad4034503900c04500840034800a8070a54491170301c580100001c3d0484042540940100c84032280b80e14826011140e00b410700d80c0380c013400d010982e50200c1c1e80e100207100f200c81d245000c00c41c100204 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 417055224 1250 417053974 417053977
    0x812090f071a0415080612030a0c02060f0d0603030807020609120409020a02010f150e1501080610091208040510080c04380a12090209070c02031501230612010509100b 73
    0x142c613151541c0322035040034030134048441c09102d1400320681042c06034540c1c4c5503000c0d007401d0304e490301204c81540312003d40d819501148034002c159102c40f440e08070000101a000050244514400e03001d44205517180040e082d102c40e0a2244451a003d0400042c030100032a540a418241a0340c0300000300782c031600707d00c1412074078410f01e030340300f4042001000c10840c58000b600c5544801c80b212110541080200045c0c1401c00141c40e00d8412007800c0340c02d0b00e48600c51411072000340403480c00da040408a50400100b582d00600405001e03096251340554200d01404d5810301901d01507149614041ca0201800010b41c04a42c0ca41d44c203504030708148091044108038800c481c4442c00f0ba0958544103813901608500c012800034650380d041040400250780e40d0b049040c0d11141d241081c2c903c00d0a944002820495201707021165001020004036040c81603000d07401804056800790360010040b102001a1409130300300403526149024014800c60614582c1c1541103407280e5440b50405444603011a00b5 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 417056474 1250 417055224 417055259
    0x91103010908042603040b0c030c0a0c03140c18130503030412090608040f0b04061107050c0108090307110d0807150209030601051e01030b0a09090812090f071a04 71
    0x15201c1c040f600740310440481c00800680c1030010703204c540c403c0365511419140c1c01140b00740d1301c0b804000326000510400c207104031041540301d0011307120960140d140081181d40c2d80d000943e00743d202c08410300b900d2900040e00182c02d000c014001d0340d00f110a40c02c4420003400040400c5200456104074a0010350704001550050f8807840b440d9280b02c5c0401c3c0001c0240800360310500070880950240300202d01e00342c0c5840003494001880394500e43d150b0034148003800384440c880700b14200000380a070a0000105000c204110246d84941b60758452990b070503504d0081c09405000c00c609200f014203180307481034941400c98441c40c80141003100903269104803030740b0003004190003500000c580440b4075040c891540501000c40707003c18403000f0050048001a428200c1905169850010340280d035100003d003030041805c0f05091040d007006141c654100d8006031803152140d4074903400b24010b003d01040980340016180000e1035218580703200702512110340420b04881010420002c1004807030500c91960 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 417057724 1250 417056474 417056483
    0x50a0605030901150b070f030912030201020d1104060905040213080d120605010807081909020613090f05090a030c1415090f0a03080601030903030612060b0a08030712030911030109 79
    0x7140e2601c2004242911021007002c01070b484411010f2048918010613155026000030b01055082454541601e284000d508541d14544502c01c0030010143e05400a0800c40b0310307a103045c0040a003e4030290054060b0340900004201075200a0080c0e090030b034044c20b440052000044080380c3d0351444581050f007030b08000d2000414059820751100c41c0ca00411005207400e103095605840c01d80c10040c000c050107844a04040c80041815440d41000d8001a25103a0024203a036610264101550014585449140c0d0740382d040c903a8031880710b0f01e01e2182c1441400c144020b8102c14001d0340c1c007101c003005103980c00c50340c10440c4030740e958014a0070080040041c807900c01408144c10500c0f00b881c0b41502c88908000c00382d101c9030810b80020790000702d10390010b8003800c0110b0351103503600c0c080d80075000c0c0b070f00700601800410003200240481038200204500003a40d030304201d0794903400349a031640700c5c1181c007605001628480080481c480da0004580074018600080002c44200c0001c7c25141d5a60f81503c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 417058974 1250 417057724 417057727
    0x141602061308060c04030f030503090a05070e0919121b080c07060908011803080907120803010f1a120a02040e0411030105160206060d020402130609081002120f060406050a0605 77
    0x7054940801c926500042804c00f114109480c65441413108406201d00030208003010012564010f010014540710b180e0000560706120389402e022640e240c012201c480492043c00030300340c80741d180d048031094115040a180c100d91030341c440f000d030741c50b240c034045694101c0f00507241e2802040120020300300740c9000802604101d0310b001802044400d0079003021031542d15000c80241c1e43c5825450100303c00341c0c1070400e2a0180c0d80c0031001400c142c40d9030b101c040c540440100c040c041003107406c01103050391490300321454056241d8031400b0310070420704080091008108011021100c9d0100020780c001c1c00108054941902d400d210a40b12000361011560200d030001603c801d86000e0289941c041c4a401407603034000189e0700000d540c2d100261203107004492040811065445580440780042210380c404880c4c0da5035410004c201090500c6011300b2402212084807202c4014021101c2052118032500d805843d066086c104890004d800190b005940344400101902c0310b1225100920746605e42c507 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 417060224 1250 417058974 417058979
    0x30a0f03050604050118050603011b0207090507020c060a080c07120c05072304020702040902030d110601060306031211070e090a11060a0c0b130b0c0d1505011416020613 74
    0x5016a1409003030b00d84514202001401034464601c40060014210705010503181c941401081c010500030f60b40b07514100c5500840c6188980024845007150001d60041191740d486003000c0761202585040d095102030100288480d079403141e14a15000b241c9562800e14010740355030740b803050600c0424540f01240140ca10700c424404180191401410284412031580c0191804612201020108144219800310b050025516280d0020141d43e50150844601c400000f10280250540d60181900c5104920000c60034a10070b000e00740480c0c2c0d000703000c8408010a1207003641c0106250403045414480c180000403546281d0b41040d00400c01c260180840400500b01b12103000d010300380c51405100108941120f0551282e84e1907002500214602033750703140c0e05d140349518001c9183c0a00003078032030300c00d001c400001c120080c1744000c40c807a030422861407070203202c3c0d00c2e1010910882d40481c0c01c64610700c14000c1341d14018203006000b80c603040e40842056001580039008004004001508138000313 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 417061474 1250 417060224 417060227
    0x3160507050307060f18260129030609150103021e04060f1e05150a050f0711041a010f0f1701080c010f3f0c020a050c0a05030a14030c030a0f 62
    0x206865642446e8602c2c558500b451400307100200e10400584110884220128040d1401c2d445100f01800016140b030b49846c003910400c00d041c0c01060524407d0040801050780711a001a1a04032010030754a511004d0786181c0821425250322084500810b031480140311895480380305110260030f08a0b10b0602e01410040300841303551015035101c0410381e00389018040e80e5605040d1400c140d518841640c4d4800d0721f80002c454030b0040e83c80c4004100320102c0d02e4420820810350720710000e081503804000e0300d164252040c9160041440290110f0902448182107a01c01e0700d031840da6003202e040811110203004158044134909074054003050300729800d900039941e4080203202300003e0900e4448030181c2c01c0c40209059200d805009882081541c0c5140b00441d0b050710340d00701c14100311508001c1c5000d40b2001a480f800c43c01c0c41220780340104190079250741f07031003002c1c0d00641e00058000d058480c055903413110040d05080c06410f00d03100070b009461540104000414808046540d40580f10349003000 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 417062724 1250 417061474 417061487
    0x1e010e0304030309031b0506040314010b04050115030e0f15090c060427090c03050a060b0301020a21021e0c10140a09060902060307030b090a020c03160507050307060f 73
    0x9908a40c100300030810220354020000390a5981182d5454001c0c02c59044004120545a01154100601140002c184140050400c44840705400240b280904540400003240ca0034011240e000d9600314154016611992000704000e03514021503040c1050810494a0321140030801100e6036600010045001010700a01500490a0b03039075030b06180c10909503548002c0344410219000542282d0301045540b99003100e052640c02c240c000e55240d840b4100170303031940740801040e15200e041c04109131440c20144200c4400765600c0c0e03524013500c3c815001c04030318080e1604005441c1c64081c080c0c82c50654031151f8210440c0013180110755030310050200b160801c3c00012074140140c4c60200031a542c0100c003151240e100c140301030006152080b601c2c1103c010102403002a421038004420400d2064250340030810344c2d03208950500c540e540f1322040c00b00303a00c51100e8891050b0028002c1e4540403061410780c0e8042449402610000c50703c84000c41d180c800306920100007d0140040810115007101 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 417063974 1250 417062724 417062741
    0x604020a09180219171b1002120304030e030f0f07060507061b030204151704030806040213080c121617030d020703030218010c0314032205070501110703030819020c1e01 74
    0xa07100e481a00c0c202e01b0100807050b50b01500403c04011044603961081c0b041c1c035414a41e100d40f040c4c49041500b4001c00d00700940c0a02400b80c4181c401c840501880000c180c809600644020b00c1070b182403180840e001e82010704104d8205840b40c40061080320085c0e40183d81490300c1e50f0042e222031601c481c2c565451042c1200005210351402c40d0942e076590700100951090705030a1050040d120500802c00a100b1f08007440b5499181c0c500c00b044030100450a24640c01e000c0fa40d03030700940040300c0e4964a64043c032401841e041741c0c050301003102c040714204490702c0045000940303007071024949100f01a0383c0b01800850019500048526810b65440c1035414012403e213403200f90303410b10365805031030315841380102c05100303901200107031507c9140140a04240351090300b4000781e0003d450301c0d03950303008140075250200d806401c0784454010001994400c99825a9400945840f00204a096240803100e05294540c00b003220300d645410400c0408141060352982007901081079020398215000310 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 417065224 1250 417063974 417064019
    0x50f07110c0f0f120705030d020f0c090402030106050a080c0a1508060d080c0706020307171c090809090f060a060306140613080f0d0f020604020a09180219 68
    0x40d4800a2114000510810400415940000034103144000150704011520410740e000394510350191400c14042100d0b02190000c1d01140c108800e030101c01d07601c84504000c6408998001e00d452030f958540b10620640050001e00005091900c0d0004074403640011f42042d02071b03900042021402d81060710b007044c01010b02c002c2000c0b00341003da000a007189800350000d48241d01d000d19820500402d401141c0c0700388100011640041d0b541c02020b5220b4120348826950708001f420241c1460121004a0302c8000b072120148451600780e205440081015010903501c00d1b0080c46030000585511254501400c1d8000f406402442c040f020008a140030341c010a0401d414120300300140c3c0c01c11900c40c9400c040c2100e00ca51501907075001e900610301d1907401121035200c5d0358040f14000d1408a002d0303003100c4242d507900c240c1040303400059a50f40c0060720000d40004207641c003009002c00c280d0048090054144881c0b00e016442c0e00003410002003a0001c0010400e022820040c941580d1243c1c07042d00003d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 417066474 1250 417065224 417065237
    0x10b0309070519030605041703150414150622060507150606080a0902030a020d0803221104020706020d0515040606030b0901030b070909182d030e0303130801050f07 72
    0x8030940f1803010840e921005006a4446000c5400c0010391442c9520b13003c101081192646080c6206038003084501c8180c038041c51130a4031203030041045c6d40b074540c451400c0b004403400c42c1c51100c040c001e0a0b845490150500c040f0302e01c1b0582c0111700d0200400040032550b072515250291418141c25000c42031380d180c40d503645480c40400c12590425440e130b6000d0041d07000007074034011a00109081c034000c80d03030080d0700007000071403402003003600f07805140034070070b400e00c040c0844540a60320321910200e06400307403c07c600349032086050301e07140d002051007034850030026040441400704801541c0041e1a011400d00041010b0815401c0c140310f680010f00c4135103001e00290f54914040360f003c800601014080c4001d19000900160141c001d11000b80000c02d01001114000240e607030295001100458042e01d54445084500c41d034510446440003c8802c0c07a640b820140e5010b0b603009081110480d0140010f00c889001c010740141d503100203210703080001c5014a0607558448004500400720004e1120 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 417067724 1250 417066474 417066499
    0x1020309060a021804140709051503221b05240f0901021203040c15111b031e0604060507050a0504031101020307020904080c01050c030613091406010b03090705 70
    0x400210150000940780c2d0040e9182c2c4946102e2071032040c0115410380050401039124030f441126000c0030310540541e0750b80306000d41c866080017a0341100b8001c400a021050010800c81d4609074502d8000103080c00613194032810302e580c0c1c0c1040201030058081d07a101d5101b82080725082c1803240710708100c0565401d0000c03540300e0048800c9401149402c284684010455042c1640200841c21044610565054503031425142c520380c590510f0240707441510708220380c110920b01904003c24007111100c007900017800c01e403864200c1180c4104001e0391504c00c01039590440f10003c85049044a0341c0350141c1820700c0d050610b01e095400141205080007801c0003a02c26050340481a5020380741e209001b10b4005030303d540100d01d10301541c580658060007003014002003044043c010f00c10030250710001c0c4201c2d9103a48480364240001c031034140e0483c1390820400407407115540f10080c0c481c402c41501c1c58901c84014035034039010023600018003403d000428072074030080410810000702012070350802e0051 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 417068974 1250 417067724 417067741
    0x6050901110f0d18080610080c040b06161505162a0308100503120910020604080f0904060e1006091203171302120601140103020304050316140a050717010203 69
    0x815064010040000c4c1110070b5100c11141c0c038500c4001c0250908440642c20300340e00d03c40c00285248900c000322321505801c42607078101402030301c81d6a80c00920541c10401050207400c020310980c88121940c00c0c003204082040c0503a0320a04d8000c4031038680312003101100200285c4500804030f240e08504a41070385800d04203040410103002c80c2e41c58600700d8200d440d600d04e4006004041d40001e81d141c000d0031092400b01266078041d010041040740d140d1070003031181e1810703030b151031050b034002d003071000c04200c05582068003000400107684007820004001d65510010070204905490440e05509801010407109500041e1070300039001c003041501014400c0e0360f018200c0c1ca0302400380c054250304a0001040f54810401c14407415402401403a010070684911948a1209010780e103456100d1001d900d01552003482076030300c51948400250f15000101c0c080d01e001c440c0b80d010484000d14160b8800c0301700c0b0018415000e0340e52089000b801c1c2642412080d07083c581d031060031040141c2c818400c000a48 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 417070224 1250 417068974 417068983
    0x1c08100b130603091407030b06101d1c15051f0e04030305060f061b120a05070605060d020a0e01050103050f06030c012a05030c07050f0102060c210106050901110f 71
    0x260b241d414002079400d600d107803003020003582d11300002c0c19003d1054000700340a0703000801032043d5811241d881d104e18101e1016244a00c2103040001d4058051840c01d03102d003000c0d51800e4208040030141c11585200c2d6030707040743c1c2d0003000121000e080d40f02e0040c480d4003d0303281ca00f2160b101081c0440c3d451a42802001c45100bc0001c001030700301611100070400035101c060584410003001340030680da500503444000c01d000c140101030000c070301c00c14a400c1c0240000c0c0058540f200d106903266850442141c0741d0340050080541642d0384411400003480c01a41d502911100a10380480101c90540c500700024044400080c004038180c84140100710540d540810910001582400c0c00303c2030700c02101c0c0e144002e00c00162440882c0c41d451402e801030140010162002070788103411100180d4540080c0000c1542c8030348000c1c0175034410804a199200502d0140c00d0302c0c0100700c01c881f120041c400c4080b880303480c00c6e0b0240004c02c4002480e80e4555900c1510400403942c4403000b0850b90440c0c60300565035 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 417071474 1250 417070224 417070229
    0x200c09180f16050f060d180b0108061501030e0a17040503010638070b0702010609020310210515090111040f0e2505070f020628080f060603091c08100b13 67
    0xb00d641d21140b4003908602d000801f1445500700c0d60301d5820b581c4881c00d140d5960000ea8010030980881c4864502c5580f003402010041040b5401801e0041070507071700d03540d0ba00f40004078000000d100703005c007140b141c034244103e03c014620103591034089901140e00e10b4050b0409130084000e2001000c607241c581d04220102c0310282e0b48918101c0030f40d603e0034070803801000d03142c00a0201c14000024800040c020181c04415101842a05104442c00c6220880320729a0900c0c010003d800401c00e48401e00c2000c0c042942c00b0340c8110000c10744800017803604002d50b000d81c01464442000034402d10030107218104c0954460800c2030014032003181102c0010509401d1500ca1042250009022080080e00c0200f019003035400f0b00810713122410900030714203d921403150a02140e0a8036840f50040f441121400c0c00f60340d410300c0c5069180ca405080c051b00c0d5000400c088400d00c05c11400605920b040605219602411303900c8540300e04002401c1388400d03101c1d502c42c01c0c85134001e00002c210051305107c1c03e400c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 417072724 1250 417071474 417071497
    0x42307020d020c01051c050a020306030d080105180402010908030301120b0a0b01021b0402040e09011d0a030f0c020111030d0506011b0803060618030709090201200c09180f16050f06 79
    0x1c41d21407102ca0782c00c86c0c0c100c46a5032200307103081c4000d01c00f13035503090b40145000318403c07425107000b8418001304594550303091080c2580200100341d186010130300302d000c46402078010b14050300201d8551100031328607882a8800c0840c11910102c5109101700400030a1304081010018818400c0d2100000d5803840902d40300e00780f08907212000c0d0060750ba968101e500500c00c42c104070120b40751401043e40207080a001103040308145081088004001040c8030000d251701d500da0400c4c1da6000d0200f143c100c0c0f03034500100c0c1404408002156020003c0012f803446c08003940d8041800c1ca01540010044030b8074040f508081d40e40211707504000707041481500d5100ca026034141d601c403810409551144600f0b1210b03aa090b0003003d030040ba030980d50b9000110700d03034000c0c0c8520703580b0260307401c05802003452260a5203290300400d103807010704d02d80070700c03940d0f0041290456504101003e80c1030a08043c48540c2c11481c961203034035041c00b50081600c0480007860100c0320458400020b1001c144280300b0468001c1c03 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 417073974 1250 417072724 417072727
    0x170f0c010c1505070e0307090e070801020304020a0b0a02010b1c05010e0f46062301120311070609060e10080f0711100c0305090c0303090f0d02042307020d020c0105 72
    0x44c1030900c41c84182d64000d0b001021100c1070343c0e999070b044008008010207030041d40956500030507584414000c880c0265130240101e50280d152120a00700c681100141c1380440d529040b84151503500c00008030724440504800b2442131429191690850b50307083c82d215038540041804c0c0141d800701150a80f80c0d181000b4401850003282c5d4042064101c81e4080214016510190603281929003094041d41c40c0c49484100842c180c0040702900d8160300c0c0c041c48214102c0c4c08010300c0302c3d2154580d0a01302d00d01c82d09003908004000e420381400c02000f81c2156001510f0658104015035005100c101c513581c050711200702c042e00e20000245407000081c17070361000100d600c0200304414895040d05039030788003200581c4c61003414554040c018000c02c80c1e0f8600040d0500c0003040c078a10010820080c1c0c140018011803a0038140c500340407110550b03090f01c2c1da000d02409c40c0e5102584440c020007007024401b0240c03a12a1015402c2e4a10190000c3c007408115440b00b00558001c070b400042201081e602402c00e203 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 417075224 1250 417073974 417073981
    0x1125060c26162a030915030615050904020d050a051e060303040911040e09070f0b2107090305010212041407120809150a030603030e01030b0105040b13170f0c010c1505 73
    0x20710352007622541c1082910f02040c0c03050505500030382d01d80a482a48806821b2856513150031010390b04540182c03c1d8a2041001d80301c0729501600040c090a0300c050005414401d04013103031005c40708116000b50382a0b4603441001070b070000c03406000d040c07406001600c07059420000086a600e01481c01500b0840740c1e21000c0140415000e02507500620301c1a40c1b002e0f40303181c08083d42d0784924540c03048950001003454045100d07010f03001682d10020401c034508811f0b21030240103c05400e80a0860800c1c01183e14000c4042a800e000906c0103540c00f11013985282400e1800004c010540c0b00003c10b641c000d0501803280300d94a2800c0c001681d003045400b40c950010b00c2c00503181d0102210707260000c0700c00281d000880f513016000841160702a8481c47d00c40186000150160f519030441c4a00040c3e00304020b00180c2610b07800b5192521079074680b04a92074459400201070b550302408954168442003041c0141c1b030040008410400c428030349105103000301d940300a0002c91884271010102d4641d0000f = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 417076474 1250 417075224 417075257
    0x405011103040303090210140d150b13030209010918061a0a0e0f0f1005010c060e03040e0f01080703171b0601060c05060a1125060c2616 60
    0xc440d012051506a6a00d0410b4900a001482000d5040313006145419200201b24019940c0703c000301c0d0250f616915002040020a00410301e95003020707140c40f1070400c0401c1e801000f41c0034141008c111450078410b581140100712030076405a00c8014400e0501c1350020100440f15000c1c050b003035100f030002c00d000f0220032806241404271001d03107070040c8011400240d60020811021301a0f012080c11000c0381d200d948030112550f10071a54608040d124601c208420352046d003500309840d010795400100901542910750450780180d0094001c952540f0500ca0386259450f82c1d28010800b020080034010b04e540c0d1002c0d051782504c00700c04510750700401e10310000c000c90b2400c1c4ca95000c038401130302d6044d82c40390700141c405049001c040d80c0c188500c00009240741498801c00c840102030840301410f1516950320035894898603410200510309a8261900050717075402180c5503c007041d200d08480003c190345004498409401408541c1c0c021800c0c0040e000002c81c50020200341880c103580e05000d0b0307040 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 417077724 1250 417076474 417076481
    0xb0604150c0c210204050a1b0e060405061b100e0703060b01170106050417030c0606060a110607120f140a05090102091206100518060103021c0906090605130305040e040501 75
    0x202c841c6903003800320482c3c56901c0715a0644034040c4200d4041125440d480d0100c4201c4401001c4214041c81e40e0713500985403170003001302c2283e0000007810503181c5515540440d4140e00245142d500d000f80b00c0328080245a02481811035032841071004000054022445d43d07a01e01082c030000c1d2100d50740c1c010001459101d0b40040070700f040c0c000c810040701d507075404004106c1c2d03106110b15419036003040c0b520f000800002c001c6684898112000700050745840013007010360341c042e001e003e0500c446111041c07461002030110906c01c030440c0d00c9044c0034615440c7c0304800c1e248295003800506260091145440000d01c4005400036280400010117681d48182d032030081c07082c0746060354005841103641252010001d03082d44250701040395032410b00e0b5a581400440380c401e00149414a0f819000254194401e6019000700703404e020500c0304803041318800b9000c40301815005c2d60b4103912051007009010840c010707181c2080c40c1340030041c4544002c1d28000d1450080740a0060494000c40108090000c00d40 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 417078974 1250 417077724 417077729
    0x19030204090c020d02100e120a0e09010e01081e0615010e0604080109060b090105060d020c0c040c0503041a061012090501050708010f140607020d03030912050d0b0604150c0c 76
    0x807080200c80030381e02c0c0c06941c0b0950480d2940052141d044150100d13042c030701401d078400948400a10031040308212200494008e04134a20802089800443c070703c0e81c400c0600e900812032000c0012440d410039002506100e00c4074130499041070550f0b517900005000069490307006508003d00e009807140400101d80300e40d80c1c4642c242c0e01540100303000c21215010750220000d00e104000c1000304542e158180009003000348a0740364010814000d054080d01150014012451f861095a60340f200310000101121a8441c2c1180002c07000300400c410024070240b0340701d2600b102c4a07580c241d407500c1d00c0001c50b165504145074041008282c6a031071842c1d8070f6004020350690000c000d00c45031800c01c40051041c8030034030890219031101c2900142c0d00407941c1401954081c003404084c50011076400307016104500407411400c065070342110350081401c200020603407503c00e0791207990f58401e060079141511008443c5c98480c9000700000c12a0f119003e4440010540350f04141345c801005090402501e110765 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 417080224 1250 417078974 417078989
    0xf081e100503160e010303080a02070209010f06030b0409210302040b03070201270b0c07020f03060a050a0b01140313050709050403030f11070b060609030a14011401061419030204 78
    0x50000100c03201561900303a81055044810b000800d03600450b10140c14407420190228460050010920450341240c1c40403a40c0f001510384601030b40421440c8600342d105241c840206181400780b241d240c0202000c00344116410310809805445041021150f203809004419002e409030719118000c0c0c054400030402c2000c119164131745080c01901070309101203c09840d0500241606800c41082e582442e856040b260301480f5683d084044009984108000d80c0d02089102c3d080429079030800039948292401800402c079410003250480583e000d01028034140301c2810341103a05002c01c6801e90b40c0c424001d401d0310000d0075850510701d05022054209240e40c6040104000905070103410010b41461100d8040085006a5080048500941c98000c1c03400c400000800d11520701000600010354004055840700380c102c0d43c1e0070821130055094100c299450301c0a490b5000703074940d201401480f16040c814003200702460900c0107446a081c0c84d0080d194010403040d030a41c440c0e41900c1c00f60030388 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 417081474 1250 417080224 417080281
    0xc0a0501020315190807090b0f0306040501060612110906030402040e15040b0117100b010905040603060b09070c0201080a02210405100b0604151d060417070501030207030f08 76
    0x1941026403d1220030303076140d008100300c20310b440e14042d20788807840c22940004040e00103541085118809400e602c600340340e1040075400742141da51750a20516009612980002541505e0207201074a9501e4103512078444a1a11071840c120800782412200c01c040200c45456583d42d4a2000034010440d40345a18203a220b584621070744400000da007140542e002e4064000329070307139410341c85001c0b28500c8103014013a041034002007066801e2b41c101148421050403c1c9100c107450f200403808540f0281d1056907441d03114080440c440c14103e42071038200041e8a4040480c0d45550006404040003510140185130f0000d9551451001015540c944003140000d04103142803c1c28a250764102d0000c07843c3d8680d2421600c041c0d585042c40854044480304030f8084a4a03440604c1650076038890110294240808000c3c00c040e552903070001c1c8041c0603100e1440398107444109281e4500be10640085045c94070400841c00465045492800741708024a09002259544403103443d0341c00c03001c049080c030244c6 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 417082724 1250 417081474 417081481
    0x10080402040f110c1b0f09190509010b040b040509030a111011030a050f0118091703041b12020603060d050c1003240f1a0c100504060c051c020c0a05010203 68
    0x3d01400910301c405281003114045282c60000e60985a10110040d900c40303041c0c11050068103000158031792140312070003c288054940150a41503c50485201803281d42d91100c900c1c1c149010b10070a9510031007510100190b2170400070041c0c1d00d20526180fa014131808002c1c00d140d10500f003060350008032103280c0c14407905010084501490f04240c030f02c002c086040000149042d00b09551041c121103070b0840d0b83d00076040d460120001048102000d880010158010f40c0c0c014021000843c022442800d2030a001c001820007910300c200d0b56000b480f4403031440d00740d00000d80d03524415203422a4007201d5645040301540350491030010a03541d1550800800c41c150a003158065001c146580800f0801004d80e2150301b158100c0360380f1b64014138000e849000310500100754041c94050000304c0041c11680b07000c9486000b9483d00c00515458450942c03a5400c102c02c1000c1d9014241020100381441030402925807150700c0c4403042e400100a520b40d001c903030307007039104410044a0811a00100219941d0030b = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 417083974 1250 417082724 417082751
    0xd0905100218120f0d030c091710050c0c100b13140f130201051207091a0a0f09080c090c0417031305010c02100806010207181b050910080402040f 64
    0x106801021485100c410b840401d40540215042540b0740c132181c0903001d510048501500100301c8040c01e041000581c0b100801d155520804c141c484c405404010007540c084240a0000e417040144441e102100900c242480460005130000d000b0312a0035010075000000b00c081000407c03910600b00880e800e00304080b918488440000b0700036221011842d07074030b555060300c1701444100c41c0ca00a00188007084880c50782883c0b01e0307580c1d4100c0b6203850104400c60796200030512003003124510203229070001038003c0c85550085521070281507541005040c05142144d5648c4506a20410f203004180030300c000340400203400202c1d4090803640f403480070b075680d0f41d0b000660350f40c224240b0030030f1a8006c1d85000c1001d40c000e521441f08c1c0c40c1d00810007803052102c0d0000303ca2546015100f1810f5124003880440c2403402200c0c000c5200c2100d0f800000d41202d06190b600300030300c018800005010040045554039250160300b1072f03910174130b810b0000e0035440ea4404a070040040c0003d000c012840d2032052196003 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 417085224 1250 417083974 417084007
    0x301140f070306050910031509020628020105010b0a0305040c0b04120302010501080148030207020f0108010b0f0c030f0a17010e010e06011b02030106081f020f0d09051002 75
    0x2a0380554080003c503031148103014510000351281e450351010180c0410020300c80030080701d516000c140d404034058000d64003056880d040301c5a281101c80003502c40030200464540c00e81c00c80440307031000740542c1d450070312803410b548208030508081549440000d020b002005541c10020411f010f440b82c1d9030340d80d0f402c110010210001e004c03030055003003000001e0317000e03014003c0d07212280c610004c095100104001d4940320394550714030a2001943c0562a944d07100d00127901100d100d280361400359450750b6900c1000440c21600404a060024500050001c410001c0c152400e40002c035503602e90351408a01901e2542c051031568256000d000282480200e500c0304400080d0f41c0b0340c00111482d643c980b428200303104400d020b138400184403c0000f984940c840c6c00c81e080d00c0e8003081300d2845103800a801080c01c1d00c82d90380210015a118020411114881030521500c40440c0d00c811402c1490405062009100e000300007444c443d02c920b002c209000c414800b80c01c03000d01c060382c2156565480f29101940 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 417086330 1106 417085224 417085231
    0x50702031c0507060506040203041104021b06132609100c020414070e060c0c0d03020705190e130f0f08091003020319020a1d0301140f 59
    0x2100e030241201c56410749140e4503203030348100c00d007003c006580740070300543d000721f10400070000421501c0307503400340ca0f10040b00c0241c1c0e1048404003104c5841324002c0714a203d40624803d100704a02c0008640d851640700e400e01800f61610306180c18240100c40c11201e403090400c01c10708500349881030800c10862228141544140e80300e401203421542400340820b202d07550315081c4584140c00c2080313030310404801c8909501d400c0c0000c0b44540c80d0190102c20f280603965803c001c100700b500134400c0c20003610000d060070094000758a00c0c400c003c0f91520452844e02c04042c0441c00c00c0106c400000202500208a81440c544558403000406440e050a8030940c0091003056450395072500600703004038441c1d0b000340c6c070303810f100220940c0c404030728840410451040080b00c582c140c0150150603280c202c0700c4a80b02210030040801c0c05022009510ba4020311420100a015154411000d00 = true := by decide +kernel

theorem cover : BRFrame.Cov 416906474 417086330 := by
  have h0 := BRFrame.cov_init 416906474
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416906474 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 416906474 ≤ n) (h2 : n < 417086330) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
