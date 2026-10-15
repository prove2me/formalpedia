-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5417
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:48:08.313786+00:00
-- url     : https://prove2.me/submissions/77a5d619-e51d-43eb-a74d-ef66b56f1671

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 974100719 ≤ n < 974280575 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 974101969 1250 974100719 974100733
    0x60e071a040f030f030509060a081509012303010b0d0f03020f030405100807050714030901201b0111030a030c03050105011b080901052502360703021c0e0d02 69
    0x8100c82c000c044040741d81241c030340000354040c2d0500300c0340303807090700740041d0411000208148019400103249104011008505900348248010090801402c0c810544851840150031030300000c0d8100c54021142d008000007030b04440a0302040030744410360310139601c1403a0080403409050f0107100b0806a0b032000d2010b10300e49424000000c8210b0b909049103401c000301900022041c2c0d004004440203d41c2101d0060007410b1160106a40c0740c0c0100c078403a0000d43c243d1074091500400604021481c000383c80a4800003040c07407444280700c1203007d142d80c10490114054401240140010580c15807c0c0d41c2c0072405a58488001d010303514180c0c04203040244103400d5544511640b044122641e6202c00f00300c0d51481c24a0040303900380140b0300000307105048030000e17204050300c08410340b010a10036101c05035a050f1030071451101040c0c00b08c3e0a40046a81c039220300210040c203407810750000c2c25003401400d00a04420101c8440c2d1040742c914600c92b502c04a41040940401441c2000c8010744010258 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 974103219 1250 974101969 974101979
    0x110a151d0d02030f0d060e25090f0509070507020d0302010b27042604171501050310020a120f0903021606050412050a0f03170a060e0705070f060e071a04 67
    0x540e200e803000e10311301c00341c2c0481d000c5000405030b00084004c060300310310000e060410082d0704a0056002201c280c2c012410440300c07008a004400307810868000003601c101051411b402e203e00301c0001009030b41080020400e00c401691000381d4604414000d47c00021600e1410050062601a40d02c5800d10040482c4040030151824044c030703913106902c801c801460350840e030344100a014075a103602c50034040104002c142c154880c0c180c440c04a404d14103c410100c0b20003510201284280125a059040100c07034061042c507076001030224241c1d034030300a007004421101a60888440a05400c1c001d501e448a110500d40d04000c40e60f000300410404510040c50044043d090f440783c0d11403001500c03003c100c80b0007440418000c016005801c0b40b28003170300d03c219180043c480160b50030441f0038400080085021003ca5104140503a0660344070281d083d140d0850a840c0c82e081142d00305c8141c1c15030150403000841c1c0e0301170760080d500080018913a5600701a40e00741d40406003c0303000d8248070b081c041008 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 974104469 1250 974103219 974103223
    0xa060905220201020114010617011e050603090a0c030602070203010f050c0307030b13020a0207211e08090a0303050301090e1b1203040b04080714100c0201110a151d0d02 74
    0x110712080c0c078110101c1d07480c10707200503805001038054000001c01b048000183ea40c2d0007007021080e800300000700e40c12580e00c820700742940072900c2d800001544582402030049041170801550000072079030440700c1841032980c60400c0090a038104a039045c0d004140350782103040034003503c000d05401034030500007460314950b60080c50000a0450041580b036190086e15510780410190b0f50f00d0041d07000359a42d40550401a5a55800e4402c148010800300303181c0c01e014840c0e031140b0120b40d9100d120010308811409400344103186035030080c2c40f1040308010804041c0d6404d010720b80254401c1c2ca0701520fa62401150904403001100420490f410258981000e40f40e0000d90700150002190074000f2100d0500085141d07000c1c0c2c0d0011141d056000401040400c0c00141e00001c4a42c0c405280000d40041010310000e80c55406140c000306040c884c08800540c003590740ca1400910200803204c5441a0707880d182d480fa40c0e4501c1d0781d85480e81d200c0850380101c141c590240e80e1840715134018003103002c4400000f5 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 974105719 1250 974104469 974104501
    0xa020d080f0723091801050901051002060a1508030d090c12081b0f030705010509071a0d050402010e04020706090b16120f02070212061618120c030b010e0a060905 71
    0x1400b40071074460700c0202e00041100784c40d0412005010002400070080303003803031401028010b0500c5030b46041e0000170546004840310202040560250029451790300070100508003c242c1070b4450191128041050350381003024008654900340049000180e90030700039183c0100d0340000240c4080582c0079030200c2c1c8001d08031603d0040c4408045800c0704840e881500b030103c0081c182d10b89010018118041c000f05411490180d90700c0c0007074548180da244003e000d104205088601c03000e03001d02c20008985920b9002c42e6100d80103041c05084c1100f4400060f0483c0d011402c216221640c846050091002a0498543c01140e040c1412580b82200d071001e49940030800c0207110140d00c1d680505000c00054064070b2209030301400b9011140c0c1c400325001c0d100c18046410302000c0144d44070118445100d840040f04070a0b058181901032410302c4841d041d0702400d81c00c10380e400c0c040414000009040740c100580200341c1c540c440c0c2c500b41081c11412055130520f91002514078100010702000d5589000e41c2 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 974106969 1250 974105719 974105747
    0x70c14160611071d041208100306050709051203180f0a051005070b0408190215070516050303090303090d031a04020306040e011b0f1d0d170a020d080f07 67
    0x42c0010710b210a615600e001a15003100203803180c032944000e9920555250b840c0503603c610250801031840080880705800c04072015080041c90300c0c0f04002094140d401582c00035850300e09840001d4480010862800540d05501080c1e0f00c0081e200014000c4100a14180603080b80c4103005d1962400000700740070002d002e014800c110261040445034003403421584c510354402c8060810345400e04100c0c4c04d90300580040d480940580007460320041c400705000d4007406002007280c8454070f032090100c43c250001d10003004600c1c0d1084021000c1181080507600c03840c20b1400440d9607203411101d081c10440a91400f81c10f1500307003000c10191080300b1200c0c40c400c94058030016181c2d5103c034001000ba003940200d8690f554a801000280c0b004e82d282100000d0201e40c5402c844408000801c690716840c4c40d001c5482c4140861204c20f552a0518032402e07014041d00c0306040260b103a107030000496028002440150f48040011420580c01c80d84003036002254440b540d420b45060140501651000001 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 974108219 1250 974106969 974106977
    0x3f09150f01063509250302090a1e110d0203040c0512030a0e010305040317040b10080c0a05041109100801080105070f120e1606050c0f07060522030803070c141606 71
    0x103140d52802c000280c000c0c49003100503c84111000c5c0485004603150000382e00401c000d1000031143c0540b401203200d44141c40310100000d42410181e01d009010041c1400280f11f8200107582c2c400140d03001030350045008000c00c04070f031450641000608914000b9840c0750f03802c18488811150303001481c102240c4d80a00f4003084c1f66645103012604003400895140800884405201c14002a110381c14402c41414200c6c0c0342c2c2580710407402c0c2d034422540100c3c940c84800400f007440181001c1c3c00021101a01080250801c00c1801c0005c0c00441c05104150005013a20010060100c00740544c0e03802c14000e0529402070414010300400301c43c911080c22000d507445c0e1941d02c109420070406007400d0720600b1058000c0f1071711130000800a0b031010003244146d00c1010102d000e18031020504c001141c945842c0c5030302c0c0141c00d401040c80f01e0610100803150800210000000c1401c0b08020b5111700e0b01c5544082400c4081d11300302c5810060b01c002c402c030720b6001c11810341c0401c051500c141c0c2591042c1c20 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 974109469 1250 974108219 974108221
    0xa120c120f240f06140f060d06030f031407030903020105160519060f02040e130c050618010f1d120304080f033f09150f010635 56
    0x1040440007060300c000a00340b8048007080d0001202020b600600c41191400910041c10742494050075038800f40100c2c501c0b80090a054a03091601c01e03c01082030b4800b4080e142048a4201d4003803c66009520a84064080044000806602c01d007400551800800d0840c1481d1040e200100800c5e55400001d045c4800000e20358a0b0700307000c0b500300382015407000481c0c0c00e80b503034100441c02c1100400c10440d03201e410200001200176050080d034094820b0101e803260f09542c0d800e0944443c421001d000d03a40c04017040030120300e40e22140010b1a641c0d01a0b000c0e0542c008003200010141000c0d0f08200c010801d00c071110b5017001c0512043d2412410086401c000a4903052052030308601c00c1d940024820710039a052050740368804000327003010458208440701d6080000b9000e0f011041001000829820203221140810b09000061600301c5000b10803a822079084401c000d4000c90300380c85020503102c10400400510303034048200405000b070340c0f1102401c117100c014016114130300c0d461540c5140c02e500c0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 974110719 1250 974109469 974109473
    0xb0c1903020c1e1608030c1002030711071e051c02010f090518040507060504080a02010f17100e070f020325052e06031a070e0406140a120c12 62
    0x1a06640301400484009560900620b040d554052042e00701c1340d41c032980000040b444000700c00e403a09521480003800b03c40d4066000e020007580300a103450141700c00c402d0f02e0820b0a00030042c0401070029000030b003402032000103050940c03000d90b501c880e100e0a00e0182c000509030812442c4006a503080c01e060054440e861416240300480c5c7e080960040004581190103080c42079911380160300410594468645a04084806211b07600408145901941c5141d0055104003a00c04440040d40b600000280303507502002d01d06401591700000f1406a00802e02924400041050300200b09081842d11551502d002035100d01a035941e6841004040c511009403050b181c0803291401ea00c0300544002c5203006c00c003001c070018150300d54a0030004540395410f035000d4500c901410307650845103c031a4092402e9640780810b00007403200b010440c55040103035058a03103005400152684c10302c8100340b21644820b01c110705c821039008411004618041d50b001c62102c6059005a03002c800712030078510a54 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 974111969 1250 974110719 974110723
    0x80c06060f03030d200c0a0b090f0703080a050f18010f0504140103050a0f0e06040b060a030f02041a10030204081018021905060d02030105091303120e0c0406030606030b0c1903020c 79
    0x22130f00110717035060000d690088004041142c00040d44981d032040820744030031418594420840000080782d0307012840c01c1c80070480f48030103050045110b2a00d940f41c204105c0c8105041d402c10040b21804e020041c2c07404455680180c42d000041e0741c686096810585081021141c2403070b01c1d0811414140c0e1240450b0814450313070030110454132500c10074400b80c1c808807902503881300204c50582d400186c0c03c0103c7c800d4036045000c40300f1a5004aa204007412040e000c0000400840c18003501e04d14003011400c41a1b11341240a01d00400b4944005841c1c614104000b0708000d058940218002d107807140e1400260032421305084075940594051000045010060000301c80980002e03611174000701d16211813442c50b0300194181c1d5001c1d11100c066031199100c00d9000242d9000c010041100c16540b0400034080342e0002074546043c030115404003012001141c01c5810329001643c80e2a00c6a100f8001d03c045044903d8100c3c448041c01480c0c44c0070807102c42a01c4103040342c0341b810150009000b045c07070801 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 974113219 1250 974111969 974112011
    0x190305040b0403081b06100b030705130b030702100509030a050a110111030a0605010309050606040b0d0b0a0207030e060f0403020d170d05091b090f1012080c06060f03030d 75
    0x35000d820742d42c0307a850b420040c84c150068000e0726150081030f40c2c107002190000c2001c501407040d040b00c02d0802410944501c19982005003602d04000b42485406050241d61048100404038035851941d030b0306003483c3c001e080100110103805101d041c8814002c00c1d010000440e0500c003c2c40c9030468840c1f005250444510980c00c01c083c6040d0700f05500c010004681c00025405100f203a98100405a9154012740c240c61134080090001e4201c440080e4081c18260000c6419000081000d1603416041c0e075001081d807000e48250f0681c90380443d1420030103030003682c0f101c0300c0700341102e98a0070000c0b441c0810000b48203e01000b40140400440103040000c0f04900c619443c07078201d0340070780b56900c0c0080d8000800d81142d00d1038580c407819403291070301001d502d4401017110024006c1515076903901d2003046c00190181454289160f0800005480d92002080d0000b00340b00b1038600d039841c803840741d82c1450312038041d0440707216803603411760481c0325540003088503140c01c0600004140c0002030065000705c021 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 974114469 1250 974113219 974113229
    0x7030219020d0b0114011d0105090f0406090e0109110109120627110910060509061305040c121b09090b0102010902060a050a140309030a051608040e0f13030219030504 73
    0x10f001d4004114491110a00c40fa100000c0e42c1d44c031030141001908044004629140c0c0380482d1040020184c0c03428403000e52501e511025001061295880900800300c41c12041c0020072a5560f000100c104100b04110b8009020246024101c45003440d080103c03110648500910b5541c0d50841c1c1d40e0842c580425000340ca404082d10141c03454003508000001c4418a243c082c4100301450000e0041c4a08421440c1541c404ea62054144800401484203a070301c12451120400701d8400000f80030307612400350701035a488035035503040c1d903000b6a51484141c82e81c2000d119038528a04000302c0d500e03039000c1d507503008440320307004003181c2c00343c40d540142e0041a0082d00650002000203541907400d8018000f00403503025555280881c0c000000c444545000c02e03140000309400411400a515201d60044c10061303985103240b0143c0703440d664035036131380d98810340c05a00c275002907008000c0c80503840c070342840c0d00c0050740194031101100b43c0d800035201c2042c0400e03040f42c0090401c0a405041c03141050b540685 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 974115719 1250 974114469 974114483
    0x110105160b1303030f05010e070c0201030b030d030e1b0d0609020f09040b090c06040f03030f05041d0a1116120e03030c07090e0a0b06010c060f0228020307030219020d 73
    0x2c00c0a101c004228104400180d01107401c0120060a100c2140324080c100da4500707400d0040c0d501e841c40115281c02d0202c405030704064566100090301d5905101c1029107031101d40340000c0ca58424440c050806070400c2503603888407551140c00c600d50320340b00e9202080135071003000007403036a440e0b10002d0180303160f090055410604403000c0000b000038030004103000d02c4100b07044605825040b800c019061195004c1e64804041d14501080003d000b10b0044802d025281452400c2070f85074000f28071094214110303089007815031010f00c48811040e03c600c05c41000f004100702d18054000320701c116206000c0a000301000314424650681600c00d00a0b0850030b400141a2070f0750319203c8580a541d5040750054403500c1e07185c1903248070a454002010741d210b0340e001c280c076013890751820015992400c06030025035a043c0c55013414000003503184010408442442400303000d0045910354007800c1c0c54410f80d80c5080d54002c004c900080380e000210858084e00c108800000c0c9190761000c540422210351004140c0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 974116969 1250 974115719 974115721
    0x30711120a060518010b0a050d060b09090724080f07020102040503010c050711030c1305060f06120f07030513110409230d020703030e0f120d0201140f0103110105160b 73
    0xc006508014010300115013005200c0b00c43c0d00701c481c221601000a140d021000b410100010708280f00700310305050003803d0000b00b8400190125240c2e034012140b0440640000005208404040e140d0800d01b4910109182005116207409020410003610060034401d0070000102c0f414801d404440161502800034842e0461201d4042c0c17050708455000c0b61803112025241000f0f0400080708202410b0040141c2030b0051031903800c50013840d020700703144e0300140420080406600e42000400700305803c070000c00440c0c03410040c110030580d4054580000c041c1030005100f804407503000740c0301c6065040351010038070b4240200060000c04185c10000d2804031041d00ba41502014030304008810450042544d04030074500c0d004136100c4505d8000200420034102d0410441c1c01c04e48440d4190340000341c543c800403041c0300249441d0111401d401d00044c2e444820700026941100c850b02d4208581494052003541190f8078865003110740030f4454100007020440d41c0c0d0540d9840c40c103c0c11603408c0020b071039617 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 974118219 1250 974116969 974116973
    0x306241314060a05070221060c07110103060305070b0c031b0d1d0306220f06021b01060b030a020f070f030c29150a0e0a0b010f050c030711120a 63
    0x20441c0c85000150040c520007405541400012111880e03155038825141c000c0650030454510070407504d024603c80030409032903035031000300011b034020000042450b4544050f45000500e50004280c0c9030704240c1000020800200005043c8058078018822145c42d001502002e62550040402280c140200001c207030304814400300f808160850310b961020000b0340c9100380d90040d00c01036005190964401e40006171250490180718922071506600041e50a1040c1c546e204105c460701401c1c0c0e00d6542c0010700b0f103500c00091044447c1c070300303034000244019031800c03201d030300c032800b00400c070703640164000511128a0711003a0031900b0541d03110a6240d5004c0241c1001050025406012200c0c140440c649507020300403005212581a95002c0e0f0b4a41c55554030103003413080d408044e0039508002d14000214110b40c1d80c14040e480303541400000580c1800c80000105180800c1c5100010311204009448d00104041300311141d441e0801c1500e40c000d0b540401041c4040c40b134803241201406180e540d481 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 974119469 1250 974118219 974118247
    0x10309151e1d070608011d0406180c050109210b0c070507090609050c0306131d012d09050d05090102281a1509130506010f0305010e0c0105030624 64
    0x201c502e0003001181c8072603454000c140d0b4801e5083c06405000c1c41003240d078407481151002c04540c0306100e0311002c1040506850100701420886800b10380c286143d81040c0580c1d68403d1034200140800420620110345100d62900401103c000142440002100181e0341c940100110780c0015408011100210b5a03495450010701c0799000720090f907407d21001c5218904564103032401040028003c0c42e80300c40c0400301e003008021050b682c40380b0300c4005501c910103601c207208010035005d020200b54060f1154503a0150724801c5c3c103100c0c00c01140b82c02c2c1900082600019080700c3c0040d58200f05544000b0140180d1400d11404070b502840701802d442116442c0e0101c41380000700e0b202e0940e900d1110180c1004030710340d5104030b030f8100383c0105000e00c0e801645041a0184d404c10f40b0460300310302c0718210384c5483e030600b04240c004182d1709101040403c00c0141c00d00c96403200c45440f00240c05204e848000003401da1001134101c5229808000005441c21400c044c1001d03580c03018039200f59140301801a84d4 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 974120719 1250 974119469 974119511
    0x80f0a0201110f09010f0207030b0a0b090c121609050405010f0521030306061605010c0f200d080702151611030909040615030506190b010309151e 64
    0x90015400c002c80b1000b41e250b1481612220a5502c00d4141052400801190f01019007541482107120f000c00000114130091401e6000d91107240000c108108500c0c140281070402620815444c04204002c62203090034001c1c0a4200340c5058120386c0000501c03108894110284d0000b0703030300924001c000900882c84544d29411a034090b141c2c400020040f14100c500d11200c7d140707130442d40d002040010301c00d1915600078640f614500101005e400710a844050844044031600780c0450186560810110b40040a400c01801003200c001c1740c40440001b01e13512280d6905080c014000880e000c030760024024011202141001c03403201d0014545500c1860701a48055140004280d0010b02c03100c0040003c0b044600864000d0b0840600d501c03540d132540010503110000d01030240300c01d040480001e10a210b0580039005c60702401e55016078412401c42251003d05505d414540b0f4a0480000070b00780081c50680c3d03043c082d20014140002406400000807510201031495180010f0b1a00e8081031411103 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 974121969 1250 974120719 974120737
    0x306050603100c05181c060e0a05071503050c130605030705121005010806030f0303010b3a1a10030c030e15012402060c0906040504062403050610080a09080f 69
    0x4002606950b400d10006c40c440c103d0300000e40f00032050b9403002c250b264114200d4200940c0849103982625110310742441159008007402d04000381d07442040c0303580742c0207480c0c100d00c4c0a01c0403441c01350601904007040f0380c0f03031080340140305001c000200d80074042c40076141c0c03601c401e042c802031501d005e15a80c0145030150040501040059011070382e1800c0010340c460380c120b010300040d4a50390802040e140c0c036400110468020041c0074a00c2c5140c0000b6225400001a250781b00700f080c04d4041a1040503070700d80c0b00362400300391000002c5c07412541c1ea05420f8040c2c504141800a100c001a450440140080020400d003900c20280d01503013002d0005400390484210541426043c01c80f020f14a0100d0360984240b80164400f101107541c1c00b0b0030000918a01c580109040d107080c0d40ea402041c01e0701c03501d6005020782914038041114840c1b0f200342c01090062603103400c100d40d14000c070014070034410300c19111003000340b20000601d00103140d40c01111595001144a41c45030840701407010389600449c0d032 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 974123219 1250 974121969 974121997
    0x5120c070302010c02010e0c0d0503090d0819140f0a030905010e0705091806072d030903030c080c04090e24100801060602030406300e0c0d0c0306050603100c05 70
    0x3101c02280e2042c1f0406030000e1081000e05420340c1458104070f080c200c420005d8685000401048081e6524101445050352240c070b08291940d48028500f0301c0c2000403503036042401844441c01e0142140d4404480820320385185d681d403201c102c032104a00814007440c0080c880e6103415070000742d2100004a400031a9421180c1c4201c5030742e076100c80714800111481d00c125550080e0041801c4a0103907040390313440c2c0f03460041c0c0d003540000c85035030384441d1a0403d15503001c2039840310800141a81401035003a040e080d0b082149032420541c000c2a094415403040340500369682d11404044802071003288220500b11003009a000d0948620500000e426142410b000070f521800103040041800b80c0c400300e8500342c0183d41040c3c607000e4103544042501208248203500c9038007000e90145401d100d01007030740e43e407100000c0000c0c4d1550783e84e142002e6181e81a00c190300f1403102030009030130844520240e0b03501c46c0d000309041d19800040f03841d00540458001d1001e0504502460140e8440d01515100c40b018038 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 974124469 1250 974123219 974123231
    0xb030703082d0904110d060f1a072d050109082101081504020609030a030f031d070b0c0102071a0411010809060402040b5e0c05120c07030201 62
    0x15500c0200d1010742d100300c5069060050000614059002e50a801d080e01c41851404020075501c6081b11060781104040c015402000e01460107601c00e002c0a10004035501881d1104503203c003074859a031290201002c015000c1a420700114851140000d140c0c007500a00403010356103042820b0350030034800703801d442c2a481c2041c090b2010800c4880e0403982c41c840079090003528010800017200c4010000d036044442000020030301e48042013081101c2d4000e9a80d0010341015100050903600403408031300750000c0e0030a80140c1c0740c0010030158103c2c1e900e110341d69521803c444011740680111500a03101c0d542207c0f030341d01c1c68070020300c885d8815072140c19507280c6d02001500640b1410740070703150000790790b01580000300142840e030700c12044040020111031803d48403941c40380c00070502100001c501030901c0307450220705203010700c800c500003003500b4070003085c042842000400590740349124025544503150b03407401d0750080c42101d0f46c569011024480d50314019a01c4e521740d51120804034010341ca00782e = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 974125719 1250 974124469 974124517
    0x141e071a0702100e15030a050405010e01150b0c100e030403060b030303010609060302090a050a260109122a1101020d020d0e060d02041d01030b090d020303190b03070308 74
    0x2404903001203074020310a40e41d80e0300150741244c281070f108103040c1e04114500854620304d000c00000c1d510424101070080740c6803925140c418251034000b029981c050781809170142c48000d8031885042a00d411760481078a41c9001c0d10b0031482e12210300e0180750001d00d00324120300d507a10b02000a10990340566024841c2101e844145680c80c4000d1103107800042000b0000d000c018466001009041802461400c2103520790000030b07a207110603403211040030035540100c6001c011a542e4589a580ca0710000c2000f24915142c1c40c03684445102c0100820048110703524080e40e02e0781d0260319840b401aa840341412080c034090010340c488245c66400341c8078001070341044910000d040320344650155641c64600f0240002e0024a80002e0030441d99246c0a000c040395103581c0c0300c0081424035003041d501c2115455404c1c484039064000d84441555009000362140b11070b000401c5a030805028bd46513084100c881843c00000d0400c8204c60b9418043c40d034000041c001c17800c000d000714081400030398802c540c80c5 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 974126969 1250 974125719 974125769
    0x2108010305070b0901020f06070f140c031e04171e1b0f0310050c070c0e130803070905030d091406070c0905040314040b030f01050f0d141e07 62
    0x24803004006600040c0180300d4500e400f03010340000c80c01801150710344401e6402d620f061140845000c00000d03c04000b10a1240d07002480311002640d100c0e4051030000a141d029860713208010141e401108a8210020280e02c114211401004540c0c5110648420754000713076100c0c9e174010750302c54a03201c0703d00421420f0000810303110b540c4441c2c020203c1031054244144901030b0701b8008140d038540104c2c102340c0e0080c0c2d11801000d1244001c0d04200750750b8255890610508202604440a9007409604000c0c0d642e2940b84204d851940000781c440e101c0d03807045012142c01e007854002c2c83c0c140c01136030a940d46081e04401c1e0402640d415a10900d000d04111060040d280241c8401030147c2c54001ca04004040e1541d1146800c40d00910300640307407030400d902d034070055441079201403404034000040100d20720f0030511443c05040100c50312900441000f0015035042120140a04150244558018a040e040103a1300b04a00d0f0b403031215030300c440448012500d4848600c03c150200060480c07290800d020 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 974128219 1250 974126969 974126971
    0xf0e01020c010c05030d110403020a060f05040e25020606040f27061103011e050102010209060306040f06030501181b0303170c0706060b0d1428020d092108 68
    0x1039000344507444415004550000301900e0030381c1d0900080014600d002c41030f0003140003403003003030a259a8881c07652040c00740420b000c2e40a07400300561500224081d40e80441140d00300e0b52120750f10092030f104c002041c1c5c1110041c00b0001c03d0080c1110b9800c0c4d15503004a051031180d1006c46003000300c000b0a1a850083d60f80c01c026000c10b09000e4050801d1400e0502d55a00d9114028a0000b415030030801001d8200e6000381c120402940f0300c0c1380e1040109541119540181800784002d60804102502092260102500452149856508940000d1010b0f84641c004640210003031020341440140b0f10030004600005441c81c0c80c42da552148000c1c109101c81c400c5980c10b42c0ca034900c8007007000358400103a4001e07010840d141400c009030004202107008450160042e481c0e100d0769aa040035500f01280c8154450740070300c4078840f003001a0450090704080c0c00310840c0100a41c0003181100e518024810016200d400500c0d007400740c0300340f06a00409a44d240b08600020a0a80030320b01c040e568890 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 974129469 1250 974128219 974128247
    0x1050118090920090103080d0915090b04050609070807260a08130b070209040b13080715050702010915050c0423030c0102150615090d060e0d0c0201121508070f060f 72
    0x18108842c40340423404e6440104031a01500110303440c080707000000810307a070210382c095070840800d90a20003440010300070355400a1482004068862034002c0f0b1644462540c4035840c051107200340c44081c5000c004113010fa480c02c03a5020b4990440042c9082289174120240c060012140c034000420503540d8017040301c0800341c0050011072542e0b02c41d0740d144003007a80106030500802e0000300e0100029019805010220700c10f071010300042003210210002c9540042c1440110781c140621580410600182c08642d01e01030100411207560b800410405803146500607625100155503640d45003080c4100c1d004111005c405686c080d03c021401280c3d01c0b00d01104220410040340003040103480d101e10003940c22a88040700310305065a140003d80455800e503426903841d0307124184006100b43c14009803052071501c0c18410001ca000e0380009002030b2a101c401c8080503520303c04922240f640c0010000207084007412600b14607190800c0340380140d170314492003002c5601c0b035000e00342c10f03400703003541c455101 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 974130719 1250 974129469 974129483
    0x111903110c0a1b0f03060c030b1818120c0102040f05152502040c0e04050105120d0e12071d07030203010b0f071b08070e010503011401050118090920090103 68
    0x1014646801c0001c3c40c01411a0b040d20345580f90000d0342c5080d00b02203100071401404001032076840300b2005030075110551010f03803180d4070702c400004c00740c842c0c0507019421283e0000203a421900e200107051414000d0a5070361840741020862000300c600540082040d202d0081c14142004d9580702880207001403060b407803807522000e01925104032294000001725400c08540c0702c1001425802003805c80e82c40701c3d0f003540052040418401e0394107080c000d00e801440b040e5003200b40080e5864de103a80301d108050041c020060300b668840865512000a00c00c6000080256100a0ba848000030ba003008000c01840540360310000160783da41c00b0740b083e01e049403100400d83c0c1c030b80740584010301e030769905c40001103c0d8010724003400c6a016a501c0784d102c000d800072a0040c00ac076030400d6140407600c4030591115101e07030305016480211821300c070907850445d042803c182080303100100b02c0304660100364001c0071409207040c45500a014075841000000c44044000d01e214104003c03d02a404100740030180c004 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 974131969 1250 974130719 974130733
    0x3040f0302100315030804170a0b0705070302150a0212010608060d120c0b091e06160f14030c03060429060307170907170f1f111903110c 60
    0x5810005a802c040440c280350000d80d240d2190641c0d6444141ca800c01c1e01e8520001c00c2c1400540030f0040d4500950070300e41d0080407402065640ca004580c00204580700704640410381800700b600803c04c2e8009207403a0840e159403880d003488500029008404070740c00211022000154250180401c02c2c050361014100a511080c03d446401000070004c2e45002041283d41c8107a02240c001c04aa60284026001918452070344103440c14908035028041c1d002504190140716a602d895280c616503075000f400c1c03090b00254400c8007902e0103106940700c800041400401c014440511a001b1803191070212030800c00780f8480d480721101d8280801d031107188440307403c04041103468410069540190710340f420040a00e44030403c41034032941502c0e00b00035940020420302c010700d00c8440c1da2031708101c010700804207560900c60301580c0316002c0003461030b07480b40d14207604107035100b0350040459241020b0705141c0d0342d080400300700b20302100d00351003200003882c09208126090281003100c90126280c0010150 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 974133219 1250 974131969 974131973
    0xa02030c090403230412140705060a0c02100e10020102030121030c031409040e0601030521030c0702031e0d171504020c0304030204061214031c0b0d1707050f03040f03 73
    0x413901e8803218280c00c9820510000034001c1d41000e2550035244140240f1a0003480d60607890b14220b51604140c0c030481050003400801d42d80300020415180e011101881c0e581c00484003a6403100300c40400076040802410442c03c0540c05400071812142001d00315044000403000560100384c007940010700042da030051502c0401d1040c040070812100540401d8644200940000e0882d50072842060142e0003c000400c00d000e400c0c41000c4262840d034801c1c900020717001809181e1440028450941d0f0f00b0042084019900c2c10005203540704400c0840a8400aa01074056514541c10020200003204445600120120103040c02d0240600382c5040000540c1c13442000081d40000034400500c0c401400000056a190f00a03900107064134180c1000300342d0070381040448078181c005e8031941a0300800110381c8014001245004480c0d00b88000150f5611900002e448406100c0e00540018580c00081000428850003400480d2040d001c80d41c841703124440c01c60703d1b8040e900c2540707050902c848003000 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 974134469 1250 974133219 974133257
    0x120d060f0f1d060112021b1c110633060d2f0307030c02030717040f060c15050402041812031406030705120a12090303091d1b12090a02030c090403 64
    0x1150800400712a803a65500c00e0817142392400c030003210b0310145500d5004c590059082099103c04001040140469103000100003c1c8840034241c4120305040b49030070120681c44c0310203040c1c102c3c0001007903a9961440c3c080085c0107041810301c44014550a60040d6403013480e05203264850016810845045655100d13050340180801d41403002540420408000040c0314030901c1d40c0304a40300041a40c60724203000b800180703180540c100b60140013101a01c0c1d40400d0b09454080140840c143e070100309640c840c400314000d088110502d5018925041b00d81c3c041000c2c803800e030f1185d05c0a0303030780400c407002c44443d07411403000040d5961138041d00582400e00090401003202c13404010510221508004190755020002010142e1840010018071003031080550090540e001806030200400103089901600d541ea250040d240008480c0362904440d42d4901010a0f00c000000d04980b2a095240c41c250254560242c13000c2244030b40030302000301c80c1600d1b20b45005030007550980d036814a0310b82800e410740 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 974135719 1250 974134469 974134477
    0xa0203151c0209130611120a0b040f02130303180b0d0b0d121706060301031a1503010608060a0f0c0215070219050d140a02120d060f0f1d06011202 64
    0xc1c00c41c210789004080541c41d003450050051005201e4100c84c40e070301e801c2000c112204489a8404044100015064011541c0c0884c0d002900c1d120006041d81d9610001801000c604070b12501482c004181d000504030340060480449009881d00c00d8090740041400003260414010891002014031280388207590a50014040c6034015242c841100c03031980b10781c07055600c1c0c2851940000d2024014035074952a410300b05420100a444082c290350440c1c0c0c440b015140c1d9280741c0c40c120080c0000103400c000f0f1220040d005030320054020000d03545c40e2080143c40e48411106030445070b040c240d03c00040b824030b1064070313415201a40039000135400e0000202c40028003400301800c41c4613002200303141c404a02404c402c0607120710002c0c800341907612400703000382c0e11807950218000014410140c00a4020501110800741c40240599411040c8001c1004125a030400c0c40c01141c008030115180d40a1442d440076a04543c0b03001c1c0c54400382440c1041208000c40b40c00d40020545400800c2d0f0403201c2e0060 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 974136969 1250 974135719 974135749
    0x52419061d041509020d02040b04032315010303030b0f041a030708030702030712210e04050f06090705070201050f0301080d02161409040807020d20190e180708030d050a020315 77
    0x5d4a0165a0010100b031030300030380c02c162a4133259881ca002d21810340912422042480b2010700400c03a110744152284000500c8068241030302c448c980c0b1a1940c0e030b0444c500d40482d006008000001c2c51151816140b000d2482141c000c2c810440d000c1787c0c143e400001d03150380315030003401003103058100320b40880d00151410701126464100d26002000c42d9010105080700c900580c1d0785c0d480d1166400030001a070380003415154030031010209000089d01d4403201079038031400701d00f030407580c90005200403161442080010111f01001000104400c41d0100b80c500c006c1c0625400c0320199503102800b0000c80c6618800c3e249880c0ca0003155a2141c180030a403940d125000f40811414680c080e000703d401d05500350f038100ca49106101d95029030b030032000d18485004c041584c40301d0350100c14a042c1c05d84c1c5065030142c4420500e500000840380c500c2421044038a5079110300351205c0f20782c2c41c030003140d45c0c1e0042111282124181000291007250030300c266032140c14201c0b03100ca5074541c0c0c541442101e503a86012 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 974138219 1250 974136969 974136971
    0x303071101120e010207020a05061206040e120304120e060301214d0a05120102220f090c02030304111513030b0604052419061d041509020d 61
    0xa0061401083c8a80c1034584400000960359501034030422903c141d65401c294420101400740201040750b02e99a180d200100340e030b00042e0814031041c43e514000b0b003070300384070741d41da60002c10801000300c1d031140503a500045899130b501c40c0c5162001c205440c0024041c0903045003606100c0451490303c0d0f1640f01c501c034080c0503824002e0104070300129071a500b1190805034984862170400000e038640c0f03805441400c89610302c002100b00800003d074003203514031405100380700a500700b1101314400e40c11180100c1c01c92210360b042080091803001c070182e036845a0b2301402405100043e800b4902d0140000200169026505d10b40d150354074400c00d094209915600401c00c5100c085d2055902c0c002030000c024000f28055103940b0314030b00210080c40050481d40a0380c10031092069400d0030514502c3c540012202d81b42c000000000490b50021001d00d10101600c054000000c040d03400c20b01c540e41c00c0c6000040c8090341e41c0702da4280016960b0299003500120f003d003104000003d0280c0c050800c20010b900 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 974139469 1250 974138219 974138237
    0x7050a0b04030e120c010e04060605220504020403150b0d0b0106080709030503030703150f0605070b090a06050a0f0c0306031112031324020601050d080304050a06110904060b090303071101 82
    0x1155404c2d03c00246004654001140810550b0b0402c5141d280700700200c40c180091420244001d0a40c01403900b0541d01c6100381c40f0640501c1080308850b1b025110180c8110348507652818010005441781c000c04020038507040380000d080c01e045514a40f101d8100c1111542d80c1d18150f0100c481c0c0e940180700750100040c02d032012000600c24401507000302c0b11030ba400f18178043c05100401541083c1d070b00484401c204807004001c000d4108013a40e11440d080780a102032580c2d0805e5290415848104c0104080e14100c100101840d95500000102c8006e880c00c004021006000707404480c0d841c000549902d010483d40500c618280303240d07625500c81842602d05055044c40e40648140040c0c1141e804003180540c00e00600340d060980400320031091000300300301d503d020b0220706e01c4401c0c0300303000d050b0b030f64000005400d00c8400c001c06d00040340e20840c204903004406a4284103600301c03411a81c07080c0d0800c00700140c00101c0c4400d40b4440d1100a025516081da1070b65011007203860500b030b1605200102c2 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 974140719 1250 974139469 974139497
    0x20910200115151106070c0c03050a06090308010b1e300108160b071104141906080a230a02090702010204090f062103050418020c060c07050a0b0403 65
    0x700610000080b414030804000742051040c43d8a20321002d080b0041102804012400b8140055102d40084490500b03495184090501080d50181034001402902c54420140704100090344000d80c42406669804500c0e40c0700d61481040e4400c2d094050034084060120f004d075200c0300c000404201e080709684030750b4040c049030381131500b1040d001800941400c060041281c21001d1003d1001c101c2c0c011411070140f800d0448151160041d00d5020b03245625900c20000c95840e10350010b000c2e0381c4a10398901e400e10b040034140b030200c1d09007000e1410301420003500184141e0b002807400c0f206680700b1101582c2e2404084621110740c0001c0703d2240354465052150003580300c0c890400e001c0c4026500142c0d5946c1800c0c1040107940d03680301240c42551814204014841803401d2070b031805000c00055007042042820101c0e031a0059812003e46044400c90022100040d0790050000182b02e10564580d95030380e1301c030155603004440c00603000e608002d0074900000c4503008215403240c860705091031044844 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 974141969 1250 974140719 974140721
    0x41b080114041202010e0601210c0e1803040515160c0b1908040f140c0307080106060909050103021c030203040902030f220c140406080d09180209102001 67
    0x20303401d155444848941030006200354200b018941c41c690340000e0040c04581441070313540340310502c251074214180801c070121404031410034014031600841c0d94154a904c540c50ba12042c0b405070340a0800f03004403240a440c0c020080181d504403480101641085100716420a030f440d4406080d0a50010004600e4000074072941240805081c00d9680d554680e0451040750f81d200040030014818041c120301001700041d5080030020b0356a511260240c500280110150718112000318140d600d4042c1100c00300e00c11905603ca102115516075400081640d910b5800084070741c00c2c003001c0e4203c02001a84201c40b42d545e4030440c81c5610030b00c100c03451b00f542e070850303581240c00658270445c0545008003408070183c0c1060380c8070086022101c10806c8848184c4c3c621074480d8481c410704a000403030002145a5558641c0f00500408840081d50000d42424600520b6071101c1c0c05195003803003141040810b044058802c1d6049200c02070158203111440302c8081c2d41180360030441c00019102401901003070142 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 974143219 1250 974141969 974141981
    0x90301060b12060a0906150e0303070c06080610090b0f250b0a0f0c1205100b0d020a021c050d0b060906072609010206040209071124070306050306041b0801 68
    0x10400b041071400c0000801079800c0803980035002480c10120144807154620b12001c41269440c00c00d22202c0050f0030102e821401001005040c10f40603c0000910a4100c07450501c501c5c0101e468840f00020514241c0e08040c80340620002c2ca0400d10015111038417080083c81080c50800c80780740d0140c5044440c0703055510f000c10850b4400821420f014038546217001e80c0342030000141090019002d05507004180f56522005c48208503100d501061030248001e050001812003c62079645c0c40801d1748005000c0d40c800c010400c0148205860300a007a031440031080807125030b5999031403408454903120310141600c2c00e0710903401030b41080844421b966074001041c085200c0c0b080c2060000f5610600e00100b841101503504079442013180000c1a030f4049107841d8440e074100d80c1051503440d01641110300e441060554901d900c100e2500007050002e14079211411380c1001c1000c40260b0320890114190b403810722404c1c0d09035001902080002e4410040442840c04114010070625a1907031058256a5 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 974144469 1250 974143219 974143237
    0x307033f03090507060503040f0f06061203030207020a050109080601090e0118050a0b07082a0717041406040501050f0a18060507060501051801180b03030414032b05090301060b 77
    0xa50740d5642020000c092105000030021030031b045045181c151034030100d40000503002011114044042810450140e100b200909040381c03075a02c4911306403402500a500c020001d0780304030500d0000184540c803400d107005c02e40381c1100c080e28040c3d203030104440103031100c01c29080c1155215030759010168203801042903228003c1008180b08505410402907010024003036000304002c810400c0f03021407010b02207032801c541083d410005103100c40760091050240480080403011580100d0710103801000180055400e07500a01c50030148003020407500784142c3c40380e14085201071204035181400b9001404a4030747c182840b40552100c000258903840301e80d0400c1000c2080172680105108143c42924090071056803001c49800711540c00865000f014861042c90f0051440050854009600400384070740b0043e0441e612181c07590b244220554003598041e02901c20b61843c12212070f02e04a041080c00a908102c4200b03261541007203031941d201d0342a680d019901d0f40e800140828908006000a00c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 974145719 1250 974144469 974144471
    0x807081e0405040c1e3203090f07030317041e0b010f080604081909090207200306060123070c0306200408060c090a0302041d0c0307033f03 61
    0x90906007040300301c1d00f01d00c0c800e030200000100c805c108040451180009070b01141000300d880d612201c20f03018075850440240f4410050214650b040448844c0690b00441d420016125800200c2e00219138a0213140b00c05400140c086401031400c070420012180c0089c0139065400d000300407404a003215a804410849071254000010014043d40304c1e603000150604501a10080c142a128200319000e84060f100c16a03000c0154466401c1c0501c103990000d00416500b9501c440f1a407c040c401500c49040a002c400421880a4160724001c220780f03220f07000503141ca60426000c0d070340b01b18480091000e152040d841c100441e60120362124070701c2004502c1102c0100e468130718582c0d52101561410391604110400340801e1020f0400030400950141440d4001c503259521000018001006588080d4001d40352100100c2d00c24001c1515420f0101031000310f41b0804090410726654800034070001e84041808c0900c10b1140c40ea90040c041c080602400c1c001c00c40171441420005c211034090f000b4042 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 974146969 1250 974145719 974145727
    0x1d04241d010e1f05101502100b04050c0d091119080114060a0e09070306060602010207022b0308190203090a111009050904020411030106090f0510020a0807081e 70
    0x154030240555280300141c0c1e40940841444010003214a22185504640b81e43e03c40780007401546074203c0740703001454840c4420700040302012010303403207585115806200b0303030616082200320b05160103814018400300f8040c0e840c0007211203841b80205556003080701c800103905450281e07655100b01650002c1c4080c2c014412051400581a003111042150170340d50784000020400b0b50340d10024000e0885060781020510303651482e682c2420900c031508014411480c040c000324141d0350560240c40c109200740ca528104024140d5484400030000140100704031052642c50b002070b200301000e0307400903207403558620043e14800f2032a0683e04125541d0b51070b54066601402840494000c40450301003c0c0c070000d0b400b81102c1c40007407030002c00b4010b0070b0044150b0030110b0219101c690114284900503007480781c5030358490300000d000300200d2240440e1070304c41c1c64020441d4544291045041d1900390020100c80c1d0306541c7d8010b00f500502da05030340380d810510061410368804a00d01c015401c1c0f89183d00e0355 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 974148219 1250 974146969 974147021
    0x1e02010e030a090e0f060f09090a02030a030504081510061202070b010b0a09060e01050a0804050a0f0c080f0c0607110a150c02122103091f02040f1d0424 67
    0x400b05000b8014017155100300d00b4008203481d4103242c020030500c15520154513650300c06680c0d02d8044800c2c0029018840c00d54220709055100c0082d00c15112040241c41e80000c03d0503a2000f6884280c8a2150444000728100000d6008101110241c800c8040250070010036807640d5803c090300b44e20102c0c00c800300082802500d64041c40010281c41681000d00400c01c1300d0000078198001e4039003420a0240c481e0106051023001c0066444d01d951081040d0741100061a10140741203061003441082d20403804105140140401c5007108404080c000c641840702e2519200c15152040340b103d82c0103141c0103800309400040001d00b1f210350741682c9640c1e05400241c0306000c0c0140314204081c08a0f00500c4154103c02c50944c0311030350382060602c01075202c1c2c954445980c1001c40da065a1001e446400440f42031855964002d0001c80302803c50b2408210394943c82140b81081020095010441480029000404204440d90036401c5000ca0010084503918110101c86c2c0e1031782d4800d5002e40f00115042 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 974149469 1250 974148219 974148239
    0xf0910090609120504030305071b092412080711040e030d05040201080f06030a2006070302060103021507032c040908030f01091e0b0d02032b020105071e02010e030a09 73
    0x548075242d1314245280c1303031a544005145000c0d5180041c15444442c190075000c009228104024007507603901003200d544000352007001c0410054030345100d1001500001080c5c5c800412080312550000c0c5090302d000003656405031704929607251550b04c640d50b080413800c60f120400241c606108145000141814240009494400000c0424003d10420b00c104501504c01040280209901110b10080d05904101038607442e4018200e49801c04408545542407680c0010814100c80c025503000e5090302c2e2003a4036800c42d109400300580850601908403118a40c541c100e0524a0812112402241d070540001000d407001458103503020340d80482440038200c0c580900c180101011002002803c07281c9540c1c6144128603c401d0300ba550303581d580c40401b52201e0b070440580543c000d045e114030a00d0f0510000300c0a18078203803030001c1503003d410440040d00520509024180c1a117800b504080301c510845010300d4400d003d03408554035450b0450080c0740c104041c0c010000b26032901503500703044c100c03207032 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 974150719 1250 974149469 974149493
    0x3a080a05060306010f09020327010f061d1b1309020d0f0c092112030c080705181c170408011116062f0a170f0f0910090609 54
    0x910941140f4010483e48000307400060445e5411038000da00da40e600d1074280c0d1421282240c1c200400b9903003c00d101d0035030040d400700202c0c43c011708d0b04105907511200b100d03c1c1d4240301503d00030000549004103810382e03000c01000e03114425840d48070b031074040310403190320b21094590320943c182600410400e1300c4e07503128010f000381d006d03483e4010401c513806000014400381c03d5100741100c80e2429051030085450004003020304c560403c585910705031002500800903c10518400001518400840d100c60720441c1140e1405040c81d002000d5118810100030311106103800b5280451403401c910000101004c0301e03424900040b400b001e07169450a103805007514011a4074650400c020000744070154442600e00502a41002d4005848184d518070300703001c1244410582407503843c0780d13440c03d4a100682d0003400030050b80d5403248d685c10b08041c3c12980b590300564030040d1001d201d01c00643e90201c00002c151b407059000c0121001c42800805541c12600012000d95080c1e4660b80c038902030015611502d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 974151969 1250 974150719 974150731
    0x20c2503060b010804050d030b04020c0f16121214070b040302060105030601080115150e060f0a09140105160524041205030f01030f020f042901050c3a080a05 69
    0x204c0050b1800f50740d02c9403581c602c105458249617a4058071000c80e1220360541e008805844121481385107030700708070781e5660722260845002c540c00200109403000e000013520503072980100c92481411441c1c0c02552548034254a185149006101c24404991070344180f82c0924041c1c2c0240403030b5414003045c503003000c005800c007451a80c1004a110b11400401c3d030203104803236030482c80812101104000f200c2035101608902d0b88202c02058041060341074500800004000c0e07201d10407903c0d521481c04001c008180d4681c2d02050341841102d001070a5403500b00c00842c450760540e01907280004c1401c0c1d40c81c01031140c0d034141803a050104002c0290300400e90300441c0990401904600d0301210094094005000081100319080c0c03540045480790301c9420802c6600410900401800c034103692104620000b1789107050b02070b40740044155001e9000c960110304040301034031800001c01810180b41900c0e910010b80071482241034401007180040c0c541c4500a11780e01c0404504007010720b5000c0c0c907400317070503 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 974153219 1250 974151969 974151977
    0xe18010509210c16080d1d0103020304020d060606050d0e0712020d050a05150702010b1009091508060f06121527010507051309110904020c2503060b01 66
    0x788400d2540c0015000c1008070015441c42c60810080d0490340b450084010303e00992003040902c1801c80c564800540640300c01030115541c4031601c420440e07040d0011040301c0c0702d038140164101c5855200342c0003140e0040c0098401c100711991a62000c00700d4940d64170a0001030310114403441490001c0c0a0125840c0304440103203405414150307030324040c08612400038480c440707900055040000070f0210900d800c5d0400305032898415910040307600d0800881d50b0030019442c204400707209190410600c4000c0e003003a551481c2e500d08003058080108044460b0400b040548440014216420848507108030703000191b0590501b07050080c8848a2507028000c04a500a202404105281102c0c1c5680c030a480d441d40082c10704400442c441141c40c1501c194a85509040802c140306030000d0043c080401100b4a4404141e50b850030403045880c028204101c6c698104a948030620305038000e080200c030032505544010340503600040001c88800101882c03107000d4170f410004d202017441050000d6000b820 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 974154469 1250 974153219 974153221
    0xa0b0108010f0501080601020f0601030b1e10230301150303081e070318050d02071a04060c0f0804051816030902030a350304050606010906050a03240e180105 69
    0x30002c42c182020b4002c4504001042c0300145407a032007000001e00e5010b000c42514030550312400c000c4c0b0600011500803401c84100b04082e031111812892081c443c110383d4a40511850038603140303400022980c001d100001c443c024000640b81c1e030a1040702e10404014114480161840c60301500b032400003804590b00e0400c50110a11342c6403d00301c450f0b4070004910740000d000c0010491800d01d00b00f00c510280a51240ca42d00d40060b50700050100181e0b0303804004010300c14011085901c2600c5079015000c0021101e04078a000118250072244a05100e40520781c00d1948400c0460214005281c010841f82010414404a80388500300c52903513059610f8244400017a54000c00d03510100c0c9a801090095621400e0b8100c062600c41180b01840b1007548094040c5442d1484031640c0050740d05070340701d01940001c12007641c0141030b004110f03000b9856081c00c01c0712010041e0010b00c0302110021540944074958824461201c080002404110074280c90500300a0740c003060b402078860b140c02290789084 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 974155719 1250 974154469 974154479
    0x11701110715020403140606130b0d02060d1d06190b0609120a023601030b0103020603040c0906061d010e061b010b09040c0e13030c030e011b0b0a0b010801 68
    0x408440c0150b030400ca20941da5200c4202200091190341d001500849076044031158061000c2a99405150112000342c1c13420402481402140c1c50034243d258030030140940d50b0f0060508c14040d0440c40001c00c00002e0641c1c0307450041040c10784904a80784e5541040041002c0405201d440030b0180c20000b008009840c955004217410b0b22a03014481e01c58041c0205084035014101b000030761440e8064613040c0c05c03002c0b0704400c0d50b840070f03100041b009220724043c20741400c03008004403d0403281c104c07000c80303000c0e40303181c09000c110f5001130300540e002e4040790000b062086550044d28000c0c01319a81c0c61949901110503d84c00101000c41e085c10402003441a0581e40d46a03000e070340f0f000940c0e01820b03840ca061411a640141148140103400c02e00d04010402030040c3c0f043d489086856580d0303080c5440d5500020080f010940c3c0070001e0120f08094a5800441d01c0b40401c000380080c1070405103140003000d5503101f0294161403080b200c50007020304100b000142e0380141d42004c40c083c01c203009594148 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 974156969 1250 974155719 974155751
    0x90903050328060e060a0e060307060c0302070e13171207050906041215062108070606030b0a0912030b01050d0203100b030414070501110613080c030a08011701 70
    0x2038002c80c4081410444000c0c0c412800c004141d460354110b000300300e0309580d59180210b446084070360724490520002d000442e41391081d0300074807070715008010305015810840c1c152400e003d5141c050382188200d04012840c10004000c050007001144850409600585018002103038002c4544a00901c284484a094004546141d4200d00b69003401034407a01c0c00c001080e600e008a40c01082c040001c42003c1d02400403941401080400221041c040540c40b0450811820410451129150008a0079401086500000c0c000e650720560b0082011940c81c1c55403440b1060507a0300c60800c4d5641c1c00200100701c141081c4400c5644682001d03c1011341c29400a040c40c02815450048290004005680841d0000c00d5901500240040d241c42c2d0420781006502e03416544200d920600c11040d0208040d80207043c1d4540c200d050340001d254582c2c88440c05802280c4e0214101d5004201303000c3c505404c8002d0001d413040b540c190f07540e079500703601d440038200c811019a00400c0c000e9250030200285006d913 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 974158219 1250 974156969 974156971
    0x203032d190c060f020f070c050f1005090307170c0405010509101a0f07050d110c1507030c06230105120d0f111207110a0f05040915020a08100909030503 67
    0x300341042404030045041800140c03040d00070004c0c0303082c4002120104c8a9001000c0c01c19240103120025045448030180111041072424044d440310003a420000c1c1c0074031070320040c003140c2d6014042d649600e59a00d8107000c90926412090099005045000750a00b041c3c400c00d40103000c00c89070f042c22070401c5a0b54921a2010780180600001f00d0100701403042c0c280070403a5038030464900c1095840403d428020388505894500d0f40000e0305440c4400c104440014040c2c2280c40002c0c49400c8440c0e40b12000074166008850840c1480078042c0c10302c01183e01031080c0c0c1080111010340c11a6031031140c074000300801c4160405485002198046d1483c00c8002415204a41e0789040ca121001c450748019900c4810070a13440d045441680c1406009a00c1e0300e006d4180c01d4484c294101010306050104a190012400b4004031618000b0041001d4034141c4c000106c000e01543c02d1906a0360f000789200280da00c0481c4441c0821007280520070404504041c0400030001d000003000000032543c1d004210b448 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 974159469 1250 974158219 974158267
    0xb010906061b02130f0603021207080610180207030219060203160311031f03080c0307170702130b010e060c06040b0c0f0706050c04170f24010b0f070203032d 69
    0x20792410b1984003072180340c6c424005150010308820165006d41c4180f9915180d50007601c040e40100404268442c40d401c0c003031070503101002d03000004185104c451400039003111806030114850207001d40104541c07181c915419500800015070740c3d2601108006203242180903000c201440c041c03204100162040680c0c2d00000e045a100308080d4180d024207140c0280c0b80c04c0070740400e070002602034545000200500b41d852080454005919030800c4040320380c0240f11000c2c1d0132000c1c990a460540320141d20458074100141844020118101d02007a4240c11940e070b44541c5030710280910040c0801103840c0d0f54030400321842d4615046a08080705414003455500a09417900c41c0b0120301ca80e0102c0058801a003680140341220ba841c0c40500ca603250030038402c0c5200d6000b1008510a0607200702c01c0385010a010b420717009000c1e440d201060200e54080c0d007103520300d40740034005400165002d200502194204410f880c4822000c1c00210140c140c09900c2c00d40200d44c100101c4944c07180c0c0402ca04c4820b1 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 974160719 1250 974159469 974159471
    0x11a060d0f060e0f0a0f0603050d0f03021330030903080f072906011107180e120415030504120c030c0b070215010803040e220b010906061b0213 63
    0x100100c4420001d030409400c460500c50080c0304018001318410880c910402d188581401598111001c03041102c1d424080a459904142d2500d0100c90003100c81c0070007030340a0301e00140740604005103541c51940c942c0040b5042c0002c072072042120a1071103429444031495044c04402201030350b030054040320071440010204c00c4013151a84052140c0f100740c0d910180c100d448440c0300700c40754505c039441c126641184a0a825200081a00b03544a5101c12086004070b00041c4041c1d0300b4100c001d1040d104080000d902252500c0d090b0380003100038331026029403480141c082e1221300304101b40131100044007a030010146003e08000101d0400c481500d055549820718410045450400301d600c6000450080c08612261051010442e030010740f0035107c140040212a01c2d036200e9003400e8407403027680702c2c00e650702c2d0542c0c01040c40b520401304038403140c084440d10000f0f500900e1b070383c85d01c0c041402d038008042c603540d41008001c01ca803c003803402c0d16141c20301c1854031580025400510440d400c1103c0346601 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 974161969 1250 974160719 974160731
    0x601020a12020a1e1a0c0f0d060b0a0306150c2004231005180f090a050619060914190e0109060504060c080f010b0307090e1008011a060d 60
    0x1e402480621050b41e0007413040c1508144054100e50000c800c2d010845007802401142140245c620049030701848030400800d19103084c00720310124a0300001c0707580d68500d5484800140c001c0911000b014200c9a075140440c00501e054bc0311f99940c8908082c0d00d00348000c03c01860009800d001d0342083d50388000101c000302100c6540407074028135004c40c140101507241d450300c03900480d40c913a4140c46246220741504805881b4020f000c1007692600c2c00c41482d0110780086800320b510a603800d5889090300d01151510203003525950700d018000e942c036103622201c40500c2080c082c03030b6002d130b00c02400030010140501003210590078100400101000002c000405220320316512a422544201058800034011381459040080080209880807035500b854080c1e4010400e011b0078005228241c840145803030b40e8030b0b000f051300c96030340010481d0040100703e20012030308210302165a03000e4407900d07002450140c20881d4103401c40700d034801d0b841c0030003059111120741592104100e52040286000200328 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 974163219 1250 974161969 974162003
    0x304080904020a0e0a080d05040b0f120403050c2112150d110f010c020a03030e010c080307030516140406030b0a050306040807150510050904031116060212030601020a 73
    0x21030040100c02a0720a0000079554480c6502619075003880000700ca6046840303995240c0f059031248841009404903500f400100094114035002d0020b80520700f00305441c0a50035401c415001008940440c081000418400380701107040042404417500300940b24250107102c0500400c6000d030420005040400301c00184a0000200c40e20030f0003c400703001044010150719041d0000c00801c51014040c203084404550550b210314400400503401a29814030141161800c60744c1003800e0514506100d950b24601d40003540c0d9400462044000d80d400007510b05099100d601101d400382910403c010384c0c1c440d00151300d0112402c481c121013860500040740c40c05540440c0c50f840095110a03490b0180302d0400c01405540c0004100e014410b207000d89040008100c3c4200711801030b030f0141c01a640c1064188004e042c402031403a0428080d007044424007840c0c40800703180c040d05900520741c01050074400c115a5804000c911000b4080024075429460446c0000350703640c85850300900000c08423405440 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 974164469 1250 974163219 974163233
    0x2a060414120a0c06051e070f02062d090909010902030c2106010b040503070909110f18090123060d0308040827011407050d0e03120d050402011b0f080304 67
    0x102e8940c0c010f664440056490b040908545c0016003c030300d1182070550b5620071a02c162080720343d8035500c0030b400d0442071259000e010154102458020103241d1031400c454452624090f0003120b07d070310381d940ea50b1b60304140c41404118070f400303003245000da818443d010006903000b01d0f46019800e01541c0203c07403040241510450050342140c0c0c00a0f600415001141100780e14000f0025a00705400b1940c17069520364405040311030b10710024042c00303501a0480007614150000a240d07400083c40317040c400c00801c80c01c2840d40016110394615170b5555020384200c054100d02c80011042c0b00c03c0b0702d0f16918003c40440d2901862080c010100040003001908100707800c019a00075006014000b00200c002c0c405106100c1c20001050f0f01161800c0c013800641501c100c00c5520301907010002e41b02c0c2c580d03140c00503510381450414013503040c050010303050000011343c0c0c0902450303007141b540403800341080e00003d02105900c40300540e9000300d0110701004160902035000c1120ba01500065480e40c41d414424 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 974165719 1250 974164469 974164483
    0x1101020c0d11100813060c033c09150e030c150405100603110d0321020304020405090606011704020d0b07020c0a08060105011b060209032a06041412 65
    0xe070710421440d2540c0501c2000368522040060544692089041e10041a140e0070360807158003101d030b0360b0001264002901d50300718654809940c01c1c013103030101040c2850340541441054100440b0750744003940010490340005100c0302c88515070701308070f6404103491b0118020074500b02001c143c1e1f01c60501c6004010100100c030808124001a80c0d5106500c0384036516004064600f503403a44124031080050103050322035201120b40c000c0181d0800e0001c0e00500a41c141814000c0c0d0911008204882035140e40d0303c200b0070180c55680e4010394a00d02403040108503440544922030a5018504000710340e40c004500c0e13403103901840002c842550300d0340f001a080508003031005103074288003c288031030141c0004400443e03500c100d40c200026510b41c85070542c1d0300000d04c10f450000e8605520241c510031070403843c0c158540254000340c034195100307020074981076000e1036805071250b0b40103200e9810402d03184506a01e1004841d59850585003240b80704040e0080700d0500e118154240212035144001c000c14 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 974166969 1250 974165719 974165743
    0xb0708100f140d0f0f14012915030106020706021b03121606020406050720030d1101020c03030108031b12030106111f02180111060708040311190201030605010305040c03110102 77
    0x201480c100c1d6843c00729900700c1c070721030210f034200481b6403910341c540b0041c00307804101c8100450302655100385c11503032040c05203135103a03041e080703031000700000501c4104c03a00440c044d150a800802d411450410000e02d403050f4104c002a106600030409c0703120795408a000140881d000b049251030351441030868014000344074000340614800500040c005400c440540b20441c020b440300341d491001e909440181e4085240c95a90507084180f001001da130040c829140841111000141400c1090005920350f070300a030044052580040f400e01124641e100340e000c511012080508104102e101c150b0001e4007041c0102300600c40d00d43c1c0c80c0c0061110821082c028280c581d2440c5805550060741c01d002940034081c45020984210380801d00c40d40610284c045460b801002000e55580d00354040301c603240060800c404102d5041100e01030b80300b04200000c6030240c2c0030885180e40d1018170025040b2886a8002c50505040600304000b040c4110074001c2120f421a001b80c0b4145212030040341060b000e881d00e = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 974168219 1250 974166969 974166983
    0x60c0513030b010e0f090c041d061302121b040f0207020904120e0415050402030901060f0f1d060f0d08090a0e0a0b0904080703111203040b0708100f140d 67
    0x10000c288808009103a0480d40c0c18400c8005944a100030b0f6800d00c441206c0c00fa040c0d0303100801c5e1685c0c9003059031000034038180200643e1046a9010031081c288032050b81c40740160801e0b214200706506d000404054100c8a01c001008032035101c151244d206070112031054420f0799501d80c0d000d810071040c0c048541d40340d8014141c0555250038a860b060440c07158046d1000694036008407502c2e420140310f030b6220041c01e985045c2c0c4403480c001c04c11010b5400103180000d155200c401c005446050160590007034480b140d09910118105920050300c54a040b4130703540c043d41c0c92024001d0b207403248a00140403d409491400d801000c5040c2207086200e20380951b90404101103000a0956860750300500a012141081c00740ba450403003002143c1409842c0500b505c07504005180000740941503000790103a5490540d0110301c110f40c42440c680c2c000f15400d44084a484042100701c0e540b0019255002c000815048841c500300079100521507420702030103020075420124241c00f6622503140225403548410 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 974169469 1250 974168219 974168257
    0x90e0f2e1b03110f041e03020406080a03020105090303070912020102070b0426060f06011b0203030712030f05040804061101060e01030503070b0903040617060607050109050d0212030402060403060c05 87
    0x100e00c0e208400307074003a100001d250003000d42004035070100b01e610b034120022005041c00e0404442e001200074054502c510407103003400010050721103000340c800070400031001c1e2410742c0e02810040e0030b44d1001424040140c00c2041000071464028010748140c0d4003a0418041c42c10b560310041c0e1a01449030041e840e6142c001c5400221001d1402c01d0315200c4100c0445241c1690b40750141d180c0e01c10043d2200f01e6180c40d10790014070654410440c50500680c0d01c1c03540715240d2400e03000310342198480d02042d2204903886200d404040d0309030180038001141c0280070031061400f500c501143d4003450282004000001504041740b8809401980141010300c103e00c0c04e0356507030f02d0025925403208004441d00c80d44180040d080c100080b05403030483d06181c940c1c00b030b0741c0308800c07a500e46004004c0c09244d0016042c07203c600442c2091103034030b0140303108a0040c6024108664080e103050596001755001071000c01c10440182c403014181c408a0350711160104240298400940e4640030b505040c03034003103c24034 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 974170719 1250 974169469 974169491
    0xe0c070209250801030b07050703170106020303101409160507140a0606060809030f1c051f0506040b120406140c0a1205010303052209060b04090e0f2e 66
    0x1501010b1a00c0901501c00400400d045040d9940802440003400c40c6000c01c002131348046c0100c0040040b24170902c1d0450922800c268100c011f43e200f81c2100c130050380084108002c903058441002c2c00340c61800f5620091100880000703513840c2d00101f6100c085207400c0c8840525500803002e582ca4950300114000d19415a5050942e8808200e00c0568402c0e0a01c10002072150007007103658018034025000d1440d000d14002c4e0044c040c0d000b0415003158040c1005807003004a10340c42024042c4159070640550003a410028119801481d00150300c84c110410080040301c68440c101d071305030383c18100e9001240e9107904040780100714002d0a01d0b040d003410700400058440880040848035040d8644000c05031100280320100c40d404d000050110354100158082e0601f5102c0300324080c400341d42c4003030318140c4503100384042d0344082d804010f02c1240407030240312400c0103009008154400800800702450b0b004241036507050040b113145503001d01c090f10100e100350b40101c8030110502a9406208000c001 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 974171969 1250 974170719 974170741
    0x906020d0609141e13080d0204061806020118030c0c0518041b0b040302010302031005130204050f0d020609060a030204090c0c02101103180a03060e0726070e0c070209 73
    0x30701d6044030105800000a41041041000d0502100c54000000300e00d44c0c405c407000d103445c101083c1c182c1e484401400130102c2c6c0300c081d0008001400555665980c0c0122210a800341c0f100e07140c000e1020369040034484007035406600c3c259201c1e80d4152515004881d110b083c500580d0f14035410141e003110300a1200b4041d115140701e05405140b160040f0102c1000c40006203c5a000c030740540568280c080000f04051740c03203500596000300d45940103480003903a0b00001120100600c42d06003045401080030801450900c6c0203400c8a01c06949000c4501020f50010754107110307464a8034801e000c04142c5101080c070075030503540a016915030801c008901c13218050450040715100700e00c6841203000d000c01d000d22809580c4030801c07445000751700f8a4010080c81921a21401600781c004a10f0840000400c00d14050040d040e10400064112607080c5014110700130000c2e0825136207144440140491040001440c1003162803040e890a03684d00e41021041e442c0c07140040c003941c0040e1100501c9060610 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 974173219 1250 974171969 974171981
    0x11104030308010b04030305030a0905030c0109050d1403090726070b07061a21011104170105070507030905060304032d09080a08040314031b0f0d05040302030604060906020d0609 78
    0x35100c850582c4e9035006955018071a0340001070020b203050001c10701003441504600d034020f01c5501568206031032840b0803402c40f010f01d203040c1e4030365020798000505a50090782990150500d40c0e690b43c0fa5240c51407125540e40340314451018460224010700040d19040000140305ca0039050644003020f030341d400f405417160404030040e940b003071608241000c00e00c0d96038101000840098025403c102c210b000c811002000244142d03895522010040e062031410002000035280a042560110042010081c21620000e00110070b12174104200030104e074000107100b003103a0048902541c1ca40d51482e048902540d03070044800a00450409148911001c5001e540e140001d075542c00103050b91240d0182d50703800411009000d42500300070900104040c8050511131046c80800c59151100d011000c1d8070741003486844c00c00e02d4001d4045040502c8041c400c08002515925005052504640020703803540406400109030fa541d4100c002d0070002e0700d40580346804120001003040e160390f90048009014 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 974174469 1250 974173219 974173223
    0xa050d0606110c040e0c031e010e070806040b190f020a03150609090906023f19050912130509100e1801151202010e0109180b06070501110403 62
    0x810100c0104425104000100c0d050007030000504015400909010082c00c004140410301d002e40c14804036252000c115a0050050040c81c800c500303106007a0150846200070002c2120740c00c8103604000d04c9100151440d0001d8103c15012010348451401d0f82140c1046050300c00310900f88080d460440c226503016088201d1540c0b4140036041207076840c15000042c9004100210341080410302130300d9896400200700512501c00145031000d03c1d00c404201103126510081007111109018064080700c0258a030b8201601c00c0b0280c1500b0a091061203008840220700e48203684c410008810640030084584030410f81540c032030313a03282698070081c201c0109005e01c6010310110f002150301c1da140300c10948100e030341d02c0d182c02c10951903008070300c0030081080402000964850340c20b0858002000801d50040640d050855420b08051001410314502d07403640398180718000030100900b581e007000c50040d5541e90940080c10740c0610700052441d015000002d4403d40c030b4958030702103650b00d030001001a24 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 974175719 1250 974174469 974174471
    0x1710090809182820130e0402130b0d020a0609080c0a141009030b0a050106110105160819060f08010b030a03140f0f03090105041b030f1211030a050d 65
    0x1420700341039022451040d10294840d4054581d1214101c1c80044000010003c03a207000c241c0c80480402c1e1955100c03182603104001ca000030b807114000c02c41ca9051001425004400030702d07498690002031403007404000c0191a1901c03144c000300f0310354502c42c080314280d074010442c5c0308a545401009003a84403601490030b003403040d1240346189181c0781c01c49504a4200110741820f42880c00c0501803400b031407810070002e221505901100180103944032520460580c540040c2e550324082c030003007001246100f00c4a0f1645460b080c001007502c0300303800012083e040d007030941c101c0d129040c00900c0318007107841f54030f0b0083c9000f00104400c2c01030310034130044942c1d007802031200442030010175460781c3e41c1100060215040c1c050110b4104220405040084001d4a26a00304140003011142c540d104640c6400107955aa0030070003008601ea229000032a0107010b690141030648c0e503400540c4105403009032204c901c10168403079241c07154083c400100c1840040c2e03610340f0030149000d0010780007021145262 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 974176969 1250 974175719 974175739
    0x204060801050f06121b0d030504170307380c0c100b0f061201230d0302030705062d04140a0b070f020a15021602040507050403060f151710090809 64
    0x5c004002040b4201014030260500603005080410106180a0404405001050000146203070240450703d901084400103190340c1d0165240200b8000c0c41407000202c07415021510352000c00c2056010203100048001105160301c58002c001d1700c60045500b0728105124000140c041411035401c200c920b404c0c19581201803207682c40820500340111410010007040c044010031003007042c5c406d202802d941c0c185001c8480000d05c80071455249090000343c1c0982e1002400b00d003001010009298000b4140498010007100e0003030100703445003154801901c0751451008102408454110b480027032519404548440049240114159a08440c03d50100380c440000301e2100e4008074546490580c00600020228510f81d1184025000840b1903019104036009601c0140c44138032810b80103031072301e03202c69032160301d1032401d102034a03d5083d03c10140780c24115442c201001752100c0c9000e8502d00c0000c00203070074030501000e182c1400ca0107004101c1e81460380d00c0c1d0500c50804010060414213440349180 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 974178219 1250 974176969 974176999
    0x902041e060503040818060a05030f250e0a1211100807050909191103060a0b0c0c040b19030c03030e030303100b0c030f0f0a18060f0c0204060801050f06 67
    0x948440c0e10841020420810024000136580001002c500c4810521001c03444c80c030901044482e00310703100110101e103002060049000c101d03140f507903002d4490b001c21214500000ca071040340d08048140783e814003a0700041c000c031a542e5120300380c01404503105400071014003418007500050b585840a4054000036a00d049054415210b442c800c0b1400d4881c02d2414880c0c0c001e01060b603600411000d511440390311174090070030590042240080b9201c803103a4403030611400700404505207910074815003400300500e0925450103c1c110515800072100002d0940290f40400c4149407101110026004680404000c021590070f02000b568043e544500c7d008501400303040da20721050703c1810501840790402c104c00a442001000c0d044410030079641864800403600c202a0011a02d2840110010a02492a60b80300280e074039640c403200b01c642c41170362400030041e10f449a000d8014003008170742821001503407200c1c0c020400034040035000304400d14100320f0034520303600243d800c2c600c50004070b012050 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 974179469 1250 974178219 974178269
    0xa060203040b0f03040204140703050703061715070315030b010602010b181503010e07120b090109030f0f0e09040f1b0501020304050915040509060406060609060f030e010e0304090204 80
    0x2007654003928141c3e280469400a00079150001402240c0c06074a0306110760f14409001c1a0500034921518085032074104001f025041c0c551542080c01301010803000c100c0e840b140043c6110600a1501084100317480701030048000d0003c02041140c00f58100c00004200856203040504941c0e082e4005c10186040000300b0040583c1d41040c0140c1006c500045034000d1946d09650300100d80c02400007400148903d01d003420720081c2d0703000c80507404100281c1014401005845503104113888000c00c009181960090442c00001c1c5800d41000524981d1600d007901072400340701d030490001e000148902d400d1810709461042c050040310060700b140620403907803404150384820754005030040c50405040c10180295584003d000c0b443d945110329190074161220710406000310742c4600038000b83e10382400c1c440103841c6a50301140400c0303c98113041068544c0702c000d03004a02d140780b8021840c410f40301d03e214094010805c250304130f030000141c00195012903500820032117200c0d1344a24040d1010035a062 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 974180719 1250 974179469 974179477
    0x6080106050619120e0307140d02030a0c0f05100507021b090610091a03010303020d1121120a020a1101020306130e0a080d0b330c0304050613050a060203 67
    0x160300b04030103001c8241e460941104440c40366220346003889030300b8820601c3c4003d0b035044035501001030700b0008451060045075011031f031920089a0007001900003e5074020360b20b1162440480401551040700030800a0081880040e41c0c0c022080394040c2c100f4003e4180144401d440000c090b10030922180c104201c2d850500f05c440e031000b0400050b56841d0414040340d00f03604420181004502e19020602030018904d40819a151003e0281ca0390304600d4041c0c60002120032201c240820303c107280140020025240015611402004420040c1c0e5180300c54140a42448040201040f00c20000051741d030f90b0150031212040d5440182008480c03d00714200d10045d01d906820101c0b0318800003078108903030805042880060704480030542540c44003e4160044c0078540c202c40d4451001e514249000502d1a40b2134034001082520303001103080c00e03040e91050307050110304400080340c040070005080c0300b500d00038180070302440d640b01002074001c1521605070040f0b912811441c180441c0051001041e1 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 974181969 1250 974180719 974180729
    0x905010f1b0906120e0102040b040806060109080304090902060906282f030c0304060e150a05030f0619081f02030c0301180209102303071b0c030b04050d0306080106 72
    0x1100c00c2c24420111130780c2201c00040384c000b54480e0300014005000b4030080008004244495032202d040500d8941003d031301410f118104031118034140700c8210003108450842c1d0200000062091041c80462400d010b000e8046511043c0403c001d24044110707901403006400c0e000b0038102e8017400341c0085c1e0325240c18001c01c0500b5040700604c200490390b1841380203240303102074040b00d0818215105c554659401a000040025206426040d4500740803056411101109010710f0030940400303c028240c0c0801815440c500d208100400e6040e292050714959502c1656011401580c45c0c509540daa00e00c1d071446001441202c45801c07840340524030a0328066048490501c1c607692a1210701c0381c42e4500010352942c010340c01c10000401c0c1d5138106924600e810746448a14610107140c8103d0001c032046002d00440d00c4c410004c11440d2503100101e9203200441441c40d10380c440d42d9041450f4111a10340008010041d11005d01c028803100066003010404903540c1800619154500903007039480381d00c14 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 974183219 1250 974181969 974181977
    0x10621050105181e07090606050d1104140105090f090a0e06060d0c0b0a0216140102010b10050901050d090503040915081b0105030c0c060103060c18051305040c03060905010f1b 77
    0x213000c5500340481d0210f540e0351490001c4a00d86030f1a004031004803402c41e4020710110b40c00040301c0c02030300302902817a441c0d00e41d02d40020f414a0320b000d420149031104400f0660400c00000340d4840c1559a0729942c0c0c6400d0800380c400c1d0a40d10308030140708000e1140e803440301c000c0c1c460500020342c2450250710000a040d401040c0f0140c0500e8070018240681103c4020000d501511070f10307800c00160454103000420440560412040d0070000290071581d2080d980350080159014011100b40c1140880b81d020400780b07000b541e5403581d2801038004001040e4000c00304d020000d80024004801e801030200910031481143d040c681e41c0b2456547c4400d003c0b00881009103181100708150300074000f965114034640652032401a4070415982002c801340c2040b60215611250080c069602440625140c00b660190800560074040051480c040c0c0c44104ca00d0140c42d034002a04000c1507026074030003164407003000d0001501c10301c1e01c01e0191032600d0500f0300d800d1910f40d4070020040c107100302d000a14481d840b = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 974184469 1250 974183219 974183233
    0x910060b12070512040f1a07140306060702030106080102091207060801140a26120a1b0302013e04050906040f0e0304061206170316020301062105010518 67
    0x10020201c0c0c0740041888003482414001c019206803003008441c400c0344070703250034518015140740004000d20452514020b41c07240c1c80400c10095001b0507580102d8034101d030341c039860f90303201000200c180c800c100b4000d401d5420b282d4001688001500644410a0120742c0d8410741083c00f40400c0d5154501c1c81124001100d2100400004040b00401e007425440a803801c608551501e5005040080c400508032041c2d0f8a05910001941d003030104800c98181c3c04c440030b15041840a00800f10074502001c1c1c4c243c40c0c010703c1002c0803d4000d40c0001c0c101a24009120071010007042900e18010309641c10f000c004a00347d544054040030700d01146d064410040c100c503e44d8880c8000d000c001e014001d07081b100a65a11000b804c01c407410401341004048650782c07240c00380240341c12003003a20005e502c0000c82a070649195689203602109981201e408980110603410b200c0c00003d02400c0325500c803680100d45401c5140c52801500343d803c56803070242c0005e000301c0d01c0f01003030061030120040d802200c94200038 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 974185719 1250 974184469 974184487
    0x1401051b030c090a23010e06091005090402120f15030a080a111005090f07090b01081b090a1508070c022d040515031b010815130905060910060b 63
    0x2602a101c2450f001d030000c20619140c010400c09900440440e4446859a8208010660b4024900d0440500c1500c49a05001d450808565030700d80c40000b010a00c880401c018009442d10360517601c103121b8166040c03203141440e400074a140181540c680001100320701004500c0d040018140340f01ca684500428030384540040112192491620000a54040e0b03524002000e0903501030386004080c3d8002070514171a55458040c50141103038030050196040066601e0b190fa00207551517401006180c034406c245c8481002e9402501c1134070321696010440343d0010400b21100300300401440844c3e111810380c1d03201e101c02540c1700001450b00950103440e0100b01d014084640224240c541e46c860303100e10022164100180696604591100c0b41c404005080c1d001450100682c0594168480e010702c20100c01c1000207000707000080a8804022016080ca079807525000741d8400440041c00c000c011042c010300c0c046440b45003c0c0c44d05c1c03031031748101400040444e5561003a1000c5440500300b09182518003 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 974186969 1250 974185719 974185741
    0x608181906020909010305010510140607020418061406090906060d02010f11031c0b0a08100507110a05010e07080102090109030209040f02060c0307060c0c120e0316031401051b03 78
    0x41241101c180ba000d10500e40726866401109010703620480000c00e503498210010030045180e580000b840ca00d04074540b8086480e91001c8848003601500d020500c02c0c1fa50800700c80030380030b00e01d00034050303482c2c40d15402d4110054107080e40907000848041030907888015042d6641d01c0140d40c480c2c1d206403071181d000015030141a40d109001002d007403d02250b2001414075003960009101c0e1460084a4086040040c043c1d100303030b0440c1314080300c034124002e00b80100103036244030712040c2a895541d24800b08050300e0082c0e80c240c0d00d03945e842003199200d02803858418040c08055050494600c212800030900e1401030003503c0c040001a504d000c4614510740030030411640c0a80f041d0380d2402c1803035501c00580c8880c00204140ca0318a0f0003996a0082880e00c282216400c24240003040420103c00d80000e00150310285040600d141c8080c000613004006401e04441007810f0500e40b041d82d000204104040000806e00007820008001c1a44c404c000c000443c5003004801c0355103042000042e10340c4c1c1035 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 974188219 1250 974186969 974187013
    0x20c010306053d020303090c030f150415020301031b060f020c041109120307030f1b060e0f1c08060603060306071202090402130315060302130c14070309060818 70
    0x9000c4442c1041d98444442a480c1d03c4424a01401a0000001c001c2c2d4040100300038024880254001c00203803a40c1900341c0d403907030301580018284070389040c003180612444400c000c6a803206004215602d50796450510820040d2001a291b23002d0241e80c0058900e00400b2049004641d070b8000e003400c01e14075010000104116050440d2868090101d004241c540700b100c0306038032880030000c503510502410702500600c6922040c23800c10031362180405038910345022110700154069000300d000b04c01038902c81e0600c4c01e0350044a125100d26404144c114260800c10800b96650f80c5440540362071744000c1c400f513480104c1d111034059000c0000b040e805445080444612804141d0050410079901d001600703a03808926003410780c03a080201813061100e003044444101c00c4001c410010245540d0120f104c220207541c0e165060340c1c0d5800c10880943c09800031180502c0915182c5944c0ca0170740c5805080d0703a44034001ca0002594810001c4c01d00e0441001c2410400d440c1c1d0000c1101a55964503030b0f94000c0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 974189469 1250 974188219 974188279
    0xb0d1d150106111c0c0302280f0519030801260309010f1407050109120816030507030f3204031e050705030310081603020114031f06050a020c01030605 66
    0x1c1111002c2d00304404c03003032040d28811103e60710750a2104090a00074a4411742c0c5241e042170b40348544000c80c40b03510100d00c40a86c80d500803004001b421550a1103820820400e003c0300090b4051841c1c1010150711100340c034144c418600059a109591440140c1390036810600d0002550041004210643c050381440c86028414a4032003090154880b98601340c3d0805901200c03580e45550084041241050844408004e0ba1600003080e11b4851020030140780d081c840c0d8414137645a0110b1001880b82d04041e0000b90800c030144011600a00d5411240111840d804c0d11066003190507404c4880c07a04415008035090764500c1c0100f220307a803000510061421800043c030108114400011324203001a41c82000d1040c60081d00d6840c0924040c200304440d04c8210108442003020700050b0b810842e00e001010511095540f0fa640d00302c080009845000701a514601981d40300061040c0d12200070b07c0494895405e42d481400604015410303100ca60180302d074050f00140d6441041d11503441c0c0707080d035a0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 974190719 1250 974189469 974189473
    0x160204060b161716050f01050714030417160c0e010b0715050c27030705030304050d0b150415080c06040509040201030e1e0c03062a0c0102040b0d1d15010611 69
    0xc002c000c00c0184c88014078400312855000144000c5004000307109182d071104040c02c2803110303140202800e0703446100c020701c0202550402d2482d4607241090409580400e1a09000798060401500b040300010006201d50511500401e0004c108040000160340d0030b9948440d140800c04001c0b450703100501801802c1c0444100f080c0640708002008464180c02126603107070602c1d201501005160601100d03402890080c1e02c200030400c9983c8881c4541e08404c2e404c1000414103450710f0344180c0c1d60b040b42c5014558481e080044003a28085200340050450340603408660f80524804107010a901132407103842d6100c40c2c00317000140954080e8000c02511b0100d6000d440f201a10048440482580540030741140e0703011038200c40c2507080030455142c02c4a650b01003030f0000d02c8070300813445004403c4e44042c00b42c0c83c00071a841010380400d40607180503020004070151690035600b002001050320400007400b004040c0140e0f1005d81010450f0100010701e4140d01c00d1070703801d1030b90649007020342100d2a40b0b0745c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 974191969 1250 974190719 974190727
    0x201050706090b07030902211c1b0615081b040906021e0c01060e0c16030c06060b03071b15021c020f030a1422080d02160204060b1617 59
    0xd09100c1d9400d00c62410b68500089986c0c0c280140185401061140c856655550b500d802e000d1200241b2100c10b1206080710884e132181c40401115403c0070020000d00203401d00d10448100301140c2c00c21507420700d444ac5e0109003595100a11940d92960320a00502c0525851103640d440c105508a00c100034001c0e14054500050701103201301030040114180300d00300303011403110407082d002c0c0940030081103600300060301410320500104440c0701d00c10b940b54060545071a050101802281000882030700404100a22983c071042e00000340e004880c03a500184110101c400c42c060f20b881494206500b0196600c151604014030348025403100b8800c140e80100c034000a40381c03602138002000b070040c140124a0b2641031a05112003501c903880341b441058010702c8200220039a02002040d801c54803a451130340c0c4000b1a0520007002d03c01c150348440c04900000352603442e0040115140002482030303508208603955a940203e0328010707040892000110b844c0c40700085103141042c0b813a1800000161450 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 974193219 1250 974191969 974191973
    0x6131d0613260f071208010b070309090b0109081002071e050a03081906090209040c05040503100c0507320111160804090c020a172113050706200c0d020105070609 71
    0x82504640002c0719040350014140745d9595000b4440c41c01010032007001402c250003130f50081c1840c41c0d1809407104a540e2150321031038aa1003242d012008141c0360094a03120405071000c2c2c8040e40c01300205503001304000c143e5030742c296814131554601942110160018108a41d000c40c1c40743e0000d00901c58450b015200080600518071449004140b460341c0103035207811542c14402030701c0110700b0741814030805000c1001103880109520034100e080300b000181d40c0808501c1900d6030b00a003800944001c1c0404964207191805804401d03102080d0303800d082003200039441740d50984003c1074250100710004d01c088330300c2c1142d10810461503441a045a41490340325080601181c21445a40300180d20601d5410180309809080d00004140c04003c00e18003141066500c4850150045200348190ac01d000501c102d0b004e2080300e080b07990712034107460040790740d00c4000300750032400d111601c041c850650410103201d00c0040c40042c12440076102c04003d42168005480700d4201c014241c3d40700d0b440c3e5080c200 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 974194469 1250 974193219 974193247
    0x70209130b07170c040321090e0a060810050606041401020a0206121614090f0105121518010f0b030c0c01020406021b0d03020a0b06131d061326 63
    0x1100b05078558600d2030b501014054650030520140c240040d0290400042c00421007074004038501244d00f080d16040d4607841442110f0b4540c5592240c0c01d105540b0781449200501601f29108480c0781d502140c5401d140704c0360b46000c4071016074007544c1c004c0d070804c410071080c200000c90941e08a0140180c0d034440c03403da0080f4080b0362003a807038078800d54080f07000c00c2903010f0440000282034400b440c107915240c0154071510079900c070b20b840711807149003c1c0c1c84811480e841501182d065035091081c0c209e0600380a81070030b4003080ca103c4281d1080481c401c0c011600a0030445c02c904a822110415440d04c1c039103000500f03958005402e118001c102040740c56424030b8240020001070805500510141c40440e10403840362009180a034880e12a01010b207000c071b50300041950701d280c2c0003603459815031600000191810018102d1981d030314280084030602c10381103074410000000382010740c0d5071552400403203c120080c0303c40091080601c07040c0302c112490b90440407190f018607200344074546950500450 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 974195719 1250 974194469 974194471
    0x212011a0d020f0a080c0307090b03270a02130902030a0807020f030d3507320706050f160e0406030c0e06040615020705040e010b090117160506070209130b 68
    0x41440e0f400080070341d0034030384c4605000d0388500701c00c4c0d8031030031406d122400400c240041e00c00c0c2c0444560100219540b052140e01000030f0b04002210080c10020346070005480302c22000e402d91051364003100c4010081994050588800d50007006040a22166a180c12294208540a0743c100ca260702d00a1101e840800c060818a4a00c1e101d40f00c60440329051414101d144156150500751440700c0c0d4064060540c4502d45c0200710340c01c0003400521142124240300f080102c005500d40c030b14200301084003654500030700321a2b00441c0c06200658803040d640700e4548096811001e0242c4403112010040c0c42444040c011079030050010404554980312501c16080700e80000c400c417100c0c1c07828401c09140902c1039070010a0300340c5100220881681010b900d071400c81c41440c0c062034488018220200c82035006079444a0300030010285540c4415030b50b03405142903c0a0001440381d91625411182d414481ca41102d9006104500e0500c0c1a0309001507018043c180c10007000101500b00c0000e00c44038501 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 974196969 1250 974195719 974195737
    0x209040617061501050a0804021519020f0102040803040509101d06030c030f48030f0a0b181e0d020c040504080409020319020309100c030212011a0d02 66
    0x8004628800a500d061031000b82940d43c00e200c462a4103885642c20100381c580c2c02111781040840c955903400480d6a46503140e00d0b000704c80f040001c0200712a0b00e001c0d00b90a0340d900541c00c0b2a0b1079030110954600b02d11441c0554466540180010480362900b880e220b5440310b10044000300e0155116849038486038480d000c4440c010100d000c00c6580c0c101080742d081c2c02c0000f00c000f41b68401244d444503880701031800103541207810000c3c601c1c101d1403d102c002828802031a212075600c3c005491401e0300200344844240c800c4c00780703200b0302c0c0d014040081c8a40256800c03d007110350341e0300c1f0126130318400c900710100c20045029103040031020b010b90809801a030340440000c0c0042d40b4142200904248141c14141e1140f882e110510003c2100081a20280c2c1c1c202c00005035640c480d2481200a28544041080503030b00001c100040500c0104541e0158a0b80e41d00622100d071101100780c003a03005602d0403100451030040100304151402c1d00d10701401203240f1080d03203885118264401070340c0c00f2401d1 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 974198219 1250 974196969 974196989
    0xc0a301b06110712031a0613170f030d090507050a0b162307060305010f06080c0306030c210106090c081504020913020c070801020c1b1908010c0305060f010c03050d02090406 76
    0xc2d402c000b00c080e618410b646c4d00031141c0600c0c180320840407108280c040d01814140764460b400400404004000d03c3c001d000e80003044a40f58070b00498800c1c050041c2c20411600d5009840c000100c074201000400140e41c042d603025420a1b204c1c5400400c51104001d080d10050401d070200414a0080c02d00245440c200300c000d4980107080802c0503080e190107074001303ca90149104204a0184d10071074881e01f011155046a03620b49a04000138581800d41c02c6855000d400e80160f0034500c111001e0300ea0691004200074021a40d03210842c1e41101e5800c2c1c11034000c0340743d40000860201c0d07130104520314808010f2005080c4161900818405040000c01125490380051401c2c03c05500300140b034020b15420009500e8040021031054450000740100800800b074140d82c5503041d03580c41e052055000c42a4201803004c0c1d03031249854064a42c5921003404a86050702040550504090300c45688806031103054800d00701d6642144c1c02da2100002001082d42884840f07601d80c6e49014890007401c005907 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 974199469 1250 974198219 974198231
    0x30a0b0c0403080f0d1113030807080d15080f0a0f0f0c1802070201020c0d05070b0706110d020711010305091e03042c09031606020c0a301b0611071203 66
    0xa84004441d00361b40c1d9580e104c0f000f44034031000820411000029030358042003150f212002031518041c0c0c2d000d1900082001030070f04c5401d232040411070344020100c8034070004503194035084440040c0c4a860000c0b0140210419002c0140401d04a83d00304245610505808070507a40c0c0b044c000707060101c800700745030480c0d030005079100075980e0412020002043c2202e09040f004d0850751120340d00c0f65641309640c01d0710408160130341400a580c0c042032070700000c03004090355810311205410082d40240811a0000c01e90040e1a130194424030500303201b00c3c81c2000034400c0c1c2c00c9001c40704000128601c0c084182e07100801000c1540300c200241840b0800c0060549c510f04501c804071200103c1c3c2c000c1c5107024a9100b400005039010141d49035099440e0004030040c0d8030f004583c0d155003041c02c0c0e00400382104482c4091004a03843d20100b00040d8103520718008592040428110340041124411590096a85c5141740118200d94401c20840c825080414030306a85640c50b001c16401d207019410120b540c6007 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 974200719 1250 974199469 974199487
    0xf0e0307081c11070e06060706140103060509010c080a050c0403140a0209010819122c0306090a030806270901020a030c03020403260f04030f020f0f030a0b0c0403080f 73
    0x109110054064500f80031000c458a405901c0d0303903038030074450f071044044030301d0208446032942022101e141d5000f81003804031b1844104401c203140d10a01c0704892043c40d10000500000c010301c81d05041c00815510760007151210280c81020700000340040c83c40c1c40c0c040000000140c0c881813401d611000100140651400600400403840416441200d00303401c5005840b0483d05415504c401d500d52044203e003116142039800c95801c0c0c0c010043d50040888625034503d8103060315030f403c0042034101e04032041da03541d0390b0841e5150780c0781140040100701040d004c01d84c945041040f080f00070391401200d115480c000600110300c03002c281c0d00310103140d5000490948103641801515294196030606516280c80c1d99110704070070303051311604511405003c010310030040d0350030111140c0f81d00600c60952030b1a12410814400002544200d2150701c00c5010522a401c2410603c207030719600a025250019940d12080e21246004228505e00035040102000085884000d804503486110105844120803 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 974201969 1250 974200719 974200753
    0xf03130204270218060135010e1b04050f0904050102191106100e010302061b0106140307080c0d0b0403050705060708151906050f0c10090b0a0b030705010f0e030708 72
    0x120342c00b2504d4180d04101301c9182d070003100341c880050700d418400ea21104400d0040d02c090892103200d9900080310b800006100e4410401325000704880c858406038054690038604844c0b0940c890113800101c1c81030a603c0c00d00c8d21403a540c0d40706025100141c13502201808a01041004031701d01c5011441c0b00d050107111250411640b58030811502c03ca1000c02c0c100303c0c000780746000511000740f040c1000030700c0c0b444080002100c0c0001c1111500207000c1203803903c0943c1104070210341c1080c0640304d0210009101c080018007000305403c042d19034503100040e034903014400903006009400703010b0100240700000308104090b520910440c0c1e1512010b051180380c108082035030510b100e204a03029203040250f10305603002070781100d007103081c001d50703403980451074014602580c1041038840c051a5440058086590049110a0311800d1208036035540c4d543c824084880c800b01d010f405901059003405194001c0c074074804680040d0038103883c0190340780006494042650044003c913001a5440c0300c4507110 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 974203219 1250 974201969 974201989
    0xc04030b10060e0402092106062b08090d24060b09180907050a080f010c021207020d020d06090f060c0f020316110a0f0612020f031302042702 62
    0x1003040c400805518002d0010000d01018040c5031003960f000031100c52030758484903005080e03038031541c0c000e81d118020865136480c1c0d201226418040c52001104408640d42d1012042400130740101c003552a42850f102c80301d280e003128101641248c0500309100200e40204005000d00940040c0380c1c0d08682940c1c101000d603069503010121010080c4204851981c4080c2840300501000d126154641d4852184910344245540020b40103515404082480480840e48042c00c0d00c444000b030055041030b032012a5900703002c54003110321034018010b480c0140340011034003415500060031181c51900c00d446000484986000c02c13a030070400008440304228441c051140098014201184288c90f40003020b501c0348079041c041851501d8001005040240340c0354440c65030340300640b005010b240c4480c207190250105006100c045405882c4100454019000b03d03503a009010384c1440c01c54032380c106031840c49903050000301d03841030303c46041038204003000204882c0b0096060740c04000b410305006001c3c04040c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 974204469 1250 974203219 974203231
    0x2304020408030a030e0106050d030c050609060115031a04050a02070209060a06090302060c030403081306030e0a1211210a14091c1e1113140117150c04030b 68
    0x100500c0104141e6901009840e908110390401250034003003c4145401406503030000c40c3d20901009940051651020507482458424802c42c1d0b100d8445803000c03036441100344aa580380202072248050454400e400008019411303418500200e408a00020f0544d44202e80c2c0c4100349502113600b0f01980342c000c500e1038018806403662a8901d061450041c0000e03c1c07030001034050b1000084102c04c800702001203500660f0045070954480901581d40c80c08500d4509c11400003a0400318418994140400d1400b09503611541082440c03014203000e031b80d03040280c60407503030758000c400c4107424011501c1505a4941c80056a4580d50040b010024020802c14090701142c07440074010700000303880c0d0715000440b03922042c68016214820b803618049009000d01054015911044250100000d40303410b615440030880d541646500701004140845004104a100310344100d8010080004100040702d0b014003181d040c3c1750346030242e81d4a0600b04030140e0310403200103c0000d0810522120b0051079402803 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 974205719 1250 974204469 974204471
    0x506190906140906240d020114040b031e01260c03062a040803072423180a110303040f031209063b1003201204080903162304 55
    0x844081a604543c0402c503010346d00407060344e4024815a0b0246080741070304c00c06c1d071050341d9403035840f03200480c0c0c0e0390000d031207008141001140c0107262080c03101e40d103030598488002e80051084407100100e4518421131450105008100a0880c01d482c1805124840c400300c0031544041d84414041807030700400c40240c00c92120041c0410b00c041c0d2004811180303480e80000700d040710001043c04100404005205005c1614602141c580e03c6600708809840f1111510020f03004943d24000965002646884900340c5504003000300b400050300c49403210314062000d021241044d44403031440301000c2403500141d03014071565a45980b9140d00c4541100900314515081c8101d00043c2d00320511400060b103080c4074841c0140b03a2201d851b807503070301c0c031b0b1002c1800030301c0c0545d45002c1c81b0001e001402c00b041101e154207091a107044807000d1480840d80c0c142da400380941c4030b55903107481e02c0c007564000401403a85401620b06e82c42c6440f41b00102080130b0250030b0030906500d05020340782c019110f1a2450349001e6 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 974206969 1250 974205719 974205751
    0x9070c020f240d0e060717150609100203091c020427031b080418060e010506072a1e05091b030a450506190906140906 52
    0xc0080035250000b0030141100c5032242c21400c40240680064150310600e440703400704000d0b80d01d500c158890f9442c000f901980469442d40320101e000c8151903003a054001030104290303402070a182902d440d402d49680b0661341000030f55030008901e4500c1d0f0030040c0c443c40703060307140c0360962906120742001c07520280c020310002c28180202c2c0c141450100409001c6c0003090008280d101740ca0008403102a0740701800c90742d5203858036107025040f42501007820005181200c0031840e285c14140c498141d84005203c42c0c20240c541d81e46040700039000c0c00720309091a9013000c0681603100e000d114406040040b8030100d8405144240c1c840709207059010702d2207014850288400908101001e55690148580e01e994a640700101540a08800310469509004556841e030000d608800000b4112070201340788140d080d00c40e540c103100040c542001600340c1e0800740104402d075484070030114030034001030b03400300d50004c04e90ac80c0380441e26108800580d400143c0108502c2c44400d001c0c082e4000ca40000004032 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 974208219 1250 974206969 974206999
    0x6081b030721021201060806010b03010e070906121113030c06081e04020d0f120e0103060503010b102003040602010614030f070605090307030501060f03060e0f060f0a06030209070c020f 81
    0x1d1000e1803000f03402201c3c81d000c04551184203403c1400608020001c4503883e594075001c41500d03030b00c24070440422040305c101003403215100c4c040a0303084401998801a808144105d03403002081100040c64900c0c10400000452115880e180801180180c1d4a01c0d00c2516091000d081884000d040401e00c1c501070990b01d0042e01d178403080070b801c070350191540ca08141651034510700c5130854030306c0a4898108038450400c110b0f44112418080c42c420780c3c090000d01d9440003418260768407145400d0f40702e4461030008108903c02c1c0d42d8124201d0516140340504408071035880c0c190343c003075080840180d445800900406201c00c07200b0041c008290020041c10850186180e1641c0c594010b92040000016010a881e50100801e20103590040e0082000f00e565114021001c0454401103890604014564101403008600c1d51140d5031000c0180417103989031780505130311080c010724810605540d0300000c00542c6424400d544a4030268650b0300070b00146004001c1070700c46510315030303202c0c40410002e180 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 974209469 1250 974208219 974208269
    0x5010b0a2709080c01140103021903170a1812030e0603160e190602072c0f070302070b13020405010f121104020409051f0602011b0c03020106081b0307 66
    0x401e16920540009004100b4a840e4201c2d10800d11021200e40c2800001001070004c40e0304541200c2c402c860b0001e4009001e02e41d40910031203071002402c100c10702c4000d00980345c0d14a0003002445001d00e08140c03190400d0314601e4030001b0940128140001702030030fa504064000c07903100242e042c1218003a05510b403074410b01d07441c1c501c2ca4400d20104004140900b641e40c50f140340c650700c227014203101810a6510b5400095483d2a103104007020181c2c1d5454801c64404146140400c0910041e2100c8460303881440c0d1070782c5020003404080070554200080d2000c0391a00d0842401181c40740394002c1c070314000d0300410050b9031703042c2c00406180284500800c10200c1e183c2c2e500ac0f13010ba0040307c001d4030800c0080000d000b1701496000401d40d900782801c111030134456480214001c05c030002190141d0f51188001c900301e03000d01c0c0301c005015001c10000d070091401508841c540d5031191001049245c2c0301d100c8641072030426985208030100800032201d546c90180034500181044100c1ca9640c00181c0e85504 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 974210719 1250 974209469 974209529
    0x50a06170619051c08210612030301170a0b010608070f090b0a120204080102070501051906140f120d0203090414040b0c03130606080d0f02010e07050402180d05010b0a 73
    0x1900c541c002c110368048541c004c403140c0803078a0f088034086071114114180210491041c00410031115580800a11645403c0903a0403881e41014011810740e0b007000c00580c0519400e8034039010900c94a11900009140011401d01030403031b40d500c038519400c2960019196521028000040c001e041809205084201003034a664282d1032501401410b1017004100003441170303800c00c1816500000b0020240241500300c81d004581e202000c451074050a40320900700d8a05026080700072030743c4400c04a03a07162103a00e840d2102001000f65124a0407030054514043d0380180c280e0168002090260042c035003072180d95483d00c407000c1c041c0558501952082081c680080941d40c00312808804252495a00c06042400d0b42d8420800c000c4191145220755a440b84050454005040620341b400030f03074411f0060082e060f102c0b80040456500f404100000394200300e0001080905c0d42d0f43c4209540c5c1c48040700c90190340180d000050083c0c003181480003200c3c0070740001240d10074090000d00c248007165184 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 974211969 1250 974210719 974210729
    0x6020c090705090a18140f0c070b07032405090c0c030f0a09180f18020906040e0f1504140c010507060b040f060b120615071407050a06170619 62
    0xc955189540c0780000e038a2601174210000c400c60481c03c040038004c99a00001681030300c01c0c01151280e40d042d13440740340300204403040c2e0300c1e0000a100300c000040c0a5103005420032482c0c14045050400e40041008d041e5003602490710382907802c40100501d08040745800e07040b0442e040c665150050202882d0303600c0c801c2d4502c1d001d50070000120a000e0074803854500c1c0260124101802c14900346403a404040c00503c2c031900403c51811851111308090f00c4401030001c4d0707000d031014000c0e94607207007008020400c04c10b5a1030140a0002a03e140c4901800b00d203003072032049054803801b03080508151011280907800340d82c040c0d10107004030455a80010039944215402000410385015407000b00740944035104c807110b00b003420010045041d0540401806c6803a000101b240c49a584003810491240101d0031145100d80c8200414404030381100e82021000c1180c80844212981d18000f080790803405611100019000c0302d2540f24040b14201c032650410b0382152000ba0a140300300d9850700d42c0405100c3c0e = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 974213219 1250 974211969 974211977
    0xb10030203071b080c0304080f0c18071d04050c04060e101728051f0311060904060506040b0c06161209050c09091f0207080301090b010908160f06020c0907 68
    0x29900b0403046504036401051440251ba890790b588104e0300d030b1784ea0043c0b2520303805030084030510703013160505002000c11030650540a90503600c5084040c0d0300104400051070003624842c1c1c0311007041c1c0f554012107018101c8500b0050b61a40f0306030000700801c000c82c80c030324428a100c1040c1000300398001c080300e1500741c0d642201c0041d40c41d40b14004041004254410782c1b613000400c3c030403086c04801d60009100c0c4840790300c0c0e8070301c05441a00194800001e40030003003210b5003020b55041030741000806031088140282002030b61503225000281203421a80c040e40356188006180140a10240203e0340c21046a0340d02c4d00c1010040031000d84a1004410710210656480c800c2005019041110325203402018080004504100940d5030300d0381315112071300000d5100800400d1030320100e40308445000d034010f91076a080d0790804241030040c0844c004203904210032803001190104040c00800b00240329409014400c070319000041c026002c1076400b18007550007404400700551510409282e0040507464 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 974214469 1250 974213219 974213267
    0x5030306012a0b04210f030506060d050901022d1912091406070912110d0512040302030717031206041e02040905150109060e0a03150b1003020307 64
    0xc000c820401a0b0740321082c01c41d803154084018400c0707106506000c0d60103075200803d034081e450403114030400030304003400c0000c0f0100c40c844020784c800d90000d5040200249800d182140e04041c1c282919010786016803075075030005c0d0f214552082c940d4503012103080e03807040071241c1e8041600c098017402420030364445009610a0001c850348100000c5c0c10509610004100c070040c54149848038040b448802c40c40c0e886220080303940c0c240140640301c122401d524100d8032a2080360364080100c070591000c650440f1070300d900c40300061401d00030b107401e101c0112030322501d6520b94010145440815804100c0712145090030340d40081020089558128001502401079252000420014103004800f0304000c1038465800c60440c05540090040ba910f010050250361256400559086450100c07180828400d110400c401805404c0b20461400e00500180002ea601d440f04d040c0c0c030030540c0c01b40701d04e10350f500f400744042d00e00140c0541c0011f0a42c5011410f61401101c0544880304401c1c0e8441d00c200042 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 974215719 1250 974214469 974214497
    0x5150301090c0e0a08031207110a2604150201060509060d030503150907050c0c0a050d030804060f0c03230f180316030810080a3f08160504030503030601 67
    0x205443c07903200c054400c81020b980c0d400303c203441750801c0c0c02141480301d80e003003c0b81c00584100e00581119240340c010300285002c65440b000d00b50b017148050040144014120440350a02c14060002008400342c8406120240302c4003c1c2101c0840d000070344038050350414004580c039448c444480c2d8683c503042842d80e80d00ca0081040140ca016035920b544a07200b0001c000e4007a50160181a683c034404048860700c401c1d482c03c000c03442419010307842c3c1149000c014100420f220350719468025000300400210407541004003c2907410404000001c40c0d10f80920b4400e81c452440c0640c02d520345000c910207181001c0380a105220005400038445041594501c4036209041c42100c4c1d1130b04440312880201c00d00703460082d00d242002c03201c0501190000354001001d04000c1100c420050f400640b0b1132a80d030010304501220441e044440c0f80c07070f000000e80000c11864524032102d09020a031075020283c6860480082c084100d90506030406c24103100400c0020700c000152a0040b4003404d242072081046 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 974216969 1250 974215719 974215727
    0xa05010320031507030c0314042001050d0903091701020a0f110f061e060a08370f0b06010f2c1f0f030c020318130c1805150301090c 58
    0x2d50107102e02d40c034440c81800740f49a01588100860000d0791804e009240c0048c0d200342400500f290080c048108a9511140c00c94080c83c4d80c540c9c3c0f0314141807180c10845000348042c2240c0d2000000c0b0086a6071190500c01105941d180104802d4a2402540380880385c0500400d13078400c100030f2505200d2050013002d48081d00b03200203450f0412550840740c1515140700303464489052031500302c0c01a44014041080b40c1400301c202829a480c0b0030040c158201c1c0400c14150300540c4840074907105880d504d440718407200c85255205154040c00b5259502921401c0c40040c0e000064103040c107101030101a69403080e007180303030780c0c4040220011400d840701c020760f1803035070b01c240c00080143d03c180b0342c7c119000c000d0003482d00702c09e035145c0a0350f5400c00752003002419400c41c0e1450f28184013682c0240030303262204076210f61800700f00c60042c00e0301c03800c1c2e51a5024482500c1c4003411003c08503120700185041074008002c64002001e048400c0410800a030100c9042d41c4018051099496140c103401d11445001d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 974218219 1250 974216969 974216983
    0x32a140f01022509060b03130f020f04050906040317070c021512160905010309020906061b01110a17060d15061a07050d140a1d03060411090a0501032003 67
    0x2680810701056028401c102da502d903500c1c0135030343c100e074504440070490b03041c0001613a100b0354030602e0322411200503460b8451102c000c81d1040b43d0241070680500e4041d29540a400d0103401800001c0169050a10b40900b80c0070325074052a803100d002c00708000e0416031049140c2c50003901070302e1000c0e41251410b070701c2da060304c50300e08403948103920308040c80b001c4030201c18200d2074042e569492407045610340c0d0046050b184600b8003e0750154031840880e0151415400400031440702c140400b615003041007206080da003290030808400040403402c0c428098000c200e11401054007100d1781c041d40341c01d50000b4006005c03000060300050031400f40300b070490001e03401070000d000a04074601b0481e418103182c0503c2d5001100859460040401402030140100d11514002d1320080007103081c04000501210b00c00320403054811000710740d6140140c0c5d85ca0600550740140c1c002c0c5074051181000b1010720911180150550901510300001000441c17001988402d80c82d5159a500d194003429000103032074204 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 974219469 1250 974218219 974218243
    0x120b1512180c010309080c06100e0a0e0a080a0314180d03050f0a0903020a08030a0c0f020318010f020c0d08090f06070c060806060405040e010b12030909011203030e0601032a140f0102 80
    0x200d08028041c007541c601c1090421110070840c800031654500cbc0011007078410340300d00102c044d0710005a400000b40c00e03a015148100076403400090051079842c8540d074403d0181c40103a0035501e402c04500c0720741400c0c481160001c15074101441181403140381501048070040840b0f02c00d0303a65020400c20180309101c202955900320741e0554603070410422610050040388040004260208070302982d290001c0f068680b6042e20b48129000f4504400040d112010b1503000c8404501030005e4400d1a560346030210501d050050114540315034102045c801245400c4041d14401e6400b4031008000585071080081694503910700140551101c00c0805e5040c0103a403c069030040c01c20441d6030b10580150b002d00d280d02e404860a03102940742d154404d40b240700303580d421340e002a0f89000600c03554110340b155082c1b05100f803030001104091400711606240d420b803c220351840c00400240348050b5525400c0580d00160700c3c01e40b240e149800d10000d80403510811f50b034007130f920381c8480f2501030f0700921248040c00 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 974220719 1250 974219469 974219473
    0x50a120812180a06140a060303200c0a03050f102013051206070f0e131d030c030a090b0306090a1d100603021309030807120b1512180c010309080c 64
    0x40014130740f0070301514001865154005a120010700380d02c45c0c5000c1c030021a6016112000c5129119011240746998170214081d14450318500040607120601200021809580a4014200400c800a00b00500b0000c1601c2440c10600002500b0410100c01c6040c0100e401d1019900c80060b1101c0d084900d85134007895000010a02881c0841000b20f40f00781701d5041aa02c07188043c000110540e0154052307801c5680101c25143c54100d180001c4d844005010280e5445055507116005207a203180d204c3e401d09030b1190800b14000000b55004810300c80500b0010300740a00b10325015000c20f140280082c01410941d0700c40701c440305403a1442d0100d04507200d000c0b007a15110840519440d02900440c07204070700501480c110b28540c88040e2103440c4405905a40e500419221200300b10f9400210783c44c4400c00c90b9039101000d070603903a540074402901c4072007034000340c58440d03014840e09207110042c80160a80b914080410b0304900220b450307a6091000d0074001028882c504216580e07016048018000e4 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 974221969 1250 974220719 974220733
    0x504091b0807260a140a090809060901031803090e09010513021507022d090405101e050f0106080a0c020a1707060203130b060d0b01030831050a12081218 67
    0x10010350004030070b00c003076405c1800310740e269810302000303c1b001c02a010f45800000c0c081c1003000d01d4008000d10414005140c0450f80d80e14400b00e840d80000040000c60104010207420030020000d4001c4580c880c007084002c00003403804040c0030300203003200b0350003c1c4100c81250802c4609030003202070314465074000d40314410030000806070142d0600c4105d000b5a40c011070112028040c0351032140750744078640c00030142005040c414000e03000b07880740101500b07420950364050090721840b4400c541c4101d580001e0460b05501d4901c01402401c80038210440050038002d2040d040c0c1d070001045506150f024034150709400c170308002090036024800c8000d086a000006111000e010342d0034401040c0e001d1302c00c0c041961200307002c1003551b8440ca84000d1100030040010004540d40c40050101c1420541c2d807401d50b12010340401c19144152031030b110310f203928040140b1490030502400000b5100081524003c80300c1c584a0300024005d4414881c0f20080c0440060192516000081c1aa000c40011a603130 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 974223219 1250 974221969 974221981
    0x3050a17070309050c04230403051c0b091003051f0f0204060e18090703030f0314090105160518190308070c0e060f010507020f1f0504091b080726 64
    0xd0840000700740c13418402c603800481940340038403405d6509042d4941c40c0b103008580f4030854184d5a00244264240102400048100300644a03014013a80c2c071980c00007040e0102e0703002c00034140005001d511313041001210900c00203034002405d19242e800c0c420880150103c8004020103481e40b1164414418004980011259040082e80c400b40d4022030b840d0004040d02859508098000c44401034260300140741040468000c140c0010740d0806458007140c0740d840c0c030802480154055076005180c1e90b654040041c0720b000c0f90303490420030581c1c0c076029191400f041e000320950240c0c00b440e107100d1a011541000c60000d4562400015540001d00b5510740303a803810200041c12003445042c1005419030300050407480c00c3c011034111000f0584030b0905044681d020310020011103112030303400c110441c0648803c0d01d4003017030444440466640f250750b542d0411500b00c00f40d420241c01e1189045120716a1440c654000e100350398400090b14001c8070f500042111840585175910901d08003200d040c0030b00c04 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 974224469 1250 974223219 974223221
    0x4050a020a08031e0a0917010209041109031c090512070306060602011b050a051611151c1a0d03052506060e0609180114093703050a170703 61
    0x341360151240040740c50500342c600b84550348610003140000518095040c4580b141c007110201103c0e51300c800050030200810013140c101c4200f6200c150212502160920a91904014100380c010510f2402d84e000c00d40343c4005004550300e03001e410700c12400c010510500480c10043c4100454100000307100311030790380d0700203802800040c900300c5102504107070882a09000c1c008840c820710752940c4440c60000800c0085d03816044070345084030480d6905204251598030307800d0808040c21511002c50751040090382402140000000c1c0000c25810200f44429564212010342111041034030141c1c0d44110a28040390544500d440480303140d040c005850345400005d480e039811003071040c0006c00040f9118203000b10094011680e1a078411b085000281141840070807068004003000c00108090100305841c000c0e801c0f040720b40c0e0005500492100702d265000707003405020036000a9406403104005401c420308032440700b0010301403200014002541c64440c0c44110354100b144100c111844c105910020 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 974225719 1250 974224469 974224477
    0x622271202010b01050301060c060b01030902060703270e06131113060906030204180b0112060602010f111c0902031912020f120703030f1401030c080f070501050f0304050a020a0803 79
    0x39005610300380341d154a0b0350203001100e050316007a88074510310030103036650300e0007810010034628101500c4030310100060700c0302c0001e03100c401d119858000b03e080021101e04603c0e1551b1081c1308421000840400c800c0030380c051029080360042d40ca608402e5a25070124000e0030b50b45400088011000a0030840d000a051801c410b640e00343e503480c01841d41e2040304030245d0090340200203a08042c00a8500540680d0703100401002060410040710400c0542000454100b9480317180075035120015502140030b140f040a207400001403120b4204500d20551001007000c02210744103545d5900c2000d070a55404000d4903000e8801221503207450f40013490030443e40401c0241040151060b054104114000800c90300c041c1c01c4202b090504240ca580c90032009003c2c50324043e01030304d9940e030713400794120309100340c213030107980600700880305c85241c003ca140c6400103251070f54a00d50094041840a603034010200c031010b00032045255160307292800e00c141058a000d0000b980003804442c0000c1078203012001d4 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 974226969 1250 974225719 974225753
    0xa08030906010905010501080412230c1e1b150708071a090a32010e0106060216050303070305070819030507030b01030b21100c090e062227 61
    0x244200d1b66150010b4890341010b840c010700d07268000901d1780c1c900d48507402e001900d2002c0c5020f001c0c00014480420f295510404201c0c4590f088100c081c0081030204802c4458810320307100400000c06031880480082800c1c00c9400d1080c45403203410554081c070002903c001c01d8100301d249a8444640c44d044a114106501c0201604642c00c00106a440007140d4445078580103030b00c00c1201c0d40c1030922a00e00d07801204240c1e8408480d0035070581042424415441d41d00001400010f0a03405d01c84003074503140c3c3c07406c11150b00000804051100d61804403c0d076918592500707100c0e489542a24184c02503008481d40f1081d40049801240003256243c0c0005010318020b4a08200310301d8034000460a5030780c0c082245400c40082440b41d0394140ca1854050440f0003002d0075034101c106201001c5c0146c0340c0d00c0c00c020000412241042c841118550741254010408481c4060200c0191103080c2c004a12088409015580c038120250445050b03100e2000800d11060302031040300700c600d003112054103d9030700 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 974228219 1250 974226969 974226971
    0x71413141305100306050a18050f07050613180209060d0b01270510020a0f0813061d0d14070b0d1406030616030b060f0307030b0f0d0201030b030a080309060109 70
    0x1009080ca10315124041c020844107190f80149403c41e03e808000d444c0260400f044603546101c4050036054801c03c040400c1d109001411000c2540c9104515045140d001603100c0c0404200d654002000074950300100c50201002c0c900c42e1401d444500000d0140003c041c2c1c01540c001038075045120079a0000ba04100e00b62620031940324110756000040304c0785402c98508007401841846203241500d0700c81650f000743e1044402860095881049410061000f02c2d5608404203d0180351055402030b980a040176151000d1155a2101c558000303901c811041c501503090784010b141801442c0011642c60768910040304c05e03040d07588a545280764040c022400f2000d140541c0000d01c0510411914010f0380018018135840e140c405034241807002882c04c21081c15542d11140034161038960161601c448003440407a1a850000800360035600440742091150a680b007400e2102e80d075010f0100103141d02031070000794801c4060003081ca044144640603002d004080700700500350341d002030018141c902140d0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 974229469 1250 974228219 974228239
    0x50406061808010b010f050f040b07031115070813020315070c0201030b030303280204080a12021c1407260703020f030f07150906050a05010618080607141314 69
    0x8003404c940d5241d0105001030411600c84841c0c138481ca004d4520105240d5038189400e54071064071050342e000490440105052100c40341c0201000e010306440311101c102030b00c0c100e142c4403100500040000300001740c0400b8110101056407000c1000d01c6c1c2c1b41003003c0d007070785641c200890041c004550050b0100c2c0041d003490040e500034180441580c0c066914084d0281003800a1840c9a160800c0721600c032040a07804c4c41700181c0e0000c10019402150b0041c4007441340140b0f0060002d00349140c000c281c180d008045102c0301348180e8003032440d003c08048800030b03036215012883c0041003808541018282c0d60b0404041d40403000c2e1340402000218865000c40e042c01f1034404c09551030b4050103071402a4041d05101c6c0e10045106040c0310032006d03a2200d800a521480f0b0354a003400c8031401e0300c0c9503c1c2c8903070b1200148403550300a40a011b9a00201044050f03aa103413694860752024000c0205080203224002d80545905d024162080c044040c2c5080d8640742d102c500f002002c0061910185c0724a403154 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 974230719 1250 974229469 974229479
    0x6140f030f0d08062809050c0c070b0f0408120d1b08040219050618030706090b0f09030111030403121a0315092a04050a02120a050601090504060618 65
    0x65052031160803000644026150108103841c24280100145d0704000495410400b00c402c05600711081094000e0401c0038a042c0884002158001000c1000044003001148965000012000c5c01c0310380c1c0c5100256074250300f0360070007070902507540281020b1140c040080003000da0100903065074071540c2020800401d0522020028a01210a142c0455410301c00318000d82403180c0000d01030585c0c490200d0050340e4810125125038442280c065200304a44d0004209203001d11030f00006065034034001c0c80031713801d081c0030308600e1023209801200450009940c00141e2802c0d045292034001d110750700c50700c030b250070b04001c2c255901c0304650500b41c80c50042040e00351101e01c3d240c400c001c18080e00034560f0304130000e5050141c10005d403400d074503440b88010f1480c0140500a02a50070058544950b612100c2c41341070006440700a410b000c0906c1c014080c0407102c803405400ca0b94410b800e04e101181076100c03000140e40344401a008180c0060912401180c0c1640040c80468081d4440700b0040ca1540d0361 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 974231969 1250 974230719 974230723
    0x30206061203071a060301060e0702010209030f0d050406031805060415050a0c0905090a0605030d020d110c060708070303140c19020705220605042a08040503030f0a020702030106140f03 81
    0x10000140700c040010748a0b8813100c0c0021000364454009000066501e884511005501208131450740c0141e40001d40300d09181014440d010704e026501c4000c02a2920504020b0007034080d50203240101680c0303c1140700c2041e114040e545580350801d055035524141800c066a03040741004a002c0c00c141040e0102d01407000e240314040344450385540d103610399802c01c01004040c00010348220004c03500d481d00401d041d07805104140707400d070710368000300901c0d8840c120107400c484081580d01480d4010700313000000c54441600321482654000395440d070b02c003690324054004012000d00785414203415020007080b200301c200100740441d806500400d40008140701241c2c2c83c0740600a080e00003100e04d5004200201420101440c1c008110340440c4464075103001c10100e8000854284800301d02110b00003028120f030008000c104024501004030f850586c86030303540d910000e86481507003801500041c40e040c1c210f5054854103a802402801080c1ea43d181ca0a11b114207014603034840d04185c0401304081c0b0300 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 974233219 1250 974231969 974231977
    0x30304051b060705060c1308011a1002030c1605150901120c031e02220b0712090902071203050c1809091509060702010b040908031902090607030206061203 68
    0x40000140004090100e215032440740d08800a40c015209200e2500007130303401c0c004144140c44041c00d854652118480f04100150194000b51069150550488144541c8580c6c00c003409001e94006400040014049165100b4940c150380079015444201544c1d20a54801c0000c884040742c2007907060220401c498118400c0c03484045c003040903004249003c205540103500ca5402505000901c00302c4003200c01095000307114002c800c0caa0014502e02d102041810f130b41801011102002c40702c1d4100b00d1407d60602c40d030038000e08004401c0501c2100c1d54810714032032010789000c010954440c5c18901d06920010a5070100e01c02003400c00c400511054510380c15242610241400c40114a4540c41401103841021302142c030907026442c00c0c40000c01300503466901644845000300068035000e08000e0840e40700c0e00d0b0031480307141030062010210700c403681a07a4005008050016081d039108400200910641190342c0e00020045016424580c0209000307202c0c0030155800031038540b060244a4032445 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 974234469 1250 974233219 974233223
    0x612060a0b03100e100f02090a0602100c0e010c0f0813030f0c1406090418050d051908071e0309060c180f12080c010207061a010e01110706030b03011509060303080108030304 76
    0x100c41000d05d20311030b2042c0c00c002048060404014584503c160110b03003410029000788026a00c20202e8141c014001d105002080c080ea00e030100c180008600001d01103036140501521180268801009110014045034020b81012480c40c444070f41e60325105400c0c0e40345030000d42c3d050911a030300298515181420142c0d00000030300b0300d880c20194100f0000185070131303410111299074030103803040050b004011346030350a01e07552101c90b1184507150243e1050241040301004101c8200107019207241c10140c1c41112140001c0c4c42002051582000c400411001c07101405960902501c00c45c10394000000c00c1c61180317101440842c0e641c84810701040d41d41c0d544150220910815410008269010090320300301c20090009403400b110368660340c1c207a92072203508a03c0720b0182203404e0020340e0000c19419105a0a080c9482c03d203121101b1175841c3c1160b40304220a040c1c03542503440c01c03646e00b0b41c040411464403122072100d15440e6500003004101e1408118042408000082071111000055a10480e = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 974235719 1250 974234469 974234473
    0x601020601300b0412050a020a030f1b03090623040501030b01050f0f18093106050a0501050103061d070e0d02030d1710050114030612060a0b03100e 65
    0x80d1038420b102001070b40302c0036a0500b4101000001c940b550102a00c4600140140303030018076401c003070074200400450204044180f01c1c0030032030100000e4002c110311941c00e405041c14a182c0540000c1910007000300854221200300600c070340d008150304402450184e9410b5500c0e19940000000506003c1503034000070341594105120801c0298404d8004005610040c50201c3c10030b407401034084c41c582c00840d03040c00d000038045032030600c0b040c0b42c0da03131150071040c11950754103503080c00580e000b201c428020702810a005203043c2010038018000c844043c1550142c2c0c10899071030042450401040280501e5001905208000450410b036880440c03210400e44034641450b260110250f0340c03000c58140017900030740094006405a5000c1c03101180948140e2140c43c0619440d402200e0030800040c90140c09092081c01800207903403009012106030040c6051555a0300c030728000503900312a0050f0310b8024421541040310710983d58001c4680d500d01502140c1c1082070052000040d10f8582080e00c50036 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 974236969 1250 974235719 974235721
    0xb06040b01021906060e01080705011713200333060307090209010905130911060c10021606060602150105090c0909060415080705011206030c0608090c0a1d0f06010206 73
    0x48581058443d010f10b204101c006080caa407201410000b6100342e100148c180c00100d02080103503001a105c3c00080c0310104c1003083e500d044218030400507402000a800c1da1565a142c58400040350b2101048501c0181201c0c01e0010b180003e20344804201e2140703900c003c4081d414494031600c0814640036100003400303858114100001c160081d00300c0d14006040100b9441d0001c0e9513260001040d08030a1101c1c0045202c45c0c16081104115040e989001c0c021380081102240c4030310003080c855402040010701503901c0c0042d0500e200404000d07140949440d00e001d034000b403007680000d0b2000c40007068601c1c28a8681c0c1e148100600f404048891107070346c0108011800d060303d0100345159202d1801031002444034141074807104900c4207500140b0705035104450902156802c800304000c46090b1007000d03c00c0a0540e034600c8200c858a208000920450304c000c0380b03982505000111490501421510354242d44040010004904007640303200404031801180e08101c6401d010340c410b01041c6c000b001d2b1 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 974238219 1250 974236969 974236993
    0x906061a16030c300801050a06030e07090e030a09060507020607030c081201351c05190302251a070309061b0f021501091503140a0b06040b0102 63
    0x5000741d810811000c20600d100401c000910311000e890340b00c1100c100e1360545030641908640c8161440290b141032240a500402050340c441d40b844058454625012855111001415140000075000801d026041c8001c0800782a400405000c20030810f54031111180c0d55500b080d01e1030f200d00301c0301940081d0200444400b081c0140f00e1340c1e0400f4803e0f113016240c0710800f150b02d040d800080e005680400a404171a280403002c403248003422600002005000354690100e455880c4000023640030034050b580d205810700780c0140150340810440e51152454207091202c018025405404641e00221510102500e150200d9920101c001d81c0b0802211580c2544840b91858402c0209400f08154843c0074803000200c990041e60b55080c000c1c2c02486d0032500d00c0c80c018100440349400e5200310752200440e0100c801d02040c0160441e104071100041c111416003040203036038200d40000e03001c11680e10103402a1040002d0312581c1078011400704003961140700800040d11040241240140d01c54010010 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 974239469 1250 974238219 974238247
    0x31403100e040302060103050c0118031401060312050d0507030b0603060f190806180609150c0d05040f0b010506180f0301060e01030c0806070e0d0f03090b030a0906061a 74
    0x2030030042600d6080c040035034480d6400c801c86822201280140c015100401c2008020000690509000d00380800c5500d5410340403079a00d102c0b84005802481404a18408420294040c2c0003a540000756034425501504018100364003040010344420f2800700019000e41c401e214072083d041000341043d1a584618041200702454035008075840040b444810815941901f0b81800812112014103520702d460900303810107404072002100c15402400c00c2182c4a040403906c1e564440601c21400d000740c6903842c100410b4020720070802d555929103006c0c8814014900403001c9e40900c80c5e0704650b40383ea01c0c0c4003840b41600805501c03890030340980c075140b19940b40c07100e003000d48000302800010300d0302d81e12541c8409505003070348241c90744105003805000045c1c1c00d01490ba40f200c03c0e03081c10780d40c03c1404408100c0100c0603500281c000c0000d08620703003c15205401c000010800b1001482d00c90409608003801400b000758211049460003800003240642c180080400c640c0b6860002e003841c244c440c0841c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 974240719 1250 974239469 974239471
    0x9040308071719020d1517060108010b01051207050405030a0c050f010e060423090109091202030403020f0918010606110f061b0c0307140c1e1f0315080a030305060a03031403 76
    0x3c44003502c0300d21080c01c581d4846d0740d04000342a00100810400d014080c41402c111060f044002c142c0d04100c3c180e0300c0e917604901102c0b20b00344885114007560b07a0b120421038940c0642c8e00f180381c1c1801035401100a0100c101c07600e9040d11801c8818140c0468508010f41d040440c4d2581c0316002a0240000c0100c8065400000c1c2c056100740080c0740102541400914219000d800240c025a43e0300240c00510030444140300100700c5500045140c40c0c11174001510003410022124807440421000a00e0b52441e541c991050540000003030042c00d4860030050315221521810300801e00c140da4070f606c062980000c8060141c015060f200615410150440d1003070b5100c00d101c000944010004040000c120441c0d817120500000041c200b04d011030800c01c0031951103411100003170401d95003450015a0380c0c02185d01d034421100307ea4a10074112400075000780c80b841403c01c0c4520301c121000a6000b1020452509080c0b09642c100403c2c4c0c0c480301005100182e40c007020f00082c101c0060504240c0a1000075 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 974241969 1250 974240719 974240737
    0xa030e1c0f0c0204090605100f08060a050601050c030c1c020d1413031416171b0102071d0f0906220813180f18110406050904030807171902 61
    0x6034021402d1034004c1801d03141c290400b03c2e0040d54803000c1000703415030440400041e100440c01c03805120702d0003808079962035014144920742542c0d400420203580c054000c64580440880a13a030b2280c00e18170007151640070380300c08404074035000340204280e5407020600c40700014040d00c0d0300e17080f805601c1401c0050b401c1002c12510b071160840c4084082120b5101e220001c070010380092000240051104039800040e40c010408032400004070241d500d00421241002411140700c8003e2414030030040b4a000442c1e888640c0c0500e56085000d8100080300000b44207a5240c44c10001c02d40360826680d540368412200b040000b141511461518520b240124004502030500b960601f20b548852140f01ea1840d4804465101d140c0c1060301c0030f400500440e42c43c0044c0b29410000f001034051b001000d41070707880c0700910101078240c0300d81407995941c3c0440090200586240c1c0e0b5441e2a14001e80591029600900801d442d0a40020301c59003603250701d4428042d09042e004450140e80302140650452045 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 974243219 1250 974241969 974241977
    0x40b1008040503041a190c030c0609020a032f0319170f040b090f0a050303221203030b031005010b0a050706142d0f0402060903100903050a030e1c0f 65
    0x100184030224400040044c404100f05c0580d6100301110b204011030740c0c80c0804050113280380040000c00c0d040245101003d80001c0301040f42003040c800179049034640d0f04024501c5000b4540380d8200030440c1c00c05440024038801205c2c02c0c10070707502015540c068100301d5010700c0f4a4100c2e5840020041e040308189841c1c072003002801c11010b00c0d0f0661040d0000d800001e0402c0740411580e4140c0b900c03014090b00e1701030503a5142ca0b401c2c10200400c0d1203119607070441141c2181e280b0f40e404085207000d040390060030f825810a0301310503545401000f8103140c440581c403920a41880c80c6d004c520620031075048400b8189001d2610440e0003060711544c0101805641d074580d0740c0c20800e85807603550142da200741311502c0080c0440c920725001c0301800d4048a1b851403030580c088100b01404600109580d001a011a4800e8541840400207858642d484504880c0e41d0708104c0810101078218000c0c5c084504070740c90034025503000c844075980c1ca1803003403c06040d42010460010021340140c0b0f082c44904001c2c40c2c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 974244469 1250 974243219 974243227
    0x1140f01060f02100906151d010915050d06021e25020d0b04030207050a0803180d0203030c19020301050a090f0209071107061706010801030c030303020307020307150c030b040b1008040503 82
    0x140300c0d01103410405c010780d1415110650b224141304040f4040002d8201c075044114840d04010004100c01014050301402c2a03481d004000b1641d4080c00c0e01000304402015942c511036649842400f1f508031601c0070f4044803000401c03140340b9038140c1c20303030310807001070034402001c03200540041c44150740c1c0c031200f680c000c100b4210241c0070900849151340f20324040d400800c03206103001d00b841403180b000e038042013250700103020080740350890b496456105981181c501c1d806241f0350000078118810340e03030340100512802c40c82c040e01c4c4200049000e5068000c40080145648184100040d1040c008004101ca1032500100d8010303d04103502035040540d62a0120040a00c8250589400d43da500070304041481c244642c6414805041a241c0c018420b10381000c00d5403440d6503c00700e040b200d0100030300303064012002580b458800c1050750102904158414a07650005c0907503070081900d6940240001d00384126010f15085c50f00800c250380380d0140c8000a400c94145084400d48405030003107941d800204 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 974245719 1250 974244469 974244493
    0x4060903090b070809011d011d040615081005010201050f063c040b0a0506120c12042d031d03030d020721020c150a030207170c01140f01060f02 63
    0x3201070f1125601c150451a0b450031150005004003041c41102481c440c0c0e01083c8103c0c0340d138086c0a244440b000c0d003080140704408440041c015001b950400c0140358440083c0410659022510501404210717440c4010143c0340c0004a09880044600f240c0444212020518504004030752034806044a840c0c2c0300d00707a03003400d05c25a1015108015007100c13440d00c80e20031118646885038441c09101103030200340a40c507090110b0365600584030010703000d550740e200042290442408442d800380b5010b40320007051a16140c02401e4007454540d040b80ca482d40520107034208100d200d101c2604d500f41d00c61441c6a0860502e040314410245c411b04d41501090240c405582458009042c0c00d61040e010074016899030820b030f140621120072400212340c0a40c0810100743c56600d101d81392400603c0380d02c1d42d202080e00e002d070068802c000004150f945e4408001c4000203215000d03081002c00f0302c0c000d21a0940074080c1c01e06804068440c0104004c049004206032801800c01131110407003801941e480d41400b03 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 974246969 1250 974245719 974245739
    0x40f060c020d0e042702190b030117010e070515072004050903070b060405130b07020f0706050901122f040303090608070e121e010b0a0501170406090309 67
    0x2001508026900042c03030a1442504008031900030340041c0ca04005000e5481811000380700e0980d4951039103201c10380320209540f20704040d0f8a540054459412040f99114060b110541c0700344115241c52003880d028011600060181d071a04030a490000d20082e03090004210400801c28562034103100208030010004208060601c1e006060701d2103800b02d801c402d03041c00146d4400903c03400b80d94000304910f100040c06403248582184058500203403d64400000950b0340108440140108141d40c04100f07a196002924601901d40764091380c4403266103102c10380c0e85020740301e600c0780410703418091030403040d405510400d154225000480020400035003115480c403103a4007011004c000c0010103100341600810814000d186a18026615240600340100044188503400d4400d21015650700b00000d82042084140208140c15445c13070000300d8001ea000340409503040e4003d60141c040000c80d0341c06480b110f1a0714075021040710700f55440c1c1da18072000b031000c10012028890b841001090507881 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 974248219 1250 974246969 974246981
    0x30318020907142a0706020118061a090a09030e0a2d0b03071205060f090f071110140f060102070308030c0705030708031e042001020f01020c0604020907170f040f06 72
    0xc00f22080903c1c1840130290b5080070a180c01c16000d580c1071110000a90090270204c80c002608600d00151523403001c40d510300c64541c1000c041c0c3d40180302d43c0621852460f00c3e031011b105036119444d555010308144050240100040c800e2124007039521005401c4081480003403c1820210709241c01060745441010a403a00b0603641d98000a46541104200407241e11410b604500100c2c5e803000030003640c1000609607030b0000d00030410340c45d1032000720300748501512000d400b200d0700314145e4414094244c0070340003c040e80d61020b2035800407a004552662810748160b4001c500603805000007070b007503442d03442d002c0e0f002801c1c0301d000450410412010039403e0024144541c403601340c1c1a1780c8d0030039031455110380c05640d09500d85a03402009220000d080c28001c104003000d05400300d10203071200d1006038100480d0a59485080d400050000303a0300e403000c603951b4071680c8215540340507611282d100701c84240480802031010b04400020a89030000b103102c1507132291250395030b082c01d2a507560311f01041d604 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 974249469 1250 974248219 974248267
    0x612070b13210c051003291503010e04031218062405030a03200f010c110c0102101e05010902090a060c032a050a050f120a050313030e0612010303031802090714 70
    0xa520703414003a1f17454910100302c3d40c110700350222400e5505164001c0086c0c1d6019100506100c100041c0e2003c060301d42d0400b1928070410841c0c511880d444d810548040c0c4a582c06101142d102019681290354040c00300e90242c50b0094000c2038003a1082d9019141d03104203071441482d100401050850300c84c020400041484865000898a00302044c405400190048460507c507081480c04460590f03000503c5001118094804117110665a000d000b0044001104201c8903040c440045030300d4015400818101009480031103002d070781d8242c00c9440350680f1200a000800454030300c40b001000f0350185d185400401c2c034180c90110142d0703d043c41c104c0a40c100316282d4111014904450701b00b03202c48203006899080782d91030100010f900429512006105400d103000107822801030500c143c00100300300c00701070105640c50705848080c1085080034401200000e0812001e102e15150610f850100d4075406820807125486502d02a280401c030203402c0c00d80c404092020060130346d032200240d100c1c1c40d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 974250719 1250 974249469 974249531
    0x80d020913090c060e01020a03201902030f010b0d0803060f041b0e030304060504030308182a01090b0a05072a08120a05030612070b13210c051003 64
    0x141515100700c40c129180d0000c814417001e4a51a02c55903004a03040c8405545854032030680c20810405121055004215080030701c200c2440807820000b400540301031074002c40c03c0343e40361010715080714240d9460300c5900341c0107150364400c0720004d4124005103800c0280144000714404140000c1011151a04000e030406841119410300080e0003a80001003000c0c00d8000d5031501e0b040801c003402600c40c0303100003020495210005a24500715021014880f01d541c019103108200d0050421884240030345610f00c8400100007000b02580070700e80321811248080c1075581025081041942c0e10f8100743e10a860780c41403d108185004c10b0740140c0c1003040c2c02540f90740c403807034200b512041c0750000e8410820442072040200c6801c1c50380040c02c2d0f0398030a404842c0785103c00d001e00c0c03001c2e0820405611850703a001d00800c1c2030000d41110601c50041c3c4400b40d10240d4020420040144446601e0a010f4900005030b41c0a01c00c60401400340c41c041107207428013003034402c20020220404c41910110066507 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 974251969 1250 974250719 974250731
    0x910120212010509090d1b050a05030c0708060109050103051c03090b0901020d0c020102071a09070807030302014107110304080d08060d0b060112090b160f030612080d020913 76
    0x2516100c0546500206124024906c4440c5030b00040c106240a251031000f0184074212841000300c108000c1010940c000d00350780d00da03500141c4a40e9070341c1e840e01980351580940d030000704d0340c40102e00c5500e040300d822030300400c99a040d003040a5200d50f009041941015201c2c00d900021442500c22940111040400141d5400d20741c8401803c96200044000442e4010890000807502c000e80031600804141004500fa84884600a1070080141e02021302c5014003d0000285a01944004290040d004003a50340300c540261101c819682d2030054408204001d502c03504006140e88141c0d031290328ce040840d00844850f124070302d140c10682c0056030350780c00b409680d16010351242510313409c40070903940100150070320b0751440c5105d40e00620290411802d6550503440519035042071021580001c656881802d000c00411080686030103007078049603c0d0070586804600c80e00c01d882c21541d2451522406000301e0b070310140b1650101e0742000c3c2c0660280700d4108c4a03031700c1c042c130726000d0f01d81c1200c00580c0d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 974253219 1250 974251969 974251979
    0xd1707110115030b0115090b03090f0615030127030f02100e01051e0c1611090106170702210915160309050a060806010503130c0605070620091012021201 67
    0x200105820080e454a05102c42402450300284e01205642c122300020741c4a0380c460304154508514004810600d228441c2070007000c00f1280341d040c003031110075402441b4041c20071100b00c00103400314900c200c0b40b81044c1c07030b0140400e1140702c02c000201d0741031040c0d8039010310f006c994105403042c5000404e50b40e550761051011114034840700e140285880d0003124207518140881c813a0b203008049a15441c20613017a6682e04100c030742c000b003440840009100e81c0b0b003940c617104024415043e94130340060007442d00b804502e0070307400066040c0346000c50400e800e08031180301e0300542550b041968400c0e004a0441d645450145907040680440402030503a600c65402c00c2c03c00400c620b01c1d40d8002030003011203a0050012a510140031503002d4402c3c00c00310b0742c0707407544054403810140c4e80ba4042c00c034a0082d50f01040940e0700100070032002d402480c09010281c1003100800c071401800b0030a00c0794100800015003542864021840e030a05142040c5000782d51540c00d980c1a6400840441c090384000401440 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 974254469 1250 974253219 974253233
    0x3090c06190810050604120c090f050919050601260105090c031b1c15090b090c123301080705130c0804260f0c010c020d170711011503 59
    0x5030100458900f82c070100c2c0380c000429032a100f1400340125041d1540c00d60000e0180b546000344c01800709020400c15000d040725014014002a5180080c50140302d9800c000302000410000d00d1a070020003410b950792911030700901a4a903c803041c0032048c40086158074161080c420948641c00200207000c0d8801c00c60105402d01c92240700750150800c0100b400400c030780f180c0039102c08010158441020342c00341c1d410a240ca001c02211003d140701c0c101500c00f000c102c4e1480f20140219410402c480070b00b0160020040100040c0c880e0300c0041d44220704a15480310400354442c054151002ca0080f0b00b50000910440980309806c4030059a01203401000302d81442c035103002c1d080c0145441000030242c03910380240180c20140020f0041c4003010000040491003809101082d0741803502c281e540d00c40028103141580118046000d95481c1804500081c3c0c0041180d0612035a16600e207803a01d4595141c891044402414240c108854000107500400c1d00f41300d561036100700c090b10488128a5850104 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 974255719 1250 974254469 974254471
    0xf160302040b030321280603060501090207020607060c180602010507080703061d04062304020f0a1809081e090a0801060b07031419110f01020304030507060203090c061908 75
    0x54001d44c4100241200b022000c403801940d881c200c103080b030b4141c4407035039449510820600b04029000e2240c10b10310f03003020b4681c04601124070405060010f0703030783c80803164128041c81001940142c0300b0030030080082c4141e44041581102801c00d008610b00c02213004030340c41165001040980c0d0358400b40000e65800ca101658000301e0340c0f0341800315a0a040050a014402074203001d01c052044011608020f142d402c1403445641035455000600c0899613102d584070400c0e201a40503808040b201c8155041460011069440014106204a12503001030000f000000b00a4072584001d1241c007951055440f0740c2c0390600041142d0945920303a5004114600c59641d02100c1d40fa858204100154422041501c040b281c050038481040c0c2c01440f0a084184a401944070320b0927207941681c650315030006140455a41404119100c2e290280b9596080348000d98016001c21000c1c0314040001da071580085a000d1142000e840f03825544101090b106e0f08114031081c00d1011403441100443d038420402 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 974256969 1250 974255719 974255741
    0x10906080907032306161d012028080a05030406020c010c050301051f02060c1b030d020a0f0302040302150306030f07090b01110703260c0a030207050a06020d0e0603090f16030204 78
    0x150407184a04030203804004c1e4191a250140e50a07840040c1e180e006580b420340f407051030144002000500d0300384544801160201088001c000c4e0312b000c0b04010401104111141d01648943c80c000c00340d80161740982004000700c03000c5808200e006060407081c081c0c103c066030a91100b41d280d5051900300859a68540c590300c600da0404502c065449600064a540188101c24034540d81e03c2030341410482e100a4101d081000c0c4000542e8000c2c00b0308990040c4840e40719503440f02034030f1004040c201d059210b9480040d41c0b1031311b4400003740007054840259000310005044651240f9040003050810a850307020b41d19035943c9070b210038102d5811201500b03403405004041c0880d00d00b159030301c4078954501c42c00c1004100700b494100070416031001c1201c407070254800850702009098034000359141e4250044c0c900800c0314150005d0000e000040e100f22003125511040c2d084040001803020f140c000a2021546105428050000c24401c1c44040c552000303130824802114254014041a92000011303 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 974258219 1250 974256969 974256991
    0x4060501051c03050a0e1801051807090501030c09120b01030b1f0b0702061308070315050114040c1817070b04030b0a23070305070f0509010906080907032306 69
    0x16550118118810308880b8580c03500f4416140d000070007007124401c00080075140c00280d006600c00518072100190303412100b0840342e40e000c1500011504204020a64208000c5084001d041c0517540c065005207604c1d91980c0f900700402c1c0c2c2d0b103144802c2c0c0170500040548010312034a00500c1800100e01c03030980e1207048010414030016010140e101c10b41d249214101694501007101801c6540c5c14007140c12070034046407030f1907116480d4058a9200c9180c3c3c4002c0f40c410b04c000d84503420056880c09107504031b51405100c00c00005804040c400a0039005d1982400c000c800c03000750201081d298221005009065200304170540c44007034052601070903803c50008070700e0034041000014140700c64964080014580405c3c1030403041c520307121a880043c0054600100001000300f0700b035155120520509080da42e050070070780c03100b105403194800c40203501d000444143c001d21055004110340c0703812500d41c800b2a540d80d5584c0e295038080c1c00d805642100b210750050041c880000041120701d4102d100045 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 974259469 1250 974258219 974258239
    0x3070905040c05041802070c03030504060305151e1201020414040b0f0d02060c0a020901060c05011506020705011d1002010209090a05010b07110d020d06060512060c03310b0406050105 80
    0x3d851405284100c05051210014014918040b901682ca46983c840c0d0540c00c1ca6450340342c0035000b50040d024440c00646040000396195901100c1d1050801000d8600d80e0040541030901c0d54003008251110341003551b00010082c10042440200014440c02100d0003501d420718042005403000d0f0341c0300c0e504c00d10010406054968840c1c0c2446486641241c0090b170b100a02d0181c5070400f2042e0002030b500620404c000514560014616880d95120380000c100f0100a1443d1000410140c01000b006034804a41481254000d44040a000860554075080d2f42010000112420076951070800141d40108203c0610700740720002c40c1c1c01500751401441958100b20f403d07801c0e03000704d02c030142081c40c3d40e16455440f902d807180c5040c001070f006400b62030b03100c245003400c0024080b5031160a01400d203034842c910b4407940218210340207841c4441054656120b030400754a004444c078429425418010751031440c54540f1800054021748500c41100341c0c0c0c6410300300101102c0c8141d0215016100d221 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 974260719 1250 974259469 974259491
    0xc2d03030408040909020a030b130606080109050706080717040c1e140103020a0903050d03050f24090411060714070b1602011107090218030705150724110307090504 72
    0x110036141583c4a0361000242c85103071b4000100030141c41e41c000b4000c1c104000522110307041407006400321501601c401d01000d1740e90481c0300d00301c403148007000d000d0341c11450090101d60700c00c21583d0380051503032a06030340309258503031901d001c0d45c0c0948080b00c0b041c050000400912402080358240300540351403e071011840d06040456405403403031b249041560010307590180038086c110302806950400d04940c5814001030014000b00415200710200031402000500c19221800c011504000c0c041d0f03528180c0c21405040c00815038000d4021104071401c081c40b844262103990141049500800110500741e0f16a180c0c3c0e400c04010341c12012001604000c0d04038a5040d40c020081c4159080c80e02d986040304c2a40120309068040e004560507030700004141d860700640c4002d07906428000c43c15540d10f10780d20000c00140440030180c2180c01c00d001e0101c030003c100382d81368002c036031000c000d0b10b035686a41c208402c0c811100030070100c405503000441404042c0341e10110042c080c002c141d5007000904968 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 974261969 1250 974260719 974260733
    0x10050705121204260309010504020312030c0703110a080a0c0b01090501030c1e180b030105010b0a080115051c1d06190209030c0301090c181107030e01050c2d030304 72
    0x3c10103040041c81d04030700340042c0f4180403600b0500120a03809520707820035010300d42c082c1c4415a0700b42d2081c0f05003204009194010b0044034058040f00123540d203003540f15034046d6800c980c0b040c15012640941500f880c0415a514000c02c203a03d030564925404600d01e24000c011650180c1100300150300d05401400020010500402917507415281c50b00015210080d100070b80b00241c00246091030308594924a55107540c0001005c071104500078803c0b60380b194991803042c00345a01c10300010b946400100410a840032036241c1982081c40d05610f04540c280ca15103400902d190a81e8000e5034901c8001d941851a0081003140d1180101a11850a041d204880078002e515a1202c0450340062500443d9804003e88211342e10060028480300a203420711006000306031286810240314035507050220746040c41660071400d40c4483e00d60400e48a500d080b140f43c204420b06505000f0704110801843d0700400c0591181e0010032101c00d00034080341d100f40c0c2d869114160f4581c00b03903c248180300004004c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 974263219 1250 974261969 974261971
    0x1206010b0301090504060902040c050a17160c0c090228080421020f070902040e0f01081f110d0914010212060904030e091008061806061e100507051212 66
    0x30080104a9464a0071b001e00140310200c0c0096115290010983d041600900948558403c2c0d40b100d01340181140340c81840d41e00c02310394400c0c0840300c6d00e94030404207000e000c0c140c00b1540594200110580c58060300000ca030301692000c0401181c08a00001030448072480c42c02d901e400b0302d45451725040ca43c0c0c54031000e510000031401462001400819020320801c101400698a0400c5031034041d91303605114003d601a02030901d003040c1d41070028450300703110f4040c0c074100c0d99080d000b8107032107078510203440040020b0905000ca80e502c17800450034020580c405084102030a9400140c01036851800c20b4010034602c07582c0000b640140031245030054000d9007241d000000750740c1111075596900d41241c1c0740904144035540a0142400d110031142800c10090035540c2504c05c907a2281c0b00c91820203900d40041550150700d070304c1036000032418100402c040030717240344c0d59450149400c0e041d000243c00d020110050800100301090080910404100840440c80c0090446140003041400007000750741c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 974264469 1250 974263219 974263229
    0x6030506060d0203190602120604093903030e030c03010b13020d0603050a05030c06070804080a0302090f06040b070501060e04020d02150c010606200d020309100c051b1206010b0301 79
    0x3101c0b9100340305545043c81040281008441150b002c0700151900710000d41040f640a070715042e0550000309542090700c940b1203004c2d0440d0410700f4441d03c22000140c0b1030380e00401d02c03041c00d000400e10590780d801c451181d400745104e80c0f07640e80150050010715103001070121855110385c0c14104107020f6502c501050014183d040e8030007690724a0f03d900154090026944014101d00c074981e050f400340203001c0090001000c106003a54082d4582840071101101c05540c05030204904001d2901101d00980c010710725074102402141283c6101c0000402d2034005900c0240c14039400250b05040020a02c60400503040c015200101d0381000d4010941e04d180d6a00700a004200180ba002040703201803080c0c80500341c54034020700201da190740000f012072544054005201c181c50428021074103000c101d078810046039900941c141214981042030180c5103140740c3c4280104904400c0103da41405182e40c07a001c40680308204244110a02c80205024400c03a040e58000e04014405891841d0403603044403 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 974265719 1250 974264469 974264479
    0x1a041503050124091a12010e01211b03050106090b3007240e04090f03210501140108011e030611160b06010e0621040602130b13090603050606 62
    0x5041080140c0341d0740010380100841140d05d4441c0c4240d070361800c0040c880c80b0102e10b45106140d0740d4084d4401405000e000d200451180c2d001301030300300e100342c0e40e0840301d0500941030526841c130100241d04500e103190b0401d03586a51a48811b202c00a9540201e01400c901540d884030b0501501d001040c0d2504101d0036003070b20300c920210224600d07000700b105074041d01c0c00781c407100c03040314440102c4c01c1001050320100c0c010650a40140075a41750601c1392802c4c07130707400a4110f80308000c25034040701c180000458400f8000d01c0409480754050003817003500c1c041c1240620203804a0350190001d0a038050503409510000c1121011804980416001c0000c40c1c0d03210703c003c0354400c2551140e00440c002c407912486611840c26179581808003460400380241001c0e00c940c516180d44e101480418400d6600c8020400003800206180b01c505140407076205000e20001070622141006401a441e05684190010040403a0000f204070360440322000800140b0f1040000c1c03807941c0d844649400c4002c0007030f440342d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 974266969 1250 974265719 974265779
    0x2060c0a02120f0c010c0807080f040215070b0103020f12070b030c190804121b0f080c0a0f030e06041a0d0f060b13080f0c1201061a0415030501 63
    0x9030080045074020301c02c4104640d200c0e903601507244465081000512011741c20b024101d00300c40d024805550049030240d603942e40a9807004480c0c2d485500250080340c001401d120721807696682003010709181c5209078100c400d80d500d54010050540800ca010303a11803000c00c03a4a141d820302c0001c441003102c4500300500d403281e0710f002c0e50520f5401407580142140c1114010341030603540c000c0c403407032081c4e1007906400241c51020b50110346001215184144034102011490302003440d141030800c04074810001545005201c04255050107c80341c1d0407901c81140348a1802056000000c16a06c00700583c0d895081502d000c070001070302130b4009078032a201c030350014900c003460703402ea00300c0804e9212004042c082542c1c0e43e038030402c1c0c0d54050035a14401c40228a0041408040800c08080c10090200109100d8030300e4810424504054455464035658072080010035a8006260203201d80c81e480c80319845919160b091195529955651010581350800510154100c00c16059003400014002508 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 974268219 1250 974266969 974266987
    0x10051f03061d0a1506050d0209060403021305040203060703020306010206040209090c04060f090605011809050c070b0702030301180b030a080d060b030c0403020f060c070e151f0f020d02060c 83
    0x1090700350000a10030415401c1152488020501c02e4080c02c0d55520401c4101455031040d66280600d01400340040e2003003041b1036809419030041c142c1714000a040c2c3d86040d59030740c00900810100c401c400308640e202d104100661909200031036001140b814150314520380300c00000e4417220010002840b0320110000300700d145404101898031902d01800c20011a6191024515041d1640c0300702108681002408a03a95204120b10320300749041030100c81806080903481c201134132005140344200c0b00309100d654045034200c100c0e54007800b01da4024554039414464190f80769902d01a46c2c0c3da5181c100102c000954900040481c4029005421980c540c0c1c00344a0040c09004903500c503010b0580e0101c18441c4a500c680000c0080341c0c4200c0311841ca0f4000441801350702d01503ca0b030800690441141080300d1203182c060b40781d100700c1084c03400c0d445001170800161540f000c80f4495042d244c048100100c040d23003042000d0702a003250300050100c008080c80003980e0302ca0042944000d10700c08100e03460 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 974269469 1250 974268219 974268221
    0xa14032a04030323190801081902210a0f1212111204110d0c0503071a031801060f26060c07081308010e0a06050f161b0c170610051f03 59
    0xc80d110400030f500d00c070170a143c0009100800c00e00800c0c6040c02003105c4c05080d030402088040c0210390180c000d00701b004007008017002c9190f151440400500843c00110001411040c00c089140d2250148041e68001100e008180301c4a203105445080e1a0447c903240e4000e009042c4c846103010011243c0e0107542d240391510b000300c0000601500030b44071105550410400e0b14458040e150260219100240d468884d01e0000c4403603000400e65100c02c10129112800700c0100f0030448501400104141e0368400c807d1224070025405034070415088400c0c2c01458054055101d03070f8030705160080025040007003202c40315114541d8001d0400d080000c4110f41559400084001040000d000300320a0045040c840c1e03c41614160490b600d03881c16000450b10030200081e640646042411003070640b03001481030300c9444610051000100210074200001081046940040c2441d10051260710021855161400d00040c0036042c022405800500c041e03240c2550084810720b03113526083c0304059000c000d030 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 974270719 1250 974269469 974269477
    0xf07110307050a09060e0c2a0c0310050702010b0f06030619030204020301090c0f0906090b0d09060e100b04140a02130801020f0304121d060a14032a04030323 69
    0x1a030061602c2d80f0000c1c14268641c00b040480d82030080420b45a80c03140c284030300c0341c0b090f090300408801d018041400f109a400004c6413a800094080f40c00c1280300c10b00082c589000d40001c0c0110035107900801c41c09a6080c005c40541d00c600765070508440403840000762482c04010403042c0910409507600588494090380d490040d90064400c5503070756103032903100d40070744070244903500418095034000390024860461401180c80940d100e6014a00340007807001d0a40c4010a1843c0d150b0b2640c0d09640491820710419040c00103040051614070140d0001d1010340b040781070f0307840c46117251001c484800d48403450f5443c0c3c0f02540110041e0f6402c04007518240c5820325421801c81584041090308000c54504021030246000d050703980402000b0302001c80300303a03880049941c1501d03501c200c000010f05001e80903080500d024241714454108081c60140d03560000c1742d0b5940390010002084c0242c1c124020306006024041d000540350604584018045c11940d0580d0104694105503520301d60b88035400351 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 974271969 1250 974270719 974270729
    0x30318020a0f050a1e120f05190308070207030804050d051f060504050a0605130e0c1c1716170f030106050304151806021614061b0f07110307 62
    0x100e544240c54a9105000b59003502541e40600e000c01c8000c1112481ca03840000103604554803400c0d503604100c2600e80e04038581e0000c9460b507000001e008000b6206102800300410301c441c0c54800480e16080c001d00c00e0402508801c1550080780d0140082003000303085800396003094582e044040c00c1864168070b0403494205072121070b6603404059003404c0da0b6810920807038100319030621007511803104040856a540c80381a50010b4026803800d5000800c3d04900c80b00c0c21050141c4000b0b10300f171004034100c001c1d4071280109090521a540c400c101900340c00d010400d004100c1c1506141e1580509030034410b0445002d05020f5005020007101c8051078100c8a00121042d485c1e40ca0f035954a5014004d5042540d08071100306030641c285900d01c402e8400c04481103410744070070014030110b0b00c1d0200254007500401d80d60781c409904280c00308000d0001403c1030380d480c200819291800e0202040c02050740941c2241806003041304c20100303060f01051340d0740503400c129a40410f9040340002890f0641640c00 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 974273219 1250 974271969 974271979
    0x307020d11162603040609031211031308011409060103020d0804090c03291e0d0206030103030206060108090114160509041b0f02280521030a0b010509010c03031802 72
    0x40460450752005068110a4422120003540c015803601d854407170003180100c0001030400202000426514080d055400c009401c080042c1040c0e02001421a40300c0c480480c3c0d843c80910041110304424418000314036610082d0308070900b08601441d031600018803001c1e1245441249a100b80844007088030018100c445080121a03d4a000540501542e90812038041004280c0b4041084522245290640700401826100c075558004021040c181d1a1598001c00c4208188006803206401540a18042c1e0014012440c01600041c512680200251216410241c4401c0802c00c1c43d04015000311401c0c1c240850301c5416070003240c0e6400703001c2585a21030b0501010540045d01e00006500300f01e05a520f800d00c29190b4501640e5485943c11038101c18408c3c50240d2002c841e0200d800c1051522a40a480540902038903658080c5003818070711441e120300009000030210719100d0108540d41c203090882c2443c034450006031000c0d00c0b000300a0241a1201c00740c200c100f036802c1004000301c0d80185 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 974274469 1250 974273219 974273263
    0x10f0215090705150a090905090717060a1d030301210203060f190605010e100c020310020903010c032d0e1204090501080316080d0603080409150504020307020d11 71
    0x741d80d82d1500544103180c081d41c4000030440e800c80483c0d0448107143c00940b2a41101d502d401c462178014a4014800d0045000e25080480c1060605412160709400d00d4028041c90600800d410100d5036850501200070807404021003554201200341c90440e161101403152445600c240c0341015496401c000394540030305010080c0001002080794050300711000d099040c03984180e40704084404031701880c3d0200e00c101040d14518a80700600118290113882c1074000302407a42d010030304d8505d044004110759500410f505010b030909106200009a55141c140308921210301c400c0905102ca000404183c50b0780c0c032807010780d40c500d0b800c1016075a10583c110307501fa0560050001c200d80007401500d80160074600000b498940c0041994600310780c150243c05012466a140c9110340e00c9469925123142d168140000070490340b5026100401b0b00c0c20020034001601d525010080420341c00a80c407851060003488905680000c401a903890141050340c80304524507107141c54024096640c091460360b0007 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 974275719 1250 974274469 974274481
    0x140f0a030e0d0801081e010f020f0304030e040b0d02300c03060a150e090705040516171506090301020405060f0a0212070b071223100e040c0302010f0215 67
    0x290008102203680419038150b074003116000c03103084500384600c00301940504400c0701c041d2100c0c0e20907054504460000103e030700850024105a80118821017001800403080100b815046540d1844061088808019010361000002c049500110000e400341ca10065000c00000005a088902061001001c004c040e503070310042d81d640180c6440d25000303005800101c0c20300c151a000f40d0300900c0850034083c00d11400c0209504800c5030080c6010703440d03c510400040d071616144560360103500c840c4065590403405800c0a0b04000660ad28802403120300000c00440422801001c040f402048031101d035a05490700c00280039020383d41102d40d100704000f0304108030340c00c0800207100507401d035001d0700e4120256140013020703801841c1c8040d1810341220f0003c0c5e4458403910744d00e04011180c0c1e00004504803622481e02c43d22041c1084442d000c0804010301ca00c009181031507400074800b0307040464082c6419035610039429620b00c8000e05000d000e00001a049000380096030701c0603100c06c1c6003002450302c2 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 974276969 1250 974275719 974275721
    0x806180f22380103080703050c15010b0406030c0206240f13020309060f0c03130212030304050a1104150b0c07031a040b061503040f151103010f090b10140f0a03 70
    0x2c0410708880d003141c850300d4a0140300309954504a0360001032443c2080303040e4038240c81c1c0d07602c0300c81a020a40562214404c3c0440b482952601825039640069103c9061000290450301810300c2001950701c4041040030303003521b19030294040d00f204800034401041c4180402c1540d003041c03191651000c0e030391466882880d1194080c40c4142110b004540003034603000c440b11729410099402c1441680b040000031014400350003518412032010780182000c2005d104010b0131a0410b850072112a00300d0f90f10b081c2800700302c03c50030b0b00a3303a013220200440e00c04e504072038040072410f2290f100c07400b0000ca40c4001e07084080c04110000c40e00112151000340303699404d80c10b003020071103089502e1031404000c00c03900d080510aa1017107922012040b031941c3c44e01d840b0121319440201080b100c0b114141806180e8804c64000c1c0d400010541c40340c1c5850b9410114145404c1d94aa00040d1510b403415035200603540c0c0d010402d424034411030924050030400c004118000b40700d019500022480005105a0f506a00d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 974278219 1250 974276969 974277023
    0x29190e030a02010e0c010c1208090c060406050d0605040c050d0e0c0423070c020105040b0706200904140f040b0a02040b070b06100e0f01050a020a0506070806180f22 72
    0x84019902d0305d21015005650f10078804902030040f2320704810010815006049040d004092081150f05884003000001d140d03a0003500240006800458070208080c1623000e4031001c2c2c00304840502c100720150000500b0b83c0038045180d400c050302c1c0e0800041902c0d090141c5c50007420081c005000700341084034030410540310a21251180700e6180d00050f0701c10321458070441c40c55416511949032524040801d55142c1040c00241c0766207603603440c03c0700c00409080c3c0d58801d0007140000562900070010800c002c030f8080f0a00d00c00c00c0710180f02046440f071451407450340e02a0f4812005402c94580400020003400785802000381c02d0b50020b618000e000c01e4100346442024121407272400340800d02003c1714005038000007140c22850000710628150702400c09800c4c5030256204454100402c0e4554a05d403800941e0620301084141c005d00006082200351040040c3d10148500f0180c00c040980c0d0b41c0c005001068009091280010196020880640048040d030040d03440340180341050038505200c62 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 974279469 1250 974278219 974278241
    0xd090b0402010801170a060905030c0a06050a06050108090a02040e0a120810090b0123090a1205070806073905100c02010605060403080f042129190e030a0201 69
    0x81e0700000040341c40079500445d02103101c04002d019001d549a031001c002d80011030084803240014860f6170110725040103d6641d060081802040c00c3c28440032400031034032150041030400440a0800c103484c5000142078030728070b034103a40005801d49680f41d46030900344070100c001c1040c41c603e1594195103612144440c080c440c0f403480841c40b26a520501d00849002000190100d40c022059420040c1c0d00b50364511001c000d410014070f010030307101c0050455101c40e04852030f0703603450700341480a002c001c10450020303014140080495003031181c4050085800b013646110150309448400100c101503064120500110307040e4031078203030041d25149886000144098029504d46019000b40501c1402000100d0b04081c0c1500e02d001c2c2903072a2420690720051b408000d6820400c0006082050640401e00c01390301141c00c2c0b2265181807520082d40042c1c0c8505852801e10240014601030009003075680040300d170b0b190581400c2403d50050082c0c15046e9580c4000d000c003040d052102c94040d00f114010709 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 974280575 1106 974279469 974279477
    0x3090c05030f01020d0c081311180f041b180b060403140d08070c1a0402040e010507091703041a13120309142b02060d090b040201 57
    0x70b10b109000951a07907000884000c0440d05128107968401b9500e03040d0001d00703100c20050340201c2c01c0301c0060111b50710349082403003e64030090078612080704a6043d82107441e14600e80d0014080840341070318804800104010039041000800c01a106001c010440b0740c0b05049070b2100406810700e50780d8210404100110110f0b1800401c04640d030000d84c0141003001d1080d0000f0144030b0050f002c50309000094800c800001c00c0d078080848940141c18160656982d1800000c014240003102959554640001d000711640c0c46012a4141e0351110250040c0d8500c000401f41e80e84628400c070342c20814802221081e960807100188040c407000b01260085986580385255102d860780c0040b4007258108904005280103003101c801c00c80c5048520024003260303082ea081503003008251880900859199503401c55441740140c44084031051010841c400080ca0421544001640c00764045 = true := by decide +kernel

theorem cover : BRFrame.Cov 974100719 974280575 := by
  have h0 := BRFrame.cov_init 974100719
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974100719 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 974100719 ≤ n) (h2 : n < 974280575) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
