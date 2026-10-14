-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0049
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:33:35.785374+00:00
-- url     : https://prove2.me/submissions/054d5f4e-e5db-479f-ba0f-a59287f694d5

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 8633100 ≤ n < 8812956 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 8634350 1250 8633100 8633111
    0x406060618140301090b040c030203010b01020d0f0c022101050601030501090b01020c0402070819050a0806040501080a02090421081f0e01030b04050c04020304080a02060f011503150b0c030c01 84
    0x910a854104000d4000410300600100c20010003034031204a02e20b42000400004a1900945c2c59441c808400e80e419600c0d104440824000c6040904c01c41410140900052003150941d00d0010060440005082c08000c0c0c3c3c034815208644139040482d620550507800c031002d405062070200e008050031074041d4006824907000090b030114a00c500d000000c0103034003034540700c030080007884041d5000312402c64200d0f4041102106169200d0071000c103428099403426541c0089a4004080581c0030745164826850540100442c000000c9c5003001c4543c103503039114841d901c3d802c0005824003a45040152502c0d11a12840040e60281c030303140c0300354820305015070201c003441d0007400000054000d03203111818020041c03000c10150023040741e01c070788540d080340c0c20100341d900410300341e810585003112094004240720030a1501845580c0d8032200e42c84002d142d940c9400c2d400240401d8480c0c003a004c1c50759903000403d4400c1c4090388036019064068030140d0300c440200e0010382c0c950100000c00c0d000d51801c2c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 8635600 1250 8634350 8634359
    0x906070302030a0305070e0604030b0912040e0405070e0f0f040f02030601090b0a120b0c0c0307060204030b1905070f0509030109020405010806041203051308090103021306120c03060b0703080601090b03040803040606 94
    0x20301f641d24101d00090070003400d050556442900a02015051403003520401c007034017024412400c000d1019180140704076802d420140303045032030042c154000c28400903041041100c51404501815884810703c0000c0103281c4a6040c10010703402c01d045c010303415009150012034211200d4001d500c03c000b09882d4600040e80d20000760041d030070302c0c41d001050000110041401c2c0e000c4a00900440780518098038504181171fa552403c07a0b000d0381c8100c03802220a401c004c0b84940c07440c51b80862040d040414007151030306520040000384c1002201003071242c0414000c0c880c2d10f0940c002400594080d004100650315210119a140801c40c4e013181c4000100c0007003201180301e4080e5900440050380410100d07075a982d201100b0350002d404440c10140e01b0710140350032242e4041004010800764564540170005d54003007809442004002000b4541050002c04c40110203c0803507044681500e0a0303280d80c0c68034401220f41031303110751000761005c0011041c08144000e5400035800703248500c00400c4013580c0d8 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 8636850 1250 8635600 8635607
    0x105030c06090a0905060a09020c0606090c07030c020402031003020306040b090c0d1101050f2703010b01091a0d02040308070302010c09090b090601080903040b070807021003111803030906070302030a030507 90
    0x42c480d0980e001800700c00d080110040c25001282c016800422050b4035645814140040307821030b0980507a41c3e4805002d000c141d0618031411a04451444030710341ca0039403561000b07004401c50800090141ea8004005108402c48140140107558001c00382c914508042c200801440c0c4150751805081c007034014850300502d8603440c04a00150710800704040202040010f443d19004181c102c1e210150400002d03c504401c60508001d0000c1040d5094011120031706240c211034515032000c0c10700c102d200c81400381031030110303084201007440c00f0829901c031030b02d610f140003030b018540c002411090081420310402d60190000c94a180c001c0e9101c140b0389a4400801c0140d514200a81d90003619403804504a5486141c00d1540102c1c0301d01201d117400e644004c0e80b561644400d0081d00c103d040410304030300718a00300714003106200705450180b10848429110041d28400d0103008101c0b0846002d0003051520240140c1d4035101c4018400c503100c100d1428042d40382c0c0c0c44402c1c4400001c0c42c250000f0304d0b0a00 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 8638100 1250 8636850 8636857
    0x1006090219030504020315090a05071e0b09040f02040f18020f0d020901032a0201060801050708010b1803100207020405060d0302030a0c0c08060901060602060c030103120509010e120102030105030c06 87
    0x34125402409070304500c416802094080e00503a05030040d411101107001c40d00c0c01850184180750024000c1d00d0207170a09030705011054020311032103145000c00c81c032641d6904108100b542d041e80c01c016540c5030010000341c02000500c1c0444515070010900081040c0448032220480340116550b02a0421040d043d004a208070301e650b046680f41844410410103065014000c40e0006040005d8680f5811f41083c09480d20418031611184560307065070011503083c01f801c0000d000c020020b000500f080a00640080c07814010310300d610b4000318200c203d4055998240c1d51284014003074a01d41040d05040340c029610074070081e400361381441c001c03031600d0404000c107820036901036000e10704082c0001c1d011101e86540820a441140d100c65001c50822000c1c84400e002d2603002000246007480c004010341000b00043c070b0000554801c0c0010408911144100a825004ea00c1c049070354261a00040c0c41c9101d0038455030790000120382a602011505600441c140d40b000c6007240c2d01511600100b00c024403 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 8639350 1250 8638100 8638117
    0x10305010e060a0908180409050105010b04060f030504020306040206090d060c080601030c0807020c090c0702031225030f03020d0e030313140d120203040302010212040b01030c050105040e04030f03020405030304060210060902 98
    0xd006c1015044445841740034a000400082001c03d10204640310242501c1080e040102c1c1d80000060030000c00781c2140900d01003a8082c00c0032b1286207099000603845040042c40a80142da000520029554404011184440d40654204103554407808014070f140d5044030082e0100e4a01702038100e8990188502c1441a0700540c01081d002c0d5100051110902d40580fa890000c40103000d20001a54244003136600d1031010f6032125110980c1da00160905003107034400103800604d64074040c0104e54004043c9a86000d141005640c40d10710340004c00c01000c1500b4014800c8c0000700c203110030340700b880742c000c04800d015420a00500b0002c0d0520340d04c41810515a4001c16407141c100d0a800d0001c2d0042c40d40240640001800c2110f2a0030758443c4200440c0c0c03c0324408008001881003081c4040c1c0030300540028640b240c1810708140114607080009040542406001c2003003003125071281e01194068400982034076115943c2e41c42c06035035010f03d441d40d080c5481c00d110001c40c0e02c525500c00c0c3d408a1 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 8640600 1250 8639350 8639363
    0x2010501030227070e03031605060f060604050108150604150c0204050a05070509040e0c1915020607050d0e010603021207060905030309030a020111011808041401030c02060105040c17010305010e060a09 88
    0x42e10386250580d5803080c030405c2650140030a10a10301594070980302880e00da070217080600400e1401c0d00c030f030b5050664001c0c07450b8070400702400280401d0360f0089480740d014405000d103005000d1038400145460203181c0c0041c0400b030308200e1104540b40d00c42e012100300d40c8281c034180400c1d155407048000b6140d0441d00302c80041c00a0040041a01e096000460101c04080607030b40d06c040d408011a0340110340c3d41601003081c04510040125486051206640040d61710207031100d0700700520010078500c280414080c2c0241c85000c09840600294000402580c1c000c0c0082001d0201d50100c980f200201c1c400e010106400c0e11300000c00381070100844415280090103070900d14160307801075a02c184050034882540d969585041041000c40090581260054400c0b91701c9614200c1c20103c2c040c05080c6150406080010303000c0482e800151140c1955001c4601060703915984804a54a2001540507101c108842d000081400810350200c18210300c00310507130303c456807071941c003038256001c451000744413 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 8641850 1250 8640600 8640679
    0x20f04140904051b01050c011103040c060c02090406050405100c02010b01021501080a02041e0501090204050406080c01080a0c1407120207081c0f0509130b01020606120309060307030b03070303020105010302 90
    0x200041440344c2881508141081402c019000041c0ca003103403082d840300c000e0302c03c0000030320040c0521800810028881440c000d5080c0d403503a40441c14111010344020426500e84c40030030100310007401207a03030301d001009041100000580cad000380600404252a405030180400a20400404510280c140c40d04d410060404290690a000c01042c24943c410000700460b000461420080d0052500800c0f4807440945c072136040600b04821140d02d54003003007280e4040e05910a590741c206540503070001c4e02c60000641041280e0701907807800031f998000c01580000041101c2001081a000b980f401155422284510b0f01c56100c6680d80c01070300d0b0240e074441c00001e2401c107803e01c03030441c440d080d19061404906068501011a45101c06285c820300802d440e205469102d581c100000c9600801c22507a98038000b003601800f035141d11901000d580101c80000000d103c2a009401a112140300542241c403001e5483c10001c4c0200000e0008034403801401a40c070350342c2405006600741c02c180e05403c4e140d4 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 8643100 1250 8641850 8641873
    0x30302060609040309030f050c1302040608040311010204050a1706070c240915050711070501090b07020a171b0d0b161404080706030b0402040b0702010c030c06020f0414090405 77
    0x42c4100014401c4040014081001c80004c00d0462002c400911460040130003144c203104200001e08855050303083c1078414441041420752207150301d60040d8050030221890110140c001c0d01a114503001a034101000340c20014150300c4415400300410070a000381da030141c0f02e509089840f400c0d40940a4849580e00050baa01e030000102c000030b100c14035400000d0035030f1140e6260381c4680c170f900c440c0c40b1000e591442001405d0303402c5a00030818200d0704025080d25803d000018007403214a0042c01c0c03240c8008941e0790110f44451880308003500f09240000c3c80100e90a00d07481d03642e0041005081c8038041c1e002c00c8940f0703083c000c55050107140e1105000d00c550356521401900905115940e80030002c0454003142051031a0005001414081c1e0141841a08090b405400c0c2d450440b50385019501c100020880d0454107415294981d50900e40480ca58200c4e0804698250040030701401c0350b0f01c00650090f851070307540c00400454100740184c0100c0001142080000c410880c0c0140c47c0e0703081000c1500703 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 8644350 1250 8643100 8643109
    0x201061521020d14040506090d0807050c10050a02040f0b0310030609020d021306090c05040b040e07050c010c08060f0105070c0603110f07050c150408030a050a031d0601050108100303020606 83
    0x1003900408800040c20203c182c640207081e1036245070303c0110074003003a007880180402800703801e42c08840c0c94002d049040785080010440c2d2300c0140210304004020a078140410b400b48091591468849401d0006080c5044000c00070351240c0b0442103811013060001418014880036a44503a1306004401051450342d12104090881031382c0c200c0e8030414010311540145e88000f04d01d0070000e607220b80003070a907042103021012500050208018860705010812102882c402203500b41c0e02d002140980c41e46403104c0c281c4847c050480940c019509044404a6007a44018203501c03450080710740c1d440d0386003400010341d418841c9504c080d02c00b00000b08107102c52800380d0400f56030000f2040b81c030340c900140c584980806030402502120240c0003030306d2050f101c0c5030520030090bc0c1d801c1000c5051420385000d00d195aa07120f0140c050081c0303e0701241c01074805000313038030010680208820b400944024081c1d4103890b01c1003401001d0100700894007007500284d004080100741d9505400508054440f8402c21 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 8645600 1250 8644350 8644397
    0x20307080a0504121a070e03060c0d0b0306071106060103020702011d1309051005090309030601090e03040b0403050f06091609050a0b030a0c0905090c011b0c090203010b0a02010615 79
    0x70034071008200000b02c0013811045540341d41e0082d00d9104802c18001d41340c100010010f4002c1c81042407524051005580219180b50044544208559540d18085102000c0d0440f000304a030705014600800100c0d64011111050b080b05020546059039a104010740480c01001c0300a40000c1c210f506501c501841141c40201d2030b0001006113240142010680040d45c68080040b5600e80008121113401c100c54000e680c0c01c156124007642c2050080d00c00300303680c4d24052180990301611a03001c072001000500488000e814621000c1c1d40e903079202d05100c2e80d5109803410b248080e108000c0058032800d40420810542d80d226030300c440c81c441c03910000d40084d20300900382c103801da40c6c0c400340c00e81d05a5042102e0130080e8440c40c0880c044a150103071040c100d0b40c0041c166402a00030690030b10b0182e030310081c00500049045180d035000a403500b0986007144003a00110641840000042488030801f8050305110324242d0003030080d03035261038050703801081d4030410f40f0100d44c0b40c19012402001e201c512 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 8646850 1250 8645600 8645617
    0xf0512010e01020c070e0f0105010c081e0d05060f09040305040b1b0106060810060903080405010507030201140916060215011512050f070e060c0717070806010f0510090602030708 78
    0xc5111181d140380542268400154041240c0c48150108903c80d00ba01d9000e9100403106041a469072400c00083e01c02e0701c2c901c00c01416220001404000030104039078210800d0300c054940c2c1c2d03c03100103d034228003c003400d840c40c0f80315800f566a18403062502d4014244510b5040d42c640381454504450500039401100201c50340300080014200c01c0d40092054200410540e0f50b500d1050070076101c811808070751034110b84104034046100f8004507045404480468400b883d1040d0b4420311410304070300409035240d6040c400110b0320244000004002007601c203054820780000000c41c0c0c0c41c03205995a03007a1109054000b04200300400090080e00800a201460790415030048402c250003e4100c2d070b4102d0700d4524502a410504c0341c030650290200301024000d4400703501c1e20a8203034580b680c0358044c0c410031400c0001640051049070080c400310000f082d09404451865031a407610489400711270144602410885040e903c10510512601d400c50300d090300510310b40b28036070722280c04075400941c2 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 8648100 1250 8646850 8646853
    0x60f090901060305191202070602070605070804051c020108090c03070e0601142205060f030a051005060f030108010b010924020a0b011205010c09050102100e0109060203071205060102070f0512 84
    0x10b000000c9002801045010301d11400b04910218091400c99044241c85801d07604660140c0d42c00e00030143c000800800361011414036070749405061030130038524070598016075089100560000c843c200250480b0029601c02d80741c0402c03a0761085403c681c2e521541480310f61644c42440c0c10000184c1c1c0c0841031f50000c0040c0f600500510064031041c0e0f2950011146c80b45981342c1100950305483c1d210144400f07004101c4080c0c0c60480e00364030a00c400c0c000900b2031210030742c0c0c42c4042a00640d45580c44402450f0281c00d01d0b0301ca01d001d06040000b9002482001c4ca1175013000c14001003980301c0d035403002c1911003075001e1070b089612540641e907a0740300796003061040d4840c4600a801107a11510064001d2010400303100030301e4140e1800343d00303468100401106200e030012051200d40c0e0007040800f60600d1780c50000541c00e40c483c2031140584506440504294070010500031080d07405810bc48001c0d541c9682401980c8400c401281d80c0c102d14801c00ba10401b10030b000303210a02e031103015049013004040 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 8649350 1250 8648100 8648111
    0x20702030604030903050f060106080703022a0c0405060a030b180c0301140106020c010201090803060f010302040e07053c030403020109061506110c09010b070503190806090f060f090901 81
    0x6012a2811006480543c00b2502011080081000800c2080d018141360b1003e8020395243c0f01024001c1000609070009140d00880c090104500c0513840c00851501100074160b141c81483c01d854580c02ca490640d03014500b82400a64281020b8101a00712136001c18100101c1d65501164844800d03002c0c2d011000c0e0141c01c042c1645039909000d141d00070b0818040f407000d41d524000e00a0701d40360896031305d40d0640e418100880d020510325001e90340d1000c8259810710400c801c04004800078400d98000f4a40703014035100b070040c55540302c40640000e01d0440032400c1c0380c141c2c02215003640e158000c0403118522070308860644010340e410156400c07502c64000444c1c00801903950005440c1d101050030303c1640c2494007080016440b4550b40c81c111520409025001501d00106e82400d41c1401003442d00840000c00d4400c10504200321100900a2400c0704100d001100d00244005401e680d080e01c1215520b01080f00e05012541c090700580006000c030740700510311070500001420040c4114025541d41 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 8650600 1250 8649350 8649353
    0x1050309030f070b01090507030c0c02040b0307090f140105010c0c030f0201030b120105060301111206060c0f030f04090c0305010602031605010e0102120906010603050c0403060f1806020d060501020610050904060207 94
    0x30094902c3c10300c03410345110340707604045c41070b022540010420340426081840000f1001c1d0080001045940c0554020804459034400f00e40740009541c0300c203840500e420309843e01849160b20100c03e911048210b21141d0b42c0c0c4200460309044241000f4041d0800ca010410020742c40350320f2400182c0c0306060100e8001050800244115984000c0103020394469040101360324081c4100c000542e08140340354240007100b00049003044d4000c00d440d001e041c3c0080d0031650140c3c104429245070000904890799181c14000c800e8503600584108509181402c90301000701e070190150318182c9aa0364011800e00c4038540d14981e04100300403013074410303542e50010070300c01d02c900f8001000c0180c4051507000705818114101480c201059000701c003010b20703000c113104041c42501d0440c0c00b03e0b038000d0008555108000620030081a0f000c007224840748008840804221468010300440780d038800040040c59952401a41c45a40440b0301c2d13417200c03841302301c21303c441d2a0119a036034003d40210801410100346 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 8651850 1250 8650600 8650627
    0x306010b0c010b061b060a110703030902030a08040609030b010f03030f03150803040f050f030c0306070807030b03010c0801050909010b011b0602040b040608011a040b090f120703080c0d020106030807020105030903 93
    0xa205c801c00254070f10140350700c46041001215000340303c06000700b00d80380781260803034900d0060110003010503032034540c1881950340c00c1101240ca1900402e82c01c0c0d8503684ca1101410007000c41c8002c44501410360000a03040c440160380401b16505921240c04501591108030b00428040c0aa040415200340020955030401c101500141400f00300d030752265420001000603104985080910907440154075003c2a01d01140c210b810240350304000c0364076154900f0550161000d4100a50590319011441d280d003580286500e0480c1c00640d803585a0f80c03100d01c001c1d801c1c0c80e002c0240d140441d402d00780600d0f10000c0241d9034a6042c1c01100010300781601c030000042d02c3d0740190710084c001078aa200500c12240d40280010440c4206038070f681c505840c0120640d92809441c080301c0c4201710380d003030740075140d00d1300051080f800412905a58045840e4030f004816600244064400b62041242450759140148a5401666000343c40b4900706041a401190745520040030302020740400c5c480900850071 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 8653100 1250 8651850 8651857
    0x50d050405030309101109040c09080d0c120201090302060403120e031201060306080604030804061d100e010c0201060806010519080a03020c0102060c1204021302090d030302040305070b090306010b0c010b06 90
    0x1041d80503680d00e0400d48020b40c98285940050100c052820000c0308108602008641c140c500c06d075000308072010050025500c814995001d0038003405000c000200955121554901044c400c0702143e00806025408900306c0c0caa0b00c800030003507446540801d0102c0d02405207842c41c070313400d8807021031203a14420045055801c00003042011501c86070051081540601803100130b40302150041403e031920307807001000d002c00500051b03c100d9454040c4404042c081c540440c0094001046400c1c1c0206841d400c80103101d80050010b00d5403a2110302d0f401c0c5403040c0201411500540000c01950b401d05003084000000801000c01c012424200055215024005101007600a0700900010188030001a05084c001001d060340c070001000b40c001440e100c400300e2031b0420303019103a000c1c0c1844014107440007803084820591744400c0301007101040541c0b41c0c0042040e030340321b40c040c2d4460580d52500c41006008950f0502d50540007a001844101881d101030700100344a03d00100e4490361080c0400c840f40d0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 8654350 1250 8653100 8653103
    0x30815040c0306031106030c040603050a09060c0c03030605100504030201030203180d1106010609060f0302090a030b0c04030204060506030c07020913020604060f0f0228060908040b07020901080102030606040e0403050d0504 97
    0x751601c0c0f080052181120300c3d920506800d132400392540c640a05515141d1043d4007c11040c995a040811100100c9910501265502680400c41c0100240380945000d04070b030400c40029041400118450400190507001111151a014242411a40103401170b4100a08903d0902b0580d40907004030700c410008171011500b140c68010a80c01110446800c203501604540144548a40200302190740920755003201803007840c005858481500010728007803540c1e07202070a198590303024441c0442401005104480c421541000016030301d01c00d12010b07002c2202c00350043ca109020714005400e0072000c59901c424042104444c038907a80d40003a68580191700b1860015090101204541da00034944295021603400200307032000b001c0041072008410940000031001711554404200006c0d60070030050140d010744925150f60710351041700304035041040c0603803241c03040c1800040c0075070041c07003101e015072805044d00d4036081c140030303425004803005082101088810041c11008138401d104e4103020741e = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 8655600 1250 8654350 8654357
    0x20402030103062a0f140c0609010f0b030609030a0c021503070c030917100c03020409020d0b090c0a0c11010e030f01050103020a080c0d0b0a02040f03050a0b1003080304030815040c 79
    0x1c8091310071030a80039000c400d03106254a0303c11595903900303402244072000d00c1c46905e01009503500d401240001c41c010710030503010510500d400c1c000110010340007441d40140038507040020031210401c15940d400c00340c84108443e0810006803200303a10600e01401d0071070000d400d210f9500c404940796201303507204584000c00542ea01c01c1e20070415034020307210030003400c8900c01854007100180e4030380e842d04851003040f11419038850300d00340b085000c1d07010f8400130451000110340300c6401c202e2590243c41112684d0f40328004000001d84200c80030016078560280c140e4a40381c8000c11aa10b41d42c45521040e281e0f03050055407803844051703aa0030415042407120110000c11706514501c180141403005d904440f0490700b16071035814503601c42020312152240c1184c12400b180d00c503030710580020300c110741004900c4031244901200707202c8001983c1c0c032041e10134149203003140e43c0c64086603064a900c0c040100002c5081002c076004c030f482900720130780001c0d80f00c074940d005440d0100010b048400303098108010 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 8656850 1250 8655600 8655611
    0x1403070803030a0b0108010b03070e0d0201030f0c200706020607050703030603060204030f0506060307050102030909040f02030a0b150603010302060702060a02010605060c01060e0c0708070201080903040509101404060503060106030b01030902040203010306 111
    0x4550344814007d00400c00180d1060450402d404058500c0c101071f240c2a010341820750a420030342e8460b4004c0686442c0354030080002440d00c8000400307031120420128000f18518400941d0900c4c000b03038034004c9603d2607020741021b0301d0f03400b011039113a0b0100c0030581c20980c0390300b404070100319144000e0000b0751169203004105512441c00034141900105000c0c417a42005004001c81e07600030040780c0c0f488208444d85161a9501c0c94031100c8000c80d404069094420b0403468006c201101243c1c0e80503800d001d008000fa6918a420030080b84400d010003900014140054001803c2502c0903200d2203440f40004124281c550b03021403c42d030050203501d0b0b541da4661404020340c20300008855040400c070034040345012115216605148034106000341003150001c00100c07540e0052040c0c4010f440010303c01d01c400d04000c01c0d500381c1782c00f00707008540f40140da2214504c6107187ca44111401c581c4041d002d04000d030718003d0240c00621040303249506150710384501c6401603495100850185200304400145c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 8658100 1250 8656850 8656871
    0xe01020115080d11071203020a0b0f0108030d09060212040c06030f06030209150102030c0a05150609041203020a0c050709150501081e13061508060a02040f1403070803030a 75
    0x399103001d9140c4590401a1505000100b8081024645a00760342030210242c00c0903144107240c04480d5111044003141401c00c003040650101d200c1c104d0724003c03504441d01d81c45080c9003107019402071103205981d5000304030080d40c0d10038640211444a008800040c14002d060800c41c03400340c42110119810026030409200c9c140e003510401d00c002c211018204141411a804a49514009842c5a82010b204440030840b42c0c800c00c00c80b07000380b2a03501030702c80c50301d0245031580c0d81e00c051500326501d4005c2c00340011418104a05034500c0b854012404081310682c40d07006500940c000080b15081125906c0c4440106008010311401032940842c0010311000d000400e02550300769801c03150421640b80d080c41450150400041980c1111420310700c3d01d0b0b255038407440c00c9011214402402d0a0801c07065005440310449044203d41c207010a4038079039983e08014100b2071085026a406004904405108029603055001d04009010b0300b05d0340040e456440385851500225841d8040c282c03101402c90 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 8659350 1250 8658100 8658103
    0x110f060906150a05120a02060d0e100b010f0305040309050604030308010801050604090305040b091c08090f06090102070311030c0301020301080d110c13090f061503050c0616080705100c0e0102 84
    0x5034050b9105494540b80c48026001a051141c103201d4a0710802d41850281c4124006201c291509940101a6903a80d989400307800081c103405144444a03005400b4045560031050040f21513001c0143d40341880306045c0310066009140243c415030800210303000c00320703c50712036000400c0690700079201c0601fa58506a0403e080d03600c010105801a4184201c00d00007070380020503034094030140c1c0720701511652000c0220f2000c1121002d91000e00c1c07407140c28182841501c0c401807000c000b094a000704403030200c0d4140011071090506003401a4030004040010550389403ea04007110300a041e240e2001d50200085d007641c00031380102e0303003c2e00700d89590f5000c0c64001d60360340300c3d4180200c050010940810001411408520891181c5a45485900003007001c240304202d0303101d91102d0104030021903044501420091400120740601c5036114813105440d100d8150380c41035103c403c07519113a00c050340d109030058103c0d05040b6003d12402c02d14070000d40d660700542100540170780d40c80709100c0c1c01c0d20009 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 8660600 1250 8659350 8659363
    0x507020f06010f050d0201050a0212030c07020306070201060f15030209030f0303090706081b0a03020c01060311011404050603040212030f0d090c0b030f0a0b01020a06020d060f08030309060f0403110f0609 89
    0xf43c0d6140000001000180c6950030b0f03090781c054090805544070690040107074140b0740e0b40040d429411034000b00b00117103e540007001d81127560080d01214065920040260301b2640e41c0d01074241800c041d41c808111041d03840c1e05600259542d4580581404044c0c40881d0ac1d2070084210240075030408001c1100081042103007800400a503c2c001c507150502094a050f0207409480340ca0080d61300017169409180030782c0448404807a000d0080000d6662801c01105450901c02e0060000322781071180f0084c040040141c0f0700ba144000c1c51035146440310703400c1000112410901501501041c0034406400503e84d026003452400c00c00081400c16051078400d00c0d0000030f800030042c0500501c188801420080a40d95000d5890400056034207081c40050303250200d8190000e01031340c00000e55407042103042d00010125240e21250420a544030a88643c8030b000440e030b0115550b001c42e0008841c042c803403400c01c0e0064013030304040d8480c00b080c0c0003250919400001280781507225070141301401c8001c0090 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 8661850 1250 8660600 8660609
    0x11401050301050f01140f010c05030a020703050f01060315020307020c0a09020405040b010507030c0f150f0e01050108030703020604060c090f0e060102150702070b0702040609020c160b0f070303090c030203010507020f0601 97
    0x1c1c40b44d070f907042c01030842041c1d40e02c100250082090034130420f26640250742d82450a40c00200b03c2e900d805035100300039501c00940c00203d905014030506204820414081d4a00f503079071012107240113600e1a00c20100a400c0240042c0441c407410b100d20555840d048855005480400340142e039a81c106800e01043d14006034803941002410001c44010a074401c0746980d20b00e500c0f4400e003103202140d08289010b80d40c00c3d01e504144030315181003804403088540c08442e0500d070540c000c3c02940e81c1e0700003c1e0b17164040c0c1c403409000342c0c00c10000a00042c0c21070744412400b6850f82000701080707440f8a081c0381d4a540a81041035044100d2050091540c2c04002c50445061070b075800400720310346039400035201e014a2061141031007001c43e4210031503866411000252402810031034440040181041d034540d41841e00301e200460303103007020405100320030407591701c0c0d07440c0c44c08145031181d01e035030440c002c11407040280c54841d01c004002c40166401c0c007445000d42150f43c0204242c20000c5041410204107900 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 8663100 1250 8661850 8661871
    0x1a1c11010801030209180a06020c0a0218010b04030b0a0204080709020924041a07020d0605070f0201050903030f07180303050414030705030a02010806010504080109030909060b0a080105060a0c0501140105030105 92
    0x400059075101115644040d0524541c10a91b0a11000782c0c90030701c12082c028803c0303002062680c2080b00015800719218001c8400f2000c4d900c0340c4c40d03084d8222000307000c1c20000c81c0341000180301103604810810b03044512034400601c2d151741d841820381060404d8100a01c0745400054841903031502900b10859107070000074140c00d0114000e078403100c0b4400c511a01d4906461283e000b8160030403802903528558011340745051007900d601d819802404201e8401003c1031052400c0c403081441441850301c113003034444c01035245403600851543c00741c01c003c01c8031040011100682c000a592080750000441c42a140e2540311801c10b104800c050031840c08140c000d40c05100c041015035000a42484a40d0b02800d0859564031030f10012113040c4103d8004000540c2403105010415904c092450300311220600704001c1d440d254807100f4141e1290314407500005140c240140907030300d403c40052411007114141017000014039620b250a550001e000c8411101e085d0f80101300342c0c1401e00403d83e0103a503058 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 8664350 1250 8663100 8663117
    0x20301030c06051306031a120f060c18011b050307120905120c0f041103010602030a120b09071110060807150801050102030d02030a02121617010f03061a1c1101 70
    0x25401c03508032005205d400c2c01c064031201c00c1c10084051484c0d00418403009002007400d00c103250402e13580e4003c4240104050320600f000245d0311400c450940e444511007103464940c940400004403004110b01402c4802c2e882d004071524001a4104020114103205882c990401400000302a00f21141640454000c1d050000e2480364080b02003018510001c040f141742d0319011000001c02c00034528001400d902c0c400010020640c10f8000000c1c2400394800c0e83c81551180600d90784c401a149981c0050760007194540104080900800342044110524801c4840003480d43c2c3d02c1c04260780b1254402c3d0038640003c4410302801c4190600340060302210f042c1000e03d0b52400000035600e1203544040100c4c5070340480420020205a01119041d6641c141c00c41e0080c1081c1c2c00e2401034000700c440d00008244c0404c4140789151807a28104d0403a400d2200d1122039070310b16200e00c0082e1818040c240b441c080e4224911f28650354038181d00003501240c1030b00c52140714852034544201c01a40311518103010546 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 8665600 1250 8664350 8664367
    0x10807080a0602030901150e010905060a120204020c0a050d09031106030412050c07050d1104050f060108010501031112010303051c020f0702040f0f0518100b0303090105160b0901020301030c0605 85
    0x1200026264440b1005949584030945640105106003900001c1020242c0c001081d40144524605030345100d40c0c00c00903500c40c04100250b550407845a289101c44140c084405840d10b0340c080e140204c100815100307a4601e039980e4a0500c0903404902c0d01248800350240244810030040080422095451510b10b08154580c41d00c444001080d82d010054002a051083d4906200c01e00c01088003a0500c240701c5018984925080e98003800d5500442c174080004424003c1c00b2650360103420180c6075448140d00b002c00440240003036210f0f0400c400403c02900d80c0c81c15040316070b00d00039402503035032640b1900c1002c018040800200044441c0030300600c03407126000c908908940020754100c400082107140c1e1842e8001030b003641140350181a00c0c02003004240e540075080c1008041202095494901d14032854030b04550705a403005405620a00400c801035000d0f070000c0240e4001040e5041e003c08440d6034800c0c0000084800722545e03500400100f041110245e00080505001e0404c5802c00d200b0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 8666850 1250 8665600 8665603
    0x70612050907050f01050705030a120e011b0f03180507030605060109080606010c03030609020a02100b100909090503040308160c0501030c02030904090309050301090804080c10090b1e07120801080708 87
    0x4034003d0340d2041c0088103040354030b68040c5085840701584001901d845100b62070780076208c50b10010800000c80d007044400000e144041c800e1224000941840c0a22070a0002e000c0743e9a118100511080c140e441501802015060034400700c824418001807002078114034244080d00d40c00340245050005010302442035010201e9a160701800a1800003003101203400d0460242c81308d40c0c05000913074070001d40360341843d5005c94074002c080d0704050140b0030400c1280c18402c44540c200000400240d4031001800300c580c40b900008120342c0103004903030500340c0300e80354409540e0082400d4400e404001601074104194403407104002c2c502404d04100c182c8410310080d44034465074909612441c0c1d80d80e100c0080500600b03664001e403d0240c003c010708442071070140c500b039100c2d001e1814544501181031000e071a011140950b50122584d450501e9460600c0910650b00000040010340103400541441c031102c80000d401e1441c0907080c86405421000ea002d03004e004103030407407175040e00940024440758a0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 8668100 1250 8666850 8666863
    0x1e0304120305040b0f040302010207060f0b03060609010803040e040809040606021e0303070504060804060e010513020a090507140d020403050d030b0f0306010509070f1806080708090c2b02120706120509 88
    0x5d0340f04e01482d660711450300320300920991a006010700d01e0012000c101101036400b22500580540444605441c0c2e5002c000c0010740902c0340018070381c030401c0f040c08001d400100481d000352040e40300030b040c10704c168001801d4400c907401401c0142d0040c0c4c664004144c41c100d10745071034040c0b100594a54104243c005219218501458040c400c00d800031400b000f00c5607101041c10541d0400800c0310b410f00c80f10440b20103c503c0000d80c4100c4445402249151407031003864012303500c40d140e240320400c00705012201600500e5920140b80d40c00c0c0400030100784144006d0070400765907580080c0181140d81000754200c1040c407541d0180d841440140060707110990019081152418003141c02c5000305402c0361040000d400030f080d404005080003a8213900805200e00a42c05e07074803050300c04d0755803e120303c1e9682c03503d07a140366008100c070170050600400d040b010700710194011038426100009802280145d2071080001b801c2d61b101600801819030701030702401e0120b2141c2814065400c20240a0340d42e0306 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 8669350 1250 8668100 8668111
    0x30213050402060c070e010501020d09050a120302030c060f07110a030819020408120307020601080a0b010905070516030c0210030902010c020906030c1201090b0105010504180b03031e0304120305040b 87
    0x40e40d45001c1010356441400713455268844404440c2110b40f00d074401c3c1c0c41080280304803030141c802d4105075880a07001d82c1c403050a0f540d0182280c1c00d050b151203e8103211020f081000c1d800d40c001003080540f45c3c10f091200a2207248501041c00507401d107090b008010084441c0311202d60703000700d00060b0020754010140c903081071b80500c0c90750101041900b00c100a00c00c40c1d211b1905803081c2d056400385036805c0c9000d10f104450790740a4515a80c1d031501c60540310304102034005e00382c3d40258014842d4006903449607401060524041d81000c4090030715100c0b2001c00981a804213009010040442c0380008007262a40c3c0e00d868188905601e50b40060300500e83ca0000a110721140b000040c055181000140510240200703039800d445054080b0074000c002c4a0030036142c5010650000c40c3d903502410480701100c003440b4101d009801c0f80c854080090255221450f410300041042c142c8400e0401030200720f16090520301985d0303003080e2801c068041da0100b41c403000d01d0306200810010502ca490580e41c001c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 8670600 1250 8669350 8669389
    0x90b040f02030c06070809040b030c0301090507030204050f090d050c01090b09060a0c091503110f0a09090f0203010b070204090c050306070207090f051605210f0106030b0102010509190807060603030f020d03060302 93
    0x40440400070303041c421129042f9400d9807030044200300307000c0300041c4401200c2c000c0d201004640c950248281401008440790b070702d01c0d8040d00f090003609100310000d018210101c0000a081022a511300340c10100956400280d640700300180444080c5070300c03c400300300006040440101e845d000084901c4588440b846041c99074502c50100d001881034112402803403410f0390b059032102081c0340944101d040c0e00035a0003042c0792010910802c40140300b240d041c0c8403514405420319440d5800c00002d070411110455070446000c0f00050740d40c0b0b04018030750003081c5035000b4002c418100308031002110b80c403428a0f00e48500b88000d00050b9034030300035102d00b1800c040c41c10a03541d8041c2d0100c01c1c00d465940000e03400700700700384003000004040c00360850706980c0d550354103000e4203040c140124280c410651b004901e9400003948450300291850b08451103511031006503042400c507440e6242150444d51041c0d011500a03480d80700300b50703414020809000e803c3c2c1000c0200b2411600842c80d100040203555100 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 8671850 1250 8670600 8670611
    0xc081606020301060f0906230d150f090501060e0f03011503050c0f010305010e0103030503070908060702010b040507081509060d080d0207030e010f0203030a0b0105041502010b1009031a0a090b040f02030c0607080904 94
    0x15002c0c080427290000c8a0007014820300c0b0041c504502c0382c4200b44200311a80042d114040780c03c0c7e915000d6203040704d0040c1d80d03900c20b9a0406007040b402c019607201c030540c1503603141036400000c500220710000031800b0750042c00039490074809000c1010700f1003c0c2e4030304041c6440b006220a44088000a054030382503d080f81d22940c8404054a401d42e154012800324801c11007007041050303054001c4a5908801c1d82c041c0480d40390260183c0d401c0c0000e845400082c18003600740001420203d60080d80800c00034080142c0b8215030b141c5602c581d000b8000c01c0784498002460205258000760003024412085c40c0400301d140e21084000c1d140e001c0500754401300ca0712a213110240d81e01ca00e0070348001d0a2030f072154240004005501a00a110203e0407a004142c07044509030014010441d20080740d800002c24040c1030700001200580718001003900c0055541c460928012a1000b440b280c4610720844000c08250600e0042514007940341040c03d01c5030604001c800c00042c00242a24082902640c4c08642c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 8673100 1250 8671850 8671907
    0x203040201050c1204050415080307030f030b040f05010905010503031204080a0e060301090c11010506060403020409060f0603080a030e0307120c03020c1002010c08160801060c081606020301060f0906 87
    0x5030307807140d100b591070f1501c5540001010070b043d0b00c1c024002c036503007101d00b0040e1008149204455030160b220710a1541c0003030220201181c001c041c01d105180b11890b0018000070380500040c1198200707d0500c02080c5d8620040c01400024814280903090860085040c00300101014111303000091000f2704000010a036444414011900f610700404010001c0d0f44942e11005040c000f051450350071800070304580c100600903030b018481d00e40550b07406802c151501d030660b020b20010b41403045086030010350750510140d49201c980300f41e04c0034602c1400503d940c0d07078038000e001f02540d04801c1181481d802c208041800540d1181094865400701d003130072401507019090590810a007080d000340c12848020403c80402c0e07065000650301e01164035081000d803500c0044070b01d6400000702440201c0d10303800060081600802c8100c2c1e42c41d104284540ca0030380c00d03400135040d00d40a1802280c1143d00440180500c0b41c100480c810005514a01500230902c1c1030390050246560000c80316412496004a03074 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 8674350 1250 8673100 8673107
    0x13050112060302040507120b120d05220902090a060e06041206090501050c130b120a110c0a032105040b010b0f09120f06010f060206010603180b190605060a050d0203040201 75
    0x700a43d0010420041ea16050714060160441c510190301ca82e403074a107000c0c0c4a1b203041202000d22000d108020310301943c101c0401c0d2060b0344860306c41d48030100100b00680300c6100e0f207900f001c0540400d04000d43c0714034201c0e060042940554010030140410700c5501c6003562290740540b0304881144010010b0b85d002170500340c000704480340340a082e550031f01b41045a407810310f4008102c9003910704000b80c1e171166500201401c50041840c0c0c81c01400016011442204150b04010f070501031040b0072618010f04000c84078684040042c08401241e0080f034032210810291644501c6498445010f01c900e207015510340030720303081c140252130716944080780a0b811003040909641c15154054032a0a542d51107080b003a580d40c0c0117100d4407125215a2002082c49140350421034121020344c0c0050000ea400c1000a5000e04032250807040700c220f00c800031401140180d084940581c1c00e0340c4c909900c0c0410b020b81c0c2c0701aa21281c00c2240075050410100d4540c1d64090116420604800d00042e113a03180d03403004a = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 8675600 1250 8674350 8674361
    0x160b030a0f0f091a06030f0c040e0708030307080702060106260c041a0c01061403030703030504150c05030a05010b04140d06060510110607181503090503030a0605030f0313050112 78
    0x1040c81c5403804a00c40d08101801c07140c0d03540c40341600c0461341e599442c0c40406a41d01c00e1100301c100c103070700b09100108441c10181c000c190340d0341175a0305888806448a03e2640781d034001b02d03241c2000410172414001169014480c00380500322604e0804c108440c07410002c00c04041d10000d02d90030020b00300001c0c80001c0001c09a40c00b5284030803542c800720401642003c1c140c4c2110100701e00c0c551900b6070004044103201101504464040c019505064107038805400804000384207450484c0e082251a1606c00507120b090700c10403032502d0300307626801c0c944186012035405070007170092140200828001c030820302400c001c0c031100444825508142501d02440a050340340c1c01544c0100f221404101159002105907010400d031000b240d4896403103860460301d481c802004180c44807504001417100301102c1d40b1007081d00d00700d0704000c2641c1006941d1549140e004880890031241c0d074150170f104600d4207000e40c400c1e200c0c00b1070045081070300030700008424940d04d00c1002d06101ca0104180881e07040d58000 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 8676850 1250 8675600 8675621
    0x9010b061605120a030b0901050603040b010e100801050f07170403050f0a09090f020703080c090907030903030b030601060806030c04060f05040504020307082d010504050705040209030a170903160b030a0f 89
    0x2030b1152804040a0082d00d01b0400441c0701c1c41701500040380609085e002e03644100d401007174040c0c40340d02c0c0401d25045e010014003502c0d1040081d2002080fa00703024003509010745081408001e0074680340c84010000c2c000ca0600c00911a80700090102081e442005d903820304100d0007006640302091207003907808560700e134050341d802400c1c04008004400568041c040e954081e850750f0407107a85084d5170000a219061090350b21030007013030110b41c500740300380e12090070944039040004521510900180c541002684410001a190010407025040078000162401029142488030078140f1710000303080340e0b007402503500459131080010250b42d0100880c0004000d1a400d0f5101446d01c1c0210b0000c0740e640c1c02c180c4035640111210720029960510030148240d40110151200b5030905c0204806503009502945c0c3c98070032040f0090224000a100d1141406078101d080d98942031170741454240a40344a000702400c41e0030108014074881501185c1e070040c4000310009d1020b04100d070f20002030030346002 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 8678100 1250 8676850 8676883
    0x6080a050106030302010605010809070603051e041203061d04021002150906160f0c150e01020a021b010201020a0c1704030803070c1505100603150b030403051209010b061605 76
    0x280401800010340c024820b8901950081c4a219115001035890110944010301c1c03d50000704c041050b10300c00e610654108064030020341e0b099000e0b020380607900300d0944042d12070b00702c1c4088025800d40c25100302c3d0300401e0b101d0f034143d140707400304aa01c040c003002c002c1029004043c9008006942c3e03200b44900400b0281e9040081e44d02e05000c0b000c103581e9035040319044601d40744544480e25003401003071145001c19140c8d442c0d603014600d079a0340d600c105044030a441d00c442c0c2c40d003006a6a00500380050501c4040690081100f40d01075070401070700c5e29941c1042415079104001e008545a802991070044541000421607040c5894a039402c9600c107a038800343c0300500102c00d002c00d0960010003c41c034540545d2a41e80d2100080306031104903407007520a05450b4000300400c100c440d0081c1c012140c08130144ca015240e8598071440c4d552251320899080340020030000d82c50000b5249a0300540e0826101c8008101405160010640c0c0d8801e4110980c2d0030140d1103006400c00104008030240b9410408 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 8679350 1250 8678100 8678113
    0x40b0f09030a03120b06031902090307150e0f04060b250602030103030c02030f06090613020102070302040e030301030b010f120206030c1306110d18030f020307030506250c050c090601030608 83
    0x24000c0c6001d85100c10406550b0901700d104142d403a10b074041e40c1c0105414209400c1100c124a40ea40007580000b1000782c05000b9030300e000400600a1515071700054058590b68660032011082101590301544128411480d0540a0050807001020b9178003000e0340d0300c120f1101c0b1a14901640d40c046d00010000c1c07076140004004010598012050701d0740c94420345c22034010300322803116161204030444003c9119071200d00003400d049103592003110014010f0064403012071b01da80108065559032a61100d040e4030000c0100304000c0c034a403c29006021640c50001000d0400e01082c5008110000c003a00c07511011001c140d403032103840f0484140744c0c00440c1440d0550350701d07100035001c050b00d00860b50346409003030200c1400c940078904407014003100c800210040e606682e02d000040000b2401660180314428010000681c20008607006030b4040210030300ca00d10020100402451901000b0204802d001d441c800252002941200740e441c220b840c01c00356511003004070020081f40d845240305204e00d9 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 8680600 1250 8679350 8679353
    0x13060306090c080f060a05100b040906051005070302030a05090a050306070807021009020d0f0302030c0609010905160602060f190c0c020f10120c050d0c030b010e15040b0f09030a 78
    0x9500500207144a5510b407000969142407464a03041c1d0008580032540000c1c00290020b2942e50006600c4401c1200f00100161654040d4030036400c130b6000441d40c503903941014070491800380380007004500c0b903140c1320307181003226503009407a80200340d82c920a03c800840c0c4130401d581d80c1581800a40320240458216260001000300034090640340074025010707181d204004108640102030b48550050600c1546500590310000740e503d4010050301107002c00c0c03010440d584001d001d01c502400e1080c0020510f0b21460409a06000c140c40480b030034000705070000c111003500811000d901420305451100507603164600300080d450001f28401d00503180c80c450b0003100d900580f190035024020380c2c1580d0f180c0070030300500500310318802040780841d990361001d1380000e4803a040f650103000769252060500c03c9021395203080c0c805081668001c6920361b8aa8091540e002020b10060102204d01452110040c464106039206d240a80b2098800005d43c0c44200001d0303900711151504040c0c100c80c6400180d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 8681850 1250 8680600 8680613
    0x8090c1503070305100515030c070c030c0812040609050d0302070305030a090e0c04030201080c030a020c06040b04030807090e0106030b0609060d0603051506090601030f180501050a0608060405030901030b130603 92
    0x40b900c42020034a0a004110b030884d104e06400309541c4041c041c8001c00340d2902aa500c5a000101103520040b0700300700010014602e401b075003000310311484a8410290401c0051410024000c00300b00809809000400400303a1100d4801c0480c2c01c180c5808486440506080b41005070b00d4101030305901c8000340b0120700942c4503900c44101c60444560240c80d0b240d410f100407182c817491101900045086c1c0104c0d9032450508021900030641000040c070f484c0302d00d44d00b1130070808211820350b0900404800c10050542000005922011034a8a1400c06041803118039441006001d50b03010140c0d112030321419501c40d5021207190280051840e603d03600961032110140005001c211080d00810321025a40513000b074509008460080041e00181d46d50001140106101c146400e80141c884c540d218400300d540c104255618007807000402c80b840c160101c0c409541550f80076020700d61002c1c4c00c01000c03440100c00d68a03004424a008034260210b0000600700445d5045111150381ca00107002040040c1e = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 8683100 1250 8681850 8681857
    0x20a02031c03060801110702040510180903080a052703040308030109050a06230105090409140604030f020a020306180c0a0b04080105010509010302091305030f0f0c0111040506040608090c15 83
    0x1072503809024031a114001e681c2600d40060b9480000c0c2d0003030280c040180b4080e000144e200d40d810541c80180c65440990788030110800345104000d6540d010018107040d071107690194000c0721a6014821800c2141d0500c0451400b0901804881b803c074010100c15401030044500954002111945958460141c04000c180c240e40205046181000008007901c81820707150556013410300780c6c0344c0801d080c4010341e070560041c15075550140d40d9450140c0068240c02c00b400c2303101891002850140340138900030301610350164900d01554405540240145c0c2e0005150380c1c4941c281800000c02c10035680e041c1c0c5800c0180040f41e82c41016030340e010684d0302008000d8000c8402c058020300103640d0394003c1c00f1034080c0c20b0001940194ac1f030070000c1c107408600c1601c612042d00c10412281307000c110fa859406d00d6045280d0000320340400003001c80000409003d400c0302200301c049031074a0a850840041c6040c800c520038841401010030015692140900805d59820005400818003241210800a41e60f0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 8684350 1250 8683100 8683153
    0xc0904021809061906030207060906060602010c080a02040506040902090307031e050d050a0c0f0f050106060e030c03010203090309010c0302190605010303030e0c030706111f0203010501021504020603040201080601020a0203 97
    0x10950400550039240020440c0b0804c10704d124103142240c02c0c580114042d600030f490503100143c85861900000d49584109401130034107500000d18580d10a4000344401d5000d000070786500e00501c000e1100d80e95400c01c0383d04403280c1c6200103a4030803a8402290410003564406420b929180503034000c44040c5054140c805440f440a0307403010001d03002d041c1c030540600344540d80010300c41e401d40350004440b040700c0d0302c00c03d004a0013404e0045890703540c1c5087d0707640c54102c0400500904840400340c2170800c107521008204070001c1d030651424600003983d80c01030050a5040006034843c210505009100540030840e46000d960908005800d2503000703000c00f0311045001924085036009132000120790306aa1200003006001102c2c0752200840e4030503900010a50a402100000f14203100f0007070340038003183d0103440d000d070712036141400190802c404800c010301961089030800c00140e6846045030381c001d6090802078281c0c0c440d03000403850006031b02d80c002d4051290f010800140703801ca100300800403 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 8685600 1250 8684350 8684359
    0x105090903030106090b0c0a051b010e010201021602040b0d05010c0806010f0305160f020f0105090f010b0603010e040f060f05100306050106110703120e100507120804050a0204050c09040218 83
    0x1900e40652460380e81c40309228040000306401c000348000390a07034009103070755550b40b01265100b07109a22401e051040d103c000c141c100d200300d103150340c141d60010458040071109000841c05d012001c01c5011000d205a03e00038030880e0383e0105a07142d990b911100c550384036000f8008011b403810495018285101c26039026000ca0a616444140c5a129025441c420340884000c2d101c0001c2e40c03002030320034000b440c1081e010760150005440801009201d2617100c0d81d1203000601c02035003103512547c00c64041031081b0380035640400062041014050000c0d030419070050030908507100a0030a070b0014116036000041443c208414804281b802c40e88400540f03000f0b00d4108102e0340d81e05c000343c48c102800740c040d0303689400091080000c9658803c0c045490200c1e4141803105541d060009440509000c00a40100360b010880d070041c085d581aa403103200d2300c01e0420309000d0400e9150035a4400aa00f0001e209503100c100103050785419006035034444d40050300c01d40d240c000c010a0546d00a01c0c00342c005009 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 8686850 1250 8685600 8685619
    0x90a1e06030312060b27040908040504051f0b130e01060804021306060c020418020603070207090e03070201050702060307020109081317010b060304020d03020a0f03051c0b010206010501030b0d0803010308030105 92
    0x222418421101182c05d401180c51422290006944c88002032a40340c079a61a600301200c0b01d035459034064540d180d03200d0340ca03880d40c2d90f00784000c01040f64805002c8040b2003548444402e4106000c40000c429584d2031f0010342c0d2100d038184a420101062038101c1c040c200410800021070903007012806000314401c9813643c0030703484030010800840d9030034400c040001d4114a445405810309511581c16461040c0400840710010313008600c4590041d2104070040e84519001c01014110307210f50401d0030041c101070b524007085900000c1950150150103840b8480c00408101400c0c001d50202c106180c0c4107403c41d868040b00d009030a030b45e01c1d80f0b110f103890b0302407150503201c9403500612805006400060109003981c80d55000e000600e101c481045003948aa2100540414880c2c850a020355201c2d540d441c0e6252510040031402d011045444408641450341e41508c50380c000c0b800b1410744034280b0300004c81c80010b0001600d840031000015080c0302e0004004814419804011030580710180e600b10f05 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 8688100 1250 8686850 8686877
    0x7050c0409030504170109050109050c03060a050103170f0d060f08070608010509130206210411010503040c030b0702010603021302040302041508030702010507060b0405070c020109150e090a1e060303 87
    0x64903070005006000550400c02130003640d0b04680725152202800b8000107540245940d51405c444421005440691110072071880d02e01e410080907500080c1020709012039455541c40d00c00701c80c0100190041c14001107040d0301c2c0c0c0703a080029281030389015441880314540d41d224020b04800c49003d2017804c0c1c01080d4022034000c1c00751541034100c0340c0203480c1c20003603610001d0140004000d0f00341268400c0040208024401e0b0040f0011007000c2c1072903280c155400c080c500221340c01011450541440014001c00011034070b864245800c40b07812110080c0c80b65581c0b2801c900405003034100a50040040009031189601c941c045d0056900c2030342d040250600c030a54951824030148281941507108001d008010351142c0054101284901320200c1e02c50807542c00034087e60001c9030440700242590f03546009560f40101d9031001400c582042c42020441030100410042640c01018050030340b040c0030840064083d488261485440d40341c400080b801c01000e00094003c500c13050300040c50740c109684 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 8689350 1250 8688100 8688109
    0x5010911190e0105040902030705030a0312060e040209070e030c0312030f090c1c1106040902181002030d150801020304050303010602010c030c0e100e06160213060602060613060312030207050c 84
    0x74180d0b10380d50700b0711103540c3c80c0c682000042d056408040381c00d40612000010329440411401824622030b0701c2c3d07481c180c007503a0080812211250701c02c0041007640c3d818480561516804142c11071030b545070289011a122011900e00411410102d4040c400c6c0c980180085550102a601030f45000000071038a0719820791035070356800600240f90f44040e129006001109804c0680185280b0401c054210202c83c0700014505410a920406449800240621174265205d000c400c0c41c0104403540c00c0070503c0ac940c000c0d81c074090b00c441c03100c18075560381080c0500d0b41c02035034031001089104001d40da07900c0c1600d813254580e0000c1c41032001644c2000850010580207000c0c3c1010100140d03640342032031150800b0003600382c01188001c014800300c0303154010305480d00f1004106040c09200c0010a400440c8103105100c1403480090320f00d030740740110900000f0380c00709035503400c000129254420520a1607955004201941c002468040490881c042e642d81640240040c40c0c012030958200491840a11 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 8690600 1250 8689350 8689399
    0x307020a0e0402030d05030a15060c140106060503060409080705010c17090607021b010c020a030b16050301050604032d05010903090b0c0c01080c0706020403080909090a0503041202040905010911 85
    0xa615030050407410340f8441c1b03d00c5c00707185c0c07202d01d0304000704000c03c41e120720b84100c1d01c1c503070000300000b410340b8450824411200c0320b40d10303c9081c1c00001c011051801e05c0080042c000641020b10498440c621102801010810380e900f40b60000000c0203503459100001d070403200d901c0809070000000f280011540f00300400c0c00c0c0d210781519005080c1d1982848424017003a01c440c00303218180018200d0034409600c5848412000d144212200d110608188441c080782d6045502a041002001c0006000b01d4681000744d0301200c0d400501080c40c55040d0103180d40444c03440500d002d0701c5a00ca208003003848815044401041d021b621a44000c0d91954100d142c141708021042c3d031140d2001c03542910551064004940c000d42d5036900e141006844e54991007070781c1c8146d0094603030b0b500200d02d40a6514000b07555030f4100c00003d00130b107c2e5001542d5001d480e4010b0b031081c0344035207440101e004255152a08003204090b44074008002494052038590340600014242502032001c0b910060342c10039000085 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 8691850 1250 8690600 8690603
    0x2070b06030f0a030c021206090115080307050a0f0201020114100608010509090a03080405030417070906090204050306010b0a050f040905180c1804020301020d0219140304080403080d0e0f0307020a0e04 88
    0x2421031081e940d1001e1360810b0301c070345d8100e1704003c000203030b140c1c500014800c06014440312800452074145000f09100c444246030000e4001b5002000352034005000000c1082d0010f52001c040e04c0c000c0030303900041c2e005101180c000e8020118100800000c03015201c464001d0310740c542c031800c0c5981d8942040c04405c8200b00d0314844598444c0a01c1000f2a010300c503000d91261190089900c1c081d01c80e5900409034111f5440409990f01c01e507000d0014102500bd008050454140d0460030a890540043c2d624076040c82551085880040d018003058400c10844070341c0352545803450f030703141d64404d6050018001140c80280e01001c000380c1400072007012501c8620040d0003450b03038200d11f22066040010f17000242040364159400c02007034100048600140005603480043c90003003101d0321030050107048038050f040503034010401c10007000540c64010346003680d0300181c2950b165240c80382d6030b00040a943ca05008035206480044017038450001c01003041d00e10903611801400da030f400c01415581c000382c50 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 8693100 1250 8691850 8691853
    0x50c06010e070c0b13060f020705011a0109061206050604031110080405030307050a0e09010603240602070e040201030207051506040605060403020a05060703050d06150906020c0904080d0b0301050a02070b06030f 92
    0x110f4004500c141100c3d5401138105400c1c204c150381c841c0c4d10101250303803120205400c140c0114400c400c2c001d0a00c101e83e1601c81c91004d11020f182d90800003000d0082c10b00458041c001000c130003015901c03d95000001810025000c1e60303032607072a400c00d0100c00741490340052003841c880c03076101d42c1c40e0700c180b08150040b50300070011815070300c070300301d069030355400501c0c54204011040380100c0f141c1c1e5074400c01c80d008110030b88000034401e08080702c0c4291040008c241d45000c4072410710410401d41e00080c0801211440da03003840640e165440102c029110309074021b8418072840c0c207142c1c10015a440341078021481101c081100641e6802808800d02551101035400320700d50b4010446420075070700500c92944a482c00520307140030715141e80c08441241d0003101011440070051244039030020f5041002e402c2a0000b441008001c40007d03c0c0b2100042005004010224100252100e90342010140400040c0280300914007041c064009411402c0d081d55001d1001c400b0803224240030a00700c110070344000 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 8694350 1250 8693100 8693117
    0x11a091003050601021011030103060507210b060702030d0806011107050105030c030a1b0c060f02040305190201050c070602031908010e0f0c040911030703060f0602070e09030c01020703050c06010e07 87
    0xc006400802000302443c1c10350140c80c030f90000c400e50510800c09203030583c4c00b01076200e504505000040b11401007540040c0044202441c1c0180e0000400b083e03020803c50000c03c0f600c502c8804140d050080109c0250103210304110240f1240e003140006102d55402c0e611240e03031580e030603001076503080e4078464107000c07036010408501584080c070300440d400b0280d6803002c0352460102014107805c46001c1c00701000038800301c100d0020086e031805000ca400c2003c400c10340c00e00c1c1c10350701c8003078848500145110000d404030500a046900807001e49858008071000e03201200c1d52a50040d4403607116007066480c4d0007079110501226401405818140e850b454500b0910741c0d11039040814210010f08031105079038041c00002121500350140003255011030801689030b0400c0f40c0007400384c17071894004030390350784803403009101baa50b0000d52801101c1d100780f0404c500fa2148041d640c1144180041c05009500010703a080525400100521144041600302da0b00e1780e83e94468101002e9084c0e4940340041c5600 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 8695600 1250 8694350 8694379
    0x7020606130509010b03070806160c0b060d0f0c08010c1b0503030106080a02040302040213050405100302090a020a03150f060801080d020d0e03030909010311040e031c050717010e011a09 81
    0x80e0b10150380282010700002da11141400021b160022a82c030500381640142c0402c00c0d806034010040030003200070f040029507988aa52141032160b002407280e809407030300345100b03401e015203907000002207a0041c510303548e0b494031000c500d4043c2c283c042c40c00d004aa55901c2911030b01c1709002c001c0c2159034008000e90b08590826000310362101015051010240e028400807026a0b1544010090f5402c08116618154039010601098942c021300310b0b103030754402010810268880d000065030003400030000507550800c8890075030090000035680d0341d18890400c40424012142000001035842c1610341028582e669200030350b603010070311403840041e0850b0504204540c016060070402003001802e807030030050030101107550000264400c0c0d84004031000c2000340360a061085848460100001d18908080b00078a0030400c01c80341c2550a0352542c440000343c81c2c0d445200c01062030300503034001c1007155a45550420ba4941d081c016840c4500c41d03003400c00007080e542810ac0b002c0610107400d0708131401c1903 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 8696850 1250 8695600 8695639
    0x60b07050d0f17010b030105120109020904060b010504030b04060f051305070b030604020c01020319061203020601050609030703020904080705190b06040f0f020406030213050a05060f130b0a021507020606 89
    0x1981080000d02c40140400000400706140f528068010482d001d0740f00d61410b41080f04444151001d80120f9242500100c00f40e181e00000d81c1c3d0240e0005400f151201e003e40040f101481a50700103171292100704240420455a134208071b041c0d1480703440c1400680c6504114403c6001c82c050010030b140c3c089142044802031010241d6801384000740010704110158541a00303984c0129214850052100403400450b2058842da034064414074580204011a5070b60180d511501030003030910600020503841c00035502007050b030002c0c56015081d420300c0c0c1014a0000d045810008080318280a10799000d18051083c102409a8580040c0c1203031803a299203042c4402400e4040b4424442602c400d40c005580340c4a00040c402810107076001030383c5031105005103c4182003038010501c1560300510800103541d43c0c00640d4601c0030105100c070b03a11100102d0000b654841948880b04031480030448518403500484e43d00700045903107000d803101d03544010080780c131408102c5070030350720a02101e0b10608070000f = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 8698100 1250 8696850 8696867
    0xa060507021006060e100201020a02030909060a05040905060103030306051f05030403120e030406030f060e010302210d0905120f060c07050703230f0307030203040e0606130305030d060b07050d 84
    0x85801611142d4802042c680c040d00d800d6005000825403401c0801014100014084500b0400380b000318144043e03000001d45a00c9000c48051280300040301099065440711404001400000c104000328a0f080c47c2654540d1024070060b400700303140800008860a12014520200602c0c56588403951038500040d01d20b60005072094080000d0703000051001e481034854180301034454402540ca80d441d002004094550080c1c07841d51160074031008000030103110000f281925412a006aa008800708941c4429900d04404c0d6509110b400890100e80da000006001601d4040da18280300d0300740070380130030342d140c2d01c26031801c281e80e028100159403e4200740107001200d03c142d00780d60b4070039030780e40714024030b2842100702e110b039001014010034004400b00585034040d0b0041019600b03155181d14043e41700d0189118440107840c60034005103540c1d6030502211800d25001c038074048840e0f10f07418403941e44e80040f00c4962081c1e04d02000424400d00a1099a1400e40e010004210780408040c0840e031161 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 8699350 1250 8698100 8698111
    0x30c01030f140106020705030c01020304140603090f1204030606150c02040b03011509050a05060306070507030f0e09040f020306090313030210090312030f0b010e030a1716060603050c01110a0605 85
    0x350741d0002007564030150b06405000b480507900401d1150300300302c201407c09410311301c50b42c1558001c0004200c5c0c4441000c84020450301283c90301d8884d03881008850600020848410482c0100000b458102c00f0744000f030f209480c01503100700b180c66100c024210b14078020342e107080041071482980000626044c0c210204100010340086101c0c5510519503441c0c3c50780c3d4204001d400c2e15001004020b09442c8581d6074440002c034000c041c10f00b4003800250240c030464102404000c910800c0484145c010303001051001005800c0b41c00760300d024104460340030400c42088bc428041e50b4041100c40d01c0000a45180010041c550818030b40b6540c00c105011410040040c24810f4414000005c03c4440b40c81a5030386c012610701050321018a20200101e23443d4103101410702c94001e0984106840014a00340042e0b80301c03202c801030140d140070906003802881101c20026040001940411009030448422a48030320300310b40120030351400550f50421400440c11056105c5150034002c14920707045540c100 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 8700600 1250 8699350 8699381
    0x3080f0606181905040908040504051303050409050703090b041b0602010c0207170c041404110406060503060402030406060503030c030c070b030c070312090b042009040b130305090307030606170a02030c0103 90
    0x4584e40d0300400e06a40c0c00c1c8109440d66a03010408102e43d0401d80107056105810200b001c85100d060351700a0306901403030142d9a0380076903d000240030302e40607500c05070005d900030304113500300d1500e850880d0846135070056100c140c5407040720001c4d4186c0140181105125190041e028850803c00b860351144215001c481e0644140c260540c0e140d01c56201c1c03910620740c0788081e56500e14003828a6000304094500c42805145070000401c10158840c0c143c80c0c100a0458000d60b90746c031a810048090300054001d81e90502000900e20340300c4100000038107400d4401c20503543e03800d50303940c00420340380000c40e50301c00800303020444000040d2060840046c03c0816030350001382d01c00d941d140c1e201500780841d4200c502404003e14210404a40b1303618a07800305040b03840c01c6580c40c06075140b0386030790000b40c400346044480c64040800c0600680a80c0c011020260403600e58550720b041443c054403181c0b007818500384000e012100e04a801040380441e041e0094020410000c4501c011130041c5080c0701c054005 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 8701850 1250 8700600 8700649
    0x6070c0302010914010b10050306030703170706051603060e010506040302060a050c0703060c090e060a0504020c10020708070b09031207050906070204180303050a090b0112030509030a03080f060618 86
    0x20020342c404c510800b04980001180c44980d000d10031200441c404050601c00c0c14000c03c1026a800180e280039240d000c0000c8000300c0040308000d00c41d020380d41c0001c0c0302c2420030042042d01d10301841021903440d4156400d02c000c541da0258040307200700a01070785070000c50420044c405400d288006000110052a01f68900310789100301c981019110740045074200d8070758a03e07110003540f202c11315010b0009403401400b80e06042c00010003000080c818035010304d4021403d650455824402c140d5114150320055640d078007e40360814940d0700000c0200c80402894000c501c10900010648040c0a44980c404203d034482c1170059600b50031108090740e0100f01004010010b89603400740c4c4070404000c255014425071030f0b14001d015210000c0131421524640201c00020680c01e110842c116000c2c00c40c0c004103410035080481d458071410022540601c18600454209544a81c00612420341000010032907115001040854411044060003420302201c4915040c9440d41d600c1001105010001c000c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 8703100 1250 8701850 8701853
    0x40b060109030b010e07031401050f281202030601080d0c03081003020d081902010209060702120304030c0e0a0c08060904020108100e0a0c090503070506030c070f06150501030f05010806070c03020109 87
    0x43c1d103000d802000c1012403880034010040c1d01030040103866442d140040d6019814680030030f1140c01260303a03903442515241c40d805140c01c3d22103c2402201c0150074060240c6445a40040a103442c01800302d000303100c0c24000181103034000c40d222079040050780c1c0b00f01c04a41380c0e80302202d40c02c80c05491000f411484480000060752614400c054184c800d020307950301c0d401c050202441c034861452041d0256401001003803201d0b80c0d100704440a596040300e840719141d2286541c03500c1c5015581004040d00c102c0400460410b119500040c030440d400003040c02402058403048512100584e4407070b17000031452001c02c00641c003038079085030702c1186443c1000b82255206401d0003044415506400c01e40e5031080904c8496510a00301c07000341600ba0020000140361501090b00d510008000c0e44d90250301180113420085c031071032034002da20f411100a00c11114100a0716003481c0040c03041c240840d00c3c00440480e50030f218002c0701c0c100c511300400741c0607580da070400c10b880142420f80101c046550344c00c00e040 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 8704350 1250 8703100 8703113
    0x70918080711090a0902030c0d0c050d05070512010219090b1c0e1006050f030604020303030c03130c1d0109050402030a02040f0905060901051b0c0705010c0314030403020d081e040b06010903 83
    0x20b100383c4c0000408200400741c1d0044c1410807600104080c0103800c61071720786000c10600d0b40d410046582c00e0700d140300314110509021341003110359008543e01085d1568842401c1130150003400e1790401441d0710704090114070b4400c0e24601000d11030411034039428040c461039080080c1075407218111503000440c41c42d090034241c03802d00000200ca246043e6880701c05200e80d0030484200405010103030018191410590006035480c040240000b44181000000480b0082203104651615600c040780a00e4bd075100d00c14240c018000350b0b0150764121170390000140d0800e8500507907000d2034000c0c01400003504035400340805042c4111000161644401090300043c000308003a034406d0306514000545810811303000381c8060f01d83c130143c2d24104428848100c0d0340c24045040d10859500b400d1075810f41d80e0500e0240c6040030074503000c00c0e1440011041000307040d000300da2059114801d646a4010742c0d0b0b0340c0310f0400e10301032420740403206188500c005000112400b06468000c181410900c03640c940d2540c0c0e21 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 8705600 1250 8704350 8704369
    0x14040c090b031306050109020406080408030402030106050a0807091406010e040c091206020405130903050406030504020a0e0103030807080603030412080d0e030a110105060402120f04020103060b04060c05070918080711 95
    0x2821400300b410350800740003092017994050000b0b10300541c902031800200416000024001420140c0700001003021580c09500000085c50040c0011000341d43d0340d4038a070b071902c0c03051040854007400c21070344100600500344218805c50050311424800050350b0f040c48010194011281f040c8035102e4400301e521015000240845440350300e0242c2d41d03900304801c0c4045410091510301e016402c1c14280c20000350004107842c04e441c402d2070001815035440c0000746600205500000441807284000301c103042e80211580c1c4121050344074505152100401e041c3d40380314521030b44103421003000042c00045c620b50700038444a1840e6002164420040d4006411a0301c50f4802c030f00402e014801180c0c041c1828003450758408402c94003103044c80310b0803408000e5010010204040242500002000c41e8000d60101c1e020740000d21201e500c554a8800281c2644c4650b00c0035a528032501c1d00c000307500c80b10f900035150000000440e1082d40342d403a43d540103440c0c000c007208503580c032031040b070305441d0ba03ea94042 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 8706850 1250 8705600 8705611
    0x1c0501080a02030f011404080a12020a11010c090602030a0f09080102130303020d0503060607110102030d0501090c0e030715030b030717010203010f05090906040b0a09060e06070207060914040c090b03 87
    0x140004141d10301c10185480c101c6115030080e039040801041762240c451103044e0340315411045041c1d484072081004c07950311000700052a1054030224606500c1c80d0302140351014420310718020004590380403c195031103440791081c40016802009030260f0309110314003c0f403004441c2d0030000c03001ca8803550031500f60303040020046040e50708208100281a81003007007006403000c0f820514a18105000498082d201f0400d0182242042900307000d03a80c0d00c2082103d01255282d002003105584410403503000d0581d850100d070001c1d01c07180703003200b07c0d141c003003400c004440032091043d0042c40d0080090303014050010210754140901e91001403d00303055a40f58442000b00c200043c1e80f0742c18581c41c0c8100a50720b4110034066170100007081650709000488a40013a002061600d2640d00d00c5150405895080740c02440d403820f01050030f4400c200003841d1409103455800f500c00036912200100c40d20303603042c814a101d505066083d424241410361040040b200186007002c49642c5580700c03d54030740d1003500c5 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 8708100 1250 8706850 8706853
    0x70e04030305010f0b0702010e0f120a020102060901020a0c0609050312070509040501090c020606151e18040e070b03040503130602100b0609030c060c0a0501110a030507020a0206030403051c050108 86
    0x802042690610840f03002d072804040341d8554505000d044c4041e40144840241889034149042d001a5901018491405c4004120940c00d41440b1412a11134030310031012030140c410700e030200d14241418003c0d100c140c003240d41c07443c0b500003440d141d0601400c07a140d004c0d5600c0c00700700000b40c001d141c2481d201d03228010a40f5070396a1030314480280001c0301c130143d0140020304c3c5059036201d102680425010340102c07007214804000c00c03481d6101080f9100780a0345084600c40d800341c1d44642d80e641c40c0540f501c40c0c85c10580704415000e14080c0b10640d4010650220660440c500c213000401900c0d010f5600280a081201d0401801406000b088000b0b0340128015a0058030304840e40052805001010380081d80c0b214149511030001c2a5a080480c040d41e00c0f442c40030408120b4008100800f0351100d42140003404004100380506040354011860803000a060030000f425070b41c000109015041d40c00344c1507501e0f5a9403920300301d07059006070808944001540031032028030701c038a000b014060f194070340 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 8709350 1250 8708100 8708129
    0x1404090618030206160206010509070e040f02130503061506041a1201031a0916090c021f050708130309060302030a1b05030105010314060a0306090318180b041e020c07030507 76
    0x48117020138070707108000403c5511040c0180000e0701d4680f01d081c0c0101c0c0d2070030034024030080b03000000e001d08803101040c0703400ca102081c400bd0448180f00c03200704803007040c2d040e201d40f9201c12080080201d5880d101030f411203006c001c00c004e08107040100d402c410201c010b00c18200003000700020541d503400c0c1d2055882c24800350003220700035003400640c0e4220000400512154603000d2003030100303a940b44903100701030f0b81c1d94281a10090081c09003010680b8148441850840c40401c0c8400400c0b082c1c40f6000000d40c40320006102c90108070040f0142c0381c250b203071926482e1030520220040e5100414a2743c00710b0302c6001c007110341622284a511a011691201500c035070620000400700c40c502e0300b440504100090600c041504e40d90354050035660051008903002841d07081c1030358032980115601603145001070b40041c40b0404062a1003004114500c1404000115000c01050382c040000866021490036104090101a030f0700038044d107160070f001e0b1202d4039500d80350a802d10764070350320041c506000d04 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 8710600 1250 8709350 8709361
    0x3040f08010203060a09020a090312020c0909010c02120703020a060b0103090203010e0a170a0918020705060f060301060905010503151009020c060f0703050103080a0c03120c0c050d091404090618030206 88
    0x9031704140282070341000450410100d24002411a0308502c0050504440c215440e0b409610904c460742e00084041d2a89101e410588040c50084ca1041c1c4407500600440304c0e4504031391025030031210041d415900400e03c2200c00c3e00c0c0c83e8010804a13a806060580c1c9004031740042e1800c2c01061100c6206202521002806040240714009000e442c00500b0384101f201049040d00114840d0640712510b044602086100303118000034401e40f03030090030a100e202c040216002040403007510994098009024851ba034450780380a4030420300034103a06070025900e800c048807150003042da00484998004c28015612490101242e02c1203201e102c2ca6004007003005200c1c0034000000790094110302e0100510740c51626204114020301d082d16041149031002e04040c148608001d15038280c0d6000304000307404800030b0203013920300043c004842c1030180d20800404c4a018222050440b046801c402551049560402c4000c1c0081281107844035691203160840866005145428505c250004c02c62070414 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 8711850 1250 8710600 8710609
    0x10206010e0c0703050903010209060c0706020d03020711040504051005010b0a17010602030702010507210f1805090109020a1101050a090b010f03030203090d02031c0918050c0702010507020303040f0801020306 91
    0x141c0002440d00c04150074050540002c1085500310358140c40c1064603402c5140009002e4401c0342e8280f40d000350003042d02d001c0c0c08030218501084840b140c084464010214000782c041c0c0c003580d48040c04c201c1d800f01c0c40c2980da0825402060f03020384203a06950f8419080c6104404403602a004102d00107404075103910b1040d0050f4203805000d1940941d04d203290f16280c4002e50300d103d0a032000303040140210b2008100003040d01c006059454601c0703001556100d80030000c00712464048000c1c0091002000140c2c00300340c0c1c00201e80be9502c0a4668092a0709003100140030f58080c00e24042001030b08101c01c54001401e1041070701810800700007003140540e074102080e0003181a04080181e9142d40c1d4100002500001141c44a0b07000750703202c140c2c1c8041400082c0c200070340c8580295421059044d0801c060346d102c040348007a40c2d4601d4a01002c4061459040210346049922449103407082200e9800756018502428100340300404403403a042c4c50700c50b16000a0050750100085a4020080c02a035190 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 8713100 1250 8711850 8711863
    0x20a060c08070201060b090904030c0201050c15061c02101107090203010b0702040c081009050c0f07050d03230c0c010209060706020703030605010c020117040201020304080a0b100f05010f08090109060c05090102 92
    0x10705000d19040c07901000008ea4508000740008050101000c000411a402242510390304c22844050755003507501c90445da00c28103000c64117940b03d807007606a507604174551318600c0740401d50040c1c15070b01d00c1806150241c40400e0090b40701c032498480c0a04c000344181311400114080c001005440c1c1e00d80d0194410710056602222545c0180006003080000a0a1420942c0e08680c020240400c40f5100c0f80c50221080c4200112104240346c0025200c00344a80003890300221603403582c00b04070021786501c5490030866001400900c00d200c0601207646a40018044c26140340c032a03000500d800201070014a15500103d0101c1e1072a401088083c180754061061000401b000e0a0010101c10540c6c002840420001801d407207840d40580171400303591003081650098440c1500300c8911003214142440f40c904c04641c40c101c3c51114a00114a82440240c02011910f060b112141901040c07117065030f1002000701044299075891184802045081c0904407803030b0340c9900c2d80c0f076841d00c42e08002410502d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 8714350 1250 8713100 8713109
    0x604060c1208010305060a02030601030f09080a081501050f030405010608010603150e0102040b0906160501020d091506050319060e0604030507030806030d0e040207020409020d0507050a0602060f0610020a060c0807020106 96
    0x42c0c2401000850b4003c240b40d54000040c1c0c80060741e80d03541100607002402c4070350784c041507130386401020410008020024801c004a6807500aa40d076654040150708818103503042d800520244203421151510401940d08940300740f0003c10041d40380c1e0403843c03c4610039407040e100d6520102064565020a1103000c18840d6400d0007545800c5c24820460100e10803070002e0b602600000404200241e0151480941c540e03014000b5551601c00a4103900600b00d007403020303141240c6107001d080b00100300d031150000300d400190180c0b092201003140110000304003c42516044e0b214400c10141d024207218541c8183d1007621101d071607981900340100040c40092450340a81d110b8454108000d030052480c210b0028121405665202244045000f800205031300a401c0040c2114000c02c000001c0345850555005641104445556850482e540c03002551491600304038480404da841c00c2113240840103400900407a01640800e07610101182d002c00740701d40c00240d40c2014041621360a024810041 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 8715600 1250 8714350 8714357
    0x2010f0806010e122401090b0301090b060105071b030f0c0801050f0412020c0a0906030203010b030a0305030a090f08121005030f06010e09070f0f0806070816080903090604060c12 78
    0x500d001c00002c0c0c901149190310510502c0c100303220500d071031401c0181514030b200d40c00e09201c503d40c10310242640383c002805036007810b50410f00300b0740c11410144242d42c0c000350812209182d07a1502d00040d80c5540c02050182c1d1001e0501e103800140702100754a100055105030030300031550300036007041c848006550b0403600e0280d04203024880807020100c40160442d0304001c04041d900100c180a80c68000e0304610715801007078500000900038110b904c401b0450f4000d070002d0003c00400c1c0201030300c41030003030380040101d032042c004101840c002e0703400010311510541c4000b4001805440d011400e40005805290303c032000820400300084210b43d441c000c220a0300241076504400c15441d44402c014000c500e8103090110000744980b00030400c020081c903041d801e019881d0340b642052000903442c4e00801c2c440f0b11606010a00c00d41c410301540b4443d414070304545001401c6400120f951032030103007020340948400c2c07107440c0c0746580e110001d100511403521150606100c1d8900740d08285411003005061 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 8716850 1250 8715600 8715617
    0x10e04050c01110705030d090305010608010b0604030f0206070b150a08010203010518042a03060b03030901050a03090204151403010b0603040309060807050f030703021218030405040f060503030c0102040302010f 92
    0x5200140c1034011031424281211455000300071180742000f03541c880e646c0b5100d0041c1c1030590a810071043e5003901c0c002c070002d201e41601c0744171090a9540844035150441b6080100f000442c81c440c03550a0010304c000e100078035190141c0c4840302c02c0c640587c1d1418111800300804005807030b054104500501581d4025410f42d0701d050001004016841e140d00342205011000404104001c00040101030040710b9428034023048c01040d802c0c0c1c141030b0001315070341c5103803074901c14280c540081994541c4805944143c40d080300f0f00c008030060100740c50201d030010303100e003907c105c2140041000c402510f03e4807544e10014010104160035983c00c0d00403140103620410070b00020070351040c0c40400792003441c01c04500d503843d401d000721807600c510001e22501000209c2446500303945500141258a424100c00d40d20b03448519001305014042e001102150340200820042400c00d80c00256000006c01f0300020401d1b91100401d003150310500c92903015940c005420b20441d0303003059611803000f41d2460031aa0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 8718100 1250 8716850 8716853
    0xa030e190203030301170f01020403030309020a06090e040201030207110306040503090102010c0e061605100e03030a0506093102120606031207050c0d060f1404020102240a05060114070c0e010e04 85
    0x1c0321300c0107002e4003a03e80301a0000341d0885500304001e07800e602030000210346d00c40d0f89080080c020400391000700d10a0700c49030400240140f2401134207040d2a201d0010403030b0380d1910340c0150000d501c00d0320b013111005043c3c440780322150b81c00d0068038451400749000d10743e02c2001100090866000d089803005010b81c2c0029550191160707810b880d44c548500e04081c0d002c0c40c450500b01d2070116071801005c441da04006059000c02c6001c00518090000300005000d940c440c4800c00100582c2243c40c10707103244481c03041040010842e45803106865003825010604800ca401051081c0074001045440e5440f000620241e402c0810402c2004107814840c03e0800015507219030b180c81995501b0b9104a401860340c805220342c80d0300c28250b10960761010041d50800c01b028000201c4200d400b40c0c00b6006001c00350000c040001000140440c000801c4400380d135400000c180102005821107040141030502102a4510800100452030280400c041413600e05180c84800303c2c2e05820816903610072a06000 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 8719350 1250 8718100 8718103
    0x40b12150a0f0606090b0a0201060806040f02030106060507020904030e1504060305090f0a0210050a03020405040603050604020102070b0a020309120c180a051012060209040b04020406030c0e030f060c030a020d020a030e190203 98
    0x381503446c44000f6603030b0b584440100307d014240d683c02682d81405140f060000f04000c80c151144054429002030041541e04c40f000c0d1211300a206000e500500004000350010f0320034642c0c02e4003d1700003030445102150980c6411800e42081d041040404d613100c040c401001401c0180000b04481e050040810481a6010440e0724042200c41024000007003841c40e416800385c0c0540300504400351040010603528240b0a50b1100c081d28183e001d4082c2c0040810780090b50402c4844949840e00154070b0415500140100c080a440009000b40580c81102002d9900c4810b00344405900d0000c4024038141240034070111580500b04034048480d0400800000c121040c01321081a000a4010307210000d81c00401c0c09486040c11581c2d2181c4002000314090360103612541c07030040b0076a42d082e0b201094605045e6540301c1c0200c5c07001c49610045c0002d100e07548410044d036111801c41c0d070160a08284034050380590b00300c201108040394642117203205401d0f04200c00c81510b050001c180390711003d641c0100c4d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 8720600 1250 8719350 8719367
    0x102030a080c0c01090804030201030c080106050915040902030f180312010603050c0903010c0305070f0e060d050402120f0d08060102060f0c16020909011d0607020309040b12150a0f0606 81
    0x5007404400d1001410354440c1c0020380b41040c000b40c00034010350381c441c5001c0000d64064042203011a145c04442842a4403038000c407410703900b054541500d4070000c1c2e02001031035055590044072618003044045480260350010750300601c0341034041c8007e808e28441c0c00004296204504500e03038424405002403800c50008141102e1580c100098103840b00a4004114030910040c207405601341145600d030141c0c1544240d1040c2c060399200300040542c49003c0b28241540310025501001c1404041d0021820380d2100c0d0b00b0034030003800ca410000c0e442c0d400b2410300052042c1030301c03546c020080300020240c0140d091a0f0008003440906014a40f40792401c01c402005402c01c19a4080071070361021a045481c081c840c6035070001d04036409850200e0100d8080e00d4400c10843c282c001c0d02c444039000000c0003030a24055441a0080c60400c0d00200c1403100070a00e000445500817180541e001001c103050198102c02c2c1e242c40101003091502484042c00e9803000e0b400405000c3c9050006c20880f0b9229000 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 8721850 1250 8720600 8720617
    0x418060602030c030d27050706120e03120705041d01030b0606030402010c0f050c04060f0801060906050307150311120a0b01080603071a040803030f0a1a0109050105070501150803070201030515010203 87
    0x42c1001ba42c10718a0951104859000c06401c0e00d501c5100612400152800454172260303030f4030b040180035107405000d0318490003000416a0003404000c0c12011203a44007680f100301450004e060903660301d04420405800d441020b2503100c0f02c001441406030b1a03e0140e44003c0540300e440c5141056800206412203081d00070f00b04200601c0e0801c10003105120461600400a000f030040e1501c1c0d110425040341075200e41202d40d840c0400000307900c01180140f001b19800103025204052405001c41d08400c00381c1c91610415aa81d0391500b1004031000180000400c1400c1840080c079090540e0b1045805003a0454107001d01001046940d42d800280381040d201121007402d5081142e035901c0d548d078001c54000f00b40c4ca0101104000780d4400c095040e5200b10021241030040d003038a614000b0401a0f40b07581d160029951110078407455002c1d40c01070000505c83e03000000c042c803001c41c1c84004c20700190442038803030b000043c9003025981d0500401d13421081040702c45280c0e5035080d0011f5500c0c41201c50 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 8723100 1250 8721850 8721877
    0xf0506150607080904090503030c09030105060a120b070909060f0510090e13060906050403021f0c090b03060609030708010c030b03010e03030417070609030801170309010206011703040504020418060602030c03 91
    0x313442c03844d5103031034000060441d445812207449003002c0f120b00721941c20024400b4020340c038120004603180760455484044070440d0b9400c10350800c50f9120800c92501c020420307002d11001c0400054007000a201d1407000f0b00200c0400751a440c1004104018901c8603c0310b0410825001818803246001d81c030a550004507180d40c0c0520400346140800107800700440103443d880c5030a007040103141d000700340f60001a91420440302d1004810050b01c04031140949080300140d1009814055500c1a900840e0801001015039080030f00040010345801c440d5000a03030165141c04441032055010f00452800c501d08800910107880c001004c140c0c0c900001b84060200354121080c02524842e0f0030445046540080781441502214100a00707000e1081c0f054401c030b890714030070816034084041f081e074010300b205078061301990b442c202080300740c0280201d401841e0702003000001104da07100c0c8018030082080315500d04a0065080c07281040310040e50000c400e540041010201444001c411903010412199 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 8724350 1250 8723100 8723107
    0x816030c090302040504050703020306091506040902060d0e011d0a03050d020702040603020303040e090607091d0c0f0c070f080c090a050c07020a090207020a060e03030d0203041e0f050615060708 85
    0x3882158046800d61000e0341185c58241800305008010400c10150b900990480c1c140344c4600c0007040d0740d43c2c030040c080440d04005402244035840c098000100041c001003072103081c0080035100c0d00031105030441ca810b0a0b0364401d4181c0d45041c0180003500700c0b0640c000a8859003000782c0b0040c3c0316205401914040039030000d02c000c00c655035540f010300a10707005030450b03450300d448960b0320307807074000a131030712400341c8103000004070454451940f520079950440003042c04110103c1d04500c64000107086001c1d401800d101d40c1c10310a040e84050815142d00b100209a1130303142040a450407441038015a8064000d4403c40b1455102d011880350000c0703074810000b42c0e50742d07240c04000d0180036601d0300961215000c2800a41307001541c014102c81c0d0f000f242e4070003589613120000d45583c2d05003548a901500b0038000042c0c0d50f462070380650707801030081c0081140c1d588810760102d98014210b004807020640b40d4a41030900004104542d40241d5a80c0c02e1140c0403c914005441406141c00082a000000 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 8725600 1250 8724350 8724371
    0x602030613020a08040606050409020f040b01030e010213060e0d050c01050c030903030301030b04020414060108130809030717060c0a0c02061809010308180301050609060f180702030406030c081603 86
    0x161040104000c40301002c54851009200042c1001815602510410705001002c02c80c1d1406100c2c90341034640c024482c0d8403403900038007172001410700391040505041d610620000c21520a000a24848620200f0504c25074180b45015203035148034200710b0700a5404038103900c00034000049921408200f42460782c0c0b00c09149007170915505c2004000e6415020100000007046000340300503000d5882150b003404495071500e180300040000710307071040c00a1034480118000407041c000c21100180517810062030200c1d0000407d14000c480d03482100b13040d00d52640c2d40d502510a0101d280c000e0f030001c4040b0b10345214500e000740740c0703044040041c1c4143d400117950010300881c40750010441101500c120099a1f40381004546038010610742c1c03030303514800c402481c158074040c458a8490030700104000700790344070703039051100da0b0504542e40ba401c1068000e4500520f0002400c1c80d07c6540b699004660300e40c08d02e580103054a10054080d01809040001e20803603000801109070039020510300002c031480d08 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 8726850 1250 8725600 8725609
    0xf031605071701060608010b0705070605030c070b0c0702120303070e06030601170901090201030b0319080702060903031b011404030c060c030209040204080106091b120504030207150c110906060706020306 89
    0x90707006102d109800e9040301040581904840c0803100340703031102c9005a0340c40001c115148281b14008266400804060202d1070003a8003031500440f200b2609030900b130080e0b80b000001c4200780c82e00f0351003803404030f10001140341100c10000440d10002c007450a60601c040064228000079050034480d02e004000100264420a02d0742400d06e032079642441181841401036000300000402640024106246160142000200106c009100c40461041d1000d541c442c040030350005d60080340d0111003048100d54942e0100090446841161949950003424240e018212001c0003550001c2203900c60403c0003080d0014090800c1a42006000ca1503400509089009101c0c40f01c0a1382e10510114020032110f10551040c0161000040d04011000aa106225941078200102c20000b591078940c030410000356008690407500c070b401100d0b0a1900c411641d0a2000103d500da1b00248000040c0c005008028500c00d0f01814283c0781c04040c1c4c1004800310710300d4130600c0c0e400360100d500003000c100c0e01d0700c4 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 8728100 1250 8726850 8726863
    0x70c0b09190312181a030903040e071809060303050d020d060807080a020405010803040f051002150a02071b05030d0f02070308120709080102040f03020904080702091501020706020f031605 82
    0x110314000002064907454486a030760384a0b44031a0009010420046442814580820690f145d00c071242c181c8107800c1c00b081c002c0740d20040c05041d15000c00e02c40040c62240404546010700b0240d140c805d10007241000b41c082c03001a903031020f01020700b132010401c08a03070048121015000001c40c00b60707403210482c09160103080d10b40e01443c0f42e0701c15460001003110002c204608018400c49040c00a640e8540034030740d5038013a45c000e010042180c100200442e14105044280103005801503800102c401031103070294603c1140c20710003950300003c01c1c1c420003890030074840d450054091041c500780e007001c2c04242da400d1124407000610040c1c0c4500641c40d0700030031000000716404054540d0f96078101e003400320303505800d032101c00210754104804201d0032410b000307a40654500b403007540140391a6808011141501800c182d8220340200058030142e103608000e907103e1021610703800000145a40028a46882c9a00107821500600311181c00408040f00300e032820010b042d512140e00004e420190f040c9030 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 8729350 1250 8728100 8728129
    0x130905061c030203040915030209010608040203100507050403060b010201091709030a080309010207110d080a0f1202030a0608070b0901050306040b120f0105070f0f050304150b030708060a0f02070c0b09 88
    0x1d45489151080503400002031050f01c5025500703000c9203c078035200d031905a07140d0000030745c414100300040c4440d0380314005055005000900b06d0314001807080e01c0a040354401d03680d1030300041e4000360500c24015140140200c1840078030080205908641315000d00d0f170302000c2d1140d6074280000707010344299410003007460580e1308000600e5807403d003c00a54000e6110810488a2041c0007882a00b00e1900c0580184a41d400c8001d852620100700310844a103980001c0c0441407000c041d40e2280340ac3d4031480a58464100c0071400154107042c030600500d03041035070340700000030300d800c100c03201d51640c0c400d00307503500140b081d40c0106103c08001d0009441d860000e01c0d02d0000c2c072400203501451501504028069181e6850314600310790414030031036111440b640b101000c5002000420001040030000d07141c40c00382e4880004056808078002418180c3c59440f40c4000e6000c1d40c18450124906d1281840907000108114901140e9544801024406204407025030710046492002d5803200c05400360760300c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 8730600 1250 8729350 8729389
    0x504020c03090f06030c07032d0c020301050a020a020703030e180c030117060403050912070803130812030601090501080a111306030b040b0603060409050f03071a0c13090506 76
    0x46a403502150360300d402c00d962452040c0e0160b80d1810541c01c0950071a40100c00711001d42d4540600c0d91000d17102400301c8030340d60407241e4841601c65403080c020f46101e000c40c4017568541c5a07601c9640101400e41d003026024613072451041104070406134002421038112581414107001903441800020145c160010300001c144941c64208068410700100840c180c80f107400000000b000c510710a03070303583d46046400401140080111010034130300140440201340c0c103402106c1045445a4090341507810084551083c1c0141c41420f004101c0140500404601007181c4641145055000244244160b1040038103206c01000400c00d041c216400c54680e0a85054861f95100700c140458042804c2c03c1c450400024070b0a112010140317450302540203140c030020800e500f1038880a00308001400c10540482c0e480c070449130004000802030001d03103c0b030341c015000c40200d0b542e003c90754108080d00801c94034403402d080190b200b0144030921404280d50281d64001141d686181c0856481411100840190f = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 8731850 1250 8730600 8730607
    0x303010e06010f0203070312050606070609030509010e041401090504080f0703051206030a02090402040c0e09090105071106010e0103030e0f040216030e01090503060402040902010302160302061614030f060a050402 93
    0x81454030100500800c820303618080501102e4030300726124000d0100050001e82c404583c070445c0700294200c5500060000c00461a100440e038540f81180d582d100c007140031500228146009607000241c0c80400201540c0a0001820900c00307042000c0c414001c0c0552590755202081c140618202541d118050303e004141c0d91f254107042c003a1041d0001100c55001101d5640014107034200890360b0840c0c103502405040d40307a2035a508004c00340c400540490308100e40e100c12501143d641a0504d806001c01200004e60b5082c52840140854100c00381d038851039000e1001080300301c44d2031942c0c0741100e13010b03d04444101800f00003ea1082a0700d41860350190011504c40000c0b041c19140382c10851194440c08a0001c83c1c000565551045218007a4950007130301c0082c0141c00e05812650129205140040c9441d1181d040c0d64044287c0c5401500181d20400030043c8103610b1580e5004035a01d1400c0c040c08642a004d075072481884001d281c484126160340c0812520340303c5550610190800070000d40d00c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 8733100 1250 8731850 8731859
    0x50703030c0c060f08040f031101110405040b030106060518030c10050c0601060e030a0b190608060708010603140103061505040f02090f0402040f0b07030c06050a020901020f0105010e06010c03030e030301 89
    0x11152400142c600340304120340003070340e6801031505043d215030300e40391000d01c1d81e0365843d10303c884152044150b003070043c41482e00b03900700000c5c8503031810b0f042c440300700d15201d034100000d000446101d0104540682c4c506a0184051a0040c080e52003a00a55851012515640c03001c2800d05c03100d2a50b80c1d4005640242d01101d0740d800c00e010300000f854000c01ca603950ba9031044201c4c0c102224481c0c1607059000b0580c0b10021a482e40c0245038021190309a1002c01d100d1440f41c001128550ba100e45581d41211052000556104c8449401466107240500502d00301d00c0b101c070140d20041c4002440540d444411020a640c3c404441009120041c000c000d00e81002c80140c020b9030000c022544071322030800c1400844d00d480c0c401c1d80c00303030354030000418521801c3c1203004010740c0c80b181c0c2c10b50901612845003400907203280200362081c1c03045140940c4442c0c12400180c81c004140740044480c1c2d0411005011200d11007003019800182460480c90b0300c0c4150405070010070744441842600d010010020a = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 8734350 1250 8733100 8733107
    0x207050307030305220c0605070501060f08031b0705090c0304060b13060f05091003030305220303060302010305070e0f012102030f1006020f070902031909030201050a0506040225050102040305070303 87
    0x3e03c40c05c1e031000f0460b07401d010a40180d50700703000c0e41c40c0181180d00c120300034040c00b0301c500082c0c20502d02c00e0000080e40d544a4010034007039212980190b203142c0c8006000d40e00100000080402e01c1e0070f50004100c83c03818400020103042c401881002091b070003100090500445400048260b8006402c1c04550f0409041c0c00010340001d01a8001e8015600d000041c1800d00d05102846043c481480c03950b41800d59404801504018065a482400401c200c0d04003440f4840007a598130301c6070310b002624503d1440003600350b0354024445024810303102024880c540b503481d10140741003000d01e0440c01d140316800c402c6005942c0641c1004040340301100700b090091401400303d005d0f441d0f80d00d10820301a036640c2d0490707035207203c0039a003581a023042008100c040241c1e0099508594a1421044104609944d803400c85d6027034541600140e440d4418003a46001900c142034125a0640e000c2d45888450705881921005c205080340e002c5070240b900209121081d8143c50142d1f9104090b50030f036644c0c07818000c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 8735600 1250 8734350 8734361
    0x809100f021606060e090304060e0f0d020307060215060603011404151a0702150c2104050909061f120f060902060310060806101b020d050d02010e0c0301020309070e0a02070503070303 80
    0x2100f145c0c00c5401146c03946500200380d0381207890b960f44203900300182c001442110042000542e40001d0380004503401a50148a40c2380a803545a0040c80403c0f00c22a481003a62406011140074520810041c0041c10b5040001400303e40c088c0c1f004110540d0b0a00d41c85107858080d448900341544401ca986484100c5000910f9440d0084400401e140000c403003200d06882010918800d40c1c0c0300c4820100384810716000561002d00700740c883c40c10281d4807000720710b800324110381c00b1038150003100070092040300001010300c902c3d1400c0f850307543c2071f405c1140b01c85600c00d5505000c3c1502c0c2103040e40d6010011150002c0e42000e43c058001c0e91203003480002840041880c1c025034000c9584034000035914140210701742e6082d440b9541e0712492503040b501d41c00702d905008009980054041841d04003152041040e00c0d9200d1165000154081441c2c1d142da04007244a0001c910a034010014080300d14800280441a281d000c5481c2e1100e480da038862000038070481c10010a00c1c000418100d0034582c056104 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 8736850 1250 8735600 8735609
    0x170c04020408010e12040506031b040801090804030308070c0512090a030f0501060810110d091e1407050402040311060906040806010902120f0f041203060905010b0304020a060809100f02160606 84
    0x490b1411101a09691124011b0b0b010b01c0e9003007034050000821088036000c0424903280b50080c1c00389080c0d1246046804d4138000c0030103444007040060100201544484111343c080e400345040c2a0b0b0310740c10354030291a62081002e0010507100031604440503916021f00e00002c50340b15401d140942204d00d4003d0281403a07108501c411b00072102210700040050050034094a44150501d2600d050951510020300d0340c00380c207a46034040b5010400c54030b0f404200c2e416126015880744455424402d14551a1040513008140600d005000410009600d035188020b51801110060317207692802c00451030901030b5a01a014504c0307001e000080707400301c9074000c01104071805c40c404070582c1d0341740c070a02c2510803c1c0c80b1902d1b03ca06c40d40010b40410343c81e03441180c0703c52651602249e041e54420140050720340a07000b0098090f40041408110302c2d00e896214001c040b142000701075450715150260721500754401c520b12441c0c4400c001084039078641d04489883c0001c04500e48901181d090940c014141ca004 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 8738100 1250 8736850 8736853
    0x10030b060102060903070b101205061801020903070e06030a0b0c040501020c01050f120403030e07030b0603010b030a030219080403150c030b0102031303080c07050603070c03020106050910170c04020408010e 90
    0x100314594400f0603144c1c801c400c41c10043d4640034850f51900c078020b0004202281d05681910085554002d0390007058207580194000d10040c1460550103068400700f01100a071684100800754260f140483c00008030f81c0350101c040b00a6880902203410144c40500c01010040c0c0302c1e003003001c0d01c400d10002c0d10544100f07900b114180c000b6103005598a118900760200d0440f0148548002300d22071b85400c6074464445c1c5004115812442d40c590328001040d007027118099900c104000d03980c01c0903c200814404202c1c0103060b101e00310b44019490305507051011810000f01c00840042c42614411640203640c04100e065040c5140325010300240300d04c40c00540000d0401c2c141500030742c400003c0d1011440342003a40c4081601d11f50b141c05440c4d100980c110303683d0244c05400034980d40d400010b10f118002d15280c075100290306207002030840380b454121902c07032400c8005201d40e800030304090074140d80c09581701003070b500241981c0300d2924840e0f4030081c1d40580009008941c80c40190820400c0c1000e100 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 8739350 1250 8738100 8738123
    0x90f011103010f05060310092406020309010212040308090d0f080313030e181302010c02040908040f080102120609190501060e030d08090c01050f0408030706060311030604050c04020904141003 84
    0x40070060b0358413041d18480b422100710407090001d4125030b07210641c000245c060b1490001ea85181c8400e80f082d41d40d000700090b030808694401c01e03580501c01e400380c3c0b692509400307291c9403d590341c4051502440d00541c5c06806514052030801c24a007060038640ca8005e02d505450745041a403560302001080c40440000e088075451100605020030703403209a50b0b000d28102035980c0da100360800614101c89090f0b040020014500e00540c45e0740c40b8680c15507009000c901d603141e00745582c1e032801c482650721415450788104124a40d00e601c42c0e280c00d8002030112000c954039241c03000080c42c4210801c4950300606e103803c00000d4460b4106100005c000c0d01541512015854040300f6580034404854950441c0c02c44007040541c1d40c400c80046c00407007001d804079400e040e12000034500d1038000ca4000c846103a50748070705006002102900c4d801c0f1020440c010300e00741c83e06a940741d40b81c07041488664011178000c12401c406a8480d0007080582081d559045050700d0120405498010303103110070307606c0b118002d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 8740600 1250 8739350 8739359
    0xf17010b040312020606010801090506010c1403090108090307030f0302030a06081b100207030309050603070519111203040809010305090304090c020105041101090509041401020f0703050c1b0d020405090f011103010f 94
    0x400d82c0d1b031003480161100c2e030b00c0d40e2a00545101510000301102e0401c0311310480000050b203e04c009078000c8040d680115142e8580e20005403a858010785110400e920038082200002d074800d020050140061a001d6103075210204040040d0001c1d810245142c082c40102801203030587c070304017080f05011580000210f00040c4240d80b1605d190101400181c50041c3c2841207003000307001160080050b107013491504140b16454a00040c40d00b034190001050754035100c02d4100208a1044012105520140f40d130400b996562194490018154181030701c5d880012514681801a20000c100d9810140190914041c0007030003003800700c40c03c48000d000640150000e52049024209880380500344a2094466458010ac441306101c04881c1035034081092502882d61b80d00a082114403e0310340e42e49a95111041c1c9040102400401c0e680b400c941d005580c4030b541c1e613401700143c1e0b80c058600264070745075aa94030341461200c0c0700c0410690300784600d08407503d0309000158121a400c68500b8000e9484 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 8741850 1250 8740600 8740603
    0x50616030b0d0602090d02030115060215010f170f06090c04060b030f040b040503090406030c050909010e061302010201020403020a0e090615031506180a02040911040302030a030f17010b04031202 85
    0xd081d81290403504000403100000d800d50f0080001d0000100803a2954005500182c00d4500086100704004108241084156010400c049060380b90007900340066040042d180d603c01d59038440c040549219514a01e001301060210038512140e00c1c06440302403400145c0b1503036a0181d50000b0b8000d81c600140020030000a00030380b40107500411840f4191b460b03039190901c1651000e04256031502003080602904d40d150b104400085114001c2d2401180c9071074100000f90b02c00034620042d0b641000d950115685021a035142d100030300d94142c54100c421400105d00901454000039000a656034002c20000d041a1221744035604031001c54101e039481e1440c0c07002c01c110700c0040c15015444410381c610124a07102c4490381c45500a0800d100c02801509049000d940503149070444d41e40c001021700c002d007442c0c01084c6050403824000c61500b442c0d0350110b60b8500070340c1800303000c200071801c1d00c0303598034412001010324052200f2042059612a004020f481c0d2080c801110002c10f80303400880707100d00 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 8743100 1250 8741850 8741861
    0x909020604060c03050409020a02100506010f0f050d020f04141906020a080717030a0506090601020c03070e0a0b060403030f0219021f02030904020c06090d05040b0d0b0102030d020705061603 83
    0x5000c0c080074101032405a05654a11601c0000c03801d110041c040031641c0100d41c806082201350130b80c01000241c05807030184040352406001c42e410040a0314a2a42e159040303202c003941d07580581b62055030b40740c101e04840000c2c010450001c1107180001030000d04600c40400407000042d00711500300c100f1246080654043c40716104900160b0030012202c1c0c04142c1c210003a01103140a08540c0303402038a0024887c517668021102da1801c075954070b040c0130003428030503919580310101b030005108404e55100080e039140b00c0707446a0340080c140c0c03800103111021641c110000304403014004039111521b070b2030040d01200d0a03818000041c0706c0d60000c80405241c1030148020203030042e1140703200d03145201108003001d581203400400c1d03110803c1141540d80380d520041246480035001341100d0300301446240d0500101802640411500784070071300061940e141221401c0d141c144001845e5020000142d003140113490242c030041d40301040704014000c003c510148101e0000902050000212100350100c1c0c2 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 8744350 1250 8743100 8743103
    0x3050f04060c0203300a0e040905030a08011403070e0901090b04050a030305090d09030609020d05030a05120108030708030f041103060c040306050601080907050f03030d020301080706090902090f010818160f0909 92
    0x124000c5e12540c046040740d00400200c062458080c68000c104804101500c0f41d00301c1c2103503168800500c45d440282e204040c203014107000e20304802880203500001e666251240a00e4086181c034402003884607000f50700003556640d001900028624103403c140d5200c070b40c00c41d800d501290400e000a00620008101b10000741c9040c0c40d40d80300f060454035508001c01d40c032041203801a0308925620003190301080505001c00e013603920a555500e03940d0003840c074280306900c51140c50f0702c207028540014406009699101203819011203059840f81041d45040c20314401075905070280c0c0c4244440340080500074015680503203018080c54541100443d90900200c840c2c0903140c01661f0284000e140055210b400d044000781203c0c01c02100c0c4c031902d01264021780c08030710f4030362150408014060b0043c01ca01c0040c03000c440e0440c01c103a1858081038840000903141030404c030030351000610800c0203076100ba424150078800c46c0c0c03d92006c1286100ba03040c00b40106104020803440014881031a40030f140d000380d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 8745600 1250 8744350 8744413
    0x70201140c15070201020c0f1606091a0705070902041d0106020a020f040e0709020d02120601180905060105040306020d0903020106290a03020c0a120806120303070c03050f04060c0203 80
    0x2403a0b03090030854140c4002e04200c1c1155020445040040f00401c4886104890200500b690100f40000030840380c0540c2d200001b400345542d0100035000c0040701e4a08550b14128a841c0d0300d080901c2c2a500701422030b0007044180b44081400700c3c0e0180c21340d0712640a807102e400d0410440c1d880301001e07039a58041182c020f6002c3d01c400c8449442c2e0170683c01000300c0c0d00e100022900394607103031601a402c0e6003100703210084103075000c107400c54001c4007820819044102828850749102086000c03000140705800ba1803000d40d103e10100700c580c0d20034411034008580015045427100c1e000c04002e1301800c4403103400e40066092a40218030409030010150200740c01a0860903890f1046d012107090b03030004102601031503401e00850b05088000c0c043e40340860f2113001401c150603580c050240c0301c100051300c0f541c02400840500e11032007000004603074202120f420054100e50b020324089580344600b01208065a50124000603256008840381070120302c21420354824040e85020300c18491004071015420 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 8746850 1250 8745600 8745613
    0x14030606010e0301020415020a050706090e070e2d03160503030a0e040605060318010f0203010b04030807260c0c030d0e091f03030e040c0e0105091009031403070201140c 74
    0x5960046401d001024000f50001d0b0815950355940c4000515002c56540560061900402008401d020748009801d0a00304030403224103100c1c04000c1100020003000034086600c00e413041940d1000b00c420584400a10b003008004242214840101742c0f40c2a0030b80a0b21500c080240c103400c1480030380b0191003028005500344000309504441e6802c070352662681150750b8580214907034a528004510800c80d12090282c0304c6002c5240c282114022010301740340320300c14401401324445a004440840380c00111554480f00c0e141080d4480c00080c0415250701d045484441400391003100207410019180016154404002c4e414141ca940850504c0b10000721310b200f04442070301c1c4c2184950f0b0001d24211428081146041d10201602405d420503408100481521043d520b0980154044d2045902d46500090360303420010f4954010403210900c0b400640c821696038600c1a40b0400045810151600c465060761440c40c0e243d80c080394080c1c2c00100401d581c071244103103030000c82d903400481030000c080 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 8748100 1250 8746850 8746861
    0xc0309030e061b06070305070807080402010507060e030d060602070609060203070b06060c0f03070c03060b06070c03060f0902060d1a011b060203040f0b0a0614040905060f150a0602030405010801140306 88
    0x555a0003801c1c0183d042c0031000501402210800541d03102d0400d80d01d001449040420703000d405020010441803c100400d4104001030f6441001d43e820182d1182000c0f0318030b0001074002d42103000c1d25200c0c0c0c407c02c0c9030000c0014480e42c00100c8404076900da8a03194041a21000c04980703030f202c1c507103010f09049100c0c004218541041401000013602420550b4850154582180d085500600050f174144660100500603c560380c0f0441c000044c0403100e0b03d14103189581d5824110004d4840505400da4900b9014141c540d103820110210b503000b000981c0d00e2641004541c000d10391b104428000040c2c60030045c89c1c0e5402805004691409018100d1542909035076520103507000500031240403a50b03110080000b07174105030b40744c0902032004000c95998107010340c002400d0b0600645030303c25410f20744030300013166003c5031954200e80c000c540c500460340e8000c031058240e0050349207140c0141252400180069010010740181c980980e1035000a9990741107818541400820703072541504540046203 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 8749350 1250 8748100 8748109
    0x40b280603060801021e0703030b210705060412060504030311130f0603050105030a1e0204020c03030703050c0a0c02040902120a0302150105010201091e020d0203100603051203010e0103120302071b0302040c0309030e 94
    0x81f801e407007440c1c007140c122480c6011440f070981c00ea08400d588041d108036128140d805204050151800b52103880c02d09150821000b024010841c01400c03c55545c8041030525200790000c0110761011820541e642205402000305c90110307110b00c180700300d544180400d400d0300c28003441c0e048440007001001d15080e5a1a040d028010340a2042e091507491800b000068031580007a01520940710051512894066230140c01c0d50f100500341ca202807400c00800c40082c0d0058009280030f50151000502d0008034404103500c25140f124500c200d1003400c00303007410180e000441000c162401c00400c181a641c42005a00361006a140103000300400000d00c00c1d40d800748035003159000d0000b07116601ea0429900424180700e0f1307000340c140e5502d40790502841480420064029014061810941396625044c260101c404042c0402444182070003201c5128038032980685c0c1180d5000524050380d41e070b0900080012800c03500c012802a41012414105a0300910585940c02d81548031101800a10780801c03 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 8750600 1250 8749350 8749357
    0x50c090306061008011814010902040504050604090309150504030602030406060816030203030f030703180803100b040308030a051b0309061603020a020c010809010920090c0703020705040b280603060801021e 90
    0xa1115603074a07e010f035200350240c1000c80c003c01e8650350040c0d4950407c0180300a4840040182e80110b00f02480d460010364401a076404840218030101003404070008211510320a50780080c160a0021041c8002e010203684a1402c40f05980c084600c9041c0707516100f1395500312440060360540040c00a140701d03542000c001c682c49000d600d00045d42c88111300b2a1414050415019189660007208101c401203c01d107a0101920054400b10b04003499503450706290320002304052080c0740c0301c1010411403010f80300800009801d414071161a86040c0510702d55502d012034031104c5840358074045040850107072080b1488106184e010300200620b040054034000400341100f601507503242d01a1010510b10850a1b01401c59170040844281255040056900d8050905909904100300310700c0060340004041c2e00716075060b0f60105450441c2000140400703680350207015048146152079170b10390003000144041d11885d442c03c21000361030700043c5080f4002e034810306c1c0c1d00e41c004100e29581100c099014 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 8751850 1250 8750600 8750639
    0xc090c0a0804020a0506070b0403090503031c0213050a030807030f0c050c01030506060d0f02090406050f100309061404080304021302030105150c03130605030405010e010504030507060b0d06050c09030606100801 92
    0x1320714181d540c1d038001c2412a4000902541d09650704000c3c8801c0550043c41c0600526081f0f00842c180b00d00c2e40c1c0710401140b100d0135082c0c2050780c0001c0304c1c1c400e07140340c040c0980200001800307480c1169480c24080003503840440c003100042c600ba03001e4000c29024891400342a41c20400070700e9103480c80360040d4010300307004c1e1101c6d5007c4001e0180840d89013550103540c8501c41c0b09640962a0055038042c07005507515500420720a045805018549880707100c0c43d401400403619020139410500d0602000802c00f07220100c13801c1a80c40c04100a000040008502441c4250740c4001182d00704450035040340020b0142640c0840d0b407a15481c0940e02100207405010002e02c02e40740340c09020740091140d15100d910501c04100302000f00401c2c40070038415101390b042d030007000784800e20340355400074481e10803480e00905040c0d0760141c468503511800d80b407200c201d600240030000c0d410716540640c01c0d5004070a040d4800d11070440001c4040c00c0040c145600d403001c644644d0b0182e400d0500b05980c60410800 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 8753100 1250 8751850 8751859
    0x402040b0f0303030a020c010e033a09030c03080a05010e0c0a1403040c03140303040503030a020f1207030213090b06030609090a0b0c0307030c020c031c02030903011d0c090c0a080402 80
    0x10907072000c0c0d41c2440258041e011207400142d0301c203c6220303014255110070000c1c10b4507402c188000c0e4400314140071051500c0031805141c04039141001203c94003d80305411016509140109a408140d001000e910402e8000d883d07141541c0d4640100405842c824050500c0040e804004581c0d01c482c041c000e0704480e0a20700300a00310f10030448141301c07160011a001c0d600607400b40d004000f03001c0c60708030203000354403148040c40c41d61626486031590303880040c1010300c1c40780c0d00280b8400403a4120782500c00083c0b0090071395065091001e0000d01075000405149101c3d0341c248c4c4c00140e001000d105440e41018068039060840e03070350404000c0110700060221400780100001040000c03030413001c1324807803084600c9041d100c1c100313880000c048a82469401065500c040b180c81003607a0300180c0054000c01c0446224155401c14800700d0460040e0b080e040d415600b000d07410080d0074485004103003001d5803c030446402d00071910400c0300c84181919038041100c0c0800004c003403103104451a40c1e0050000c0c0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 8754350 1250 8753100 8753119
    0x20319020c0309120606040c1d090c0d0c03050703050c04060207050402030c16050304140906091602010e0313030204180803010303050904090c0e06030114100521010c050d060602030406080402040b 86
    0x80208041000c84e81a4803140e8029808000b110710b81482942090341d240c1c60034560091410452080c02e00710f81c03000c46e07c01c0d50501c0c0010140202c070000c0300e6031001002c074144543d0403105400780280038142e54010100b0b0503d400030f41050160001d603030480321958028a0302c50700d000140002903101a01116441c00d04110703104c0b442d02d851588002480c80342c40107541d03444c42c1005038551282d10510003407003100041d060000d5951011485071b004030484e42040010400420309900420b001c00b460745580c080425601d0035030301030b010a4000c0b24001d036000d20691803164052180c20341c0440c4010001c80080c401400882d12481c007400c1e1034400a00000740040b8140ca611048410a80c010700009402004001e0386083c2070040f800c40000c001d805103894207085c4100304402045010b060b0007540344400d8025501440c2140ca20610400c10080020324140d00c0c008000c2e60041200160140c00c0002c001820391000080700d04550180c0da03817a4041c0c44035030070007020303211421480340d0118081 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 8755600 1250 8754350 8754367
    0x100e0a030501150f0608010f091a0306010f03020108010b030403050a08070e06120a1503050709020d0b04060e0601020f060129070b0a050912070b04120216081b04020319020c03 77
    0x3d12031041c01003101800300c140c5a24000c9044942c6006030003030b00401c00007800400413100f190310380100799030140c0008950706029109030301000b000d40060355450302c1043e000084401c8481c06010a4900070b0f03031490000d07a21a515007a8601c41500c0c018001241040050b03d02841010644e81100a61801003504030103280001d0090300501c10b0f07282a0070b145014040076408911030a0390610303802c00302c8950b6924541f00c0a44440350362060302003040d00001c0516032441035512102d40707541e000b0820000396032108040e50789404100c0c5c60901500c03501408502c046400a0b04504030303003040c50310704602224040082801c106511500511400610080001840350407202e40f141c0000c060004013454168040f508c0c0452103085407400030020000140841c01c21841240e0160300902816446094103074124540b5180620442824500c098085501c180104903002c50000355004880c01500d40c0c420001244400d40e4201503141142054000481e800e030060b00c0c01c9030080301503e0401342c91 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 8756850 1250 8755600 8755603
    0x80105040203030301151b030f0909200901050405030a050708010c050309070501120609020c0604060c0c050309120c030604050115050a0501020303060d0606090606030905060708040b011202040902040f1406030606100e0a0305 98
    0x74807012004074020f00070003000c9c641e000c4880700003000c264030b042c080f00c0301c800818112012a200362500c200b00c000b481c52541d90081c41180e00804010307080f601d1400c064101152201c0d01405854401d50070000808001840340d000e5138040c4003800003030f0000b613160000540c1d0011075281003c1710a9125580082c8e00078441c405000c0c00341d4010082e208038a000d1400350111500381c1c040a0901241c0c000d8900410800005d550100c8010b03100c0701440410707048090700e40001d500c0000d6040c80768000700002c201041d0001c000403a0451500320b9102c3c0c031201040021145070241c41e005034402d100051031480c0c1100b03846482c0c0d02038140040d489803502e0480099401c5500318001013a00c0f0241542003100410180358450103515268207541000c0d502c0f0044c1180620454201c4070780100c1290079507650368400152030b58000c0c0308020b0304603900d80070300140c058141d4100c0b08542ea80c0000b441410042055442820014401c00c00a209144103840c60200c49028581090440c0b0011000480 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 8758100 1250 8756850 8756897
    0xe060705060709150215090c0d080a030b040204050f06130306051008160e01031202030f07200a050102101a060403050f07090204030f0602030402010c0b010306020405030708010504020303030115 85
    0x80000d01800d14260350060800380241d40079140344240e02500c001843d50100e8107520070a00e0884100043c1c6821f12110710300043d4943e0f580d4019100740c115030401032101e008080d0803110b031b201407040c1041c0400f004101e004512807543c01889002c4024854a0100d00a002141d81d070301c076018016842ea1207640c12074004036a001c03030100c01c2d40350903c07262004004001e103184a90404180c03950a00440c00c80113071041c44010401540074036601502c500900c16500881c00052405440310b0701c0d410310100f650041022400365601d400d08218081c1403010369401030301c030103800400b28815070000b002e0007408403403c014000e0700001c00038117941e642c4600400017140514010704190320891187ca0034039a107139001e4100584108403c20000f401000501000b03900080c00603126a590300059a003000b111000500e045900700000c8108440750f400b1300280c070320035422194480d480711001400c958040c3c5010b545540240010849285007070460080300c0c0d420701d0091409080308540b600c0420 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 8759350 1250 8758100 8758103
    0x70b0702010204060e0604031a070c08030a0207110105090a031403040e09010509010501050108070c0209040303020f07060c0e040c140703020c060c0102030108010b0105070201120f0b0303070c05190509010608070e0607 95
    0xb500003404006441d40840040c000b0042111010700d000d01e0f40d41c03032400c078044501a4501030f03011040080c029900500b00f1000741c90704041300507540c0ca089902d280084d4040380048403100003111500005d54420310550b610044d001c1e00250b189811511000540c0c509001c0105540c80200800304003071900c0d0021500580210b000480c5070305040380c0c814292001604100e042000c04130030070003010752061030f40804540658184080c1e440c0d60604501a118001d44242c0d040c00004191082282a41c00032900700240c0c0e803000c2003014078004000541c2d4038050a079000403013412446030400d080e00024080705210b0300484051112601c007041d12034118100d104200e95010004008004080c0184103901c6001d1901d28a0901170b80e0021741207541d4000710f0492280e40390764400060074503038445601203800808a0b500c80500f45001800100319019541c012061170048803d01d00017035101c41c0503560300800c0240141e00f056000c5400d5203004000208008000350380503400e884150080565a = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 8760600 1250 8759350 8759353
    0x603050312090a08070803060103060e010806091002030c0403020411040503070b0c010b0402040303080a050a061a0a02010f0b010e01080403090b0d050105091302060a1b0605010b1207021204120206070b0702 90
    0x401034449070030461580284511041d800902c0740c01c0001d50044c040f41e01c0d5076030210526440c2e0700e1702d0004070020030058016600640301e0304e00228540c000003850901c0740d0307910811076051406220001c0182c0c04142c0b091191204180004e00042c6001e4003c0c611150307020780400e003095610760020346412425801950b40010001d2610103d0344280240c3c00d041d14140c03025442c151540d035000b00b032191f00401c0c0540c000d66400c00f28440c16038a8100800034003044c1c920500001800e0182c12641d8040d03c1140059881c081e0511080c4141e8011002c20010503121210070096950055451072401041101000081600410120140c1c0b000e03110007200ba200001d415810441400503a4401030305207020851240c0601c0d005a9070041100c96840c000e01d0100005900c684030000c540c038404d0402420305041500205801081ca0058030101e000f214000290b81c8541c401030742c48940080304040c0700c2030104024408048440340c00c40784644090903161a0230065204e40d40145030030381d0100c005 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 8761850 1250 8760600 8760607
    0x706050702010212090d06090609061a030106091b05030705130303020703022d060c0304050d05030c1204060206010308090a150905010807091206050903160b010509011208030a0e0102090406030503 86
    0x19940d040240880744c1a200865620b00004140010400c0d07050032001401140c5440a20702040880d40107140c4503079005406000c2e000f10034800c072100841032106140250310b41000014081268080e6954070091031412580828001c0c000f00c4066000078032100501c10200171581c03071108003207180c0000794080c2c0d020b4042982544100919250003510040030704510030103c84a180b010504040d011508850713499035a041040c445055000e0707584125844001c00410300284100030008201c28500e000554072814481c9240f0002402207004020040c0d01c40360041c00003c0c1500c00038002510001c0400004c2d40c2c0c0c409103488980c04058000001030f0b140c481c2001b065070044a4182c1000c154100000d800d070030708003600e0141c2980880036255075140c030049007080c1028412108a0b9116108440501c441d1f4140000c00e2802031082c907000d5403d0800010721400808000041150300c410114519100c0c0c1c02224094000c544402c00d1070755003000603424503511407080070010362060024585 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 8763100 1250 8761850 8761853
    0x2101060311040e060f1201020d0504050d090b0708070302120316020609010204060507030c0206040e040c03050c010311040510021515040f060305070513060f12060507020c01020d0507021207060507 86
    0x95400c10720a441c40204140014070541c0300e089040c95020906403040100350519400045d44036020b000c24210551000a54802c00546600b1040c86903019008a920740f07030041204483c0c0d482c130740c03040101403c01807288000040d642c400911100d03000744100c070780c2c400c000c200303a00c155841079664403640c4d80d140c0805810785406010403544404003800071800c0514044000d0701922541308000e0401002a0030340045643d100141c901900b0030001c000c0c0b41c1e24092408840203951408241d0f520b00c20000400050340c428024615110000c1c150542401d2608007405081514616804298041c030041d004d070508180c0500351081d10a42e4100700400282c40611048500b00301c4111103da05040d41440450000117800c2c04503032003981d0805803a040309072900000c004540004040b2a075000d40041d45202c1d1440044204c0c3c024401004103840f034410580c0d542601c803551a02503006009100081d60043d000f500020340003038401c5446101702285a4144605604250089803001c00c42c4030 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 8764350 1250 8763100 8763107
    0xc030203120d0f050105100c0305040b0705150109020f18030a020409030201021e0304080708030705070f0507061706030c04020c010b040501080d0801050d08090f060702030102030406050604050603031201050d08210106 95
    0xb094010b043d80204019410100850209100002c00c00d061081c030202d44001c05108100700e6009011184241340c44041c43e1800a8031001029540c0501c2607aa1740007044045c2e0034421107140407540143c261900e20300c0d40d0300441c10785401c4410b99040c0503807050140962607a0041500d0117100b60300050380c54034581c2c4219004000c2c0440544c030503101303200b04800107910b4011a010b8540000c0e2003a260303a02c0e50707000c403840c1c482c107140240118560a880380c00c2100008207501642c0c07035600c801611105013010144513040841d1030316410341c000c18100c11203040540c001c12060114200104c0d10004440106041d01d00aa1140c0e11683c8103a0240b0070481d030044280f405000103e800300150742e0141c80d2050240070700b1080c50b11850140d4000102591820300304c42006501600a646074941410008000d0108a80050065043c800000c1aa15000c42114907690002d40b002c5a0342e424401070080343c0944180c12138010100b084080c140346a824591600e030705600c859400310b9030410034002c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 8765600 1250 8764350 8764361
    0xf1b0e0907090e061201090512040303080c0307120e010b04091103060601020609060708060d020406060818010c0203040b0f040e010b0307030b0301140408210a0606021b06030105010c0c030203120d 86
    0x1501081102c45080c000a045903d80b2a0000e80846903c3c0c030003400150180c3c010450001d0042880c800c08020031304a080f0302020f04110b03402508e480040e581d40d00c840c030300e0b188000c4031004002013808080e0000543d071030780949a4880c40740000148003c0300ca020804070b5040b00300580c0c2d090702c900810391551800f004005c1d4048401e2016001381d0414484459072400050019000d00003500b0001c0c90036100d48107440782c01c0c0e40083c818002c080d5500c0001d0042d8a054414070342c100603882150f28000c4050103080d100c101d80d5801149440c3c03404111460356044115120308401c020480000c200c5080c162241c081c20121136816030324181b644010303048a105a504a00036414644102c40e1081103055090303120703811140c140c0d9141da1603a0761200034070010080003405003070b150034050b006080d9401807050311461b07000c55520380c2c80e012300c00381280427908080d9888002000184803d51182c0002202940705034400300c1c605449070f00017800c05841000a402c3d0032400316100308420460b0068 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 8766850 1250 8765600 8765611
    0x6090609050a090201082a030a0501082401060e010c05030711030601060306030f14030d0504050714030304080316030207030c080d08010b0702030601060f170c040614041203030f1b0e09 81
    0x801950f502c0380e0001e803910710014100c43c01d8034841101800380840c001b0f4048110403200c4000fa80d2880d0895035240144420f0040e28041d00c121880f041c1d040c0500d001a81a01d4142410072032241e103071080480f14040c07016026410030902500120000d1000c0000d45051486091003083c40d1040b402030500d800e2050f4868800c047c03c0c40e40410202d8400b0721416011034018114080e0141643c8980346540304031014070740c0051420081006011002c103280d002c0c0c80b40c290381c242103080800200b5941c1c0c0207034020360100d034004000c100080c8103440030070201c0902c2401070390380d42983ea0321041c08203000c55010860b1130b000080c0c0c0c0c41445902003082da0141c00d000c903002d4142101900402e0340c0b00c605000d8401846100f008088030b16000f18015000780b403403145510032518004068414a410500c0ba010215840002e2507407003902c3e001c15241502d448501b010380190071707134900700e002c1d01700803c0b0f04489903901c41e8032111300750084601c012020101d03194402911404e5040c458520001481c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 8768100 1250 8766850 8766871
    0x5090109080d09110d0809010305040201030209120604020901060c03050904150b0301030302150709030f0209060f0303040602030d050f090a0f0303020d06060810090209030c191508090c0103140703020a090503010609060905 97
    0x80300000b603c26802e1f03400d02d00382031900090030f55076407006a00a108001d541039101c4000c03400343c01e40c10000102148102c0c401c5d18040c00607680ca003403e0700d000c207580c00010b02042d001d01221110742407a50245a00000b032b804100c5425585d0500c00c2030704d034800e0f081940180c00c244007420102070100310580d00400c0750724040c07003c2ca180d61241074801207a80002403241420b0f8011590716600d201c180030f40200002c0503260b55960740c0d000a99240e20801000d03a00500302400900b07594981d00b0400e2240440d040900b40107001c0e617490082e0202c454178110181070f4288420350082c0c03580c3c421000030b04002e8682e60b9050500c240000341090700c5501c205100381c0100b003007000070746005c00c0d010054941074500f152210748440491160702c8407a00a4140340c980446069541948041c565010b0341005040c3c40342280a80011829a40b4041042da804001031000c00c0845110354000d140692551401400881d110400a4250344059100c010740300e4031608288001f4a15100b0242c000c1e0780c124 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 8769350 1250 8768100 8768119
    0x40f050c0904021807020f03040b1e0304050a020d060e010f0c020f12040902160f0501060515040605071202030d060605030108010e010e0a030302070807080307050d0501060512060405090109080d0911 87
    0x1800182503099180e0340709880c3c0c410310080b1305c1c064000c00444502900c5101a03039283c5445100035440d68005582505005003181082c4000700c41d60001c0307034000d94004000c1c0500d01015002c0c4030300d15103c2042201c255a45080e9841c90620078407948044443c203200c0401c0350041444001e2a1401d041e481645580191a5070311218403070004540032250016000350f00c40b1741c1401c1d001201d2041032000303091552500c1240c0f08224040d445002a24012070f608014059000000d60243c00f80c0d000310b00c0070400401a08020821b60302482c0c100301d01500c1101d103043d0701400d00c0016610f032540950007003040440140044842801124690720680008026602c455181c1a9548a843c4c501400745a40000c101040c080d40748102c50485070040b0b2035a40e00d040c031000050040d4440c62451070040c0c50f000c0045201489070044540c010144a15075103541c840038104001071401500400c410342d40c540007200000c04c50f00c05400014241c0d0000110075005082c466010641209242d00c10700024 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 8770600 1250 8769350 8769353
    0x308030a0e0607170721020d0e160b160204020a020a1101020a0209010513060e090d020c010c05030318010204080f030702040605010906050a1d060304060903090603020f09060702030109060203040f050c0904 90
    0x50300b104d0307030303d0180031440b43d984511006030358100c44000b003001160400c0f001003403041c02c15001440c95005030306081140071010300b001615540821180c1d489201e82c14400c10201e590030f405815030300414138820304071400903030018040741d10000d10032000d45c0081c40c00400340401c490315008a1242070000d48180311a0381d00240590605014a0b03124822034800e440b178500540c0d000030f01801c0054082c505a040101d440c0d0390791041105000f00610800e0f4042c3d040f5485052201d42d42035000c3c0c0203506540310070b1303010391040030702a149600d45c2d035003070200051031a401c1055050b00440c40000d195229107070300500c000d031103030340d04050f052003d076040401c0403951001c100d030b00040388d51038400410440320402004107000c0b902e0503070303000b000442807009006d6581e001d901664820b8035690031040d501c010540503401070841000b9094030500100669090590003820664401400001c604407a551910226003007030790113840c0d000301100301204002040009101c0c001c1e0444000902c1e1519 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 8771850 1250 8770600 8770607
    0x806160509061e07080c0a1401060b030109090203010b09011805010f08030301030b0901090609031e02010b0604060f09050d08120109050402060f07030c02100305090c04050417031f0308030a0e0607 86
    0x60220f090700020034546040c4240044100780d41c00c0c0e079840700d141030f0382c0c1c02c142440750350358440d100c0d003035980303000c2030464051807401445901c1c00c50b11100045810342c0c2ca0090b15500900e800d24060303805540307603400c80c1c625680e0340401c907001c1d02e00702c445806802c0902e9284001c40d14141c000c901c264a0b10f40003400a284004203030f0b4116980a003c081a980c0d40341205400f40c42842001002c0d01d041000c03010405070003e02c19010b07210180c03085101040345150481c280c1e41084120b5801c404200001e118440c03180804020351101c41c20108140b42c0c0e01e901003612402c0038542558007020100d20840300702810360816004112140040c80a41029000100c06201e0a10060840c850000e6a8030800d07004c1d01442e868140c0082100703403200000382d80a00908000c4803a0345450241c41142d1009203010310500e80a1900b03d03c002800c03801d00c625014456001a2064491018080b00c042c20304e01501d80120286208582c0c1c25181c0c1003040300742c01514048030143d1003036045001040540d952 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 8773100 1250 8771850 8771857
    0x70b04060917030106080402010f030207031d010203040f090504030207050303180607020f130905010e150112030504180c0906050414040504020a12060204051905060f0309010f06080616050906 84
    0x2000140081d80105600d0500700380c400402d61100203040200000802d05c2c2c10090035071041d4000c1c0c80d05445420350410072402c070700c00c10400401281071030510301c00c82c40120140c454071a83c1801124905507c442804032440300d9035121030750594640302008105a814400200104420340c021400c3c01025205000004032009980d4001c503004501c20b81503541d04181e11a559078060030040c2c82007088095a000b900300340406031070540c00c00d10455010100003400900e03942514a80421a9007441c1d0400c00d8601c40315026400c0041c1440040f810b624100100d101e48410f0070380010f0102c01102d800b43c1480003e07840f003070500209210400134800c01c0c00d049041c0303100c2103800044542d40c9100044004841d40c019000551350540b4000030024507500500513200304880b0100342040300e019030240d50341503014064000c103050042e0152078002601035504040f0400001c140c0b03556000ca201c0464a241d84100d007940e00c0310381030050b402d00c10245502c0d4005280780c4980b5003c440f8010407003612 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 8774350 1250 8773100 8773103
    0x31b050a18050c090d11090f070e040203090a0506090304030b010608060907050a020a05010501120c08010506010c02010f0e060a09060e01030501080d0f0201060f17070b03060901170a0f06061401020102070b04 91
    0x980ba5400522000c4200c41100d40f0448001e2500103078031518280f000250302022600c6002c1c85031130002c14031080c01421320030b20440d000e654400718001d008042c400030350005060080d0900c1a15840e50025805221140c80f4034039a200844c1c0740e0345941807103840c046e4180d202c2000c1c00b8441080c801c50f516241d00700f07a44000e0a0900c99500c1101541c01c910b020924607018200b07502c0c0030300110b0308120102c141841c0f580500c010600c0c0c5921012924202e900980d001030101c0c0300d01c6401b00065000c1c0b90700000d04c1d0341c2818100c16219220000c281c0c0c41d4030031100200054a206010f100042d0000b1800c0034154080c03804000b150304280f405681c1da003561004c0014000d0300e1554600707040c400d410801c082c09840340c420304065a501300181c560350100c270b85c6c5c0c405c90041c800049072081600096a205000090401da9103928148146134074420603003085100d4004c00c041740010804c0b400056409034412100082c40700e1a10201812525000d12000d04690040000c1c8003c9039040c6041030300103 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 8775600 1250 8774350 8774399
    0x7090608010b090310050106020c0f030102090a03020111030c06010e070912111201060b13080d170103020f0406030204020a0e0306070c050a120309020d050604020a0e1e04060b0604031b050a 83
    0xc3c030300080000d141400304601c03000810b00b003000104403107601183c405541d40041e00c00c100244500d0041609034000c0680c1d81c2d8100d0a03002003000958071801403001780c1901841074034034000800d050705082603000d070803003414021200300344003940742e01004810003020300c014001454109542d6802c480e4505000c2a03200d00c01782c84454245800030b500400c000c3c1000d901b42c40d5a030210b40c100704140e80140c89a110702e401144200e00c0c610b4000e10b4265031603004481c400c0202e80c04c607030030044007040c0c5103d050340013540d0700404001601e0354401058a0f003250745071101030300b80300c100701450f2140c010410010407104800d1680001c000040c04510254441d10002e414100300000710000d00035800045d45c45002c15410001b8848040386003805140281c400c0602c040c1c50f41940180d0000554801f40325003000080c40542c1c400c001e0825811038031400c40032400040000c0002e940381c0150300240d45c1e080f0100c504c203990314040300041000340026a081c0c000c40c1c1c03505050041900c08400b0442a4 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 8776850 1250 8775600 8775607
    0x91306050603150f100207050307090b01020604030f020c100503040501060503030c0c060d0b03030703091a030717040203010f0f0f230601080408040503010903030225210c06060303020105060907090608010b 90
    0x3542e0303134815002181d560141c040e40d200c4462400080d902c0300d0a1003a1400b070f01480d100410040028001d0b0f030158101a00144056151035a0889104141c120210118040c200600f600c5944044090148241580cae60380e49038142410704608544540d84124401d500c10000f40844c4000828818003441045072800c0d00c1d80404002c440c0038100d2240b0007035241c00006041001c0641050700603098400c10100f1001620000710300303100030301c0280c039010081171140b131502141c3e04401c0c503181d80c003510103000892503125020904041c0c03541c004444611548841120401e400c1c00c0c4079101521030b082070341020310f840c02c40e2074094800303020b4140d6040011041c002014003c0d450100d9000f003034094000c005003041400c0003002034100140d010510b040c5429403070340500400100d481159048000d402c0005030f00c0f0251501c1000c01600c00c400e10914100354404141c81e48602c20056010f50004140341c50715008010f0083e900400200601c80d0b0000188006648590f5a03415640d040c846140d4 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 8778100 1250 8776850 8776891
    0xc120f1409010905070e0c12070e0907091404061208070203070308030c0d050609040506010b2d0d0c09120b0705070615080c040e060a020d02070b070302091306050603 73
    0x94141000845000318828041c008142415803100c0846402041910170041c0c0b04c5259480019090307543c1c4041c0402405580c0440d05041d0708550454441c1c146070f401d118403603000c81d602010031034041011906086c4104641102a007a21003594001c0b102080558140303c103004d054500218081c1064002140350411920300700100320107580c200e00815101e240076501c03454254002c6441c04803480c1008046451401c245950501550740080038140503070804800c0707011a0000c034005610b81d01c2034420360940e0070b0102c40001d00c0340d130501000759032208585082420340d40c051013024104480300034100442d0b640020645241c03a80000f04080701d407a441811a058003955402426035481c5c4070416561a00c074000c0328041710b03058019941100c2c11141004200c50054042100c15000100000d5110343e80341e004041100440320018207114481d1101a104142198801f000ca5400103a2400e1072418648080e80340000070018040c0d28140310104480d800050200800040307510409603 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 8779350 1250 8778100 8778131
    0x606091503062301032103020a02060609040501060b0d020705010507090308191701080115050f0f0f06040306110c01060b07080406050a030b1002010f050f0103020a031407030c0e190c12 81
    0xd5010305124043e10095841e401c00300560842482510790400b2243d03040104079003e070007035515080c0e454025140c40c3e540c00742800300400700100121915540e880c5d0105544d0034140180c5003240040780010307101c250301d10b065801c444003e0401c200b44254001c0800002d644107007103c1007800140036100c00c202507524242d4521140d1030390700031402c00400001c07407840015480285484080000c2c0c900150b0b65030188198401004c04e4150404414658440f4505007032580041ca008040c00451402e652501e0b104104c50b040c013101c01c074100000414000d0b4901c02d000d0607001c0c124503911140707418401d994294562107a48030323100a00c4000308602c140103020781d114803041407000d030000080c100c60030340003030080814000d521a8149048045010100c1138100702c0d0590364080c10b086071a5003503490b03800b40c12500710f00d00040380c0f08442000c00090400d5078540003c011a84890707955003085400d40007000100b0070911806454040b4008407550b01804c00400c0294042c40050003001c903880f840d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 8780600 1250 8779350 8779391
    0x50607170c0a06090605061912020d02030303040c05010206010b03090601060f0309050106030b09010c031e020c100903020c010e010203070b06060307110f03030429071d0d03020a060609150306 84
    0x4400e4042e0680381024007200360000c1003128401c401c1004981d61340e40030400c6591114500180012a00c0b8081c02228401011198003a000078108900c5584035800285140d0084400b2140341070880703c10007055030100805409030820000150070340c90680101541d03003105201d004d082126090341621030902aa010038032498018009101b00354807400c20f16400d55098410300030a600e854034103000d03688a0f01c0b4010b004040864000001072141c03005d01c0c042c0d042185d40210901440a00b4800e09000d407113254111031198020b02107440d00200003404c9001041d0209040d50410081100000c8410301070b01e50000d0100d8107240c41c0e4845481c1207500c41c4240030420054403629812030401600007000c1c40c402c0c2e1058080011a2203151181905032079075000702801401c81c08049818907014409213500c00c070100104418914182d8002802903800c40c2c020380140c0c2022106005100e03c0b4051b080207094910828050001551440d00740514140300161100380e0b100584205500540300b603 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 8781850 1250 8780600 8780617
    0x7020a0302031c020c01020c0607020d0c0b030a050103050c0402120703090305040f03030509030106050103020909040b04020d150516030b010c02010c0203030705070b1b070b0403030305090a0b090c010210050105060717 95
    0x12550f41c4030103001c0030f6081030003250303421000d4821100702c070040350702c001410300180c0c0c00908201d00780132555007031103800384030f10380200c40c0c0581c41e40b40800e080c4115809140705a081c4100410154034509016040000c0814543c6c0114010802c06a801070003500b6681c028005140000d48840305040032a003a00a41d080740c3c000c28030b83c0340c2c00030070326901c0409004000d00c12002009015070340c80c0154200d00c0703a03003105504a0310400006012640d481c04913680240042c00880c103146517030f07603141d03a9280b08010010809503500c060002140c21000064144901030a0401c018a444000030709071101451000741081501c0c1409421500c00b030040d190003d0b4010103c5241e01d032a80100e9205802800001d0240640c00d4000115080c00058420499281080d454501411901e044010b03040044c41c18429200b00d1007800d0015140f245042d1050340103002501040b01d505000905056074003541c00340090802c00107104d243e030303814211000d803a07000f800c2d021801149a1082400d009072103030f = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 8783100 1250 8781850 8781853
    0x307090305120403030206010506040e0403050f0405040c030203070e01110309060903031c060302010f03060f050105030603190b01050f04050610080601090e0907090f1401050103020a14041811070803070507020a030203 95
    0x80030030501448501603c2a0707403090b02510190303a220b000b8030845004038070540413041a00c0c00401c1c00300e4040e00c0102207164074044a0b034501500c0f071001c40c060300e100c0980000066400010016981c1d8000b440d040c0580003445c0803004c88180d8440d442c2d0302e00601041c42d00c01c0d08000307510500356500700101c2d284480d2450008030031f180c030f1034690f000802d15031109a0104001e2002002014402d100d060150343d42c4000c9032035424284801150250030050400d90144582030100fa030780341185044030942e80c030400d4082115030411087c02080698000194051410001840020f6442ca0840c850513291850300d01c07002d0b669400120b03400c40440e802030f0080b8100d40180540c01d0000701da46000c0c1d400c011014410050312880c0c40085801030300c1c844007880c14110050129600c690010320400100707182c1a07050810030344091107070764096403104601210711080010901500e000d618880840c1410807800c0201a4868900c18803004000d0010407500040c41c1d400c542e110440c41c00503640150 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 8784350 1250 8783100 8783113
    0xa03060c03021b03030103030201050c070b0106030903121b02010b0102150c03060109050d060905011103041a0a06260705060901050409020c01020f03040f02030705090106090e091905070608010506090904080307090305 95
    0x10f481d0b43d1668030070300040d401542000b000071000c020709001c07601c025500c840114066845c001d01100105010f120460070040c100964111498079030091614121081c041d20404484108003e800c555402c40c03250705540204a134002e540d00002c0140b80e0000d6101c41d0546e8130b5982c0c2c0d0041b1554040c43c1c000c82e51150350703505890113205103588080c0040784100e00801651000e122405000d0100712401001912161107010303800c8096503070b05410502840001c68500d4485c002e84d071192340000440204000a00c0760911910003c20440b002058140d0b6034038541386480c0002803051245001d0206200d40010307994100c1c0b03009604880504030020310540d100d050600d0a5480c107405c0e503030306900c00e20403140081610f29108034403070f0481d12039484285d0340d60b103451154110800018103901c128010408545008100404004038451040010304200c45c14080081c100180c10b8101502590003840313000d260352900c03d4072541050f0003410301a102d40e035000c012900403075113070001011800f810 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 8785600 1250 8784350 8784397
    0x6150908010c030b060306120a0501020406181205030f03130c0603020307110708070501030e0307020301090b04020a0605040501050708071b0902030604061a0702010309050f0d0203070b01060302090a03060c0302 92
    0x2480060a589a21000348200700c042d1408030150b62910416550280040001c5005480d10310300c4892112031510030759507000c405440d1542240c00a034044400711b01c54140807410900100801c00c0502440414220302c0440e945400d542c2c0c1c000c1740307500141c24500101041100f207100c81070454155110000c0410300e511900c1c020081d400a95070703207000c140b00d101c0782c188a01010170808250f0302e910b001004058582401140502440c8407640d2241c041000b20344e001d80c40a016030020a4042c1c0058421410188180450024a5440700c000c001090000380314a070f0b80b100072100540e030404451520f80d0110308040701c6282da0203110a920701306801c40000e04c01d016401862054004030740c200043c940c4c40c0c64100081001d402d905694040400400b80150b0103540701e00102400760048550703e091700c1c40081e1a202d100101100981d101003254402c11007800400f43c050300891a0030350a060400000c100c0401d2a400000e05180d254904080040d201e40d05440d05000d0035030387e006058241 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 8786850 1250 8785600 8785607
    0x5030408010b040b0f1e0609060d05010e07021903050304140f01050105030c060403022b02130f0f09020d0210050c030d02040806090604030c0807060906021206032b03050a0615 77
    0x1084201e01907410001c1283c02450036040ca5084c0900150003140711502d0704199100c0c408400038859480201409091100d82700c25015111414030302030000781c154140240740001c070300000d14201c1194000c285c0b40704030604d07541050455691509200c0e03102c0d111440c02c030f1240d0300a06d0300078041d0310406d03018901c04601504501e040303030820750540e080340342d8120921206114602001e90806801180e903250801c0710910000c0000c0c910544000900302a80024810700305c134400303142c0294030744181c5020a10b45116044141501c01c8041021440580c0130400385901480d003e0b11421200e1100500540204201c0c4c0f03a20b6900d00a0f20340d41c030042c025180007034101d400f80e1825813140310700251000000080c05402150540ca500d4401e124503610161b5a601c801021904283c82d84241d4000920500260603140c1c83c1c0c1134071404038509002811f1030028095185920781401c149051401144400751104000444c40c0119480e80c4849004010b41070941c02012a441c9410742c0f0210160f0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 8788100 1250 8786850 8786861
    0x90602030a14010b0a050a0e040f0c0804030e03030405090105010c05070302030f03070506090706050f070503090d03031e0902090a0e01090803010603060312020303010503030f0d0b0a0e06040c081303030c05070503040801 96
    0x804903164041c2d0b00c5075043c10481c00b95080317420115a0402116602c240900300e003034074440d402040482e542d402010900250f404406403800480c01003c103120030581c024541201e5050306400542c04c044c542030015001003010701c135040c144030305088031406014091080b00040c54018045990391a00c1541c80c0769284c0c40310b08291b0307150284401060000303c0110304082103c0003540c2c1e81341404900d500408c525070018400700da041c4400c1004004649854003400c803c9400ba03140001c54210000d0341c039210001c2840c180c103483c0d10b4140340100580d20004040c2c0c2003541d21000049114400c0f203e18010455074001030480c21000c0000290203a040c0c111000b944d210720000811410414001e90f6680428040c00d5419002484000003001ca003802911114036082400308000603288040303048070320540c0211041100c07503403c1203840c3c140340c001e103080c05d2110f2818a09a2070900c6446000c0510008020304040d119000c140c0e9080c0b00d031003914912034100c03085e640d846560b0114030b8000d0a = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 8789350 1250 8788100 8788121
    0xb0105100305010e010e0c0c010626010516080a06090603080306040b01080f130c0b03070e03190201050306060a02032503030c050f030411061e03011a0c0a030c0303090602030a 77
    0x2069a40c8a031461003802054101d03120386641c1034190342421b0350030340c5440c030081086544800902100311528424080c01e4020440442e200100316410011000001d11f0295a04c205078189010f2000c1d824110541c1180400c562270a084151264a00b0801400b003070342c41070f0480e5003484c4d004020300c0a14002103000c0c14040381c042012450071001500c0d401c0007100c0c400d504441c0c0034001030000d400313145c004010621a443c090340064560003080d0840d0820b031207d80005181e1034035150305080c200080b1560b60804007003500c1080580c1e00081441c40020304880c000c0c18046031903401d481c0200191400504031101c1d0040300d030011149642c0a100c40340003a03000078200303900300e42014066021140c26981804415203142d83d00c0c5c482c0c0c0c4c1e05080104d4920380103c030800c00001c075402080380302e0300c0203241d50f10350381d540b9454610020071038444d20240c1400030004000f0310303202c0381c800610f0141481d8075060440540a80e42400e4000f0046e450380600680e00020401000350140e03804884040d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 8790600 1250 8789350 8789359
    0x5040207031805030d08010b0f071e0528020609150a11010b0108070f0c0201230408010e060106020705011b0803180d0e03070501030e0f0d02070510030c0507030c031205040b0105 78
    0x403607403030040507628200e069071714010422043c014060030700d80742e0050200640c09421685040510340d910120b4848800903862840c448600480800c001030040740d00c3c141036542400803281035000c25520075400000028807445000800d8016602d4070b06e4144d042c4c2c41d0012502c0d07151903040304060301e0a012040c45174201d510709022200198040ca805602482090361100c102513103203401660740ba2001c0205034180004240c415842da001c0c110311926a1120002240d160b5180003e50390079a0080c400060f0780742c12800040c40b4060740040c101084450918004c0030000e00f1400300304580f80b00c3c103c0034003086000402c0042180e00070340080c100c0400b2000304da4003000807440407142048518034241d4035411510040010390721903045540c001d07031410300750b444500ca10040030380352002c10392034040560407092081051707240501c810000b100c42406c081c0709450300e04000074480d01c100c5500900748404290b014050504c0740181510100d0800c20400c15070400e400d0503003400f0300910865218 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 8791850 1250 8790600 8790647
    0x6141b1516170403030b04090606060f0e011106040204050c16030504060e0301051302150f07050a02010905100207180603050f0610050d080708070201030209090f010e0f0c120702070504020703 84
    0x80720301c80c8010301060805102c00716640e032607958040b00505414a0805d501a850310761646c0401c4032882028009e03c060344400000c903195490103440c515454000c00d040c80f209a00c80d1125100101d5001c1d80140d04450000e419550501d08900c40e008204001c05004404550a400c058114000b481070750041d4840c0c415042401c8205400e076502107038540396520300314076010b005050104c45c03120f00002c0402594101000c1080401003500504e4091f559640198248025540c010003904064842600c001901b0103113207102075500c0c00540300d0714a02c000c16035140000e040d69544604080c5a04c04151350b0711003031040e01203a4413002541c941e0f111108820000525291500400b2009540711070b140e8141032540c2c84d441003c0d0040c00017641031507000c01c03220000b6038800c24098410180c000c03211140c0d505280e001c05a9040040802c1c9480b1031410038011301441c0d400c161200d44542980e180c6150b5030702c1c042241403504903440b15030068004140d040401d6004031150900c0d90140140d241d1 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 8793100 1250 8791850 8791891
    0x306080a03020708060a0b030a030309020f040207030e090105010311070308040f0b1f09020301060f050702180112050f030702010905090403120e01020903010e010c0f051e0301030b01060e0a06141b15 87
    0xc5036031480d8419070527030081152100190090308911040e0780001d04942c6c900c0070b0b64000c030701660f0001c03074124000307603550b40d20f281c075407800d000400d01401003841d04005111248050300998800e102000d4280807680d0001410003000d90740c59408543c5c0409041d5103810100701504c0d12151070658108241c002e81e8020032081760750710a40b4120f4031a6610302c8d00c0d1340c4100d801900c050b40101000d9801c41907012444018403903c81c0540d0090006c1d07115140e8003845801c11a04180316280240c14940041201001503a03200840105403070b41161991000d40300c51070107641c0341d40c0c0440c0b5000c2c114240f0804210240066029122801c42034000340706203060080401d00301c0f42e20f54190404240240701c4200304910603c00390201c09a203030682c0c0e590310210021029180c10980c0229a25041d000044c06480c1c1d100a00b49001a4283d42542c040ba0402001409410b90f59115980204010884104101c5000402140c4590881c00e450300313030560f14011500e111007220f400c0d90030761441e0b09582d03 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 8794350 1250 8793100 8793121
    0x306070809030a140405041802030d02071a030711010c02030337050601091e090606110601090209030a0f0b0f0c0301030503030105040b041103090c01090b0a080604020a0306080a0302070806 83
    0x7446006414080c6180803403044041d10490502100b00e200703a00207000114103500d81e4030482070888511036104404d481d00c0e20416242914408240c0119004020200003240d60b2400071443c060680044d20b07201d548101d0700f00d0381001611a0150301d58280f00c2c04e060082e40100c004c5024070490781c2031801e010f0003031001c01d03108480051489103170981840c8041a0101581c00300d40c0007a4145030540c1020340d80d1604003a01c2019540f030000200701000300f0401e40c4194441c5600618203410840c0242c910440459240d1405100f58002c440c3c00044540181d98207101c040d402c41d5100c00300800112240c00d20080c154412034086040f982080c010500c80d20501d030540381200e5000d40190302d581c0c00d2600740800b034881c015500f0f4120780c45a440142c00a40e08014601c250b903a903008001c0001036400045c0b400405a01c0540c080720100100c160b00303503001000c0340d40090156005656101c21620440c000c051940c40303a405405644060b4007010360224110301296404401c46603541c44022100 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 8795600 1250 8794350 8794367
    0xc1706040204120602130e010305030d0501090603030518010e06130905010909081608040302060a05090f01110703060203040213020f0d14071b030c150603050708010507020a08030c04030c0e06030607 87
    0x4404001c80c6070300050010b07450390001c0404010400752007001d10780ea58030f842d422170307c02c1e0412a0b040d040419819050600c41c8545801040c0540003031114a2558401401d40d1203580f0011240508114600d0141d90050810038541c44001e04450794800300c442050590f10080c1c041c00c1e00c40c50a110000172140034900942050542200d11685088104280d01404095004045810f4041408004050b0359420302510100540703072140d581c2c441b042010083d451000f6a00141400307050781008402c0c4000141c1c51058a62080d801a42ca46503400012208800d221b6082c82941c00041d0340810f21420074040c04140120800030302600c00303803002c03000c20740381c04039040d1000910400c103403c41c1480344a9000e00641c0241881810303000140c5901ca04400c038001ca00c900b59499590810030400200300340760042c00000c00070052414140300007500d40040410161850380088045800304410004035002154400e080e100e01940c0c40a0450000d8000c9078154401e018210000304d42ca4002c0201 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 8796850 1250 8795600 8795609
    0x603060f060302060f1b01020708030609060a06050406030c0201110703020102070209010e060919090209040b07020f06040809010507020102100207060902040b181b0904050c0d060812030c0703120c1706040204 91
    0x107140c1050a4005d100c0d0850304204200551844c0c3ea11081a20460a20090240c03d00a0320711a41c2d92420f2070a0019950015141394000c01595004011140c0e201c0151801d441281c580480c0c0c02412036422405003484000d0030a450400042800402d0380560007802d181d44289c50701c87c01c0d030380d0b90701c03018a0444e000c5503441d810590326400030340c00701d01c0d20040d00035007880c0c0d00000401c0c40c055004901038100403074040301e070031000303205018890750104900c2d048915584000c1580b460503903508107050150750105030510401092160031607000b0b00126105030941c81085481d224181000006002c41010031b03400b940c0b5060045e40c40b0b041c0000003c00c401d0314280705550648415840401035052030b440b6070000381082c84520080d54540c02414002d000040006407500c40d1001c940c82252090745c00414954031040c40c40650805c90800d403a44140c0081065850349510f003011384900001400e120b41e9146481c5442c11001d800c880c0640c1a00c1031495080d150356190f00034081244240e005 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 8798100 1250 8796850 8796859
    0x303090a0303020703051210060306050f011209021f020102031f12020f150a03060305010f0506010f050309010f020c0a03030c0503012904080708150f010e010e09150a0603060f060302 80
    0x6501001ca4041c0d002840058460314000d0b25105924030b0900520304295038201c4001c0040e0f01c1009042d40c90b000d0703d001f8210464812200d00c00000005c1c02030034490b80d070104095200c80144055507111440d100d11600c0043c3c89000c101c104030b000030b001b58000c440282d40140480020300d10307a403080c0b46250a80e00c00707500200000905400300440506600502640700b1f00041c00c1c00c10b5011110043d152029242e00d02140341400c1d86006429656114900c1c4c5020745010704010041e030344440c6090821a0174140259a6224001030b5070142044800e28000d0500015a10645c2540011081d0703400b03020380e07010003017028085c0040b10fa520003071203803050200380140701a181c0403c0741000c90008000f541624680ba9403034008604140b01a80110700303a8118105810603030503111b00c4568403598455151a056040c000b00da001168103014042c00801100c00140050204001c3c0981c1d44404404441907460901c0140c3d01401860004807141c40c1820518212488540140e034182c960042 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 8799350 1250 8798100 8798113
    0x6020c1e071d1801020408030403031b12140c15010303080601020a23010b0306010603020304150605211009050d0f090b090d05070e0705070606060509031209030a050601090e01050702030309 83
    0x120104024800500300f40b02071150400f0080f10150709100401c000d0281101079a19103207181006800c00c00c8040b00d00d055560101115000901c548461756013070b51480c105240c508602c0c419918040c081c80680030510301c0303100c1d40030300c80500180b4298102c0317100c1c0d65038040d59510140126103602d2000c03c0180b03c9c18101c02e40c1031000401e40601024104c03c07600000300d107428040020301d005d0007a401400429400010300c000c0c400d001540ca681c004c0c04030030a10005152601080340c1c03264046074149446c03290134072441c41644c00d200d048011614808140480c840c01d081c802c1d11148002000c0021945206554504500821034881204d42804695080c45041000e004408030888022a0140115480420340c00c11841100d801103000341e0700c0d0381e1950340c10f00e410740481d200d61b0883e4090281c140106113540d600000d00085800c0b082300d8070340e2102d480b00c01282c50664a024010820300589001081c240143c0c9e100c21002d40c41c6000900c103c1c2c4850809907121f100544a05856400c001d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 8800600 1250 8799350 8799389
    0x51c20131413020403060506030c180403030f020403060c0201050906071106150301020705060c07020a060905060a030b04060503010606020f0123010b03070207090603061a0102010203071209020402040306020c1e07 93
    0x1841d003021030002520b949021040c640340c00040b80e00036001111440c0e85d60b0140003160074100b00580006906071540c0c54996a0405210000b550043c401401c16460350200c0004c0c54150f01507600855001e0003d0114010354003000e4040c00088401c00890b02c10b450001e0320072840b9016580c00d89141d540034001940351028000382c540c0400b109250959020001c240c0040d00c200449441002d9000b1182d4841c40e81c1d104028000d075860b8403810070050010b13810320140c1daa00d011243c5540701410700044c0c089201003c03070044e040943c025541075103000c1000400d99008a4002d0302c2e105400c00802034001841564800c00c16404401d07003914807040014850008203000640d00b0035084d0045414255540000070152201e13a041190b01c9611560f000c500030124000a00300e0030806d0000f5411842c00090003400e014031902c0300161103442c0e44200c2c0c25522540d04a034051a0080340c10341d030300c180c0040321035512825800c110407018040414100400000b24001c401e4400c43c91421a11440c0c0c03 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 8801850 1250 8800600 8800619
    0x1103100608041406090f0706030225050c090c070605010905040503040605130905070c0201110c1c0219060504170705010c0b04020111150901060605130e0403051c2013 73
    0x24001c8070f1003003583c20090b22100e03003000754910070803880d00182501304440c900281401400e0b03100005260040c450780702c290340918900089501c40707070902c184105460810314a00001c0c049561340059181042c801d0a14a9a00515085005040034000c99a80f4034980c01261000c03540600f22350800c0c042406294072a0f030041c03406921001d8035000c1d686c0c8601603d0700b220b20540e0710700e0100302c114400b8011560071a5030500d050140b400074090a000000100341c8410041c1c21909111a02652385021552000c940f20224a0f01d42c0c076201009454031000742c5107900034000d4404d0107024040c800d1603840002080015180b041c3d540c000400381a54400c0b80310080a00b0481c180400e0f04103c0b03c21100803c007455105030030503406022420704805003400c40780c0384e4010104000c0d040280c502025108540759048030f40b039540c6620f140d13030789040c110342500408803140d090455214040540c812160000900e4520095003440c5021514a0050440c803500300e81c0f020920480104020107040c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 8803100 1250 8801850 8801867
    0xf04050403140f0706140405061803040e0c0301030309050307180203061516020909070305030316030b03060c070501060f03030e040c020f010207030305010920030f0c040b040602010207050111031006 87
    0x4281070950014101d03060702c1e03480e904200b540f51440c01000ca005414003a4a00904496929260302d83e00c8900b81600c070603841c0e0314010000c110200d180340800e501d03070800f081224010005001c007050301e41840309801c240741e4000e20054000a03038104010039507145c0402c0032070440d10103560411003c2c1080394030300040d4100a00103a40040c40c1070856010340d034020000d02c10001e40c18189140481c030343c810010f1401000c0c000f810241e00071a0140001140041241d411080004d1540c90059804004402801c00c07840029018001c540034015005c0d4040c0107030107817500c1000240560343c5c0312802403020000300c1c440035001440f031540126050030260310812a1511520560708800a8401d807282a44d2040d0380031000a0b941d00010045020a40311300e0400c3c3d000322000d11809002c24107401980d000c00340108081d002e0800c00300e10401d040d10121801414503019003900d40b90b80710406030003900701c2401925107500f000c08138041071502c0d008681c403801d00c0c403003003400785030400d04210345001 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 8804350 1250 8803100 8803103
    0xa0f0e0a03020409030302070308090106050d0201030203040204060306110d0c050f03070f02010905010c1805040501050f1e0a0605040e0a05010501020d050d0207060501080f0708010209030604140a0f08031005030304050f040504 99
    0x844840c0110140e00d0358055881154082c0e180580c1d180d0717280c40c009080c514002c01c40d02490745420004c0c00160742c0d02c0c0030485495024640544c0340c0c0c645000040041a40398001080da0346040d4403641c1c0c07804040060316005d2019981080701c0848200142c68900c141682020004420000140410702807100440c004805200000c0c0d0200260b641c582140d0392052900041905030705030f01c040740b0004090502400065900b1b018651416000c2090344082c155440d2080414500c55140311a840b60340d021002001050002c41c10343d00c01014049030320038019180a55002d000141d0781654500506048070030682c01005490b119100458a030707088100d203046440e808011710008900740c0d014441c0600600c0340544a2044400d01c0e661401225a00189469005001e0050540c0c0c1c0840c0d040e502a8009050f14540c1040344021800e210303130b481c00117000c1c8510005940500c1400c4020318822001c0950868040e80c45604150340ca0195200e82c0d58425107940041c036a80c141a000243c02c03a = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 8805600 1250 8804350 8804359
    0x2060304032f01060b0c06010614070c120b070f021203070e03030711091f090903090503030316030b010903050a081b03040b0903070b0708030a0b010e030a0b060906060a0f0e 76
    0x200d44910b0488107207240e00e007010200000c01000d20030b12080a104050007084a865000e160040402c00383d0313100d4505108840501c028100100c000c9400e42d021603450710b50010f010100aa15422481c03800da696050a4543c0050b150024002030302843d03070315207461030a0300205030313164000c0f10709061980018005020001c10801c0e038407280c0c60410240107520b00c141422a0034202c140700b0300003840340040038000042c1d59054003028103139030407854405950b003480d00410048800e081c00e030b902c104943e00003078261200000b00182c0300800e01c10311070003400c1990b0602c01c2120000044520700a64000509140c01044111300003413840c80041082e01c0c070811030010811584860181560404d80c007205100000064000c51440c0502201e4040d00042c02c03a0350030581607454504142c04000c1c80441c04c140d41d42206060341c1c0c061104000000d6004080315106410340ca8074201c01103080d141c040c01891640c0c042201c5140c0b03041607038030a0509503078280d0070402e001c0701181d045808549a9421 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 8806850 1250 8805600 8805617
    0x32060a08070e0a0c080f1501051603050304020a08031912060b07050703050607030207080a080702010f0608150604020c030304020d08040b0d05010608091605040c0512042117040206030403 82
    0x18418244100001800c1e00302c03680c00035283c40e0030041c058602402e22403041007a0340302001000d480180c19030350400200386200645c415144016102840b4111408034074a1f40100c1380700c205644103005601c01c41c82690600f40b000e0b6070f8020a0394034014100ca096540c640300c3e0901079072900c50300182d1580300707030401c021070555507540619846a00802c81903419802903031040c03050040800803290082641d14046190248a84400500340079400d00882086189004902a113101750800d8100121110040007943d503902c800c980d50b00360404120140121000000d151841c00d44245d0b00406601c00246186980d00d90030004425144202150740074000e20012403441404001703440383c1102d13060f0005840d410011b0182c61442c00801201169005410103d6070740ca8069000084a2041d64003240249048005540030300072a00040b5400d4458000c0009004202800c020b180d240c9000141c24182e500c40c04850313421400840f50300300e02200c2c0105005007400002036034400d01034030f068150b = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 8808100 1250 8806850 8806859
    0x408040b070213020408161203050301050103110903060108011b020109020a0509040f0605040606050a0506070302070e10030807080901080f09060f070c02030f0715090f1a090904060f32060a 83
    0x105c1c4c1294222020a900429141c5c4041500360141000380c42c5429401d90740d85101c0d90002c02900c01401400c1c1055141c0c03072889020841d2806403141450b004050350580c6d0386500c85207000b4480036818814070b5003001d9000b000d0b01e0042c41212262500600070062840c20002804150711024004848001000c840f82020038014455940207501c10039010501910349010050300c090340350030581c851740d400c01442c80041d0b00000c1d0701046648120044443d1750345c003980000c0130400d9a002034000b00d80000e80000300a08007004000031707582600d5242213602e90340c0440011400840e03160410781c2c480404510b03410b01c00c47d03102d44d003c07440b45450811424150b002c24280a4800d80c01103080d0b100140c28800070140b4130303070444032450070310384040294900009000311004e148034942e03801c016281c01c0e44a144645045942164010300504c040e8241441c00000400103040f242d01c0b05854254800c0e00d29100f04070120f41c8008206803100c00700302c995103006d000603000d40440d81c003643c0c030b500004 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 8809350 1250 8808100 8808139
    0x10504051203040312090806060109240e03070801020d0c0201020301060c06112104050c09061804050c031e010b030703080a0302090406090507030c080606070c030b041703010f0513050408040b0702 86
    0x171044d2450792211003ea2501c40c44928106000d0101d0741403007a240018402c00c0c5c4c0041c01c40c044029111041204116152800d803240381c81d82c0101500340c0a004000314007a0015001040c81e00074011040003140c1e4060801c900b00e000a000c0c44c80040c1c0c04181d18004500580c0010800382c2c82c0d01c3c8098a840c1030440c0c006904109120003109038041c6004220602c4018080152075940940b0640d5841c80c0c04000503c0c104080104095982000404a410701c00208400200c40d600501281c1c1d80d205400400d03e111106000c01151b030b03600b0f008043e070071400d0210b04c080072a030f40214214201899100c00354080c0d00159600d0b03802580d07601000501121901603c1e00401058400160050400c0001052543c00a05075800f550040040c100085d07642d500880840b0381051480d0fa031600c45140c0801c6000d881415007158080200010480d4802c507800702040b120100d400c1c90700ca2102c00c1e0000141c580880b006480c590b0244800c11003803800d04014012240300404d4000912108005038 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 8810600 1250 8809350 8809373
    0x80d08041704090e240c0a0309080304050a02030609070f090b19030b070e040501030203030d05070c05010903090609080607080703020a0e0405010f030204060b12060607140105090f070b04050105040512030403 91
    0x240150303441d03064034004402e05001010002103480500b8000c90440c00c545c4041280180c03540c0c6020700c4c00901034080b5440f0b40c0c00340c46407940c001002940d03400c0504005a0b10848031806034800d028030004604103200018604d401c403194410384906180c9024207280042c004000401c2d00802d0842801141e05503086c10000030b14415600c08986040002d00184507a52550001d4041c0d80750000500250358000141e881e900210038020450303a46041e4100e44606d02400014095030811905c50205a040010a4180c0c2c0c40c1380e4a070304d080c0d680c4982c1a5611842076503e0008940701e58040b9203035610940003404410031a042c54000aaa001d0104003214402d9100300907000010310103104601d8a80100390041c0398400d4124181030030807140003000b031400f6110307a2040c100016407074104881e0140c0c1140580203c4000c00c41441c0c4040410303201d0030041110400d1b4010b40c1000f0032182c0c09c84060b1000e0343c606070341d035500b454140014851010003100e01d00d89a44800d000000000b5002100d0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 8811850 1250 8810600 8810609
    0x606060a211a0604050a030605071404030503030f1e15060405030703031709070b040e0a0f020a030506100219170415050403030e0103061203030906060503060718050406080d08041704 80
    0x14070010080d99854220018050341d807040c3c0302000100095038803060008140c80e000b100018050f210f01400f0f40d0070820728103480b03c81c2c94003c1000801c0c0700000c8003961258200040c2800d950360b400c10f0303801c0d50f0080141030f020030000300ca02192500c4003180203050b08410180c00140782030749850004c0d20307122642c0e104500107035074228148018005070901030707049840d0a004086c42802c1103ca10440d0107540210b1100704842400a40c0e1000c158000d480e0386207880c3c40855440e0081c07007000300509001c031800e90084a401c24180c4c0881d02c00140c0b0f04002c80c0c03401000241c1e0515581d1301500704072410220044140920004c01c0d950701d19061407000704201d132180c0355154510302d0050310701440110498141460010b08220101001a01d9501c2e143d02d03141c000703600300d0b162600e8001041c40c0e4000d940c01d44a01e03010031020303c1c0c2081108640c0c03189148164020381e0707601d0402040c2c41c064003404003650011a0507480c858083c422070368003c2c1c4030f05c0600039131400103000016030781c100307610 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 8812956 1106 8811850 8811917
    0x901060807030603020d030305040201020d080609181e0703022404090e03210601090e0903090402130305120904050a021e0a0203040513090b0108030c0606060a 70
    0x610050f6078020002d0306c800490707080090080c078048908038050310032810040c0c01140994141d074424803004018138542d50343c41c00c04000c144103500c1c00d4135061140c2114814130f40f2400c0c01500e0b0002e002c40c001d094403441d500411146083c0001275045106c4020b0f410888600b0100441d4299aa84080820031649010302c0758510310607603841848803803060f1080c8000f10105201c0c40d002d40c0e4240e80d40d918030341c1c403008000444038003603070f0750182e0380e03c00c01c0307840454240341e00900b2403450040000482c00d5561f0321424205590b5445852074030781d00140c45040ba05d820b1240c0368008481d003030f045081a10040d00c42c040400c0304a20001c7c4040d001c0355204107a032082081350003a00700034250008620050604101400b8040801c4070403442030303400841c070b280f400000d07112040450401891162103d20520030154040c0c1510b10800c511400700700305081c034030751181e810b85d1207191 = true := by decide +kernel

theorem cover : BRFrame.Cov 8633100 8812956 := by
  have h0 := BRFrame.cov_init 8633100
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8633100 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 8633100 ≤ n) (h2 : n < 8812956) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
