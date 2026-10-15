-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5409
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:46:34.13693+00:00
-- url     : https://prove2.me/submissions/b8c8c328-f684-4d17-984c-32ad319c91d0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 972661870 ≤ n < 972841726 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 972663120 1250 972661870 972661931
    0xe0a14010608151f0612051005120a030e121c090504020d020711010f120b1206040b0106020d260703020702031203340e0a0e010906150f09140301 64
    0x141441c240c0e04005031800c030040c4c0101c0401a604000d840c0d0819696aa10405580c001c81e8076503030800c0c80000c101c0d2640c80f0301d81204403100b9424505101041c0100384601c41e40b118000740d81b0400500010038854a071030180390740300c030a4096002030740b00c1c0c980c0440c3e4020f01c3c00c030b00f580351603c001c02c040ea0049a2401c07004c68003c41d0b100c08220540c0c0c1d03e8080c03000c082c070b4011000d08885400400491300700041a043c15070342c0f814207003d034031082c403040400d01d0200b00312140c9061528010105060911520006025400320046064440e44103c20314028606003001a604408601d8843d000c01804600c07d16600f0031880e801a181407010401e401b035210000e940381d00e04580c0591880c160b42000180c0444010804e2002d10503040c501c8440303a04501d000301000031000041189005a6041000b40b1003041c40001742400b06030700084103407241e0f400d0f0075918248110003610f0013407040100c240850b41c3c2017001e000c0c0107800c82c513800c0c042500400204000c1e001100c884c03500d20104240507e03a = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 972664370 1250 972663120 972663163
    0xc0f010908130b0702090a05070302090409050d090b0f0304030e0a150c020108130203030706050402040222060f212c0318030c150a0306171e010e0a14010608 69
    0x20007880b04507400415100022a1800d011030380051020000108084c2d410382d43da501040006200b58142d8900c8034014104100a545604009540380307114500752001544442d800f26100404c00140e5940030300519855040d80c030b0383d0354265252842c440144d50011114140002e0380c412001c00d0f0400e9440c0c0d522180303409566400018171020004003290300c90b04019070300c0d0006032000011641a00e0b000030000503d0b8450380b0008029104040c0c0300590500c1c00354000c07081d4800f030f241200803504070f42c80d6410340c82040b0200b60b070a9501c6a40c480d103110700c0c001d0b032681c58140c15080720601c038600b0305c82c4010300d154200840c075204038000502c201c00d9101058604010181c041404800b41c01140101007410055000448000300740420383d100741004a1400d0406000750008000f030b00740d11070801d0038408100d00542e52070210310360341d80f0303081107880110580e1507040c071416002600200c05403000710104d455450000d070003048540402d40d070380c0c50b001546031824043c0d80109001c1880da0640c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 972665620 1250 972664370 972664387
    0x2104080d060e10172d0c0319060513122102040f031205090a030f02090f01050120030d0507020303040510020f1e1b060910051006050c0f010908 63
    0x844036260400c90240340c03041d0a2008400a01c184801103404114400140070401c1d040f203410408505900e8002c805010010085d10402c0c0300540004800c1d40c0c104c0b03c644401c1c400300350b590f00d440c100c0c0100854251010201242c42074010f0341c0d004000381c02d11102c000d0160780c2c0d00c0c915000100f6000002d01e80701404024000f00c040c000e40414029071041d030605040400800502d206440300806d6600c04807001108640103800303540003889d0003400300004a0703485c144441c1903038980c2022407080c00e10100141c0640c0000c40e08606070741c01030390303036240d96184151400303240e00c6800741035405403105029001daa550540550b43c498030383c80d400345890b8141450010f00d41110541826800d078018052944045415400d940c40c035103880f40700206600308103c11a40a100c1c03080d03010080403038841c0072882007600040d018001c1440400716074104040350100310890702c0540c1c2101c0c500101c01410010300e8800c2c00034168180c0300398103658003420300c01c0d5000c0c21250710120498090740040341041c2c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 972666870 1250 972665620 972665647
    0xe120102031005031c0e0a08010e0a0b0105011107170f010906090203060c120c0307030209040c0f200a0807020f101101060902090904030f030605130222030f030302210408 75
    0x1403500744c004140180182d465403400c0d159603c0c0d03000801901224030728481e62503034034800007414400000c1214040d0b80c200103854001c100c9007a104010000d0000469520540217181c4040f8181e003c3e0080e41c0c03d0400d015103400c3c000c0a030480d544a000c50301c20301207800b8070030074445900c0740400080c0002c05105050810fa0300801c1559a40c4003481071344100d801d4005441d0313004d00100304441d500e60322142c0c02c0c0c000f4005e11004503005484e1001c8030010641101400f401d02010f0748550703280801c0108000d01119000c4c4240c02c0c0d9400002c030031400a82d80e2005011041e100409500082c5c030010041400d050000345038400094481c0b540c00d03000a420701c100400f0340420340b0b042d81380c01c11045c0070840070300c0083d1004003000340441161040b940300f82c0c088400b4000c0103140c80760340301c05500c4410207900440e21000000b04c0001144101540104d82c5604503680440c0580e104400b03901c4c103600a410134041e400f008051412200c0d809910114032030300c80c520561505460700000720414 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 972668120 1250 972666870 972666901
    0x150902070b0f07080103140307060903020309031204150c110607030521071b060905010c0201090c080a0b06130e120a110c061603050d05010f050319031403070e12010203 74
    0x202e902c00500428800041d030b100925a040d82d41040c1917080b0441c0c1c104000303146124680c0c0c041e0106240c100c5c0c5004250b030100081007803800840c00c030380704510642404401845030f4481da00c0340d9005804104207150160044940050240300d4000c4240d02c2d08020541c15402607404a00050000458a20701c2c071a0840400804211000710045440d01184c09081c880d540c6000610350100b440c0980b0420003190480c3c414150300000910140782e4001d0080d003c0d011810f0210344020780b004000c40d21103800201d031601c0c207411130292103154984109104640c1e0320b18029203030140e01c410300c10341070980030000c103520810b241024968544032004001d154090802036031440d9003100900740400d580d41001d6511041403404055003501080c54207507120b01c201c0511280003414030340006500540900d036501118030079070944105092031400014041e1070400024041140103600c240000c00300d901542e03003c01282009011603c0c441c000800d08038a0f0001a04160340001c10003103202c0c803202e201c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 972669370 1250 972668120 972668131
    0x907151e090f21030c11030a2108090726030a05040317090a05010302090a080703080316080f04080703050c10061701020c0a082104050303100b04140112150902070b 72
    0x4050010340d81c10041c409000d5202d5004c0c0400c540e4101c07400a101000421a029200084c1240c11b004402d02e0011100f0301818040d049080e01d0b0000d03141554001c40f1100d00c60303a25600602003031810500d8503d80b1081441c010b40840408011034003c011041005000110702034864684a902e0340c540315084003099000e18000040901002c0039540342c401240e01a5282400c0241c2c4821075140401c034010100d600a542a10501e04000140030741c0c00c00a600400c450019040200300b141d2003940c0c1c1c980309491281d40c8440041c00507001c135024101030001c1c18400c1c5801444c0101340304d26145032480079014032440da65a501c0402c880b51026091064009550f4025400c0c80990259140c640c00c80c0341010303001813400500c16040100c01c03c00484071500045540c0141e09090401c3e6550b032b0012aa43e518001480502190780f21540c016101201c05103400756107055088401101d0b041d80300c0c0c8401240329103801a03856140d510410040c0540106e0400680751603035070038036540e0201d01810 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 972670620 1250 972669370 972669389
    0x50406050607050307061d0a060902040513030801060c06111b1506010903020f0d02060304030f020d031401120510020c0c030705040c1e0908030325080907151e090f 72
    0x80e02c0b0001d100401903803007094000200080d65600c401c0911442e05940c184c20300c840c0540c011000800401c0e9200c81c800c1802a6410040c2d075440618400c00000b9142019010034560f0340100038003440352180301c2196114010102c3c01c40311444c1110303900e800c4044006c8409002803030380341080f42c0c2004054120145000c005059040000006c0c080e200c80d804081d000350854912043c9503220443c3c42d5142e01c2d40908401e95902d040c0c18010a10940c0a0f0640300500541c00d4030501d05120340100c1e20010380003296002141d00c1c2602d900000c07029044210758030300544880303203010000341c4040c01203142d041c40a014062002400c040c10240141c001c18403c81c074080c07441d81240c0c3c0c800302c106070001e064411411001421034003551416030030383c840c440505c000001c015200f001c4c40401d0003a140c00c000d03601c0810514990588450908607a141425403007140300300400d02d00b0b103040c41901d10017418000e0201030300520003668614010340d03410100c1e04200003040b039402e80c0100c00005002800 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 972671870 1250 972670620 972670627
    0x1606050f1f060509061b0a2301060b1801030e06101a0408030a0c05030c030d1d010e0a080306011709010507020d0903082d0d0c0f0201090c170705030d090504060506 72
    0x24000341c91801030848041c082c54000c188902c01002d00801c06ca8092104012180c103101c2d5890316001c9054402c1250004621504251104030414018541550f0902c0003907070400d03030a1103400c42c0300c40c070b840702c42c9040548506c0038100111042c48035070301a5903004440060a8180004a100307000305000042040204000c100103145000c0f040d914515414a070004c01048141403061030341c085c8036620b482c070340000112610501c1e100e41c0400c0308485503e51035030b0094420181542201c2c41c040041e6001e03004101c0844c00110540010340e44035105042c4454442808500705510880880d8503044581d520400d0010681d010080003060980c1031606070003c50a6070744034542c500501c0130a0142c0d10401703035110754144110341c15103030049001300b549448142100c0d03010060507441000c0d07404509003500f00d00c1d400784103000d402c00d4035401c141260000ca19190700a240058450016000c0d0300950301d01260701d503824030503807258294a0380d480b0b403001d0420041101b21104e913448280b00b40da040 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 972673120 1250 972671870 972671879
    0x26060601020f070b07020a0b122203020d03090c0902040b090306060907090b0f190e09160e06030a061e0303110a1505061f030905010b040b060306061606050f1f 70
    0x90a4801d03130f9640380c1180d032036801e90700c040346d0600003a0300401074201021603404458510642124070691040c2105070110310a0019000c1e00d007039261000d00140c0141e0203085c201d90094103c1122030b4400c002c0c505d01240c1d601c03510030480e00243c00494210600241d00720207440e003040080d801c204222012941801e003034002511040705441600c034030103404940e001880f08030310261000c0e12405240c069601c1d24292006102d4182070b4210361090003014041105411f001c2d039010031b0340d02c050b1511454180f8242c00c0200c0c40c0c100504101589454407004500c00d046641102030b182c00f0191989a8a8110300d005002501246140d0460354881c0c00c14001054603103d09540c046180c880001d02c1e901e5210200d0031100d50003a03811101e20342c0108001d90340b82d00da03104900ea5030240e0002c20104060000708015520881d08103640f03c5810f0020074004c0c5000c800810841c11001d07981c1c40354442b00c1d5541825210210341c200340c0c110030941044403032891082d030716004040c1c040c05c80c40c000b42407 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 972674370 1250 972673120 972673123
    0xc15040b0313031116030303231f0504090c03021002030c060606181002031309020c0d14071b173d06031b170a03031526060601020f 58
    0x10b184041070b00c4160045000d050040320381c489019804002e0760b80000b01c5000700c0b9174400803403004400081c54140c01135030403002d0110200c5286c0b4080e0500c0c0d40d03501c903030120700fa070614650060903901c0e07480800052665274500c079002415103d002d4000341130f4514010010074050036441c07441550010402c881900c40c1c089149980040205c80d0300e40c0324101c0b290f0302e0040030941c4444940100c3e83e58400c40413560004003500c000b030401b030b45810b400f60301d412840050b80035295403c0b840f42d201c0482801e07858080e070303620500e211001080504000391525070603892360354000c9002c05105640c41c1407110750310303408400c80b10480328070003480c101800054020001e40c5404888000180402e0541c0c10f03282440c08107560030b042d10034180842d45d282c2c1080080d0850502c0d0000501c06403c000040d0b000c4c4000b64411700750603880141c5180c03100d5490030b0700030313100e0000d07045038403030380303000003164842062000c0e0030701a50302d10075541d00e031965a030118500a009010241075600c40100c1c00d415150 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 972675620 1250 972674370 972674377
    0xb03010b0607240207020907080406060801060e0f0a020f0d0212062b0c05130f060f08152203030e0105180705011d090108160902040617130210020c15040b 68
    0x1602c98550200d143d00c0080000b4040c40d80000c0d4804041014403041070740c0f05c02d98601850142004104003981c4011041c00c0b10110321505000c0c41003880000d120590400c45668400e030005005850440c480c641000164010426088829804241c00c900c583c0b6490103d079001c1401d441140e41d000b1400340b4454010311503004042c401c80c1518600e0308114034100010001c09014207a86a040402c009580103420046424010903180400002d501507007101602c3c00c603126400a0082034400603170000700c1c0c0a00078100050014000d2500030040348016014050038000d50b80000e10001c110300c282e0035100007030440310840012000c80e03081c0c400082000b2084923000d09200c0c02c002c100703013078000c0d18201d15540e295001040030000516014081072030540305c0c44a0400d854000e4903082d5140032405540958000954402d1151000c90900c0c60010340002103803200b091400c02ca42e000507800000d45c0388801c0103030080016010305041c80c018030301003001152000e80c00d00b41030403080c0c2071a00 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 972676870 1250 972675620 972675653
    0x80912040b0c01110406091d0606070312150617070c030e0111190c0501200d0e061c0222050d062d060e06030f070b0c030d0e010b03010b0607 62
    0x40060742e00c079031180035404000d098030300c1403001da02c039540c0e1540500001060322a0009480c00ca01b1021100b00c2d80f200542d110342c01c01400641003a5180d202150001001e6401210303c03030b038403500049204418900d80005080640c0c6424411810018105038190050940c40c00c1c040c590074a02d000070b030040680ca00791a0207180503824803000c10a050300d4990360a141d0700184204180701c40511840e4000401512001e8032140c1e908480c0c0ca00500400c08504140c2250f034102ca18444003440c496030411842d5800180642d050107030315600c19046082442032103400302c0d80047d00a1001104948901014441070f07000740c06289800085240781d14401030091081741c0e60326104a6223201c4a9140c00e20401101580c5030002d03440c1c0109009000343d0103061881c505071070005085240000b81c00900841078006410030614110902c100b5030800d480040c83e900062040780e005948500c03401521540100012800380b5400040c182100e5840507940c0c005d503803c1180202261a4800904141 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 972678120 1250 972676870 972676889
    0x6040f0b0c13030c0306060614040509130203030a0206010801050606090d140a1a10050603061e1201020c1e06010602060f090c180601030501050307050a03080708090405070f08091204 80
    0x756030300e01050549108464415034507921412021081c08103400d0060309480c0b180c40300708003544d151031042d2602c00b50716120245800e02040140700c1d504003003121580007081d50149150b0890244c0c0081c0c05e41c4c01041455005034003c00041000000900034550020020396920b40352903030000101e418007081c0c000203040d004c0141c1d901005801c041181c10401074100b507450b54451021059208000029141141d40d174601c10004a0989451402c880c0a00d40003001c222680703884000b44050080c03101803c1c1d50022030b001c1c01a60742c4101b80002c0105500c1d80d0090320519042c021540240303140651030301c4180d0701c400010310809400046054001074480301000d403995440a44518100700b0179030aa400400d00c1e45404042c0c8214003a050240e1826203050045070713220310515a4844080c800c00341e10202800c0300304041481d0034001c1556034010340d00d840c540650a000301c0c09540d0187c0303100c1d001444058000005540c00344030583c0000e84000a0038080c0c1002010380c900303000364098841b54 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 972679370 1250 972678120 972678143
    0x210609071d010810080609030301030b06012609070b0f0a02190201050306120a08070c24081506070602040b190c0309030311150106120e0105160c021309061a010206040f 74
    0x50381140c0d1a03400103104c00b00c00c407806c602d00400a01d40b01d0300203100848918942101107082d660080711038140b455024a181000004c81200c070b00800b800281c82c0311164000c01c900403c000c110680240310480e08600c40c90340d10341110400070726100700140325040b03070400b507810500180e92100850f03401c140119500440c070903041000714102040107000615000300011024104041d00c0766070402c0310800e5200300c01e003024101e40160355000e00c1c00540c1c0020400c3c000034110038800c8842c0a0b02c0c4501501440c00c3c00031a40ea4030049074400d03080b01503602c8003c10821481e00440c060101d80d007503103144c4007821041540d0068100b15041c08010280f103011030300710109030010031440348029110040b20b0b145503034072540603004205034040f0b10707d070b241829401c03c1000d405004180c0510f140c0c11103c1005a40304104623101d5140711340481e402002c20540081da20101e00a5050141c01004005024992034152114400000900a040d50040d808010100e8140b40f8080e903056008131070b03141c1e07 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 972680620 1250 972679370 972679381
    0x221040f02091909031806080f0412020a14062a09040f1b08070e03210706110f12011223010b040c21060e07030c05210609071d0108 58
    0x21020141062a10f1540c074011503902410313442a0810600781c9040312242c0d6081d200e4504841c2c240c011101d41a11300c20b00e0340440c2c009007071204800c2c0c1e040403910640740010b909590b02c80305a49243c5540c041607200e10300788040012000540c03503140103969000f800751111001101403a00400000740e1145035601c1d54900b880d20603400c2085000e285507486410788a240780f020301445000d45d02c820015901085062082c20001254580140c3c1e8120340711080b0502c07860114150300428040b00c1c190303190005a0f440c00c111201500701411111142e81d00c600480f445400b50040580c05003440e80c0c1d01c2c85110000c1032040c524130b800c082c1041005d40b0441c84002d01c49014225942c203140d0480d1801c482500d8155010145040d5070f0441d00d11f00c0c00020704880441d00b5940c2c81d002d081404480c030004241c10702d009501c01858a409814030b1070030311821029075207506900d0b00c020031500c0441c004010507843c207403001039404040d50900c120301c071110b010400883c030124210743c2d060001d400007194 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 972681870 1250 972680620 972680641
    0xb1201090f0b22060e040807030f0513031b082b0f120218031b0f03010606210e070b0306100201140a090c03050607050c07080111030601032c010221040f0209 69
    0x10217090240b4204081d410300b4903110002d0303030001c001a00001e42002c94000d0042c440c504a8030b01d1201d84202c25010781c00d40d151044100708000740304400561f107890004071590144010815815142d0307034001912200c0310710700040040c0034248030400141a80d0b200079650040c850034840189400d00686504256180032303000d481c029080c1d64980f280c102020204215001c800110a809583c172400000c1a501071600b80e98550003079501180c5102080c810020265410b901084011200481c0c21402105e00905182a64000322401e400010030450350741000a0b81c06020140c91008008128106155884060b0064010b4010035240c14642c400d00c00c40d804890065074201090307440d582007400010380981c1c040b50a88501d80030707084001440840c184504006500401021861507441d40700443c01464100090208074440c52428110040607410596050103080c0005a643d2416038052000c440b5808082ea44492070400b04000960090745a5100b5603054480d400541c5134100400d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 972683120 1250 972681870 972681881
    0x307030b0a0b0309010605040e1e03120405060411010c12080a0b0a23101d010c0b15011206140d05030403050303131211150a060b1201090f0b22 63
    0x1e5022140520100714510300e280114042c8001400070440d207a5903005210544014041441e05c642001126161001800c034401c4c5004460303605407850140c0a00b0360003107240c0c06039020350b01c503409401003004000da1a1008039401c034007401e00854022040d918180d0451902d0b12540c03c010000c4040742c500a429040700f140214010f0440200356140c1d401d84400e101650240c10410480f500c140c000c03410060076001814116580c0c49460910700070b49a00000200d00c143d0381003100024443d03011441d8106007034020f80e1403450444508030000001040c554014000c45c05441c589842080748620002c25059403100c140d03200740004095082c51130460040d41d00150840c000041041400c008000c4055001842100c55a04010705804200d511800d400e02c0070640740e01580003074840e6080040c0f001d6001c102000f000c5002900c8042442960700410b2841840f80c0f10301c1c005002c2c0e40b10030701900d144500e9803071042040300c0090780010090b19480e100105800140280344000820a4010 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 972684370 1250 972683120 972683141
    0x608041e1410022505030f03040813060e0111010203013008040618080a0c030609170a18120f032a0c14030c0a0510030b1002011d0a17030703 62
    0x150b940e034144035030702031020b0751110b00703105403500510210402c0940a8001c0d110600e030000015410f0141908050100350300182040d2803140e0240500751070f005450742c4100240c0002e1b03560b034000c0da51050000d80101c0040300212600c0c3d0061006005d0b080306071625940502000315500503060b0141034803a484400d03040c2c0a80210070004000c81d4598010111501c050952484c642c982c0d42c0d00e01c7c410b91503820025000300741d04841c0208101007112764020030340c460b000d1050b541e41c040313103002c0726003183c1d000c100b11030085820700030029441d1401d180e681004003244200704003542c91a80d44c041d940c0401070001001c1c404d4200045451008005c01d0132071b00b0786c00816401c1264003504005036010a2482103125807140800c18208034240890265124000904078081d02400d0800300807241c0315a6825804040d65141701100320758038030740c06040c85460381c0c0000604440020015110ba041103a01112a070f021030b61000c0021807a000c2c02a0303c540f140c0c02c190f16525040d00c12005044401d45 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 972685620 1250 972684370 972684373
    0x902060d050411010818060f070e0a0303020c1314010521010c050415020c0a150c0203031201030209090f060a4704091e02190b030f010608041e14 64
    0x10042000199060440c14110980b5120850781ea4051b12011000c0582c048030000d0700000b01241c503101000d1245034105519041c001160000c000200340e41680e40e90003903005900c01d01c001211401c1102d00b00b01203400c5000705002c40000c0040f440c200c94018400c42d4040ca0030080002c00c60091410740342903001002d0300034010344a002500409070341050080c1c06400b10404010100103000044a100800000d0300001806141144607500145510201c0301031040a10b0040c00594090008060307000702a11041250750440c014000c9441000b40044d8059100c141500e560710000a1210f5102d85464070104100e0706034070404c80100d000202e1008030341d0300304150315242488510100041d2441045045000010108010642e00310b440b000d04a141d0301404907144d500f400030341c2001c480c009032020003051100c002d98050152a03a00c1025040c00210510100780c41c268550f80c0101090b02c0e200380c0c83c3c200754440048401c505541c1c8607440781400001d104020b404040941d00d00304400 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 972686870 1250 972685620 972685631
    0xd08060d02190e041106160b070203040b1b10020f0f0f0d0e01140a0c12052707060201050709140609010c0b091b09160807140a0314060406180902060d 66
    0x410401103c8016101129002e00c0e11510b10344a04100c002c1d81c4500891100c2400d01c2200c039244c0380764240313025080310f00318041040007041d440340c40401410f201400002209070162200740e101c1c00c0c110f0b5001612540e500403c0300070641007100007030754040c4540183c0c03030b961000a2807200806104400608100a0415200da1a4490103500030440414200c42c1200c0030350710b1100f07210440703082c0074014001c140310a030500d141d842540d104540c06112501d000e4142d210f580e5041c4112140039100c031480c0e9005030428812070360b0a0050a40110060038420a0300b411f2103843d030401e0342710050160003080080380e400142d81c030130103c49038030903002180b410050420414103603c4003c41c0903010182d40026078180ca207414902c4046100d20068214041d91200000c01182c0300c0070054043c0d420400741c41c0311500301540c42030007015003810035240060b0341405030f4460406075600900c0184141e203461000c002c40a0f49901c15180004420000642e5040f00d10010b811030040f401e50090a500e0300 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 972688120 1250 972686870 972686879
    0x2010f0f020703120501060818010902041419060b07020105160b15100e030a12021f09030305010b0a0e04150f090204170622080f03070207090c020d08060d0219 70
    0x41d401031601a01a41d00e100f410088070743d031801079885c28482c3e000014a0940040e07900c00c0d05003000041c00749400000700315840980c0008007a44c09100c00d090015460310280041e80c0284c21031700c1c401c2c9820302414491245401002012400742c120041d0600000080700c05085541c510769520240d0b0008000300c2c80d0034240001040c42c0c601c0da48981c0902e9565031100613040c06002c42d078010000040c02084020034a64401c2c6030b90810085000a521503c01030300e180300300106400e08051411180040d0251513410024241c41c4117038400400170100f0810900440d505c1114540802016280416009095110440384038a580d01150075045000c00c0405c000c4010b8004004031940300071000c40018001c100307a0349488080d5155002e199000b90a0000302810b62030f41d404c91409020341c142411500380303807044c0c10b5200b154000c2c01600709040502c240388541c824142d2000403031000b40482d60403850060304540c0080d00080c403d8040111000456a8068054880490720b80400440a42c1d4 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 972689370 1250 972688120 972688151
    0x60f0408030d0f2f070c05090f061e1c030908010204080f1c121a180603071703040b03192d05040206090405040f0818120a0503040b0a02010f 62
    0x70580140070340e4146100c4945040b00c1442804200e2514881184c0401e81101030680941c85400f00b100d00c1c09049100082c07075595200d102d80b0411252030390308182d00d001010406004215061599903600c179149503c01c6031550150fa8141180c84420480ca0503075604096a407a0001d9003c1d4100350700014011901800208032000c0c0d0704420f03012038036142122420302142c0020700c03000b40001000d20304051030b400100c0c5c0045810440010780c030f0b0b410050180204500d0340e0b0040e81102511401c00038002241030030025038000b09071145000042c440d40e070000c0341e160f00c640c2c41207805c0e403031010001c036565010765040c146d000300c0e015404019032110100c80408500b8800100344142c0049045203071000081d0240c00c0c45103030b0090081c0d1800716101c0400c03000b8507000d401505c1e0606803070050000102d000009040c840c00d80507000340c10100107010044041d48031104025990040b9104900141000083d134040d500003c0343c00f500e502301d60204070300507c0100080001d06050074401d250348a036 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 972690620 1250 972689370 972689381
    0x1050c040503070f300c09060e15060910350c0c03070f0809040e0618010213140d150204060f0c0b0708060604170309010e011706060f0408030d 63
    0xc0c01ea00383c03030740242c0da46044ea00c40d800501c20811403151001d01c084070094185004061820000440c030200b28460310b843c070310a003480d00300c1c001c2984c0c1c0e136000340300c2c0842080b941039015018050f104103429094011407030351302075005081e010341204100741c111903001d9800002da04d0b4054201b201c02e410107071407000402c589608001d1040403034401140015014008440320005200300030744c582400356445642010140c83c050741c00d0742c2d05002c05605641c843c01050440c9034240010222030801038550920355103514a541c42d40e0384104484001c85015503502401c8400c2d48203070082003c0d6120100f0f06c00d40340184018029608070550220f0001d140e030260040d11001d5517042d41025802e40141c4440c0c20006d8003400214038000060b641610500440d036000d480949143d0805680b00c0180900c1613208a01000325007005c02e0800655034000c80c02e002c2c2c0c1c182460014218981d2a143c3c100c1c8500c003034029805040e000402d42444604001154000c242810880c0d41d41c540d080c415100408 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 972691870 1250 972690620 972690629
    0x200612090a2609150d15030b153003030708040b011a0304060f0e0a03031e02040509070e010311031f23040506030106030204150f0803030c040b03090c0301050c04 71
    0x2444400d006407800e03402d0340c9141c07060b2261440c031868007040740208108084280e0046014480800c60882018031601030b2001000c3e0f548080500141503242500074440001d001141ca4002c66400300d10b66520400001c0c074102031000f07541459480705002072060b800c00c2d514039405200c0001481a060750054035140701e035010351520880f590b260660a00c0c041c0c4001440440304c5424008600072802951028800c00b40d400800100e0108401d040c2d410303e030031085c0540c04240c0e00d8007801000c1c001d1507a81414455007480440c0341c242440001091550054810340c2003082101c1c0400240e4060f6000b01e02d1001c00e5501c89442c0d01c0c01518074807045049643c03641c4035940560b00041c00b040d002c515841114249030007142443d05480503c801040018101941076484080000240e2500d01c140d250410300120404d0201d800c0190b80007144c811755002e00420b510400400c165642d42030203980c207070745d00c070500c03a50f480c1c84035001240791203080720040c0ea15510708424081c6000c4e06c500140201e8 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 972693120 1250 972691870 972691883
    0x31f110a0503091005060d1e020a3203120c07050a0311130905071509090c030c091401080615090a0f090e03070b181c210207200612090a 60
    0x284c4240c090003042d51401e0710030719006440d0582e00c800045c085884001200c071700f0340101700580e01d40d80018911071242d504c941e00e041840711001d41c18043d50300000910801c0640071840901138240400d50b158000b490910324004045030300c0c44c0603041884410001c00008114500c01600c03400c00000040d200101c291058801c0c600c6900c0e80034103400744907500c5402602500281c1e161030000c1c29030003413441c1d000b810000381006c0881d09620901c00c01000d20790f182e80014154140c05806490301c00250031420f00d4841c0200040794680c0e0103095907610000c16078080341007004a08410840780a0070844982c80580b86a000c12180c0000900c01c00701c4605042c18084014044038a070f44a00c83c0400c064400036030701002a00c0452201d41c9a52114014011900039641e40c104004265200c0300c011000502800d6842c074603203401403186000300c0082e0384114903181d003035030b1342e0600d0781c01507900a42145000c0c1c0c22181d0070348d40d08050782e21140700c5208040203840c100e162a03450300903800046406 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 972694370 1250 972693120 972693133
    0x1912051207030b120a2a090f0e06070207121e05030c1b0a0b070803090a080705010b030d090e060f0303190c2d060906090f030e01120b031f110a050309 66
    0x13007500003100030f005608161031015080042a40750f005140e8081c8100e03020210744000900c81000780300d405681664000c0001d170410080800c0f03810140c003e003141d41154042c3d41c061040c0c0f0503155210700388542c000c0c4161588401c8081c18243d00045032406007060101003601407100304045802c0e04050400502c4140f182c080104001d01c41201d40139215682a0074088140050002c5005580104010040326541c8540e591242d2965200d0001240c099450b80b1034552941000c0007552045c1030030b0304051441c40c0c03c29070b040e20a0400100002e01c00c901c60b04801015440a01c2150490000150802d0300c0f842e85240141c41d02490f42401c842104c807100d154a81c40e08002c412036241c02c01002c4900c1c61111984840010749100b20382694003d40e900e8159000a036040c0103403200d5407003a15140c0e08000000d00151090035a0003d061080e41820880c50a541c0d011850030700704100c40a0350705c44d226100c0d4030000200426110b41e0741c5891b00080044000b6007000c0590310640c80e58080310003 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 972695620 1250 972694370 972694399
    0x70815150a200a0b060d2a0b0a08131703090d090506040509070f0e101d0301060510050a0302310f2303161e05031912051207030b 57
    0x4098505041d000d010b42109002c3c81c0001c102010350343e0800401032100050a01c02d440d00b110101c0764002454a0800540350943c0400e01c6108000c01041314284907404c02e0a0071502405800c1f00401c1d01c0c2c181140a0760020800c030030341540404a0740000d070b03041d80360710f01800305655803507a0325114804215891400a26071030320808460649101410750415915070400550b4190103005005060013592035a0180c42d4942c14060050700c5a1f0782e0394580200d00d45000c1c996100180000c4a0081c0d04040d0144070307544507000400707580101031500d10744d588000f170022002801a000d04400c0f10781113100341c04ea0b02c40e0107607001d8655401070420b0340e242c5540e151030b038222032034612130010349082082c4040000105030000002004001e4191000c107120000c1c011201000ca4000c01c550341e60080351202e50381b0411001c40050310042e4010310082e2406001c543c500d0043c0b1500621010441d20043c20803449103040e10441901c220448019061008016000d090031200c002c1c0a0308100c14a1341 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 972696870 1250 972695620 972695657
    0xd0b0405070f292d030105090117070605030a11040f08060708070e09040606350708030334020c03150f04261810080708070815150a 58
    0x25801208400c9036861210004800c3d4820780004601d00071320001c2c15a0714558400d0801308118003075040498a540e5814941003011090060f00305c1030001070f00e145000541e420000ba0f500a0314158100340e9140c0d40c6150058001d00054212840240404907002070080207031240b00007501c101c6800d0764040d940307944044503a44012140d0f20001100010f00c54402d050424880340c010f401803074040b84242d142c0740d20074100148503004200c05021800d400c6854440303965004003404526025207c5146400c1e0580c0c0c0da40000750880e80f01100703403000d45604a000c04451101d101441010550302040050040d45903c66012001d0181c000c11880300e00c0f51210481032489818148030110140d219034646030404031020300c240030304413162000790301e5040200024141151803081c5407200240f641c0180040d01194000000a115010050000c0c2d81c0d04504907550000c180e2403c1c95980d030356040c22016042c01054500d4114200c0d910031244407244400400d2080c415442d4080400301c0d00c10b036007 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 972698120 1250 972696870 972696899
    0x5120708070308070507080703050a02070b04052218050f0d09030f0b0601030e1209030c030a0b040b100b04140103050f0405070501030e0f2d0d0801140d0b0405070f 72
    0x90480c48100903140010b030280a0441d0030491502c2c2c010304200159890a1455022420580114034003041a610007681001240d004c0c2460441940c101442d1801003000300e1401200321000941d200c0702c81d48403404d582d012800038159602d5603c038940f81d034108544c85901303450300c043d10742c0a480d0712a903000e8003440b0802d04483d401050412307440708986410758039000c0039051a04254640603007a80301001040400100402d501c00b29548074002c0702014030300540844007d00a801441c03010020a0410041c1341d0710036000100c044056550701002c001160341034208007001c9101003401f26070304098100150304103200b030302d003000395403103010350002d03a40d80c00c4800030320390380c0030503410700c01940300760407980032a26144210740c00030301d40742c1c42141002c2c41d140714a032907890354851644820031560030000e04940c0c0c0700301400d91001146001440c1500c1406620510441480200282c0c1c070fa181c20710503025004425100c0a04003464800d80701c0000f84195140e002440c100402e80b02c15001c0003 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 972699370 1250 972698120 972698123
    0x40f1b090e060310020a0e0307060f0909050f070e0303070b090c041406030c0f01030f060b03040b1006050a2d08090d05270a1206090303051b07030804050102091c051207 74
    0x6240381440e02c144c000203035006010140030000200c00030041078400b0001900031300110f440700009040c0445008040c00074643c4125440c509041c00d104134040c0110000d900083d0303920f4501801c02001011a140d4816244014401100013003041111400810480704c261011101401444500007600074943c10645100780c0c9074001d20f407a00c000340303031100458407410f030181404a10403210400355811241a94808a200c03140001040b080000720600e8550100c10441100681410b0000007003032800303199450810f2100c0f6135003451441d0b2020540f0310003c501000c0c125051403107040c0040c211a0151001402c3c0d1080914200016000b03009440d00715540010005103214010039030249401d60030703502500110b459001098101a0800303d9920138010b40c8040307480c000c1c6240050440300001d2100d022300c0320031b5841494640405044aa910383c042c0740002c50b90b1218101640284500c400e520752007900c918940701030202240c41c03c0040c60080058400020101203a00320500c40c0090 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 972700620 1250 972699370 972699373
    0x121213080d05040c1511010e0a0c03080901090e180c0406150c020a0302030d08040519020607060914030a030c080f0105090429070302070b1b0315040f1b090e0603 71
    0x3031101c060155502c0258024010505526500e0344c0c0c1003100345408001c040744000a01c1c0034107070081d10109000380f5400000250007826000960b89444100090300d010003000d8920000c0d62140581c0710380183d5010348462046281d450a0441341c1c120680081681c10b200e82c007509407040a0b0345014442c205c200d508056095400b034030581d100b111408601c082c103c0e030000f8000404000b6031810080c2d0400420603481e07180c2e550405007402480c0500300c074907640301500e8079002600162940c0d0283c464039a03000801194104d001d01c0c0039100106035054004040c440800e8185500358503400c50040d0034101d0316190310076100c00030504507600003401400c0c1c04c0202000844e0020792140410610041059400600d2a00b00412201200d50a8442900103600840d1803424896102e00e45074024100c00ca80a85012034030301100c2c614000184018480c2e04032050a0005841d03940000c01010488401080110074070400050303005850b01102001890f58032000c41d60510101c10507008040090 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 972701870 1250 972700620 972700627
    0x1503060f09020d0e0d020601060909110f16061506030f0204050a0506070201021f050f18150a0e12030f010b071502160206070b04030201230610020c0312121308 70
    0x101d0800c007030341c4540b030004031155583c0c03002d482d40394061040c001c03802190350150285524000004048040e9030700300880c40c5241c00492089500c625044540303007e0405c24154440c424480b05c0604c2500ca288040d0140381031640c165125050501c1c010150307800c50302c5c10003d00d6a143e000100700d01032800344542028a0b0355042c4580cdc5000b40c0a0001e071441441207901c44058030340034100452a224601e108141c681080c0802c0c0e00d40382100541c010540e14800c0c6a003200584202d030386e03256516000c0007100c6003001240c54100c80e43c1100440c01414030071203074442401c2d08500050f034000c0721f01d6a1b10803500400403521140394012101e072160050310812071441107110b01c00003903225800c04100284178001110060700c944020b480410f00030a000c1602d440e080c1000703401c1d21b601d0a2085030386803d00f500c4051410800c1788681d002903050f40c46624113000c1c26016440c0c040f05c408102d5151103010070201060b030380d0744028005891000c8405001da04e42c0281984e00003442075004241c05000d2 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 972703120 1250 972701870 972701879
    0xb10020313120f1e1203142406040b0705190b0f07030213030620030112170c0609060403030b0f010507060b0a0b0d0f1103100b070609021003061503060f 67
    0x2600c801c4094012091825040b00c284c0d82da03c00310b0905062540070221084284043c4150070765020051503aa0405020b251100150720140303a40c0101403040d503c440c01802c03483c246000c001d15058440c0603080b01c3d607d41d151020301c407243c1c011003800ca80d1031040e0816519580c014205003420658015400f6560707440b0003502c0b0012100c000c0c00c0004059003800103442c40100b2801c0180110300490000646002c1c40854950b405016403c003001048208010440b0f030315054410201142c021a034002d4512048840c0b202d03d2207680d5000d202480b0b24000e02035000750214900d40a140309480801c00002c0e0a02449502082c6624450120b80248001400302e0055000000307441c200520103030455071500d80009664002c0c00c1d51440300c96680c889085041e034184034205001c003088242078118500748610b0040b042c0e2038052081e0100010500d1400c011280d0030082030f6540c0140000e284205840004004101503c41c002c1e034a44180907181c1e00c01d003e0710420050716040743c285410705050 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 972704370 1250 972703120 972703139
    0x7120605250f1211041e050127030b180609012d150306020a09080106080c040207020616051b040203040b070e0f030f0c1f09030b040c0302130b10020313 67
    0x2c16031403809000150001c800c60f2030052003040b69140c21130f003640d6282c5042602e181c070380034000001c1c20350701c0c0203050041c0030681c0c00c0031903200819010702c0340d0070030344826400404040501c0d40c0000c104130b0005040c8144000744001440c2c0c6040c6c03903422070300c01c0d03580d80c00c81d1800d851899814900c801c02800b84080d486206426aa426016100011941c00c00f0101c801450840359802914890350201c1e07401c0c00c16602105032001094000d00070321025081c0710240c0d484001e41c440d5144115800075454003192180e41c15200b80d8540700703889035010070349070800c00c0d00c8188800c0c3c0562503503080944130040346824030a9901036500030a2249503592000020fa440c9908815070a0784000d0310080e44a1507541000550400d2410708080c243c0d011159090243d40d007201015a20443d101c1c4445400d0141d200d200740003265000384400500b80c6031030901384140c030042d0300040d410440003503c401c4015400d421540854000390b031061a4001c000b54203d889000703084030608140d000380400c03c00c5161 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 972705620 1250 972704370 972704387
    0x42a03020d0603050307050a030e03010e030d150f0312020607050a1b02060405030307110301060501080402011d06040f032906031f0b030109050d26010b130302030712060525 76
    0x100d0781d0000380c4143c40b03403503007803039500541000c454903402009076208056200c1c1c00341403840300c05c2d4004e02c00302204051003a02e81c000d54542e00103003a80c910b40c0340002013600c3c10030300013080c400b1074000840b5124100210f102c6000c00c400c0000d4800c9030082034455201b035080303c1c00341c00c040c1d17a104010f8019549220000d811481c059a00c41c40c00e000100707041d1303000d00c0203140040c8641d608a64403040c40b418142520010b61040b0305000340b000c200000b50340c02c18000b00045c41c0c0030107504907540c4014000354541c010b03500400c0320361402013004010042640003c28191202d00c1c1c01c600c0340a49018006510141100d055415802918101ea100103c0c0c0007400f403103615602e0041040f107180c1000c81e086581031002031b40c1d190301c141040c1d01c0c0c164100e090800540082e85500384c111461000f0207001d06418424140d005400041c0270061010100d09017010b582c3c010300b603d42c66907441c852001011481001661428a00408141c032001038205015030000c41483c960480b400094007520502c4 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 972706870 1250 972705620 972705637
    0x70507020d15020d060503010e0604080a0c0f081c0603080d0e03070b10050909011b0c0503130e070311070c14060403060204090501032117060d15020702042a0302 71
    0x404545100002514201c440d01100b0240c0741c0c0103807114803502d820000c3d80c0c181d03400395000c0e0345003e4070071040341004103110b6031241c0c100d0305250341c42440200c00c0f00c5101074071401800e00e0710013a44850070040305400411040c9644555210a40c91003c00c1504031101b5110080c86134004100f01c2c00206202d80014110049013030649041c08504d480700e51002034100e0703240f121044c018405001c1031a0202d0013903080380d11040204012440035031040038007814071a13040140300c3c403001d0000c2041002c10450b801287c00d29010f042c07540d52140c1c1808001425a41c8601103820321164100003817825058485094100741400380c094a48640c6503034038800ba6011a401000410022001c1505800103100401450380d000840d0741c5141090100f1000181c4181400c011081f080c0045c0340e0b01001c1d03044101215030010b002621442c00180510110392030051200400d0342081d030b0304070002c0d4040c0c00c0179402901c0074880402c040d40c28098a000003800801c40000107149840514442e50242135200d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 972708120 1250 972706870 972706879
    0x906080a1518060b0f04090504020f0310050603190f06020306030102071b08012702010e191d01060801030507090509011508010f0b060309030a0302030426030703200307050702 77
    0xd00304091401c0ca59000d420810040c0441e0540c00c1d5840414440c034001040481c080324101326511031134206900c039511600f407000f070300d410100d019503a035500c44070032502c030040031607003900f800d01341500c00f0341022646171344203001d6401398001c04921501c070280e030030f40d1000b044030304103101d540c2e428025000900400c0d090b6609106c1d88000840882d9001c20f00d40100e40413000162400b15030509507031280da84188808010310701154048440070040480b1a03090a02e20103c1140101203150300700603444440c183c91204000041d03114103c685d40008505600980718642e8035018240c405010a101c010460740c003007202000140016400740341c0041d407200010403880081d01c48007010100c1500101c00031795648001e08503007205442040d00721142900d619042d89000920f0380d440c2d000303203d060340605400100181c10803542120864405010341c060340f90789141c0ca19035a602d078204555080101e85001c2044080d039070009444e0a0340b401b500001459559560b400329041e0300301900807a0070 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 972709370 1250 972708120 972708131
    0x150c070b090a0f03020f0f030403020f090601120221010506130e0c0f1305031e030f0702040b0613060f0203131503150e0619050307060c2d021e010906080a 68
    0x3e041c100e1682100b40c003c1d4001c051410328964002c3c01c1c110300c4e24007072000741d200300410801603c40c1f5036a590007180440700c000440c0d4070800140c400c0e103034074a41c29680510002da9240140c05c02e0503402c21480131030307030000d14683e04d510502100c0d2082130302108100b0004003080002d01480007640340e1000c1c400301d005041010b075035030040d129040301d46000c03c0f00c011404180f1860504018007a12420100841c40c9120f21660120b9203174414001c2c5d0441c28200050104299100c0b8ac010030821080900003a540fa480400340315805000350148030001042c0400030000288000140c42c6003202c580c0c01171150925110344141f8030501d000030343c01810388070707503a010f40b240e0100e84000c003c0c040c8004114007440c0100030003183c100948080e41396152200024030540d240050354005841080c148543c007080d40313051640208146078103081218820f40c030030100c80300c1400c40d5405540c0c801d481c1485039568070407082d05600350510f50303540040d49001c0c0c200419840744541540140c480c62002030b030b = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 972710620 1250 972709370 972709373
    0x201201e0322030203030a1a1f091211040510030812040312050403030c090b0f09040203070201020f0c07050a1401020a02040504030908150103021908030304060c03061d09150c070b090a 81
    0x70300c109030ba6420340c0960030102c104051a40035000311540702c0d990640e120480105440000e442003072030f01160110b504d014004480a0340501201c2018000701d55074840000b10a20b420280000207421203405170b420080450504001d01c4000410390384c1c00a216410901c000e20620030104009005030200024458501d102100384d106160043e8040d43d0042641003c01401404c1c4d9502030b030100100d4a0100404061f5103403c500380e4022200403100540c1d40e88804100b240640541c4d0f443c4d25888c08005400031021b100090354008903501a00c0c0070403440e03036491088050380340080080f4090381004e0003900051605a00c401c3d07200c0d2080c1070080c0441d4846109030f00d490320450100b447c1140c032000620075407400c04c00c8141b1941401c0a8400e0b407a050443e500e03164000a00024a070f2911400d1038038203a0b0198000001a1441e1040107a1540c151600c0c03402040017610703180924051031241342c1c1202041a10b2a12460f24044543e24000303843d9185038240000400890130350090401220 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 972711870 1250 972710620 972710671
    0xd0c0c092304061a09070c02010c0f021512070c0b06100c0b0112030e0603040c05011206180b21300406080702071212051c0c0201201e03 60
    0x1030041e03010f20ba0001e02032000411045081d4140700c680b0303218403520020000015030008810560a50a10f01100812403e05d0303c001c1924040e4030017948034082003007a0f8031258408001d45045400401d00410680b105282694080480c10001d003002e0000400680d1a0034400600840c42d0b0151030503a8072505242c80345081101e0a80100102c80311049200c01410380c0920034220303032501100d10601c2c504059a4140d14034a443c071030117043c4130030084044010840c9500c040010500208200c500b100303031400842c01800e04d60003039886410b003200e42c00e00740d40703075201250300000802e40140b40304610f0881e14260840c42003e00011b80001c40e40007110a41a07030042e10040c0141c1e01c0380030041c2041b1300003030304200d241d8110a060184e0f02040d940070031103d5005102000850030100d546001c8002203045c80340c0c3c148400c04086080161180b081c642c150f110b41c04410396107101d0000c043c1d0704000c1d01054800c07000b043d04481d140c1010004102d014000550308118017000318050040c0b01c1c000f14 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 972713120 1250 972711870 972711941
    0x60f090306020a123b0a060903050d0e070302091806070302090f0303071101030b060c060a050703180b040c170a080c160b030108100209130e0c150c0d0c0c09 69
    0x1a8628598410703c01741040007009480a140c4d0300e11000b10800130801151a510840d075000580b82d01c0d102d0311580700b4103002c1c1085504452020390140400c0419442c4113640340301d0751204070b000e0010100091110040c1400c03408030701e1240c10203042a6126608100c001e50000d06a030341d8480840317070346c051403594100300400310584100090141020b1002c000b408445241661a00401d0108506110303407d000c02c40c194000118003001a00f5200c8801c00c60080403040004501d04001c61820b2003800301b50881e00c0d208920440300040f00b513480d03c0d0101c840d0314144407018150b6201c1080340000800d100c002c0d00c54400c8030000c0700c0d006288405440c6828031a6400225007110001c0180005130040c8082210480031220561411407020042803005006554100c2c1e01d950310756034a43c01c0d070014401a440044010104000000e104031586881d81c45400740500500c901c03070802000da4040d4154080a541001079a00311074504590300020300340c061540c1e0884000981c5041c44420307080b0302c0303 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 972714370 1250 972713120 972713141
    0x10515091009121a0c09011b060b040f0f1104050a0b0c010f1404060c170f04020a03060f1a091006050a02120a090303030e150c130506180901060f090306020a12 70
    0x581395411100c9011800c040061301d084040c0c0000c1011501590300038003100d0044110f440c40c05140040c5040c440002c00840c0c0170144c0c4142801e41c100940ba801d170304906010f865000e4200712940e2407545140d201e105038030825401801e05202005200880b00182107504004400814046525001032085940200d08c0d420800d81e02c0041c4414099244680d11007402e890800b40c000c01600c0a5034103413028010462039918401900003811501d850780010001e50f032100d4140200d1400700101c2001d4204103105040b05c01940f0710200c1c44e0300e0000d0101c0d000c1c01031600444541ca01303012007101e6560000006200390b20511804025030216403008120503911940c849844c1070440c500242034072000400d0010035401501c003030301c40401d03840713956401450b40d0203055070b52503209203020351400240e840300f40e0005000c10840c46001403a0350444001c1c00440307a400c40e60f82c03140816100040405e90060018402030340c244005502c0340d0050440c8482400c000d51010380540d0b1a00548220000 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 972715620 1250 972714370 972714383
    0x30106031406010f0305060a0e0a0507030b010911070c1a04120c03121d0f03070503011406190e04020607020d0f15050c210709031502040e01051509100912 68
    0xd2038401d02906000c2d60b03000d0420410001000c40c60754480ca035032050081e10180080f075403000c0003118080100305c48000594040c040da0750007a6641020b0386803c40c2445421541d90a041c502840d03041000111201c19610031f100c5000300b410503c034002002c2500561001d110710800000c9510a140c01080394118806e1010b40c240310b09618150100c003407126010014096170340418031480341c10040894032010143c0d8001c01d0103030b42d240001e180015aa1240390903518200c0d43d8103001c4150203038144030780d8055410f012004854031104030000c0c000e1042e40700c50403840380441e0040c44c1c07030002425032600040480309054201d8903100007081000d902240d160814124080015040d8080c0981c40450134107403d003001480180003098491900c8003208810303111001035510750060034604003840d04042c000d00d40d450301c0c0707a40350000c2d44940a1030094091400c0001441d1502d004810070712428080c0d15420000d10303074140036030302d800030354000d051000514000c0f90440042c080d90388018016078 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 972716870 1250 972715620 972715643
    0x411340f0b0a150311240c070f050102060609071d090703020d060f1409090114010f0f0503030418020318190b010e04021f1b0317100302030706051803010603 69
    0x44200e0403540c48900c41e0a000c10090410000b14031200484da003202820344081240741060701100e201b060841c1d0f1018145400420170718106000040d0500a43c1c0300c82005034582c1d52600c00590790340400301d503590384c420749a4002030f410920445540341201c100304040c41c40400e00800141c00c01804641c3d000000e9804944182c0204c0103014110041030b0030150043e103607042c401010098640f03019210300401010004c101a003009512503050b0320548841e0501658440d1002e036281015032145c03005656501001190911340801194101c41c8404400e4024103100c000c0701c0007a40004003000300202c828542c90b400d4038400d0014484103841d0040381181e1508502d407180c1c0f0400e041e00091541d2214004210040e00c40c8081d945100170f20120017901801000c0007116030b18050f4031000c19401c0b8007001501015003007003900403441140c0040b81800c1e40c030380c0c8510080040910002e503040d48243d2080041a015000401c801f02007030510740c0f107200a103c042400d4441680c401c98542801c071 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 972718120 1250 972716870 972716881
    0xf040b030c121501050f07020d0506010803040315060e0105131b0509040c03020705030a051e041e06020a020f0f01050d29090709060311070209070e0411340f0b 70
    0x1401c807079226140c1070f0758a00c42021040020501e02850081080c500710003c1c041c1d0030f540c1c81d0308100745a07503404001c562179580c694272150340700d4002d4801220b01400c5040c08000c41b01e264090341065501c0c96000b40596840e08003004410704071030146283c0c00b43c4d1209441485200d041403001c150b00b46469081c0d0300c015100a000c01c9500e602c21801c00c1602c1030080d000052004400c88061103010701d401c9403035001140314551028034072686003000d4900040e001603465201e1000c0110700c0c3c2001c4011072095924101a45c42c0c03100850025440300c00007060545500e0001e072100c81e141018034001c1d007800d444c0d17040c40341240d550042ca42095805c440c41d0b20814013a1188402d901001941c00d00001e0502100141500c403540c0a0310f42415140ca0703074280d0601422043c0c03079401c1c0d002000d90b126070820107005001c034540d4080c018002c41c107021015001428080445228004003507041610340c180003600da401c0010300751043c45a0304480124008a2480d0124500540c021841070f02c050404 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 972719370 1250 972718120 972718147
    0x20060f01180c0c060510050603040311160815040302010219031406100c0f02030c18090105060307060207170f15090c15090405090124030b09160b0f040b030c 69
    0x5076610076900d801c0c0000c605007280d00c0300783c480d903450b407000000c180751b11041314450b4041e2042c2c01c241d8016a000c4100814117034040c031095620b10124054400c42201089500c10134401c45c0070340b0800d03512281d10314604007c003c0700e05034800e0107840014103140f440c5042c0382c01400c1120348007000980310090040908a0454144e811010032584030040705c0070180081c0024110044c0980514041e054203401d5440511580985400c001c040c00c40d880715441c108940c4940a8131074001d80e40c079010000b9903600b8001303216810385085800410304140342120350750b030019086068400c01e0052070460f0060000030403c0240c5054a09105040d0b46000300309145007141d1201039610900042050f1420035202504845165609039070101d0b035a620004500e01502e43e070700007541d180140502e1003a441c3d9518620b0300c00c0c0c900c5407881c45110303200e11008aa84002d40345c0f541405942031341040000455003001816025018104075050995030703880180190000c82d4084100980015000004140c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 972720620 1250 972719370 972719399
    0x70318140102011a0306130305090303030f0a05090703170d0608030c0609100204210303021c05100504110406180305010c090e070f080f060d020604140f1c020120060f01 74
    0x1500c240000c070b00350b10000040e80d1108040d0040340070515402c07c1209141c4500c0454072285006012a6541d0614044400c42c05508851724000030303161101103502c851020074020b048903048070401d503e102038030020710b02a40c041801156030690310716000551003030a0020341000d1081d10050145464042c004d02d0070712070443ea0700b244143c410801840300c2840b503c00c00c88402008031020f03543c0e4401d8034040d0028801c45075010700301c3c1a0000403450540d607030f420031482141c000d20580ba055179690701b070005449414003203020001060009100b030910071089110545607941d010010683c0e81d441d41d81c00c403250798807404001210800144050a43e48e140f1681241151030b00b2481e00700400310007460144d000d4000400070342c0400c04140307a6130319501d03001005034004180e0b5648540d9206188015103210f00c03801d004190b11b000041c21032404080145510b0a034100c51641e409181e401140e9440b0b1400300707051019400300d200324240504004181c0f00715038040c000c1f5000c4d4100a0800380005 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 972721870 1250 972720620 972720641
    0x40e03090a0807060f05031b0d1a0a1d061804080403060501060e092a0a02061914011217031e0105030f030d0902060705120406030b0603010f0b07031814010201 70
    0x240000810004241d008117031034016001c40c5009512038940702c0307108071241c44218100013009408114010050595800420020380403030768a000020038905000c1c4070b80341d070b2250512500009010080b000300700105541d121000829200c420000c0321031005000c0c00558080d85e8100003c20f01f4001c0241521941c0c2c0580510f04000e062814050b0000f50003420052800b081034800040707000c2e50b602070140d820407040b15070000584415001d58020b698403011030f03d00c5034a0b0030703034106540b021699214010340020000d11440c40340e0b0a002d907001d5441d400f000300f03e440c3e01602c2500c100440024010310b004181c0d1920364005c44e40940540007450206030044c0d0b22a03013004502c410700500020480303590b146180b101294036149070000500900400002074501c0c095200411080c061542c02841075542d82c1d101080b80710451401e004203400f0034002d51900c6407a90509002e2121039601404e8a0f42c0700f46402d40307079040361600d014401ea00380e40c00307d42880020108140b041d80c080c060040c41d071 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 972723120 1250 972721870 972721873
    0xb300a06091a0f030f10020a020613050a0b071202130501080702281403040e06030f010c0909110910020f0d1803030513030506010807060f050723010b040e03090a08 72
    0x980141c00414410355010b580280314140c29074a02071141c4017441000b802e501076200350303260b40000582c20704c044e50144c5a8074005002e040000b461186103c000001c07004e401c100100070318401655a40102c40025000d8002d02c0000029030380580759500040c0b270707800c2d42c3e0102c08071950b191038005004404060806010742d00060074030400001c4809041c0d10702c40440c2c80d06c00302c034280c81c01d0000611003101c104c400d150000040128902007030401d011301400301039048880f80d044203a1081d00b01d450030074036540061402c050401c600c44268208d12400341605800c00c1ca80180040001c14041c5001204030140e000b0721200039941c4001d001c0c55210b0b040d141071100b0641844500418842c1e000e0200405200010071520303940003003080c5100c080e65101c07003101c07069611201d0b801c0d40c4140520495000a0300c4c4150218400e116038250b13080e2a0f4405400011210391040001d8104640c1904810940d640d0b0710300a82540c441c007940e0000101c92016695825103a014000803248a41120031135 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 972724370 1250 972723120 972723131
    0x16060c0314071707030e060408070209070c1a27060403080105010302090604170114090f06010f0806061e040c0c0b18030d0f02070609050c04140702070b300a0609 71
    0x90ba03410010904040e000300300041e01a03555540c05800030a60398001c440544501e03410041040b24000081c00854000c07514200749a986000444040c039842500a0a0b00003240c0032000d11100030000580080384a4600c41d000340c0a200b01d2061a02d2480e007054460340400240000d2582042d0554013411082c80c1c10351401c901032740421002d114030700c905e402608241c02030307200e000802e5004070009000000054498240306040b43d940e24951107488410307000e01c100000300d03582c2c03400c8043d08440d2400060842682d034042048145000d440005a0034005100340c0d81e00c40d0f0f2030707200d1400c448007a03440f5090210040c0c01d1a20400744024141c10791540c641950701c03c401400416100b0001c03501d5070201e45504441c141130040d00609400074080390403d1a00c100b0440301141a00000c0c00c25078007080022103050412244010a8070b0b07400140e0402801070204070421401084d03d10100040c00c1c0c0c0200c0b10303400405e941c403103d480151181102005018403030300340e0b0044000401c80200d040c401d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 972725620 1250 972724370 972724381
    0x423010c031a031e030d02190f0c02010c11210d0207140f060d0605100302180904120c170d062d0b0c100e0102031006030e03070b070516060c0314 64
    0xc1d111340462404442d980c0d9020390700148030301003086501e10132035884259120704894244022120b82d400c0003402080210343c03a011824817810889962540580d6014131240081d10b030010000030017046640c00110455070603501a000301c02c40188114a48000c0402c90201f1100900f02103142d0064600038070404105103882d40c0e43d1004d240360a4088480d50b54031780d40b40c24084010320700d650040760804540490720310391076015030250000d13082010a00da40300c1180410080901c1c022140101074013070541075464a2440b9820b00e0703c80510400044200e00c1501c0300030388903504460b04110683e03495030818407083c070000301410243c620086001081c928110035403e404001c80c090300f02c20b280041b0324940d10307031000c000a5179070880362202003110440d891041c41c00f0f584121501440d540c80c1d1100040c0882c406c2c824052508294409507081c104150750311720640c000904681c0030400b007803240d200302e03400810088020768481c40c00050051001c500160640f000700003075140240c5040100103 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 972726870 1250 972725620 972725623
    0xd05100c021e1203070503070530010b03090706050d0908031f0503060c0f030606040902030709091b1704140f03030a0621030c0201030f06030b04060e1c080423010c031a03 75
    0x4d0700300c0901c0c06c3ca43e4995031403e00448030b501814407121641c6580c01001411400948048142d440000c0461042c40c2e89a0030000d40c40d200039512000a980711403401c0224a01c40c0000c2c3c0400c1c0495400442c0444150701c980c00650020b81d66101060800300203031001204e100e8141005000c10f8000d06041d20340741120342503901811043c075803240c0000001600035038404003154040c214000045440741005040108200101d015980b0310f01e14001d0128868083c0c60301194880c4910f0361403184034858945440240b103009802250b040c0300121040031940f00c00d022081006400100941d05d82c030300840792205a4900f50f21210b5843d0702d03d55030a030310105150600c8845a09400d00c95942c401c60b00c0124000c154180e4101c805519000c0040100004003200c00d0249015120501c040d0350440c02c9541c0b14800100030303001c2556487c0d20742c60302d2800b519259074403034040c0b58240d1f4400ea0903c00c1800500504144882c04c1c0d41d60b803110021250980b041c0280c00d881411034260002016020a = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 972728120 1250 972726870 972726877
    0x50a0c09090504031211030601030c030b060406030f180803071d0117040c0305030d150f15110a24230a0911030f071d0609060d05100c021e12 62
    0x140320ba254400a41410f0151a028041c40385611041028500078180098580c00543d6202d0000f800c0104201a00e0b01c00d0045101301d10000304072038500ba00e061802d0f0000c00e00e02d00000d05d180c0d16a103031241103407042d5100403130a03402440050380d207261600005102d01050504003204d000c021103203441590b4000c1120300300e00000319600002c0d45aa0400855054aa900041c41c0d0302c13000034480451129500640045000005241d03552500d4030384d0b103940e1250601681e0300700d41d41c07600c040c041540f03d40525060304419a080d80d440a0460304c03031202000310301480d640980314018a0164200c0f041c0f0407584807014140b003410000110300182d0b1950207018001d0360b641901c9160034802d0151204d82540440c600804640303452800e00b441c0b51312964035111304580088229114141c08a41c002a98840c185c010034803c4c940e640d00d81000200c1c80004000d8650b071003032500c800e8001c00548601e142d2030100f030700100320340308200f95840054015444a20480d40044810b0144542c02d1810f8 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 972729370 1250 972728120 972728129
    0x70b041a03010e0105100e0d030e010f03061a030c07080328020a020703060e071d07020f121c060503010f060e0105010c051c1103030a23041e05120d0e01050a0c09 71
    0x1b05103d00b19540040b140c624201401c2e0794892000c4a8080c101038002e0300200c400c00080e00e07501c1b60545942c0c0e0075001c0341c91612811180c514910400030f540304e91200103650090b11210000e081c420035448215070b6400480d03541070300c02c0c2c03840e811149002e0749652020304c2040600c0154581400d0100007501d0380c5443c80010b101a4a58440c0541c07660244454006480078a40c241110048444c03107941072070003078034624054082d4003041c91038480007103926200c0b89032449103549001d107054071070f07252144504001000f943d560403001c01d01d50350070f02400001c401c204c0d0001c921a401c045020f80d80207010b81c0841d061160b43c1c00d0754070000e00d02240c85666181140001400103403400001c0c7c41d2240d64040c031100d01e02000007000440c0d0b501e58030002c040038101d541203440c0e855001d03e5130401001518080d0180d801100300c045d07010000b94680e0141c80c811025541ca518020034010604e4200303646a9420300c1e00c488903200d00440920482d607000b000542c09002c0400444400707001c0018a008 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 972730620 1250 972729370 972729379
    0x5091b0a0c031e02010902040b0a060906050c1f09060e06090a0f0f05071e05030613020d061401060f11160509220303060e062e11070b041a03010e0105 66
    0x300009060203044103c088007440e80541c4162080400002e000305100c50007244141c1c500941307000c8506080c00c26405464058803610800380c20003105a4440e00a0111810301c2d01c01c2041c1500324140c0c10000903041850080007103052034061a048050b80c00343c812303d2101742d004e40f04006166100041d2036000301d810201410141504d030800e00c01d03042c0400c00c068040e11406c140002c4000340c08440604e1388031030110118106071110205511031000b6a501001c1550540d403280241c6000c180401c1c540d44110400596a082030214502a8500340d1210003c9401003051110554001024512101c07446004d07007001c2d0140da030140201c1065000d900e00945451001401c0c180d1004100d110030b4040e0f0804c03400c0941203103401005003405005041c1e8180303200000c2007040c00c101002c0001b4101a09050346d440c460500c000b4240c1000740c41240070003580120b149601082407013100043c10524008503503d505114400840b68201c1d02c1114065004000400c212000e1000c0075042d12700844 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 972731870 1250 972730620 972730637
    0x70e0d0c0506120612070807051c020306070e040e060f0106030c1701120c08010c080c0d2d0b011b1704030b130b01050d0308040b04020303040e040c05091b0a 69
    0xa0400090380203800181d000301000403200d81902d1010680d511454044135003208a42c2285052502ca1900c0c0c450b101c095404100c00b4800d0746094007245821400c00000344c88d5071402500081c1c60300b501680c040012aa11290015140c2454051800070f00c2110313000304003505011020180c9004148201420581d8403c58110301d40c1c4255101c02c04140e02111a41c3c031035840b01003155034140c404408030348103802010006120b541c1800780c1d94039a1040d880c2c008440da26403e80740e034164818a00900300c10307036814104416030b0791241d95a15060403420071a8000081d1094501115100030341035050151000c0c40030140030402041e1005540c1c4000c0810041241400461031409180c0006200001380010809010407110f4400c9200e4002c00440c411a41e80c0e009001c0087d03000300012b0002800d500019012030410200d85030064406402c0301d141c9603868620024800040d9011582036110400401080c075024102541141c0d120001c4081c91803c1c0190304102e100320b5071076505101d21030 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 972733120 1250 972731870 972731873
    0x4030308180f030a12060e040827100201020702131b21060306021c110706021c15080d0915030507120e01020403051204030803010e09010209101e0305070e0d 69
    0xe10407030b01400c05090440b030301c0e04000d98000d0318115543e1074402e8510f1034820000707401702001100354001d6421410052500300e900c140e91035460401c102e11220210b42402e42c001a480740743c605046480319500050300c80c07240b841049400d18070151a241828108103e08900a0501765043c20f010810706040104030304500803443e910740c140310f406d0201c41c07402400000b40b1580307400401c07403504800c2c400d000402c034070182c0788122400410204502d4006202c0480001d050342d008180c1c00740c0303000050030902c0c1660031a80c1500d81c60284c00f02d40c0d01120b1020001c54104020044400100341441d2080b5420041c41c612811880e103121800c041c5c8a10100311002e000d00102c090000440c9802e010140131081618040d42c41780c801101c140c0328541e01259a00c03608820348007900d43c0407040398a0369182c41a1819404000b42001031107560821903101e5a5440d05400c585002c0141c440d8000c0c2c002c41800d620340c09030f802a00b00c050500340410042840e6203ca804014404102e400d840e07400e0341c5 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 972734370 1250 972733120 972733123
    0x6040506040e0925091508030301050d020f04090c0e0f0105090a090f0507030303052a040611070e1302040c05070201020d18171c090609091a130c0809030403030818 72
    0x4000301403840c00301c000c640b112911604c3c0b0a40064450079501440005444201641404201e00c90020180c200744014452031030b000c004c151106000404c0ca0312070004840c002021180380d20811a03c0300c00240040156500d00d01c4420340c85070040012221039803403c000b02c2d040341401030a406034180e03581c840e03108000d481440a42015084000c5954840e01c034503005e0300030403059440d50807620b81d040540f410840e18241085c40d1140c0846100d00341482c0103012395554100103107210042c000c3c0d160110324905034a41e214814a025440c034220791909005200449281412503410843c0070094080980d030001128030401c0414034180180601520003200550703003a42001d800c0101400154018220020b2480404064900d078030b0000c0221000940e40301e90300c0e00c10b0b000070440250042001c41c00c1c5501c01c8581041b00030204a205100100203484040d111822003100f9036039032600e01038030303500005041d4010f100400451801c4d04588000d41501002130800c140181d04c6001c00904a10 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 972735620 1250 972734370 972734383
    0xc0c19080a1b1202030c0d2d030e060424030b0d0b01080d0801050901060305090307060e0615040b0f0d02033d05070f1b0210170606040506040e09 64
    0x280d4240d800080c081e2520140e0000795082d0507007052280c0c00046511074207620b0310f940d070f20fa000f0300500f0380307883c2081800102c00607070606030385003001308000302a200b0744400c00d10603483c0d10726580014051680b40207090309540340c40060160400380000e215112070079000b41051703901550048880700340c280b02200580b00320265560403400303580e04502003046608105040c0d03aa03140981e95003000c0007004035909102407180992240d032000c0100519400f0f540030540068075002607910f0101c03581c64203030550740360a0010100d81c0c8000c0c200300320084503d1026844040c21201032081c1d201c0c990000d000d403010390409034442c8030b25540c200304540d07003045540d02c062000142154080a038442d986099400740000e07480076204a960b05509002911519208404a80303540c407400c0703000382040700d03034070340743c0b00c400c0707d1200108030301c002598070f00300e0721118009283d48030b81d0000c4411104140d203240142c03203a130060000740003d004503030310380d8140c9090390000d1021007600d0b581c00d5003140c54402e = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 972736870 1250 972735620 972735629
    0x50109120213020a05070506090c060306012012280522050d0f21020703060b19090203222d0b0702010504140606010801050f0d060f05010f0b0c0c19 65
    0xb4800100611200c5c2c103d4084d0041c1d40c01034099407020f5a80c0700300b4a40b40c42411807226441f0740100700280c600d6001d4540400d4a8952023012100740050181440c0352561008501c480b485020a9080301101242014501e85c0c1d06400000c9020007500d00c003503c1e40c094100c07942e4418000041069500b100003011390014040109440a0801c880c1414101403e204409856950313040103800803084000c0c01c0c1641c0c80c3c010b036004040091841c0c0380c0038014054039107078584c4107a480442c0d156003400740082001401c1404001652814019600a500d4070344641e003040e0310314400500004501400344120102081c56105803483d48400c02c281c00710740000c14000d041030103405c18019056415407205110f0b920643d0070700030000e42d50152540c0d540c4112142400140418014003c1b070908480c601c1d8408000741040498002c50380e2120700b0b58450007490540b4991307a100403c1940c4a4190940003005800c924910380704c20029000d803144500369403035001c1c900c5d030340744200800c404074031900050 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 972738120 1250 972736870 972736909
    0x90105151c091205070b2409090d032715060302030d0309030306060e090411030f19210203040b0a0513062001180f14010903080108060c040501091202 66
    0x100300c554407440203116804059a00300b0700701404450f80744c002c07030880380300301d402568580e1107555107407e6408102c3d540350b03a0f502e43c0d8034003000301d030075500d80390b50b030034090300d550400740c1a6111031920090440d09441202000c1c1d48441c001c0b14000c041e510344405420f604a40304120700441c607860b03440503102d06d905c02505480b44a10410b841d590560044c60928803070b90f000e114440c4d40310012540303060328400d40d1fa44810b840c8046030002d56110251030601c03c2c003070700355041c5201c0700c4019401c01c5881030030040c10300700140c5d0399006c001c0c08085000c1e828081c0720f6899002021200300030369034015409a003066410000c1d00c413009034040c105440c10120308043e0960501d171a0b080050008240601c040c070b54003030308081345403100f0060040c00d0001c0304400c130340b030720030300c013a07192594520003c0200340d902c00c102002000c1e11070713800e000d01c40169001c0c0d15480ca05514144e810341c90240002c2580120003014001400240e03400b0701030008039903d80c0e41c2c0850244042c000202101503a14100161 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 972739370 1250 972738120 972738157
    0x31315110d0e0f0f071d01030201120911060301080102090a080105041109040302100c030209130b031908070b070302040302193c0f050a12050a020418050105091c020a0209010515 78
    0x401340024424040d2688010030641001d4851690341ca1103000b030000a02144400240c4058990303140d201c180094002c0400380b00c281485004101c00d940281c02028043e50000b5075500706040c02c50110004140d104001c2000d1320300382d11446500052422007074843c070895004541854820004c4c0340a1107003880c4200318068242d08054000d60110805034001d00603007400396035400e09485002d55070300303026019101d201c2d0740b0a11722070710418180049801c3c20b0107000d2140400c81708405207205030380c20788005940d01d0441c0104040e010a14050509500e0803c0701403100c0d084030b140141c00c004074042204030b900f1006484207022600181e451010658400001aa03a01c1c059921400c8800580c1d00c011402d459190aa42c0c1811004020f0459030008080e80c0050034264000e0704501c500060101c04541c1568a4a080d1882030f600081950310810002050708200031182400c07054a00041007100f4859000c079503c40c0052040e54481c1d06800410100c000404084460070840ca001e0b800c40f = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 972740620 1250 972739370 972739393
    0xc050f0a24091e03030905030303040b0a0c1202070605062805040b040e0f0c0f010c0515070c0215120c04064d160503250902031315110d0e0f 62
    0xf206070744001d400051102c0d00000e41402c000c011680160340044000005988040b103000c05001c41036003d10410170040780c41900e00206202600d0918803070200413407181024000c10511900c0404d0710740c50402e500c0c0b000c0119202c510628022118107407000328180102c0c0c00010f0050650700c00c03208150003690000d90502e04045221b102e14203085231074110680f4690011030700c120341801700801c560720031400c1e082c0382030840b450994406106d00d0000308928443d800b0889441d004040203441c040085a40b0840b542501440e80e403000d41e003001031341050700d405d500070006098100500484550007003041503110b000c81e511108544c00d5080019040d00b1030f2640c03440700e403445c562400c050041110001105500c02001c1085030300c0140100811001007518120300340d03a06240c0600d40d5507001001840c20350600245100701c00940481c0b480a05609000b003041449140e100c9107640792113400076048188006441300c0d29482c07040002c41c3d0f0f1070b2205051034031400020100c1c0b140b03d224610030 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 972741870 1250 972740620 972740669
    0x1d031e0d2f0c040e0c1005310503150708150f0d0303060b130e15091b072f04150b0c01020408061302031c1407110901030c050f0a2409 59
    0x40403000c0a855021070312180c01e0045447c4e001d0447d40c41c080d00c10f1441c076002030031647e403940c1659003002015200c4003a0744400091802034140c071414103100000041048040c1c00241c0280c0c00003425003842c0180401c00009001412000c1a0701c1c45200c07107040e40000e051295000c80050040c19200e90ba4800800c2134889440358036104102100000c8400110f0828846941c401a2a4064201c400d40d44a030302401c22202c035020102c4652500c00c0c4880b1010a43ca240488512100c07007441c03c00d122440c80c600d00000d6404000503001d141010302c070100d20a88101c007407044680500580e170b1200540d5000354060300c1183c1c0542202e21401c03052040790f001e0040e51000c128070880403507030000c0d198120b21400502e107900034800700b4020720003c00c005034400020000c50b44182086203010030344600044a50a00780c0080e104c00f000340b03c0c20300142c1132140c0f034090f0b1403030200c408031046460f143c3d51a8020078214502e5440510b8181c15900ca5405984214040c101644484010710704510612 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 972743120 1250 972741870 972741883
    0x1107050703031121030609040311010c0e090106210f0906050c042904150306090513020306180c040b06040f0e15040b030d1d031e0d2f0c040e 62
    0x40d4150040e82d0945048904e01304000500c4c0780e004070343d1800c55a0b001d0410202990040090701886441d1a6664501a0038030522400142c0e50b241c0010000c2a0801d0061840d0140c0024040c010a0040306103442522041050b450520003800b0602d014010f078140c0151100000042c451400c0600388012290381001401c1a1400608403940f810503c40d0403d1512207044130a58903018100000d102400506c001644036030746030b060200350700781c1d58012f00e4100c6804403804c0482d008071603010340451030207000040e004068008001000755007402c403070b9101e04400c10002c1c45540d40d6a148400783d110300c0c007650001d254107404d040c0d14651320108080c0c1c0d06000c071014031701558000714404651030b06100b84001000e0203001010f502c0900b030b60944414600070100f00041500d002c01284685c1c4c1000a50b0401c02141248440242d11456251030100710480c1301c2b0521200b45123041101d0300040d0b0b25040d8003000a220100c160b03070a100182494002c000664001d81801d81c00e10300c0b40400682c1 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 972744370 1250 972743120 972743147
    0x13020d0204091104121b0f080a170901170603011515021515010302030405010e07120201090504050403080606071a0c090306060a0b0d0f180f020907110709110705070303 74
    0xa00a5600415811103d03204500a111441c69044a9100824601100c036180d050441c0c0c041315070700340c990540342c504560940c030901e0030743d010b101d1030820071880604401030034440c046000d0424004070006400760121442861004401d6400940c1699094000314000141d0101c040d030030702d46903c0e2200b03080c1030203402c0ca4050300c15841060010013405079002e20070360359071039000a402c24920044000e58070291042c0c4680d900c4031010800042d051100000505542d4001c8014459510000d002980c40c0e03407040d44500e1400c2c003000003298110207100d5005e1001c40306e20b0360704c501c645002484548080c984208000903403080003a00f440c060010015404d0403812a1010356170301003040301030341d071502410700400b2050200310100380709908130355029200c0400201e00010600d001c240300d4002083c041e50403803d110141320a505216192030380000c1c691070a4603001c83c9811040f541c80f005807180c903142598035141c82d404400441d0503907401c203603c0305c01c3d0b41c60780d9500c0c2001002043c034a80c4 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 972745620 1250 972744370 972744389
    0x3120d0f020c0f19110108450303090604080a020f0d020d080a1b0e0a05090c03060a08120a0503041a04120305010b04050102100b03011e0501080c0402161113020d0204 73
    0x60300800800f4060100140b650100d40d5020104401c001107c240c017001c0d003080c90006880d00b840960560400d2034450380050803450320000410002040c08803c1d12107280032441c0c00400a0040301e010204205c1c1c1e01a41149040380e0715400b4640403440c0c20012844a04e03580184901003160310307804120141003d03660b1b0f0b94440310381c0b07841990b2000c40d00c0d90340017003c2848048030411900b034000d07900600100401000100c1c8507079510b011410000c4112001c2c1850f035800420000a450701240c1d4201802014004000104103036004461500c15003182130280301000c00041c003003040b10b50440d1100e110840c10ba41d10b6040519003d03684041c0b444000e004242410000300704103804c0c2c4140c5045542c161b00902800b28503415000c001c206004040d42c05548404a20103200780c402ea942c000100803910014903585413014460800348424041ca1040b4010811900748034003095040f02c0c030b031382c2202c10204065003400000b41c441035100540080700b80082604840000c0c90382c05482211481d19 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 972746870 1250 972745620 972745633
    0x60e010f090501021b061c0203181203070509030709020d02210709090509073606050a030b07201e030331020402040e01090b090603120d0f020c0f 64
    0x40c295400400c601940c3d0043c0d1000012041103810315900c1c0b500301c20003804452038007141c0019002c08000c50302080300301540001c01c0c0007402c4c003080044c0480002001c007801d00d038040120782d003900b840003070560400c105001c42e030f200300ba03a000d21000c402461b208004551383c600d06d10b951006500316580e072404c0310040c21407c3c1c1524500220680c07054149554010182d4100048140248805004104248189180400c1e26900160301c442070395401d55420181600f040085c0404503d0601c04681d0300303061650801480d180c00400c032013034a03481501403007c2e80c2c950b10100c444c10001c2200d010b1482002ca0007888202000c1031443d0102d40c0c0300350281e1800180c0dc1400c2c3d0b00e101c1601c0c0703000c12185e00050100f1440c05d6803160b1800344c09100c0030300d04401c541c0d000901603070003a4201000700c6440d5401049415034501c81c150b1304a40544030103505141000002780c80c1da50b032070701c6039809030343c00601c1c0d40c510030a5610000c03101c031001108546508140702c0840c0d840311501d07a14401445043d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 972748120 1250 972746870 972746897
    0xc06030a1a180112030302130e09071a040501030b18180c0604050d032006041212150504200c0709060512060106180503240c092407020a060e01 63
    0xc0c8040d8882d04052064070426480c0094603002c8903903145040c3d04150b800e0100a900c0800f110000c0d0081c9070701860380c0d14504000c07811a040c14000d50011503419520b43e9120000300415043e14115a400d003030002d40c520300d41c0c0200c3e075501058411440c400302c0100c200505010000d90740307140813001104540b00b6041d0001404004e02c00c0d03000c0ca5510130030310061000064860184010205e040c45030303c0d504904c42090701840d02d00180c400b160060200c804140925038010081c07d80204140018004000b41e844040c100d80f0a501070540250b44800c81e5000d1851115030008640940d800d4003a511850380c0343d0303039490f40c0d101d01941c0700317041c1860400a0130b490701b0f41c4600640107201d40039007a0381e481d10f4026201c124400c1250080446510400620341d03174203003e008c003a6515500018091b01ea0624000e840100061a0480d549007d000b0006161107a0700b54080180720007241e0303500c011164145100c2401503a5009510403c1c6102c049142544104002c04619007030f00c603c415282807 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 972749370 1250 972748120 972748129
    0x60c0302070507210206180112090308040605280605150a1d0a051f17070203180406090e070f1a03070518030d020d17070912050c06030a1a 61
    0x41c41d9028215901403101408840c404465500c007034900c0950345041c4070203d6010840d160084a03440e082d011998805659a50f00004035031460f203800d010410541c0034070b9402030071111014001a24240d030b1400010006042150454205032240d1580e0240900c240406c0020381a2400707841d001d20080c007801c9132105000d0043d2038021446458074141c481201002c0e40403854042001c6030b00154100000941c0d0321040d9554103a00b0076a50140025284040054203415408140646d500070003010000d0155003c8140c42101200c3c643d200e4403c0d40480002d0042c20194000d40c050710b00e42416030701018400512a0101d0b1100a680002a0350b203440c03001104055441c0c0d400c840004100041007548240010888000c14581c181034528604020a1406a00c0c0c041d02e400340c4d0000d00813100c1e10750490030f0700030707881403030540d00107079160a00c8000c04480c0070b0710441c201c1610300650384040041c00d000321486684040c200035100d28094200d50050885540f08155a2034020040702d9241030 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 972750620 1250 972749370 972749377
    0x90c04051503120c0a080f1603051b0715050d06031b03050d031104030308040303090f050708070b030c0d0e070905040c0510020c0108060f0d02061903110c060412050c0d020a060c0302 80
    0x1c044c40503019842d10390710b403810a94000100e0212200003080384002c103071506140e100407a4001e5032403c1d160070302e9005d4144101c0103802c20b4041035002100402c1224a03204821a003030307080b803500c1c68039500b003101c0d0b2102414440d04000c1c03641107800041400ca00c1d140c1c000d54100e03800743c011104e100c0342540c03050781100d1071f070f0fa070075031008504010501c04680100c41080c0c1140c03003854002140000d944621340d240d1148072044030725800c03d0008111300c0004010300000781c060140e50700d246051018149009228101d2040038841d154002d60a60010600c03202d0020062500306004626144c5484140c002e814000d05200c1d00a8441c981130961001400619044060b19409072a40342c903000c02200c3c1c000c1618075075100d03c1030540c460040c2c40c0c40e0301a004241c8001d1000180301d005542c081c0c2510a115900322150701c040c44880f500200002c0d000c3d4115801c44460036520383c1e80e0b1380466881c890214540040d12454948900c0030f1381c001050300a26001d45410008036118040840980c2b1 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 972751870 1250 972750620 972750637
    0x30609062403080304080f0c0a1110121107171207050307120e1f09020f01051612021912020609160605030a06050a0e01031401050f070305090c0405150312 68
    0x41c42641400021180c00045030428050304074542000005852800a540036078901021a00591003e80401082e86030340c420700c040c100c038102c41000100c1390041c4aa49503041c109419520758043d800d01a8101049031131264000f084010000042d0270300400c20f6201078102801c215505001903581442401664080c00c070556421040d21804400c0501410f1000c000485a004d041c20712140841c0c90355242807404004a00401c03100e80e980104110301454900c85030500c0000c0060710002001c0c4504080043d1307209000d60402d09003600c0491408a03080c4645181a0f10701403200e0a10210381800740a00c0d10b02d508840f09907a9031180c16072600e203549485044205842070603c8168000d90155a2003841148006442980e803800596001782c00d60000001a100c0001802840f03e10300041070500e160301c0c028019030070322030074445811000074540810035070f496001c00d44040050000c0c02c0071800c010800c1c4064107107840c05080c03070002c10320b20324424452081c80e805e0358081081542c0241 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 972753120 1250 972751870 972751931
    0x1203190c140703090f0603150b0304120809121204050609151501020c03011103070914090103020f06120a0507020f19030c050703140102030403030b0d0b1801060e0103060906 76
    0x296000c11004107140c00c8600e04505010b489130011030380c00240703030307150006051039a8086440d0070426030340c2400162982092440500400801c4042206400780c0241a80d051800c00141d076500b2800c9401e10388400c0d810b802500d000103000c1400280303016031303074011405401681d003070307458500e01c0302d45d1150440090b04070a00c0800000707a00020410a0480c0914103006640b240c0f26810006821103c240e03100c65100070000c0184a0320603807002c07412000d044121403e2003044000c0000a010880510009200d890181411011500c2e1001034880403c0c103180c450303a05081c4042d541c0c02600301103d45400521500714a0b6140d010000360616200c50f8480240d4603590858500f159404290340c001e4519104514001000039581e0250810325848030000680728102480c1c000c090b6422120070b1481a48203c1d031507408a0070050072660000007041c4041c1621440040e0507016240b2684035400014018000100380422904519540c0b0300c200c00400601110f055640c9000c17540c110780c0c21350b5 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 972754370 1250 972753120 972753137
    0xf03320a110118050f061219140702070e0c0d090308040b0615030412020f0a0501060f0f150f020f0102071a0a050c030a0506010203040e071112090d020f0a081203190c 73
    0x5017080980303604120303c06170100785004c0b040d030b801000790740003aa401e841140215005040b4880c56201e1820784405000003120341e030804d0007000350364413010b000d924481400c000c007040051003403004861804103401b00600c0318540703904000c1d12500084600341d40c06088000041c441d0700d061400c2c03103804055161880d08503142e9454603044101c4110075002903200e110184400c000d01001a80700d070b584110f0011032468200314880001001c103502c203800442c078246080c4070f000112000301c00072214a203011a00c41030380490807450091807120f0301c0a254800071341c030700c10701450300c02c0f02d80558041c14948180791920b012200458008440e40705040740f092002c10f001c10b09039005030740c104505204880c02d22740c5688130001008003c2e51201c0105030941000c403c0e002c4d09000c3c122040d040144480c0c2050504000300c1c032000041c840080c030070342401c81182d0003a070707031800d0b2070000c5c0203150701316407164680d0950110300d5881962250394a4107a0740e010500c40b205802554071000c2595203c0c041b = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 972755620 1250 972754370 972754379
    0x20a050601051c060f0609020f0a09080d050d0506150a031409160509071e08070315240909020a020c181b16150b01030609060f03320a110118 62
    0x30f0429120540c170301a145c45001880f180c0d2800600386500c503980440d6940c0b10703036074001741910504d41c1c454807850300401d8001d00590f4006050b40c00c141a582400325182e554000000c5203070003c4004814003c0340401c400c2c464990507800500c02c9041080d010026841d040c8040f07940d12b00400e03081146a01c44003003480f06043c107800d415005041e508004407030040300c2c000075119151020320301c000111000100300d015a0b05009500e840010003c01039034250818160b1003440078080c050160841ca140b20a043c07140c8034007461801000c6003d030031507c5000d44c7c10000d45803600c907448644200409a008200d082000d40c00d98050b0380c2020003030304030760840d00100c202e0b604015a0341c0071220040407504040b81d01b1800c1c001c15405801400642c6022180c000f4003164110b0f0048080e49240110500c401a01e151941c400d483e044207a0020b21884c008070041c2031a161103e01070040e00f141043c9442d0b00c0c000450b400d502e8820b000040f83c00c541180110b41c1c5440e40300500001403c441010003 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 972756870 1250 972755620 972755633
    0x402060a2102040308090112020306030c060906210621060a090305070506100e0901140c030c090d05100507030b03100c02030c0d1205010509060d1e12020a050601051c 73
    0x10a4071020052101c1061080c036008040703030041e43c0180c400a60001d8601042d40e40000b4040407138030154000c508500702040403990300c1d213206402c24000c3d070b40014400d41036611601030b1101100141e211003001003801411402d030741e2013610714901075941030721140e08210f011100e039140802d0f0f900c002e001e91b03901c42203079101418142d0003d03000c2c018200024408540c09222041c031456281a1411131036150140b01c00700c0c4d8a00520500d003a9141045410410300007545098001c8408074880d900c0e0786031540d140d1802e2160801056019992041c81401c00134081584d44036080c0e081000c018590300d104040d400d42da43d034034901d80c2c1a0007800c0500c005081c00d91111000c0c15203403044a05120500d100c403440d09101d1015100814940c0111400504840c01001c0c003410f81650032902d5820540d001c64140003250b000109081d5100100e107034420305410f10550040d401200a00a050086074040e41b1100044015603079401404004911030521203c2c1010480c02009500600308081d11001c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 972758120 1250 972756870 972756887
    0x307050307030c12020a170603071203031d01060e180105010e18071707051e0114030c0f0712020c090702030418060906090b0907080f010e0601030915051008060402060a 74
    0x1009001841d190030901e10b0803031010703204521b010b44606510420340b01d024040c480e0000c003031910980c0492000c2c0828204041c000211070b915003000f20701c000c0d0303034400d2005410000d16255680c0d843c2140001c0d0580c400e011b0b031809401100e41255298040807211401da40003401900c54900d6200042160215040401c09210710078105a0340403544640010060b030354107151609039540196401e124910b055004846c6003006548002c90304800c103000030f006030000b030ba0503000b0300101100151701006041304030b0b6103371030f13120380515542c4016260074480a01108030902c014410010400400d04003441081d0040d403c680043d030400d40782c802207200700c1e0820814580c0007a1908030000d000724060007400c01410a110300801d141d5081400d006000000801c1201040840c10601410080825035141501c60394160000c0303d81d54500168040d1000950051441690b801c21100c06c1406a100600609600750700701481c03981c88a02c3e07555403100f0b80300690300410400070628000e000d80200e = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 972759370 1250 972758120 972758141
    0x160902040302240702120c0a09020408121b100213050418060c0504031a0f0f0708061005070803040606090c0207081c020f07060215181b040b0607060e060606030705030703 75
    0x940d161141ca540464954408140406c400d0790102c0000d0030107140240025010b01103456086040c00d20f00490595141d41a401d144520800040c0e4041d04081d11075881d51002041812514641010544c20700213600a004888901d007112801050b00d103424051300c1c4036204502100000c1c0051a03c8810040408124810a00a081000000207400b00a0204c00000c4000c002c1d000391504504c140e0308000010054940e04040f4410042c2c01c0f5004a000c903040941035441c00251200303250151054131500b40003408051003c01008200845a044902a030341f00c1501400441c45c0c004003130b42d90307072410702601c40f0036049040100080c0c0d60b0100c444813041a544110342041c654101300508281d401d0300581c006810910280c20041c504051064022000c1c1a030a062a01918142c50712510310590481c0300b45044050b4281d117a40395005040c8444004000e81c5d84c23001c60b841d0801c020110320aa003d01402a0400665245003900c250b9104040985500385503903242a0100c0c01060000314 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 972760620 1250 972759370 972759439
    0x6280b04061806051224130c090e0d050a051615020309060403020c030a080d0f14130b0c0a0e0616050a20090106022a04020c160902040302 61
    0x400203108421041d00c000c000b140304000039589040809005a0715140420400701e907000c00380d160b0352a1404c40003001a4440782e4003504c8162100348880003081c003183d4000d05403010001000c078042c0c113507900c2400c040080508940354044611002c0d500740c010051500c010484c14803000040f08030240c08551414030a013071684e509000c1c019840100d80042e110941158030140401003019010440450000000c60007040c110351295545802886034034401d21364a501e655480b1140f00694102d0311204002240b07a01c028545540c5c280301c062a20b80d010b03500c0554041c003068582c1c40c0035041300c84408040d514520707408807100a1005a5100d001c0b200f004071550381e10310010032010b01c41094040d100700310548495000b50501649941c504004034890103414004011203500001c203280d85520141d04d007601540b4001c043e01c100d4050020641e0028000a40150f41030008a407103c0e400020110441d5031035200d1503410228015408025040900b001444042800300d94a800c40c8a0481d403 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 972761870 1250 972760620 972760631
    0x2151005060901030e010e0a021e0627030a140d110606010f180308070b090303310f060e1e0c0112090f060903020c01020c030a060b0a03020603090f06280b04 69
    0x1017516007100c00813a03120388190003180c028021842c14003113107101010390b0040c07180d44114050004025100d0703410002480810585042d40c0342001008414502000805607689006141400d01c000c521404c3c00d05040e00034440600c0c0194061101e030800701c030141c401040307642c2d04c3d03e00649103502040084414400441100e094100004580b400514801c00000d601c60865191000600e140035100461a410074403c0005201d41400b0312002407594411403442c1006100e0500103110743c000010b802c0c2032191340144180702c81500f0040705007151408480c03184002c8135010b16005240321500c1030381d810103c1d500d0160340c0301d10101800c000e56480c001450303581c6940c0700d107540711501d0000c0314815101d030860800d0580500010b038241e2001e00282000d09040000240c071002c0d40c403c001e104036a0703000e9040745030f2141c1a086028541c040c22065403402c00e00003d03940d4400034002300b031940c410b8000040c031050683c0c017840300c510f1100d051a44000c40001c5600b001c0c2079a0022580c01541d1030 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 972763120 1250 972761870 972761891
    0xb092b090b161b030501060b040302130f20090901050306040f080d0f050411180c0715020712083c06040b060d0f0b04180201051b15070215100506090103 67
    0xc010020083c10300041c80404a1a5142840c2500d81c00c1d444800c8140d000e1004101680751130900b4104085070010005a004c107102010008140b208200b020004812180004c020a10700040030508c00031240092103a036a01c040542d640d500322801001d03c4c00d2031012500094409000d480c0c1d401040b80702080c84800002c5440c12640c04540c00e40e0508640c911200d4103090250141c00303940400c4501103d00c0c50507416022051003481e90040100c8040900714030069020760650704102d600c40700c03860b01940b003200000c0c031078641500c0940c54010f0300d002c001d150392034620f0104054051102c01c100348801201982c03e2156000349015040742d281d01c41c0142c3c59075840c0c018039003105c20600c0014240e6800408200b02d4a1109003075000314078040101440c0311906038400c006980c240781445d0780341489001030405503104101d1081c18030401c203260030449495404548a410365608440c0007800c98020050700e2801a81c4942c50300309086d40500840c24800020102054107060215044540 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 972764370 1250 972763120 972763133
    0x7060e0a0c0312080906160e040207060b0907020a0506160e030a140c0301020f0f03040c09050c04060f0503070e0108150306011401110d020d0c0f0b092b090b16 70
    0x540104484006600506104000141d80700842007031403850101c003507107040c0700000d50f59540608035002e441c5101d000201400d10542600307100b00030240c0195120348041c9001005491038de84864030803103584002412040c07000074080b00d07594121006001607140d40400d20032243c180882c800c02c021111094401580b010846808090700ca60503090041221f0f4808608261300c40e5030b1944664010480c1c01c00d21103140d0b045d12035079500d0548056a80d122485c01650060590b0300215070642044200b000d05000e50000c1c1081720800c2d26150303240d40d203029080740d140c4811500c100c003003400c0000c0b9030015403041e04034036404100e10a4661040d00054002860044264003845d01c0380301c0e50110b00b2803940c0c018068801c2000711001000e0b21040070901075200c1c504d0380f020908026180040a0030300410840502c61690000d00c261058207004078142d40f505d400c0e070400315110743c0041c880d00c40401504202d29600318160b984405071400c0048490342503010400512561200482c5140880c18 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 972765620 1250 972764370 972764383
    0x50c250506190e0f0904080c030c060709030209130201080426180a330c0204140603150c0703030902151603180b03060f0310020c030403140d0507020607060e 69
    0x6000d4400d00030b00e6040ca03001807109524501c064026481c66101a081340c4600d490301d50410b034001202500c0e1412200e10918501540d000b0803031910070401809442c42d0081c01000580c0d00940340d510165540c1c0880180d049424a0020b00142000002901144ca84075500c500000c4052040382e0507940140721a0f0650401c4111104400c0d40300350701d056900d8210f24100c003c0042c2107408195030071342c00c070788c010407503110155008400c004024003800600c074101c0c80070792690050003000300300c1c0240718014280008403800f50181c03042180c011801510892000d03c24400b81d246180782542070b54007280501820f80b0101d8004501895013b40410341c007004d4040011000c29000300044542001800400d00d1141c11015030f071403000500042c04100c0440780d00c050306843c01d11000440102291400a4a21a80c20f2a62000c5141c8802001c0800200f007200d00804c4040b00c80b20092101e5034030390640c440d6040100381d0400115006003006000307000f00c1402800d0000c1c0030383d90301f105241000c0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 972766870 1250 972765620 972765637
    0xc0c040f060915080d051305090f0a0507020703260f0304081306050f04140d050105010f080c061c180804030b1b09091503160f0602010c050c250506 65
    0xd407109824400b1400900c50488051a1100305800309072400c6005911111a00c441000700400000e8941c01c000d10042110000c20000c1d120b00380c14a440051012114402d0f00c83c50446800d00e001300d143c0e54800950401a00d801c4420382c1c00e0f000359400203021101a010254003400010b21048200302c0400c000303503200b54010301d01c90344c1d02d580380d102012603000e032074100c101071000611603000e414081c24180e0f000d0394000250300844d000e8a4000078104281164001c101390700341800816200395442c154011100d80d1021104c2100680301001030600403844e5011480f440c400a0001c0716807940c11a03c0b0810041d00000000030407a1200e003425405500f040d90300509520a11404160b540c1e9070304143c21005071000d081460700f80000d078040c800505107038041d030800c0c407000510756001c0c4042c002d06a0100000080142d444801e004e0402c118418240554a414228610207000708110b9400300100e02c003400c00c07003003258400070340b080c3c9220002c15551078000c07020440c0d07150070b0000c2851a = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 972768120 1250 972766870 972766901
    0xf090e090a030f0c11060d062711160813050307030303060f0603020301081e0c031b030f030406080a09081c0902120d020c010c08120c1b0102041401050c0c04 69
    0x50280d0b0901a0540b219a070090080102e85030842d4086880051418440a000ca0b0100c2d07413100c0c054a00c80250900350840b807100322502d4110303812000c032005280c082500360b00c2e042c89100403560a0360f00314051001030741c424400302760007440064944070080c0341c040080f103600d0300b440f901d800220b80b5003a10b981044002c40c0d9106010300258054090750402450680380c15490740d0b051030b0002ea00e0b002c03115210b410308814251003900b00c200502c038140c00c0c1d0340041c04031000c08440301c680440f042d18458105009000b040581a01110080119415100c5544405240c0d84a484621004180482041d582c070107050109540e00040c89808404007824044041a082050300400488031128850240680c1c80703048080c02860b00810b031001c0001003401c1882d04032100f0b082c007c443d0702c02c0004e1020442e80480c1004081348400d406400824148082440100354443d1094201d02c114040c2c0348054900b0b203003081040d8425802460401c080300d040c0e034200c3e8480300c003042c15142e4001464910 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 972769370 1250 972768120 972768133
    0x717040c031208090c030703020109090c030f1505040506060a02150903090301020d060618051516080705010917161101180602010b01030e01050c0306060306060f0c06061c050601060f090e09 83
    0x400100517034103800707004034081e00c1150716550003c1c02d260014401c01742090f0300c0710903400c1054041e0f803180d0484000790b2002c0c8a000200741046002c039149000745031185180c5400301d0150306001054501e800c2c01c0d1b400801e455055010031889144c4001d00305071051008000c50b45454a080c0042c00d000440250003007005801c2c1000580101c2d00340c0c0c504011000010020081551481800c030810140c940403165500010640306404441e003540142040c00d001820f50200300b015480301e02607500034002c030750340d04190141c00801413240803038440829829050460100e01f0000f00360821402c14105960010450144101c61008682c01100980d5407882c9040345560180104141c01e14030340700800040c6040c014030100c41c000900541e010300f4021000516039111001250300c4003140000080d11044540e44051b903806040b65518021103140340084c901d40d0040403c04400342d400320203031469a0070840121480a400501d200421500309400201c0300d02c480111801841c000c0c2c00f8020 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 972770620 1250 972769370 972769381
    0x6060d150b18012a03050f0c071805011e142e0e06040303091806080a060501090b06041503050a0609060609050307150f050a0c0b1e07080717040c031208 67
    0x1e0265804046120f54201c0300d002881040c1c4505004003a0785c10f040180c0c0b0340c0344d004d402c0c0070a402007e41c01340c1641b01da2480400c08441103035000713140030703143c00003400f07283e0b00e0b95102401e60029a15031441030203900801d022042c210903a4680c901e00140c000c0c0c6011030410504400700c4001c9409101c8105c00e041c2010300341b0b50182000c0c01c8484203403076070b529091441c2d40080c44010240b103441040318403a01d0240e50842e441e00400001d080e80c00c100c903084103040c00d01c034004080a200d501000ca1070402c40c080e5904004040e58111150440380c9002e81110300c5003540649001000c1c1112607540b0704c004079503d403043c8103100c0544100d607135400817641007901b89440c256440d006020740070044024400f0059005c41c0c001c5070b00e40380c0e182c401d807521421801a20710740031160340149090303140d40810116400300300b51b1800c400c803856030b110020746502400340c07060a03090303a038180025042c105660071410241c4990342c02500c10700c045601d0541e26202e146120504404507800201054140320 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 972771870 1250 972770620 972770627
    0xb0a231e25030b0d06180b010303180911032d0a06030203060a1a0d0510020d02091309020604061b0b0106020604020111060c04030b0403031e0e0f0606060d150b1801 72
    0x3070903070700390604102d0320759400009401d1000810b8010402ea454241c5000906c0246400f0b20b58958040346820765561a454050814501201034009212900c500000da40c1c10030b008a444918007010705503e1601c42d9203489019414400000c40200c2403841c108802d21950000b841c0300711190a00010340b2402d41c410181402406011044840d0604005030306260310040220f4802c4002c0b034020210508600c0d1490521540a8000028a20102e2a40b01c802c80c59001002500812101c0d401c0244c81c010030101120344101019402030340600c014400c0305e000d00845900661759900701080b1000c0c60740c030070350710100981103803005810030b0090004550300003400081d43c4410001a14891414083c4039a490017244006041000b907000840c061601075881004a140e00002c2103400208280444000c0c06080340e0071800e03889042d22174011041c0c00320700c250150200800540c41c02c1050541c401c007030444166030b5075165182500c0043c15058150081c82c480441c41420200c44034200c0026 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 972773120 1250 972771870 972771931
    0x303070507180f0e15070c0b070915180b0f0c160303090e0f04020d1a091e010209060d0b0f1306031a13060905071d040b0a231e 56
    0x150120f0070b040220121040200314004d202803885400c80c929034944c1c108441c81f000f8041c000c0d0482e40404180840c041e40480c401c001c3d600c144020f84000640d1030401c131100400300410b5002c03031021040511078624141c1c01401c4001244002d54201005000f01c1428650350a140310541019424108101600400840e0080501c00540d030f8a03803030856022421964000c20081c0f00742100b05c4041d040154252403190103510049906105181840340259102035102c210207888004c1c201c0080400014001c454094001a00c06820700417503505020142c02050b20a55010840c4e40c11401305840e05041c64960b81070354a0013060003855802d1110380d04107800a654550301074041000744030080c19400102d00e07036102500246101e00c5092080c200902c80d0441003c0486040207900340e00002000039018902a03191800283c5407407a200f000c131010480340300c03c680255912000800da0034100a90300407200540300c0240d018411816002c840300f01c46041441000117202208001c040004 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 972774370 1250 972773120 972773141
    0x4020d0605042a12090c0e06040b040203011203080a060b0c060a0b0307061d120f0a0507080c0a03030c1a1006182102040906020c0c030f060606030a0b030307050718 72
    0x1c400110581d01d04801144603102d00f401c18041c030342d074140d104d040c40f5038001c0c445107400000280740c150315034404c0c105204040d60114400c41c2400d0001c4030070310380707882142e0403100407000c02000c0e0280c6076019590140024603c1c00c4099844000284d0391840e04000c0552030792040140003a440c0c40c00182d011240d40301c0015010342e0100105022045d0403070404052000000c1c1d40e82d201043e01800500303034a580400fa11141e01880034a01100030001a0001d0007a00c50401d4418043d00d454100742d07180840c05007550f00400c2d82d2002c2010031f01620807160003d000b09104c8041407102180c00c840b4600644e40e064ec1c0c40d0340c2d0300040090a500c1862a14103072107141110400f03030b00d0144003103074840c0001e040c0007428103440c40f000119070340c56205c0507446030312040a44d1540d010f5a151074880c1d40c0740714503e000c0c0c0501001500d8085d0040752a52084800a02140c2551601010100140341d4101d565030144000c100d06c5000c11402c00100008001c4031032000f40b4446129808025603046402 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 972775620 1250 972774370 972774401
    0xd140c030d0207081011091e04061703040317070b0708060901171e0309030615190b030a05040303060503032a011107080309071d0703060509040503091e04020d060504 73
    0x10188043c4c42e001c01d016044585800340840c4040c0b500070b45009500c0350103421940100803003403041d411100741030318030b940c14001c42d000c00045540362003281041c030030703020304610076001000107000081034102611039a02d00d1600c0399003051440c0e5205095810b05403805001314410b0300800186d40b83c40049140500b403285407941020f9050140c096848144071440c0c0300307190140703040700ca10700400c0080d10250000101203d840741003441501030344140b4000580c2c0904002c154011030180aa80145c00b221140c03441d1500d141c1d101c02c2440010f240291044003090789138640050717281d9040028288152641008080f00b902d1b030000b440140c00600c4280f08513074103068900c5500c418007401d850344240c2100c0800d54942d11802d2281c01c0c01c465400440d148407003200340038003c90b07030000d181e03200c0c0d0040d85007005183d444204000d400c1008a8009085a0040044c42601d0030102e5004c1080c991001035071039a58080f000150980e00a2220141c070f0582c0d400081010789007500030f8112080e111a07 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 972776870 1250 972775620 972775633
    0xc08010f0e0a26130306241802090607081201050306070c02130615020307032601090c03090b0c1e13060513210605250309020d140c030d02 61
    0x94019403a0920804003822507241c1a180b1044029031400622000c003014101a5450480300e4100b1040c1303081340070a9500f03500e81111141601060048090000030070505101c0040c07034816168582504070100c20a52074080c030000c00a601e907840139010403841026036a40b928504500c0602c604016071100388a42d0105051180003034100c181115000c0e016100c04d115242011003070030152003603901201d0b81541c0b9200f051004c0303902101809082c0c3c8203544403d5008a07087c000b00e81e03041c451661803905034440e03004224108480c2c1c40420090134605001c131b070314811511001c0580e10121481d200c40074001030500b9002640058100c0500c3c403079400c4900b0410003141c44406481d1900440c0c0c180200001c142003200c81e89004400140461403c010b0340d001940d0041100032685d002c100c46090400e004209041c0725500707000ca1491204d20704010808070041d0032005040700490a1341c1150103a265400440c464100c92012001041d0040c048440c0103000e00d444c100d925038079a0704541051 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 972778120 1250 972776870 972776891
    0x31902180106120903030204030507060503090d0f02120d0b0306191103010b070305030601141306080106050306030d2601081501080303040b0103060902210c0108010503150a0207110303070c08010f 86
    0x2d880320f0b110718042000250007140303480e003a4020300c99a0005807580c4100c85000a01c15071042c01540324032034100580b04050381c01d0b8000d46880400c83c1e035680240c0c00040e00744035402e0014020348440c682200011404440c1280424140641500e0405211005540010000285000d004d0022400c004298550b45c98460100140c0c040c0c4c5400070b04000d400008905960300c070700f1400d00480e1450610542d24801205e261401c0c4003039218401c0400c90000000404a028401b039900c07401028001d03100c0841c109004441942000c14610800c0800010319460400c4001c0014080d2001600911064100d0340d9042c0c0b007070380140d02060041e4802c00403c0001480001481d04499102d01c0c00325042382c007480086c0031905c0100c0f04165028100300c0c100c01040002030601410f04d02138a0702950740e62201c00b03054480c10764029a5103945414400300e84d050000364001c1c0441402400710b06102c02501001a00390750090105460003039000f4001d000ba01000e00c100c1210301d003104030410107402507 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 972779370 1250 972778120 972778127
    0xf0615020d0c0f08070b090d0807094403090f1903060b180708060a050a06050a1404030c03080d0b0612130f0b01090e062a0c0c031902180106 62
    0x74680001c2000c4043e00030041004109426501401c1e070042e081c16442c6000350030b40350f842d90325030480300020b100d0b0400b0807142806440c64800351a40d112000380c001812101c290081c10030740a146410b0310b203220089400040b00501c052407900c005026507034441100041004400040311000c0c8142e642410b80090a0300f403800700b00840358054008030f40c03c001d06c80010a90300d29001c030024101020010050f5190303010b070980344905401c590038420350392607409103d46c1070702074007540010440c1013083d83c404500401c2054000b4403035039001854203483e55141c08034250240e008580c2c211010804040c0420140940c054201c400c1e203400d81000381c3c1400d000c10700c1c0c00150100c8103c01c88110a4024000d0984858500d5500104540e000f942d50354940b500074100b580c0c14458a0150030f000c2030707c4407440302103142500c3c2e400c0c200c040d07003c44803100c0d11203d91201c0d2202d0300c944a2400d0019582e1030510400a2841c0820f81e0181d00c0c1a01d07005216200c0c001c81c038840c3e1181c44050040c080c9540 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 972780620 1250 972779370 972779387
    0x80601050f010c0303291002060c2a070f031e0213090501020915030a0c052a030d11090a08031201060311090402270a12080f0d0f0615020d 61
    0x203003440c1c42d03003c41446003001c1d001081d414a003d83d00655886000c2440c41583c000c880115405980c9400303240740d90181280c4800741502c5008220104100b15142c0c0019082c410b00e0300004101d101c810f0844084915203089942c0d40302c4030000c54041402c10034840e01035070b0b100e682506804186c04a110583c0003c803002d03905100888280d641d001d101c003d104095066400c58003000c2c0006801e2080200303506580d81040305d501040da824100f404c89240e02c00c509981c1d10716808104049541292980c0031855540b441801c00c15210a018004a0024a0165050001c1c9680c04a0f560f207800c4805c0c80401c00300d031780203412281d004100780005900d4601043d41103600620703000600f010310708070750310040c824241c1707480d4840e001140d800000c46068070300c0909031824101070a0152450014001130031468458036031400014003001011a81d09401408800c1c84807010618142443c9111011251440098080c07550f80f03070800d00004500f10606820046140010800710110f280014000d51 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 972781870 1250 972780620 972780649
    0xf060103050309010c15020a020c0f0a0b0301090506010c0203060a06030210080408033d05240717070c0312200d030902033f07020117130b071808060105 67
    0x18036074010014050b2442070032255104148056648401c0448025511444180ba150bc141c950524003540f52034601526400c40701035050b4541181c3c030b854a91801040c00401083c10300800750f89580060f03405003c01032141c140d00a0009a1a0460052240388601c3c10010410300a50340305010209110340141c03a448600020802040a05d0514001752089020200ca0850b4105070000000304501124507054840c180c0d0307045080400d00f241c0c041e4030010410404001801046902d0200700c0e4000d0404060440c0f0504500e4480540d40c0c0f0306020b05140e005485164491600b005e0040c3d0000000100c2c481020310280d80171004483c40b525603600c1860b05082c16070b10107001e003c6440a000c01c0200d241070190300866070703500c9a641c207070218108624405a207034400b1039014401100003500c500d9a0103039a5607a031640d416031000086100603180614816114804d000007400c03030000303c0e1082003a50354810407002540d5590701307008041c2e00000900e400c90001485a0340b07400340d0b071401d040d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 972783120 1250 972781870 972781877
    0x100c08030403021629070c0509070e130f050702010903080612120a030629030c0901110a03030b120a02030a11010c050f0a111e09091e0f0f06010305030901 68
    0xd441c0c51a003640751030945040302d20120b2840100254203030b004101102502d00502403001e21519440769050148a4000300030204a59003a0601c034600744a00f01d264411064100718884042d05000034043c03042c1d440108013240c2d116814403a01c1e80e42e82c01015049560742c0000e000e103141c1540e01401c0000010a003038058048004000d034520005c002e8403211460402c0c445640c0c210b24a002006000c8500800d9000750080d05200307603103500c8030b10800952420503d201d085403a4281114026030020040c1410085040c0c4800103c0e030f014007100d45040c1c40f81d00d000800505450034405e138a07101c1044075500d80c0084282c0f0000d6100440c01840b1181c0c80303005424442d92000c01a85c040c04281c2c000f070403a00c60306101250081d00000d106801d01d002c0c0340309200903070000f020004101500d00000c055454001002d004c181050f078950740c0c0040944044d625045d0441100c000c80004481c14032225a111881d140c0040109110041882d116000500942e60441d100d4a640784112a240ca040 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 972784370 1250 972783120 972783127
    0x3060b03191e0e030301030b010807030507030602030c042103020706051c0209041b0305070215160e010908240112120c1a010605191d011112040b030f06100c08 70
    0x1c0d03480c0c2640d88010742d080c1c02000785040460445503681c0090004803030f407402d02c42c0045000c810005522084030360100003400c03224195560310000e900040e180504060040c80081000c54a1003510004200007610070429000581002031809040d94006810b0110411411014040040402145902c403039009070b515a54180807a000385615110311400e41c0000044403074496041c0c0205000c1e071110b13804c0301c044640c1d0200d0b8030b0b081c2600755641800050704084010201d401085940b040341c10504020141507540c076402406c28104402400401184850995042c150201d1a07070240000348c4400f00c54058030344e01c680c0d0b645405100306040c0b20510030b10400300000a10101d000d0187c42d01c15050650392088080c0840d0407540d1080b0031003880e440c108120509c21108119024142050f49120074040e800558060003400780c06013450040321040307215100c0090040000301126042155203107001591001805000b40c00302d403290f545041d0503c40543e02c03c1d080d00000707030058000d03503a = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 972785620 1250 972784370 972784391
    0x130e070305150405220510050906190c0f0f110d02100f02090d080f070c0e09010b03010b100c2108012c0c0903030909011e090b28090f090303060b0319 66
    0x2400c80c11f03440d03098180d424101003100d01d0402082d8240103480c08031002840c0320800602c03000391650041c281c0009690f40743c0440301144151ba60401c0c8025500f8a481f00712102035100781424825148403015030300010034181408614450341001460011085007810702450001c2c560242061028084e40c9000c1024001c018460040322071050344030303031802c0d0580da4440c0f501120317500c00c85002c03000303500e054148250b9090601810310150001000c400011707544800c142c80301e0600020030385910b8502d0860a51480020441d551149215100c400340c0f0f41c1340600726521012003150865103090701c007104d040f014800b0f9950540003202e03486c02580380c07a150404a49540981c03800660302001a50000804d894400c040a50011181c03841d0700d0055203403015442510054405650802084401d01c40f40240f0054510304e544a80140d29a40d681c1e00e41c51036040d5072441d84200e01041c0ea43c0c100104050301840f44000824a1562007810752800d4006082024440402568610389501000c0d4 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 972786870 1250 972785620 972785623
    0x103060b0118060f080105040b1f020307020402220b0f0301120f0615030605060f0a0509060a050901080d20031b120403080c0705011b0305130e0703051504052205 71
    0x100000300340b00140300c440d42d80d607802454044106407042c00b06141800108007410b0034000c460f000c4030081c01c141c4101500d01c030100c00c5030112408000c00c6010034444030b030050b5642d0004040c500c4003044900e030842d56482c403030f1206a1320f85d4424004c40c1020000c501000319610160781c110354400724207011081050800c16070f0300d2582f80300188031b14507008000c030400100c44102c105590280304200115030300d110900c80003004648859610074146c1104000c1e40c544605c4641e4000c90203071605095a940303070045841da82c001c0e0070400c00382d0400d0040051455104151102010011724040940515000d205481e0302c81e480f602c040c00f074824045001444801c2110b13009190072040f11560b074a41c0e0b414103a4440e0007d0310b07045002c0c09007500010700383d032040481080168407003205141a000c141e405a486900030247c0030900641690002000c1400010080c81008240c030b0215403440c0c211500c2203401c0440840501c00c510304020300585028080d4840c0e00500140601404492242040c5 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 972788120 1250 972786870 972786887
    0x50405060711151905100b0d050406020c010519180c0e060d0b090f100b06040605033102011b1220100b0a0e01060c02092d070908150103060b01 63
    0xc1054000c410600c0380b0034207802541c0c001c1c050040e9080000d9141c3c140c0d5480c06d841d9900c41e03503003064014445c840010b43c80e6484260020f01c01d810041c41c01552603541425183c04076541d003412030640000e0141072402d402005007403400380c580c00380d0742d034065070310b499240c12030780590b80400d15a000000d40725101d8a5031a2042504200808058a044c1c0c1c6807560701e04d4008072a5a07980600c5920001e41c54003801340101c80d5174018202401c182c2031000c1210f85800c0144402020016901c0405112610701c09003604010200a40c0342c45910701d00024000317803804640d48410498011f010008600300c0690110791501520344600203000d9012610b00e400032003122203103036008450141100307000b40d9215902e80034041d1041207040d640c4221100c2c1546092040c03d02007803081c2902e00040c903042c00059070042c49008490007480304082281141c0707896000c2c41c1030359150304060108254022070204000e1491000401c24200800c4240070701d40418480105200e45900c5980003a84c020140d5 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 972789370 1250 972788120 972788143
    0x3020a050609240f0c0304030207090615080f06010806010f111509060f090304120804080a030c020321091e0907080a0b09070e01080a020d0204080304030b070201050405060711 77
    0x101c504500749610344503100c0c51010320800080d8019800c442d04001915080303807282041c07100003841c603954030400d0310403640020811000c41c024003101240d419503d00c10702025060209086d8400704243c040a000f0210107070860140500100c20452103a0b80800440e030f0040007880e048442880e80001541c5501d41500281c0150241002604840c21421001c620a0301000b0071208141c07190298880c0f8150144e5500c0006d4100704404c0c4103160b4100c0d1103150b8140f06182651500c2d036103441050901449002c102c0004045850080562070100b040c10000c00150202d40c1480000250a01d45803080b41ca000d4025114600c21200c0444544401c001c62500640022183e1402c3c0c64000c02c0c40c141200c1495200d880d00c215414681080d5206e544107030099101c003e641d10280c0019a000700f402000003025607020083d640d0407010b2800030340028002440190307142c500b54600a521200010908002c581c54001084049880010259000303d0710741000b80d030b8464282900e50070510b030642c6 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 972790620 1250 972789370 972789373
    0x603120e0402130b091c0308010311010c081c0f020a2307050f0f01150609030831090b0d08030f09100504080a0f1403150418060606021b10030903020a05 67
    0x1d0004031040381e0401400b05d1501200c004c01520038501c02446821140040a40001c0820005000080c0082c05040e00440141032200360308815940c1c0c0c0d202e40d17001d000c20803825103800c0c01040c00024213011707944e00017007071100550034180c105500400c5c00c0e020500c8040080e0340700c80c40e1244c90110b0001c036200c0030740002c02e035407070408021041c941e2481100301c400070a602e07058421002c03d1f08418080709840050740e919a40700c2c070b0342c1c6541019405c02c0889400801d60000e0b403000c413064800101400301c4030040200d108500e825051001c49010441150040c0303c1c80400400003849030086a0b0320058110308480c0e141c803003a4040c0e180440e04015204042c1c6800248800d001c00c10340500802c003c40c3d0303500648001288000c4500211003400d41c0030b00241071000c243c0960100c00d048210940140c4001140c1084140310a100300c03900606440c0c0903034030349040c020554184a40b40507401c100180c2c0840040000103d00c101e4010503910307040594078140e03801007600c28411240c04540110 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 972791870 1250 972790620 972790657
    0x60120070b0307090b0307050d020d0e070e100f0b04120c03050109060614040e0c0f030a020303130306060f15030f180b060a0602010e03090909070305030d0501050406090603120e0402 80
    0x10407000d501da00554054000c660025000143c041da00000c40e4801c0f84103507a06401d21841300070039800b0350007543c1c00300c17012522151607081da11170401c0004010807140e541014a4102030300c01199001c100e42233140300c080451014080f505883c0c00b22821624001a5aa10300401d800c001d02c00c42e1003a00001c00329402c18804006104540c3c105d8002d443c1d40552820890f4007580802080f1892990700004642200002050900c0d000c010740b510401d014080e1040e054250f4006429680454010705054a19503018000c0c003040e8803c800c0640894914161901d0800381c80c24540313904642c40808141d00c41c07013104500805078102440300c0002400002030704100d8507000c01c8001044842d00d002c1c03c6400c1c0e001075090710502a1400281d2842c025500d0b10521100b4060310b01002044100f840c031420f0400400102d08000400c0820b076003030000100da5040500b040161044ada003ca0140d90801c2c4003072006c1183d90f40744010260f101e0820408080a400115009c1d0243d09103d20711120303c0e4 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 972793120 1250 972791870 972791879
    0xf070c120e01020c04091104050604060f0905040b0a0509120c100e010e0609120f07060b0d12090b12010b030604060f140a0902070b010e090307020916020c041406012007 74
    0x1001c15032500c026025107082d00d402205000459814101c0170304240c007628811802030a295002682244010380081103c0e9218950814105c007a948860910355039041003009000b035401c3d0392902300c10310580c02e100508200441540c0da01c0d1a40144034070f5180082c101103071030401c000c1d501a580c3d0b400e0702030041d0540c4801d058000e04600c4814007090141d40001418410081030030100f01804a4500341005000208028240c0007440110707005c40d0349854641030386d52500c0c0080d00c02071090444140080e000c03034009014072501d0340b160f080c0c03040504c03001071008002000c660541d0012007071b02c0d440340c5d01d040015000c0c10301e5610080d00d080000d440072601203071401e505812401e059035562000c503501d9980304102c0c40740e4600981102001c00062200e1003030b100c5081d4001c14008201c0f0300740341507500095038404065801c01544040b00340c42514054040c0194203a140e01200c0410010681801044c1e00a000400441c1000b04c0354048800186440002400380c40d06a400c65103030a40700c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 972794370 1250 972793120 972793127
    0x41e1a07140102130b1b070810020a0201020904050f31110f0a060302041406070206180a0f08061504140403030510030b090622080a0c020a0e0709150203120f070c12 72
    0x85c00b01c20761305290101b90010010800150072044030807290050a01a01c1c81820318001c2d003251a480d030031075400f0451892a613a903402000e02814400440503102d050012070b86400c00a40300f5840b007004120000e528580ba802400c5aa0260308044c1c902022f40750880001d282001c00108142d00c83c4490300302080c0141e050340908103644410404003c2c200d14501000000e0003210710003540444100210083d82008101ca00d40310107001d000071260b6601d4000c11400640382d50028002603100d03004001410218030343d401c0003648261404c101c92004000002d80c0301c000100041c081c15141c8010900000100b1007043c010360704031401d500b86060428080d0b40300c04040e2040780c2400342203e000c400c09040da4800004a41d4840401c03032a145a110342070f00c030601074800607a40406400300004980319004449442101d190b95032800349828003a0184000842c1070798601190f00500503c90105009481305804c42840400035201c0d554650046400c0041c0700c50003070000386000c1706800f080ba03b = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 972795620 1250 972794370 972794377
    0x803120402011d0607151d0102070b0c0306010c020d03051e0403140d090317040b07050a0209070318021513080a0b0115052706041e1a07140102130b 65
    0xc02d07030300c89030306052003004081c4a52000c10403550010b030800405000400301d401b00310300c0800c0c00030049113281c52010307818031040c80100c0e030700c10594002a50000f045200d01d0016403001c0440c2d07405041d07080050008008100da4407000380640d21051101042c58003d0050301d80c0015807001007410b10714455103102c0e158220303120880741c0e160814400c800e180400f0455003041d00d03055447c0940d041c070307644403844c81c044040c0815105c0c0c0820400440c0340d0081030f004055075401800105043c0d5081d1041c08880d94000b8010820140303081e00c0f0300e10380c0e00b414103884020b64048980e040000780d0345220592520071041104c15080400000040e010404503010304501c1c040c21100c7d400c2c4c0e90f0303074094007000c810b4415034030000344080001440c0e0720650403110655140e281d02c5030040c100e0100200b013907603120f034000c40004600c0b41842c0030141114003004000c2e003220840d04940101591580440d4050b80000801b01150b14414201e01d503c2541900c400b440d0469503005041d6235026420070951 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 972796870 1250 972795620 972795623
    0x10150e0a03021c02090c07171b0a0804080c0312040504021e040806090d0309050a031407050d0206100f080c011b05060c0d0c030902010e0f130f0c0f021b13020408031204 74
    0x5c040c6001900da2080078081d1050141c001c100c4000d1920100440c484650003158016248400d0045040002c61b0800048030818880c2c40d01603643c1341005141468420b21800c03540c0f103940510301700300015614000791000c542045d1005038850781d019004044040c07881c680d8031510600401d0003d0340280000310540144121402c0e40c4c891421607a00301c0507501e00303e501408981c4060440303c00603108044074415179039443c000600740351090b03071220f00701440c20130050016130040d07090008070148000c0f208028030100c60101c00c2035150442c920f032100901c0c901e140c10311161207403d1203200c902d0034a1407140ba03804016a41c041c588200c544103181c01101c00940c8261424000e140154024420303540392580584400201421100422038801d030095a801e401c124290704401c9103d00301e00070806091407100021410542c0003030014019010400164110351003800f000b4419103441d000d0b07140154003521030020010f0000c1d44000030344603070380c0500079070700c000211034450f20401540140100e = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 972798120 1250 972796870 972796879
    0x2041206090201080708101e030602030703050411010f09031407081c0e01081302040924060e0c03250c0c030b07030e011a0904050c150a0810150e0a03021c02 69
    0x180c640c03010441d0780ba06c04942140d0344030b01460041c003050000d0000100641c1407a2141412661a55581c0c81a41c005039006401300e40c03190240f0040085003024185d541a0a20700f40b011903101d0000103201410310701c4081c0981007070840d8541c102d1420310910b00501411011103210301c284506801014448408007000200c004c0d646414640c03084520034028044a0351041151001713400b00002022a00e6040301c000f142c0070500c48640900b0391200c00319401c0c03018005040342c03404c1c0390400701c07107030080c0564031b144410010007418400100703012000d0300038640ca080e00c0c020035281c10390381c00d200c00700c0281255940b801c00004200000210311701c240c00c1a9000e2141070745804c9014240c400b0b49042c4601e041c034003030300c145440c00c0041c13500b5070142c050001c6812040052001c00d92625080700b280f890040300003000f03003215800805858002103108803120044d49042e91010103c1d0780000d01404011460380d5002c02a551514108065030300104100381720110110700c1ca10395480c0d0311040380203 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 972799370 1250 972798120 972798137
    0x312060a0b03041b0f050f1e09191d030313032705100e0a050105090a1505040303020d09081c02030d0c020309010905040e0a0201050f0c07181a010906030507020102041206090201 78
    0x4031085c442894003102d0020700010382a842038010004090b400402d0602d5110340203107503d50994501c010203000750005002c43c0c000810340c080e00300644c0c85a110895404110f50700c4007640480001c2225409407220400400c05040d03494100c074001d0f88044c05854400c01ca10130001598100c07080300702140c008a9400790001100001600c104005502d010350085603032004100c030b075000d6002403400313080050800c2c24060319011540340b100001c3ca000c5001400c045800c0c0f0805030108011018404a803d000c01c8030352600b09c1031555042c07040300c0c5000117142ca00301144160300030000c0c2d40c0307210588034040c40350325048980259070343c100c010601c1c00100f49200c00242402c06200d01054218420080c2804501c0ca400545181c0c2c440000c0c224048010002d40d499074006204450281032500c420307429220416400d54141c4580440142150090150240d280ea03017106580e0221045410080741076a0341e443c3c140d009001d5980003070141c20502d01c0c0e0404022496000d02d488a100740c803070071301 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 972800620 1250 972799370 972799379
    0x1e10031202070e090a0c090b0f06070c0311150901050a1403070816140933090a0515090906030733020303010f0605070f080711120f0312060a0b03041b 66
    0x2501c045c07411000e80300f6440303201d00340401003041d017101040ca1030140204030101036070300c04103001c1c0e03111070001c0e070300340100e04001c1c410001104401c002906003100d00e995482c2c401c002c5040c0c1803040a14207414000d00041104045028940f182c5034000404001038480c5040ca102038403c030411101e00e401a107001d481c0740d0055000d00c0b190f0300410007800c0b4031340c02c2008402c20b1184112500d05039031008072032441d5500941c40012981c81d4401c4c0e06502c1c15840700c40d4a0240102402c072500502d00c1110010b01d4030341c1c80a403076010b4518542007140c48000c15103900020038181280ca8001100220380c0c0044509560101e195082803c0171031040888149030502c0c0803030f00c82c00280503050004c40300742e0080000c14070900192540c1402249188400266583da8505540c0038410403140181061410900c07864560161508003510102403d010a4801d03610380d1640714003d100c0c003820509801040c0c55440705940c07040581020305072150340f81803c0c141700180710005000d0070f00700c1e0684080800c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 972801870 1250 972800620 972800623
    0x1b091027090914061603050c091011010b0402090906190504151d06010e10052701031a030705060c010e01020c16080c091b0c01110913051e10031202070e09 68
    0x2d104e150085c20042c2c0f1400454000c4015090281c001d196001c0103014900f010341d5021907205080d200c64032000c1c0510a40d176149400c2d5186210068850303031040c096045540c545110300707a403100c400c07030707440104078800080340307440413015081190082d00d4450306281191842110388150b0ba2070714010701c516a1310f540309840411301100e90500040c4224659801c0d4101000b58211140407070a00908190158140d04140b11003142c0816204582c554405a9541c1603c25413844074100081c10300084906008030383d89084500c20f69001d039000041c000c4602c802980510948003004009650301c406404070300b90b8030101c0303081202184010040c0007803071510001d807016048030013402c1c40b036181d658084190701c240c14400b84064a59820030800d030310150207100d9200b0002c030404103241c0300c1f00042c0c2405a020601d00390310300c040c1e1411040c040380000e0b54002400e292202c68264659a9503040c0a0f040540b291b803008181090380c0307807281d5000d60041407041c10f41d0104000d0b51044d135034402030103 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 972803120 1250 972801870 972801883
    0x1f0f0f05010b040306232706090d050f04030b090622121404120f060e010204060912141f050c031e0a110a02061b091027090914 56
    0x1070201c030b5001c00003000082c020350021441942120055418600d80c0403d40c084031008407007410125280541207600d40c0704581c0355004418458005012a1405d072510a5547c1140f000036402d00502190720a1100030341c0c401c0710040c583c80300c424402810100019a5100c4095605809600750f08460b50502d05a0301c0c1d80c403107803940100e0310400b82598160255401c04a10b1104034503410200030200b117080c2820b1031030700c1c00b6100f8400d0012010450812200300c801400942d00345034010402007203003c0c2d101075000d043c1c52542d241131036017101516040200704806401c1d940b090150702d02c2018038107442444403859200308007080c02035540d88009082a484100c034000c0310307140900b07550342c003460f003021016500c6060400c0004154010761200919a000348149170010385c00581007008003000724108500c00c3c004008420b05251140b40010550081740704007804004400d4242e000c80d41c0c200c4100d11b04030302c1d0340d105e041035141c6070b00300b8001803d24003030b00380c0d81c1c00c0403030440e115643e1000444 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 972804370 1250 972803120 972803129
    0x9011203020613081303080703030c0e0f060306031014092103010b0331150c0509090406021603090e13031209020a17010204080f0a05030316021f0f0f0501 68
    0x2030086a501c0da00f01680c2c2030041c480c1511421800d2020403282ca5100403200d0144d0300403521240c40f2101481e00a0070746040400c680e00300b01410801d221103481d00ca02c03407546180200c5040f0303140e03130b100008245000d520543c0034107031508000c801040c11484800d80d9004c2c00499060b0f80e94128401807440e0172800c501c210b003010800c01c0004104865051000c0c5801900c1e46c0c01c0560070044901c46c02240c00c22401600f03992100d20381d0448208201940201c4144c2620368040c00103043c03880002d081d5004010300c40e8061440380001400b00110750b411070703a41c04021f9040b09440041410b0040c0f0302c10031801041c0f41c0e14059000b00701c8504004e03040040e640e1f8199030310900034481d4072841c1c000d405441400c1707030010f000c410003080c0c03080e450044213440440000016140e83c035242c040d80c82d00240b1075550711a5003000304520040340e004030480394095800c0211168801021034200c0c50b002e40f41000300c159100c146119030218a003074100c0ca1428000d800144040300760307030002c0002ca030428841c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 972805620 1250 972804370 972804373
    0x10611010203190e0f011b030b12070303030c0504030b040506060a0e060a03200d0615060f32130806010b040f09051314060402090c070206070f150207110901120302 72
    0x203d81a07108066003003086058044c82c180e800341307260030090a0070b45900b04250074410742665200703620719a051084141210003142c9034481200c4168000361541640c0c00b000d42015119000071882a004008440056a1101441c0c1580c5041d05055071215400d131841c601c501414040000d030020111052030290304011f101c11051480c0d40d450070700f040f18008103c0038045000d51401456601d401402c200c2074003920020824091640b101e50142110f508040c091001ea0064240030a6000d000c401140b040054001900c1c0c100300f13008002003146084c0070307800180000d80e40310700c004070058540854068004480140e43c0750300b040c10003400b80380900c2242041022042111109a401c29500400c000b1290348018102e03403542d50055a80b8410620710b036000d4400d000171414446407196003e80f0400d00c03942048a80d038000750140c0306960014003040880d1125030284040620407841400c1c0c04102150b903a980da1515144035522194910f1007011624000101c0180302e144200744da561690 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 972806870 1250 972805620 972805651
    0x6020c061302100c020a090f020919030807080f1c1a24031519080601060c030e1212161106070b0412051e07120c110f011115010611010203 61
    0x1c101d404c250302203002d80e070000450300c00140d01c0c0c4003880344800c0c0d00074242015030760381150002c0c032400701195030300d14940c95040350040020940600555007065485008155135100902d070341c00036030007129840040c481e48640919005841a03202210904401c81d1400070480e078070080180312241061030541c1d440b510050074156003c4100110743c004031440d08920b400c605d410215800c13a10301c154001141005190a0003000c20400c0298010303c01441c1010110714a0f950042281d1900040e217405a40214481c041c0c116040c0040845403024407501502e078001d00b00c074000321400c01d400030b85d8080e80000c0060034038104031040706d10003034201200303810544403550354010005100da1b696007000018052064243c4980c0e1030945041d0090428944071605803c0450701c60044680102c240010b034a14400003074800150200700e4401211510b05840c4440010f90310803480c000d41c0c1c5428010010580b0b0f000c514660054140d81c82c41c0c0d10008029021032070a400c07480305907841e1003100c2100 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 972808120 1250 972806870 972806899
    0x191d06011d04020d09080405120d0509220f0b0f0406030f0b06030a0c06020102040f0618090509010f1119080403020316020f09040501051902040506030115090305070306020c061302 79
    0x307550304804204058401460101d0720811101105d00c13003d012a0078002c00101004580347c04104289a10900c02c0030b4005113080d120060030038499a44030700d00811719888014010348038181402015a0520000e01c004112481c7d0607008001003001c0b1403056010410000d4517061038444c640c180e1b50700c050320084261464a030090149c80003421550325104000c48030000407207015584001b00529000581c442e800e01006103185201030b00080c081214402c1d0350f81c2d5510f40c3c000c00358200c03000100001015254840028058070f025040c084155041c0300b4015820104000104030384010100c04042c1403042c0c10701201d00c108140c5000d4016403082c00002e080e222400c0c040708001d0310080a408124000001082192400301c6080d80e9607503441c400c119140000701d003207a80400f81b84100b10710301802d0100040d22400b06004400000e44072980c0804003038000d4100201660700441201e4240d607a0b458a140694042a00c00e9840d004800109880408100048100c80c0e402000b042001205 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 972809370 1250 972808120 972808157
    0x50301030b130503071514040b190605040207081306030228090e0411090601020c01052d07082212030c02210a0506010e090607050d0b191d0601 63
    0x2d0254154001c16090380350002d4010401050400e20070f2500341085010f1201d0030301181c1c1d0070822108203010381020440010324003080d01c1d0344020420006800b058820f07225a004003400d07000b580e0040e100003440340c28840404d015121010424a084240d50b403604e4084044c0e01403e02d002150704466505130b202c0000003205003006003203601d0060708180e510312200140c0c0d001070305c00791406200b0104001d51070601703000c156480314088c0010800d42c0c0540c00002c000e0700c1080c402a4149404180014181040f0b14151040074030f44800c0c6520f80c40103090540c1d241e40b0a01d039040d1208551171b505808800d03044c01150442c2d01c3e82c1d240c521f900000d03450641b0802034022080f64000644104042100103004c0c01040ea01c42c110f00402e200c000030715120b8074011060f0002c1742282000002c10035524400104980d220f04c46203011522441481c03034050140403c00d444582c09040821007801d02421070341e0007822140d1140c803006a5142d41c004200c1c2d001e07020f07160103002401103e903010500c0380707 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 972810620 1250 972809370 972809393
    0x50f0a02030708070b06030136110d030206100e0c09091915050f01020a230a0606030302210c120f0d050406060303031d0c10030e010513061b05030103 66
    0x605005491510707103155075080e480da2049404490200011080c085030703090910684180000340071101c02e04007801d840071084800302101c903040d44240b40c40118204032119648110006000e4800010361a007440c1c0a5110002222a00c0300085030711000548603465400040c061355031180010700d005a103206000c5140c1005100a10750019170400d0031740c0407420700c00d4011618a03445514609030400d820050000c04105d0000c0c1194031014400c03001c1580c03403e40204452003440c2002e41001c0300480709041c4031003441c0c05807020303181000000500d50081142c241e0500042040071840e2043d1502600328001d0ba043c400ea02e2b8041d15507209e4844044004007201c490300e0303600c2e500782400c08440c0d0054610454086504e181c071044100704242c0c0500030192038000e020340520b52403c100c40d00c19a281c0102c0181440790900100c102c1d02036000780c3c0070b1805500700500a005502d80103245004a8000440880c2d0031362510a0300403614002a51031020f40c02a81e8455256928640f10201c404a = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 972811870 1250 972810620 972810637
    0xe060d0209030f0c0901080c090a090201020705060a050a08060d150b0a151211040b07030e2106160f4407090801060302060301031b09051305100c050f 66
    0x550030000c100d80341c2c0d41044041007803006007004003840381c2c20100380092444180d21901c01540300c2200c5520542c0e0700c2003590344c00016903000064409550004034600141c950160360010000284080001ea1001c01080e010081c1d803250209501c03020140100340c6008000a801c040c81e803000b420b0052140d42144800c2745004041e0000d035502c03401d41505880321362200f00c010444902002140310f10320300039824042c3c07048800b641810b00e042c902118178030440d4401020440a0030040025a442d03d4000e1420101c504201c4600040e0b001400d942e000300b03854200f03103015004207034103220f8070402c80302c0070f07051040d6550041c1032000c40411030b41a003564070f20381c00d019280685481d00c3d11190100801d0340311140f4003440c0d5041c0321401402c8607206810100385030741400403c1c03025894200c1141d04607a4055001030150031040800781c1a82c42d141c202600003404c080500c040320b03804c0c44a14006902075070039a800000c46a0380c0c9400c840c140100c4e640880d5082c8050300010000402420000703 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 972813120 1250 972811870 972811897
    0x10501080c0702042408010c020c0607051c2106411809070e25120b0901090c030e1606050306060f0d06031406040f06020315030106090504060e07060e06 67
    0x30284104240c80e01098006c469540c1d503440301ca40f009a0f04015542c09a001503680d03030314150b419110a611044e0f051080030318903442075800f001a1388505030b0060219210040c460800c1e00d03004500000d0469171044281072444544040710041d20704130204140c2c0440045c01e41307403119840c0040c41418514072500e0f404a900305401c000c0302420303c04d452207000903074080c04d102400d040d03500c5010800038200744108242064146895124000300251844450415034440944400c41201514040d003405801c400f44500024002c1e503540c00459202405031020702074406000c00b8a5a50303058802195801c80000f00b00308000e174064801543c1050002c0d100034038041c490703aa20300c071b640e008040d242c14940c0d0780c410400038006006c01307280100c2c2603c8041c0642e414030780c031015003000c08140050f0500342d001000c240c4d01e1001e10004101c00102030002d0000903920100100104822141501d005083c882945085e0502080744000d4072215196103508a843c5030a01200750007204110000 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 972814370 1250 972813120 972813161
    0xf060c030d0e1c050d02030c0415080f0c07023607021b010c030509100306080a031d0a06090e04061d0303191b05211e010501080c070204 60
    0x6a0805000400d0400c801007004036901c050035801603d810520090b0586040700d0803224643c0030340c084100e40c0e20003038403c0096201c0d05c071411a60310a1103030758020b17618000d01c4c2000f640703c107800003036451003000740300510700c01c0f6a58922035001600c20104004d40c48403101c1005400d000c0d180e0f840c142907040c01c0851785811503d254614411080595060002d0b83c030824103121300c81e082c62000340e4840400c2c81e0a00790541c4980c0c02820501448181604c42d0b401c2c6812007201a00c40e51011004001d50b40850b9491000c03420094810300280f4040803007202c44007801c00d000c1c204840003100301c65241e980d10003001c0c9024196000900081c004403a030640311080d00c02e8100b0449000c0d0201341c0f4010166640c1d0600da0000300c0240c2c800e69400c54610705207a22a10b8400f8801001101e00c6028200a0707a100100840c01503106201000300031170b011042e0620000301d007403a0007000e03000d1a1400100443c0d803038500540f0b191a0440c0e070700105803400c00c03441d0010f00301500540780b84800c00d00320046 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 972815620 1250 972814370 972814387
    0x40e04081201030c0e2d06150406120605041104061b06090812070f1e050c0601091b02010b030c0d0218180c040e06040201081b07080a0e011803020f06 66
    0x50307040081e4826200c0c2200d07844144504400100c689401440e0990281164042c120b03101b84400e50f400060300900c00e035840010042d441d10101a0901d0001d000b100d65a00d8480c0000f41030207549415a001c0d00c2e26080012034642424460891600f1130788480c01d06251400004841030108546844a60074294506e1400078070030303009032800c0c030b445010b1054441d0120303a07800c58151001003607c01002480c0c0b01c00709040e030700400040a00e1000c103580d1000d0400c03170b11041d070b1140304002c0c20b01c00394070400c00001007141c046d42c03042a0b04480d2000b01d504480d07c0d441c0490985070801c1d0140c1d4980c00c42508141d05180103464014030920251109912032404c4949081d00607003100c0030140d071203203014141d1501e40240141da280d441e003160100280c0400c0f025a650742c1c04000c00081c18010b82c41c0104441107420340300607403104188543c43c2e5607003c60b442c0446190b08181da4000101e03048442c3d8822ba580154001450003103a603001034501031468080080c0301c4124030403035402400c01c005810 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 972816870 1250 972815620 972815647
    0x9280c091e020313030302160812040c0b13060f0909020c07030201030e011401091a0d080c060c0406080a0f060b04030b15010f02062e060c0b0a050c040e0408 69
    0x20024410034400040000c03000540305100c41208941c104007a20400402c5400c20031502448013194052800503200e079043c0703030001410031206801a02184001c40d8441070b000001134800e01c540e10650090350030907520421180c00303002da901c4414014505000501001780300d0082e113a02900c203840c01c4000c003541d802c4444100d92103030312000c041784c00c080000d006650f00345c0943c804201d8580000c0280601000900f102e0710b106005060049855090404208030001101d0505038802011502050b0b03151400d5074030341d844000000d80c1801100c0000702055600300c140c40c100e40b016141d0500c0ca07034448034810700525960808a0300540c0d204004502e0600450180c03000e50310455505116052943c86580d00d1002d0741e401c1c0d410030041841c0c0400042d070128116402a840719680c3c4c1e241009608261041c07455004e0f8011600441800021019401000c90500501494000482e0303115041c0709800d50340102c803400000e0200f00410441c20300c81200e50790348203028220650404502e4490b00 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 972818120 1250 972816870 972816893
    0x5150937060806030c100c0303021b030a05070512042103090305060108100608012003040c090c03020307170907050d150c02160905060f06030a0b1807020111030928 72
    0x701c0010009020040c05040805c176a030411541100c4245495400220050418a540000404250300411445140030300460000d102000704400d8076200c1400751802405500080403d5495200e0440c4045102c0001d100312025294515118012a011003808210000e042d45085042110090340000807801c01d000c000d02034881b40f0060902803902c59100d00640b869904440580d9140814140103004603c40c040c290011000006881e5a15400e1a58a841e4181e0100e03205034144000c2070982541580218400c01c0c007912a901072071154822041880b07400c9903044134030703481a2424442c40c5000e41e540e07140385100c1c005043caa4100344000005842949201401503440403002005003190001c4250240c00300210400107841d001000a82d020380c40800d441c000c5e41c0000c00315403480410340003091b4902016001131082c031100d501295010720100c4d071403001946824800700a41c00101b08032800b07985110024405102000e5142a0100403034800c4208450040c0c1311a00003610090907 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 972819370 1250 972818120 972818129
    0x20103091e0309050a05030102042412150501110a05060703051302033018060a03020c0d09260307060525030606030b01090b12090316050705150937 65
    0x81810f010303d40f8003480001245070300030714420390041c072040c0710ba07000804204000c5124201a0307060052540019644100d1030712210302c1250034030520407120303001c0b00442012144281e0b2441c841c0c500800c003068480e441c0a000410729086000420120f40c482d800081c0c120380c40c81034450a007034907680024605203080c1e1420100d5140564009282c100c002c0828414240c0b10003414a02403601a4420708155510301c0d55119403c080380350700c80d45209906803540f00c3c41303050480c6c010821680000e03011314030a200d00b82e05045a11401e21034044c407012965420724601004600f0948603554200c0981b0b0020440d208407081c68201992080070700c480c4850220061700d0008400d401c1010007402d441e4010403050600c6a920000c1002498003000c07203030b12405145e681011921a6040c5130b04500c211812260007800b074180190500801096107400c44000304c441180543c0079001c50074903401107e0030f03142d0104203200080d158080b6072003ca21110501001d2105042401040380038145d0507400 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 972820620 1250 972819370 972819377
    0x1707120201020d23070b060301140105031905010f020f190f02031e0f03010608070809010908030a0e2505040f1515030209040c030c02150f011509080a1b060516020103091e03 76
    0x1808850b007004cac401c0c00c0300240c0e80e9038000d02540c10200404c0c0d0710329041d01003c0203071070b580c56982d003445400e42c00080b05500184007590f03112440c0351000c1243e04102c0096843c0f40000c0f0602200c9401022400e02c80b414940207107080501e0401503042403410000501c000c15020400c0740700588110004601070a410340f03a110580c00e206030001d001e0300d0000e1411031a60314000400010901c0349081e01d9000140d9280401c0701010068054140102c03c10000b081c0141ca0306424001501c2e107010a00b0b440c8180c07010006000110502c4050302c1c0c07002e551aa002d41c0c40340342030069482c1c6503400c1d40c4c1d80026080240c90300d840c081c0820100c03517044016000183c0d580b14100030040e07040c4003003040310b015140b401c91182403806008e0b101481c184103040c0c1ca0110740700608030380c81c000d820030401400c141d001d8920400f080c4c1042c600a0180203078206122000c4d13480441d41074015010b0b228907050807101e908942101d540158001c0406410030b48120b10701c0380d0ac02c440151400b42a1002a120740c1c0e = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 972821870 1250 972820620 972820643
    0x150e040f02070609031b050c06030603011b081e01150309020d12030203010f0501030903020d05310f150915030f020c0c03010539090603011707120201020d2307 70
    0x14020000c8000440c00f824850390903606c03070041840000c0c603108100701140c41564948502d000240180301c1d810024510194000c41c604003142c01146081c492900b806005002854600c02300941410900440080f110000103048811784650b10042d41d081c400780c0400441802500d03800445c1e48030b030340820000f9400200602c640311815009200501c420b0800b40584912960060745482d0003980040070040c011514900400e00d81d000a444c2c0b0070882e00c444400200d41c106402c00810350301071820f5403101c0b80c1d00001c1521182e060215a03c20540d5204001e5080200c100b100030701000d4400209501c43d079007450b015072544001c11841000d42c00804c10380c00050181820740d17200400d0307035a010300d50941c2552428190f042824040b840c0c55080840c0b103090401480e1b00e802008000c1d07410100c0072002140801a94403603c180a03200710031a054181d40d5041c074407503d521814000d0050704048001d004280c010f124500c91202400384900a641c0c0342d4031101041c1e00b01d007100780c44041020 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 972823120 1250 972821870 972821873
    0x52a09031903050f030a1b030b060a08150a030303050402040e0a170f0d180606060207051e040f050903042108222309010b07080931060519150e040f02070609 69
    0xc0401041f04002e040074086103c010000a81c41d014105a46044c03081090002e0050a80741e040035611140c010304d1307400030ba616420000c00401007110b040f0301880c0f0700f11258242640c00540f00403601c0d4400a0021610302c54050000d4035040b251030b480403450103010303514a00c10980540c80354450442941d4403000c1c007a007451015242c10b64840010f5420828041c000b540729603000031042130201c1c011a031110902c1c40072500902d0300c0c94030445c20030b107004180160b4103004001082100d04c4950134903a002c0c4600104020048110b070002c254103020042210b10005000d84160316030034542030894020740c0c489079040510b80d00402e03040c0700d40303030007210703030054074000c210703035008d0144001550306204080e5a290024410007540c20702c2045040406080f880494424980528110000c414000030904c41030010f07040ea030040c144506008020031100b260251179005c1201c08204194030b0441d2038400640b1590360007148d19030802d85031030091404440c5030000f0314180e48103900014030113985 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 972824370 1250 972823120 972823151
    0x304080f19110d031509020a1101050c1c0c05030402040b010c0b04320d030b03030403060e0d03060617183a1e1202090301052a09031903050f030a 64
    0x4035681c0e003043c0343c580101714401e03030074810214060310144540141d540701881803d0f1a1123141c04220b1a0560901040000f0480c440c4040c0c5040f83c0740c642c001c186c06200700801d4040d90808401280002c0c802c0c00003c0240c6065005007400b41018100403d580c0a90b848410990000310b4068a441203a100c62075401c4800400807013070240040441001031b50a081c140e0f03190100388039901304250300c0305483d80081c3d82c2402228001c41e400b60b001c021048400c0207c81d118140071244001103490800c001803001d0094600b514103138142e041c0850b942d03641404000001010320145c0c5114819440903c004d04040c401681d400280c02e640352101114450140141009000d0030000700301140184010749000814448032010b03542c00d02c1c07002400c40720352a5009010b4440c0065043d0708044c2401100c0f080308043d85a9210360682003490703640888855070342885000803050301513020130039240703000315030b40300c24006188640f601c240b500300101416009a0410b41d82c2c01d030401d541300c0c0c142c542c0303042 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 972825620 1250 972824370 972824383
    0x50c01120b0303070623040c030303060b0405060d0f0204080a050303150f0a03060e01200903060709050f120a0c0e1608010f0608070c050613060b090105060304080f1911 74
    0x45031030180320400d44500820344901503c000140789a07100e8003074014961071040f842c03d0f0040b49403130000c2c680c981403c00c0e20a2031030b43d2005501180c82d045000c11814441c0003110103461026294034646642400e04500600640d418410220350174400418642c40c01e009501140b4090b00c0195100d0070102c85422280c0105103d040c03041010502100b103644071901214102c0c1d4205500003030320010072200a003d812003024808007446648040b04114844c040038004609069089440c29580c1c400b0980d080840d81c01001d9219414800d001d07181e00d0302c515405c40d00d0132034406480c55900140d4686081004076000400040103400410140c00040210000c01b400035140026086d450320011000d104050f0182d1010007002c40300052004d4000d480a03455507074004200c60541c81c04100e00342031f09400b50800c89046081c0310b030821551400940c0301d070503503000809591458482e03607280b40c01d5074000810003c9011061204001d900042034a140c2015011780f55541d81c42d4074060500d08000 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 972826870 1250 972825620 972825647
    0x501050604081c03060305030427091509030e06210f36070303050309010605010e030c01031805030c0109060f0516081308040f08121c1a0d050c01 64
    0xa120400c45018002840f61100341c01d00902205481600c5046024091980000d4024480003400059840900c034556400e06500e41100740b030f100301401100165401e856024103911254054107d100d910b940c01032011901c01e05205249807861004200b5940040903460304a045880780e8000501c40802819402100070390713001100d281c03d400300d4107101568444103000f030841c03004405003c204065824418860241150340c034543c1ca107801404d41d441240c8804c0c00f5403c0038030009407540203201e13103c0780d058010054a01030180000440080501d022001403c40080040e0804030340b082c0001e10840490000208241129041003401da0310800200400c50b45803c080240c00014100444150b01307030b41c81c091950380c40300c00d2032440b25542d24001410340c0c00c00042c00035000110304000c20855115405981c9040709101c1c191520b030283d4645001c1c1000c0c9a1400c42c045000f55000c54400c00d032044000e6613030f0010304d0101c0c04451160404555603031040c2d040c1c00b555a00320340c1034042d07407 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 972828120 1250 972826870 972826879
    0x20c1011060103051510060c0f0c031a041707150c0302090d0f0605060a0506070f060b0a1e080708030d02070f06050112060605060f0a1b0204090f030801060e090103080a030603080d0f050105 83
    0x7989407d00c02480c601078604003034907680e601a00c000421802462003c02143c0000318040150b03101c0110741c590075000c0d1800ca682c8060f0301c41403641805114203540708241c101c0d2030b40c1d103100d04200300a8082e000300c1c5100d0041550030011003140340d40b590040700810703015a1440d002d0655030719103441190000360040f8030400d0711800c10002680c8040864080d00e0f444041400341064900c0c004010307040d51381e040c0d544034101d0310000c11840041e02c56440300007209510303c00301daa5982183c07512a09503008000e000c0e0400c0280b4031039840681c0003080101e01c144a190300400e00c03030702c0301421501c003038002810104ca0504680203114041c00f13170030094032044501615058141c40c0d6200135108031a14a418010340000d6401c1c0c007030030700b0070807a10b20350043d10500000c0090b02c2c000f0340c11034040038103c0120b6020000410500d01c1151b0701e9180b12009006041c00364255100d1750700d030340c00080d82e4808161700c480f0080001054600039203d007031510203020821980241d8580103644d8141c0005024 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 972829370 1250 972828120 972828151
    0x603051005011b0b0903070209130b180309060706060510031505130207060501240e010c2a0e090724031d0d0f110105040201020c10110601030515 64
    0x102004041044210307942420411040703a070300c0b100503080e00f00c02040a003480e0500400c000003400e000c0700500752544220b9020703055503950362402d0040c20396580003030400023145000401740c02e480caa01d941400000c80442c1e003821801000500554890348080f82d4041c0c4800081090f13003003001121300703440200d003402d00050001c50040014603102d481003511681d0400c0c1c0d500078440650b0304503405150400001e000c41e6840d141002c03078088000c0c1181040c2100b00c0d0002180743c1c0b0410111210140503510001d0390240d07a182d01c0016030408107440c040c0004e400c0c81140c0e0000d88481c000c002d20b880301031300b00c040ca03104135028140000c41c0c0c001d0340c1000380e400e50102a00f2806500004480300d42c200000c080241e803120b0b0b100c0d01031881550302c070b91241e2892084415006224841d15030706980d1018030715403115001d83d09981d02510000e016030b200900c00c0000740f825a03621521624280341440084090402d00c03481d0103000e900645441d0801c980500f444c06030b69080b20390015541c4294410b = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 972830620 1250 972829370 972829381
    0xf0f0d06050906131e15050a0515180424030203120a0e100e090106080103110a061d120d111e0d030903020c10030e0f0c1e030705101701060305 63
    0x1014912076400003050356101c0900d848444160841c56940404940410400c6207000e030b0300c804c2d0586c501030244942d41d0303440c000a00380740c81541680c614082a11160400e901d500030443c1d03000350700254a80c02600c649442c0c0650481000c445001c412910000e00010305d5401403508104050f4410401d43c1c2d4100070010500744c0040e90112400821f503035080500e21400c10031101c610359940c405600241c2c18000044480d400003c00b8140c3e402651500d64000459041151704096486070001007000715104003508040105503081540010b045901c880c1000c020850805508a22103c00705421048031051507030108242c50649074050343c901c160054490f030650f074500c601c8081d04101603c0d1001101014400d21428101c02d4000e803041088400150700030f4064005a000144a0312480be03003000d0b100000110180340301c00c050085c02515044140c08801103a0310440d40c0d0b051b01c10007800041a80f6102004075002135181d0303e40454000118540d04801010b0744600e0405003403000340071 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 972831870 1250 972830620 972830629
    0x1902010b0a050906030f06010305030307110a020a0b030a0e06131403090108060d050304150504090b01140901030914030c340b071113020c010f020f0409110f0f0d06050906 75
    0x1034402c1200c8010b0a641c6240009250101c41d00c0c0080c0103024440000041080002c0614000c40c602d884d9051030140f0f841c07041d5540d03510090083d521042500f401c11114620000842d00890000d00110303410710b4003400c40b468540300340c403911150314002c8484018000b0f02c0e5100c182c5011408040d61130400004002801220b000d00342030301c906401d00c5607104000081080f41c005200805070300d0611100000c026003190050b1081d801d98a0900126440540c0b02e40c0141e900040701c2c040769414400d0b00801140100300542d01200e070300c207042020307a182410800203400c680c86150003c14014407281c88404001c3c107040b43c444691201e130300c482d108000c000800350b81660505643c094a89003c1c0c14201c88080107121596000a4107800c2c0006d902d00c00d800514084464500034070124840587c0c0c41c00301d1081c031400c00e0f02d0701428071080c494240f00790488007410038014205814031050181d4110141d011119070b4581140c0001e0701660300c2c429018081c0100000c442502151a0650104 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 972833120 1250 972831870 972831889
    0x80603012004300b06010806090727031703010614070302030708030c0724110a090317040b16050601050906090a0c0912080c0601090b0109060f120905031902010b 71
    0x26400351210003802403034030f599a401c00710115498110218010b00e0300b00241c003010140c0d03600c1e00048140380024003070700b0000c542d5406442c2e2175603140c03010a2840400000c488202d80d1300c044448080d04004045004441c04c40601e03080e1030b8100e9a43d51401c200503180c40148040c83c0c420400900400021a40120030b55004580210746643d580d070301c0c200031011511030f45d800105040010114007501450144051004980220702004268412480e800e02802003a86000018003c01400d00020703007040d00c155000c0e044050718908054854802d0100c0d900405440c81c0c02c21841c009100c00d000080000600400701901e10801c00c0c1440000f1521160000301141c5c9100c2d01c1d190b85641c0039108851190041c54011819074503803185140608040d400496131980300e216030780c004608041c00784615000c0f1041612503a0a05142a80588140601c0440c110070310480c0342c03160002000700d020b5050300510420280d50ba40260803141944030111480400c00c42e89040c480c1102c58507505001d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 972834370 1250 972833120 972833129
    0xa0908010e280213020f030a050702010605100e04090b07111005010f060503180618070503060c070314120109020403020118060504090902120109050604031403070f030b01021c080603012004 83
    0x20b1200945a0300114002c610054014607089100044054503030034050b01135030040c0c4500c801400395817110344040b8286e801c1401625400074507210b030002c000d4000c19882001510190021802000f2070700e40c0540110112051000310303076903245c120038204040c003103c1d1803d03507240020401941881c0300300002d2401800346400780080000861664980840c3e40c168030001e1000712006850003100d075410891480607180040c2c0715002003c2143d150218a1030312696845820301d040507150b840445e5200b0025410302d9004204201085907a002500181e0203000040c2025035101e01c1c601c001030210062149202155503100c0052020903400f0044600311210f80502280c1500e072400051600e021202c1c0228407580b80074000000c00c03c010074014403c41c000c1c1c03a81d207203803030300c0403c80d421702d110498107500002d12641404001c60702903071010600d10340610440e2a1035070071030505003070080c01d02440c02c00b242d112002c0100d2442e00b40504007800362a020003514441ea0080c50140c1401140603 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 972835620 1250 972834370 972834433
    0x121805040209061b0c0109090203041205070c0f15090e0f011a161b050306070203090405040309121a0109020f09060304030c0215070b0711030901140d020a0908010e 72
    0x40e00c6207641d8819055551501302c05034140d00140a061140f50f80750300d04c84420307002c9003c0450010f0f0000300c81c0b00b56031149800c2a412162a100b002c421151a8803410301140e10b103c940f2000308012002510103009000d40319011100c0c00b40d800300280521070243d21000311400010100241031000c0084641102d80e48440100041d00003010708050340500d1013080e1180c482c4244000611611590410740d00441940000d81c10351600185034481000321008000342c1d1003002282a9030400d0b03400b1a40c814000e1a080070459101c6516110b910855102501c1e0300017651000c0130080e004110090040c003943c402145440c02500c0b03e00b0303040c041d4491a03849a50080b00042c01d040c014000f40410301c0e0300a229004007102c2c41d6840c0c0e0550041c1c17105903403541c01100050480c034080d5613103403100e5801000550810003010700448092960451003907070400c05121000d281400c41c00900104101d680302c20704074905080b40e650840740c0151290200381e000314004490441e0f2030130000503a40c030454 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 972836870 1250 972835620 972835627
    0x1e1406040317070311100e191e022404050a0815041103030d0f3914090d030909050609070c0219051e030616050a0f0318080a020d0e030304151209050a1218050402 71
    0x151411103034054004201d450180c6102c0e2f0800d991005001350703403044a440c41c94584840c80300d95148890303440000799410f660003180100302c0d00c403982803610000404880ca81540c2e400204d042c3c501c1500154061600c60030045840341019900c40070840c106507441c1030520616844032012140034000d901440101310526489d100c00c2c10480d000840c000c0c0c0300c100c4d0715085180081c403240b030342d21614555526100100d1040c0ca0182a050f02540701c0f1b59450387d5442c959000c000396040715951961007040d2a0303e00180c95100c190311f810004050440001001a014007854108070005014840d00e2003415080090690000103840d50071099143ca0320003030103985020340050120500a0350b00c034110030110820030107000014241c04a0700d0b801c1d90b010544143c8250788800c020001c0c9a4550000d2006104048103c00307004c4141c000e0345464000d03a02c00005180450321202c605903560303041242c00700c091104803040103001c44d0b40d80c5803002c002c50010381180b0302c60318680115845071b034001 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 972838120 1250 972836870 972836873
    0x9150501172a0a080d0809060f01052b020301090813080a05060a0e070806090d091514030601140c010b01031d06040f0c1e1406040317070311100e191e 66
    0x384200300580030240407500c0b840f28249020340020001c40d03030482ca5104800c00030f2010014014200e04a074800340444500d8030240100d0040200807244104030383c4cc102c220000507075002d008940d0010700a0703446903914024a22020aa008560040e134030036840003403402d001460001c0d1166100b0000200081c405440c1c0644a00b0841c142c0c4c0b00c0d00e00792151500b800300380c43e004221160940010740341c1000441c2d0f00c02c0c001d0340f8800c0402d10744000c03039601030a100350811101e000303551041d01427500100c2c0840415020900e134011140142c6c103a903686000d1041940c242c807440c0e001100b8070200d40c00c2c000c40c1120301603540c81e005000030300110049155a0801c80400e81640c090400c1d0701c584d214134414843e440c0e80c0b9034950720550b4801d0050480700441410118103c84c1502d4102c21501424102c40f46003480a03401804200d08104030f180c90440801000e000c1641c2042c80c109001c42c181d0074441c51706240c0700104c140d561181d850505c10340001005240c0341080d182205454289003c0349 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 972839370 1250 972838120 972838129
    0x6050315130206030a0b03060f040213091e06021207170408070302191103280b1f0609060e0414072f0a0507090c021f09150501172a 58
    0x1100c5000f90003403004028001103014681046020344016412030b142942c490700d010402e0803090f81c011b50803c086d13407100c1c4100200d9801c00134405014840050a1105610701140c02118003203007516080c0c2e0104484036401e000c030124680008142c9450350398159a842041e0300840007400042c072038103001564108150090060319034000c107011a22139168400c0c00c100c40307881400c1002e10b01c207000d044035800062060000703c20303500300c2d00117400c03841c000d180c3c2d955002d0490281007001000d2000c010184128224208072000e0507460352840c0e14540ba03c1340203803d01d8960f08009108600341185032442402e465401d5900c06c0d2980351281000050303040f1a0410405108001200004a0410300b6815070014902e03590034482c1c400c6070951551042da1000b00e5240000304030051708107000d562040004680344491079000100006098a5203a98100400407840041c000441e1210010406039114113030019100b550000a0111000f4460050340314420752424005007000c0ea00000159844 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 972840620 1250 972839370 972839401
    0x21905030d180801050a050405060f250201110406020717012003061c06020a020f03031026071d070c12082205010f0b0a0e1b2101080f0106050315 64
    0x2440c0f4020400c07420140041c101900080381d00307503044c1c407810001c140b40148858100b80308840c800444280403011101c20303204645045c0d84401159242d403140340c2d07202e001034001c00007030500ea00144013840c070707000303c44290701040c0e000941542d26001d01c0184807480003ca890a5400d5034800958030342e941000905141c40318408650140f10030501d40d42088000e03801008012055000c07102c108000300c004c1540c0e88403c5800c100c00340d801e004108800c9061030052010702504164088040c480c01242c0b51400301c460f8060906e81d0001226291254600003040e5045211450700100f80a00b40e220422100811000343e41002008000100c003ca108001540c180b11910601210001542030080c0600094207102c5221382c43d10b0703c0106280f0742030002c034040318696440f0025a9407003900b0100c5603012000010041030b010404191691100820342642c0100c01085003041e5041c82d80700e5160118008814146030f14085043c0000d07074000400e0080000016503040960751051281ca12400 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 972841726 1106 972840620 972840629
    0x1c1a0f0a1401030b0303030703050a0c0809060711190f0c05090f010911070f0311070614120901020403080a02100e031303060207020d020307060903021905030d18 71
    0x41d800705000700390a005040001d200c100c1840404c0c1964022a444000265a8410010042c0092003849500c648920300032510340f0703000101c96641c03031015041d10240100300c0d00c40714001e4000c0000541100c140d070700110030407030300d0300c0c01400b8a0070404c01150040078141000c201428240134091042d0700e5120034040d26440c10110ba80100600340381c0e03420880e0f04005260105e0880c1005021452090b640e443c0052031082145060420680110003002413002c41b04c08028071031415140403072006d209561468903503004442c02489590320013070444601151021450f80c01251000c02000000014408070052150840d280e1080340b00b41c0300c0075003109100f071020407096400381501c11720184c010340c8610301503000a842d24455a120744001980c80384140b0840c01c001051120b4049641c110f522040e0620000944902d00c0c00b8440c810400203141038020044400001401407 = true := by decide +kernel

theorem cover : BRFrame.Cov 972661870 972841726 := by
  have h0 := BRFrame.cov_init 972661870
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972661870 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 972661870 ≤ n) (h2 : n < 972841726) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
