-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2179
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:53:56.365431+00:00
-- url     : https://prove2.me/submissions/a8597f3d-c166-4e52-98d6-211036bdea6e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 391726618 ≤ n < 391906474 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 391727868 1250 391726618 391726627
    0x607021002121621020c060d0b19030b06030105040b0114060702090c0918010f0312020a05070324020405030604060b210105071e120506030709021801090e15150d050a0f0c05 76
    0x1001703034944195110b120b21982e008659010020040c0c5c100d4054900c2c0100807425140900101c0da001d01075600051f00d4040340e190000716130741014405c003802103030000701291a9a19218128215a43c600e05a640100701802a840141c0b1011603050141c180083c941f0744441da020300341300003405440091021844100b0040084140200000003581e4100100003d6412544c0d010307450044910002042440385481c00018050806410200703212168142c80c80309940c0d103240c0c402d07806031340240c80c1d04da0440c90101d40010205e5116540c100700207805105140040b9042e840760403000c220104c25a5100c104110681e98040d68601c422191025100507402c00c0c0000180b100c00162480312500f69130340c1c0800d10680d02044500000c2c501c4541c10b41d40c4241d010084c1402c0441103280501003001040c010036400b22000d01d16100d80c000d011070b007170300c49501000c2015083c144002820f500c00104103940030f6030480d0259502c20010705a0100f09440406454400c0341c01351602030040100900 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 391729118 1250 391727868 391727933
    0x7050601121a0f221505060f0406140d02150301081020120414010c0c060c020102090105030c07030c170903070807151103040801060611010b01030b06070210021216 72
    0xc0d8182c200b0544000c2c100f007065075544822000401c80400b034424803501145c9443c181071074000758402c8030f0656506d00100d40100501080e24410302815000700380c01804008282032540d0400802070004004110007490743e022203206e41d0080e00500255003050610b10fa404050740a100310740d40d455809008060086244242c15005440b48884a40300d51004141841002003140d8141881070f00200a600710407640500124526201150030500380754003002c50358018404c0d1404001c068540b0b03440d50380d82001c903840750f0340483c001b201400400301d402c60200f4151405502511580c030b5415a0341c4414900701880c01985a12040466008400500407190700300c88ea074580420030f0401c51894820425400d0960003a904902915881c0500c00980340e80c1c0020100340c2c00102c40c0003045411002001141030751400c46401d43c118004008000041c1130907030602003600310500c1561001003902180c0c0120382d004004130002c00c00d02003003100c14041c4050241a0450142d5030140700e410b00d08 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 391730368 1250 391729118 391729141
    0x9010f0303080c0424110d0203040303021c0c120c0b010b07060e07061e020c1c17073c080c0c0402090310050603070b04061709030703020a020402090607050601121a 72
    0x101000d40c03051441d1054103000c60140c00c1d51b1007400485800d80d4044507422000030758940242c402600144112041c00c0440415078072031302e0b450a8a540c910000c000207449104000141b80300207020802074103015408904003a4400e4040e000d00c40402740d4640340d070309000d819214000f02002ca55040b5000c03c00c10103800142000c0c1c4034017115031489c41c40c0c142c0308080c2e05100c1319442517504441c0001d090402c1498001d42c200a40f13200d604808083c1e4007800b41400f1034052103000500c020740402d0403d000c84002d12001c009201c4204040d80707000c4007040e050010540b5428102d46041c40440d441050b250284900b101405042ea03046007840389203000a0f540b144070f4020301c020f969441c0045205520103000d1940540307086000540d84603503604c401403422011350b000701421000b40c0d000c502912004001c460003030b0381640c0148124902e607000c020003076000303520b020340c005401c002c81c0000030130a0002c0c40c0240381e1452491030045044c20a03008804460141c1e120007049502003091481c0030 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 391731618 1250 391730368 391730399
    0x30303090c120102090405010b0d0e0604030e0409241401080a0c0e0c0702061b0d0c0206030708070e0a17010b06030c0406050307050702130534030e070509010f0303080c04 75
    0x300c1e00410500d20400c00b141c020700c103035104d00340c0080c107210001c98a0705413000106503d480d00b6000700301d0341041c2d0200c6a100e0300282d030700500041031004884081d03d01900611107060040e0140e0b1882802e2414051001341034900215420b9250b260000c00711000c0703c0014010010305001d0910055103a845034400c03102c0c2e01400070b180700d02001003040c010809055550195000e0102a6515004d81d003c3e107180c4080c01023858207129451480180301e11920038071041a5010b0000350071911481420340d42084024000410401000440d40040c2c0d00c45040500a18001c601c40154556991501e429a40c510441c5401030b4010400d00c100c031080042142d084034441e00d410350304c80c0c6130848211140c4c0306000020750b1082a50800c28680e8456074010790080e00c989841042c02c6030b02031710000c5481c0c4607255507800c415030b545135030402e40d029070040d42e220004041607590140c1c1319000108003134005c3c0c004030716991a08030306008140e0049075403a0882b80c00009241018a850080c8030000d04 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 391732868 1250 391731618 391731643
    0x90102090114220b042111040c11030406030204090609060b04051302070602070b010509090f07060f0905040e03030906010f12110607020a03060b0f09150108040f06020a091403030309 80
    0x80005112118810031007542e4902c140710529103040030790304c4001252980150040030b171302d40212040e41c41c14845160706144001c2d403201c494038a2861a804110091032030600d0036060005245504140040a00040000d004944c0300161214103001588003280e0403a00221081e41c60719500740000b5090406a400b191811a280c40c5404120118a800383c0100203004164900210303142c000c200a049440303050b54016200038009650313800b802e540d5400103c02c02e2002e500142c00030b001e0381d4452030110070030101500b08624616500d8010804075840c0300c0c0600502d420200c280300c2c0320320341403001c2d0f4010300d081404024001c2c10229038402d0500c1100c0000c041300d041c07400500403a11400d00340c2d815070780c000781660040365403401c3c204064855107040c24410340c05400300d03801c0b900d0041c4001c1d000e120a0320907800100a40b00c015150004090700030340f152014082000002182400180b100580d19921071006030320340300b0080003450150100611035081801002200240007460000041c1e = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 391734118 1250 391732868 391732907
    0x51e090c0d05070b0708090f0f0109090b030106051905010e0d05120a030908070b01050301050a0917031b19120606020c09220305120606090d0803040206040e0108060603060901020901 80
    0x701407030510301c1c00043d64410201c04c01c0200d407400510403114081c04000703000f540e0280a4001c12401c1003140e00751a0051400704010400c02e00140e102030b44003141c0c003040540000381e01c41d2140001441403010031080d90140700c0240d414483c650f0300644007040307640e040c1c0303d2200d80034860b540c80d5110084c600da42c0304c4d18800400c007505607e109410503d409508201a2a034070029400c041061100034040c003400780d07007403070701054141d061480344007245504620079250607040150030301000e60014110354503d540e000d829400c000a500010300005d41e09c00c10500c000300c3e0201015202d0f60b010464948110304d050000c11085401040302c0412540449014405980750080c1086046c0743c08101c400808402d800c00c0304040c5c2140c01002da41c1c005d140018120740d903050805c0380c0c40c410011420342040840000c9000100ca000107036030420b2004107418182500e44a5041c440d00090f40500e0040e4824400d2200c181001d00890b40c0050780b0600075850140f001c0006841d151081d1005401030 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 391735368 1250 391734118 391734139
    0x60f1406150a0c0b01060206040b010611100504020d14030a030605100e010e150307031401050406060f0804060e060709090f06032105040806100302010215010f0909081606051e090c 79
    0x1c1e03c00c084002205510044940d003550b103c100095886004441c03c490f14140100003050311406103602480190310440140000350380982c0c1800500300c0504204e030010a940c40040c0022500c041003501c8401080085403a0500c0f86401400d803601c40d03200600640000c2d901e9030403690b200101041440c401c1c00c2030b0314081110000304581c1203004c0884444042c0100501121543c1a085030107520148811740303410740d8031038040100b250302d5032040101250351580b500000794010340d080c40d07000e0b018100c0050b102501c041c10904100f0704642c1440007820328141801804510308c03618100382c0318800100200c81c1142d982c650b4806011040502c036a043c004103030320700c510a00c22203000d041d842065690342d007030420040d00d04000601040740036000b080785921150145202241c100d0307501e8503500400d02e00c0c002001004015207001501c68040400400a9081140d110041e01c24401c0740c0c006014a00041a2905181030075802c00313480c1c0e000007d0068808000036542001c0000721640c2400 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 391736618 1250 391735368 391735387
    0x30408070209040501020d0c020f0303150102161409071d04050a0f2a14030708060a0510080106090b040f140d050a030c020310021c27060f140615 64
    0x124010040002d5004800508100030002d042d0090a9404420a000d0040d108400c00c1640c4418000101c0e584e99030042c0000b8540f21241406455102c2c41801511019080c901c2c0810a8102a81140104400140c80c109503030410010b41544862641f40001203c2c003181e254004104003100c82d148a03030b072184041980103000b5484240c40c1e400190080121021140c5100108c400030300200b804448500e0f0100d4a071406030064100f01000142c80c20320390f9880b4602074412410260041e504010961070200360740e207800c1d500b50448000e9403a02001d0b50314200340246110039a0304180c0c1d80c0641400104150101e2032110426613210800c0420b48c40c400d03902003070001d5011400a40780d0700c1002da0080605800c8925504658026801e54071812050b005c24010780c8500d65441000d450b01c0c2c400c05541342025405114a8042d40c040c943c0031090005c50420450a01c0300309540341940e4030100ca2803000f81d840f564201c0d4600244800161038100700003185007001000c1140b18240c0000c00714031 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 391737868 1250 391736618 391736633
    0x120506040b1e1003050f012106050103030e130b03030403020607060f0204030b07080601021908070204090506071110050c310308120a05161409030607020109120f0c080304 75
    0x15401000d0062004104a10300004080700b03460281d501401c0c0d03400c044040a4805e00440e44a11442d1802e0340c000e0b4079005801111070103c20b080941c2105081150001a0701da000b00d038001c50081d541c98100b407400800b00000304407510b1140e00500d103401003020702510040242c80071207404031580d40c0c95512604100b03000d800041c0440858900c005000720401c5007604246000d910031356102c6405039074401c0160380d0f5902d4692070b6180b40584090b5103000680300402484000c1c405040416820500c0c0d441618200d0150303501000706104051980b0b1003203080044c20f4480181690070300c080d007401c00c001e203031500c2600d0081071811a801404658106000c0c4c6c00803010340c0000070101e58070740d01d003403107003072504220321815105031b401000c500340c0d003041d004840c01a0740c01ca1610451090000003070300c6c44140304000c1d5411110a01122150f51b03824042d45110f1101c0f41c0001c228900300c3d15040c00d101240310015414481c81040e20f24070a6404405600110f0744902c40b140e4a480340c0c00c1c41c08 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 391739118 1250 391737868 391737881
    0x60a11070606060203040807060e090a020c03121017010603080313080c07030b01090b1e040b0f190911030c04090b011101020a03090b06030c0d061a060d1e0b0112050604 74
    0x810703032070a0200005260794004001c1080768000c400792190191107800480740c80402c07031905948024003401041c903d0700c036540100345640c1604200c07031a20b00c00d42c081c02c00d510030469540b40f00385500038041000c1d141410840c40b001c0d004500170014141140c0d40d00b407440c04080c20801d00100d124025004000030001216810001c1c1c0045a1b12940e40e850015040b0600b40140380f202801c1c190708c2c6450b400d01048440141017100c090f11040f08160040c8401000701c4510550b12000d080d00c001082e85681a210700d10106012090008a0900303480100303582202c03040c0c140c052000c00030800103111078401c1e00c082d40e20b801070102c4c002e110707880101c1d2844101019000345500c005120442590994080500c40c0e1103192442595a15442015211600f000403950845200703094800040c03e20381c00a0441401c44601048070a0200c002c103549410500106000941c0d0f041500c042c1c0b0f20400051440c0384e554036047c040481070a000078020100f6006245403252114040b45803580c803504001d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 391740368 1250 391739118 391739123
    0xc03030a091109150301290114040510030905010e070518090102040e070f0e0405161103041502150a18150b030d050a1412040b07110a0807030206090f060a1107 70
    0x105150038a40b01c2c3d0044d9418280c80305110390f00c1c000500c03e0785000c00ea20480030704031981d2000d89400040c401528105482d50720303008540b20410001c501580c1d01e40148200818954001455102504c0e140d400c441d424181c0d2090381d4084007007086140d07103120184107503050985004016448006007a806030240781c00c004000c03087c2c48104489554450f100045004c41996010404110740040c0021540d003900c030f040f415680c0c032110182c203a003e10441c400c0d5040c000d007180d10307107692001d50491502c0d41100701001a00545480c1a10309050f01902c2c2c0c04c603070407180404c001040c03100505400980042d0091180c014801e198000484c541d20240d0010307400303001e80d21801e10f6414002c2981d40405124030108601c555090304220710300d8141c80c108000d403c3c00088030346403910754420401008042d50100040080d1034800c0100602a60000c40c0c03142d10115102c410034600682018001000c0c0c5600b0386c419246001049000900c41d070f0815528540050b80c1c002d41210003605d849000c0c8003 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 391741618 1250 391740368 391740379
    0x12010f0f020f0f221212230a020708070f0e0108010c080703090201110d0504081509030a0507140d0c02090105120a02060c0c1203040819080a0503072c03120c03030a0911 74
    0x180d554210b5442c511042c0c03146c000002e440e004590706503510001c080380c84450740708203450500c13419250002400802c4282c0100e5800c0d61356841c04070f107030211035005014001350410040051001e08500036014100100c020700071400144001003002c80d0088c40b000416444828400940e40140c0405101d40800c00c03d540a2568a02001c0c20360380c041d102d20b00d003d2254000b100320308419140c80b14004c00c600f101652410305000801c85040c0c02600d4203542d01198842c400d0008201048801c1c03101c1060780702c843e1703001c242d40104000d0100c164072142c0200000300f00152003103c0402c1801800c1d6040310b40319142d20341d004580d440d0409501050f03400240ca0f140444000780f0020203002142e41300022100d5100c05020b011070082900d10b030041c2031100c18020030740e15a00a0f000380d517108240749800081c0d260341030690f4046074600015a9190000002c0c1c0004070f040901002d070740340c0c54207100246045803d1480325604c3c44000c184420700c555602800b010003003055500341c04120000d00d03 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 391742868 1250 391741618 391741687
    0x31504090b0f07050703080f10080d0801030516080d14090307060c0209101203050a030f090609120905061e0405030f0609070e010b07031d12010f0f020f0f 68
    0x1010710050710151841d007002d60104000900452043d82240d103101da140c1c4d07610340309407200d000701c3e00035a80c080c1c803030442134403449004550781e90704110010221003540c0d140103282d4510b06019052800e12412040405007002d000c0c80304003000110a02c44600f1403420021205d14200c1e124814051030002c01c0d81800303903000024441d41e000010040c1ca0703000312861034142c0c881d40036807950000b241c8074000348038a03042c0c066070102340078001420442d0024100400ca440003c0c85480494020302c1c0c080755442da690340c004082c0070005001c5041028182060b91600741000e0000c3e03014014403140c61007142d00c240d00c00d42c441881d0415980100000382c01c55620180d040c0500c1d442c0c800c03c0301c00404522900c10001040840ca06449040700d4003604070604e4540075440071142140d00740c90074501030815501c614101c3d2912907807d000003200c00c0000442c039000311900c0054505081012220500601a06443d80d19000890f086584a075518581d80d41075942110101c0d081580342c0389940101c1c12 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 391744118 1250 391742868 391742873
    0x4140406051f090803120601140903011104260304120606030206030a3801030e0109050a060c0f02160b030405071d040606050d0b010317040b031806071103070803150409 74
    0x1c9903429202c040e1a0048441e80350442180c2e2405094441140c202006010617040d5000d29100300c4070b00d48610f00186490b02c80300109094413203101a5003040c1c3c50004007003120540c1c44d0b002035010610f056412030800f1441111603524080c600030855030170300480c41c40042004c141e2101008540c042d008a840340703460003a1900801551070f40d207500d00d030030300383c3e0740400d82140310340180c4c04080341d04030107605140c403004500505414428158070341da90109200030480c1009100c03000c0d4410000462a680449802861a071a0382005820365101d00d040444c880d039100c3e00201904c3c2c0b000f00c0c003601d07a9a9400c0a0349070807155800503445a80301c0403024143c02004880034070460281c03401340a500e64410034005600f0740d00030003500e113138242001400081c0046018906a6a00c5c010560401f92101d5103400340c0e6000755403400c0c2c454500c88201c54540b4040c00102d60140040c1001500084103645c4030762a03120705400205440320010020303100840d42c0c40c06102040c0050800c01c454a00b40c1f = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 391745368 1250 391744118 391744159
    0x50a1401061a03100611100203060f0303180a0f060503041209050d03030b03070e071d0102031c020702040c02030f040608071b0f031d0a0e0402041805151b0414040605 73
    0x113440c031360383e418201c1002142c0c1c1405044102e64a080034001061030703907000c0051b82c000350406442c42c0e40c46880d545071018580da08102030303c607421105000c0c0c01880491000c22880741200d6000a0840a03c103404119054000c0c00f9241e0160300300c4881d038403402c0b50510888800d000c6410556000300300b03210903400d01d0343c16404007105a400b07508551181c1e4a0705d05030881c54004861700300c0080d101f040b10034188032070031074850740c180818011641021031a034401c450740050046036102d4a64086604e40c15032609025511300c41d00d0324006589842c003081c042c52000c1c8541d01410342800008400f0030040c500c81c0f0410b076904c1d210070f10b461f100360945207008207007400745440c00d0340015001d514180c040b0794940070f00c0b0b440d200300401042c43c145ca444910090804000c01c01c0e607000d581c80c40c0d039605401c98292030034201c07072049018141100a141c0320360307403080d4081c0c089903003c1d010a000c400c8610b103020494090320000402c860368880d04070005805010660040ad03005128000b4903481100790 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 391746618 1250 391745368 391745371
    0x603150b0a0f060e0d061509050c0415200619050f0c070b150918010c0f021c0314040b0103020307302604051c02060301062f03030106080c07050a1401061a03 69
    0x31308c070034001d5840302e41066119014a0061401c40b00c843c40481650b43d000e401681403881d00705241080c0303103003030744403031402e00070204c078008101c210310307801041c030684a4425507a1220b203510300c2c0e00f4181024001c012040c000d6410040200d41d10201041c14030390800041c02014100401d040154a8400d88582084812407411403403582480200d03482140603d5500c000d181c011b40c0181182c12070110858040350010f640a018559558054807614032000402d612890280c0041240e552540c41850714096541d40320042440403900309442d10078800026040c00035591303058590b00000f5043c8001c09006072102c80301400a500600c408642d031200262084030b204640032901c8041d803201407241e111030210002d501500800041c4255401002c1c1ba10841e03041c10854000d16200b9040000f5009200d10a03100f543d001000400840da80941d6140c5d0007150002040d08003821a80c130150348010b1000001c0c2400c83e80d03810b000e03910201358410802041c890310703001d4002c02080d0811109600 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 391747868 1250 391746618 391746629
    0x305010b010905040b151c020403050d0f1418210601030b0711060a180c09050a0b0d02090a5016050901020a060603150b0a0f060e0d0615 60
    0xe0030500050546050300c2050181500a410b010121180d44451106d50f4000c0e03103d01007080020340a0903046030a48007401c061032007080100228200d00e603002d03240c144014084420441d441003400308110081d01500c0701210203040c030f92a459030034800220854138401c1d81c41c0c8034400e00781c8081300d81c1c2c4c000138549040724028003140800d911084070880c1d101c5940049150183d01120204446a0aa501c5602c111003110100a1159280e944003941b558281e4020022140c49500b4840180381601c6010000141180d41e0149154980d011400040000700601882542c0306412458030342c6285099084030500307500206840e01e0010401c0e01903a06c402581582e040000040300c61841342c1307422a00480c2c070052514986007030103104440e180d011030b402a04500034101c0e1580042e02da8007134140514072502c0c5030408011300c0905c0400702d4a0030315001d48a071801020802241503141c92180545506180c401d1299030b0300300104183c4580807100a0090346080510b91030100007071012416100c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 391749118 1250 391747868 391747877
    0x190503040c0b0313030e0a0b030f0106021912051813060e010905090303131a0103030809060703110904020d06050303131806060f08040203010e0f0303061203030f070302220305010b01 80
    0x54803024402d030345000c00c5543c01140000b004034100400c0c011280e10b05034950003403c0410540e00c680700c0000030b0700255180805c0c103610100500440750140098001ca40304008020310484058030b81c6034403540c003e0b500c0010b001000802048009450940350016400501006281003510300344000400c154400c0720b143d261701c4030002c01c4000c054040d1900881c1440c00840c19500c511100140e4519084021910001c44008089000f9424180c140c002c6000f500c8000d09481e00400303036130910328010052010585032070115111380382248141c0d10400e00a070f5006884038201c210100c01402e07a500304580c14400800d0078440700303251800142c1078880810009180c01e00010341c82040da0b940780105000302c0c49031051418424465103105911a00040001c192000c20340d101d9400d01c0c060710102c49031500000204030305400c0105a640b0b280c24510010340c13071860043c0c3c0710100010041e0400c8201030f000541070401810030300c0e21100b40380c4030b0904100d24940e2454403600a05c4080040b50104 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 391750368 1250 391749118 391749143
    0x110c03070f081504080d0b01090e040605010e0702060709181d0c03010b090c090f0103091b06090506070308010b0a0302070b0702070e010b280504080f0303100f180207050319050304 79
    0xc2080e4060045900c0300740e0500b0449014031046c05015041d001c2e904210307006a0029020600c00d50480c040e60045000084650520806100c10360004002c44c0135075111201f800041036005d483c0500f140c1c00e40700300c60300505010701c43c403000d4151113410b0004000f09c85070004c82d04a01144481d0ba41e5401c8008001d00e0f5078000c148042c0e41011240003030740d4601032041200d08c1c104410b000024500500d0300144483d0a0781d2410300014044411250460540400303014490700980749002811044914074107006030303903030000e18211050240340c0403a02c001c544900480c1c025010358042c0740c0e00400c01d040790300e81120000c0da10b01140c070606094501c8003000041c0840c4403030440b40504964440d111070052010038949407440c00010f02000c0020801c070004070520148a01d206141070701d03000c0d503944d05200c4031203aa0282d95070042443d07030001030400c210733074200c0802030700b141c9101d2a009a11900281403aa0841c041e601c40004418030100e40204100d0b030007801035110318031a48041107034 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 391751618 1250 391750368 391750393
    0x280b0c10050f040c150e09010308120603120a1407050304031203050c070c050910090c0302090414010806130f0602191e0e0616140f0d02010b060901110c03070f08 71
    0x2c004007610040c0504022180c1482108044160b09001c50580d06100d1041d100c84800b194421400740d100303459400d400f150802d510108440c519030000c808600406000104c001d1001c024442c2d109100188541104484400100e2006070382c9904d400c20140ca48031580da0900c07101006082240100280c50800011788400c061400c1d140c6c100e4000c0050501d40742400b003809030012000d03113940b0010003000f03000104262517000d8440444031680d00982c036100d1050900098400048851140c05100c00041c010f01000044061b401a286801848d044541342050105406000780107000f13217000141e200a400c6422aa888012000342d45a18151003c800b015402401c080d201400003850303150f1600040c42c1120183ca0350040a01000c10080701c182c0d40d4a44100d004500c01c16190404115810074080502c00d50303070f08403040c0c0000d1102403981400112544901031580d41800b54403e01c0780543c0038108124080d101014088980041d1205c1d41e071092683c0c3ca100310304581c030404281160 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 391752868 1250 391751618 391751641
    0x6190b121005040308100b27031006090f020c030a0c0812041a070201090b0a0e030904090c0302150c031611030a051e030901080105060a021f0603020f01050702280b0c1005 75
    0x89a05c0c005e00f0318140f0501407420040000a13048030230101071550303000c41441c2da041c881d0f044c0c0352006200000300c84e0b190000703010503070310115043e09407284148194868040040112198100c2c0d901d0181442c50040c03901c00c1d200d01030101980307848c0c10721323000300010040e1503100015800c41c50500044265031750300c0124281c9120100062204d04c0007008150b650095400402d042d890388401d03a4102070786100890121180400117595550400008009600700143e40d12803403000440d0791803038203a03400601c5581e48600682403d00740c0c114221841484001098440c4034038000701560542ea00c3d900703050344d07101c0210604100080d20076020b4225910000101c9011000c180c50b0759101d40e1804081020035040169581c00358024040c00491340340d1b1442002d80c450140e0400000c0744c608600512140724081308986050200c1040403402607074865804a540c406800d03100c09002d111003805501e1101c0343c0d4088103065038085010b1840704004102c0006141c0c40307502c20096507a68408641 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 391754118 1250 391752868 391752901
    0x3120215070e010c11040e060a1b0203040605030402040b06030a050a11190e0a0e0c03150301060b0909040c0b0f22050f1201140c0a030e06190b121005040308 69
    0x1000c1a020302e20414103500078604000d0060003042400801002e00010900f40e41c48141c034031840340c010504111840e0183d100713044407919100c4038400444d011481c0a50780744a03500504040c0040400041e0855440340c0054034100b10142c01a500d90510b0030403140640010307250141343d503042010b0107219480e240140c684c1d20882e0340320202d00c0f40b06a0015291540d0209040e90000d10846003c64541c2d03040840d140628040c9098035901e2030909008151031394540700e858800d9041000407c4800c3d0860156816500700302c0e02c1301c841d503c90303140011440340c1e5076210113007081c0e02080401000840c80b02030100302c03940030503554500c0c0c1128081d61400d581c900410358084480d03000d45485041024035103519850050000884040480f40203000b040c1c11a45c4079004200042c9103c9ca030741e45401202c1103100e4250082003141015960003480300190030b083d100307480d0303600ca040d4220f55800314005890348040003592092060070380a10b0207031004403001e501060001020030203000f40c281140 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 391755368 1250 391754118 391754131
    0x1030b0f031c0e090412080c0403050d1d030f0607090e19050c0403140304050a060503090604030f05041a1803120a03051005060c060106080a0605010e0f01021603120215 74
    0x601034000105049030204901030080010403c100751007006603221081903d014500406442c0528806100002e00141d0000d1031032407041410300c41000060b20000e89a000007169040106034204d00d038240c0b4560f20981c07222664184103804840460480105807076010703840c44d9541088150b1600c900d0400d03e241a1081c90010310b6696600142c1a800c0c0c0c0324903003141d920701c1c00c01d1600d69030340c0740c100303980b810102c50500c00d410004042001e8600351200c00020040350801500f5803400920031034a5140c000c0018090245900700c03a0780680c411812075004d040d10300c0703a440340c2c071820920072240ba4000d8044219000c52020f078a51180c5000141c8074452440380c0c46031440d19a180c0001c5005c2c0102800c100c003060b214401c00301d40e9070345210203451900d0030b4000900d01c9601d0460010107c800140030f840d9058944103052149903808500d060081d403064801011692481700100c0c5403130b069072900007103900f00c90004410000250310f103182455490342140e5601c441c9408003481c0301c2003550301c0d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 391756618 1250 391755368 391755373
    0x301051006031116060507050c030706020306130b010804030e041e021b011512020319050303060f0f15220803120604020f0d0f0b0909370b09010f061401030b0f03 71
    0x410b0001031760b90f080310f64401202c0c50000e00740710102e0641c40c42c5030010001160459004410402c1c5030800c5018402c3d00071000d401802030342590701c00a011040050005030800c080380050a88903111500300300b100e8050601145a450429071080c8025082007002100f860220aa280004941402100107829245440300c090714a40b1120620360590060304036090b000301e003401354400b50340303196600080b405003000e140e5a14000040002100071150038920652400103d060700d9120344d01c004c090200c1c01c0141540c3d603034400101c0101445284648921403511401c013043c14000031029040714181c40041c5112030715400200400d9004214911074100c605202c41000380c84030742c100c0490014a00300c00109a0181c0300440d03040b580883e00d10310300b644181c600049200700c1c400608210310b80346400d2200000d407101042051122000003038001061480403456041d000e43c0024071144620504000e9640d45844562403c100110041e000c24031b00740c15000035007032a80c80d010b20407800030003 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 391757868 1250 391756618 391756657
    0x29090706022b2a060212160e01030209011b0812070509150a0302073207030f030c021503040b160503070c06050c040f0801050a24060c1103010510060311 67
    0x3046900d43c00361507100100005403241c110041c4100e0300458011800b5440c0035988026601c0700d40f0a98001030032041c1580350782c0a8441031070740e011608014010003460056a200c900c040126a4404413110910004414080000800c000d0b00001e11800450100e105065540d264054a15008100696802041c10450403112010a000900c8038044a090050600e052900c545990050780394000c000321212161401e44150800c140200c880051f100030700c03115086541da81000c1c000b8541c014140a0040303152401c668924107001640071011030b0301a00c07440d141c1030814600b541a14846140d00400340a0802035110b034084a11414003500c520046010700d1b540c405c01010001c10030200c000e011700c408100900484441e1002703100d0309002003490708040004104480c0c08a0300d0203420b80c0b001c0c0154402413400030b8041c003198501d081003200102d00341004401803032121401390745546820104884440103c0c412400e480391903404114030410241004d8440c41038034403241500540c0c42 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 391759118 1250 391757868 391757953
    0x60f041212060305060f06010207080c1e060405090901020d05061f12180c0e06060405011d0a03060f0905160b040905061906020a031403132909070602 66
    0x1d666204101098200041241c3e60f92549802c0881c20f44101009440900500c543c540e4100078110180140002520301d1500300400940e61100311204209825505240c13910340d50313290401da0b0000c0401074003d1480386441085c25000707600205452a10b84d242401047d1079042003142d8118401440c4010702030b10b5030b1240183c0301c180e100705804102c41d0b242c9010a2201903011111034020388103405044802d800c20203c803270380000081c0000c1c002c2c401404100207030384c0d11020242d422007100e480032205c4d42852000c2039001c04982c2000c0c05043c1045403013041c0d41c14550005c0345440c081c8042da00030107400c01e441560907078240b0801108070428401809088e030540d000940101008000101c1c40c40b09100940b401c0380c0d141c0c03119001d80c00c04a207020516402c4445009202700c050070322407543c41d142c011004544803042c40503100080c40030f80c110300b0410050700c0b00c60094130007005004d40d00c2c200c00b496030380d0030003401654018001d004400409200b107001d0205036000b010988505919a02c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 391760368 1250 391759118 391759127
    0x601050105160501060f1206050c0f270d0b1501020106230a180203071403130f0807240c0302210910050702010c09081f050a020c03040f08060f0412 65
    0x241c109840f80d5584400014020001c1c461140003844010f01099030101c4608148046600051503c1e02e03c1c2c01c100f0001103034400c8101101c600b09504a02420b94266209910a041c02c880d04030540080c031005029081c02103101800b44901d4003041d404e056262403800490a9500920469688244444280b901544914842d601c0c40c0001380042425990700c41c6103400b400c00741c400c0045010780c0001482040c581c044042540c4081780607045156040c4a0480185c0386900d0b900549018024100c90040241042c1140d43c1c0540001103004a140113684010ba81c1c039804494100b07007440e20705410715460290083c0c0b000c091013500b94013441d031291200c1080d03043c0001d090b40028010180c3d115078503040e03445603500501c0c150b40002210051000060300100702900302071104d6000c3d110310015100b42000e508100103000d000484d071134803007084541c042d000b0340401402c1808040340c04201c19070a8140031044803480c10072585182c42c2c450204481450070303100504040501420901d00c40c0c0075 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 391761618 1250 391760368 391760407
    0x1050f040209030a060e160b03040507050a080a0b0a0e010f0e100c170603030f0a0903060c0806060a0e011202040e2205032d0403050a020a0608071d040902030a230601050105 76
    0x240c004d1701c6482c0895162000c0c01c1c00d40d0341102d0340c230b0071010090100f070000400004010f06400e699030403109080050060f0b5034842002c0080078201c0f43d074000741200c5002c1e0401c013240f52003d07009001500395212040050501030060042a1223040c1d0580c9a10b051401401001c0409407904c843e2500307104138007420780c040201410341601c0100000d5a00a400000030710300215543c0e11441154190b02c0c0080540c0c00c0b54051408215503041072128036038800040310260302841c2000307569a4000300050302c803000003040090b01c1d20b2001c10001108500144641c1c8258603072080307054541c204000404440340494000350588e4400c2c4110713440081c22454072800404108461000c0e1f1000d1428814154416003089074281c211042c40740840c00c100984402a000d91f040422140c5071404006110650520351090b0720680740c1007203906a21680e0160120940240944120300400d081c040754138107030880a1052940c0c543c80200070710402149103416210305a442d149880c000c4000c0f1240d6040 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 391762868 1250 391761618 391761641
    0x41505060d09050322150c1a04060b030d170109090c0303110304051314070f2f011506090807030b0115110a150c1d0d051c02010501050f040209030a06 66
    0x10845080044130016202504080c030326130242101c0d061181b5440e41e05420307819042440310b110300304c500007000c031071005204660701c51490103140d90f40d06241d0003078110b1020350f50b018010f403602003135100ea01104000b022105c07132074840c0d09640c3e140c0c0700b00203c90304c910000d442c006000100340002031052516000c1c842e803d00860341041d850704000360481d50074418006045036035031003007013260356820342c0150301c0205c1b0300307052096019082d4098000403441700c4000c0e030b0321419032111440f6480030001c0607403813000720001c02241110300c0340c196039503c9600a00010803c2e003400020010400107510013520340c031218140b01c50346000502c50403c44250032880a00402d010441c032800b000304170110b0468081c01c000000300400344c030324404070b40708029a40108880031205003090741640407800d0322100c06541d05030042d1900d05109041c01e0900c41d8048000000d000b600a0640d0f05400507030603240111100380d0f050035220200801c92045442454054220019400101d4581d620000110b0f0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 391764118 1250 391762868 391762873
    0x40b030c040f060f14072406030503070b040c050901150e040b0d110a06030e06041211030a0201050f0601031b0305070e06120109051e0c03270c041505060d0905 70
    0x7900c85203140c0d0607140c00d4000c0000114845440e5a100703601c04d405920081c81060781d6841e19040341c070350074000503c2c004003840c1c0140091411f109880280e1204000f503030804181c80d00e4464620309200c903c942030f030382941d41005801022400b450f0803001c03d41201c0070566444030502034018103560140d030b52000b5903070041d51007101e4070454a8003071707110b50800c5c030810048072140425400c000c10000c1c40e8000d001090315100040001080000300181c00980116081d0032001000c0001c442a031800000a4034074040480c2c1100002d405404c039034090a4150502c0b003603943c1e08001101142e5600c001c0d80003083e44001142070060083e0b012940000191038242c0000179444041091580074104c070030b0302d50f80b00c0e400402c5a0310041c0309080c0c10000030501c05003800c030b000a4540443c2c1010b040303060042d0000010400c0010b207a20709200e03900c9d00943d91443e503060843d4003a1106811444240141c0c1414075406203d8084c50708441a98002401503051698210500e0000c0c45201002c98003071 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 391765368 1250 391764118 391764127
    0xa08030a171f03080d0c050313020603042a0905010b090109140d0605091f090203061b040e0c0903011a01020613150f060f0602010218060711130c020c010e0303040b030c 74
    0x207441c2c194145025500508400380c4d2a109031200504890b603040c250000c10005000b400280500c42303503999503044e01103401540301c3e1120300344188490300b03e036100c081480c58014041506800c2c0003040044501e19041000f02c0c0e0b030f0701e15840039203200b890b08081c001298030000b03020814648000c010405000340441e41407090a548020840e102a102c80105a000d842400f040910100480340d10156910081c8069026540826501c44000d0000c10f41c480c03030b850810389003e28102c01c1d10000e0024064503011401d003080002d92030b9114a40840c000d509101c0c01c403450840c401c04186081ca010b030b000341070a5640c078920036182c18008030101c0300100c410130b4281396015035004805d96502c0901002500900c1d1415411034118182c0c040000c0d64018454080c000c0a144034a45070150280d504a0748ca0219280030407918507110341c03880c1c0c480e112121542075601560701102c1102c0054003218045400d69005503220443c090700c0035070581c01040305101c403000350b2016540220580c0c42e00b0342003 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 391766618 1250 391765368 391765411
    0xa030902130219020c030d0f1b0c05040c03021612020109020301091a07020a0512031b0c0703030306080708060c161205031e240303270a08030a17 64
    0x40450340701002000540202c3d460300162031825000c4003103802c0e40001d01007100c41d000425110409150110140040031440c0c1c00600d0080b4051600365030110210101590b180c41c000340381c2002130107803600840c60441581c141074021b200f120503110840c90d80484482055035600030b180b040c8501c030001c654a41c140d28006840074012140694858196440894804009504114001400501154441c12061004c180e01044030901c401c00110450359982e141b4001081981584c40020072a1100040c420055040820524241d81c429034050010507030310150b8680d910420702490180341c0259000c1035602d14514024054080d070001011a208615114017001508561041c008074a0000c10014103843e00c80c4400750302001c00e90100e19030304289000003031641e003444c4800390152180d084d010281c0d43c100151070700348240d801c6030144403240180e128541d805096006002d00081c00d0017080d10400030095070490861552110080d109070303204500400700291070126110800340302c2840 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 391767868 1250 391766618 391766629
    0x10c0f150e010b030606040203040c09050c040b0c0d0207050a150309140613120c0b2214030702011218170909130b0610021009030201020909100f0902030f0105060a030902 75
    0x224009010001a81400b42d0044c5820f104004010b107106a10400400c00010b40a038081004c1c1c4040103c0050349581719141d0940620407600409070030b10010420005010002070f4080708005c40d5803e0720780f040d54035400c0c0106202c0900802d0305600c03600301c020380a0348c880e9000810441c01041101d1550b4449003103541800c0c03050710004d40c6c59454031900d0781441520303081c2d00440190740c076180044a031140c0744c1e001c1d002c4014141c1900d0f00c080e10140c01644000080c03040c1c045420a000103140c02045000b02c0d85c80d484010100c3c00306075003455a041e19071480c418014256072030285002204110b80d44c1c00b00c1c0100b40344041c5900c540c1403209180503241c01c600c4500c18080d160380e1010390002c1e410702100904006001621400c0c1411008060740e6000c603d50b411309884400101d40010315103001d90281c0100c4c3c0500e030300300c6000303020050558540f0a044086031190f54003a03890307644500d241c1d403d92000700c400303000031050000104000d042c004028045039446290010b03680c0d1141d40000c4 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 391769118 1250 391767868 391767881
    0x120c03060312050405092203030903110d08061c050c12030d020703020304090b0d020d080d090b04110a06020613080d020904090605040b3d080f0d0206070e010c0f15 72
    0x800058010030207001754205071030619000b9400440d440303c1e22040403030022a44030164401801c041d00d451303040d01014014203910120102110590384843c482403c0140710780021600d551190b00301c0e04014560788041065102d4594111003d024510051024003040703698910301d60001d8441049002c544009078405400d45500ca5400f03950343d203203041014801e480b905003078a0304c175132031010380e020040e40c59518020809602107031603078640c081c05402c0c7c80203001c440310152064803540204070030480060034031044944210b54000d180d94540c40c0403699031000f2902141d01c0b904820b1220041410103004c1d0851400d981c5000d85861406e0b000b013010b5520351070301110250384420070b00c420054104040c82d885101d001c0d03d805e0074294024044154000300c80c8210a8801101c11403490203250307210000523100f0542280e1004c24046586503941d0312240040340140143c1c00442c00c1180300c1d003002e030003155059681c0507950b12581c64680c52104805000c85041c078808030341040c8841e040c021074 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 391770368 1250 391769118 391769153
    0x10e040e07120c0501120b03030304020f06090a0602070824010308030928020f040b0105070807140a0812010f0f06200f030d05010b090d08031b1207021606120c030603 73
    0xf4a495113401c00241c4a5224680c903484224188541d80c2102c3d1000410f69074003c2e01141c440d50305030080e0000c1500c034800c08210704c1d0481c10300d0002090194001807880c044400c00070850310315590703110828203401d800010020482503020010000702d000c22001d50340000881c8143c1d501070f0b4100784a615043c40c9590a0803c0781c04089040e41980b61000b03501a0300d03001550f05012a03001800024040e10410b24000c114030310100f441411301a501044540154845040311151038040c141803c01c0e400401c01c07540d1400080303001080341225560700c0c074202c038100500d0848090804c14240c6802036980216079021a420200e032507814420030095004906200c0070b13540d03c83c00010b20a044e076105030824800710740704114016036a01d4203c1581c002c281c0240010b0784a40351107140b810260300840000c9000d0b103001c41c6a1400600c8082d4490140c101031f000c40b0041c0001d1300040403800c24501c500d40100701250a80ca454000a404c020002c020074900020007035181e94520740391030b003c5601e1 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 391771618 1250 391770368 391770383
    0x30a0e1b0108090604050c010f020f03160b0112030507020405130b0f0115020f0613172a0a1a0a230f010501091a090a0918051209010e040e0712 63
    0x460410356000070703803180c2001407800034141500d01740c0c0715160f685144140b0b00741002220340320b249400f031007070000105076a441810703260340380360516880403880011541a0743ca15101800017500c410070a4211485581c1504d8141c1414095002c01c001040d0051031059102c01c610340e285d002074404a030b014820080c1c200c0c1d00c0455410301024401c40c2d6284c0d030700f0905541c420b0071061000c840004605501000c0380d0304034100414240f810400c080803581e8815038020011540410240e0305440041c071088480521400031030300d0000f803503615400c6000240a2030ba00d480c1030011040929210766200c10040f101150714545c1d4819101980c60152400150203054030901111000c180ca085004040c2440e020f6a41401c1004107084130540e000f1080c882e24000820805e9030319042d07421001081c0304c250400122400901c140e000d0f903140703a400c58441c0641c51007007842074140360540d41c42c82410780d11000b425242009200c0100b800410300e4801748a0004001288030400c09880401886200e8 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 391772868 1250 391771618 391771663
    0xa0f032c01060e090a23010e100b150708071b080a03110607020d170406060504020f12010501050a210608010516090501090b27040f1e150506030a0e 65
    0xd0f01c00010b88407220303c0d000300e000d0344041220707850708608100912030030300681c80e0310030707010b500418a92000f1035590141348020381903d8001c0d4070911610341d06540d061a00034001c3c1c0700850038800e05200a00d075039000d00603100495006000f059004007001c00d080149a15000b0032440c012690004500003049121219128101840000c4c2c000303c0900042036582c80f082c40160200b01c2d8003c0080b00c4d8030301c150000d010300440f07400c180c0041102910441d030321046100481c605901c40400410503840c0c450001071654800c004a45221030f5541d2540003138100c1c3d001c154000416801e050f21056111140403a0781002841182c0c0514074255402c20810922a0080c040c80f490380e20482c14000d04c58020413400b101708081700c1d003810320b20455007280d035089075070044d030b04140b5000c0d00d03005032900011a0b08014154821034003560140c490885000988044d0029a010750049400b034142251041225042000146822215050b00450101c0220600c1c500e0090b003480c0c0075000207003008 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 391774118 1250 391772868 391772879
    0x30115031103101a1e031f0e0105120a020306130c1d0a020a0c0c03121d241611010e0301380613050102060c0a0f032c0106 54
    0x1090060303100c803004507a801d43c40c240000c070240003e103129500441d0082c3d001400290902c404485511030088001c01c004030b010351002945800c21918002c0d010500321412030701150409151040f549510740c0c02d52141c4c280320a00000d2101015070308601d01c181000c807001640c6c1441218031481a240031113004451380c0c01d2441c40c4410b180c0c02401c4a201034072031840315101341620954841002e0f1000750303a5a0882c1021124940e0380300c0040c0c1150844200842001082c0d5000c180c0450503642e62411010280d0724100f10301c8904074401c3d80540e03140700f4541c0a1648801014050380d00c2c0e90300c94140940300c07564004110815004079240003004088440643c6c103c5900140392030160007c00003c586030390644943c030300b4186030308001e0041c11380b603800018030800d05007100070000e007140762500440e41f4004ca0003580da008160140c000c2c0d4001030b9098041d4000d84080658540e105800b00001e1941078ac01481952900c8441703000c0701c405041111340313140481d1310f004600000014403e01e881c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 391775368 1250 391774118 391774121
    0x7060f17190c0503010305071e080d120c0e031e010b060301090e16051309080d0e0303010f1205071e03020d080d0b010509060906030a090212070e0601080f130302010e0303011503 78
    0x540c2c2201c00d0180510060001c90320006903041958030300d5501c2034802d9003c1c0085200503603903521905043c802e1132a02d145a0742d1241d604112040c080d041440743c03e001c2c85055807424021126603415502c0340140c05000c101e1003c0007500c0d09408c9000148000300600405e00c0c0e684240c011441154070780e41c502c1c3e514101017011050019040d010b02d4034480c00c0600144190040d04032400050b03459158a40500c010301046070089508040e08001000102000780d486c0c3d0000d2082c152010141d010001c1c80e038002070580011240d0010240c6841421302d0402c070410015503010511800c0d10b12004001038a40d07070888001e0a0103801469215445076401000703481c1814001c6040010900c01c00c842501c2710025212132000840d02180c803135403100c04110051000800c06940030719207400c004616240443c45505581040e00400701d81c0e91041c0c01550410b80903078800c3e1500a000c8001450440000300012840b8424030001c600742030140400c80c41c5400c02c1c0c01c1a615500e0091400c0c45680c0c25 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 391776618 1250 391775368 391775381
    0xa0e120610062c040b0111070f0503060a0605100507111809211b030909010929010c03030e15070201020a09060315030318080111071202010e07060f1719 67
    0x1840e05100d03e0300341c000340c0c0c9854000c2c414035640981d40356494643d440e80605102c01e00c0d40c0c030790001c0f10b00d01540e4070003107042c01c0031f180f080a0090140801055015545010301b106460016150780003400c0038401c129110ba010300d405a0b4440341100d99403c0b0750b580c0e0036508840d03041100c8110464144407940608001c8090040000080b002094011800c000425516811000d0f8030011030410700c03500040c01c5100711315842d0303030040c44040082004201640451426610390760f140442c00c0380c3ca18841e60050840003140e0114045061040c000f81c825000b00580c0c885034800c1d03c0c1c2c80004107003443ca01030f00035074004000d44d4010419103c510780c040441c40003005145002e020000320444501920000c0e4000502004440c040d07445403148814010f2004081c600300030414207a1103440e0341c01a0b0403110045a00070750b44c00110b182648140a60b0b200a0103010150080398544a07082d104c40c01c584420006102c82c40203045010186500b44910030b040d55410091076640000e900011180c5 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 391777868 1250 391776618 391776647
    0x1201050702070501030f0e010509070e0c040f1202060c010513032709050601020f0a05031c05160e220608070b0705030d0b01020319120f020307050a0e12061006 70
    0x580400c01400560004403441103030780c28280052a2103441c0f041c02c002c1e000a07030080344103608120030302529050024180b401c0340d0302d011100440b41c640303d1040c18180304900c22210140e0307000078241f1a850050340107210242c401840d45107060500c1d5030490030340f48100c0f034082c2d104082040c075409041d00540f18035440003640c00840840844020409943c5009004da1400c0e1555072000505590081020150300300c2d0407400c07a80c00034040d19107285d80398050003002d92248049544241c5211440c0107090103440300d20501d484800c1d030740200302c0d040040d250907981d100400403119442c18001110a01c501104480086002c504101d689480d200d843c1e840a02042d00c2009550302044003c401d56400c0030441c0740c0490241e01480040340307180a807480280069611060490800b5000314a0682111250b0001c1c0024a41c3c0f2000d102280412196040414010060991143d10a450030210b503d002030401c40a441c0c500b125500c0d10804442000d060032a94900780443c50308407041405619 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 391779118 1250 391777868 391777871
    0x7020105010b0d0b04060509090f1c0c020409020a0e0a06050a0b0304050312100e0109271106090a03050106120314030402030705092a030a15030809010c02030703050703060b1201 78
    0x1450a22208010b20070002e50a002c0e913550030f100b035240d80d40c40e0090401032000034015030301400c01c29405522a200c01856034014800d04020711001803020329040301c5541c4035114803000320190b40078440584100001240c0c408217004000c038000501c405454010200d400c07001690324280800e001000b83d042d00300c00c9041d81c1c10310400c0009013000041301d40084d0a8541c2611a444500d0007680b4840140c00907001303090350400204200420b80c0c010301c0075070701000d6141c0d80519810700380b039070444ac40d010240c280c8440c4103064009050100c0104440d06001d070400240503901d4032600d017104d02c2604412804400103000400380341d0b1112003100f041d10200001482c40c1414ae00090350340d000d902c6803030b018485002c0001e4984801802040348803400d042e142501d90843e1050681503401128020442403602020114819138004540b05070f0f68040000f618003620720006440c0000710700c1c0e0499041c8174255010000510600403070300118810701000c12203a0740d181c10441240070000501110780e = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 391780368 1250 391779118 391779121
    0xa080a0306061409041d01050405010507030b40090602120f0118180515091903081302031f060303080f040b040312180c0e01090605060a1206120b0f07020105 69
    0x4841c0760040f50451802217400044a81902446010b04d40914015403007951901003007006000064000030700c1803140c0c2d58104951034488040004049036101810210403070036076040030490307200b4810303000004211a0038006000010b6401d080c3c0301d48240071180b0540218130401d52030360380d9440b00d401402c1c40c03034884919170400740410755087c28944400461521200f410010000426100c040035401a042e02d0407000d4041401d1960901581c8440c22072082c0c00d000c0e040c00d02c1c03042e04264405d41c1a9103840103515044134101e028420320070183d134180100c01030303c0424082b4082102c1007024aa401141003850b43c240a0001c80c030043c0219103056100d000c11000440c0402441c0d80a5418140307429803851243d4084003d00c1072985c5850184081c030075090070b0246c488440801c417162080c80d01c0c2960f032109444000c1e41c01d1440340ca6042141032081c030380351a002d0280340340000d00003000004d4142e51a02120800088103506440c40d42510080c0a0380d80c040720740da075078814a140020701c880d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 391781618 1250 391780368 391780397
    0xb01030e0a061533110c040b0a0f060906020c03010605090a0c091503021b010e30030c09010e0406180207050c060c010b0108090111090103110c0a080a030606 69
    0x4034841040300809141ea01c0d003450005055030140c40001d050a141d00c1c03c2007600d08002040f10003662142d5000708103a03004841e070a05d2283c03100c04e41d018001c00152080900190034000a010880c0810b94028124030000c070307204003900c04810003440c4a5803001c01c21031419030040e0034100e04604080c000d9040075030501c01521400f0640750084a0301c0300c0090746094601044901c207980e500700c10801d040321002410942ea16401078402d030507440b1002107000710001c3d1a01c0c22a007103014404040d8003c9008004484501854591000020b591000d0503c01c0820100901d90040743e01c000d5884000c0303a001000d50f8044101c4225800c260f804010301d0342800003644415071500ca00380c45494000614a007044414030403001c03030310342c0980f05580303c8944180042c040d121224074140000d02c1e01002078549001405070380d0342031000740201e1345031044200045019002141e10242004410410184580c1041140e440003500882c2c481c1d844480019000342614482e5105500300310799451041c03c0d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 391782868 1250 391781618 391781623
    0x50405100e010503070807120c0e0a060801030506060d05030d020403060515102001060506040801060608130b0c0a030e0a0b040c0b0906041806031703060307050105310b070c090b01030e 81
    0x20000708078144051b242d500c8500c11103501d0265030401030b41905106d1000c48503030f001041c035801507500b180c54061160b101e003011030720342c0008d100203801903201c1e101140c0307a800c001c41e40780103986c051001c2d03d01d400ba8049480c416039000d80d001310307402c1c0da680041014108120a24810700181111446400c0340014001006d0381183d5500360840a03620110500020f001d5106070001d0034041d101c59125541c40710401c2c000c104500c11480892000030000312000080203640449030b82c001c400303410f40c0d21070307000d461040c1e0002100407041c146d40340c1244a16220070407000c0c1c40c01e8887c018007055481c080c40c0200f5500520752040381d1b2001c0510000106039103180989090350494941c030f056160a40540340060001c0303a0000d00002030070903654141083e400300940c406c3d00151300b16a0780c19625001110b49108200c2c00301c143c00200800c821082d601c2d2072314a8a5003241c50380c4d183d003850b2a640c00d0b10709603002a1040b81d1030b0b100c5960400103101e02c1d004081c0f00000c00d003800c0000500300982c098 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 391784118 1250 391782868 391782871
    0x3020102010b1e010e0f030718050a020a170c0d0e0606031606091802130f0305070e0103020105040e060301091e060501080a030903020d031b060f140105130e01020904020a050405100e010503 83
    0x44c14012003d51002c20381d180c07040481050240102202c141640da210b016040c600f40c0b2a444a03050300b4200081ca0b824083d00071034540440701c0c0c0e00d0068400c1b11080c8102c16803c082c02019072004104280f980b603c03a18000d04c1c80028140300079001c54100082010f00e00f81c0075103a040815420700e941042055040f400030b00481d0150b60326802c02070100792050f0028480c1c0440c04114000c80000440c0d02d1800038052401c3d07a10800440780102e4554800e03c0920030709200090016404000c240316640a42101541020006c0c0c008114000b070b50f6121441c40500070100c044004040b19a10107010302406400d00510310103001d44621000f40d14010101c210a0201a000d0f00004490700c0425100e502c2120030369010349860704400c100b07803401e14003515804805e800002c1c1400c829402d58565180003e049030401130a04461400c10030000024040c040ca40000c2554284401d42c6691160700003481440c0350341d525156654102010090b404032088403003070801c50900f01c0400940d800c442100d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 391785368 1250 391784118 391784179
    0xe13061a0705120a020705090f040b16020c18071d06070f03020f01050c04060908010c020a170405030303042105160201180323010c0e06190905091003020102010b 71
    0x2181e071004241080c91401c40640703116041d40c0030001c0c0100b24168086183ca09961702100d842c0308548400000c9032603030310300b41c80c0500711410394000f190340300075210514000c204c10744c01551500740000c80002c3d0a2880010481e480498020400581907400000341c45507455006405114000b1039021841c140942500200781440d014002000e00d1700030042410b000a844000f807085241c164031038049034109115030800301e41e4a1a01084042040c0501c030584401c0b0750052402c0a000d4035240030060440740c3c500d248410820000c0b8641c0c9052009512690213001d810010310340100003c070040307201c42040b07000c0000500c88211400819143ca234001034091070300ea0712075440540c14026045050740000e1046440702c0c041110216401218007407000000d0080010a0380c1d01020b890720040501281c0e0f000c40c040021070b5200031190444200e80d2564581455019250f00c0456140c600c141c078402c1c448000d111040046681c24040d80c4168002500c402d112030b61180c4504a0032076401050 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 391786618 1250 391785368 391785419
    0x10516030608190609020904050a050d2d050c100b0f03151302060918090c120a060509010b0901030503040f0f0f050d050f0607030c02150403052b0c0e1306 68
    0xc1509004c190f4111005958000b032035003900d420305c0d2410903550101d501c41141c86019100ea0b60b1145401072120032681042d030700d9609440c01c0c0d01c00c001d43e030031198600e00800303120301849480503501040144c0042900d101d0380020300f00c00400c00f0840345044102c4003034132941c032001c180c000300c11028071600d070407240091200003406200e10004100d8040c4c211202d800420461900441058071002240106610003c1e00d0301a507042c810300c5020b8010045110340c0c0c0c2c1c407424051000900d80c0d03202950000300c10000140b04a58080018840e01d4203030b20980e0550300c01f10341400854841e0b4810b000030a0650403001d115440c1c0340c1c40300354144003441098442d0398800907a0701484020321100e107005643c2c4085e900c2c1032500150240c010b0529070240d400500c104110310000c00c0c01c100d403c900445d0035031184d6041c0a445c44002300c01c09014003040c9030b05402c40d030f101d0703884441070300500b0b1083c40c05d034440b040503064074420b0002880d0080c1c0e05014143c01c01604000400d0410140342c038410a5480 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 391787868 1250 391786618 391786663
    0x15150e031c181d06130b01050a1b0c120b010e01050a050d03051201062c03060f070c080c1b0303091503090a1506090606020a1a100302090702010516030608 68
    0x2544a010103e501c9100c0e2400b00400d2641c51102120b500d5204031012940d40300c8000502c0101d030100c5080d680d075140440c000708099001240a80b60446102480b0b41c40d010000545580c0d60304901500c3d480581c0d03900201000604110361100d146016000b0340c004804558900000140d0605007445030a000b207110302001024103200b0411030b4601c603541810207036a03503544e9a00400104031088100744040f18010001c0d0340c003460304a29001100020000d041c141c6410000c841544800380c20f130b1061059501700d5400065030803004e440070071901800745c048100030001042c5030b088040b80144c480d400402c8281c0b04d070398840199180d0803005003207442d125518403013601c6c81c201c1d1b01d030f00c041c14008100141051105094015406071100d42c00107000140d0b4850003a65176100100c0010042e10390700d0f19044100000e11040c940c8410025190700489580782c001c00d4891074290340310b40050b5100c03410041d1030300810030888008440c0e07207010841c451500e21126202d0140c0b0380c40040754607a040 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 391789118 1250 391787868 391787897
    0x1020c030312010e070504030b0f0108190506010b032508060102010f0c02061602030405130f06060c030912020a0306020309010c020607050c2d120316031109040c0315150e031c 77
    0x4083e47c0155a01192040443c10200141110300e8024130808513580b0449480541c1c0382d020310b440c1d20076154040000c280036401c05180c0800d43e003000b40480c07040303010f440d80c4241685070f11041106101c038913101c2e10680d09010000909442c404000700c0c40c40f03428480b610726856800691217500144600f002402e6482020341242144660b500683e8003181c04940e5200c00146035001e05610f18102e402080341a030f5441066629980e10700c00600441e40d01442000301c0c4040241c0516420300c02024070600ca51641d0744d50040b42c0050742e100c1020385d51460035070880d81d010454503030489184e0418605018420501039603610141c3c01c160145a4841540001c190440c03600f41c201c0d029103070075102001c0061444050ae0340048560810240ca00084d20103200c0c024840c0540d840c02d016405807401e0914000d002c080c0800c2900c0b030041543e40c1861040300c2c3c81c040900380181841560315070005080c440c2c0103099065007100148650070848120b0f80044584140001d04401401d15404440064 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 391790368 1250 391789118 391789127
    0x50609130507170907050f0112090b040c0819080d0c0c0b130c06030501050a05010503090c091008010c1403060111030c0d020d030c020f07031506030204091101020c030312010e07 78
    0x30401aa400341c00c0000b4010019040050703415001e440e0079002030036580302d800c003598424540c880c0781e0300041054082c8490754410b59503050b1103c0091004150120503568025152504807015104906150001d202511041c070400881a0640181541c5907440e81c944140c2e6211b2641d00d001896520003520070114011014800c0140d0449500380c1c4601e48503030034001d115002d140072034002c854001c000c20742c540203224481c16110f014141d1503515050000540c2c4175400030300201e8591042c400700b000150303184c403100d6105000c0c4aa58880c0075103046412400d680c0d14212040070310445400004089411505484d4008002d1030594081d07078040060302c1c02c41c418103100300c0702c0740605080e01c0301c83da0300040c96205000c6543c2d002c00c0b14103590b4401300d07120140f240c500201ca8001c80310070401b0404030081c0c3c081c41c0541d0000054040e5923036001504484103200111442c52421a00c281030750380500c8054000d0f00b040e0091450500300c00d100c261b500c481400f070803d60054174400b150085205 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 391791618 1250 391790368 391790389
    0x40b070e13020c0f01051803070b070314040501060314010b010e09150310050108070506040b0a03050a1d0106050307060c02030a080d0209041a12160e130203030a0c0b10030c050609 79
    0x1601000c65454402c0d42d10340e512401303404110a039079030a20020840e5003000556441117640ca080c0a182004050b5807440d000d8103000e8051410161100c000300000c54401003914011480b800000824901d1440e01442e01e01240401c1c81040e490840d40010030f98000b6020360007814200c401409680e900c803142d070000c1217a0905035416220b04040100049071903400b607410303581e01d80111038005950780104039540c0326a000c0d150581400303101d000c0409000350400e03500300381e0301100415013100c040600b52410002c4404024141e442d4041007026003010720844000d002e40385450f803003a52090300400d66034074030743d640100782000c002003800c1d0400c1c45070306440100000820034041d4098081e6515007900c20003400340d11030820800d4044a880b0001015105403801820380342e100e915024440845810040922511006010044005a40c188000d0680c00850780f074442c420300c018280140d03500f000038034251110210700030600204040301c1090048900c201c3d02c26a0f038641202c04201603004 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 391792868 1250 391791618 391791649
    0xe0c0a030f1707150e0606010507020402071716170304021f0e04050c0304031d011d0109050303120f0c070308150f0406060210180b010e102417040b070e 67
    0x10049a100c3c200100d5a502450b540b6041800703001c01d6410015103500c1d10000d886040c041441048558010b08050300500708490107140c41e1600d19400f80d04140d05940901404100700f20880c070203600300409203854000340034084101382d007545003a5010a0154401d00310040300d201003030703e05414003840350802c2426610301410600650401d4608802582c00c19035045000c03440848100000e00d003116010503034034005a460940c1c000003425140301e11520b5206650402205003030200300d1342c90404c0144035085c0c03a203034001e109191001c000c002c01000a000b10030349071020014400401c6d804983c460b003200d15102c1000d020f001d4680002c900c0c68020034407603005800d0601c009015070300401c030808a82c91f0b0b4501030100d44c2e11034505640d0b01000d40ca00910304040d030801440300f650040c00c51f0b50711222581c25260b9058845101000785e40741e500042d5155034290207590901540324003640000828621200300c2800c2555036400f407402e0081c04103003000648001ca0015650780e0070900701c0d000 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 391794118 1250 391792868 391792913
    0xf040f0c0803041e0b0a120b030c040e0303090c01080906040b060a031a01080714061801020f030c24010e0a05060a051503150d0512030903130b0c010e0c0a030f 70
    0x81d5124059110704c018441c41d1030883c00701d403a000030f40708245022594055819560f00c5141d002c4401290f00500d50503868035014490305014042a448034481c503d0710100d40f00086807680342802ca000d2528014000c550b041100b45002d001c1a204009000d40c2c0042d4800a8002e41c0c0d51054007150001728581d0001d014032100b10f40041b07281e6000d6100d903041e01d030101c09030760300c9544800030301d2210380d005000c036500440200940010304985081744846c40720144181c03544403085018052864005800140e402e81124040c0c055034210500d603001c14803011401941158540100328840c0305c00180030100303250f00c800010b1b206960380c0303042c00c02800c00180b000f40c0c00c2101544c030b1a219002207482070304017516071513840d00c40d182041d40010502d071300500800381c00d40841940303007103904042c0c00300006100500103504003000f81c001c45005808200c03500340c0c6031440e8600c01429100440d21244258002a40400581e1076103421074089c2c0307030411900452490189814441002800b64003120603 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 391795368 1250 391794118 391794127
    0xf0c11150711040506030d033b0c180406090c030822050301090503161719080723090112051f080609070317130602100e060f040f0c0803 60
    0x40c10000251030954080d82c040141003080c10180003c9035000d540056050384416020340100707120750400c070101038a2110b000d20700d040c5030440d6035008000002036403002500c0308018030120000c001c1400c41e030310200da10405074888135458120f21200500042c003200c0e01c800080c400e1100c038420b52700c011a40b0a0300383c1d5640d82000d48514416800d40c40242820741c10140c0010070345014013800c14015081406140707440190800c0200c11140964200c44049601c01600c02421250300a03110400d02c006184100a46005005090301c0c00100b4940074440601c00c03000d0445803d03440314203042e09500c4042d076904156001690760185070380007008104c0c00c090400545201c8540c000c120b0100d281c0030500c3c81b6403a0400035031581c01c212800d95807a80840c000b0400301d4403840d04400106d480701a032a2510050360203100d2010701e540c00c4a00544c4c080f40d9040c04a12451082c60800503c1c1000f80c98a810041102400d25201803c09000c0d05603c05265003400388a0803400003c100c054100c076950f = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 391796618 1250 391795368 391795399
    0x60a0225050301060e060a0b0901090f08010912080f0a050a0b04050405011a01050406140d020702041a1e010e0d060209282301112d0705040c0f0c11 65
    0x29081902900c2e02a501302040050b05800c90324400d80508001031a0300480b509007006988076070000303090700c1d0401904035000903000008030444d1000d0403601c000031841089a003000c0310010240040201004207100070081e10305552000c0340c2d0441480600414140c031050b0701007024008140c80503078407a00e0581804200b000550002007000174a80000540440d2030b001940d060103a486820f002c00c00084041c203284810100400d0307103c848010050900c490360300400c1c1120484002c441080203040d1030740500d031500b40c1c12001c10804000e2070400c04040580000c0444c42507051321800b4a00e804200c0c3d04214243d019208250005040340c0307111104244600300902031716141209050000c07070081909040b0042e50611400414840802c41d840b0320011154114032018005090090440c031701c5950904400f40f024800c1c40c0e40c0c04141c2400b00c2068942059042c0c1d110031320861500020450b1580c0012140080c2d00351030500c032100800c1ca0510344805d00240503000e40c4070200c2c19403c0b04 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 391797868 1250 391796618 391796683
    0xf04060810060506091827060604111602060310030b04050a060b010e090f04020d0804060906020c040612032114090d02010e10020a021603030e091003020f060a02 71
    0x60300076040381c0c2440501d03982c009000700c5115907201c886c4c2091210209800c100f110040b00c1d6041502c0a440b0170312070319204c1c41100d4011b0742c0315550845821890620006240c24011210301c3c1803c04c103083c2c40c08078004d107501d11950b8036984c02809400080000f41565002d074800800a5400000c00b00701e070715042ca0300b562580c02080c03044035441d203403203a882e245501c500c400f11681038010301003a130161611015010001c1c0300920403079011041d044410000342003400640000c003050344510600506054000c0d0810060105070742c01307a07141c801e040000f1901c90400c20ae1140c0c15050040d80035200c0c07841001102991244400d81c60704101c1032120580c881d011645c414030302c40007070310036a1761105022800c1c0c425540860505600650b1090721241040d801020f540d19140101d80d500c10501c0889250410b4650060300842c5c0002100f892030b0904908250b8012000d40507840710310b080d58001401c00182000d500d02418001c209411154000c020720b040000240818402441c1c0c000e00010 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 391799118 1250 391797868 391797883
    0xa030501081605060306010318021f0905010c0803130203031b0d0908030c060705030a0b03061503010c02030a050703050d0621060b010c050a0b06030c0d080409141e060f040608 77
    0x4258414841d49a0501c601d0010442c10795400602a6286031122401100035080c2100a40c1282000c49114001aa1004c001488408205490038010b001c4c6020290403454554000c0341030086074900c1c02c00142c100701c00c0340d0b0700c010500354141f500c0c01a4004a80b07140180308142c0240210304442100c070324000103d9490b1201e10303588201110361100d15541d2a405441c035161042d031b008101241d640350061b0065030b80240c200000043d910302c0d050029142902c1501c40300026042501485640e040c28010200303036000e2070000b589850304d5000700810314450581d0240422601041c40c0c201c0d452540c101400602000380c0054485030364030159690258606000c030303403651800c1920740c299400368818040440c2c1182c080c102480e050345405107020340041c10654035004044034485940e482d4406d2160040c005c0328060b4449051035403403001c1342d942803080500300d2404e004100c8e107510a84082c03c032140704650809000e440c0e50020501c009505040660f03c1828002c0110b585900045d000 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 391800368 1250 391799118 391799129
    0x50604080c0a090c050307270e0912070308071107030b01090f0f05060105071106090306040b04030909050402131508070b09090f0c031611010212150906030d0f05040b0a030501 77
    0x4682c02c0b552541d258003100d20707032031324800480c0c0c040c0000751805001e03240701d0150701d00c51004506071842d0300b0003001c6007038000e03000204200b995605000403c81c08201041d503c10810403c5403904140741c501030640b14004222504100c0c0762840a41c6280307051140c64019030b80810500d01c0c5507101d609440240a80c440c081b00503510f411810b035265002070046900500f01038450350b01d4806a512a40390040c40300b0f082581002c410040d540c210344003040020f12807802140c1954190510345001003d0108a034000c1040504060030f200150b9a205130b4421180704202000402c6000c0485d0644105106d50040c0d1182c01084400900420500001d1030940c4041761a03a507140d84018081550610680321040c0300c080510029000070703041007440c05442d00d00d0408039800103001c02d07280d0a980c440682c898400441000f8010221400111510484021501d4070624941a00840d03a1000d80300520800c12134880c0911040c240564100c802410b048072a0070313076440f000309024001c0c000038880c1 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 391801618 1250 391800368 391800379
    0x10c030605010f17011818030c020a0e01030b130203010b030a080c0d110a08090102100c031d0a03020604062301030b010f2112030f05040501090506150d0b0c04050604080c 75
    0x2018840c620614040386102c4e042c52500042d80d081800c2c0c0a441c207850b0542158543d42d44c0343d4292102100c1007107001c124401c2c1d4034651004004d105101101c82704e58070003011030400000501c0010070441c03815a00c180300c40f817a805e80181500000e405070013a12266170b00b501812401c01d00b480290030041100f40c45d400c04076500404041c004a07140a1502501703c903c0d0015400c400005011100429103e001441210341d10a03070340d0742a00484880c041c42170082981c42c50f01c2d2045141d2004080c007042d1214000c0c050000e80394134065260030340180700510b220394519103c036035164403590014064800940c019901d603168503002402440078007901480300c070310020010703200400d1200001c000301c160003801c0c0c500c149075560210299460b00b0400c1410748411030145d00b80103a1050600c9140202d00100e08010642412418240301a1200020300c12840c0c000e40241c8481c142c4c020034941c400301141d9075a9403403440054501554200740e40c0103100041c001600c58000412941c03d0404548 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 391802868 1250 391801618 391801637
    0x306051207090b0109030215070503040b04270203090c0108091c030504061404020d08030a2d050919080d020f16060b0d0b040b09010b13020406090f080c090414010c03060501 76
    0x5548801c5e00d484000d5020700c001e6a103040c20b80c81c90000d803165500ca041124100394984ca1401d201d60042c0e040200c0ba40a044568021280c10351040301510000481c11851400d0104400ea1201d41d2454824180004071002c110020000c2004040005030b0180c44000041d40d08002005081c0175107098507014144242d0768000004060118000e071383c000c102030352010041d41e42c1c8a440d000200100700d095076039503540c00003480202d1442e0006c5c141c41e58074035481034107101e50422110060a0b624256100d4a0b40c0100030800032103d244d041c1c0c100003116241e01000c0b1503200a441090000d0820300e03804107194000460000d02c40003100d1080809000100b02070050001650350404003500e21440c900c0071070040388035815610303003081c8018000304100079040e002c01c600d40e203e03807020081c0341d500040c01c000c4c11b035004022002a048882c4100c8902d03140200a0341e41d02502c1040900c90310402d004503007082481e220740603079544280300900c803c88000e1303c098000c2c2018400c0502040360700341c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 391804118 1250 391802868 391802891
    0x170304060905040e3a2c0901050103020d0209061209100b03191a0403050d0b040905071517040c1403011506030c0e1503010f0b0f031501030605120709 66
    0x15981303c4070400c401030540c1d0b000e404251050a8039402910a0300080181d000310070304100070b140e45200e40641310b170080001d901c103030364003241c150740d800c59001d5240c2d50b0510550340e02e40019904650007440c0140c1c46841154444009208001c0b4059006900182c219040040010814071418440c401d8445405100390000141c4034902c00c002d5058000000d040320f00c039440341c0c2035007500d03014803036101c014440d8503500c101c0c0401c01d0300c0c2a404140d0200c0c28001461041c0520a80302106035414043d404042d41c49a0341c45607540a80a852500000040c021a110308a202da81c1140800304e07c625040a080540d082c48250040440c0071090740d144080b242014007035100b000350209c0d4441065450000110018050300011030100f1812200a5211303903191078a121043d40e0404401d80d40b1351504140b2242c641141e8844e8020303c00c288603642ca5600040c0c04d6950240c2c2c15842604040c2c801d1004800a0105400455114030011000102050001401e106890080001700140b0394481c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 391805368 1250 391804118 391804121
    0xf05030d09061b0c050409050606040501060f080105060a050903063c0a090503040801090c0e0f01080303070f05130605070210081003080904020d0c020d0f05070c05100917030406090504 81
    0x34002c0002140050f040d903c0c220340c3e0303910701c9400c03d4003480703102521540712400242610103480b020340e244c1c4c3c810000d0003094900307440758500424003800c040d0383ca00c0c0340a0300500460014420248640c10119110401c10300450403960494001020340c1c09074a040e2030400c11065040d6185465071040240324140741d11519400000280070050124503035031910400c0010304000a8100c4880c0014080021070603002d0007440c0d00b462040841c20001410f0401100b10a40010b2007107c244405200400c105000030045070b81200140c0b42841501c0842202502c840c0f1600e18080800d9a410f00002070385640080a00240d40c42183c10044258030301c0b200701c0d0001002d842c0f00e9262260600c00700009442c2c8002050841d00150000d414100080460011100d2941c0c0c0000907800c80d80c0741c6401180e00c01c2000c1d512070720505046003090750b1601c510300c44094501502d0701400401035400c040c140034500310002003c2040404007856084003029071a03030060700c2064082003000b200441c162400313 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 391806618 1250 391805368 391805387
    0x60e0303010608010803040b09061c020d02090405060d21020111280c150b010c080712090803030f010e0402280611030c12091c030801050906010503102c010f05030d 72
    0x2308000d051401104c10406554820b1800c08409204000441c0300c80050f40081c1c20000c1e070704440103840d0b10146003403009031100100388a00c107801e220070340c900043c0d003d405d50020340980307064882c4941a0490990040003184140e03c3e03000c0700400c00a17405c4200e10300d03a94504bc40320821b40c146018120054a68107000c12008142c0710101101710380070300b0b540d4020300311148145006440b190154803091416404000f007030710b80e000c601740c210b13807101e4000e0300c00d10090101d81e004500d90300e010651032418601c10b02502d0f030300b514940e02040940d40c4e104018a107012580103449080c42c4100d00c1181a1681c038411038002c20750f2031011980d000404016624440c40c01c0d0050840f1000e890b040049681c048041d950384601280040d158002004140705941846619408040c0d4100802c101070b00800418807410044c2c02c000300701000c0fa81008440403035841d110f80002ca1214486085081e118071418074160060100c000200c5600c010341d04d0b030417610140c054400c0002455000c0321090340 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 391807868 1250 391806618 391806629
    0x31101090b0a05190e0703050601080a0c0b130b0315030c060412151508030904060b070206191430040b0c0d0f0c030b0a05032404060603060e030301060801080304 71
    0x906000950030581c0c40d00702075071001c0c80700162070304030341350058120803205403030b500c0380065202100510800030108144c6000d81525030040240e03014550340c031160301d2018099580400300c049100ba24511865803248040c10082c40010303242e2505001103281d400f10000c00a22030b03c110681c5c4501801d06c00221015540e0044140020200d603403940301801c0c00114180300c403141e589602c0c540700c007403003104000a84450406166a80745280420050307d5280c1c001c1c0100301c13000c018a00040ea0f600045645980c510340060704565601d41f810750b81141e114000d01910800050503000440b0360045100701d08911010125202103a1413610b40c6508003101c0082c503074031515000c100400003c1016201d101055840414170f0f0300c00c2c0c031803581500e40c14051880030a8484180d19000d260005652001e840141c00400d14024030040320740d408115182c9806641d8035400100d018440240c100c00c01450b00410b0900c03d002c00040c01c030f580ca41c82445010000f03100784001203040200072040301c3c2240c0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 391809118 1250 391807868 391807883
    0x211605090d0605040519080d0b0108060a060806150d0606021506010912140a12110c090a0b04020c07060806030d0813080309030d110406030b010201020c030301090b06070f050a03110109 81
    0x76541ea034000003410050020346240c80b900d80303c0c2d0400c00021503054856441b4102080c1c458007801118010f031a030785100181031007644010880c00d0703240c01c3ca0708811100240b83c81c0e000380d00c461021581c5c2090790180c0d0101030b00b0001e60405100c490f0340101088460540c00c41c0c2c80414000280f070351180003950300900084a840040103261078070b044c0781152600a0303d4203139200c03c1944415241a01500045950b080c0c1025101d51068101c41102c001410b41800f905c4060003030000900803510003040b1138441c50b601c0943e0041a110769042d5114100850211003005031690300152000740220b0382c0b60322911443e001252401d114035400340c00f81410604003034840f22155240c041303d401c028681340c042d200c140b11300c09401900303000366204110008005907840741010390003011744400c034000c5030545e0300402c030030002c095000080701d044500c2904000340101d6001e000034120b02c5580f001500390703061680c11106001c0082001c61702e003886500c503050400349600f402803d0710000040604104c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 391810368 1250 391809118 391809139
    0x140d0c05040203070908030a0c06050c1c05090a24240501030f11030f0106020d0201060e190608030309010c09090905060a090c090624020721060221160509 68
    0x40c00c0c02d030003650f0020828200b6640d456150300c9110319642004401400240000741d18605211943c4201038101c03804100580c079004020740c80402d50703070455401032005a610b10004400300b100344500c001940e482450740c141c00200314090030001b12001c6481500b5807500a05040c500540d4441c4200c5c0204402000040341c50400158004c01c42074196107070b09901c83c2076003d01e1074081001148150360501c81e4090b1941032420080c949031002c0001c4081da07140c42400d11403980036510305036000340e90b46220150300e04400f1803e405000540c0c001402444003009000a083e01034012040d1081180d4a001c0c450b540e0303030040d00588000342009003558100c1c00105840040700e4004603049801a0009800035a03500304040844074298846030044440f00256a405440c00840d0342c0065040e10040004504000c10b004d0340a10800c07080942c41c0300c0148402c1004400d40540710350b40601150845115880c01000c40e02ca60304880411003110b070320205034070b6030340a070f0305940b61817501410b50880c0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 391811618 1250 391810368 391810379
    0x7050c1905010605060309011e0c0905091807030c150306050d15200d0b120606090901090501050c0a110a030e011b060c0f110f061306020c010f06140d0c 67
    0x10304603104030035109552251804070301910740340011030203501c1d181e0000a8400a118818a940d0310340c078055618281411020038001c0c3d404030104041e501d007150b280c50346495400c4070403102c0030100d4540c00d0034040c5850010a0042c25006801294107041c501c0c1a40b19400008908565203406000d43c003007856103440d40800c011100703803500b41c18594400105256455003400d0011410100480c11100024681202c0e00250041c00307000700c0161000707813208800360300381a200c02d0024800c3d0b0080742c0e20b41c00181c26410940101c5000354200000b04428141050712020340d0b803251a0440c041003000c40d25282803c00014910750281e05640c2d08000d040d811001110381c0178881d0095800300c1c2c203500c034442c0810070030701c00e45082d01c181b82c03a003c0709801d454501600c42041c0207240031140e00071549070030301c952000c56120390022552140c03441d4240309160a000901130001014100d43c40c0c038099514004459120000b40c40030134080e0890128140e0400c50003000c0300000601007041352408004 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 391812868 1250 391811618 391811653
    0x10120515180601020d0f05070c030605070909200c030d051509060910140a0513020904050c040609030602340203061605090607050703051b09130f0210020f16080607050c 74
    0x186c2007414a1701d58904280e81c0c503014900c0403c2d0f0025030b0620345d99410700010640081c103100003040c201900b442548000d100401000340c2020000c20b880000041d000301100c1c1c2071003100d0b80800038040400440c102880c0e0f201c007d1805194840c081c10804021030080d00d0a0030070203204000808816149600f807008080b007202c280c102d001c1c0c101c040f40c5030101e0240ea400d4403c800c0b107129442e0042e19000c007407003003000341d910160450545810411003444000c0c1e02c41040b4080e2904075a000d40c0d100440214100d01c85034621030035000100030810002c6203e0310105c0400c2803402101100c145803500e080f110080c5049401da007000c00c40400000310729040c920f01400d091400784040c5d8500607542e031030381410503000e03003019504c6074070440703031840b061420360076031900f050071030546900300d88035541c8880e240d141164010f88541c0c4800b2660180620800c9418a40341451040d40c10801d401501903030640ca0758003850050307005e08400900d038144501d040c0d94070070100000800c09458031105045 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 391814118 1250 391812868 391812887
    0x27110d021207290c06070302070c0509040305070203100614011b05060903031b04060c030e040f1d0f0d0504121103011508010c0806090610120515180601020d 69
    0x98104000320050403603824140055001451850b4040080784068201610464060120501c206000f030240900e132540004065900001c507060059031101c0b9802c0c0326494009a5022690010480303040108050b844000703441114400d4040300c0b0000c004c81c5480381038a20038014a04242401d011019040d84203241d04101a81103010041a000b0a52140d40c200a4210780f548555840001444a004540c1c1001d0300d000c0000f0702c5c0b550400f0b0418200910500b00010083e0410142e90341216099595900c039600e04110b1070b60030400c41c160b6441c480b0300100101c00040680c003402083c101600004589a500481c0564501e454a0308181c0741940e050040e420036120001190280c071410744092140100144c0c4805440203110320700a41e080c2074a9008401500300403000c0144802a04c031000075a4101604480030031041072010001c0350310400d680d00c10400a0304180c07c1c00102d00121131002580c0e0810b0f10480303c120001c681820000605980081c0144d001c001d10200c0340340b0403100c3c0c9 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 391815368 1250 391814118 391814123
    0x30203160e160c02030106080c01080c0a05030105060304060212010e060f0402070b0402061b0f03120a0b0112020904150b1e04060509011d10030e0708070b1804061827110d 75
    0x1220700c204d40110b400c40c0c1141d00180601e80c060905130340b43c2d60300107400c103038042d4222000c18504801404001d0103400181320710b0f03000e0800440070a04008054040d50310030030320100715007580d40c3d5802c20500313070b118103951160080544407200c4402d0304050003184e0ad1a500121210314644840d424818283c4c080c01c40c40c64140458403201e8070041c014403464203e410440000e5464854010444180c590041e00e1480d001e464106103c100ba6000319026248000049005071681c3c492400b140c090704410800407940114204c0128200744094050300b14514419505400e0502e5030100d0130030340c416806072202050042c045011158410707821040090070740300a031501200315101007480d003030715001c6560221340c86a02c0504881c03401c0150000a140c020000e1030407901e0012401280e20032140f03807044a801c140480c2940e51a603070040c01c020a5109481084200306607038110060440d00d816400e415900c1110815800400c034021000741c0e044400981440064803c02440203d009400c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 391816618 1250 391815368 391815377
    0x40e0c150405060403030201021c0209030d14310608040c0306050c0708030103080304140718051005030706020319210e150901061403071512060f0906030203160e16 72
    0x31640f61608005070000754400e0700003584400c174840800c903840301e0143c2804440352051200300c03190b950000d414642e0010500b040014a1542400000b4a10441c03c1e84c3ea007900c40801a14419030030a0305a656072540f00503e440c01c5501c41404480c6600300ba2070107046600c0200301031001c035403030b82e01441e040782c51300500507c1c003001030355460010b8000368000c1d80c0d054404000c11090100c003c8010605d15010000350400c1c500704500c0c044064807a005101045075110009440d204a1079807a1001d004014211081e16545000095aa9005071807200d80707040d01c07030500d42c0001d029081c0c002d4100e50b2703440c030600c100e0743d03044510b0000c2c10102006404c0d4421a048144071840301601075006419080c00840c13414140181c0c0704003100d1138a40c4038000da00c2080c00304032050000380c42041f45007181c5000101c006090700d0190160109401864913050741400001ba98552580510110781c800d81c02da45108075940c8031004452200d1083d0000c107e0135400244440801c2c0c48070034041350007803d0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 391817868 1250 391816618 391816627
    0x3040b09090a0e011b0e15190e1203030412030b10050715060303180611101d250503010b0f040b270405010e0307080406081003020d051605040e0c15 65
    0x1030207096030541d07460a203440100243e50f6070001e5100d48000180e407000e031441c0c115150802d030f1a1460f071080231144011001041000030000d407162820768001d05005090b44080c400d040e66007912540141d0f804c8a11b20a4082c965203610b00074003500109000c0100b00c012070010407402900c8030b600503181180c440c5614041c04024140c0e07445002d020318002e40e078406e06000c00501030805503d26800078401d0000c45000c2c110350381000140c801510103107801c0440d8100001008400c0303008180e4001c645800346185c0405041c4490105220105003d29000c1a07142c1d950189070882c0c48a403495500080159602d81c45d038245500405c10030350014000d1211010541c1a001500d0343e10305034100310b9000300301030005000090050138401100e12003e1072800605a841c9580ca1040d84150010310080900003a00140e1540703014008640182c200801c40300c01d8644a03072500c84900e415818911140c6004c00c050929114104412403094014049203001204005900d17840d140b805498400810 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 391819118 1250 391817868 391817891
    0x80403050714060103030306050105040e01050f0a03140607170c1b030f160b01061803290c07140c01022104090227060906030411031507110f03040b09090a 68
    0x4400c400c60103a454040c1c07850313504626008094441503030045042000070311080c44041081100681122401c860440910400700046002c030201c60b4000740c110708504040800e9211701080451040c4955510841c4006141c5031108805a00303486545081d07405000c100000180d40c030800240f2801070b0101c1c3e00301035503045081540ea0090600c48900c5507804001010411200c20841c0540603505010312920322126120807a0100c510010740071850008026a0000c8014101c5078140c14a000c1001c242c6404259051960b0110b41704558100d10502000100354011880210010f8141d01400c0c07032481c442a00e44180d20300c82151030240e0340c2000000354174811031005109100b0058040c1255803142030707004000a5000041900800c0200003140807170780c0b00000c60f64801d91021203041e0703501c10040030900d03000c01001c100e55030b10208010b00171544e4110b8540340d0240f00c02c0048034010620f0000150b100e0199102782c6039002d00a0159100c14940f0814841e4800195a0001020103010 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 391820368 1250 391819118 391819133
    0x1505040c051c0b0a05010e070c031106150f10020d030c0201151d0c0a090306020d0b15030108070503010902060a11030d0903090e0105010e01020a060b0409020405090706030b030d08070804030507 85
    0x342c10b2080b203008441ca502c00704500e003800c02d9031080c00c111080240f5032502d00741d4011444020114401c000b0b484550408050062401c2c0d00c2840c65a4115803440c0740c0b1030030380450340c07402603030b60740c400d01040303140000600c2d000c01c01c1007007510680c1c080d044500700e41d40280c01a042c07a105490946d500c4441c1c0c0c3c0c00743e00060042ca0018910080344c5061120030302c10384284201c0280440c44e44803c00c203c050042a00b1400e00b03c100c0c0e40c4028016900d9130104048001401e0604006074800041c3d64094444182500650b040c0c034480010307110259598000c060032201c0081009400c08410700c041c3c81e5440c020b6015119080001083c0da25140e4a0010482244c20b0080214045488000d0078881c640702c80810074007401d02800d062032174801d104000303036990080100007042d0076141c501c103500781e44903500301c105d8940c2d020700180075a00b025000329840c0d903440c1c010003000919000300082c02e8500010700340700e032543e15100d54465440d140001c46e4800ba0040095003400b5040180300001650f2 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 391821618 1250 391820368 391820389
    0x509010f0f0b0a06080411010513080f100612031704171308010b181801020d020f0706050a0603021f1b0b0708010e010803040501031e0203240d1505040c05 68
    0x200002070b641d03460200f048038165968115200700034001c8200300004000d19881c02d4190400d08095880d000c0e41103e502d1600d109410044060041c045040b0030b01c0307000642403c40d41c400ca00c0a1041e20f454083e0a402c010348600b0160010b42114203c10006a44042168000d805a204640040e1214003801032503400101c040012814081003041488420b04c515010000d0880b1b45405408241e0200d503030040019141c008402480f0741e200c8402d190941c1124151208603c1c05d641701c0a100c000400d168000840903203ca500380300029180d01800c2c456201501d500401c902c441800010040d200c1e0340181c0030031028409620b00301d50551814440040406101d041c8041482c0743c0180300508000d010791000d10600c025000500514601105450940d0801e01c2c000515402d2440d038850300d064650b8030140424070000500c040308801d203150805d41c0c440c00c041c21030203010078424400301c45010300c2d0140800d20440c0d10030105681d2608400d4004d40103604a9401c551140f0019a1401c031 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 391822868 1250 391821618 391821641
    0x90112050709090b04021003150801090614041707081e040306140c090f0d0f060c02060c0c060105040b061c0e1501121103070806010905060a05040218040509010f 71
    0x2600121441001410040600906148141808010780a944920070040041c20082c0320364024000d14106901c01d6010341c030f40350000080c90f240c956079000220300a141e490015140c160900d46104000342c40000c4060155a010310050040b03102c0d000440180c4c1c208200884070054104030240401c030714030700f01661003103802d21a40d5559255142500807100b40e466104e5024500f80b003040803c0313180b40242d4482d80b0003520204481030020f00010150015404000c03e44a07541d0100c9042c401c40354801d03803448006800326001c9880703103900c0141602071440c680034180c0c00903005100c20300b41138103c600414000f071320040c01c041c45400e09004452500100f51034440d520200407003022000c02182030281601111041c055040c0706810390342501d94000034080c022805602c0f10300780c03001c2007540020319410701a25841c0d40c54403920740c09000161010352081440f100b0125030341c9454400c40d02d10310051595141d5484c0c0b41c0c400e01000e040010468680c5541c3c49a20403480034a90182422410 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 391824118 1250 391822868 391822889
    0x5030408060124020a031e02010f09110306010e16050f0906160209150307090209030f0d0c150c120b01140f0702090901050403020d0c050c0a08030904050108032b0207020901 76
    0xc840f0141c090001c40000c45201c2194032401340840481e0300030590310220b00f84031902c0c9001400d41102a405400b1131840c45440903d008003407070070f201c0d20206445442c181101524810790380c17201c2060004a007a5081c04030344182c5061103526034040c0004115a0201c42c0300d050a0012400005100b500010b100b103880a808401410445c0342c114400c59111041402108070140108042903941001e805502d02159000401e0420341d501004031000c58860002225075610711108010544a07040c9402c0301c0298554a01e21004003c500618210f54480d80c1c2d8212003c7c0f600c2e004e007018090b10480d030350621207840303242543c50010000030050b20400400303240d40d800c443d20612007080002070120296914080a10001a902285407102c01e040c07440d002e03041401c6420701a09281c0c4160724554070501e40f4800040d01200800500790080c03080790100010f070790707802d12251644121052000c41030300340145c0380108540031582c15140c9500b01001800c107400c41e40402c3c0211401c0e0403084491 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 391825368 1250 391824118 391824149
    0x30912050a170c0a0b060d06060329070f0c0309051003151202031207030908030304060506031608190804092a1407020f04020c07090b011701050a060c050304080601 72
    0x84039030001e02e400e00a00d49605072a01110303c903015194060341c103006115400b40e0010860700d51351070041e8160726400800c10030030b060b92840c1225a141d03581100c41c03e8041c030180c00c42907010548411030b1084d10241c46050880340d004100300c07850407581108038240716203640041696100c4180103000c01c0c20540f000107a81c1b0018500e440404465400111302c100010403080058034049241c00e091000300e42c04a403606800d10f003ea4980c0415040800b0911000c0100414440a038200d60b000703400a0b030a07244c0c0c0700d03e5040c145803100c00c3c070b005001d210742c0940800c104071143c1c640520b9110740075002090401d52a4a0203400307a80c0c56102081c1c070b41c00c60b10070140c08545040001e4125080c0e50512940d00c00103881040c85070700406401a2244050008404890b02c2d40e8040381d01d1000502c054a540c50f0715410100c004140390a802e90000b98041d000c40d40c08900d0b905040d040e44e500920418280b407400e5011500c15a42d68002c40e05ca02040c4030008a4100812a2502800c40b915000c10f58 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 391826618 1250 391825368 391825373
    0x140a021e0705070e07020f010e0105062817030702041503050c01020604210e0d0506041b03080702040f02190e01121803031d15091509060a0207030912050a 68
    0x28449044a01040c1100030000700000500000d0720404940061802c0e8000c2e9079051003d900303001d40300840f030b00c8079420700c8405da21119066006510800f0229403000100b8a901303035030102d201200003802c0183d40d010100f03100381145600446e01401e0010110780c9040010390110303056903d040003403001c00140560500c10410180a00ea44001c0c0a20007040c0c4c1f0b10b425142c1c6005503002c248078000f1224000c0090301c00521030520315803519400b0341410345220403031070450b6841500f01c4003903440c142d048042204c2240e40c01c001004603034100c002d0314284003440e000c01000700520b24070000e555508014100744448400a5520344050035200c440c1c0094011001409140c06a00c8941060707143c01c039410f00400070f54400d0381d00560540750010b0803840700803062100030350748a8500c04520590303400e0108141d00814aa106407105000e0714001c40d11010038150300d0341c06071060030b1181c2180000400c00c070b40300d030b0140071164001d2500a611b150344003400f14410f0b010385402d4079181c20080c0f9410a = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 391827868 1250 391826618 391826647
    0x80d05010803090d0f020303040905070f140f070209061816171006110111030c180406080307030c050a0804090b0102010c0c08030a021c1113290d140a02 67
    0x1401c0d018040c519041140e000581d000c058190014203100305140702e501591420015a0040c203001c0c0c2041000382000000a4143c2c0b88650b50340c40058064426030302c03030600c20b6060301c1e00351a00e0000c846c1800c66a0f401c20403904e0009001c25008210814503a00c100d004951940c09a014254094076020361200010907901340e038405e802c800543c240a0190000c18406800222505440c2002c0140f4000c0005400350945514148100a0220901510032031001c01030941c03c00b1101c201c0660043ca40500c82034070305600c5201001d40041c01018042070281d00b40706910303403048041d100c890f4281d90703580d20103410603040a1500390361460a408035580901c1580c03054829400c16080032883c3d82d80d00c24062000405031140d41ea004202c011800320b0304860070141d00c400b04001e010f0205200d6000e41c080c0c00100c440c1001100b404400a40c10b0604002c48043ca51444859250303807161010340310199200104d80c3c41e03e1a070b074402001160141c1c10555028020462001d60307145c00d54032140e01c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 391829118 1250 391827868 391827871
    0x30a0507031a010f0e06100c1a060a120c15021609060905091603020f0f1530010306090f02030a150f0c020627071502060c0c0c010305090118080d05 65
    0x130000782c58030300203000040a01c1007499125604407114400e80c0150351040f40c1e802c103079080042503501200c00d03080d5100340c7c1c4000c00b481000300390f0f0110616a603c5140c600410184540542849000c1d1810312a0081641020680c1410380c012202d25945c007003c890300740b01c481ea21000c08141d4070275082c03000d48107e000d1141c00c1a01180105000c0d44019080c29079480e180c88000d00c181a10510040c682e1109145210300342e02c010052803190001c8091804e10750b0200b0f4111032400078a04140e248450070900c07034024603000080d11203c60b82141e4401d070040c00380490507035030004031844d00c00041c2c0d003c1100d0713006144240c081c0480211648080010346000d6459010400d080c02e880800280d800541c2070341c485040c544c008040544038045209014040b0f40391010390240035008101222100068030300f60b00c6560031250b00703a5904074140810300500b100c1640030b030402040d12800d58030070341056400c111083e00004542c51240d4405951300354407031045a0b24031020848603c0b000c1c1d68407489 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 391830368 1250 391829118 391829129
    0x3140403081207112d030a0905090903041a0a18090905010e0316020103050c0403060c0804260403062a030b18070e130216030905040b01090e15030a0507031a01 70
    0x10005030725010603607880341d8580300700e40d40f045c40d11a0400c00303440f0b044088103c400440070649903503001d1014014000400b5000e058014034428010405602c0300008030b801302c0340800a00100f0150300440b161290344040311076000c00100503c9403540984282c0a0801040300c4000042c18a080c1e103030460070348500b003601603c0d40e00148000e115140e182d10400c05441e609180000342551440c0418a45000d507800c003604140c5400c81c1c002e6460b800070340160060f4010003400454807041581e03908202140c60100004035028042000000d402d80c1140d410b840c520401200340c283d10800d075a060210803000301c00000e480c0c107040b070494180190041c2a030f100b122440e0783d2502d132082000c0c2c9070156076541c0c54020042841c5480c510310307030399042c1c50b40310900802c0b01c1e141c1605c43c10010050100350144602c2603190880110702c541c05040082c0480300c0a0b80d83c040b070f50f42c4014202d22036901180b032258150003000b00d0500080c10921120028601c250b1035400031411034607802e04c100304140c108 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 391831618 1250 391830368 391830377
    0x31323100903020c010309020307120501061701020306030709110c42011a120a0504060501090207170c071e06080f01120b0403090e040b2508040f03140403081207 71
    0x807012a902040c074030700d03003082070a000c100780f030803071010130301c1d14503541d01c640c62409800406404114040d00310904a603c902d0360412001d28038000e1a00306c0c401a50581d6042e8020308081124410607004150b5922861040d1400c1c24140d1083c2820f14030404a084160449811420150414860300d4040070441d00410201c907000c41060302c09008041c000c8240103c04c0d034540c0d11101032141308649010b80e000354031010a04000210001506041d0780454146041c00004141c028051090f21981c5170080c02c1c040c182441081c64100d070b980311401249450151190101e02007414002c0d009e52001038a42060300a841e04c0f0005020003c09008032007007250002c010045254031a0519480702d41200c101c280c661610f1605455684941d0303c01000b82d10b070902048184103d4140307441c4604138014854500000b8000c40c1042c054054070b040c00400c003400c0100740403030000129100c40a201c1c1c10410380c01c2025805201e81d54026900071141c411002400b41c2c1640074000d00990402c2003400e0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 391832868 1250 391831618 391831631
    0x51e09070e0c0310080304080708102f0c1207050d0c0b0705030703020d09030509331303020306090604061b080f100302040f02070614010e070503132310 67
    0x148980c080001e0100e00c00700038007201045114134040c0f1103200038900281125643d82e500c240694176823910b489030509600030244500d642000034003c03c50400400504244150650380d12040d1150581d005945010000d020000e00100c04000c40458a5590035501da01d03403040d85040c2d480c00096035921030410580700c0b60130000565450b0100d13040344460510503269503d40c58110020302400130224030950511030440c2c10701d40c00000401c2e4441c0141d900e00000b100001c40d0007981c04e080c0d004041488a980b00c08181404400054042080700911001104d81d40341c000074035005003135494085070b8002e0300034001088818400c05d6040c1d010f4101d210150303013071604041d243e00030040c030543c000050440062401d4001c0d850a4000e50b41c010020451a000c92500c030000750024201191014540304c0d50569103021210380d80d041302d15600080c920355446d80c0c000c6610b5000070301100e50705003070502a940080c0140f00780c00b44190303643e044c903049a0410f92105244c00603a8880b1a0303c3d83c075100 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 391834118 1250 391832868 391832879
    0x9150b04062309030d08070201020909040b04230d0e060921070e011802030601020c031c090b03011404020a090f1413020c060f09030c01140603010b0303040e010302010e0d06051e0907 80
    0xc4030a0780e05c00c641440c0b0000da41c0c0844c142c2c0a84148402290b01240d850100002c004100e4210f50050b4003c00f500c007080340f814201010141c03503840e00e80409610041c1100c03001803160485c0180041c0240c1468200950b5902080700c2c07002500e4003840c0451103410b90184203104200300002001c083c0000740c19075141482404003940c20314901e1260355000000250390b64020011a480c1000203011207400000300000503602144e101803050000c0c1104100140c91591542a281600c8001c01d228001d1031030102044000e6020324160001d0010390000000c103210341128110080c802200c0088040104000700a0310030380c0f12044041c11172051001c2a10544c0c0000d990f0b90000944408090584442c2c15540c554002e03004d10348055800c2000001500940c0307441280a000290000d000c01071210007011b49a0185020301e01c0402c182100400166201d204a11000b000150025109109580751001581d00803201c0d007070213003000c80c4054070000815501650101c0001d0103003147c0350400 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 391835368 1250 391834118 391834123
    0x210050a08060112020702030d02160503070311120f03130509310303020f0d020d140106080a05070c170309060606030907050909011503051506031609150b0406230903 73
    0x242c0100d040200403203103240c81c3c0400b50b04580c0c01ca5001401c65a801004060095450a03810100c5050a24050f40001c03941000110901070ba50f10903c0c801100300c59100344002108504e089050b0384c81140d030660b2800200340006c0401c2062943e46c030780a0383c00c0c401030048500000d84500c0b502c2440c031000100700301c0940340c81400303602018a507208001490400324080d004603090141c43c1400020014030904042d070040c40c01e851600428084c0d6912054a034201e4402445803c0c0071a260000141000d00301c1c1e40401e0303002d641d0781001000d285040e2941100d40340c0d0118201c604600c000244014901c00304182948004100e6040d4607520b44183d03101c0d103d490038800c140c000c540103800300704c0c0800290465240b0786c1e820301c60b0024007607032810710642d58118031804100d40034845002c5682410049118100b003010445003080581c6032a001e003004240d50481641030600381c3c200031900c0f4800100502c010703c4166603101e90501da1641e6030b908440c5000ca00000c9103802c000004168401 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 391836618 1250 391835368 391835371
    0x7050d150609180f050a020c011109090c160b010f030b0a06050307170102120406020403410c100503062b032105040501140a0b0d080904020c12070210050a08 69
    0x3c0000e00d0380c684a00501c1c9014000c402c020320501403c1204010022440741e01400d404002e08009000c1c02980904007401c40c41583c0040fa042080b24000850101880d8000c140480701081850700321030300d5494082c2203010071b801603020445040c80230030030710141480164200d101f11804002d081c1c0f8050011395210b400c1d224800c050341c056030740c0b803030820829070660342103040c00200000700b40781502e062030003944a40000c64009110707403600c000c00d0403030b44a403226070a00c0c04080560040010245414824100c400407564802c001c0c2041c4162244900710030700302015206c251b02d070700340038003008034101000440504665407641071417541c3c03020a141049030703500360a1008002c4403481000300c103070008c0381c10300d0819400c120601042142c15070046090500b4018140d01c1610b920f1018400c0e100c6403c07045600000072010f00b00440c800d54004d0060b450014001071810000c0642c113410401c04090426070030f0404100803040d4180f004884200c0401c0d4602a0305e0441780d090b01802030ba00 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 391837868 1250 391836618 391836629
    0x303021b1516020f100c0906050f0d0207060b131a1212130f0e070207050d020d1205090d030e090903030f010e041e0f14060c0d0905070e07050d150609 66
    0x10300b440049607550090082c086402042000d5441031800c40d40c07001c0161011002e41b000043c040702e00045e0041c4550165108006a17a030450701c0d111582040d04080d41050303c0c03d643c0543d40c5c0562030304554404070b0181c0c00030301c064400b049ca042001503825481f60400315031401b03808900c41010606201055421403000c2c2800f90580390000100ca4000d880d075142c1102d03001c0034128101040c4070249555843c4244100d600b103461503621402806017654440c20000d42100714801c0400c00581070410400c0080c14a14006062501c80300c001810000a81010740104c2e4000a05410302d0510035a502c0e40300d00081c00651541c1071480001158903414403500105a008201080c108108040307030b403199a00003503140da0502d4040c180300303004a00c1040202d58080070480d0030081c808003c9405403081d640021450b090041010020016090000c8102c850f8051910003040b1920031034004e5020b0003207543d80325100c50a000c40303d41101c0c11240b01c0162144d110b5800c2240341d50141c1200306654 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 391839118 1250 391837868 391837891
    0xf011715060301030b091b1c03031418010e12070209041a010b03070323010b0901050f0a21020702100f0507201003060305060c03130503070303021b15 66
    0x68600a40801400a030040a94407050020000060260440c0c07800d0203980441d0a5400d9910b0301030005060082480301d80390020303002e03000d21030a02092002010348900134100030912a91005100b60041012502c40208411104201810b201c0911a0080e11880f0100408180b50300f14a5980c09000300c40d00207204062103c0020708100c0711441d08039030300384d00080c8209256107681c1c4025450700700300c8850740042e01d007071500c154481000c45450441007030010202c8883e4209504843d03e9131103000114140441049444a00352801005000c15040c5640f4907010111260043c3c2442080003201d034105401802601d02607030390380c140c450302e10806003070494040c81201070540307007809460b8002c0d0104014071942000088000300526403883c0845034512041c0c4441025402ca84980c0000380c000c1e0701c20320004140424140085800c200c10048540199007540c0d2080c0c0783d81d009403400c600003a000319100404c050343c424807004481c159000b1701281a5890850505040c00406802060 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 391840368 1250 391839118 391839121
    0x10050d0623061b010e1c0e090c03060415030602090a1706010501080a1b03090203100603030806040507090f1e0f03020d023c0306090d02032d040e040b060f0117 70
    0xb0f41030b160b6414110040200244242e1850b454030a0312002c61010348403211071040c05042d016803003031140c410a00001821f50341c8503207031031010941f00e400c0200030f2a04a951811104016a0102d00c55402944102c3d03000d0b07555603c000512040840992001401c0305c5030740608401031001054a50540b00e007031901084c2c079941d203000e400260480003c031200403018000c0d44648580c0c1030300640b00060083d070460710161307685036034241202c070b003844090005101c00300070074464503103900001d4105000e03181214a264139131200c0b40083c003080e885030398045002000c001c4804040034041005001d02038000d8205071035500410b4400c040c01c00024419100141c002c0e0241070f043d0a02c54a0382d030b0303c40031003003a400c500d5031210292408142c1c0074801d01c90b170000100b0040d000202081c1c2c6c0700e0350307a003e1403e00c0c0042d084075604038094100c80c280d0000003002c048540e9001d0019000618010b503a010380360609003441c2c8007031680500707081d020f120b0001541c415070360011507810b50006141108100d6 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 391841618 1250 391840368 391840387
    0x30e150601031d0a020916020307030e210609010501050402070201090506030a060b0415020f0f07031205041d01060e01020a020306221707020a09180204020a030b10050d062306 77
    0x3040e9400c3c1c42c1c2c4900103011541c8020150003d6034000c800d201b034444001e580c41d00207440701024009148240181d20400c45040083d00c81e000044250b000a000e4404504d60000c15004042401c12403445541c0103004105242c1c0c1d090094034010881941e0842c0b8102e815000201850668014640598000004114480c0b05917110a00415212184689441d00e8002017121641c03600700c06401845a03600d007401100700800e030414032804180041a0f26072940c2d03182c5419103a0b5207415418060184070010300c51016001c42c1c7c0420b002c0c120703102900d40c1845409002e0101802c02c0ba41150f000d4440750006807000203e09401805502c05805c1003040d00204080c418914640108031902ca441d200307040281c050b01a00015108980301c07802152142038890444a24a081804140c007507104007016042c9640104900c102c0d0b440c000c6400d0701c1000210b61450f040b0a8188000740d0700041408400350a81b01e0030000c1c080760101843c0e211004210000110310302d181c850710810340092a2044e = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 391842868 1250 391841618 391841621
    0x1b04050306011523030a06050103140a0b150301080a120201020a0e0105450d030c2405161d010509040209010c021005040e07080105011e0306180501080c01030e15060103 74
    0x3a1040341c80215002120900130345072980003507034030110340c0c2c0c10110041000d6000f40180084c00c64000003486466031008a000041d100104081f50400820340159130022650b42c020f50181032080c008141c003080b5450000007101d102014207085901c14403070b00e40080c0e80241005800802440c0c0980c0300c61000c1104900d0398400041241c074492111503009800c060076550450750302d0500380d240c0200c0250b40074044449855240200000d82c0052200009003411000c0c1143c645003c220300c113140798021225089403402d6400040d00d543c400f02a0b184076034004d61003461180c0c0c0c0031041990001d1080060701c9401641c0d1100e01c02c940224a043c85644940d8030b007139440b90024502101c05071402d502a000b07030700c54041e0030031207220b10300010100390141d00118100c03130040c2d403058140348070b42800e01120196000e02404040d260b0200098003030b03450442121071031907140002800d52401c0d01d81071820602510a0f8107040c108150311048810109806690311140181c130b81080c1da030b2000490 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 391844118 1250 391842868 391842887
    0x3090503031c050109060308031b090406030302031c062102030a0611030417120403180305061509060910030f060f15090b0114030a150305060f1b040503060115 70
    0x40d003500c00422141d90041d200c007107072030b07a60703030035400c1000940d072180c003400c0581c0c40a00000c2c2c541001003020811204245020320301082849120074101000803001805550490f4002e0300181d00100304040f0242010142010142003901e0400065240c040c10007440100c42700c020304101800030100c42036480500c011111a80e0021080101c56a06420314a050704144c84c10340d0203d958010111500c80c1010882e51602c440480003125a43e0f1a903048800141012580e9030002200d840000040c00070092680500150b1560000c3c2c2c8510300203108080c20010507061041601c5001c1c411440040d42604080c0c94118001401c60511814035601030001120b600410b90300c0d2544242003507200d042070b9820380e080c040b000e000c00794800d4011141035100104280c14030204101190740310782240d0059104081d10f100840d40c41c1c1c0c4d04d0302c07440d04012044030099a9000c0da01c0810143c04018040101d03412102c100c900e003001c0c10540425940d0405000b1325044c0d040007140320721914028007126 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 391845368 1250 391844118 391844129
    0x610030b150703081b0717030402040e010f020a0314061503071b030e04050f0906150102070b04170f06070507020609010e030d120c0518040f0b0d0f02031005040f0f0309 74
    0x141d0baa05018a070050160504440c0c84202035030320001034151100d900c1c11184190b0300564203a0318501203c0324a400e40e8000303042240c0c0f082e03462036080c0c0000b03801e001c1d083e5100002c0d130f40103844400c40e4a024059410000c41038a0140070724040259030b640781c0000c0d030807158a4000c0310751295200305c003d0b140b046561000c900b1407000018107008240d40030301c40301081c0030203a07014042b9860300708a01140e81c90559400d04140c02074800207483d4647d18030320340f030341660500c11103007510346c0d403088200b007a40140c1200112079580c5c82d000c680c4001c20818801c030078441c90018201792408820083c1240a103404c024824180043c0d5a40e1903072050007251a86031300102607074014508040041c12005102c00181c0307081c1d0808080102883c061825281661400240140e41800c24000c01c030040c80308a960040e40d565444030005c0c81e44500c50f003040d00c14811a09845c1d244840d0041600e450b103101000c00328113080034100720001e28040e0110b07101f95801944500b1000c81440d050342c0f6045103801c40f = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 391846618 1250 391845368 391845409
    0x6120b040f0219150f08062e050d060503030c28083618040c090608070f080601121101090306020c0a0303060f050603011511160e0f0610030b 62
    0x58a10883d08201076030843d14081c000392400c0b10700d920f041c0e6030100d40c2c4807100c000c2958040010046d0501c500480038510450283c1000c822101c07030328400100d180c540c40c00c00110003149440f0b08520740e11491001d0b107007c400540c104540b04807120350b81c0145000016010b450500c0c120103a81c802c0303540321400340d4001e10494556080c003941080000c0c02e034a00c00e40070400b0741050722100010040084010101a045130500c1c07600310201c585140010740201d484c102c03004000200580d940c840d80c4040d2000802408000b4503184d1300c2401013095400442c0c41e43c010000411294012401c0311141d02d0717125080303000d00d98490300143c0d0115513982c03015201500000f40e1017058103000c1032854003a4482c1e101004450740350941a40d203010540079036500400108010b01445000d8284003a160f07109103400300c034100c0c10004003401c2800320008180c0c603117a00c2e10300b4007140e543c00c4e0ba426404081c0e091000c0e4146070000000d018000c40152a005140c0d035150304a1554423104403040340c0c4001c2551 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 391847868 1250 391846618 391846639
    0x31080702040614010e09060a0b0a0c1a010e0106080f06040905150712150e181207030503010303080a0b011211070b010806070207170615010507050f06090106060306120b040f02 77
    0x20241c90740f600300018540002c0000d81000384d1480c245c1c101500035a8045d0130a0030b820704080d50081180d001c064000284a10350300420009040380850705941c910b0300d2403280403545024016a01c0710b02c10781000041c0401c01007080400396100503030b280c0c86182224040340e0b111541c10003506005e051600c3d001a40b442004208240344c01101e241c1c100080e914003000b6000500141c0940c80784140200240c1e00400004600840031454201d0f941003012000c1e5034200100040314840d6500801c421000310300701000400506800c000c1e82c0f03a00500c2c1c94000e01600e02c100340000e000501036040040115034440620080b4000d4000f5540b81d0360340000c40c020a540c41d611a1503680d0411600301005102e64400855030415a1090001311a2100000c14035078035152100f00781f800380105072138100f10040c0004008280200a807011041c0e202c0b01400e09802c01c0440d0a00703450b6180c06c000103140c00c0502c1001141b00011044603481d0708401d074100350741c95502e8002d0302101d2040d0040d51001c0700b80d0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 391849118 1250 391847868 391847879
    0x120317250c060e0d180302010912060b060d0c02060109230c04050406080f060915041415070329030a060b04061d071701050d1112160e310807020406 65
    0x441c951010700313646554404107500c03200c5402440c0c140c08000e00282c44000b08002d60400700b00b9aa140340e1180c4404540304e200500440c1c2c07680c09c2548802000c54468100702201c03501840201e02402da55203041c4521001c0651a11000300344075449102d0300d00000000d4540c400b40d0307041e0b13005004010818460242d076081c0c000e50381c0c02040d5407401280111808202c113008002950881c084186220055655480c0c443e20305807a103410307010b040c41c000c05000442210f20307640b001d407258010f914002082c0461108000c5603a45002c001030011424100c2007c0780d0780c00040030700c60a0382c846004225580a1004140030381210741c0a0710a2028010b100014103904c403825030700c10308042ea20f110006040a034101e400702c40c01c0c42915000480c9004a502007080c40c8405d00040002a121a4401c080c144210785801002002035001d107a800c00c0501902003420301482e0890240114110404040404042034810384070500c410202d445007030404111522003a1035140f9002401000f03900c2c1c4c1d65 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 391850368 1250 391849118 391849123
    0x608062805090a0201050d020904060f0801050906240a180212070c0c0b09040209090c1903020c030301120302070e0708160518061e04120317250c060e 66
    0x6503a140681180800c5868040961107001e2280d405034000300703550f401c150010755066010000c1d14480f507408100400f0310b61901e001c1d480013800c0700d424040c40d407031425500c2400c561000d4420122034100409010640e20411508440340340180319407040c400c0c00200160009156511012201007200302a420081d07841d80542603840e10030245600903a0744400484207802d2456000300540c1c824001403040c130b96605d0240c09a83d0000e84010b10b040300850007d0404a0103e540a0600ba0b00250706994010300c64200d44003540507050550070400d00d03200b100e85074003050103102a184a076410300b80030f243c820045c080041243c520a500c0b0750414850040000c442202c0850044414496051600c1d01c101c00b25000c1905504002414110410800c02c4d03642c0160404108004803255101500d00745000904c0100714002005210740403918001d46004371280ca1805022080070410400000751101c0706510504c114103410004036a40b020349410f603215030085e00c03070b6140071011040741500 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 391851618 1250 391850368 391850401
    0x606040e040615080d020706031a0310091106070305030402040e19060b100801060206040b090f07090e15090604080f12072007060f0e150a09060e150703050904060806 73
    0xca82c62075003d50316044031580e1030700103c4811006034092841084003e110f503100d8803045c40c0c02d12a510b4401344800000c0e103408200c070000811507035200c001d0010000350a83c100741008080d0b4009082c500e05407805001c5000081c03001e03000303680314213240c4500746040c00217a0040340c1c0040012002141030800348014840a1703202d5014125244035105d0b528040d11210341200d11507401040580d83c1c2d6500c4144610001e0000c0c1d0032486101201582d010040c040035001c2c0c103a103040000c25085450300146010070584641d00030a00c0300703090009008002c2402d56005800c03d10300c0b66100c00804c6260300318480d581001c10420750b11001d222045da4480c04d501d0380c041301410360802802c0b195070082c1d104c1c21144120400f050300480541036a50280b09101307000000141011000601c080d480803950740130f121442c0004050000a02c485131300300055001254050b91400c51652081001c0d001902c030742c0d00301409101c0080fa07285d0513666543c00000c060100103042c0d072102e050464802011810 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 391852868 1250 391851618 391851641
    0x301090605041506120b04110a050a06020a030e0a03020a150905130f050603060c0a030908070b01032a05010801092c07051002011b05030402180c030403120c0c08030606040e0406 78
    0x4142c1c4c00261444260500002c10380c00014110954071155076900e459400c81c1091a040202404000380da559130000b15001884241c0103411400c00c1d44c42c00a050341c100d040d07114400c1c0060141840561205801c0ca020b0b0303501c401512283c410b000c3d0082d144182258800d0340c0c1700004056440503c0031300c4d000841e911014003c00e101c0c54991108260305c560b8100e0346913100c3e4505201d40a201e510ae900817900860003044070925003442034482e107880d03800c240c0050710115800f091000c240300124001140d04141194803542c0d00341000700080c250765040c8618a4000c0d110081204a0010300e82c0800d042d04070070b41d29461440c4d007001019110741d035520965208070f503000d80510078240180a018102c03001da08501903400c100721000c1d02c9030f400c040c05c10303a001a03984c801030200e60100e0380e500e4098000e600210b078403440c20380b07001410b0980030158000600c3c1848080c40d0095085482012110b5102083d5a100d03511000410580d0249a000a68a140c10b030248000c1c0079441d4802c040c0c2d5030 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 391854118 1250 391852868 391852871
    0x40b070515060d0f021521090607180603050615070302010501181422080313050618150601030e07290903120703020106240206010608061c0203010906050415 69
    0x1520702c81003040c42100980d02034034058002c400380f40140342441c41101c8598074000d4040c03c03c0d000d00c8030112602414051110029440003c0c444031003000c00c40240c0c801c82602c0d208000c0d110059814a1545a51003a08185a160b0000c90029a260100300321903141a405a42d220b0a0504000307000e0a0284640c0071580d80c1141c080002560394000c2d070396030019107500e40440ba100c010580b11031610464129600c20a0400610000345904009500518044048001d002c8042c14014108100138105055288540241000c1d488011801d0606228041c094412030b95820300182c02411140311010968040c0f0318010442000764a50f4115403001d4540c1e60b10340c11001e00c60042d0522031681442d900d50b0050303030394003030291201c0010402c0d184280300200c1c14660390400740b440702d84401c1c01c1c03584002003101a20385082e4104946801402c0a103046541c50800394049040000a0b42c0c0d030200ca030b90801d10403000c0d51070035044207882da80d100d5002c02c440c1c81d0508010740c0071814440742c6090765 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 391855368 1250 391854118 391854121
    0x3330a14060406080d081902030103050a0308130308040f0f0c0605120603010b06161506060905010e01030c08070f05072003190b01050f0d0c081c32040b070515 70
    0x181010f21840003600d00c0c0380c00408030303070340302080540700c6800003480c1d01401201e81c0a19207200441d400550b00841c0300350010700031020103150141c1700b003100502c3e2420000102840d02e000c03a50000d0718031740050b04980e190310004c41f60b050405c22031071000b00241051420b030b44005081c562200080c41c44031001c0d640c0b004a61201c0c41050f00381c821507664a41e12400034050785440c42c41000281010754801d583c0510b044100c0d20003901541d06590050b404582c9501c0c04026a51b040310241e85111024a070800a24140042c040c000c000c0c05440c1904100682c0b042e44045805a00bc1ba00c440e0b400540c20142402144007644296041c0021640079000e00b40101c0000e000f4500f207040208e620002c610703850386c00d100c1802498609140c2980c0c0c8043c005002c00040703031a440003a40944184000360484c59401d80e20f00c4455845036031040304001152403070300c4001c10040c0440003024609241e81c50710260580441d905400749030001ca00c3c2d6107002416100704107000072602100c0e03011520703443c9107 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 391856618 1250 391855368 391855381
    0x50d0e011701080a03030b03030c07030501060302010e04022d07080c010c300924240503060a0203060a1a0a030c050906031b040b0d0501180b03330a14 66
    0x74080a200302c07030301940501603c2c0b000a000b500094007030100a812a41000310810140f464075203154010f03a041d956501040c003d5591041c441c0c0307401c20080e2019807806500110015107403e1500130f03281e030910300343d80070074071810348404540c889a00200d038180c441c1e5040c010380d8000c04030007802001003004143c0c00740f41c015498005183d4041080304060304c3c0c0030085504400390091040407100e507010314462031804000016454a4010f02c50400150b441c003411030441c4a4110b240303025801d040c40041004556400a0419030041d0500d4002d03031a031311104007080044e1003d4000302d1401e111021000030000100004d00702d4200580d4003807001280a200507100c92054104041c0c00400c2040011016224103040f10300d00c0b103508102501c0c290350781c0903a00d44d5400c86200c0861050b11000104603407078140d030040100c900084410451a4a02400a603a802c1c0c1200d0b0900c07844442040c018071690000300d01c00e20303200491108800c900d45140342c000200200041d82000c0b01c421004103c1 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 391857868 1250 391856618 391856657
    0xc0905090a020907030b011806081006110322090212091506010c080741030310031b18050609091b06070602040801020414132a0c050d0e01 61
    0x2141a0050268001504c41500403005403403865101414000d4a14024401c43c81c80a4020002c0c001981c030600a0304048000c1c01114049034009010005900c0d80119111400b108032448004005990145621140010310818a00ea881225a1803011444000314602544280d2084605c241a1401181c0340c1914401000301900c9642c0021020404000010094002000380c6400740740043c02042c850041c4080070004062804a036520b0a2090502100903a003081c0d04003007500051400e5240c01b4402c484601030078880030b020354500700000c00b0000ba00184180c042c103010b050182d600e002d00182c0e0000b41a043d01d26a024006d1000001c00f008004a080c0c02d50b080140300094135044411b04000840d0031080042e41d0f00366080100050b400c400f44014001000701c2c011303490901e0242002c00a2000710164060b2405080c601002040f003101149901e50fa01c0d007030f1481c6042c1c0030601041750a0303802c3d1040204944542d035040e183c0682c2000c09911180b100740e07901e09075003403203540126 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 391859118 1250 391857868 391857883
    0x30203090d1422060905060316140d0e03040f05090f0402090601020c090405070603051b07020d031218020411070f060c210c08061f08090102040902070c090509 70
    0x306400201d881029184114821038003040101c480e90705050a80c800b4409144100b000c50041c480c1c081420008150452813000c000d21080f9240d50a516152071551030480200c41c50100304490b100c09800c0c02e440107401c1d202d8050360305004004410500790000d030307280d000740581d0303032603034041c581c002030620300080d18604c121400c049002c030765112a0700f480481e01d000380845041d40034201c03155000e0b894180d2040d118500840003085043d10380603028088490283c010121480c0454200201c05116002c980c01e0541c180c810400901031810308032078040400c18052a41804c11541c3c021040200c1030b03d45400d80216020084c100210602600e24807800f07100404003c0c0c0148a800414460fa0011410104900740f40c03d41a081c00d03410340625002e0a0b041031100e50740d004c064030081d4026102680305005a40c0c000c6804040398080c0c0007050004192001c120582e07001848080c0290162001403850201c2076407600750754907122190846900908014614020001d848035030700181d03d8 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 391860368 1250 391859118 391859131
    0x90b1801021e0c2e0c06110403050d08060105040b0327010c020c0618091906060306030c0320100306140603010b03010e0c040302100915020c03030301180b0607030f0f030203 76
    0x7440000e00c00700c00c1c01825400c0010341d211110103050301101c060a10644c4644240d00e42c0e03143c42c058072542ca04501200d031030a8003490141024003042c4001503002076444140c121504101d0207542e211801207600344280c0d080201c00000100038402801740007604881c0a0100882c3c80104001d108021402c07106400365880050784001ca041a0302d04100d0018201c2c852904014001380602c1000319031194030a9580382d08d81003c0da600b60800c50980c0c820040502000d1030f05000307051075500d5002528000d4080a0203020343c260b100a0b50544c2c24581390010200a8109400a280f003000030700100918840c40040080054804015240540840781030b1401101024210303424200c0980c20b020004141c03d441890800002c005a0340e070703200000c80c2d01591354599030041e0038580d401c1165018181100c1c20365020700140c01040d54044140c0b0b0649075007080e040740304004911007030068652403140981006000030100c0c2815801a8012010b8126845e01c3e4485d0380da0704021022844100d070003 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 391861618 1250 391860368 391860373
    0x91507020409060c110f280204092f0f040e010e010c200c1309080d060b031b0702030a020105180a09060e0c03040305041512050a090201091205100903090b1801021e 72
    0x516407c0007000368000020080301140800d9284643c0458100d604000c0c060b40c202240400d4501d07182031450b030003007020301880c0704101241c5800000c00c05010548841034491910307440c0764101408254801c0901e01140402441081132140700a07100070300449000c00182d440f02d003110100da07030000d410090440064000c0c1200010720146100410028008a0302044100640600e12006000b1040a055040c5580d0303605d040000b0f001040521ba400c117080d00c9e08060010740701503030340402c84180076a0282042551000e121800449068000480e00d6000b4071441c1c0c0401c41083d140d0145050360356840c0030b4402900c580c00c1c0034590780011140100028000c2000b40240c10141c8640e0140300102c2c24000e50780011500042c003907079012514100c00303035030b0781c98202e05540c1d02884040041c0700e1500c000d148107205489454844120a103c0c0e0380c26a1292101700c1010b200348400d500030a0840d2203a51500c0c24884444241510180800d0040c0f06081000c050038028070040506030520000 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 391862868 1250 391861618 391861633
    0xf052a0304020d050f010b03190201050a0e030102130b0d0e072904090207080c070506041d060f10020607020105090706050703030f09080c0d03150803091507020409060c110f 76
    0x2108425500c01441203810458902e55640040c00800c8078103100303030740b400010903000f00ba2003d051030221507180320f07406280301401250142c0d80140864004548515058071500304203030200340a4820b0b40350341455196031000000b043d039191009001038103170103a0240316000c0484449aa164004c2c000c10300842d65984500e0850141c030b1440d02440c811004440c1d0501e50b407040f0160403078000490a480d11940003c02d051410001c0c00b4000142408550b860b040605003200f40b0080c000ba84008915850210701241c05c52303031010280e03040f4030402010700440f0810350200070340b13900f4140d0318980075600300b0001c40c0b907148010640005480c0076940b01801c5c40d4083d20120050050342e5001c280c250fa0319038003d000300d290f01c00200400c130070220041c0145101c05400408480c1c030541164024940502c0521460401100300c4443d0107040f2400c00803400703681e03550599480341041c0254002c1c0340007108030411903550850b030078054440d00c4030f5007059118820151541d842405001c3c2a401256 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 391864118 1250 391862868 391862941
    0x70f0e0d0b010824012d0f0e0703231303093507030b160e03070f06110f07060e28031e02010c2301150905060a0803030403052b0f05 58
    0x2052224000700300414010400c2d600c0d40811fa0410942e0000449800d00d40c080000060305030140340b142812002c0002481141c01c40381c21684400a80b9000c4000d0107604954249449000b81501a1030a07214981c44412181c601c0c108000030344c2110181c02c45804d0019081820120f42002142d03002101c041180d81c0c1d00b50b0250440c42000010390034002500d41c601e810382c60411101000d4102e54009401c010b09029001d41a0180c640c0401c00e20380c8441c81c01101c0e000007040d00411503005003001501d6403000d0700052480a11a07004000c01201230702210304041000c66140201c1c1c0c01000d074074005201c20407194040c691b07100f5000e40131844000c00840011078402d031300d030b262028500010401e90102089103095030020009641c28180105003400b030f4502911501e0b8001a08659400d46c0d986000c101c1900c17800300400c054103002c40410136450902052415011000304040f9000c011041a00a04014240c00128003003a5107084005052122036043c0400d444804000c010440450301 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 391865368 1250 391864118 391864169
    0x30d0c0c120c0e090c01020f0705010c06200a0e01031b080414030d0f0204170613060203130804030605040c090501081207052d0f0303070f0e0d0b01082401 68
    0xe401100c1100c03028000042d40c0500d00d00c0c3d90300a00844020302105100900024502000200c40198580041c10200300d0ba80c1c010200210b440d030300c0300c1d01007103100107148106480c1a1451301124900742c001070303041005601c81c40248244a007620b042000856000c02c0510f071403404d1031a600420402e40201c0e0128805040c03100703c5484803011280360803207100740002507426a01010903c16000719050100801ca000c8040c00c0096260050609240c01c10b00400130806000f00613203110740c0040070400031140e12400c002100c1d00602c00a60715070341c07440c280008100c119800e40d040810301030040362041d07490007202c1c100d649600003000031540b400140c109036407000d1400c813080d2040d42c004828402c4915505003281004c24104481c0c103d000d46007a0415800c0c0210510642041040100b500e8105180c0020205240b81c0400e0b80201c440c00b140303503111030f0507000c1c259000b050000200e11703030002544606100d01c0ca0300c001c540030a112854450079000c0c06010350380c10500141204c2c48145 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 391866618 1250 391865368 391865399
    0x115020712020f0a1e030204050a05071b0c030b0709080c031605120307060906050601020d080c04061116090516021b06160b0901020720100e010306090e010b030d0c0c 73
    0x3813215455980d0b88800081400f000103078018000d800e400c040003540f5003072003140d6000c0c805800c10b101501d841007004001040368507084482c002201c0d815030510400c00118800b5641c041002b40040c14009400ba0840d0f801c0d1003020740383d210701144c803061400c0c0854030030424201220300280e042d00b00000c00c01c031001d040d19403400034482802194007140003030050000c030034005d21002640d802d001000904000401c01d00d00248a0010709000041105504403421034515140034283c03402c810500e40d04005641034031009241d10041e021918615642c00765008000396220104421f2890308203903156501000700e11490034a00c2c41110403414040001c04401000706d40025019540780d9561482d500b096507030030b0f85a9800b00720036003000441002500d105655a2942c00948140800112040c1d62041d840341009200844d5a41507406600443e001c0c204289c0c09000c0b1280100c0c40c40e0080c035407084030520911900f81005041c1d4000c104a45003940c0000080300701c1410140c00d0902c4821 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 391867868 1250 391866618 391866649
    0x100e0616020a0201020c09071818060501050301030b190f090309080f0c0922050d110705040209061606020904020c01050f06060c030a03110f1c0b060c100e0a020315011502071202 78
    0x1241030b230b809d02c1008011000e40103048049100300255840c3c0500788204d0f80070390401ca041c032008000601c0855160260385a000c028401e119851340d441c6907840c005046001002c1001038180162841010741081c2c1040560325440d048840000d94214507940ea5400c840ca0f254001895402051010b0094a02c6103602500144002040400d640c3c9107840e20800140f50b070300041d03d4941c5011600020301c150001828111415403e00d2401d00004441e4030980c80d41222400e01149081d00700400e5405840c0940e100a10031034855405600e598044c220031540c2241c032140c5000052850301e401c00c04c0d1410180008015070928007000015001081108512900312000b40031480100440e240248021540c03880d0a044034420b1180d55415500b003103190034400e040601c100d4480b07a800141880b94402c100c540880e40319000d08610741000040f0401035018018440c814540c185024245412514800344c110000c0582d070341d0813030b101d01c032901905405824030810500541b0f4510b0003140541c1c03 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 391869118 1250 391867868 391867877
    0xe091b070206070f1712010905071e0e0a14010813080406080405190c0503012901031e11120a0504020d080a170a1b1b060e100e0616020a0201020c0907 66
    0x103890f21194191100d04500d200c0c8010009182d000611300d0740803c1f40105240340c03040c01103040103040544104c0c108035060b40b07400c0700d18682d00b078202c1c130a180f100404200503045c20b000b96168084100700070100801e1a0210310701d400850401403000c110402d402c2d400c0584070f03003002e00b01131048034490b0010704240d40c0340c03098503031004001ca2403610b40e1050364841e502d00051980b03004203060a480e88524004400a0b030a00c2814400c51011242c801134002482c2c005014121503034817880e0049140403402c10303a4600102c11604041c81b100030701001c0707101d1061001c1903494200480c15203604550094104241c0b840210008419030f01070842e200c0d460502d0b840400022040103820a0104c69407003003039403107084030f104508802c3c075806040780b06442d090803d00000001c50341081d40b51100140603d03602c0d030b5211003c460500102c0038182c0c0122051100c54908130b515a696041aa05500e4079054601030002d100e000242d150102541038003c2c0c00c00001010420008840c01001d00d414070 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 391870368 1250 391869118 391869143
    0x4030c050d0f06020d05040b010b0319020a02120d09061d030403030c11130501030c050105120f060d0f2f0f010807090911070605071812030215070e091b07020607 71
    0x103c00d0300250200800308040010240351904125080c5141a4080102e0500c20401e205200300300300d40c100c103540b134030712809641e950503a08224645483c150f0310b4003028002140200c108401d9402410f883da0158009103c104c00c5543c02305d0082c400308581030a42c4c1c0c001c000810000b40500300200040d03000b0352290200000d000d010a4400140581c03400d2041d0303491006100708010108400080d04007880e05038100b01c02400c6c51100303030001902028980c00d240001030500c1c0c0c0e621482d00000e9500c0044170b4200c1c5030600d0500504200d010804030200010140022603c0c039003000707a00d5902c0004e0000c2e00240800006460381e036005013000b410006501c401141c444402d000707101d070401e03016601c00e41d614114206001140d40150005042242207904450203c078036000c000d0680d542500700740c44c0a903aa25082c0e103041200900c01d0300c001d076400f04100210303402180181e4031a0003643d982c10250b603905030b1001e0406a071524502420420722561000d42000d40c05040360358071582c166030302d1 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 391871618 1250 391870368 391870373
    0x1d07020c04060801021b1b1e0d121d010c0204090201121b1d100810080d05032212050f07140a0c0603090b072d0207170304030c050d0f 59
    0x25554660403540b21690005001d86d5203000501050b9501d2001d0380150040a81140c40c2c5520425401c47c06403203058600806a50381d00141128603000c07100500c4050041c116141c410500e0380761600c9140840c1580c940c1614601107000000e121100503541c0381d8501a0a6082100034109030400b030f410800541d0403540c240c401441051103548090411020440c006403004049101c0401d030f014004030101d03003401072034440503149201d9820a00b45a00d55545640c0b4000e401c00a680c88440c0c24419011600d0500b0b4102c2c0080d4054030408000c4d440c10f10100350407005128012400034450032030751010240251260010740303030914150350881c1c684001074035145c00f203801540d42c1c80d03c1a0402c0c086281000900400c02e0014841410f0500441945450791801400002d02043c107212485d5515082203403040c58401600d22100403088018240c0c2c2c030002e45c0e504d66030044900084070100040811000081510120395111510300c0d40c290604081c0100780c0791544040f02e044408843e540c00 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 391872868 1250 391871618 391871621
    0x237020d0819060611010f060302150306030f010603230303190b0616050102040509130c230907080a050106020705060904020a0c051005060a0f0605030f04050c102303011d07020c04 79
    0x1813182e0703a41c26100a1090398410f08580341c6c04042c1005501d010020401602c4103103c03e0740480b03030a01d56503201d03030760180480d0900782020103812309940b82000100401044c102513005a1003000c00781c1c04501c128903012a500d20041d10505111a0182c005041144c2c00303401004803040d014028a081140031082685000030054080796245d4000c18140040c2c00c003a2a665801013084802c07400001107030320f41003d0302e0094003d008030b001c441074401d5002019001c80782030402c4003030511002480c114000404504066542060207030603c800016003134400241032003900c81c000e014520f4000c5000c00c000007503010520301c8080c0601a602c0c03801244052082d441241c1800c030011865280c0141040f801c84e0040d04994481086014148030059100c41543e60000c0c2200c1c0408840e01c5a08116103440c1a50b008254004501095464503691015110030b40e60301c04031500398074191030422058240004d02958902120555981c14070340082150260820580c0c0192140000581c01040 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 391874118 1250 391872868 391872881
    0x101a060a0201061503060302090a050703060b0a03140705090a060c0501062403060806010e040b1003050d26040201080f1906060e01080610051603050c010237020d0819 73
    0x405030750b40d850f0800041c90300c07065603225000c0b1450108000c0b0b00f5a8002a8149006080082c01556450004820502035400b44020b04000c0070403c3e00c407540f006008000e0980300c20900d15400115011840b5035009a042d5841c894008182a0807942019030440e004050503e09848a6490f0400010041046101000c03085005120703030f0707418401c041010f019a8510f9004244542c4000300400c1a5503038100c07a00d4120390f0040c00c40b001620740f09200c01c0818050b0b08054218040c110001d0340140e041001348812000740f04030840c1c41140071192000d20b800469000e800b0510724000581102d66020419a102c108500d9410991300c1c22512030003203032002d13001400422030644044c002582c001407241c1d0b0101c0211070700440c1ea004406e0003042c0380981d03245000030f01e80c1302000d0b008140c0140c0c01d03560b01c2d110b40780007152900703c100035008220040c59154420f081d011103100c1200c00460710142c0003404950014140d04105010171111004010204520721f032808018902100050240c41e = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 391875368 1250 391874118 391874137
    0x405100903260d02040807051c24140721020f1207170103120914150d090213091202060915040f020603040302100b030307030c080d020417060f0c0903101a06 69
    0x1001f1060070581403106244400d0014840e4100d00c409100024540350125603a070002d0118002074000039000d914090650711030712005940c0e20000308950241d1140e031001840c3e01801d8540000021214010100d00c0340b40d0742941910800c001c0e09030000c0c040b2415540026007071404107060014070100c4110094281c00444084000e03810405074036511092250260048070700e20344451040da0001050410b201401e5850103802099120038105240e004900c9240c02800300742c522042406110010960000101c2e08244010352142241d840040c0d030900c82d1103460010014034007820042e241840c0024400c03210b402801d81c08100503141d0304091070283e0300c41d4000f0058a103c03046007200b034841044107140a0350092240746c020940c0401145030701600700e10026501c12035424402e001c2d00c42d54200810782241c0c0c405194008000003012841522043c0a418054960b503666290921640ea14581d26510016410008461945c41414040a40040f203080301c203144021854a03001000746 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 391876618 1250 391875368 391875373
    0x5030d020607020c061213060e01020d020c070b27060418020a02151902030c090a08031c0b21100c020f0c0a0f0308031f03080405100903260d020408 65
    0x50010664040026403d860340845580d030410020b1b100044251200614030900800d80340624414000280d1002c4040d01c1810029507680800c101074201175409107100031914442c0f8180040c4d40c1d05450192690303065904410306008c1e01d8501c003450241c3c44540c64036800b040411002801c611412031340740702a0721140001d6212a0a2100030b03051906035090384423706a410704114001038030940c6040c9003540300c035005803a1b880308088080130740100d0303804a801c00540d11010400400000103402801d0351800f608840810380103800c000d6520302c0342100c0c3c10252459040c01d11950b4005002c003920074540c1101e090960822a103000d80301510300b06405038200d981c00d030540f035000b48081081d040c0290342c940c044514188032201e1040301e510002d040420040b001c50300c1c64035500f41c2d02045150b030118118070701d6107904100e03000340d20912589208041000c2010300060080c5d000070100d98000d00d6444041040851282c1c03091038084038100c00380020803010101305440d1020f44080c1c16031800 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 391877868 1250 391876618 391876621
    0x180c030114040614150d0305040e0708040c0801020a0806010309150903230705060408130b0a02160608060d0605060a05060408060a050606030405061b041203030515150f0f0405030d0206 81
    0x9004084480c08515024410300d04020040300d10b141d05c4088814400079240c0b0100c1c1c603040d0130112014000d41d0010b1094168180a102d001039001003c14000c6003d1655980c605644009035404c07031294401d000c0c0460103910008070958000d1303008820181c0214054000c3c450700c070106000b00c80c250b001c02c03004a5003c8884031502765403000c192200c00b5600103035074a40703415a1203450f0786040060009148400010760001124031111300500184114407686403118070201010f91100800c10701c0c0c2040840640c40040c1c02c600c654585405150b0107000e001c0040702580319480500001054260002400f84000415032118001000181024400740c50302e0300b05403551106962024042b0b52140d5002d005100c003080010071295040f0300c13140003490f9070060380c1c000300003a13003e580e0002c0301f144402e001c184103064241e00400d01c00e016040320942d040540000300440072802c00c44501c3c19040a10808a003002603600400c2c3d041e1400b000d0ba42810303950383c00207203800d5030282c507100107030020380 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 391879118 1250 391877868 391877873
    0x21909030c170606270a0902040f060302130507050f0c010b030607141206031509030a0f14040b1c020a090312030917160c080a1a090303180c03011404 66
    0x2001c000707805442e0b90b00122200141e5074540d50700300601458420b11454407410070f42080301e40c17502c2a440000c14542c04521345041400014900d45806a0040e03060000c0d0400d00680c03807058806482e402401008030311a000303001e10080400802000500100b046030459102451010b01761980c100d2001092000c42541810b0400c03d0203850304042c808019071500044030200260740d0341d100d51400030044e582d1240d0000e0f1404e103503a4081c0c5030010000e4180601800044024014200151188844001132007000c0702c80303880c82c03807181d0520f8600380000d0080c4283e50004000380541c17200d800c0030340054104c0d1901282e00c44030790300010419104c01081007200c54600540701c0e8070281020000c00340140c8078811031048084082c426600001000c0c0c1401e60b80d1511020a9a04210128480740c0c8814025603221039041c02941d848848480780e50102e14040401d5120325091005141140c031442544540c14001488048090080c9003807415151801d20030718000324418440c4645906090 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 391880368 1250 391879118 391879133
    0x30106140411090303090d0c09020d020301151d061e03090105010e0a060f050d02012003030601030b030a0c030f030207180621051b06040e090a0302010b030a110906010302190903 78
    0x80b8942a01c0505100311542541c0100070303502500e2040c0d17100841604c5030b20302151040d210760440c0c18040d20100d121003051849a000d14140e983c03070030000c0c144202d02c00050700e071b00107100d06800240100c007000810500740b2070f02400e0414950a02c100c0d8070202035041b185a504122001c040b50307950784004114035a00383c1035a0307811999611042004908210038180b400c0e50300c0c0a140d004000f41c000f40d0046900c030300a40314120f041c40e030041040d4641c03400761948960083d15940e00003420441405258030740403901d0f40101e07511544149000c2e1030f561720619100340d511401d0301540100c200020301d400000036281126800080002046800c0058010b103000c0c40035072401c20b241c444080b8000280303002a44d1000b0001c2031160080040c20f1100189072449260044071605503075106000c01c1020008071071700313020320a40080c056070f400c64050543d69401d00c100070302103d0110004c503801e410314114031600140e041c074025190003450502c103071422418004150015060740010014000340 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 391881618 1250 391880368 391880381
    0x6020c0f0c01080910020714010e15010501090e0105150c03030717070903151a1002030d0b01180303031a04061401080601050c071a07020a150324061d0301061404 71
    0x1d00705018541040c426465031404242c0403402176980c0010340f40b01b440700c000f404496140d0344500034401071603481415a129184454003181c070003040000410b0a60003440314205485944c1c1d103011560f860300041224448204911071480d0a007000b144442080a00003035200d90341e503446909420b00d6101c0d141440a0000b8405c4042015541050000454a0820040c005540b54001c42c4030a41c81c0b40814043c0003241080d035000c2c40900041007200e40100180c42d400d40404020403405a4620040d40c0701b00c1100c841400d02e00c0720000c1440000e000380d20075040e030104100b8501e10f4081c8800414200e4440c2d0700003841c0448051a01c1c0362940e44294020f500c0307803081c07920a00301040d0b4104182c1d608464020030f40810180020004e100f0600001c4e11001c81d00203000e01911540d400c41c01c110f001d12180084002070038400d4151400c2e019140700b80400751064055446e040c81c0082c00c44186110813052400005414804d0609070307000d00a54000d0818003000d00b003819004020401103880 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 391882868 1250 391881618 391881643
    0x50604170d0912020108060103140901060e013609020604240315141507060501051302040807181401061d0a122303040e0a06060c0b0105190306020c0f 66
    0x51996083c0320403445030340712480940e8282031000054450070016400b0f00748809496009010135000c0000c5204150054001c45404111040301071b42c0341c4d07007440c2541082084c9103402044404850422198048410421203c144000126a44a540003405070b0784135034005000781d032980740350440c44070600c0301010713403e00c0c18102080412010821145007841c68440d16051070b084220202040e01c440c171314034455042c070113a4540c3c0c1d00111315080d00209401c1c0606070054048401004c0740c6081c6108440507185950b00404d005c500d0003041c0940022240341d0180c1c0e9588540031500d01020026409000e4002520b85604580c1052400343e03203110a10400b0b4440c9200da1010000c00841d03800c4d01c402d691300002c5205040c100c0320004000d20300070a06d00b000c94070000400041c0007808031011809001100400e01205035100b000310740703502070150003a1468030500300421403840d100c3c0110040000d400a03201c1803a035203440c6c000483e0880c00007003e05400408060032866070600c41c5554402 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 391884118 1250 391882868 391882877
    0x20c0901150806040b0f0d121103071a0601030204091d0d05090a050409060b120105010e0a0204270e0a1a010909030906080c1605150f16120204050604170d 68
    0x8461100041241d4070103000503010781c1e520245c601481d280d41c0340001220501802048048606180c240032400c01ca400e25000900001d81c0c19814070400300c1241c8406230000f0044030241c00e0154602a90034018006506151b0b0030080028001010300a0f2210090100d410f00c650740109825130f03041c40c0350032680d4004c0150402c040d502e55071781c0c090b110b025200240c500056031038080c03030031100510f4019140c50340012109103810040005400c01ca040c1c983c0c0d1070382c038940e5490b400240c2c4244d010380d01880d410541c908841d034000907a100d40640130401c60074004180310014081c00340c00c2000e22501500c0c1c0c0150000c00c0d50381e15446020031401002107d0007004103c00c1510000d081d0707545405420200150000458150300050040d01d18611580d902600d8000031071403c2991030449131742e01c0b900000c0010000d0524240420840c0c82680300e44003a0b0508080c070413007110880b100b15410380c2002e50a000202d880d031240000382c0050f0694204625283d80510f603c50301c2d02034481841000c00 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 391885368 1250 391884118 391884149
    0x9030906090b1b01090b0f040c08030319090f0818010311040e1303050d180b07030b01080115120509030406120b0a03030507020301020903061f05011403040f03050c0607020c0901 78
    0x20403200840c0e41c0f100c00951107852592100e001c16000d4510154060840304104080c4044001411001c501580c450044401000e64406465840380400c6402d95044400e255020380750380320542040da2814480c0c203030242004c005603944112500000b140c3c000e90700e282d052030441c03540c0500ca2401c500584001c4141402c0c070b058004112003500800c3d124117821510350400401d0300840a60300850702c110010b025030f05441c0c0400e023414003810410f0fa415911540443d908601134400c503e44110180d68100d0680c0c00c00145441410880b0800404c01c40206e640f548030888612680340903943c0c0b440a99940d914001c0b000340500300640b41c00e00458038040440758a076070f910700001c0850b40c0c1350421945844e150700000340240113004020740c00d4001d00040049840320079442d0f0244078034503000032102c00d45410045641d031080d9094a0200c003c00c10200c0d0100d4690444003600c58800d00e0304c0e40c504031808150134105007041d200080541e0204401518610300301042e24058284002e003903104 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 391886618 1250 391885368 391885379
    0x602150103050a1b0312050904052a09030a0602070b15011437080417040605040e0603010b12030c01140f13140a0b090c010203040e0a0b0406180903090609 68
    0x11603243c0800240b10038a0032a5004101c40c142411a000316000110760055084090015000358018045284241e00d00030008044000840001c0341081c08002d00c00c5030007140d2207002d84182d202e06242c070303450b02c6429845c1c0e0005130f560004000d514030440f0310f548141400c0280e50441003404806071306000b0810348900c41900301c0d2003038950a00300c4102c03400c681d00b02c2d00c06450080c00c0003002d1725441145410128407842c0c0000c4094003a0744111850b28014a03a070301c50f01c8440c000c6000340000208100f1040010180f003441050708848010f00000b2111294400210000ac1312540e1500308d80010941e666401030a11402004080c03102b0f00040720300d08808186544440101a421050011400e0009008080d02c1c0c00000d000b080d8200c0d1440134090600805c40307801114065924401c07051400515480841544c0440c0c0010404902585947c0e001d500989403410035240c01640d03070f910014904403001411034441085240008602c403807401e004003a107050740c110701d00380301110008002 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 391887868 1250 391886618 391886623
    0x1a09010518011b061506021603150b1c0b0a020304031407051501060c060b030c010c140a0804090c1206050121150902091813122106060215010305 64
    0x5084a0400c5100e122079038480140e8410100c02810b45018850b00401010000c1c103511040905a20740104d1801507602e00c8101d13076139151005038140c1c14034024070401c0010680720007aa103d4440300c1c40230800e00d10501c0031843c009804883c09040201c2c417084034041c89400c1a0307458016031f140c5029840c41c6400d0701c02900c103c003905400305101e6000540c50b418081c09205e011088036a201c4484c480b0f503911000101145103010b803d0700c01da80303000a215058607000641309403920f01a1540e813089140380d1a811a440050f0546070403a000d019040800941203900400182458600020b1281c03020790004107298401080322000c1440c121b014400350f0b81014200008901c40c401243c07005216440200c040c0228100b070008011005074080340120319500034082d0318a080c0c410303100c010f0702117009280c611000e0f92121412200b0340c076014041441e05402029000042c02e0015450300020300030090074450071a0300c0d118903a214401e0111360741c18044681c20f550bd0701d160300300650440d1a01d03034 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 391889118 1250 391887868 391887877
    0x40b030103020907121a0a05060c0d0c140111030a0e06061e060409050405030405120607050d020a0302090603190509011a100e0d05070e010f0b071212020708041a090105 74
    0x74801e002c40f40c0002c415070311411210a114106010a1020a00c401098101020320b502543c1c400c8031280c4002c2001e0030840c0a95404408440040120301c0d0030441c10703181c2d58010041550520200c512a0000e00424040d0740100700600c0c6603030b556440e002002001b01c17141c2c1c1d08000340f1070f0402010f000450b5200030314034100e150044122444449100c0000705244115402803d01340c2c2400204400d200e40403020b802180c10a641d4400018440f01d04030b512010203c0342a03000c1201440341403220360007a800340980720160f045c014903145110700020701540045902c0c4c8102820145030482560aa0043c1900069554000d0102c1d51020403209034104820290b039020341d80000d00000c9551061420f400549000340003c1c80000e46420300310303101c403071900401c010300707800d0400002c0c0d204003182048120394903e0402828088240c2c0d60000d1004014040404c119100765403031520402c0344000c260307051050a2296440c2d2404584112500010261802c809410300052407566000300449 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 391890368 1250 391889118 391889123
    0x8030c010b0a0b1e0405191e1d0a0f0203090a11040e07090b0406150c03020c0d0201090b0703090f09020405040605060307140d18030906021902150c0f120a090605040b030103 76
    0x40d0316504d01a485041c902035544042d62000401d80300f22412520030070f000c015201218024400807400941c00014200540b20302e200050786074056811007585c60348500d42000641d1000b1414070b60905603030041c0d800540e1049002c1e00052141d60030000c440703c203038010b204d0640b07050100046440110303449407454451408178640b42c202840c081d0b51154000c20150403210541c20314102d1f4460000c01ca116020001c601501c00c000503000140341010201444642c1690b41407640c0d800e00c2022422900814000c43c24071400400106082d11025422406041421401a207440c40c0c84108002c2e114550b001c40d00a6034104140920190b0003041c1c000ca46556036035142c4d0751000362410310000c7c0032140500038070b649001c00c60820941d0002500080720011307030846441080e800052001d01c414004000d601844002e001091100708030f003c0e2025060170020f8440401c03000071610304120440d0341000c843e480014948480c0c0e500010001d018100902d00b150516080580b0351f4028031041c00b01 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 391891618 1250 391890368 391890397
    0x601110111041208040503060106030902150408030403030c060902030a15060e061c0206070501050705040e0a0e330405010f060605180d020d0204020d06140f010c1b05060408030c010b0a0b 82
    0x340c07024412103904039002046c0107800c6031129030352110010000c00499030b0480c440c42039001c1c0b001e00c0c0407410303080c0c0d8240c80ca0b0201543c6001c0c510360f400c0d140e40d0442c00080f501d9030f4841d14044050380d000d1010072090340c02030002009a060034070201c01181c000e40c1180d650015440c041c4109901c0340c1005c400d100081e052a810248018000101d0500450f040104a5800d10081020300c6038444042c10440f840e49260f01d500d0388668805009582c221090040c89a0040c500c41642e808000024003041e601c0007070307540b1100d20503908018683c100721800d44190391030381c4140700c00141300c3c8602e0008101c1480c0c1380341041c41c80c10301200c0c1c8000d4200a28460701a01500500b50754608100d07070500da07030083c01155900d03044140c0d08045c240a10601c01d0910800e04030101e141450074010300721800c16035507144034080c00e0752120218010b00c0c03c0d0810007003a0140c003103090340f9600024009012034074019510b443c296111b09080d102900016030042c1c10208042140e00d401b2000c1e21500481c940342c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 391892868 1250 391891618 391891649
    0x1103070b2d01120203010b0402070515060609030307050f07050405010602070b07170c0d0905010201021e16020306040b0f07020c0901060f0c2a05060f030105150702030a0308060111011104 82
    0x240450944150010840400030740000945110000302c000700c0c3d140300b0307002840100381007000c00c002c901405801030083c0d0024000030b01460441c0302103590000340246014142810710000c0392454100000445055120006200c0d11201c00c104240080008440070b110030341c1410741c02503c40c0c060784245210302ca4041035010401040308260014207026009040d01c520514012030fa80745040a840e40c0450b0045002103a554410700840b400c03010402086056441480d441401981c010314450072221b071240c84103401070b90f0030b000c241e0040b40030389002411810030280710034a01d0b0b009881081550300985821190391901d01c40309045420303506025500d40c44181054070519204c044c0148010070704980101c80341490400d021103400803404010b400e548483c280700480c440c0c10b03003444202005000410240c54200c52035000081d01c010f03900c3c04c0802560120b442c200b00d8990840115141004100c01560b100144400030300810009100e94903015040c901d06114a000b025115903900d413 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 391894118 1250 391892868 391892911
    0x308070210091508010e1e0c090f0a120b1501020a030305251e050c0a0b0601170a02120f070801062618070b04140d020406031a01061103070b 62
    0x2ca000182014085400c540c0041c00006001d034400f4020000381504c54008514982c05d030701c03080740032030f200414800d009442c0d0000d1251181c000090081d03008000c0101d4010175117502d100c4000400c0ca03803070186400c0a1524042c040007000511170080c400d2405007008041c4c0c0c7c00105504203d4060030001405e44400d110b459103168103104450000107089000103070190312040e582c0150b51000000803c40c080703444200d409100c2e0191920f0a42c0c0700038043c1012500c00c0003103c1d04075005040880d0081004400308400740341c101d5490710ba030340d4046940e450451443c90403d6110300c030381c18480d181d441c208034003600300c6c1c0d018052241009411070841d107851910800012100201010300d81d454a0800f000010282038480c810721103024840000a1800c80101520181d072100c15100383e440b01d4281c240b0001d0301600500f80d030b200751502d1700040459000084d0300451001d0303102d004455818048082c00d05080404500c00740e600401910b40440e03a40d00006030410345078a90064901c1600 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 391895368 1250 391894118 391894127
    0xf010e0606040509041506170705040e0312010801020405150901233f040812060109210c0e06060d1113080703120807090605030613050109140906010308070210 70
    0x43d04030380d411618079010702041c031220342440280800b4105003801202c1d21181200d010081c01071848549038800d6506100354a03041e00490311a035207640880e0b052201d10341300a40868001c0e4094010f0781d44c0086c0900060070558000c0c0e80078886510018500701c403480c0028110380038140101d83c0000f13888405202c0c50309040888400d050440b081e2441e600c5001c1d05448080c024a940c000b01740c0190741a9550502d0641c0c402d48501c0e0050545420030640740c899210340700c8000c190038104020301c0004030711800d800c0d0ba00900f00713040c001d99007401046460490700c43c00281d042007100e04080000c003c000d03a50901200c840f1000d001c80402c0c011624510100c035409424840c0509045445000c1030340000014428210f9015080003000001c4601c1c00361160300b800d40b44d940000c4c1d111031040c880b50f070140c401140c02880152980d803080c01185481c40845100303802070f00140d41c50303074035040d8446850b0061607000104000945465403442d625882a0320401100134015a8041c096641c0c0c40d004 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 391896618 1250 391895368 391895377
    0x507030e0406090605090f0702030f07060e030703030504030e090c090f180a0209030d030911040e0307020a0b0c07051f0e0d051009030f02010216020f0406031e05070e0f010e0606 78
    0x280c070a2000d0754698079410702408850144900070608a000a050f03100303a00324042c0a1081600650715014800108503803d03031010505844558407500ca00c0c0782c1960410041c07070010b020756070000c1c050038103180040c855a101d40d60f0510a00c450350601290507580421100050000ca0300074000c808503002040c441c85409020070b800c0c5045508000540701c990f001001040c50407015104500b800903015411078145182c098400c6011281810359410141d1244807001a140104c80c2449642d81c005010120590000f100b00e00d40410340c400340c5442000302070301410086601d02420f200d481030340701d0b1008140340b0b84070030003203400700c0900c2c6611400814110340340c0000a943d40c45100900401c0600001c2e24200c000030030b10a07440d40502c0c818400d85515403034141012400312455002c0061108824082c0703a8401d50f516000000144a042ca1451000c1c441ca075007110900b25081032420140039502c5000359048090800407100110003165054403800c1a004000c0d841c1d01d00441d040c0d004 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 391897868 1250 391896618 391896647
    0x901110316080f072309030f101d030720030d0c1106071101080402130c1d221e020f09130c0e09040f0b10030b0a0615050703 55
    0x1000010702200c00d01a202611120039107031503030364868441034901031140000300c600790300003440d80b48500017081498000b5a07a90112a040b1810048030b00c00280c20328400082c8558240d10040d514480c00c0003d02483d02c0800001800030040095181025143c0c4151781c0c000301034100104030f80b1024a0940b220b1180d0000c0903048540320030a00d20702520300102642c043e10010440e141c2a1035a14040c0700f1502410760000d4602138507040c4500560b04114040c0c001c03a40a55045007480d15400e0a00c10b000c00855284d403a0528507861000308a21445a0032800e13004080e2408807411a41d0060140d164016034100e00041520612042d540200046240542c00d03600019414599001e400d010708940b040c1101d481040c11110481c80080b210b500c284040850140390400b0f14a144c6055450740c0030740150708507110000113a0b540150000120740c5030441d074041283c28400d00c448500c0b07030303070303010007203130700c00c0250500f030204280400d4000d6907a1b0702080b1000602200f058403032985416408c0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 391899118 1250 391897868 391897901
    0x5060903070605010b03040c050103051b0313030e030a020a0e0403022b03051806071206051309031b0c03080c010e100e010f02040b09060c120a080f1305060c030901 72
    0x4058140686a612524069400c0e03070500d030010601140035030850380915030005800c1d03456460000198040d1400030106d4120800700c43e41c075029030305058011403013111002e1501a9001480c030b0060301c41c042041d10940607500c2a800c50b8016201d40359881c007a140d541400310700c20303078981c038049240044dc6041650400340c40d403040c0c1403000c2c84c0506108112456102488280d075103402c6d6020000d420381500e11750b0760215011501c002d002c2c1e085891040e00100b0041620340d100c502050851281070b102407800d650b20b00842049c5680075042e0080980f40c280111114141a11043c243c044140000740184da40020841405902580f241040c00501c9041daa01c0301004850080149001c048041c400d5003007804100059080340700719400d0741c92916015007440802802d00c841608804003c269074031843c0040325007a40300c8000f9060502140c1c0e98440c2e01c1c40c0c044200301990742c014010388456420070f40e00341c0000c0c0d004107950368495407086040d83c0f85d503a4501d1107800341c60b50030f15045410 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 391900368 1250 391899118 391899121
    0x122408161217070b06090105010e0a0e0a0e070807090c1103090105090409050a0605060901060c03090905100302090405030d110a050a030504081306050712050306091b1c090b0c04051c020d0506 84
    0x40304c80c003452407080c0c10444010119a03a903000666403082011041644a0729881d014084060344001241d0042c0310a0000100d200c8030905107468000c00c0d80144009070311282080121a025015000d040125464610049066800e0b516030724050441824148400402c541a594031103a0201c50419080300466107820450300300400103000940d4224082c100b01c0f0b0002c103071603025560040305180c0c10394800c08018501036000e0000d00000c2d081c600c0d05040c000001004d40d0f80c18244ca03000d40c1c021009169030300030318240d034000c444405001c1c0700c02540c28044000c480b0380083c01d48580384854100840c0c01e079114901030100b8850a82d0000c000300c10f0190210341c0d180d1040103410090702c140044001d0070100c020948590108480841c2c0c04443c80001910b440c41d01c0d041b1030000188607090710f0800c03128503000000f589119149001455840c8039610a01003018441c60300841c00c110618034041c140004511012841c144138081d107030019000350119141c0266a030119500817068545030b = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 391901618 1250 391900368 391900373
    0xe0105270406060f0e090618070503070810030c2607060203040608090303042102031306030b03010f09050d1d09040807150b0a0e0712240816121707 65
    0x90100311062401107240c480080b441600078800c3c10001242c0381c48240e50350440c1c40c10000181c1c0028071164201021880803c006044d03290894012002600c4080d06c0c1c0c44c10308401020b410000344029111203600d60100042002c91000409039899480b04a480d0a00c4121183c81c19011590100c400e100b440e4000840075408400303001a00c0e0b840d50381c0c000c1c070b8036014040341d624002540c019000040340007101c1402040d50403100d080b2003841c01a01e0a100d0054003102c1000d070107900001c0404d031580e00e80003441c0b0703080c844e00e1109091110700300000e02c95038030b802e5614000102000c01b4000031501c0009004043e030100f4620300e0b0020540300f040e01d41840c014a594000b841c08448100441c18009031144031130007a2005240080d1108c40028034000180c141c580c000b0309801c0610001c500000504102c034000c500ca0081c4e01102c62400b0040c02040a00242e200c3e8400c4507150000e518080c0c400049000050445185468602084400d07044c6010700d55040e410f8550701c0c504c0052081e04 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 391902868 1250 391901618 391901677
    0x60f050f03160c1502041d0103020f04020a110105090615121b0a051302040938040e06070207080714010203180301150303121a03030910020f0a030309050105060303090a03030e0105 79
    0xd9072049140c0c070302041540c40001034605c41c09e00000750322201c000100c00e41c070305042e4003908074071940c4d03d08029a000c21200d06421100240d40c14481c40d0426010003181d098110024140524150391900180038603900c456202c1c81e09503c00307071021404080c03805166541d84200405080c1c000c000000035a60f440c00c06000798000d1040510490030032000420040340420140e50340c00c6024a444c01c03d0368a40d0b074942c0c0c2441c124641541c895602c0e4030041111400300300703640c892440741d0001c0420f2400c010106192a40507400440e003400301c00e0120403903980c0031003610101c5c4134030345100c40820800c0001074050f24140300300740391203001d80c1000014035510010301e40f01c418100d4420441402c040c07011028142900c050709806030710800065001c0c0c00c0581624400b0b10461056400507845902000c0c146285550180d00180c0c44000d03c40501000f8401d03103070005404c90007075160070b9400e000300d03685030ac00f840084c06120b080c2d032034008564010011a56070802c000144002c000c000c0081e0b0f0b0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 391904118 1250 391902868 391902877
    0x23220512010e07060503130803040506041106041401050304061b050a030e07060e0607051c0201140901061208031b03040f0302100c0e040c0215040b01060f050f03160c1502 75
    0x244180c5020540c8a08804188501049072070b1a101525105081241c1641d0301c0e0700250000c111585a41200000704051401840c01148103901600d082c0c181410001d62410100c034581c0d1250000300003c020500c000c0142c006481d00031300b810f039241d54541c10a40d0081601c850100c0041c248031801645d0349030310000910f0040041e4604006100c03045500325a80d40941c010344010403128440404e0a14050000c3d114846c810030807103940d0a4442d1264000380d40020054000d0307074440101d5624244140d00c841c0d03001d0b0010b4001c10416150030b0307040403851080034000d010b00400202144010b0303e080c0040505100000002d95241418900441841c038082c01c1500140101800003e070488036005101000e491980d0b0031805501d00c030104001404180c102400750f1103005100d120340c2800e85000ad00c554002c085c104440e6240040242c0400c510001580c2006020808851030042d1041601e030446c0450900c842c403092a00800e480d880403150020305500e18144e000e09038144641c0050 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 391905368 1250 391904118 391904129
    0xe0307170f0d031e0203150105070503160305091c0c030b0c07060e0705040614010c1106040f09050a05060a030519030e0909010e0c06040506040909051e010b09162322 73
    0x3407400003107040c2d04d030490000741c0310603241e80752004441480350300c030700080c00c0f2643c0501d094900c1c04c03884401180c0c0b00c00320302e10128042440071480303100b103140c1404071034064007640340c000c50070000540c3d4064007403203d4000180b20286000210f800a0200c02c02e42d03008a40c461401c0140420b15501d695981040e403040510903800d0043c046105000007541c42480d81c01078607000b001c890740d5541d2030f4106400c10b00140d041075080c80001040c180b010034060081645000c0000c26040c1090841d095070001051640100c8803443c0400c0050340018400181410602c0e0040b0350644a10f4110307007808034005070a03031155440040c0140c5860650001c508100e4038402c0340d90201c00181840090b00651082684c021824002000704032020781208003ca4450000e0b12150204034186818502070400040f03d583e542e00800c06203800d000c0a142d8111020b8201a101c04200307090062051803140c0388020614000340c56018540d0700b0380300341c81d2803242681000300d070078503100b003480745251561040 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 391906474 1106 391905368 391905401
    0x30606090a112a030c030418090c0b0d060504060602070e0a0e0307050d0e03150105120c04050a090507050a0602030406050a050708040e15010e0307170f0d03 69
    0x4040110b030000f150b4110309410190b0310310384803078802410f007280d204100d61040c03402c000040d0b44c1190199825080b80c80502c082010150400c2d000c0140103150703142010401718118805418580703c6440c0c20040699188104004e0b1001d0348900d45c0942c020103021f008200c822100700398026204840419804480340010707182d540a01e1042d2010f81110380381c1003d4aa0028507000c003000c049008254030300036811140c0b0144810700c1442d203d4074030010b0303c1080c60014000a4135411b00104100a24a0001a80805400b0f00141251240038100c0040788a00c0c203414013100751034140d4000c60034141001c1f425035203035004802c000d00b842018047c90000811200090014200c43d4941030030500b08070500d04443c41640e072046041c0802d210010460740c4000402c070084a44031f100181c52001d0541c64603003003210700000c00c1828002d00c0c8407250481d030150041c900c0042c0002c2c1 = true := by decide +kernel

theorem cover : BRFrame.Cov 391726618 391906474 := by
  have h0 := BRFrame.cov_init 391726618
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391726618 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 391726618 ≤ n) (h2 : n < 391906474) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
