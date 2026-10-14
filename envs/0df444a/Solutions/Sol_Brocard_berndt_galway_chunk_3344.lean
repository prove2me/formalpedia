-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3344
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:23:15.776555+00:00
-- url     : https://prove2.me/submissions/12aaa5c1-b9e6-4f09-a31d-242c82b2fa96

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 601258992 ≤ n < 601438848 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 601260242 1250 601258992 601259011
    0xd02030a121a0f1207090605041b0c080903280b0601090b072006070506040302012301091d2e110d0510050301060e0912090108043509040e0f0705060715090b 69
    0xc020402c0c070146407900c0c2c1781d083c3d90040bd1452000400081d50744001e0171034204001c1c1038032a24582824101c0c3e001c0019404482d98a10701b590020401801c103000da41c11040a10f00f01c0440b90034440034040030b00c24084040c0900300c80c0d2a081c10b5000e818807407003c030b06a020b4517180d10740300b581c5001903030b030401524220055424a0b8010082c44a011854401c0320380c0300c0481640c992130950100028010f1000c03c0c200d01600c2c50546c0d0b00340404005854545654000142c95071852590440d10740980c240341514041c10105c071070944102c4d100648901c1e404013800003515440300c100b40300050104c0c1e1302954140d400c20304005444c0403341c03102071251110005440c40c8400b80c060568180c8a00c18001d8041403413040840d01244080040d05202c80810755002c0c61210b90403101c00d07041c20b01412121410a0004034134600c0c0c10240616012840c0c0100244a500000440c86484108030701600d0b0161501180d05024800d1011700c0c1c1d81c002000b050704009800d001d0074100c40c15034048406000 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 601261492 1250 601260242 601260251
    0x10f0b04050c0409051314100b010503010605070809030a021201060305010525050a03020c0303010e0106110d051c110f03010509010b040609090209030f0d02030a121a0f120709060504 80
    0x2141054014180310b10b01490449290904020900d40107000250542c1070001c5100584000201c0d09110540008070074001071010300d02c0103440b10140c0e080107000c2d604004082c001045141d41003010703120300035800300f100c4c1d49030401103000c40d240c20380820300a988040014101012804107600031019240103a00070b01a6130344968010701680130000c8020051014000e40d240c48900c1840680f040b18118030b0003600c0c2c4004085c04514540080e0000c003151220480100041504030883d503050f01c40c00b0010341044c0c0c051040140c0180204000b107900d810f04d02e44a40182403c59025645510103002529102c10180003142401d410074020b06019070206400810041d008005031402c8540a41c0e8000c011420601050041d4028102803505032182c0950a0134081043c0851040000342c0e5000b151540c507807600c000c0c003980c80800050300c0140740ca0284203074010300e4058011800340c00d4a0240312000d092000c22030b6030300d281d0449841e90140020200700440f80380c10140484108480602 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 601262742 1250 601261492 601261511
    0x2703030906020d1b0809031f1b0c02030c150d110d0c050403083f06010305060612040206031308030a0b0406060809190809060406030f0e0d051b1e010f 66
    0xe80700041c4e00702d45011030429801250024102000502e000c907005416501442110f5610280001c40080600506511401d050540c3c0318802e043c80c80c440707a14501408900d18540109880e100300003030580c01000c0c0c450705203a101500408458081c0540c0c901080000310301c3c0400001600440b001c82001c904141c40c88641d18403030006e44090f250048809403800520b0103615020b8003603102444500707002d94859a04020a00d08156500341e2501c41482d01c0d86003a07000181203950040c00903106403014808101e032403400070440c46c2d12580c11f594a40d41d9440e5841c14014a0907034000080a0703503000010001d410040e41c000143c00e03581590140003194860034241c401d404101c804c2901540101c60803110b9921038094508958020b13101145411350b450003181d0385a229800a40100c1c0c1c81e85250050100707203200d031a18086d4100302400c1c0c1030303807440340c01030551040d250000407a108013070440c1c81c2c0303500a2012604074401d5440e040e1030340c40580c50003406040c3c44032585803100d28064080 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 601263992 1250 601262742 601262747
    0x170a0e0a151409011b2004020415031d0105090a1101050f030606160204060f0f080a050303010608100e010e09060702010618090c0503070b0306100f0c032703030906020d 74
    0x1841d030036140c44440b020000e115040c10303690000c001484c1000729044168030400122014a0107580c058034401280d1044000c0c9920b10703284075011030b4005e83c4100f008000f818012180401e1040052038081001203048070308642082035846950503551800d418070182c40c0c1c0c0010741c03680c020b105c1c0c0030800907a1074580c01900c1c14003c3d82040190030400300001041c80c6410340041141244140c0080e4003a145500402e088801942111110146040051098400e00c5d504d5030010000c0000611040c60665a181c0c7c03640418403442c03081c4490000032450120b1601000c4014004038100e100e85903a450207140310020302911101e085006140114202d01e00c18091030f0165643d00000200c21030101d50484001d001d490070603a40750300d810202003070540d410310106000309a455220768481c00c0100400101c1e02d160704038603051042c4004a00185600260f400b403000f60141046403250f12030303281d50a40c0da000400b4003040e25940020200406030009107075401c0e10001e600302c402c9002400c40030b = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 601265242 1250 601263992 601264019
    0x3032c040f0e1e0c090601110f03030a06140a0308030606040b030c043008210f061017011a120f10050a0b04050607110a0807050102010b101b170a0e0a 66
    0x2503d00380c2c02140f0100f80781e0a082c440207800503010f00d0054004140801d085042136001103499041e90400001d02420704001d0058030068000c0900f0707081d100904200240a5411521000300700e8100480013607040d90b60034094600034181061019a24580306400d0703000c0c0c1e800b0740517020303600d0500260059410422884883c6494a02106509030411b0b911a00b041c1d400c851040d6820060041143d003c94002d202c045000f001c0090a9617000d082030302c20400740a040c800d03044100070105091090f88200700540300d04503145c2d903220040b451100307080145544542528000c0303003108001440a5542c0c1c50240c50703c00c0e4090407640c0c003180e403a0810000c0d61040e52055036124071003803009200a01e000001030105900c14a07880c0071402414001c2104410710740d0000c42180c00c00042084207503020301401199807001c03594141c0140c1025800b40c03402d0241c044074910020244007100c02c1101800c40d174030302c803000b02141c940c860010707240086c60494507800079401994014800a0103a091211 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 601266492 1250 601265242 601265293
    0x31e030e030304020d021c050c09010b1e0c070510020a03110111120c07050106060207060f021513150612050106090c050304080d060308030a020304120903032c040f0e 73
    0x1462940c1c07280d808119480b00c2801040c0d0344085001c0d03641894401d1002e07c0170070944280040d10206007140200124810168440c1010710400c1003050045044a94424071140100c00e48036103c659000702c1302c0c50040b8542000b500b241002062a1a0503000514400b00c54403965030341c02040c1042600b40c1c282c0341a00131302d0755400c0c400e2010040120819152030782c02000c01c640c0394181100d940b078550968070b5683c03010025130400320090098a904c01c6503606401d507030340000c2ca500a1001815080c0450050a514013030301264100e80c00c000c886112440503514000083c0401e039107408a54407126503c01c0c04075119840d101001070308908500030100c005031542c46d010704540d42e940740d00030b0551203008558012070b5110070100015490701c0c00ba600800451200503103a00e0300d40342402d070560242d090001401006481003001a900c0f0004591007590840031010301c02c04c0554050b004944080c442e94400c1c1001410a403200e690360101004241050440308403242c0c20b00e00c013124200070034 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 601267742 1250 601266492 601266521
    0xd0b03061312030b180a050402031218010e042912010608070b07050a050a06290907121418010501121703280605011e050409050c16031e03 61
    0x70b01ca18000c0c0e02950020034078000203081d103030701078039100540511400300310358044015030b660f801d0109600b0100070078004c0000386092245800452500c3d01c3d681c8800050150412600c809c44085039159a00150000504442e000c0950104e5580c62090100660320349802451411440482d403407050203040308613400180640300e90b6051448401075544001c000741c5061152200010004504201103d02030b4004d141c0026002d4070f1461a03620101004084940d250103d4042c044546d1030b40c50068200382d44d81842024440400b40810152403a124a415240d00d40000c011440082c03c0d07500003030302126030003084180c0c0c88000400d5850550740300a00300300d91541c4020001c01c181c0300296001038031a0384800c1c10300c8180031780c6c003840d08014200040858039580300304955600400307515042041c0207192a005650400014928051449401c6400f522003021030751000300c0313900310f0baa00541d604281964030031a04000d00a14592a20403288035030040032040f90b030f803180c800c0c84520000d21 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 601268992 1250 601267742 601267763
    0x20303030a0501031b0b030118020903030c0109031202030c090d060e011107020405070302131202191d0c0f07080702150703020d120b0d11031f0f1b0207030f03090b0d0b030613 77
    0x9d002c038601c0740d1007032407211021a0308004005483e0340409c0580700641130800003045100380c91800601c06103144662040d030714014000d0150800c1e822054610503202039400803201840ea0a2a1024101c4240480219481e00c803501074003600b501c0041900c1da000f9a0709000945403688210124441c0310384029100c40040c00501806002c10004c20085000900744a4514440410072503007a21030303400412604948000000050248034589a0202000c2e0003d800c0c01801e0f4002007a6100d54075004040200c0051484110358034002a000780080141601e41c458070140b8001c1c2d61200490208008580030480505004046028201e1581c00c040c0c59006102e4603556802e10f5904219100765160007107842c140c0e1410202d442c00d188244000700080f03524071005502108550f0340e04009104940c00b1030288409a40001d0303048100c0c1d5000030381c0780e003140d0310382030480e540101034020310500000050456040c1c0c020746c2100514100450a485045d03c50801403400e000c40401d0061032440c00d07 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 601270242 1250 601268992 601268999
    0x200604030918090c0b07050d0816140f0a110609012c011b051e25020109030b0c071a160f0201020403020a12034107020303030a0501031b0b0301 63
    0x700b0700e20201e00c400b19201261019003641e0b0b0b1400741c034042d00204102c400204141080c04810007030030566081c90b0a00c0300345810114a644a40c0001c501014203001c2c16980b1004418040ea0441e4201d0380182034907503c0d1822441c004180c5140b030481c0043d20301c148400704070b4144041c441d02000140d07003404910300100c145405005c0c603480d8000562155030b1001c1511468a40310320b02d400c210302d60303944c4540e9819228061520326842080c001244a824003100c40d00c49403950b828642880c1d418100310410189100480704081c1d2600000d011803028000e11401e64002c0d80601201480b82c1d40c4401808403131800d0002c619012103a20b1712618546483d040401c1c007a42600e40c448080d4400540f8240e00c0f50003180c07032850f00d944011048c4d40650038050500d50303c500c0f41d0000ca10040c954a01c0f1440d04402d5103114603400503560440745580c0c41c40562941450100c0300782d103901505807034407882d020200d400108800d01c02594220703101d00c4800c2003c11810000301c16145002101d6007503908 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 601271492 1250 601270242 601270259
    0x9030a030b010915080403081e15040908040b0d06050f0108060f010908150f0c03010308191701030809030607020f0703060e0a0f080a0e06040b0406210501062006040309 74
    0x1c0844510b4188200e00c0c0703000c03500c0e524500640e04084001c5d00d817812103083c0f5240052900f0070041c12107002039148800f02030f0441c040000150803401484081c9048512080001c0042c241c919004010600004000481070303091b001404050f245e03c101081a1550f40051000400d2045171840c001a10b02d0300040e11881d180d04c1c084404107040c0742006820b926a80c5003440d00a880b800e1094052105040205d500b59907841035600c0705545880a085501d55556400d1500940340104e13440729512000022551090a05013061a4850071a400c0741d692800d01c0a560741c072110006010340500e50020b07030031a000040d44908081c400c0001c004491070340d03c41c00010207014003600000e00411011070041482c0c1a030004626001d001c5c1c2543c1c0b08041c4030f000e480c0d05079401d405030007610180410071041c42c203901a10f049400c41d04200d0310410104c0701716504c888800c0c0440b1301a6203440000f1507103950002000b0301d20041ca65040c6050f40214034082e588550444000740000c54546041c0300010 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 601272742 1250 601271492 601271501
    0x50a030e07051c020a090b09070f020115060c060b04060608060d020f18160c0b01180f38150717030906040213020a02071413020708040501090503030309030a03 70
    0x800030025a21825240d0001504421030110000c0304600c0f205540300a628000310808001c1655031030070841800c1e05000f01e5030a520080c0060141b00b8480621101c0c14000e40188200c03407125515400c1d00ca8541750301400c0b0100ca0309080d6055440c0c00c1c0c4006050034144110340c280c0302c031074684108030b9075454200802c0300c41e9200220307080300b00130310005200d8582808010728000c02d0a0400810b142410f202090300207103984200c100b040c1400b100340410540c80a16044d0f40080d242585003c4480c40c00e040901180c80300680314918003203843c075001c5c4803090300c03129100d00d081d0540d440c0300d05169003048614200f000190f01034a4007550340220307400c003001403501c64031401c01d00101d00318816401c180b0350401c07242c048003500500104000c629018000c0b44a45c0c40b01c68045041c40000f4070000d55070700135400ba40c22101c000c0b04003140e15641da0401c1400e0350707400040666450050f49401940d641091081c00d000c60305003800441c40f03140200a8a00c070343c002100a50502a42ca03000301c0c05403 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 601273992 1250 601272742 601272761
    0x3040c0b0c101805070b070b090a0f08070201092106050705041a0306030c091e0a02030c09091f18180201050f0f04051804140c330415030e0c01050a03 66
    0xc5a0403002c803c009402440840020600e2045007a1174030780c04e05256410b00c03801001e4000135049440b50100041005980e100311032f8116541c10303100c4c499480140c4451600e504403513060009030741c64048002c150340e02402c000f44150340a200940b207900c0d06072164001da004003000c0101303481072082e951402e44d0285500c884001c00701e58402103000d0200d0300c0c0400c11b803107030004a40c00c5c1c0000c407130b02e5180d070034101d0b0040c0c1d080300304510b0340c60101703400c1055008680401d881000d81c4d1000c00c140064105022813890000c0444e0700302c1a58955145181c0d9800d08440ba850f103003001c4075118030130304008969038199011b844080c5015505040100642d0001400464180c014880411b05803602c45d003aa454400403001a0340500b01800d20012090410001d1500341d0311080d0041c500c0d443c0c0350078294006843e0795056115400240d00389103a0310300c4030004060b40e0300104e030005054150542b0419010015282004040c81390b0080a4854000c10388050201d401001903803a40d034440c0c0c0c01413169 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 601275242 1250 601273992 601274021
    0x619091104090f0b090a080909090c0306160215060109030b18032b05040c09110d02070318060206090706111f0b130603113303040c0b0c10 61
    0x100c1160200041c1256404a81551001000b12204007041211600b07150491070b507400601e03101c0c01e40da40741c070000e01c112034a0070701410102c0085040707040200003510304100000c065600d06d02d005480c2505c54030f5440d125000500c180c0c20f49980591024000710b02030720b8183d481482050658072011107804020f4907070202002c03841070441110000340007a000c0000c05c038410302c000900556824409090060000360030034540010312001481554081044980c16034002c01c101c0031510714088607000d140002c195540c00084e80008241d44210341c2980d1080c80e641101201d80c580c042241e0724070084071261010751042109004890191142c032125440002c110796803100440d080038001d0b46003040d0901140d071160085403413481c000c3e20100001c04c1000e81085050300d980c4800e41c900007a040c2290250103450207141d07070a55002c0501c00b8070070030000311a42009101d2086402c0390b0040300d00313403501044003401044c401441030880f61070b8062180103010003000628002c00400890100007003 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 601276492 1250 601275242 601275263
    0xc1a09120301120c09022704090c0801020301170a1e151b0201050601030228110307031106060604050f010e01020115092901080411040207080c061008061909 69
    0x540281402180680201400c0c0000710215184c00850b0b1103898010080203030040c0803505004040c01c11000b00800200f0340d1906c1c50b96501c01150042000c4500544101c41d6100c002c40c04250540040d412500401143c0145000061040e42c60700e41e810002020046941480300f40168400c08000080340564400769900710b400e03030070b0030844042e284d441030340304c0030200c07415011034080c8501d0780d0041e82800c0661801400c0120112508000c460901c2885010904805d040c0d102d003c0015480880b039045994039511820b0151004030110003520451191b10300051960034603800780e0301100c10150256400004220041d90360b1521003401c18119980e0f05c4444840c10030150507040140b149480002d034040c0c40915001c0c804801000c84010b20841d10069802c60340d10003001503010f50480643c0c9100d412107800200a48201e0b9409170510a010503805840c034004908640107444554488107000e035202866a00c805085031845400c00303e00c9175801500825405c0100c419100e000e4591 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 601277742 1250 601276492 601276513
    0xc0c0307050918150a2c0d2a030c0506010609050a05060318030a03060305101a060304050a060c05030a15080d051602030706050304050f390d060f06060c1a09 69
    0x1007514101c64501407030f03440300302c401c6040106250b1b00c80c3c00301100907011441101d050850f641c844401d4000410041000001b00c1030036051800c000306c0340c855204a49508000f405d0041c5a503071422001d41e01801031800008045014026030011a40c02070041140180b038041085201d40005280400c241301809a02c078100c441880200704111250b100041ca00d41181003117441c00c9030454035070014a1a00349026056803414540c48480342040758160b07520768031460400d0a1103000d800c0100800d0902c400a428141c00038081d600c01c99142c0b104118140044030141901400c41c0725012254101243c0c50340c006100b440140048951080041f005d5110781c1d000c60326048440d03005c01300050001c03080c40208502484000e0301c025540004151206141408035411203482901c6035141d81c4ca4415541c03410760400e0b02e00210b01000300018401c0080d03042000c0601500a40b2000441c40d01c0d10104045001c0c0d1518181c880c1c1114015182d61083c1015000044d809042d0096070300c2014942d0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 601278992 1250 601277742 601277773
    0x6051003020d180b0a0b011b0618080304120f03092006040803070606050301151d04020d12090f0519050402070c030f080a02060f010e04020103050408040f0b0c0c0307050918 76
    0x30b400316403007415584c8003880d01d00640021100e005510364104040e1040d4540c416104030101040303141c21000c00222a0034108941d0140c054250006003142c07070100401c4240210480d8121981d0341a0716140401000d1356000c500701c43c0310300300041940e949807001130107010b0880c0c000142d0500240005140540741c098080c956004428205c0d80a5140d820a200720700b0280078028000103010403d00800b401e0200d41e03000d14001050300103c0d080190300007010b542d91900418440381c0c02c03500c0c14801d02d0103424018514005030013911300000030a04001a24102040d8084541c00c00c4503c1c02e440e9400e020030040a0340c00450282c645852440c0301001284840602a02d0341d84038030a125510700510318040e040250041c00000c00030108001002108408404140c0c003980c24031780001c40b65914940b030301c0075000b90b8109000304103500501180c2030384c2c4031b030003007500c0800c400c21110700c0320300c10040596640d980e005290300847c00502080307000300c40c031031040c80060070071098400790400b20401 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 601280242 1250 601278992 601279031
    0x20d06150f0e0105030106050906100c0305070b01120c0e1b03090a08130e0c0301120f052104090e03090a060c0c09050408030609310311060901020406090906051003020d 74
    0x311039100110b100400151030244650802000c0070b90384c0010914204001600300d003806c012042c140a03030748411004040c400c004584200e80e001030040099615605134102d1203800280460340e001d01c54001040541c0c4442c0e55503c81c103181c228444054200901d9241250406048085280f04200a0000141e001000391901c0060781d003049032120725001c038514148501400c038221b800d104000500c1282c2541102e001e069810510b40749a4023020f1402624007001905135150b05a145003141c0044002a00104201c0d0101c66003800f0340b4603a610f50944901c0343d01405a88540c42030002c0108900130005841175500803015003505139034910400e02038501c1224101d40002c80002000840d1600240040d0482803014804440c6000084044c420802c1c104491505400100340a8100362084003494582e07140c4d00701303480c1d01c2e040010b55140030b90400e01034400864050240402c162505100b04803c03039200070003d0440843c00303102a0000d50000c101000d61a40f01e4145103488410070783c4 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 601281492 1250 601280242 601280249
    0x90b06011b0f1110140a14070210021b041404030807050c06010b04061e08040201180f030605090106150509131103040309050a0918080a0903050f0a1e020d06150f 71
    0x460b180d140155808002d440348a00da01c0c2c009201c80c0840f10030210014a046c0c9850b0000d07404d10b0b20021b000250f072403900f4021040c001307501c00480e0302c0c503959456001c64a00d4003240d00400c21001031041004000036207950880444a40600100180100744122001900012a0305096141c5000003000c40d0410500f42c210380503201d00041c003007140943c004052074500074861f02e40c002058903d40300078005a40644040e04108882d08007803481c2c403542022070000e168080141d405240d403443c000024200c21070340a038040d442c1c0b40001070810401e00c13203916140120b503200c92500048204000d20381c162000c00c0c0d52480d82e604503110300900f01400440c0164003c1d100d00250300d00e810b040015081c01500003031615414038201c1301a4501900d8020010343d1b10010b03d0340c40d100ca1100840701d0858990011b4524170036103000c00340007000440c10b000314600980d48400142e043d5a00e03154641c07440040250082426031260000c0b0300a82d0251070b485500c100c9101c25140c0d5209101c0c508000c0341c1 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 601282742 1250 601281492 601281503
    0x3060603020907050c0607081506040303090f0801050f010e070e040c1e020c0102030702060c0c100801090b0108130b1b040b0a080f1b031306150303030b0301090b06011b0f 75
    0x450030300035440c15140070b40c0d02c06002d1070898035018212000c0394803003202030308070400c0c41070640200c3d85402024400601000000d0409070b02c07660f984c14014031500c01d500c24011629010a00880c401c0010302a6510440c0d10f116284016443d05c400d9030702440c1d0041420040000080e0050155902c1e40102c1e0000c0c407a036684c030022680c40082c04118131000a5040d029940a0180018140d07000b2050312206601160955107507400b0100070381c00c04500c41c541550000b0001c1040100580000c1014180e42d101740080012001e50750054941900685990b06c03240761204241c40010344001d00e4a9200042c1c00305505c2142014041000e2508203400180d50b208002c602103150607480761503207a122048075140d8544c0d0615810100040090b000e0302c500c040700000c0062070b00d194811a103100e06a00c600100103141121080494002041c00202c0000c1d0600c450030441d45414000c500415401c081001c80380d40700c9000641d10071040c400200052400200c22801140841074403082d800d00a0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 601283992 1250 601282742 601282751
    0x5011d0618040506030a051b01090b0a030203180a03080a3b0c04050c09190f08070306060e1005130b061b0c060c100b120a050a030306050f060d020a030e06010306 71
    0x700108000d0b10b50060259020b035200180e481c0102da00000c00400c0280d62041080180c2c41580048400e50000d0304038801201c2c00142e4111a00c0c0e0680c011403103401460780140d290301144c680541c54150b1200c3c003500007181040404c6800a1136440b40643c60450034001e82d1450007481040300c1a0302d2000e0780b40b1040c0d000a003000700c20b0401c1c403642c1981c60089800700312524081d82c2c183c600340181c05213980541c01441081c00700802d4218650040c040007000f56040310b685100c100d540300c419001c11a40c080c01d01200145580007008414000c0101030001c1b540307181001c090200c101050a45c2801286d00d41541c0b01c10380e21600014000341042181200e191442c968150349000310f600d1240b40119402c00441c00000f002040350700071802442400300d201e101040010381c12521031076103040b05000b0800c02d4020010002441740703413544079860078401c041d079030710422040b0309444a40e581c0000c010000d032204048540e00601540308203003000107141c0150001140342ca2030981007204c545558 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 601285242 1250 601283992 601284037
    0x1104080f070e1003080403120c020a0305062502100e01020405060a050c0106050303090102060705160b0708150901050607020909030d450f0f060e033105011d06 70
    0x800b455002c400d0100b410b090a156a40308055481640300107840c2a603d290311090b0544660010054550005c0520a03c2c41c0c41c1e08280ea100c01d0103880180032882e0848804101b204500850b03802c50750103030003810500c4c44043d0044050055000941c103d075501700004106966828007600449010f591102c1d103c0c110139626508440407030300300a102ea03000380304d01c4021740c0c3c0c0040c455502802c5464681c1d02d41081201c202d00340b241050300100700200036010400c496501218640c81031056401230b008800d00c070400e001c0602c60a0080d141c200408000410150030090300c6203411000a2045030b1a2600701c41c440001c441d030b200d11020036800c070800b00d80b50310081030440d00d0040415100c5050804021001002c00c3c100081c0300501e0000310902c035100b8041444030707001c602134000d441880040440804c15403203030b01c842d1918041000c040708800801004940c0c410300c0313921700e40c080d01d101c0b820700c001036a0350034035600d0281c91100d10401801c1c140c3c0741c40c0003401d003c01d00900b8012102c080e = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 601286492 1250 601285242 601285259
    0xc050d02041e0e2104210203030d091b063921021501090e1c0f0912081206130e0304060306050d0c2c040b0f091204091104080f07 57
    0xa2209206090060b204c00c02040d40c40c03c108603000c42c0c280c40000401c131100c51a42c00d04a0b540180080e60501003c11044004076503034001141c280c1c41242444198200f030001c0300f81900e885d01030040040c1c0905120f443d1070902c0d10903a042c00d440b03559034403000c04410307640c613a13007040c050400c40e50b61603451203280f620b403902c00380d4150704d00c0d4030f002400034030540440410900c481403041008098569285a12498080c13210064115000c4584155001c01480181c041074140c00b81ca40003400c48200091005500c80d80300c903103150302624240c82c0440b40303010a410004080c025940c41040e00048540f4440244a0b0740d214100f6000a1620745240c0b00001c0c0844100f94040d0740540700350b4a40368002110b00d440c40060710582c40c004184001070702d1030702400c40800004194407810b03c40512040c40301660541388100d0325012103031441d61340c101845454101c0c030420003170f07511310901007400407011540050410003051151203041ca6650080136282c42c0605c030300c5401d250043d000c188038811 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 601287742 1250 601286492 601286503
    0x206090303070507022b0b060907030207050a1b0b0408070305070b03090d080a061a030108070603022106131a010f0e0a030f020a15090806070206040c050d02041e0e 72
    0x14009405141546070084000d0010b100d5848000e21680380d000c00d80e9940070ba403000800c1c1d00d80c0d010100c102e030040d0321710701144401c00c00da030b07201e200d05800e800243e021446402101c0c0520b9116010b001001811303641c0078a41c041200e164103c40403103030800b20343c0000000251000340420f0000385010307499030604034207003480e940040e2080901081003100b41440040c203000f900305149009a500c0c1d03122403159004041d15080703454400706a415102e010040340010754182d0b800c1c1000e8440ca107503195004d404030b200b1948403404044026220300d030081600c031800ca0f130000d405040e18803a20000b03c8520100c0f400c07842000040da42c44808080c031940d00c4415005e00c550541401010b5068800001d03a01001c140700c001c00d400080b45624046444407555040240109044003c00304040034003d0310650440c0290101da202e0000050311481c40000e099018913003210444610b203042500b4410441120f0340141d80007519000b621545c1d00c19480d01c40303901c020428001448452000035a070508 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 601288992 1250 601287742 601287751
    0x50d02070f1b0e010e04030815121b030303130b041e03030504060b09060634050c0907051c0e0a050f010615030501031205090d0501090b04020a12030815060405031c0206 74
    0x3e0415801400000b1280c41d403180c01a070035041c55000c41e03a5030881d046040300681e0402d82c1040302d80c0c803580c0d440c4400052407110081030a00c0d44884146000c207050341c0e80002c6511400400302072001c0d0f03002ca1010b44507940c025024980c4130318103072003600307a0b445125000301013180003e90b11010081884401e210714020100b049800202c1c3e820403000042040c050036014403034988a21103806290b100012540c09000000520007292240d903007032850310b810410355003e006880031000641c4240c8203a049506200c003c40c4210540c40340c1007014001490003010400d168807406844a0114104000481071241c1640000c01c43c2c40c2080340040a000050342442e09140c00d2a00600001e0425078031081000084d00d0520f456900e800c0c0060902240f076407000c1d100354a0644e180c0d043c810400300d070920640c001da4020300c600c1d5841417401840c0c440040040c0001d620403002c1070180d40341e044d0200f01044020101c5041c15201d20009007020a05e003d2110211010300f1881d1005406020080c1d00 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 601290242 1250 601288992 601289009
    0xc120203310f03030e0a02090901090323040e130605161d061b0705060a09080705120a02090c041a0d050601050a0f2303090a022b03050d02070f1b 64
    0x5040c01540d0b160303400d03070071007030020245920b91605140c002020801d502034140c0081c031104071810100c55590080080d4581a000241c4030344001420750302e10449010304c5c04400800c28503051502000340321404c000350140c000c00c08c03030402c1d0a0211741d040c010340780201083c006209140e08030707c0380908481c1d00c10481130311900d6400b0080032180d03516000e4405040c459001c40840c5410710446030704000c2540c0000d944101302040c55411349500444001c1070f40e60040840c3e03000da4480b000c000a860034500c024181384d005444580042c106100220341081c107424030345040a4885101c1d62105111110102d0350b64004102820380c000103001e0660030002c00e090a038900021841c0050880250580d442c05101c8d007034003984072110100d50001d8000e140c01911a459082c0070782020b481d10200c01050b4801d0340407460980e03809600651100c0608500c1e403038014000880d81d4181d80980002c10107200b80c6509210040c04030724200c440c0411984510710074200c03d4544448041300c224280c010394134 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 601291492 1250 601290242 601290331
    0x10b040c03180615080a032012070320070b091c0803010b070f120c051c0e010c050a0206070c03170405010203070311012d0e060603030a030c120203 65
    0x10042d0342c00e0001000641c2240000c10281c02000fa1200711034a81c0e8000341d480e20031310300044140b652005064981c0c0492000b605100c4050700d41541e922107810250b400803140420130100020302030441405542e110403107029451910149060900103282d0101072000d500207110045440c016160041001616203c81c090303400c00e840b62507081c0414080c0b9840e83e039000070390005104016090708810341d48007810b4151000d1801008180521034601100c0920582103031503000c65092000c1c1902c00d440c1ea880c080301ca000351004460302e00345d68500f40e481c0d0284007007840250f16940f00511f11103028a41040d8074518602d0041c0009082040c2e0040001090001b8405683c1c00301c11500890307058a8822241c5002c0780e00c4500408038011030381d0700341c002c050032089480c1120910003040d0031002c0081201001c4190010b48551040b11a164035400802c010126103019a1003403026030114a08030614950200911080343c0c41a103560b6821042081c001840c04401e0000c1c507a4030400000444 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 601292742 1250 601291492 601291511
    0xc1008070306170d05090d140706120504030f030c0c080f0307020c030703030903201011100207170f2b0b0402090904030818010603060e060a0525050d060602010b040c03 74
    0x7034407194040651403c00c0310005410204d60b460047c11000c0e20380280e107055507001001c404d45e07903440152007840c02096414009030300001c201e10409201d6601900c0f0b4594005500c030040300104000c0640000303000f1401c0d1a03102003811100500005c21104583c1176403410f1480c00603240c10540140d06d446680100d2044c00065070068441c0304a0b03500c40402c0c007004d00f41600d0307480300007840a2215000841c14204114299115007141015a64002a2840960043d100318180e00c502c440150802d8101914007404a504000601d19801c28004180c2450b05801c001c160f00458544084803440e000c50f042000030300d20b032085880e2200704032011450400764001140c80c004004001800f44030318400003416049a0154007055080d0850007000a940c032442c02c140105104580c40c4150f03c104d40c001410441a42308403405265480308092800d060040805564003138900310f0b404004061084020414803800307002e01505c225000410762800c0c500c01e0104880480c004201054203040000c0b = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 601293992 1250 601292742 601292789
    0x1a1201051504060f0c080d02030723091323100503060114010e040b0402040902041e0503071a0c06010f080609060c09060d060506031f0b040b18030c1008070306 70
    0x2c4044030000d0030004980b00c0c0c070310004d0b00c1440d00b41c407005d05040070000e00f568404209900441c030070349098a58400b40310b21044040c5e6083c4582200520b403000070440c0d403685251083d0b5201c0000c5015401282000c0030085140209005041c8601e48007a49024450100030b0150040007500cc10740040030190301d04101d4000e54100b844c0581d061080d0085840904e803540c2c1c000c0c5060801c050811340d603c6540302c80040c001e40c4035104114040c07011140e1858103d40b40441d21040f60401001001100e0428901c060f00704425051f0141c0c44034104521134081c0000e11040d03001386050080c1c941d41c10f2401078000e04048000340a000c81e50071003c10000c80d252000140c0d22000b40554a41d0f0f2035002c0c0104801c0109402d80002d54400307008010000c103208420800300000054040303540c5803c2e40c503003c5610901880c004c0354003002c000e2060394254883c0000305040031200808550b41c01c5400804154050b50400c8030700009030525041019003501801124024801c00742e0104805004400740d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 601295242 1250 601293992 601293997
    0x240f0c100519050606070501061403071a041401090e070816030216290a051b0307050d0f060905180106050d050601050409062d050c0a0e04090302071a12010515 70
    0x4101503030340e000444c00c1d42c3c031150155074007958054000c0041c43d03151100c02800c80c01418459200348500c603008180c03136100e8540c544414114003505e50415040954107545d21010b00301040c100b10020000046190842650381e0258080b91100c00c80d50803c0d15421420050001d0078200741030041240e03060200312100c502110b160807d48a401000600340001071205882c0180303425030720040d00b81300020b08290f00c1a406070103100e10000c4103000d910707064521b90208a81160114000380540b14140d0226007000403812618000003400c2c40e02e8072442c104484064801500d0321150201f00c1d14203038408d2043c0f078013a05040380d00078080003042da50300b0b640303000501409004a44464841007041501c1e044082ea40454003040c00590001c030500f15140d42000c0b00031203040342000c0204903d4016103080302d00040843d5078480d0721102540c00e10014242c0d0b41c0088045120725900000c81c0c00702403203c08040c0d0010203510350340702c1810612030141030060300001c4c8100550700d4004803002c0c00072704 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 601296492 1250 601295242 601295281
    0x504081207050d0c022815020306040207060207060b0a270f060503120c1c091403100c030b090c030736030b011502011a240f0c1005 58
    0x100000c5a603140641254a405001d4048084608150070301c2c2c0030940202e407400e18203142c481d950702e0740f408495440d545800e088001402e18039801c1c035960480720141d002540c2c0464041d0000d03180008944c0c81601700c0e80411030550781e59a588000c42c4092a0012000c0000c03c11400300e00e084214280040d680032030460300900381c8942d14550f151403200c042d00032000910004040d19540f218210144102c0e910040c25000980104540729401c1c0148165408403000117550700d4290034144441c2d010400300c01c4041c03031303814805c1d68030f4500c0300600b40c00b5210b4072030101d54000c6140c4003190207100807802e02038880200100700b0310802c04000d902841c5462205200b6501b081c00d10780d15560511580d40c1000829544017090710088203006d900d80d11281240d020100e01460302d500032100328201c401c035502c1c103200c04128802000c0c60b41380c8a8a404030a4031141002031054900700701d0445140d00c048000c3c14526404141000c0f2202e081c00720380c1e24141082e0701800585003600041c1d00e40024041c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 601297742 1250 601296492 601296517
    0xf03060b0a03180609060b120607140a0302070c0602161202130b1309061a09130312020c06090708150f010e0a0605060a02100b19140d0f110a0504050408 67
    0x680b016182c03e0030101c01c0303106070404010002a020380c1003a00150035483c10b000d0042c1c05880345910400c40000c1c800344100b10307969a141000040002c0d000f11548146100400c164090081c100490803000d01200100b400350004d01000e40e40c543c004013850080d42c40407140262075119540540c4822881e10002d000d00c000c001600414000010611540b150070001081c2c0703081540740800c443c0350300120f4034140450300c65100c40c0c01c40003000501300040360402100070b00c0c104190002401280ea0400c0226403100c050700307020313180b02c4891400904444034031841d400504100040700060005644413000740503800807520303002c040c0c4c242d524410f100c0d007401405610001a020174070742d40140082c0c00c1c01080e043d510116150003c1d038503003501c0c111001e094501044401546400391107140a4a06192501220303840c5c8018115200d00e00c80d885a040000805441c000604c03a01060025a00c41c524540b035491508040c8480c41240340c12190041d4036200034000405c003a1001e8401691081 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 601298992 1250 601297742 601297751
    0x18030f0c030c0a080a0e040507120b03011b09050907050405031906090803151504050d02241c060503061905130804180f050f0f0405030c0303010b0a0f03060b0a03 71
    0x311a6925512071a00e0b050100c0c0038501c10b08041148050044c91340c113000f40d0751745041040040070001101c0c0155010808a2144036081d1400d00d0300d40c004032035026008000184032825403070145a4010010448400140000c07806c2c0a80d2a10524407504400607141c0710382001d00b00004070f81da03420302014150302d101c504030706c80c1c080266540100200d00d6200164a4403800d000325412155581030007494820442c0c9014102e01d00d807104151001c03a50000c1c00521040030f0342d024001c1c001c03001100710341c0540d0300a22910300850640000d1031b0180103046002c21070b0040c08208012240b035034008503c00d4118406111001041d070704d41c06500544c1c038000158a80341c00010384c2a031482c1c100020300000010400250a107035005510245030724844092041e90050003a542c112003040702d0401b0fa40e01c81d01c2c0411041c41d50000000d47c8544a14200c80c42e005c4204041c62558009900140c9001c0f000500016003d50082039809248a1410144076150403c1580007150042c510382e4010103944 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 601300242 1250 601298992 601299007
    0x121406060a1226030601020c0915010c02061303030507030207150c061e11130801201e0d0603141504110f0d08031605120a090602090418020918030f 65
    0x2c401040307803c0b45802e00f00211100040b00640004d4104070780b0a030250003410b540010318100081d0061040302c407514105840c100d498015030301451a403009a030001c00501101f11469000441c16003e0742c081d40320a502c031442450000d1500b5256000240688044141d81c2810758215078002c002d01e904c00b03404103000c510655a011251403a1306482001401c0030000d5001a150744000d01445c21000740016066854050301c50030303a0001d40d40e4401c034100c1049030305901940765010785410365103a480e152035010182c1000070075401282003001d0950b0b6070b460400070801c505100c03201c4050004042c1190004c00360494807d10801400505031400c4902040d5896507030702e0101011100090007660403090760f08109106400c2120401660861116284001c0c0d0061060b10164980170b038140c20546da420039004003511144604a441c0e58080c41081865520ba0154402c401c1d4154240000072035540100b182014003d17100e04100408044180707034140c00403040b03c0c180034114030660f42e41d030321 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 601301492 1250 601300242 601300253
    0x40506030a021908010312020c0d020402090109050306240906010804060903090b0a0305100e240d020409260f1b07050402030c0a08061f030c03060b04121406060a12 72
    0x5074116002c601d00c480340200400c0c075044a004c0341628010141c407940386510300400c2ea5075400900c019680700c00000d4086005281c140c006041207581894500c070b015590f10b000c20325004058035811451010544a600d0f000009020b080f440ca1080780c2003c032504010001900303820001d030000d042240c41ea5683c40a240c00f07441544014402d08580990320301c00e002c401001000252034510a43d4070800c0c0c00140c100d010624103002c0c44290544412014191022282c0d030380348040c0580d04075050380e0075440542c2d2144661403240380110964500d40042040700958041c6001000520b00018000101c8000141d0241c803609507901e900f0204400c80070042d90b1910a059005030b51050002080189148040c4098000b400940d150303410a611441304200c001c0140e024082e914034a0200341c038034903a10079003011018080074140015415102c0010440035840394000b1610b10700410868001c000c1d030712801802d010b0b40c91024010504045002030011040362041d568080003010300360040c0315 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 601302742 1250 601301492 601301497
    0x10306030b01140d020909010c02060a0e0c120708030f07021c030509101211071b030210050a1e081009020c03030103020f030f1009020a0e1504050c1b06010f05030d05040506030a02 79
    0xd8004005c085240351000015019100c0789d45004010702641000c15013000290280c28140c150305806000c0b0306c0c4202052081851014031300c02e10311300c00d880c400942d244051000740345902840d02180e595400d240140032440b003542118161b426508d441c1600482e40c01004d4542403042215008071604000c5403c580e000800034140a445280440046280f81c4032001041441e204c0c143e6054254000d003400f442d650158070010350440c150030700710b03100745118500400742c500c40d82c1000341503080ca00c0442c210000c107011186022407400c1080c0080104681203a00081090a0040d032510012402840d00d900040c880240501e08080d010500c3e40d5090001d14180c001784803c4590301085603400300e004e8503c40034181d0160f00740101c0070401d64061401c0620480380600c0f01030011944000b0701004000050220740d80002c14090b04403d03900842c96440350a1400004118550400c8c082281c540c042d03034000707403080d070028a40c003189070340080603a812034108480302502e9640310114080070b032 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 601303992 1250 601302742 601302769
    0x1090b03072c09150321030f13050a0b090127021905090411011b020102060403080432011104270902060705010515011d06070515010611010b010306030b0114 69
    0x6006801040f511649440c50301d04e96000850850340e040d01d52403449902c01c2d0040303032202420711080001440c84030004013440e4102010704c0c9072518150700d0b9200ca60034441c0300c9e1411507400d4581414014502800d00a003461601b8541c8904c1172041c4281c5000700840008200a0103000d038500090f100361150034004000b80006030070b808880c038040c6440d0204581e0b15048c1404100040c0d00151a000b0449101103015410f800601654845460541f4240c0380100704a50000d0320850b110240182c1000847c2d0a00f800c82c0481c1c3c010100355802420750b901b10701c010265070300601082004150040314010200032100c100040c5580201d0020f0140c0b0071602c0103034000c0300000390740742085015070001e881001031071010124818004011501c41101b4410410001020000d56201b8680342d80141505d52040d012180306c1e01c8011a40007005109030b0011002c500350780211007100600303015550303040c00c0034602082510b08503a102403008406008211000c1c1c91340c20000700584603500884600c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 601305242 1250 601303992 601303999
    0xd050a0209040230040320070918170901050703350402010e01170a0c02011d060702190b0f07020109050f030d0b0604080a0f1506080c01090b03072c 65
    0x1500c4408110107280e500000c610a031300c00304550149031140e034400c005401940d055950000070b403a04031125104107a1007003184828080d604c80000d039100c8510035150422002c6100055244003070400d0f50103003100c0805042c0c1ca003010400c1e010240c0e0b02204560783c40c0d505003070500d0180c0200d40c0b000c039040100d001042c043c411000d095820544d0380001e45109034400d0382d480c658080d00d40700454848404040d000c0b1551030102c007042c0040102e80105441d00b040d84000105031124105400c8012414244240c0e42d0304000184407a0316414841d503440d00d001d10500b42000041561075841e1603034000c1c92500303036100d00780128001c1e5100303400c50956590080704a4040c0400c503c40d0313a17102c1e030086032078541044c80c1c4002040c81c0d0620005036000c690b0104041c285214594441280c81021b0000c11143c08040b401602ca5521f4148642c0e00949160001480e0303109551002402c03d4505400400c107100c02403007049004c0b9800382c00484502004030340b250341d00d08070071a103e031403d0249008651 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 601306492 1250 601305242 601305247
    0x20102240105030c060c3328020723012003011a0f0405090c07050f070f0807050607110109050a0e01090c080103120e03162706080303070e03120c0a1103060106050d050a02090402 78
    0x15000c030741a21000240f41c0078000500c080020300c003800300c3c80360300d600502c02000310039000e20202411074540031000800001082c481441d3703d8a00c00c0109046928414480c01300c01840340601944940610400203680d2500c0c0c42c0321050a906907004510074240b1481e044130008500590080a60340b220b6031000131507000c1d002d003c04550700c030b0000c0d0081150140d04038100040d40a4001000402c0720409807407a4540401611000d813000100c2000078103009216800090540b50007a806008101c0d03400f902c042035040c41c101d002502e02038002e0744201700d803003001440403c80a01403800c0003c0c55051648d078640502c8086410100c440c00a9a0726185c08040080c5003503421841803140c3c0c1d444009010b0b404042d40b204000c03102203000c3d280c1707168418000100e51134090442e8000d01c04009085400291700044e511015074000580b05082d0f400004130740c0c081144080c8a403510710003c4001d06555814807400400500a030340c0c7c00d0aa1039121004252440c1441d4102c1d0a0040060810755 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 601307742 1250 601306492 601306501
    0x2030d02030a090b0c040f06052217012016110a090c1808070506030717011805250302070614090c1807050301090207020102240105030c060c33 63
    0x3060f0700041601d141c1855000110854003a0086905660b4051106403019007001f174115255001010003030000e50011481140e0340c510f440000c0000c200b40c9945a800c0c0c40403902c0700742924405003002d27401108803016180409440420788404142582e6081a0700600c0e09080c81011f41540c0c110303811021220340032801214940014001d00510b8550011a01d008041808814640e20a00303050b5004104c051006280800c001e40c0c1120301c525015081d889603583d030524206003a4003081c903d440310810301010f80300300d02540354005111114140d054100d03a038041c98404805030078008055000030308030100109a400307501d21589006228441745489211b059950114030040c41c405c100030846100d00d1160004454450221644c50b0750441e480c1c04201c030003a410003401203055014000b00802540c40035006100c0d404400140e00c0c03045d51504041c0b6003002094600c290003280c04005c19100c80c039001a46050700c42007000910f0a110a00380780000c3c000d100001d01e5510503409080c007 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 601308992 1250 601307742 601307761
    0x3060f040e01050703060e040c290d06050f0f031005100801090f02210c0f01111c030f0605061602030a02060406021f0e10330e010602010204030b130302030d0203 71
    0x141301d84a5034500300101511440c106006031422a4020400380b80382c0e5043c429065413003690000c1113082418161034004d46500440f0640104005203e1207507920810051444e044441c2c10b803020054074036180050010001c25140d07a5403090940b8401d444402181c0041c88900780343c0000c00e078160080040440c686030010361344d40200b8050344503e5580c004084141d840701251090356014400602040c5482e100b0300500400001d422814403407802682c03110801e0501c440c000706c40624084101d070b20100c1c0c4001d003ca40c900c82c04242d080d86041c00621003030f100c840840b40c8801043e88000e107014000d100203841c1154041009400400202e4009445500041e00400c0804110b010422840d83d998803141200c407501c8080680354000c9503109601d518030361001a50025182d42d9410030005130b882c82d50b48044000c3d4003c40c0030180e0408110100c036070701c03144c1d01502962000390302c4c1500e15264411480301c0a080801c10444480040f070801d8000c0046034012186038900395101c1c0740a0614 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 601310242 1250 601308992 601309001
    0xb03010302040f02030903031605070f0f030f021f020906130605070b01051503040219031209030209010e010b03070f110115080607030b100e0406030b04050f1504020307060503060f040e01 82
    0x100d000b0350815900100c01c40b02d034000d9900c502150f500550540d0b40b0190300b041803400e001030754018010b007000440046040d4802241995004100e0450754561600c4d006089a10b820070000031034001d10b5a691400300e002c0107030300d1904500100580c131940004c0004855116400c83c00f14111503c07000000c0182d04113001d40500e1b0300074505106180e030f0350303c00c1c0030405415082d017005691f002c100042c01440c01600007070b82c030381011504415141d10f0765030309000914118540404102d05081c10800c529040101c140134002c010601001c41d40341035600d20311800040c00f06028442900c0e4609810b5108032446160080800024840d885090700c030610b00030503901a41500380541d10015503032502038019218005e2005e0308985a0a1013180704035503404011306c6480d0b0103511440008082600307442d0041c080e40c0200050051034241c081d440f4504505103401000c00c0e02a90b0070000503980100b0218225080d0781049550780e13803607200046d0201403000307040360310074642007032141036841c150322 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 601311492 1250 601310242 601310249
    0x50f010504051b030705062a01110906180a08011e06050306130203030c070906050103060603020a0e011101090204060b0904060e190507270515040f170a170903071d0406051503070b0301 81
    0x880101988084400340e0030789c1c00000b12b014620b4010007030b0810604001c8028000403069041c14101c0101c40c000141c0503d40326441114140c0d11100e1505c4188144280040a00307490b210811100c0d14100100e91100c80080884950322034104180040d9101441214400f44030038094503502601c44551700000c103c240a1140002d1070102f000c91094064400c41c0c15030012a10b0794510760402c8401103d03041d0f950a10b440f515520782c03403100d0050710350303000f040050281c84454a844404a00610040310a2540300c1d912015480c1c0c00c0c864450322030114202c400b82a80710119050707442039400d41740d901441c2c03030014012504140140c0c4555011407030000b5204211504141d011000c3d1502459016901032606074025218007080341c4a20f090b01d180303030f040000d410740b050381501d9114140840d4036100d0954044000080c5c80300145028001c6c10084c000c00448030003100e1006600c207080040040004200b90358801c042071041090942040e004e203001422600e420b0303140c42c0401c199070028070 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 601312742 1250 601311492 601311547
    0xf09040605011503020c1903020c060d090b10121101031b1115060604120c080a031d010302040e070f02010e0304230a12080f07080313050f010504051b03070506 70
    0xc075003e03224030038000c89042e0701d0404002d1918410410903084072241d5541c0403405c1d840b49030b00f051100c0c0c950740050f285a0580c1e50000440b54520b08040000c0706c80284140111300c4114414010200000094846d00e9080251070b502d84500300d0040e8024000801c0f03002c010304100c82001e443c664842031500c80400c2032800d0360980603100280000f155401d50711035902c12001e00050041000e401c00d40300e0070501612000c000544e5030301403035051103160003003640000d10100f40500201c0507824503080d250800e00c1c08501c1c051804125400d41c0701e0107080030f0208800c1c07422503603120b4400d41081c200c81310341d0070989071f480e5602d4400110601e45445403401c7c2400c2b00d40c0d5204540b40c01d41000317044034040780001c006449155030350200340d400b1440b556502441440f860005c40d012601951090040d0080d103000c025440c28000d2500200f614032032803907814071041200161000c12101821240d40001e00d450111407070000b414568240c00980c0c20a002150040d1005a9a05041803080509 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 601313992 1250 601312742 601312769
    0x904030c140a29010f0b0d020f0c0d0f020706020303361e01050c04050127030813090b010e0f0d14071d100e0c041706040606050d0b060d020f0904060501 67
    0xc3d044040c40400d10407045402c412030300030059810660001e08043c200900c0061034801c1208181011741c00204c000c1c01d5035400701d4410002c2e140c00243d650390178034480c002000981e160903c001d569110042100c0500c17004800c2081c0b683c524400b45400003071400d2102c141d03414201040c940d0701da01c4060f80001c4090300c0300b10f0304c10601061207190f01403160301941c0c516050621006443e103030400d40b086150b2101c0032071040748240820944001440c031400020307030380700601d6a03454414441c64110300a02132909600612503a041a030b0310889a40985c0d110390440c1c44080060012291002c014100440b90740400107031600200d519000ea400e00c0407040ba050b00d1003041005280c03811140d2021140000c2d1045c0140100e117051030740e11021565800b49482e848241410210040c65240b120070390180d0148800c028032402076001412041e54484c10b8411942c555103040000600b000c0d001e00f150100d20001e544514107880b0030381c040030b00b100d05942000e2400c2002040248103815481c40381 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 601315242 1250 601313992 601314053
    0x306033306050303040302090c12042604150f030b040908071202190b0a150603090b0601020d05070308060d210305090d05120601020c0301110a08010b04050904030c140a 74
    0x1e10510041d1107028000350b04040c1140d092241d01c00c000b810340c4803241c10610040030103403080e9000324400e9204280d010001c1d007003a4410240300d44200c402c82d9881c4000d000a00c407034046031211110690b2185840301c4401c1e00c0590a90040240e0001190000c0c1040214402c0c44038840040840601c0b600455031011001c18007282c0743c010f088aa10114068030380b9160100e12071000c580e4111059100c001044002c0c801c8101a900352a407060000c40d0b00d03038000740d0034002000d003d594804028005420307030404584000380984651400102440001000b190990300c441c141c020b44103a0005042e002070154407a280280514054600006400c08000451074280450380408541a50700d616003046820108040c40c002e0007407919046128100703403054603507424001c070030610014604082d0354001d00b403070042c0041c505800103816031200304070400c0151200c0e14159445a090300d405901846140381c508194402582007000c01e1188005a0307040c030400d40d9402e00500c02c40b0f001220300418 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 601316492 1250 601315242 601315343
    0x150a1a09030709183e1c0506010b1b0d021c0302070201080103080a12090c060215010506041e0308040305101409060c0a050d02070b060a06050319020a030603 69
    0x4e400c044a100c15080500e1800100d0318001c03120160030708000c50301400510b450541c212195006003907041d1058160b01d0102d030400155007a40000f100c0b0408a481880d5120b050b507880d0b06100d20b0300011400111001c0507252034451002403284002951111908990001d5550710180c01080901c0012110548018002d00c00c40c0c02055040c0c695188507861a2104031840d0060726410044c82540c00c0089141c40292143c4c00a03540b00707401c525946810508020f280160300350308507810991941c0103121583d544c405541c108d0f842c03664a180d84941070006200c21700325903400240342c42d90208000c070070441c0100381e02000d6040c13644200b2000c2151f01100045001c181e482d0142030704200c0200e4820700c0c0d500010b140388280c2d410880c1c90b20840c0c03a094012603201d01c0043d07450303480d072070b080c45446d18000ca803000c01094140360242c01d5090046408640902004001d00016170019901380e41a001ba00f10790011500002034803c044c8406411206640c110082c011407032503c803061010b09103 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 601317742 1250 601316492 601316501
    0x1005090601080c1512040609050c1c1202160b030901050f010b0a0f26010812070203031605100906051602031c020d0e0106121101090e150a1a09030709 66
    0x610b00c0000f00000c10994041c05408a0381070704801c2411800c00440c680c0448285c1c00600680c4103141c00681d028941c01c0240c00c3c01840030525200d4020320020140b500c0f01030021401c4203030800e0b04049101c01c540c1d0241d2a01c1001440701c41d203d05080c80c009040c0241c04042c5109440d040700038016659115001980244240502c04507824144656200140300d140418900a494103013503079011805201941200c81941004409141c07100c0180b29401040c040200b14025a210140c1020101d600098a0307010310160344136001c00c200307510000c0c4642080701d440d0400c510700782003190348458100103020b440100c60b220000c1e0300004440b400035200108965024900c21485c886210000314010027a50000144240550f1030354401c0002000070b200703620007001e1210541a103030b151454000c0c080105d558955050005030802003206841c449512030340124454111590004082c0002c1c051b00895080200f0082000f4400454082907074010142140c0c01c404480c1c040741d40d191100c003500e = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 601318992 1250 601317742 601317749
    0xa0b070e0a0603020a120501090e1203060108060d050309090a0c02150426090402160b010618351e01050412030e12030f0a050603190318080f1005090601 67
    0xc1e260310020000d0600c07a44c0035283e480807914289192103030852001c002d0b0744080e00041e80540c1d50f19150000340783e0401070071900c400c0d01c00a55080d4602a0006044d05800404403400390203482c00d02420090700303000702c4070005802008030340182045c200610041004118031009407244006000390440c0c1100c41c140300d06d40c443d041810030785906c01c290130300b111f1005036061449414030001704541c3d214005007511b0b00c4d03a1501d04001c0700075400c00300c91000042e031010341400726802100001c0d054404641c02502c03030034059003a1103c0104007103030708010000c10019041288003100064076401044c420f0115220403252440910b40c60320f180d08030348064034014902e03003c0e50303052402180a50000e020b003034040d10a44040c40c030f40c043c03819050b80c001c523581e891019542040044000b59845900c0e041230b4264000c086c4a42d0300d14191a0b140083e880180c2070011901d07800c0c00c441e580c04c001e0360241000d02e0950300c5a0304800c08140c1c1d038980458606100d141041c000400c251350004000e4103d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 601320242 1250 601318992 601318999
    0x11060a021b070321030b030a1e05031b01150807050405040c2408090d0c1e05060711100b1e040209040207030503160e01020d12060b0301180c08090c150d0e0a0b070e 72
    0x1404107a511022840b00b0301b4401554509009d0840c004a07034188084c01c0d0001c403c0e110362a0b100c0f0100186070031211100c010b85400b0003041c2d424004030b0800504501074a4058900140b283c965043c03014065445130b1000e00700702d00002d1031030840d10311750343c40512061464844d040075441d440c00480d117549080c1440305c0000e81820128010620341002c0500003040c9000305184400c443d12030305d003030503021103090020840c280000b1000c1a01002002c11118503410100300c5050040001143c000e070001c000902c400a008595200d0b50311079044980b0440014800c56480e1554900a005500111060009003022100040c80711b40504102e000d4488140e018010800c6040b4090f6403024505401018060759504041000c0c841c0c00001c7d0702a041050106a4122070302c02e522040c5e40390642044200020b65003807040380400007500c401012003c542e41003080203013000c65459402104070701c00449050940409a014010600c8441c41d4000c15034030046503100c0c44180d41d5200d440800d02d80 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 601321492 1250 601320242 601320253
    0x1d0708010204210c15021b060418020307030e1606080a02090a270603031106280c020319200615010c1104240611060a021b070321030b03 60
    0x1e540b503408440d04105100b203a40c40c1090f41c440e0601c2c6540c4a120a10b03c0143c7e20480c0b0b01d001d40c40a500518011010468426180508019080c45508007440741e1850305600400030072840b6000c0c0c0c002042c3c41d81c40a0440300010f00d00110025007003d5885aa4045880500480c21015850013110b0400e1400f4202c1c50310760b454645440d543ca440324016148000141282d02d0002d0700fa4050320004501a43e81e80071400c0b1803e00c03550a01c0c5010388410180c54041d400084100b420044109440d40a42000207441400e90004c0c0d00314132488981480c0c1c50800074811100f10f170401d004030107102c0e000b82e42e001d088020095150f41c452054505c010505014914121a9885a407449480d140700e160440e89141e0080c01003400e40e00543c80052000502d0034174500303491090714210000b00407915095030204101c0391502d0729000d0260a40750f40c030f0340006054004009203a5101403e500d100c0803181000d5582c00c040810b900c010400115104503480d80414543c846c0c0150300340c16000801902 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 601322742 1250 601321492 601321529
    0x60506160b04020d0b0a15050402030f0612070e010b0a1107080a02090a090203030a0348090312050c011a06160c0b042606070f0f050d1d0708010204 65
    0x40000d0700090040303912a10b1038000340e002903000400035014105000010034052000107100b4081e0707003d904000d0003207106008211011b15440300d40d5800000c140d980c1854540300012441c142403064112020391908940006140d60340e0400400b11480d00d940c4002c903041040715590344891b00c1d0700c109a40c907404500054003618144200a03003000d5084000244440310303902190941e0458051040030941d182908030100e41e62040d0000e400c0110b4444051040d01009910400e80f070300c0301003c00c502000c1140601c40b5020720900b0001e5500b0201c0303030503e8081104000c001d54005c4010301d60755420210000c042581e40c580140401c1e000609080c10030036884008059910800415510780803600380000d200103080c00200060540300c0300d40d01e924062500008511182d081420000e03600c848200101180e10007080e92540d0558a041000d84425400850301c1d030184034400d41c0118900a100c041038042901c51090704024001551103090361400094201d02841c03244040487c9c510480304c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 601323992 1250 601322742 601322753
    0xb010c02100e010302041d040b07092102030f15010311040507140c160902040e090c0307030206030717070e0103150e06150d090f051209060f03150d080d06050616 71
    0xb090720b940601d030060174950340d003544202d1034100340c2e4070500d01c1141805010603c0480144594010114144000c00e0b034500010f09821108603802c0d03c00c41030065031407001319030b024441c11030840c0d80a001c03603402d885080d00c0145a103100b07200441d40501248110306050503d8041c1d544030f03c1540e142d000007e4400c2601007242d500a00481c441401000c00a150001c03140d05010060489004016151800c1514030000140d01401000b515400125500c02940d00011b41c1c600741e96041e50950b40700d07207036a4015140741540030384941910000c58200240315501000c0c0c000040c0d003d070303018012840e4010b04141c4060b1303a0301034584071a000600103950303800c0c100003540079010403030f08003490102d2912501044030114541255680d881e91180014031004001101c003610120f070303046281102050010710180720394140e00b00c42000c0070000401143c1c03184020111480c01800142c16504e0a03d440c410b10b038000100c00306128507007400400d980c1040c0083d600c0501c20742600c400001131540310b0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 601325242 1250 601323992 601324007
    0x30a03110c0a03030305060f0f060d0213080a05010516170601050a0c060e01020310080706080f271c0c0305090402031807060903030305060d03210b220b010c0210 71
    0x500e00c251141c41c51114180d11105106001503000380e40020385828582e00b001001129000c0f068807480403014a040e00d645d8140864102c0c00c5c250000581c1d4002070ba075100c0b610449644070307000c14016802c1560501406411941c441c0102d402528248030382203a00395040300c0b021601c400d980390304d131000034020750040d0020300e1051164241014100c0309503545900303071800380b5131842c2240d401006000c01e06e883c3c00c6030300700038000100140840ca410302c130380141a418024003a103c480c4c141c00204031001c0050302240c48024038241211000074003040349955440140c400440440c1ba0305480c6001e45106000d41c1800c1645640c40601e0180940100f10103508090f0009400e41c010307401f060231080307042002c40000d00e2a40c40b101192855403c01800b250341c020400f60107610b120310a400000da0204d5002011805d401c9038866100c6125940001881860111600640e140c528a40700c21100d0a00400050a80341c042c0260901030004650a10f45041e00942080290720041902d0b8090300d40c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 601326492 1250 601325242 601325267
    0x91104050c0d1d06060306041a040f0803010e18010c020a060e03121003061104050904021c0204020f040509060d1109070c170d05060301060f060f0513091d0c030a03 72
    0x72a203082203005240d0302c0440f5402554440400050554101030a2080c485070703a04c0482180608020f03e8070f40c80340010b030800c0202c01220711100d00300081c00c00c20380000c0e0b03020554020248503100d6860b1f65013a0380500058a0506024003210300408c010001405044200400395024002c8042195112009031114203c0e07461640003d010741802d44045412140c41010f1245054040c1781c0f13142400360458038003408911f40c2400420061040b91150343c1c00707a410503030584580400a60320300d03020031001060034000b9031140c0006102c03001c104094001d842a01d9040300c01c0000c60b16800d0800920003072002d0002c203a05030880720940c4030300e410b03000c0760741c0240d950901c003512000d03503500d0300c0c80b564030403032010440d04011590302c03814050f5201e0a90701003010b6000700075240c00d010180741581181c0c4a410108034169911284c0c0c144100207aa80d44240c15080110507a01e03403840402820010018000f2001900d1812124403000100900c034402d010b005008600240c0c0c90440340e4101401 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 601327742 1250 601326492 601326511
    0x308071205010603050105030105060f0a0b0715090503030106080c04150f12052d040c0311060409090303090c0e040203060408030a020d0e0d08092e0902120604030f090303080c1602030a14070909110405 88
    0xc110c0c2c44152881d0080d07140041c0724102940e900c0d814044003424070003000d415140035040911040c4192060000403842c4064a420000001d204100b02142c01c0199013072a4882c982c10a01400498042429008035600c003c01126000e1034400380401141c00040320040c00d42e0010b04820400706602c1801d180580c00043c083c9031502d51559401c4090f900d042908a0001c2d90310035221051164a82c0000d01409010503800784608068002a07900c20003c3c00c060515040007000c1112201d007030b411135030084103d540c2403140b000c0d041007094031034056000420105107003034001104c40e030f0003140d024125100c00202d100ca102c1e1441d41c03103010a1790650500340301075a0f182c0600c0544e0740c0364070383e41d0158802d03030040c501803030907181c01014010001d020f8014818000301c00d20001c0d821406056000c0042e112960300c5241d1043da0005220f0a0302c4041d401d4000c82000c1c0c0180602c10301d150643d5801034048458460380c4000200407100700c100c029008400101021505260a4010039009070009 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 601328992 1250 601327742 601327763
    0x1f140112050705060307091a09030a0209060f040911040f050702030403030f141b01060b0315131401032904030c06242606130308071205010603050105030105060f0a0b07 74
    0x92012680c80da000351b9960000c56402c0c0e40410114001680c644210348600303815506000a0001080e0340e142c0409001b44203c6500317001515170344031000d6071060700c54024000e000e80d000c2420644401e85085035824029402c1c42c60000d00201a402954025401d60b4000e502d03162070b50301e089600c032a41c042032104004114004440c5803060f034015102c02c1c0104000001c00146200d5960b0840300c41351301c18411108188100301520f5a000c1000569200640b1444400c468a0325558001e0600c000400c0d9107030100400841404040c140f400321400311000010114410401140b00b2000704030b40040009242e0603119000400b03039004446042e010b03a07402c180c500284404d17004d5031140b5802000c0341d0040085c0101c400c0008082b6074400000c00c502803c180d0a006d4101e240d60f000380030024040c0600400482d00700d606c0b8010f01c02c021407809900308815615030000501504d03081c4601da01c03a608140110b0040d1901c6031f41014596070081020030388510b0541d084a058004039000d0b16a007103103 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 601330242 1250 601328992 601328999
    0x3040501082a040e012105060712090209011412010605032d06090c0117060904060b131104090501060224150319020415140f130c021f1401120507 64
    0xa980180000e13104071810307100d99605005081c070516074002144000310160354080e401158011a0260700f098003031912050f800950650322000c0d0410f80030003034204020740c000080960080c03000032800c04080310b011364544001d90806080c1c0380ca9018842d819000b46003000ca120065140188294120380315005803006850109400c00c1c6c000c54000d0095044030b551b9171125a8400c1c03042003c0244008141c84500f00307100400e2284900030002804c00e0ba5549140d17010b69251005003004e81800c401c03d0102000e07071481c180d0700380c21074856103d4580c1000008241c00d40041075001c605880164205082114101801d18000016100c80480f04d810050180c00341c4041c44444400c1201c10729446504c07001388180000c40d12180e100d414034040c090001c2c05600d41c03074001d42017003102c00c071915041045c040b400625240d10007038549503c50300e0040301c0010160003080c100440c101c014080301081d010102d07100c06440c0d03502e2071600341844001c014031410f0301d40041c03014014000e1049401031502d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 601331492 1250 601330242 601330321
    0x30f060106180e0421112817040305120703050a270803030133050a05040f030f0b07320d02030c030907060314040b0a090b13060e0304050108 62
    0x2400d4800381e41d48031014078420400a03452175500085401403401d0a8140c80c0308200c1c0d5200c0018402007940d85000d40360a12445c00c084100c1c04c809a0400d60043c4140c15180000c442ca0f4058401200e10380985001812903d50b4441511036043c1c03d621a01d141403800340c41210204d003070030f20801103080c19003030403030021220015540160a14200544e0f072235041003070b0a600f4009200052400b41c0c01200081d40d03604400200605180c007070304010303868424000c0107588500554003c10070f500312168000003030006441a64094a001d00c000b0882c42e00c03807541c1200c501844c992041c01901c0e210514070580d41044d1180c1d401100b281c03080600b82400b201205040e40d00565500d84019408030510004031000c2c00171000800140c2410002e05040c00418070100324010409894540341d0000101c00303039040c1c0c1000c444503a00c5200c00d5264944109802e03405121003000303480803454054480e207549400800c580940d00c050310340308000c3e07072604911200d4007001240c420420910030003180c101103 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 601332742 1250 601331492 601331519
    0xa0e15070203091201150b030703180c090c0c2001020f01023103230f0a060c0e06090d080a050706020a032007120e03070302120a0c05030f06010618 65
    0x280e010b10307a5400140100480540303094400b18560b450f101c51110100c984904139070440b1412102591240d5030400150014a2141e0481d0102e4154a00e1a002c00c610000c524099902c007031010450940c2ca01c8085400d022a00c000070a103081088944134181888030102c0c24509051040b81c040700b403010b8001d42a41c02c402c80304103107001000201c4400d0254424251005407010058071440b62542c2c5036541c1400340242d100000c92947c00a2014400b800e110701b510300b40011048510b140590b03c2c00b000106511394807813001510445603107244d0314042c0110340207114000d00c003402861003034039448015071100d945103048c400200880030021b000341c005001c0b03100f4251000202e0251800014018002c0c2d41240302c0170311800c12001c00050a654050b41c0b24174014a08031502221140c0440e281180380d07000650300c080103c845251281c0001140cc41062007804070081c240c2c2c0d0340d41459510945140b000c100c83c0c0250006000303a03841002c4a030702c1c00f00d003145401c08003039843c14440c0c81d00 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 601333992 1250 601332742 601332751
    0xf0b0325030c0905060a1a070618020627010c150e030702090f01150528050d090b0114010f0c080d14011d07110706120f020c0a14070e0a0e15 62
    0x480d102c5082100740d141640006d0010010b500ba080c940070044584400c0751b100daa00d005002c0780da1580303881f442094000740c06d0f01403a40034080d103548007460440c290b05581044481c49101c3c0c1d034035074003503905d5200c0d6100f4000a82c4c4400b90002c0c449055500101919903110044054030040c080280940e0b80c0b050340500410f0140345e040b00035418400d03940061315508220394280901082034800d000c4450107080c840c03580000c9e1074040032103101e80491f840d200301909442d40030304284544092040903980c050403103007450081a01e5144450040d1070481f1031030001c50100d00408102d90202e400d0310018501707100300c218001002c0c00848004500c002d0280c00442501e6100500b503d443d10800f04101d0308040581002c00c0380c8400d2a00d903650707801041c002e01040020b07480039080d049003039420044207035204a20940d02c40e00c0c1d6083c40790b90341700141016a401d014103042074441420108605007603d00404400c1140e507200104036000d0541c26008104900c950070681011485c9007040170f008 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 601335242 1250 601333992 601334009
    0x6120411190f0b0a05070b061216081c020601170106090906050402030105070306030c141f021c0f020601170a05120405040623010804020102030c0a0309090f0b0325030c 74
    0x3140c0c1030480490b507440c0d094010100d021001c1041352022a00300c0192403555600085510380d560720b40c40803c00f03c10403480b0b1000184a10008003c80004940321081a07509040440e180600b01c05849001001140e0b0325101581002d00117020350003100d185c9a00c4417008100100d0020707a40e854030360480700d400c0e0046d62420303551070501c02103280030f009254101c0c210b440c040c807075a82142c445110555980c89940d15501e0001c00c18126621504482d280181a8040c00c81040c180c1c890083c2d19002009004081920440c03030668010b802101400700440c0031754001c143e26800d151841c0071031400030140c1041807098181e4580001c3c0200244448000000c0019460310b24041c144401d581403900141400e400504594200c5190b014007882800c400b440c0c414040d44071400140d045205048480810340100c5088400b4150090710800859128400c2000042200014142181c00351100e8603455000340f0b541340c107001c10340303080741105440d005207241c6050764a80e1140080d13000e0350f009010 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 601336492 1250 601335242 601335289
    0x203120f0307140724060b07050c030c151e041502010b0901080102071a070513030b0601081006170c1b010f1404030801030305071e030c060b040b06120411 68
    0x942c59440b900f62400718000e26000c600303204844d516900700c0885040e8510310241028030628203090981c00003802040581140740d51101c8600b8a81d4541e590341c0003481c0039119000c2c40c1925070800c510100a555031080065040408020046c490311b4440e10450115000900001c20a010f4440b00240444540e0f000019200300c410300380005804164060380f0b150f403040c450100421191031a0040c0500204a008860b95481c882618130b8040c4525400350300002660100400003c00c1c1d003207024a00980342c5013920781e034180c40c4003074802d405e006040004060000c030401c0d02150790981500300707980007441170030103007440f09900200c02c00c080d940156a44580300700380b00307811a1003400c0a076065442c44c1d145900d040d8070041c0001906100040800c000024402c06101501c040d18520341c420030028800c25029003030040540c100d901c0c0503031320113140080c0f00c02c1e07a2030584146c4030941c40c040c0400e42060300b402405131031000001c200f540c25806c82c481d005004da898030307140c00003054030003002c20 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 601337742 1250 601336492 601336501
    0x7170a080108060105060f0d062106050c13030807020d0203030c1e0703030504051c0203030a0c1110120f06030c0305030a1412041103153c0604090203120f03 69
    0x20010081a4004100b540204006100548030001180e0440303c12194156850b8101c08a00f4010041d80d031040403610740c080c1c1c3e10100844034028101d142405807034180400d4541c00005c000038403035490482003107001c004003040081c2a00c4050b000850004158403c0710800d034001c241590300017181029180c2005504540090b605030100c0200004030009020140c210303600902548258001c2da841101491442d4404100c401e044504456001d010b50381c45079021030b40507010b003d162500b2038060036a510280c00d02d0508012428024540355569028004070007000d070300034a1aa45410b5000da00c4103800300200307142c280e480000b07500c1640203554dd6a0044401040303540800450b8640840820521014000d1290f145400c1500700320585455080040007a14101e088103c8422010520b020460000d40071424510040810f8402460742080000f801340418a91a4a4110704e100400480e103503050591012407140d201804030390418900703002d007600b6074000b00c11511131f1810000401 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 601338992 1250 601337742 601337747
    0xc17010e01180207020a06200d12060501030c0f03020310080105010b0a0806031633031d030a02030301140303070f111009120213060b070302010905011103040213050603010207170a 79
    0x10308402c0421820b220481e0700060a480c824880ca20800048907501000d00c00c1c00725000c850318801001b150300441881c10043c080c0c24590036210b15032407900d40001842d501030700941810914598510415296000c1c0543c003e41020340094880c207042e150100e480e56092003664040c5c403d8240650301d491a000006011500007003a450194021404030b401c251003031300820781540d4000000342411003031401c1030018008000c41c503c4001c0768882c0383c3e00070b85800d98004420380c101da070492010001084501c507503d220328280301300103074000c10041210400c10401c010f03d40344001c042d0b901d0010651139100d40d50a940c403041c1c8200802103005101d9251402040c40f80302c0c641d041c00c0601603e001e400c1c1104580800000e4007400000700015403800c3c2c0c5621020107440814245030300d600850800030700a15100390100e031990f20301400710250314203803c140d03482694024a100346483d40ca41080c0b0113801c000d410550199000d10030303a00000c444501807414030004140c40c80d124070860400 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 601340242 1250 601338992 601339019
    0x1b010e1207060c050408030403060b0f101106010803130e0a020c0706050a080f0f070309050703021e011101021315030209041d0d0e0114130509010303051b1b040c17010e01 75
    0x100002e0000405c020440d805000c001d40e0201e0707400980c0040c0d0312421702c011541609080c9110ba50046030840b140c0202500102850120500803080ba40d00341e0302c980344141e40e4440c3c620710145501c3d0841040100104082c00c10341d11443c0c08501508001c0c2c501810380ca01a01070b0040302c00304e1000f240060010f0390240b17409600080c0c400d1100120304114100c1983d000c40900f8107820152249514802d0003010003021005581c0a0500950507070032032400420200042c00060006501001010300c2040500940c1c152004074103007528078030301d41000c0102000159541030b040c035400340030300003581d0340c0c41c803a00c2c001c4401c441d5000c1410440751013081c205000501040c2c04d1090030140000c1c00c3e41e100e0701010500e80402d600c19034805400060300c2c41d03004c0c1e0754002030744061140000f0040542c070002900b043d401d44070b000d1b00e00784403503040d0940710522000c49850500f802d8160120628298000001c401100d0030f250340c3c3c03a080e16000b80307030410090b00000d00c207200d800010070a000c2480c64 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 601341492 1250 601340242 601340261
    0x90406080f0d090617040204020c160504110720120601141c1113020c0f1b09070f0827070f0501031823062d07051b010e120706 56
    0x24203c1c0010b040c0600540789640c82c06629079002c190900050864a541e8100d95040a400c0d00f10b9070303032200d82c95102d015840c8030702509014a084c840e4a12500d03421105958540760701c45091803510ba141d420300042e044e864007410790f00c601c0c985682c00c00e605092114030b01030010080c0d400300320844d58042c00f0703100e8048252160126440d200c0940410f03560350f00c0004c06d101c104c0340200d0181c00811040040e000340c802e240d00341d000304040e1487c0c03010300251840d01281b04054035451000d9079400c11219010071209a0049640303004000c000500c90050b0701e0b40038040114080410f110303100c03030203241000d803117090300326500807034090243c0c003040c0a9000041800340fa007480345190311f16880242000f0100001c00ba102d041c04000d040303d03041c0207490008803c0008a40c0c00d8a00803117100503c88002d82d054294401d4841100041142c040e01c1622828603501c4844c40e00003803110381265526850040000c5550f547c4c50517003110300c2400f80715600f05d8641046030310b62885040800845400e802c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 601342742 1250 601341492 601341497
    0x60705030403080613110c010212090d0c0b100f1205060c0a0509010c0f060510030b060109030f0201080a0b12161211100306030605161205060303190203090406080f0d 73
    0x7003200280c2d01001040d801903054a0360500b11252024074030140c407180c0005c0d00b41030400b10305942e000030150302511201c8200d240c0340f47c0607126242165141c101c03006001c4c0028120381c400b10041241c04c4060b503000503005804c8081142e80d01c1115482c0c902e00c1c3c105150800303506142c1c4060000400c07000750401d003044103903440e1610700c00c40542035101e010503850602407014030784010300c004604001812600898107001500d480122003400d1242400f0450340d140c039001c0466499403141d500002502d6019610400302a00c0350015190317070700024140108907441c0e0120031100c1e210410142843c0b000e00f0014020424905003c0d1409a1103400400d544200e0340e980f1800f0440084440450940507222743e884001d0b990021000b40441c1c1c0c0025141e03e041800740f000c9000703086c0401003001d903107035580e4554104090b6141c007071b20b41c00e0718000d90541c41404078003200d041e00768030a5800101d500480389014000c1c40450b05842d0b840c3d216450703c1e00404030051070850240f1000390241460f1 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 601343992 1250 601342742 601342747
    0x203030c1813061403070f060c0c09151d01050310050c09030a0605150405060d0212100c05070b070807230705060f0708160c060c050f070c14012609011b080702060705 73
    0x124040c11307401f10302c1020204080010101c06011014038140094440b00702e0034040b0720011141e40303240d600e980c03103082100c006404009050485503448141601c0000f406010440c0203411108050309015290600e41802048140700301da80c104035000c1c0301c41c85582c0201e41032800c8100c0c42d401d080c00740f40803402142010100803141d80d0717602025112030790407a48840402c4910840070300d013012200e00c110080c1d02d000d08551100c0e8001015049051143c001803800d0750f68590102e07490744082d14403a0101780d111040d41d501000c0c40c01c03d62014013140340c1c03250900c0f916071107842c504103081e160101c0c005006011702000c2a441050f00e0790100c070400a000c03203115007800c006c02415410b10083c0c01c05652b010b100603c10710803011030301410982c1c500e40c0d4072020142840c011880d4240700d0443ca480200342212444d500408800d00300b041703801c03444201e0426001603482800002811907085540e00c107803642c82415540004c0705010025a101c0c03074a49054100a031916102800754014030105 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 601345242 1250 601343992 601343999
    0x7030c110d0c051314040b09060c090603160e040f02121308072013050901060801060f0b090d0816050d0509060d0c09030b16031a010203030c181306140307 68
    0xd40c0303840c100d0f0703001e4455089180e0807940480c01094012049150340b03040e08148070512002450180c09555900162003664507032010001c181d105046602d60003000601c00079900049503480351a4040300c41c103104030100c2c0360200003011100c00032580030f03056501085c0720600344180d02050703034404104550044101c450351207200b498040c1f6400140960300840d0b92200d01d452206a01641901c003401c856000300985804801070841111806000e41c0f03440c2001a186405015007000c65141a0340612140d04145160140f50310408030749401a40c04480c1200145a140083c85c41600e4400080c1c0346040614201e0b050100d00381904c0100700302440089003950320720040360751910f030400d8002844503220906031139182c516400945070f0b42c00c180400020180700e07804040304403001c0d682007104968181c1801210f05940f40380600607401400040d071000d601100074102c0c0d11088184105030260040019411010b0b0600c103088203844050401409a2a003032100c08070070101d0180411506 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 601346492 1250 601345242 601345253
    0x3110406031e08040906170c0a062c03030c01060e0c0a0503161b0b100501020613031107150f120e0a080f0f03150f011103030106050d02040b07030c110d 67
    0x544010740d103901036200b180800201c98201c800800100f60305108942c0d07a4000c0d00000d101041e5202c0540c01006400000d500d0704a0299007072b1051512107402c3c00c0640d01da800c0460b0341740040d01e1100d0129588280705940c00300040c0442d81884000400d680d0b080412104c40c2503409080520186030030301c801000035030002d05403036206c42100c540852060b540071080340c2404595580c01c907030083c80c0348840203000c0300344012032194080703e40005440740e8030001284e9480048a8045c0b404500900700f20000f8400c500c6200c04a6440c030454031010740300c5003401c400c550b440c600340c00468940703a007081b00c1540000c04c070000e0626140c1c0070030080440c2c1c0c00f11131b02d6842d20304000b07104100001c0c240841340c045506071402d10303e009000548030f103002c2c904c541c0d00c41114040c003482603420a00050256102c0c80c03805003120106400303941036900c0d10005891030340000907840300c0303030307400b0710000c100b42c103504014008882c002e95402080200c40d00742141c1c03506102c01c0a502940122100002044 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 601347742 1250 601346492 601346513
    0x1e0603260a050a031e180b091219031506020714040905032b1e11091008070c08070501020904050901021e03150a1d0903160807051507090311040603 65
    0x34003030304010030b612a40c1004d401280b06600c010030803240c82c050b895101c3d00461015049010305c10f01040c045501d90519043c9e48180da810003403c0e8550130041c0e02081c080007095511911054100132800240100e410500340c24160801001680007810403c001904041030115255054400700404006e50326082d03140e104400b0110b04089401c0400a030002c2c0e103500c04d51952040794410407080c3d07060050072040c441190001c2c00c0080c20503105541e1207940008881001d44014284800c0200040c016a443e11006200c10103000342c101d22800030607600360050404900c40c400051b900d80d0135504100450740c001d461010968410321803803040200ca51522a648035140880980b03958a05c243d0440211314400c201d038104150510004022100704161805d000c103813802c0801c150340c0d01580d01d60301e000710004200c0081c05800100301142c2100e004200795030088081e61102200d5580b48a100d82d019035007580005c5c403184040061055807404000c403503408840500400740385444502078030 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 601348992 1250 601347742 601347757
    0x2604030315150c0c0e010e01260316051501050307060e120f07050a120f08030403031404121b05030306150d090b060a24031e0603260a05 60
    0x60369121290400d10455100310001c01041203102d00400000310010703c0740c3d190040840ba030035150300c00464109032462415040e2800d00b200c40040342c0c07078190b0b4408045141d07115502d42d0501c50701104000007050008200000c203216030340408032040d18210349081500b00502071880340c0840180a550340108400044032001d2a004080484100c0080c0c14519628070f0b1414038800c2d140c4400c000480445d50200b258403c0300c0d0724a0f01591110303c2c0e2501079003044000c100b4035540f002c1c0703000281c9090146410500900e0005902032a403401714111510986068400401140ea200103055200c8520103500c0c120301071520940300359580b01542c0c0d01014040512800c49124800c070500c01703010948130f00030140c04044c4800c44480c206061482d00a985060080780410030200d10654a070308411210307200e1428288039000d038840f046000b00380700c10761034441011070380201031502c00c94054100914000d00301301c0c40c904500c00b600242c130f1036003000d8045104400d100c410303d011341207005d41c3c1e141d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 601350242 1250 601348992 601348997
    0x20607030509010b03100501090b060304050a0615230301061e03060506030a020916181508060f1905030c01020105010f0e070903060507020f0f010e1f090210020d260403 74
    0x10b40b94881c186016007403031514582c062044910042d8600516004103048456800b410070001401c00e050044a2100b00c40280155109265280028000d9030041c41d045440c0a556003c40d81c69240c0c50f80d9000900c200000310313a0086800010910b030a100d800c0003007141d20780c0003c5200d40b03210f451200210310710010f08442d0b0340f28001591510b041c00401241030f401003450005103480c000780704c1005449904c0400040c103070007a01c0c0c050041c0d101c81d003040c0c85080b01c010548201e1a541100c00503402004550098800d000ca60025100d503580c5002d840340f22030468145508000c1418503001c01d40940c141160704080c0100000c0501c40720307001c165043c4400341809076035060010303100400b869200600c807518100420060310ba000c0703038070060f5406c1070040d42d4840225101c41400d88504400d0303189160070094018038194421100407000007015003001c59865400d8000400381c0030a41400340c0540c00110328401907542c01035403c0500445010702c8034150741c01d83c002c03a181c45070043c0000d05 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 601351492 1250 601350242 601350251
    0x2090a05060c0c04020307080907060219060c0c0203010e070302041802060301051003020906121510050d0906140a0b1503010b0301150c05010c0e030f0303010b07110d151407080702060703 82
    0x61582c03051000000c400c10141c025540c82c10071000082c8820801c0710401154080c641340400c41d1803010680302d90000c85030120031a50002ca803078040040004d85400c209201d050304583e001600e00b070003040461031038a07002e007113458910f0043c0401c1d41c2c0314003040150004c15448190050703442e401643c0c150340c0c0a46104140c804107080c203030000e11407282e1a5a0240003c00d83d02000c0500e0611903200340c198031040c140c0015414103100351a40341e401400d0208606000c581e100740d14a40c0a411054010301003c903020500c001060400c44064500111207500c40010701024103007120005181c47c10079090342d182d90715251081c00302d4041030080400e0005070004215840c4c0c4a0003c002c4055001402000941501d01004e01300060240a89009029400000500380b00c04000c0da4102c0744600c2100d898134456079202100846285142a03101e6610361811021400c1130260007255000c440700060303161004a515002440c2c010329641c108481201000415907003c902d090700003145040218 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 601352742 1250 601351492 601351507
    0x150e0a0303210207050309040b01020d02060a052d06010206010618090504080f210a02070b01171c1119030c03112107020a090903090b030408130909060f02090a0506 72
    0x4004102e0b41d8808018140045181d6042c0000440100345042088900700441010b00c001644c40740c861480440141c2c0101000504111850704026400f84948001544c40c000e40208200f50200c1c90305101140b80c00c00003003011658041010a0150a03a802c0c200a283c80c50302090055081c0d82c0550450a5142c601040400c803c013025140309038445c01c400303a10b0b102110080c80007458021030034035500821340c0100301051080d00c00c4906803a00030b40030701c1407a820300d040c04010242c0780b400400c5d64843d1200e203800344010801120201e120903079076100c801c0d120b00d43c41d900d41105a0041d1615100d000303c0d00001a03040418403c3c541e81c1810b104d81310750000901ea03802e20001030341030910944008003288801d408030005041107407084454420094882040a04403108140c0080c0030a000d4034040c4402c06141c070145600900c1258410310300261140031000e43c1c5066880a00c880d03885420391004c00026009103019684419000c500b040c0403040003440c10400d81c4038040c098880041e414 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 601353992 1250 601352742 601352777
    0x915060a11010207020a09090201020d0305091e030d02031609091b030e0c0a060302252301150e0609090c061803030d0c0918060305030703030e0a0c0e01150e0a0303 72
    0x413078441d41c004083c0c80c1815510f104100142400080813801801580e9850000c180248a224040c50700703038000307060035030b00c501d6501d5840120514002c4544024401c0300304910706400154402c0c10944149407250700000000b0308004a5038100705400d50a000f038406501c3c5c2c0d20040d0010780c0c0c040b464045035900c0540446403c0007040e40415801403100e8001013509901a001031401e0b0f025503030400400d5002940316900150521801010b282280c2c4102e41080000c800e40880d41841d000001410400e070307030855000315030607030000c04501008010056103142403054076512030040d90241c240a01c400d00082d100303108142e09803003000c0c40c2c0c8007140500d440c00c20558030480001541001036030b2038400b010b010103655102d00c01a45444c40c0007045402c016018401c101c0703074403500031402c1107c1d070740d000d5000d404090000c2c5424494a80c008001c01c3c0c50205000051030b151a00f02102e505011f141015542c4007080c03881030200c8552413401d035440d00004041204d41510b010b00240300c2000c640f = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 601355242 1250 601353992 601353997
    0x4151d0f0f06042403030203091c0b1609091407080601050c15070917100b030d120b12010203180712020f121213080d09030809130209060a09050915060a110102 70
    0x1004104801383c0b002008041d00040241603104048034070318480301a000285610071800d50700140050a80b40c0030920b8001168554480c078155418a0100f841e1540705040c00c0b10741d801d48400100c0c0c00d9a040c40074481d00078410039013103602803034000d1900c00304000c601d6440c0f01010340a80d80c0c172206400035002610410b901005050700083c49682200c412020035034030449012031103841441e00d840340c0303907031314001401e42d41c0100151981e88000e1350507079000b001408c0748550f080d0010f80d12070383e56150032421700c02184030311521031260b68000742c07481c0c50604d003803030366040850140c010503104005640c5d0940e603070005001c04c9813541c0b82086800c000030f007010b0b1802c1101001840208030901d14403100b21205083e95043d004850220510300e9048850090a200c040c0601c40c0c100311110321390510010f41300c4400780e01c040151402000001040440d48190000e10028001d007205002da450b141855a030084001c000da080704080e0301d4006011171080c1039105040c0070310201a0151400203406 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 601356492 1250 601355242 601355291
    0x81e180d02011b0302013c020d060e040b0a0e01020a020c13060312051c0506010804081b160905060f03120c0c09070809150903040b070204151d0f0f0604 67
    0x1500342d10309644c94060f002c1c043c80c60441a0307140070280750010311002d0003100401d003005503600f101c0c0201d14000d003400035404880c0b0075074030640301c10010400703054000c07074a4011031103000c040241d0700e00200f501003101c1880c01030310f4a42c0d0041104864080d40000c0011038042c04944401c8220380c0000c07035800030070090b8001081c141c405031030091101e4002000c0d00c03012030160b840c800d400e00c01005100031200111500e50100359004003041c08122408050014511025104002c13a00d09075146403609800c8110000003110380c04c801e002c8207401d0300400b900980160b5402d6040d040c2d810001e91101a50410110007410208010301d004104100c200145003010300408014146410000c0490380212101c1c000c2d4494a829455640e4418110a1058803002d003d1350034581414418005940120400d030790194540380510700c030400c0303061082e005142ca103091001c02a030760710081541c0c990081c6185401c60b07070034080242089044644582c0041c0c1100e0010320022901d224184c05032a800 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 601357742 1250 601356492 601356527
    0x510050d05090d080709050d0f081c05070f02030c0d080c12070513051210020c0c040203162714011101180308010f03030c081e07081e180d0201 63
    0x40074814021000308554000350f60071366441e083c41d995400259845c014500c15150410303010980305c80851034200c012400f0324850000340c0d14200c070304501070f440c00c518050f0810398543d540e0103201903142c0145403003401c00b0817030010b5410705884528a507142c012600c03003403046c0811840002d00e0501648200c8601c400074079485181e600b0800401031a9401c41513041c11541075180c0c0104040c80e05041c42d00c900d00c6c84030004d05183c15000078140107500104e03540d59051056034500786007540c450001d94424054041c00300489543d141d0014220616a5a0b0b00c8000c0c4c04420002910240d42040b401070303030780b00400301150003115001200c60813020100f01c803440d46400aa4807041807075404098100f80607540d2000d159886034100150a0030b80e00c0020301044000c401200040c88030401703001c6d810084216819428134920030000a90700001c0229080305001230001d000c2e0240c010000c20515085480750f040442e514906203801c0ca40420651041d80b00040300700c1168841c2c505a06601c100c1e0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 601358992 1250 601357742 601357751
    0x4050a02060309030702010e060708032e030516060509280909140c06160605062413090504080a03090510231e1b040302090c0301060e01020c03070510050d 68
    0x300305601c4c2e41280c10101e0010724482000241c510b0220240c80b40c880c0c1040100e032850b2215103e141c84c500c40c016004403d1003004074811242054685200001c43c0540081d2891004500020211581c190000400c2c004e09210602c42c07516503a698101c0c0c00210902001500044007210040c0241907009110b51404c0107400380030013441c0700060144d401c00c2c40440c0c80d0000c5480070000d25008007005454680c1c0d811120300041002900a00d4104602400170f45601071101a120301c10011000311b400741682c00101c0426810380c80e40c1070303402030100702c5081000e820030b50b0b10f11115120b140c0703000040545480100c414003100b80952a8000d100ca40e08009424034000750035200122281e0f00c0302c4200b20301c000501c00b100c0080000070070300d00110b921241c0e5511500c0c4c44003104160404060028003d01c401300040c0c5504c1111070043e4640104240c8961500320000c14410801a0083c11074018003805052501c0004191041c1c1c0d008580c0b140d00340840d180100c0d00e80c091480c40144075400c0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 601360242 1250 601358992 601359001
    0x11d1f0b040501020d080c0d1a0301060b0a023d140109061503060b03040b090708010207030c11030c010207090218030307060509060c030c030408070f02034206060304050a020603 78
    0x600c001407084480a03001c3d03c000c4409018141e600e500121000007208100300445062400c103688580e4044034280150140c4010307100200b07084540c6030b08000c4200d04001349082800e85c04015842600144880c0d44010f0512655001c0600652584040702c20142c08110725510075140c1014041c110b90317003452035056a40d002104040c0c03825128003d09140c282041c1c980d510321074050301042d46d0b02d40d503c651a54807196115086410014052415402141000b01c0c03250800c0c00204000c074000e94034180520b60b1400c1030303103082c1c040d640c030b5502c00e6201c0340162810366004110001111481240181c4802c00c0c2241e0110701d4083c00304507036041c0000903100c42000000e85c4014010a03506045540c56030320703002982c40c00d1100303890341010f40105000160025400900a10103948515042c080008069001c24030340103081e010300700303208a07e490100321700c10140c1c1004030b48140c400d500c049510011301d00d41d03003241d009010300d070240c000000090140315040088003d0a036024080503a2443c1c03 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 601361492 1250 601360242 601360259
    0xe090405100507020318060a023a08090d110118050f01050a09081603050f071a060f06040501140c06010b0a090f050f09041412070203010b09011d1f 65
    0x24400040e581d064070746000301c1e94161000040e01c4403101c02e01c2d071060701c0d403280350704001c0d039a0009085d110461258060032600d00004c2883c22510700d00c00f00c0c00b55840c0d00d144000030740041190a03548100a036100802c1070040300014200b01100003820010752001211a84c0c07070143c00f17080e112003001e105002032001003060004101002c184407200030000c5032a90700e4121300303988002c040908054001e0107485e070b0341c50901d919400240c1c485d081103403510001c1500d2038010f810108040e100c03c0c4850012487c0100c40c05ea010340d01101c1111854827950116000808034000c0d03018150410002d04407007800c0d81d192904a90a40c2164803c9070300c40d40e9104a0000c055000c3c2034000002105080009080050344401d0016224000d1010080315280420700c03140340001002558503480902607e010200c0500000000c044810b0089680e44824018542580c031261b010b2401340f10004010004088660000407024040305668086a01d94804074001c02100c0c6030640080ca9840500094040 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 601362742 1250 601361492 601361503
    0x90705100f0314010b030c0c10050403030c0f0e1507060605030f01060303140403021f02010b18060a06080c0306010302071a0a0605010f0c200303040810020a03050105090106020d0804030e090405 85
    0x201c003503409105481502c5602000d400080c81486540d0b030040c00404c1c0910114005001c8182c040811140540d404075000001e488065070154046692000c089016980c81200003003011715a0404850042041c400b25590001020703100701c580e031011031068200034103a04032000408004040b109a4110001240e000701660301c000c40c0400c2098801140741c0303004a00762400c9a0700202401800c4943c07110a0f100d402080600300d0441d580d0ba030b40218036507200401c2080ca10070540c1c03561003901c0d01c90305000003110a0b800c503000f0b0020b0340c0308010081c1000300442e50720417403c0c0781c09a20b802040c5440750904d12184001c13002074a04104020611646034011000c60f070090b81c40c1d0458094019082d6145c030f61041d00544454500910302e0341c0e41d14070035101c0d00300c0b00c4080c003141d2829a0300c00c40329050200355100c1240041e00001c44041585d4103014060150030308403141d600035490908080c1da2240c89848071070902940c0d200080c10b040c0104bc5071080340d10050040200d924082c0351007600c82 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 601363992 1250 601362742 601362767
    0x11070203010f1a0904030e09100b1b100207080412081309050a0f1103070c050c1810051503041511040b0304051b0102120c0f0102160606091a0909070510 67
    0x840c1480445103d520700040058000c64140c0c581055030807040c070a020f071980c00100054440341c0f89060004050403048014000c400c513401907030381b0128496065508080c000b610424550f80180b0201c0041410341027105c04540c1d1030031001c401203003546440f003424002c41c446400b0303002039403000184042d42500003511821690b1000c2010080d100443d0048840b00b000303d22403100c0a200103a280750140c1c500c0840507018104442060a100c800607010b01c0300342c04551620f102036000e01402045a04201e07000d81012140d0265042005c2c0c4007840c18000180050b00d620302021443c2c810908a81c0211011900285203903615601c81c204071400b07a00c1581c003240c0354400c2d480b440c1d04400207405010f001070390503030103001c140e0780c21414601c0d5604a5000428903005101c1c002505000c24802085298900306681c00c0c006045d0400f00101c414940c4070803081d40c00d041c80800302005811603030103504012900a070907030700c1d040d00300e0f4a01381d0681c001b580c000240b52035104007181c1008295038034 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 601365242 1250 601363992 601364021
    0xc060a020708070b0a090e060a0302060c010605091e07050a0c0c030305070b061906030b0301020c0f160e090303010603091505040c1e050a0603020307110604030e120f0c0411070203010f 81
    0xa43d40d82d960714814038451218032400103034a20f01c060080582020380140c102d0801008101d940f40c503a000210b1039481402c80804982d9680c00821441c01c00c98415076102009941511010008600110fa2550000c1000c2c0402034001906100c1b14080d04190083e6600400c0b19005a1f4503441d0180c950390103942d00742e50401caa28000386241c6000311507008480450311115411034a07140742500a400990301c0694155000c0c0204041460104000400d8103580401040c611540b12800c8041e584103800004688181c2c001f0003c4015000044a04440c054580021480720a040441c80949030382550b101507420030341400240301480c81418180c0780a0070600001c8101c980c0301e5502803040d4490039801191101c0100041d500a0b40075660042c03041c1402c0c0c00c1040c03a034200600f010003c03141200404d0f00c00c000c0350a00e0900544180c0c007182c41e440100a01c000035107820781da681040e014184290307119014050b440210b48155100e0035800390090000d44100794401d4040c00c2c241801403c0c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 601366492 1250 601365242 601365253
    0x1080304031a1e0a020d090501060609081b0915030105091606020309030a080307180303020d02010b01030b03150702010e030c0609010c020105040f08072303090f0102210c0c060a020708 81
    0xc0721048024100e0150110b40c2c0e14041c5540303030035183c540c01000203001c0651994203001920701c822480c018413070300a20400001031044d06010020706051042d401c0201039134850402d1025824512110400d81001254010056500c07100c113100d212684020841d015400c0c4800d00c07130501c400040b00c07214070241c968124109501c0c1e000c100d94034026015940d50541c000d10f0503e01140c4904011900303c045440c3c280082944a00c800d44c0c182c120740e10840c01070b40030901c0d80c81c0302a03080c07003140c8420000b4030b0207005200c0c41e80d001aa84800c003030ba480720500000c80c00b2400e898001d601010b02402d05c0001c0e2921003142c060075a48598044482d11842e50a004d5141c00ca07a2062182c7c80c444d036402480c2040480980d1150811034008100407948030400054908040d050180c103625180050001103130748000c000b0601018640a032440ca056500c4140201c40e008103e101102d5155013201c54540c40300c0803400b105181c0051000c0b0380360406800214071315140e6010480c602680c2d00c2c94101c65 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 601367742 1250 601366492 601366523
    0xb040c0b16020108070206070f05180d03090801050a0b0d12030e0d03090c05060a08070c1a0f0406201605031312030206071e0e0612012601140f100305060108030403 72
    0x7c5e10785600315007400c00a100d842440030035501803005011802c6866039891000c10902001c51101003103840c040d0301040701e0701d10401540070240106a4484205a010f00901c0e81500c0400c1c000c0300c00d10341c0100310341a08007091581c03510070740c840d02003d05144119a40d0000e12500900108480384052300d10901441c0d01203164109282218404003456a801d912507403580303805c0f174a0240c221412070760000200001d0110f070a0589240e07000344100b030003c5105003018500701003101e0740c60b54007145410103050726900c030040c00000e613080c0c0000b5844481e8107961a00e0f0a60452040965126030308017180c0e00412900781c03522955031414800d4084504607259100706442e50307884c800049500c20403e4414401952145100fa450130308003030416814039a40c0025038240d42002d801400300340fa4621040f01b0848208540c1c40050b202003002004403100b450390481c1c16510040040100c015441b0219010744c3d4003100350001143c101003900c805507151003885440b0f0740320740702c03d5801800409000 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 601368992 1250 601367742 601367747
    0x604150e1603090803010909021207060801060306320111030309030c010b1e06090a170d0f09081510080d020609010c030e0309091005300c0a030b040c0b1602010807 72
    0x407103104d401c1a0340c903095a1915500c1c1c009400c01501c2260044680c006000d2074440401040c405400f86460311031096052882c028111038882d40040d0b90143c800c000300d8050601c500c1400c0104451080c0e03001c20b143e607040140c1d44060f0600c00707520f46100020800158080c0400645451950f43c0700070b01c400d6030341074100005599855205941031308403040003441d03803800c40000c119050b805032641d9506a940d0141504050582c0d10a5a4a40024642960709580040e20380000d40050030482c03000d6082081007a0750b0b60a5840d004c1424400501280d040580380d031100d070042400308211254096090030003922010262000307005582040160540c0746d000c0c1c042d000480c2010300045092484035400c120520700d020b030003c944000c60860100301a12a12108800c00403100f0081c800b88001c1082140c80b40d90304045901d041c0c1103000f00c10f02c580c3d40c000c00381c41126040001c240b840d444904150b4505811940600b4040d000064000342c400802e0030441d40c01e9000741c03115a074503038501506 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 601370242 1250 601368992 601369001
    0xe0709061e080d0f0e04020a0305060a061d01050c191b0f120209040213050106051b07081906110d052508070f0c0507120506090d0e04050604150e1603 66
    0xb000100d0304001580c0341d550b403103a41007001031009440c015a114103004081002c0341d1000b114800065118810010981800c10406000700924a8802c0110700d0350401064803c0800214a040000000354180c0b0ba40741007001e4a0048071340810300e003072100c0038070303120400b01240002200d041e41c2d14040011145d0828a1070f608803030a422101102c40d84640c2001809080180201c0e80f003610700004104146d01c3d8803e80c2e0207050305859007541e40040420341100100c12011400460388030000c2481202c20111301400180500c080542a480c65450301401a005000341010394440210340800c0400711500228022a011311409a00031001c00c40385110003010783c002c0000c20700c4000400c01207413141038508a036009034174140e4501c6d0015560b0900300040b980c03141d1035000100c0b008005024007406803075000b1001c40d008041c0c40888280213001c00d154414100c0c0705030380d1030000464a8585410440c0ba803203822520354481e0313132901100040e40e0401d640030f01035a00b02e5041c1002c4a070183c8078 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 601371492 1250 601370242 601370249
    0xe060108031c110d0501061211130501140c06070c0c0e0615031305030708090f120c01141b010e0f01020906070807020a0b03240a03020915040e0709061e 67
    0x42402800c0c100c14400b070082e060721404003110810030894445503500c648071340d034080c11460351480300190400c0e01c44019120709030503403c002e801c100105c3e0000d801c2c55030f00702d00300c030000c0c00c2c840d10504125007028554011000c400d04070f40100340801c13840781e902003070f07401c0410b10400704102101e480c0c00103040c99550844140f03030440e06d454160903540c05001c0c0615404003068142c104c4102c015500d85045400001044034844008100b540103454841040074110174103403801c03c4603130510390101c0d940768401001d03075060000c2c05095640c450140c00c1103543c41c000a01c203881c11124030340f00550080002c0020302e0894080c00380102c031050b106008403600c4240040c2020704010fa00d07240d036143e560001800300c1c1d010641c01c9002800301c030140b000e5481140b041414085c0300741c1204400c618002034110103807044031290300c20710060b038489845a820002c5103c902c0c0c5036401800218000300000400040035100314900004c528072150041300a0703424000500031840030103007440d00b10500902 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 601372742 1250 601371492 601371517
    0x130e010b071a0604021b01060f0801050c030103110103060504112205100e041418060901060e04080a210f060503060105030a0b040c0b0706140610020601090c021c030e06010803 77
    0x1006180b150752020354140c0c000000030300052400030000800d100d401405049007149035111001001800e80303100005000788180c2000b03024600c0d2030707000c100841c44140801000d181456494102d141d12030f0344000c0c054039014108100760440c110080c1010b07000250010520402c3d03146c0040d0301030b5801d8041c01260005040b203507801e0710000040c1c1f660f58042155039041560b40042505030140d0b500b105000b4081c5400403036402c041c002029090020046c5841000d03814038034100b1030301200d59041540329400145c070b070b900c4110259044070704100041c030024600c9694550070149811540c4156100c081d4030b50f0404c15103a56105046d141e40017441a0355150304404003082c0400c45020140e42d2192207194401d031007a4a44202c000a40c002403008d41c3d006944500f4462001d100c811615000351045880f01070000500c4c0c1d00a40c0d03103405004640300e060b2540b0040d90042d00801411455911400002c454002040c80c010024200c000d9420100e02c02c220001400c024044100d465038041c03503 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 601373992 1250 601372742 601372763
    0x3190603030917030708130f090e030d111905030603010605010e03030703031e020a2a1718060f090f010839120702120903070e0a020c03130e010b07 65
    0xc6900d482c0c40e07844010b200400d00003005102e0020711070388000c0003910312104a4101c40e0341042c03423400e4810b5031342e0001c0380c80d1f500e001c000c0806503900009031200d480503c807010a40300d00fa40c2070102c0c1406000314802841d40054540e2a1198000c00590301c1080144d00801803541c1e0b460044401c5280a44000d4041e00208259408203119400a0640d50041c0354001c0d42a403440b8022000c0341c1c85002c040001030302c0000c50f0f010750000700c0c917044000b60f402c0e8000803205680d0303180c8950108042d0407105c4d011000152a203a0030841800d00980d01c84020081038541b01182611500766200c04c050600c074840b0590034905030b6001d41c6109020301d2500f02428056a00d90b80b0101a80518800000001e10340400030222004601c000b0456140c2241402d402402d012001078604010a95001e00c5403900b446800c000b91030008140b003c0b9604221041c1e070940314019100024070030a045a13400b03000018600b05241c0d00e031510041220301711140820240e0f038686404003640600300b00182903000e103 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 601375242 1250 601373992 601373999
    0x1005030c07020d020d0321020f0a030b010e030703080405030c0d1703130b0115020c0406050609190b07050d020607020a0305040608150a06030606080a0b033003010605031906030309 79
    0x5031010305507003031000c0c01d80d04000f407054000600c40302d004501100003c031340c9104078084d409407007001d442d0704511000941c01c02151310300b00121801220000000c0668075004103205a11030341851400b9100542607490642e20b90501c1c0b17107242d0050140c0c03802442049110501400e010044810094000050700d110300050a04001c60707900c041d0a650fa8442c3d006a0800883c00e60383c40f4600070b02c513280d0021f21f9140c981c00041d05103104045564401d45c1b414000300010780b143ca040f40c0c16054110b51607080c007400c071545510721141c41e41017141d11070000700300e803410401c000807030250201e002d400301e46465965800c12680c079400e00300014000f401c140010050180688000742d0003d403020b403800c0d000c445010224045032659402000000e80314501040206e03006004140c000c001c10800340b14200c880c4001c641d440801510310034002e10202c4502502001120340c00041e060b00000c102c0e640d50792584010301c3c542054030380c402070f880d054002c020345100c588142821240d0503110003102918 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 601376492 1250 601375242 601375261
    0x601060f0c05070b030c0c0c12060a0f0f1802120304030f06020a03020705010f06090e0c0a17210a17041502032e060e12030f0a21090b06100503 63
    0x441d4404842c01d2195442c0864004c1d01303000558414038144102544403561240014071700356000b2003036400740f1810103c500c00c40342d0205040b540014003010106001071000b48500080000304484030641d032402134500d031246c24403804015528001c0766482c6004104264458480c46a840010b092010f0000c0c2480060002e030007800c51b68040d070600500700f141c6038940c00d09580107a141044070340d680e5003007802600c800d842062110b206650091205041c7d10300811120501402140c08490781d5901384104074034100b00041600c4030400da603d1442c4141c0e5440d04a5401c100302150100311b100201e03d580064014000d803155801aa8103d41d000c01c6400d100001d510260002005400e44105180e03400c0c0007034808e400300c05106c9100c07006e4a24054008200300c0c059000300e032081c6034400d10305945d0440042580c9421a030030603156941c45121409595169081842e90228502911031072043c0aa41c0d100c1c09840f80070301204902950b0b0f0504010300c0080008a80c800f10390300b0f1000c100c5081 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 601377742 1250 601376492 601376507
    0x8060118090605130b07090e2a0708030f01231e0a0e1006030e030a300c1103040614070c0504050f090d090e01120314030114010e030601060f 62
    0x1500080c000800407030315201c01c0162401101c0006a002c00041c5800030030a011030300e1a0301100300c0c40e00000d00d50618401154091000c0c1c0f03001b032058120040412030040e4440300100d020304c0c010300150341c2c042a180000b40f03034004540a04030100f41800000d4001540305481503001c89031001d43d03120071120b10400000f06601d1040700c64510191010b400030b0b444800034500034181d0840700d403055103005540424102da66820400030541020150a0441d2000065a45502c0c160412001d03040c40044014103100800103c42076080d070b049035640f9aa90300d82d0000b08801003a5480d00c2d00e10088850740c590340d100d58417800c000251001164100c03640d690001d88805c038443c52a0b00545503540c000901034030f005681306200241c2c0d0b41c0134045104010090355101541508181071100e182055200040d07905102c0c08204441060311082014450380b1a12542120200401c0e140d5031111600140038428050300381c04648072100c41c8050303280008002d030484400d039079248110f4045240844412 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 601378992 1250 601377742 601377779
    0x501150c0308070306170f120a0503060d080c1005070e030a0c18020d0e0706020706080f0c0304050c0a0324020403150b03120403030503070905120705040c020f07080c03010c0207080601 81
    0x35070740d1703540800d000602145100c042c800c3c40c2c0092802d0128020348900f400707031000f2000c1f0103800800803900c059030020150707580b000b4101c906840e0740b0300f2410003403c0d40c41307031402c596480d0103843c031124041840c1e07922040c01925603a0381e49400407000002d0650303900da01c24002c3c101811000040024921701000003044c40542c030005400d1682d0000c07004140ca0071480428643c0e0444a02400803542c1040908020412494811800d050000c4030000b0400040d0840f19142400000541405800c003e0480c11100c09402040100d9883c1014100482d4841c42c0e000740c4060011004040c0086000351801d8903000034015042da000c880b8000001c0000c2c8100c0ea0700742c040c240c60590081c0c0c603003000d07200460213900c0781d41e07682c0340c00c420080090183d81c102921802c0074402102035074038005550002d599080d1400509c60300c0000050b480c045851462410a10841c10302041000b004a2240600710058000f40030350410907074140d845200e6806288403550004c1c00400400500d0398001050 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 601380242 1250 601378992 601378997
    0x10c06150b032502060103030e040f2301090518150612100f05010506071515050a0b0d14060108040f08040e070f090e0907030807110405090d030501150c030807 70
    0xe5580c0824000075001100e101c1d001241c09051404001d5203003092186001481c4003800041d8110341e0060030429101c802a400743e40d440701c0c84a50000ca0b0703806030711100044036448501c10546e0701400750070300c800d00801d5012814140840c140d90f200802c0080030035806805000c4203040c00026016003d401800103503c80d444141c001d40305c907010b111074080500000c3d03011944e41c0721541e09600307030380c4180d011500030441000303440c0100d20700e00b400070312900d0050404504c05840c0c3d84c1444031403019812a5030f00004100000502c0c04226004203600002a0000c0c40300052080c1c003404035407000c607001c9000ca42841c00050014248070302009c2d5003803242001609003621045031920301706c02124040041207418610418458009286100400c0180381254041c80d03c1020076440d07442600c0020704c001004609002081400200c500910343c01800420851130400d10140c1d803400103002003400f10746040008100501101214100343c030043c3ca900c52070b4902030340c00b2200400001e212408 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 601381492 1250 601380242 601380281
    0x7030f030c12020708040e0403050c01051b0301030308131401060e0a1a09090a0803010906050f040501031104090201110105070201090b0114010507020d02030a02090106020708100b0a0b2808150d02010c06 89
    0x500d030302c007d13171040c0c0994000e0f6507d645030042148000e08440c1c018000d401c80d02541340e1444070003503600f03003203078192503043c6000e03600d5407034170031648c0902081084014003010034241030000400c4150710803411181622000a4644c07248041d41e0b04550080c4080d00c5d410366290010141d50601400310741d003101c0d81108555030200640c4481059804c00c0c0c0195141e1511480100500d21703006150811009048804020952440e614401c044090a28550107151a5442c52040da07008584042003074a886009210910785030b58024020012520102c079011100000480d04003440019a181e1403010f864542c1751080a070204403c0c16071b0010220390521503a40d010006031200d0303616034001d21140e0010f207402420310080380e08065014641005140c0b800407107001c950f807008190030032a0005c0551503681c5400000319624441071140c4118154030303410031643c00a901014030ba00c142505000d000b08200c4080c2080594007100070064005000b0940000100382c99a00480d24130123228002e00 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 601382742 1250 601381492 601381499
    0x30c0603090201050d05012714070e0d0b04060e071d01180b0d03030c030b040902031c14030115170403170a15090e010e1207060f0b04020f07030f030c1202070804 71
    0x600b0741b4000d07008400d481902c020002403101c141c501d049611200c0250500c40000401c030302c1813404900401c014204501ea14071413240f13444504c0001c503c10f40202c503203840c40c80c083c00c1200144c0050030b01c0302c03424482c400000424081450352005065104d00003225580d281002202c00700c1a0580d01c200d1480d5140544411a619010754404c03051298401050045c40124060100c40e178800f000c900a5042154510050381c2c0401d0b0b082e50554a1001d0800202100e8000c642001c400321801004910001c00030070b0a150f80c2122046201d00c0ea0b032000c10020902c0c001c0c41202506603801000704071900c000200d600500510642e10504c105c07000982420403900e010365400c80c550044554659801c4202000a030a0207080b40c000d28190040162410a090984046c81105800780901e0f65642408503481400e8000c0320711400300178020f54a600781040c1c140903903842a001140440ca06c460002080d40c000e00a0b40c11510243d1180140800110b51641c040d40c009441155901020400803 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 601383992 1250 601382742 601382767
    0x303041202012306090c030105031906090203060112050d140a030c11060c0912030403050606010f1827150b0f090402041d0901050112060b030f0a121206030c060309020105 75
    0xa04a81d010102c0343e5070320b00304141884a03810303001e00b403501808401c1006101d1901c0000e412030300c3c0d2500181e241201000d50821030020121080002d500d40a1310000084440e04c151f42644400e000b401940c3d220016840d041d10440480142c0d003102460601500404a02030703805010b00e55140d06002d0480099082c2290070020115001c2c0081c0d00f022402c010242059031403004002c0d2000011441c090450702e07010303600c0340c00a0450b410041c02c0c0007416030b1548101612010303400303c2940454074075240d080f14407041100c0025039065102c201e00d1190a00780e680503c42454000805130314410341001d01120075a40142111400314804100d4001b403501c0d42c0c80180028104924030001c509101004147c0d640d40c0039100b001075030304280c0184604440c20303d440d0b020984c010070014003404842e001c6400c2150595034482280540f000000500520a4211116540d11740e00d8030720403010113100000701c9505002c0034102140e0f0038000d00159010703500c500b10b0280141085410b115500341e14 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 601385242 1250 601383992 601384031
    0x90e07020321011521022b0903030b061e0d090c080105040c0b0a02100b0a080a060b030d140702060c1f09120509010503060d030302040b1b060711030304120201 70
    0x2034402c90020401040078019000d403501440a243c80e081d0912107030105034a201480c20300240903601ea0007e0304c4045400c8040e40300309a81584000031050550701c82004004050188003071340400e00740641500103140c448103c4805060020308503141441d0110900404e41225500010659a401400001c285020700000041081d6000032606192600d40035041c19060343c401e1140000c18011a500306401141c6503011401000b400103041c001e4400040d051103160f8490000f6000f03000c040014070102da0840480f480e000e8040701d82c030f05181c4c00102d6201d590031007540d521801c180586001860700304024840030700201d084403100724400441e1902900300805000303940c0d40d031752420020810080f00c4162418907a04183d41030141480001c0d190741301c002c1405224048481c80c8508150003039069a000d450003080e65502c0e401d401e0307030512001d841030a212550348907502c0001d802c3c0e0300c189491103d00350903101850442e112661040c0200c1c0b44041300b1810355407210075076650314128140 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 601386492 1250 601385242 601385287
    0x201050c0f0d1e0f2705030d02031b03011509141003050603011b08010905010806100510030e0d0306050a1202100f1e0906030c020c0102120901020a020607080306031c090e070203 78
    0x10002c0c2c0000141c209106181490320741700713889403100220790041076010041d5480078201d15000350f904da4a00e01e15100c0501070406010424101000225107c2d40c02c419052050b83c0e2521030141e4141c484a007000301c0c2403013407440e961040304071a00d05c14942c0729030400380c1c00c00000b50020a1501006c2c00c50080d48010b5401d00c4000303501000108018003c5000d89801400d43e40098946800c0c66240031416081c6400303030b98050540102e504028074803aa0109840d4146001643c94130b4005181c0100035102d10b116003881251407050209114080c3c0544040131640100b80d40711840c4502c4050391240e9506000d201072190000303540c48220780b64070030941c080712180d43d03a002d0300e41044c9016007140c1018810204542c0910208502c0c0e036000580e5100690003105125100c0240d000104d16100304400002c0d08401e0115541c01005500300203903001d018104c2c259800d90307090940e45241d0510504948000566281c81004850840d804c815000f4600c0c2c4180c07407520500940750031820b460045c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 601387742 1250 601386492 601386521
    0x60905010212070807050717090d0b07021608120304111206070c0606060806301c02150f0609060103090f05060a05010506042301090819030201050c0f0d1e 68
    0x201080451640b000146030302910720f04001d03040801c1c507103458002540301030700c04681031000520480c45039502b800005900c0c0d401031105800386013590b030094648074450580c10607000302c000d01080c01200071030b00e540c005506001d458255602c07a100c09410300420b419498010040500e680040c07a4113110481c41180a40c9407130400c210b0791310746101110780561083c007c01010030244244e81d51010007210302c100c4041110f0004107601c480c031841400c0d0340c01c0714a006104106000042010b41c501d214603020003902581c41d41003803401071280d100c50403641505090341500000b062880e2141040e5041003040c5400502403a15940d400c6c016000f0f401c1c00e503115400300080123080222406102e02404040d01c00f141030514112003104d05803d1140d0b070a84140302241d0505a07a407080024078000c0c0464811a1000c24a03c44981c1c074124031404281c0055092100144280800c1d40072905054441c3d0481c52500203480000001002c055803602e1048400b40307050310242c2e03014056180c02c0b42512 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 601388992 1250 601387742 601387777
    0x821070209010306060617010e150604080d090306060806010b0409020f0702130e0d110c120a020d0803040c060507020a090c02010f2d05131214130503190b0105010c0609050102 77
    0xc002804c01030a88407c40041000c5000501100340200c2c1c004d0303007000c1d091402101d54017005002515034015070b00140314078820300040b400c2090340131034840116405044c0c00c00006440b582810b407203103403d01418400308000c0000700414041680100001c9803c2055641000550707400280384c04c40941411741115121020700c2e921000c14080700141441e50708003a40000b01c2002c510f9150666946006c1c0300d40b007152100d208490086c007644040c107030300621841d2080542d00e00001c1580058a056461566890b03006c0b64503402441210202d40d0010801d881440c5803a0524002d81110f80f4800e045540790341300d145a1902d01d000e010314806614a240c141c0d509a01016a000c1160404012002d8117200074051100e1240a0017240c0b260000300b11a81819003240507030f054400da8182e90440c842c001070020100c8500da5440066030380c11020303225011902803100102200700100a0710150220780100815030080b140c900405100e402d0210700048070340c45903422038200c12506a00d01003c03 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 601390242 1250 601388992 601388999
    0x6020426010b0a060e011b12020109030801060c05060c031f0605090f150f09030f0d0c02040b0d210e1309030f090b04050f1f0306031b082107020901030606 68
    0xa01607030348405003d40d01081d01c00d241000042280d45004011810311040c1051404070650046018003e250013640d20004840e000900034000c0c894000198000351305040041100b5100c3d03c0c00c80c442a401100a09890311052554110f40e400a8230b080701e010384609406c84407060002c0070070018011a150340707032103011090a0040041040c421148155480b00d2101354411a40e4152440c42c81e099205a803140544030109207881701da070351584000d00c21414001c0032594403280c2024a24400d913814003000d2144c0c3c0c18406c2641070014020025650517160b03607078503401100c40a050100a1030716000202100b80452007550209003042c1646d52514000000e154018803018542c501c80e140074070406161084105c1d450007207000d003030b1180c0345072a1103000666541310004c506c3d000e1468004440b120103c03020f0010202c51000322803004003444080c4a0406103100041103032446405004202141c40400f03040b8004406a400382c05828400c0c1c40242c0c4410400c54040c500c50500011042e0a = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 601391492 1250 601390242 601390319
    0x1e020919061a04120203070506031f090c0e010f0e060a0302070c0b070305070b040303020904020412030e100504301209090207122003130618140d060204 67
    0x40300c1e00086003000c00c0b040140c1e00038000008960440d1004030452100c80703103a1000030705000041d80085d42c03000011040c025200002c0c204964080240080e055110f030341d41d2460030079980e9403d00c4001080c0e4900020416500980517541d0803032051a090040c00c03022400140c081d0014610300b00001e6000c04c1c180b0400510300d02c045d001d03142d0084c0c0c850820b90640c0d001416841110b000802810742400800c1c10540030340c06036002000e0080c4255203031030300c8903403501682daa00750003078000551040030400c0c6030500340c5111010501555680d07242905050f603c2c05003850303e00700c44041d0440c40c4410b007040141c10100d901010720484410454181c408001400010f151300500c42980c0b04204030760000e803842000c1204c4020780d0400d4103082500c05202c00007081d911085601c40d001c002040c00c2600480301e150000e0707038403984401c1415443c0100c003144810303190003803034a060140301c401c0324240b5040300c6070280188500d8000d46003c1e03c40c1d08c1d03a02e00c0580d00d49200340f6500e088140e142c2012 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 601392742 1250 601391492 601391501
    0x70213050c07140604050c10030b1003020903150124020c061306170106020304210f050c130203040b0a0b03100e060f09011a040b03070e010f0518010f031e020919 71
    0x4083e00052280307042c00c0d03e5640d00d96038952800343c03281c28a030443c3d04029010741c00008480b04010a45010389030b10200240280d8050014140309001d225140b901c0b84407203803a0340e4142c0c0c0780c280c40e51141000840c03407543d00c0b4846100060941c450380c2c1a50b1010782c2c421005100102105181c61006444c10b40c000d00802e03c10004e484005034400014000719034000103035012260400c21002a10480710003040d0505001000905188290620b01c000d0100000700d000200000360385004a1840e0a01540c049010940d4001d180a0480d4081100f840040d003203950303010700003803d840084113000c17003c01c202c2d0103840035402c9a410510810044005000e01550311500010003884074034045040070508210b080d140310301c200c4c0d9a1040301040d48040104001401d8058407044082d6100d60310001c0d01440c2b8401c440c8680002455500945049001241203e0180e00740144c41d50540c3d0f00c4005000111002020307000f08600742d00003580e100036029029a451500c07041c04800f03810488030568 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 601393992 1250 601392742 601392773
    0x4180b09030301030506060d061d0a0b071103071b051c020f011103030601030905030f0708041701020a02070e040f020a0e06040c030c0e09060a150f030b0a0f050402070213050c07 78
    0x750024801000410404548a5404201120070850890301407400e0700060692141401413030801e00d0000320040000074000071480d010700e00300358040d5a6400c045035514520b02800d521500244448c0c3d00241303001085600904540e4965140207480d030006c80c50125a02e00d850001d65603c041c840e040d41051030b00301d00483c10a20b404454105005d4400c0c0daa4400902424105a0b03a200340805003c4140159019641400321295907542d5604000040350424018000084080003d849600310144212210f415441e00904500c51070102075210a2100030000d80e90100440300d9040140d861000510291540c0341c40309045040c42c1c0c0c14001110040c1452030309161030103400220b4035070440d0b2110003600088401c42d03030950781e0300046000180540d001800301c04500500000c0550000380400300d280d030540e010010a02c0e08410032185500320710455151603045801408681010f40080c80c1850015001402c0c2d4641d00f880002180c108448441d01800c001c81c0e4281080310014081c01c09 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 601395242 1250 601393992 601394011
    0xc120105030a080405091302040e07050a0e01030317070c080714100b0307170a0f380109091103120310080703050309090414010614131b0f050904180b 66
    0xb4400d1651814914800d070f004082c407a41c3c407040060159101c030041c080362203901070400d1100d002c6448c40940e8540c0c05000e0203101da60001004282c000306642002e04894155580741901610035508140c0b45e04050032003c1040045200c00307020a81541c020882c651142080c1340e8107107150803d003410070103500010f04040d401c0c283c034003540c1c0d0b40015a9005540084500400c1c4d450342d03450f41c81c503082100000401c03201c0b071940c8600520000034640b00c01e1900082c0c00715940140d00458a8402d203150107103a40c1807002c130005120b40306441d88039025191040d00d6000322107420703400181c604002c1c803404542e6500000304009001b04549041030062500b00e00504181d030030340d925151203004440d03186018000c14170016060040b42d50001c104031242c180204101901c624a0300c0240350104203150066501140343c1c4d0141c03640f8450b003103110128440a01e80404001c07012216941686082000c07c4030900155609907500c3c40b03110b140007a00d81119604c0c507401e00c1c00c01c0195a00800c41444d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 601396492 1250 601395242 601395253
    0x1030f03172403010b040f0504020f100c1112030705070602010b030a02180403140409020307031b02061302011211041d1311060f1c0b12030a260c12010503 68
    0x20210107000c09440c180080d5500c0032001c000c02c0010070b00524080e0f100c0740e441030601031081e18101469100900a40c02500c0c004840002c4009204005c07089199000010750880c9000c4080303007064076041e00300030000341015483c1050000c10752035600710b00d1040c1d07826000b080c0c0c10001c203502445440f08400007913003d4046140580c000130040304071a0303400c80e1425409800102014421403c08884010325001c41752a940c079085040025001104d22102007840e00e120200c424159001e280c0c038a0803c1d600812556513141300070444000388060890500c42046a170f0525451103015550311a40031403100c1e6140c40c40c080440c115032035500c0a1580121820b0141b0206c03070740c0141c0c90309800c2c0d08003103032010345044100400c1c018811515a0f4203142ca01040e000c44080c02e40c2e0543c0d40d59a800d110034813080c2c16a41c00c018218160050100e042d92041000c6003030341c0c0c091690541380d0100c4010300700c1d4800441491031401d400445200c0b81001000800d4000d1ba411840c0c81c0707000d0002078000f0311 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 601397742 1250 601396492 601396501
    0x2001030b01110a15061d0103060b0109030f030c0f12030c0e12070512070503150a050f0c1e070203010c0c21020706030e01021c051b16080a02070e01030f0317 69
    0x5072550183d103405004040007049400c072154036500428000d10461801045640d14465500000340c0c00303000c1211140d08000c0780f6070041d84600024401d40e40c110002081c82c242558054a00083c006004c4074601800080c160125452001c0746610304030948001c1205898031031300a0040e02821903041c0300d82d0240a440e0f808850001d45c03074068079002e03034070269a04000ea40c07407071038042680d00c001c0c2e152080034010a1219040e25682d4050703810400c0c20701103904ca0102e100d0000908032241e40305804c0c14040b8509290410040034403c80011502c2c070701e04a01600402e00350707808043c00743d001c21540455001000403070b810540807116500c1324001c03218034204000b511109588030301010141c54507481400c4030001c2d0f0403100c1c41e100c0c1d0404c44814800002c10324001d030104407141c00161030080401e07440300349124102d51803110082c00f101c06410680d0b850961340c0d00300c045404e0440c802d614010404140c04a01c040c003a500851607103007400d88074030300148400036030034001121907007090070710 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 601398992 1250 601397742 601397777
    0x6030d020118060506130e0102040e090a0218070c020d050c1f0912030302040b0d1d011406090a0e030703021f0603020f040c1119020a060512011806032001030b01 71
    0x8030910782c4080d0200384c5890300750000d6405003414403405201031410902c80c8441c00154010700031640840901c101507078801400c075881e00c1c03034114041c0d00081082c40c0c010070340340c6041c81190b000b4101c0c10329600c2c549203500403800c8003c41172400c50b9581c1c030a01844101e46004024248a1007070f001007001c015107a90f60060080e080c601c1307808c00d0448500700b260100340c042d80543d0090001070003000c1c0c4881400480350082c154200503000414025104801c0c122418003c000310507034400d076603c005440703580c1805481400100b01000c495510700e1080c002c010240300801c2020f0280c0c1c000c15007030a501e0040c1c60806003011030726034503520785081040103072600f1940300d80103a01143d0003d044286a41c0c1601c0b414081c403a5401c0078060700c084140d40f102031020400e0b00600030b4401c0032103551164020b0710f061140998031801d10120034010011901c048405405607188000301207003055503643c40d0340d1120300c60f1a8507468540c10743c80c42486c1d96890311441180160910700182e8403002c0391484c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 601400242 1250 601398992 601399031
    0xb0903070623070b07080a020c031b031303031d03031804020319111201080d0504120302070f090504020909060c1b0c130207200a0b160f0501020306030d0201 69
    0x10241800340885481103200c40600e0b1070030b8000a99081203075601e080c0e1418a05101040b15582d0100d400302e40800d00d811002d10a0f03030002000c4100840c075041e070000329071102d01c3d040003c00e1a1844100030803050800c40e280d0840045200c0d03112450200310180e0b90301d2000c05080f110324066402403000c0480e01c101c0b010b940400d100c0030340d401030360707510761030007050240107404c44501c1c07075609120010700c01048003001800b81e440c8031881946181d0700e07585220b403140e289040750340c0060000d000900076400020680c0104030f00c01c1c0100c40080750f40340314104030039210b0b5001c1c400310fa941c1c00c1000b0541c141046020f90102e0351201401c1c1614100089028602038030300c2c52406140d242181d1824450100302558042000a0900c0300303442a47c503041001e0340c0544001c40c0d002d080e00c903003030b10140000200c800900c00f0007409000e070303582000c80e90165504880006a0134180042c14840411a095400580d060181c8000750340c88c0380000516182200041103e011a8580083e00400b00e43c0ca00b503 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 601401492 1250 601400242 601400249
    0x1e0d03020d09020a030c080d020a260d0f0912030c020d120b09010e0411120316060b1210060b090d0b0c040509090307050706080f0f0a2403020a0b090307 67
    0x800503210444450110000c1c02d81d0b050007034015003003010100c00e018604030303d00c0c22a81e050040702d80080302e00320100d03110020910000c0c01401005c030f810341c200420178030082510b00d0140299090502d5120148103031a00c84194031906075071462403600f88900b01003103914544050405000015035108000e5980601440c3e00301040600401303e20b00401c5908030003441c080040ca10350183d42c69003540d1604a105036000c44460800307060100703903810803400d00306190820001540c201100703266001d00000b40080101c841030381e0340b525070400b80d4560040d40d070480c9280780100b2001d2108031140080b29420f80040c03110120900541c0c2c029524100e03905619030340942c480d1919181c2203861002d90055401c602c1c3c0c482008000c00046500c0003000d8100c3d05e0142c1c0c00c0741c080e02e69400c810f550020082e550300c6051142d8100007490302195000443d045078141100160341000000c0040d03904c1104800c8550914140004105604e040d202203005442c507020f0f450f140c0011000003ea5807100c030b20 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 601402742 1250 601401492 601401497
    0x70b15090c27130f27020603010b0f0d05070c0b25050f130303110d0f080a0b180a1409060601020705010807020106030c1d1b0301360203091e0d 63
    0x14039100c6a1103403028080000d044030400c4c004c11040c2002c140142ca289401d141c10300c101d801d02d081451500100c3c01c1240758018091601e96420101c0b60080ca500130305284144000400140000c07110b1441014415201c2d0369840c2880310b601e290003c648140038003468440100a05228410511400f9600e00150301c1d041c280d0340e40004401401d541d0041111441d85004011800000e0503005941e5215441d0141c00380c50105021305410b0b1368a6160141c000005411440007403095589a48030000d040401031080f06421401c2400e1030070600b0480b00e4060303003a10342a02807112907400030b40981154203030303000d081a4507212000070b51341d00d0b151048504101e58500403506841c000c0d40318a014641100912030030940341d8403112080c3d040c0c0c0c042105100b45a0b0009080038070704020341c942d0660b6a5601904e90303480c00151141059207103940c42c00c00580407962000380003400e08108a007501520016880703280c249c3c503140c180b5091307403008829613000210455518001140f040c83e96600d60 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 601403992 1250 601402742 601402807
    0x30c040c140a02120a0201050613140f0604090203060403051306090b070308070918060f05060a1e050904050f06030f03070f150b03010905010b131107020d0503070b15090c 75
    0x1224100c2ca441c044c0301390365100d00d20006448500c6076064112506c00c0d14181e450810001c3d51407440402ca5007080008070490541e0000301c1d25482107840c0003a0001001040403c90f80c01030b40000b03040c101c0540d0300b10041030f800189155081c0c2c0300c9403610000d0181d800d03d11000b5280090411b12480303014401030801900c1e100041c440e90181d8a200040c040e060081100d002da4800140010007160181303200c3c03010f82d043c001802c0d00d082d074115407003851a940c40c2c03151411380030030f02c40500002d9a01d07002805001c0c03101c522292a40c2c41003070310498000c00342c0b4200f400c2c84010b06040c1581c2d0917000c401900b00700901c0d00428035108076500c125920000c54400030f480702c07102c40020704210f407109615500b03111880f01804015001044103210865150b1903450710a031a00e0110303104595200209081800094050325200100c000d1039030089040d00d140001969469901e150308071001c40c00d1182400407407607107007804480c0c1c60f41300b200b06480c0d51920011005d8a4804902052012180c0082 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 601405242 1250 601403992 601404007
    0x23060604081b060c06040c080714030c10021018060e03071205030a0b0a09020d0507020606210307140303010f0605030606030a0504050a0506090102040602061003020f0d1e030905030c040c14 83
    0x100f00803a90000100b009941c5a8101450b042034245211310804005102d0503d000c116071038407a99141d9070340401401031030700c403c4110034002c0d440c40c01c0c3c0c01c2d041035020701c0d40c3d410110b071064016050400e9130304c919910301c01d8803480c00100b11403180420380c8141c0d2041c003580001a0f110080310340001035a040072030b100e41d0741461500161200700039603600a6000c08000034441c50030b4002c1c04190700e040d08181b010b541c42260490381d0f100222385965001d1a15010079103484500c1d0514140c00c3d40d844156480d009464036510488030075500030801c1e40e0701c0040100304050003024800c000d4205807a00d170b49182400740014015004c00303004007023100d0b50364020804100342040352030050350b4400c0a4800a25185920b14002d40041c40352001501410f00014070603003000a00009895000340281d040514030020301c4011185090219015852103c0c9500d000c0c2e003660854244030710036500d038030301241440241405d2050183c2070074002c070308150103011082c2d00a000112048021200140c55122 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 601406492 1250 601405242 601405249
    0x1201030318031a150102060403021908090a03030e0910050d170c0a03020102041403191412040320010e0a05100c140f07080a0302060f071223060604081b 67
    0x6103510003046014080043d4100b6410400301074441c0d01c210b40c00c3d8002c024407100698840200b1240200141c0004802c0302041541e016010b80d42409441203506103103000c40070480140343ca42041c0c010481c40c000980c018608050840d0380308500c4108200c4203444d14001c0740300d0a18000c00104017448038611000e03042c940303034103584205620700101ea03920f01c10350402038000d60180c02001505640920f008855040c001403c94141c0ca03010700c1c00c4000059900c64503800c0c5003007510319001c1d00414142500d050002d41c0504051401154480440105007054215980c0203071911030502261084040325650b0b40c0d440c08084030700c243c0e04401940b160300f4080b40c140c0c0d40315400608035401801315068501c070000d06008a140c021084a11050301c514401da60b804c1d840748000c1c01607002a0015503070700c0500400b16000f0300726082101e40140741407801c006580c02000c441d11200180c5050a50840140b00151f411410030fa81040c542410328111544500845482c0d0200c070b40e01d038042204584 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 601407742 1250 601406492 601406537
    0x1e0f01051021032705030f0d02030f07050f100f06050d0302030702041a130b090a0b0616031704030e09010b040513022101080f06150906130608010c022112010303 71
    0x101e00350654180070050344c840000300307609000300c5001c0d11035191036440001c40040c18018500b2140c00843c02c000800345010241d600a0200b180ca0303000f19a03010014120400490b8800d118100c000300e40d03400c180440038215501d030751006120b800c04401c9940407a4000c001c0311996501518082241c02300084031402d03141c0e00b0100260081131242294130000340d190700c21045501d08489074503064031200200025681c0f04d05000e640303d00100101d6003500882840d41d10100d1280c02e140d00c286409060804114504850960210b09100e1400c200da141403158240500012100581000e08040104035443d442c0c0e0108081194006802041c0408004098440241d450b4420b80e0030b6840faa582c0351560300220031840c5510501010814008005001c0c4422810160005925a80b040c04100018080c1c5035580005907540f0008200d4040c28000c0c04c41e41401c41c0c0040903502c0400d24542038000003a4083c418800342805843c10004c0b9241d105811603030103246c0f404403000c01c0b0108802c0032 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 601408992 1250 601407742 601407767
    0xa050604051f0c05090111121b0f0109240f0908030a0c080103031e02030f0406050a02280609060f14010513020c060610171024020606040e1e0f0105102103 68
    0x4102c0400d00e0b0f1607688a1044094206038101d058542b5444a0b04105084e1200d003100101350300c01e02d0312901048001d25110500002181e000031400c0100701813200708940a5000545960340000104951440503029105100b02945080c038000c0d89507840c001c018480314005039a41d81420084140c601d4420419038140315020820305070354039511400606650b20400286003d40201003060941c01da00025120b40d081c80040700300e10100c1150307034010040039030520444140e035407000c0601000c2043d01c2040068000c021020446504207001c02c848064003a19150320135004028008454001041c2140c0001040c0c0d1600f8041c200307180b0a43d000d43c0c060380360880220740001000401038568075900111005a250000081a50703e2845403207400a0095005a88500d0204a503400c2a80c8025a600329480541d20108628030340f06103205200d2407480402c2e40445c2c1d0304070f030b000420b22400b60002603034208500418604140c80207282e0000c02401c0c1c64280c0c0c038034201c0515020f9080042c05 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 601410242 1250 601408992 601409023
    0x1d04030f031a1c030201182001170a05010303030509030a0903061505491b0f230108010e040305030c04090c080406060509071d030a050604051f0c05090111 68
    0x4015000000d8103d58031460400e5005608203440c5015243c1d005c40e0100180b5000700c0f1000203808c00085900d43e117040805c1d0306040098003402c46585c58810b00d9034600800d4004408a415403540c180213065900c0a070002d5241e4100304055140c4a0300a2580c004890748800f011034152807401f8400c200c42001e5009039040160181e083e40b410b420f12540102c46103090b80702140c2d003180d00030f28401442c940d10001003910171119440000c0350502c0d89005180f803014007525407240c3c0700c10350604081c2d12a030001480c0c00148003c080c1001c000b100240544d4020328140c1c021f585010001f030580d88010f480a000d0100000120307034916003580450300a400c00440511100c0f00b9010020a4041c0868050ba01d4a24105002c1518500140120700401c40c1da500d00d14212004440c0300500c854200801d5890701c104000c00c000150280030281c404c078051400b80055000f402100c5c03004801601c00600344603e40381c03400c0852a00042644c4125000b803a00c0000c45c2d002100741c5191150070503490f01c1 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 601411492 1250 601410242 601410259
    0x6190510080d231c0b03010617010e0c060f0301030f0305070c0f060f0804030f18030b0f061201150612230a1512030c02060706020d05011d04030f031a 66
    0x50041e0000701d01d070301000790780d10f40e2030b07109110211801c502e02030344440c9182d644580d8000380500d0101d4200412400000340002000c0b5a20300f00c4080d050b080961040071070b51202550300c11444180b10103003607130000303864003494400c140e40352002e98401404024081040c4c4607c0c50705152042081d580c1096002c0c40c11841a9102d142c5121481c003e40305510000c0c03040550503844078883c04006004650603190009004203d04059410180c03850800038403400442000011480e89c40f00c02e03000d0329911066100d1828503d0a1141c000003000040c0c0c1280c2c1420382c0e8566140030944000c0441d4071901d001080d0004107409040600036105895000071001c101c0c00c0ea4841c107544d500d50203214013544c20050300094440c10b8000800900c00c1207101091031b403540300800d00070f14049519510081c08645454941ea40d26070403a004140c152000725514801403101c800b00403c141180e0741040c03c20b122a20b02036800034407640c004800070007010384400301030000012640f052006900700506400 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 601412742 1250 601411492 601411513
    0x2030c041703030a06060f0e121204090e07080f3d0b01270506160b16030f1107020d050f070e060f100903030309111f0207080619051008 60
    0x542c2c0c0e420075210b01402910300600000d003036024114040f40c03140b2644408103101008400c0100920895140304554010b00c920048004460401400a8a200040060114a81400185080d426410482150b800742c0180b0594030790000382178442d600c9022500100440c3c41c0340ba002d00300400b030954400c200140c80080d403041e5481c0c101c003100b95030a90f280c1ca255001070f05200074a0b107000303514074682110a00188182d0401c1d000405003240944001c2072108100e075200e4131801001ca4140884800c0d400114004540c1406815071112103040e080c06010b43d0710748118503d110343c2000905c00d504c6c850380102048010b0007500110f54126083d5a00c069541e0100c2604070000c4030403074400d60328400034072114074140070408010000e645c0c4007950241956000d50013002c142d83c0544e400711151480c03040581d00d916200700c5103100d04403402ca010050b80c0000c2e161440300d07080108185c002c2010046070500130b00c10341c18800304291011940b80c503405402c03a20500b00340c2200c29180600007002 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 601413992 1250 601412742 601412789
    0xf0c0302032e0501030e03302409070c0203010608010b010806150702090408130605040302032b0e06040b0307032703050a0503091903020609190206090402030c04 71
    0x19403160260020b01100c62070350384010652038000021030503064125070030900c02548680c0c049840000300b02c04591030000c0341d019034201081c2c0e05000080b00c422041d058110b403c1d1550341c150308101611020010106501d50115601580000d0a40104110000184103910801070b03008903a4000c6c000300511501c0d02002400b038490007440c01e0101c3c902c103000c11081d050028406003407642d10501a030a18500e41e08111408101400270303200204148503ca04100503040038000900d00e544070130b541c1c1e030315600c14181000403105c0a09c1d1081d4000c911510100002446840031280d03602e4000d50300500075001131050300494001510700c0d5000f100300a02260154030164030514a0700101c180f00201030003200c803c0091150041c0007072000c0c8500f00c403050240b0702460700100e00400303a54520b0081503c2150b46058403209400580c002070500102c003902f40594640103c3c1d807001c0724951078068003c11018070400c148240125400130000350780d90010b00507200030b1b00c2a21f00121301440b205240c03 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 601415242 1250 601413992 601413997
    0x403110c15030702071d0406090311100204151d060f04030b19200f070221060f1b0313172101090203010302130902040b0616050c010903031d040f0c0302 67
    0xc64013601c038600b030202d08107007104014080481b44920004281c0d842d07030b443c200607000f140000c4003404825081800c0410301440340c003039000086d1030b005071200c3c036040c0324103200d0308004c90003c20b0011020b00c2c081803c0460414040b440d0096920700c3e90341c1c0100754482078038441c551011b0003e0341d01314140310410021420032a42030081d6142484000851500000a40d00300c1a5440d0800010458000c14110840c043c00c44a80001c01008400c0301c1d04610f24550b085034880202ea5070404030400c00e582540b20750140e04440341c400f181c0c00d02d64050000d481d1500c03025100c00c0aa02c0110b202e9030400044030f00040421848804007602c030441107041021420705803202582100f6500008580d1058a1017a00c0c1200d80080c24074550088140c1801d0003440e110000366042501ca10217006152207203401003410560080890100c103800d400c3c15820f02210f500c1e04c83c10810410b47c20000300350300640279119009217074031020500030311a001400629041020a480314200301c084064250140e01 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 601416492 1250 601415242 601415251
    0x706080103170c03040909020a05120303070909150311192c100b0a1103040f0513060305060726070503070f02210c03040e01080303061305040b0403110c1503 69
    0x209940d4140440014000c0d0042c1e11066003d984144001c009451140d00130f89a158000346c81e02c80d9040e1104c0104400c407540381064841c1754000000e001c80b040d8001c0f1200000d1403140c03400c11048030210160101041c10b440b01501820f000c0b9104c1c010340d6221204206694034020051255540c0c0d81401c9081006140d84200c8441441202800d0744101d5000648600c0101d580c1c40800d6080006800c2c940d001710100500b004031010600e02002c00400c0184081c0c1440354284503c1440c02c3c00300203007010220b0410f90320784d013001030400004400044103038001406080c840b88070000c1ca00c044e4905080040c10703801c1d03000b8032424828101d80143c0158040c00c12540c0d62035080c4441d000c240ea46156240d080e11441000402c0101c2c403040c80c0c80038110029100041d24501a41c80c00c0301640900c003030304690980d030000400d200039031400c4d8185000510070302c0000d02c2070f850692201e0209500040000c0c050003540c01030031419581c24881142c2e4440c00034900e10221b01e0162803c42241c004030f5 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 601417742 1250 601416492 601416503
    0x3060106090512030c060103140a0b1005030f010911040b060f0415030518060705131707090509070b0913140a0f0b0d0203100e0703050d02010c0e09090607200706080103 74
    0x6540c0840e03c1012086031662000b10f40245503592859560368410411126035410f9805003140a00000c0c00884610b03000d14411414011624204020541446e85004084085030302d0b059486000580d6401e2000031084100c0300002c000b40d028010503031034401e0914039030b5039490020f4003041c80d440607050134021042d0350742d0400003661549900000e071038804502100961010380054800e038484c4005081d6841f14045120b01250b071502c6403034030351a80c4018008544c004820034000c01480d44503d0b036001d0303024001008800d2804400e04111310a00004a0203242241290803a07100301c0d820040b42c0c0c80b503142e07400d401803030703c00c07041ca008040c00180b9001050414801c968140340681450015a030010090150045264107882c01842000441c107818042d007440080881c0d41881410303c00303005500049100c02400b00c00511703e10300d43d0592842100840c1c00d0008001c0c0002d5115400f5203581489000d042080c40b2481c54056055040440c0e8401d580000c0bc4065025029504030303445031 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 601418992 1250 601417742 601417759
    0xa0c03150e0a060e15040e0c150715060b03070e06072a08010522050a020a0605070b010605210405010920010305010504050705030f15030d0f0f0f020309060d0b030601060905 76
    0x1071a50a002150560340201710112140d04c001503460640d210a6440c20740d007017210348203561240422221a010464100d0112000c203c0174103100116413101c10018500b04104582030a1440c03a8240d07010183c00d280801a00032251262b82c0c80e02c3c0d04030b84034960041c0c4158019031044855102d040b082c4103841c81c006c00c0d200000110f00e041406603d0084041c048040c182803290721000c0b100c40201403090703942c1c0c0300e54040c040151711020a0340c0060103455035019960602030420f003c080406902100402c40d0810440d442b60841403e1700d050440658022410b94443c0e0900d1805000d8055000d4900c820350350402e501c4603060f0b50300e030400441c2070f2002d0000f03a9072081000110740e4200c0340b4802003001040016502254014510380c09101d905c140004090b5920207e40b4001260381e91002161452903e010100d0308003901284a0a003442c1007802d001e02003100075101d0003543c0c481c0c1d000354004144814000540e41203001000006005c5030b60030742c0e441500401e45d20262041a0103400d99 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 601420242 1250 601418992 601418999
    0xa090b0a050403180305070605091809031210080c06030c0d0e010209040e210a020a05030a120b03030702010207090513050129060c19060b0d03080103020a1203080a0c03150e0a06 78
    0x40001100e0300b21010b408554907200049c2c90603840000e201d40e00c05162104000c190401221103402400350600840d1200e1000c0501801594064011070502050f031000300300c00311740020180b5007040c0544000c0c0e1281c03180c0551420f44d001d114104481c0c541848460708800a055014204c1c40d1001c40d0107010f00c10201001a459030080c0046e020800e803055402070403d00c86030700a144140c000c0c8125001c1020589031242150007000c1d00b0400500e0358500e4008818103070141c00c5100c04d040b0052351070011182e0020b59650000c2c03140c01038894652000895007007101808480e240c0d0028028048501d1202c0001403401981e00c209080d540410455402070030410305031110240220014000c44d510400078142148400a04803040d513212440f1f0314080d210110154081d034840d40f00d80c04154110310411481403c0d941201c1134642c184062040440e900c03d12694110704010070014003010f004070b00710050104005d409803001d0081074002a004140714880740b0807070b42140c040000c140c8 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 601421492 1250 601420242 601420277
    0x9021f020106140102031909120b010509160e0907031b03090b010801060506071e02040207060506120105090a140f01110a0e0307030c0e060f04060603091b06090e0a090b0a050403 78
    0x340350f462180180e1042c82401d0840015041204445a0707504090031800c1c5c0d9200c01d58001100290200c818090500040225050103280c0540059000c84002d00c01c50124800a103009000c1210610400300c140120ba40180242c2c0003078881400c0704840c1701c907a500000d014010f00240501291200e070144000500307240d041c4111000c0e510000c01003898803029031105207000000d01c0c0d540140d5107c0e401c901005940364401040c00d00e21500b404500d41c9001802c0025801e600380388034086074108000c01644440218484403840d80c890034401c0a2205070850500d080109000e00300c0c2c4e07610301111022801d44603401b412680441d540d038000c42d81928414951100ca1602c00281030381c002c00300c1407080340790801d107155100501404101c038074030580c0300041c160350360f0ba0321200101ba942c18056090011404032407150b5418401d114280600d0103000806040c080d20409800503200b0010a1203038450f40c11210078030741c00000a24445c14100c0c03040e0010081900d084000c11207415040701c1c640b0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 601422742 1250 601421492 601421519
    0x20909030702010e0409052d2e050403120207060603060e070e010b0c071a16080901090504091101081f0f050f090f01060f020109020d05100e060c0a03020d09021f020106 74
    0xa0f1f00001410030820f03150f06030075001e14101c2d00c00403101d41d03640d03a400c2d400b00200242040c2075444885015803d41d41002640c08004050a130400e10381854200008a500036803032181c000a5030b04016030300c0b0400d0400b40014512500010071090402d030322031012040c0007032503109468021070031810990365001c504039140300e1180d0218007600f000d0003c00c980500107090154554842c14144e1034079802e0030144940791148001144d0380d400103d0204900c0d43d0082c16800034160940701007002202076224003030f452001d003503890304029105000501c034500c00802488602c404400c102c41c0e190301e42582c03801d04403072806901d00070305180520351000c0c60945a000c0c02070303045100c8400282d00f00b003001c4501403c004888820341d0f480381c81020040c0c440078a2000c0c4240107c01400540006804074802d403205820040019440b00c001d210841c1c080d1411501c42514505006070703110000342e84003000c1c044503080030b0740c44120b10b1185607100c0d0481d402c2c4804070280794001c0040c10303240e0354002d100e031 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 601423992 1250 601422742 601422761
    0x70c120506060d1a0a0e03071a10060207050f0a0e01090204030506281d030f0306090a0b030304060c0215030106050c010c0320130b030c040914190216020909030702010e04 75
    0x21218440c50180307844604c0f107001d80015004101240d012a9200031a02c0d680c002d00003158500184416504141c2240f40c0310380d04501100c4500c00d8852511200955826443c09000d1003052000001c4034640d0303555070040000c00042842480c5036944641120086d001840700740c615001c0e1100140000f41c0140240e64000b0201c00c1c880c0c04d418400f03103802c2c020441c4049448100c05c414440d86043c1208001130700c1c961400c0c20300180d0b01c2c0f8001c418446e40b400007030300c0050b103182444214102e80e503001c0152010b50f074044c030b40203404151600000300e031007580042c0e90000c1c5030f001001050303c2d9030210041080b11800e5000303000389080c8460480440b00e030007844c040b40d450b00340140000d00c03000c9001001c902c440d04003c1c40c103054540c103a018490b842590b07401c195020000d000c02021032a80202c2094040c00d65038000c05281c22240000b009032000314010308a0740c0010f1000d00c01c0c19200c030100100d80c014041642a10b4032440c0342d5540c0d400818280d010840c3c2da0004080d0b4640b5014140a0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 601425242 1250 601423992 601424003
    0x309090b04020703080412090b0d06050312040b0f0c12070309141206070e030109050d0306030308090303040308070507020103090f05060105041d0c010f0c06050c12160804080f070c120506060d 84
    0xc640c0e494031200302c7d403518042207004015243e1000242020ba9801400c09048082000240305243c08101450088050035009103c00148810040040c044059420021003028031075901e02c00300c6100b034141003410216407002000030a0440c1413644c42040c1c3d8040d07541c825506404040c42c1810440c0580380104180d03a168082c00014030040c1c03241050003680d00000d400441e001003559191030030110a680c40900080c1e4600302041495407044005070031104070760103180355043c5034400910a800042c4201d046c03100015042045901c60f60000c052117801a205040c2002c3c2841c1c090b4555400b8810744d4410341c10041c4d1142d54a0f0107480e040303040000c1000400301d450300c1c40010341d10800201544414040100380c0400841c00a01441d0b00c200904156565500d004a00c00000ca10780680440d41230030005160441c2e69400ca000c560b00941c20080113915912a01500c070f0080c41011390007440e2060040b00012914840c0c90711001c0c0034420300a4440f25a40c01c414044072620b103240c0a0403 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 601426492 1250 601425242 601425257
    0x30c02010b15160b01080d170705030402011805030109050c040b01030c05030406200331030f080c0c19020411030c07060902060d1109040c08060102030f0d1401030309090b04020703 79
    0x5151210780041c82002e40f03281080000070060748850022030400d0b4001000742d00a0964851025800100607107203040e2180c12100904083c4c4005026020042c8020705210040ea0780c42d62240b44040b11000410000f8000e0044140d03034a0060307110031000186070b00442c18800802c00c1c9600a002d0030825603000d81ea040d040d039483d5120750000e052182c6c00511140d1040140502d4650040003c522448c892801c2c00000800c078201c4c682c0241a0b40c42d0252040d00441c0c0e1103002a80c4070155510740c201901e080301c0306480310a01c5050f01c2c40f030003000090780d21504282d43c510303031410b4148900640c000c4078200124542100d09101c1844100c0740c1e0f48400303c08001000c00249035901c1500082d0005d44000c0c01c04144050050072961500100e0f0401c420100740c1d00214503240c010041d40100d035285c514801e0170f20500107541c81c01405040c1c9034a030404100020380e8a801c0d800780000700c00f90729010a843d41e43e0304015000c1c03095801101303241424101d8104071800c00d030003283d01d0b4a9250f5248038 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 601427742 1250 601426492 601426519
    0xc062c03041a090a0f0e150609130e0f0304090c09090507020d0c050f060a1415060a05090f0d080a0909020301060903111201050c030a060504090822030f050607030c02010b 75
    0x3030b65215401295001400d0384000c82d000d5107189001c0301400720300c9036404c064184416111000003200e1810b5101c2e040800c2022180e844500780d42c40c0c07880c102030000c80c5417160004401d0601c2303182c6c0d0b0981903c2c4404a800101c0780c2c5076130001c1c0d03044038603a1203a4121980ba00b0714801607070f0f4101d83c0907001da4048200d44d503103503110f0545040203d0059055480e405400001c01d400c1c83d00503182da40c4ce054543d60010354004c650002c180c0c2114642480b08103000c600c0c000302d40c180c001c6620030760600c0000701d4444031685a42401325801c6e40000c00e0f00340e0014180c5007001e034a8000b082c0410014844a0020038024064801c0313078103032005d5032a05c070f41c5180b86680c1c5020922644050741d8200601d034111028615090040500614552940c00c0d01c80c60000d10300003c07148190b122920460030a2004404108240300302c0308802c60700034a0446a08204a0345031103c1241e510040540c00d0303001400e02485008150740c0d001e1070b01a0f07010710496800200407400d84880745989070388110905a4203 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 601428992 1250 601427742 601427789
    0x31204060f1106090706080702010207170310030501020301180e070617040c0e0a05010320010909021b0a03080403020114070e010305091e0a020406090501060c11010c062c0304 77
    0x382610841c2c038240d414641d0038003400b8200101582c0b03900003940868800e004140d0450480e0307a10a149100850411250b40c8490303030003500a15445801c0310000002c1200003500f0070070100039580200c000d65503560360f0201401a03150100d00313004007501d0629a050001d0011820702e003100c01580d1066141007100c4814010044050b004a540c591010000a40200004403041c40380c41c209600080030742c91030030812100c80010b041c40e03900007003401240c0d416a0708041c4903400c1c5c80103c200183c980400b108100d0a1180110b0102281c0c41151111420558821190303449907110754000e1000c00c3c0e280c13040070040b0800761000d0002c11480c80c103066842d4400c0c0e0000d60301c40300300380c100c8205905610012000b221494040944e903008260b881007503051a005013001000810030803c543e61406a00070b101118428000303000c00b00c4031b482c03070240c0c1e0f12482c90240019000300040200300300100c0d010005448050503041100103040c01c0406170940441603404903175451205180540740310010 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 601430242 1250 601428992 601429007
    0x90209130513021f120606050a0305040501091a10050402030103080a03021602150a17013008370e0d0f15020307391a0a0b040b03120406 60
    0x5034202c081c05090310700035aa80c030f80340825440340d00d0035070f00340e8002807000202007a5500b02943e407114140201000515449421504a0314040c540040d83c4c4c3c466162450141c00403031405050404200e6800050840380d10000c0c0c0282215035865004c2582c5078140710581c0000d11000d04400d0b0300f48920f41c0741601a40083c04a040148d03011200800300d0381c001401e4074101010840840000b180300010247c009504003c0c0d880a170007203409962600c0e10208900038010035128060113207070034080c901c414070001c01c9459a0f0149005072513203602e040320701600001c6c0100c100ea0b12400380c5100f160300c4d4000d07400d00d50400c4907941c00c829501c00005200d5002141942180d4080d4111034000100f00015100403444d210a03401598900700408001d28030049240a00641c505113000c25a90000b0b045004a501d001c1f143c400340210300d18281a10350000300203810001820310420454080301c6a0300c03c4100e50301c200c2d010410320420000781b69603041e15141d2100782d024100070038002d141c002d551 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 601431492 1250 601430242 601430251
    0x2061008121c060303020606040b0d231002030a0515010e0a050415030f0f12170f0c0f03150a0f0e06060d061a090114090603070818030403110a0902091305 68
    0x51402d00505190040c0d044508582c0168016000102032204902d010702858400320320803540242c4809858903201042d000d02244580030040811500303900481c180300c03a590707124580038110340702c0c030704400c8070710280104032800d4000c0da0b86194003401d107601a5100442c5040003400440ea42402c01e418080146015004183c5138640d00d40c0000000d019540c0b440c03811445400300a0032000e1618140d29031381005054031091194030b03a0720885600034091200d0303111100682c2c8080b691501441c01c51203129000700d00c94031110000070407820241d0280b94207112078003a03482800003a6940d10818403280503004541850b004400810254500800a8070a0f0b05040b50300080055440c0105910030302d882055040035140450303054020360b00b05460042454084041703500c0c103200b04000901d0703031200030074800c2440300da03002180814000064140039501d1480841c0d81e2580c880c1000c9244101201142d441144604804204e100c1180281c0d8030f4800042c0c5030008100364005542c0107488003c0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 601432742 1250 601431492 601431517
    0x40b06090a0b03070605121e0a0b0d120c05070605091c061407081b1813110a050c010b060c070e2a0a020c03010902010806120307060603120206100812 66
    0x64000b0701a9400d1101c01e008040715180c081e03440304101c20019850f100103240108517542640e42c880f44215041c01d4030b034030260918002580c00c2c048000100c0c2002c0f02e0742e001d0410202d84881d0003065400c40c01089916006070102c58890340d0320b48044685110f084209500070020403014901e005000745001581ca100b20000320f045005884405a04c0204807605c1d00022440c2c02400b0003904c1c034003031440c0081c04100440740303443d01082e4054080c00007558068014411101951000f40302948000c4811403078041c250340d80c040840004015402107107071001a546022115480341c0790000403110b51180c07000103060501c1c45d103184c0c851881d0f0000c3c0004001c0c05c030786e2100c42c2081460700a00848070501d9a000d0b4440707c035054024507042803450040d00a80c90049943c015070381100b88503500c11000ca580308201102519603504500500400505460900002004204011910383c1012025900703c0f10156519080c000700005a841001190742000c11b4040c0492402c0008296400640 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 601433992 1250 601432742 601432751
    0x100201091703100b09010207210f1112010e0c01111c02100c081513060504050f1605030c07031b0203031c0f1e0507021207031e0503040b06090a 63
    0x39150300201c03904000462109100c00010811618003075507650010b0600d003041e180c1070500b00d800203983c400b224050700c035401d09610a00307810349690407015525158002401003450545103400d007500d45030070010a1103840b42c00d040604450052007401008008400240252000c24006450402d03035103d1040c01c41c0942c5000074005000400c2c1c00d40840c0700daa00500000c02132402503000c0f110600c01d0042007010030340600c40c0300050581804015681180d103811114160740c4480000c0c512071740695040b82c00c0ca02001005405d80300010310802c130000640212008152084440d44030403038007500b81c0e100520066010034800d0321142c2c0f460072400d40f03c0c58090003075000039127980c00244881d40360341502c0c001050201c00034041d0b805002d601c0d030742c1401000a02403621007240b45030440141110369500005002c58400c00c2003458840c180002d041e074900c0c06040c003c0c200300620700705180c801c000030050005544202c080301e10540e04481d50f441365444013000c01c40703014000342141007829104c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 601435242 1250 601433992 601434011
    0x909080c0a0308090d1e0f051603051b062e0b0705100b010504180b0d0b0c0309151302040b030a06061403060c0a0206040314070605040305090306180705100201 70
    0x10040c80d26041e019032544070f19450414080c1d07140c5254140c4010400c0a039070040c00038084203a4415200d0925810450304900c0820b10840c2c50b030007485e0391205402c00d403100c04070a16405c04000c0008815645c0d10303440000c10300070035a940b80300607241c0380101d86c10101c08201d04400040450315010f00d00314090304450740c84a403100c46402030700c0306035903d800140d60440000464070403042c0000081c20b055081514015001c504a02e160701d00000c1d51361211501e942c540d40e201c4270302800aa018901c0b51003400e01000342042c42c0c200b211002c8903031040c1d90200704140300c0c5540f601c2c440c0d00c0c00258171181c1d1140e83d09000240400b40301040d054414012120001003841c0501405800d0100440c80f483e00540b0400d46001c0c0302078120034500104019140c1d006a02203036181d800742cdc0504182046014404080a95206407c8080e26a504e4041407008055106004200d0080124201d5032503480703070407440c0f160710308020070000140d100c400100101e0819031200482c03100c0d10300000480c68007 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 601436492 1250 601435242 601435267
    0x3093c06090b0a0506010e030c060d0906060905180709020405090c0a050c1e07170604170c0109063c0b15040e06030706090e130809040e0d110313090908 67
    0x2c0940fa06218180c5401c2084555648000080d40c407100c01c50040461040140100f00244500054283c010303403030b880042d0034402e03560045c40c02004100800c0015182000e80100b151150700c031004464010200009000c45060003554140ca200400e214256124800920529400104e1000501070f040c0000c07214001c05000242400b588081e95903079419542c0b200c68140806034103c401000700d8103420b03400c07140d00051407a80c081d500049105440101c1695080345001d41104409030358200406181081005c0d040400160f0300030320086d41c64a013a40f40c2c002c0000b4000c03c0c5141d09003e12074503d0f07880081d07804c01c03641000003800b0003044a503810850645507201d90460001d941d01d40061104c9401c1c1046400010503803807030b100d040d0034140142ca80100704040d20708421100e5021114091040d0700e03040312800c1600410411801c1182031845484400744080040401c0d120f030305182424001208a680a1502464852055003001410030003009400c0050b5000442030001615800 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 601437742 1250 601436492 601436513
    0x203060a0516050408060c07060b1c1a0105221d0705031903020303070f0e0918010f020a0c02091305191202070e0402010f03090b0703093c0609 63
    0x8500a401041c1480c0158010700b0b6903404690381c0080000400007006a4080070034003642140c010b40100d50750369220705018000d006152903007544011000c07242c0342452404901d20285520401094880c0c100c542b0120140c2c071801d11425400c4145601c2c00e562802107015201615020300c2da0010300c1052541d103400b4009075000200c0f01c60381c8645000d00032850300300044401400c8050400006541300c1d5030094807404090070000074000c0580701200200d000f034160107180c80000e8811000307460174203118454224104005020355203000c2074144102518002c452903000982c50318004001c640c1e003801066071000f840c03d00e8841491001c0c50020700d05125080c002e022254142040700a5414100030480b01460040190f512020741007141c030b510600b00c50750080d0242840b003c0364103066420340c0604512f00c4002c1c90b080c0e00d80704208800342c00d0b80c0107840b0340e07004403181c0301c2c41585181d00b0b000c01d01400f081d02c580c400007510b507240c41e540c400003c9941688102000300d0b00e9070b4590744034600304 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 601438848 1106 601437742 601437751
    0x207140c0d02130b030a0c03030e010906021b01020f010e1c0c0c060309020609040509071806030803010918080a05280806211b090f010f09020d09020306 67
    0x80c9940e848036044e0400541a92001c1c007103883c000103441c0303481c0400c50100741c0340380403501035512030f06c0d140301640d4090f0010200d12040c4544150341000c9040d180d4110710407002e402d99050001c1c0100c107a0000c0500c014802c644450342041000101d202243c020000d00302400320106243c03001ca0fa0407580300381400900b0510500210394a4482e0461507030700942040c00303104032030000080010845080f40c0c0c0e1900400707079501c542000d0329020700c80984061403d0005101040d072540c060407111f8000c126961100002e40da43c0159031b0413a07070b00340011070004124003040c01801307080002c010905580400000708460006000b01d41c025042d24080c1e080c408410040f10703009151441c0c0300c2e4039081100c803044406d0004c51202c44880d841c25001e058044081024804c221b6800c6069401c0a0828142c642c10500c5403002504041c00300d15605868103140c41c0545c60070300c20140203 = true := by decide +kernel

theorem cover : BRFrame.Cov 601258992 601438848 := by
  have h0 := BRFrame.cov_init 601258992
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601258992 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 601258992 ≤ n) (h2 : n < 601438848) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
