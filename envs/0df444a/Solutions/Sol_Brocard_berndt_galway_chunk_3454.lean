-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3454
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:42:31.567988+00:00
-- url     : https://prove2.me/submissions/f40c29ce-5377-4064-9c9d-ffaba628da2e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 621043165 ≤ n < 621223021 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 621044415 1250 621043165 621043223
    0xa1a010c06240306063b06010c14010e060708090c0607110603340f0c03020708060108031206060c1c030f09030c1a06030d0f0309211701051507060b04090b18010b0d 72
    0x2499114000d03c4858ae03600a04600c500110300303228001c04900c1c00d1780640324143c8640e0170200144180d411800501400d0380202c4070440d50b1450f50702c0c2c03840c183c0e85d07201c01035403003161440002229a02d840346600080b50308446412406140304400318801c6a0000202da03c0e451070341002c44000b552032034220b190141d5980030082902845002103a9000040001c0490500980885090f51941820044988121f14000141d680040304070001217a5650701c41c2c0b030350f45250400145002c1c081140500362112044114001031a040036803040001c0544074400294400182106516107a40801d50300c020354051242480340341448070b820755102e5006014801d034020140c40803014102c00d40c40360b8947d40c9401d44045030f080b011510f00c003071130384a056040780e030f009140c3d9019480c4031441c40490360218100740c446540390060314485441c0ea02400442611a04100390940b034031071400110f01960465800040c0d040c10720580156450ba0002101c2c2c0f50086100c858a004101030120006069 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 621045665 1250 621044415 621044423
    0x70f0204021c0908030702010c0207080714060d090812150a03031101020f0409050402010f050a02030d0b0d120c140a1524030b0a1a010c06240306063b06010c 69
    0x30f0b4000b00900c09000d14003070140b503002401058051001030b600c1301d01e42e0051108580c0100c0d010842090080d80c02010544040c0c01039160407040191107040d5990440d0030340d4203050000e503002c1c0800002d94450761000950000700162207510380000e541ca10b85c0d11014082140c040a84d00901c0c1c020340c119180f07600fa00d500c0a07610380d03440041d00064401103c2c140e0100c0c10080281110794040c1003102c02d12001c0c0d5000d540360500003a1088000c0000d0040c0a030031941d0306540d10001155844001442c290755140c0002805141c41d2600900382400b01a030f2030b6402000c101d50001d2041c42e5039a102c1e144003640070507190003420304400c1010704003000205400300c1000001c00d1141c403000650150001b00800c2c07002c41078803032900b1109082c202c0c1203800150701b8020180461501e0f07100e6009040c00340081005a4441e00700c2e02e0302d40d4081d405c140d80c200e03911101002180b5911541d008100c4040c0251854040403160100088031610301c80025522424006006680b244012180ca00c0d80 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 621046915 1250 621045665 621045671
    0x615020601083304080d02270409020a12081b01050907090c091a0708070b010e130b070f020715050a12050105010503011211090a0b12011515050409240902070f0204021c 74
    0x1001c1d940408c411280720120040ca10040124941402c107070103031451882c2c0140c001302090349890080001e03207004100c1640c0207a001d0003213442e1b88002c035110081a000761000414203042040a0394201001540f0050380246000303040c20720203401040d001c3c00c60710f0f14a0500482c50340d04c0304114191280d00d030020031100d80003903c071040001c12525107050314015442ca00c0035641d042000d6040b144e1495000d8030b051048000074084910601004148024070300c155144581e491916481d0440070303030040c03070110783d0104908031104e900c03041c200304480d4046000d210a52619002a0051006008680c2c44e0741081c0c01c4c0c4018800311b0340d455030003002e0180c100d8a541c545240040014030022095500c500f0313500340f190245110500a801c00381e107030314240021031031824202c28250039444500c00213005051000003103550052003001490038141c007850480a0100880f9546d4604c1500042072113841070100c0350125a820540e14203490381039038010380d5019003800c950103180450034030309544c1d41 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 621048165 1250 621046915 621046927
    0x20d0204080f070f08030708030402031c08160305011d060102030c10062103090b09041d0a0303050106020f0a021908010c0c0203010f0605090a050a0615020601083304080d02 76
    0x30001111800c414201c41a103e0103516508480207000c0c2510134010207a1090202c14040b510400c0110b40080c0300a003110214180c0c02590000080d4800020300030482480130805105e01501070420300d2400740c03904000c03070360400c040100c1d070003e241c03a4107111081400c00191203900070801c42d01651041c40860b000c00d940d0580785000b8004d603004038159086480d042c01401d111050808640310360548a1891041c109154100560484c48649500ca925800d00890040344010007d40c000500c0e005014910307100d050260580344103070310402c00c640c070006020414020205400c00c030254100c540480840045c1120a085000c0d5080041d80794a40900f02039810f400100c940030482c425402070100017250318a82049030228452107410901e003000242d85003017a9482203901003601100043c3d0140c4410080d00c6490340143c110000d0390241005000c0070700104241100c00040951340300c00003402c81c0458400d003410001c0c510f82a0684804182003054000540d00d031410b0080003192140 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 621049415 1250 621048165 621048179
    0x15010b030a0b040903050702010f050f1305031c1d0625060e06060d0609060f0c020318030106060c02300a0213060e0105120c04020a120c020715030c03020d0204 70
    0x9030003540c0c800c50751441d01001141d607081c60f01a0341c0040e9090303120701741031060316001910f000a0b80d29071041040410446904040e208501424403040c60040c000011820007090628000b0101c4110780465902c1c5248546c05e80d0111015502041d404006440030703c1031404501c1d00e02884003da076440b40c0d0503000032296800c1c4d89001c05070038001d074801d004100c00003501030b848010a42d00650460b054500138000304a540e0080d25074580b1440b00002c0046d030b003031503a4003280e400300c0c121303801600001040880e1040c156001d00c01508114020410b00d454988082d056800e03800c0000e0080e640103600301c1200700111604d4185110f03034101002083c55800143d0740b00c1542c03181c1284940e20006070950707031050310b21a41c810385d1140b05d80c0d0207541c0d003000e0030005111607201080d1920321540c00e07030101c41c0c0c4a42c00502404800798a50031980201c60030034274155920650790b40110344c0700040030072008400808401e441a1a41400500e400c01e6080840c040d102c0d84600183c0c9a00000e8009042 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 621050665 1250 621049415 621049417
    0x203031b060f01030b1503160f0e0f0c03180a0c06180e01050d0f02151303120c0b04030302180901030c030c0b03010f0b0f09091005010e01030e060f0915010b 69
    0xc14168019940c00e552100040e0000300c00078000500450b41c01c000040c00c40c1c2400c0e404801d6030900a0403110303100407240c980b0045410a410024161111b2541000284140251290000082410144e4a251442c416280f901005003a0350301c403021040e0f05806141d05120b0542c4a40d0441603403c812526100050603228484200b103069005415001802071008079840f4140c031f1000748404610000c0d5210300300c00c1c80e42d212003664007000b2131201c0d200141d5000001c041c0403240720b8800c100b052860412982004620b182c01c42031001c4034104400040c500c00345158055803608005171500c582440d650881c0c01984009504800c581d80040700744a803914071603040b6445180040c4505481d056000c000d40020301c80d00166081d40c0d0001d000d82441840034208541c4288005801c1003522000101c12500960b040300305002c600310180070550b4030001c600d28120307081c20b040c04105103610f4540c0e0f50b008001c1000090303100c0e00300031410302c1d00300740900010700c09000b0814101c0c0d40c68645400d03c03 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 621051915 1250 621050665 621050707
    0x20402040e18190201020a0219080313180902090a11130315060f150f3c03020412020d060f0e250b0414041d0304090b06250609020303 59
    0x14511960801c01e542441c2c003c1c0303401d00d103903040c1e01400d0740c00443e42c24071258101c0500b201180c00790b4140c0122b40c241e0304002a010b941c54500c0c803150024034180d42c1042070000c0d07094006016080c07003481000340c0c03907260303005030404580031001035048210750381500280541c14889640c05076542002091020200b0740d08000100040300304955651604240c0d10f56800748a60706400e854a0020f4207410b010b581c14180d1080c450401c191404071002d012000c1003c010041801c00d00b09030624030080d4800d850a983e58045402c08601e0700b070812440e49043c41c59180d00a00c9540c3d202c20b4002000340e00c0d04a46c44218111909000768005001c000b91a41091021002c46d41c92400c40841e550401c0f02c00d6204403072040d072009181c28140741c10000021600103107960803d0b2100781d180380c006a410720f00f0070780e6502000510b8580e400c00070828242c5640e04250b41c4141c0c414043c0181f16400d016001c0080b07160208802400703042883c1c248080c1c610342c03030041e5150001040c4960320500201940d18 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 621053165 1250 621051915 621051961
    0x302030f010605120604020f010c330e161505120f1609240e0a0803030a0e070b12090a1e030f020a03080402040e0328030e0a12050304020402040e 64
    0x11807440000c00179503c01080350041c1d0300020048a454855001d84000c01d5000d00074100c40c0d03500d031038644902c01700c04030704017200510084011102610301030600c80c07070400c0a40039004d48102240c0d01c2c0301c21007980d001e00590b040d08145603203030408180654100c8110021400c0207980c02e1900c80b01030104800115100d1040c0d0b84096000c7c5240c1c3e01c205914010f0714022980c00407000c00001018404004181100040c8003c1d4141e41c5901c0c0d0780c1091180041c80000029650391418107441000da8400781e0126055a2000030305110134040e1034103550281030300d96948000d940e0740100381e038500400c0c0c4901418481c0048100211052241608400c1030700a032030742c03c800c240340d0b203080b6a02c0130040009000144138401060052515400500442d20f80d20100c03410049555542c84000715050a10701900a001005825154243c000d00c04005164070140296030717800d480358101d6461510105041000010002c0c045540355410f40700940340880d2641601d2030400d0044294100b00c0304940 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 621054415 1250 621053165 621053179
    0x60b03060109050108070203160f061404110d15090503090a0f03061a0904061a0301020c0f0105070801180510031703040204050a0605130506040207020904121106010605160203070302030f010605 85
    0x2283d80d5015424043c01440b107540114a014607500481c01c81c002d2002085503100c4031400c5c2200850080c0c0500482404092024101404d207840c09007280080d1100060189a06286200103d008500c018211100c2d104c004104414549401d500310f00c80c00701e200350b015810300320100d05948040382030800c1e240f02d00d000308201c24030010168044e090709038003540d010034440d00160004806401c84240201800902c0000c0c805d1600040e00766000005441520340c4542400b4802400901505410113940d060201c03c950404100c502e8402c006901c0310052a26040490080405809004000c0d900405450002ca403500c0e0b941c01a5401510164401c1c0e0a0201141018800b84240b1088540040c0f015421081000700d01028140050150b0703849a4280414000b585a81c1c00b040e2150b882400030b5041030340b4186003d031010343c1040e01500158001401842100e81107003c98442d0700742c3d1002c090484805100103031404c070103a00025018003681d250b003880038030150000c200b6113404449203 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 621055665 1250 621054415 621054419
    0xf080703120503011203180f06030e011b1e090b0f1b07210201020c09150a06030b0a0504113c070c15110a0302060708060423060d06060b03060109 64
    0x49031103010a0041e0900036030601701510001c3d004004070000e00f42050794401d00c02e9960304030384483c098aa803007400400e0321080f6222610701d00b0b10a00f00101203056448200300d0300c150300101015500a2038422420081d2541e04180e8020322135032000703200030f1480071750b20740380303c5c6003c600c40d003100801c1c10858920b85210400c51002080e41300984114503890301c1c2c41400c401240c05020400c403000d034190b0044189504003034a0740c0398858410040410321481c154100014407030410301680c07250b41011300e02920210543d58000381c44003190b40c22240803c1000038003c4095082c440c0b000046143c0070701341e0080c60140d041d1003546900c90071150b41a000400881401900f40c4101c2000604c40c100c014024003100b80c0100e00d105d002c0d501407401d048064000c0d0380c28ac0c038000e80140250056800304040111540d40b040a4503400310703041e942480903665240c441186424000c1820100c610001c0c002a0141c844903800805141c0095052046944d0b078002003520754010380300b150018104600c0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 621056915 1250 621055665 621055667
    0x4030f03030b0f030c03100f021b0c310c030e160501031116060c02030405060a05030a0c0e0906040504030e0a030308060916090b0309011b020105150307060e04050903040f08070312 79
    0x5c801a80014015141c000480e120050082100030341c503030302c9180e0a0100001c80d0401c60160040c08003428010040d11848100708503c1040103c4009030419503018082742050711101d51041d0f5104d404000701c1c003008081c0007603014100c00034541e440d91040420340211031020789400700489e0000c0e201000f110000e034001d107550744600c3c42c03040b8000c0285090640050700c29442204144498410789040c2919140054400d40c1300d07151080003d84040144580d1030040d10800400e03403070500b000032842049a010070907505004105501c203c0c0e41d0b41c000b60515005044c040d40c10040184030700b007460b88924000d07000307040648241d4050452800018150b45020b549840724004c540c81c0c0c141e005251480c0e03004a6400200418003e54a90312100a083c0414408d140051866000441c50746003c1c2c040b6083d030214400703034a2007540030b5001000308940116203004c1c000c0d003d4034081116621200101c1c9580f20700d9001d945090194000052200d0011880740d05032803195880340101c1a40c600 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 621058165 1250 621056915 621056923
    0x70929040204121b0f0b0a02011a0a0510121506081503030712121401050103051608061009050a06020609060702030301140d050f1006050f0108040c0306050c04030f03030b0f03 77
    0x340a80103146003a2600440c1014102c0000401114549401303030f03480b80100740d0320031490307804200144c10204000d10b81540a000c0e01154a004038200000d1103011000100380041e144250340c00340485c20f0041c54031a2082d8811080043e2174003042c06000000f14044882c1c201900c68140000c1815000c1074140035501c1341744901d000000d00941c108600354554405048007010341304240528005060a400300b580900700101c00507660b4103c90b90300d0540090705030340005000c105a80e10a40c24080007903000160b0981001065403108881c20401c80c060ba1903007029080380398000c0000000198141d40041c1e903620035080d010079030b4655103070540e05036940c1c0001e000b58803182d40848500074650400410058055014104175041101641041d60900f4030a1808210940c0c40b41d03014020381c1065031480e621980f0038a092000c81c03521b512805010205c900004008030380391004240ca080b180000e0303801854009100c0083d507a45823134003030b008086002401c1c0c02041c09418442842c54045 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 621059415 1250 621058165 621058169
    0x807030209190938060403050109051e0c0d0b060a030f0803010303030605010c050a1e0b10141503010e130c060221030906040303050a0e1b15030603070611070929040204 74
    0x4013034403901542c4030351903d64000c40c0d010701641091080c000000404c07001d0107041589400380000c0c00301403070030740900000c200c110a800605036102c072504030704503220404a0b94003290000414007040c2ca9040016030320211a51000c1c0429400380c08140500110340000c0d4100c80c403d84080004594402c019581c0c04950702d005403040e000b10f090030000c1403008a0030301c03070000e9a0703905090014241c1c1d1078651891085d51180300c9150490f50501908072503500c1d41c01545012100b40340c00004000400380315201c14003d10101008403400700741c40048280e0220610355001c2462810743da00c03550000e42d90980d00c1071000390320051030741091828070044204c900a008a0003d80321942c0c890320140d0207410090f1005030304903a5030056402c441c07828094030901d50490a0341107000d611150410412503ca8040010b11180400c18811240d50000d032480494049081001611800c07545032400c088441d800140c500742005010003519104802e48500d081100d078441c20601c06001c00d005c12030180d4 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 621060665 1250 621059415 621059471
    0x1104060302030406060f080c0306010b0f0d23071101051608060103090c0e100305100507090312031532210c040606020a031e09050108070302091909 65
    0x40005114240c400d070015948a03000d003001049556456480c40c044081e1544442295000220008203505c2c0a11189004080791001142001d2240c1da50001c0c9104000c4202e40f61a61070250075408004d080c000c1710702c4019a04000c8182c40e122001501c480d56004188015518020000c0d1800b1481905000007005654038098165210700040d8018085554155000440c003280080c01e807007440c0320b07517104a0a40018008503403540c540705141c106c68038000e4186e00c0c185810490300c0b07035108482c0341c1180d0300420f0000c21a40e2152047d4010b20580002940e0101d030000b02094180400301c008090858a4940e03002000c4894248401181c40050017a4000111642041c40b51040751a40740801c4c0ca400030788400d405410700180488206034040c0740980c00004a14040c10340010844000740d180d0f1482040440303041c8002085200d26001c0e0f01d040c0003101000c6048070740720744c2c16032340102005000c059841c3c0c0e2a20030b0469820903441010980342c1404100c0107d5850804e4a0380c0207001 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 621061915 1250 621060665 621060667
    0x5071d07021f15031212020309030d18150c0f0201020a0806010f0e04050906100803030f06040903030b09040b0628030f140d0315060903051e1f0510050411 68
    0x20310151141c1980c42c0d0010b4021254503860100180b21000c002900218803e4803241c10500c0341110160200c0c1c0107080c0f009246105104220040c2d40c003008860348030060180001e171103400c0340102250500d070700e0405029000d035403403c0c141c03449003980b25100049403074440101005282208900782c2c4181425440080da6201c042010395002d505803c0400e5030b40e00b040c0d43c1d8150100045411038104980049641c1c4c000000d102d9030702075035040c11015182c50000745195140c150300c0005030650150440d030045039510041d6051610a5010320600031005000c200d481c100340c01d0030000c0c00c0b0141d4095202d03510403d40303400300c0009100e018070307540f80300d4404089191035034403041c00b0024200c02c01d4400b450f402100039582c43c01804180601001d640300091000e10030160030205a025170004018030913006024004550005540a421102c400a002c020b00c0011401803c18030180200c0c402c144010f10425142c54540e007015100d91680d0408940640d41e68041000380d920300d1130141c5407480 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 621063165 1250 621061915 621061933
    0x40501091109070c120908240a090302190c090603080910030b0f0f030715110705040b09010b091201020a0e030c0d0b040b04110307140f04200706060b030405071d0702 73
    0x1c61240307200102d0201b42881100e86903954001410301c40d401c000c5034581c03141520800844100c401a4a41000010030100308800b407030f0307030065a5a840d07101d241048110703d4a01d241000203824404000d82080102440035968900d080c41d4650020801140f1070852409411a50b5210f8411659030820060000300c01c01c2c0340c0000d012040440d0088a50140910000030400c201503480540c0036440c1c0d03555000c000d05c1c1030300e070f0b60341482c0d031540116205034104400aa5159601031505041d84d2000c40140c0d80c07090700c100064a030303204030300e0343c0c108950011495080494002800811400d019400c0c2c84c800c111400402001c4500143c0c010040c19040e0041008a0a0303862055802445040103090012424002904d0020543d0180a40d80301004900c040c1741416a1040c1460100f6142406017030720b000041d00b00f40e032092081003400030000c2400d005003d904e4111000404020000c69501e0401c6c1c2001503c0740030078015610300b40d00110340340140003d4110f40621400282d806012440 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 621064415 1250 621063165 621063173
    0x50a09021309080d0212061c170f0d0603060209040f1515050c060f040c060206060a05060d020d050109050103020910060e04050a0617070303030e030c0a0204110f03040501091109070c 80
    0x800402d50a603114802442034050032a644d200902608002e41503c035410f15005082100c4ca803020300410a42e403251b0040e0344002200d1181038030380c1d10710400315180c48281c806079401c0c05004025102080906051000050000c1c40e0300030f001800080c1c0c0d0074407200001003486415980d40d590418942c0b0b889050401541d18a41311902071248280380041c078000d868000c440c500341c0f060341c41c0d10b003544503103040c0400c001c01803000000402c00b900107069603240040c00070380905124401c40e0b00549000481d4008071101b41d04850611002500801c03013135840b12900c0d80204400d0108a0042e250000403d0103034507508000000c440495807089444003010045c0805404080e1450380c20b035841c1c240100700300c4180c03040410843c42c15402000110304c1e50070000c081d1188400b10714a43e070010040c0881d074080100b500c134540b03501030b2404104c0e40d00e1002a030f92641704120640c0078450340031040c40100f000641141c03c18078001e030b02c030800b494048000c008603c10180d03001c4000c5181441070300001 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 621065665 1250 621064415 621064421
    0x604090c03020c030309010605091003020306182a1003060b03010b0d060504110a1806141803031b060a02030f0402090a09020603130b0c0f1c0b060d020c01050a090213 73
    0x2000940350140c14885280000f6140d90400e6600c0a056512400c040c44541004415070303500521401e5480d0071186550041703030302c502010301110280d841640d030320069900100300303203100c06031640f10300b81a03550305c07800028001c0c00e80d02500384030342402000f40d05a248a809451f0036100700f502500e181d81d1a24801803001e910840c511800607031035220004055869101c0e00022045001000b652805078550052098200344020003620721503070f40c14800590700a210540101c02381030360301d03540c80204d40d56181d1080102c40300c640c1480005104594018071140003510007802404440c200c0c0c60f40700000c0103a010032105101280350b00c000041c0549842008941c0010403c080020070000030f40201d0301a03802120501e0032032075042200820131406014061b40403107180809070800100f4010240705101310784040001079410810b1b00d94007042680b0201004a00400c0a56105541040701d00a90406c003914401035190400281c080002801402c010a03070041482901f211010320b15030003 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 621066915 1250 621065665 621065681
    0x200c07050d061b0f0e04050705090609010c060608070f080318012a08031905010305060f0405120301060c060614030a0222060b040e0711060f15030d08160e060409 71
    0x115250402c4800c1e81c0f084841965070f01e1895680e000b07450500080251106091402842c0190300d000f081182c00d07540441520b95001c403c64a050b50b49012100496840e40c03a03110182005290940c00103200c0030000d01d5800315040b1030010351443c1c0da102603a40d142d001d0381c0011a0040d0398440320710b29031744c810401101c05903000394944003072445400907045030081c0703c40c0846001030b00005001a101c201100408021240300d000e000b9581141d03240c503210000030303018041c00010400070600b080f0307092000404c020070707903000c480d160f681d54034005003112600442030b1903070b515110303004c00c102d40d4100880100c5c00c1e01500900040e03d0b143e0a0003d58242d00440e0703070360691405001c03a00010240903181c002d00004940d19100c60400010192242000e05410188a0529000350480002040c3c156011460a0220180b13580b86803c4030560000c041c0d043d98517000b0000c58100064100c0300050084a0250103200040780b01f000c240d50090103c0b0305194880400c0c4402c110a2001da0041c6c05 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 621068165 1250 621066915 621066923
    0x703020f2d01140307020109030908070f182702040605090630071701050606160f080f07060507080115051b011119023009030f060901200c07050d 64
    0x4807410503001c1011542c02c05d4030002c0042c0d4454a501c401c2c941c1c08103c810252035600050203482e458000886000c16182c030405d8007032840038017400350882c0c0f1644840e03a40c0e00310001d401ca030003120b01049015446480412485141f90074408030302820030301314540c400e007005000f41011040c00c103441042c0e41301d00c0590300300c40541e581101040071803c1c050b10b401007868840015087c1311361002542920402006035008650900400c0c5044032030310400c0600d580c119010704041110341c1442407c520400c20310411000e030000780c0104015203540078038851140c5586403442d03a600d0b6030311401070710407400d000d40c00a08107000f9841e20f40809280c03110409908000052810f0034094260f103941c0080302180c1400c40350200600ea0590140202800040c0240e50b0095000d685003640c10084407101c501d1001c40000b082c4808a524204001544c80d00c4440855045160800c081406400d0305042c11026a0040354810502000c4100352041042068090000241400c00b171240401407220161 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 621069415 1250 621068165 621068177
    0x11070305010606020c091f03030f0507081201170c01020303070509120604080a120e15070315030b06040614030309270705030109230403052a0703020f2d01 68
    0x40060310034401c07000140540d0b005007075080d2000c070412402e13070801094040e444183e09102e5040000040280b400daa5050425403c072040306202282d04c0c4c06241c0380100030090004186c108190b1a60340c050480312124504146080800005a180d4180051aa005d64000d002080306140108050011110080e0880d0b80441c0c0c07404100d03180c074105480c281c520380e60004560011076402441c05403c0c829402c809e04c0174140881055607102002502c4407510301a02c00032643c01071003500315050055242c00b0101c19540c41e4102040c0110060b122140318134a4040c00189100c0740303100c0d0500c1000005c0185041c40c43e4a41480105904506a1844281035160104610306040d507458090344140c0c0c0c5041e202d40c10a0292421144041c20070646a800112009450040e40c030328554030583c1032410b61b0b190381000c2d4200c00490710300d000c03403928031001c0600040482400940102101d000b100e400c40280003400a0090302008a4190b010200142d5005105c040e003107405903510386c0d0185800c0c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 621070665 1250 621069415 621069419
    0x20d06020d02130e090c0a030b0c0d0e0109030f09120f0609050a020303070305030402090f010e04111311090405150d060b1809010c090f0f091509022b1b1107 69
    0x520442903004500b0204100084c4642c1c500300f040300003a10b003402d5887d59400e41c00d5444c0d02e80400ba008000d41401c20f0000340c1080161001d4021108100442000703106140305860040d05288001c03001200003400c00c08001210f211041d610341110340c2107850b5009020082d11403001400302285e060340d96214030003141300141c03070030401820000c0c041d40c2c03055101d081600c10002401805080010151010001808441904241150801d0788882503101c200d034190045030300765081c0101000c80f80c1c81d192020104600030001041d180004030b800f0401c51382d401800500102018000541000b24551342800140c481c6d4000861002c000b0410b80e81100510403c41d10034404aa900d00186d440e0100d00d180c030750304241c000001d01100001407207014103190b500050501c06106002c441c5440d800540c1d100c0348580d010402500500314250b41e5a80034840c08141c140605880b00c10007860004c0d003008691041c82420700c0c80304490503907000d1380c02d14241211001511100025580515000 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 621071915 1250 621070665 621070687
    0x41a040e0d0f180815040c1a0f09040615030614040e07030b090a021f0e01020606030c100c0611041701020a0807031a1f0215060a21060c1206080109020d06020d02 71
    0x45440c80d01045e80a841c1d00d10303052402100c20300440c0d01180d220480c40030f4101811a0180c10391300d00a880618094440540100080140c944c0780d10443c140c10501c82c0b0039040c50b515811603020789041601c0e0507440a456400e21086440410303802036141c0001200340000b42d060110980c01103041c3e0100c401e00303503064002503402d400c9080d6001c1181540807000355070719080b054540800d5024000303040d1500c3c0110200e5124264082c15034852808014103400c02805003079490001c0340c1003401002920201401d51070700d50303c580121403011080010641149805008481043d41181d441c4c1d192600c0701030040d0007a100781000015116007011942069840308080283d1021084013041d401024421029060a024110307090004240d10100009502c0305448482156060380150300c41c03c10300c03c04110591402e080c010b20890a090400b03480960049a10710f00e900c91440801030a03a440310b186088903102403000b9088002700d146540460080e0b40544028200a6405482c00c00000a = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 621073165 1250 621071915 621071923
    0xe071e03062004140a0603050f190f020c070905130c0e0a090602070510180c18090221060a020403210311040803030a0e2d030702041a040e0d0f1808 65
    0x490702986200402c84c50407480e000702c1d070310001c0005003806c01c0319003400c601403001c0c004024281c0c0d403213480b103a80c6003003512420b0780650100281c4500c11500c1d45121041141c44d000c0c54852095114180404204041070202e800e81c03100b54010f04a044d407500d0309490181020300284180d034101c0d540c454110205041d4001403100b58407950141c480c12050b50008011680c034003652150302154034508078001100791041105031030b103094241a03008028070208002e001d500030001e4100a126250350f051605626040700000740c0c50041e1a6a580c0e030030000000c0303000384d110140c68074416405400890f005004d107695502c1079840c01145801d0310114a100945c0150b02000c4507900010800034450b8403849a0f01e030101d11030f409030403250000140c0c00415607081c035981c41c40b1496502051a4900e040084410495000c1d1050080c0d02040c4d10900b90342d5003422540d0301540c10140590a00d00700403a0185010480d9264074040008104085031148009030700d030030103550700d84000b02d00040100 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 621074415 1250 621073165 621073169
    0x40203160f03061a0706050129030903090402070507030b010b0315040e1005070f02011107020d0b0a15031406070207061b0c0305060c190507030906081302130e071e03062004 76
    0x15011745d80c5c1d0b08914108080741c1050748a1180000c0103001c20715910031110b001910501214001c80e22a15071355042c0d03056114001c8000e921a1000030032030200701c0085000c0007100d0080d207980031076070798400260711a48000c94601281c0b06403100ca40c14640780c2a8030100c440c4a000c4121820460340d0001041200c0040e103070000481c050026882c03400e81d09010b0080340ca014809943d05082a0b41d02080c1040e0740d21200502401959000035100c2000b588600144094040980070b450f07540d0400b908a0505608448400d014000c0080d54040c00000c0e0181100c40d15520081440740522000380d4016a00000f240c0d0714560b03000000100d402002043d00843e07040342c0050b0381c1c400f00b841000d080341d03024110605203e4144403107400b02e90002209000c44085052018081d907845903480b1001103562002940034124805541003a209940000a2801301070220f5200c40d848607800303580e07410002c00647d04d280d048030302403000600940026140780b0988014146144100c1000c81c2150415 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 621075665 1250 621074415 621074459
    0x1e0f090e1015230310050612190c050108060f0103020a03111917010803040e04020f030307050703150608060c21130c140306130c0f030c0e06040203160f0306 69
    0x2c44014003229aa650744801c8a49814030351484400c05000800d0301d0700c01c001c08100455030703a24005040c9464002a00080f041802d0076a400b4490880c2507403880000b00d001507800e503000380c501040d154041d414040c02080004c0c0380014091428004401940c000501101010b894120007141d0444507406801840070100081e00094042d486c000c0c280368490414100c0041c0100040181203000310840f400d4510a100d0360440d6651400030550003030810104e80d0b014803000422405026021501348240d0340304c0e40e880c0e1103105460310302e0f009070f80f00381c000c410482d009a000708011003c2c00008000c7d204504440c5240784000c100041c900d0f4a0441d0505501341e9109584030400c04000000790141c42d21241a544112452000c656100303070042041422582852802c424005020075990080c5900015a4a51501d07803510048051891142c40c40081c0080c01148031481c01c0c0c000d80b48900c0b810205115800c401070800c41e118146459400141030740c3c0d22011030b0908840303607015110080 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 621076915 1250 621075665 621075701
    0x807020c130b060705030c06060301090c150c0c0603050f090d091e0302030a03211b050d060801020a050904060807121b180e0f06040b011814010603061e0f090e10 71
    0x47c641c054107240004055503c079925101c98800002d900c0920141550640f03160b4030358002843c20107507644a040c0401034403a0a4098000400c5581500100e1113140400041c8030700d900d078144210341d074440100c012000b1a41510741400310110f00d884591140813038850007004a03680390046030a09400000c01e500080b9101c4014441c1304c030a07501900803541074403081200720130004100301c401c80d01103c042c0c02c00c00d0001e2a2102100103401c0507000d801100001c40d5182c15030304001d0b10a903c4102583c0c012410b00c8000206100040754800c00ca500c0441c8208248081c1c0d9600c5d05554001100c0207080340c400100450160040400e4001483e000840015148480e410052810710440940002907200004110029901d0345282d03044814403041d0040b01142c00ca1820080c05110601c3e00650a0031000000c0c41d40c1d064000e981141c403100718a80d1100c204050741c01000c21203012300c806480d480e1804104c1d913207a0b54440f911403090101941c42d00d400502406c002e139081009640c0010304 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 621078165 1250 621076915 621076927
    0x906160f02011b0804051e040f1a01050f09040519050a0c140a090603050901020c0a08030f1e3c0a0605061602042d0911010807020c130b06070503 64
    0x1070080fa0602c0c104070a518622074020540c0e42e41c030030034402d138040c65015031001d011400e14045948480c20507010018414081f200044d225507005040301580c1c0c4551012a00c3d8054842d4018801ca9041184002c19246001c800700140009001c014100c2114540c00b5002c92901c5203441c41a5401011910030100d00540c0c80c600050030100303c1002041e0740c0c1020050f1000362500301000707901712141c40c00e0104840e030328400224024003e0307031400559401104800020402d911008500c6140c568481002d1520b50020050009002c08a40024041a200030440780c2062110340c003030910030080c0410840859104200c030b0b020a484001c4a9555040e040c420040218014807002c0c200554003681490369902c80b5213401605043e010780215907442e0f51415150707100c00190100c0500d810580d80184042103404001d2615041c1581c0d44d00021010354400e42c403510146020700140e40c000c2c007105980d0001c00c0842c1c1014800407600c980e03524000201529090042c014441c0100041d6032514 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 621079415 1250 621078165 621078167
    0xc110303090d021e06070309110301020414120309101b060f020304060c05090d1b0b031618050f090907051504300b040510150303030c080601140906160f0201 69
    0x103910850999013052030030410071038072000018035079440301c1c880c80c01151f44600c9041003000740a032884400d4155000190104180f2100174000c007030601d00351820300d1076020600c0343c580c40c0e006841c401680540c0031419082e03ca4811b400c00040003582c90f0304062407107030a556181c1103442183d502d208064001c002c01c424482e4a10500e400c0d556141490751901000c600000d092038003000d80107240c00e000c0e04084041d503000c1906103000d01990801207940742045007040001d008822030800000b50601802c0c600d421504846008a40e030240c0300c1110a40580200403194038002c220f4003482c422050000760960f503008443c0c20b0062040c031440d54403070505813074102c1c06407580f02c00f15040d030743c5d08481e0b038000b507108201e0f041007500100a04025186c5103011820500403101c6d1920f850705101232076403126400150007085a1083e28208aa0031224400b61010641212558040f501006400010680c02c200400710403000a000d10f141c1084440030302c84c14400d941040e10000c0450540c5400c40d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 621080665 1250 621079415 621079423
    0x614120105090606131b090513020c031207031506050a090f080606061c02040303031b11060c0307090b040b040914040c03030e0406030f20040908030a0c110303090d02 73
    0x550200a01c624508a034520b40d6520026242a000740c40b15902040d180c0d0051744842c0e420074000540c41c20110161200405800d068011544182010703200d820000c0101d10840d160012468007650900818810b85840f10800074145003d0544440503102d00482d441c00081c050300c0d0a03207400303032207820245000300007004541004000450300348040c0315009000403090b0744894200c9a207507603031907e104421601000484102c841a002040100c100743d0550044501280b4030500340b4a149010607003191742ca041b101c521007ca400c1000400e4819800c400110307400310050030107444041c2d0320300c090070280e400341c0c0c8201c5801c4800300301449500320601420700c0500206414480314141504c41520070b43e020300c401818008102c10b800d0180d141c070382241d0007c60700410100c40b41113140c10032512813402a105401224070f8240f01c5405441c03c4d200d89500c4640040d081401e503078600c0e46034401803182c1c02c02d20081c4600102280c2e519a81003000710b20070702142010b00001c403c09800030b850 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 621081915 1250 621080665 621080689
    0x606030b01050a080f040f20100f0e19050303070b04020906030f0d030e0712030f080c1305040e010b1009030302150402130b0409020301021603080f100521010614 71
    0x1008400c03c406006103034007648180e001181610241d50f07989031403500c0031503e04003c800504144040b030811801c0c00090708900100c0c181900c14240f65050104200d0300c001c045095100814580d001485603400c01401ca05410509030312000c110988038000a1b01e503030004041242c01000ca0790801086080045040303401c10f0042c0d005040031041290000e40710200100003404050303544155132001c5404001c100c005201110006aa8140c5410000c140902411203078010501c43d40103e078616802c50b0481d6086418840d205c4240c07400c010810000e000d405090160360f6403102d880d89116511801e158240540c103489001a96196281c0030f8200403100c0c80d0b07020302030948003c01025031100ba6602c0c1542e845040300007260080000000c000f040460400384d05584081800604914810000d08209000e82c56003846685c81464405085508503040300122141100420160600090011001c02c8a00100120310741c08a102421140c8507485020032880d0220007a1241c286141c030808 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 621083165 1250 621081915 621081917
    0xd1d0304050603060d030309120504080d0e030c121606050c0d0305040201020c10180902030703060807030c0b161a0103060501050103090b01150e04050f0a0e16090902040608010c02010606030b01 85
    0x8140340c0340400040c4103000c014035050281c0206196901018400d42c030034950799920081490040c014800014035503000340c0134040d201d100740302c071002029000b400414090f04004005240c022042000d01c42d003024203400e40c440b54403580c0503c9508621850000e00030300f01644d61240c60f4080c0c000340b58607148140f1f081c1828180740c8414000580d0740031031046c01094007610101c0d22056100070482d0f8445554800e6401110016030220341e603c180c0d00118014080c07503400f070044c280c0f1104d50325150302040c40b001340001602d240800c458000c4c0006008080c40c9150000d8401e500d60311050501c0850882c150700900124005008005d03c0f0b104043c00740c8428a801c000e0840c0f280c0d90085051018003d0b003188003404861582d41911424280c841c1e0380000d0814001c40c2000c0245100038442074502b888843c5c10003101d0000200300290030007030340806502c810507062a02c0d41510041c91203000680c2c1054896001080040090140f05042d503802c0c1d00014182c2d10f050760080c04c80b02d05480040c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 621084415 1250 621083165 621083167
    0x270e07020d0507080304020d0807060e0c040507021203060d051c0c060609060e040b0a0204180e0c0d02031f0f090b090c0f0a17030c0105040b010807060824011101020d1d03 75
    0x110120b01813a00b03513a40700d0b80c16140390981210509042c02c46004002c0001c107501c0c180b9a041e240a8004294052204001c0e10f00f400381b1b444511090f600c0b40048811340e0107946060000840700d240c1852001101d03070084e0181d5000d144004011051070903107111083c0802c40001031001040756510609006119a0f001040070300e041213100c66003540f0181c40582846540b0020842c4001a581190001c091400e4812928451220620050007031000010464003485240e00c81038280302e42c403203030901ea0007000742c640f014520144280c0c020805805200c0c8a948050705109082c00e0f00c9021401c40c0a9441102d091801d14481032070420340305480c5003c1c500c0214110115102c058111040d2032004241d070800d0101010464030317600405403092510340c2010140810b0044031450b540c10703942180d00340c968080d140e8405850070901603541c04800414040c2c0e80e44032a41c1c9140300452400d052400c401e0085401041c40d09903081011a60100c980d40c0e01c117001c2c0c5007011500301e032007040030700095 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 621085665 1250 621084415 621084427
    0x70c140c0a0506070302010b09010f0305060a1b05181c2a0902090312041d090109030905220e0d1107030b132d02090c19270e07020d05 59
    0x10038460400e51146501803c004200f45003051300030340081100c200c0181001240b0347c0d6a542c407284001e01440203071054040c85c170106284812501031151501c0d0070f0414020825903490041300e65506c0b894a10824014007a807410190383e4418640100b2900d0300c070300c2501e0080703e06144c1c1e030307021401c50b82c40d003c82c803a017080503008903003508040101c0c1d00701080180c03a180700102090402d800030500140d02c150024000ca28060340c0c2e1a000010a80081c26517190b6403010300990807124904c0d00070340481c500600401041c030b8818450068007188a0b881000f6641505460040c0d55240c070344011980c0100d4240c0c11001e510030840301041d40040014951a4030315143c0c6003160501074000c01130030000c21003440038020520551040022010b8020804a0903138404030b81c005c1d201c5104a1042c0d9200c5d010410600d03108041e00e481008001d000d1500284143d001c2d140038100ca9480c90300200722610034202100003409000080842516500c61494101c03002424401054580814003d0074845 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 621086915 1250 621085665 621085669
    0x203071205061f02100207050d0f08041e02010311070c3b070507020312040609090524210c090105150a0315170a1406150904020612070c140c 62
    0xf9100b07a1032105a20501c4a04003c0080741800440c62403034445600000b050000c03c50f0009443c024440d050740e40300007c02c8001c000310748024094030090204954070318500791400801c03c5492296205050015a0301e52840348200e050b00180b80a86070002c030620100310050409400304040208146001c0300004115861000c0032030404d01c41e800c03000451300151100303000c5c00807203504035002021503200c1c002c00c480b480101d9109000714000143d864000286404103401454022b0043c100e0341c1c00c51600d4103a02002c0c09410348507403980010484842c48005c41d00d814002e00001762000a003444c011050180700341c002e8107901150141540644400d6002c101d0f00036149540c40910300031620080f480e050000041060b0403240d00b10b50b040b0b88241101c0800122401c10520942e04010480c0c10402500e495840445000d011030f4060742003086645020364890758824402400035042011808000368404011075402c2c0100d24880000c00c11700c1081c040e0340d0b0703e0301d0680c03000741002c1d8050301c0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 621088165 1250 621086915 621086929
    0x161514060f0d080705011d0d09050a06090501050a12050a090b090a0201050919090614090a060803030c0f1b032503020a080c1005150406240c0203070315020307120506 73
    0x90303e05078020542c101085001c1d0403101840d04c3c00300401603c10316450320300d0b40b612100504c800124000e40d0000030b0701d0410720390321011115282c88000741c05191a0040d64190711070004141000810104212076016500c101030107544c000000107000201440d040b031240d10040c02030000750f031080009100617a44542207a24584081d521034042d500010340b80501c100e115040610300d281000400308145d4095055010124012122110390780c9405607410b0440303980c0c0c040c22030719810810001e201a0842c2c40140034079003100c0981490404074202030a81040045000c440035007002400800300390250301109650002c1c5030500d8030a07806035130003a58850704044014850f501c045034102c0c81b03100a011344540c41611040078883ca05d003070001c07a00b143c0d25104080c0d101d50711341400803840300340c0d41012052070656042180da0742802110240c824068200c0c08980c14403034078070302100080364240c0941c400094003202603282e080042000d00008bc0c07082c0c14841451070305e81003080680e2024 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 621089415 1250 621088165 621088189
    0x2070602151807121208220308060a03080f070309050109080d1d03060412020d0302070323070c150e0d03170c0c07030326090d0302161514060f 63
    0x28001100c85030b4050905802c3c07500c0d55024204400d909542501030001c000718444144085980f5030b00180e40300030304d2100c092130310004001561401809500041d0040e40702030f40249000b0320350030300d1990300d5494a0a0b03601148114101c60000714090081581000c41c00000c0d11003420100d401604081c0a141e813122032841c0c1d03208001015415140b05028030310b617041c45010203401d4801c4c6280a05001c54091036031640040144079189415004510030710030b45080c00e0703040c0e440005608045040c004c54220b2400e0011210608102c60342c0040e44644d0510700416078004038047c06145610040c051419000400f80903504100c45407001039804070014000c0401000312a80c82d458500d0021214081d91341d106003540f24042c804024550080e80c0120301d800a400b8000c00790145404074130700340b94140e0340c804503a40110040303055140240c0107000b00b002070210a40005207140c03140401162034040c400750309a522000c1e0b5290a651802c25584000b041c0d40a41e80107100c0b0010902d040d03895 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 621090665 1250 621089415 621089431
    0x20030705060105040c050d11090a08161e0611100204150906020102070305030135010207020415080c01211506030f0b090c0904090507140901150915020c041b0207060215 74
    0x300322002360010360308280d0b0f10340c0f0f6001e0a000700241d00c1c3d041c51a0f03212800620744a0707ca948000000311811340b6000c413058000c0c4540c08501003440d040742500c824601d141d00034401d01450848500213107403403011308020711641040120025007628060031303042d20f42d0011000c40e4010000c0001003a040710850b81121105031008881ea58100204052034071084500f40076920109248140841c0c150003a20105000310f5003008070700702c001541543d0941e2032203050301c0c0d600503400103400380d0700074a003910001c000314020280c60002e0704d0f1100215032860020241003110740f0000e100e0258140b207880c11101046408000080d030150018108880003809240d042200041d8841c1a0b2190703004003406660003001c4940c00794a8003d1540c00c2d81070040032500900001000041c900e114154200702c458007500e03034001807420001d071495456420f500b00303800d41c42200d200041c2601e680c031901c140038407100c540607010010240001d040601d82c2d0701040455119841303201c0038181d8816420f41101c18 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 621091915 1250 621090665 621090671
    0x6070806040213030803061914040216051618140f061c0c030303140f0705070f020d11270105190803030c0918040510090320030705060105040c050d 65
    0x1008000780107071241c4154039082d1200e941002013001503c80145002e42821160a112241500a0f42c2c42d2408036105c1c40485650302c3d00400c155081c56402003d40f40d0a1411003041c001880e21000d140c8026600401c0c1240010502004110140019010300001100051124031038290ba44014118050081001140720300c1c0800c0140c0c1d1403c0858581c100319613139641c1c1d0300d0242e081c0100c3d000e00300c0c4802d070046420300f4100d105d0032036801c408910501400c000c0d00c105441e030364000c0b0303081d8011300d03000c5851580f45452a405a600c4100009505109444d103014400c03114040c030504000b00a01a83d00081c0c080e0f094400600b074050781815100d040e03510440e610940340e82c60610481c40c1e44041ca00740800028014080c410302c008050220050ba94541d080b10810440180c0d4002114050b0454110b60b40903900241250007042d5054020303d8442d0a03030000f105070341c0b00c051034080d6100340d80e80002040401c200061280e0b80c0101802c64081240c10f00d183d00141031803003a017805c945880d41d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 621093165 1250 621091915 621091921
    0x62d13060305161422080d02010c1d04060302130b01020d0e030a02131401081b18010e0411030618010e0a051c120501140f041e0f0b0d060917070302060708 68
    0xc2c6000a03540803017100207801d00c0389816140001c20b03411150042d44010301504240b0141180140102802001c0301d03910908010700320010f4100000e41c9284207540981c65090010260381c5000c0800d4a40039901c2d800a03044400e84006842d064031901c1881c1407200d00d1070040740300c0e46c0100b4650401754040e18803480c0bc4402002c0c050007001007000400c00345920700004141a940041c80c2c252031050303100c0084807001d04600b00050320354403180c0c240d544000c000c01844016104400290400d00c178140201c0c541d0f04c207200203810100700f00e0700301d00d09041c204a18400b0400074000d01840840c590090000bc8500d521015100c100c0603030b80c840446281060841a94800c0501c01c119610141e41000710796101c1c40103d80c0b24210380d00c0d86120f00041308440c05285801c1c490309070182c2030a0028841d171042c4000880280002c0d86040803410394800202401f622400d0032000181c0c481e00e030000d140751140c03411345050581100c010441e030030107202240000750000b81c1960041000c0c00c00c41040d075 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 621094415 1250 621093165 621093197
    0x12102105150a0915050123120709052d0402300a02120c03100b0402040509010e0108070f060f03020310120c14011d062d1306030516 58
    0x9240e210041d81d440e460420008907540d181e001d0445148604030840f861001c492540040d64400c0c02aa001c000420718200315010201d49204403900025002505058800f8075440c2803d95a0740211070b11a103502c200038408140840900e010040e0f01200f40082d0303c01a81000f204d4801003000380901d180190440080840c0d40040c8000142c1d220781441880d0010a0a0348504124004034022510340703004024800700465030079a40b82000c1d004010607a071148601c009010b45c401016009a4200404141a11441c0c013450103040c81e20a95610b80d45001c0070300b4036140256000403034032a298038003448800da1058210000d0100c518015889880740c0984006800890340b0044816841c4402d40080045003040503040310503003200207005515520065401e0001c00b50900c03000421a8115101440c2520107440b402e10395070003c1a6000200c0b040c07401a51412950f102c40328000302d03500d203002d09200b8801010f00014a003d0100e400c1502584401c0d030481c1c030480052102a6140c080d5032 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 621095665 1250 621094415 621094423
    0x2060a080f0105270c041806050120060f0a020c01020a0305010807080a020105160809040606030509100615081e0405100b0f1c0f06020a0c021509031e030f0a030212102105 75
    0x84d14003021204047c1c90646a000001c1c019445040e010901441441d8440040d8860200c401003411000d046a9601c001414003442001008105055804e00c4501d40c3d11400344054079a000307258400040f02d5041128891070b010099000d404c83e41d0001000200503680070b800c1d500411400d1165031080c009614140505d80119003200b5001850300200160b4181c2c150001030003144080c090343d2609440c12492015a541400342c01c0446030089080405075100305280ba5110234420a0440324450b61221180a00300a48041c1c0c2c0c203500054070040584104d1140760284c1204443d58003190010001240d120070341405031410210440200c030050091010b403d40300d0700e612000c1199200044003002c1e10b003ca03100c0c0103078010350800c08010200d1400e2012600a0600200144110003030a1409201a40c81c06000baa0f50300060000100803d800030240034000341a403030240e1030b038a410030102c0e01030800030908064098a0181000307040310810080c4100c400d0306080c0c41c9000c54038240f26180c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 621096915 1250 621095665 621095669
    0x2a03030a0e0111331006080105100314070f080a020c1e0a0f2003010204140d0309031707141c0305060109050a15031d190f02060a080f0105270c04 64
    0x10240c03550f404448144e011000e03c0d800261180003041549856000801c0b11820b17015030004105a0030042c800c602e00b0300c010700c80d03540c00c0b480c001c03500035005d02006001c00342c04e403400400b00b00400074841d0a141c200d4202d59120014010842c00c000c2014012562000010452144d5201080454600a4052152543d160342114450381446c25030314100300c2c40103005803048141c211180d1041d01a1a040c001c940c21116000040754071100740000b080003c10305d40c1403c4041c040da0200c0000010844100362010540103007955403075a105007400100c0d4080d0030032284070b9810428042e12090501c40988114000d203180020361503460100694903065203401c0543d2090f80c41c1c00c005241090120320014440c11681c080c015003246d2407400c1a154044c004001403900084001084000c1100310708503800d0080c03441200c03c8420ba0017054480e440811480000780301c002c20845080d40a409107401030106a03000503102207240e8608070001d18000030106d6549402000c100011078580907600 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 621098165 1250 621096915 621096943
    0x3090609210a11161739030601082a06160303020408101b0f050714070b03041101020c01090f1e031e050c090402090115112a03030a0e0111 61
    0x4c150281c50300200700d03030000c40c45007080298005001000d003c8000c1010540d940302e8288284176582550303c0080d03413a00301040002d02104d85207900c0c1e807555080150724001c0024038094160700011001c61382d0200076591071521035207403180508080d5140c3c030040f180141d1368002d50202043e0145011400b0b03108560000340148075a0341005a0000294040103219404800d15485482c01c208282c0e12a800b07030b0b02c9170700492814080038001c10f02e01d02e0440c0042ca045001d4031076039600c0e05001002a042078038241c404840f49040c429440d6010403618110b031401b424100c41c803500c2c00d02d001980c02090700030078502d0000301115610540c0d40c140070501440e48a407800700010301c1c1946580901030154010b81d981d20680039403071544c1c01c00d20301740750089401170603894440e030034006034540c00200e00744240c08102045254840c560000c0c000c50580117070b40c440015456003103400780d4102c0c1911110a51194104001c22030086402c901c0d6102c00e40702c00c1c00c00c03000e403818130f503d82810807280001c000 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 621099415 1250 621098165 621098173
    0x111190e06120406091b0b0d290111030408030f0702100e1c030e060708031009021309050c160516052b02060c0f0d030c02030702010e1c080f03090609210a11 69
    0x1198007015078010740b00040c00030b101049903060700e030940b0800000050b86030278442544200260346522850744000b011481504891a0a69445034145558411244d00c14010b1011032841d045151035130f1520314980d41e034605012281e8642000a400c00d40c0304048066420307100c07030440101405130050040c01c02000700802c2e01c401d030605148409600486800781c0000c82514045148200340c4240d561030501442180c00d128184000c1c003005000c00b40040c0a0104d0503c0041c2d0000141605600500d00c104060710903950311107554144004c058002c0ea00c07400c2001001d405540b02c207401d81035000c40040e031040e0401c0081c00425014454ac2c00d00843c7c60140c41c259800805000448001504d15640c08005189000c1c1e001c036103d00034400300900242480c9407007001403419201000c01e14a2141c46080815055520001e00740e000049148180c500803003042103210003130010b50780c00b4140c000a04265101051486443c11803080600e1804001041a005451041c1000010161000210303 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 621100665 1250 621099415 621099419
    0x415230909030a03150b0702150408030d090314070f020607020a210c0f082109040e0a06200703110a02060d0b0f030d05040905090111190e06120406091b 67
    0x2c1c0c6a0f030001c903c0c440881c1c105030032103a5000081900c40304540d030417042103050050780e43c00c00141e0b10008005a85118081c000896000c1c8180300030822100104000102c1c0c0f141441c000d42000d0600110700f058031010b010000128100701101000c5c00da0448000b030340c03582c141c40002d02421154111801c03c0080d5810040342189944010002c91300546051041d076a9841d505a112106c0340150b043daa00030301c1c0c902a44250b650038662020305d440c52011b09102101c0049821200d003020703041450740c07240045005004081c4260803071444d520503c100110100c141142180c801c00d078000b070411441189040110600b8481c0d403280560043c45141d50300c3c400b000da440500007900601c0d2060221400c0c000300c603e0005510900e15403140c65072800c15107440c0c5218000c00d40105014459500c07682807140240c0d080f00180182d03000b8003694866400306c0030005180407440d50200780151001c09c4020030140603501c1e050390082e8480008500d500807803601400d050003540350192101100000 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 621101915 1250 621100665 621100681
    0xb0d020c070e0708100b0702011d0121020a11060606040e0a0f06030b0402130911010e060d33050d080a0c0605040b070212180904080403080c0c0f04152309 68
    0x4d894012845481c072120040c0e11a4210b05042c880c078000240451021482e41103818000408000754400504080c0c400d0400188107942280310b6081c0700010b03942c005038244035030303800c051411301754600080280030384c0c545a40414924403840c000d000c940c1082d000002c1d1080c403e90000030704055070080c203111708c1e95640b82c4240f902c0c2d02a142244608944084141003018034461480090b0300001648100c03102c55005660000740c140e0466081401000400c0071780ca00360188001564a0b400403c3e40c000700010f0050303400208000759441158000410002903960340007042c4450b80006d580e50f51040740800680d508002c0340d20050815040130700300800c0c072154410b00c1d0b104903116000e840c480051003501d501d461164281e010321100c403805444040c0c1c00d0000149074454403a0307220516007901c94881003015040703c200a1526440381207030141c1800c005c1203000c025003094405102c00e101000c00101140750a005608640c0980c140c1c0c400740b4904140c0c44c138030903040603248042d01c0c100100 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 621103165 1250 621101915 621101927
    0x1e0a060231030303060e07120e0705180405010606090b04090203060127080c0a050a030f0609020307080f120a08130201050910030506040605090112080304020f10270b0d020c070e07 79
    0x40b0a80209151210019540072170740c0c0b82502c43c3d03500ba075030707040d00ba00b80140c0000101303070f84c03105000c80c1e2141e07810100d2651107000540012920958512441d403030203140050950740c0b00e410140c20441200801c0005440443c00d03030f81511403400300941c49990b50070040b10281c1d00d0071250362446042100500005200d103603a071050b501080c0640d28881251418801381e446244203840c2c0000e650b5400300003203004c2402d46428a40b140384085020300c2242c0001e498103a00e0780041c0031940044442a4075840b082005100c0b169a441c605400c00301110030241895900a00c1c65104580300c1554004581c4a40216500c80c800200b4060340e035402490024004d107000c8400b81e0003680380c03080c0401c21f441c1c5030030840d0403079039149000f1680707108542d1240010b81010b4000c903001800214000c0840ea0f8210030842074010595440d00003940700041c00a00c01c201584030b5501e080c0000040c4600c09045c0c0807644000c0041c07038056030712058800c880e80b4081c401e610440b1449170707403030900902643c820 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 621104415 1250 621103165 621103169
    0x140d05070201110306030309010c0c170d0f030903080f1b0f09131107030f0320030a0f0903021e0f0609070303170f0714070c060f021e0a060231 63
    0x140c003c01c1060081600c1d01c075680f0040d24039551541c01800319140a41c4a04030400386240f0805010303002c0c42c0d4900920720300044140300c070442e9800403c0b2024400d680070128801030b080ca0300d400d224075000ca0b03c01a2002c1000b800411900c030864000405140155061241c26005040c40990b52001c818a901140e00102c26142c400c07003058a05070540c102c14064030380400c5100d40550320b40686030b40e043e00d85400c2203402c0340c00d241e101d203407c4900c452090308801000d840349000c0b41c1c2d2483c1941c01101151036030b41b0466030706c1cac1c900380003100441e138002201c0380540151600400060421802d41d8a400e00403d8048403611911081003407040012543c2011a0700c00c0c0c5a014148400b0b038109501a07000300d551840c1e1a10640001d10301038861210340245441400c186450910591030340040d010050300071030003041048bd04148017070350401044403a0040782d84505484142c9412164582c0b07284a4003500e242e07008680d6005241d171070f400740e00c80a14040015528806201e2050210080034 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 621105665 1250 621104415 621104417
    0x702012102041a0c030a0302031012050318060711010e0402070f0f0b0106020604030e01050a0314040b01180c0206042003071707140609210d05070b0709050d080a140d0507 75
    0x2a42824181140c000d131221456950003031400e1449204044001350801400704110b03030400000081c5506040d090461b200340100099a071300c83d00014030604050303144891601649040000c41d004c82ca100c1c02c0511903442c01d107040c8004420010000e006401403940c00b50030304111500c020204004042005c10f400c2c40385040c401790341c0e81d0b40c005a80b030710812903025000c1a070380910301d4010b40c41107005200042141c28002140b030317429038501c84500000c6404890240c0c0303100040c081e1054101803d40060030102d801c0c072052040c1c0000a442c0c0d40d000c3c10081810340c0c07140c81c044055202c02c0c0d090600c824003074112080d00c0e070780f801000304042c8007030b40c403e01d00e0186990101d22030318040c0500c80801006061946001c0e490400d015070b0301c0041501c000300304100c80d10a0001042440312200034403603a683d0315100c0c441800c041c030421030040c2408050102c0e0320707810050b64a6402c110541160011000c603200c0c8003400d000e0b202040c1c151502c0d0711807440084c0d50703140000035601c411701807107007 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 621106915 1250 621105665 621105689
    0x903090b0f07051b010512100b0a0e030105010504020f0d05040c0503010c050414010507110f011416050c09060321070204060303050d140c0d02180a080f0f01110f070201210204 77
    0x1e8a0b601c0c00c244c403500d4200900190702045100c400e001c12010544e0411081d481070847d140e40c80c1070340c1c0941d400520107800010340f00348400c00701d403400b4050240900403c9038111b00e0221084140c10492040445a80a03d625480010700b400110808840207060140007402580340034180285070307602c02d0081c2c520003080004c1c4018a5403041c8140c81841d58007000b6240408900c0f0300b000110350b160f0100070b0404c40f1034007555206120100c0900200c0c991240700f00d00050315450201d00749008041c1d081e001d01c050608010761a80d001820706000007109080040c03c649000310f1910501c6842c1d4041d4009050050010406600100400642e200180d00700408060301c00749501c11242130302c5c948a000014003040b1081d5145600800007000d40802200120300120045500c0070181d90240300c0c290403100e00000c900c0300030320203014400030050003000103201030741e103011a500566840f4000445c0209400003164000e03c08503405403040c0c054000d613030300c0c070030440000b0b03512901a901e00504 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 621108165 1250 621106915 621106933
    0x72c0d0c0b07291506070204060f0609090207050606010c1a0c180609030a0b130f0b180303010f0b2b09120e130f090b0c0304030924030903090b0f0705 66
    0x6a0420f0714000c1401c0804100b1507074440356084034040d12101407940e80004100461001640c3d140310307203001000780404160000b442c0c04005044000207074006c0c080c01d801002401c0c0040c4010864a50140003420324901d03402c0c1d5402c2c0079188000796060284906030340030a200324030f00340b000500b02e403c9000005d49d2080250340e05000e07850140303038050798040e44540d00c2c0c4000601040721466000c66241400ca44402180c0ca074941c1c400307a00481914661100000d2000c1800f00500861000304104015480d5500d0b114562034043d42c40d100d00e02c02d101d0041b0b10140c0045204108500000b00c140b82d98196405c9801c02400401101100310750301c6400d0454403000e0f50080200c03a440e07143c000c011840300c510440c00040035000d040401d02c174180c4d0f81e2504a00080101800700e01540460f05490745a1400340f80203800c40d000303038009248001c0e0034280c1c12401c110004030840010b13001d160100388001540380540c3c400e500ca40003106a1a4041050008010134502401c40c590080e811a07072448 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 621109415 1250 621108165 621108203
    0x5010e060a03080d05060f1509091e220b01080615010f0f08180d02031c09020f010f030b10051c14040b040c12110108072c0d0c0b07 58
    0x80c1d4a101c0100745000922900d0400b5545601450340180042d1403001210305006c0011580441c4503038500c0301e00e10100b0b941c034243c100035141030b07800394008031102008418024030f030b02d203820010a41442c050050081c40018540045000c000c00c0d845220100103503118201d072502c400c011254000a11451080f03008150301c20b1208550044041c1c4950040040c6480d0460700000300811281100c03250400d00c00c0700c450200304116074800c0a9000e0f5807600c03074015070040d440c603200c50341040032401d06101c4030160781c8004241c4524942420006060010145c0903000780020b902202d0b07011610400052215401034000c2c409000c024044140c0c2c003005841e44030803220103a002510a050440000d00055001c905540d001402403502c0744100c1d60342d151407510b00c7e0030007030201d810303501c89108a20706503045840d91360080221304060941d04500a4071851020b8038146001070000100c085401c641c8071000320140c00340d0030608289030f41d919084000da00360310001e400c4a141c0000750384803183e5 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 621110665 1250 621109415 621109429
    0xe010221100b041505040308040303202d012a0f0813110a0f06030605151e0901170a06060f020a0c05061e0309070503010515090a0e0309030a0605010e06 67
    0x29a0004032914105801c200c41880c45944c41450b103000e00000304004408038040402800007540b00e80e540300140209000746110050032898140050780c02003601c008084d21048050800c603040c3c090207c425158120b0841c0580081c1c15070032980003110809540f000c60f00030261b08112075a850b03220064040d42400c4400c020210744c030083c10301900c80b421000403014900d02440f0b0300000e20600f0220b480e6845150007803245d81c0300d580800e40d6500c04100ca81441c401c1c410b000a504001c0600700a5146440408206c0010000403910400210348545038040c0305030040d9400e00320810785242c54140c1d0b50500414242c000e40340429455240007810740d00c0000c0d04a0015400382d2a000c07658902818001550003400300318008418100802a00901810255200da8102d0004207102c62410003490300b105d2000c0c101499114014268540744c2d03d9506502341c0064425000040740e034405c900e91800c50007000725265041c0030f010310060901005801031410b99181e2500a01c00b81c45840c104030407 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 621111915 1250 621110665 621110669
    0x1c0e0d2f0103052202090702070e0702010b1e060702041d0d030b03010b030a0314030a11221520070302040e06160f08011401090306020c0a060f050c040302130e01022110 74
    0x307100d1300b610303400c0d00501341303080d1140d006003903401216100303034640c3c000c008489030455110005070f540d540c00c03a0003860701c07000064000718074140006040c0d6090340422954803801101034004c42c0c544001c529954410391405d643c01501c3c02c00d4810304584400e00034080d00403034031814407039801c1404a40780c034a00414813030401c99042d1650800c5131100319801e034403500700910070701ca080e03520101445001d010400a002440c1d400700059210605100d90501d030840b00d1300480035614a8010143c499504600c0600c1801e081755100394441204c070b41680d10b000e510b500f000390441d080c0500340261101c00038080d8020944030002807501d0350f0303c66045480b8040c2039100710004c0c819900411911014107854181210189440460036460344c89001c02d9910041510809900942406061114900c11100c503200790301c1080c401c038200781c0c040d002c55016900020348910f07044848000f1180303541c0d00407180120840c00070f5440300400c4c09040031410500c07014800302700d003038000100c0f802ca0082103002 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 621113165 1250 621111915 621111961
    0x7020109020901051e010c08040306112d09010e060405041802090f130b0402181006030e010b0609190e0a021801030e0a03180b0d0501081c0e0d2f010305 67
    0x190385c1e030f5039004480c11170f103084042e01c01d10340420011022407060702502c1d050840480d55a40d0f03503801403010100207204154907041e109120000c884010300924103d6108503030034a01520300d5540c8400044552049901a560051500c900c2c0ca14501410b40485510740c02290080c846507280700c0b9010710800d00f1070300030400d000e0003903901001030854400c0e03541140c00640304130801000c60051034614041500c00005043c5100000c00001d03906000d4003003000c21090003804030840540105149001d0b400c4894031610b8a01411244248082111802070010035402801401e18201c1e00c17000703600004a034401c05034980480c5580b54080d002b80035401100700010600c0150740e882c21540c0001d450441d81c1150548032000444801b840041d1034042d1b20f0040001d03003545000043c51801c6640000048a1140c03c030481d40040d401c602c2142140c242510340503248045c43c42d01e520459401c141c1642d041d000515101082c030485410b903007143c1c3d02a201001651610351003484800e0506403420 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 621114415 1250 621113165 621113209
    0x230102030a0e0415121b0f0513090302150703020a12060b1602030c100305060307050906100305100f1401080f1303110114040b04030f0c110d0302150702010902090105 73
    0x400f41860391211404403500680504441d48804014007202c0c0c0000e8107890041c03109440001c00103038003030100b00610f810300d00007074028980004141403010310340013000200e54501003c000c1c0360003071103080c1c0d00c210b50b47c90142852401c00c0000d00250003401100000802801c10000f2484440c030039a4140c441500415050000c1c4411009802401c240100c0c2c01d800349030311410490f1a500d0f4030604451403034501090501d090002d140c5040d0850344654859000d00c01401096100c0000d0b110981510b40340c0401e160350350000e04808a5800d520948440c903c0c8080040e82e03412080014102000036a503400c4592204403010071403000544045000e020b10031500c4000134007a150403091090010004191401460b4a519003070300c0807942940c0b11070403441000101039000041054602e118100740460181c0754841e6480e1401516196010f8502d0000300d005041c000c01c1940d100300021400d200040c41d004100070b000c5d1480c0c582c00c07070040c1c2c0208004103840ca07002c2407031020301e04207840103 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 621115665 1250 621114415 621114437
    0xa08040e0f070c080a1e110609010b150d0b0a03150c020706120b22052d0f1801050702030d0609020f030604021b01020f041511071a040906230102030a 66
    0x55504c542c040c2c88080e003442819041608840c01d40d019500b8203244503181c80358440e646000ca1403e1130301c003c10003034060740351140c41d02040d40d500108040340882d003048161030300c6100b1403240040c80c0e16008698003107081d00c800001c11901010700c0190080d11103062040301c0b540e40c1c00341c0e40c8154074041c040100d1240070000940c0510380d0710111800d6002801c41e110151085c081034002c580641d101d03210326407500b0801c01c2004407055401c40c0130013020f40424982860402c181c1204c8400340c50803100d000004089903084240220800a005680340200010b00f004c1501a549512a4042281035410601c0c00500c400c441c1c400e8424007813894a1040c50b554580302044000c1d070185080400b13020008040415048091029140140a50020950320f50804100d0f542405080c03403100f080100c02000b024100c8808240f40b01107545044018905030030074486141d050046400242d00c40d4503201c1c00068022108841c801e444485980301170354859103030012a142d20401c980310010442e4070420f = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 621116915 1250 621115665 621115673
    0x1b3901020601171029030303010303050301090c0c1202010c080903040315020a11070806010302010206060d15052707030c1a03070f0903140102070312180b090c030a08040e0f070c 78
    0x3c551601445030309640c1305041c80441e02c421641413003804000e04854502465100301401d043e5280e2074003c0300250f065603d103a42c0200340c1d1005009010b81c1c0d984611142c56070324010110007842d01d40c801080390847c424240024000d1215100540014050030045038000c007012003108d0541e500311070381d60b100680c00d1075548081d46c410080541001405400094441c409108900181c503007140901481c0d45540002481d040001e041c01c0c1c400c207014946100014001718010745010b400d004041029036401189000c021200745c02200340001c4050b0311402c0041c049854000e507072141591484481d2111600910042d1440c141c183c0c800081001ca80f22501a2030340c4200703070200d4030b4500d05030f6490340e5626107130010f2040600a140c3d0003042e48802c05411000c00d0070f150010040c1049491035400f07201401000640c0094003180340301c00440e015400038082001580c1002d82110703e42426440c01c601540c2c020320400f40352022002c0413840205103105264060612a60741c00450031031621 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 621118165 1250 621116915 621116939
    0x120209070305011a1e0c1e011b110c090901020d0f0221150303040f061e05030a09030302040f0e06210c010509131b02010b0f0a03081b3901020601 64
    0x25200101050440c1042015a1204c010100407100c50090100c030800daa111036019000903810001f10b90600050400800300060910059405460040701d0501e0101c0301c142002c0700e0300c1c4040d8000480208000c460001500186990702c0600b108001c898070381c4403244100e000701081240f46007440701017001a038200c004072903041164044010120012170707000910351390007903200c0c0700307a5031683c0410020580c2103160703050640920a011040360b0440200285184001000040c42c01c6c3c0d268160014148a0b81c1501c0184c0724840a103000c03952a410318103001d0720200c0f00e03984a6100019000c05c004918101010400300d00ba000784401c0e5a41d900544030340d08500c40c000c0d0001c80082030300c5d0041e88540141112010045580100031807910b000900356038030072905501400810303040200e03582350b95200e40c0489400a400c01d484110604000100d607841d00707000d00c40b0340b044034103e488840d000020074510707915458081028092001d820001c0c590b0300b1803102d0160300918010800000140 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 621119415 1250 621118165 621118177
    0x8100603171b01020a120b060a0906080c0405030304031b230607061e090506130b130309032013050c031b0c0f0f0d020f0604030c020109030804120209070305011a 71
    0x20720320b6180d00c0180e0781124226003004140c04001010b00a005842c5401031007076001100f01a200c1c2c514016070440d0250041c40c440c1306001c100008000001d50682c4c4d85000d90b400b400004059955559481c14101c1062681e030003040c81410449a0008d8444000202d00d9916a8000800d1040501c410704012203500701840a4038095112401d050a00040000b00303100c14031603220015140380e43e400c0461800c00010204054507040e0408880820002858103500c0784214180c80700d40700b00c3c0e140845450401d9400142042071008104100a0314809034031515141640c00c54415085d04404900741c600a48a41cdc054003c20030125660054010401d4250b243c001d4615190005003142c00c0d1070021803118a0000760400071031a64003035010f0010110a40d810b200619480c45060401611800b02800040c2400752500d400b50840e40941e0304d1900850b00484540d4a4503501d40044501c1c8681d400308900c1080c41340e0014420501034841e2034165200c490264010f00244c03000e980a0358842 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 621120665 1250 621119415 621119437
    0x204080a030e0120010515060c0a0623010308041e030804030803040f05071716061e1e0f0e030615010e03070e1f06020d020a0201081e010f0810060317 66
    0x2d801c2082890300031141340354442446200001d210b00c0c0442228a02c0c40032680007a20440c000c210440d00c0102c0003505030340050300320100041b040d01d807400040c502e0f1039802101c042c041c03c8000010a00091002130400c0383c01844007010100400c00004514030310718040100000400d11041c030100c0c5180c000341d5402031244510f5210b0003030a413503070b80c60034220743d102c0c1c1e90040300d80311078a03c0c3d403000340452022101035030030003003102c0d082500c068140c00c89030700300030301260100e49220350081c4222480f0041003102a54420f100c128072000502005070b151070040861000c2081c004242000141c1510030942c141c04c210b00c0340e419134011105400c00c18a40c65041c8604040841c0550703000380224012101700340600c502e5102d000303242048400542c80314042d50041d42002c10400e130040b03508448907909180014090341c60303420107084c284900c1050380404c50440008501500110b004400b0b4034442800c6035942800c0502d51400d64178203010041c9400060450040840200005406441c00c8 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 621121915 1250 621120665 621120677
    0xb120c0c0309030724110c010e190801050412020f0d0e010306030204050a090c080a170318010c120609182010091505190c1110050408060a0204080a030e01 68
    0x12500002c0e10308a0075170032500c0e80d4108a0980580c0f1043c4882c1d0002000c5242003203d011003c0c92172084c1c440c0300144565043c498203812045465941c00b0113038800b8070b00c20440c2c000e071544038800a4001c1074116012200301080c05010035030036000040c6a4030381c01d0110010981400420000c81d0f1f6034084407049814036464480c0480165540d01502c0d1044101200000d11000350b800d209494261036844030b6220b810042c95040803c402e04038205640702c200b80341560700c2d1100201501c0e400c1c1e00c0740102c00d8551074000311116566219809a00100080d14207208140e22025000101c4000d5400c8116941d6a85542000074050010701c28584c040041d041c000346000c0804520074240340e4103003d0008410070f1080c0024404449060403400d124a00700341050942201c023002481c400000c0c6045c41000c188500401400c81c0440120280242410174010000000503105801a00554180b40180000101504621300c00c0d10308803007002004001a43c05501c0c15600035401d418803604100d2 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 621123165 1250 621121915 621121927
    0x60b010908030a0503061e100e180a09050105061207051c0c06111903080c0c0a0c060215012115020d0c0e030f0a080d0c110f0307020a0b120c0c03 64
    0x140520141081c0f0310162074042c3d880c0340000c00c01141d010444040480c4600350340003031000b5204d030070004020001d181070003241440000002020786915603144070408400d0410480e0b009800c1d04622034691292000340a240c50b440104690030710a50180100c55100e403008000d189807034654a140e118001d03601c2c0c00743c1c214a894030401c03403065401900200708403040740b04101c2d00c10010b1342818026481e544a038184640d03001001c0c40000f4010603404000802c860514510500a600e580c40d885840d54034019626100a0b40b14443e0b020230302d24120b664000000e84e20f11400c0e07605c04034602106201284015903943d07170a40c4049080300e070242030342400030300c013000304510480d2180c4406803110050b02c19400101494503400107414410360b008900502c00107660101543c0840c04404008204440203010466920001ca1842d01c921f1089100e9400440c20100080c003800c1c0c000d072055280070b0385a411141e80b07881003040340d02008030704100003440c40c0402005841603420400a4a113404 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 621124415 1250 621123165 621123179
    0xa060c4d030703080f070206010b040b030403030e0706030b01031a0d03050a02031b16230f041e050103050118080a030c110a0b0106020c0f031009080403080304050604030f0c050604060b0109 83
    0x42c200b10b500f01c0c04070b44428140b080c0b0020542d07031907038409044c1c0300508481d0704000c249181405035100e1441c3c4501c0100124003054040e800c4004030002860889034499941e50008000d010320340d04090100385090340c40782e25400710000c45d0500000c0a8100644110f4980c0c084410b40d01c00080b000840c0014402c01040c100042c82c081c1c9144034150041904031949804220081480c0d4041d0809610031300c0415400341c0a10f40d80404190100c42001c01701c0012000b1030040c081c0500d0010b03501c551408000c03907400c4103910081c11380e03004100070040342c2e0158440d00700641600c030001d4441c00c02480681919482608400780268191130700c4040c02d50159401071034420664011280c1244102c01400000e504104080310860101c03a050845083e0401094664201008a034401c5840749648000d02c1800000c450041d98020750706580c0c0c1c81e090410f01d444010030396040f8000741240000310315481c402c1d000c0280701e50f04800900712070740715996003600800071000c5040c18414103a200185030 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 621125665 1250 621124415 621124417
    0x40302060304031e0302030906040f1401021216020129041b0302030a240e04111507050708065103060f0c1b030c0a060c4d03 55
    0x1443c03182e291508201d108a505504440804104008040c814070811071a140c1c0003d400e900075810212260045480d41000b010348a00c50740c02030b01541c000904e40c076581465140584c801c2409462110902d000324200300c2c281c910b0740384000e40419404820035513150040881c0c844a400040c0300003120299001e00030314046a000300e400100e940072040000c18102da02541300740d888030086c4000302e022407240c000800291802040e81c5e075503940740014100410000c03051000e0000400b501c11104103600d40d80340e41d80c800d481c212a14052400b00250440c0002155800380162100c1e68111402940c007180001c00d180420403240c0c100b01a01c0e903115803059038000960074117201440d44000c58030050504e4130701c0c0034100c40ca810b101d903000c102408140c1c03c2038624001d210000c0030030201070404058910b0165680ca00304502030302400100b040920740c030450b8070201f0740d1286501560b1303074181254100082c5500915a02c0e180781c2002d03a502d1100640c03052240220034281c00d07005046841d03455 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 621126915 1250 621125665 621125671
    0xf04062a08073021090506190c080c0d180b0907050603240a0f06030c11010e122109010c021c090519050409110109060302120f0403050403020603 64
    0x140200015540060081403c0d00d0304190301d18801d0040352106181280b582044048100700030080b0780b03144404506101150215101c4012000b407100c40c0c010b04149458000544400e250f8069102c2490142d070100e0045a0380462983c540600c0da80d20050355020980c0030109141d01195500e1406078000303882c461000706140513210603222031400d240100d00d4a2003542015203e040c00380300f04200d03800700d00e00184500b01c6185a1030f0000310300d0804608505420b03000094003555132040411003c0d0325603c620f00d02d200507170b0b4883c001d120307484555080782c048882c0041540c102c50300c5030346040c00c610000c14000c0d60540b4850185545c2d5001414012410389211146945400590366142d0341080110b00030010011508000c980840010f0b00e070700712910230345000d55484d9849201c540c0c80030583c074004001c0540280300c001008e00d410b0700110198100386011a07100720001c25814464400d031000f20303100c0c4c01540c2481c0c49400c08904840d01c0100304504000d0200804001030310740b5009580 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 621128165 1250 621126915 621126923
    0x1b0b0414031b010608010b210313091a1e1002100e0c0f01020c0a031401090212060403110601060f050f040302181b0313021e120f10020f04062a 63
    0x181910342c008116080d546250301c065240da04111110045550740c4100c1c818103084034244084125030000907078114000c00d08000d040c4010380c040018030840700d070050905401071640c0303060000341880c1008072020301078403155502240001ca02419041007aa89440c072082170040300c1c050240e80c0310328801e840a0b20b4460303100e0381042d90310b07507050b05009840b82c0480c0b10900141911410b450041980722000c0d10003e42a040c3c83c1d104840c00308020f42c050f13030360240c000c0c000c4c69406243c07004095403104c06a60403000200b4030700b41040b14260205140c1d05070f680039501d00380d4000140b50100e403d6000f4100001103240c0411000005a690000b040d458841c61080003001c0d1030805803024000c03003000b1102e14991410000c001108907060240b0101c65070480701d0405001481034071304142007005103045e4011081e40804100f61030000b502c1214510100111203c1040142c154001da0242e00860854031f0401d2100340001409003804036000d031b01650f240c1c503418010342000b2a0000d0720b400180c03 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 621129415 1250 621128165 621128197
    0x20f09090a23060c0a050c010903050702130603081606140930070201120b090c040812070203030d09050f0115090c030e060609070309150e0c011b0b041403 68
    0x4000070303450000a01c0c0e082c0120400b000024503800e5444803c024403082003941c00090301100e0354024400e651441020350020000c1212601e006481780c0d0003108140d21a03900d0041e5208024994060442966800318125051032002541020382c94052001202c441d038071154240300f400125250030b442940744000808003007254440d001c5010540188005154800e1101c100c14903001000700c0d801c0a42c28603003000030306103180c5213a004042c407034103c5600c561201c060040820041c0050025550000244c909220304242c1041562081c644000e4068105010380d81000907141c1c0090450740c0142c00369450981407036602801c50b1200b0000071186018001c061203000d040c2d120b240c1441506007030070000e00722140c41d20ba58854004050034071420340040011000d43c42a0060310080d0f5008500740ea41d0348410703a890006d0401880d10391028450008071103c25031240c46160760003d285003000249000390b4a0341c003400400140143c0ba5102c410080940f494000c2004160400202203c5 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 621130665 1250 621129415 621129433
    0x40209030304090912080f0f060603041509060b040e0106060e060a03020c0a06090317071d030708070f140603040b010b0d021b0d080a0e0c060304020d05030a020d031422020f0909 78
    0x2800300c000c050300c0710520747d030071804200117400700c00e4880fa084102200e400341c0360f0b45d4910340010154440c40c1c48580460400c1c01d003208000d4a504902400c0780c0486060251060300030a00d401c8400341d00c10340001601c117a80240650404500404c0d542a03540303005803400122522081c076094420400b21410340d6a50090410300d41c0c005060f0300d1081120204084034203001c2030003044000b2940755050405003503102c01c240f45d6000c114031002801a00c0689400550341d8240760f80c074141e18414407401d854100090a52072614030100c92186600c101f800302d0036402d003000c0d205140c000c448900890341d803c00c01c1c07425207546c04003840741d1160322000074068288607001c01810b010010f00f03000c00050a060b0805991000800c05403c82c0700107954203600e1340d039140000707644442c840300b002d0042c5c00000303000040d4903808a401c1840e02a1a14180140250400418038000080f60f1110722000c0040d6000c1009240341840103c4600042019500c4030b032080028040090585003481554001c1e150 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 621131915 1250 621130665 621130667
    0x209071d030d0804080a02072105011103040c061b06021201140d050304380325020a030c03030902030607050c0f010b1807120c090306060b07030e040209030304090912 73
    0xd8106102080d40605401e00340b0348005010818040d0006003414030104244240b10310801000005088032075502203040c20b070b854400700010911805540c075500b400100c0d54644004012a4095079001e03c13401d201600d00b0b402203c43c0b54908441c499241c0340c07200c25802042280c00903210490010f00090000d500d000c103144007003540e07200518000e005141c42c400c007003000401928100c03280812681d511128145071181c2c0c13002c0c20003443e18034060f445036007405815450043d5116824010201d03810500e03007441669110b66141c20080107a000314010000a8498a59171581511901340401d16920640c00241040021592180028004031302020040001c00450f1800c0c40100020802861608049481c03032004804034165444004042200315200320203c1541f150080c0c4208041c03404400d00500801c0f0742d1106680442c1001d4001c1094161081140d82c402d41c551200c02446a810083c88080d400136910705074180130034000000c40c1c43c101e00407140c01c684110704280c900c4403a800 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 621133165 1250 621131915 621131957
    0x191a090a0e070c06020f09030a050f1219052a0c010306060903051b150705070e0a05010b2a0f060a050f13060515100f12110d0207050a020907 62
    0x721065841c1c9805050198070341d08121142182c0b600b011016981d43c080c55040c3c5001c0c4209400c50760140300350071005080c40300108941915102510540325486160b50a003806030107000240603ca945a2880b444100d0040e00200b65000c0a506400010008200c1504601c2c40450f44a1000e410240340c80b4503a6034103108100c00381000c2d0500d07600003030654884079680e0245003042c050300403403040f1200d016600c02c59460140c2102c08807455440b000c43c68480d444008520401c4c1544401c00085820807125000781c905841420042c28180f00c266a60a420801c940342d0303203c4008500900d0420520007440041e80d5030312010000c14450914101b118229107008001c00110034904090050540801c10700300c03007250b00201d0100b11034940e194031041b069200240250b104401542c4022055003043e0016001034a54807881c1415482d11000815500c018507181104a810003c04e0446401036010f0940d1b680100102e41908003141c1c0850b140c6541980c03100301041007401400b0400b40310003 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 621134415 1250 621133165 621133169
    0x1110f0a080703021c0209030a061b0809060606031f0504110919060c02060d0e030a0908150708070c0c0305030c07240c060f0b09011410110606191a090a 67
    0x100d0f0451503d80480d20195528800f04844103107980c000881400d559410441c040d903444d00a2410004d21004e0307001035400c1c0700e01c01c03240004160315200144d4014000310703c40c1d11860780601941d1455444400c0c41400011130a403c405585220f1808206038450b4400e1000c034550303907481140d503805207804010840344032b4000e0b00b00e01c0c00100801d000c7c031644401544059541610507a8480521000820181c0725603140c03060a031001081c0181e40750740c0200d41000b00d0302c00300c064602c2c114410582c40001c030801c60b100000b2900010104032400d215213821844140110611106241c480e6600c030b0650344001c500402e00c0d4410b620910603000400880034074548000e50b88a180d60403000041c0c9030b40c117608406480603903242440c40d00320f103072a04003020f2101c1c000c01091483d82c450b10120182d90340303d40349030700440d8501c1c56005000d02528405503240440d071f00408035603540404020b0700b1560103004041040f10000300203100256055030000703910b41d903404252110100c1d018005517840e16 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 621135665 1250 621134415 621134417
    0x20240408010614300a12030c08060d031b0b131e0302060c0d06120c24020c2106040809010215190e031e09031204180e01110f0a0807 58
    0x400081c030640d0f50f60f107001400007013600800380d4540260f05800c3c2c600341da850003507802c4c01000b12000801504012800d051302c2140c40812010030444c0703044500b01c03811600280c000e201005c000f0040b90084101490548424000000c0004c80355220010700c8002e4800c2ca1405040d20101c004024641c1d0240081c3c242c5818184070003481910000d6032000040c0c0a1150081b0000d4020050200ca070012005059900300c0400440424034000701d88004c00d21419890f0045003d5081042a400c4d002019100307041d4000c100302da4803c2c0401c44d10003802c3da01629454002031110f6941a0140101840350303001c0c00401361100061000a410800c811034007846200e214020001107201d8101420181118820001242400b0801d400c2c518460103c00340f08001140800c1461490000020414548241c0561341740c42d0b030f82200c0c43d0050007903008800c240000d240702d1489006242d8041d06440c030951001203154442c0b80c0a1801952290617202c00d0941d0016404030700b15085902d080d00200c2c1 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 621136915 1250 621135665 621135689
    0x11030f04140a08030c07170a060603080c060601050a020703020f120a2006042709171308061506030a02091522080c01140d0f060611010207202404080106 67
    0x71701100d070740c46070150b0088280c0d240302101340c0b8590142c1080228015070b4000e0080100030380340d0a0030740e150b800029103000369200300310000700654400e0054801e00300303064005018081c216800c016290400703902c0d4580007000c2810011181b001049202107d601421001c0c07418003c2030004d40c0b1904e10b40001d6405550100010403503000304181d05030056880e641100740105103410700b040900340605002d040356450180100c03000070360000404c015030b00b20701340c900d07050303514404580c40d03c90031100c1c00d681100c1d0503880511424068010340e0300100c040d00052501c0903800c0001d1010802c80c9242640c80004075404000c402c80c601108014052183d00100c0b45150110581d902d0111958160400840d500102d0386050fa000580700c80301c26001c4c00340009644541d0001c0104850f220f4000050101305810f500f142e4188221021240c00c013008040485082d51903000034039410360a42d07080025403d40c9190032520b1100200034800c40800c040d510340c580411503003510342c2504454032002b0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 621138165 1250 621136915 621136927
    0xc10090308190b10050306011107080f1525021606080615071203111303080c0d05040e0a180b04060914010b010e0d11030601031a070507030f11030f04140a0803 70
    0x940c2c4101804c60030342d6803501c0d40c2e40c0e50700c81c4012100c040009090070f140d4428100d0110310880041030344404080018111a05900c085206000304642550f0340c03401c41c40c15400d103c0300c5c036000e0486e800550313140c0e00480d0040d0b1117101140040b00070540c00600015011400c4c031505140c240d070400c0d90904d503c0341c8030341002c00c16215000e02048044c01c1000345580e5400452070066000d0035100301d95001606001c03181d03503c3c01c1032410755205103034000141c00351520104c100340c000c900381e07801c1e01c440110384016580c079803045100800039112105036034034105580000040d0900050791040f48213810108464102c3d2038003064841c199608070310a6410052411003d99000d904d0301d00380041225091441821402c011100e0020358441e10f4241c01003c002006209285030192480d586000c4200b40ca135844007811181402003200080028030ba403001810202d00c5401c1e444680402c860a503494181501d01184803980140d01040c05c1007580007500702c06262000c0c1410050003030001039407403c0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 621139415 1250 621138165 621138169
    0x10b0105040e06010f030b061201030512040f06140706020a0c050114060303180d021c030e0d0206040902030a0e1603020f15070803090708010c030501091508120c10090308190b 77
    0x142c00521250411441d54503c0304164440e401c9502c0040c0c0107451700755614062154001c0340c84c401d0200307a42c103104102080e050300d403202d411a801c554814030b03840101c5050880880e144654031080e07911a090500c0880007103040791004004100c02501c80861504040c50141d09441480500d544203200d603004100c01900c0200894664010b408440c1e81400e4084000802c0c4103240309029402c0003118074542c00111864030745400c0680aa145c01e9481060402080800104024000e4010909010410019406401640d0050310310301021502c058004040d500d04000c00c84203176148041440f00300103508103c03442c46c150394001c1d65203201d00001c4c0c45100d400c51180072001040f0200000008000000901c515030241030540001d20106c030078001c1c01000342c0005e00514940718500810000d10310074500050048a85035409000c0d14024a140e04103542c006d01c80004444c00707140040f000030b0f5514482c1042c0180729880d004843d04003041c0a40304001c0745801001c255140401c502c98503 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 621140665 1250 621139415 621139439
    0x50310061401030b210303180a030e0913020306090303060a0801050606030c090a0801060e0114030c150a1b05070e010e040807020f0a090e01090b0c1612020309090a0608010b010504 79
    0x1d00003800d012544c5003010300491110118000c00c10090700700720344070140c1840040b0045000d0300d0001640c410a0203125111031321080c2951009012903000354043d14241040399109074402c0503458031285905568010a040440484024900c0e800003c2044a02e01d825140c00001c2c00090380204464500100030421511010306081440030001ca0341c0303d40e960b20140c41401529241000381304080c3c5c0c80b9110541e200081c05804102a811400240e442c200021015a601b00080145030360078041c4039844459440b0142400800051580518100c1002c1d0a5000c66074405c80041288a1034030701074150491040c2c20007182c034401d4900f4172011620100503540c2342a01154085d0101c5070480001d60112440c0e0300c110710719130034500250342c80c84065000c01d14050048682540c00e0780c421807403824a1041c80460141d4540000034070000c10010700c00b0242c6c011450044174070b800d00784800961008412110040c40548a00050115000038011031040c42c1c000c1c03c245041500300240d10301c40d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 621141915 1250 621140665 621140699
    0x20a0b13031b051c080c07060c020a0b0a0e0f0604050a180608011401090e15130b0a020901120906020403020405090a060e0d050d0507021e01091a040209060d0f0b01090605031006 78
    0x44240342d030310880140b0040c0403c44917100031010454400b01d5235400003420480100f0303400c1e44641c1141400003000c25001046491109442e5135078500c41d0114010001492441c0c88100e03000202844082895200c9004141c0582a140c1c01d003012100841c0052090b1592034014641b140d061000a54a901a840110781900d51800d00455640d100c80e00f450f1800d10f102d105440d00ca205501401018131048922800c040c0c0120080310107a50794071103403010f0b84200341220380014900e0000300210302c110703400b10401c00e00c90800035103060782d2600040c0540707070180c1d0b400000f40c100000e00c500300500e61007104116003800c006825402c0013500040c050f80221a8164010343d102e074001500140f00380139461601140c100503007028981156058020003540008454400d0201025552486804041403050380d00900e8024240d07201d41c20f1244c0c285d90000d00721b5210076100314110000c0d10b420181400b800e040840083c3c510b151000705860200d2070000503102c6481c01c4014401c4803909281820 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 621143165 1250 621141915 621141949
    0x915060507031d09250905090a090314031503060f13020d03110a030f032d0903090f0306051915090b0613090204050f011119020a0b13031b05 62
    0x10800c10b412048034811040c002860b40034145004001800c01d1100034103070f0020701721690030140321030714a00341c03546050380c0102d9501c100f2240004540d45102d4008011a80c4a464180407045020b800e452043d04169012003416083c034009066900741080169800b64420345120310504010030030100d9070000d2003001e405000b800b00c211062501444407080340611003c101c880d41c003540e05000b4400c00d06a030214001034107000680034000220006840a80c00b0050341c0c010000302854950300400341564100d0901c4914140041c114203100b030a0001980a8072000c6050300d403c3e601c520302c1069940d501e42071545040008009058190081400c1c2c0e0521100080c80a03c0c0d00f0024055004003000d030074407180c40c0d6a0200d41c21055030040c0003100c006544141c01907280130015908101903c80280c025809000f0400e038154010255022840c0043c00c0801401e40f5001b04c0442a0b110700f424140e0b4045604003042000900c03403110300c10100f8584607952650800e00051401480b1040d594 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 621144415 1250 621143165 621143177
    0x10e01180b060a0c0204060501091d09011d0106211112120c0a12080103050a170f16020f0109050a05041a0603040b1506070b1305010b1207091506050703 67
    0x1801500540e8001d00100740c00030400d5844124402c3c00405040c48400700701d01990030400b0018555015003e0141603840c45484000e520541c400c00401c41e45000300065080d40d00c8880d83c040c110b1034082115030141c0c13048000b04181d0b0602e86003206003610b00b2611a91218104481400f0442a50295448035001c9031225800c245c00b1901d2450024a50f5207084030a00016841c400500001400088c0504ca10540528a0a80340c020303911000309210140443d00000740c6040016003809040c01c0da115130784c500c1d07820640740210300c1105800c841764200d000c6032a00300000652411003030107545c04d00c00340390600314141428007180031101180305880c0a252103150a076059510001880380b0707135201500c510348030b00c0e041c01d0107044007030f050740d105204400c40440401241000d004844040e6044170291045445d00e041b1003c440d45004415203a6542e564108a04d03551040c29902080700d000f0010103c160820f603100c0100c400860501803007091001003044a1500003042e00d02842e0542028 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 621145665 1250 621144415 621144449
    0x911031018060503030a0903020423070c05151e15210309040f1d0a08030112080c070902041703120a110f0309030d0b0f0306040b0c0d05011418010e01 66
    0x78041c211a810060b894040030801708581a0700445e01d1003200d00807902888401c42803205800d444030f800040b5080449144001070000740540040842148100101c40c400400110b1007a0b400c10f0070744800003580c095002c110300d11000203c3c05a00308204001203207034070104000182d00e01c40101c0c864030040c1c030b00c030b43e80b015030b0740d01402528180d20740500203010040e00f451b00600142105407030807a50345a501807a0300c84d41d90004805020f0340e8000c4120b4516402c195003102c140800d4a4115400d040070801c80c404880140911801080702ca40701603292030403c1c80d00e03222124580a0031800e5031045c01401d401c003040c512056001079420342c1c0010f904043c901600414481c468581840c003200006101074030500000500101c20b4000040040170101420884100920804aa8941d001c1408a40841c00c0413604940000b40c2c903032090719000380414120305688007603000c3c13007414900000314030042c1020449018a0107241112403415030401e240c2e081031201c18000c00789001c90506039 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 621146915 1250 621145665 621145709
    0xd0e06060d0b0a0f05040515010b0f0d2a0c03020606031501031209030f0b010e0f011d07030f060617010501030c0207060507110d12030b03030f04030303020c1006060909110310 77
    0x3081c6203598100e11305011a10f0716040c5135584040591800e0351100d0440000203600110a0039100d0701d503a00365500740b80409580310303c80503000b49280a583e192030307004003180820311a00015064102612210745900481c18060f003883e000405003801f0790040e01e580d04004891427a0141525800f10013610380a0040c03008a608145681009003211083c5854205020355030f9240c0e4100c800e4940c0c2011142e0760654041041c80c0280301d00d003060a00050200b846101035054540e00000030b18001503590600203000041c0d0b1050b900500104e00c4481202e04005002c1481714054103007824280145c0100500080d036503082441034101708030010802e20704014051130603900962004001c01e4421110b418041c40d07003900d00840c1000310303203000c404480c80d0070040256248080d40b050020f00303141c40d47c0c405401a41c4407020b15040360154080720071100f500d40c820320018010ad035840340c40140c00c1501c0c61080350707040c0c3c0c00009808014800c01c83c1c0b5003c42c2e5800c4080d113200c1d0140709120103800c00 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 621148165 1250 621146915 621146921
    0xe09060a080c01030221070504080d020c010e06090112020f0903060604051312020a060c031b0309052e090b0613150b21010803210603060a110403080a050d0e06060d0b0a 74
    0x20103072405100030703070600200c20381c0300018205485840050b2f0f21902c80d400b506aa031002c18411603408507242d50350802d024601000500340101041c103000c0c10b540150300211080360b021004403003481e140414200d00340d0408014080d44660107990070009403c02502400c20341148900052000a00911950b1554400d01965031441d134890000d01040103a50b8010703025150001008404a0380b02c0c2032105214824000c0a4240c1d40110117041502c4d00055000100000d03415081c80c4041e822000c0d0140b80905d10171a4200760080102e40454201242008000280d4a881e180000e081000c0e901901901d881e1f00405c40c2c00a0f400319603075134040800d03600300204902042d11140440ca00000b80303002c010009112600144218454414105a410650360020381e0301c07a0305507000350001207480040750300c01c0303482c041c62a10290516903a5618a0000c0c3c1c050101d505c00a5008507181104142c5070141d0740c14a1594006084a03140c070a002c90308203500a540038011041c00004242c04441c154 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 621149415 1250 621148165 621148207
    0x1306020d3e030d1802010f020309100302090a050d060f0605060301030b0109050a0e0609010504020123030c0304020f03070f060e0a21080d06030f1b0e0714120103030e09060a080c010302 81
    0x400c1c1840344180b4482d000c010701074501c13410b03404210a820b4005000e0b2001c003c650070314000809a01403e034440341c0440080d00805d07402500304900081c007260320f507100f8403241c807043e210740c1012803040c0c4201c442009603102d503400940030ba01c040c001400080d0000e02024103440d1415400105030313070780c881c0707000140001c5000b181450203641d042c82103e15042d04003c0c031460003138a0303405203e40c400d070480702901d5103c000c10181d404240f01280015581200a642041c0002c0280c140301c00d5120010381007030001e902000c00e811442800700156600a01c0d0244508804c40d00345c83e1083c68214000c540d940d01400b010001005520407004100961043d11024640c80c0410803486840745400d800001381c0001c2074554003014407544080710b09001c0d1610540740c000c0041c0c403c5440ea580299100030308001100e40741103007030211078205041c070314007280210f0295445240c0180c114041c05070703041014040f5400750076070007070610030348200203080740d6a41000c0c0b800695908221f0040800c002c1d4070 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 621150665 1250 621149415 621149437
    0xd1101090b1801050105030f030d05060a05030f100f0c0909021b06100e180a0b0c1c0605120f060106050f1b010227090703111306020d3e03 61
    0x82c8640981e540d800303141c001c0d980000030010307030340c07250109640c2d00d012007515007480e0b204000324031075445984c008581210010b8041e010b825200c40001e41054842200b0001c0e03517000c840c02c030406c040c0c20702910401c0f01d2400800c10000b02080001085840c9500aa00707203140c0000d0194441c1c01010003c401484920081e00d51500703200340309519003841881201c1c699102c000105072a0b00074100e65003000380510004240b468bc0341e64682c090850000d0a074550280140041c807031400e0300e0203d005081075580d00019000f070030003017080051107401c50400354035032103c04410189100020110305440660130082c1d10785805101884481c070a840103840c85100b00040407103080015006040c40111014207140040032041c2c0401c80400e80c02d072569405032030710010403c0c0754081d501c51148009680c0740b90b464440c0341500c1d42e07031440f00b540c00040141e00c007440c6905841d52200441038206402402030721640303040014410703449229120703a894001c20141c10340f00c4e0b0000b0401c688243c500 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 621151915 1250 621150665 621150683
    0x60212280302090102010b1e09060316090b0a08010c0207050f030c030102180f06070809010e0103180507080706050c1b1206072c0102190606050303070b090c120d110109 74
    0x3800e0020702941240c181c4502540c20902c8107070385c0e0300c0c0020078600d258149510310001210a13000b04450008060040c82d058080d0302004100e0140010508000c0c0040c0040402c5030f82c800001d1080388480c0b540003034184d91600131642c00c10f0b6030108004040302c00c200c0301c803030800d003181f130029041c0b83d4000c0566070715601c00903050500c0c0d01d0100c0851081c420031103a502407518204280800c5124a01c0014640c100c00c000c20140ea6004034407640e100741c410315001840c5452400004030045080805850310707070100c80104003ca0701044502c01800003403410504000745994004d9442c4401d203050000c0b8000a035000e070060300c0e00305148400070815001c03241c1608102c5005441d404240ba080303c0491403440c0700707104900c0f50f00241485200185e001344012850848815540a42490122581600d60750006100d5801300301034580b05000b844040114182140c82c5868842200d50423405423072824102c21010f00d001c07901034404416810416454080c15114500602e25001d000f418418 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 621153165 1250 621151915 621151987
    0x80c09030a140c0402120c070804090c050c16080a03080910111305010c0b060f03010e0f0c0109290a03110a03060e0708010e0a090804080d050c0d09060212 68
    0x80c070407082c1c05044038a14283c8003860354070010f0000fa8860090000c8a8040150200e030544002c4001000210301070300b155803d00361a818904203035074540619400203900070a00902c4100103100c80c0303d00003807a25456000a00d052500b42e1a41c415110240a00c455540046c0c0e1031031062000b9102c0d6541440c0410241014000420040d000f50341d64000500341141c021801303502a61200c4883c0c0d03005034807a082c50703888004110640000b00c1503180c055407903246801410030201301090800041030013034010b01c2c0c2c074000018002d5010b03a02c0f10703402d061b0030700d58010311410b100702150345100300500199490a907130500381d001d41021700740c1014010002403950310040d41644081d00f907550000d011481c644503c41d04440c0000280a440c2a044488000c02c078580819840761402c1403240d80c240382010340d1454801d00701450384072154041000095101100203081c8002c43c590340d540c1c100480458100b0380000c0d40d0700e640510420142400140150aa0850116502d0802d018100c400c490038 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 621154415 1250 621153165 621153173
    0x210903070621020a09050d05010e060705030a0b0d1a0405031b1515091501091d0405070e040b041b030b131b030807020904021903081804020901020607080c09030a 71
    0x400e0420140030140c100c448242e81c421800d0080b01d40762480d5560340c145080c00e200c1000940040e5a00880d403641d42c600700030168039018004d05109000035160b4a80300d00d44060b414056501c04074480b48079034051061040010200c00101d0044400491400001e41c1c0d00d00c0d01c41d10310320522a42040c031200b9009034072340b02540010040c0d84440f41102e901900d841c0c007810100080050070303d070b40d405544140058440c921303212503001c0101051502c002c4a96840c4a900741481c0b1142c2e80201c14608e140802c020300504000c014024412040326038030711300d8503403601650000c0142005140b80300c184211240240030075100300c041e64000d0700c101d909082507248491040085c980c2143c00c06611003400c101102c0f00b0a015003140c1c0c105050703d141c8840e503030030010300043c000c0040b40c2c0b00070303c070081400c44007421041c00003451042103140d03920500640074041d10070034440705c103101e5030040000041907603000c60165000f150705d00f00f07030b0340580310b80703801000a00403036401c2d035094415540c0c04070900c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 621155665 1250 621154415 621154427
    0x61609120f12031b0e03010f0f050a0e0a0503042702041d010f08070911130807182706060801050c041e050d03050a12060e0402030d08092109030706 65
    0x898407070098881002c6030101c06070103031000405a402118640001d8030540e81c0181d6400d03450200090000500c550164426000c4410200c40101c0490b038a10070840785101303610440d0519071552000780081d41d660343e55540eaa200ea4041c00c4584503107040c21490306610b200368240201c02100e819500c4a171503595000031485036140761300c044290003000069400304030468000b0f40f155003000c1c02d0790b05d0401e1002c0c3c0251511b003050070b40141c0100b03c40343c100410307851088050980c0c5009000c10381c0c91324906118442c00c102c20200568581400103240400d440f407130003604685011300240310003645c1082002450306070310160b915400d0004008404801000174419212401540c800b007810300300000c1c8410b06035004103078100d1502080380003c24042c002601d00e1140301d241035510812030208660a840b165801090888161400d10045140c2441100c1b01e001140c82c024295180401c40d00d59a001c1020180c00140c049668841e01d00c0100d82c2100c0c51503d024045844241d074522300103100c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 621156915 1250 621155665 621155693
    0x1a040f06031e0506010210020c0307050703050d0815030607031d01050a0501090c020c0f0904171908220b090a020603090607020c031203040201081003060f0b010f1106160912 76
    0xd50356902c00d8041c91034014454903000710410384c01426615040c240a2000b944102c800c41005e00c41440b0010004204014003409148030b0400b900c55150103000283c545e030750103031044030104403423400d10500d81c500160b900d511082c50f180104403050712820110104080700d141d80c02c01d50038482005624051600654100c5c0d026400c100202c0e001c00404030b03203591503802d84d02d60044015440c03003881e18024107615046400f4075030040755041c1e0071740d4180241c1c0c000090000b00d40105c07070f0310305d45540e001028642d202c10540840808083d10f0000d45c8400956840000c01d064a84408a0840c110802490700c400c0e81c09003545070f0703d0030301e100c62035941c540450342200144901c2e40c0302d0b415401c010598461300d001d000d560301d065407543d600545042038020682d242481106c2c4c00040480d501d405840100f00c2d2602001800742d020400052124071802c0401c001c2c89400145800c0c111000245564002c0e114540840c040c000c501048803220402d5100b40380889402c400b61040c82050010421 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 621158165 1250 621156915 621156941
    0x604030c05041b302a11101d0d02011a0907050316020316030903060c0c0308040b040305070819140c0a060e030d150e070c0210031a040e1501050603010f1a040f0603 72
    0x25000a013801700300c5461584007406c410703941001d482005c0c8802d1541046100103012201c1c2e00040c2e44102081d8a00320000b031400340141e45400002d0089460340c030504c66451415500c0c03961615000ca0003410b00d1201805000e98106004018580ba520a00580c0e1450800247c480603403801c0303003001800f9080b1070100f0303075100d45031210006181e4094809180d040d503058503510426612030312100c40c0e00000070002c0d000d20504220b0400082c88290042628980c0301c6240401740e44c052000400708070b02c0441d11455150104000c0d1060500007503082c0070b8a07070088000c078244d00d070880c00600f14003c1d40703803001d12181404040f8010324003016164087d00c20800d0800030390356400d08111002c100d01c9602079044218950300a17045842500200c80c8070100900c0506100c003013201140c01c03143c0c40e42801007180c02500300321480349044004180105170490f0958190350405040d1006441181300d50703024050b0301c0c0c0489103c03148600c290303001401c1c0c06c02440145ea40e85e100150280c0001c40c3c61031 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 621159415 1250 621158165 621158231
    0x40621030206090f060106050a11060f09150103031d0301060312080414160e061c060203100e040b07030b180c030a05010915050603070504050604030c05041b30 70
    0xe200aa4002813080e020380302e50004200703c0c2d03e040001d030380c1d943c4041144002c00800c100c1c00c00d0f4481c03003049aa801101c0700c0380111010b2a14ac03038000d0500310307103100e81c2982c0c02c0038000401c040790340144030360500d20190400f0308001a2000000340100700c1c80d1701c001c11a01100c1144100300d07411151003803150f4060341c0062402032401c15030300d48075048141c886030243d20181c41445410003005505a1280026040c1107042448110300c0b2511041c02c11304545030b540000400200c6020b80300406d00600041090000c641410340d00d0307040502000b464a003c1541ea10142c51a41d55282d640c40d40c46c0c00c0300c03007243c0c07501d00b024401c0310b54541c01243c071410b12074101400091100c2c0c4601c5100008048180108451402c201c1003007101d0b40301601010410109000c085a907a488500400040d0712680904003000e10f4a42800199001030110440c1c4500704c1c40c80501103504000400d8120104215501d10f001010807104900d03041a542e5401c2030380307030042c45018081c00c00e00c0d03108095822075407e = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 621160665 1250 621159415 621159421
    0x9051806010512150c1b0d03110a080c031320010905010c0206120c0903010c030204080c04050415240e06030705030304140d0203120715052202010e040621030206 71
    0x100c88190307800307076440b0f030607500c0518049150000d0411658016005110052400780500100c55140e18030030a020402d8214085650303c1c0340d01441502101d4684401079400c0c503028942c06000f03a42e0040c1140d60034040000000c215407001111001c001c1d90200810150f45044020030714812090480316011590940d408550b40d17000350840d940c40fa6006143c1c6140c582c070100740c243d030360720050900034541c40d05020050295034207010307041911000e50b50060f00d8520b80005c0781d19004044071502d000302c0c038220070b104c086440703103502e50724004540d5030101d9400b00001c608040b8100441714440c1d401c0c0c09840c00b00302200b05400040c014801281150744143d2100200f540360305c154840c2246842006003100410b082001b814a2101e0008007640c255882c0800141c000740d00105080b690f800d12400c200070300345c3e1207100716038000600744c0ba0314590081c8402401441022408043e05100e81d6a405040541d00d54000e100a848440700386d42268500e040500203d100d00a000c5016005003400 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 621161915 1250 621160665 621160669
    0x80d060f03020904020d060608101e021e0304030909060b0c0d0e03030d150824070e01080c09061c020a113f0301080d350a06090518060105 61
    0x80e419203400030004441e40e1565400c000003c00485030484295856440001d5080c1c020711882030300781b03042640400c40d40c1c440c903a400340c102107010500d90014414800f103140d65032600200300400211424066490b1102c1c1010703185880700b54072070444107040c5040407502040c0c0c4d00182c039905052004407030440009200995000240200c0540c15600504c025050044640c01043d9030b801001c014224550b29484054180b00340c60030303006044503420b81d075503044101f459240742c3d202c4000c0c6800e0b9850800c80000034038405026101002e1001c1c00703d0100300c107549042c1100ea000001c2003141c01c044807848000006900201102da020070300202a00e00d0304003001c00c1180d003505d615181e0042c81c41030090090074904c18003901071440342c0501180300044c540c0b01c004502910f143d0004015415480d18014000300042c00912200e403124030904000f600b0360251282c0190a00b02c00e00040c1d03441c091040003d101e5a40848a994280030a10821586140d03243c8500700c2c51030151507444c3c2c0c0f00e1007 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 621163165 1250 621161915 621161939
    0xf0703080a092916050a1101090f0b0406030c120e0f0118020303120a02071a060f0a03230f010911090105030604050601060f0e0919050f090a140a0f080d06 68
    0x90b070083c800b20303e600440351445401004105030000c140200ca05000a5101e040c0f402d000b24404179584e00c83c40b440240e1568024400c00020720222503541002c07402c1c098104801d018034407500041c541c4940d03a000c88a800345441c5910302c00350b100c0411200390000b001940da0050780d826090703654a4024825040d400d540c480c40702e840e40140040d80b07400004403064041e090700038058500305034280b204078001108842c0c0039001004040401d0000e0505504101c2c940f040c051600e03105060300502000003903190300400c0c0c2ea03105016070340b001e49010b150341d143c100501100d02d2646035203400c410204014190007003c0c1801002d0b80c405126a0700e45062580d00e0f901614003604031362001c001000024400c507141d01c40188285003c0941a4202c00820500300301a030303400c00494031007144000007000510400c3c2d4841c1846100e00414200304d00707926141d40c103002019003280b00814126050342010010308101d81e5010aa400c483d00b030a0804400941100030b06041440c2072100004401010b08 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 621164415 1250 621163165 621163199
    0x12050903070314070816060f05060f040911030d0917070518070306050a03060b181005100212040e061807020706030b120607020c1009180e0f0703080a09 67
    0x500452a192560b18107a07500d070031030f1055036081c40040105200149810026001c0c0ca6041219488000900e02d4128203940b950362070f5440c602d10f03140400c2460b80e035200540d1002c180030340b000581ea10550816030008280c42c0400c0c1c0d094420002e03a25130140e40000450304451015030f02180412a0035240d40c0c4800040c8a61540102c1c4400100400382e892402c00340c11420358140003d42c942d0b204041441031400b0380c01941c080d40d507080d02c41640e0a0a034010403c40102051541c0e0b1454000c1e102d06001300c071406014061141100c0d0300403032900070441750350711501c201000c4ea10b60307689555141885501b103441c4c6008010301c1850251100c4d1200140d4020001a00030f0080c850611404400501c0c40340182c43d801141e480b611210309106020050103401d29602608030000c0382010300440400079403040c4102711030100100400750608660b41040034040c0d401240070f4402c141c0091810007819019080e502440c0000001c01c400b4100805a2081035280c5601241c1d171040d00390107520942c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 621165665 1250 621164415 621164431
    0x70506070509010917030a0f08060a060503090f01060806090f0f12090402040e07030b040b0a0308160507030b09250e040f24060302090901091e050c13020a1205 70
    0x65808201400d0251018140e0a0010314200311815034444202c04040403021210550341c20024100a00680c0720300d840d44110003500b022070389820250045241a00248a41ea01f005004004120210414800008a191180003d01840e40ca80481d29240c06007a90045110700c2009490040104041b0740f409000303c1c1c04000e00f141500b031568010311071344241e184950056081001103407111a8584180c000c08440e074000484c80311580502003290121030307907144101100c940400001d0072150465660405400e00140039101c40e180207454a41960801802480041f04000c440320000a0b180c0d0b089039483e03408080c246408540310105906400b5a0f8010549000010003048400c09a000c9580c4103451304044a50500171035680d00d0303c0303194580036030b98a4490800c1075147c480d421a07003001d0403000800c00c84103d030740c0750300120114040a51460b89c0c00d024070303420f2180500c40100c40c040f01600d202410800c402e0188025845500010082210b1819081580c2030f648950b071f201d2105 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 621166915 1250 621165665 621165673
    0x41713090b1c0f02030a12080928020f040603050d260f150316090c0e0603010503190c030804030614130308010b1c0f0e0601080c0904060b010210050c0405150705 71
    0x106840e41c0c030f0100d0740c1c02c0090342c051051201d180c00050000980c1070000c005a6100c440c01d082c6000b1031401c0414562a080002994001d05410702510284c0c3c401c070107030b040311031803d6000b142022034042c041a52014000c0d00030071441c0280d00e90011201505490f8421491a041e9001e413070240304040180e03030102e101d010200004d14100070245000f061000000c04032288000c480d090448003015541082c0002911407c3c5010303496080f180300491304004544450440d81400b020903a584160700e03101d40781e8144c04000030140100400c400707000d15000030a0070398071074880c01d03c540a01129440d0089071803032040001c0480940200d205407044e45030383c500c1e01a903e480344107811500715030000b007641c1640c1c51810a943c086d5118580305424038a8005c500300c060350400c00c2c00e00c0c0b0140d2191b01146c0129203050070701e40d2040c00c0c059100d50b009000080240310f420040b482c00c401c3d4a550500d81c0e1800c004d11a01850750030140048903403c41c0c0142c030601451811080d0340c02020001880307a40 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 621168165 1250 621166915 621166969
    0x6030a2a1707030b180717010e071509050d0809010e0d0b0a02031b130501140d060315050106050c0a290f04050c030d0c020603040303090503040b030f070503130b041713090b 76
    0x30300c02001031084000c0d800089014101c6581d01402c2841c95802000c2c078209008807140550780280cd0b0700020407040710769906100654446021074810301915604001c28200c003609155108004588100d4018074803c0c01340c903020304800000d6000b902e080740b0740340e481203110f41e01141d2203040340e4084900c11811503510b03140800545401034107440203240d000003408011940030300d40c4940401903000d0070f1703481140d08608441604450040e0810702c100230080010301049600051548401507101c0114030541420000007190865511030b014024083c003028010248500c60304140142c1c09102510841c02100081540d200105032084010079030f9100080054601003000d194028064200410010b80c1c982e909402c2d580030781c0050000341c0e4040140700b41101c60790340182c1c0c02007036070900520303608240c035a84504855500000b0b08c2c085060700000d0030031818560001c40e201001910700d0b11242d58403e40400d002c164003801e01407509c0d00340c00b98114581360003000d140401580c100c1070b003c0d0b = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 621169415 1250 621168165 621168179
    0xe1c0507020d0303020c10050a150e070f0c0c0801020c070b04060f050c0f030f0c1c05070209150303030a0c11010632091003030806030a2a1707030b1807 67
    0x10b0b07801c1003e03014503034207104980310a0018481d4156030710025600250324503040c5400c40171500070f0350104d0010f103030b40b01040c480b5113482d810664002d5070b00c3c103044100c08094031044034076124120380284606c80528001482210540141c001da20321001a1801c0c01e882e2024107113039000d05e2090000041d4010005400d480c01b41004102e4540200291000256911032030f51555000c1c0c103000341a603d0020740060780d42024003144444041c02400b000000b110210000c0c0346020740c020280c8100400004103200c1d4003000c0c8008110000903094030786034039080c40c3c800d0007480200c5150b07004c0b40c001032000c5550041841103c06503050400e40e0250f0340500c1c49150410710740020221102d44e0041100c00455554045242c40b132203103643c107514010304500d0024510307800030700300031301a80c030030711011000402410703044102000007520280400500340ea1402c040c98158080304424110030900701507240c1c003080c2ca0042c0c87c02044c0c0841d0715220040d52101b980701a0781092441c1d004100300348190 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 621170665 1250 621169415 621169429
    0x706061d09070603150f1217040501091a09120706030608030412141002070c0510050c0a20090408030925050d0c090f0605090705071a06150705010e1c050702 69
    0x5000d19245c2c00c0c1c0540e1921284e110004941e0401142c0b583c100c07500b4030030821445011407440895842035030600c1d203014000b800740d40c803034005c4e0b10b42c1781c000300c24101e600c000e48000d862001400030140688031520540660311084207008000c0001e04000d00464001000404c490460303400081d565029107454890940d00c00c03009440c41d590b40100110400281810b00150a10030b004250001020b07240004010014110350f00c00000d01c6414001c03008410343c003041c203200d003940212110016007042c1141047e0685420100f40e80071a021043c00140980c1c40040d61080d40c00d40101c0b240c0841d80186440c800e42803094510741240b48000c180b04a04001102c0414144510600000c0d5529050142e0980303600624014049035102c10402c00e03403510041c15504032101d41022440e059041d00da04210482e000ba062400254500c04140b164807880100c6070f000c4101c03410300c0c0d1500c09a2404c0da0103010195046d07640c910461079250540c02c529a00c600360700003580c842920340b041e55402c0c0000 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 621171915 1250 621170665 621170681
    0x80f0d0c0b0408041e0f0e04033006080105150108090a140c04020315100914061606050717060114030a05090c03100b03070b1303020d170706061d09070603 68
    0x8051007030200154001700c00845a44000076964040039682c103014122000f142a81c1c01a1081e1815400303000c017007038010799185c0411354400e8042d409981d038079030fa182e03c0001264201011610b01500017800541c1035024900546078440e6074008078694500444680005403aa500741e6040b000c0500c00040603590304454070302e031030010b035440b11413181d000074202e07001120141e2500c2d505040070303107689c901100c007082e000382c007402c0c9004902c0c2400c01e10491243c0056640c0e020351400a041c207580d42020103040034666105000b8040e91030200e01c0100054a241443c002810090300070900542c05142c151a401440020343d070f00f150758070060200a000701528140701802441c2c118040c584003405240b2514810b0800480c1070420203090615113540e0303034010035940d00184500710403020302ca041b00c422a80c044640d443c603d0710740d0601d1800078010714000692088006040d00410940ea04070808407908007250f4140c0f842400e9100051080c21200801c140e0040d400520106000f5444010 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 621173165 1250 621171915 621171923
    0xe19150309050a030f110706050901030e0304090c0306080607090e060f0d120306180204050303161e11130506030c100c172a03031306020705030a0801080f0d0c0b04 72
    0x80220071034450714203005650703605034001003070071104141850304128010b2031584444001e0110600d8900000c0c0f49010f00d43c0164101502d49080c10301805041007980e000e04001d41c4108002d840410020b00104141d00c64200c060040c5000580035500804088003120b0958495209654508041080c22034807000296805071401c0700b0039020590000300030729210615240051954140714901a180303100034030a403000f0380104018403540d1400b006603030810341c4180c0300c40c070241164600009001c2c0107084824001d419002c83c0d00c10310659903000442e190080d503604e44165210390181017a640d040701c841f078143e405050a44c0306401c00320285601048213140002041030156503102810451560b2003070081004680d800260045044000300781011140394440e0b814080c031626240d000042042a0f00d0080003804400d1010903012a01d1540c2e1200950b0b503240500c0901810100742800388070709078407076602c111001800c00a50840c500c0815101c02d00322074201d81e100f1702c0300500244129 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 621174415 1250 621173165 621173171
    0x191707060f14010f18020c0304081f0b0f09040b090f0111300703020a020705181504050c04032004150e070306210f0c090c0e191503 58
    0x14003140c0389100e9501030315901c500100d00140c00702c5a1514202d41a04a80410741c1803003802c0050480fa04c00040c4c10341128140541c1ba074107482801404c50180380d201d8001d50144405a2580401454051100307622201c0c0c200300b1a02e4072400d0242034000f0069482e001582c03400440e0101d007070040c110380e0004940c070488400460304c58116094648900c0a80031482c000704401440009038070a02008922002400855130b407461001010b01c100030b031100042c550f001030907001032442486414041d140c00741586c00180d0380058504092001203604408031030541000c40d00a180500506014400454404d42001e0450b03c649034140030030920100c44007480e02d00078520352200d00480d024045904400901c5901d45007501a0302d40e0010050410185844410310540004600034244400054070ba001161468035101852000150010302090303c3c0c004005418000b03074101c440480e03559030301e5940414110050054000002095000d00c4541290030b2050144c1c400c1e0300305000d10b4914000c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 621175665 1250 621174415 621174427
    0x70b091315060e0301050f0c0901052101030c06030b1005040501031802120303010f0b0c06040f0302031204050102030108070506120a09020109150f031b140a020f2d1917 74
    0x9a507440046070302682c04204200074201062a00780300706940b1103080c4040036613514040075200348a00c102c40ca40e030306020b00840c2d05095940000304d1005229008000c1d0307800c03075840f82007425170440b451140000280c1090f014a90303508006000a6121f040c94862509140c00c000055010306087c012134080000201034030030159a03400c50241407004402d02442d900e50409400c01c0d1059526000b03910410403c108601d88201c1c0010150b0703100c3d0b00443c05403180003603850100e085100340c0c08035040402c0b412080c40248071040d401076048900c40d40031100c41951b50001d100050192109104803050490300058807007031903030440300c031452051600441c8070b9200e800000000a45640750b0000403182c18150383c0068042c03095444a10803080d150f0304254902d50000c00140c0026400e803001000070034298503503070003000940a0400b840c0c0645180c85480703102c4c51580321089100801080104900d041010130200e00c0285410f080d6050f480031f07030a030380c4501b0285000082c0c8503138084010010 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 621176915 1250 621175665 621175691
    0x1020f0301031209080307081e0d0906140105010e060d0506040902150d1d060a0c110304061e05030c0a110a06020d050406061715101a0d0c02070b0913 66
    0x10340c00b9521510906006006041006181841603004180c042d4010071203600454138010958400c84682c42c1c81011540c4582c01e508200d010340c5c0140b20440341008607180400c9415080f1220034a4030340c600398110782e0395000444180820185054004604004889a0400700d8010503408000a00b011540701c1813940482c1149403d808855a10343c004610070703640d1a094001d450000d030203c00d4441c0c50421035000c241d128100503022000d104c1d941c441c801c8a10340201c0b09a90018401810381e5200c9945040103810199640b2141c0b684044049d40860310340d0082007034a000f0143c0d0100c0c20304010000e042594035046034108000319105800b10000060400c2c0001e0103115000b4202007000d0902d464414242c07032003030b08001c4d0007042c0341010690200b400540e0b00c0792408014207050194a030701081845c2070015401030421603100c00550141c1c4188003005003054402c210040118204540301242c0311490350007031442c001d001700030b000b18618048018005082044400203004690601 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 621178165 1250 621176915 621176917
    0xf0e03030f040b0a0b0a060f0e1507030905061602150909010303200d020c1e0409050f0f0105011401050304031826031809180105041a06010f0801061101020f 69
    0x640744215600000410040240c10060550400d460a20521242da40c00340026640d504901a0804010104010a0b02c0a1088d0030131254200c0280c8266042c10300e0034a190080e41c800b4005601080c00000001100d0030080c045590341e1042c0141a80c2064041d030070009400301c3c0000b92800a8400e1100803100e5407089c0106000318826141e0f2030545400b0205407030064070b41e102c4982d0a4001e5841000c006401064204d00c10000700d070204040260880c0344d1400030403040c0038941040ca081c0100b401c02c20001080081c04500000302c1d40091841461a070030303288240181c3c14280b5001c0301e001501d50086d00507507001807190400c480c041012511442e140e906030f900c1007684203520020301660100310070f500000380342d4050240d441c0044000b03421030844010740d00a0b004541c103800245075254156030420b00c0124520090106043c0386c1461040c043e018040348001c000034401081c029809055030750f0130401c5a072100c65581c0e00e40001038480300071440c055510755400f00440461801508 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 621179415 1250 621178165 621178171
    0x3080d0510150903060b01020f070608090109060204080a170c0309010e0f0603040605060a08070b160302011e0510050d03020c010e03070911030405010c090503100b010207050a1d06220f0e0303 84
    0x2683d1603040900d9030403c10300369a0390b40d004c141550132010010b1003040d4007003407034801e580c0303942007201d06500c41082803401085250b102a000302d00c0800c000c070301e0386e0001c201d04284138000d010490100200112841035032062044181c0c0a600400188040354025084090078100003001c100c2410000404240030b94021a0102e80607036403401009a145001409100500302d0007004100d034900b85411001140b2544180320b804140248201003018400d40005240d050b282d03030700d64030013982d102180001e0720041d6827007400441c1009000c965070074816001083c0c1a00355008100500790313040151001c241c0d01d002c00b9010700030030070b020494802c2ca02401e010510300c40d282c1da07500e141c941400750850312140e42000400a03aa80204442e1398005441003000c0e803c000002a10f0fa6280c2c0140d1815111b030b0302440d000914041c0c001551141300401030764000161890440b19950402044115100f000780b12592080139495481c0c03103035850384807086005110340e0001d4910490441c80349550811 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 621180665 1250 621179415 621179417
    0x317040e0a091a0903040608090a020a03030f090501021203070f0c0b01060e0102100902100813051009110a18021305090a020309190519031e260103080d051015 70
    0x7500441c01040b59202040e5001a03143d441c0001c00e08081624540300d1280d0310a60003008172400200c0c446940030300c10460444e038024000084c455a901c0d0140110f0440c03440c44c004544424000601e95002050440400d4540d030780c4079140d585d80100c281c82024032002c1102c10070441d2403442000801340c0301c000740a0000c0342c680350460b03282c04c000285010108600b02e6034503402d02d0f0b025001030f200e81c210240311140e00e0803d0341140d45c03104001003c8801f004c10140070307441313040c01040b4800010780c04030306021b0040e000e8101003102c140502403080107510402c50050380300741c603920300496241d014104091016021902159440c0b00007401d0903400d440c1440481d6001041c4075142d8002c1003204401e00f0540301402c3d0b2038005845041c0c80d009407142042242d24801c1c091810188140250300002c12514481140c11821803001408c014014201d2444083e0320403078a000307100a400c2c0e940c104ca070300201c86440c1c08030b40c81909010f050081c00300d8280711a060404240c4210100c1c450303c0402c01 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 621181915 1250 621180665 621180671
    0x15040509040303060f0f0b1e13080c0f04060806010303050f130306060501080601020a0309050108180a0c26030904270506070908070513020a03140711010b06030c0d050403020f030a181502070317040e0a 88
    0xbd8041000f40304111940c5d01c2c1d1095152405c10819a1300204110741102d8060912507125130490644150b144190352005c9104a40c50718084100034243e404038003622001e0361034410070341d1a8001a642c3d800785000140c00300341c00860800c025032007000703422780c0085071a0406281d5150b044031a40740009030032040790303680d06005051000c0300c0b80b080011058107100c0e0101201121100115403248268440d03540150340305d40013800e26884c60841940003542026000c0003005290a142d070700c454042d01d00d42c1c0007484905000490503000203000307064802c02080c130580d5082070505d40000703601c48085101450340312140104c5c0059464402880350039103440e40c001020840111608440741c1c000128810a01030092042008401083c1d500741055000b0020f003079141c606069107030405c421008900f5100000f030008845a00c90010240c284c2110f2004032002d0304c030380e0035810482c034041c10703400142e0000c1c40070004218844200c816000d11049035606d080d0310b0380c810090042c400c0b910a211175403 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 621183165 1250 621181915 621181933
    0x70f14012a020a0201051c150801020702010f08150909010f0513030306060305040b040605190204140a090608030f0d0e030d02040e07090e0615040509040303060f0f0b1e1308 76
    0x103409101c0c019000c480384040d11440d03209500280c030b540a41422180103002440d80000c050080e1703400840603040c42090f070449507980e00c180601035489801c0880c00150008184a001c41c06440c00f40e000e00500541c12410f035140f0014480031400c02415405e0035921921040f038040b645208450245203008403100c4800344904000e410b440703c0e0303403043d010949000c0070000415080949203400980c01000410213455098042401d1034421000350021440010300003080d000103950034860f84400e4502041d5a80d84810324001c07130740c240c0300b001502d410404c940c2c00c2820403500203040c3c140501c0800542c1d090600515451904800b203544025540094180300c019402004190300017458501200c050b070400002125919001d402d050090254102c0d144c0340700750141c25900a05000350901c0544d15050074000c015010520982e900c00007040d0012500a00c1020001c065488149019280107612550342110341240d159244103400d0610550807000100e41c12440180b6680340140075501d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 621184415 1250 621183165 621183221
    0x13030c050a12110409030e0a271506030504020a030c080303042001020d0e0d080d050f0106020607050a230703080a06090608150603071206051911070f1401 68
    0x403010703410002030050088800b00000b92076000c0b5000ba280c0a07034002c2441882481c0650740d00b18030302c04d0b4590260b100b03d0701241001c0d000c2059000c00071030039000ba030f42040b11012201121240d01c140c1000000c0c20409102090213600490342040c409040d40e41c1075070b40c98403070b83e00400154012081981001003400188040180031462040180d0135006e0a8901c4400103996403810050842c18840340703c003003025555609181040c003640007840c441c1c0d24000302a03003600800d0100c030441c100d04c14a40011171420700c00600e4521400d00c81d00d030390345007008146017550303500d0a080121200f14034000c824000c050501015204071446030f290075a0509000f014101500c0d03513508103401d11442c0140070008000300080d0b10300c1c1b50306004112000d41d00d92001180c2010300c56008480319410800c041402c10100742d011910903a0074203c405403491030005020240e411035803003034240b04024004c00d408240841a450b90a5100710342070350386000d0380c41c1c856095a10200340c8095600c10840041000d07 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 621185665 1250 621184415 621184429
    0x30809011103091507030615030209100203040b040b09040b060c0c100315051318081305010c0201140c070812040f0b030417031306090c09140411010c0201030213030c05 74
    0x441001c160040c2180ba1680da07050795241d4460143d0030410281c800b00d60f40c039010703a01044c0074100c40c0158800e10440742102402a5104c4102d46000c0c88003401a80e11252011041d141a02c0a004000e49440d02c4d15040903600d40083d94107691181e84d9282c4070140343e450000400380403207003201801e90044c4290802c8998006800850203140c03c001249241240300c0c03d140c01074035001c880c9400c1c4580700c0d480260060400316208a0100c0a9021041c03d001881c4054a81c1c80c003107200041c0d01c242c46a004480c203180c11500240070030343c102d0100c1175010072500580208000782c42150480c036a2102d0552400c4181a25410000e000080620a204820b94404080d01c3d403200700310b00d9820720380e903120000b203629800f840c00032402002250b51502c1000f500c1007007982081c014816440c03141002c03c40d0b00810f20601000a140c900160007144070b0044407441a6002004401152301d5000190780c0401c42040490400d40c0c20000244e001c003c568090001d94015000071812500300400e01c0a2 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 621186915 1250 621185665 621185681
    0x115090902072f031911040507170c04050105070f15050f01050307050607020f060a1b0507090c0305070f030203100e0a0b150f0a1404050303030f2401020307020f01091203080901 78
    0x20f00c460640000241d80c40015400219801c0981e44070b44001d000c0c02c20504504007a40081e620038201414401a5507020340f5a0040e11071981018840740ca8000c0c2d400000d102d1845801d02064050200f130740031400c6290b491a540d401124002c0e003d078602c074000805c80c0d404407400d03818400341d80010b0200b800d0070807010010b0401078418920741110f54000842400e4020704c418402d100000d170b40040a4440c12140009880301c0780490f80c030800503d40a0b031035510a0040e01c0266190600300000e941c800e0081c28052071039600c0b10340d1400c05401c0e0031001f035800149100b1480194200c0004e6200114022501c80c03941103c00292100c41c2c002004074200c20103c800310101d50901031f180303e581d89803045903100a43c0b401d090400351070950944c0030074021a403225500d8000031040004454076980030038854644001100c00440201300c2e021280c811940c85c5500503402441107a0060600d00c144500014050511443c000d549200007011402c2020702180010440707428441803003024010564 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 621188165 1250 621186915 621186983
    0x90606010c080f0d05101e0b03100b1206030118030c0303053102090f07170603010902220b12100f0608010612031b0f030302030a0b030f0f070e070206011509090207 72
    0x803e07402c614035101f444240ba8000c24a01c90300c0007000c207696404401c0c0104c0109a003541c00f40d00c400040c620754564841c00c03102c5078025400c0100d00c482e12000b5147d5a25001d41c140c0701c0c4c0d090012162021002040020100188400c540314071480764603c101c51403903a15507000d506901c04e07103035205101a01ca0003810040380c0e115680c05214002d50040f0644e0301e02680100d400c44180d540c88002405010a8840603410203051504080d00100c0400030f40308041078a101030101c00e11a20a1050045000e2443e0345c181e0000e401c0504100d500c1e41265411520580010a9481d01e40f50800c0c21503140c3d0703100c00f691003503150000741059000500507a040803071111040401405498030104001e66000040405600200140603c1c2855100880043e005811034030100b0301400b041d542d44000041d4084207114078040000d1071440301c07403a544107440c142d000e810181d01c0c00c0c910306086600602054240b1640403404141c1c81d40714409818407d0055941c82e4001d48040088070b58a0940d000041e = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 621189415 1250 621188165 621188189
    0x6080304050a030f05120f1210150507020307030c12120206010f06125103020d05120a0e01080a021305130b0409060f0b0306090606010c080f0d0510 65
    0x101e190350311510402102c1d00030710540140c001d585001c900708841d070740303288512800c04241c010701117206101502200903c010174000541725582c1d1198201e002c1e11529442202c201e01c0395401d14071030005441068800340480b000e6036200c2d510401902c44907040403c1d0b103000b43e40c0000a005058411a425011600150909504060340d5115026150013000300340980c40e4500341d8404041e601c13007a250442c46c03500701c0e440c003484610040b1801284461140008511020700001c002c1d0360b980ca41c4002c0b40c003840907040f0745140d0a00190070f0131300360281d41d98001e03511008420120034006140c068850750ba10300d81221000c00141c00c60002401d80c5c503034a44140224a40c2030101d4006505a80040729000c5a64456020210103011606800d980182c1000091820440769070401c9840951102c41801844507981c14150303168030440340240b040d44a1000303d51554025881c0c801d20700e009640f041d00e00803090b601c841055000028042a00790307924100074400000141c00c5010701003007d070700 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 621190665 1250 621189415 621189419
    0xe01021803061e011a04090c18060e0f0d0501110a02030d14010302030a0b0a0b190503190203100e0c0405090d0806040c0f121d06040605090a0210030c09050306010b04060306080304 79
    0x940e03086a4140200e041c05e030505125456080d0154054030020308010a0078040b89203e078500070490001041000c0030506006c2000c03030428010440703c18100c0000d00384001e900e005004001203070700c0200d0191159540d481000440400690003007003002810b07002140ea90742c0640d031501c01c80daa294030240d010707010a001880160380200b0356042440c0c104880c1017a81c0c03100c40c01000142041010303a980726840860391500201c030050181c0031200c040301503d030340007071414000f03808844070305000703606401c6030000c01c0421201e6403001d10007042d200d0403150440c00080104044441c1503551038481c0e4861010b4040256100c202564842002d81e4103000304101c01c075010b050150b81c400941d0500a03400310907210070200b64032940c091842c1001e040c0c010024140065122041500e090310302a0030000002c02940c400100880b481c1c0c0d0103001c1210744a9403100c200c00814801030500c3c10020346120005d280d035000c10406000e4076001409541d501c3c986040070b03046805540c80099950024442 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 621191915 1250 621190665 621190711
    0x4152714013006090b0d11151c020903010f150501140c011b140c0c0105090d0f080301080c0d050604080a020f030f040510030b030703150e0102180306 66
    0x1594040e402030030580d103110105004082c0d050355920504201d10707010700c2015480d030801d4002c0c1c000c4418501c010014805a0024800300500300c000c00350201c809103183c2c4080d418003448203a2142074190669080c4a0054850307010003441d4840c1d808110780108450f121031074203215108052017003040c200502c0100500600e050059841110306001c41d031200b05040041c00300c100e03680c21110500030004031400c9282000c3c50190302c031010000884c10b8802422056044048034030326488800185250303a0524011907a680c00400441e0304101d085603140700092003a1040055944640710203a142d60400071101c1c50140419a280c0c4aa041c1e0b0f1144800f01d4070100d00b040d001034016007029512031303501c130702680b8241c140107080c54035110008540020380204405002900c0d400c0b20a0701111010301801c60075122610300d52070345508000010000201403400e06001300c0d001c0c0031301140301801c030880207003242c214510012140728172541803440c0389400c0c019554030900d529441c220408981503 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 621193165 1250 621191915 621191939
    0x7081308011a100216090f1d010203041e030504031106040b07060c0e01090308390a02010e09010e2a0409050a050105100504060c03030603170a02120903030d0b06041527 74
    0x40781c240c07000d0382d036410b1440f1f1920540050706916514880c003511280c0c80c2450600075402100c0c00d440a0103960206007000703a501122500040e0165502820541191610700c2e500120003209a0301a01c100300000e0301c5044007028224140c0500f100082e440780c0074a01900c00c6080003003650401c8500c2400380002014181525030446003040d172520050010f9800f007110f4441a41c50002c010040c1c3c40070000c40d60005005d03e9028402c2c2e03500c400c009009424000808400e000c3ca01072000c020000403502d104000c2aa200000f10301c0c02d08204556815401c110f0364415001020380380e86520070400719907064043c0ea8010700d001e43c1d6051381800d01c004020700600542c00344004110180718240103061194102501450300042d00c1ea08a1400018842035a0301c012070b070f04094040e240c19042c000020100303940800d5000740165203440204074106005107003400e100c0b60f0110007404003141e00c1051011480841e0b1b000d0300e074514040040d8031203e13001d0603c0c801900d100749101509100f0001010307 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 621194415 1250 621193165 621193169
    0x112b111603060f0b04111806031e040201020c09070909060b0906190e300c01021906200406110102030405100f1b0f030f06030807081308011a100216 65
    0x802c003140f4a03003c0060003803460a01c0c2d0050400000d0000c501d2088014110b00103143d0404034000c8000d428030019000440301c92032404c115103442c0031000600d0110640c054414410f640f440c441107800100000c0080c1c5420b0002520207409100c1e518291140358007429096a2050500c1408400240daa101e400c20822400700d041340750208a601501c030014a041d0001e004500148001c1d044036030381e004215802809001c64558840b680d9400f0035048a580c2c01030f400391040000103401e41c0a00d22600300c2c201d503a244e45100c445201a0b10301482204650440e40643e1340b140303030140042c07460420440c0c04400c0c7c6d00c10000c0c0000a00001014210b03401c420070007142c0d40545150780d40044c2568801d0072a0301903202100303c8160350109030f800e4400c0103501c04200701140e2032410380888805000041c4101d208019a4021030700c181d02604010341d03000d503074000c40d0762500403241c01e41d0350145003010401400d003041806807901281d040e01e454610301c0241000c41d910320000070040748074 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 621195665 1250 621194415 621194423
    0xc0708090303040801061e0501080915070e0a030f1a22020a0b120f0915040204020f04170f24071101200c06060402041203112b111603 59
    0x103004850358074103009031002400c28000030801e15a44600c8403007801c401498181052140e108041081d60180d111240100c0717078640181000905008000c04001d4042c01c20414020340340c010f400a66940801000594456913820410f80700324a8484132152030042c0e445015000002001209500d840b0703460503000c1c200380e119516812364004982e000509400c181207028000800a021045405020b8025640c03005d8003079040c0d4030311402c113072518110404c0e600e20240910102c3d0242c078094001e402c60351a40d8562600e440d80e40d005803480003407040e110a440c0d407c100700305009924107000071304044241c14201424040c0d018900c50441d1401800441444201c0f5041e07115001d09601003001a1148882c1481e0203001510380d41a981200e841041d1a2040710001119030601d402990112490010080c1e03074003e850303805440c0c11880344a405440d04c01c8000004035115032100c01e160102c80500341120ba104400340040001c09a60207003c402d40c80b00d19031000c440e02d82810703a0112a00 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 621196915 1250 621195665 621195667
    0x305150a2f04030b0a02090a060f2115120b13030c021002210d060807031703090c0a15080f1b0a170106020d0207060212031803070b041b08060c0708 65
    0x200107011041c01030f60805400c481000c810403500004c91741c020160560112200c1c41d1041c0c1d9801d0403030780001d02c1a204000a0b5100c54003c0040c0c00c00f83d10b40d070080c031940030041840d50a1014900301e403451988001c80500c4e182d01c0c03603000e0203918515140c0100070407040c004640600c2e10081c103840203442000b402140121048000c0364400e000c240a004000c0030240808180103000b0221600a0100741680c03d250040c00a80040300042820880c0d50006080301d420300820307040c01e070ba504000e0a11015005200141c43d07181d0b202008100039094800080e00e2043c609a0000c0250000500c1c00342c0c0c08880c0c1041c41007005040d80114052580d254034155200010a8203c82400f00c11510440842029001003101c503000314044501d040c4990032103124aa8603242243d503000d0085c00c11400b01e030100b0104800d00301c10200040f014000e64104da181054561b6400f02c81c0300211016282820802c0d07003154010307202d04004006144a000a14803801c0804070f2305203502c2410002094050 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 621198165 1250 621196915 621196991
    0xb0904020d0f05100807150302030402060c0a08030a05010b120a1509090b07020d050a09053a050d03021c051b03010b07110d03021e01150305150a 64
    0x15840c0c0441d1080324140500388426000903241070701801090758031580101d001640443d181700c002848038103d0749035a08444900300b80316400d42c020b5101600a0340c01880800401c0700400c01003110820300c902c10760031103941e8505110444102d82d07040c0c228002c0c0100410240e1001c0100c116100c1d0400d0407600002051052203a0302250706589034000d0ba011800c00305440b061158943c0003500c41e042d56003d640880d02d6040d022580e1340709441d9400046840342205010302c0c180705112355840d02118100c001c1c07001c400c1c0d00b420365a41140010300042c00340c00c2491003c000007482401455403440c00c0a5082020300400c1c2c2e803541e0800d1008500d01e5644400244440c19a8820105001c80c58140c2c1e035a41e5866156481140c4c0c81107409455512041880c541c55041c44c54510607020b030581d024003617145500324281ca0400c0c090004692030f649a2a030704200d200304100c1e0740000c0d481a001460030072016040160107070002810714502a180c40c4200b1088510782c482c0303200104502c80e4410b4110 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 621199415 1250 621198165 621198169
    0x31b0f120f130819120903030b0906040624020114090f0706050406020a021e040608062a030403050703031d070302013504051504030e0306060a0303050f2a0313120506010b09 76
    0xe5074541c50b82d17103050070301110500da01a07100401103403055130702d092141c0d90350040c4020b0710818800c0f070420301580780d10034141000b51881c85105441510000c41d088039040c14140300c01900352811708107900300100640d00c01d00200b0a080c010089420701c981401c1c035044001c0c1d1115181d11010740114162202141c40d800c5150b801e110000c0014402c00072242c5031282c04d0754601c0c08403144000754800c1c0707049014640064428143c10015610382d14075540d129030381103070240c00c500012030906d615502d040041100f100a0341e0340640b00b01c0020080503142d03000040004442840414400d00b84840c03540f0000301c10000c030301200028807100501510365180c05498615200c41490140303d40e4410b00082660001c1e4280c0307403100482c00c440c8662110400c111006c070140c400103001c03c90400001d200f802d10701014045624408052401031032401481846401004000040c960000281c00324409800035246002e4542c2003000c035603082b41ca03503c2541c0c400e0180141010400b000c41c00e600b2039 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 621200665 1250 621199415 621199427
    0x3030615210e120703020d180302030624090408031006081005060f04080d03090605150f100309150f0c020615010302030a0902040f0f05010515031b0f120f130819 71
    0x1a0a411101030f550001410001d45487e41000008002001980440360851f982c0c1442401d694000f406001181c6503118010010014140301c0b09880c6805090b0202d19601c803200288182d002c0d18525613649004043c181c005092501309809000303001040c024070b104c0c240c8158050f20025240c1541c1d442216030f85695900903540006458880d483c1c0f2110469031513001031210724840c0c0c038217018540714040f003182c898801c00c10213034100044020400c910f140140b0a82da00800ca41800211407109031a007045080e0407100b0905c08589807500050f85042d030b4883c4c07070035038142071026003564206040504644000103c00034105500030000c118020900c4e44000e04441c2d000780200140f1083d408100042c04080300050906850a80000f0341070420015004485402c002d51510795903c1d101018000300100c008070f514a1014051202d603216030800a08403000c000314109540c0c9480410451114401030070038809903003850414000682e94416112030345040c08801d01031400c084412112 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 621201915 1250 621200665 621200683
    0x50c0c0703080c0304211509021e041806020c1b0d12090b0d0915060501050f1e130e07020703021f030b04060b0d050a200703050d060303030615210e 65
    0x484032402c503840041c03c0b180b00d010407690302c503140540d14644e0b00803141044541d000c0c8080e411400340303140318580040ad00c1518080c1500180001114420b01024403c06d416807141243c805078001121240c00034100009409a8040082200303160800d1004c2441c040443d0001488191003188020925000310f00712000740505070000da465130382a0201c0340141c410018261103a41c0e1410300b108507080c5d40d02440c0240d400c10303141c5503d00b6148039441329080d485400d0007a00b01c18103031a01c00b80c03101c0400c0240ba0101900001091035800c00c2c50044030030602810250656200c0c0c50200b006880f01e081c0d40c0481c4944200386074041000c042c0030381c0035004c448015580f09107031000201c1c0860724100540030301e0404020810503680e13428000d008903440c010816000c0340036001c1040c40b540300c94000b0400705200c1d203402400c1581c070004a10503105542c0040300807a403070304002d0000810b003400740d001a01152034110080d00c076411540c4222540c90f00c2e036072141030301c0385441c4910680070031107420 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 621203165 1250 621201915 621201929
    0xf0321021c260103140c031e0307020612040212010204140f01020f0607051809090a0204020a021005010f05130515040e07030c0308090f010513211a040501050c0c0703080c0304 77
    0xc15000c20818030b45500c07400d0004a07000000100903440102001030600f084c110060018045a01d00b0110351500d03a6070f03e01040c22500c41086030400503140e0a002d040a1140c1406201e11400c0520400881d243d12042e410540da01c14001008a1003101c422024801c0003511400e141300070780c000407800c0c000c854907002c9441c440c072000c2c0516258020010131248c03a074003001103503101a141c00c0240c1c200d015100441d2a50100d00320201516050f4018a4102c00074011200a225414407100540b0402d0b4082c00f00f030058001d040185061002900c2860083e6110801240c5026500c94404422070005140142c2c3e842e090600c001c1000c109000103940c202c0303600310001d030b50703494101d05981c80700c01140d02130b404e1580a4840765002d402a1480003607a00c0e09010b01d01d00340841701301c4890281280c5000c100c1002c1000011480c0410120103192041030403200381e1174039040440c20b60700b0140c81420090020001d4521000c80415000b0549502c070003031503030711403140208916600a0b600710039 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 621204415 1250 621203165 621203207
    0x50a022104140a050303013f150902090f0c090301110706150501020a1b03151407050f090f0f030f0622080429040f0321021c 55
    0x30300d1658800e5021440341c0d100703403265a4a4508030089a442d281880401403103039100b030005000c5610480249001c0c107040055030700c00d0010101c1c0d110011100d002c1c15441c541140214402403001d11001c81030201c90b4840c013805060101d40c00710320f80c50f50050450b11410410f1001c00c2c5030308414405c84050780c00c001c0007401405400e201e00061030780418401c42d83c642c07803d4041080714007039884510031124160082c000c01c0c1c07902d440345c3e202030b00189590301d19003180e400040001907841c206091002044a0300140b464190100000e1015018000a09200050128000e141140000c95500c002c0c15911280801c546402003005501d41e984004e9040c010b076240c10321005400142c00303100d0290041c402501e02e6070a0304800d502c1c8480c001c00b4040d0b11342000b0030302400300e40e1040e29030320300d0700920300222401151104102c20741090704a040300b041c00000030002c0c802c82d0600c450f04544e0000741a80070302c842c40c4000e036031002c034416400c4214010130080c404030790160804850b4040491410 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 621205665 1250 621204415 621204457
    0x306090c050301060e0f090a021b010e030307081005090a020a080709050a09020d0204090212041e0804051c020a060201050610030b060306010c0c0308030109062c010b2a010209030d140d050a02 84
    0x780009e5044030f03108080360207000078a00d4030b0a2050040620540004010b586107444180049450200c02480000070141c1c4420004e61030b142d090140d0300c243c510a10050300e525540700000c104c1c4001030143c6c0700b0052041030a110a40d203840c1c87c0402c03280300c080016a60a034080c41e00d00079028640c801202a44013107511102445a6400300f48107500c5981e425102005a902c400018001320710702030001c0030248824002414091102c90b5001507544a0803160052940050520040d903002b03200142d4440c010b200c0c1c80d0420f44801001e40c841070406111050500f404504c00d40001008107041002c0b50390104140002c942411001e540c11604140d03a83da111507085001c1e0205205020a140010b02c20004a0311a0090301c0031200e4007094112003030340391140d00105038200e82000b06603085d0181c92072090394a51203100700241c030000005a29000000e041506004d600c0440314140010300002c030080150350740407154600d580d030a0014a6480b48000e0310000d010301c0f44122803440160403c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 621206915 1250 621205665 621205681
    0x70905031b01020c0907081906030203060a0b031b0303070b100305071d060111031602030309101e0c0c0b07051203040f020a081603030302220f060306090c050301060e0f09 75
    0x140d101c0350744280c00702c403080000c41c030921450360310898015001404000100c0ca0f0107481c940e21040300c01000401045071926500068107051040e201070621380d68425400804c0e0505200004000c000040c180070008400c4020a03200e120b8501c000300001d50003c0014105030368401c07294007460300b142c210380c1026100c55007854200c50400803483c9404842000403907662050905d400100030510241d0b00f402d540c20b0602c4200d003282502241e25010a11281034140c031a00d64410a50066507107000034032111014682c40140400401401c20070031844601c0403c80f296110800c448203044115511052414003d042c2000102034078030071701000091205209000c0e1842d800d0070b00032116050704507900c01e01c051352820100a2074081500301407040000c01c2c02a8043d081d9400010446000608003440b8481040d0003034001c002c0107030031442c0503c43e156040c414a4040c10907c00c2c2000305c005800c4004d00640014848c400070072440001c18906070701da0107810f154000c0050807100850400310a = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 621208165 1250 621206915 621206953
    0xe3f011503030815031f0c030908130302040608060408031803070803010e06030d03091e0204060305010f1d0102070c0b0a02031c0e010c030501050604060c02030f0f06070e030a05070501050307090503 87
    0x11300c2101410400ca03000114038001c0307400350403011000782d014484819040210050030260303c210061540e0b0760108400314181000070036000340c404000080142c1148104005c803049500008111340c041c40c100700c0012080320460380c00403010000c0e45040c245d40c007425460762191450040118401200000e2050502e2f100f450095804406440109018031801c40031260b002402a018142071444003001c2c0c074203801c0c01c0040500103800403544a07100c0e1601429610300e1100f15442c542d0f44d52224540207800810704481208903802507240004c40e4a650a5025090059107d01d01000580f081118004c208442c0c0c2d00071241080c2c0484074030141d03140000c11017001000140d5003404601b281c1c861180c030550b81603c0c0000c2c0840e0420703080000803201c000c40701d041241c06204441e24840c00301420040c07800c5002d814802045541f5050303000600d180400c440d0680681c0c042c42c0f000000030b4000c030305141610020b1801c04e80741d0365901030032a80c0000c0c81c0c0c0165090b000380381c8800c6440c25a05 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 621209415 1250 621208165 621208171
    0x6210106030b0906070207030618140607270501210507020d020706090b0d0b061e03041505070507060b131a0a060f02060a0b010201090c060e3f0115030308 68
    0x65504020703680c0f5030810075181c5004460700c600580007140140005146940541e0110008a0801c7c4403044980c0d035800d40716102c502003400640c4224200302c0d21561151f1100c0d004441110280c0c21928031115010044200e8001d030350500c80c800e0640390310118580200ca60381c0007807400c2400b190406540203034803030940c10701d80c0005004480e4082421402422018200c801091200d490b244c4440116030090403d240b2a41d44480c0402505440e402404101602c075140445459500d00301441c1000322041c00b0341d21500e80750300b031800700b102c259000300039a801c4980020010529141000c001b0702074507051004206940e1400c0440d2444031114901c0440c1200180c81c2165100e07211282074550000e684021001030b40a4000281c0181403908041007010040c000404c141449940c0c00110a603181c028000191a0840c14a040d1400b403003480502964045600c010010303d0640d00000100313214a4140032200038442d100300802548210f900b418140f03030500c0b8640c5c0304c0c58000e02d0303900d043d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 621210665 1250 621209415 621209423
    0x130618020405072a02060c0109050f0d020c090103080a090305030a170f090703030f020a1a07030c090303051e0d0c0c052b03090303020c0609030903330621010603 71
    0x800d001030459401810901c541c8141a9440c0048012415004c01c0000b01c50604a80000d01402800d004001c01d01070000c6142c8150080c1280c000e050310480c4c82c10220204100455011551140c6152182d00c0030a064a404c01c00c1142d4072062004152014202d551000f07042c1d00c0005a5440016803003034040c00c0b40c24014800d26005c0d1115080d6246032003069a40b0308607900010820000a4010500b451b4420480d0040d19610b1040391510280c80c00b08a004039083c1184804000d0040d61501c6501403059160410100440c10354400810038003c65604994201034031001c1d0303e1511896081e5090b04c41c42d00000d0000801c00c034401400c0c6c41c40300c4000c031003a21504100ca2801c0882955105194146241b04600ca44540f2012005001483c4c02502490303401c0000d402c03446014044039101c3e0100000865680704220189407802401300c088400d903442c11740010100980c1e4401201c0f961380c0410000500740c44a1000662117001701f041c0b0304460031880100c042940301034204a080f04d000e = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 621211915 1250 621210665 621210671
    0xd1b0905041416050a171f080a0302060c03071803200a08100c03060806040506190b03031603090506030a0f050c0a0c02101e020307060b010918051306180204 69
    0x40076030881d008140543e82119400328444000500b544200042c01c0d008030540340c9100780f089500300d196400401503a040340b14000d01d22403081d0300ca0300000404000c010480c02040c04c6a40d5840c000e441d144064103807045070800002084295110b207685444246281444506c62503807403800360010026180010ba0b003151380c03e070200c00d516116024008403880000506050b80014001100501c00c0181120500da564040820b55aa0401035548260303c00c0f80200401e00f4040b081444207100d206202421600749034560780d0a4801009854200c00e02d0049400014207901d002d49129206400650b00028040700308010400e41e038026840c414441c100070007240d221b4581580003881823007442c102098001092078018107000d045c101d6003c030140340018001c9250781e030740c80000d44000c0303040006900c04201c02e82881114803942a144c5000d08104800c01e261154203403c4c10b281c0b0503c410040d98400000300c1c544517441c80403407100e502102c108690148050030300a0140001ea050380a280b13 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 621213165 1250 621211915 621211931
    0x130c0e03100f11040302150f04090f0b0102010f061202190801050c0712020c0607030e030709020406030b03010b030d0c170c2407020106030305162102030405150304080f0d1b090504 79
    0x3c1e0000c07541a07a030090110004400c100c11100d6003076103c6041040e90070400c01c000502c000041c41560500e07600c5100c08980e100250b0002400e64800004120896103021020441282c035003401d90881030341981c0d42d0420194401e0a60401c5049034803185c6d1650070300302040003000007803004100e02407290231280e040008850040b40d030303804101401904840c00b08808004280104c16246041e0002412295402c0e22680703024281e801c1a03010744082034441140381c589140030b000d44c140d440350071750040011010058000705505480c51010744811410b04841c02c50001020403203000a2003070040711000b442d07502d00508211040881c245208a211004c16007451040c01103508032030b056a601c82c00c025440700f1044040f4a005003c0302d2020400f034592013075a8070b0b1490301110391202d40141da29a0305d00003d0041640b2050034800d083e850030010030002401e00000d40300a400c2680025458414014200004001008a101586120131407000006520008150560b0b00940302800510 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 621214415 1250 621213165 621213191
    0xe1c080705070305030a0513141f0b0907050c030d1a09011d0703020c0309090103061401150f0c02220603050c0f0d06020f091f020105070509130c0e03100f 68
    0x40500b41c0024001101000410030054503034121a4100c07810b500c903041003000d1555030b0781c41004410105007103074100103002984d1401101c0000070789131700020300707201c0200920001005000001e00e100248a404290540201004c01c151030906032410410081c5402d29881000285441d801d618415800300c0700100e2070244110180301d0a500301c3c0c8842209841c0c600e010360180d00300d0316142825100500c070101d100e94030145014000d40c003035000000d20b1410070382c9609900e54142c01ca030104040d0f00d61460203031540b18882c031441c14401d24013103602c400c041c80069017014000745c1001542c11688940d210b5003400340e1183e000c480c03241c800c88541b42903020611942c00c2114003003660189880c00100003240464000303144200c0190b50540c50700400100003040000e91800307614000c4103c06280c4207071902485207036040046403c01900703104010380040c600803614411000f0f003030303101c1c100031200c0703400b039000c0002a03134004003a80e0300300b40712400c1d05000300310704190f2100e194103018400c0808 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 621215665 1250 621214415 621214417
    0x2071721061c0b06031c050c100b0102070b090a0f14190503030d0504060212040c0303090509060a09090507150c0201170610050a0e03010f1b030605030d0f030e1c080705 74
    0x4640800c2ea18405040c1580b07481040c078800910325505802800c0c02100d51604000783c4c0c0241007155101c1d0303070300c5440f144403541c646007084982e6031020707160610b2144542e800140c1c0d40300319100e617440e29681e0700003d40417860181455008510b41842d8400c08100e20103101c0d26120507038419144a110811055003441d2902c220b8812107170550810010503200b01080e802542e4400e0041c8005458100040980342c65001d0807035080d665134032815010b108042c1d120b00030100900003141c0382c0c2c0b00c50800000081055842c1d214071440c240c0da940035041004000d10040300200003000040400b04411600a0019030180404a00080f0346404865002140b08940c6015182c041c00310001d119080c002036605910414642c4240098204007842c255801d0088560600140d60040740079442881c42109088001d441c5e02d0505050860a10290f1000190102110340c01c1c50a001080000641a001008604006541800b0340c100c0c07500303c45210315106050901640c0e40c5020b640e2000021142 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 621216915 1250 621215665 621215689
    0xb090103020a05040c020102390102030f010506070f0f060e0d03020c06072601060302041401050a3510050906030307080403060b13140105010e040c020a060207172106 73
    0x1000b0682c50b410301a508055201849101341d50000619000380e01415541d90001d070700c00140c04002d40711400d042c0d0b1000040300c0f000c03914a40e000f54250300b844815184460030500403140030701d001050100502410008140e002030700007001d601050220300b8901c0142c00811880c034034500c68043d04504d03552003442220805562000a8170960700d0300c6100712002e5490076161400243c075640c0c4103010300d086069a81c02800c00e80c1300183c1c6e0f00c3ca071034a009071010121310b080307041c0003050102c079004c2c0f80c010855070b14529803c4e00341c1c2c088400c0351b054484ca800b209001e00c0d40d050361060810031108403c19400044d07070070031a064040c0781d0381c22080580d0380c860395900600c0844280030400000e00950069940380c8001800e5900c80d00d080c0c503400d000c82d05001d800c0324840d64000c004100e103503044044000f04d6081524280042e529150000c1e5840041960050010b64005104810b1080240343c02444016a030581ca5035004030840c0c6440c507540039100910140c10140c0031845900c0c2030005021 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 621218165 1250 621216915 621216919
    0x140307050306040818210606090702060a0504240e01050a2c10020f0d05070f020703110f030307030908070b1309020306030a022107090608210d0507050d0b09010302 72
    0x2010740c3d0f959035901072a0308002c800c040e10800340c06072a105555400101801c0e00c0200d07003401494806400308a10f80344004d01036500442100303040c80030565011030310f15413015040f5404a230580b21071505005480c081c3c24101c40390080c0140064004c0080d420121503800884000d000c11b0700e4104414003140c0c41c144100f103d200861000403000d036480c2c1640c00d2038842c0300086d0b614100c0340b040c0f01000e0368400e04055000c8880041c14071108034041c031a031074200e81540b42c200c0c015a020f00000e5583d16850201800040c2514901c0100c4d5480b030301d902c030380d40c00c000c0c0903291503e503149400343c20307101c0c28000e00105010342e400101e070342040081030762642141000100100c0385000c074001e009500140c0801d8040c025a00401b0141e00c48400c000d0003a90400c1611403014000300c1c98130300f4201e07141c11400842d401c04008010010000030b011001c0240c074020708116100304600501d492050301e1919602c0790400003080b4202703410034068080080108800d006000f043c504001409a00f404025 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 621219415 1250 621218165 621218173
    0xc160512070510050603031e0904020a030506030105151020030403080c150402060a08070e0a03151406060d1d0d0e0f0d150f0204030501020f032532131403070503 71
    0x20105239204070140c000021003402072881e220841d4003180913a4006101d0001003506c44090110703905003440f41652080fa074003030007010071502c480010003521010045008005d01031040916540303e41070b44074041c0c00c0c20002c0700d60715541c0303290518850308216040051800b40d01c408158508841e00407030b00c1a23034001e104601d00200d84e1401e917100100039201901700015400c0e402219210700c280d00001d1400384c81c0c11500d0743c080c0c0203400f06484007881e030710101e0b2203220144002d40e20350388141c0303a0890540c80d01180f1208281070509038068994a16036aa2140041e00c006168002000350722400c030940e001c8a140c2004400c0c0304419043d8103000705204908080310340484802e5000b01d030031401100015203890707502e0b00d030302e0f003641c00ca440070010340007001050044451402a800100b0280b030076260240104401020704804003c940e0840340090303291030224964040c5030000202ca040003880b985a07c55541c0100381d000c6240140b001d40c100c01001c040700d40c94002041002c6420040c010 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 621220665 1250 621219415 621219427
    0x1a01080601060e1311030711010b0618040c020c1302030a0b060415030c230301260a0f03020a060f0c080f01150c1506120b1e0c16051207051005060303 66
    0x10000d1344000958000399142d84410155048018034021402840316684103108112511412421580c2c0801c103244960001c020507406003e05009030015503008840000384080e050300140c1c10441d850043d640c8c446000e41d40074a03002d001d0b03400b81d401510310310f100b049030001202c10700686100703078000c0d1010500703030304018440280b01e9003100740c0000103840c0040312514500e480b220b04210206980c0090f12002c0018410410458150321115080760080d491100d488400c45440e24000c090151090251050480074180200406c10800384e00180821141a0b03201400300209500703159035001842a80208a02290015105069030300410a2103000a048141561412184c0c0c42c216108506111001913483ca540f28000040480d801301c03e01c80d9080b450912a4007100802c0030004035081d664408c0d10250500141e903021009682c0782c1c2d03641401050803a12014403000041440c4506510b15080740461740241c151103226004840d450704e0032404900a0b660110b40c01070b055407042c020 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 621221915 1250 621220665 621220669
    0x506030f06030f100c030f050106090b070c240e0f010e0409020f0d21090b030c07020d0f060c0e01170f04140f0604030e010203090108061306080a1a01080601060e 71
    0x2010307410110007011a032401d01141c6219081c0300811064074481599200c0c482043c0760103014134001d50b90448403c110340d60400c200500381c20300ea80584000102d003c114038042000090801c4043c182c4100e5100c1714031840228042880c2c0c4e5648618006840c41c40203004034100b1082000b000d075016101c09410762402d1080c0402414040f43c1aa407040411401150940390400b01c0b14280d1701400c403902c1c1544124510401d180c201c103281e03204001c80d03200100310031040d034010760b40c1002c61840801c1e6200d605000186103a03801c100d01506401502d10514100a5680e103d84803414450302c80c0d205c40c005031070040d242c6d030344080000e18070800b540e40021507035503942142643c403521951002031041500040c207880c10344c8109440003284d03c414140001e240e04601d0440c00b4803400d10040d85410818000202510400b0301000e0061800f20107040c1c0710011a00500003520104084898603c1607090101d0382d5021150b4031121025480e0021400c114003040d614142ca010f03460742d074451028541 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 621223021 1106 621221915 621221941
    0x30a08090703080403080307090b0c06090d05040f05040203060103110304050609160b090904151109090c030702031204020607022e0906021e15010f030615050603 71
    0x101000080c3c40d0380304071025640e01c015055165142e10720144c503008c1507038004440070304020a140c140814009512442504290200c50303a2500c401d0301500e07144603030f015500e2490b0a0010520107401d0030380003560000d0303062600040342892200f41d000703e0340060780c1c2200c4941048040c081d502e40200418407501d82d181907462005890100c4014013449849007007400356401000207400e01020703112001d141c074440d807018000700d4a0504c2507060b07607200322400c501c548012000b0640500301d00040e0380c031074221a00154900b54003986604520000140203da0000041258000580300c2d510510001d4184442013400304944d4491010010840d01482c42040407204c41000400d50010b4400f80c4c0c49840650f11410b42104031489051442c8855903078035140a0800000d012070703200810404aa00650040010003900010118160411712070907521040520114410940f202 = true := by decide +kernel

theorem cover : BRFrame.Cov 621043165 621223021 := by
  have h0 := BRFrame.cov_init 621043165
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621043165 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 621043165 ≤ n) (h2 : n < 621223021) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
