-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4983
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:21:34.159882+00:00
-- url     : https://prove2.me/submissions/c49065ce-4b1a-471d-883b-d39414617e0e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 896043165 ≤ n < 896223021 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 896044415 1250 896043165 896043167
    0x9040608010203090709090506010b07050c09040516050919021c0e0d08060108040c090e1f06030b0705030f0a0b0111060403030926120c16150f020301050d03081510 72
    0x3d001520004041d000e161700103d0f170320302036204606131980c0140003441180d01e8040500a10303800070b0000d4490340901e407038502007500d030701c10305c18020b5100304020612207220a250021a4426401032449050080180b05c0300c4504002e0071010042120001070344d511781c0c0020180070300c42c2d40300102882414410140517000b00420b2000ea6030300607407102002c0d40d81e02001166010011a0003c1001852203c28410502c069004610b80c0c6134980c11141a0030040000542e00580e201e41408410380b10f01c42882041000b200d03c0e80c200c101424014110b007070491500b00c11400003050340118595031401030740d81d684145c40400000c00d80000361038040c10507040c02409001940410b032178150300202104809046074580e144d100c50b4400382e0300c2c1031022400c0e0580041e02c01401c00074180708107000d00c642c0786a12442e00c035001e91140302e50310914010814004107485001e0603002c0300d5403050004005503141c6c0d22100c101ca5a2520f030035141e0381c0d203240001484504400000e174004803410340d105921 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 896045665 1250 896044415 896044417
    0x4020c150c03061504051c05210d0605060412060b04090c0308030f060f0a09050408040302060a0203030114040606050703300f180201020c0616060219110606010203031902090406080102 81
    0x4079400e561301074150310015104900c6214038424160440300d00c42d43c07000006903032040181c090f4420801e0b10803000001d0b40c1702c0d082d003510f00d80b41c401645000549101c982c07414400e4400400c41607038030901b0940b4001a0100c10583c1c101c0241c01c0035150126900d0664456000b003000700d920000607a03106481c0d041944094004036254021090100003080e00c3c1c0c90303c40c0640500e1000140591960382c2081484400380801810441d21218140004001a40e441c400b51400c1800c9900440d100c1d85441c80c0040d000007440c0076039009918100003405440e90001c2120b910f240c16040c19507074200c8000f410714405200c101d004580400181500040f1501030300201900150140e0600c07000c0d1800601d14611110080028003590129103680e0030760038200c000d4060440c410340034026200840e1100000d03644003c00b0100800072128a440100e40c0004c4651080b606500017840b10380340200010f0f41e6444060101281550314003003194a50f40d0640480305000400f40080c0801da9850314000d020b = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 896046915 1250 896045665 896045671
    0xa0201050315150415032f07051009021f020d0e030309041a01031d1509030c0a0506071403042f15132102040209040e150601090b040608040204020c150c03 68
    0x4011285805c1491031080c0540440301c6905c3c2d40807201008040c0c1c0d0540088541da00d507683c1d00000f40704680c08900d0503c201d140749918044080354502440c8100700304050b609031042040030504001c00350f81a8000740010050050f4188012500c0b03003c80042d1840c091044c0007640700b801c1ca8006040106d407006078840c00b20b400c0c0c0f41800070414000c00410101c1da00041c0c43c2041d0f00641c01302c07004903c00000103420412110507680707410f04002d4064208041c00d00d0641d600e0f4004c0c0180a14290f000c0c0d0049058460301340c2450550030b05a49004445042040b015500e80c0c140d030403000804038080141100c001c00800c61822200c100305481c0d45034000c0308001700500400707540082c00d510041581c0f1400c441401210380e100c100303542040001c2d044100240e400aa43d40d0706521041020020611117100c0c044c0407070028580b00d800103240b096503030401c004002007404100140364104101641080c0e04590160301c6001c81201c9914010700200c0350000d4164000c28000001424001180 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 896048165 1250 896046915 896046929
    0xb0d03120501080a1524080a02010e04110d0e0309061c060f050102060f070c0204060e15010f230c030328060e0f0414010203090f070909050a02010503151504 69
    0x100c00da81c1d90500c16250650f0b0400175007000148080444403148a40c404490352071000d21110724421105c094007000c9015400942107644805042019980c02403051444844210340034014400101500140c40c025030160204860b02c0b032810841c1c80a0034001d0f201c94000c0504100c0d00c41440440c0b4180d03e030040000c0012a40c5000070100d407a1103606210410344006800130300080d11024290640080010414820415416000d40050352580250002804042d410708090708102c421799030310600400708a414810004190400319411001c001031200400b904003480401241c40d00000b4442c0660712035032408000700300a0074000002d04081d40408060700c04903001e40914918003110504c0c091a4800b03008400014151000c4400c0d1940c401d00c221900d11240e0003c2d6041400d9800983d447d1105404c0f100c1c01030300400b000c0241d9001130402501c28000d0980940b6942d0300c45000b0f00d0044d0402c400000054905c0c885c621071041c03444070241c201c0851240000022000c0d40040c000c845c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 896049415 1250 896048165 896048171
    0xf0e040c051204030c14071403062a09030a11092a0f0d06030c0314070e0c1b011b1215030209041b0b03060a0e07020c10021204090b04050c0414130b0d0312 68
    0x1109d040003d42e45124149000200010010310414040030040c104400c2c4a181710070402d0080e203840034071200400c180f155480441c00d034546d600704108100002e1014901044440702d02c01000e024116203e01c61011480550352500a48542d180c40d01c940014103441c9130801c1d01c004100020001c541040741d00030303c1d041c0c0b0601d8404032059100c16003485101c542c0d001482c0450260f94001c1e0003090000f00070403070f0a0110421603001d500350303111118103182102d5604481101c203074100700c4080490822003010000780481072581801c41d00b045c0400380c0100d15810004041202481d08001542e4040b036a40f544035940d205048042c1c0d20803201d1724003814039000001203050000c0005800341d5020b4010706005807040b001c0c008020324841c1100110b00c5401000c90010807040014000b4200c40d140204209500c030301448180ca1014011900380744007000200b22141951909840c0600c0c00c41d038615041920040070400b5003d0601e41c00d41c0003021808000405d03410a00b0b15242c2a150b050078 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 896050665 1250 896049415 896049449
    0x21204020906091e06130e07090516140d090f2105031623040e0618090a030e0a090c08040b0f070c170c010c0f0e040c051204030c1407 59
    0x3c8452504251407502c480c2c07030313040314184107011140559903200c00054900d0035003410005d420f009894000040031115084000107100c00031440c05030691203694140c0810300c2e905840c0c40100444c0411b00410299080481c110f01d8910a541002e00015002007204e50b0b410040c1c24030340d5101c64940d029203003112880f003003424401c5c000c40590f0301c03030f200804101d141c401500704295000e80c0d42440007031004201c42041d0490041c111b018002070314503c400c0003001e20f004024480d08058200d40c030445052040108840380c1c030009003402d43c1c117a1628040503040900c2020903404c20498011903e514141001d04900d40c2e03104141d02c2c8254058608030b25a03032034640d00d100c109803080d10b54000088000b104440440c111031350744510101080079440c500514a0081421202400c3c00e02d8001001000c400c074038658400003180c1c010b60200c404003d0b00503255400b42c401d210f40c040c03030250814400000341c04e150149011488060b004411080029130070f40c01c9945813001070240301c800a41030648 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 896051915 1250 896050665 896050669
    0x60e10141617180c031c1202032203051c02091f080a020c070302030d050301031407140d06090507090506040c020106080307080702030703120206070912030c14010609021204020906 79
    0x8141e0004001c0c031001d10545600400c0e080e43d00c40c2502400552040801e0418152410810f50401b041ca2440c46569014881d1004010020051044144034014000c0c40007400c040700c00301c03100b4005c1c440580e01402c107501c3c00341c40c1d45c000c02e200c240b0074105042e0032503c4071a15400a140c4040c0445d14420280d0f4800c3c000003103046080000c0002070101800946450580d034010702c15808540c1c02c540303c15640740d00281c41c15a80750a40c2d40052004801001084540305480304144103580151041e28105881c40110700c640d4000c25101c2e245e11200e140c180461a409516419041419036481603281c1068802401e4141c501c1402180740c000d51041c214410320482044c2d4956001541c80c155898556500941202c9002c2e603041c0501040000003458081c2501c0c120760068024101c1c0b4600818003428401c0580c1c4100340b134068000010001035806414100e00561003112090030b00101141c0c0d60040103103401050b8900e2001440c3c4002140c02800c1c107128134400c5801c0c402541e40d07601 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 896053165 1250 896051915 896051927
    0x61404090f0308191a03120406020c064603020702091f05090f040506100e0a0c02030d06030f020a0f03020a0b0a0302070f030c02040605100c060e101416 67
    0x14090a2000c0c0c0c0181c40001a102c1c8410a4004802d100381304030301506102035004076815040918080c1d100074041c4140340c14103020300c0440000800324141041d190400c043d4582c503118070307102d02c42d140c0004c682da036054860781c0081d01d03201d401d4203030550750030000044180448140b503070000640d401718411603034030700c03a000300c0e400994041c0881c0880d80302e064200d856001d090440c80a001003641011a140e11440c28007446850320743c19038400360500d03040450820b82c0c007400346500c0c821031000c18000d4203400801241c20080810f400541755460110481c15401a0070181030700034180400001445074070a1004100d078000c0b540014055650600d4407035021140c070009400464444041000e941030700060b10200360795040240c5055141c0e03803041c081d0322001d0421400300707200407a0341c7c095003400e1085c1006000c3c161080412240c010001620140c0754410050010b07441d098000707416501840140d0302070345443d80a008242c8112840281113034101c4028403002000303055080c10502c41c0e0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 896054415 1250 896053165 896053181
    0x20105070809060c0a110f01051e010f032a0503070b0d0f0b01021207030201180c090515060f0c0a05121905090607060b061c0b010306050603100e130503070303061404 73
    0x41e0103070301e0244111700c25079842250318440d621901a001c00183e21820a0041510419560700c0300c00d8601007e850020034000c040e01300d50762000c2d24081c04d10014403016201601102115000035640c5000081c1e0007000c4110b8114035054011003000160302c4a6003c058041c1c498049424400c0c010482081c50448410110050040e030008080a2050060f000240a40790091001080c03051a45a07040440c60500c5400c0300e011580b000c0c1085149240c0c8a842e801101c5068810304014821001443c54020040c007480e03903000000ba00744010f0020061083d240e40e1205c1512504a04440a107070240c11a1403001e044140803520014400d01c0750040f2280303c10000c0426041442c0c07034807208004c0980707941345a001a0100542010b0718425020201d1100c40000003003040c529010004050fa22650f110901803a018028490f44908484c0703c001904d01400542405a5644c41400a2030415010190203400009081020f055140e0460b00640b9004803056030203c00708030501089030b040d0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 896055665 1250 896054415 896054431
    0x2b03020f1506030a11131104260703031d0a151106101203090e1512070308090d170c0607030501060c030c0308070e042a050f0409020c1c02010507080906 67
    0x8645a0000507901420481300c3c03400513000c0e50100301b045410101711010303203901904451003c182006000c0307010018a5602c0001c041c3c1405400d032800000d940c80501c0d002c01000e000c00445003425500070760200b11641c540080601480300c3d542d1009800b0b00907620141400903400780c65248904400040d0340703000f14482c5002480d820b25141e0030f800e200c600c41700118100407401c040003400c2500c07508581d001d425424018911300029604108078050503001000003500612000c00214040000b941c0c501e0401b590905444003103454113602c50420740440041904e808101a60213010000d0050f111310300b59101004103903251503083e02e044d1444203000340041d40f0342c110400081e2140100076040070203420302c500c1c424980d00018098520f54180341100482e6001c04400740260303100003004918080c24241c0c03410304800e50081e03181c825030107070000e09a00058a0302c0100b1040000340809041c130b61681c844100c88000c000d0180c40c0542e0b07140001003480300400c42c9400d01041080c020701207 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 896056915 1250 896055665 896055673
    0x32705010f050702031509030c060a0b0f04090206160b010e010b07080d18211b1a100504050408070b070f0f0e01110d03060e01080f030304022b03020f150603 69
    0x4400868a50f880f00804030307014059010010002003100c01040d0240c2d10310340c09140c5403a2203c00c0a031400d00b0003020302e07041d6030404410300100c1c0c076080c840003401c6400390f038003080482c0f4500200b0018802c5001e200c00425440c2c1c2c0c29001d10055040e9681a00c1040840000c641d0740c600240406000783c10300504841800c2201c9800305080354000c0c80754201001c2c40480c1000d00d5200e07a14010840d4501e011480982e1600c1200283d00450051101e2220000114606200d4465883c2d03d415003410b100c1d5040b0210114500c54a40101d40004000080041c030491070300c1d01d0302c203407a500000d4046075420604c1000c42c1c9a1401035030601c01c0c0030100d07aa94105103c02410850b000301c100c07056203040c04181003e80d40040024031980141178025200030800a2801c1d081d419a203105901445568015200040d40e803000070040380c1d0800d40460f08031a44204c003540b80b003200440c1040c156100500c44416a0405030042804030810120f58107130341035030200c00c00556013804100e61081c5e05403c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 896058165 1250 896056915 896056937
    0x31103090603060d050a0203100c12150509070215190605010c0b0a0b120115030302060603030c06041b15030e060a091104052509081c0203180111030703270501 70
    0x18150b104c81c40c40c038015001c0350040e060b5500864180705c4682209940365031200d03c803500c213581141c11481024880c2004003c90009a05401070505007805064890b084000102d0340c01442042085292007141c5103c01c03c038201003007000c014410041340d5038500c50401d0400680c1c1e40c014034070492015008516284640d0350b600f03002c40104030015a0326070051494030b840c94035150900c94074145004041d0012855401c504019181500040c5501c0c40f03a8000c20040d2080c540105400750020740c042a000184075121660f0070072030040782c10488240d03580c107082603a00c41d41030b0030a50340161000c0a0366905e4540d004c4000030ba42107082c02514100031400c0f25049801c051340542e90004102c100150060010707218101c54500303a24a0710700140d0f0700b810138892010180b00b6500382c203402c2c0c145030612040c00c00020392680980d402d00c2c0b0705421002e01ca18000d9000d54110041c03000741c1419291384245616016005480566031500c4a14080903076441a044015084d015500c050311030a404071 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 896059415 1250 896058165 896058169
    0x1805060102030d0914030a09090614060d090309031a07110f0c06132105010c0302070309050d0c0b0c1006080109170a0e0301150914060108130201020a0c0e0403110309060306 76
    0x2107040310880e640c1070000d85401d40505c0c1440907045d0004a5501e540e0807510303000030701e01594580c1c2c11041d01c4625504111010760380360300403141038480442010440c0c0c40e080c28151856481540003425103003401400100480180c841648600301e1398650300c0c400415210110780d03030b07071a0361000c0c40c03240d015180074020791512001412594208404401a0f603485d00807944900105529608240c103408492200f00b120a014441045103203240440c244041c684008202c035141c0c0c8074007070040c000c64045109100240031020040d1440c819080d03500d45030078250540c1c58002415034501245400804a814601030144d1031032a40c0000c00703000146500d41e0300c1d1026511051030082440415006c2d11000d032400c1c040e00c19045812406c2e0030101e4034101c1400300b03030303603407000c0c40c07010070805504020060b03800c00d048a4206c1f04110110380441202c2c40143c1c503103500c00310041d003000e40301540060f010601c0d0741054480c40c825691110308640340da038440e989003d0031203020b41c08881070002503024 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 896060665 1250 896059415 896059421
    0xa1104020d0e01090c031403090d080c0102120907090b0a0b0406031e0e03090108010504150b03090307020a14010e10020c15040e1302040e0d020a02040c032003011805060102030d 78
    0x500c550110010782c5014051209007151303102ca00455105400c1c0c1810403d2120900820800000c814051480c14404500141c03201c40102070080040e80e010446640e184000d606840c10164050320640050504110456541c2a00e11804807914100000d421841c1400c42c030300000c440c0c18003016403c01c1c0c00c019003a00640080b03244001402d18a04034020350b11441e008000c1218802409956101c020800041003010160810741c011820032501017410b0f00007500100c02c5410510300d942d02c81d21405035003800e5104080c3d0180d40b22010060200d0194102e4100000285090302c03001c000a0305a403d002500c4500c492010258110381001180d40c1011814402605880c440301480d05450750036482c1090426546c00350b0700580700b41072804605040c415000800c00f10030007010103400555009580385820000240190b031569800384402e07000c0c0c4c00080c1c07200c64030342984400d25400c0700c2000f6250002d12480028007402480403203c680c180c41254042e241c103901562600b94000007540103 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 896061915 1250 896060665 896060677
    0x61509091a0f0906040e060f01030c0f15142a070501020c03071215020c0102030603161203050904090c0b21100312091e031a07020322050d03030c020f0a110402 70
    0x20b44903801b24040c01024400c041c4038a01c90b2124000e0741d41142000d810031160740c0c1081064039003e13a400c1c054040044031a041e45100303407405a50034808105940003034044d620092104014540000034546001503843e010104414100c48940b944e0350012650340076120402600368000c80300a2001156071400b05601038000d40c5842c21091402062500301c1c2d02400070410a65804010b10240349010301222240d400b11705002c880d00d074103004000d607000c40032540040900100280c0107210b41c480390040c080d10340d0482c0d43c2e0310486540d07603800c0b0155804609400c010405044000c10100518030f1074600a000b105010030385142503940d50001c002041c0c901c8814018000000652038440710609401036030040e030561a907614500d4107040030248080b02e00011541d100820281e0780e800800c1d1002010f900c1100c0e210803c5100c00d40180c0034250300215005085800328105060309a007044070889041d03130031034000d6190202d2464076941400070080004080f0200072030746160617009854 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 896063165 1250 896061915 896061919
    0xe090703081902120f070209100303050d0209040f020f04080706140307050f1605011b0503090c0f0112020304062009010e060d0f05040b0702010c080c09040c03061509091a0f0906 78
    0xe09042900c04c0320f00d4a400880601d000c0b03420001e9441d0460801320502c07908a410065891006403c0d0356001d061400f41480745079540ba404920818a940c49810205200551100441da81c1400c0c480502d4264414000c0a0303891144c040d0009903c2e2068242d40c2280f150208114119200c444c01214a0b602c814480c6840103414000005242c0222804410306417143c40000360b25022503000c0d02250f0b40d14080601401014400c201c102480441c10384050301c1c0803070b0f119407641c6203d001651a180850180f50040744040200010846e46074402ca0300c6040c040b5074100000041c090491052068a041c94009036070002d2010f801d082a40c00380c04000581c00e0041121942c6151100807034608036420b42d107440c8003505003c441c40e02031040310502505807400328401e24102990031454401d03210301c2c9000b55a81d0424418151280d80000098402c02d8518810705801001c02000e8079014003551042c1450003da103040c80ca807900360742c41c4949000d015403200004603030803c02102d0300240059 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 896064415 1250 896063165 896063173
    0x506010914240a270c02010c0203220e0a0209030c0f1305040809030d08180307020904080d09170712020d2a0f290103080409200f040e090703081902 65
    0x480c07960307100000c0c1c140c00d0045031184e003c1000107101c424180d59080c81d420055901d0300030040300440d8003008441040290600e02610b4140104101e6280f2420b0340c00341c80d5412100c0c050120b00010746d0014041a5402c400b1211803400381820401c48240703401d050342d4040c910152010188441d0307003049521500a5107001c2c14400c001010900717041c40c4017000c000103694602045a1003150b002d10b89041003012000750704141d05a400304034018006000640401070101740380480d80c81c1c58000141d01c540c4101e10495040c64804600b5868000c1042200c10101503519203042610001d003030840110350307603285404400d917050380103101d08002510121040c0e541c200080454078806031140b0310341c81001c80046c8605003024400d20382070a40301c4011002d107804d00400200e2441410750301a5003402500250941400100301e03044101c0e1084811000c50107d4241c54010101c00940704440c0088076038141580c50344422501d0342c506000040100e002031040310903403403100c141032401018600481e = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 896065665 1250 896064415 896064419
    0x801240c0c1503050c03041703040f05012a0f09150e03151902031e15101206171c1701140a06080f070516020d0506010914240a 56
    0x680422000c0c0c020b80c2c0302440d040c46050426605206040d4460406505107046003050751341d009100022008007030340b80c100032001c2010300c40c119000d0074082d13a01c24020071805c0d14028100c90707035003010400c030781c8400d2070f45185a10040c0030f43d00194003034003982e40b83c10080381000c2c504400c1600701c44191041002c2181444070781d403001c200e90060f03940e4274a4040078501d800c0d01e50041444180390008020360043c000d015411a050482c1e209151303550040641c2035560380041c05030004001403060340010b410003070405003a040003280040741a1a08188601500d84038001c0703a5050042101c0c0c07190f40070300100c05456104d001c044602c1d00c1e0314a841021000301042003203d200c1c080e0404000400844d110325500d1a0048411006028a003131140da60705d070000704ac41c5602c43c000c1286052041c0000c911030800c8880e1700262003154000c2a030502040242082503a40e602401915403980c46c2000c8101da00048411507403141070810304150603152421031042c80e5014154a060308568103e01c0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 896066915 1250 896065665 896065673
    0x1080c07140705040b1816170406060e070e24040b0a08091501180519020d240f0b0a0e130905070f0501050906071509030c03030605010801240c 63
    0x105001c0d40d40d8009021403030401d030030070045848400c0000e01c01c0281404a0101c9903503280b005d507101c0f94140c810703806000c040e18241c0744101c801c0f07031141100c040710041004001c2103134401001d03602101720024070b80d99a441e00303451132240800001e0348254000d54413036080303040720352019002c40b00e00000d41c181980c0740c7d09048290400800c9102040c814030401c0012981004082d40d8250300c0c402c0c00c00c0e15407600000001b1902c080d44450245612000000c016800c00107100d450116040e0b0110740d181c030602c08900090100b040b082995556a40380e00795041c8240702c0171800e07900c504101c0071605140004c8502c1980c417024910040c0140010001d2890f0350344525041c8150350218041260f1031fa038901b40d828051682c102d0607c2900b05c034000c8c0000c4c2d9001e0b0603078810640c1a140d40340d9640c42d40c1440c840703601c0001901028141082034540802d5030103060101e1442c8203403411b02c1081e460380010b4030b001c0000d0144a200618489006031200c1d2440c00c4841e8003901410100c0c40340c2e10340e0319 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 896068165 1250 896066915 896066933
    0xf0c0121240602060f0f04080406030e160b130504020304050312100816060324140f040609150b030f0703090f0c0f150c050c01050f040f08010603060b091501080c07 72
    0x80b0a030096040881004450b1108481055004401d83c040e1900ea1170030f40c0e2420924010790081c1c90826644248500500004100c00c1d101c1c20000808600c1e03da40e2514040c0c1107a000045100744060112030004550800d4004d030780c040c0e50310001a504254003030440d0141c40a00800084102c0d8003020f00264a55050118a0ba1416000c05540c03d840c01e0a5019090b43c11032042c0172505181d21304807040a01c48200c4603001d803000314444100e0114041300040d0070003000101a540540b80550000b19005a540080c00e9861207880c01101c080c0e583d0300341050360104494902842034190006440d0b20310940c001c1004900c10148480120505e0f04e40071000141c0f500300c41c0300d00354200018840d04030208815290210185001031500390903503185a02d446682101e141403101c04207018400038400c005807800b0f420071820071f6202640e1001301c180070704207900c426070f0450b2403c1c102100c28200508018400d00a0310a6002c0701140040116100302004112580c1c5034024000b80d000154000 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 896069415 1250 896068165 896068169
    0x31606090f38040b19140c130503150411120a0501090606150210021317010f0506152a01230903040f0b030613020c0f0c012124 56
    0x20310b15411903200c82030305056903080d80d001c11442c4182d0400c010006505021480e4401140d6100700ca90161103604000a0300e9080d00c1e0f504400361660410124210640141000600350a008201556164103141e19507800620101541c02e0404c005400305440d03840c004c1c0314441c090088180001403034031503814001d00780001c4840f6515800c5003010700005010318400392a0021140042880212011703654004220805203c0b40e004a1070400039160024800d00800c9129010301e8140c84081030f40d4020300c100203041000e5490305010a0442c2008084040c0314040007032514a01002088680381d9490703000c45945800c03000d103207001c44031413080c000c40b0b03440202511001c80d880107401c0803010342c040041400070755901c1032100300b0460b040c40103203500320b4a4103058696640c5450000c184040c5880c24620a0b05000140c0007104a04c0001d2a890740311403d0161003488003804011038002c5580c5014017503c2980c0040f45841c6009035101c507107031619003890405044003004050031200095 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 896070665 1250 896069415 896069453
    0x60201092306220c03110f0616150609061701200904200406110c15090d0f0c0f03050c12100e0a150e060f070c0b1909140d02031606090f 60
    0xa0401c8040c0e09001b00d103403508036002c40300c0d02d05009c0c1802d03030311074030001c4000e01405014050112543d2101150322850103480c142000b441140d0b102d4210304032000014408441d258a001c0f2071058841c1414140541c200317049030050b1500206500b0800680200c0c000ca018251446a13092001160107005100030441d0b034a464046c2e1501c01049410502c1c5007800314000c0400c003d40112141c400c101b15190442c00b1502c500000c034090070301d403414175003128009005100440b4041114100c1011820840e031141c0225951141080240251070346400f0300c039805903100f00c8510b4900000b41c0c002c0c0c41080c0360303003044400305646038480466048406070700c0c4070502d60f06c1c100b10b04000c0741030018a900c2880180d0250b56410001001000c0031162140076001d5842c2c8400300b5004d0000e520f4150280e611080b0034000d66069040007038881c0d8000c802000d6500c214506102800e00200988411060420824140703400c3c58072280d01a00040c03000700c1d0380399120030991340003c548940f003108010741 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 896071915 1250 896070665 896070683
    0xa02031309060f090b06040326211303090314030c01020f09090610120207080909070e040c0903020904060203090a050d020a0b0f0c07031215060201092306220c03 71
    0x40d2040c5030240a16580101c6240c60038030000b540e1036182c0000b00c4046903803001000030003d40c004c0a28000003007004c0c080d8007145000500301044800c48007020003143c005280b55405452f201c0c4010302041c03007130344014041001402c0c100007182e045004c3c0d004280040040d00d141c2918400d2240c04c85e07002c9401c3d90391011021880a0032800c00008140c2e0044042d02d54200701510101c0181440d0144000b00400d1500000c08200300141c20f001e8481920003d0203c3c0c0882c24113807806010b243c5143c040c107005500d4000d0380b074080d601c59104481126005460040c1946031611058043e501c003e050580a1082d40e900000141081002c242a00c2c031540c00707000c0e05141440d0558001ca8080c1056680711042400c0c8103100c5508011695a40d500d41811228641c0100da80700c0a000000c044904095520f24002750480d01074010340480e0303105e21030480c0080300b62102c00c200200c0d19000c14419900000004899183c2a101080e030140000e0100a1401103613070b5046109589030000c44880316 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 896073165 1250 896071915 896071919
    0x100b0424030e1f05070201020412060c1412092a01030e0c03030c100c020d0e040203060409020901090207150903051b0307080d060e0a0605030d0c020117070c140303040c0501050a0203130906 83
    0x141d4800c1d5508804a44000c0d0f1400c0d00c0c1002010b440d00d02441c0c0034126a58620400940324010a0000c19945480103280c1d11143b01030301200907000119a40403183c007074031180380b034102e024621590191179102600744081500341d004400800d00d2417440025803080d4001122580c1d01000a0b140055154005162501c00c1801c1581528214042e05095511071420041940d03040045400c81c01c0050b9801170b282d41d14140003402924015401075000307040030002084001d941d4004008040c0100e11500d8010b80008001c02104d80640010780040d105001840d43c1c4d5a01070403030045201032a00b02d03800c04001340c0310040654000f901c0000a075076980820440008003d6aa43d80a0811007080003090710b0080401e0300c030324240d040300c000c00a04040840c1168091141c6103054904105900c4091030540300107809800b0a50054039882c0039250f001c0701103400001181e11407903200754205912441d000055544e9049560024150f0201380040351100040d58080c0006210840c0042200c034 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 896074415 1250 896073165 896073223
    0x18150f090c0e071701030c09051e0403020d020d0c020a0e06032505011119060e190506060a0e310501020a0903021005041d040821100b0424030e 63
    0xd45514900e03c0405013080104042801c048000c8121011020045007036524800d04140039040600b200001500800c20b101c10b2550014800d55149180d400702c4100c5034100d1016a100c1c1c6072800001e5010000010a0000340100340e0110b4110340c000d012140f101150305400c80b01240702402980700358803c410200000c1d03034422014000081c010024003104580d4110402103240103800103001da41d11019801d0341c1d0303102040192207400400340c440e0b51207001c5207401a111041510000d00c524609100480d20450800b0038500401d0001c00700c0003510300011807070701202a00c5d1920003007407900d800315070b010480c00e00040ca400d12040e901c0d0f07030b1030f9415481001152155a818041041030030b202c144000d40341e00e07240340e06288500352101d801e0750b10b602c1c05804500c1480d01040303c0900c083c50081404d411400b00034040d81114080c4100192208a411b8007401180300d03000c1110b540789007502c0319160502084540707043c1c40c41d01164000f0480b08483c075004500514800d59031080d610300c11300b2 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 896075665 1250 896074415 896074427
    0x20d08160f050127020d03021603051c020f1504030504051c03120209030a02041d01060b18010c030509060d0615090302040b12210d1e18150f090c0e07 66
    0xe03009144034a10038030f04c0c280369484101c24020001e0003039402c4901541414000c02c2000081140e100400f0f10a54503454141d864103a200119801ca454404d82d140e640360010039403691950030030004182c08852038210413483c14000d03006400b80041003001158585416500404410900c2e42c1c1d81029501c600c0c00a2410b20060340303243c1040c0c4140040d42d050790300410140036581d0111004900d00070a54020b0040d119040544011907181c504d00003450f82a200141c0700c0b00e400c2d4001b07152201044030064030510301c5010001c001031810004007405141501c0545190150150005412501c0c1c0d1040130307d2070700001c2203401103402000b00b00304504c0c1c1405007024030601640d0141444905107031040d0f90328118048692140d009112061270046480d09442c0b0701c131401d088c24040c03407091101071690782c400d90a204481301c0c01c1001c1309004030034081c02790009a50060209124101c00c4140c9001080803030410310380513498044c058007142c810806000503044070501f1880d5420801c001400c0c07 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 896076915 1250 896075665 896075681
    0x30705040e13022d0402030f0f1e010e071806030203160509030303010501110f160e0105120c010305100e0a0507090503062a28080a0e0703020d08160f0501 68
    0x40a900c4140703210058407a149202003d55000e601d10b04d02d096406901c080e0b04601007041a08603201201300000c81d0001c100180c05110400e1910740f682c1c0700c80454600320000d0403580000c52208000400094071991080350b4010140e1030040e03144007849424120b008090f03402000000c0c0c01000740180d0b61400d05255070950380ca400e00134942400e0101081c0c8900051055605201900c10704440c5100144154507003015a5000e44001c101305560107007000d01240a80041e9060b0a8004140ca06000b00001300401a0300d000300108030ba2480110050300740103050110801003980002208086840313440c1c014020101c0114280c600180010101805680314a109910090500505941e400b00c00300390485445110b070090303080c2420f40701591284894101e115522120f81107408048048401104011030351103e09a4541490072026643d80e5050141c4039045054100010b140c1004c1c400480c2d403041e010b0900b41080da86403072050034800d6109603100f0011209010400100380320b1548 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 896078165 1250 896076915 896076931
    0x309030305060d031407020409020a080a0c0b0a02060420040f0b0310020f2508030103050c040f0c090e0a0e030a2109120c02041116051e03030705030c040902030705040e 74
    0xf0441d0042e20000c14841700200080720080b030010f0110159101c0350030521030140c020703190140d01a912181d103503030342078005002e965404003144049030300302280c411150303122906d030300a0a40d5107640c1c50b042c0e00c841e40c0074802c17525040100c40c00d40d61070f2500d01840b107201c810018002403480d80402850308110b59200c00d404500c1c41080603411008802050f141d61200381050f0b4981102004c140e04840c15090300c0261004038084000401c1041c0054400311904003980c082c0301c000c1e5440b500704140d0303010742d00303620100b0f20740c66091280b00e2240c80c0881d845203482c01c02203a0b20441408080c01c552040e1401e50026141a989561700c3c000d250b50380d00e60000401e010051340c7c506480b54102000b0f0140817404203d202900c050940d59140c003c03900c02d041c040d10441d91050303041141c10075002e0482c012a41805900718041c030804040300654002404e800207540745544da084101da080c1c2c030081048179104010301000c1504211440503500c03448254681507551420b003074403c032100741c009041403 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 896079415 1250 896078165 896078179
    0x108331f090e0907180605180a1a10050a031b030e160b0d050a140109150803070b06061c050411041b090612021c0917040806070e0d02060a030903030506 67
    0x1c08001000540c030411283e89811700c600032215244100d000e005642d02156100b500a19100ca001070b1401d0207601031142c0b84820042c0507080c454061a14000544590b4031241c2c110400d25850302550003042c1a00c00740c600000d62040f50608400a543c0103480000003d03138803050188846810405040100e10610110181518111050400d4811320000d12113a684860224582c0f14040c0c200c0303500080c212520f07040780d44e150b0746100002c0a00d4981c0b1002000410800070711400080120740041d03810080392810b550340c20703083c06282da0004a0074010000645400088000c061080501451041c00c940001589a4082005482007140c07500c6510507800040c2005a4000d10200b00700c0700f050a140b01107000001c0540b00a019411100c0714022003510280c801003041c0e0300c513511507840342904401541070000340581c580264010041a45e11400114417594000c0305070401785480104000380704041680400c4050300012381d0b960200ea01c40303000310200350301400b9241d03100809440176 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 896080665 1250 896079415 896079421
    0x1701050705072d080a2c06030f040212070314100209300d0503040203010f060b0f030a06090903170f07120504150504080403030e0108331f090e 63
    0x88030101000c00ca4040c0e060b0f414603180460400720758003003404d400014058030750714901d0020300240e003031952014241004e9240582ca40c0761400080e20305080140c50030f41155202018900326000142041e03a2003035030441d04a07070340c0303500b04103803000f461040007042070002030601843d1806041e030b00c45240c580d00610500e0416110b065400c00003032400f14031a92513191008980d050050030101d00c40c594090303400312000a039000002503014074800c0d00200120340c8000070410864489000d0310a02e40810021040c00d501c40001458221120020015034030743e03200701030400c86046000841c0400d998202601f2142040d510341648151096180b0219240514004001c2e49401407810701e800c0e60f4a003c9014804122102d80e4594500307603041081d030920b0309000380c5940040c402203002034104103042e210f030b500ca0704406010760f404c82e2003800c2e42c1000004080c0c4102c100203800104130700c60b0310741e0020343d0703160a180407250301010010314038501c805200801d05011038005010035400b032014 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 896081915 1250 896080665 896080673
    0x3180108150913080307020a030e04091e1403071a060307061209210519020f0c011209060606050d1a151b0304030b0114030105190e01020409020301170105070507 71
    0x10700e000450849441e80207076035201400d6001c2c8010040070380202400720820050b9a00044c81140490080d20b40ea46400741450402040d10340140c0014505901125508a40782c26404824003681c4148100d03d4200004101c00345150407101d03080e44c840c21400e02c0c254840110310300b40c0fa0811310540c042c10010341001005803144c01034405100d0002c1d55443e1460030b200c0b1030b450b803510407022040c00b40b90801035010001c1c1590000751503003c1c2e140310b8012440e001400003c400c00208144005484004035100c015941412800c2c8074640d01a241e00408002810610461000d40348940310562208203007100c49048400601203100e490404280701d20b00c3c1c0d038031650941c15001b00e03441d0441e034902c6016110184404412002181480040303404420045509904c50613134100317450080384c00f5411400c0600340d80040d42d102d10340d0100030611050826490304140450300c4a080090301c1e003a607a03a40b5000301e0348264800200022000126a03183d2001c2c010300ea08220145130442c1401e211381c403 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 896083165 1250 896081915 896081941
    0x1b03080d14070c170a091d16170712060b1b101505090903090d030302192f01020f0403061b03090816050a06050412030606020601120803060a09020a0203180108 70
    0x44089101440803802001840c891b502c0c420142807171400e8845100c0e040006500301c0c032400c1d01c10309010b4a05000904200388181c9511054504404122520f615059070a98486071001d241c1c1118944940f0042481c4540760020550f0b4080741d0b0524001c0e1450643c03031030410700c4110720048580d007011520390805a080083c0b50545a0469a54a171740c1c550444003491441070b24003d580151240c21481c09250b050f034083c2c8800d6000e41c03489805402100c50807125003c000308100184400d2090301913064800110804072040307944001440c0c140d940007a45a00d4000d98011540140c0f119911110b2a402c10421662401c0508040c0040c1e078156840c146c0702c0c01146000642400e40c0402c14091080030081c0402981d0400802c00c5942440d05220100d86d00c0c813150300000c21304042e40040c160b0710025149040b214900c0a0395054581c0e9603a0001c20751014044c1036004c488002c2c0464084820b100500c4003410781d4008550b640b04070b03603021280380780b1234800605003c107650411180c44445030b = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 896084415 1250 896083165 896083193
    0x6061002011509050a09020901080709060515040603050603070503120d0e0613030c030e040203010603021b150a150302090702010e120a120903020a060e03131406071b03080d14070c 79
    0x40100e40c0b030345e5000003640207201c142c601a5000780c4100000541080118051b001e55121400500080d42c03141e043c8444c0c4080083d2110800c642040100710301481f80d03220b95005840207050700c03056036071000028503100301c0f80008020210002180444144030348140c414428210010301554940141d031400300c60240030001d01804030418402c400c0610030710040c40445001801151256181c000041c000e400001c110fa01c20101c03680c85c461903250000700510300000140010010b076450000c0c03c0c014024104014900090012011005070341e4800400c0c030035240ca900028855003c4000300c0c0c50b14010320340c0042120303c10000040d409600c0015100c47d881031403400325294a841c0740891401d0b108003000ba10a84c54010110648507010008050440744183c0e60918561114101400c4488c890307202e6522080401144000031442c000b070381c440448040034075091964940328201d0603413120720800c450a5813120b03030070b039141e10014541d600a4414503043d41805800c1d41d8000b4009845 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 896085665 1250 896084415 896084429
    0x4030f02191a040206040f140a06080f0a2705010e01050f2e09020d0e0601050312031303020c1806011b081b03090409060b040c05130303140714060610020115 69
    0x2d1400102992a0482154000d11030781712150300a6543e61070a810001d90580f52501c07075021504009842481064443d004100740c0140710303000d440303000780f10006002c4204421950201c26240c98003101c28292241d14080c0200000b01d025650b0700c20301c600311900101601e1a1585450910030820800303142ea480c0c221580e03490000d101c040041c0502c1203180d6078000c400890001510220f1380115030010040020704500300d8a031a602c50040580315a1a4104809540b034241300082c0c0d00c1c42907043c6a40c1044c001d00664811a1043c404121240601628118800c00c000144051540d20140001d1380111301d10000211a040d80c0c1c51003840d202d0110124406069284a44c441400900440340c540400400c02c0040100d6441d081020f0312940b080e8510641c0b60411140405002d0021100b144c05442d82c3c03084800c0c1507540a80b00114800c9800f042100c0501100c000142d0440c0e54004140700d0400400d9a85440020801d0021803d080c80c0704590505040c00780142094003c40c00b6902c807 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 896086915 1250 896085665 896085713
    0x111f030209060706051312030203011a0d0207050d0504080c01030603030e310608060603030f040b0c0304050d0c08010e0c0102061812030f06010f05091f0c0b04030f0219 74
    0x1501e00026818054108040d1165283c0000d2180c03441000d040c00c1c660034814040745119070382c0d940080d01280024440c1d45d410760344114501d140001114014200d01c10a0140141001c1a03525410300e0b0030502c0c643e81c40869400a8103000d0200c0030442c208040d8804d28080c840282150b07002021401c07020740141c09261042070a180880c901e81c048080c45203121220f50750069546030910242106108440c524000e01020404500700401110030950802d565185854900940c444c0954040d16090949000034071000c60030307a84e282031b0b610b0424050780801200340e0038072101c1401c4940d000601c900c1e035800804040810390300031031020b500200344441c008110450681c024100030b540104100890030000400521410854130315004078000e03a07818181e02a0b0349800d03542440340c40b00c032541c070940b12000e981d800110003052104410452501d030f41c03010b8039681c402015460603030b0b044010075500401254901da0401c400c1d40782042c1d04210754029407568a401c00180e04049145c0c0d81245 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 896088165 1250 896086915 896086927
    0x2150f03042f041805060a020315150702060717030106021f15050f0a03050609070e090601030503040332010515010302120a0f0b060c0a17040b090405040302010b040c0c111f0302 78
    0x2041071464000107170440181c401034540190380000a6004072100b0000101291580c002030070310400c010800c3e030140e004c19241c1046a001c01040c2d0300009412640340b4020b40601071042410ba006d14024981a0010140c4683d400d107401580104549142c0c003080c50042103042403035203448402c04486040c0c40600d958511040071a208241c0e0b6080540548654420300220b29000502c0c481107030592000900d036904c2e580320741c1303854080a20019110340d005000900205111082c40c0d00c59581c1c8200080024180071445030340b0010b0404806c805035076a00c10498820f04000d041002280c0904e41146030042c0c140700440c00a40c003400c1095280c0e943e412000d4149042e40c0205d2207810300134030785a1100340090000b5600e002c0d402003100c100c48410410112028154140c40c191007203104024207200c410804e11006010050094085640b0360b079410485071258460310100e01c209070340d4100b0310b051504091028000b40341d6030074000c491039150202c4031100d14000207683c41461402595640d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 896089415 1250 896088165 896088191
    0xc06060d020a1e05100c2103140408030403020f030408120c2d070b0f27041b0306240f0c050106060504080d180b0702150f03042f04 58
    0x81000e4200540c082480c64440c03048120400c0f100d421207008690788484c05800703413001c9a09900c9083c0051600c12207550022100504c68502c022021780e1703140024000503a036100030380c440010355043d175103140d001041c4000c1c0740d81400841041a0301500031403400f450040c01c9903031075030000740c010743c10070b8042207114080b031003800b21902041101002c1400b2540206c2a0b15440313080241400e042c0c42038103800108030a0000a03038040d2080c0080c5942400c0109440340391508084515503000120340b04000841c0e9035a11401440200c10440414248400c03200a012180c00d60883c1e0700c40c91004415400d081021480c403001a4154648209030241000e400c1c1d50342c14180b0801007040d4208080415241e0340034025100700c912400896a4100e150b40e4103032850802420014000390040805114000d030304070007001c510b07202400350b012a800e0b54020383d0043c0c010850010701d244001051109005601e500c80a0b809840884c1e081c4802d003201008040c4c003290801c0d68003031900c80080c200e0314 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 896090665 1250 896089415 896089429
    0x105150409051015020a0206070209060303070204050a0b10020a021e0d0611030717060a091107080c07080f03130905072c131103180a1b0501090603020c06060d02 71
    0x60205800500260502116140d4203010900405110056030703515898400d1001440046c150740203050b05113440003580038440884001005650144000c01c0290300603241d40c41400d208105090740003072044180e008004417200946c0c81a0119030040d20240e004d42c0d1942107034140307000f1044081000c00031a4001c1006070350000c0026189030310b01000385035240c0344000158030611a41c1e690301b2250508481e460b039251001e03a131440c0c01c07035070b1003c051007842170550103000d0340030908540c1c2d410050b603a0b0b140301b11907008000c00c460540210740200071032242080016860700a2901a60a0a0300309000c0f4030008441d02c91107903415140c4000c01c61071030180292002ca221211400a003900600c4c500049680d0051001c1d802400620301c0c80c0810b00d50b511810203a83c843c100c299146803030300c1d01c444824141c0003c81100d03500419500d9000950506041a17410140e4414804d05528000015009885551194091500400ca011500070700400c045034094421616076002203034a00116120f = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 896091915 1250 896090665 896090669
    0x90f0f09070215010b210c0f040b0403022b060c17070201200913020d0e0a03020f060f060a05012304080c03010b1c0b0421120c021501051504 62
    0x310004080c004001d90101ea140d000d03c44030030701c00703000c0d0340d03a21000303910740c841d5109500007454404042010740380115070450300544c1c9a0b209504010304039001c4c8020b58400d90180040110002c1c0400031400c01c1d8a4040044108800001c00e00c01085042c0fa00c0c44140c00000b00b4181d030311607880b84924062a4001c60320310740100302120520342500042d00910201304403104001c810b805056200403010121840010040c2501c4d100490709121179004e900710030b458014030307501e403040314040650800c9079540c1c42c0d004e0350042c400458180001c80c01c1603005480444640d900354200200383d25207a51900803100c0a1a0040d8002441040400b28407810a41c0c080d21134030019000456170000507240b944803004400030003000c03901104000d500761840f007511004440080c03416000c1240c0061595103d4042c014090002c0c154918100259400c1e007541408140c2d181c2d0841c0420000d0300c508114040503000401d0240c4041174002d02401051140380c4c81a0009001c1441031a00d841c2a540 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 896093165 1250 896091915 896091919
    0x61b05030c1009050f0a051e0c0409080418050421112a010c1203050c0c030c0a0b011e090e031b070501110d0e3105090c0114090f0f 58
    0x160540c582c41034000a031503860010f82d00ca201d0030340c81d030080707002c0880c1400149074004c0007440b42c1590b2200c40040f00d08208115260350288050000f03250b101d50041107892880b5021080e503560400102c030703c503881c01294400981c5c0c40c1204020006180c0ca03a107102000c0a140301d07000139246500304036811445540d01d0f0341140103c02c2c0d00130042100000c2c18187c0c044803800c048060546a0045a08001070039000c0c013080786c04d64140642c180603910407600081c81d81890b52070250b1202c45d0302d2542c1d210031210003e0fa03200052000c180f001c0c070903005000d0007142e5400c039030b0788046420b0340070391a003540207141055a5900386076008a071b041040f207007680d401c010007150402000c065240c44080b14480c0d240425551540000d44207000308011021600640b114030f0203a1014081c0b00761443e4000300c4009100002003800c4440c0702541c8006008252500042600d00c1d00852030340c140b012081d101414005409140700c010350301003041c4c40e6249030070b8401c041040d03035140001344a401048141c5e6 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 896094415 1250 896093165 896093173
    0x22030602120a0b03120d0e0f0a08040812210601030b1203041401030e070611011d030720030705191a030a05060109050607020603091213051306061b05030c 68
    0x40440c01d52011018810020300404100b6400c0c40403d043e121003100441004001c030401c103146207590581d00010244815004507000b0041c01d4042c1c0f440e061b00740c80d0555035a03001080c20810010200301200c1103140c01440c06090000c4e520110420b010212100d14000d100440000c103c1c2e40300360f20002065100030014600c205010300b84036100d62042c01111104d1904d12003001582d402401014010041880103159861501340c007110354059a0806044035503c3c0c00050f10364145032407a16440d107004002a542d038486625081c0307141100590744004000d480301c0c400c40d182e500420340c030b13003190002c0c2c66820480312201000c455480560b0000d0307e12100600711303009000109400f40d0302c02d203003110b01000076031641401910240006c1c41503d52141c401c015000040c00c0540203990030000b11411204058140880d00d1201d4100c132200c40080342403160300304403918084141551003402d0308002c06c000741c2480c3c0010050500d5403c04498220013103000c10400004200315450101e41406503 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 896095665 1250 896094415 896094427
    0x80c09031f0e10060f060c1a041a100b0405151603020c09010e13061113083702060c030d051e07050a0804030e0a0f0909050106061422030602 62
    0x1040040c045450642c0151054911140c50350001d40300d45070036620100c0366081d56600d00f2908888048280504854485805040c0c2607000c5a0300c61080c080c52040501550101040c403040a10340c1004144400414140303804020303001404007110142c41056524041c0c0d400c83c141611032a200d0140902001240110541c09065010416441d20181220f41d810182d83c0c0c4c100c16038203400117544291000e000102d01c03d00080c0740f0f42c090660030902030021820300700b0000d6100c90341c2c0c2640d4004011900441d2a14002414401c26400009000107410480710030000c0200206005030a0003401130300009041100e506082068444810101006005500d8081805104440e00f29070100700084088085180d140c01a001e866840031590748441e9aa5100c1d20b08881a010f003d19450f084590040d021444020a8451001404840c035021034480a945450b508640b440d6200c0c1040040d00311910200002d00310458248160043c80f02c840001004a2544d8140715944002c00a034400030788 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 896096915 1250 896095665 896095723
    0x1090b0303092d03073218010611030a0c1205190c030311070218060a05040e1c0f020d0c030314011401120b011218050f06180d080c0903 60
    0xd00304800c03c200e04410203e402c4000781691080700d806100c8201010b01656a204140314400c440c26221800144003074200036004640d0070340ba040b06076005501c1c00001440026004103e001d40c1602e0f0310001c500e050071500b0020100f5481c0880142030580143c2040000c0b441101035176a88501d070206480c080e0728100380940034120441d022404641001190324185114400780d40001d138000c1c003c014204c072014040b155002c4010661640b262504a000c10141c442e40b1074424a041074100405048580784148110344404000000c07c10024101107030000b42c2c00718840341c0d40117480c01c02c1002e0700d03602c1c54150003800c1c2902d216505000c00320000560b502002c02c82807000c540a0f01c81103049000c02c40030405031482040c6081c04030b2205000c80d80d0b0741c0c0f00e82d80544e00c2d005e91103014002030344c0c0940d1500c6c14803c420784a5203042d8401814001e216205520002880321100010554600c1500014148120051409151441c08500900302d0b850600100b40f60012141d84814059501d204e = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 896098165 1250 896096915 896096959
    0x8040f0203013905031512010e01090218061f03060e040b160e060a05090111070b030402100e010c120309140303071215170a06020d05060418020901090b030309 70
    0x10901c410010754100e0007440380800400e002c2c00c10140d8800341745544d44100808640c0b40710324016040300b52070815182498082c40b480c080003420000108807984180100141d9100311040740c0306548202d8140002c955590f42c401c41050307100d103407004104914071402d8004009683c81000d0303405800301000100b0a0105505101c1ea190320070084c0100d10700407085841901c007031143d640150082110161490080010b0210000d05140401800c03011404240c101242c0b680201900130000c01444114504108003000c4807070140350008645401200080c00070b004210041c001102180785042d00611a8000d498481c0d0041203225070340100041040d40d0303034001c441c501c000400c452002103044002d800381f000118246810468264140100c21020340c1415241014500c9021089000240c0c0c900250001d50102c1e0000292072814100740019503181c080c03031030450708600d171030500140d0300c2551450644404a40c0016480c0b03002c0042803561084010b06a0300c001d440000c420f0b80301d2001 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 896099415 1250 896098165 896098211
    0x10507080703020a021e03211501080f07030908071a040b010f03020d0206030925050f040903052b1409160f0603050c0f040923130308040f020301 64
    0x1944452a5560300e1104808a004c1e0b0071040005810a50a401e910004000c04e521074140010a44e40392140c540707030b20203207034074a042c81d241c4540300c1c44100b0178000c1c1a17900c0940c00c20300c00e08110403039181442c0c0c10010100010400000d06684040c030505110600068030740e01c5902c586c00312072030403807602c25030116070f0110340480d0841d6900c00081401c0b4409814581126030107808069001d80c2d0b9030811100d0303040188000314503c920306180e02040c021445100b0a00b00c00d500744021542840e003031065407100c0950041c041d032b051080210000394014205c45c405405d1303001d081c2240010b410810305612080240f10203250918419100052140000c50300079203501c0c0403214090b0810780301903079881c41c920031907610307a0001c03c4c100300e8140247c000e507070702c01059089145002d41c5840800c01d1070700b16411012401d5070301c1c0b2400e0100003201da840c9d04107440460b038402e00d924000101c088110080c500007000c0100304000718041240c011840078000da4000c00900c40c0701c044224510f0705500d15 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 896100665 1250 896099415 896099417
    0x201061716050301150b03180610030b0f07090b0c01060b13090f0b01020c120109021518030625050906030a0902011b0b0103020d051c0203040528032402070302010507 73
    0x1c003600040501e014450208800d007031a000004c4540b5083c4805942c0e080107226003040042c2c02c040d170180c07681c07c1c007080d84100303681440010301a00754144088a06e200401c41d401c02c403000c909000704a071300800090f04450b00d20706401d5450b50714003138880c003426940d80440002000490f110203410100d406079401d44090000070800e0062010320001941c03140100c140c05a0041000503c00b0700740200003400310f5021100125085550f0b5022442c0c070381c20042c00400842c00401c0d00d11415162418a41d54010120014502d03030803c102110403500d40011001d841c076448500440b40c007030040054549400b0000e00da0b9442c1d00d014000744011b094031120490001e500c2d0302c40c80c0c585012551800c3e20b42c68001504038000d0b03095500f8805060700c0f4540642e014130498003241144181c010035010780c0e413080c0c1e019640342c2c0c3ca000c7c2030000303443d0010f640d0361503414001c1004401200203052101100d07080001141940304c554450703400500c010043d000704034000a400c605042e0150002d44c000d24103 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 896101915 1250 896100665 896100703
    0xf15051003060b030f18060708040c09150b031e1305010b0603040b0609071202070507080105060d020310330f0b0c0d030902062a0c03030703081602010617 68
    0x400d4012012070300c060103090402e080038004203002c0074411004550141070742499060fa0990a0f042d1450200d0440344180068070f4403003000100802d17030b04a03034001c2030500c10a00c03002d040829481e01d0000309000306001c142c404000104d072928416003041d101b440b82c80a108080c03c2120300e030185040080c80584041d0709003003080c252810a41c040b20700c540c0c0c12070350071350140c0c460700104514880041c6c0341d80100303c0d07030000c2030101002c07034402808030a01c01c40c010700c205864000d034103003515030040000e031085011071400380250706c1c04a02e0441d00003000000081801120019070044992107451441d02d24030305041600c840702410a4600355040035104200711a0354003c4c04080348035001c504655a00810b2655032514080e8000d150340070310091145062920700092b160480d1070503000000c3d80304007014006101c0505000c5011140020740165181c0324040d100508001e038041c10700c2005240c0c038079020300c2d00d074401e50090020b003110310411080f0410400c85c80355280c2e04a503642c0507445c0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 896103165 1250 896101915 896101939
    0xf08071b03050d23160203130e0f010806070c08130e10080f06040f03050702040902040f060e0108030c07421209120c020a0b0a0201020c0610030308190f1505 69
    0x789006504c5408001890800d02558440442102d580030741d01e50401548418003214541c000500c4084003d040303406190b200038604054180001e07007040c2c3c0003d2694000d1401d010f4200d900561114400f504001d08035a5054080405003124600d43d000d903494120400a02850100c00342080c811601c00c0c0045402d4000c001c0010340e1160000d40d07005007001954485000045e026070050000c46000510009940b8003540200381a140c9107003031890010398415080c440c0201c202c04031713409003003c00f0003107082c000d0700007400342c2c1c0e14042e010b60611040b000e02c0c100f00314001c0040c46c031015a01c000c401c00001051184585c1c45c1d031350500006020900e82160341c0d012804070720030581400e401917a03042c5802044041070310510b0310500c040ea003004e10307031501003521020900202640e844941c00142c0c0d44100c0c884c554109500a004000d004d08003213802c20110350b0088506400038107500035100c2860309031380a00c005000040407a40c00030b09041416204035440030641080307440540b094a4040b03 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 896104415 1250 896103165 896103191
    0x40506010e010e1311041a0a1a041e080f010c0e010503060d0602030a0b060c070f1a0708030c090d030314010503010603080d050c091518060a0f08071b03050d 69
    0x11007402001c0c0c510340140001581807096034104c40c3c900313018101060010f000403010400b9140071803070850325107051001c482ca075410325a2100e0024021020400300414502c4028945440f80b0310880080f915802c0c4142d00101d20f8414010050000c90b00311041a41640700c940c0c0a0700354030300001d010a400c0c20020145502600461b441003600400e0101c2c101255614180290009440c5a11280c1d40d100030305001c1d1240f0006021082e2102c00a12a4500d823900c40140a00141c11007510701c04c034029034410000c0c02e103055402080d0f202c0511a141c0d03540302884404ac1c0214420154030002280c01e110a140d019403048244480c8145242d00c540c0c2ca810505007a2156444010012074081200000c519851742c4202e4004603031140301468001840e0003d8400305001d1a00d051281000400000c540a84d1001c1c810703898040d00c0a83c02d081811030090900c07403448000c00c090040400c0010803592040d641c101c010328502648141410b89800e0090003070f04115035000d0854a002440d407242 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 896105665 1250 896104415 896104439
    0x50306150f010806060318011508062401090b030703090609060b010915020a1e1b08191208130c1502010b0a0e13061e0207030e010c032304031a04050601 67
    0x9603001501d206d1854403035851015001000c40e0840d03071207559810480b06121000c0d0811802401100c0041680c6c0c03d0040710841100c52400504c8981080b00400310031036604a1242c004640d400764000d901c951b10508254041c14008100404261034503d4034003c00c2450352000071180c0080c0d0f1840ca404d9101c1070440340500000c035420000da4001114980041c16021120303000d0b0400820621303a05010340d0720b00c902c01020340744002501d20000d0007405000d07400c0007059600520010240c003001416114000d42c8003042c06403070100705520001034244501400c00004a962106031782c0c040d141d45000c04560501c01f4480714005508003413034a481c03480d1424000741035030f200c1c040c4074465840e88200300300c244a900c101100c1c0380c0d03258503028014104021744d2902c0180f4071840580d40340001e290061010840c1c400f824184043c1023042400321394008520b400c1007804680c0007110105540000310b860003283e000034040b0206041080c40d03451030b000094000ca20a4044802d9642c0f555032549113 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 896106915 1250 896105665 896105671
    0x30e270907050f060a120c050301051f091406070c0b030a0b0405040c090c020f07030c060e03150601030203060402130803040303030b15070201141207020c10030b0102060408070c050306150f0108 85
    0x84800c807003c0e070400e42d1622000803c109401810450b2458141540d40c0c000d0f2020038140c03c010501c040010400c50400300322080c0103030144e0408401c0e000000030040c0034900346014a000f03015681c4125003d80d190102103c0e031043d0000c1240f28a10f070707110101d5140303510844011503220300780491410345003003d0094500032135000386004440c2e800c24480e40c1c010700103002c5d510114426180e110410080a21030320010b1401029802041410054041c00d0b042d104425207002e90300c8100c0c0c3d5400d8859844081e07030400d9003403801595945034100002d010b40034008001d64540741072075002440c60000001401168403949090003090684820064009140c451041d0804e60411080c0015803244030220b881d151080001d44c144450300c0c00c1049007003821112034001da0300a85035aa914036241803e2000c00501d031805010140c1c9600000751215405003005002610100c0c4001c02c00114518200180a01030111340d0356181c2821800d000b0385010b00c0f001c2c05100035451030729082d4403030500c0600c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 896108165 1250 896106915 896106919
    0x516111f030e0c0616050703140d020105011d04020f0a0b0c0f0d09030c030f06090618020f040203060a031e120f0f080c12130b0a0c0206060d0c12030e27090705 70
    0x208000c145001740c000c0c1c1c0700003141260f06000c0c85001100040045170b5407102c810980300106800081081c01908440c010707040244d4060002040c89518411a03003030301d0384aa41691282514201100490100e05294101511507070300441c2c503114240c4009205000342c11041e00316070f1980c4402c141507071090502d0001400e0102e00d28028004106116030380d044c458071074000000c0301891901e0720b038112060303640140400000341a0600540c40d0a84c496468950300300c1d400c41c51414030000003140091944401494851070460340744010714000001c142142d04140d40e0084140500c10082003002010108000300f03180942c410021440707007440a1207a4014070107549040a0003103000e000010051501c0f500305100440480080c0500003040d01401804101280c415540b80c1d0103414003100600c0b80b40140b00c8107504001050340e103031814048580c81001e0540d0702d212400c08940c491f200d90070150300683c0c2d0151045040c811101805079001e125500e01000d5144d0344802078444a981c07003060303 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 896109415 1250 896108165 896108167
    0x403020304031e0c090203090c010801080c120a060f060e0a0c0504260d08071b1709121b01110102191220070209160516111f030e0c06 59
    0x4400102000d203c24280c020419003400c0b0b10015039200c0c104100607400ca00059038020050010000080000000350242420042125810081403503618401c08000d41e101d00c250b001840000f94043c4a00103010390410f2060000c004008600c0c000303000e180c801e21120404803070004420503454030070000c3c4000d5542e0340910345490480d002269031403000122041c60313500740510a21a0f401c21010411400340e45a1500501d0982d070b026024032015002c91003901009440400041c002d00190300a502c1c1d070508450b2374140e04030100340c09045a1411840e1403140d51400c00c664458524080714a04090703032010310703446610050354241e010b00b500ea47d070100c0c0d00f040c82e0000140120001d40c0307144404000000c0c1070445c1c09a6001c51a07a102c4880794101c0002100030550400402645e404034011b41407184102c45403030020640d204811a483e1000d002049100030800265517001810b50010922056030609d821200007c60003011950301003858003002440c0c04101040c18189900002c01c3d0b9 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 896110665 1250 896109415 896109419
    0xe0a0905100b032e170f06010501020f2a030607030b040f0903080610021c050705190b0408030903070b250206060d02091b0a020a11010315090b0d05030a0c0201080f0403020304 77
    0xc1040410180d0b04d0344401e000034101203410406042044a400c01250040c08118400050744c1d0800d401030b00700504540280c00124000840081c1c01e880d01c0c183d11038072103102e0400c5040c180c2c40364506060715a042c010001840400c65140e08112803494048404000700c010203c6c807442120290040180890315080c00104c480c038108092103140c900704e00503545800102804008000c3d8401d480c1c0380400c5003c510305c01840420043c201c40e26006aa02007440e1441e502c55501000c0014030080c0300280010000d0a4a0801e0040c1e0f00c1d102d034440314680e402d003068903100e1b03018008500312100c01101d6617000b40d151480003e8039801010060003144561903983c0074000d200c2e40051000c004c204030701c0b0740c0305010211440180140c03001940500004600d62405c0e41d084000d901a40c1d0426040100e20346036400480740c20001c4442c8408001120382509000c100c0d4410381510127481800b02140c1c03003540e50f401400380305005100340c3c2c86044558030380d00740301c1c1480fa0070740340900140d000303000c2 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 896111915 1250 896110665 896110711
    0x9140f101a0409110a08160f0305061b070210050406030f06060806010309061805030307090b120115030e0706030f0b01110613022107181a09070e0a0905100b03 70
    0x120010303e074051641200140b8114010075540c9120781d000ea2004c2d44a002c04e108410781046069014000200b40d12100300c0c07440d140c560382d50074060522820312a02ca4082082c0500b004c01b00e624241d805080301c841c0101050014019411500c50b901c080380c208820900f02c1c19051050b881503032800c0d26801c034640c45000044000301603810080724840c3d640c203160032a00804443e90130700c01c0d00c00d038001c0da0f0b0303460000c0f0018407610007940040b00030281401903006509144802d917040d62100c201d450b140c0a94400120040c1061503845051070107040c001040d8183e05810042002c00c180038103010040340d00e00116400c1d000d036080007609030002e401017185c140c090b05030801110b000503d80340300c8240d20b00b03402c103000401c601c500d0040d910602080000366000c629001000704174000c02c20030043c0154094401402c541c189600c81c28000001401450180540091110002d807801480315220000c0d0340c000c20065615880060440034006244001c0301d0449200300000c50480c3d101059420f4 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 896113165 1250 896111915 896111921
    0x6080f070e0601030f020403080a18030c0303080c0d05090a1b030b01091113170d030b06120a0f0c050c06090c0d17120406090311030405010f110109140f101a04 70
    0x3119034100368481545d615005010b0000d40055401010b4040c3c1d1b58004400140001d5001c140e03d825041448200f000800d441002d60822a0380500703080302c0540e500b00030340e5294440d80c5000c40c2c43c01d1826040c00390170500082c0e01040e0b103100d90002000300060100228440150b440010031044440c801440a80519001b2450401449400705d08203810b015030b1050003945030b0403039000c00d01c100280fa007180c0303010003680d454907a01c6d0504026500304540440c0c45442040707403262100c4040f4020071030381b03855540000000403110008215000c141000102958029500e03000c242c8102004a00c40810108490440c000d008002c0c2d26088060764402d501f205500389c640c044402c00380450300302003080b900700700e219902c50b450000d9101c1c0380c1d14002d044124408c803040c1403039206000a00c003690300010307140080c072000c0c1040704071412003001c0e0501602c1c2040d80100380700d54444204000680c0051031110194001e0151500704070080f00c400200c56102c14004402c0e004851102c0d0702e07082541c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 896114415 1250 896113165 896113171
    0x9152306090a150c06050c040f0e060109090c090f080c01081303030209030a08030117010c08060d050705060a0201050714070812040f0606031101030c05090f090c0d0603050d0306080f070e 82
    0x504810750150780c40c42003586105000c403c100206142070a540100210303407145076488480702c8085400c2600f0312100d07802607072260281c030007111080c401140c400e0703000d811501d0040188640500107169061030040c00c00800d445040700703099044001080c8a20701040c0b01c1c1d21294107a485039160358401030414202c1402c4042036043c1b5900f0450320440c0c1d1001d0050400c02c0303008803000c5680c1d5140c00c3c040c0e40e03000c610408503081a4905181485455844520075800c000e08454510300301d40389003042420a10b99901041e070003500083c00840040d0103410282c440c1001e6125100440d01c80c04078805075220700100240814410401c410502c0300094105403c00e01138004036000520341c0c0d4840044404d160010303071b04031101c1100c0122941e0300d070240c0c4a80c981e491410a00384010301c00441c0b040150241c029203c0c0061070000391021036100c0a50f09100610402480080d07940c3c20990b13100d200092500300060b09090012901c114006802050580e04e0001410318030314040e80c2c80601ca00c09 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 896115665 1250 896114415 896114419
    0x50a024605160f120f0201120b06031303090806040c053708010b010201060b0715020f03070c020102150105100e1c050312060909030414010c0c0915230609 68
    0x49144a0100e4010481000346071000c0c100e0000142c00c050302104000341d15800102010f03504a84000020315010b5081700296081c00e001e103d100f10044d01b04081d00030703103024541001002c42001000f480844660000794040c5d02c80182198599042030388642c002c03035020b0014081da540030041c81c10031002c8100025505070b00c0401c00710111140d08065a16140b00b03203000d00c44e811061044150a201c0c25035115401d00082008a160121000543c010420050526170b4400315000882c415501180d043c21944110039940b481c04890160031008945010707030040c4a078095000e0056a080741c00c2c7e040e00d500070b103154001c0c40c2000b000c60300c214100b11210f4204145a40c1600820f0040d42600400d6214002071501c0340001c010001804800420041c070604090b020320981d218080121806d881114030b455840f450301c040140d9100d411010000c2c018040260001428103c42c0d11500c01200d502015503c0e10703645034440e8094a41007101201038801c20b84000c0c2c101d14042e0001d08540c000 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 896116915 1250 896115665 896115793
    0x3011406030105090106180314030a030e01060f061110020301030b010e0106140913060b0a0201092d03080417030412083d030f050105060109230603190507050a02 71
    0x2a0340e01d0a0414203002d04000c59944042042f550140c0c06005040000d05541c008102040c03406202c00040c01d89807090b441030001680c1e80040c5800f0a105d50100383c0340b901030030b643d6540c0d42d1809081c174100c00d100300400350602500125182c4d05c10306200c00c61108660003a41040041b0f0f0800081400030400094280d40c6c5900c0002c3c3e449200c4060a02040301d034000080c4842142005140303c00c8001c881d41c04054800c0002c03940e09180200c02c000d032a05858160b1070b660703492403c0c0d40c1200f604828040c4600000c000c020070400b482c0040500483d07155104802502d81d40c4141e0000700b003150f442c4a0044010a00c400040c0500380c8500541d0100d01c200c502040e81d07a1107040c0d0718150702405840c16511076081201e13958001140c40f00600702c0960902c19917a00340003810740003005030005445408004003141e4010102401d281c0304c040d05000c20031880c20f02050180c080c4d484800d52402600420700011448a20b015000e01c6060107909042e1034055024005456071504400c4800c031644 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 896118165 1250 896116915 896116919
    0x90902030a02092805030a0503122802070303060602031602040203060f1504060f0503010e010905060409211209020a1a07050d11060c07050d1809110301140603010509010618 76
    0x41c1e030840d0100c0344d2144030340b54000c1801450070303401e00346442d030032240c001e602045611000640006c101c401e134616a084201c0940c40c1d44104c00502d282d0101140c41c1d003100c5403414482400b5507401860114480d440401055950f040181c0e264001c482aa50305038401400d4540035040540045030f001d8002802034100d42082c500260200c9011031111411103c04a02071204039005551200c0c0a5460f060070b80c03e542c5084080d044092050190300201d40e1a040400e4050700d0341e8000c4040c070744d8404041c0c10f52082120b0700808614031141102c000540c6c55140309106001e91041516158020708000300080c1041e01070250091003c503503510141003048a14003080c401e008001014032551355010180765040745851034407001504603050a0b03001c00010300022000951284681480c1c100806406203030340c41c812901d8090351041701c2c0f05042c2420011080040401503050f15460500b5400d507015030400d12506010900445070010702031001030040c00d000d041c120810700940002220119 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 896119415 1250 896118165 896118169
    0x7030e0c040f0f1401140301060503061f0b16050105100b0f0304021504080709050702010b0d0303092a080709020a0c020d060204180902030114090c100504150e030f030a090902030a0209 81
    0xd0300c200c0d00313980c4090f9010014041e0a2821410300b08016088000f072140e03500306000603882d420060200340e500004034206011203a102c11000340249102440c0a40354a80d080e120b80f40160401d101f03c40f070754039040015001440c000040790944034607540300c0741403158800b10b84010f0344c03002e4002d81e449511071450300017840004000f840940f07203280c054425180b40004540a80d00041d110368296410a01290b0b56912030380301466007a074142c07801040ea000e81341040070021624a842080005521104980c80314800b090310040303902c80c900700c6484d1651100740404a0103079405c200c0004022120f01c40141c80e054200417902c9024a200500d8965070310444144110703400f600d440c29035104c0700c60b1710075840c00788540c024866041744021f0543c50f211240304e80743c0b494452003074468481446200c001500c036005640241c0800c000140c0c0030f140403040605107800c4015418828071440040780070441d80030060b0b444080650700d40e890b126040010040280d0030091a0360215a0709010519140d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 896120665 1250 896119415 896119421
    0xb090120330c04030b07020a02010507082104030203040611070b03011514040f050f1e01030f020903010905010b0a1203121d0d030c0915020604150b0a14010807030e0c040f0f 76
    0x300e011040300b50b542d61a518145400c500001e0503030082d034200501c541e0150340c00000706d8103216808801c46030340b0928118087c661840d00c8900d0145510080304000c01c0540000090080e6042c0d5180d91005424109155649441d50700031131201c3e40c02400100001500031b400e096640c5c000e0305211848088a40382d400c5150425803002c043d00c1184202000b0038140380086081000040e01c1d0340c0d2802000d10109102840302c0c0c641c0c1810540d5807000341e0341040c070340e0741651600140140248014140d07810224007070607008140e144030b04488040000c80b880b1038000040307541c5d4981c031440707907108002e5030410051146800040b00051b0040d2007082120051002d8032041085403400a460810340d60000c15502e0707213030401440303250001481e407202500010301b2684141d018070707007907803aa03849a080000360803100b160b2908895000350100e019580300302c2203524108282d94503e080c1c1d0b600c4ca0110155011000081520b80001d1400d00d45414aa00f1034111028274a07c04034210343d440d6515411 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 896121915 1250 896120665 896120671
    0xf0b06070c03110913031d180105040b1f08130b070f0f0521040206130f140616020f0103140a06080f06040b180c0a0b09012033 56
    0x7a84000c0c20a10400c00020340002e81c5002c1940d0700346180c07400724401d0710300036011071014040c0040d5201401c0e084d80310041c684e013910405010160b1440c00104131506140083c01003500c00d605120311103807982004039034828031300e500c0c980b5000304440b00c000c01d4416000162624580744c4d01d6040f5840461103030035000e8015411581d034006511100d40c001019501107103900410030800700b0003c403c00b14103000c01c034010309141d9240e0125481d00e10016080384240d50b10700306040c405000010745406024004800c0343c4162080341444901710040200303510801101d0308d01105100c01442c0036040000520000420604000449107480d410300c5c14440f5045412044058032482c1c28445010103000307042043c010200241228240fa0703503901e036072900040580b03442401104251089007805c01681905007809403008102680380c03000c1000b50b901a11000e030110302c030f0b80300b0605040711400c0c5096165440700050030110302c041100544450100d80d82c0002241c41880429848038200700082c0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 896123165 1250 896121915 896121923
    0x150901050d141903230d0c0e37150503090114152d100203071b0512030307120e0a060e0a210914120a1a010b041202040f0b0607 56
    0x12010300fa01c3c00920032501034041d0351030300e0348248941c10001c2400050b901c08403442c0d2408208800d402100320b43c4464000c0d00958040c10100d0320003211500348000c0d0381d000001510007044a01c8015184019481c0c80c03081030b01070044c214903c544244104091908405d080001041460302d140406800c0344003031754151125181100301c07108d24908040304a46810018084090403416080c500c01c8a203030300f81c0b410380a40e1001d030103108542c1c401c1c411030f00195400682c80080c03010329804407104114600a4900074668001c000c200c3d114001306403442aa1103654500ca1480c800c0300d5580035100c5240003070814800c41e2810f50000c2d84030300031000b80040c0b010090080e1401c5081c12840030000c130710075503d401c0c8003860040b2070603840103003401a91540100800f40d0300790140400c0c04031240c00d9442040e0b00440070b0303007400c010010507229244500035011a415980b14500d100280c42544144d101070911002044018241900032481e4290320480000d015262900460390725072006070125 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 896124415 1250 896123165 896123203
    0x204020c010c1b0f0b07050903060f011e03050c010c02040b10031b0c020a0311030312090c0f030d1205090106151e080601050307030f0f020c15150901050d14 69
    0x10640d81d1060b00b01c40e482c2848800303800f100080f0f4a410b1a050b0040002031301850656000039001809142216941c050141c200e41c4035181c200c06071003400000307000300a0f07000e900c524868400c2658501d0801529040b402030520104e100005480c00400403a0403a0003a444411694203551110303902c549035043c40d18007083d96400c407040074005810000c460000e02521404d18070140e100c1c1d070550015a60301091a10300300d45040002480e6006003041c10b484004c1110030044d6201d00840c0c03421050005a45107681d40c03841c9000c1503140e030000c54800000a0000c7c0c140d28110b2969002241c1110406000160150300d4851002c040008070600303201060210328041c00f041c20381040030101a5003840c0c004014144800020320610019000f802095102e45e0306081c150211b5000c803201440410045550364948810b0076190f46218034484100b607075490000d00b08d02001141800440c00040080102c0d17030a0004020300108250003d4559041e4201d501801030780400015041d0050b0710408 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 896125665 1250 896124415 896124431
    0x4020c071406041215090606380313060207050a0501140903090a05010e030f0a14120405031e0f0106090207061a0310020a1b0605040530030a06030204020c01 69
    0x2810601c1446504180108030401c01003103d402e41441550205510035641c0705c036126160120350181c010310b00050702d482c1c074040001895055500c2c151810003101c09005541b03403005011920b0302c103500c5020f613181d0703007080001031184013500c03000b10305062240500504014480e2280307498000c40210840380d40e9954508400300c07015040070391340c3c08400c85000f07502d0100303240c010421008045c1700762810301a41c520900b03c141e409120000009007500111a07403500241807110111104100046003405081e2201744600350302c10131901070381d9000d002000c01820a0942c0724134640400c2d121540390107400d28213189600300f03008540c020003c401b00076031250350509085049071182e18204090501c285d603140c400740c8003c2118504290742d0840181c0703984408500362031501302403134200003108885402c2810005036600850182e4081c500f229130303642419003100c0310340e158202d01425000b180c01c804059100000d0046034840e07030140300810529565800f1605a8000101c00211a5150131172 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 896126915 1250 896125665 896125679
    0xe0117090312161e03060e0403020109020405090703051908070803010f08010605090910050c0c07180e0708060f0c25200f1507051917030f16020c04020c07 68
    0x106802c03c0d02100d602d0101440c3e5003029101014002c625031001031144002c00e011802544400d00511040b9801411842d041c90001e0080c09000000ca20640c0307400d02141103003800003100f40a03070740c0c400f00500c0c0311441050162426101c00600700c0e504241000440006000400558001d10202800c004a2410041c0e524252001c503003000b4007514042d010001d44100000c2c602490040d0f00400050a8a8142c0c6543c494419a0505d52607817248810001d08d03101d00c0c150f10280140c1c100010071a04d036811092589030035891090344ca140d40800b01044261810385d59041e0084480c4d5503030341c51b0290004117030800340c031890301880c6400101c690b400240001d200c043c001400100d00a1206000b5072000911055150709036580501c8454102c4040c1c01003440c00c45d04120f0300300e002c8400c00c44500100c1a0310006e20801210701c403040c01450114003850380152401546919458440307076607600e24580410800116540c00c51095051491560721144018030f15680b070400a0303c2c610f030421503 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 896128165 1250 896126915 896126947
    0x6021c06030c031712060609131a0a05060f04062d05090111070e01090e011103040c1a1204140114091b01090b07060c0c171206010309050a030e01170903 67
    0x2482184d442e0040249001c41c03c17a255215a2120b400c0368459103840c02c85000c181d507d03c06e00c0405400d81e14080001040b02d00303180f03010b0f486010403a080ea080a4a071024006940112080d032032004c00184400c2c4400b502030b14541c1c3e80d00d4600741c580d64043c03241e07901d00380da022401074010000c918001540f072582d50380034914901260300000140b0300345181501c80031030300105205003103119546105001c04c0b40d60030740225201042040400e5100d082605002035444014481c0000c0c0c910419056425100c003202503514411260030343d49080d82d165240c0c9403201004c0402c2c500555030700c02c290300002c202801c03100e0140c0b14a40080c641803004004070303c5240c41400c411810f214282a080010340b001d0b004407490964800c0000c00c441c80219002d89910020078001010080c0b14054800e45186000251100080c80341040040740c80342d1006408035682408060959044020002c0120340601140b0641030341c1071400540b45801c03d5001e40740c0030401c0d44d012102e03030400a8030740c0035003289013 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 896129415 1250 896128165 896128193
    0x120307030c02180f220f140106080f0706090f0e0f04080405030102070f050c12030f0c0c060415020709050f0412020c1503010504061403100f020f07050f06010b031306021c06030c03 79
    0x5c074810642d491a210002c5040300c280d0024040034601d8003e488807802034000d000180240800c491a0411505807561581107601440d40061110303000042c6001c080070070341040b15208115500192144035603410840401001a1101c1c05c0400c4001a035403001d10090080a00440100340b1703091725840c1050400d201207420324400c1c0202086501d18800120459010b4091840c0450360b52100400c2c240c24a02c0c40c1500d69032048000c140001c450086002c81091010550b0030b64103007030307114151541121015200c03070004010303040000300050301c0d0001584000a00e40121092216080002000f89603242c100100d4850007000400543c03c3c14007a10340640900c6002d44485084280401d58884a0059948181d610b508002d080100d0340da0454440c6131042044a039514540e05105944406015400c013161085800024840c4420000d5a024466120049060070100e0700c4444c00b13500641080404042c2e0b0249281e41840035101d01c00c01588034000d01c600d43c038514285510010140 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 896130665 1250 896129415 896129461
    0x150418110301210515010f080d030c09140102011418060f0603030723030a05071e1218090504241424030a150b120307030c02180f 57
    0x41c0018820344100048018416000c00820210030501c0e06003a80340000c0181d03a01e6250644c0320000c50785190f4096184280c03445a811290709014400044088030030301045200000c00d0700308280403408180ca00020314440c14400880d124030341c01e400c0011260261170003803651451044023400d100090010903403096920103044201d10f80100401d440c0d1040c4080200b10703c1e076501c001500007820030f0080074220502c80031203443d4000e04002410b00c1e032060409071442c0c0c0742034007207403802002e07000500b6486901c02491001e24400703401c2900e4040d01004250840c0c85906000310740c214480c492140f0840c001c040b41d034980d0105010f07007401c80c5110301100a03107504003094407811516400f8511740000a802d460150003940300e0043d0355101c1d650b01c1c1c050f4540168803114060120582840343c542c0040d4004010901d00f110811030304c40d403080310401c01c540041c0aa100440e009481644409001410030100c0d4141044c4e0070300704110440d100082c203000d11051000302085c1d6041003c0c1941a = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 896131915 1250 896130665 896130667
    0x30106060504030b01060809100f0914240c09030a050115060203161e0f050a02011107050d06020c010b0a090e0709020405060d051906061707090308030a020915041811 73
    0xc42d25891090344c0e05000f204140300841001c00c070100400c200305189807070100701c208480c80ca0300500f54081d1403140002c1e5000c8044103442c81b034444d804035000310007406031f0840e842050510f01301183c0e490802022007580070801e2000c0e40340c40d10207011401c0100e02c0365000062131401e207a0b070181c0c40e002c150004802c40d030052080d0a0003040b1002114901c60708498894554050303042800403c17080c0540050252002c40c1d203150800ca40001d030340c1c030311b14400d0301d441440a01c40c0341c070603170b82e2050352044e65405000640c007400460540e81c000c041c008080e10000c03a00b4100c1202103148240710798428031100f545c50300440c800110078000440906100c1506601d0140340c040014170f80d004070703800030715401e907203070302151003040030b524425244c4522810500005544e050007401202c805101c184004c80c221000550f80b0707200b0480c04d41560b901c142c1003421a203c030004440250801c90b41c19030090b401d10050010b42031854003420003010401101c64113290446021000c0e030b0619042c0000c6240 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 896133165 1250 896131915 896131919
    0x7020706091206020d110c010e0105060612060f030a0506040302061308040b130e0915010e2a0c06010306050106030f0b010503010504020f1c020325020705010804020102010e1b030106060504 83
    0xd03010401c0c01c22030b688040601c040800a00301040203100380414140002d10b814103d040c0540c0b01400390464640c1c1000802c041c0c61f04140c0c1e6403d807074040752119442101003021604443e0a5088181c03c41c1e40a0102c403452114a8040f07440c044482c4000c0e035055109408110815070304002260b480621100070384500021aa41e5010601883c010300015510118810b100b0041000b10781e0700900107071005508906014291325110079003001c400d480c1650a81c0040782c5402e8030502180584010030700e9044a0018044060b03030b41c091810f00d14540581001824811201000418041c5003d100c000815502d80b0741e01070100c0c5c00d00100c1c100d2040c10300b4400d50840c1c0c0c1000c1030f241103c105a90161341e40c0c00c0159442007621031074010360403400c0a201151613903810b1b0f601541c07007600450401e115906d1110004c0840031034010007000180d121701030501095100c0c0800d5070304544103000115100814910980c1000d4003088130f2010a4800400f1105610342401900300500f41d81c100f55203818 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 896134415 1250 896133165 896133167
    0x11106180a080a17070e010f050c030d05180d0804020603040f0510051f060c05070b0307020106030c0b0309160807270203040b060a060f021005040317010b0d050606041d0a0605041e0507020706 84
    0xa80081c08c52010b1100108102407820000d0007150501d9090303100400c254a041500c000c0c0b00165121070f10000d202c1c40001c1001e04c1d00440c81c0310b00594000b4030301401d5503a695207503500c01c91140c10407510b6014a40a054080c1ca450180a000e003000034007e44010242c0040d110031410f49500c0a41003200300308040300401c00102d007800a0b15200110284c1d203036250f40059005d404c2c142e01c000c0c82581c5100001070190030303140c040d5004214442c2a06c09104004c802d50210202c2e6002d80307500c81e00610310411855180c1180d1001004000343c20081d071000e180d858104981040740d0541d82d100e00c0004020442c581250500068071140c00c0040d49541d041000a5075040c0145030702c000903a503840410240350003140d8120802d000da00d00d0590740d41e183c0000c120301b900001c50f641440317070134900494100e00d0050196001c1c0c0e004400c10500d03610280f8418100010060100c0340314030b680d442c5c0498180c4542c0a8004240240e04d0075240b00c0c06054008000c0702c000901e403000b1904006000d001d11 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 896135665 1250 896134415 896134427
    0x20403120503071b061503051005060306100e0402040b04020f03040b0c030c0409150f081e010912051305041508101b0c06020d05010611010b011106180a080a17070e01 73
    0x400700c02e01080f000c401c51505c0001032110040b009481c01d0b4180001040110000d81d00d105000c16650030b2116803142c200340740c5d0b60001039506030b0222652910601c00030080209803036000b0300080021600d801d20070f001c5070407070f4800c803101c6403800c038008100414002c440c115987c00c43e10398400186503140070840204c582c021405040b4103903844085e0b00030401c012200d89030143c68812040c0520b660340b064241d80e20104034110403111406441d042d05800e02c107100d1a8155078001410840005241d0b40c11580b5a0140d01e900020190312240803a1544891007180c03800106804c89000041c10f2405103440e1074001440055007a00b0b0590510303081c00104000c0c15500d04500b44180c45031054a00b140290080803d0525064600000001e10382d40c04040b103200c040c0703560020000d1207030900c0115480d015401011402c2c1d0322140101d40700703424a0741c0343d002c1000040d0a803a880c0800e0f55443c0d0054ac000d1101c1000070b803a000b4181c031030452800c8055081500d90603d10180b804240c000390070 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 896136915 1250 896135665 896135687
    0x1806050702042d090311030d090c0b03011a1b0706020304260a033618050f0f090a02031207061d19020a0e040302060403090803090108060f0303120a02040312050307 72
    0x1219251a8050109401b403405040e440ca400000d894542d04100d445000814061205480d01c2e1184040081c40103080022603043c0c9a0607460282c0009100c2c4403c3c8550b0302c440c0409005000011002d40c601d0b0040c44144080c10940c1d000e9562140350942803040000552040000030009500c5903022a0700000d101c0c40395039060800d01d0702010241d4040b04c00300c3c5502004188401840a00346482d8840220131040e6251800c08a6008001071050340071a041103880800321034511001c1385005042c070001c0c503404130001046402040455003c00e00344010000b0480c00003201094020802945000b8130000410000da4110700700c0d14030003c16030300ea00040b002d5560b903100320200c00c2992521510000604494042000c5c0d6007058a0000d64410b0100d60540008a40000118007024040100d031140141651100c0705500c0300e030304002545080c018000c1d03141c401046910804c82880400038400ca003c07540040c2c44901e03600f005040741c0c60010410080060030003c001d400c1e900280201a = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 896138165 1250 896136915 896137001
    0x3801170102091e061210060813050d08090709020a05040504110c03030c030a0605040507051e031b0c07031208090c22020d0f020f0a1b021807180605070204 68
    0x405040c9910204102c5e225800076030a40c40c0e45502001a12000c0114840499486540d0045580d50702481c10790f548040540c024616000403451300c2d255481059216000301e803c4c001d8680c060740c0d4900304c1c0100c1e4001d01204000c00c00c007042c104020300d040e20684d0030304400b2520407864281076007c0c1326100d00c80201440306c50100400807505185141e442003016000140c02044a030800707420180554100c0504144028002c3d01c44800e560642030a40b80180010f074081400c90340d50000002840c1c01c0306032a0200d900c0741080000c08203060b440f4030300400c4a0f03515101d1040c2068500ca50802410040712801200329844080761995440031400c03029440001c01601c03001088446000f529982d0704410095001242000d610913036000200102c1c200d40d11000220403000c030010f100701e440700d68040c0d400b220140b84070001d034840d000c0d842d5000403540342401420300c55200501c00c0fa201900200d002810110307050301141000c1c1302d01200b0010a1601038810008205881e9a0f00e008003040301c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 896139415 1250 896138165 896138209
    0x150304060b10030f05011a03041403071b0509070c0c05060d1103040f020a061d0607110a090b0414010311100504170618010e060412020709051815090307380117010209 73
    0x350034450900940d10465031100e103454460f822040540c40e4180303d4042c040c402c5940b8070208880d0d030300400c0480e48456004044080b0980f900c801c1205c150081c04480310041e031526030361602c00d000e07000111300c500e01c03e015441c002c0006006121a06145030000d0080c0710306e481040c2003138001c1c1410b075103010000300c0304690381d0310103440c04220000b10320014640000d240100442c00e042242c001c0524141d040d03504101c122400003200901d0b020a11000d01103800744024078030729061180700d01c50f001d841401c046240c160b4580d90220441c807009030b5140c4680105060103942040300c03c0025044110340001d0112500d1028000d4a84a002d40000c00e005410b5441c0fa00c014001d0040100604205d1307400c00c40c52a04250428101d800e03400152410f00410440b19410241c5101c0c440c000d0302042c00031404c20303440c2d81d10f1030142c282c000b041803400c0080700017118848094000101c2c4040c011092810b180d450070300c0e244120503244414a0160740144119070184d19489590054007100000c10 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 896140665 1250 896139415 896139443
    0x210301050d11040504050d110d0503190b030f030405100507020f010e031f02070c051207180603120e010f021c23030705070507050609150304060b10030f05011a0304 72
    0x30340490b96811500359002030600c020003083c0400443c04094180b05070311802810840c90080c00d0f110520030f00c105000c690180003003201d07102140d00d210403c4003280740014a80781e203c00000d203001c02e034000700c81e825400024248038900784140800704200039400e0042c20440380f94000340340300c180a1011070410000e4a850051a40c0400180c142101e4564564800003299011030010798098181034480d502d40304070000d1745042540030144c150389110b000e02551810040780300342000001504112090f22450b020010407209140c549840b49551294908660500005014140030305521020b64200310403484061500c1e00800d40c40e50301a18100f80c4800c0c1d0180e5203003e0910f0364000c000740041c003004020b40300c0d17000402800054055000c8596290f956010040c0600c52002e08e103412608d15000034989510f1640510740051203918041800e038045000b01300719003c69a41f20001944030000f00011505a11031305014044c0c4e0043c460742002c0054070b070b01e801e02c405000200350017680905 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 896141915 1250 896140665 896140673
    0x1707200603181005130203070812092707030c1b021f050d0903080603100b0619120926071703100b030c0a030f0e1c0c0204050a020c210301050d 63
    0x30f0900d0700c0d1007482c20802c40c01d119100300d900d4141030200701c5c017902c80c1050100340150001041c0400388001e404207403070a030390b0906112818044c00d400440c2040900d07800380035940e244c410710380309140381e41d0002030600d5001c200403c801c1ca000361145040041e184100b000d61110250b403850b45000c10004180e0f1001c940e0104e5052050b2500941e40601d00543e220825500036001400380c001141104d104c0715851029038111400c1300c0b0410340c041380c02c014204d000810318640c0d20016900342044442034811030300480959401320f404880f12691100700ca891360300c140080d032200140085a0b2400e04000b0b076900c80c0700702c03265000007907204004000142042895800100545a401e400c03649900f000b81c0019615040010b100d00070908010420f08000498420799000c00d40d03000c020300c08440603580c0082103859200e20941005002014500540c42e6401042e0140d0144000141d9400c0100306503420100c800c1036054040700b2191240b442080c0071419681519012039500b6142e003c0d602e0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 896143165 1250 896141915 896141923
    0x30203130b0109140612060f040201051c24050120030f0406020c18131713080f010f0c0c110d120206060906030d0f110a170720060318 59
    0x2000341480c041c100046016226600600c3c01c10b901d0070071980b100c0d1078201c10482c0d88000e09805021513803100000405403c161805030350840e0060500916140e162025a600b0310a401e105400d166120003a4002aa000c10340c0b96040d03008039245c00001a00300400240150a21101000d0007039544065422441003403045414521540b910281d543d5550000a0344a01c3c01f5820144036200600407411500d00b0050064810340104003143c1100780305a0310202402103608803051180c80c01d111000f0241900084440500300041c020700ca04030300415200c0c01d680802200c140d000d03041000b07844403a07030010908030080c0d51001c040000b41202c0400b15a040c09045400f8100031103080603403881c103401203210350050000780c441d00c42c0750b9070304003c1c940d0b9022034203181b4000840d640c00040d240c500c2603141000e0310704041c01b5945d9410343d946422500c0016074507192907128000602c0c43c10049881c0d560ac41c03c03040c0000380740741c50345098000b490a005c010300d08811035100490030000c0181c144 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 896144415 1250 896143165 896143201
    0x1e061e060f03010e071a13051002100e0c030115050906060a030906231b0d0c0c02090c040f1406041710091407090b0a0302041e0203041b06050a0807030203 68
    0x50020420f00050149042d5540034621a2a1030000000c5070303881b6030f036400c00c1252107420311541c2410711289404240804410003000080440c0030300a1a00c20304e90840c01ba0710002004140101090541c1000301400c480172440d0030070050801c04c008101c00d49032170f0000380c5c1c480d801321086500d6828200b029000380043c130703030003d02c2c0710b10304005d0816043c42121001d80203800d010300034045a903101c4a10b06040406a070301448140c05202828140030a9040030540c4182460801c00701a031540c00308042082c142e508050528000c80d0602c0394203035805a80300144066103003440080703074000104420384260301038412001c0c00c40880b035285042c20840c542e10b41c3c880810030130502c1813034141000c030709002c80724948060143e410005410130143c0100318010310b005115000442c555400c00006010004032084a580300100c18110408c040c405180302c0c6019034110311b1340000b041c004082e6000650040014840240b10b0200074171340c000d0302e060740000340741001641c070745850b020b2844540442d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 896145665 1250 896144415 896144419
    0x100c050d030207232503140c01020f1605061e070c050f041505090a0603051f050c070f0b0705041208040e010f05090408070201031b021e061e060f 64
    0x30500425100340e06074000e000d080d000c0d12000364100380380b10030b080c548042c40c641480a90300042c2290180c01d84100d0320503a0f94003003002e15481560b2a6900e00f080204410041615000744a10b00c2c05941c060052540f5078141d20003030042c80c1800c3e00882000e40c043e00800e4010030001c5214900300c000c920400d4141a001640d0503201c10251526804001c081e00815010301c600c81280c1f2458101400782285000402001100e044d04140501480c000010080504603844090001c01304d4024010850741051b0b460401d5203494078900300e01d0546c0c80141000c04041010003400c400b18060180303a903803040c5d00040399102d03621820f03c1124680a10380100260103034a191050800c000040104200c43c40842104a581e2340c131a1071101750b224920580c0d400000000008001030043d000030800c51744141400941764001200d00c440c1140c40d5088040540c0c0048000c0300400324442c41d180c551580c08004000c41d00d030505280707802c091468410280c0b0740b010320101d006a583c400145852100c0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 896146915 1250 896145665 896145673
    0x90a050f06030f04020f150c01060f060f0315030c0e0108060108190b0a090215280e12071d060f031c030b12030c061b0a050306010e190b03070329100c05 67
    0x54810a44182d44001c1603645990310f04ac0d40060ba40d90315100d00802c403000742c1c40d10125078074540c03415009420701000811501c00c240340d0100c0010711480d40c1e0800781c010000d031603100d503040c500d03403034540720042c0c00c814100d51240c1000800c448070010504030702035010345140001c1c0c54414a4070058512410000d50113000000840c16103550301d0041c0c120b04910018000c9405840c0c07e01028000d0504d60900014990145a42680c144140018070008922007146e680ca40e903107010b07011455650102d00503000707a40e410700605207040008035074045400c03006401c030120300c4020303040c5c4861000322040a05850304892040c0d6500c8022990b501c0d011001501d6070380398070848442c2c641d1412030f044185104140940c00c0004818401c0c0d448809868860038170b0340d1143c00040d02c0d4007000035071565000c2c0314806661800e44050100d10000c3c011548000c2d140c4c1810200039007503802100c14240e00b018000c80040848000100d803540e59042601c803109000812801110500c00001020b42a841 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 896148165 1250 896146915 896146939
    0x50c04060803220b0915040e04030c0c06050a09051210090f020114030702060403210216020103050c070f020d02030c09010f060e0a06120510150203090a050f06030f04020f 75
    0x20110060486004030201082c4074071243c2d1460084007224090f400d03503d2401d11a00003d030410154141001c914828401e0400c3c0d40c030020802d030324108031000c50000b000400c440d403c1000402c0d49002400460034111b0401c510120001c1280700d280c4100c5203d042c00c0140082c00c11014481c85484600d80b2b9010701c007036010b80c1031444143c20500c2040340061105010b0601602000040c3c0380240300a41c0502203076221520100c8083c140d14400000702418203c042d2200708980c401030224070b48820b4420144aa6030002404582c0c0040c50060343c01c0c800c001c00c900190004240c0c0c400b0a9045070042528480c500210741340c10b01c0f9002554110144000200d01040c03100018011255150303a20300160203140184481d0f035804c3d1103403201151005110000d80c81c040e81010340e10802c0b503072064003030b20f0740c0d64903a580150420440c5009a080014080305030700341600e250002e08001e0321000030113841c090100780107101c0103103400885110540072a0031541c0d0740c8005d080b4944003e121100000d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 896149415 1250 896148165 896148179
    0xc0304120c0602060112060e160608160e0114031906180c02030f0328060b04080c0f0a03020d06020c031305040b1801060f090b030c04150e030703020d050c0406 70
    0x1460240c0155004100010001002d600c00200c1c241a20b50302c040701c4841540507a501000b62058240101040c040d81d207078400b03c1606c10141c000205015a5420144d0034030580600c4211348051000b81008900d001c001043d980000c01d06041c55401c11002d43c0c1c83d500c9030080c540c0321115000030703840c0b181050400101e523032440403009a128140712081083e00c400c85400c0e030b900d104006194488500c1480040d4201143c401c3c103072142c0c219508590010640014a041250600d402c2a41303014008101402254030800c030300c3d00a6002621178101400301c00000540c10341440c480207100340080319001c030812a0a4040d9480c00c036000046036154144c3d512180750424203406407034000c0340741c000c44400314a802c0074aa0407007003581c2032810040c0d0800300100ca102030760300c803040c09000700c0d41c0000503120312a030015441140c1c90140c1c01e46840c1010191440064000309103c1005540d02005601c3d6a0205041041300e42c11140c0e0072a095007444c009040082c4038180c41e600034908440001c2036 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 896150665 1250 896149415 896149439
    0x16051c1806020106030c1401170c0c0717030415050408030d0c030b0f0a0605030903071a0414070f05010f0311070308041b06020703060902041b11010f0c050304060c03020c0304 77
    0xd91150009848200c1e01c852040703003250407600c000ba2410801080400c03210001d0b069503c01e00340107140603600000d801c0c10384c2c8400782c02950816204240001c607141ca8080c180100d0700640680710003003200613004102107540f4001d40c080c0b521a22100303604400030f5401041243d0081105005503510345a151070007400400c1070159240210b41014005802c5161061200e0400301380200003610b1141008411111034100405ca02c04903c0f08000c0f07035000c2781303c040fa4100300c0001c2c01d0794400a03140c01d183c48440c3c2400020200103e5214240038411580d040300182c09460f0203103090000760200d42011000f80184400c114451100051140203259001e0819481907000380d448804404004000d201d10342460b00c610300040e04640c40600004c1c1080d0041001e05000078008510a210095100fa02c0316100c40d61602084200c144803055110178051621800c1444004106224640c84081c10b00c0c40024801080d003603542240c0c2c1c21942c02981615a10705048080380d45580c1c03140064804 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 896151915 1250 896150665 896150687
    0x80604053d0e060d030e01031e092117280209030c0a050a050d110a08030a080a0504020f1215010803091206061c0f060c05070b160516051c 61
    0x114040100002c580141c4102c1d2550280f540070306160300e241615103080381c031202d0380750f600d0381010388801030020645a104075441000300b00800020314041d2901d8403240c4040c07600c98605d8444038100548450a8102c03104400d02006e1a0881034680e03100d00ea4003c0b400c03500081000804103645d64005036400e01e501810111205030f003210544640704040040b081620b224165020300540c000f8029800c04524900000b0300c02c907040703041d004410000454071131081d0800b00700c1d6800030909006165200d501c840d080203c0440401c91410282c000c1800000040f0f0250700071080ca0b41c654101c1981007001100d900e083d4541e0144550310b1f003403400e40ba0351001c4d03806445241082101d0f1440303140400c9540c02420b00a1003000c031640242d803a100040c090b00002e54030300075202d01e0100400d07540e000741041c3e051140d55240c0d039040b052820024418000d0000c0c11481032440d8018074030341c0c0140850346811403115080c1101c0c0c00da442d0040c0740900b01003000400000070041188296004220051 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 896153165 1250 896151915 896152021
    0x61406040b0307032105131401020d03050c18030c030f01050921041a13080106090f02070f020f1c0b011d07081f0306180c060e0108060405 61
    0x4000c025400c2096603c400c2400080c0c40700c0b0342d0820009500d40e010049102d0a207040c1070042c2400281102507008040d66841007140710f40101d60300e001c075039040c010183d9140c0c3d18181008503013883c01d908903031406800341c40310140e03400802c10542698100700c01202c26200804807014183c880c0c02c203501030407050724280d0291007035000d4040d01c200700040303003404a854641c105080c240340c004944100a0500450002e80c5000c101090701000d02101140141c0384d4100041380040c5401c0e1481c00319030f6200c80c1410218070601820000038500c02728040c0940e0101c5041000200010000f03600c10035007800ca1401d05241e4800e441000314400016040380c035100d80401c1762440070025041d01200032915480001d0381c0100140c0000b620b101c031015a800d80d80c8024040035117980e900012203c0c00c10141c2c030182544101282045200f8403041e01801540c98020060811800081c005c008081c0115110701e4503000000c2545102840d02c20017545001c00b092040380d40422010f50580740310490300 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 896154415 1250 896153165 896153171
    0x1020010f05010611150c0405120106051011060a0515060a02012309060c07080403080a0216140d02131404142a1011030a020706110a0f08031306140604 66
    0xf1658014103500c000b02c00104080d1050348010b08001c05c800c100100341d8441c00106000200d080d80702d410829001c608840e00004880b41024200004008400789240c00c00019400c146900040441d1540e0400300003e0045004e0f00c0751080e04850300300805401c2c0d040200030580b002580d505410000b07860011400b0340d809542102074041d44040d040700c0c01c001ca540301c0c0380880e032552003d8004191140c001d500050510ba185d031340740038856005480300706c010703031050703414503a00235074826120000d201440710b04810401c0d20012840a150088003c1e104000303116a0001d545e510384c020f5040400c1da0000c50000d403429203801d500307ca03941d04a008191142041e0051131a60144408900b444016460000d412001040041403010361b02e041017040004000c005403c00100040c06910740ca40e0042c1500301d04011005001c40e144c40901c0030242c0c4815400310100708441d084040e080d41190703599a590f0790380c039064030000e00d11f414010041840c06240d4801d5820003104107014002c00c0f5018 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 896155665 1250 896154415 896154419
    0x10c1e020a050a080c13090605040606063b0d020a090203100806060a0308250302100f1a01320405090a0516030c03110304050706030e0613021020010f0501 68
    0x303c6044a014069207a1650203024854040d16090807902c44490803440003140071030959581400340d413021340d4102c40c0e903901c0b0501401940e07006030030b299040c1540d82c0790601d01907101c0411850186500842c40d86552280300c843c3da45d4030750607a00034180d0b0f0040c0040888503580c40e00c01c0000d500845164100032546030010506900100b00c55021340d030020210781c1c0850860321030b00d18550010650b892043d82c142c0024162a1100081044441c002d402604400a0310312a41c800d9883c681514010709190000304000b00910b8600080c01c10006c0ca000c60080156822052354846107804412480c2c5d40d1041c41e01042545030024000e86070140c1d4a44903d44a18111205545040d10f9103040e21088516001405100f40d104074402e0b80749180c081101d058280c140c03c4141d00c10349060b81d140d0004001808025010b0003190020071442c00100214903041446000020340300c0402481446582490f4403164480d5a80d0070007680b03540781e01c90140a602640303c2c020403400380a0080b00d4200000 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 896156915 1250 896155665 896155669
    0xc0301090b180a1a0907090e060d0b010b0702032830081015020a1b05060f0c1e0a020405010602010b15030c0c060906040b010e071409010c1e020a05 65
    0x180322140b1040c091504160711100541e0b0094280c0715001c882d145102491070b0450390f54222014000c04c0c19071101c20080c1d041080200110000a0202d4003803000e0800550000381544411340c112401c00241c1a2074003018400607052002400340c04072681243e5200340035200c0101c200d20b00e61441050f8ac1c81c00764041c41e916032114000314119618285861141211440c001c000c815170000c44074075654180ca031583c440403800d551a000310401a1f200100d440200b240c10134070b0032050458894070084961619000a0992164160340c9911000110300160464801c02002d050444408812a4000216080241ea03140c890718140d1107030741001c000258490042c4203011818101400002c00450b50250854196001400003448108200a01c010504007408124028545c0d00041d0204d030070107082110b60405d041c0c0212001410740801c1c802000d40080c1140c3e5100400c1101c182c03170310701c500016260301d0351003000644070b26641d91104000004010012082600c04c81e07801192035140c1c41 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 896158165 1250 896156915 896156929
    0x70b070807020604030f03020a0c060c0512100803030601200109080702031e0607030b030a0b0718090e0a030807021606110d0311090d0c031b050109080a050705091e0c0301090b 77
    0x100174011a5007990540c4078540700e5001041004d800b814620004d40aa40ea407200726480709441070300040c40400c192400344012031034990442400d050b2000300360700704a0300648a20016111505012000348a00740d0180c900c0c0e00705149542c0080200006101410008042d41c040f640482c807a0040e1000b40703c0081a004140700180b112000400403660303008000e4009003549004a07604d807264603101070008a41001080c4640344954624255007a0700070380508948d803039040151380e03509020444008540c0011a03151064240c50401d02c81d4035102c0084e814101001d1818062050502c4013248058100700242d902c07030100b2044410100c40c8200841c1111040414500c400e5020800d02000340741c01d844491446000d03000050300244d80307503220300805006140d4844004100300c2e081240d90703042051000208000310141080b607042c0d41d103054417000c0501403180700b00020404100358000d0300c2c0c120055003040e1808155242440c82100349d140e04240305004c015401c0006098050030f04503 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 896159415 1250 896158165 896158171
    0xa030e01110a022205240d0305070605040807020d060516030612200303030a0b0315072102041e0306241505090a17010f0b0d02150708070b0708070206 66
    0x2e8070300c2040c00c3d0308000700480140c034a030400c1c0d41903000c1022090740314820b43e8000e90403c0f144007500c1884864191010070410510361040101016050100380c0007000c40f80000c4d4040c000058640c0d4a01c0d051503140103240001e508890840d4004003081080c0d40220702071b00103a0107201d581510250102c050324800e0051160340036205400600003401001000d50300f240b00505115200c0075100880e1458100300c0704006419101c1185031240d003801d0041c412400c004103000b03030f214a080500a03000d05a50f01c1c1054001045202d035018401c032640c10340d00900450101500700d1580c01d9481c1741c10030550300042e1119803514821008414030060b906422a0b51a00007100451400c5007080000d4408402d03130060050401208045070b9400c050360010341f08a0f50014400304000d110103085443c1400c00591a40c9810000011583d1305c0980c0b04007143c0c1221000b2800c2d405001d0804540a2050020403908001c207140d010040b400c5142031080d55140e94280c00c665031201d0813a0380310302c16 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 896160665 1250 896159415 896159447
    0x4051003080f09030d050406030c050901080c1b012c030405010e10020c0303042301110304050622030605090d0206061003230906010819020f0105031308030403020a030e01 75
    0x10a810400100c0c168050b14800c1c0781024054100f010700408a41042034803102000041c00000f001d00045405100343ca00100441c40d1407801e01c201c0900107480e01501800108400f00c010a4a08a00c5444500340c0f81520403c4c00074040c41c004012002c94100798407e94071620210b101400d58108400400e540c2269416959804609600707001d01150310500d02100c001c50080b0544485140c074104010300042035504101610f0b07440340c206070480080119082030400800302c0c0501d513010800030660f4140e03603044441135900c0e10700003400321440340301e03010041c420100c501d0700006021095005900c10081c51040c0c6981d12413540049032035000c1264119480000d502e840c150503446070703000ca401314001c21216401880000e0940080ca0381c1205c0c080403a6000b0300050022910611201d482d50309008a100c1041286d603001a0002e4a5840303040e04105000c8001a080c4002c2e03501c05146903040741c6581d9a80c2454200217460380c24490069001c41c080380400410f6500c50000d00b0710455003 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 896161915 1250 896160665 896160691
    0xf0f0c061812030c03030a060504140a020c010b120120070807110109030602131502120304060b030a170a080117060a0c050903150105180702071203020304120b150405 73
    0x6107490708640c100701c015801046400a51016000401c011304200390410020354480c50004620f00c159403090700f0682c091410414958a01e15982c0203064010711401d0300540ca03003030307040c504038014414a454154060b040864440e48124190301c5040f92069180c0280c100c01c042025060742480385000060031441308000305070100d003481440d49103020051420100680da05c1c2ca64400b40c2c0c1014510b111181d44841e401c00072040e03c0144d5401400440c009006002d04c00b070750740c103028000103102402c465102d005280050341c091040c500c1403580101d56a11025041005e01342030303002030b214000843c16601c000301c8c041928601a01c2030b051498010300c40c65541031101009461001d42150500000740040d030080d550900c507510300c04030001c050000030b41c034140400800241c4856034928244026040c412141c1e40860b0304001d840061315500300d003024515081740f8600c80e944c0a4828012489c40d18010405102151800343c16500e001c440044a40303801c10040701c1c03040d100c1401c81d0403 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 896163165 1250 896161915 896161927
    0xb100e0a080316080a0302040e0705090909071d100f0b210c09100309330905190f0515090105102d03061401051206062101020712020f0f0c06 62
    0x40d0020081c035800817a13103070150400b980ca400484500005541220200300045481c1600c0d041103699290302c60003000c001e0036200d184c407005060b602e030a6401468100a140000b0310b4042c200300a800003418080c1c2c1002c08550f49201e40e0711310760450900380c1da040098250f4054111a900c0c0014010180d279002c252030321003440c0070001082e0300843c03880c0c18503032200030100c041034850b101c01c6400c0c1d501e40403081e088100040f81c2c2c4509904444d04032281d5252101690110b0380001c1c010690101b040d40c6203007840d01038140b41c103ea2400000003041849030018045c40d0a01c0040c8450003501518002e00c841c6e00c0342c030690b1031007580b58061a289207640010160354510040ca00f01c6081c50004407842c643d40d180d40b2518103490004808a001000031030041005003071101950354240c0300360002d08400e00f0b1820000e64011a000821803020b901628031100014081d411583c15076804440103a904084180180d100c0310b48039000c4295018032040f0800159021070800754408000b051941340170 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 896164415 1250 896163165 896163173
    0x806011706070819050a200c01110301030f0204020703170c0702102c0103021c0207110a0e070f0e030d11060a020c0c061810120f0b100809010b100e0a080316 69
    0x101c4000d281b00d081e00d0301c9400011018000324401800c0210400d01e00d50380305038440e822829200c8203d032062050004000400c041100c2c0806400c5650381207802591340c1195050480340203080c140c03281d0180b0a52402c0c428440503100c02040000c0c404d55400715a84130715442643c501550300c40c038240c0c03c0c60400ca0740c5090303000000b03150035404050500505200c0060142140786180c604401e908550010b220703414445401c20800010300110744903140c69042c803000820541002e000c8030301703010602c400c00703c0140c0500019013050401508644100261a5004116240c4403070820014041c0001090134001c45000303e650562440c80145004880340c07081c001c2c0c5a100100c50100d83e65400c100782507a950303450410421200c00c0e683c002641d03219481200440f203040c510000214a0301c00315808507211003007010100b10fa54100400b180d680c610556024000901d101c56001c1c0c0003c603940565030704691640706650055030910f61064039088080d80d607118105840c003100e09a0100b400000f = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 896165665 1250 896164415 896164421
    0x40b121b070b090105010902040302010f080604111c1413171b100c0c020a05040504150f091b0317070305042105010f0506060a0c06060806011706070819 67
    0x41508000c0c1000055000c5400c040580c0280710200c60481c0d400d0103020b03151100340909400340c0302c100f4085180c81d103103500180c0300130001c0c0f030000144442034000034825502e03030b40080e11354080c00e810316a4a0080c0080050318107220016085140c0c41c10280340401703c1c45900b103d00c250b41c00310803600d0310848e9031112211100f284141074980c4204205842801c018207248010481407207004100041d5121700c42c1064940200110041100801825001d41da6810405044070016140083caa890381d040c21040399149921003920a410008044145840d03031f405240b00720300402d86541c502c01c105002d01050b00d114031018200d8902840707003501e1003592000811900b442418914070f815601c41802440350702c1404404034503c80b40ca044024001c080c0a1512010314001042146141503c0000c40c1e9000f52a0404208110b019115040001d240e202c1b001510480003168030035a514802100000100f080344042c60050780d01107480103009086060140a8466000c075155151201030001 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 896166915 1250 896165665 896165671
    0x121501270b0d09060c0806030601080a03390c05011709030307270f0e06040213060f050d140109180308010302010c032f240415090b0705130605040b12 66
    0x40640d0760b14440000440c00d00c545210040d003500c59041b03600e815400c150030400705a0100100c1c0d0064001d11340000d9000003c00c181ca15103407080100802c1481103440002c0046089000c080d0b144070540003802820b021801c2221000da0b9480000c1258400040311000c00350368904080c0d10030700c08a81002d02030b031040380490482e881c0f403131203654a2070340c0c0e02c080b0301140e407013003c0d61040750405205400f10081c00341c1d441501510294a410007074402000d6880e2544600410002d002d442000414442d07411206c00d020b950506104402148840031a0041c00707211742816145000f60380c2412143c1e80958a02164040d25804c03c81e078650340064980300440742e8120308000c1c90269440842001c0c90321107142485400e003201501c540c024810b860200049003003820000c200c68042d210104180009034403507849a4410300c10b0041000e40d8020f8021a000142003505440030000c01c544d004019040248000800c1208590750701c1c000c0e00c0512a500407099101410420303114141c5402c0d0300b0a070 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 896168165 1250 896166915 896166937
    0x40c0302091f0b0c120d1119090b0a050a140405041406120a02010c06090201090b070b070206090613170712110106090b010509040b1207080a0c080d0509090408121501270b 75
    0x8541c0f025502c491440d6110810006083c000300410308c1c0010351040360740c0050000203540924000c11600058010301484510400f00311031600301814074810b01c4244c400411001e00240704120040f80203180c5c01c4002c03903455025080360050a0440c0b400042c10700c1358240c0684070443d1260840d11964050110354609a042c082041c60010b510014200207051040c003806542c2c00c036080200c1c0080c14640080d00b850010741c001c06c08d0100303444082119002d69036002801e064100711000f40a14180100800500b004501141d00c00d029074204414500406d0ba0000800c0703a96215400030048079000307942140001c4040c42001524101548250b403520002800c1c80320100004041c01c2c50442c080d0000700943c1c000d41080d42c10008000007500180c45008084c0041070301000c0010311302c0c05074220243c800c6c191500401c0a0000c680212001020042e8034040c071880e0200e08400a81c150f04c0c9480c0c000760f00e80010038850300b4101180c0f440b0585484d228601145081c01c7e251158100382c001c1c0e0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 896169415 1250 896168165 896168171
    0x21040b0f07091a07030f030506090a0903031514031005010602100e0c0d200a150c020d1403130806161d090a0501080c120604020108040c0302091f0b0c120d 68
    0x803850054940f68a1089030002c00c101e80d955849142c003c0a1601081c01d9205160810781400b003503950722890706500040c441c0e00016100c685040450103040007030b80c031402400d000e01000c2030788404440954503100c001c0c2c3c1102e0902c0e41500d14141203500903c203071001a00031611203c005580e64003c82e0200054100716990440c3c06800150002110f0b42c044446182c00c0240c00e415101d019450350079004c0803589246440c1c90704aa00c00c00d4407002e15200204501c2c52007200c110354a201c10400d00c240c01101c280c9480c1e00c112001170351f03503010141c503480030400030303200280e000740c00200e1510443d42240121280404403c045c0c94420031601c0301c1d07042d42c41d0b080709445143c540402d110b2080007020808a099490064103a0520003400545da024210b5002189034000001501c4d5401030345c203103807007642c540d02d40c1455142e5010700c0d003009602911802c10700c0000311411111110b061400c01412070180e079100b0391204e4920600307070b6080590700107040c44404921120041c00011000e60404 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 896170665 1250 896169415 896169419
    0x2011404050d08270705130e060408030c041206021e2b0e010e011a030d0906230d0203041a130209040606050603010f0914070e0909010905010c0521040b0f0709 70
    0x10f01190008084140c81c5c0c0880d070200560311b00007150302c4010001c01c100700100ca032003144082d180c1c0350040c4054545800080403034540c0c40740b0400c4800a01d07645003d04250100c51500801940c004400304040018101c41c940c4800207240465031041c05912003c54503406030402d0300e000040e202d440040d11666860700ca90008400e01171180604220b10000440b07a000e46904681100c1045205009a100004449009420820800a640b01410502000c001c0b4a1026548410031990880e0704040890ac2050021035900510b005504c2440c41c0410341001c4a03a4040003070044445809984c000210724015003001c0a510b60098051080413807183c2d29880403038560391081e440040c1181d181c4c402009500d00b44d219002c80c2403d03415254411781080701300100402003c90b0194403030303d010404180f414809501514034268000f00900c000900d6580150803a044140c0c5c01e050310b02c8107000c05108440e8844403078422075018480190603200e070200760300300c42e04c02404030043c842c441c000 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 896171915 1250 896170665 896170711
    0x31704051e03010f2409050106090b0c010e15151f110127020a0603020a121d010f24151b050a0620031501080a0609140702011404050d08 60
    0x445c8108411581d44404100540030802c0d040840390340f202503401d15050061115541c0020340200701c031030300501c2d0b13038480104801d180c1c014001d0b01d44200715446224122107030110b004280510a860801c151035401c64950207000300481d81c14401a8180d00081c6a140305c9405140c1e55a07400d0003440001032611014000490125690380d03515560b00001100b100c05c5103001d000c1031002e4102890705500305041c3c1c2c08007400b40a0b8020140004a40381c240b800d04042580e009140f02d041680002c1c80034080c208000c034000c02155000c036a03000300c12280c8514030441001040202e40074040800c151446150080740e20808840078660100811008880490303810001c2801c5a0b01501c0001100100740040d01c3c01e15680111420310700c64140704002c01034100015800034540282803000c00f035a2140703041401400f003038000e060810300e003250b20390301e90100c3c11161380314078103d4008014003d480d900c03c541450701214018110340c0540010a6102d1240398500d030810008070385a8540b58100c20 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 896173165 1250 896171915 896171921
    0x120f24030718061205011a031612080705060709090e0708061f0b0f0d060e070f12150b0904050105030102090a14041e020d24140d06090507031704051e03010f 69
    0x4207944517919001d00f40715200702d51f40c181c0070520045000300300301e5224000da00041040f901c941062445102030000078800140c0031500026030260035100c071441d00c1c2c440507040740294011441402e10304025010881c00000d4518180e0351140d00800b1196248640519054000c1c1c020541d83e10032902d0010760391101d20041c2541c61042410f0705d4490000141420071200182d0002c100340100406012100f50045d00d911015003080c500307941c040401030300034405801c091700c2400c40c0c0c005111001410a0321440a0714411000700c0e014444d0780da076041007600f03034019000903950213145400204104031003001c1c41062004090710114105074029002d881d143e012101c2c03100190b80005815a408019204010114002c01904078061360f0008100307a00305100d014141c0c80540f0720311811117954580d076660004583c007040c00c1c01502000e2403c00d4584045100440300716060102e01e01032428150113a4095400141c961070008031920b110300d1000d0401c001d03040c0c040d5a5a002d900001e02140 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 896174415 1250 896173165 896173199
    0x6060409020a0c0b101d101e090e1209120c04020f0d0e0a03121d0304060c0311010c0f0e130f0e070618120206120f2403071806 56
    0x3c2c03560407881030107040c031420343c20300106011248403404505100b80c804a14040303e0203030403800c484403e551001da8070f0410400d660040c3d2017001380b13202c2d5580311000340c8400740e0a6030b042c3d4a007408aa8413a43d0100d42e50b244185520700d2400e800d0100c510903040100410b03015401c0302003103078074024070240403400300d0b0b10441e060766400000061508002c1907500444104290f0400140040419034800610088040d01c107541c00c1900c4400c400803603442506040c125102c3e40043e6a41c55954020240660344072131402c80204110146060100c0c03018441c4185e0901291a003c10360b107560b013001c46078108501005030380510b41a20b00685c1c0074452080000c0942a05000500380c0b21a120b8a850626264003500030007055070b000d43c403113490001c0b0710000c890500d00c6030b030000300861001504902a5140d4000d100810108102141420600550251890012541d2408007880801c101d880c4c041c92150340607130006400300000f04171580c1007214031002c3c0c8000155107440e600104101d15141e = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 896175665 1250 896174415 896174417
    0xc051518011a101205101403061b090307030b150324010303080c1204030c060501051915030e030a030501050103060e0402060a0e13020c01090c050f15070204090b010314070503070f0e06060409020a 86
    0x2204061144507604107401e1451f81007140140041c0c0380020349140590042010203441c0f030400b0500b01d40c0e0b9101000044040e50b480500194140303002060760001100203d255846031169500d5016a0421003100c0c3c541514400b40c46400d030b82c01c54a080c2c03001003002d000100518001c010b9a0f4034481d9403200280158865a50f0b01951a10703400c1c10300540b101a0003c601c030351f01c4003c2880c40d4110914051003212001c1c0308041c00741d04528002d41c020524400100100e0000244207904142d059102d40c0c143c41090b20304210309901c50300d00e01c07840c100494009410100400c04034294500959a090b46a507006206480380f0618001031400d0340c010000c04065691100a180300708003121502c0e1000c1c000507a041c20002c64660f00040c401040c007081d40d400f05100044078019500e882d0040124281c10680108030713541d41e4600240506c05d640107075441c601680e040401c0500d4040b40b010115034141e102c065140303041001c40c40030080d000d001c0662200d410000050300300400d0025003588495 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 896176915 1250 896175665 896175691
    0x5180c07020f090c031609122301021b070806061302090f060a18080604050723060712020d02120901034b02040b04150c051518011a101205 61
    0xc0091400112441502502c6c01c2c46807030382d400e000c50108952940c5809422280b040562030203064408018450700c11320b150381e03500001c3c0300c0c500308941c0b032100303150b00d00c10700200c3e0a03082d6542e4143c2d8807090141c0d8800c1c3c0c800900641d03900000c00f56005080501e8005048901d2408000d00003200d581c0f205110038003103440c0b0025a41015051600304005050b0300c000b40000703140c00e6442d2916040d050040203075000641d40900c201003400000040190700160403985c1d2000b090030450740b059421a41c0308010f100745414110072510100d95030010f03000c02401e05042c58602401074014080381214010094008150380c1c2804024503c00081c42c40001002c01e0360191808114403030609110171441c10740e004000c100003005400e012681107650a442c605039818980900b25142c2808107005859072045400501b1004451b0301d80900034012004118240c004140625084e5143d00d135000002182104640788141000300041d40140031500e84540140f0510800204480c001c0d80c42a03000780c8 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 896178165 1250 896176915 896176921
    0x150b0d11040b0901050a0501030c020319090e0601051617160609060b090907090228020114010f03050a0204180c0f0f0e090606130b0303120f0105180c07020f090c03 72
    0x182403242c4981c00c40181c030382c00c01d0703581404003080d042585881224100b6640f4888a40e5291003482a548400380207564034452440700c0c480100159618028007440d1203400e008220258000c0d1304840f484d40200d55a00103440c0302d078407004c080c55222200071142c04401c002c190700824200340804021482603500180143c01803d000045425225426001d9104103040c48800d0380002142d8080710700000c0e0169850a41c540750f002c6e41001c00c40c500349ca080070900115005c607010b40046002038402c00a0303d000340e82e07510040403007a00318070000e80590031125030140035052030340045038212100d01c404290300b42d1541e0b4403101c081569002240c12502950203002c0e441514140740000e0582c8181e400705420590882ca840b900c01601d56441034035480185410400d041e004a160300301e000f000da903103030040006c03103807803115084909001e5185041c001007214a07204030080400c40d81c42c0d1010340e00d41d4529032034101c180c0c03081c201139a019807a00d100c1140b9660340c1401c64070030b0510710b0302c00380c07282 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 896179415 1250 896178165 896178169
    0x80d0306031104180f02010c12051e040f0b250f030f0e1c020a03080315040b03010c2a0b0106090306050708070e060d111b1e0703150b0d11 61
    0x4101c2d485240709074108103880c07483d2019440b001140c1c980003200400c00180364401070703410030300350800180f03103030b00143c8074031047d40d081006880d415190b000c104110080d1122031071854415401445d080c100e888906000c10b44102d009002c09810f00e81d041010a544c08440301c01780188244d04543c5d1136010003410081644c0309864120448075410403440d00e40c01c00740081d030456045845010500c031a84080403c0d561650150001175402c5900b481da00c1c201845c2c001c81c4801c041c03030b903640101c3c03d001184280b17003014443c0c0c0c041d0141c1a9100e800e050140c4150fa100e4000380368400801100b40d021400219070408040e0380200030a0304c42c01035051035490310b41c0580c1c03402005c607024004004100250150452028000610f048070f1103940d5403611452200240103c05080c82940804943d11502404404450f10510610002c451140e00c0f80d140c1c001000c500140884003a400c0502c2c20000141c1c0c1500352241040191070215003001001c7c04101081060745054886c500d03920038001c401c0c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 896180665 1250 896179415 896179433
    0x105090a021309030806100e15030604060605071208190c030f050a0218060912030309010c0221040e0a0603050d0807030b0402070b0c0906091e01080f07080a09020a080d030603 77
    0xb520501e024400c600494401130f002c06001050b940c0192030f00400c0314055441760703c4800013100005c00200300348980580e504d5180d0001c6030294012031808002140541c0208240c0e2132059000d0507480300d07400155821903c0b841d015210801081003003022481000e12800380b604d1261287d0b40001d81a1420103c0d4425600b000e001c800d00248100b00303850b59081251001132441030107844659507044800041004038003011031a08413808040140310505a040d0400802041c1c181d00719008203c008000140e0201c856525940f5070600308400c20409040280203544150b0480001038025503944400b820203510350350000008100350200140c29030144161001040c041e181142440000c0d995111a104060052041c050000c1030340c45050740c0365001ca0f101c1d45000f4010004950580a000c00d1000c604040e10303010440110008407040d5411b02003a1044400790b45a040d584c480c1e0760740f04007e002201091747c12a0314440301041c0d1400400c0305482c00c4030300791350024a05145003040c2e111 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 896181915 1250 896180665 896180689
    0xc0705220c050301060c0f240e0c0306071b03020703020409030e1009080307080306060c010e0f010e010c3e03090a0f030507051201061503020913050103121d030105090a02 75
    0xc0c05010f2006000850740f0580140c0c1190b40030145179921060341c1030200d0001842e44034a004c40c01e581c1744210822045e908420003003030b019011212242084801c158844d481100c403100000c1c00040c8504240704801c4c606109103006c0d0040d114195120340110301500e00032207058012034082c4490308028104440c0e00703080c445113840c000e000703542850400703510707441100300240410b40040081042e564940f011103101780f4201c0020800b542c0802c5482d9200c0c000c184004016510b05007e049a0080c1802115021605562a400c2c1c00c0390341000314900f02c0e2401d100341c103009503d1b14200071b0408075503e452860381600c001103232240700c48010801c030544140c0102c0c1c02d02c84000c41c108001880082c1090980d10111601c0c0510030740c01c070665004050552100c0d800d9440c0c2035003109031503091390050071059800c0d10070a510450400281e8141d0300e080c0f20061614008203241091544101a095045035901502c070800c40c2c901d1001909641d401c4d110005070b41c2224135120110702c0c0141c59444 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 896183165 1250 896181915 896181917
    0xf0d1a100509070e060a05130503030c071d0108210c0d09080f0f03031b070c030606030209061f05031f14120f0a03032313021309080706020c0705220c 66
    0x7a4604a040801c0e41030046c04c1d20031043c0140030800e9205682003584020240c0340160441e601d1380882e081c80e81e52412680b191b40f019183d44050b1070851380401d000c09050307680348801081064982da0259110101109081e1101001484500ca0542c410b202c418031041e01591425880c0c3e0170a81098140540343c3c10b166038a50100f07040948503000402076a9010b6400c15204520b800400504e110300d00c140b040042c80000341c618040200011948a9001d4070f0094490030b07240c3da00d400904c503114038101c22042502802060303199916101d24011507011142031001100740400ad020307a2440038541d0028032020a030302030300000c0b9003480c1d44101952000c050080c1240717004588010744030546504060109074503140140c10310100c8100e009524080d00051440c40c1c90028102400b10a68103022403051100c070500301d540601c60f005c1d150650b9001071140d442c1600c5a030b64140254001285c4509501400c81d00141aa41d4400844410382080d00d502c415440e082511074100c2e045500160 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 896184415 1250 896183165 896183177
    0xb0102060901290a050a031401050a06060206040f0c09060f090c05042105150c03092109060d150605180405011a1c0507020c0406140f0d1a10050907 65
    0x3c2c40464203003250103109008480c0c611804604140401d848415580029400c86041100003041081c825072050741d00503410b000700120707101c40c0c03210401e44c4c03c10311401d4010b03440000401d0101c0c032100004409107106005d9852010396a25030181901c0d02d50b03112520398444480100f001c071405006101340c00000340741003858a414a603a4130b200706040c3e00f000c01c1d110008111807081207410015175490f45000940c450013841c240c24002d1032a1700c1100c09078002e015594101e08110001c00544589180e83c01e543c9003000103100601220b41c000b5090149803e484560f0b1014008840c00d910000d441c65594441d9220602410f4070301c01421440726078051807a00004204903084400c041c00d14505041026a441d211500348207000300b0720b0074035510700510740428004140e400240a0012020035281030081d2666031000140e94101c1201e25600001488000825803400005400e840c070b1044400c102407aa441c4030703e0307d095004841103a0f0f060300340102400b962610340c1c00f0560121240c0707040 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 896185665 1250 896184415 896184431
    0xc11010f020c071503111b2a22050108070303080c0304020a03020402071b0602030d0e0120090616060203011d090a14070b0304060f110a02031c18060b0102060901 71
    0x2c1695501c80b8410400c008103040900c203803052207074102c8550b04c00e5202c0d103d61039884480d0300d60500706034400c60300d903180301302c0c04038405001c070084450074040c140041881c05442e84000340640060301c500a0324000c006160310031031f03620151050300e01800e4410020180c950030f61a010300b42c0c81c0c011f07040d0341544100740200320041e80c801c60440141c940c10303680907071146c8052400030100c0301400002d000c1030382c40c1800821103a070f001000c0c2c4207681c801402442a458103003441401c0751240c0d03500880380c142600007403d016041c000100300c001c4c03001e81168601400709650b40f0a80510090840c7c00580000041004c0407a4580c201003d8140811080540c10400009a61104031023030081c0b40d6a030aa4a4010400d070601c1650b004160300c0f02c0d10b40e80c03803a0911f01200140030408511f4201880c2a1500340800c040d80e042e2800c24825400441c030300000c20b14604001286011011600c41d02c410000b80b40d00e4440900c03030600c40c030600011515990110000e0b0800c90001c10803007c981c0750600c0c0b = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 896186915 1250 896185665 896185687
    0x20c01140702060a050f0d0c0305070903030e0613270f0204080604031110020703020303040c091506050310050a031a090c01120e070509040c09050601080601090603020901120c11010f02 81
    0x494280740e90440d5910f136500b04848041d20103015017600d800c1d140402240c100d5180341180c1103401c505805036004c0004d962000c0c000e8900340b242c1d00018002403109011000c15080c44402080e1001401c4404007203290394103081c0c41318130703510b034000c00d44140180001068014903028072b60f18040007400540c1480c0c04c00500743d03a81d40c0001d00150411145007030003400380b04140304403000b25619210944da80c21280c103010b503496000b07450840d0040d46a050004040203c1c0c802d10005901c04c0d441e011101c1d2910708202c50640010b17141c00419070301c01100141130b81c1c0d4244c2c1c0c00001c5220b021443d000a4002c5940d1141d40c5000b840482140c20200c00600d113a030f401181d266044008600005070055140441843d040454005c0d54009040d01d0600041c003460013894421519000000e00031070343c4150046628203001e60304140880c0e10b1103003c0c41f40d070703010390094900c104062400c600b00d4030010030040150303030040f0861008035840e031180302c000700d400f80188010385020314401c5d46840d8420308 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 896188165 1250 896186915 896186917
    0xa120c03050f1b01061509050f0609060a030b1c05010f1407030207060204050a090617030720180a0c11010203010305070e0613020408010b13050f0115020a0b1501020c0114 75
    0x80c80002c01d00001403180103284103045a00640c2c040c1c000810165131034401c1090280700140104012810b206000105803170706502c5030600d184040e29603810105c0c0201840180e402000101080c1602c882c00d201c1140c9458070580015060300b0110b010080c6a814442d0840b4841070740781108074203101d64012811100d05460381c1001d0185001a40d401d1141415002805143c01043d03000c0509400000c5200d4181c0140302603a80258a80c03140a40b0014038035621f10a04500400080541998400c00b60302c21840c20346010b0050010818401000d1407000c552004483d44200a65142c90b0300007410362102c003641054000c03200031840c6505644a90303554440c2c91007880c4141c20075a00081003521003c2c09001031903200308095490760b840d205000d0103084580d0825000b000c2c000c040031000d095500880307016007144111821585d0030030140c40c04403026992658154403441c2c251200050055004034841c01c500041d03e5004009000020b00306240c004949040004d1007075000e40e1144010 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 896189415 1250 896188165 896188177
    0x609030d08060a0816031a1314121201060e0901060909020306120a14010c020706081902120703090b0a0501180509031c0b031213091a040c0804032d08040f020d050a120c0305 76
    0x9880c049c181c030509042c4502d4108116002918404041821301998010028642c140c9080380c442685003d20b1005010040009204401c0018040c5404101d0992a50300035904408007418405d01c91400c0b00a013450440800012108441150354501c091242841034940840c1ca0344081c0c20f026280500050241c0750103800000b400050050a070020750081d070444440c0c0d555601c0f8442d0743e20f0400c9000c0c00070504800144c0300030b500c01c8001101843c0381d02c1a281a1003840e0100da4181070400240001403100604e0040c1d148410080740280b4480c069100d04a80301001c00419265120350a050802c41401050500460240071803103100d0301003282401900c0740d0311000503940d80c2511403071007000d0507116172031b41080c0390410f03200101d6800010b0603c1b0314080d0b259074222542c844d100e401c00d00d1303080d000803003403051704042150410710070710019400901490513039418505c0360300001c000e104007403401c642c0b03540a002103008005110380302d0b110000c01400c00840c199010b480c0901184902 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 896190665 1250 896189415 896189423
    0x203090f031b09091608060a05010b03071b0311010f02092b120e09010609031b03050c0409021302030906010e2503050705070c09020d06050609030d08060a0816031a13 73
    0x40c400103452072410820058940b0505411700d5103990380c1d8580d651100d6054404a041d40d08000005c0340074203852089138000d04035036450300089203041c002004990300281d405ca0412071003205540000320240100086400404001070350f403081e10f420407a01881000d9104425003040e17401c001904440d012105403141c1040c5131050703203054040215a91040501a284e0200980e000841d01a511003058015280b007070141801c407001c4228025095907640c40300400301d41c06041c40070a80d04003500300022491028141c4500f5a040c011804181d1f001150749001550003e401004240d0358030f038140750000c450151150615003085600481902031401071014180c0b0703803012031211480784040b01c40041d0060702c0101c4503a200c0c030140c0302a500401c0440459800c0800c08295840d1600484034401030040080050300c298441c180c4401c1c00c000d1a039a40301440040000e0f4110044c026402c104505528648181d41545441c00620040301c807502c40d050030000800403041000340c20340b00300b0307508 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 896191915 1250 896190665 896190679
    0x1315020f010e1504020604090c031a042a030e0304031a010f0605040b0f1603091e0b0717090a15091706040b090f030a020a0b0106031509050c0f0a0203090f031b 70
    0x11400403071b00521881d40300082241c039044009509951590200944910107550361040c140d6000c2000266040040402e450b9859884580018542c1040c2603041c640305040101c2d6110490924a00715001a401600c02c00302c0d04100408849650380342601411041101c0343d002030402500525078003840c0038032040c0760340020b80c0b4100940018242d44140c0c50201103003580740c0d00b40c90010320804480c824003c00a000c510101846d850a843c4071060b0780340b000d02d1070706010307268841c2e08625012500e0507050510400245120340c442091000160004c0c01c080440449400d42c002e040c0c00300c0360712040403c007503561003410303108010590765001a040303007148850b070700c1d6481414101403003a002c040f210b100006a0a0310315030040354910085000741000c007800c0c1c0e6038400650541c0e8070b09011309000030a41c00188003510040d8031070742d0814580c407902170400b061001c012500c0d41c05808003001580c004a4004118600b80041815409081d000340009820164480441c0e00405050605c9020 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 896193165 1250 896191915 896191921
    0x161506141009120f050715030e120a02280203030316090e04020d030507032f0c1c0f0318090203060306090d080720070b070b100305211315020f010e15 66
    0x1c01046074001400d15010030380c00c40c4000c7d01c1d0190040042462a100f28085d00c1683c2c800c0407030801c184c07092022241c001e040111203541680c10052900342401c0c0060240c5044180942c0341003000e10300ca540c2000710440b0302c0722441c0c0b0103030407002694070401c15090321108000058450781e20b0f486031541d040c10005d458080500e000d4800e100480d44070b00c0c07000d080d00b40420010030455019150101200241d5400001d40802e00c02c03040404c403608110305080ea100d00d000100745022107820140689041c2102188000807049507080030b50100031840d4000c028090240f42c103004140d00007500b80000c0c20884078036a4090041c0500030000e070140b04100310b0181da074911540c07500c41a150500b09691140785c0b1034922100e2600310080c151020009040002c50f5001c90104107010741e40c0000c02004401c4801d1462000100110b1030483c48160a2044510b2010b0070010380000c2c18880505103044104840001d280c1076118250140302c1c0c0c14102c1200340c3c6400411034071000010482d520090f07507 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 896194415 1250 896193165 896193173
    0x1404050a212114070513050108010f0b0a091502070905060f090415020d090813060801080c0418140a030f030c08061c080a0e04050609060303161506141009120f 70
    0x4902c0c0070f0003031080449800c0000c1d042c1d1007070052010b424411030225040391100c0044416100902440d04000e0001c2014400904135001901a44400d1700d8684e101c2604c5007107010700c1d24001103d8a0242c1e10005040c4140f540300d02030150b0108054419100320032140000411078000500040c0078101c119022060988140e0102c038243e1410400c1400001428a41011194440541420040e2180e00c000c55041d100c1c410460494100b40010070740b4a54040c01c010041c50404514100f4140d10019a80017854507040c040d5030210041c060b100c03004480c20b000c1c10b485100d0120600301403409600000c6d55400c80c02041c1c11200aa50150200180c000e18590107185004080c08018011071030f45000b80e40403841ca01c1404050301c003031009440c6c0c142404217010301561100da05400c00d220200c0c103d882528071225a40c0a4800c42001a503441c00950842c1c0050b048020714022100041400d420442c200c0d0100d4603241c83c000c8190b6181280d440895400800300a00c42c1c0c082c00d001c00700f44 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 896195665 1250 896194415 896194421
    0x1101060617071d0307030c08061003020618060405090412090918031b0c0f060f1707080a140901020903062202010f020f0102040e070f0309050613061404050a2121 71
    0x3c0075040702e2041c3d0316420500070404503441f40b129940b0650000503040d40e020a42001140c1c1d01500c44c0d42040110480448035851004c007190b049102803100190541e905ca00ba00d01450144c603110600414402c00105254013680241d1440da0900d20302ca101d82004040c0031011b1601840c4c41c003078414100300c22400900070f0050107021040d1002001c6030130003400e107c4004641058640001070041401d0542e03107070300d40c0d440031522040010300103042d8a0207200748503404880c220f0001260002c8000c19403071003400356a03016a40c0e40c00304640810303060401c001038000030380340e400042005000154115901131844028100402c900711a44024001c01c9046501c8030944002c1d5200c6446500d03009909500310b4005c800145103054444046000348180b002c100e400c24050701d82541c1c0e501c1d2a940f42001880200c40c1660380f4020081c1c0b500c00b03500d0050141d80f08001800908900303081c840f500913009491103806081f9180c80750106500000c41503c0001c51810b85006001e00403003210007 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 896196915 1250 896195665 896195717
    0x6041a0301020d0b0109080f030315060715051021060b0111030301060e0108070c030f0e0604120f020a0e15040902040207050f0601090509030427020c070303110106061707 75
    0x356001088000304480d441e081008801003e0341c4002c01c49503101a10b5a4030080114042c0903038008102050300c1030003c0007118854040a0000791820b00641e81d41b0225150804402c014981e44d0414414501580b200350b03801441c0e0300e08201148200c42068640184401400900300b40d6038525005d8180d015a4075852184402d40944c4c0e1a50394400028103801402800036000030020701c0059010f0707014684440d0440d805581c2d401ca90340800c401510f0a400c00e01040307030b00c00410f1100040c0302c003030b4050484059100d604140c01c0d001462040c8840c038949500000600c00700c1c003040010241020342054031a85044802259011460010900a1107100320107012406200b003140d000c40d000180c424104c81c200481005141d072141d50960302e0b8040d5000d80f5481d00c03800e14115802001d6140003000300c40c0710b64001480c0503103802d8180c1c9010002e0380101d010843d81e5260f061f2424081c400c010081015040902920100749440c81c10801c000f043d000031f0004004072000ca4110752004601 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 896198165 1250 896196915 896196919
    0x150907030302030405122806050f0435040314010c0f17042603070f03060614032e0303120231150507050c0d0b16111c030b03011406041a 60
    0x4104201900b030360f030561f003201e2041d0782e85410040411605100c0d201110300c05c640100411803803508454010500c010b540c0341e00221203800c40f145000a4400400178002148182c0c6030071005007000c01060b0964525212110a110741418154401a0000c5200790000d000b1014042241d480b40380606400d000305620b09600b4455401d220300000725070004501401c5107489141c00d000c10743d4021815914207004100005101e032100b0701d082079402020b5608801403041c6490b210007a0060f540001c0e9034801c401c1c44806603442c0070024190040001c6c40700180e541d905520f05000e0780140076040ba03118042541c1d0038014400600f805502c1c0081901904001c1d0500720600c4940d08001c1158206038010f5400b03020324501c3c01e000d032501402c140942c0e03070b103d06019026541e084002c16602c040c00f004905009100303400314208102400013070240103d41214906082c014440103041321940201c40c2e000340e00d008c5090003403100114105a00681c102c0f00411200820340700221551085050a6 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 896199415 1250 896198165 896198203
    0x1050f0d06081b04140408040918060509011e090512070602090a0e1503010209030a080a020a0b10030c08011812090b12090115060509100314040515090703030203040512 74
    0x911604191010683d80000480b81031200154142c4c418017840400d440c000c118800400003000051150781200703008282e8001407041c40d0b1515100c1d981516402c640b00c007480d945d1203124000b02c07807646400c0402c0710f0708803000f00721740c02030759403840e40d101c9000004500030f03a008100701d401c014142c0c04440500c90042c069130300d0b0b01d41c1d807170012001030310030380b80c80304091700d81c4403281c0090805100f510380241c00100104000c01d41a124205168000d00329001180962186500840c2040d00528000c0b00c1265980250628508086026810031b801151282e414102079034400c46042d20032003a038a8012100c0c20084071000ca054a81c80c0d1141e00600103120301090001020801c0354480b807203400c1e0ba50007880052650034541107a20781d0b900400010481c01c1c0a109000e0510b140c4149042c480390130005241d00d8120303010038140038100d40884441c3d0005200c0c04030351001c070208a0f0000b085800804000f030440d60044d44a02860007894041c13003401c003480e14801070804c5070104090340c60040b1 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 896200665 1250 896199415 896199433
    0xd080a02011a060909061003150b09030c1c03080a230a0c0503040506040f0501200c1e070b0d061203021b090103240905011d1203010501050f0d0608 65
    0x1a01030804801d407032415403903522000200f400c0c600c080b9409030710010700c20b40340b50303031341004001d04409420441c00c00c0551340d0321074001420044d540007006d0205480003076282c4014904140c43c1201c8112014043e1100c2d5200721868550307000d0203c03030a641801c00703401f207540b44d980d083c0080a0403039240d0701449008203000c18103e46403043d04c0c0075081c510001d00484142c43d2055038a8441034600410725441040040c0124424240c0145403038800c40c000300340104000c1e9200c444030b00c500c003011440700002070720700510344003080040b01103110011010781041314809200d07141c43d050701c030b0751221400014803040c01d0030069202030050310000c1c00342001c608440c100203550748a130a000000114001d00f601c40d0a1509070140f034102d030392100d16410603450107001403004801c07400030500c0d000e407540d1401001035828040d0401d03407400c1e071105038654500c2040481c900b1007100c10728081d22404000520590341c0c04000c4810012080201680d604c85405200c1c0081c8803592018219014141c44 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 896201915 1250 896200665 896200667
    0x10c0908061e06210601060f020f0a030f08070e09010e190b130906060e0702060108100209210f2e060e0a0903110307260307021e01020702270906090a030804020d080a 73
    0x2321a85403e540e400c4908410b0091030f25952405080340c0074011132038801c0c080303001d140324805580c0c2c0420740303241c003d0704450f42c0408554400001e0300840c04401c00c2d0000c0090a0f6411048200709540d8840280480c10b804c001203034003904000b11010002e500c0d29400c0c0f0500000350840001010806040ba15500c1c141c500292143e900b801078a1440c09a204080400f009500075500825001014540f0442d0506010b01d61202012140000350003840403d060101080c06203050812484003549142c0d54952220306182d028041607000082c5072440500004000808441e031001040e01d0004030103210303040a940f00e12482c0e0b00c000c0c035448005861001c2102c3c0e03041c55078040906110b4051101a440040300c2a80401c032400310042e8001c070068400200c401030180f1011080b03400044c540b10054010585110031a10110f1a180340104444088529421400d0b4082d00300f1000c1d001c58148219081d031211031418001c1c080140f01800702d0190740d10014040c004680c03200d411a13540c2c0724240c0c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 896203165 1250 896201915 896201927
    0xf010c0f06060e0c12060616140105040215070507050f210d2c13020f0c030c0601120c0b0a02190b06100908030a030e010e010c0908061e0621060106 65
    0x3580706003d50110200c0c0c0010900703816030700075403140303070241600303513542c8044c40441d41000c2481106c004150903403002140c1c140c031320401b0022034130001148510b45801441407000d080013070444015000c119401c0802c1012aa43e01034070001c90b02103058080400000b04141000d20f102c20380c041d01500c8001201000150281d030070714040d1503100d9507038600b420340c50030690b0454110010300103640403503a5900e00b2515001d45440c6804005052541c2001080302e035410582d8800c075258800111900c034050200a40f48c01051543d00d200501c041994a801c5507003814840d000002001007089401540203011441c041c450034515000300031400c1c02c01061451b41070360014002e4107103000c3c1ca00c170f080c420540c480a9034003c85c002c5241440d0b030752086004164511018034555070303807128600c47c103d003802080d648030525a20300301d08606100880e4100900500080d0041e00300d03c03c40705060380141c0e0940d6000c1401c03101c10340c40008010260078031002614041210f809030000104100b50404 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 896204415 1250 896203165 896203169
    0x405210601060c14030a0503040f020d0b09030a030e2113030501290f091303110d081602061905070e0d0606061b022107080601090b090718050f010c0f0606 68
    0x8040c1c416450b41c503c0d51300d07407a445501d8464000031010400940400e442c8100c00341800c1c030291070803201540903114034901c1e0324165403600c503070781001a00044280c4d15025030101519402c02600c8100910325103945485810401002030071008152031009a1140195034015030708180240070788084002e1f03100394441d41a50b50a00b003121045001018100302c540c80158000203040300c8c419846402c02c540200200c01011800c12040d565030040031402445000d220f0003030ba88840129003844460554182010030221007158005410003c02c1245988010403002c0d5250000070151075210044404540454010f0703041030300e403010881002080d60011040b100541d55241540f1000013003039503030180c0484040d600160600303285000d0100d0300350201460054a08807131030696200000e6040c008268801d036003a44c3e540440000700d04020240c2d40e03022401c1e00d0010704c461014441d0345c1c0703410f59600510703000303405a54003c0084d0740a420f0010301d0a810401031415913440b807400102401c414 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 896205665 1250 896204415 896204423
    0x20d0312060f0f090c2001090f05010510060c05150a060801090302100c0504060519030902180601140306031c140403080309010b0409080f070305070c08010c0809070b0405210601060c 80
    0x4040006940e044d0307100e0702c00403c29640d5090706ea01d0241145e41040c40070407403545030b207540c0e444840e000120141300c09040305200f04008107071803405010b4004041d16650141c0b003809083c00399a00020000308400410401100c041c0c0095218004084001c0540380c0040c02c10350311741108002495000504042d075107000079024445180c1c0a00100c896020310300c1110301061051050300d01d198124400c0300304040c200c0c03800044441c2c0c2074000403a119040342904070880000020301c0041d580c0188501018085141620318500340040441e682d41c1070510302688075030841e011580c0d514440c2c0b0640150300c8111000c180c586450741403c50300c0d075000380c54110440d8600400007440e4105400388030881034000c2015030511400f6420012a984414011420080304115401c001a041c9070103001a0010b1000002ca502c0004005000390401824903282d641c8821002c01172100c101f0704680c00d8a8003600c0640300e441040200c0c035081f461001c6003070010300a0300b0011590a900044d050303203e60003 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 896206915 1250 896205665 896205689
    0x110a031b060e13020c120a0504080c10080411011e02032101030305040e040c05180103050f1b1e06030108011407030b01020c01050f0715020406020c1903020d0312060f 73
    0xd41c40040e907404003a603002c1a048a1507143c0040e0200711603000d031243e1100d003c15969118085007a800459111520341320110b2800306050010080800502c5000301086d2400300da49078401c5400350100c400208014649210a900003416910804480000c00340001c9200340c0c2c0c500224010752240c101010307681841030032102c160f072002032240b003280c1201e405489840c0f03068200b0700301100340f56001703006540c4481400000533554a0b800c685110400c04030340c0302d02e05541076141250a2030300c0003030740030040d0784005a2001c80e00181d1003020000c0e20102c0d03081841581c03a0108108140400d2a40786c3d00200200001910180642042402aa50841008066580c204280c040f24002c4042600503031040c120006076501074802400044464000c5504110160f65507120720007103030040502c02600403400304992501000700e882c9407075084621a00d0004041c86241c0030744918440a486508210354100134580108140700d0304005080c014840c05480301e1840c810720499104140001c10 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 896208165 1250 896206915 896206919
    0x6070f0206040b010306020a090f09091202010c2f0a050a060e0a15150801020c0d0f0302091804021801081f020c060601030504030329040b0405090a0f110a031b 70
    0x84040340551003594012000b4100d6420768030341b030009402400c03c01e41030214224001c02d62210100742140103041a1101203900d1100340f42110803e08040012401d41e81407948024180c0e8204035200c42e10395088010600e061041c00e01c1c1750002403082005034190086521560030322802140480e1102e0184201340a0504178030552541c403030038104090b1242d4514402800030141e075421005801d882015000491a16080314a007203a01424140c611540402c2c0c11201c9590000d281030b40d0201941011403e00501801080f208030348441e60700c0002400078002400c43d82c4049100b1021101054404145e43e10707140c0840d5907401d005840d841c4d45800c004004141c001038000c4802c66045000546002e4550800644c00fa00c0050030407010b00d80c4540700e450480300f40744600610902511006002e4100b510300784400c5444040c0d8282c000d90424003000500da0b400601524403952148802c0c4204120741400b031400c044e03052200740d102110720800800d01c100445103884031a00d0f840000340e800d03 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 896209415 1250 896208165 896208167
    0x11070803040c05220f060b040803030a05150a09050603071d010905090109110f032b030513170708130e09010e0106030302060106111006060503160e06030c0f0904060806070f 76
    0x41c108130071165080e04d10101d071a040c141d0135002100540002d050100b80c280c1c540ca200e01c2d050f00a5000030105610100070042804104d01860390091018040d18545041d9a4085480c0075900c3c001c40729219199008035019031802c00407800200014020400200c2034170302c507a03110182c28800c000004d0f04020202d082c0e03100603c5003140c103a51080b1001c0c058440c1780e05004c9441c0b81400b0156150040050710510f1002d1807003140701804016038400c40d2101c950350f0103021910301a0004c0c0841d0140440100003510380e1024000c00c3e1134101301c0030740707401c1d2070300d000c01151040e450400c20b030125001000982007000d8030b1239070050b1072001c000c0c803a803c1484121403c0b14400e101c0600141c0c800d800401c2100e0241c500091404858000da584210810207020155001c690007140060000010016207400322598041d40c00400d28209000d42650b0001406900001d4400f07841396400044124000c07480100304d41c0c1981001e001480103e0381e80c0846604c0b020708030385c0200400d55000d0707984855 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 896210665 1250 896209415 896209429
    0x6160e0424080718050c1605063405090d080408150a05060d060203090c06180910030b1b070b090a03031508060103060b04020919180c021c0311070803040c05 69
    0x160790140050f04203a41602409405000e0240c511806c05008014520014045401c3c5c03020b80b5000307000610950500d81c00b101000890490011032170062001e000203014808141c0f451403c0f118540b0b01c2d16102c0300c030700050501c140440002e00c00640000e000540d0200800d08506085415032400300070380e2903d0a25095610499050740d100c9445c900c5030700081e076541c0c0591340050300001121040383c034034400300780c4541c001c4008181c400c101c4802d4a59624003a600c06a000d1a01c95840322428036680d1800c2800c3d2015018420100540c200703000310b06120000e0f9110135400924220703481c240980e107035403034001d0420700380c00007402c0414003196140030301f640d42d046a810701d0040803d41c4ca10b8481070010300004499540c456002c0084540d03540c4d8241e040c100100c1c884007130300790181c0b410240821514902403c044200e0809003492102d9401150314105491707084403e8400b103100805c02c800421801c455610034034004604503080c840c221010b54483c910a01d910001070303071a01c0800c907035 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 896211915 1250 896210665 896210669
    0x2711102f1204060f0c1e050105040b1e150607021008090d0219110a030609030504060e04180b1f060c02040b09010f03260d0507080708060306160e04240807 68
    0x2103242c1c80d0840b8403541c1720348a49800f05001c0c3c00e401c1c000002c013024107613401c4840e8030f09940a0b91288103000034018010714051b008038104400c0c4a500c040101d101c0032041004154107095400d0078503001c40b544800b030464800340d500030b201450101e90f581c00034100800948036003031140f282110700300740b450001520b80c0514a01010400b04900181d603645e0050350b14a0105804c40c10b480340000000d000b41c020a84080c0c420703103c1e41c0c1c0b590b0400c0c60040002d44e905080b40d01c100c0c10070031403c140e01c5691102e5803650743c20010354815a40e80480c03004003d4005200303003040070081000041c409511880e080b1a003482150144611107111003003002040e030030700401201d11100c00080000507880c504420071000b50b208a00560000c5145684407a04000c507039420aa4607141005802c0d41d1056426512a11a00b04400181807a5004c40e0f03803a00018650f00c140711450003140324a82c05180344d50f03090b401c003d000340504604c840400700035040c0c01c8400f043d01c100803400031500d0900031800d402 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 896213165 1250 896211915 896211917
    0x501272705130b0a0b010201020d0e0705010f180603050402030115091b0809060c1e1c060e100303051b06090f0618031c090602030a2711102f120406 65
    0x1515403134900341030008016084415040d59400c000c0c42c0076203c058007904442a49031000f070b01441d0324060015114500c919004020001c0010403524038050708103100050703170060b180001c1e113035840d480807a0040c4140e119000960311300c1103000421011541100b64000c41c0110520401c42c8144002c0e00c4281040d194226aa0000c0000490807001d070f001030302032015003000f21107020b04100d041d510b03580e0250480e94007480c0c50b131151049140c414015100204481c040f1252079140c01d0f680c82075227104900000b010000000b90107884000440042c5881d401a45c040da48981080c4050707a5454101305403280f036070b000d841c1c0040c1c2d1a84c14100b903140c64a1044010b14513004407402c40c1ca441088039015492010ba541c00c440010440510142d03103c2d60504c000010a8405d0b0410809981e694024004c04800ea840070f04000505045049404410544050a88096140c1c05503640c0c2058448510003a21101420149880403641100266080d10603070b862a84000c9401345640300382d00880b4 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 896214415 1250 896213165 896213183
    0x50c130903090e040c0b390d0e01030b12071e1a030c0d0c050d15060f03050405030f0a05070309150c020d03021f060e10050127270513 59
    0x56443d036280a03a101e440707041d40c5a034036070701e403041d420650700038040b2825035161150080780445900080444c2c84401e80c0d280200310350b80c1c1c07480c25549890021f8000200308a665802c0c0450b40a5013100c1d56100000301401c0800a20ba0f40c4503039a41c500c1e11416007030312110356404501c00f142400180a441004400c0b80e1003001119030301400d54005400001041c40c01c000d40c11800302244216204585155141551442200c0c12041500d4201c00d4403240745110300c03000c00005401540059040c0020f0501082c0f903501d90600724158094210b4060745241c00181151b04158024000c10f80f842c881d444000400751500301e614810148a18481e0119060541c00b40146c50407000340f04446d4468030456459000da02d140200a10801c00c4101c110703911110140008820007002d00d60051641e035291103420724007400200784024140d04017003144601020342c3c41e903008800c0003401803c034451a210084907561031075180640c002c02c800701d02601e82800700f04c5040170f0700344030103482c0d800040300f03 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 896215665 1250 896214415 896214419
    0xa030e0a0312110c030d08150301050f0601030b030a051c110309060307121508100c02060603030904090f0503030411130e1b031e0102120105030d0f0e04060b0304050c13090309 77
    0x181c40c10400e100e01d5440f58820300b241280f042d68100700c1d1580010203580c9003c100c3c1071101400b8141003160441c903100c3e9041c1800c0003051203403110319682c403a009103004a11550300344042402c2c0425004050240c0c003c110340d055042030090842d032245141c0e0b40d00c546682e0094841d160303c9000740700040b50b00110070404520f00c18441c407454054190042000120502900301e4003021b000503500c6071146801c10100d400190825201d0780b140f95805001501c05460500c0c0040d03107a1152140b09449507a84510100c24030129919030310810f07030300c4400c1700e40c1c9090508044e01881c0e000710810780705000318000f4082c01e80c1140070b50801008078030014010407801d141c0166051001c1d02c001c075054031900400d41020301241101c1604848001c00041c2da502c410b000d00050840140c006038003c4d8042c40082c04000c0e48420700070590b03500d80ca070480200c030040d80000d00ad005c0d586e10611407260003000780300922902090000c02e40380121071070312104c0ca59203240000e42e07241ca100600821100902 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 896216915 1250 896215665 896215667
    0xc03030c0706031119030c0809030702010233360c0d05010f02040902070209070809070905150d030e1002070617040218091506010e06220906080a030e0a0312 69
    0xb00d9003900340b44200c2c1072044a405c1800a0300840b110701c800aa120929455107a402694041e00040100c001c1c40c5010700e1500041d41e51800303000500148564003c0700d050300800e07a0700d0681810590303401641076041c02035071032030003840c0c0340f03128801003140c1e0f0b4015403003a4900105000b0002d000c00904041807604003008080740c83d40300261500e540720300b002800c045030f51006001510f01c042005031030b040640184000040000e180000f40400341040c040ca20100054480c201c1c2d00c160303804a5240d0f602c6c00e1030150780c0199070405402c9903903070407018201740c0c014035005081007055405207143c010021003203a9030460f902c80e10000c144401440078030440c149101641c000d001900c10172130959008003100400c00100c40030755a45d00420480100c40340601c0e42507411560034a041040d18040e4400509103100b131003003d13035144809d038500d22140c004e15032013000101034680007081011b6491180c282c0b12a03511004400082108003568a24600b64001d64140c9070003402d810004615604 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 896218165 1250 896216915 896216921
    0x9020a1409010309020306010f2303060105090c0c160608100f1a1303061d030c060c091f0302040614031512071205070302040b040524010903020a03060506030c03030c070603 76
    0x300c0c1d581095155101c0401503281045028001d110880380400d24528051000da2034000e80c0c1c012141c04210041451219900040c2e068151801150103171802d864074059003a080c80b030714000031041d020704045c03640400310b400c61100441e066070300c403030401346d882200d1000352490500904003000c08500041c404082080d0b440c05240840f260810703e440303d49500d60340e424049620443d181601c07110920a0720b209060b400c0300c0504804001c50400202d10700d0151540d03001420810080d0b40030988403e035503070703944159a5020b01354080c808142c150f040c0080c00381d48a806490045844000382d007400e01203c8040300c1c814542a000d142c071700d40d403c40801134a02e003200400740861040d420041a4902041d03041070a142c4a44020070b0494a50320501051b2545005140c2c816071504080100300d0401015080104011550a2004140306e80059882283c940c02c0a90018202200030040100d643c0c42940503110403003c80b60b020215200700365903072055015802464201e9642013003818000c0e0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 896219415 1250 896218165 896218177
    0x30306090f5103150c031b070206120708060d08070f050705130c030b0f0607110103020f161109091e01020d020f0a17011508040503071b080709020a14 66
    0x31041440b8849061040036802c680081e070380a528001414500b440c6030410240d4105810302030380700c5041c50151604009070000034144012099a49042011204528115200d581e40101866200c000c16000039080307100880d400c0011034011404a450f614000c40341702074441d88100180d20f4584165a201170010031501e04480c944100900400d0130303605d440d414400880c20101c0040d030803c04880060642e249005854042d840c82e200c41a010307240ca608980c2d040b9080200d000b8800081c4004030001d1240801040c401000400e64844000c0b480101d0303881240941108541040141c040040c281819110001254014000d61919801c4e00320b41034409030401d8001824210700d80c41010603030340701d813002d4040713080002003c1800c03a0300203099510045042c12040340703560501c01002482c0507524441d5051103080c1c400182046410422103010701d40c008442640c2c1e90740350080c0020300c002c0e070045000034061294042012082c51081d140c500748a6520f40b00746040360000c00d400f5030300c03038 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 896220665 1250 896219415 896219491
    0x30303090c0306050705210609040219050910090501170a151509021b010b0f060705010b13020403021302190804050a06050c0306030f1b010e010903060905030306090f 73
    0x807540001c08501d251190f02d03c6030160b038852556440180300d401c01071041c100401803404142d1002c1c80a180c40741e15845601a5059a400f81c0d13404800e01c12000300181c642c40154024403060800000c07001c0381207004101c0700310041c144a182d0722000000200001d800358503000340d02c1400002d002c120811404810b126550030001501030021b00c40c039504a0182e0480d0052503000a90440c0d00c200c14254656503205c440001c1160441450002d1109220201550300c10f00010608005000007940603440700390303004007980100f1503410400006500305100c26841507980d248590505078030740c001c44849200b40702c050804030741445015035880001400681c0d1921408141c400080c00d540324039400f039510071312925102d2030010704051829054000d282400c0e04603d10120801c0d05165141c040c654003401c3c49a05442141c004070341071b12065101170052400e28000d1001d000e070120045015080aa6095005966030302100001c0390301650001400c1a07107410311441040040d455440006903 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 896221915 1250 896220665 896220683
    0x30f04030305060d050d0f0e0306070c121b0c0f0602060c09100c2406060e1e030f0712120c0519021201060e010e0a05040c063005060a091503030309 65
    0x503245c1918140e12071648401003040664481c214540103110400c10303175001c9000b403045140200c0020420301481390018620007503515800b040d1405001c1c100703980d0100072050711174442c441c10704a0100b001c40c4031346481541101070101d5035500c0490b1042c850b1102e210800c0c9032100c90000d00a55040e151501420017408003d5800014491010960420201f034206000303440c0d1a000c0c01d0032944940e011005001d00c00810711820f40301d44050807070300d9070300341078900c00c00351200d022074140612a400d0030300501034180003240c410307040300c03100d8050ba00410304000c00c00c1d1080c1013a221102e00b0080507005030f2248062840381704c01030030141c40d414809000190b45401111500d03094981c15040716810440e520014044071500078040365010020b0701c0180070301d06103620340d010a0211030003074404211040481c07061039910100690500200d6002415101c070090100b8001031100791016441102d01c110005813035031b55405004036000c5000c8401d4040351940e034056004000703034202280d1005c1 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 896223021 1106 896221915 896221939
    0xf0105010509130f0b09090a051006050a05040c03060f150809012f0702180a0c0207060503242e091d060d050d0908010e0102030f0403030506 62
    0x3c070780000044090480c80c400018103003041d0b0b05070700040c0c3d140600c48061400500e0025503401001540c10110380c0d60305a00640705944280e0394054500b400074060f920f00303640401c000240c2420001049070b0703680800d0200540f40e511450005080e12803401c01540c0040b60b0903804200d1400800c9140c02561094086903a0609454401c50361071248085851071035044941e0302d60000c01181c00120040c2c0c2601c4050030480d41c07050031506050a0001d0940009803100aa0745a5150281955640200c85400100380301151502c0c5000585030151929810b108021001400100e01e1030b150031800d851190941c544640400c0107000c06081202e072800714140103510404042250301c68403070f000010f000224140300a045801100101501c0c5604180920121851074000388640d0403201c030b50f2400c0b800121000403540500c0310000340024420b90000c0c0d4810001068450205 = true := by decide +kernel

theorem cover : BRFrame.Cov 896043165 896223021 := by
  have h0 := BRFrame.cov_init 896043165
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 896043165 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 896043165 ≤ n) (h2 : n < 896223021) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
