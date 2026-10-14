-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2716
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:31:51.728408+00:00
-- url     : https://prove2.me/submissions/32b02f78-fc59-4f72-9806-e847f209ba7e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 488309352 ≤ n < 488489208 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 488310602 1250 488309352 488309357
    0x10140603030a20030d0603150c0c0b07050c0f160b0c150604090f0f0501151d0705090a030302010504030e060a08071206051003061d250314070e04050906011401 70
    0x101c0e45a1601543c500701105000c40d01002410350280f1240b0360103042030324424500241e05c3c19405a0301402c444107008054003040315404000c0204041c40212a4010b00c036140c49450a100c402c801401c14002400260712039001411b40c00005548400401c0580350030306802d424000d400c0100365440128090921400824501003025501d81e07410042c0e03c5500115a652a0b8005150048581640000c25a4154644880741040381c40030308540040b1940107900f11540c0c01c030300783c07501d0003644c02500c00d100b4440208852115030319001c0138003000314040d80001030715180c0b030300b405401000d0300c0d8246482804100040003420f030300003000d660004404c3c074203440b0f159031100140e4001c01e00c5802c0281d0000e06003000d6801c40e9450381006080c3e0708260304c40b0b4008001101409104082514144545003c182404540c07644941c0008076800e49854007082c0254185107140ea10343d0141d80310000120120b0782510b041c00c19004017a004500c034030003810b09614124071101e4034189102c82504 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 488311852 1250 488310602 488310617
    0x3041505060d3011070f0b18030709061502100b091303090b190224040b041b0902030406150302150c03070501060e090708070501050a0507021201050910140603030a 72
    0x5030f08100c48042e5079145840d4200048403856078001030300c8651500b05a00c050b2048040c04210780710141012400c41d410b1940040c2000c12509000058100c0c0340c01c41605845884800501c541550081c880201118a4040c00511490f80002c0c10101c1c1c0040114429003000c0c50060583c030307404c200c0c540c004002e010002d40c42025190854422050744d005071528000420a1f00000401444203a0030300c4207502100c442c200581d6126070002000c2a0390424544502d000801162110101036402889500031080541c240280045090b090b900302146143c0d01104000401602d0300c00e039400418240d4a00350306c030307103180d0018040700400345501c03001050118441d070710200d0400941d0708e03650740a802440500c0d141e03040305480e1f100880300c00081c4d00c1820b1300080c001e00301041d0030003641d034103a40c2c0520b08809001c05880301e500100741213800c40300611201c5d04c0c02c0380c01e101d901c0c0a04041c8000d40b060008039205c01c0c003561000c90507115000200410302c0f003190b03400000c0f07403240861404d048a = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 488313102 1250 488311852 488311883
    0x4020a0302040506180703020a090509040506160c15020403020103060905040c0b0d0216061b0c1208100504090302060103021f0909150e0103030507031d0303180604080307030503041505060d 83
    0x110102c3d42880781d041d44030031172014041c00d02d40540140803d0300e4182d655000c01942c0745c08000d2403c601380c8010340306070482c1e40440e00c031800e140d5684490308514200b81110040c0e139624025103902d52500ba20110340e02140500441da85401900010461000240198100b90302d80c980044803030310403581d40010004682203281d410360143c5204800304a01024110048e00307000028100040004852600b903103010501e2601501d00107121a41200e41d207412000d1018003a504214060b11401c001e41c0032001c002610344d83c0e4000c0b142594881c2e8050b00310b43d407452041c0041c907119030b00c0d00701240c4442e6091081c12940090698200c4e05842804112840342d4059408800c180d60020b00b05c1022460012051581141c0107040d0b8521a075224903007451071040b516041c01c079155025625030400c021600503a00d404c0000701d000c0e1070040100c1c0c581607681800c0c41c0345070711a003404c60120388044200424030545075001420b0f0b410011051006140c9040056016030994000400314000903d261 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 488314352 1250 488313102 488313109
    0x201120b040b0a0b0714030a121a042a140915040911030f09010605090606071401020d0614030c010f1101020c06040f060f1401180e03160311010504020a0302040506 72
    0x116480402619105403d510340780d0321481544180c000381d4a09503043e00c03144040c64000308844824609a071079000d409121030034000035011507040482070025454910243ea03482e481400c2d0801c9419000034180708407180c107c4400b9040c06028010301c140600021203880091080740c05064003201c000544090364044442540150f0300110101460143d004070b00360800c034010740c043c02c1c0c40040c0352250313a2000109400d8071401d00031250411440c1011903002c0c2411000751510501c01c08081c100050390400713043c22608440710a00110341c40700d03404c1001c20000c025580c1e44803030940240c590360442100181140c182070880404109030080804c00b03001d020350543d00400c051001742e41c03443c14103007068003e9901411065079030302e00d45400c0b04c030416114400d040010f001240c0a1005a10700500003ca840103240c3d1140e03015101d02400c625443c2c00e00080111601c0e080b65510b00f41c0050500500925034840d00c00440e0f8504024000960340c6c90040c402225412030300400c1c10b0b641e44021 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 488315602 1250 488314352 488314361
    0x27050123070e040f020a0807021501030503040b0a02011b1d01030603050606060318100c110a050601150c02090115180812070c0e0420040b01050d02070f0507060807020d09030201120b04 81
    0x101800b085c40810300ca1800f55010020318083c5010b64219050b50720600340020500b0030a220060140d413040004100340881e07030b00074003100410340c000019212020b002108181407034044c100c00040c0c60050300c2880000c07007403169081c41828682007000f81e040d9968142e0300e120242c1858401c100120004156980c42c4200c0d00c100b400e61000c3e030303840910703401c8480082c00c2d016201d00c010840f05204000b403040000781c8060040e4220000700710503440c1102404400380050028400c100c050b01030400503844d9411258000c00c40a019076088080720720300140901000b590003080802002d01c00c0003000070024036001010841040c40342c4c1c624035440c01a0013a0560351081c200c200a041c2000284072400b003407607040a050000d0403241190300020002280c940441c003a0105500b44003041d0003402030360190191078840d8000791481800d40e1070311842c001d40c03a07102c140000c1c1c2d0281007020940e414410501003a1a5041c80c03103a0318290360020300707810700c048040c807415942d0b41d158122a9549400 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 488316852 1250 488315602 488315621
    0x306060e130b0f150301050f10050909060a0911040305010b0307120b060303070b011202031b01120b030127060c090e010b28020109020f030d0801031527050123070e04 73
    0x544105480c11a511300c4850700244550340c8201d03c002e40003085403d100614010242060b81c80a240081c0b200400000c2a005001c2c250440340b146800f2031480e4480c07080500903481074442649076446e40c540301e420342d1840d1001c680030f50404081005003440002c607100d0726039030011020f000c0e96074010100b4070b10701408002500c403422680000401400320f40c0d0a5550070300a4043c3c84200d00018014550014002c0c1611f000482c071b1421038200c0d404551154402240c01400070401d20341c08441c9903c066081a5400c91640742ea001e50303c100b010303a00c500700c00003009040c265065854051240840c02c014856101c01c283c001800d41c00c074405100706603111410708403649d03010200c110300080c020003807004128051100030f40e5060071480c00007500660000d999032210040da0860f5074100d00301c01c3c0302c00000e142c107842c1d401441c0070007108619502e260b2243d00f4240040304244c02c02500b9501e100e8400014844050701e0300c4068080142c110b03901105030304284040d08212030205001344894103 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 488318102 1250 488316852 488316859
    0x30c0601031101020d091a07080d051f09090308010501120e1c09060503060901030f0323030615120403180b0c0a0c05010813030305040c1d070306060e130b0f 69
    0x800110821401c4a001c80d066882a4200d4281a40f04030080e07510710018055440c1c40c17601c1c51102564050702000600100c0d2140000c1030420440010040c107861003a16504110b82681c40031030342c1c46080d01c0d001001418603038024050b15105440151660506000700f40c10000d51210079100302c075140d007003100500c2840e02260080302c420f101d00040000040c8401d070000c3d840344000603481d441038080da0300840d1300600b140010707480c41d40c40d19a10100240c3c11410300002c1c151a10301650001566040807580c01c800954030710700178040240f1810300e5070440e00074000500000524042c0100d80941c00743e0306080601a0841c40504803c04100643c00f081c602c1c0400246914402030115440168501c952400c1d50304986590056a0322202100c0f0f40d0003c4c01200a00320200b4403e03045903410900a01010f90016216090121100d90080b02054003440e011b060055040d49445210000c03c07c1c3d10748040341c0161100001c090b5450041040072803034a0b200c000543d503070b940900300300c20031008 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 488319352 1250 488318102 488318113
    0x109060e06030408360109050102070e09150c070201090504090b0f04080d020a02030702042a120f0c0e0109060203180603040c0801020a020a0302010641130e07290c030c 74
    0x140340094070042c009845c59511040340b410a1484d50081040b6000d07100d05030080c0c40351138105514040000801016413071300748100b110082011296107440c50141d10040301e0155650120300016189408582c01203005510300940c039404103401d011855040101c2d100c6210050300c407401d000d0101c1c010004180300b1584000303420100c55400200401100784240c9003440081aa12034048025080c8500107881e1060142c107900070301d00c0388010000d0b06040f800009411914090402c00311828001844081107280300796407959030708504080010f043d544019403600c240c4004181c0e400300103070002805504044046010031440c000c006018003ca40021522005242c50003980c0745c01103801030300954a002000315511024035213016100b4018610303415010a54842240d41c0c0c0541000300104c008600305110540d6120441013520118881011440342c9001240c141040150b80c46121001c05035881a80800c182e03200c00c011002d041009191104100b14a00f4110b125022172040d041c00351 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 488320602 1250 488319352 488319397
    0x3030702100605030109030504031b08060f09061501050405061c0f05180a02010e130e0f0d02010e03030618070c080d0c030b0d150c050c0604150b0109060e06030408 72
    0x78881000d07120140050248590790000d1500300c1c1e01c8460301500003402000180003251012908011800306040c0341802c4a80d600c54141c1013035010368060b176121511005100e0719400030400b1541050310f00c0300d19140c10f110f20001903c244154030501d406100041030201680c0000300000405100c0d0703040c10300260709001219401484100e50b100711070703a05500c0074100c0c110000350340752034990306131a044990443c8200300b0a0a0003044c098507001a103a070800b8460000a0010140b544aa02c00814a41101c810007a094842518488910364400e004006c043d9031140c1200000c01c2110b9176030025616100003c0741d42d0019500094048000028100118103a0b64030501800803140d41c100162100e00c1c041024038071101350081e200c20200307140708280d8403c80d840100806000e040c003074501605004a182052003c40d030a40f0040e0100104980820060150b00384a01003442c00f5001d4030706020f00034102e0203c404040f40500b0010000508211605048422600c480070411011140 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 488321852 1250 488320602 488320607
    0x1501271509170303040203160303022d0a1a1302030307150b0909030403060b040501030b04151b09031101090b070b07030207020612061011030901080c1605420414030307 74
    0x50b00c049004c4c8c450faa00850f44aa00c4082c1e89007a01d5055000c4c01e10350090714803807000e80600c002003655112880d00c0c680b944800400c8854020b0303101d064807121400d1841c5511424180c001d15621840101501c0320005a0f40442210880c9501a00c08040e00700d010800500a24040c40425004181c001c14001e0311a070000c040c0048921589007405071070801001e00050f14000e1100604d24600e0074081000100c820100301103803510504000303100c40b152282e00b4480d051290b2401d0100d00b507c5c40500c140912403551800881080c2040511f003440c0c5200c0e07071507034410b254002c0d24007030036000850f8030588a41c048034441ca800a11030307a01c50700715600450818178250303000c6204d8070040d0388000b81d590250036800b540c1c0d00301f5806541400384103801034505080c000c0c00307103510100070000c8000c28140018a54100e500032802404842c0200341c60422030b10105622000b10078488225401c20310a078810020141901c000703002d071540315441d003080035010400307074000540004801c02a4169 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 488323102 1250 488321852 488321857
    0x3408041133041220090a022205010203032e090608060f090c040c050403080f030115030504050a030309141219180506070f05010515012715091703 64
    0x401c99080080603a0000500d4039144100c0c415040300c140c9102e044004909503200000c00661003d840181e800e8a000004040180440341ca030b00c5607070b004c1101c12201442d90040c0c4441d00740300262450351414480042d61f80c0c00300410f80900c0030601d40030b07c07007402074155140340d00742c000e0010b43c603240751201c900d500605600e0050020300e106440010750603d000703000b03071801070304050051303c003018035203042c40090f0840c4030b8000c051080804c800000a03400e1002014400d40070003542c2d803254180b02e0210b420211034805081050b040c0b800b8040895004110400c020b6030500300080c00120750311700810380005d6420304800e50700510250408201c2507200074088805d07409041d03c0302c0142c0890950b5902000082c3c80c403004016602481242800d8005040c00d5028508041d1070308100d68403d4296401203614003c1404c08103080891560041801c0409026541e80c640d0b0920002401100100c82071241ca2900e42221204804050180d840348001e0701c08088034030f4544100755006aa20b9 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 488324352 1250 488323102 488323159
    0xb090d0b04122703030f031d1c080f0a050703090206072003074202010213050109030f0201031d030c0c15120a0209151234080411 57
    0x41c8055280080080e540c3c641d00c00101c3d03400c0702c0203e5690564404890f07540318003228000741541d17420a0450340e0141c8031041d138030300d00c018000c00c850307800301256240301001002001c080c04100d1003408040f950580b104c030b40c040c101a00c00681c03603864a108030b0142c4804c803c081e40108000070800b00703000340d01c070030081038505180e0014169800d40041c10b640c1c1d569032040d1a09070b4040400d80303c007090b03a809140040c490305034116880d61600301840114908105809001d85c0d800600b12002e0303a0103544c030100801c42400c3c207558507032540d1284964811034410080c105661045110740354141d07420321641c1501c1e04822252188030f60407145680701e085860f80d620404a0441d0401416281c4089407600040c42200d40d5007038990018160283d00454030560340000c000652041c001c6000016044581d0001e2010025042c200070301449000203140c05032680c1018a6075108100100c10b032440d07018a5440d08103155900c0307051000b100940c0518040e800b8031516910b900d0141c100b403012640 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 488325602 1250 488324352 488324357
    0x1061101060e01080a150e120a0306060c0210030e120f120a051510020705040203100920031f09051e0705120f130b101e0506040b090d0b0412 62
    0x480b034980301541903261003480341d2911507002501e550005031403100d0000c9000c0300110003040040243c0b01c001e00b0a950f000c0d004010a501246000c4034036454050381009142c42d040c804607100c010380101d00144031030b101507000d1640705c1c4507003070143c0410044400402a180c0d02c460703c82c2d2000007100010307400620080c0f00c0034640000f0820b15030041c8101805080c61000300310203a49000c5c10301c10003200320720300142580280320f0700003915215400154400d010304507500b00745a04140188007110109002d240d00d024554035407850740107595003202c0e00454180c11440c801d07034400c1081c0030010015007000720890f007003800340148441200348c42e00b101c101e0202c40100c00e554190084519028240036410300700c0301000419100240840b40c50340186491010b50100c401c00e45500b072400e00f0a4800e01e0105225803000c00091181c0000010302ca80302c0d0761281441458840080c840703000364003a1802c81440060340c5452030b0b80d0b40c0922008a5400500140310307203800d003042c194442c446a5400007 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 488326852 1250 488325602 488325611
    0xa15050930070b0723010f0c0305090d0206040b060a091803030612050705150d090f0b1602071a1606140f070c12050c01090503091003020408030a12090b01061101 71
    0x301e03040086106801c2d5200300f00d03000c0c2082400c0c0c60f0352a854030242020030061520803402a6407030000e00801c80400a01030300420319041038807006046900041c40c881c810342068201c10f1500381d02050040e045038000e10542c0440c1c07900340029034a440c00d940000e550b14038180101f4101c40c91002c4130364000c0d00a803010400140e031081c111015807500c14004040c0c0c0c100d090b0034086858000521b54034800d00d0404541003110403215401142c1e400c040503030710b034480ca4100740704002c2c0740802d00b540404d000317001010b0507400001c040c1d51440c050141c1d14468560021030705c445071003413040c2d40d80c140440c101c0c01151520f50030403200400301154039280c42c010400002e030b1900891001d4900428140d5103141d2030b0f5403551200307800c20b03907282074880803c90104500c9064010174015281080c1c010006950745410103400c02503590440c112a906244c0144410000d0f04408000e462803094242001800b044120b000b40d4010031a19200500032915403002145e580c0d840580003080030000b038003c01 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 488328102 1250 488326852 488326939
    0xa1a03160e07050304020604030602070314030103050309032814120a09080c0d030503040b0712050c0c0f01061412100204060906021b0f0d061404110319020a150509 72
    0x803400c2c4411117019400010400040001500301c0c0d00500216009107041c0c1840b1128844e808100e81c000c0e4020f407030036840890052903500e0244002001c0c0c02a0000c421001000c4d00f0601201d883d1241024055440445011440303450510003046c000ea240002e00d0394540b00c0500281c080e40c29409200c01d0703841180b0299102e414000c09240c001501078450354156070316955040ca4104000340300718204400904a000c205480c2d009007801030361081ccd0b085450342c406190f40b9150649543c0c1c1100da03a03040000802113081120000d06001905640c00d40c01400200180f52a01c0401040500c2681c030000e00012060b9000c1e03100026600c5d03070f50944140d00d0030a06d00c440c4014800e10310651041400c03004800c1840e203d5483e640d600e1060380c000c81d400c1040d03401c80e115520119001d03a01d03e0300c100200d800501c3c081c0401c6403880c0d440c0400d132a001c0c001d074000c10701d10806030003102440301200e800010107a008000390b800f05000144501c0c2d045191003118844603006204d01c0450364003003807460 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 488329352 1250 488328102 488328107
    0x21021b060f0c07031e0219080a02010b0103140408091215060a050907140c150112110307080d050304060b0306091609110f0901030e032709040302060a1a03160e07 71
    0xf256403e8140e035076030000101648045581c0c0051241c134a0551290b080e00598002d03819011441c558040c44030144c98042005000e401d451400701c0160406140400c107813040c0c3c041e000d0050304990498802519681c041022a6044d4500c2d02d10a80911030ba01c51a200008181d003010301c10442580c005060075621024400d42450549011011031041c52034041c0028a01020b414149411400c4440101c0b41c4003000b0800c0d0006e81100300124014802071003031101ca000082c20030542540140038075860301941540300d0300c43d490ba030010820b0000108081c003c80d5081072102c8200142902c18509007468000d656842c4201c504a22007a002c0001071004003e200744402045607621243c03030f01440b60036186195103c1c4c0b1125040c19a2000b4003001d00908101038480203c02046488103000c05807400b024503940074801ca807042c80c0c0c10b030400000a5000c078401350080c61004001c80d243c0c56901c0f02c1004d0050f0415801c1d098843d00d502e028990140800f0881154030356014100b0303c2c1c0394403408 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 488330602 1250 488329352 488329357
    0x90c1507020618011407050f06010803040f061d0913020906010905030c0d060609240503031908060310050a1a03010513020105030a020d060b0d050a0b0121021b060f0c 73
    0x41c0d031050051000342d00202c00d250320407849080500d0400150030050b01c504411b60030414050b655070b0701c0103800e1074401d00304000301400b510310386005600300b925002d070742400c902c1c00c0d019480400c002040b408059242a1844011070381009004502521b41082c00010111450805074850b000301d02c045a110b5014650340c00654901501404202c0304000c2403080048455034200c6c2d5076540c1e128000b4040032144207031001408524019011001e80e40740010412a450700518802d800c1000307102079100d40c200c0004900102410071a00c1552440300181c1010070810b500d04d20f65090208205008410b5840746403e0740264421120030702c0f44a00b8107080b07030000c4420903a40300c207404041015601a0f0040c6500484103c005071819504080c6a4207441c0c041d40103c0c4084030200380342e000c4020074000d2660003030900714108228031503100000d01102c4201c894009001c042480c40501c0c800c0380c0c040703a10032000d59840780d1244100c140802d039907140890f0007261006c0000041031884485504 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 488331852 1250 488330602 488330617
    0x906060503042609010c02011709060105091806070e0301090b0702030a030609060b0d05060303040f03120f230a030e0601120c15020a0602180d06090c12020a0306020f0909090c15 78
    0x24913800d0040c40c0300152501520700c5800e03810303c040720010140b0300000d202e043d8440c0f0100805440a945068240400808003a0103000c031481c108090803024800062580e501ca1040c5c94054484440032001c40c0c010484e84d0f202400001e6070104008800750000b0080003205244e030350800c03490342d0b95a000421145d19026848028a007086078017284101a00070341e8000900405032480c00340c1d549844415507880d0b40c000c8a0311030300d00948200c10340e040a103500c50401a03003000c20070680c2030a4052151410035200d00c1c82d0030004a505204d1511960090f08201e0402046428039615010b10006400041c01c0880f10088403081c089a025042c1244c00e0074070f40581c0041c000036034140c0c2c403400a03401c0001d03150f0034103101c2501e030700483c2e8a0410340c1184034020880040d6180050400001c0400c0f1034000404880d0707080d500e180182c41e20203241040b26080100140c0314210300000728080e02c1103440d85c070f512403038070414852150030126454101080403625881c448084c0c10038501a80034903c1d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 488333102 1250 488331852 488331923
    0x13031b0501150b040f0b0304210905182509181a0402210c0706020d020309070608070e01110f07230a051c020a0308030a020406030515031c0504090606050304 69
    0x80400a86e0254000b46803c54494a0048900c1040080120810030910900000160038020403c201d040c010088403446102c40b240c850b203480c014000b03007100b12001c058200c04026089031540200d115030384c1500076042d40d01d031004042c1c8188030850301400382c081c1c6900c004030700c0c00f01c0d10b01d56280910848001c1c5041281448114184800050382440300400070f00030220104040c8000a000748000c0426610b0014010303201c1c01c041e01d0030323460b0100c650068014800b001040c41241c94000300070b5100e040c024a400c111504050315603605000203011002030a00c104000800d09848c0c045c1590702c822112450207103142c0001082102d003034405c4c800d140d04005012442c1d40d440e0300580080d6445400078000340200369607503907a00b2190340300f29001d46001e5130120b000e02201c0c4d0b05015070341c1c00401c0c04841d00c1c44c101c840400039440b40d03034441289248980403140da1481c94061005e13038008100c0d00c0c3d420048160b6802c8050815441140c0450307010348820b08150303011a0110403d01401c5561 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 488334352 1250 488333102 488333129
    0x10501120c0b041a03040614040f061802011202090d0c08030304050616050426060a1a09010317070203150a09231e160f060912050613031b0501150b04 66
    0x1134084041e8406030042d20010740310316002d501c0c1004500002d000b584603e40080701005103080c614120f48414580e0502858100c12540c0981e90040035071440d21b1404d82c005a13610f2040340000e5040440f414020124994140000360f0810080b000c1c1d4829800340c0240d5900340e4500094540080c02d82c1140d601245052005000f1407046a05002880c0d4030b1000841e1200f00c1d500840745442422206400481d1702c5105091442584c2d01c0f5108203540159a20141035066039140340180311090650582c00e00040361100035585c0401141c0d00030b60061070f000d03645041550040015210510054804840840203100700041411509030300b92900340190036202c2d00c44002040740c10415012000c80d200301482502280c00b1074a84200800790b212041072482c3c0341500103403803e407181d4040061038042d0300011010030004503080d40d01410340702501c080e070031203490251079040c50719074030501c910001480d44041007030551260040ba196159030102c1181c0d9070000044038401d43c02945010b2912 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 488335602 1250 488334352 488334389
    0x807020d140f16050c010c080714030f07061b09150305191a030c060301050607081312060b03013c020d110a080606190818010501120c0b04 61
    0x40c4408030425625210380c500c0c05060720a882c0d540e800042c0000000c945001202003008020070240715912401c0c20403201700300b4280c43d1040c480c003030b140e0060541c18100220101800d42030007243d0310350210582007a114001030603e0700040c200032143c0007082070300c0e8035060035141c0101c008108803141c40c940010b5083c1d101600701d000c1c1c480601480e440c000f1000c18003d500340c4a0003140803e8040303a11040040342c00c02d003010f00d00786161610600078001080144070580319241200c00300c60f08281c45598402c1031461940003d0400c0d44800780480c07079007001c0810400c00c1e0304161503c2204030028080505240843e0304160000c0a003445400d0800c0b010340c8402958040b50078501d10b240030010708110440d801041a80d0301a0200c000c40c400010700c0561454001100b50741040c82900d10f81c1c00d11014a0342c50601c1c0003048019420710502d0000074505c22040403540e00011203050080c452540d441c0301880200b065144100d0b0ae001d80306034085412028070090320102c6d0402c000790a082e440 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 488336852 1250 488335602 488335607
    0x90a081c300e07050a0617010914040314070605101508010501021b01091d0f1b12040f020d06151a0d180c0303021c050909060108072106060305070807020d 68
    0x1141d0b070300000940503407200007410380d03600c1407070800031300f0f06407140f80080101480c01c007038500f4140c020003a21031034440c2d541204e6010200c45a030042d0f250510240403800800804424003442d240200018103010400224110400c032150803034a03000106030048081c000141c07030f01082400388070b00580c401d504410200951203851042820181011034080e91105180343c001e2089075074449104200006100d40385185d0040180d10024620850440446819180307a180c0303d070608190244140e0800324051100104040882c258000c0a0440c01005071402c10040c0480f6105045007a8542c1c0d800129000c0c40c0c41d030600c2d40155440314a14003043c0c0c0d09260020025001a1100d080940144800003113003808a440658043e030020410050055803e29800d800c94000c10104101400400315548441003201d4000509003068a642e96030020220b4511480024015142da010300110844940c00d42c00601590411307a001c0c400c0e5915091b0503580300206594003001a4000c1c6d040f01801403 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 488338102 1250 488336852 488336861
    0x915020c060d0b09131209181a030313060206061012090c050d050c0a06050415030b0319060222050a0e04051218010e1212090a081c30 59
    0x20810030700040e12010000801e0f13490404032400c4000250b09507401e02406503010250110051506c0c100c4105800e08200e2410002d40c4a01300c1c1c40c1c55140d42c3c1c402c40455198805000c1e110014044039100c01d802d001304404191144154800b500803880811068201500c1c03440c81c43c4074a03113036403900200f10800d0307200a000d2008192141191342d0804215556111300200b0b00901490003045624001d404000f40c04182d0344c49201806000c000401450841c0c00810302803598509000502000c2c010219003011001c2c600e048400c221110300c4000c000a45c0e0103090a00e509881c0082007061a6040000c606035038000c190340204d814a08120000c02d03079100d01d6115102d08180c43d030100742d40d040044c49800075007201c2500311280e50701445650340250034148011084078028128000507290684840024140c0f070200040020007650365220381d002c070303402040b4043c2211803c2c00d8000710311080d01384c102034440000c0c007030b0704034a001c10f07000040b03035040c035003503e00300b0800810345031407650081 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 488339352 1250 488338102 488338117
    0x1e060b0a0507020f1c0803010e10140d0f08190306090c020a0b0903120a05060f0d150b011e05040807081c0c0f0506040605160c05060115050d02190915020c06 69
    0x1a6004801e1917255501034603009616104003111a200d5050140800c00c0e03203001003043c0301c400c22090007007040811343e070460480d6140565400c3c29a10243c102082000c80707043d0042d0203c0c4001076200751028001d0701c900c3c0c0c0303140d56031b4040080d6170310b03440c44030b054500001e07141c40143e020011240201d82d200350358a401a17918400c80740380840003101c071412543d048581c03040c295691400c0102d542421090b209481100702c0702507030302100b5a920032508540b00b45040d40b066545041482959009481a90000350300319514200646030301c400034441d078414017030081140a00c2400040f807440000e000c0403921030210210180c82d0701800d0886000940300d0094595110540700d00c401b2032014001c10f406a4003c01d008103080c689441220280e4a4440c556010400d0500801021420204902d4190f03520000035041e03640c980c01d000c5810740a0350841000c11131000507414010300111581d03200d50342281c0c40d0031402941da11340301030b400c00140803050003580043d4081405840c00c91b0081142 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 488340602 1250 488339352 488339359
    0x923010f0e06040201081e13020a36020d051305120703050423060c0d03050c0c0601170c0a17160e0f06120d0305150604060906081003061e060b0a0507020f 68
    0x9041900700c42c5044200540c1e801b0b10900c0308080d07c0c010b604006480344090201d20004bc008401e00c1074005500d03004045444d2030100040d45400032810040d01110b850240e01c03001800641000b40d1030388030421446008803224804c2c0840c460710510484140c2d180da981648030f07030b0700b418034051152034641166010080c4a05040110a00680c1ca0201809050710020000c00401c0301c0e0010240495034040c000240044040c4521040c0f8640014039034191000030038045102003081d03400901d46000b055a443e4008070707030701021820807280441201c030070400004464000c02c5d00050240900f420b802541c0c03440c050500051000100743c4880c0e0b03000030300908041e056501d00c1d01c4140c10a0a00302800700080d443c0e109100c0307c3c1c004404542400641182d04605d0141380c102e000d014640d06129010501040c030b800180c0c00c07404042c0010041d9000b00b0284440e55503040c02c1c0c5150105610b0082c1c1c51442e200c0702017040440242524040d000380d40750a13203003850070b408014000c0d80788149580d0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 488341852 1250 488340602 488340631
    0x1211090901090f030f14030a021902060c09010c0503090a1e06180509250e0a0906152a0f030305070206041106070503070501060e1e0c0906030a0923010f0e0604020108 73
    0x5a5889800c007d51180b90080001a220100c03d011400d00304880458a01194060b0003405449a001c004440c111002402d00c207280141c0707803030100c1c1107004030b41c81c980d80103c3e420300010342040c050380c0000603521080001803201e91141002d440c0700172180305006861881c00014007180c00c00c00c100d2500311092103100c100180c0e40007929034074100552140000250351b00389004076804c269456001901111206000715414030013003d00c0c40c9140d0310903004001da103a130310f00b00c580c8421240c5400090b044000142c1d0743d8150900c4e900301040604100c0010345401c0006004a10214210703009551004500030641620f80820605400c80c0a041e200f500082286200140c401d218400040030a0580c1001c245001560102c64641d410b00400000f0030140811141c00e00c19012100881d104440158603a1292002d080c001c0502e104014050790000c48140c48050030803101060340c0d0100c00080c0601e590001144042e1548510004c1c0581e0001022038015030086114a500407440c808219 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 488343102 1250 488341852 488341877
    0xd140f0909070e011d100f350a05060d020112020c1005040311062806150e0a090905060a0b030a051c030c0f02060a090303061211090901090f030f 64
    0x500c0e00c1e10a8591502081901d2681042960008050040025035403c034010304010031000c28246135140d41e15504201204094041c81d90003410901e00b82e4519600d2401030200d143c01a11a00401c1c2c1d0102401e51502e8000030540010f5000f481d10407040070340032200c000b109a00543e80040d00d2807208180c10303002e1100c1440e102d0104666000c10040c440b001c107981c1000d09002e0511314103980309404981202c81005180d009603e500c1c015480c4201c00c02d400419242e460360000d100e2a04161900c544070f1041c000b045a0203001c140e030148045403d0001c882c3d50340021000c80d1a1420004c00343c0e041003000461380805a071142003002d07005001d40d40b07a9281c80d40d4103414119040100020013060000d020000755152190740c03540900d03800c042009820201000e5910f50000380b1001792503403101c0103542018480d40040005003c40b054218401d82c82e464a00707118540c114002d402940d6240c00110310320814003444003c0c54000d1844039203c046c584040350618181600b0b5070902843c0f02122 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 488344352 1250 488343102 488343109
    0x3080f0c03060607171c0906050711030406080601091203021e07060c02010c060912020f0c09010f1202310f050601140d09081206090609060f04020a09080f010204050a06020d140f09 79
    0x1d041b04181130002071070a66071030500100c1f40003070070740010006090091442000e0000c11103082d0f926a091580c025952a00100c03005103250b00000420011440c0d01403c041d00041d011000c0c944452510074a0440103404594851042c0300b203900055005e040480035500500d0f100980d10b00a44020920001f15250f00700840b510755141c1005901c10645200440400d1259880000702117031036000302d51505c204011080601d01503c80c00c1c114800301d92003150b4a20b416220a4102c804c51b0710500342d08101d62450580b03241402180325410a89038140701c44d0a449068454a0161524a40300412148001840e040400380c0076803603580b11844800f180343c2c40050040e05c0f4201301c0710111481c224003807082848000e4030142c0941000814072038075540344000113890a40035580161680c8003250222591380c241d47c800b0046015140b09160000e0064001f0800e441080c0d80f6407030225a2040126941e01c1640a45000100c0482004101d041e10074010107519042e40415418010a071000 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 488345602 1250 488344352 488344387
    0x801170a05031914030f0402100302070f0b060f03030705030f030417040e0a0e060402090a0c05131206051b091909020d06050f120c0607021c03080f0c0306060717 71
    0x102c040d0b0581e092000d80e001513100c089004058105100d036400d41c1424420b1410106001d40000d00c5020b1500407540340c00d20a5050700c0c1c2154012001e401486602c0c1800c810407441965000c0c06601101c04583c00c0d818000111011260b014000b980340092400075800c181c1c0000d00304a0b40441e404c0c2c2005a000f2048010300080c1c409418103150905002c01c60404403142604000d5440e0420000c000150b070381d480d4010f500c203001c01004070341104080801c555030f00c20300194030325004030040e0100c3c00d1394100204102e2903204030781c100320507150000b05c031007022036031800300b043e510b0200548801411b0030f1585924040700103526031040c58641d20b105040e82c02400306541c516568030010411407031302244465400c44162458000d0750610080c481c2c441900c03880e80d0303008920024406046444a00c80401c0280503601201840d0000d0b1070004c00d95401600c500e0054030b40c0c4030210708860490011a0f00402d00109902e25200056581c003009980c007911207880c5c5076040c0104c44030305412210 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 488346852 1250 488345602 488345617
    0x6011e051503150f0f1e04020403050c0f040b2b14010c03060608060109090b0d0212031c0c1e1205090d12050c091207230f010206070801170a0503 64
    0x201c592640b800c0c0f10140364402d542e00c040342c0300ba4864031102600e901e481d10b01d040c24100945100c40c0701c84103100e0b0555282c05441030213800510004001047c0000451b02c005803507012900400700b5010381c010072065400c85800c0035400710a0129030110106921b20321000f0701c84241488400c080c49850310701e02d0707050309110411107945841c921105140d152282001604050618050904000c000200440351a0291410786556014504030b20b070b45484030f03e1010741d401081090b014410040a0b5104d402c15656001829031704050481d0440d0076010702d00c030340d0103d66200341c5010385042d10350510400b40c0e800c1200740801c40c540840070b10030b540507a0340f003003241d9801414013984d03502c0000d080c401d90b145111070051400c4140300b905142107003141c41c007640455104a05581b91a21141006016800480710703d00b100c82e10003c50008400141c0414411150040d1400d902001641ca4620880e24040090000340040c010f191102c810301034091000c0302280e9041446030381d1145503034004175 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 488348102 1250 488346852 488346889
    0x1210c030501060807090b1605010605043305010e01030f0e1b01120b09040f080f040303080f0604020703200708070306050907080304031e020d0f11090603030c06011e05 74
    0x3005229094220b080140c203c5c0301407030300c01c28642c60480b149084d805224403c0760b089140c859007605114003500090301500c1c0c001c1081203040d0302020700010f0010410313130808080340c1c50f8040380380744031100d80302008450303040e19a031440149800046000344054424081155524201400300c100100400300c0101caa50007001c00340c05640c0b00141401150801da02c00603828210f52501c103840e914402034000c1c0d4080010341c002c020500e069651401001001581c260b000f0030008140340d8080d0019000b00ca40d415011056264641440141e129000c0043c000c5070619110580940e100346490101ca21080141d940164071030891078100302e840d51040d43c0c565294828000000000d010520041641c107008529152071503031044c2450301400d8a03000e01014810b012401d41d00c8210019020f1a8080d0440200115514220300b0480140d40301e240a480c503000040ca43e4213000044a0202040d10010810b50380703000f0890404110000c15001c8155031882c0001d0503881d05c2001e2209c0c0c01d1440c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 488349352 1250 488348102 488348111
    0x18040e0a051b151615150b0706090b161202091008040606050a0b07050606010c02011709010f020307031a012f0c0303030f040b09031606020a1116030308060d0b0601210c03 75
    0x207041c01050750880c120721780742251600312a102c0319040603031075508070341c5180c01240d1107000703500703008005105c01c68014000942e8407040000c166500b0204942c48101500c1d600030b80000d81441a00324000d1a01041c0c210700d403280300500440c00b0b0b600550340300c0d00c1548049900ca40b104041582510130f070307019881c29040816880e082003c18095903601c03800c286400c940d041c01b00e400003030040c14200920140280403101040d2052000c0d048003a2207840c0303040c00e40d41da060508004000700400d40d40c6144910107075070b90350300c0c1d98030540240700c0d44640c50361840006091641c440790300d0500c02c1e2032040315118101c40d44005440c184003451040a088071400c0280c41d00c0e00304182180b200420300301e13070f50b00104240f6170303844594040550300c1074100c1d03401610340180d0724094034040800a020b080c1031181c40342000f0f4112072142c160055a00c03a9544603442e072551014004d242c0b1801d031005000c2c885000c001581544507200102800d408000c800c9854045120120101d0381d00000010009448 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 488350602 1250 488349352 488349397
    0x50f070b09010e120a15151202040f1515020703020411040513090203150a09020a0b03070905030601030c0501390b07181e0b18040e0a051b15 62
    0x321400192105440700c80e0403040e44c1245030384483d041c40e4020031720601c0103001188450b6507880303214540c1804000301003043e2034588100e81600e03c490202d01c01d60400003c0464564140100c104d0041e50302051601a030400f200c4850841d0002e40440851142c4000040075903954001d00c940404602035095a582c208018000220500d0551b14042800e010818005890016480f9000a03106007200c40c580c03540740154014110558010394014071408000c221540c08a0040d4050100d64441100c0c20b82c0d01e41c14961145c00911000d441048100382c00c00c41035003d091002c070301c2c400030207100c91041540d11201c18811119005400705900700c10025041140024486030000d85500f44400d040c5184140300c5501c3c1258010500d0707100c504a80c0f03032425020030390028042d154903013100340c460a034198100030b40106000014880c0d420075810002000007c2070004840740c01c040906011400030003450b8001ca40d52542c142c015100a01d15508240344c04003421201c00130400380c0c18550701 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 488351852 1250 488350602 488350607
    0xa0915050103021002340e070e03010b010306050a0506030c1e0403050d0c0b06041d0a0503030f060d05060c0a05091005190504080d0e061201030c060219031b050f070b0901 75
    0x400000f40301950b0142400c1c290081d05141250406c640c80c1880e2079590b921803080004001c016408011091203007010b005200d5088020750b1020041603000b04003c40182d8011002c0c1d410034440e080c2c20003540001442542410700040d640001c8085880e0703e48071250020b481203100968481d01c000d80702240501c1000402c0c00100407070035282c981038843d01e8580d11034014020313014100314482d135502c21140c3c203103812f007101c2255440312070710070750707095110b80c1c105162242e10458030204941da03543e00041440c40c010502030300041c2c00c40010300031556182484019075021648020600605100121041c1d480358400a00b01c4640d543d1240c488890100c00842d00c000030f0501e0041c480c0038070041c005c1d02000030b142c440c42085450f003003a0fa1103805010075042c2c0328221040c12881c40c0b110001c803e1001c055070000850301c25078211290300c20a2810f403006580e44040050015902e200c040d045180d0142668507440d0151b019540c0c0a6109460689400c401d82d0100340c100c280454a500a0b41c0c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 488353102 1250 488351852 488351869
    0x91903020601030c0803120105040e070e0703240605030c0d090807030f0806040c020c130f05010306051806040305091e030a03020c0102010b03070f09020f070503120114190b030a091505010302 84
    0x404017000310b05050641516000100d0305004480c050b596441c1c00410301d4008210a05c02840030f108030f02158181001b0003000b07030095400400b150951142501d1400304010076020032039141c1c4d030700c0320700f180c0311038007442c240d42d0000001083c0310b61511403000c04100c40030f0081060f18400d80701d400d25011400c8024083c0359000b40800e2155282039800a041500451100c100400c00c1b900c480250700102c400200070004140300d00c54051400001008024503984100d0040e182c1e00342d0064403203000441107a980c541100c000740000c9091100d501541010051480703a504400c4600e180300c464140030030701e080ca40080580c01a070100d03464a0344c958082c8108c500700c0320103602411516080000344d031100800d5108040d00e060780003c1e0100406451803e84100a9022081e6541c1c0c03d4480103e80300900301b8001d0041c10f170441a8507800f141b6201e07c80c022030790488062224000d24188a000303d54200030065078a40381c50f880050002444200e2100c1c2c0c203c0742903400201c65040d4014081c020 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 488354352 1250 488353102 488353109
    0x6080c0901090b030d1107080f0d111f020904060e0f04060c0e22021620010806030a0609080f2a01020a0816022e0b03030f070308091903020601030c 65
    0x75141c040b0048194a010a08442150940c1000210800294031b420325142d01c50340400164040d079800c101d0510400320f620f0403038401e071b9500d078219000080003254466040e000a844042c04210341341b140c0e80c05980240c0015600100006080366907202c40c501284000c1f108504001819000c00041002c940b05240c4004458545040b03180301030000300c0c03c490070b1501c101085e250000e8107401e2202c100c1e01281d0b42c007041c002d820582c5607410b1600340001205140c0c00d00c150001070325561490751040c0c42c03a07441444024018170a00d1060380300d04004003101141501c880e40100606203910051000030003080040189405501d0181e41b4284045c404603041b10510b030340100180b0b6a0564864862034200c2d01440e000e0480003815041a4078203c5990040d41070550b1000704c0e1010a031094a06e100c95003851413040c0a1008950704245c0c0301d2084619041d030780b403010300c0018040383c8102c941c0f580c088652001c807070902810044c3d00040301821001240141c3c003510042c0308100c6500000e800a = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 488355602 1250 488354352 488354369
    0xb0d1502070c0f0b09060306190b0a080a11042322050c0a09030314040911090112110d0b150304060509151b0d140c0d1d210d06080c0901 60
    0xe01c1c20a48080c0c01ea1150202c0d142c03190341c012002c616165100e090481c102704d4404900200f5680d00d0041c41c499800c001407080103c3d40000002e0451441c0340075004140e00c0c42e000d01868241030503203003140100754403203a100052041803055401c2d1207803910403811724401011410800c0900d14030702d0540f40010303c4210f00503024424100b4981d001510f0380141d0343e1500b41215000c41c000d50040d410301460b801918540e092425490710041c03040003e100300c5000ba070700c2803c42030341403400ca000d0318003800768481d00030010032500300e0918895001c0d4680b000020704048040c1400c9c201d800311500b0580d81a1742c025640e40c06c0c080c10310010014005d01030342409081007a40f03081c41091140c2c101103400194005400a1b1207440403003154001138013881c4100e00400c1034208031040940d6504110a5080e110303140820b640c1070904211104240b60400d00024280d40c140c0e201500040c2d116440101e050420910002580c812a40550030141141000074150340441a041000c0a601039112089 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 488356852 1250 488355602 488355629
    0x31306181d060d0f06051003030323160c060207140114101a090303031501121a0402070203070e07050d18050309040902010519020601030c060216090b0d1502070c 71
    0xa4400507611500e0744010200c818005103040760401c2c40c0503102d00f8400070509072400082040000f0800582d000f0760b03009950412082146400446c000520000103d0103600001c0020741c2441c402c50303a91030440814900304814041594884090360070800044030f83c91103200d40160340010911900b000034002c800e210601c5e0600005503218140140a0901c4215420820902001e0740c10b04a8045900180440703649140910740c00320b04c1c1e400e0103029400500240d20700e02d003036141402442285040c440d05024501000781c100b00003075024250403070b00b41c0503003140001c002641c140460f100360440d446003540c0314129a0400c00711049480055100c040350b43d01100418400400c2c0c55003800e00b07580c00544000d06000607512405850275050960500d01c07000e42c40194086056030403284280700404149480da0002e07a02c505100b89640804004d00301c0810411449801015a03140040c2c54004a5a66a01c03201c99142003002c0c10001641c00003841c80400c1070201c040401008a01c01c0c516 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 488358102 1250 488356852 488356889
    0x5060d021207210527061915050108100305010501080616020a0804140409060203070504061d031507180b030403110609030307200703061e0b060d0c0203130618 70
    0x14102180c0c8150703400e80f0b0355030f41d0008240400007181544280043e180034480382114400c080d40e80c0d103007140c1c7c420055508a10346108070401d8015040c4107040e21003a03007500c508040c011911990300a01602240704115000404130300e00788a014060111400604a40d240500b5490304400b081c45c00030046511064844000c54842c1040e0b500b81d8014284079039020000000040203000744410180c1414400014400e202e074003d401031040303400310384558001e885400300001960b107044989030b400d500011840c03408c101c059950300303912480c42d0a040c88090034840340b54080240c26004070388068400030500090503000b80e103484e030300b4800300010421480c22026964a900000d8101428010a030301d500c0d01c0406c3d42011800c01c01403c1701111602981d0f4101500075000600c0381c0c03080e20070003041c015014041c5003c0d1488c103c20140886160050380104100104050032000086001c140044441001000d140a00800642c0d0311044c81c9007031142c1d19801d413001c90b4803001c11242100d40c0036 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 488359352 1250 488358102 488358137
    0x70605030402150a0203071721040b060409020111030406030c0e041b0e220b01030e0604050303061909051602010e0d0926030412050712021c0c05060d021207 69
    0x190803011401d40f8183d10348511034010b900c0c600542030028061a001041d40c0318061882002c0c0c420310002e00b2405555100500452001600c203a601030304207207460000400e281840d800400600c1d1062518804010202554038110380060b00300174002500d034410300483c5544140d03004403244c802c8030104100c503250b4505840c42a07601c04200288922a094040c259030f80041600350400300c45614090301800c00d1030308009007048042d042c0420316103114044a0400050038502c10b41d130240040d8a141c0303400341046007c2221203120502e030501c4050202d50603040d0f0140ca070140385c01000003021030201e0100070b0b080d41c0c0b01180b4405107078851000c425880d076000c001030003240d240e000c60602c007281c041180790440304084440a8a4840040c6c0042c0c03030304600c6915280d0303c0c0114261055551102125050880d5001c7c001e0f600040720b40c0c0000314074400400c0d400c0d03150b200c0c000a1942640d541c0c0030580743e811098103000c030f4540c0030906012801b00c4502c2c141e071004041c54540c00c045080e0240 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 488360602 1250 488359352 488359369
    0x807110f0402180d0201020c041d06130f170f0c06060f0303130e1905130c0815040b0a1d0c011e05041502010b040f0b040b010305011a0a03060b07080301030302070605030402 76
    0x1441a0f4130240b0039000e6900a00c0b01c5118a0800b030030034414030813041d07003c0c0b50000082042c80c2040c8a460005040803d1042d1420000703680025610440c45440d01c3c5c6001c1e1400010040250311070170486030344c07402c00110040000c2c01c40c0001910140c613280c420480c2082c0c13074030200b0340030360000c00034481460901c013000c2d810f50319684011500707502c4000c41da0001c04101d59070750001d1407500050003484c02403070341000441031040b140c50401a0301c44d01980d460384c480c00707980846030744d034040402c00042040400a41c02010007500003200c502900305400c0c444410250200340d50400381044601d540d00803035801c2010045501c11140c00814030300100316111354030030200065034192410400c13034030039003002c500c4c0e05c4001c0c030501c4801503910401006212410f01c9900c0b030752030a00149415406401803e0407100e40310380c071074039403048210100d1450707100020b03c40401d40e45410104c0d2658890010740311840c0591006a101c2d8118a000b901e4500d040e0011030074042c050080000680c0d9004c030 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 488361852 1250 488360602 488360647
    0x8040504020c120c010b0a1205030f07061e060f08010207020f011110092102340b03101401080c0a0c061b0f12060303140c03070807110f0402 62
    0xc00503038507908400780c1424203140c0c0e50820040c1034000380c0078810150540080c5104201150f0540407281d0303c1c0e00d45072076100d050000070555001030017081d03403801c0d8200141007860300940b404111b0440c1d9026a08102c1c59800e08407009aa40305001c0c0700c16060109800007408a50008615040071074000400c81c0005035000380c10008541d024060781c00c404d0002106051142d0304c244455442850100159000c8141480010841401d1011203e200003950300104103d04103011015801d260001b942d040b000021412200e0002400103540c0d05a000542c840c02400091030b400508090302d20010880f40c45c400da04101d8140f06100c440c200f00c6040343d00103a058144030700d60400502c0c00101900c608a0040d824100c03000007440c02c0c0c0c0d00305065552284850b52208840010905544100d410030b00000d80007030002203215a696104900a120642c6254103c905061542c2e4903c15158032802c801c940d880350501c0d400c0414102540102001401280d0660030708c032001580e218064800309 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 488363102 1250 488361852 488361859
    0x70801140a14060c0304091b0503010510300b03011802090109090501180803040311011803080408091507050d05031909020427051603033c0305150a03080405 69
    0x211508010f588060031101114042002e0b40d8031a903a03040c10740001c144620044100b40000e40403214218440d03002c49043e039400a04030030890480f40d5088540e0301080200b0609000c100c01410b0180b040c81660303e450242c103400c02f041c20700c224803e16080d40c2200d14841c1e0b40d09030314080c0d0300069641c119980d042d9814203000140d2121681000c0303016060383c1410b9041e040680c4410380604c41204000c506c1103000341c80340703814421100c4045080311481d251100000c0251480840028800c0003d95000b0703008503122424102540000380c03100d0312802c240800c410700040c20f541000810301815a4503407007402c141d821403409100040d190f43d401031000c94440c1d5507142c42c604664440d80300ca036403181242228241702e20410b0464000b940001c02c00d40d6203100c0c1200c00e0b8100c0105440c400c0503264103594420302083d01d20f50b41001c00c988401d018040382d42003a61140820304c2032907601076120081d41c000c1954141040740c40e88610030012030901a1200300001c2c004902403c088500300c0f141034 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 488364352 1250 488363102 488363129
    0x160b270307080a080709120c060e300102040e0708010314030f040501140c061f0806061e0121150e060a2903190612150504020111010f05070801140a 65
    0x1d15080306d004141750403540c290490b01e0301c41ca0600002d00485002d680e01519030b010912090030401c090041400812140100318066070061421010f440001316900c9000250510b5101c030b400740c0c00c04900b290800001040e601c01001440081c10704c000701002214055881c00e036418814850511550080505101135074000290032044c030411607040d0300c080010750341982000c0744400704e4000d0034644a0180314205102040c41c00b0040b071040d025613801828010080d18008400c40c03d1150a5071460510a51075074000101889016009100034070610020307440004244030f260100c3c158005038030800d59a02040461340303601e030341002038a1402c808680501e68400c1c0c43c62014074800014411441d02006204142001c40007256140080c13500501c01c03d41c860058203984800b5281c094001070680028a100c90810381c44250407e00601d0001d050000100480d07081d540040f484c1d84003195074108001c0300c16440000c050140182e00e00014802201a00195050030540034a181c0762205 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 488365602 1250 488364352 488364361
    0x10050a0c021918090507061412060303090303161a010b0901180503100b040612020a0e1e090f1618050c1902030705240705160b270307080a08 62
    0xb40d8215402018107504140c01e4029100c0c002001d07280c1c02000300c0b580d20070400041203950280e1009880c1c110008039181c2407050010312560400c501912580c2c150000304181811924180000e040c0a101d25007541c0c8a10414a40361100390700d208a0846180e852000521118680c4030845155100900c2d0003150b08244a250003011a81503004903418480c410320351503003040d50782107280b0000c0100c6041251a0351401c1018401d06007040083d4050308102083c0440314800c01416005681980110303445505500c0300005141c065610b82110750000380c046100c1c440c100176219111815029800f41c4500d0308558000700c410f1050200503e0b91128002262042032800f81d40740d10012103155030340e50904103406501e030fa01100301902d20b4083c011a210946d400c5d00f1f040d45454820101001d0700d0390310010202d900b5008031182c120303034192001e2400c01041c286000c841c0101d500080310504080d111400c200e0030310003415001600e810902c2040007042d9101d05a0300a0103c5007450070240e1b59 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 488366852 1250 488365602 488365639
    0xa050d0213090c2106051f0504150c120c02011e110601031a010b0301031a040204020706060b0301090e0111090f0102160303020319030213030602090d06061410050a0c02 74
    0x80c0d400100c5450b1800c0c109205080d480f400c08910702d0706100030740302407980013841d0806440c0340b8029140c1064291244010203a0201800c1c02d5811152a00c141402d860301c4030143c0c05810409002d0004145100350300600541c0101c0502e240401d04111200884550010307103150140021008400e04c800d0042c05028022414030043c20300150640d1520740e120301e030020040c800d10584004da084800c0011441c001c450381206d060300c0d0403140a4810361404001082812001042207801540a10040c40018410300071070001d007500001041d00c96040c40d42801c1180c1d84051020180d83c14190400302c000300315411541004029581018400d4240b8010703454000300082e81700242609107030000c14994040301600b40d07000400803940e128507003c80200c0c00d038041c81401d980c101c20300b0b0030100000350150740200940c0303402804080400c8841d0715250f04949071644030034120300441451203240e291002000c0203800780350610600f442c0070140014440c11141d48024060341084035021450071 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 488368102 1250 488366852 488366887
    0x1030b09060a210b0c0a09060206010602061b0904020711010e03011e090501060308120912030708070e0a17030d06050904200d020604171e151008071508010b0a050d02 73
    0x160810b4280c004c90505802d188016400420340b50000342082c000800c503184040f50840c102d8200350300902e410b48032400c130344440402030784041580d64010003c50b00b55072603500192480074014141420030320710380030000d01108151003070144a0f03407403e0403048210810300702e440c06502c1d84500004034003d0503d0910b00400c0076401c05003e070140480d00c3d000041d10001c84911070a00c0b801590b100e41c9084c41c480500d80010340784603000c02c4401002801c00b620480e04030206081c018000d207292691650400a68140ba032040b80b00d90308006005076011007540038a5005040940701285640f406803503031070450960503404514000d1680e20031301c2c40d0359a200314694040c1c00910305692650780345098090400c0091100580d030080a44000b143c07402d221440400c0e40c528030152040a04004844100504c020442d40568112020100d100c040800c0b888000e081c3c2c0582d40800c01d0000c1401a211000582c0000303848001082651406540802600e0055104040151f2543d003038250740ea4442 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 488369352 1250 488368102 488368169
    0x70f050c09040807111f03050916080703140c1503040c0b03010b0306030606090601020c1c12030204050112020a020a111311250f08090111030c01090201030b09060a 72
    0x380e07101c824042408035810044c090740c1c0c401c100c1c130600100001d0a001c1000043d10700348000c1081410880d540500980056600849400075241e00c00c1d40d4115540d400e150326000100070b40c0c05034009200b00003004000300c1c10660ba0328000c2685502c1400015017036031482c00017654518003c0085000c01c070300c20030088042e1030306c2d00b6595240e60712450780c072849400031101c0611a02c60100490035600b0a00d4480b406548182e0282c60f50442a1023400007410720b032740d2141d8010303c542c240c42010440c0c6031417400c3c036088c0982d07000d82d03594540310005045101a039659007489104215a0100c150001014220140c1c4512a81ca07070f0480703000014800070024882c0198241030032070319000081c011005081406010400c165100343d4940300307120301c2028110080100b0040c9a0b01808210300c2d102130004030341e05140621307042451791619821500540d0f0503640a83d15000303003a0440d80c050140c1101207909403180f20352850940300040308158280b00e020b640c00d0b00381d05038a80c81a81c5014281d0306 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 488370602 1250 488369352 488369359
    0x5031c090f030302010f0501120f17040803120907080708101d01090b070207060c150e0c0a0e0402090606070812070324031a010e0106050f0409180203100b06070f050c 73
    0x41c1e5803814040c3c0a015840041c60b5250310701400071880d44441620a5141500001c2960a280c0d25640c2c40a01c1e8011480d07488141d4828040022843c01c2000200308c040d50125150350300742003402185141c04000c0d04013203010780051100b03020102c4001520b00080000c0d080116010642000c100403141424403520115405c00801030140406000f085005101c01e03401c490015503550030446564039501c400a0100c07100840060301100560010b0601e0106e40302911694104c0130b0028003c2c04456220315180c0c04480d0801083d85010f90b5900e920032800d881e03041c0f41003040d40c0c400030b00340b00c0e6400841e025440039010902d4a407117940b00004903112071100b80f804001c140600036111400c0d100444095440a440a54a481440c1214101c444410b060b0301c040c3d0034400c00b074a242c1c104074104d904070a8140800207401d45180900899021918001c041c6603c030703030042c0b5090401551014210070704003890510251035000486084581204410310000340e54608582403480c2c001c40e0030f60 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 488371852 1250 488370602 488370629
    0xb0a0f03060203150405100504020309010b060310150516020d051002130e06191503020f040902030702010b0307050a1203110616112404050a0212030901021605031c09 73
    0x2000781542c0210b00480d04480a4031501e4000c0c4100001d41d80c085170012180003510404004a05280e00030350341082000e070010032000308050100b90660800c80300307a041881108410010207521103101c1d03050b01070514100c1c5c031305000800b0031503065441680080c0141c1c449e0303100300305000051002d09460708908030305541d1504150381c2e40754049580d010728100e00103400080391207407034920545501c00100580502510b4a0705081e22030322501c00a24005140e0208584803416108000a101409038041c0040c0c803401e025400034211424514200c4c0aa8030280080c00b4654640b0780340000c031110010804800b5201d0f14003100c4442c0380c41d61981c0705106d00e47c00c0c00011007130000002c400320500c2d503c00c503140c821845943d0307a03191801d0b9920380d000e0b54490380401a544140c1c07000d038094002c1048544c000340729401b240c4080b15400320300f0202c0d040444c180c0b403d50390602109505140a0f4880c052103403c21f40060388440320052903400034400009040c1c0010300a203240340044c198000000d1 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 488373102 1250 488371852 488371859
    0x10f0b072102030301090e03120106080c0d02040e0403080a1808030c0d060807030b070f1e1407030806090c0703120f06051e01120e0307032328050c0307060b0a0f 71
    0x9540f60006e0140a00c224140071210ba041400002614000100081e592150707034a480f81c1511095405000e40503880d02c01c01043c402c45500380002d00c000c0100607900006480d0074200281020005000d000c40d06040c15048034403618000b5031044940c0d0041c8603a0303500c0d00c8100b8020602d01ca81c4071086040d0342400800180010003140480481e0302a03036508555035112001222580c2540903a48003141c180c04203200d1880000c0380f01c2009806900300700c40d03c1111054040c045070004041140090030900410040307007000c07001c80740c00a52100f806401c001d1680c1d07001d0940f4624890100d10f16640c1c4107080200d202580160f0014031014000d040402c101020000c088004440c02c1404901c001d014480c40403218400c40c9281281c0d280658148141950129683d80c40158801c2c0d00c815415000381840e0f03800c0740103102045a4025102c940c101080a0420841c202d401000c14418103000c181d1246101104450169511801c00524424184000340d400140c40d086421034801801c80403 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 488374352 1250 488373102 488373107
    0x7121b0f0c0801110304111c05060a06060e06040b18220c08040c0b030403110609010b030705060c0d0c1406010314190c05040e10020c0304150503010f0b0721 69
    0xc91014040c0e80c03610011512042c02c00e0a8401c000b8501c0000e00c01000001c02160100c251111001c1b0f000f40116417103409890800504500810b060719107420103030070300c00c6c86040e500c5404000e100c5801d029413003400100000b44640510300c43c00c101d9283c0018101d0382d4420560450b841030f20014000b10128001c2c00c0d184242d1907514010280041c90002d000b00840c1c01144214401c550100c0198910b23410845e408a29400292080b818414080851050b4031014414203206040d07a000000c0c08040f040700b054500380c1c69034003d074042d42081102d2000c0c800045040c4040d0881828007107800551031a2451690750041000d1585014501c000310030400031440000c1050072490844036001d013400d032050403015124400400342d0200380801c00103800c040e0824010b51040f041903400b03040c1348040b564240e13402074841c4440f54000040510144901a000304441c4406141140c01d56050504011455115004140c0400d03000708008080100301c640340b80c50003c0a051072402e00c0e2040314003 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 488375602 1250 488374352 488374373
    0x31c06051e10050c12090d0f050606030c0103060b0f0a0c080a080612010227272505040902070f1a042d02040c1e050304030e01031107121b 61
    0x2544078011000c07000c0b440038800ca040d994500c03189406044200c60a2081141c243d0041502070f13000340c1801c5001010440c4202c1c11290a40204090075280c58800205802c0080c0d241c1402c0c149854071800340300700c1c1c0741003050b0340c1045803080710700360b555000382c506442000a1450043c046140022407140a942c80100c6c00d020f41d4040c0c80803a04111400c100a00380d01510111841200d81154146444e020040322682000b1001d000c0f40c00c4d900640211110f001c84c00f40e0074094154404080c07050443c054080d50303648190070b0188580304400000000c01920581c813502004a40104e0b0080a2040c840002d9049540c00052507204110448000d002070900701d4040d6642190b1590142e089000240105142c0319020620958290b4541c2080004e14818202c4c4041020003580c9143c00042c484052806240540310603840c1e1416203002011039034801182c504140c00c210f601d0180c90020019500c84503030042d504011100c000720308682e1210741100d010b0618090409040a1241c080d80 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 488376852 1250 488375602 488375659
    0x4120216061706120a0f030e0414010509090102041505030405030409050108060612010c0906050c033907030305030126011503060513030503040b090705100e010f020708031c0605 78
    0x8800d4503643c41e02005251201e00e2440041030704034001000010301e00254000c1e62600c20300f412421214820b01140440700800c0c04122010081d0006100900d00190243d50111400380254509410400c0c034842c0c0e403100c25000f106002c00480483c0421405106860240a00c0c850070881036079610341d041d960703030030a03100c0300d00903000900b0b019040700c810b006a902420301900e8400070246021006c607825070281800c074001d8002441350324910820783c080c00c40d5403041c841d200c042581b1010906001c2214451040c44203900c1b444003040082c0d0860f007960304560906404000140440442110541c404907580185520300303131800e40d602440c8204842964000d0b0700c10003241c1d444e200a0022034600c814046c000c12014000540024803039a80c0c607130b104a40c0410740e02d102340d4030790200348001140c0d1901c030301041503401410f0b41942d101d09501c61041091000704411450201929203070302c2240c0d42c412810711030302a20302030b454103600540f000305000b60001100301c49150541d071410700c8005 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 488378102 1250 488376852 488376887
    0x1e1113050106110703120f11070902070209090606010c03081815010f0605161103031e0d0e010911040b0f03030f07120c05101a270c120412021606 64
    0x4030203c1c042e40000707000029070340c3c404a140d02030391805030151142c41c0c5c4141c1d8101081584842c010003400140501c0000f800c0c681400341c2c131180d10b481003010420f80140000741c1c82d846081006445d07a40a480c00c01c1c91605400c10422a465812900d04001c03034281c1035102c03074440d2400414941010840c89812600414004001152521070840e03882c0310b0542154540c02c014628070012460003480c10403940801411280784c103032407035218a2000c2660000e01c02004010034001c440207244d02421601c7c54956008001000007540c1c1c02c5c4505e00c002552074019581c40400050a8681d4002c02813000402401c9913110701c12860150340552183c20201da10865490380c1c0e4003554005c4141219203130f40140900390300c100c4203040c64003d020211000c01040105150084aa00c8203980c00f13070301405114122101100403118111403034400f43c42070360412000c005900d403080ca42d03900640c000f9440303280309070b62100b90300c0700300d1501500703000007541101d5500001072480e130400221230280401e403 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 488379352 1250 488378102 488378117
    0x307120c0e030c10021c022404240209060d09051603031205070905060c0d031104140d0602040905130c0e04021021061811071e1113050106 61
    0xc90115009109401c0840d01a4040f044002c8185451880404094000d104a468030625080b4500503203629024901c00350f0010703c0e400601c4104e000c0c1d10b8003070b0124a80d4800080c2001d80e01d056041d85034050366000c0959109070110b00441e40d804480403140000d00d181d44aa80c8180c1c01380080061210861f030328400c11180c0c600c000c44500900702101c0d05a1a0300f444060403130b4000003d050300502c0300d420000c4100c0081100c4d55194043d0800000d04801004074a103450380180499883c0b0f400d880c2107240601003042042a445400e40103080705070fa260000041d1450644040e000b01e410500b55107050004000300201183c4402107510b000b600c00c80f030f21595031600c0860311041a10060740041045691010450191490303a452503000d40d4480207a80d0301501c1e5000716200d980103180000c489405050801e14140549041040c99140c540d240c101c8503039561164071305030035070002509901c1d0000313002d000340100c92000d0342c3d401805000e58107200380008801000240201008110003 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 488380602 1250 488379352 488379371
    0x4020309100b04051012080705190b0f0108120a090e0a09170c0c060c0a1a01060905030f030901030b0a0306062606070804350c010501060f020c0d02060708030712 71
    0x500865000342d05441006070744a007841e0001c0c46e04e0003020010740b034108080015400142e4204110580e00340030350700601c0c0c03111003450b10300104440940301010700e500c07020060005032000b113480c000700a6904030140e95202509415209104594002d01610084000700540001c5070741015401911661804032441c0d00d50011043c1c9001d00903070069664090080e903512818030300d00515280f003407003003116180c2c261903464004030698031220a404403004801040b030b83e60010f0940024003c100d000d400d40b048480402c680c2d90060810700b41c101030710f0f044410000c4d141d0800c40b04c061600040e0910500d0346035015806a00d4404011a010200b107202d11600100046441e6002d0b0740301e9645d071003d5440f50b4072000e5142031074032400ca141c14055444480030144c0704951001c46000402c00540756100000c40b036007101c0059112a044c0641c03030001100032640441c0c28940c5450880b1090070310381040c0003040140c014900001c10810380001401691600049540c07014001c0d54002d0051084 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 488381852 1250 488380602 488380609
    0x60623031506040f0b06030411090a06050d08030c090901031101180501050712020c061c050708091c05071a150402040b07141510060206010e070f05070204090204020309100b 76
    0x1110074454a801e2448008102d07546029081070f00c0c01e84402c0b6010414600800011b42c0d507a1040d0b8044a0101075020a040303682010710b20030750b221114034400c028942c070f4100032541030380f40f03014020044207002001880201c0120155050347e140504503c149684078548800c0e1804c002c0e03449404203960060000012010f07900348400d445c3c0680d90542044150b036215402d6203d10282001076001e0354090b000c0b142c86060241841e00c540305c2107102c07040c075400041400c03100043c00103410802c8100400444020024a80c3c420102050707001200602c0c03403808503040e014904e001401c078501901c1b0600070701c6288005500440900140c143d42d4480034042100304d100c1ca216001581c0800c0c001d42000c030701b54580148640160300c0130b0310702d600001305070390030215401c076003000c02240709100c00d10400303504102c0d942c050520701b8003819050419140150191000321520410028001402011521150003071424103134050000d46d120300f803200203e80c840c80025036900c0c1c068500740c030034000c0e0f20307 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 488383102 1250 488381852 488381863
    0x70911040f03081606050a0f0f05061f0908030a030c021c02102d021b010506090115050d05090c13060506030a05100e01090920150a090306062303 64
    0x18100c0701c01012a610755a2110510707000461100300f02e10400110030302140317550013203900c10207400c0000207031a0048003101048076606010b542074649003c0c1005090b80701c01c8039001040541c440c142c04015111101114054129006881140000b00300c00c0c4a00b80c05420548400000c0d800395814460070301040c121008514803c040164032040103c420150315034030072451240014880741c80c05401003582c2c03d0340b0304081e020405050340002c550052040c0444038044510015000b440b15041c031f0f00000d5170410b03040c06841440c83c000f80a2040c90b078026001c44903020085d400501192810740304c2541c96500402c440f0b03002d40c00100c40c0106080d40761154906a0300d006000c1d600b561200242c5174020200280105400c5140c00c00103d40c0c894000b41c02170003084034842c00700700f01200345030007a0611031030103091100c1001d02e40049915a41c00303a00c1000050b0100e0401d84405050508543c10215640b014101c503141882c040340b040c0d0004c1c2d4007a100300b884141d0002907240790051541c0c80 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 488384352 1250 488383102 488383109
    0x9060b0316020f07090e030f040f080c0303030106080a0f060306092111030403080901090f030606091406061b0c0d03112b0302032d0f1501090509130609030207091104 73
    0x84e00404400e2000d0120b960102c45c40d071a80d00f0490f400c20346882c448000c664015001039080d40b4481ca820811818104a100c10004042c2d02440c250b526180f40603040e01c00181c107100002d80c076054040c04005842e4031000095812500c2031004980c24240b00340d074131056420400720382105611900b100b900178410f40025440040081d89009e04c0c5031918a0941c11443c6894104408904000b411601c0f800d400c9010b90b0041e1800262145461314030f204070317180b424a8050031041d0004010b9180d683d03009403042c19030580b0700f02c3c84400d00c010f40541810f030305030310642d80031499002090500d0f80c884049281c0300c07200e01c12146400820240c48460901e10b4000f0000c0c61121450070303070010b1207034000e59080650301110801e42c1c000c1032000841c102500711020302d02002001000078003451040841d40018201d01c40501c3ca451000000384500d80c1406200d00a100341000700c0c074003c0080c6203028650780c021004102c02103e80c0b40c020340320307a240c2c4120011300303080100c1400c0f1060064100c8044 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 488385602 1250 488384352 488384383
    0x10207080a1412031603050a061d04170f0d0e0309060403021009080604030e040b1f0e12190b07030c08040b0c0d0510050102150411011809060b031602 66
    0x41158680c2ca0898000803101c40d4141402494240c441400c0030300051030084c500e100c1140800810244000c1c11900e00502d0030f51140d00700f403401c03c08021302c080301c040b440300c07800b40c45901580c60b410003500c0b240815031007500b103000002d554400c0380d01d420058a03101c80088000c0c02a00401d40d00ca0b0b540740901015103034040b104000c200300625001348098500080d9040c170302030b210750350a07280782410011241500400ea0504400701d40740341901c075003d06c0180883d03440d4003501c07545d20202e841244003a00c5000384081050028625901d0346412401441441c0c1102c01c02e00900300f06c00340042041800300e40604115020852a500a004111070f90042d0790320fa488030355498035184544000907100754400c2008100c0d5044003802c2e80507092082c0041d0340e0250b0300c2450500024600b003103d80d50040242510f606103c000744204280002c0f6140034078007110025090014a40c600025501c01d1002c0c03480c0020000d0a482d589015521850315058268400c6400c0780342a070300c8000c484007942c01d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 488386852 1250 488385602 488385613
    0xe0d0201060e1f090906020421121409060c0c0406121a13050f160611150a020c0303090601030201120e1009080c07060203120108120d090503070b010b090f01020708 72
    0x51880c0c0d5895941c0d103500001c0103c001480e681c03201c103421564200d0301070343d14540000c1d0038880f02c1c01807901c1c8044d0041c5031042c40d00b01d8603c0e403504290000c0a01003102005008441403112405c0003095511040c0010f007060f59400c02c1801c0c030b982d25848809020f025500300103001038864a070000c0341000030b400101800305946060b402d0404c0e810014400c102c0b20a00301243c0c40821810400031409405590090814104001100401000c0c580c0f0000410101080020050001040407148001000603004980e150031b000400a4087d8408043e0300e0710002c42000000800024058102d0f8001e0326410500ba2180005031f041c0c80541800181d180d002c1d1400405508040d40008400b030302032403045d400c181c0ea00c41f443d030612a0590024006034000b00d2000365828180c0d000034010503418008204619105401102c940900c52201c0c0300c003540c0b50704103003c0c032105000701d070303101c642c00120030441d0360b1a1241f6064540240c1d2409010b48c0314444e02c510341c1e500004090041e908910002c18 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 488388102 1250 488386852 488386861
    0x15040c022d3306010210140702060105030319080411030607050414040b06030103080d1b12050619050d1b0f06020c030d081506070f120f030b090c030a0e0601090e0d0201060e 76
    0x402c04000a000d0504522962041da03001141c0d41c81081849040c0220000c11170078200f100900d00701041c1c01c468443e40042221402d00b045125403903516001c541003040303943e42c80d403c195554030112001507406014401c1042401d80e84440108152035100b502005000e4450090004640c81c52920340e800801c05c20040c4003044550000e0315040081850102e41581d0134042c20003084200c1c11040041b07000301140c042900c00074002d5603880702c025681e1146501080b94a100300d0441882041d002c0c075013683e6100203002c0f90b820303610350b2815500906010300360f545100a0144030f00b48551070041c0030b081385154403440d0208029110700c542e6950980191600a01e20440a9462440c10b038000001c201c0701e000500c40849868089014401d401050300c80f592004d080c100d1801041002c15241030804091541d90000c0642c03c8503400c0b54003a12561610725803801041412480704040c407c0c00c0c00040d04c450b003500590030284948056a00202d0000d9050b800c0c1c900030300076440350081850008 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 488389352 1250 488388102 488388193
    0x17101a0913081e09030106151209080412030c05190c24030b01120e0102040e010e09061302010912050d1206060813033006060815040c022d 61
    0x441c03800f189031001e461300140c680080d086454036885074400038005201c2d03084070b94200403083d02c42003104005100c070440c0d035596030b2424070807030040e0100382c004200b0b08424584650400803a4941c03140c100c03002c078001f070441e2507030010000f1000c50340301d425a100411925204103130a1600030348503c1040d0100380152050b40502409000d690401c40e081b00300404507107860103804240d180200005130380f01c1c03c100d4101300500e0140c02c9001100324040c28440240c40011700542d218041100300e5010b0980b82c40100d85824460388440d440f60400441392061110106503402043c14030b0320303100412420088128103440061082e500401e440c40001030443c1103045480381840c2c42854042503403540110030040411400601c250101c0340504104a046068881c01c13000c0c11450400b90060b103009060500b030014000e00082c0219196454000418001c210314056106210700b618880c040200c0d01128140f080d0428101a05c00c1001d80540ca15180b4400e41c1e680405900050200152000b40c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 488390602 1250 488389352 488389387
    0x71415251112040b0301080d0c030903120e040207080910090503070e060a030503040e011e0b0414040f05010605090301051f15050c01050106031a0405010b030117101a091308 76
    0x46003035a00507003060268070700c00c42e4001d0003d80402d00d060f40d00c95040a0080c0c3c90706198a03604400d200455a01c00c0100c0d8101e00c0780300490f0351014000c0d0554540f2a001c59a4041a031091034100d400443d0410070024a8030280c800c0c1d10b8242d41d003405078012554112247d201500c24507426412800c0b050004241e00002d065224030054080b0030f9082c2d40ba51074514550065200c0d40d60a54a50018054050a2044d01e540c40000400201c00903050101c514880e100d14840d615200040001c28019500c55820061402e4400b4104220f5583c2d02c607030250041d03110204252095280c1070000300c1105014006110809190409180d080c0c10f203a40d5240320581d0b05601d030706001c0d013808003c0b0150400d000e0a8060300d45503901240ca0303103c0320780e0852402d40209400c3e02c00c0d4200070040c04180b0600d800d0f64115104040c01c09500714045001900700340c0047d6401111600b800c0c2a440300d00c8907070b2000e02d10100305403145d400c180d40c2c030080b690036115100801409120100300544483d1155020b = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 488391852 1250 488390602 488390627
    0xf040b0a0e010b0603070305011a0a0207050f03011b020709060b130b07050307170a080c0a080a0213090f230106080a0c110a0b0411010302040602031b0307141525 71
    0xd1443d0a20001840345d400c1203a40e880013a84803401400320380e0700100e04884152900c480a0700b4841e4142c0e029403944450b0040c0c81c01503c45d24403210340e0f60b809401412028803c0d0100802e41c2003420802901d07040c2a00840d541542003245c00250100400b08641c0c0490800d141840e80600346400e00301d981c0e10445041e41c0c02e100500640c0040f50010b03901100c0e0b507170440320099403550644000f5086140040182440f4001442421b5074103070054421607026000c40c100598880b0450b242d4a51048642c00101c1c0303c600d00140b00d5900080d540c090321104041601e003414424205283c8900c90500b40a007900068004000c0340d60445190416240d540040c10701c842d4003a03c010003d403500d00c02c0d9005990164802d001d101c24005044103c5440c03200031b180a503d01030404101954034440d04030040030607400031803803003441c01050040e200c0140d480b440107103800d0307010841c20303a541c0003a800d42c05d0b41d1072031040854155205c0c004100c070309038070f00300b000443e05400081c1519480055803 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 488393102 1250 488391852 488391881
    0x41b0206060d0303090b01060c021302270109091104050f04290a03140a12090f050120030a02160b03060d060f090203060907080f0c090f090f030406170f040b0a 70
    0x5c001e040010a0b04501b180640b24540e1843c11030345450041160340b0b02000000549144104131207064503220520900d840c04044100305001c10313a041c0100d5003d4081d0340014912403800c0c807016445d2800d08020801c890301111246000d0442808100484410440d150086c1d910001e0308164245041842907000c0d50083ca944a0f550f6a40c9032981040208454481250044844401080045049001140071910b00291560304003071981c40c210b1054020641805048001c40020321000007050196010a0080da03844102e10180070755580d481803c46020000c90782d60100f046001b04040d02d201c0c603001442c20000e00e40c10348511004205890441010640350460b400268404210701c0d8001c103a000020600700f07142644050924410405030b20040d00040c84002c40d6a4400452903004131110f0048034041d1030b4216042d18000c90403008000d1030002080005405410804811801c040000b0b03140791a9140307525420340d83c1c011540204180c04060218176484680c0e400f803101e542c3c3d5003 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 488394352 1250 488393102 488393111
    0xb012006070c210c1b06020d2a05030901020d030e0c04020c0f010c0810060512041103191b09180b0a0603020904050f0705010807080417090d0c05041b0206060d0303 72
    0x3408600308541403548035101050943c520318041003180c40442c2100c0f451300098441079402c0110003034507910b048c41c40004107c00d03805051410440b0f0750304204c40c00058503c0310000911868026240d400842c841c6000d80034106107168083e009008864140d201c0340060400c4000c071104010082d00310480c80b84540c42030042202803036009104207c0c2e128a01d464800d958a1701401692410103150004420010144481040f1309010240103803c81d40c868860403030a8004400b00b890540c01111140c0c40704007480c515000e000c240840d001c0d4480003050040c07070142e01c4503501c205a078401188480303c41036404072540401e20f421005500040350040109000341d803500010104031050b00c06403030a4001e4413410382c0b106c0c0100100c400801080c2060a160f10340300c00302426412000b40080e04042d001c54204c0000081030049a11000004021121004503400c0640c688002030040b603000e03d162071403e40d41c0b0b22007001e40b03101c068150740c020916070303440400340424440b401ca01241415282c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 488395602 1250 488394352 488394383
    0x4060603051501090c180e06031c0509010f0e0d0f03110a0c0801060e0609150d06090f0507051504091a03070b2116030228030b012006070c 61
    0xa102c05400703041c424600c000030354103060f5054129600401c21300d00b88201c4880304e050041c103100744803049802c184190038566582e00007084c10700d081c903110b41c1281c81944440b03c04c0c240e0003501804940c0804e03607410b007003012441c1090b070301742502c0031401d030b40000d80c2048600051650708003001c002e07110f40340841c01c00c4070a40c44c2c1351401d01080422100c92040e4901400300a00074402e903801000420038031020703820050041003183c0780c0500700740c442c103254482c06056a226500c0c120b0275164024020015202035082c5180103115010701242c89014503140025076107000c20010200d1014240620700d003500d00142c0000408001010b013201460101415100307075018050400107100075501c00340e4400c03103080e02d0400e040240d81100e010104c042c0600c04801c0741d01498040d016000d00300140c3d0390402d54956890038283c50641154183c0200841d007115525030021840c00c0000e80750792904c000044403503845a0004e00c03001805501c000b001802c95032003000341d24485030085180c413142c2103d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 488396852 1250 488395602 488395613
    0xd060e01060f0e0d0209130f02040606020c0102101419090803010e0108010509070b0f0901090f032d050a0305090d150c030e190204090f08360901030602222312060f04060603 76
    0x140b4cd20400140e04007140d0306c1a1542c05011510300c5140e0010200004400d4501210a104000d00307620066044424000500c240d076a11140d8101d4001c105aa08c940e5540c403000d040035024003c144c2c1950918011480b607860000308032007035603120301032503007400d000000b05002e41c0c0203183c209042014415000840c049108410300285d4010482c140700301e149140c203843c0030300004000e203400c21450010313407001c00d10200307141040c00c1c0e261400aa481c518040044c890030f0f403602003c1c010358120031603902954078680c01422020115141072001e905070200598603018051410100000080b00090052074035074400d0085502c60400c03952864000e03107803141c941d00841d41b509506161018100350b00880341d007200b5040464500f0f840c1c401a100404600ca81c0b00c10f11004080f2a004a1076101d0f01c1003120b00d51201c404044200984582d0b41c1c915015030b2000426503401c01ea18592007046507080040c041c40c07001c1c0103100240b1a603124040c0d0241c00810007042500d0241c3c2c1c440002c0000740 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 488398102 1250 488396852 488396861
    0xb0a0302120607080702120a0c060b12100e0c0f04050919050c03070f0825170106090b0411040608062e2d050d060e01060f0e0d0209130f0204 62
    0xc44a00200b00d503252440f00580022000b4001e070301950300100034485802c070741c0c8080354011981480c3c4252066000d140940107042c01c5100329038451031100000c16510000599040c400a01e103000b0712404105646203500c0f00b001c0e04405400402400c500c298605007900000d8010395180d013141c00c03140c01c841041e6094448032004460a1300702d14001c070643c0ca030070020311001c2c000608204170f401d4070704000607664004614000600320480440700301000203180109000b031031804052240d0742c41000300b250080c420b5018031101640f815440801905051003041068012500040e10f49030400390184c1e1800c000034000d6070b002c0036290324981804131035405100071401d4a000c1e280c0040610a020700141e0b84840008111424100c841d02a001020f4407040d03042024241640c4d142c0a0281ca14040c20640c1c10040030400120000180158001d408a401085550381d007182602003904000c2e800407035403000f950040c848404641c0a4070340c1c2c0000c030526441071011f40000c101d41d0307010034140d5 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 488399352 1250 488398102 488398129
    0x40302121602121c0512060906011e142115010f0c050a060f090312050c0a032307050a0923060d0219030209040f051e040804091b0306060206040309090b0a0302 70
    0x1e400031400d8011407041282191f0021021a0551203618120340003c00c00840140c05a600d04450072424500310b020b04001c0740707030071602c0d84040d41d2002000c0000185501942045900703403144800203404400700c0d41c509844d9041651000d054400c00e0038201e4003076074000c5058416000d0280000d00052140c0f24080139205c014401042c0316101e428003504400d021241012650300784000c0140c1c2e2001c0c541200c0c290300031414005003a000e013050000c01c102e1624401c0250b54481024420402d8114015040f00850340e1790f41e542e880d4480201d0012070340300520741c1104030039884106402e4a080000740c03020016404005040c4401280c402d005090000d42c0c440210f0360020f4110b50714106402040362050305580b0612540c02d2211201c1ca00c03045028500300a143c5c0200441e003000b08070303801c4a00038401c1400c240104030b00d96880d001d0740d0301d000c4101c4011910b41040000c0090010130f07001c1c0b0641d059210b0b07064851904403440c005c0c1c0801d5004c6644818032a402100690325200015001e = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 488400602 1250 488399352 488399357
    0xf1a0a0912230a0308190b0303030406050105040b060408030a05030a0b100806040b0607050c121219090f030809010f050405030f01021e0906040311040b0414040302121602121c 77
    0xc81c0c2c42d00d5a40701402042541c60701d8002c010b092010941084040c2e40101c005042085007800c07801071400244070005229502d40000010300040c0000d540055040c3d0710304450400030105c2000c00c20065209070321076103d00e03800a00c450b0b070400f400346002e0740e0b018162220103e088502000001d0082041035140404034245005210103414980709050204034290342003480c190003920717038a40e141140640d440c441e0b00000220389948400b0f0103842914542c80002503119250031075590b41901c00200b11000113141ea080014103e8080100310003240d400a84403885d0181030001120710410441c01481441020000000d43d51010041080c00070300000006882e5500c01c101041c1c807020054001c541050107100110403030390b46104940881e0340c0228544202240b4401141c00f90100115842c0d001d46080004c0c0c81442440d0301440c42144268296044614504503d4030a4003850065440c00c10b03010803001c1c01405d081d01400141d03400701c011501c1c1d80f1541d010011a5801c4100c601c1c00 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 488401852 1250 488400602 488400623
    0x30203090607080705070f0f02091006020f0309060d18080a020d08061e011b0501060603021b0a03020c151902251805130215090102070f1a0a0912 64
    0x14500244001c07030304039006180101d02410306200051103070285900c058510a005c0d4500b600b084003417408503c0d81135000d0a5042e05151240899410f865144911409401803441c030140c1e010000c800c90340940c500404003030520040e4030558004004480c04603880c1081e01200d580403078280c40141c1000300c8158001d008181c0b160000410341e0f0b0000e08181d0040058808012031051950696518407500386009101140b8404c2400000000600050700340d5180400200b5031a9048c0c000b40050344000300c3c03012400b1005008030350f855005103c09401a0441c502c0c2d08003d01d06242424032140d0401c000e80d08208044450441c280500c44411025a0046001a240d2101c0c00700850420700040315002c0410310f03000c420150301b003805001c100c2107070b0384000080119810b0040218202e401401c42000c1c0803d04c0142c681640c0b00e2001d103070251041d403000107484042101148196071f10b005042680c43c03080315940b2456082040e0101c1404100c200105060210b040244030140c000c0442c0f00e0f = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 488403102 1250 488401852 488401861
    0x2040207020d060e12030103120e0a030f03030204030c051903060e0f0f0d0207080a0c120606081c09081b040b061b0303162c04180b040507080a0218060d12030203 71
    0x30701c0d01202c0540841e40c031750140f00400208195800e00148101e450415074107070348a0710002450a8150b03000140180b0100c0c9080050550540c0503000f42c80c8a00030b510720050b2030720f0030890140c0c0004011001c003810b55500340005a20b0f50800581c0005110444800340e44000203a402c050b42c0082d185629882141144503042c2d04200b5900200516000341000c01110313242e2026000341405240b10241d4030310021030400040e948540c0040814000380d83c0e00b9280100d4200c940d001788172842d0001fa0200d0004940308802003414135075032010b00d2111801c1e544902c1070102504910340c00e250300030000c1c481041085615005543c401030342c50b0155a030b80ca010b05a0f403031403a00c68003e11003040b103000040c01e10f4510340d80c10282c01b4034548942c52005680c441c0064054460764804c082c9a40c081020002044821480d49000c1c902c180d0544540c9505c0e60300c1c182e0b0780c3c00680d1002e544807503000003800c2051400f002c3c0c540c0000b00501090510010f90712028841d2003c0d0b81c07060000307a400000c21 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 488404352 1250 488403102 488403131
    0x160828021b01140a0b0303220f060e01080603030f090d110604080a050d080114010809071a1c0b0907111207080a0e0a060f11030c0f0703030206010603060308030a050402040207020d06 80
    0x3a446116824100400740741c00300800d90300d001c3d9180034130484040c8c2c0105a03000000c0f80c0d801c0001c10b2075003001001300d034071136030010086c0195a6201d8045015003020410514000c019507211140c0c41c110302e400c0500003c2040b4003400410301c00d4507114a580c2c191425912101d0081c005005000b005103d4000c8500d0901d2900900781d89032810400103400504c547c2400300d01a201c540002d04c2c0c04212a164203402d6070904855600420a00e00241581c0548085001c003503d44050081d001c2e80c00c40a11186030801e40c1c0c07400680c0c1e036004202400103a01680100044500100440102d40e0075250030b1031720055941c8904425120340002040031201c06a200c030701f02d600500d099070203140341854000041d00645442c5104414441780030b81401d0091070810a036081051842c044500114224038007944891a0b0301080e00180201000420050b01030f0191100b220762142c002e03840e65440a07221030041c00003600423603009030204611005030381e40e114981000c038085c00b0006240c0c924203080c1e = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 488405602 1250 488404352 488404391
    0xc0605070c0e010b0d1a04150611030301210516080705040506060a140f121512030f0403080f070605240f0306040b0403090518160828021b01 62
    0xca11008400500ca90139a00c415110800342d500c0c030114804040386400358a003849a031807641c0003894506000b01c803130785691031b02088600d0743d207410701c60500c0d0640603070300d0388000d00481515940810211000704034103e207901c0e0050168040d9804081c0810504a000030141e0201c441e0780e0007004244004d15280c49906c0e0401e10849441d481c010340075202400b410340c0b010800c1c1807010089103081007110104211003680034075422441c09403801ca080c04046075150700815008001840c000c08035084004104ca01c01c0043c003920350300785071555075428030704c0d4081c8650111005051141c01c0c0080d0440c00b41e81e00400d14080b1020f201200e14034030341d620040c104a0315114220b802848180c54074003041d07154019800c0a034285e42e5070384504003912061410f40c00309801511802da030000c01130104143c02d000d41046116507507410a4407604030740d40003040e00c0d40000344980340c2410044081c2d01100c492040703681000582001e003070042c2e0260083c4502032814640e5100c413020410148000c01 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 488406852 1250 488405602 488405609
    0x28080f1314040903020d031d100603060b180c0a051306030c02102f07120c03080a1407050c0c1c05010b03010c051903020d050705190e13020f070c0605070c 68
    0x82c20001074801e030303c0c0250366040a807100420305130754140d90003c00207040010040910400c0454040410f4524400c008100920080c0da4191070948003000900e070850500c4140b440b0786403c0100d946964aa405403907000361000001d000003001100f030902041d820300d10040142c3d4500041101c202d01019040c10b501c00e90000025240c901028110070261010001c07032030451035098407807a1409a248154400c0d140d0240902c890313803803e0006203070700c2074040f401a48aa0b6400c1d1040d280c81b04598262804001c032181812103900c002120356101e000600900300c154012540340725120008107070f120009518001003c0402102d403010b00c03100f400b07109614035054008012920342244c009003180201c11820b00b840714100d1621040611a406482516100e82010849814200d102808a40c8500488804110400e013400101401644034000800014141900e010840e088100c0250f00030340c40d40038a640e09000076004513025409a01c0682095122282e58440a0800a1b0f500400380e1 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 488408102 1250 488406852 488406859
    0xf01080702061f050301050a051008030c070510030f0c1214060a050607151a130504050d0809070e13060b03120f070204020906120709050328080f1314 66
    0x20520428036800110503038440c2d541079000c040c016100e40b00106000c2c050740000e0f810340c281f000b800030b0b0310341a40c0000e001d40200756080d00e0307840e928401c0e19103d01440102c900380c0c0d0013004007000070307041c518440500900c40d45000941d0403140b04e04c4208640c2d00c0c600c5400052508140208120b030f070380c421003000080c1070076501d4080c5080300c00100f1800b114080c80d07000d500045008820000d580100f506001c400e01800e101d1806282282c2c055a49020380d16441400704050b54140400a0700c42c8500070394010300a000000c0640c0015031301c0d520007070101e076400d20a0180000741342e45aa0001c90140500d94081401d030055414040d047d1001c1c2030300140702e40c1000c0000d140030042d960890300d101c00c003e0340b01074541440c0d00026000b802a10038058000f000001c00041603001d8a050030300c520343d0307030b154082c21503191000c0c903640b40a0901c1140c0d034402688a0790070041025a8180c001504c03e071107003442d002d8106a6001c80d80c2206c034810206c40d408003404d00c44500301101c048144001078 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 488409352 1250 488408102 488408117
    0x313140109030f020d0807050d030902130207030c02090907050d050c0901051f080403051b0a02100f1d041b0809061b040b0a0903080c031c050603070501120902030601030c050f01 78
    0x1a1180e103003d41d100c020091190010341000b0341080115001c1d00c050720381081c01d13a132660f400b6501c00b030050007010008a203e80584000880c9107174242c402c0e1445d00b50103550310101d000b216030a00803401c00c09000e01c0454458130702d0000d4141c0e00d010440340c000303103c0d20140900103640028001d1031501038010314030130810600104001640346403038002d010780d140f50810158030b40f82400d80b01803144610402d00301141003160350050100290307001005d8400da5940110030100b490403698806641d84060000e034007405402c0040c0600342001c0c3c14140000c000156100200e540c1c0c0c0100c0b41c1280300031010404103010040601c1c010720a0381e034131401600070300c400f8903001e4880f5404d07480340b80240300d0b16120100700615428454030341040a150310144041e81c0b0000515601d035030b60007840803101c480351001280140d45600b4050940900d03c050000d0020070300744001550b418000c0e111900516036564920b40142e5420000c5500079405031a05440817400c2005000c0d00c2e020102d00c09040c002d40 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 488410602 1250 488409352 488409359
    0x8130302190614180d03050c0414010e1926060c0a030e07030503040906050105090307090221041208010603090209151c0804081e0307020906040e0313140109 69
    0x12464480700c40c00c0c040041e403104094074220009050812410000220220402100c8a04000c1c9091600c82890440350240c4031518120260351013210402505007003400200050102d01603403000c1c020050418960183c28140494000b0900b0f03542d0205090158104020030150180707103d02c08441c1400070343c15601140300d00c0381e54840103403120040d1240003038483c0ca40340c869070001800b000038405803407201e0b669051841d03803030f0021f00400c0120385c80c202c8005000c0d801282192000c00d009400780c000e251610f03801900940000720f48904c00d40c010083e15000180e00502280f06600c106950074010050640081c05140305070042414940f03000c9003032000d41e903800c3e0110b03401404101e0120181c0404404140d2041c49003d42ca014840d01d2510801040740d0700b00a0301c00c0e110384908407010b144c8280319014180400c2c0c0200070710764200b04442009030804a800a50104000e000804e07080c040a26540c0395500000c0440000b12003020141700c00c11b110080c201c3c080c102441c000454506 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 488411852 1250 488410602 488410607
    0x1002030909060f0d0f060c030c020604021e03060c0c15061807021207030507060c090506030408090103020415020c010215060a0501030f0b2706030616030b0d0503040b0901081303 78
    0x1880301280e11840d000400109195202c16454070348420140034982d4589072450700c500340ca0b810900480c0e182c6d043c9a001c101c524840e200d80f60030020980e0007800181c03256024403140e4201300c4003143c1407001c0c0b4459080c060700c040141c980651219031003d40d80b1001801e14030b083c600f8004070000034441c200c0c103004450f070b60700c2404142e48aa40113840d100d516458070030f9144c0050101004a0701034081013040501d43c1110203440c03002d000319024045156880d10840b43c5010178002d89034450f100b8030101d00492080e002800d54a18181401803419480f5422060202c1c0104100401640f040c40d0744452542d0610000d001c44200090341c610a0030f040e000944815503e010704c0e41016039400c4603d0200d01039411080e08400301521242404844e9107914003003020003928480c505d4100b00100b910381c1070000b09584580d84868123a000c00904072000c82c003070031103511040d0707101f1314062428010607001e00040005100b400d0340680c0d200040b000141420030000c011600514854481001013034 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 488413102 1250 488411852 488411857
    0x40614060a03080a170109060509010b03010321021216060b0312160501060b040905090706050309030315060d0f0e010b120307020103051009060e0403140a23040305011118100203 78
    0x241e021640e1602c42620000461705000392040394501c009200c4c00000b84d1200c01d50001050f10011781d489407150b0388450442d89580310a01c4020040c02e04c0c040c41b80702814040034000019844e40c41541c41d1803040c51742c6008182c21000704005228003208960081100c24860b10061390343c15409401d141c07442c598443d07480d008800d032680203900107081c0001003140c290b000e180a421082c5041d03807296168003450006000c2111002000e200f00c0f440031458500031010b603803003581050000c40ca19520300318158208c00c00544550303044502800b15051200c6075020746103080030400000555000740c3c0d40080d0070344035211000343c001c00410011400c42503000c000c407200c981e02820040340540b01c40c401c1340d40c1c003045035000c0b00d505442e002d00070408580441070b890046009681d80104060020100030280c442c1d06140d0f8080303001e0a40050500c41d001ca5418820500c01c06007070304090340c81d114542520600d10700741080460018541840340100c0700214149042903c03e0740380c248180f81c0c080e5991 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 488414352 1250 488413102 488413109
    0x6150d060e0f1e190f051905010b030f04120e12011506090303021c0c14030309010b060f18040e01020703020717010e0d030b0301150305161e09051305010c0503040614060a 75
    0x140b008184401e41604582c0215000d28117640e070030031051520f0701013900ba104030030080c0311116040c00000a59200901c003524021404803035002c42ca0340302e6030380c0e1006003c0280c0f4114140003007081480a43e50320520044a000705410020807004899032107101103064503040503040c4426450305001003030703000505034104652010790b011a18110a0195081d0000c3c000051400100320140d00c182d00d0040051401488440005d120603500300080040a0040812030941e0711824454003500b050150b89802d10342c10080e2000070b2803801c000c2481c2c01c0e64400803084e000b60348085020016142c48141300304041e25000000c1125108104841c1d484403400481d0307404040d01c58040c0282c80c1e5080d0700141e05500070305e03600d030001e617500d2a00340e0300ca0203102c60301c1c4201c20f0040400100ca03e12492111f40b015100d10b0201c40703040c00c00da9100e0042ca80030700b4100d48000c1d402e03181c400003802442100e800d02c1850711483c1c1c40740b506113460802e4541c01300b15440425541c505202c041d071901c0c01c00c501607 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 488415602 1250 488414352 488414371
    0x1020a0507020f0a12030215130305070602070f20130506031903120c03050906090d091214070e04050613031704030519080114030609030306150d060e0f1e 68
    0x1204a0600010100c80b4075400001c0c2035500c5e83c1c820010950005081180c00c80980d042400581d1113104d400000c1300f4164001c0c0c04208100191000180741e540200301c86071158203031038804045921120100300d03c2c644680c49941400740c11100c07620b440341c0300009224071800d06001d00c1c0b4106000c0b03522180314401450440590405200c201401b41190f81e040140d2200c04000290940c1c00040250205441d058128083c180111300d45d042e0110741c401c04030b51382e502c2d41c8003101e16007045036180c040038110581d0b40300302000c401c0190403801d000302801800c11104004142c142424242d0904002030f003840b484010202503240002d4004111000480c2d026008800c2035496013006e4485201e40b04901492684000440724026048141281607610200f400301d171840940d03007416550301342580d0f54141580240001603040c030b1b10b41182442c62142051140c1000540c0d05010203885264000c828001002410070044034020500150b114881c2d426840c1c0211441281c0d240d6604044c08a142 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 488416852 1250 488415602 488415619
    0x12070609080403080a0804020f120a0803101a0c06070c050706080601051c0e06010503010c0e040c030603050312040b060402040e040f111503010306110a0504061d0a18060801020a050702 81
    0x41c8040101a24011900205482e681e80d090384401808013104a81c228810102407004d0009030504c16241500712400000600c444603080c0c2b92098903400040c41c000c00707040065030118031121481014000035005040c059194940c1503615401d01c4002401c01c0204809607288601007a00014005e040740d8842c14001001d8881100480700c03807140e10351034000c0d000d04640381c841c4c100041e07000210003007500e0250b6210340d888500301400d0f43d10b01c0508a000038070207002010326113001c1c1d00c09080f1410302d080002c0d07025030342c2d40d500e411a000b40094042000c150000c04c01803000c001c6403150700a204403800c40c506410031454504000d0050406455030404421003820001d8074500200600401451005040890321030502554000d00040301c8007070521080d030401168400c01d6441207142c90310740d01d09003801c04904643e076410f02103075800d50540c90030b0400c0250b2544980744018004034807075025210701c6080648192203890784880b416a1041013001a240d9010050300e04040c0d045900c0711 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 488418102 1250 488416852 488416871
    0x60503090a0c08163804050909030d0c0504060915170115021b010215040f080a031a010e0a1a09090c1b160306020304081303050106090e120706 63
    0x207280014420005140c18100745010403421000a2040a03448155090300310664840091040054500021901c445182560b190886280b0803144102490755207001d810719958000260000317800b91582e0000d601300040411154055000c1d103640310200d0b0501619241c03500c032004004c01c80034032610b202d00540d0006c4a4015204030161700240100b00500c403095615900250400e03011410807001610a201c551460442c41c082c020440c20416009810140140a1004525980100203d6203100d416800301d00260001018005080c950303035001480c001e4141c100d8100d0031154401c54180702c0144100440d030b985009081090b540c1210503441e00c2c0c0d03212400b45185020750100d1651210a68041010104003500030b480c1f04907078ad41d02c42d10a108070031203075a00c0d4066008443e901c7c94034001c041c40803401c503800440d00301d4842c1202034500006400c0c110080c4040390030845159444d00010010290740d805201990307103c280141c842c21003280c280c800c2e02d220741c00000303007510386130021741 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 488419352 1250 488418102 488418121
    0x80303010b0f070c0305070906050f13022802010c09050103050907051002070305060a0b240307030903090302030a0516080304050307051e060711030727091b0303050403060e060907060503 82
    0xf02c01590344882c2084000303844e441d10507110300950140c10f4446144c0200042c01b8980001510440c120240114020410081c96407010303500602c4054909156240c05c04980c1d845098800404030b480e6000040107050644000c0c000c020b40e612990405041006014013088041440000c846088a20f036442e544101d5060307080960035440500f0900a49003000b0302880c0507040710b001d1078411124034050b807a01020954205d0b003e444d1300c00c100001400080e5480340298042c00d91507000c3d050403208aa80c9900013486d10410301c8084405402203524130004129154130840a0f1098101a604290800001c681d441c01c2d14800d40307128400f214503954450052107904008490003400e846e44c3c801d041d0601240810940440c61b001c2d10411200082c596041d0001c040c1171451902c254000464039490503000d810b40041c00c0d986c0c42440700070701e02840407210a17200110300c80c0c0c980c02d48682c60750614004680d8000d486100a8110000300640300c0404981101514614141203841c1d40361603400 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 488420602 1250 488419352 488419357
    0x60a030506011e030b0f1c030f140304030c02030609191b35160612141305010b09040b040f140307111906050f0a0c051209010f09080303010b0f 63
    0x102004440043c803428050707503064005450b0960151000700240d54888281720f1246059000d610ba00c000c41c64400c40003900c24403015002c1405460888089200d203540e03041607a00c1558203c010485a404c000e0440c00c0600c4100e134046012406840b0120012011050700c2d014403a00030414503003001004041d40c6d03884040d0002c1d14207002405030307103802080001c0303148514009244560000355400b44c0c11184c0058111504c11906208480a41c07500c4420790f58003803544081255241c40352000c8a08070002d0501910401070116200483c2559050607400c5807000c0e040140555075490400000c03c203049101c541155004286c0300100800c0e0810303406620145c504d02440740000101d010901c05a006810448a02103170824940c42c140018040e81c075490f40306000109a042c04810000e0702c80b0406044000058108102c9810307580d5249400d0000410588003031090214098020f941d00c61038484002501d0b04144402a0070725413820713a80c0c0014400d0440c180000240e410f44040310a06 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 488421852 1250 488420602 488420627
    0xa111801081f0515071a0709081c030c0314070203090f060304080306060c1006030f0201091706061201020906040e010f0e04030503540106140d23010e1b060a03050601 73
    0x3446e441c4200e6020755211607150603201000001d0000b4404501150302189090103000b00607540500d66035010029009080d40c401a0f17001d15550b0003c0c103040d8840803011a10419007540550fa448180d4010082ca000c00d200d83c6c0d6000d00000e008000000e1044411a5042102142e12545074003246401d2880c001c0b21500e2030a0340c5003411000010800c01c2d00c003380003203100342c031a08666030f2912005103901c244c0c40440c9640364407480105440e030402412090309111800f00261400200d40c02082d400d0780030358030000004859800401c44109052400300103895030400c244214180394500506030300000d800045120090840020813214094040c03140020b6a4222039a090846c501d00d104030b03140b030914890011298080448101c018401c14090300c01d00b03440702e40c03c848880e00340125107107802021500c13400300301c84d034035000c902e00544508824810780000c07405105042d1a00d06149803030802000d6a05040400306040da1541c050b240b0012040c40c00140f5691840e004039802414003c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 488423102 1250 488421852 488421863
    0x304020d050f010e19050606010c0512120105040e010605030d032a0305040b01051207090207050c0a0f031707030504050d030c061a04050108070e010e0a111801081f051507 75
    0x1010201c040c2d006401400102da808001ea4200c0110fa0340f1140b84220001002003040d0004000a03510350b000c3d94410142a0164084030b442d02080340240c1445e910003c420112825004010489131910340075004074288100e00910041d03242c81c02081c1c3c0e5401902da580241a25641150548144070713400b45c00b0308000000070810704010000c0600180000c0d501961041c0104002043d00d041050312407103403030707024402011440d18041c0d218009411503001101e803401000c01c5241c0a035529210b04020f0485500f003904250721354500526504081b107000d452400060010f44042a04881500c0c100c41c0c0640e26540001420700d0201c03111342040d20000c080b03030300d41040c5203215000d0710b0907591a4041628200b000341d0b240e04041d55600514410343c10714500504c01404501c1c044010950040b0900d44049490414581c603449250001c02096800d0340c01c0000314450f540c4d2001d402a00716912440351805c046510ad1910151a4240030b503e004911458260101c50300788407c807a034440e00300 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 488424352 1250 488423102 488423113
    0x903090a03060b040e01060b0a03021303201201140105120309040906020415090305030708130f0915230402031b0f0301060201060b0f070303050601090b1209010f0c020a02060304020d05 81
    0x2e1900714018001080308078059880c0c422041d4070030805101d0703282550344645106003040f0900710103c01039442541a84101c020011000000641070074000c1500341c100349480d000e840b9614140014101c03000819099070381080304c0420389160701e020050646100303a9031000c4c00910003640a00c0d506c104030605030484e181452510610205902800c19101c6800c0c001c0e02c240c1103540f08035002a410b000c09403030b54004000040005010100a002501c0c415038a80390746d03503031662980402401c507442500b402c4d07100c50b50049611800e0038030001514090102c0c208848451130742d4144892083c1e8454019076001001c1403181301068840c085d840c004088070f079500c801421980816400a10401016608040b0007083c000024426a400025160100c80c240380302510114007034500500400e06004002d000420342d004503400600c0d83d055807160b03056050030207070807c908558007003201e409428a0044003008250340441c0003c20349804445540e100e0b21203000190301e91000c110b0080562141 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 488425602 1250 488424352 488424359
    0xc1b0312030c09050a18020d060e0903180a0305030307140c030f120f04032a081204030908120403152a030b04110702010815040509011d010917030903090a 68
    0x750b04020400222640c51010f080c0e540e01c10302480c00500c0c01501d8401c401c0000080440440d540030701645a8882000328034156105c500e24603450080c0c81c4003040d070300000341c01c21010a625000d102c08071025a01440407500d96169030352280400b90051040140e4800400341030450741042d40d524031554420303242e40b10f80c581a407000aa05c80706c1226003055140000a4090080345415407140d074054803202060900c003407846070315982c0c0000041111030001e0b18200480c0700758015001d42c1c016134006504034205414050b10342501e03584500300382e80c13200e000740301e21006400a40d0101da40c00b0303140280150040185c0d5002c3c0071a19452041680720041510b80055602c018100048064400300190a2000305100c00d44000329840c0b403160ba420800000194810009107034801b18a00c1e418039030f0140c2c43c00007401d407003041d140f00840340c0d16041a01c01c040c00d40e40034801202aa00000c104100c5103580b021401c00180241040320b0fa03010001a5007003409004440d024580208030340c8102c4e85 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 488426852 1250 488425602 488425607
    0x120507080717010e01050106051b0304080a080405030624060d06050607061d030703021b0420040f170d080403020a05062511060105100c0c0305030a0f02030304030c1b0312 75
    0xe0100d42c2c0d031030540c03c010f8211002c49041c840c0e141611507540e652072038030001401e0190200000050099584020000010f440c0d00a016003d9000d2041d58041d41c3d4a1400040501e8100c01a2880101c40d141c0b070f860b10181c1d03400720500f410b011402c2d519142c43c1c0c264220b90030002e004541c041074000c08006600c108010303855000c01e5a601e220184007000b001e109d4100f5075130340681d460040150384070150f202c0e04968400c00606143c035000b0400300700d0410792001403840804114640c1c081c508046020700c204005030400c2009090400341002c8102c0c0300c8200640d80d24010741c03070350003400701d17640115051520078840140d40701e400c10f084400c0381c2010b28100340e0b695140440c0d0f480525030b101144170150310500403a004c01407000000c01031a403d20082140d1400c1e176213101414041c1120303041c4c00040000c11003100540c0107a01a54403042d00e120f020b0050f00081c1494021034204008100000790007451000c003d50b04092500303640103503c525840050040d81010f481201c040e200c40c0c4d051036 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 488428102 1250 488426852 488426879
    0x61812050f01320c0919060807020d0c110103060e1515030c0d0b030c030a080301031a0613090201031104033012090f06330f1205070807 60
    0x9000c0c00007003180d15007071446240e2400d4545001e00f4210300302421049044441a0240c3c0c001d140012070b103141c000e02000180d08544465145040354415007002c100c400e40005415038440003c1c00a0302424030880d02c0101000c0c0070b510010040b9152441f848400e9100380d00010241845811690070350608100c41882c0002010440e4841c9000e81024030702c102c0312009613405161003260741400e1105621441c1c0142c04105040350b010721502d144580705030707000c02911103154041c8076425665415400d200c40c90001ea008008100240d00040c00103680751581c0c0c100707100020030b0700001e100d0b82a10040703000d0200ca0003117101901c008500403040c0300c100e0980703c02580303641111400c100341e1524440c01c0c00001404810114580c101d010030000c070300750081e0141c10b100c0d030b40034209411640c0c3c0d800100c42d2008806040540100b10314103c100c2e4800c070000c10244818502003103d8945802462035542d140566850300641408480c1000380802584024208400560f02069110700c1d0300b42042 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 488429352 1250 488428102 488428123
    0x20a0b1614010216240c05120a0b060f0a120501050307380a031a0f01200f0705030706021c030c05070209090309010e190302060903100e0109060e031306181205 70
    0x4007892042c000f0403400e90b204468176540d1b1503c69606000d8807240442e01030000a0504580c1c54a030790100d00329980310b40013003100341c0c0c6590705141c9841c5100702c01403200141091010768203290500501c41590b0000c0c000c01101c11290078811001e03100050350f101809040707081164000b000c2000012402850090b00c80248070360f8080047c0c0080502e541007200d400e500d842d40000d4007205401055118610515030341c98082c80b240440425811050700d00101d480c0c0c0794525401218050055203801d001ca85c0041040b4401000005406c021800d000e0340b40d03070504000e0554030481c0900e840d01aa0950341e01076002044030b515880c1007a00d154a07070340185d030114005405400791483c945010101c0107140184e11004070070740b5007540d00740f00040d40300c400010b505204076a8007400c0001d00703004110b007100c0c83d0030001c582000c2916107482602d042c26032208040c1c105100c1400300918664800007161180d02d00b15101003000408416121855002803c91032149135000083c04400102d84480 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 488430602 1250 488429352 488429393
    0x1501030515060f091f0816030314070b07180302100f030c030608030405040218120106030b06040218040b061606051906060c0809031018020a0b1614010216 68
    0x2a40c1e580040064569502d0245503120480b0004501403400700c120429034003d10107517a5040f1501c59041a1800b03205030241c3c07032048007045003401010340c084829403040c08000300e043d003071049541d60604811002460a400c0080c01170519101e0b009800200001756000f0b0a10b0802d0b4141d483c0040c0f009202200d40c0d00420b04000f4006003c9210341b003504215100e00014604250600302004040d5001c1d03154114000c0c4503820075400e036500c0e0440501d805401c50000508a8035520f00242074a0005001600c1680306110706c0c40340b00301d8400041003500b02203c0c0010314802c0000041c100780078120078024a090f000c01c441c070030410191301181c02408000e88402e08001c504290300d0a03203c00c0d003e12b1000030200220b0b0000549848040c00c00c00c28001e003551000b042d080010000c441c4d0245408a014031906641025401e001444001416031a40958545031280008000400581c0300c0140301e00403020380d1203040700c0f0030360540750b840340943d400c14030025041c10b0101c11349004143d40c444 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 488431852 1250 488430602 488430643
    0x150702031e04060507030e132a03050f041b0305120a09050f0d0803072606040b0103090507360e0709020412020f03010213061d090105091815010305 65
    0x3010944402e0764110b50955842034030b03055241e40d080b10308080d604c0c0e49681101ca022140c0d040152140101c2200c80101000850070340511107039a18800e4030f0321a4401490701e440d085c410401c1800940740e40c40750700115108002c1c079401c00c40304442d848550000d4031500038100703502c00f550840001043d450902d65103075180c494035003003004054070719034201c2035106442500103400128071038061a407180e80c904040d0025440c20071603141c5990403076121000001c0103001c1000500e440e00c12880422000e01e001c1064540c15070b1007581c0e454241c0289018004488281c40584c1000d081a415010300c0e0b0040410340091149039201510099882d82c9090040b02070100d40100c1c14401e03034084070240c080d1441d844d0069028840e030401201c1c100c540554081149480c0504885260340082645545445020030480202000394020804140c481c170003900c0100542c3d0b0b1004141c40d0001e0240c0b0f007011040050404091400c071505030406401ca210400000a00c9400300b40704008a036503402c0d191 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 488433102 1250 488431852 488431897
    0x60906100b120115180602010f050a020705070320030312040c1a0306090a11070507051c0305090603090703050f0f070b160311010e03042601090206030c070515070203 73
    0x4074035001e00b900d200e0300000741c2d40c01004100071200c0e460801580c1d5013014558402440c0c2e143c480c6043d103810000140c1e440340d0b85c1007140c0e4003e120301c0746e00c180908011410213411384e03034cc1c3e80c888140307200c042d0443c521041900c2c00042220080400000c008040380d070340c1c81d902c0c65050b82901c0c04035400e4a00308041580000c0507a0030300300440c0401201c1d200c3c54510340d2003d081004140b006084074820640e6000003206014520008001141c061401080800c1c41c0408000b0030f141441c40b03240f0303500c2400d0742d03000001e504542683c0700c0e12800c84000b030b200d0380c40000e40e5242000b10ba0010b001403084044004580c800030400c0a40304014100380d0b010309844402c42c0400303110318441c1040c900e400d400e590022034420460007900c5d68100303001041030780a800030585140c0040d0046480400c500300031307000740101c8036642514401c41a000f03002c06030145d0001081808014201055030b0000200c8100f000018082020f117541c01d0100e1507900e040c207000081d170369000f001440882c4506c00c202030b17 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 488434352 1250 488433102 488433119
    0x712060b030f0c010f140904060605031b0405010f140d0204030b0108060c3103060e030c010e0a240b0406090207030e030115170709020d02091003060506031302030a0506090610 77
    0xb81d09200185c5840484101e2441c0071518410001c0c1003c4000341c040c884c6130307525540d034001c0c03800030f0001e941c500340c132402e0007010012916100c9031030389443c49042100b000282d0b00400ca5004a04050900885806074911030050031300c030b44003401c80054800100230007040120043c1d14141c61003003045a0b141d641d01c89005c0454814210107a06000b0140358009a8541c41e49054601080d541c54410702c05a0340d80d00e10050b103c0c071481c9000c4030341000c200c4050451007481000e0f052804140106110382d000c1d03e401510030303601d40e04860b00c81ca15042c00d60407030026401500760003030040c200300006551000104000d4209242c2240006d01c2e1030700c0ca241c181740500540b11a0024481560703d090324082c1d000740c1d1010303805a00c0059000707040b80000c9002461024200e0741c40390b00d00269941c0d000c03030208408800d4039512403040c1460850240810385600301500e174440c1c506810105400c1103030000900d01505514014494420441008074031070000c1007060080902900c400000ca41350001c2 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 488435602 1250 488434352 488434363
    0x801060323031602010c021801080d05030408041a070f0305030a0b0915130b120d030e0d21090b07030603023618060708010303020705151603020712060b030f 69
    0x2a07160503842802008004108840d030906054414140081171650b580e006c00d112050080a11822090b59001001a55014440303201e80c0092441e00300d15500d41640c1d40b82d80c9008031700a0311884081118290002260380040b00c1c2d40a80000080842d0302c0726140c000d00a6100711143c1500700d040c0109100181001300250b8043c10440b11b2042041c641da0007170203080d0303203d9807151100b192035016107242a100c2c0310f071003ca104061400f80034400200c03240034068407840f15500d2460762088101029a65002040501040301c65501000c04040c52481c80050300e44248003500349000d40d4241300e50f0580541c40101100d2081d212407080400c0c8401040e02021000340342100740b00500c0483c90380c401c03480d035500e0f405001503001200e0302c82d01045640c901101240c10102081c10321005206150301000b40c7c00050004a8110101d000c82110411007402070b500754816084807190142c08142c028041400501400c0441040b07491090034020301a21040c90024028000c0503105900c60001095 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 488436852 1250 488435602 488435663
    0x80d0309020d03080a0b18010e0f01030b18100203090f0f030301061704020a08030301030308040605091920030f0d030b0a0506040b03070504080a03050301030605132301020c0708010603 81
    0x3864001d40030303d03102922942c60042c04c00c0d0302503548100c03030031840d40c80c844139290300700704402201d14545c18030032000f40252010308078000903082000100002a85002411780c00390307111200150000324807012502e01302c0b14820b00030445c0e00110412240120000b0f1b054050071020b002c985171069070381c42c03140d00d0388401c0c00783e10001503460040f49070a0352082c0b12a504184058140c80c40c0641c2d407201d140c2160000e0f04228001388810f000e0100380185130107020703081541080501603803844070040000c024043d807002442c0c400b00049800b9500e6200703409001d100000340580700c900101d0707e03016403110415031250001c03901e4805006503c0c204104440144c800103091145407608200c08140950001040d180401c4010000172451a07001c0c4001d82d0010304c00d46640381c49505519241c01910f000410000a15041c4122038012400000d0b03888126110081c40c043c60092200d0442d01910603500c030013840d44601103000030075031015806582120700403d540a418007a240c07007514100403a54 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 488438102 1250 488436852 488436859
    0x30e0612071701062c03060a0c08090c130519320118110409020f0909010b03040f060203100302090928050a02011b0f06060609140306180a050304030b01080d030902 72
    0x410f031061074408030892070340849121168516480e0303000001d143c007108a8494034465103602700e06000d1904585910780001401c805002d440b004140400e0300c101c10f604460700b00c540c44801190001d95004051500145188014020102443c005a0303200340311559520b8400c5421400e944c030000c26054580c161802c060f94035260001044a40002e08001c000c0100c106900300400510916284001d01403122004555a103900e80c19040100c0020141e1040da07064808104010001c1d82c14101c0a00103a440074006840761540030094040745040d4200940180403002840308550002580051034001c01c3c0302c4181c1c140b40361403030324040382c40d149005105500840410006601a01ca12071f081c0c02ca0f10381c07030059400c20f52111007840f0300f910010381c0c051303582da44180300c1644d11202d044094003ea2100b403617550100801f081da1214001d2110201120700c0710600c500351000c0c08400031a40d00300e0126a2a1500c1c0d00301f0101c81c12081c070400d09640708034810311403224001c1c00f94010054004 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 488439352 1250 488438102 488438117
    0x207110906012c060c150403030c050702010206180f010f1401060c0210030c0e150a091e171203070f0825030c03110d0902032a010507030e061207170106 67
    0x5202020f00ca10401c414150f00c81003d01030765070500307001c1040a008a90541c1010317958140703400c014003182c1c0e02000800401008002500240c0d800180844d00030050342000c15010354030302d400e5420008103007032014143d401c1c1070110902c08020b41000000413401b020701c1c03101d83d84e1007c094600703400f42a03009400c80344100841070340c1d038000d62000c02180c5042c01c0214801410700d00090304554201c04045002c84082030710301075103501054200c081c003459601c006800302d4030b840401008503684140c554030340d03190300000782008041c800d070403c0b0340e03002c1034050701d0307013000030000d08503141c11524030001032200c40001d01e45a0a2641c01d03007013661222520300038003980c000205c01800315000d81e01c1c24503480d152294501c10042c4010480c111481d680080d10111a104060520b22480d40c040303150007500000e4030f83d10000e030124242941c000d003040c994071049842c003901d11081c035000e010303403091001c0381da900f030a40910740303c2c1d10450045c1c1d07491802d4520380d040000e018000303010f03000001f4000f = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 488440602 1250 488439352 488439407
    0xc0c1410050a020102130e010618082d0601061106130f0816021305011502070807300f120c0308041106040b1801030b0105040b1606060504020711090601 67
    0x74100a0442c6001c03032002500c0c0c40400048017496880d5903021010811400004002035903100c0194400412407524010074146080b40503a9102c614001c03a8080d21683c10b400e1140c581101031110401c104d02d81034480710361f03603442c010f020701d0031102c14443e00740200300009181e00308a1104c2400160300c80c40c2441c11140c0c1c0c1e10399800c1e68124100381d08030f581c62044680c002d0380c5c40100e827400203070ba2804040384940c18840350506800008406a0943d8080c5106010320030022464605075a00d00c404544800c02181c0032000842680c00d0035004003d01c0b1009a003801462006050054042c40303580e88103021a44080300d54070104100900003908400100f00002c3c140b607128500ea20b0300805086c00c258a810480c03603594059890110344425299920040f940c05010704c1d01c40340c03000d0034400c0c140341c0b801080c9440c503c2002c0c2107200d001d2915192a08102e49a07009002a00c00584110746a40341450074500162200036144d104006020002e19290700c9007030884440a80340004c010415803 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 488441852 1250 488440602 488440607
    0x2030c061902040909060b10180e04030302040509090309010206101809140d0c1109040b041e0f0b040b06150a080408160309150305010b1204060b040c0c0c1410 70
    0x91007012004101e408102c0015644418011a401035000d46400240584441d0401102881c2010207100317110a81801020142044c034522044881c200088001540c40f46800c078000d1180341c0101d81d0244207101842035903840000501791000d42a0200e4050f41c81d48040200341d43e41921030f45c8282c00b80d410444511440c00d812072040988a021800d0005145080a03401c0000c407206220005525500c04c0060140c4800f03d928241410768022015003030546910b03500d0300e4010009019400c410880b401889100511488140e030440080a02c40201d40340209980b00b041e0b906a480e8115800820401d11b8540300228500e001a0481480e04000c002c042e03481040040c01680c0e400c405100c0c01c500c01c1365001d41402041d01c00c0d5a844031140c2800800b84180704d000150004040c500070040c006909441c089900b0b04203da080703100710396034914064000c5d1450300700f0305401504100100c5180c6401c42550401140f05038407002e00c031178032420640000b1512040440c1c0c40100ca401d203420050 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 488443102 1250 488441852 488441881
    0x30c030b090a15052701050607050c09130b0c1b0105011526010902121f050f130e0f07060309120804020112060b0a08070e0907140705100905070602030c06 68
    0x48401544855030380d401c0014211181d007003401c9080705e84500301d40d5035000501816800350500320307805800c01c4403c0d00c0c0d0710798503554480c455002d203040034040391014001107110521107621130b4545442c0e10307040c03400030503d03040241d40d050f055070f800682c9644038506018050580700c2e11b452010009030148021242600e40391170b10b0444400f40d000d0440043c50f000d551602a00180101503030b113110908444d10703080802818240448560109090400760f0121541b04840088880711071501039034001480c032404a02002d41c4061420121124000010491040c41d1855400381e41d0340f1070399450183d003610609030008050000c00e410440315103000e03080942d000f42c010300d04800000680c0c8002d008403102d84d0003004000c4d00201313170b21100e140d1201548e948040701d0f1500184850592000c5072100c840a007101e014400d000c8101030b05980100180d80c401c80d0000d080329401c5030310701d04044c01031050180940d010b024401c1b01040709070001081300c5c1c1c1e80040400400c43c95603004056080303032 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 488444352 1250 488443102 488443121
    0x90501020702130504032c270c040f030b071709010902010807020c06030c03070c0c060302040f061b0f0206130303030b18010f17071508060f0a0f090b0a090c050406030c030b090a 78
    0x103030030304d07c1800c003078851032112000088a084e550300701180d02e5280030048400140014402c0004000038441803030b05c108003c0031030740e02180085a5480b0801c09030b50410440100700e1a8200d0b80d02000265181500f02241840c001c0e02c41c58150740702c4000407a1680e42145019801800070004503100d080901c00555001507140303003084a00c10184d442505a0030f00360700c1040042c1d00801c0030700c120000112402c00900c030f5410444460034401203d4003804040c1e00001d010380d140e1007181c509644940d000c41c1c00b100c0c91107401c102c046846c4e103005170080140314603850088004200400c0342004280700d4605844d004070030b20780540d11300300000101404481352554540100300000400170b142c0300d141c4050b1090394075580080d141a500f4841c0103104620f8480c41034450301003c10581300082100300c1510880007003c2600408180490003504542d402158101d180c85882c1c50002e90100180040e00c4196409000a050a00048050f1411005056441003030400404c09102c81e550241000 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 488445602 1250 488444352 488444417
    0x6090d0f020d0f0b0106020607020102090a0306090c0306060b0c0f030a021509030903010c080105040b010207060e060703030e0304030302060105150304440327030d090503070609050102070213050403 87
    0x9029540c038a1500c1c900780046131031005080c010f01c20702d5014440d05521100603c021408d16100100251400103103100c041d0100344d41d41c11040501003007036030b06d0000e5504440e0030b011459071001034140c10750040760b000e00c650156030700b030a91142c0c010003141d1117465560700415000d500d5180301003079000003070b1a9010a1008000720030b0b494501707000e128803101d01900d0b0082d80350b142a0070302080d500b01d00f1001c2c3c1150003c510912449400540002d14418155525511a1000d2800360014a684200d1101c00d01c03011500200701640041c00a060b620103a89a0308803014417000180e20b0300003a500200f0507010200f00351007620100011441c1600910754880d039880c0c150740c80d00c1806850741c503040c080000001c03c0000903492080120510b2040d008030201444840340c40c181c0300c3c041c87e1000403032240ca0f40070582c00c1c41410801c0e1081c840e00301c88208843d100c1e6182041c003d5200000482c002c0346020150450540d03240b0465115642540741e41c44d08101101c00c03940b00210b0003450f60356 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 488446852 1250 488445602 488445619
    0xc030c160605010311101202180d0524370e060708061002120702040b1f12020702060a030507030f1e110c030a11030409092006090d0f02 60
    0x18410004118401940e008480001d415411428a9403105c05d0645000d401071500321229480c4540c801c141288a641e810001611280909401030800680791038a40e840880c0190310810f00001003810191007052080b40703450201580000c1082c4441183c6400100c000d580c800660fa8010400d01210103100d0f800392035050300d080c1c0d00b00c42142c1007002c1342030b80d95020340c04000034070380c0004000d0b401c4002110f03000310000f041100291303074a030300015418441030b000c00d1800854175a600700300c0c000e0000412803440c1403003001040440460511110300000e0303808062142e01c07410348c801c5401036a00584a0b51608078811810b401070040580000201580d81140c0080d0801500c0b0f1280ba04074841d07414010f003075a050350482690400c14600c000d902d42003240314042d00300002141c89a001500b04045400c1c0c40c0c0c01c0860560103964001100c60341020491410440c0c5100c140640d00100d2a400d042440e2080c284400743c0a02091603403c01124001075002c582c4002c505080b03184002c0c00e091 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 488448102 1250 488446852 488446867
    0x80304030b0c12040b06031018021c23060606041a130b0c0d18050f011b0813031209060503130203071508240607080c101a01090504140c030c 62
    0x111024045400345c60484524041c03292030300c0c0c2400841c103c10303450041407064111040c3d2280c49110905402407190401620940c00e444140d14040b002c250003024114100041c00020400c10810300784000d114000d40000034420716040040d103041c0c40092107164010812100704450070b0340031700c02126258203600710001e20518803100421b0030607000c0c0042c003006035040a000c1d1038a04c1582190340c0104070400c080c01140c07168500a040d262007480c2c51825a07450111921000404035000360080600003000500c0360000d180c0b00c02141e11801941d900c407640004111781001003030017030100103a01000480c412044d41071a1140b0103000800b59011140e503040403925203c00c0300d00c0c1c0c1003c200c4480800c4800d2800b551030501c4051040701c602c0540340301c00700042440c8640140188500c00110b0100c4c0241003c102110310b410000804106602c0003062980c002280c1045040c0003450b0b046003c2900c0c1018041c80c1024071585d1b40421440c0c441e1018000c19030401070014110f1141030113400c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 488449352 1250 488448102 488448127
    0x80708192706020c070509061008040314040f03140a030e090c040b030112020108060303130504090c0e13050d09050306040f170a030b03060105060403030e09040302010b1201050a0510080304030b0c 86
    0x541c48544602c2c4010398520501240509010507548194414054031041010a48601d884022100103d01d04102941d44a2906481014080706043ca5131240070801007003018040031a801aa806206442c80c0e459856001c03c1d0780e004a0400100040c181103a803914074244074581c00e0300304800d01621400e16407a2103644950381c100b41c6c01025200b01000d01307441036580007050a900490b083d405185007030030458902c0491943c51180074082da58450041c0f0600006d04032800240c403000c4c034004042c0c1042f038a0f0042c4c0429030002900d140c0584150300d02c496014041103001c51b240900500a00c2c2d840b034071800424141007409659002c2010010100c20b140b2030006c004c80010b81d10b0005400d030100d001e0518254051304168001d403030400c01400440c0d0020384041480c0400c990720040741c4e5413440d040b409402c0107240d4a4000c0707448072030b54220102c10b4102078403581c20320200f00519540c54401600003582840f646506400401090005c540e2101c29103911503544643d6a14240c08044007 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 488450602 1250 488449352 488449421
    0x1091103090a1211100f051308040b0a051c050a0b061e160c121401020306130e210909061f0c30020f06250c050102070b060108070819 59
    0x1c41980ca540c1b0f54582c04000c1031407041a4002c03082e20400000395070311b662849454420307030040759000d00700410781000711072143c01141d8100c3c1403050141c1d10414280b0450001d084280c0c1d07074114032410440c00b034496091010648050300f540d8906012024682d2840300300641c400707165032510031020041a0003241c00c000310040288550000d00003054107904200000f01c284074800f00042e401003041c0007055a4000b22140700002d54640024240300c1e0b00b8145d490f01c24005404240c0d0100d64050000c805030f400080c043c1128103981601c03942c0e550404100c01c0c0c1f400c944620100400301801c2c90012403003107240468030380c45000a803c1c0e825074a111344c0b0810003c0c4166400485064a41c1e2108a50500c401c4400c0c0c0141c500900c61810200d5510808814a00084e05044102c640801906104051854545030080000c41d40c3d030980d41020802290b0440c0d9039030116218501041500c0d126040a5104a410303401030710003081c014990001a02d100d10b030452805081000200304a51800744 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 488451852 1250 488450602 488450623
    0x302070212031b0706020d050306090c1209060717060a03030c020a031e0c060e01120f060e1305240f0703091406090c1e270f01091103090a1211 63
    0x1503404812102c003c01c2c1c5020350b2078000c003085400041c52900c01581240981c0c0d00324008984c41c001e250344451490400b03024000c64600100300c1c072001d02010290204965009e41c034540d4031203100020307542d802c0c1c5170f14006981d01a00b269a0290401c0424480c1003c104060310041c460040540e0b07948410861901300a4080e41d0840e8124100081001604060000b40041d00780241030b890b0000003e840020500c040c8800e407070301d0303040344040e8850690103600a05081c0d182000300c3c1c24045a00d489489411200b00c82c103100b100043e4003044001c0d5210765000310038092031400c81e525801e88002d104409031902c81855116000080002c3d41c1a160004030004907000b00b01130b00e0035002c16480d00c0d03213070210540951600303110864103003444060481d40d00001c1e145c040700100590b0035900042401d4082104c0140c07000309010b09042107001040c104c0e5400b15091103602c080c0c0c4c100c04694030050303899050551104850200040c8010b0200b61505007500b41082030b00541040c0b10301f03001290a = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 488453102 1250 488451852 488451877
    0x4050a0219030516030e1e010e07090618050609190615020109020102010f1806050405100203040804060206010f0b04120507090510032d1412070b01050906150307030207021203 77
    0x70810004d035810508070074a400192070b0501450030300384003140d145c070481003c2c6410100100000326022400f5045400c100320740f141210117059544440c07000409060003030351540c518190710012010500c5c0134290040310300410350801c0392650301080504900d40a014000e030703510341d4000513040032040c02810aa0780c2c250000302c0d842500344002400c44070002d450004c3c051070120a200302418079072040d43c0003a842a0700041da42c81d05e0410514005250b060341035084c0c000420041008401c4007c0c2040720002d8080b182c842c0d0301d8001c18a0441058012074030540c90502080200010000310400321502030000d641e281915901c0345c80c107541d42103d419889080e4070f0300800c100f010040c9802d1400d02c0c407030b06213803010000b80001904d5034040d03140a0301c03400080c0c005c40404107043c81003540e14460420641e55800062501100b01a82440342c148140f10100001d42141419400c03050040d08410100e407960359101c00540c02900645010f0b41c02c407030f000c1c4040c07102080c01c000601d032000224 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 488454352 1250 488453102 488453111
    0x1091109130e0d0e090f0c04230306040f0506070924050d0501031110030e06062107030323160803100e0a052502030904090f0b07031a10050904050a021903 68
    0x1500b031005c4807101810f18282d600d14542000002ca5426007a2010358080404504244c045050780d2251300804c003022a071b06000350018442040941e0581001181c401d1094036030070b54413284103031080c00c1503215448000e05034080340710780c0a143c0058035100010a003000c604142a038a040c00403100c09801c21100c2800000c420503040c40c1c81d540408a000d40c501e401c1c05088a0801c0850312400c02400890181c6102002409002943c1c000c0301a2480b100c421951820760700e080040c82200401c90400502e40c505017450780ca5501107046500f0015000c03030902c0390342415a40d0807500d03400108101c408404080e00414107044550f00c2c0741c000c107403200000c281d42c208180041c1c00d0b60981c03046001c0d070b2001c0f00c07404e00c806500403082e80c03c6da0340c040314001604001c9007058429031900e040700805004100040103211501035000e4082030810032441205040704030140500040384442c00008100c0c1841050b849203041c0d000a43d001c018842d01505100d40c403001d403c40c0007003840040d008607884 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 488455602 1250 488454352 488454377
    0x20c0607020d031518050a0b0d05010b040b0904110d050316030215070305040b150609040908120114130f20180a12030f0c0c08010902030601091109130e0d 68
    0x3602a052035804007858130b01c1e040e40343c00884140018104140c508044d240d400050306020160701458020300043c140410300c51180c64a00e00801011650340e109600d4161008080d06102010f90704c603981c02880e0b501e9046d1610200080540c4081c001c403078611040050607029004c5e840d982e45860700ca80c008021002c0100400b4503070000041503c2d04040c0781c00c0c20480422000030440b5044104204030484145030000401d070948148201c842e0000d0801c07030380c2002c00012100500040051481180d0680d0b2a00a0030000000310500d455024003110783c080604c1110f90320010202086400014070740c1c0320f81190594140380c3c081c6000e9000d00c00300b048105c4d04114001e8001500c0d084440412242c10011a010040d22106004c0c04100c0c400c06185040d50003810310000298218108086160303941c0501406010f641404034068020071000080c1c1e06194041c5001074841011540e0400c034409040c0035115030b9440814603100d844484a52000c4418030035110059420360b10204c1c1e500d80e = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 488456852 1250 488455602 488455607
    0xc07210c080309030c0d11031501031202070311010e0a051201022d07120203070c03110f0d0819020a1a1b0a0f0e0a0806011502010e0d09030b0a020c0607020d 69
    0x1903440700c0140d03001001030050542d000300c0d100c5044070040fa550000d030b009a0078007503124140301c079080d40c03d441101c20100380150081c0c400d0b81224880c020040030b0a00ca60002c0380c6440741448010004602c28101c1c0d11203600800c00302c1c10b1820003406040e449561800025880c0000282112140e503002030002014001c5a640c5035414500c054a420b0750440880c4001591103072480240c0220a80300c0115641c170310901c12165070301d4205001c4040c4d941c990818074800011051795a118002161205000c1d0401d0100c2c0b44105800120341410501240c02d0141400040100c840460040300c14180c0016104000d030300340c1755400b00394128640380c200000d20035030745484969040984144014000c0d9a8818203c8600d000203241a150741c110080200b40129000e0b04824074a01400e8004151805030340f0110800000343d600038400748411100140c0c035500e4980d24140042c0007482d09201144030399000320f030000b003030000c010300d0210344224280c103024087d149900160000038915071142d5 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 488458102 1250 488456852 488456873
    0x6070b0a1d0a02040504172b09030503010509040c03051b01020601060801030f260d020702100804051203150616120f05120a09080418110405060403080c0721 69
    0x9001d00c107188505141051425910618007000a200c0c070340321400034041282001c0b280300d0f10000185480d480354002004a103a9580034108104c0340c80d8450105290032505000314004241c00d52219461a4204024080e12800042043d0381e0b10305c8460000000a80400c4840464888000c004000d409a44002030030710700306921039010403e44000610100d03880d14401280c20794000d41811550f2400c0058000700d8241c0d6860303480e5984045613600d0f00042c07130b40003800c01d1482220b0307210304c001c180c1c81c0907141da01c02950b01400943c403044100011004107401150008507400401c060001050001184c0740e01100721f000c59a242202d16074204070100318104c084040b142007201e0540030030301e4004d0840c02140d0102e2100500c10001c40c0c0c024071035a014410441e001080300f6542c81d11040080020b480341071a82c0070075460203002c0d042003071602e41070764141c1e00c3c0180802c0c03400b442c6480300922500445644005d038014074400107401d110400350316041c520400301d00d2420300c6031402d0185140 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 488459352 1250 488458102 488458121
    0x8040b060915061e0a1809020708120a0605040f0b03010c2a1110170c070302060c0f13030b19060305121308030d1a03010b01080a050a0b06070b0a 64
    0x1150340e003050180c9510010b86509181c1c0b010303039045880e01c00102e00308900b40e00500c1d00440c0d81c1800184801c10690084480c00e0411501d041c10600503603400c40c4500b00c1c41402405419607105003c0240100800c060541c6c11440b0904049145a1180005821100d10f0f44184541380d96820020142e0f06007030040c21713013441c0e590405c050042003045200e10000c654404c0b0041e20b1b204015603404004020304144222400070b89070503110340c0b03500c0700902004079a8502181ca0008000054400340c074180c1112020790b4180c5c06440c0e9a10742c0c610120403508680c0c0700381c24080091101001d55260100204015800354494031044c1c10200c0350741050560200e5800122400e003d4180702033480052140080c035243c0d204190f0340e2000382200f03001c0451542140e4010b0100040991000440780c100c1243c5218000e80b90700410480e5040608981203106032034045030b100000500e4440942e80f00d103074014058040403407000903070b2001944591140e24101c0d40007070803a041c0400800b80d482814040e = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 488460602 1250 488459352 488459359
    0x180209013201020703060f0921021b0f060d200403081812060403020109050c0a06021b0415031518080d05040302030d090803040510051b0d1b08040b06 66
    0x840100781250780a5640e224038216500d444000a910800100004540100040010354202e90058000d040480020344400740044c450026444c0050340701316085905030018031010360521102c0e1a901c50040e00700e030784842c2e400c510941d16100c8800829851600307607400124025190103a40281d480001c045a0b0624280024000284240c04031030a40ca2044080c0341880b0000300025001000c000161250b4080c40d0140020543c054000c20350703203840750003955032a420345d4044c4080b040007881400016400b2183c01440341900d080c00000c490005000454030903c0300d800d180348003507d58800c60780a80b518080e203a031840c00340305000940c0440101040c80803855103030f090f91400343c034905c0d095841e51040031904260003041164500c241550702442410940c0c2085642500112415a218010700030300c0301c3c09401030310030316110795030341640e10300f6000000c501c40503103800c404141000603070f0310141503428818250212184008580d116489440d051524107206400500030501 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 488461852 1250 488460602 488460629
    0x30f050610061710031703090d051602010c0203070504021305030f1506130e0601091b02010507020615010507060203090a0c0b0906090904230c01030c0804020907081918020901 77
    0x8600c3e805803400e26000380b82c1201d6000c64442c0c54001c0402da295a100414200c19400c0c02c403a01c2015001540c81480941c090701e5051040c0c0000396854402d44c0004401041124004030040d130080000c04840f40c005400c0318501900c51000c00d0883e40212a05030001a80301c10420040c9800c00007244450645009010035141c100302e4000c0e06840070b440188184030000c00000a000b482d84510440841041103030303445c2d40d680e01c0c008000c040e0340707440100282688061040072030050041b113004a41d240d00a104641c1d0b0300414000d080895a2201d041003020800f503408540c850000c0c40c003a440d000c000c0d1440e00082e1420040b0100540e2201000030f46c00e01c61410f03036030f5810040e0303940c20009842407030300faa85510b404070000c0c82c0145182407040301d86401d01031100b000074481880702800c3c0c0301007280b0300c640c4405880e02070040f2002980000300301300103141a449a56050b03000907188080080b280c9425020a0640300d07038030600c2040796070000001e011341c54074400c41c42c0140040c08001d034 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 488463102 1250 488461852 488461859
    0xc0f2508030c070b090111030711310b0112050f010f120c06051c15170a0503070807030e0901080a02090f0609072d080a0507020d05031519030f050610 66
    0x54443d8000d129000d003428012500c1d01140e40a0410156000c0041d000e0780c0d501c04ca40c0c90500002c5840038520386c01421285180004038840c3e03035221241c92000d003901018136001d454014007614188101a04001e1b07090706d100c6907001603004244c025038140300307400030960511811000c4090a50320545000004900b0040030424110724801a5401403912544c0d42c0646400404a0250326150b411010703d44030b516600c80000014110a49103a030614030030104c0e09030942681e0340e8400b00043c2ca00d8200700040c40014001000074007030780d8402d0400d40c0c5c00804850000d0300008090340310301603a8101d81c4480341145881c581d22540701116001c00e404500304040070070071700384e03000b4030440a01a2003ca0101c2d00c600030080b000f91140300007002074200c04090340c01803480c0c0c030070f81e8820042c03400d00011650403400814071412881e850b50300c440c19607855280d079090201050000c0e40c0c016981820701c0313400c2140c3c264202c01840c000ca564040340075503458001d01c1d01400810b802c500c60062075060 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 488464352 1250 488463102 488463127
    0x2a010b01172e030b1605310503190605060a060c230d020f07050d0b0408030a0e0304030f0521030109020a030b062b05040f080c0f250803 60
    0x340e412002044402ca096111410410b002c0c40400d21044040b4010450000410842001581c440e160440d0b810582812a00e4203444d107010390084030b01441580248050400f88104580754811808200204119a03a801103401c01c464454451020001d110740001801a50702500e508400c2c169030714080d1a260003001450b504074403000a005041c1400100d03000d084400359004c40030043e8094403140154000003a41c0c4100c44403210f01c3d14059528005403600e0710001482d081ea400100300c118598072039503000100d520003041802c41c141c0e02e800c20b5861030402c01c0680b002e18412410041c20a1260902610b0310258015a0580708100e442c05091001224191ba045990b07941d00543c9a14000d00154051316203554144d03001035010039031103120700d00c0e40c0b04420390b4401e02d1152400442580103510907548100e0b00504030319440c65010b00001c0e40d1a000704186685001980c2d0a021001c0c54603003032129030380040ca0041d8940845c405020710740104400141140c900951030305c1314a00d01c9 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 488465602 1250 488464352 488464397
    0x1b0d030806032506091e050402030408040b0c010204030c052d040f1b0f300908070f1e0b0a0216020a0605031006030509030d0c02032a010b01 62
    0x8040014110100d26039880c200007942410003900f40e0000c0b4014885040060200a84292000103244440000380705c03605190380e180c006075240410700302030308003070500020f5070014000f00c0e0300813010080043c8180e030100c0034200b90702c900070015a0311861410110340420306500001c0c411007043c04075014004034010181381460f01003a44108030904040010010004003410401c824184005e0500b03031420600100c001c299151500d00101856482c1110580304d80710f80c0554802c0e80107143d40c0601c0c42488218040b1002c0c5101080c40080c682c0c0b02e05803600800d84c2240c4405807081070004210040c44200c400c0007142d070720303002100c12549a82c0c181400117008030607015800100344001c900606010783c070058000c0d0460078095078036000100307141d10490790010001c030440c00200754144039018581c024085a0029418400d0081d0350400400710352402c9025444100654600551015100c2e01400390b08010300100e101d0000d40d9500f51000c0414181c100183c1101e0781603c041128807 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 488466852 1250 488465602 488465629
    0x1902010617251a0903011109030a0b0402031236031902060906030103080705060604090f0222110a02070e010f03120c020904060203090c0d0203070b0c01180b0403021b 73
    0x40861140c0018042142070b1910740d003202d802d40d00801d02100d405103000c4001e1030080401c0c2c00800120084600c3c440c86d502440c2c4480d40e254000303490001c0850801251240c001b07000900340c4400581c9007810300a607a111201c0c42d20358101c030001d10201316200745140c44074800d610801ca81030003000e00000391288900c0074880071480100001009649803401655500b0300c02502030381d903075612801c215050750043e00b0116014030800c4001006401d180c000c0031000d0341e000c00003c888114a90170803100440b810030340071381c000e01e01d45030489a070400c1c010301c5c603c103860380349203a65403980d05802810210140c000c00d070111105130042002e58044103d0200300e0740c004410086502e00f02c0c0b0103c403004c0d80d182d4081d50065902e81404144000d07980214052801482180c0c5000704070400c0c40f852224000c4c0195143c1c000a2080000c07400c00390050940d1100180009a8004040b880c20083e4800c01400d40b40c400c03022040000f00340d0104014810211446013500381e80140600140e0030000886 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 488468102 1250 488466852 488466883
    0x613050d1818060308070309170708100e0a02031507260103110d0b0f1017060f07140d060801050c131202150c0c0a091104031e081902010617 62
    0x102c0d5030000d050581d10000c06580c0c0140c0032555012030b030900400e958140e02558201004034103072244540c5002514030116602040035145030082a042070000700304002140c440b60040f4196200141c1d42405443c14030401d51080030002c1c245024000c240403407021100320b11075079400e40d50807032450904025044962040f1084c8090b4000400305040d107070549802441d46040c01c2c240275000c40d5680a261041a80c2d40800c0c0605903200280345c02e0341e40c0e038981e056040c4c1004bc0818041089000d04590000d001e0414424079a00b01e8035070b0500b580704c085901c4000d80d4030b13101446552400c2c060680c00681800c1e501e810129039042c2540742c014a403144a0302d80c1e40c0404c494003103449042c80d41404805041070305455200301c100346503c0301e40f580d02c461712078034071141c7c003245000c4140310303000c0003600c5803054a08203402c56985403203242000b56180e03100303c0110b04003800106410000c02c2050511038110380c00d01013981c40642540c880e504144591280000c05070b00c440c034001810f100403820134 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 488469352 1250 488468102 488468129
    0x50d05060f1609140607140309011404050d02042d021803070e1305010605060703120c180902030603070e090304210b0c1602120d090504060e270613050d18 68
    0x4c0001480520548100030181c4e5540c901030006400702101428003c3c0080e01c404017005165510721502d0710a90040320340c02409601c410b40581010740c0440c506007000700d1341c1c5550075403564020203034580b04d0000941850300020301128011001d5007004940e80194000c2c602035041168560015200905140b500c072582030820041c01000d41100005007005410306680f20098200104034001050303409440364100200203404034807800d4011030b9a01d0005020f0a5642464480030180d88003404050740761081d0760b404030700c240055040500801c0c03d8402141d40b1481d1550703443d9627545850b504a40c005455151101041011009039401201c500d5065a82d1005600d11030800c02c01c00b00180d0412811602d808043ca00000c030001e10040700d440712500282c0d1041084280c5205014008210703a1050100c1e400c00207401b220544031006126417004110031070511498032808503111040e101c21046410280502403105080c0b5540ca85002e8110313401c58161900c1c0701c001d510034069004400e = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 488470602 1250 488469352 488469389
    0x3020a1503140906010e100e071715060406030b13021308060f07050702010323090d0306080a020f1c0b040803190c08070f02031c270b060415050d05060f1609 69
    0xc886540e40074152300c03c01100c1d103082480c0b0080039101c80c0807048051741380d100c0209800c408041c01540781a02c7c01441e0034546030034014224007078991903d403681c00c600055201d81d010440d50014000449078038100c81d110341e203040403240c0342c80c01c090300866482c44100140021594010205c584175902820081040b03815aa50f02d00a1103094007251403008448081c0540100d000c901194400c0c015902400010745540840e900c0301018039000398411992140d0080c90b00b48803c030300c100403202d01c2916203603000b5500c5c0e64460301c1d4200c8040702c2c0d1120010400084105161511011001c598000c000218881c08040d01e1682c001e0080c9041c04252200c0780103680c82041240c811a0f110302c41500803085100d007503000f5141101c0c54051070304014180401c1481400c601365440f54014034160783c90780f00d2509020003002c680c44452042c01d140000031449445101e29110250b1090000745810329000b516410300420141c035a5904060a400108005600009a03800e44103035096100c4038450 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 488471852 1250 488470602 488470621
    0x6020c06030c19020607030c181802130602030a09090b130b0a12050703170f040902090d14160905190b130903021b0306040b070e040603020a1503140906010e 69
    0x3c0c0c040b070403035890fa019211000e07066020800c20700a03590b50b00c060111401c80d500a0f60780e018001c0034002c400e00e04075030800c80a400c0b601403100080c0d02d046c0c01880c210523040f0300c000e2420326400890250340006020030010b07500034440700c000c1440e6001001741200000004034070450008410019546a40130f09506070f135207014100041181c1201d90302c00b85050b14110b0b8507281c03540f1064400304d0001441e6144c003200c043c2154140b11200402502e82810324040348000d420801ca816044040003220310001400c00491040c9141c2d004010050031110244010701446560421140f4038202000d00046101e82c41c0d994001e52007488001c94003a82c00400700b11072242c0010700f0341006080078190b109050300454621fa8503002160316940c60300b0700c0c1085c19510707038003650000c01004081c40051115889420021490320700140041450350b0303241c00081d100c0203150402e1940012008401a029406218411404203070454100c80c80c50700d6425145c868805103d0b44140b2512940000e00541 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 488473102 1250 488471852 488471857
    0xa051533040609090611090d150b0d150f090c09020d0908131805090c1c020904030305150a0e0c09011101140105150c0d12110301171606020c06030c 65
    0x89000e0002c000c501d0760340040401078102403a041d50103074a04528820030517111421950040720260032103580b0007a950350f100f0681c54407421400c84e6682c2e0701c11810aa0390340140c51702102c2c09080b50010500a080d0081e049840d00e00d805500c9a141841480014048200000450314418001616081115048009000000c40c003c0c0b42c26000a82d442010b404100c000c01681e0b40362620484c08007178032501d60f00716041690301180990004606078240e141003029803132880920003c0001c140c1c420350219031810b1080da401c03004240c59208000f84000f4030002c000c06200203d807448100c030702c2c02c1120701103510080d11601100900103007040c0c1e0342e4081c01d0100010714100000b00319509070840e08000d441000c2c01860300c580c443c25407403403840340f843c0280d6583c20810030203002c04004659041c0c40b0a0325100c8001c040710b440319012168a501440030790300178000c2c2c0c140402524408035105003095000c3c4108481c0e84076881007440039503800103d1010601040c3c40312642e80d00c41d18200c42c0c0d02e0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 488474352 1250 488473102 488473201
    0x1030e0c0a05040c030f1b030c0f0504090203060604210203190c030b100810020309010b01050c030d0911040e011a030304060801060c030525020a0e1b180406080a0515 73
    0x39810301c000d8000301e140c2082c490080c441d41d46da0801c8031189d090f40449407505d82034560800540c1c1444240f0540034240c1c01180c11070030007000e079031525641d80e070a01d00800c0002c03140315010146401140950030700b4003203061180b81218070110b81039099640c10100c00381e180006010300040d0000941c0301c442101041d0302500c1c2038000c0b100d9010110610303030003a610440307441c0031a50070100c030704440c4d50054042d10195603d00c3c01071400c2081d414a00c40062040a41c15200d039107501d125803c0988030361007542012b200301e80c004600162072301c005418598204480038042d0303101b0441006103603800768140c1d054503c0c0d41b1b8008002d20403420100ca10b40210ba03040c40c0e0007454004440415400544d40b036128503c02d58020803495035520082d144003108035000c80104580c45a81070081640c003005000c441c2d0129142c01c01e002501010500b110b0f61508141200d078040c8a01ca0148001089903100c0c500c0c252182002da4a02041200f001951a12004500985903503001c16150030480000008 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 488475602 1250 488474352 488474381
    0xa080a0b1203070302070503071a090a0b1801030b09041109040c0b03011d06031b040b040f0e01200301030507050d050a060f02030115031b0804021201020f0901030e0c0a05040c03 78
    0x820409030321a0b101d6200381d10880c0548500e40300000c2c14180800d50b1000c464590115811036001240c4646d03442e8007030b00718941d00440500300400d40c0c2c8540c502034490380e060602c080740c40c0500200050112210181c02a224140d05020480020a07184a5142403001903d000d20303161030b14a0058038243d217941004090090210000c01d00c0b600302d0b00050425940382400e900c40b85c80d01d030181511a0541e0301c0f5041d104031082042c040e5800c05800100407880003400000702c070610340c16800300f1921110070428447e5100e20000c400312800310303c024a500c481da8903040c07855141d40c3d1aaa60ba403510700c1540c0c007951500c810b032030901c48280710b082015500802c0c03d02c108403154110348029802402000d0781c00150100302e1459078030900c5150040694801c0346110750105d12070580350350500401c100d034002144090080710070000c0c00a400010740c0955259100da44200024080d80d242ca05980e8072039010303580008007641c451120408685040da000229068a1801240604140c4184440 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 488476852 1250 488475602 488475619
    0x6020f1603020a0b07051603050309070f0e010306051803090418060903090303080c0c0303180f0a050601180902011e0207080708061902090d150f11190e03030a080a0b 73
    0x1859000700f03040000d140f0400244045940348001500d8070300850780d001660907503405400c000a4007580096401041a808a1b0359807943c13a00f8201c140900c0d50042680c5030040c030010010099140034a60b0003103501840d4189018100484a07a0f0b401800c3d541071143d40c541200c1195002c80643c80d012080c0c0224044c0400b00e02c1b400c015045084511007140010342c0a030016a0203c1c49206a5550500d040301851031521200001e2110708a1008210b44a015100b0210340c0e1041c10425903082d244a1800707040990700d012344040d40003500180e150141420f001103d070041c0c2e404281c040005c44544810102006c9001089103444443e82044c080c900c1180d4000c14100300c0014407034401c1d004940c44050341300c4030780046001d038000c0c0b070030260300005080b81400000cee251132400a12101082e0002401c851300b500d00f034040d910014918001030a0000303407182c154514000c040504180c6082c8015107000d000d010136660310804058404110050f0045012004290410f89103075000619014 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 488478102 1250 488476852 488476897
    0xc030f12051501080703110a0c05030409021b0f211809090114090114040f0614010603021b060103020f060906120403050c06180a300210060f0f0306020f 67
    0x20301e140b0341d542c085520f100004506502c079024080769810b5095003941480080d00060300d001c801d10710f040362030740030078000402c0ca03104d9440076042d01000540151907031100350916509002d40105c0111450b000303031a100000c0104002000e10084680440c40c2d03862441800c510782d15604600c4079584021160188890750303205402c00c40300c071440c03403407981c07139680714426441e00720350881c02402140b51a0100080224804a00c801d402901031007010406150040800d0b020320f10980140780840e501040c60601c00b000c1a411841ba810414000c2145506640026084408000035280b0403580000c400149440700c2060f6407030305540401c41001420300707103001341154100c01030310100d502c01c1d100050701e150840c400d0000354601d0400980110b164070381303803070840d8491018808269100b0f040016502181d04401584c071505540c040c10484c60400404001d4800316800b0860740c280c004000e01c81800c1c550250002c80360700c40c00050f501c440c01c0c0c06c076082c07500a101c4040d400340180c00d1400c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 488479352 1250 488478102 488478121
    0x60a03080c0109120806010318020306071b0c06200a0512180301060b0a1803032102120403080103030305090f060a0207030e030a0b040606090203040321060b1c05010e06010c030f1205 80
    0xe07030061b602620140452000c42060f044045901200a0b605600580218182c4c41c000d0002a03400403c003070f1b00c4445c0d200d1645600c482005640e01480010310bc0003d0521207064410341d0744500b08424000e42554a441c5e1039495a544083d809168240e90006400201c0174a85c0142a11407074040e00270b01074a6651984494541c010061000100d4407203464044c882c0c504401d0074090301e5040e00c40900d1418800503207184a29502c00900015a00704404000c0c0c41403581c560780b003503100e0b6468812940c11460700030161742026114072015482440310340490203000c1000c6601c10300c035400c0182c840c01700d400c041300c071000c10035940764050203400e6030001440714500103c0d1040740200400e0054560b1500b00c28100e10040b40c018000a0340d007281c5203020342c40c0042c0b10b0240e45407400c0101e880381c1c60341c0c015001680580a05511070380b1040b4000d02118941c001e00d0b00602c0744984040f03e9241840010340f0b459140c810080800210a081c00551030050445c01c8115010b10b074104a44c2c5011000c0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 488480602 1250 488479352 488479367
    0x2001230d0b0312030a090201050d060b074b0c060207080f0a030f110a060c030b010206100303050a08070909020313030e1e0f0307050315040218060a03080c010912 71
    0x203400040c18001c01e0112400c00060342d1004205000340580b540e55200f8040006248a03602241089800c0244600540b054003c2002034030025200d80c0c0d0b0707586203149c01400d003440b0740f51080100e41c8502045e20704602e051214010f030207407003030b4116020000c0b881d00011280410340041015910250110342c0a0340002e030001270b41c800404580301103150201c205d40d11840c01c00010700040e0f45000850040f44108940d02610031920100c40e49440e040e61400d00382e4043d640e003100000e541e1402c2850750369040003101e41248079400902070450850310300812030312030380c111030003400742c0303100800d440500c102840c000a021244045460b814911010b0020f000c00c0303c000d40004041500c00440351421036000c03d80c00755511001a15040d00340b00f0b00c0380c4074800c0400760b82e26002d600400107147d2018480c00401454278a54014907107028410481840030440540207030500c0c071000c100c0e103600c3d118905001d0340c1e080110140c4034092540b41c0340c054101180024052041035280032070740d640000c030 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 488481852 1250 488480602 488480617
    0x114040f0e130c1503140a0f0609061401050310080f0304051002010c02100b0a080610080d020303130609020f18100b0705070e09070f0e0108010c0507200123 69
    0x410200d03070b2100c450500309030b01d0286014054031541c82041100c4500800450409031240c107000c02c0d04600c1d41e041c0100d03030700e040310160030203504c0302c0090403c4c1c1c0e9a4800e040103010000c20030070400f41001d03181c40c082c40d40500c0c4513050000020104004c503075030310018030003003100c1c1c001c44110b10101d01d074080c0c0300c0c1c10602c90f2038011101c03c005018001c0c018020410704040d994014210080300f40291009030984500351508560f03074001c00300e02c0c024144102e5105a000114074109207203011983c1e880c08440000880454206209200048000540c0040d1403504060045201d6a19000241003464000d00d00c5034850b10385410741075a03900c06928103100e5031031060090485695030f041920140314551004055411100c4180042000385810781d800c840e407a4201d07141c854942c800ea0700750391029004400003010341001000200400d004441c6511101e25190342044141d6440c280940c004a03c040c81451710420300c14200e910500d05864009085840c0c10504100c030310440359036510503c1c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 488483102 1250 488481852 488481869
    0x1202090709030b0f06060c0102040807051903030804030c1106030a0c08060103181b080106171605012f0610090b0d0201170a020c0114070807030603080301050607020114040f 76
    0x140080c4000e0700409000d0122500498848030703e546a40c1c4500c40c80c00d004049940c090f0701404114174550091015202130048640207281290521042000050110070b5018004c05202c000340300003075010792100d1f0040d505050145d1520301a1819404106041507480d800040110800840f4042900300c0101200c1d5501d4403100c030b4031590011029142e43c0c1d40342088003640482c41c4d400003490341c4040210800780c0d281c1c1850f0030391031340d03005401d5500d2544050001c45840040451141c02441002c50006154003c0320800b40b402c0f0020303085004c0c440e1407a19a00080341450142419803c00c000c1320030510302650103525099480f410003146034083c40a410740340c4500d08030709091182c06400c140e50142c56a00110a01c3d00c0b00c8008400002c0200c51056024031405a8a6800b4001c0d614040e514442040302403411040c020101c41e0000d000c14101030a006d07003000850403c1c011241510b00c06d554403591030340103000513214140e621241d034820200000f00000e00894107900a030a0300c800c0d4 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 488484352 1250 488483102 488483119
    0x20f0a1d10020c010e03030c010e060108060a0501050109030221100614040608190f051204140609011d0d080708030402150c03040905071101140702070929010302131202 74
    0x203405201d8480303012103490000d680100207002c000c0d805090003510b422002421285000c50035a03003582528015500341d04c4a80c40400144005038092280039031100f02c0c4101041150301d4400002d0078580c4600c0301034000c0480b403104100d00780b071a2041001c1c8020b80c030201e44c10f4186141d10040104054422800e1016010781c2c000088c3c40c1c40d01070742040b04c40c0c03d0000c107074149204006454042840720200ca2003001c05088100280d005c4c40245110260640340549440c0703000b03004000c81452060740c40c81784108100020321680c100060003404106031908600e030507042404138952482d4590302510100001c0354400c10001104020340c480da03c203641c0100003400341c00540d24a40907038120000d403600180014450490140d00195014182e407611100e04806002005d08441d004003000c20b541007410b0401000070740400a020062140d1b1500700124900604011480120300920540500b038400044006a00c241c05541c000440380d00c45c40a801da4070080b40385902c9444070201d002d103000 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 488485602 1250 488484352 488484407
    0x20607141b0a12140912012c0c09010302030604060e190503040305100225061103040515060102121b0115080703110405040c0314100c0c0c050a06140c01020f0a 70
    0x1413014240340c001480c00d803804d1224000400004e850001c8000410350344e245110b14594840b40c01903c544106203030490000100b400c1c41900f810100b0703421034042d00c40c241c010001a14002030255200d46c10140004400b24120111418152854070008192403110000010300101000403c202d0784150308441c088004074118000740d001d0102345d8400220800c064020300710398a03159200c1c103403242c10005204821070706100a1500203030b1701030701c455020445030360906080f0b0040c00d421000c02d000030b1403560b400e0305c45144988240803040f40304105e0900c612102c44030940060415400080300c0c49a12078603000d81035601d440c9440240e5250924400000c0c00d41014401e2a00594204000381c00c1503003142c40305080c0c101c03560304e07044071407240801c207010010451054401c1854256140c449403015070500a50540d51904000c1c42414030000800100d6080303410a440640700010580c0c45a0742d0b000254020b0196442405450600094081d09c50703910600309691700711501510702d00d0310b01 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 488486852 1250 488485602 488485607
    0x1060b09011205160f02010f050703060518012607120308071706010c020d031b1104140f130f0b0c0306040c03140a110c12040303030b10020607141b0a12 67
    0x1041c0d46000e00701800c443c100c2c10f1144601ca01c05150f505d0380c0008074030207080d96140c40864400b200c80500007035a4900a000c02c0c40c002181106103400084102059410400c245003280300100c1206240400850180c0135410180b0014000304585007800011441c141005031101208850140014140c0b0766007841480080b405280510fa0680d520005031800340e00b80981d40b09030081c260280400407920b44810030386a00003403001c030b10071924001a0010402030000752480b40c1c0307204c08203e19a40c00c000b0708114a01032590310160343e50f00014555a5030501a071100487c04024104601200c104000c83c00c1800065024100664081080c40f165400440485014118400030581d150011a035076a0007030f00403014440f00540c6039850301d50b43e410b0341c41c6003404c944040030043d00e010070100241764052146c5007122005944420340b51003544002926040002e04080c28481f030002035050710700100f82580e081c000c25040500f100d40d100d81009584000249044906200742112001c4451 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 488488102 1250 488486852 488486861
    0x120705090c37050f0c06090708010e031c05070e030609010c0810051305072105090717070303051c1404171306031116081b030a0c060b0301060801060b090112 69
    0xb441c180c24800e0b0303420915403c40d0f45510500900c401582e050203004654001444401d0244c0a070030010301d80e045ca000c02c00360a5884a01c10072070745800a100200c25240c0040c2c0d80170310103250103000030396035031284c4c410348030114000e18003901072003548100001d6000550001d4200400c0e51614002961204007400618560b17005964010010b80d0a0080420b1a9004940c220031a0b081070100071226103c000054541001c0c40040e0304c0c0c407a001d1104069051100300040c02c0800e1000814030854040a581c0700003a1000901f08580000e0001881000f100301404141101034140040c10a03170b03010b10021001a1400d03203c1c0244042c41c40007040741041103500d006030750102180340c00e2510310250b0003840c06650b00c02c15041c04110390800041c1016255003440e21032000c1644441c01280d559218880c0c9040c41110f0754010846912171507040004104034543c812030126403030100a011038003421041c5d2007414550700340030707000c1002c030200c030058004001c00380e80310440d000c0c8400c410700070755 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 488489208 1106 488488102 488488177
    0x11030f01061403030a0e0d0516181b200319031509020c060103020402030a020d0f0b1009050d03141306090603060902030f0105120705090c 61
    0x442140d04151410314043d4011800d18100801c080e192400310f08002d8850140f00c0c001c401044402c0001c010a603046007800d03d030166030754910300d1100c20302e080500c44881c02c0000d107541e0311601d9094020445200da56202074400c0801007640503880e280040d4141e03000402449440c0c001c1d45924481c00e058a035000107014942000546c0e1343d8049070450702480c1d00411000c00c5002000400ea41501d4045034016a0382e01c0c0c03942c07040c0086c840c07808000c003940c0c209401800343d400303590302c0520b4426041c4e400310015940200c040340d406100d4051140c0c4204800c100c000407a20a51980e910b10550182591910b103a610307c0f41c40200d455401000052408a800d005459150141030010b043c61201035045040500410041403014003d01340034048030004c4c5000d4090420221006000c06001007207141841c40801205038054002c44509120314003304085919007042c0d04040c = true := by decide +kernel

theorem cover : BRFrame.Cov 488309352 488489208 := by
  have h0 := BRFrame.cov_init 488309352
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488309352 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 488309352 ≤ n) (h2 : n < 488489208) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
