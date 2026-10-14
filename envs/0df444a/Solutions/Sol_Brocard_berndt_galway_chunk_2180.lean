-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2180
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:54:13.602502+00:00
-- url     : https://prove2.me/submissions/cbc5d251-f9e1-4330-ae88-93b75903cd93

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 391906474 ≤ n < 392086330 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 391907724 1250 391906474 391906477
    0x31a09070f050f0402041a090901090b010f051b0105040602040f1a03040204150e010b120a05060d0209130204091101090501020a0b0f07140c0607020d05040308041e1e031b05030606090a11 82
    0xc485070b003404002280b00311401c00c240d02728018a042c00c004d1022400180010f8040203e0110a1041145c04620641459004d5904048200c0c52f90000c02c51402c20f42002c101a40c01030280780000d010702c80c400a50301d054008205c10700003200b41c001e800c680351344d4200800381c00c0c4929040600b2100c00030114818400f218810b0003440e607480a40d50716142c0840103401ca0034010300010401f442e0504204070743c2c9400c0d0500c8000c583c1120b0103601c994850341841180030394a00f000c0d400070b1070541400100116a984c0c0501403200340c0300c1d0320285030b1780d0004a90f245e050240040160400601003144040b16850854014a1a04001045000e80c1040301031741e03080400040c3c110360050b002d104030306c0d40520080105074154600315181c641103440701d1589208500c50700d1000d0300e02c803003801d06104440102c00041c00c0074140211485035944031000f0070000c2408243c87c80341c600c1140110511002103808203d07000035000e410740390b81d004100b002d03010008120f54909030b26130341c0d0125003290a00 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 391908974 1250 391907724 391907759
    0x2e090206131401080a06120215130620060105150306011e1821200301060b03070e010302071e020d060f1d0607050f070c03080301031a09070f050f040204 67
    0x1c5000d15a030001c40b00041140074041c00da031114525142c02803002801084103291100d070151900d0105054001105c115485201000300321841c0341d0f0400304174207038481c03001400710301042034910018613512015506c40000303200388d580c00021800000a46810740c070295a1004050401c1020079807500c1828115600c141c4800000400c0a005014407072182d90420b4082c00103080c2d26280f0800b92028072500300c00e6902d01070880d00352241d40c0c2109a00f0590324003100031026000b4400c03181e941381c2c641480d420540708e8034081106e041500b0495480382c030030340e807400c1d800454201200c800003181d03401e80b1020441c00d9810a80356a40c0001045041c0103040581c0c0c40c440001410400d0000d003030340c0c22075040c0701c407500e503800003801d00807040d40c8502641d5050400840c0d855a441407031820440601d004d45c4000c00010020000000b44080086003140c201c6500180880d5a6103c0265035101c3c000ea014a200c50503a106c410701083c20206c0d003c2204405c003900c01882e00d901d644c03c0401000c00107 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 391910224 1250 391908974 391908989
    0x280504031110110906180307300809010509041409032a0309040c211d0309100f0c080304080702041b21020423032e09020613 55
    0x107216514420404000c0e4850981c010310341044100221141d4000511a002c0c0c0940f152501003079500d584480100300210a402c000c08544225075a40402c0d800d01011540c02e0b54418851030031500c194511414400c01c0d42d5000080c00c0c94010814015905500080c4031250030a80d2034407001c00b10002d442e04140241d078440000c5032a0480521070300110040c82c4c2c09165012100301c0650102c070340000a680c41503a040350080340e6400c141800311620182a80c8a420072040741240c0a405501079200f0320302407060722071500c480c40d60f9410881d1359210f1060071341e8202e90b200c0c0d88240003a00c03070080b00c0c003c4003580c503210700b666031503403940d4016410513101030311000400145c080851074184192000003122460705e000102c41d58201515008038141c0422510401d42041400f0882940c111030281030104601043c1a145400c1c035a03944016a00702c6d4000d1199110541030b8262502ca81a9030401d00494004003502800503800904101e503c22078200c1801c0c00300880281144901030041d2008 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 391911474 1250 391910224 391910237
    0x6050406032d0608070801060f0311030a0f08070506072c040b030106060305010504150e0408210103030809070602031e0c0c030f060406061d06040c0903121101060b04080628050403 79
    0x10000b034035042117000e80c401d0407582e141c45810400f0311066907041e403c480d00403010651495011020900344400342c580180004070b0740702c40c1c4003000700c80c1c00030706480c170f01410899444e540c4140055a00104240621000f4040514400030040001d460034035042d0015001040300c80c102804079003910b01541007100441d07100d50050260313003498455186c900c1101d040c0c52095600d415a031600141c800703800035148090000b001c7d100f03c1840c50b550205100180a1006690707960702740103000181c2a1588046c5001d8141d0019500c2c0c07000054070f4200009030207010b041010f0b401a4187c9500201c0400d20724001c204250b0004e039418411681c6817500680500791500e010300d00b203011103900f034010042c005403108058000d0010121401d40c0320300b080d9400144006002400c0e600703c045c13588001c3c40c034606440c4082c1450391150700140c09400340b0009002480d2200d00051950065000d110b1069120300000391400b1804000c40d01c1c403080c45694038603152148412031007980c90171a8140c0101d002c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 391912724 1250 391911474 391911479
    0xe031b0f21070305090603040f02010305090a03021e0709020a0e031c09090c03090f060606030e0309090619030c0f14030109050d05370e01020706050406032d06 70
    0x80c4508106000400c0240c84500c122010010358a41c0c0441d00a001c01c1011806004050144c01164201c010042201d82c403850140f61030701144d960304104a0002e03017804049907401c0000102c941000303500d41c01401f40c400300307050342c4030000c1c000d0500c1001d03610031903400013030310100d0384018801850b0035507a5181090400c03050510709950f0b41001041e62818024060503140c4c01040d240c169000c1541c00315044510a00c1100034240e450f8000d840b51a0700b200c24410045a68401c10881f10282c0702400280c00500c01c1c2e681302d00406400a41002c083e0000400300e02e403007104041c804140c4500310030500d4036a00d50421440d01604403003200d100003502030142502ca0707070a0b86c1e00b50300d08070024014900d49584043d1203541c031806a50501c84041818480c000807407c07081c2d00325402035101c414545401011036421205043c4e840d01140c900410034541d54804034002040d0f40707090b11144d20341460008110000c1c0f0601300507086007a800314200c2d480360030a848009100804401c085151030 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 391913974 1250 391912724 391912777
    0x5070315030309090f02040504020a0903050105010f030b0c070602121024021b030f01022205040e19150c0c02101d0d020402040807260304121202010e03 67
    0x481100341506240321105003000040c1e4010038001c15152601c1001c2000311801c10848003a00503070304426402400450808241540007450740101c0b40240028441079a03103554090403125107010240c01d40c03588900081d14220078800529055104940052414005c0d6040854404080d1a03844202c0841c40d402c1007034541c11220002000503089482c40180c20819000c2d60b02d981204550004082e44050001d595a040c04960040e0460308c00965503040c0c0300408215141003070b00c681c1041d10165201044130306052089580004080c5e00801c030700c10f0138480c041c01c200c2c0d01001c2280c054032035002071410280075000d01d120700141c45d2501062400184100601d1100e9800b0180400c00b024900c4d100c3c40c0c0100c0300007000700505646442800c221800401c000c2c0c0700e0394200722018410004006070000d80c140d400d4880e0a14001d0041c1e426030202c140b580c880c41130b841400819440703078003075a01007240044e40070b0244503280000030312452003605443c10b60700031301000803200505040002584 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 391915224 1250 391913974 391913981
    0x303030c1b02121c122703050d02040305030403080715050906070e010c05060f24030d080a0b120606040c0306080303070810090e030904060b090f1005070b0a050703 72
    0x26024200070004596090070861031003940c0d5406842840c80b90108410642e050004822000311121240c1100050034009411031180703600312030f03402d860090154000524905100303245103400c51121000b15494034210b0710750b0008801711404690070040000012401c1004100039840f070351036a41c4410490400c000f01901070b2001c8140141480c1c10030400080100340b25501408504058178010007090040f509824990340c000e090344501c10501100036072001c80f5610800c3d800402d064903103244010b00c03100400c1002c040e84c160340702c48000302c170382401548642c1e48410101c0340041c103400030000040d0703000e0021084480b107403c0201030161500346400350142640307131801e042c00318503c1c0290103030f524400202400108a17048003c56103843c0041d400d940288180d0106001e4912074201c0c0035102e900540702c492007540760080026000c002c2d032047c3e0b0038000e0002c040808901d03d00c001c0c0b0a00501500340e0104104040162200251420303007554041c5010760301c00540740c0381904000c0e044 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 391916474 1250 391915224 391915241
    0x3040b0c101d1c030b060c0a0b060d0c0e07110102031306050a0e03090f03012306030106060908061b1c05041b030b07031518090302060c0a050f090d0c0b04030303 71
    0xe640003005011048000041200d038080c0a0001c48401c0c3c0c40c0f2042c100c0040415803492a40800006040d0711083c03000906962054010744c0c4000840d19100100544541100c1c4020312680c2c6d105820000d02144040c1150300c20f10a00b0040250644441c0f10742c220b900c111100005010000b06060501009124442c0d01803a8050204040c1c0080d0386d0003542c0c0d001c0e02c1180b03486400340046843c0903440c03e4110104482c1c074044a0780d40c1407101c84c0c1000700c448080750554042c0d8a8590000788140c0b1408202045400c808064003554075003c01b146032410909608c3d00b901582044031000e40c1c494400c41c455504000100010310b82000d107041844d42c4080c1018890180901c2014400704160344041c0d500500c01d42000100c0c0256025582030383d5203d81c2c040c604407459404581c0e0090b8003a000418075174801da00b0b981563b5900c1d1800445401041040c500080701401100d500c0e542c201d0051220001c010050810310255a565260343c0c000394008441003180071800f00b0130150140242d401 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 391917724 1250 391916474 391916501
    0x91c0201150501260c0c06010609090b0402310305060705041a0406080c16053721020c030115081009020d06090201050c010c050a0e011103040608060303040b0c10 71
    0x454001403c5507891020f40203c0c092078851300c400c003152880c5001c0e81212440d62504040c0c036030035a9038030006000541c09103d0300c5921414000c03220020314192080303030b4801704282c00940b01554141803440844100c1a011140d400280030301002144080101611032007007a5120b0740e40345e0070800285820444100000140e100030f1106000ca00d4104070b074183d00404004807035031a450f01e01c0031300043c50b1070400003070000d01541040c4410700001101d100002032445180315211000001c40c054440c4800c0310241c96001181940c60b0a11045d00034036191007410700c100e0b402015582c001a0031134001200c0103103065419502000910f609009030f640305400034030204944035a031340100d648980c00b10f500034401130f8ad502c0ca0004680c020740942e006c12484030000c206071150804003400d030341e001410050114074000a224000d40c402e9440ca010400800c0140d4105494100103546119003d0200307036040c0800d201c0816a0386410016092803600e02c00100f14024103804100211072000040c0103 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 391918974 1250 391917724 391917737
    0x27080715081005060a0c0c08010b09091614190803040905090714060a0c0f0606140d1a04030e0907180b03090312101d010504110703090e091c0201150501 67
    0x1042089001d1600121942035405580c5c400304000c041300c10a00e90003004040c2e0880c002e002c00c009105502010800c201170314458402c0d20b6603a40790781d445450604c00754040ca0b80c10b80a101081c081c0c0e80250b1081009008080b500c8141c1201d619a0324071604002c0d402c2e0f0010908202520300c900031160803494610203400d41c02c0c14102d04107550a0b034108090b010b5400009d01d098031500c180041c0003043e070800c411009810341e9250000c09840c90303114820302046500d082d405627203000342c0300000b0300e80c4c0951804ca12500740b44a016960344014000d4041c0091042588480c3c0c9940180601c00c0c801540c6030a11011641c00a0308a4540b680002d40b9504003402003080c0d0240000440e81b00c20742c1500014070b1a6101410f9840c0000d10b500300040408182e1240400740c1c8404100606071442103805000f940540c0f060f0b00124001c0840150004034808010800c0441c40c140d21034201c2400c9090301c05210241034042a584299144280143c0d581c10f000d14038201720b0310308a80544801d19001 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 391920224 1250 391918974 391918981
    0x160e090408070c03060f0c11010501050a031b0806090f060114060d050a060513020703110d0c02090c0915032205060a020d020904150503060c030103122708071508 71
    0x2101008000c100404080000410200b440b00c1d0380442c100440d44076505214040e2810442c1c4044d000080c3d150001c100405444070b1585c0060203042d05841018059175201407850312020740e10448ac4030159055105201d021a00d03c8080c01601e11907482480200310f40a03407100c4280c40c1040587c041c0a44032407801d29070001d1740d01c4600302c401860350300001043ca80c807101000001440b0b941e00440c0d024001e4120900c103520750360060840035007c4d07201d02000d03281500c190340e00c4840396a4120700141d108001c210040c335140807034640054250400c2400c0805980120306154010700c5001c010000c0070040050313840f01d1100c00d6144800910040c02115550f0f503a095660501501844540e500424118200a482e5042c2c600f003060042c01030250842c211159000c1c1c144500070103009005072400203040ca081d42c41100e048941c414610f4041c0341001008940711034402030b02d1421018461141203040412080c5040546403a002800c95903141101c131601c03200c85512650140400e8a080 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 391921474 1250 391920224 391920229
    0x2040626010506030603190b060301061d0105040c11010623030a0203120a2d030c0207030f021c1b05040c0c020a140f090916091b0e01030f0e06160e 65
    0x60303411078400307031041ca0301c90301c0d00d5001a0030548264031000503d142049400203000701d20501e14012001900200030f55a02c1d81c40c5500090518007401d26002c100f10010080350030a43c0c46440f82410b9440d00c580a00c2c0c01500f0341d400e4a40b2584055408441c0e4402004001e40544850845403021401042409440d501181d20340c0d0031000350a0b0700f10350109117881f42d517000e041d1801145070419041d440c0810468181040071000000e4500000c0c42c2611001407640000351010680ba084404960648899420411903c1358031841940d0104001d41001c0081c03900700700880b44c0c030300c041600b03141c0398200410b10084500c02c910b40030401840000300c8015807140d41d051000d80d603008868440300e8585102240903628a0b0b140180c00404241c2003180710100030802c4002d000c1ca01041e489419904c04580080d61800b4400079001509801001e103901e016907020302c1348d0344040c140880e803160590b40c3c0c0d400329043c1001251007601b004080101c0ca00c12841285602800ca00300502c0b21070b4400003 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 391922724 1250 391921474 391921547
    0x708060a12121805030f1b040612080711040903030207030f260a02041505070c12240608010204060e010210060b0702121624080f1303051309020406 65
    0x101441880f00415407010b80500248038003020b85009400c40c0c4074240041011075a49007207004002e82448110104d05e010f2074280121012142c3c000c0d80240c02402c0fa8494a000d580141400c84550340751804480075500c0317074014007085071f0003a01d0044c1c51b2202410041d04465171090b8a80802180d00c20000c80c0e0654541034201c0e084007940ca128031603480c5d4640300000d209981140321000c43c400c00d06854280d0060040c0f21061003402c81004a540d070f42c1601c101c800d281da0006000c5d102c107851000c81c03d45003542c0480310106140011503016680c2c24050f003240d000380c0105000030011300020340300e540c04210508000c180c04400300951482c2a00100c110300035000c0003842440a140d621a078030004002c03030100300401c0b00803a00e09c980e841c9a038035100009540b2118841290002e90244a401050322500c40c1c050b242c07134208a40c3d01e45004070b0385100303038010807000e000303050013820380400e007529140001d0702800b40d00680c0c841c1019009002c00006081c02001c0c20a0034400100e200618a03 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 391923974 1250 391922724 391922753
    0x70207090b010e031e0d02010b0f040207020d0c080f0d02060606070b091f0504021809060703050612010f02090103060f081507050c0f06180c0a030f030c08030708060a12 74
    0x218002070400340748004a400b20310318100d6607450300c50060fa960140e411000d10030300900008080320510001807009a0030381b009410020383c4044903405421203030030702d90000c2611500c0100301c42d00720881039540700a118019044007119500c14480442003020400c1809403408032030000380707218a40140000d03010311556030020400f2107250080707400c158003000811341c0296402c0d40d4100f984602142000141400c0b50309912512000c404034540d0f0350007615081c09002810058041507030b40d0390081d1301910b00500655001940e150b0b002e40500c1c000c1c07085056400d0301d07075400341e9250003c0000401303495880d0004002606605800c00c040c041c000391a03040c1400ca0158400710307560389003003660580a440100303e132601491194000348540481c4103889016008181c4050040b40d000240c3d5070021461484d401260348402840440d03034600c0c02d4841c0c140310b40380140039595a903a41034055041540c030400440e400703509001440c5082c145940290540303110b9103204410940714072035440306d40e4 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 391925224 1250 391923974 391923989
    0xe0306150904062403081c050103021c0302100f24050a03060b060405040c180b040803042d0e07020c10050d0b010201150b0a14090123040918050d0206070207 69
    0x581052204e0001d62130a05004500d1140d5940305070358909140c0340c154032a0403020603c24144440000405440c4a154103076500a4264060009040c181c4002c2c4601c10209905601c111101084c05140302e0080c208681000f250128406108282501c1d0090100c8110030540320b4021090006440315180003048076040030000c99082c0c2000e01080b0f0621a64201c1034000341000b8a4a0b2002c0d0000d04e9180c00321454401d007101c040d0380d00c5401c80c10780100d016105058008000410030b2842c50400902d101c2030f6030780b111500500041c114110442903600a83c9641c0110f810000d10b140c050102e4a032082d400e89507111503c070300303c1e4014201d11440403900503582d6149250a01d59100f50b002040d495407a80c041603110361210150306880d00181e10800000349000f00d00c0350042807104c29030b400050b0607141d42d411154054006180c0040c034150880130b9807018000041c030352880c1d0082070004003000344002e900000d00e0800c4c078142101308481009541c0054240408507900048440445100 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 391926474 1250 391925224 391925231
    0x1515020d05071e0b04031b0320010b042309010903021513050724030605060405060717070c061d1011031209010e0c01081501200d0e030615090406 64
    0xe00d4052500251a50f0880c01d043d803960412040240c8050a1401030740203403184030b03440b80616000e61210351440c074000c0001d000c40d0399907296420481484e07044808640004102c240b2400049822602c1014410b03507140b207584014002d904055404a410241490080c800215542c8000c1d54442d85049040e5000c008400000c008004c4050b405c1e080079844ad0a581c2d07100e956145501582210483c0300e00044640d200c0182003501030b2040e1007c0340c8018006d182028903001c200912608809000d40316243c041e5844d41d2410022001400594496030032404120f06100008055450001300c0b0403c5450320307400e003801d41e0b5500c0d0f00700c05403009078074007048168407030042c00b811401107402c184140c005920074000c20002c10b402220803000000129881810b050004541c1e0040070b03292890180e41c0060440032551041d080300c03215170708040780c0700e100d01d03d000119032501c0001840040080c27400c801e203205600c0e00740b2441350849101040340050310818000a2452134010b0720045c01c10307a4 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 391927724 1250 391926474 391926487
    0x90212070311061b01050712050907050904061122060905060f070b0a1b02070e06010504061d030102070f0506060a0e06012001062403051b070807060b0301020d1515020d05 75
    0x204180c2484d00100d50318024011401c0c001c00160944141a0076030015508240c0041c5101c10b00040b94001c44100502c0204180c86030303201d0100420340140450182d1701e0401001c4151940f51006207190011900844002403604100400a805980000e8403c003001c0044c7c0f00f142c240e0f07409480c4210b82003800c40700641c4408020000602c00c101c0c0031451640c08030b101c03891294004c43d0031012101c0d552421880c82e500c040c01103c031842603008a0010070441e00082c03a42340041007800d042c06101600051604005480d64039072900592812110750348051708104081c109100520000c200c40062800745044c00c00003c0c101e21000e610301180030307126904140441409401c010010180403c030341407100455504038001500308403d06001c681000080703100c03c03800f82542c80010040134010790920250783e541d81d81c2070b48800c070140ca116488812040741968284010724210005441c0050400d4a080c07518286800543c0149200c0382c1e09001c541041d50041418900840c00d460f10a0f600c18 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 391928974 1250 391927724 391927747
    0x80a170f0103111905130f0b060901020d0f09080102040e16022a0a03080f0717390d0305100504050907091113120b011502250806040609021207031106 66
    0x130440c0d4800c640c40a441c07544c0a00c400165440b0103044550f0581c14481901004244001d511032942464016881442c1142d01c80e48114481c1841812034a80303043e8269940070614207a82154100426865081d002c1c0f0014401003400300300911210700140081081c036000c8074544c04800c00c0b070079459403128801c8500b560349000c0f41a0256500020140d00d80000c280e40120743d03082403400705c0d50401d50401125110f6001c0c4195000c501210301c0d90b5040d8002812111000000340b60803400b10018034a003409032410078001403101c03c1c2c11f036400003410f19040c1e40401003220b0a0f0f100a0040f49072100f4004824004180c517400d4410b445404940415100420203443c03013009a41c051000b0700d900041051003480995034001130245141c40d0090740c8500140c0e100b0303401d01503507001580c003500e0341d10000004548042c1c4c241e4a0408543c3c611b030b03502c6480608052086400711801039442040c1d40451402c1d042c00200c0541800050030310318110380d00d8403600c2070003294491040720040340700800710 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 391930224 1250 391928974 391929019
    0x90a150213051f0818030c01050103060c0903170d0209120105041511030f06190602100b09010608180f0f030d1b090605180402221401020a0305090d080a170f010311 72
    0x881c1c5c0c440440ba610000003d2050080c02c003800221111420106801c0000f44500c0528043c0ea030000f002e00440c018a014a541d264000040c01100640900003500700d0760f11400e038164444141d00001c21103190600e04141c0c40014942d95070012441c00c0021050003e54405507544100f5414491600b600d40c8030000340f0171180400442d072001c040d400d0208900b540070400900c0c0c81010f904c1403154001c0079013044441c0009009800008492500140d203c2000d405034140c4107c1d0325080d6414105040d602c42d062003200307906080c1541c00050341d0325007010284a40070300e1030390311000629032051030303100208142032500c646030070420080741c4402c04107400740c80f404103201d000380110b41d901c0c419072000300100e024403180103d0300402200001d5808410131040c0701c40e50141c1c05003210100d10b582c251487e80004014071b41252560011200041e0442c0c0101020241600c8030003411034038901200c0c440f48024110321461540c41c3c010000174031000804101c4000c1100c903410810044c01c2c4100e100d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 391931474 1250 391930224 391930261
    0xc0d05010b1306020a020d020418080d02180d020d0f150f05010302010f030504080a0c050f0604140d140d0c030e0d0906021b090f090a150213051f08 65
    0x1014504800001c0c5008031200a280750201410110509980c40c8002d07625801c2c4d1003030185d000a10807986900601c1c00f80d100c10711f01c803031130000845810032031f07202d044c05604000f2400079055400a6844254110f6240e50540c0a5089407500d548510325808101d0240d00340c2c000411030341c011219141040203026004011400d1810104003150442c40500e001d1f003803c0c881a404950305000100000303110b0b0041038840d0703801c200d6091500b4007070078080350107103801e901c1501c903402000e01020300030b1420b204040c012402000300401012407408900d06100d1526500c509101040c036040e02102c01c5070094032010300d46503130700007280d03e4800001d4010703000b0781c4030741c44840c051000001d010b03941040d00901a100254212514a00d51131480807018000070b440315808440e078800642c038260100d010541c810481e070705580030034005580d00010300e4850b80c003c03e440303034000c214401409010680c1d0401414121790890001a917000440845003032410040c013001107680000f420381c02d585180141 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 391932724 1250 391931474 391931497
    0x3080903120703030507120912110f01050a0b0a050913080a17040b092a1c1a040501050c0304110907030b0a0f1701020c100f06090e030702040b03010c12050c 69
    0x1551a1a40f070001c009000031284040400c140120007510a81c5a2196150300390740038086580044100070185c409403d02020443c0707510a415898a00c0305080c09182e00940c1c00150100303200881604001800c2c00d582c00550048105c641085444200b408011000c9900324440136503644c0806001c86180740300722114800038200b00c050204000c000790400384181221410b491001e00020302c003030000c1210802c1900d51090300f0310448040d00d802c20f051501082d2005600440718001d81e1041c1144068424052035580101c04102c103008003809995800000e011000c1e1a51400c3d6890810172400d440c7d40303038010b441c00300002c1e020303900a5004241143d001014040801d40c1d0700d1040410800d00e00542404030303010003030b43e0f02000c3d0500907100c3c620818809415650070800010004007410703910800b8071900d5443c0042d101e0740c00d03c01c0045902c041e9010307607941c400d5801480b044d24804503030300c0d0181e8500100e01a40583c08401d14011602103003020489844507902498035000f84403140f171 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 391933974 1250 391932724 391932727
    0x8150901030b16020102030105011d030f070e04140304050a1403160902070501061e150207090f09030305160905040c0903140604022743031107020a0308090312 70
    0x418410b501403030510440000020021041800500300d00340d000038450613000c160b540f5000784080e8200701c04035000b02d402400710307080100c000e084140f61120650201c1100d014540602c000c0c00220721861101c030107660f000751718151900c40403a10200e018401c00da0403a06840002038203a8091100341842040300c0c03110340e0307040e40317030008040258001e100c00c845641ca080e10008421240e0f0b035520041d0f0782e9080110f082d4600d4101c42d00041000c507030024007140030708100030500c40424801e841e107103045100300103002006443e014044450162080351603c816408034000954010407170380030b503034081c4c80110303c1624214060b0703401d000a070802050104405006580d60000007a040e110724021119401d160b9400d190313142519007041c01d00421890b810340010645040c0c221039048854100c0442d128401d8000f4408002d12403c10303942402200e0724104240041d414000c0c1c3c04d200149500c03080c54044641d0001e010010b451000a00b601004509030348180d50a2159624040c0543e1015 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 391935224 1250 391933974 391933979
    0x7050c010e010c020c0f0a030803060d02031014040201170f04021513090e0705091e13210f02121902070e1005010201060b0f121b04030b0a050601030213030308150901 73
    0x1e905c581ca00040c0a0065204407804280352030701c2c0c80c602003101d03045a1840d2454640c2c0080c40850011403006a805114400d91300c600d5249511900071a407040d04030440940c14a80f000400180d500d810905521104500f4004ca0326a9075150613040ba9040710f048100341d003400b5400300c0b503009005030b0000030700e5080300006075000c3c80d8002c2d01c2102c03035640035074160540b80c074200080e05805551442440301d1b8000750005000c40341d2505a0001303802c11060042075059911440a2440012060707000d0b13189402e00d000c1c080d0000c0305006064903d00103012120ba403035050810901a410341d070072400b440b242c8860320f0903009011031300c00784c120300328403407042c2c40c0c41d014465442e9010b105e042e00640c43c06000007007010b0f410044d01c44010388540598a04140001c54a00e0900007503d440350081c1500305041e11164020000c10085200c3d05249005240004584048488c014003450506004000c084050103250aa0f801500d505040029050301c0720241182503e407042c0c0c01541084102e4000b = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 391936474 1250 391935224 391935227
    0xf14040b010807270e10050607030503070320030108031c0c020c060d060e09070e0f01060c06090302010f051008060108030408120a030e0a0b0f150f0607020f03030703090812030702030307050c010e010c 88
    0x843c8241d5228006e1096140d40b0000d102c01c6100d20b0b072010340018014804204000c0c0f1039000701c007801041010b0031340705000c0c0120007205a0700aa1141100e03900000d12001404500c000c42e401e4403078605420400704000e0503000c0d4450300700541d102e00c290ba000410000c003d032181c0c0140054402901280c03000d18142400980e51a803c2c080c0c0c00300e41c1c41130300000b4007981555580c6410f83d002680e502035001b149070398800181c168036408030155500d03211031900b08a0340707104403441a05641010b2005610b0080c14905040c03060b0850b00d01a04108001c0c440310000080584c01720200841556480c1542902200108049a018806c500a403000c040501011035103050061400407400b0f001a11518400300028111600f40c0e600480c1d1108002d44c3d5141c101c01801d5141d00240c1031070f651170082c10001b811540501c008a01103048010180100780e03040100c16200e6610003510b82c5982006c030806503407808002c24100400c00e0000e01800203800030b4202851505800000b4413056540b10390 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 391937724 1250 391936474 391936499
    0xb0a0f050424021b150906270a081b012303040501020a080f060112050613140403020f0a03080103061116030206011403070f0b070206130f14040b01080727 68
    0x78484014410200811314643c8100f0400c0e03140d030401400da00009003844110181a00281d000b140d000c0e8040c003500419022000305014040c0d00c2d0900340142040c03440c20071002240680040c1030f50b078007170001c65034542030f4903a000e0980a003d00301008a00032180180540180311109440200004014801009415000740034903075082c2d101c1c4050f580d039400350307001407920807690140040e01005c4c0c2d106406d8a6603000c1d68001c3c0740980100380300341005114405070349040381c00d4202d00d105030302088240f40d8180300301641c000082010308401c0342e658600600507030701130002520303a581d01c030350400300c4441d06001c13940c03541c100110202180d005820040d4403404248a6204861041c1d580303541c6918003c039450064402188441c2d00c1d003800d041003d041c82e040301302c080742c000d41c0400c01c1e0b804d02001d020030300c070080070102e9299403514201800b00e003c0c034582408007402181058451001a1b030454a8030394803080501d410f15400044d07038016070f8030014a20f41a2907440c4449000704007103e4a21 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 391938974 1250 391937724 391937789
    0x4111f02031305090c0a0c0c1a070c0605211e09010516020d020a080c2b020c0105130302120a0b10080705090405030f130b0d0c080603070b0a0f0504 65
    0x620b00700307030780c44007800108401143d844642110030041c0b00c004078010036038036501a0080d2001c182c03c94440c044036240c83c50b4a90701c00c07903212001c104901007100c100e601c18081c086514042c0d060043c6010030840060388801c400d41e4a850401c000340505007041d0105081020110290174075041070f40605000f404203032059a8201e24441c4014503980c00001c864602070269070050002c500961914001904006880c0d00280103210b804500c11502000c070750801000d014100d4000440340c2c4001c2e00d00f002d13580e2114140314061000e410030000c4041e1441c1200d2301a960384407405039005182d4105021070b4401070074400c0b10018403810341e144c0c0d07000f0410784d00140d00700c9034215205d40400927210000c45004207160b204101c402400402e25001e400c020312081a10105141c5a8010400a8100c4103210440603582c80c92029095842000c55800280a0f0050090795017840ea0014142c86490b02c80b00900c2010060003080e89e21460848000b85500800c2c02891400324008145140643c0e = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 391940224 1250 391938974 391938997
    0xc0d0c11030d051b0d050a0509041107030201020316030c050405010809100f0b0a0911031303050408010c0810090b010e061e0705010c080f01080d0806040e2d1504111f0203 75
    0xa1100c01911007001a82c02d005c0d4070740e511740d0303414880d9440045800f940180d10541d000383c0c507aa8104030b450080b40203401124426000540c8074604201f6a034151504403410604040c1010300c0c0c442a16081800c41c0d055650a203810740140c0d861854003860701e100d03040c6c1c82807143d203009000c81e903100e650f5021000000003128980312191b40c40d4080004d864a551040d070741c103203081001c40c070700994801e904501d441c03284c00d0050030103030750312800380c21202d0128004010642840030400c09040c0380b810707003000c1c0014100c2000480c00c20300008280c0c0a004820794007070300b40081d29a22082ca0130364a1808900342d590b40035954030003841c02c68007074000b4400420206000c040802c00c107603101c00030941039414a100402c16041c1c00d807012102c160003c6c0031950000d60310310f401c480c04c0034288501d507000c41310455086540380c4540d1500303041545000e1030004507000258003100036500301e800700b41c110381c002018181202c404000165000d65000c190b0903a00000000100c1aa8001c0003504074140c95 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 391941474 1250 391940224 391940257
    0x12050a02130b090f070e06030f01091b08041103190f020f1507201017090d091217071b05030102120c0304030c0611090a09020c0d0c11030d05 62
    0x71403490680e4440d100a070b034400b2003040000c81400031008030b560301003120701d81280d48080b0013000c00c555501c103035207240790302e0181e40040c40426824003a056001003000c010304803101d001c49005201810207080185075041010000000f560100103446412400803102075000c0c80b02d1a105031800d8442c03004a0041602e014105d1192600320380307111080f0480f030103903031406c046c80e0b0710801c03807030085008000400109021190540c4800018880150302da84a00e9400d4001881d00190810000c12111003680f003111300000307140d802074500044a034005d0994402281c1c43c6050941d2700c50b0780c1404080c4881c0401c1502c1880396091a4907104132621214203984e50300c43c0c06050a0b0f2080e05251480311403c0400326001031000b00003968401d000749804442c10405a07a204251159001540c224030808951201180340044c204801031511400840ca4000c1d040c00090316104c0d42c160280034094032500030414000d1642030710700701100c0201a20040307001d60300b01402a400410341581e0b200750 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 391942724 1250 391941474 391941499
    0x7051c03091a010b12040303060f090606022e09050a0b04081903020711090a0b04052401050c0c0f03032206030f050609010911090306093a030207080412050a02 70
    0x11500b8400381030316914000146007805843c40c200c08610007400c220105580d58000050344020b180503180070741044c40b8049111850007000a18280b84002c030b8039000214084841020710b146405035154208032a0082800041070405508140e10300f036001c0c164102050420040180d178000a10b20000700090301c02441052a800310128028400010030a5154161880c01480d000c11801d9005111b500045803225008010500b503a406a5001e030404686010b00030101c0030f0a8841e4a0740f501c2860900d0808580c003484955a00c1555440e600901100c51140c0e01034034180300325180300003411400c072503242018850041105682c41003000007803400328072000240c440d000b428041d00005084a070700c0c3e400c2c501c1c0c1100034103c04c0b2040f40c0e01d03402040703d501103840c207000c0340740b2444030385014100580640852030311650040310329008001000c543c05070f40f03060800b86640595100d00d0b0050b2160b1f81494600040d200e5604031300d407a6088240e03640100500092071f05001d03403090f60309551409 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 391943974 1250 391942724 391942763
    0x121315080f060a03021f02120f03010b090a05031014240609040207140d020709021912020409060303081807030c03080309070e09030d14010b0a0c050c04020a05031f060c0807051c0309 80
    0x48840c1d000c000e0034100010809001c0000c03740916200c010700501c0081c2d5a000042d01c0c03d010340d02c030900303440c0e1503100c0c1c1c8014541c0da45106500515203c03242d00074081540211814011a2031258450712011a6813809a1a2072781a20a440d51202005030403c04142c02140d54010384c02c4641c005105004c0040b580c15081e000741c4862010b4060400a0344102860a9030750508140800c200c0c1942888005803c420901070903000310300075243d110039820018206030802540010180756613200000c01c1001840d11031003c0d00b100c3e080f1010b076849444a0b40440d04110007503104029403604042801501e81002c0005c2c030507c0c0d42c103070003000402840b00000d0a203900034454541c88400905c10350300d215008490452803d4030071030940c2d030842010b20024003260400c02644000840100400c1102048040602e0032902400c0703907480c1262502d44001d1200e1220b0380c00406040c4045000c00400100308044aa080210318803240c40c0381e5050380007001420107040680d4900c4010b681b000044 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 391945224 1250 391943974 391943977
    0x2160b012102010804210f031a0a03081b0d09050102010b12060c07020604150302030108151006030e0c0d080307020106120b060120121315080f060a03021f0212 70
    0x401140c0346001c40404a0303001582c000000401c2952091080303065011040381a284404403180720f074407110005240c21700018100d4010049100424180311241c0e00d40342e8844034200c0440307920050b91503850030b4102c1d0120400c41c02d10030346400c521070b1090102045403c802841e00351282a8003c100c40d941c0542044240d00f00b01c6202141398000c0e00118445114200c01402030a0000c0c00181c50255560072894140d9510720621340026800b000505c40040b0500501803541030002051101d410070f00425840b242d0035101e00c030181640d40207040015401486680c21030038004002d9100d012207802c041541398421152103005510746900410042e040030000e40c07055811040d103249079038a0100541c0c4003203821001c00c10f02c042d8811050403001f020044260300f04060001c49403503ca483c00441c555012540213441c031061401c005441d4540c8c000103290384154001c2040520303032210b401162070b20075a9040a90002019450000d054106c014000611521982110124a907140341300045 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 391946474 1250 391945224 391945259
    0x2040504140f0f27010c0206070f0905190503100501030c05030a0c0b0a05090a1d0703021815160605010e0906010506030705070317010e15030708030d15030602160b01 73
    0x1e0712038030400300c1c03101c40c1c11111143c0d01000c2c10090000032004c11100445881c110058541d02d82c0d1a52180d4943c2e80c0e043c40f210b81c1000d568140b0b030628114244015041c0409801610301511031b0301c802180c078040101500000301f00c00380a17506403030740c0f801844025050901051b52200b00c00740c0b0018041c100041c00c000607940144001c2001800e144060070660f100c024a04c04001040c0142c090540d5640c40d1440101100700f07040d400e4115030003101d500e80f41d005150102f814410f10180c0210a03118480c20300300c0500300c50350110a0512454144140115a00c0181da142c540c03510b0f10400c409540964162040e40c94207503515942d90000a544140c00d008075a0041828000310306a18041c50140601a100e8209005100564034000f103514600f6800340703000c0c607003103410f004940307000030806000144180e018100850600c3c846034ce5921603041c000481c595980030401b0013030202c105950146a21041c01d6594640040d244405494146020b41301d0048100000a141d00030b000c0c140302 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 391947724 1250 391946474 391946491
    0x30c0303040506040e040609020301180302280f0c0906080304080f0309010e01050d09120e0f040902030c13020c0d02160e0f01181d0708011802130203070c150204050414 74
    0x509404c0c81c81c200344145c805401207800a4603449010700603a402e0103801c00c54050411201503039140390400a01d044150000401c0310450002030351105081410300700803d58000840d139032192801d10b0107284000a940c00423a0346031030303c8004900d00070040014001c4410039001c58161401002c0c1d2140c5134400c4005050201c0d8200d4250100c550060000c2c101c61403d844002a48526540b07030003024095800d40c040010315056600c80c0107181c4880481c40e414800e0f10100b0846504d540070a541f0701060703913440d1203424003481203c0d0911003030301122040303402c000a0b24900c1100e20006540c4880d50b116520186400340c20100c3c1100c00307000b031a8403440f0860409540c607444c1440d9012003c2c00603c504021071784406001c55030480111390140c01070100c5000340501131030714580ca0700f155041e03000001c207010410305040140c0e452045134200c0d01d4035640016030340e8899a805452528034140014420401d0004060504016502400498000b501c0c04d2022030400e101c0c281d90307444129142038 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 391948974 1250 391947724 391947727
    0x60f011703030f0f0c042409080a0b0103060e0f070b04260703060b0105090613030519080306130b03061305150c0a030b1c060605031c080106110c09010311030c0303040506 75
    0x214004803c44d9050b40191100200030715044d160340c1e4000c422241d0364280c40100707c0c52a0b0714240c95500c0000309000300307480c0001e000c0e03000d016901e90207240418030001d030015448940100d50360300140b00310303091046004115602d40c0d1f9100e909280ca0340140c821683d50158091507070001000211508640d00440d2003d00b80d614199900c2c0801040200303a47e90400c0381c10701c2082e40c0394840500808100da005550181c081e49545440d0b403600c914018124002110041c0e2180001c40e40b50950fa00484121514110304008030014401043c02040d001c1e854030401d024003000210300d15a03902c41c907002e0401e9580344210034410f1a0b4280c0e09864181000d8410000c07100c485100303610203e18500c001b00240290349007010500c01183e02140282c40e05035848200708400e240801c20100800b4400c660281c0900e85a04040c0c060401441180d060111500358080ca051080c0429103240300010000d90140d40c580c14400c2105200c040c1560081c802d01011200c036113030020584003210401411503 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 391950224 1250 391948974 391948981
    0xf1a04050d0f0507060501080303091605031209040b0405240a1802071b0b040f0e01030c0e090a02030604030e1002060c0f0a0309060216031404051e060c060f011703030f 74
    0x100c0700c80b90306408003420003106100c880c00144960180f0b50090075207000443d01c030308042403040d041c550b6040440e101e400d06124100901d44000c030f9011114102000b40540700c2d6031290100d0f01030a0044100c9911600c0c0c1402c00541c46000a9440746024100c0b00081510b2868401e000b442e01c83c2d4021816164551a100d01c00b16a02e50010b00c0038a1081d591080b1200342942c51a14282540d0804002c4141c00314080c42001c500c0c0940100a26403031700c049049500d1a11009070030b60140c065401034079030200028003840c4041241071401c171742c0902165a149828100104003055070090207100751110b1560a04080c0300007442401103a848540500d000c5507003600c0324541e0b115103001c00905071108456804100c803880501000031141c5920504683c26240040c00000c1c0d145202c0480721041c0801d0240d510740002100420580800e00c0c0620626071000030f50354041c46200c07990701d00c243e07010402c1104540c48680d0407180c146d0301e090580104a003410742c40340000c84494a0201d40f08000 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 391951474 1250 391950224 391950227
    0x1403040c0b0702060c06040809241605030c03040b09100305070f260c1206010206150d17030a0b090c0c0a020f190e160c03020c0409020411070f1a04050d 67
    0xb4010b0394801010145060154011207040910445094a10301e8010450403080c0c10080d00c40401c007200c0400301454508100c2c0302000e2030183c06488200d41899080e890204201001100c82416580b001c40340c9955560340010229444907a00310301600c80000340ca82601c0c017900070307280107c9103a203a02c0d01c100c00c41c00c002c444085803e80c901110400b00900382da205800f610880e4002c00201f0081e40d074030141030740310b907003918800341c003072411544a0420400c03a09242c0350f01d1035004004481402000285080154401c007400c0c00c03083d180c10001090200038001c50740024150801600c1c030100503070b00d00321a2726031401506081c2660313404c0f43d03e084d001480c0a5180f9081590f00500d031243d044110b0b154108050659009030807040d045900f440007401c03859190055140d0075180c004910f803c540c3e0001d403a20a850241d6009985540385d0004640e0350303401401c24640c10700001a220101400e102c031694800090541d82e00180c02465000c403544030072030a20031a0083d00504061165010 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 391952724 1250 391951474 391951477
    0x803030a3b0c041e06080f060f040c0b030a0b090c040b09040b060d150303030b09070f051b0d0f14030603060c0309010e070312180609060e0301060e04121403040c0b 72
    0x14410200d0040100c02c1510b80d40c0c92040c22524241c0446010003030301e080004408482240d000060164445a0780b00d95a0100184103507020300481e4a41c08143c840d4500350030088042e030011500400040100001d03070350035a0050860500485a04010b610b079031300c01651a01c281e000358000041c0030048901c0d0790130182c21030704019002070165403500c4104034400040751036a846541d05204070b01000c1090640c140203001e00030700e0858009000741031001c0050280b850541d00b880030301030040303141101d58000800082c082c411044c1590031103840210300034000c00328251280013042c030343e076808074102034154203a920403003015000300460b484031980203400d504001c0c19144503640b00d21301d8184400090004100441c403e061440900c000810094445442045901003507100c1c80f030104010ba41c0200c3d02001c0394a03a00b0407440700c44198021a025192175000203582d0001e01c000d0100f0801c0c02000c5200035407113540e505d1090f4802840e90031141c030043c1c03805800c1a82411062002200110 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 391953974 1250 391952724 391952831
    0xf2c310b0105120a06231305070c0c0f08120306030a03051e0c0d0e01020d02151003050a0b0603010605010519030c1215030b07030e06040803060307030c0803030a 71
    0x500c2414000380280003c0881402c4a1442c000ca49541d001c1000c44281c1310190310801c0d40400e118207401e60100441c4c00b00c2038403000032400c1512400410109030042d02a0300101c0c0c1c202194100543d116640c102e4001803511946040348503401e081e103030894099050303900a11004026200100280c0c40072919171300003088400c2c42007240218203000401950080480302e1200e005032292078424107010b040b07114001c40d443c0c10354200748200c00d200b0303501081d50803e120492101c541d0f1a283c8900484402e0f5213a00001c00c0c510464080030203100707124244508c0380504900030b10545446000450780d078021001c001c1c8030074410074841c05409000b5041480c0c40320080c541402818040c0340001e0940d00d046010510f4110180030a10a02c4070320b00c84658403010a09041c000103201c031642607602d4030006c001400e0300d00d0210108074196801c0c002100155000404100b440381c65000498032584183d580c156003c1c5400c50340c11110002240180e96840d00002040d00c0c0c00c00300c020300b9035041c980d8 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 391955224 1250 391953974 391953977
    0x210f1614031506180a0e01030f1211010207060b0a0807030221012d061a040605030915010e091c08071809060b04061101020f0403030f2c310b01 63
    0x14800010a621480f0103000c84140307554450400c000c0000c28444000e007a42c0001030781c0356a0302e0061012415020710300500541c840240052104034a2044800101244004400b540001450300c140415608402012142141c51031149541c03004416581d054610009401c01450603421009126400510305c1c590784620000c03501100708604540303c0d0305841340c038002000d0344000c56110000244907000c041c000c2200404c0c884000f084420039207004601c502001c00100100090150f1401e0115109103849400e900120b135071500c07807542602804844c080c03054441c400003150048604071034850401e050303480d080c00684030708104880340010b40c414808a01601500007403080c0c0c6502c01c1d4401040c01603402078640d41440c0008110300a0300e0b000ca04940c0c018401101c6020022088074100c0e689404d048207224a001001d403a03029a500a0403c81c0c840c42008030800c0c0714054948014802c00c8444041809601f07030880109502c0c07001f031010741075190000c0c0d00c640d51254030926481205 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 391956474 1250 391955224 391955251
    0x10903140a1106010308040306050f0402010509061c050c07030210050c040603051e0c09100e0303250f060902040c03020a09170708100903260406050a02210f161403 72
    0x90922543c54020282d01c2282d0741d480010302001846581d00c14960020250001a02079040540000b000c5002e0001701501c0f40800050703041084480c42c0041d60840107810003440b0515219880c0011504440b074264058040c2501501d07450320705200e4a40b044144405090825040c40d60440c003d040040c0342c11a42969100f1455810381d0180703003240701d9610041d507543e1b2040c2c210140241111002e5600d01840b08441105840344d40201c10340345911000c00041407405014400401d100030b8000e0701510301548101050180303e4036401050b881d80c020350341402118840c0c1c3c000c40c202e201d064507800010704276501c140100d600c4010b00141c4003c1c1c005c1142c40712a20b641845040040110320101c0c81903440c00e0410401d500490031342c1d03491a40c0c1d00700a0002496155045201900520003042c1965800001d001050f4542c191000303022210010745607210345a1038544840002d42e01c0b44802801000040c203c3d500c23a040c021003002d556950008032055400c81c1200d0354102803c95102510f5 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 391957724 1250 391956474 391956497
    0x40b07080904060801050f0103121412060a1806080c1806042012010e3714040f02013b0604090e100c0314070c05010608030327010903140a 61
    0x2401518002c0b2035807047c1825135491450b28089168418141c00f0610070810801c0d0342d4000c0c0207041d1001c0e400c00320903104162791031000284c41d240380c0d50043d0f0000308440e41c41d20400d4840e43d00010645050404541c0203c41d1030003003212080088c6200280b06290a00141c418101500300795005c1e00f2100c0c4400001c0340c0b402c0000fa09405c00402c2011108100300108501210703045801d811854504003900d03c0d170000e0002010306031443c600780c0d0011040100040c084017850780802503d0800340014841d5013800d16254240061104c1c080c0e0000d0702e01100740001a008880ca999080c046d41c032206211043d4001c0e030307030f01d0080014006600401c28000003c0301c10702e50080d02d03502103a81001c0c1c40b2188001380290b088400d42c2d8001c0c81018a04401c003414400801c1ca42900060b06045c03a00021075603113005c84c00f418654105048600000c401d002241e0560074107102000711400c00c1d0072803074001c0150982203d01c94080a0006644450541c200800ea078000349030868251030181c21311103 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 391958974 1250 391957724 391957739
    0x609010c0f020a12020406051219030908100b09070215010504090f060c0203121621150801050910051302090402030f070e0402040e060709050909010f05040606030314040b0708090406 80
    0xf102c0e034416121515444158811442c0900c1004050b0104490f2410b10503182ca80090b0385a242d2001c0d84a201540c1d142042818002e5940200600042007103802c4a070181460390301801c03038150b0040c000c40b484400308510703600219183c40095030f08078045426170b28200c108800b409482105880411080301c07c1004102d40d40645040c40c0038035001580d84807491100c02402041c001d040c500302c140b50b4500c0b070481e96807021080300d000b01541300c0500e00c41d2041c040c02d80105240740001c0c02c90b25030900c000640590641105114039102e50544d1100d284040100e0240c2e80122142514203040940b442e0061a2031070074590001e0014089039004440c2c1060039107498a40e0f0801c1c8110f000d402d04010444c500381c0201822580c0700000b070802c41c24604c1001d4512200c40c080e00e481078044000080401d8401d500c50700d42401440810f00c0a41440d081003401807016010a80000700e004031500403410b11a02100c00702d84852041c44c1c0703040f01d9a10b403030742c0035048264942c6c0d02c0b940701d000024491 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 391960224 1250 391958974 391958989
    0xa0f020f04030c0e0c070b0601050703030212161101020a020c040f06050a080a170a051204060b1e03060903040509150109030204020304111906200a050a05071505090609010c0f02 78
    0x21845081021505400c04c002e03c22040310041c40700c14068000c000e41c0340040da040c1251900000301b8241103456010301c3c50300364040e000b040c07241d0b1080f00c207007820003056140010b00ca0200e44603036100c11a01ea041036401038241e2142c4068000544e102503140f04850038190b0120640401035280000c107151910001a10040160301c005040e900c521511010f0080c000b01c0110000716103800e0500e1301c00340145c05881806001841c20160628400180c144006a000340000c1c600042421815400c49800101000712040781d1501900c18000000e8401c140001150b042d20b00003000c49105035a2071020754101440103221a0401100800020040e05c9a0026502a0307120314030381045000d03900103000c2403414280c22244441c02c030840411030140c10000001c4d0307420451200504641200b2401842c08dc2403c0d4010004d120703405a07001406400b141840031303501d400c0d0f001840541c111004844a00846910550101c1d08220304422980100b100ca071080b40708040307158189600d5000038918 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 391961474 1250 391960224 391960229
    0x1614251e141006120204020a14031810090b060d05070f1202040c08010e0c07050f0f0c0a0f03020a12060f0609021903020304080d02130315200a02060a0f020f04 70
    0x424007100c1103000410705208005080790014402c1010625012401c0c201e15000903019000355800100d4404241c80344020144102d0b0030000399035242810103001c1010040425062100d0081b515480e0b9090558002c000810f030300720b14246065259801004a10010342c00211124803c3c1040010380510180c0218010140120070f4400001c0c60300610080d00c55000c90f4104200038400107101403030440000b03a030484080c000035900d0780700c035103072482c6030030500401103d06208000000071043c50029041c00c445c40d0076110110101c1e50f038100c08003808944c0c00021b41c49042d407003040c03050014040340203526034007078034021402010800d210300c1122429007208400c0c0e90005504092000c010340c440c1c0e031180b41c0f85800c62452500c4d89800b00d007809902c018000135500001e0b2f550301c5501c41c10748034001e1a0400900c02100e600b0000c4d910091511444403102400f40504030841032240c2d0041c0c0d455100030350041c0c11141c2d1180c115400402002620000e299828407e840b410380580024102 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 391962724 1250 391961474 391961483
    0xd110c0a03030902010e0904050619020409050f0103021809030a05032508090f0d020604020f01020f0706050c070b0306130e12070606031a0903040e1005091614251e 72
    0x304080f460000601250142460701d000f482d40400b4003000901c0040c0e17480c2c0c00f0000b04072003046100034080090180c8504d0340045089410181804088880d042045040f64405c40d1300c0a5120000d008001c103c05007100c0040064009101c2c001c1000d00074002035500850340318900c011000c0c4c0422004514600035040000160300e4002c00a008000300580c1020071144001007100701a140b02c004c0da201c000400080c045c0d007000f0036100c4036900801c02c081c1c04504160030303103502035140d5500425680003041049400c0c459040005264144502124054000a4034500700c04032014440809051600040391251081c043d4120241e04003401034400e00d4882e020116840780340d0b0030200304210312014510901d025040c140010804008202d42c01c503a11404180503e40e207803803003a0741c1d04465501c032a070448031240410002002c102c6044500710515110a400c91010301480d0005028071f05040300303100ca0f1400e01041400f00c050441c081e2500c140240c1111711504014000140f000c8001100d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 391963974 1250 391962724 391962731
    0x150b030a02150a050417100e0c1c2d0302011104030218041407120213050708010312030b03190311010c2a080c01020421020901140103020904091b06050f0d110c0a0303 73
    0x244e0b65402030180d41d003440e2160008001c241da4010000300d490030001c02262700300880c4034941040bc24408803950302c51040302d22807007041c020b1110810305616541412001940781003624450301d884c01c010785050b0380e005011003905d284038104103013000c0e4001d4410f80d200c0c5400c5074030340c3c55050200040005450413149181c0c0410352407050010030111804484215802e22081055241c1e01c0a4000d04407034100500310323540a107404003175004201d5000c0c140d03010300480341d25003850721820100c0d992a0384281e54040a020b040c8070110700300ea0120b00d06400040b0050501050003550559001d202e1340084a220828981680c070410700758444841003009035000300f810004030201c00d4900100340051350450754103039865400102d0b40b50050054000384020790b007a20506074400e038103403030100e5800760040012030054101030004803103058030020006904200416110721075410340f01660101e90019081444070180c09014015102c1034a12880d0b0501103043c40010400030319000c3d80c000c1d20b000 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 391965224 1250 391963974 391963993
    0x3100c09180603050c011412011508090f0c040f020f07060e0f0a0f02090711060a050405060a021c02031e04150f0902030604032307150b030a02150a050417 68
    0x10868a8100d51440c420700d15103481040825000310380080c943d0f4013403810780044c0350202414640781c0143d0940c04096601d100000c00c0449041c01c041504540300e48420040c0d58818110941d01d03095000c2d000d0498202c04e441c140d085c200754200100d1a14a81c03005802c050603a840d00c40a0741141c202a0341140d01c034030a1b08402001845a2460b4080000141c0842c1c41c5588800d0154842550000e0241c0c948400203040705104000d20030b88240d04c0e0056403202d042614a1901621090f2016076040c003d11002c03801c040c00344d2086440e00f4103e01104440241070116403002500020444000c120202500c401c2c1c6241407094144a01d101d8624000280c912102e00310480e000342d400400058030301070500380542e400280a0358815450f140050380e10825030144501c5c0b0300361350407c05a03010041042002c01c00c4540345140104a040c4e02040400031840416a842d522508069088892070909a2034001200004c1c50440481e0410307601c0c25594066465800e115201e01750066081803800c0c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 391966474 1250 391965224 391965239
    0xd2f040609060819060908160309050324220f050f010b0112151e0501080f1e1305030a030f15030804090b01030b04020a02010b030f01050f0a0b03100c09 67
    0x3500c010344003180301001614141914241e64001e000c01809000c0811241c8208120303894001e440c113680d00c080415100c1243e242114250b032005070003200455a0083c01255908002811480c140d0250580b0004104450000c5034000409403115985545620301028001c803c0303982854080d100d20301d00281e00046040c0782d41001008030910303540341d040114884503680e11035a25025954080000100c1d41e40c00b48040745600d90b0380d0b00c114081d464241a4500000071111000111030081e2501140c0f5501e0320011080c040c0215080c150200880070342054005039451815404565450112070500c4e40303031600c0f4a503420011030355001a0305c407003403014541814068041070341c628600c5024906d046503140700083c003880c00b81102d09941c0c2c06036002140c4c8a504981455500980115a0341048001c024064082000707014000c0c4a034206000e400801441003910401000c5446800c503141c6c80c80e8040948603640c0100e0f4144031b4184203841001a46c4601009888036031250b440151420700c5 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 391967724 1250 391966474 391966481
    0xc1406010803120c040e011a120a0e010f020306060a260f040c0801021608090a03080d0603020f01051201032006120a0e03040506070213140903041404020412020d2f04 73
    0x241c4400304d9000e04c41000420322240003141502d243d00c50f00200580101c94103004d070700400c4120f16a001584080c0503455400c0e0380305809020807400280035a00c200c1d06004243d2006540e1503800a104000031459113110382c00290b0b40080c0160744144014602080e00d6a00b2010f66001030280310100c148020051061001402458110020b60800d01c2506440e841c0c00740345103000d000030300d001818824540d9003600200c042c3d0740c04038000d602c3c0c004450402c0e00501071800101e018003410904000340d5800350080c2e60070702c0c6586102c2c8405030f09554440342d0605119000c5180c41c0c20240711403201d07070340b080c01403c1d414038161203d14042c90156000c509803404080c1e05041074004203c00d2101d500c0f044100c84889030161160101c101c240351040c802400d6020b0100b41750340c0c0580510410040100051007214800600b0752041e1007420200b10480c071031131040030403d40540c110240141001509030700f50078010302c81c071240141d040d030484409440c02e180b815441c0081e0400e0b604185040d01c03 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 391968974 1250 391967724 391967731
    0x40b120a080310060c050316080c0106030501020903060606040f091104030204050403080603061501050a23040b04030c0905060f0f01020f010c0918270602040b0d0c032306010c140601080312 83
    0x107040440340c0030a4450036100d1181150888480708030800f01414030921270210303404030511400130098a643d90038103070300075044402031600c030f8010ba5010070060301e0310200f904c00ba9040861700480d11890100b4050040100e0440c11072412024400007001da034903407140d2841503000c2d8458070700304c1c60460201410b0000c024030400179141d42181d003800c035980c008243c8a41030b1290a000c0d603000814030003c0c200381c000c44440040d92070002408608001c1003805041241d00ca90000340c415030326885042c003030f117400300c0b4029007020041c00c00b5401860b210480c07010000040c0141c8544020440450342540c03140085040480c40260003008203084ca5803114145c040714000400130070349071080c414070145020801114031801702c07690b02c0920a080e0b0480e40100340c0c404a540d0b0f81c410f420562409030922411800c00302b03160800b000100c107a41ca2009100f1180e10180f0030305e9640741c000546204080d00415285401100044554a50100030090190840034011500c800c54286035010610008 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 391970224 1250 391968974 391968977
    0x70305040e07080f13020a2105071a0a0305060f0a0806090d02161509090c0f08090a0525120b0a230103240f0b0a05040b0f040b120a08031006 62
    0x4401c04c0b241c036a24821064000c5a5030740c20b401d101e42c0c18000200b880000380c000210903580750072210616005039625202c0d440c4108242c5403401d80c2e13100b0f480301000c59481d41209080b400c00c0301d40c00741071180d0f00c4240d0000c0000c1002449000c240c0129400f880c4980100125078411801e100c1e503081c0c2042500725a0040b840203010181072190305032a600321902c50000501040600032101a000c3d2038214050000d20004010099891000420240d0a40441c50114001703078045110480e020520b00b03406074002004018958000300300d919501c0c1b0545c0752040741903107014085007412141c404400c42900681e80100141400552201103500d400c0e5158a00c00343d000040e100798a0314000c1c6411a40c000b42810030b202e210030107030103040c080c0004400e2003030f103403098191000d6403d60041110700015103190101c607484c0c074144011111400381c1940d10204c04420000e49240a401041746407001038101c0915215a8205030310f80b0080070390403034840c0300c00b0040025070501e4250100c0101000d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 391971474 1250 391970224 391970237
    0xa0e010c1112130b1e03240a0302032a15090f010306030b130609020406060810090e0c04050c0c06090a060b040b0604050409140708030714280f08070305040e07 70
    0x101501076032001c40c42404c1440c880403403980c100502da070001c1c4442911400545a807031404140314032203801352900396040c50130284003600007400c0660180c1b0580b41d014000b411604900c40600444005a50313241507543c0f00d104801d0700c980c84030000010100c0f0301c0c003001600c698481c070422800340101045241054509a400c002080c4048a82c5800c41203d40b035124944425040200c041c2c0490400a50001d04000000500c0c035884140c10b4441da00104142008503120b0000a06071180821000040c0d8000c4500741041c3c6400d5221940000810381c0d0b141c40c2c40c03502c070545400c0000031610345182d0703009514580300780034060045885045080344d0070407110180300300041150085006643c0900c1d9a40381c00000c101c0d4511b1505024860441207540c0d0030342d9081069602d81c00480d0494402e52101c030744280350700002440000400700e00260034107000300d12403811401e270954003059070010342c540d40902c04205400c00401e4130502a54440b0703512403d040f0b40c40f080c0c141c0a0880d100700700f507 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 391972724 1250 391971474 391971487
    0xc060f1305090411061804020417010b090408041703120103080a12090803010b09130603050105011502010e06040b0601120204080a020109080c01020a03050f0d06080102121e0f0a0e010c1112 83
    0x503130b460350034036014040f60300c6034642080e090346c10004580d030003070250071a20000700800d070b4400c02c44468000c440c1110080c02030103d95000e000803507109440090100d40300348018001003c1c5404a4200c10084100f1241421464400130540350700070b0f4000d96420f0f1000501c8403a444c0e0120502c00744481c1c040d0305121084040d0b8982d03040344014800c9107540e0a001c40e000c0d0b1190b99034001244070041c589010700483c2c0d00ca0919500803e0288110030703244410410101609006010748149120010080d003403d940300c0c4c50302c0c01500c00c010550390401c640740803020802070340c0c2d102074409064500000d000503a80c0d03100140091405411401e207e9014a900e101141e1703002a80062859051819030740701c80440c01b070310605d8001d12080601c01c601380800031407040015400380100310f074400840034540d1131703071400300035600b8a55400904c0d0743c82c90304c006604c2c0e4201c03411550300b0480440300060f214255040071400c5a103401c4d19400083c1d036030084100006030401c48240f040c041259031519001 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 391973974 1250 391972724 391972733
    0x60f0f0b120c07080c0d02061302181b04120b0f09190809030a06151505030f07121a040510080a06090c0806010f0f061b0209090c060f13050904 63
    0xe0704403074440222189000a084100d9041640c4107198012941038580400d5500140c45035010b00c00c94006200d003030300144510303003004980e801e1190042c004d407102500001400f100101e000309040300509181900c1aa200c0702040200002c10310b00880b903501d88503515040316420001f42c4440e003c0280401400032140001c29503500304115044034000c60503091078101a00d0060785040360b498061031408500b03210b640d411042d52031246000b503a02150f1030300380b22800301e4101010100000c205000043c00030070a80b260a41105c2c450034071038a07030303e28211204181c40c5400d12550011a15141c501c0c0c090529006080e08003035011500c0204908240f181d0390351b10044403000d04655204e04441060000005140024040d941e06032000c0b0340e142c4450f1060705115101d0072003a500300400004506104030700d4060303440000c0c00748125040140d020000c0d0300501a00e54000d41c016402203103500c0c0d54000082082007107020302c258a03000c2c02d601040707201003140d010703034000d070024000c020028 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 391975224 1250 391973974 391973977
    0x6010503070c050a050d020d030e1204060f1e05091c0201080c070309030503181003050405030d09050c0907020607020c03060108031b1006140a120b061201020c10060f0f0b 75
    0x15078030310300100501640c2c108640b821500e503401524078015020a55202540854144040203081d2024000d41040b201066503c0306d0300106000102002c2c0300520545114584522042d1120700d403126003406120388507041d5001c008030b401c0225200007403060050514820400803400b01d144061201007458001904caa64000c140c41d081c1c100000d4414105406240390401864100003102e40391401c440042d1400740341840024400c0b00c2c1c5443d00c6007524464020300b881998002d024600781000c03052000054440058103c1d280e0107840740841d416240d0307000c0a407107078500380d0003451541001140a810400480c8076070380640c1000005019100c0300204a0b240c0900d83c072820304040f4400d40740d140c24400c00200c5183d503242010000281c01011440c84261138100300c40c0f54501070f0752040c0c070059120a0001c0100301b2001240054120b14080c02610046030503000054508050200c00c107040c901e149001840c3e0380d9a8140c1888050594038942c00600b034000301c440f00031800c011085405 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 391976474 1250 391975224 391975231
    0x6131503030306060c120e01050d05130b24130225020906040c05040b03060a0e09030304061a130b06041a070c052d01020a0c0602030318010b0d0204050606130f14040506010503 77
    0x140840c7c0801d00d4202d034400c80884e40d018040c07070000c100d076003881180d07445040610442a10f2282c0014040f6103840e0400361010351000c1c03088104002100c1c0d00c0140120130341440000f0f486c0036070900c003041c4070740c00d2803510031000c00c0f8611001c980602e42d44100005c43c5409007200703000d245895480e2241982043c04c03502954031722100c554403a030340c1d08001410004c007a08005880c40c84201480311825000001e940540e00c5600244290700c1c010840c0240c9402d0a4000eaa000402e181d84050414555210904a500c05003e81e86403d44070454012684031110040b00042000104031041c0300315882100d02400301291034010614000402c9a031031000d5001d1840070031452000855160700800100300b40c5503000d0b03900e00c569a51110f01035100d800407584413400c800880f80c500f00015061080b11024640142800c1c05000b464090000a0200401660300980300300988050680c000c00344000414451040413640c0f414449007001c400003054500b40268280002d002c2c5580c0c104080d60351 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 391977724 1250 391976474 391976477
    0x609030201031503120903050111071a040303090602220b09220b0409060207030201051b0a0c0501020c03070f050d0305190b31181a06131503030306060c12 68
    0x140e42d0800f42d2001010760300f9a000908072403c62108007040d940010030001201e00030360007003080c21022860400284a0007100500e00c4c6a444488034102c01a400203940041c040d00d0300007021150390b601d81003264051b100c049204510140e006968400001040303000d0840b64a00c0b605064050010522110309524511410b00092003a5925000181d00048520710010000d005150711810060000d6201200680055081c10300081415001191311450203501090103450221210800c90358540030307041c00c4403155000c001c82c008100080000d05445409401c0035100701e0000d10300300b80743c0103041c000c0304140350904040180181c404c28044c0300a000301000841c60200b0a800140c2440c801641c16810340740c142c0c1c540d0b4050007040b03030b81e01481c1000c807000c000b02c04281c00c450401d030329503d900030941900a13030015040c0c2e45400c025078000002800d031440315814180c04e2401d8503080000e013100580509810414103500d8003414000b0809400c04620151150f1103c803003500c684082d160 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 391978974 1250 391977724 391977731
    0x708120a0e060d05040308010e0c07050604021302041e0603230712090204021c0501080c0306061e10210e03090d03050409060803030108070801110a1803060912030c0504060903020103 80
    0x80c80c80e11020121001215103003c100894541440c002c3c105210a0051101081d0344000040110a0600480300b1a0350410001c200954a90b0300b080082c0300340d0504098026001c0c00005003014220300b204092071241015501c1c0c090912200804480301007120580400d00c01403d000c0f450b010305042c0b07400044a16003c00d2881548010318060f126019009401c584006070054244148844031280788141c007a062040ea40d80365030550362402c200014941c103400800101d2940c0c41d050310121031403040c5040d00c8460700100301c0003600041503004140c011070019003503001c64031100040c0044080e80c4c080d04200100384580c6040d503038040e03100940e000704c02c0c00d41e00c60245070040007920000d02038200284555038840c03104640304d030000c0c0b1a0b4122442000e50100f0221418061501003141010407141410204603044542c0c500791040c8408034512100088040b401601071542124040c43c2d408501812420004084504151040040180502050081680c080c103000d00312502481c010 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 391980224 1250 391978974 391978997
    0x60c0f051c0302310905060f040207030c0b0f0c040902030a0608070f03050f03040b0f0a09080604080703020c010801030305042d090b0102190f1401090c14030708120a 73
    0x1186030000303088407524211001e40c00c0d1641107038941c005014940744148030030380c0c100081d030f80107081407180b142204214120320000d010a540039802075510a000a01c1c0114503004003010904903401040107034009503c0030308400600003104540da810402c0000343d408035141005c00200103014500510704003e40000120b4485205c6401000c007030107090056030901c954820300041920428401181d1a000380c81215012041c00b1040d10100c40b80c884080d481d00d0303010103004100794071454145060100541001c100a541001003078440da1190300042d507911264100a0310f4101600380840c1002118001800080d51280a49080b9500c1c92031001444000021000c12649681d10382c5070304d445010700025200105400c090800402a000d441d28400a482400c2c100300b03049402808a11980b222800040e51203208030320240c02040002502c0019956010b50480e101da1107490700b400d50060b8905c982c40c044c40401c0040c030500300244104007003074404a255018002401c41403103c02c00c42d6 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 391981474 1250 391980224 391980233
    0xc030a0504050a0215031f08060703020a0c08121012030e01180b22230f0a0504091202061e04060509070f060f030b0d02030a0b0709091401090e0106060c0f 68
    0x401110f10b500400202e44055101c988980c10703002121410780c94550140c40060b00d0300309040e0746c01500d0f052009803405035664202540658095800c44040000400850020400c414003400980040480342d034924102840c4030810409903400a0342f041e240c904503880080e411201c1c03021504020b00b4441c03c02c1e00300600e02c0018070015403020406000004500c10702009081001601c504520300c0340c480c054139050389010074007408680d41d035107800e2802e04800601e0b141210400c1a00001c0c06007540c1c503100c1c404902038039581201141c0c00c0d50f80212241070103806016160317106401d1001480c0c80080d001c40b81c6040f150103040541a150f4500c0868070340e81045c046100502500c846500003180d65400003405001440380000000b40741c16443c0c00145041d11040c000c1e190002d001b46145010f580322800d40d9100a48003c040c007a06c1d00001501207114003641d2541004580e42d8500c641c5083d0420b82510300024007005980d02d804000d226464124600021040d0000550f160822444c41d0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 391982724 1250 391981474 391981483
    0x1c0201121b02010207050d030b030322090f140105041e05190915050106180605091212091302040302220b04020324150313030507080a020303011d0c030a050405 70
    0x90001d1654010300d010803625805400500707105220380c040b1118502c924600714100c039008028294140c00c10401100c5050800904009540d01c00a204006c04e64030001c2804442a401100009075100c00e44100f07006040c80925005000985080c01f0070b1025030254503140f1039012070242620769032000b281403000a054401128883c221040160b1042d174208000c1c0000d0825852802c0c44c00e10001041d043e209051900c903850310149001071550030f19005844075044003007129040724103c2d5208a107282c0c00c0103c0106429100080c80da110712403018089032400201c884d01565004110400040c0c84111007405aa40c07485c041ea106881d0801c0b081c0043c00d0301d40300065100d80080b05215405c00091a80503054603191501669002c10b04144a05040d00041043c950710b010b1000401074a0b11012300140c6500c20f19003280341030f40541d44e469143d00040c1800005038404030050084601c04020078003105d10041c007400b09032400341c00038242c9110060000070455110800720342004010003 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 391983974 1250 391982724 391982741
    0x14010b0a0e0303040b03091207170a11060f010807080307020a121e05010f051e01060815150315030a0b04242306040603021e0303130b07020f1c020112 66
    0x14190fa5403640c0e03407144190980c000f0360301110305001e90819801e85600074030072030b0882684194641200000080b20f402e281d0054080402400381d00071b00b03d180d03154113128652084d030303821464a1981d410550340a160007101e4000400c90b61042082c00c0140e0340742c43e044011229210380030303e40c00e1054985410403c2c01c048074800882c0b44100004204a0706400020401140380801c200c641e54118445046502040d40345914501420050021610071441d030341d8400d0407560703540619698207011400394901c100c21051840030100c280004844603040600850100300c0080c80a03402e03d4075501001c460141c070042094442c008031035410384c0144021111080c1c000c1e81000610143c0c4001ca6002c01d1642d011a606058980000e485140500c549020b0f2034003d028080d20230005a05422a50600c80941754148802e0003440300702ca140a03075550262062141d083e0b1038505038418004c40a24020155100b1070451402a217090344484070404c0d8141c0900e003111042c841c1c0c0f20b48000030904d02 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 391985224 1250 391983974 391983979
    0x9060703031103130b0705040617040201020f15040b090609030409022802010e010b01090807061202121608090102040e0a0218030f010c1202190f0504050d0f02031014010b0a0e 77
    0x402002001364403954001091401103440342c45560b2040c204549034403840c01040082804086802d24000540842d1a070083c4103004480c1d4039000c0440c02c0d4500b21410b8611013240080100b08010802c0c070016154020003032100525042c00c0c0030b4103590700c0f40034900a008100d54003140c801341c00409801444d1503128440e034a00e20503445450000c0c080e00070034064210a40c205003074204070b548100c006404907488000070700340311350400030b003228404a541d445084043c0c09001000501805403820b6010f00d0340021408c42403001620040c00b010001061101c0c2a4410302c410405d415928218030741c0f050810a0050b40c0d401c01059042039140810b00e5070307400d440f503100f40640700041503002c545140c0c0e91740c560b02c1c0c085511001c41c00c2a0720440e4003086c402c98014000f411054003403540d4640519070340c2806814141c0b01c801107074800e180444203894581604800c0019400d0502c00c00ea5000c3d020707841400f6070f046558409000e0b032018440c5e03c0c03051300000b508444041c4100d0015a01d680c00 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 391986474 1250 391985224 391985227
    0x3090f0112150b0705010c0f050f0a02070b0301081507110a030e0118080c030c1f0f050d02030a050f0a0209030705010e03010f020d0207060b0910180f0903030c030f11090607030311 79
    0x41c3c04400c00141c1011008540c550320300010301d00610b019190303031584200c2a80d519407401c20024084030054202803005002d6200780391000c111079036001d015501900f031500c02448080c1c0100d041c1851804051b108100b4000c1e002c084207140e400110341403461540600b0030a40c4608040b0041b6440040d80743e504552048001c00494501404544a68110401c504440b8200c0c0e240e81004214080c0c550b281c03807080c010000302c0b15140d0041c40c072840842c0c81801c18a0904140000744010717030b44110350b4070000507a6501000503c02000c81c1854001d0014801103081925a07c04a5565070150194505020b852840c0781c01e00d40e02500403491607200c0000954072034400c8030141003c0c0d00308150868a0f20300704108100107080150280d4801ca00e5401e001988602c0d050b46400344042c14100c50340c0251b00c841442d00ea0785940d0180c99115442030783c1c0051104403000c002800c5640c1c0034045070b2924182031201c8000c11581d03095500841c011150951f6800580c80d0690081c4840401036020050 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 391987724 1250 391986474 391986479
    0x308030402011407050a031d03100b0d02150a020105072a020609030a0506010e01240c050a0209010803070314090a0311040b0a030b01031506180e0705191703090f011215 74
    0x40440c2561b2a18403c1d22403171031310441c485070030139024041040160194030100e1141d1000506c0d41019140341d030041c000600484298000c940b03180007039084c454182e4030026903144280c1e4240f00d40747c1e022415141c00384c11102d00495001c18002c50101644100c01000c1e191425980c90000311041440014101c5045035614580940c90f0301c0c0c248141d03195600c81c03000019506018a101c00020740030300b221038050030f01482007651180d4017211309076094405c1c145841d00680b1448034182c003806484009503122105482c00a01505c6600b0700c0c8050341a0601c074001e21500d441c24104c1c140d0340d1154201ca007558419000c40c0090210f01c4c05640c2c441a458400030601c00c1440140d4140c0340141800c805030f00c0f000c850a01035800901c5103040d083c07400d4403c01c031312071055030040c030704070300f8210503200c002d60b590000070404860320071000480141e62004103c040050032040d040000010017450074030b030720035001070000e000c08110103040c828402072219065009034025202c03e0040800c0748000c58 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 391988974 1250 391987724 391987733
    0x1b0303060e1303090b12011205070302030a20031513020d06050c2101030b040807140106080313080105090604020f06040e0702010b13090213020d060f08010c02070617010308030402011407 82
    0x10100401e4001c44c070040400302c2c000c0c8803081111550880b40c102e6400344d134078041c581c04240101c00020340b40c9000d02840440107a0341400090300131400347c14030510820b601c4e880c5451203114490801d1203035128240d401031000c8070001c032503803048801d80d101201641c03500106000c123075082401407034540740008100100794039001500d626407103402000740c82d000314818504080000e00000e400f850901c0c000034009520507008103005407040211500ea88140309060b82507400682115241703800118400015522005840009280031390081c445d074209080c4941c3c42e10070140010b40240e44e41204000c0390707111003080300d00a05450010303521628014034000d0080c60074500451003210800d0740e00182d5540340c01a00e081640061035a85804d4032005040e0003035011540d107080590f01d42c84006813092110f80c054006210760400481c2a86007218001d003003a081d0340000c414012100c0002c105848502d5032141502c0d400520103640303407103e00050340c0403500c101030070324140c800152000800 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 391990224 1250 391988974 391989001
    0x180b030108012418110a020114100308091011060f1510050d0f0f0c02250605160c030f060b03010e03031501050d0608030c0a0c0b03071b0303060e 64
    0xc6003144020042422204902036085032000d02180000d401810f050100f4003940295803141e044440300080c6550f01a08202400e8000700300000140c2d5442822009108805850551018160442c540024116600c4080700e004208400d0b010360316400d9003040590203002c0f00d5480c401c0090880700c0600d0201c600c00342001c41166441246800e0580341c44403400c000b00c0b10b200303200c00d9450380c50a1420620310340000f81007080302c02c04001c1d2030701603000c0d8540c00d07442030700b031000c4150380a0035802c1100441203188a011010411800c540d8040401c03903654880c01b0384424005e68207450b50886014104000c2032400d42c1c002030035042104154030108052a4001082408150f00030302000c5114a141070310ba000c1156107251100b00240000c071698801c0e4000c200702d52060000056042d00c3e205440c0c55038201681c080a0f9920600318802031040e8421100024142c0342505c518614026100030318410661000c001c0900f01c0012020416009801940c007501607641d0f40d20395840c000303d800b2000d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 391991474 1250 391990224 391990229
    0x804080a05100614010903060207170d0902150c070b070f060203010902090f012f3c0a050c040507030b030607020c12060f040b0606190e010801060f0816180b0301 71
    0x342440c1600029401c40e0501c0850421300e0705844002c8404d1540d158080a940001c00896901720f00900200002c03104601500705406220000240087c8510600c03100005100d042000b0200520500f0110000007911809980807841419220403d515056824142402009201500210000c101c4e4030301d42d030207085112402c0b01d6903c0301c00c0d070300d90054801072000e44040800102d440000c026400300a03503002d0306115500b0848080050080a4007480c00901042c000e14044209801c040d541410303441d0714503250b80d40e0140c4100001a6949962849885101c0d4010754a5500003402c0074042da1243d03084a00140c1a00c80c82d2400a10007515001c001c1a040e21900c1c003803040c000c0707101000600500c030340c1503240d03101413585450f1034045442000510346039202e0800c0011441c008034483c07180e1010400c0781c0340d5000700b844d190000b4108001c16004442008070b20078400744019482030ba5560442849403602074403c2c1e150364115560340300320700b41c003c440581c41000204404010002c504 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 391992724 1250 391991474 391991503
    0x60e0f01090e0709150905040c030c080303090d080c07021008190605060d0905010e070e040209010e04080910030e032a0604200102010209090a050a0501051f03090804080a05 76
    0x22203a0300c80c81c881c42103840b44240c105456100c40418420310020b1751021039211000b02040007180c0d9101030070b0b415541c1c2200c04030340881228400b0010030640c01040070203420100059411450041e4009a80700c00c01401c501c10012060041542d20080c0307002c075195150043c00f4040a21311034000035101c01d00c02d031a900040440c40c1d5440088503085d108400945400070700b00c1c0d02d403054100006001c0c20b18041e05032110755807180140310001040004000411580c0e400018914141c010840140c01c1640144c00c2030000200304030006001c48103c0f82180000c95407900340d1401c06204a0041907541d0702212a4400000c80e23030001e0303c0e012003019802122072041c88555583c6039051b900d40c40e0503140100003403403003080742e050b6000414483c00d501e2018400103041070641000202c03142010344020717444d50b03070303840c103120800f4501d000307187c054001a18038054881c0007240b000400c41d1103285100030550344000c2c010030854090b04407401003590b101200c548850b1401c00300c0d101c6510034003d04 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 391993974 1250 391992724 391992751
    0x10081501020607090302060912060112030e09010b0403030810051210060f03030207060807170403030e0d0e150702030c040e0f1e0a1212090302070915050306010b1b01060e 75
    0x802984000ba03801d21500103596000501443d41d42400700c19001442150740c0100072076155030158204002c0e441c007d291140d003001c801000c80c1005403c00c1aa00e20403406210f04400520620071000215001c496051521700110340c0d81443d00e00b00d40d80c02d170300a140d102c900480884900c070310010310904202d5000008120007650b4040c0e010041105201c002c016801907002000018001c04185030710142c0f90909099242004480d2072941344211001c8011940d00d40d4804803800e0200318803c8000d00500f05141d009501500203201c3c44410359401a2a403800107410007113413001d00c0301203110200644140880c01130103e4803901e490704070b03000c8030552080c40b10040d521200711a20141c416084030142124000a444030f04d18928618035070018001030350004c9a9081c0d440c450488101d009034058a403540c00c20500c10251000380246400c0c0c160368140910441d0390202e034250454281d141755640d0fa2403031800d5400e800c03080100503960b079441d01d80001821100700c20400e205014148006 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 391995224 1250 391993974 391994011
    0x306010f0c0501093e060f0c0f03070c06020c010804120302221703030c07061d030a0306030c050d020a090207030201060e010905060f180609071206080705240f07060b1008 75
    0x4c0c03400640d4680c250205c003101a07000821400c21100601d51038440030b03403039850509520700f00c2c0e142c07038800c00446903568000507512082c08810b13070451010b42413500c041d240945507500000c0c10514043d00181940070512a61400719001ea8100c4c1c801c600d9904500c00d039040001c001c20700550035449190940c0b03455035811f400c1040d01108883c42150607450050900d40359850b22401028016030f10a881c4424000300007004100300040c000d05040d0b50344c0850a1801e52414420149682d40010f0048448a000e040144e549903814804d56418120058442c041c45c1000c84c058030322613120341e41c0c0301d400c90004500c485070764000030301c01d00781500d50a8624040e4020320035050400900309005407100004256907160181120f504120381d46410031010b83c2c0500b40d00202c400546c0b00704290740c030816007005103041612030105585110840d46400303203800c1c00180100e00c01d480700c1c1e030382c09500001c1e010700300078650780500e15154001d400c4490f0b250032460b010341103207015104d11187d600400c820 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 391996474 1250 391995224 391995293
    0x17010c020c0603010e061507061a0f010203040306090c050d05030a090e07080604021303120f020f060408030f07090305030d0b0478060b0306010f0c050109 68
    0x15250031500900304a1443e803030200d207402801700152a07154445450901600b86e88100d40240607a1401040e001032a021800c09080340007007280d03403443c081d00d200c03840038006030707008000d40d011660040004900041d02e8030307194080c65003075081a6440840e6445482c1404800000b600c00380c001615038809550311036490340c044000407554000020310000c0011034604064002c0c0c00c0014204001c89031454899403035101a10000301e401d800510313200000d0340110790400c00c0cac07180248440042c10950030aa00d035071301c15210090141c5001a0184d0101d80c5040c45506034030021a000700139640c96981407815000039111248420340b25a0500241c903003d61140b40034069248a104204060609080040b500441ca61120010060760b52003440b8115103a072282c03e00201012030000300324804424040550140304140c030f140b541e11700701007170100c4580502120340084003400d0030b04641081c0c0c45c0c101c81c90070715450b006119509001030348041020000380141200b00b4032512841d0107080c82c40 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 391997724 1250 391996474 391996483
    0x903160303140f030c16050709051006050f07020d0c030c03050a120203090a06080a0902061204051207030206011a041d06010e030c09040b04030c05070303110d0e01021e030408010617010c02 83
    0xf400601090030004940094112402004421000c584500700580d581d15211705040b5070350301504184d5250300070088051a104005000360509081042c20200422075006c51801070544c020700682d50007000d14203000d20b40b00c40c3c47c0110b91024510618a88134504030f610380d9480e00d01155043c5031320f0b0030a06490300100a9407220301019225441240ca1310b1001c940d09900940032200d4644d0300c2c0108030240c2c581030700820700307070010340c2d00f40700107051078070740703d440d03c5a1080c1c0d03080b00f080c0904c51b06000a5010440b141101c20244040040a0000007a0002841254410ba107112040302400d021003000d01d1466118200036210003508100340010f044d182c1c600c1405442e40940c0140009000940c00340801e038100303010349000540c404866031070070302c1c0c20055041503001c43c158000340007100c07004210f54105d8040750b2410410f00c60b000300001c1c0d643c05184900d43c0300380800e0b448520f25001c0c10001d80f030041031382c000207100c115079031000041c15145001c0380b942e0030350812041440e041d00005 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 391998974 1250 391997724 391997737
    0x3f050a0206070c050a15020c0d0201091703060d0b09120a0201090204050606091003020c011d06040b130b0402130902270c03220c0b0d0b0916091703090316030314 71
    0x8007a11740211075580c0c00f40620440300b001d4000d25803d10150745801010030600606100c260000611a6035a083c074064003d074182c507a031003580302001040041e40324840c0071116a40e1000034500e03580c9074003031428244000d10300e00500084c404580c0e446c1d03007541504030220b090300942d410802501d5140034000c051007140f004030f8204060008000c2541e200307038018003100c0142c000010703189000350010000300e5441401d52300f950f40f11405010900981110302c40d0000c002060b00c4800902580e5941060f1030002c00103032141501c50205d01040030990072007800c4950003032903c1c0b600d0000f24040d81c41034440c0d4007006c40100f064800564006a90005c40e03001790b950f0303401e400c40440103000c04c03807441306d440f0021a92035000a20009003c00e40c40c02403c41ca910f080004511400c810052000508004040d802218110041341940b142c1048001040c1c1c0c1d400f40158039030740251021135142d8440c00c07043e1600343c441c1c01200034a58011300c550b001a48e10958501d80681301d0704407602000c4c020030 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 392000224 1250 391998974 391998983
    0xf0313050910260c030604080406170405070b0a0e0a0b03180a0503041413050a0617011506141303080901020129010f0c06020d0504020f04093f050a0206070c 69
    0x2030380c14201000991080181c0000004115080210381300046414440195421508000f021a0078050b079a006882000342a40b0101c2c14a9240382c1611801e170758980328864000000c0c000514090481d201d403d6924a081e809010444070903603c6280306940d078011100c050320340380018002d06034a0404a07105441e6500080114145800c1694410705040c1f0b0307014190b40110500d054406141316801018800c1812900c00039501d80740280ba020304609590303c1203500e900d0100085609156043d0042c156403c600c1c1201019051450070b16240c0b080b4075403500c07440c1070040004104101440103040510080c0c2c000d0100d10542030500a005d0205800c0840080a080b0b0b000c00c41c0d44642d044a4510720b15160806c48030625441e035000b05e034445c1106221070b940f81c10401c410b500306000705005880d016541000b611020361035400000d1950f050320b4545050800103031403005070390001441401045421b9a0100c1508103014056500034414000503024110000320900d004040c4880403130b410 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 392001474 1250 392000224 392000249
    0x70501051602130e060406020903010b0604051011070b07060b0a050a03050601030f03180305060414163b071103040501211b0f09081c110f0313050910 66
    0x15801c110f2601490300940300455030350042c04403071403002c008403801540160401a40c5a0400c1c0c1854259140348503458010b100812042000d901d9417610b1084050380b6103059900c5400940d0701074105811a48078070442c42020a486080c0285076010302003003081211203603040303991901805126221440003600e190004001040410743e14042010214400e2070161100810714800040040460708103948a51060741000108058202010390380fa2050006211582d4003400351580381c3c00a000301c1540d503c401c03c807801d62000c0311030800e541410083c003070011105c5100c030210043c1001ca82d102c0019903401c620280d039201c040119019100107a603403014150074203007003820b0b407c01d108004410660340c0520220003a44580314401c003109607580ca91603690749480c0206181c40c103401015807600b151810f06a11a00a003500f080c3c0e0190381440d485440407081c049003800032040100d1414080000c4087c5551a0b424403042a206d04440181d03842d114000034114185c124006d481c0300c01c04 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 392002724 1250 392001474 392001517
    0x305010e010b1b0a02220f05040c051c02030d05090319051005250306080c0108130b06011106070201090210080403090303140d1b0f0f0e090a0b040203040f0507050105 73
    0x109911964080510794088511300e4a0660116020f001540650b590202c00c0c060380e01c0c0440c0c40e5024080c2c0d216507a003410304c000d040c203440d40800f81e9003604c2680c0c8107072a40070941c0390198844004045240d00101901e40309103001c50044d043d0b0740710a88107442800381c84801040c410241996145040d000303002402f41c1c01c00d0304510b50007030202604505080000c0344070581c4c00000001c51031003141e020358010400714030780a409454584a01e01c0b06041c026610b0030407000400904c500301c90581c104105005903161a00165000f0500d0707801c0000b640500c1040000f0701c1d0b01504491900e510903550050011942e2008456501c015500200000c00c0600104042449034425007041c0d62100c2c05a850500180020700450f181d1502c148200340340f03d800c0080807900300c071801700e00303448a0400800e059040c40009250407030482c80584211040300208071203000e142e02007900840c01400840d546d08003400d2801c000b40031035504441505c11000302140c207510502c00d880307111034401c003030414540 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 392003974 1250 392002724 392002747
    0x11060a0e15091020070c0906060306030f20060d0501050a090212060f01030b1810080d0c080a0c020405010611070602010c09060539190803070f0c150c0305010e010b 72
    0x186040280240c13801c0b4030903070103a501c19000400329180b103986040f40340d915040e0340100b5504640c3c03042c410b05107407032410030118007802d44882c541032740042c0401107c09000c000029084207642c00c0e0b600480081043e41c10804207a1149040e9201151410b8045544001c040160311420040c41c485201100200309603040c00714107407005000505001c03601840703d03800f05030a044100b0b100c0110702189001c0c0201d1042440019016001074005446000c1e0420000343c0341c3e244891005000070030000300c49603090b1041c203040c00c82c180c0c010028000e03035a40c0c5400401c40302807049107400740d0241e8440018105d005115500950311a40c454801d03080c80c15000b43c402e5044500c41c2c0030713040081445030b844d15000300014001c030305984011130658401c150300c90b031400301540d0f50000d015860844a002060040d01503d902c9502440d100e802d0024145003182c2081e020480245605202c0c005880c07501c9150b0011540580c03d80c1d020007103680c0e90f406c002082c00080c8940c1034903a40401a87c1e4444 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 392005224 1250 392003974 392003981
    0x1b1303060506120111121003020102070612020f030103030f0809060708150a03050304080607090b03010608060d080c0d0f030e010626071502010b010e030c01091511060a0e150910 78
    0x1c000d01c040f9501e14540d40c0360f400e442140d0403400b00090001800251006182d01c0c107a0450645521900850300350ba0000c0c0d13444106004907030a126503082d00e0400110b051b0102c0d0040c80d50084025142c2d65680b80180a030407444560301c003c41d2640300010703400c2c00000f81a070300c03459260348c9a6204c1e46138420748102100010013150341048140c600400442d60400c020700003000d84c40c0040080d8a407152000f850f00b89903401c402074040c1c0400040014503800f030320258202e18101c1d03116044003490f1a104100f03108130420468140145a03036541c1440d0007560b0460156015102440400200c442079800c1702c00360b0042c40042c01c820035900030b80d8038480494440031240381d03048038840707902c80e0001d064012b00d443d50000143c1d15102050901d5074860740c01d92100d04141d0041250300b80d403000181409116009080d00181642d40103114640710701d0544808481c00000e032100d034240241900060500049081054800e40f00c00084070082036039001e124610310400340881070059410a03015 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 392006474 1250 392005224 392005231
    0x4321008060102010209040509070510080c0a0e0a051f03050109150e0606040503060c070210110d0e03030f04090e0c01020622060b0901180c11280c030b1b13030605 72
    0x441d9806d01640b042d41d1180e100c0c0e42e000b05940e200614605190200300950000c07088102801c0203811003c1c07001ca10520300c199460b641da24207161500b500544c0214410314035a83c4181e90003200d41506001e8411000b038000450060345d0b8081c095682c1f10003480040d54503100a10095000440b01003110a20003c04581c0000c0024106403402e6a181c2c00070349002c0b000d807909420641c000845004500e00452404800c1130702c0c0c100703a81808802c1c10348644400ca1003e0b45820700c40108510450743d0340c207000b21481c520440340c0d074503215525150180c00400c0000420001441030030300c8006a03600010303009100d2001c00c0c45080750350580d102c0e104c030b0500d8101001c507011603c43d46400d40d6a942c04610501030202d0860b4214460380b0000d1000c00c3e80c00149100c0e041c401c107400741d0b0307a0012000c01c0c0c1d0180b001e442e201c0190b00341e4101d452104541e01e070400180821000d04008000c2000c0320304414000c00280c20300440340b0b0454008418548140c890014441911002c00c00c0042d80c15008141d2 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 392007724 1250 392006474 392006477
    0xb0f04060810030b1602190b0c0c013806040b16050a060504081207090b04050105070c080a050102190e060403020d020f1f1407080417070308043210080601 68
    0x1002c0d5581c1d98803d564607054038141d401110440c0d604600070350401000019406512140d520a081e5450312240a2801342c2580702080000035420105002501320444960a01502c0440544114007684001c469181008040305128451001900d814400d07541500d090f8100d01d490460340002c00086000f4a081c1114030f401000780d400c0c0443e007988121813080340540f0000b030b9100d40c10034114001000081c51201400102c401c24400c00011800351400d4407020700306156a103d50381458424080350ba40200c41903c1081c20303007003c00c103045d0094001503c0710300d03007207043e0007480000703813000d80650301240d0b0010002e000410252800100244500e070004e42900c0705661402d0124880e114828410001491107072070020306564824464045011810005401c0c200e055607040b589200f903110f0301c59a844d01c05501c28429005015078401190300c203030b40964880e42d5852441307080800c0362100b802501c0c004041c100030850742c04040100130008000c60020000200199035604d0301404c443d0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 392008974 1250 392007724 392007751
    0x207050a1a011404110d0e120304030f03110c0c0f0103150f0504050903032215050f0411060a08040b1b040e010807091a0409030e1e04110c10091e1a010b0f040608 71
    0x107940d03141d128011400385000b541e6464330b0118824000d01070391004c0f140003203042c108100325600100d0215250384021310448814460180c1c10380100d01910421181c81014020703003400007000103410400303404a910659062020765210500e0179100d000c100c034210f0821078200b5910b01e040e04080d002c2d1121900c02e8003221142c0c046005400d0445508407803126444401005210503c040b0b0310084081c982c044605c10310380140654024015100035000a100d4588880454902c10905544504404140c511551910741da00c502040c0c8030420310804105000ba01c20100b624681030085421b107020818280e10f038001e001043c40010003500505a040040074603030826680e48240300a1003888407504c2ca106e10340041803c001c1250501c0c54640e4911104001ca0303d0b1011020484424000d40346600040159060070038074041c4103c0d10030181a038100c803001408008405400c030214400000b04d0900d140c0e214602c030221403003a00d10807000600b06010030040c2c941318000c415800011000324a = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 392010224 1250 392008974 392008993
    0x323070e0903030403030f0528180803041e2102070503070f1404020406090e04030915080106020d0c020603011404020f0406033603030207050a1a011404110d0e 70
    0x90310001081e98101800e0b003000051000f816410f014040c0b81108910b0200200d0410301c000305484a00c0b0500030703c20f4601041c030303030f0307142c03511940640a11a140d40d081e90304801d00d403510304516801260200d884280744000710140f016202c0c420084a035000342000c0c0c03800072a085206c0e00048854080d0114800e141000c02c075620305001003402005c48008265000341001c440d101c0ca1344a2890440c09184144020420705500982c03441c120782da510182d403a03d846d142000c5031403100f640c00c00300c1d030341d414054024105540984140e04880c82e40d802d5400b021203ca0040710074100181000e136000b5800e000511101d410041c0c1d094850360024001803501c111034104c4031903504594013043c0401d0b84d40b61f1034500300740c0c1495404102564204d80c03034100c251503010013014054501c0d010707042640c04540c4070100b0004001c2500300d1604921031000d4004540228400e41c4000d0140703001407052899402c8190070a0300440c83c000c001888508d09020f89450080014114900c02501611030301c40704 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 392011474 1250 392010224 392010239
    0x1e0714090406030506090106090b13020c03040306050c0403150c02060402041802090103150c0908030403060c0c06021207030c0e030303220c09020a09050a0302061e0c011d0c040501032307 82
    0x1d1000031032080020386260f146c0030880d20308446199000540490a200800b0f81e150307110026030b0300c0c400350b00038010307100c004022600d440c0d4025030300000d2202c4e280100380000d00da82e0901400c1242d1244409801c0c1203c40d103c441c2c151a6048000d00c05079000f00013290040c40c180d00301500302503085045650103041500012400c0d5400e91096994000114010426664270301401c1c00e01034a9007000c41c0224540f0300304035a2481070780f2001d001d5680e90212038030f08038441d04030800b91a4001c1015500d500c80c081c036100c5126011f481e8100880d00c1e02080840307007070080b40c401420007070040142d402c507a00d07990b20341c0b01c0000d90036400c0426131000c6586c4001800000900d4084d0502c01c000684a445003000644ac80120380c0080e48900c0700a0410030060355132000300d843d55035198545144600c0594001085e13405841801a080c0d420b00381c0c0140308100b0035090780c120a038450100e440d02040303e801c0c40110380081c0806001100c1d9801101d41c2c0c8001c1140c0b0540c0411440c044951441d66050f5 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 392012724 1250 392011474 392011481
    0xf170406030b040506040e0709090305040b0a210c050414030f01090b01030605010503070e070e010e0307080a031710030f0809060a08180619090f0f0b0403081e07140904 74
    0x221010981e1501400c0581c2054404c06500107030642e0100300134451010400d960b041c01d07200d802c0c140780d1288041401c0510880c161801001d02c2007200b0384500c0040720103007104040070403503d540319011226507025080c600600300306800360340700c0514180c18040c40d40e4050010a40721354051207401814810200300740b0488050a010356007402040d415440c102d810740340c040e0311240c0310b40d0006009100071604c0e080c0c5c440d04640141010386d44c4805150059500411081074158140a80e0740005550140801d1240340f0031311960700c1000003021820000c9400c03101b6a5968141e0300850f00c284005122040000754041c0101c4507107050544200c00502568007040d034100008a04606001e10154a50303d100183c0011a01501c114503140b81e041220a4507201050980c5885014039070034070a01101c840e0700c494000c4540d40d080c413820308001c028140142d074103d0015103064002038921080854910700c088055411107040e4442d00c40448041e1181d4410100b401001c1200c26115030701d620 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 392013974 1250 392012724 392012729
    0x6050f090a150c020319021008130b10060e0604080d050a02031c02040617090604031d040203010e0709050a1d06040626010b010314010b030c042d05010e01020a0f1704 73
    0x907100d000c031140f04d01c145401c222015082040c00a4501428001a80c409005007000040d0f4a40300031240d0301e0700304070800f0030385865024016840d044240004070303038410b0103501034030081c0d151028219824814803039140300394404e1541541040081501c5103200b000200609a10351040300c1c24a65803510f50b070320420403002401e40080d030000d800c20549402215218182c1d510030000d91301803030507141e03803510344000500090800000c25841410940c1447c0c0c80c0c24040c3c4042e00c00c540b65a192602c201840b201a2000400f08103401d900195510700752490400f910302422a40d2041c2003001041e4106240140100b9445030329104040b440d068001d1043c1c2c1e05d81e440411000e1b02c440100011421134003c1c205040c105070070405070500c0100a954002d044403000c00685030780e03544d2505030917014003842d0040340b02007440302c021480c04140c1c3e4001886041e91401c80407a80307680c482c015a203486c0d41103400e40c05a00101c083c00301190107000c11300c103581d0058000703207810700305a111042c217584540c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 392015224 1250 392013974 392013977
    0x51204080c1915060509190f0e07050301060f030c090b01200607080105040b0a0e04170304030801140a031703040c0305030d1e06050306160e0405040b04140706050f090a15 75
    0x104006000c1c072600d420640c50101c89420204961802c01000c5200000003d01e1300307110b40c14844521110350307c10ba0141500c080c16010030080c0342902803500d03840e41c0c43c0f8071400d0711960800c0c00c0030803000f401207007000440e0342c4000c16000d5280f80c004a0b501604100074501d050010050494015030110500e6819440d081c07005000b907403900304d0025040310410382001e40038902e4800600042c2d10342c5850311041c1c1d03000120f03a0070b40da9500d1900c01d040b0f28000400d4018036102205100415800c8280c5506884010010000c1d40d0949010f206001080c2e21010740104101d45001e80190204001150880e00440014030f4180c3c4a4039410b01c4c41d404454004a038036550100640b900d6100c079041450114080380c02c0c0215071030280001e40c2c410307001d000364002c40c540c56021046240540304201e03030701d200a00180540d29084c1008903950f00c0403502601c000c0b00c00703075403d801c074107001c5840402e503521516694208003000740d030301c119901f14942d5a9005031106002040c01aa01007401500c805079 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 392016474 1250 392015224 392015263
    0xc11090c22051c020f0604090506120c06030106030b01020c030d18090b030c060318012a020a0b0f090a050f06010f1508061c060c02160501020d051204080c 68
    0xa840000c5020110311940d000c4000c040e090069030744070b0941c10f012001010015880f50858000600c29441c082c00c4030394000c0c000180002e40811541180b485010100c480c0345210702d40c244003e45035441c00c50302d698072100800042c030486019a2101c07503188418411584151001c0020902d007030200400403004c00c00c0d00c0480080f0300c0c14001000302400b1180c00501c68000e001d0b000c139603074840031507229205040110003d40d02c10b0038400500c0703d00351000000c2c002d04000c181c0034030302c50024034250031028119140c3c20072114000202c4400752580000a071025035240e0000300c481a4000d0701c0304110740525003c44000c9441000030820407244400540120b514000c114242200365a01640094900120301e442a50300000c40784e81c05803007a50015841ca9000246081e030051080004000074031340a001c0743c401da8002001020303041034920a000e2181c03144010781e52840c2200d03440000500804c000c0004521760b0340e040da00301d0322400c405030802c840e031080541003c0c140c4e4012104000c0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 392017724 1250 392016474 392016487
    0x60804082a0d030b0913030819150e010603110316030504050f0708071d0919020a050402070836060c030408060108030705160b0304060b030f030d0b131404030c11090c 73
    0x814100c5190012599550136040750311940c7e0240000c08014605070381d80e01e48030583c404ea8000e5800c4941e55244075646024425210f080302c0000001c20301a15001915080301170040d0300034901100d008002c0703c90320440302d001100c0214050b00700184200c825008002d802c8180b810100b040300040c0a051000c2c1154900b03007040a908140900c5004850080010070300c503000300c011a11070a4800c1c1301d103103a210700010f400400c500628a50116400a10019040c1c09110488003d824010400700d60408844001d041104800b202c00c441c0d03158404610b5010046454020004c003e84c5c0c0c60b020542c3e06180d55040081c0c10309009901004181d04001450010048141f046c0e4040201c00039940702050f0410310725807102d00000b04020b1403941c1c0c03a194140296010000c10036185c14030011aa03451942c81c615a018101c0b000e0580d0240c9810720345601440c085003d204040307001f005a85019a07100d441c1260a40c0e54507100b030369842d82914440c0c14a0303d600100c5842628a40c84c0c060b500c81c07 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 392018974 1250 392017724 392017729
    0x2130b03010e150112050a0b0c0306130b010801051309020910080d0302161103030d0c020115050103114f0504050403020a02090c040806010f0f060804082a0d030b 71
    0x41031042c802c2026000321001c3c1e0001c80300300d044107040d5400d0a00c2e01c0800c8007607207425131900c6140000544502440820090118810401548141030a4480000000c0215001c005898004400a010966410041c0158100860b29803602d10b04c1c80c0300403580400c0c940102e40c5c0e400055071b00c01e0710541204028040c807c4101302880c10140300d450110300c1c03c0d41d4504540062040c80000030318580000c03040502c190b0b0b040068175100145c3c0c7c0c27420442201001c074007a00130700d4516810038224030090340006541d0700901c9440006c01d9200c02c0740380390028a540013894620102c1140c4544819101280102a007080781603243c00740310220030b41095881908900039203107e03808648110304020400002a074042206e401d0168151105181500c2c1e20180c4032280c0901d42007040288226400007855005c0141c10104655101008144007501d40100b141c2c69081104c000d40701c500d0401c008040c089022145180030b440b01e201241c2c0c0d01072407098460a00b4055258000020784a210900152 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 392020224 1250 392018974 392018981
    0x12020d0911150d0902210706080117031806040f0e0105130509030d050a020c01150e010b0c0714031603030503040b0907180f110703020f07050f0607080c0a02130b0301 73
    0x703802ca07441c94a50080d0b01070901144101030440f5025621500707650115124404004481ca00f070351741032102880351840056070746000d481620300152506c000080d102d000c0000c00b26644c2c006101540c90034200c6580d29504a0740b04140314ac00c04010480019461001038000000d010028103c010315454541002103424000031402407042c5040b080c07082e0200c1c00070465100d140304420105850b5a00c064000080c00748050354542542040b140d04000320303a44085006a81c2607004000070750f620f900382c4600f503001c0c0c03404004841c0d120707500510002905800c03074070504500804442d000741d8422a488403454440d0700c1100450004000c0c4001c015469400750b40c4940c100c8010000140303050f82e016480c100750501c00c45140c0ea2420000e0502429030050301948040400e81a80c2c2d4500b461700030764811031007040324a680250030b0f02188a2401303081644000303000500d4175081c00003588644c00030350b08c01111240c00b40f1270140030000507140c4220702c4e00b5580500b2000688107400009041c00d5 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 392021474 1250 392020224 392020253
    0x601090e060d020603180607020d0503060f010908010e010c030e010e1f0f020a0c05010c03050601050307030f060e0705091906020604120e130c1103120103110102070306021201060f0806180712020d09 87
    0x10364014ad2007040206078040b054a5210070115031030042c00c5004001130350044d025800ca01ca1035400d0142540c00344805412400205810f81d070104a0345401d0302c091407c03282824802e460b20340110341c0c100740031640c0103044c40c0311f000108000036810342c02e04050320803039000da454640412910381408007806020f1095481919240c1400e011900c3c0150000302144401450324050540c0c1d900441803441d001d6001c2c1c07000d0001e00d914140b050401d02c1e030227040c0c3d4119a402c103110f40380e005c00355051080032000f01002c882d12900206010340321595005084c142c440a0442003141c2038014100a90320000c481c0030400300080b00080d121901c00b001007803040c02c6c000c1d0100b680d0081140d240706411004e032150449800203489903c401c1c1a0b030040381044440e07400502158000b1130605c3d42004141d101904841c203e0302c5100391884449000c0c0c4001808a441d50b034021610540d5420581c0004250781d0b01202600e0043d0b1031103201d0301c101c4100c0e009100300300c07032055440ba000d000f08160401405e00d03 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 392022724 1250 392021474 392021477
    0x130f14040515011d03070e1b040b040e060d061503061b0c020402070204022a01060510020a0224040e182a03070b040905061005030601090e060d020603180607 69
    0x10500c0c2141c140c0300ca1800b40d020803030400203a2020b11144004440e91400309182c01800d50303540c1a0380b880c80800300b56040d40c41c3c108801c1c1c0416001040c000e80c02c200e90840b6001c02c9230ba810103140c840b00b80c00541d401042a81c0041d19100280002105403040005c04000c4070205107441d0b0640c2406000c0f1407520786c04c0580001000b030300f03040312070700080b404503415411100075989150b2031000c00c0280c00392141d041138000b0440440d80c000d07801130004016169000d0020000c0a0303881302000100591b4031500e42c00b68220032f40101c0541860815059041e0306480d000508203111400c04406030301681c0175115000070281400a0001c00038008444400540018800303100001808007000100c54072104d01d001950700d2800c0d80386c03410b0100f20b001340513060119817555660300000c000b604003200d40c40c0c41008220300c900c190600420a403406908107070f641c6101c40e418815403441f8000c01030040b6034403444140c50000140e0364000214407640c600f20314011598041503c144c40c00740090312940 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 392023974 1250 392022724 392022731
    0x607031a0307050d0f120f0314040b010b09240a02010e010b0306010e040302010e1911150f0901020f031b0f0c3d0e030c01090806130206130f1404 64
    0xd4966000a0300700540700300310b601c072003010060300c0c0c10101c072450881300130315281014046010f000c0c0c01a0345400009000c1d2820302881103100726095419000b00c07002890038500c00700511120500d4005401d5280018150503520b0900381400c44158100d01c01800500d1070004a50a900d6428020700040441180c0280482062440001d4031424140502c206000b05180000d040c9031003500040e410308400b609540700d1060400c800c9800b4400c04800f074401050543c940101410150344070050b00b01103003100c80c184120720901c2070440d480319150904520031010703404564882800103154480c001545071440d581c9541c0640d003041902000308025410040c0050f14907122282515044a51928488001113003480488003042b00d40c0380002603242d080740698989074105130000d0010004404503a45811002d00440c2c07012128016940d880e00704c1d80c04920f2a40e080e04459450342c0c4000c2020381403100440e5142201005a03006121901212000f000100d070b80d1184101e40a005a4040c03 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 392025224 1250 392023974 392024021
    0x601020a15020927070503040218040b1017060103020f010c0c12050d050c1002070623240a09020a1b080702090114031903020708150a050604090201021906020d0e060703 74
    0x413508010000d041806100c1e000000404568403203414042080902403c103901d0b09107418411005001150112440e40c408070000c1001404043c0f03c0341c00c85002c1c0000d203816800c40d424440d460b030305410702606008840407560001603042d04071001501741448078090710116801c10914256003280c1e1101413200c1000719801b03c22740814101041a1a800003503643c050510b88000100f59034610701c050244085101406802030410041c092000b0300d81c610074459441003800701100310406040c0d07000c83c0c00d0b2400c110400458000d084880040e007415501e104841c0681616011304400899090400007500340851900d00760f4a80980852840030b54800803050200b69a516440c110500300c0490103400402c00d0310801642014040a00c250395403d88120104155540700b80c1e42a107440d402e00d000602c45003440c2c840d000d076058050340100301069004c4000d242c070700c54001003612401d400300107114080308540518480d8a4917403009044c0e62030141401812a4a4900798081d00480ca4a09 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 392026474 1250 392025224 392025289
    0x408032818030b09120a020c030c03190204053c0c0307141602040c02150f0603030f161e020925050a020f0d02010c0801120305030a050601020a150209 66
    0x8400680f035001c021420141c45240700c6524004d280ca00410382030400003141440f1645c0482d0120040c2003e4080303c00701d40c444001c02d80c9070001c85250b00481554490303507101614068008582000c0001032001801c0c2502014941d4485268042e802100c800b40c130b40010020500c0080b54082082c030035085c11070528280040c01801c942140c0c0400640219400c070014140c0000c0020302680100204007414500c0006500d40c110b007182c1700421006000055203543c400b00d0b400c0d20407840107028616180385200000200c3d0408456410150080007580d00024502641100c41485e46500c880030741c0303158030400020300401000e10169403000051f6070400f0007025100c40c5841158200f090301c03641824000c07481d085200c00c0540702c43c801c0341da01f911025010b620010b00e501ca190750fa102541e0701e50360851a15903503400014001b94041001034000c00341035001399003142c8140305540c4e0300d204646a204145841002800c180b90b40000c1c200c505143c100c250600a070f8441c0000604207010301d40 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 392027724 1250 392026474 392026517
    0x1a0405190501021f0b0a091b05121f03050d080a050c160204020c1203040c1703030903031f1806060912050703020d030e030706050304020103050f161404080328 70
    0x528101e800341009403141c03c03542ca030400d421821006c4d000c04011507a400d00c1e007000e45039120602c00d100e040f10501002441c0325500b141c4240a110381c0c52541c40c0c0312841c044520150784405200602c111450200000c2d00c18019001050070300e9461030705038240003640104950001c0e02e415261082041250142c09440003a2924036804940c01622110521455801d00c84030248c00c0101d00000000c000400001502d40c40c2560302607001303101c80280c000465903a1b84010303207165420740d01c00c4c0009a1030380300e0720020048105a12220b458400d5503150000780c040b0540c1101c940040d2284014401c46d0741c0f00003814000d0544103089900003009407103594540202c1d02001c0c0c05520711201100505000e14001c900528001d011605455580c80001300307160400c2e503041340040d0508020501031001a1401800342e211700140311020302d03480c5815204401040700240000e0000c1c000080c103880184064003030011207030590308000041d500042081c00c240c1c404138045c400d42c4014214001c0c0c9420 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 392028974 1250 392027724 392027743
    0x90703090507080d12050c0306011704030207050d03020321071709010b0303070b0f0a0902090f1504150812030c0a140f0403030f030b0409021005070c1a040519050102 73
    0x14000346166440c180941800c90a403c041e85500c142c502140906502241c011090041a1401c04c803985031809204501c1c841076481d140011400c401100c04040301521554009100e801119011643d54002c100c1d0342402d807200390050382001c11413003c84a565884900c5000d8560140e489614000001810f00c3c40e2201d00e03002c00b0f0500c20001212801c0c04d62211504017401811280c582d040382c41d140740d21050442c0e4000c16540712901090401401c3d001d001400c0f54010030304c1750103540b50000c40d00010301c0100004092200c900d00342009403940d2150500c441030085295940c03909040b8443d10f00355090410b80c1c3c0100042040010070f10f8904141c0d13601164a2400c41188203440380100c803103003d40500b0969071304001800000f0560040e81070490040310b910107004500800d020002110880c800280d013000003000380c2c7c6c0846102e82e0061558074072900f010300a1a8a491200344180c040c011441903100000030306019a00c2c0c28103041100036410b541a0030740d2424a00002c1d1a00000c2 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 392030224 1250 392028974 392028977
    0x51503011b0309061d010617060405070b0a0e0a03050304211110090f15030b190501180e190b060c0c0906041b0f0908010e062703070503031909020907 66
    0xb036a03c1d104000c01034122504202c3c0640740381200c0c1d080701c41114020041485010314010360136011819164000c070700709200780d8002000d003001d07500c1d0802e41c0c0b42940c02043e09004001d481002c0c28401e903512301500003d540600011a107a03800e03c400e01c11801c0841c0320b8010b004104004d55000995011000fa101620540c0c91440740c1d40007030419a0044041c0d04006068000d8040c086203800300d5400c1d03862a00e03880d41d03041c40740100c0c100a0220405e0075084042c1c213000c0420080c415540681c9000c1421b031102d4509116250f074451600840a400380d0714100841c000b801c2e2242000858022400c40c900202c410034500241c07410780300d54070f20030980458010410030b00000c0b4982d4441c1c0c801001d40c0141240c90120f41e45540b4014004100c04074110041800920702040b0300005200e1710205c0d400000061a190f03c0c1d00e5601003000c40c4241200300504408001c01030042c10601c042d140444c45140196200e080c42051200c504070040c968036540ca20b4050401c015075108903059800c040705 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 392031474 1250 392030224 392030231
    0x71103060a0b24041205010c23070611130b03010e010f050306040b06180a090506010905010f0e0c0702030102040308071106030c0a1115090703020a23060a051c051503011b03 76
    0xb032802c2c0120784c001c0d5841400c1100240d8030507401d201041d00038480c00c01c0103a40789400500c2104404031380e044200e5803034034104418068080040c2c0380c1d51020b030020741003882a40c200702c141001c100002140740c101c840821000f1004001c07071004011080d024105000f1540300035070910713012954a2100a00c0605500b08c1d5801245140c0c64000c003491070031480c000c102c04d26240c02201140034212185040b102c600c28000005041c600034401c95060b40c13039042141d40300c20b1406040c19035140c0c014000e10002203041060000583d4248010401180308038445910b810342030130803440e00c00102d10300500944040007004281681c0c0c2d400c840034007544d400d111800c00c1b891292189415209a4220ba00344028410b20025020000352502142e108850100c01141c4900c03403808550340c004000f04c442c1410f03091002c01c0c0e00d4200d028018510301882c0640c1041d4040e541040040340310040b0040c00356891f001d10040340010a90040d6840d410b5009203c1505d03010274040250060380c036103104041d034 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 392032724 1250 392031474 392031529
    0xf07080406060b0f0703120905031c0204090f1b0c020f01140c01093f030203270c041a03070302010507151103060103140405070519080703060b1c0305030c0d0b030102071103060a0b 79
    0x580d48c1510064420f1450400110910315407000c01068082619501c00c81c0204031000980d101e10470144802d40e01514035007080c80300301c00640c0d00c403070f0043c4240c004d07035800d100d8507031000742c03d00c207003594580140c405a19400070f2010412402c4580180f5101141c44040d00e118000a90880000130328624a03005075a0f0307542c1c070001000f240c01031000b540c0003a9050141c0d449400b0001303803e4140107089901b04161420013000c040c1022030b442e00a40c254002c41c00400c055800f500c040c050b00743c005c1c0c0141429035040080340c022035004640b011034240d008020311201d542c0c10300c10f00750f44014800d000301c01801d0a1320380d2a0b0f11040307403060038402d001c0701100001c0d9500c44417499004241c2101242e4040d520381ca0502c01a00004c1d100314060880150a50321410000030240d070b003030340c160303e5951440d190126031800c6507110440300c080f401c2d1609400070060302c003480104185400b6041c96050954402c042509101001d042e2500d00c41c07d0807600c0c0203a035601c41c40e51105c0100b0400d201c1c004074 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 392033974 1250 392032724 392032777
    0xa0203180a0506070605060a140f0402030901110304200a180c02100c0201050f130305030103060203090a0f1506090501080d030e0703121706090f07080406060b0f070312090503 77
    0x4401d500100c0d0400b001064000400c1203681145002e810200c5690260548810b1070369500d11480e003886130701c000481f1804420b800c1035802540c200e00948004590f215952100708081c4c2d2003aa8200c7c0c44e040814540349482c15a103100310f05118045555804491901d842d1400380d00da0b40400d401d4440d17881d040c1c0c400c420b008009002104191280a1244a45c2c00001a0003488125020400c00c1c43c203900140703000c0180d504404040c1d900d61281811239007140c0311140250001004013103548981c1d404180402c3d809160340d0400d9204042d00c0000a0511141e503056400700d2340182c801905000c014840c1c90b02c00715a480c0c030050035150006022000541c180d1400305140d001800784501e080c01180c02c41c0d4003006056040511142880180d20349500380654a14111450403241d641c0c0d1340400d5069100c0c085407501b01f03000d65404119a038031000c100926511004038a00202d0002804004064016212041c070858242041207a250682c132603584134031801845054100d0064014078007072 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 392035224 1250 392033974 392033989
    0x501030c0905270114010c0305070804080105240406080d0e030307150203070906020d05070f0501140a02030612120403020405100b0301090902010e042309032104020111030a020318 79
    0x20100189252201c0704410b5030392110b10f2000500080d02141000081858040311030400c000343c2d01a07507180c5542d102c5440840c1c00b600f04410440d1954000c00c00007801ca10240205801905044656070401c00e44075209150703042c2c503c4195001b1810b01400700200c1601040c0e0001c4c46105007003007445461640002030440c8039444004041001c124000c5607401c42a50246100f1740d02c60f140c86003002d442c0d0300181ea5600000c4103900000b4410080c80f40003c03003442a03051024450300000c1040407a038a41042d0080701100c07212203051303001c004c000c100d00d840d0b0165101d40020303c0185c001321440b003000c62001d1240e03001c00307805240c460340442d5540240c00072100c01000d201d046107450713503152446000542801d94069001411140030500c031031415128502000e0001c2c0368501c0ea201000b0b038407199101004002d12040e000a10803900480700c100d1011a00d03603000c1d030311f803102e6250030b07c0017400741d0304103004100c40b950052200108054001003218907603001c4d10030908241c0081c00c0001c008 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 392036474 1250 392035224 392035229
    0x506042328050f1b1e0c0613021309050715020309090103050703060c0f120c03150603200309060708060a0f0e15010e2b0606180c05130501030c09 64
    0x124076000c405039070500a503502c41e60003589891150051074132004604074030f40800465140c420341003004101c08a8143c4c202e051030407648a0001401c00d40c4040f40d0505000b0111440421600c01060001c01c500d80060301013010b218104040003c04001c1e01e60340e60324400c0f4022062441d806900c1c2c03c0c0705900070016903c7d04070008003075203829a103a180c20341d152521440304072086410080501810ba000d200454441c0000303985030f01400400a8042c00541400305100080c90380c0d54809000030480a174001c00503018584003c5070700c01c01022044900c1c80c42c1100e00e02c400d401401400792150300401d0244e00100c00e840d140032641c0319080081c000d4105a84032041003648490300003503090051001c644110720403200c01d600e0b18082d01c019a0720b10300c001c60842e4045032000090b451030044180b00d20780c40920031045c0411248a0780d403136080720030b240c0261014000030407440f02030a80500a0001c44046460483d051100c18030346031002d08801e004a41c14582c0312205001d189100301c080d20300 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 392037724 1250 392036474 392036521
    0x90303030106120e1504110103060b030703020403050f03090303040e0c090303041431091505070e09220f141b040e030c070b130f0605030a05060423 65
    0x1034a50351084041c2c81400760210f144580b5003003600920701c2c01e04c04280d09910341185040480742d81d03241d91b1003148a1408050882c14140d039542d0200c0c440e610640070f140305145503100180e82d2070a40c108145040303840000d4030096801044145459200441a02e046a411120070109921b400c00d1040080c041d004015030188004034000403101d0517407000e0200e5000980e005902ca448601c0105030024189400000e0316550805201c03da0000740d001030310540c0580701c0d4070f40032480801002d0646400b540c20b08005000d0444003c002c0c03828126103034020340350086000002c903140f440c050300420b81003000303405c03e5000715002040c0510251400071188408040da0151801240d00f14805603103503900e0b500440c50040b2594500a000044403040f406020007021520f2a045400100d0f9000d0a11440d106000074000a02030795100314510150042e525915100c0c540703100300c1812900c00600080c421030812401c04050f61000d0002d5103002d0190340150b8065aa100141d0798002c0c4040d05502c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 392038974 1250 392037724 392037727
    0x6290c1908071704030309080c10080901140405030406080c0a020c13060803120a0b03010923070f27060302010e0904230705030c0d080a1b290a060b0a050f090303 71
    0x3c0307003035940014416640700f40c4036500d4007519486981e0303a41480d100c1c005d81058102d0200620301d801501450343c00180d1100106c2c44040304c0580480b4001c042c1d400300d88a0348041028400780c1e81003007502d540594032400c02400c00ca06100025600e2a609803007900030306c007c0071500a4000d0703a411250180c17640c1400c03a642c0d1140b1010b80f0390a190300700c60341c00c0b1b00e6180400c1c0040500d41070045103a0030b42c06c4200c0702c811400c014141c0c80c581d8080c5105049600c10030000140c00003110501c20014801030850426003030140c0d00a8450700258208414002d151880070300050b031300072040710702600003a079980d10382c0e41d00d81c900342500340c41c9030500d61079030004001480c0030228001a007a003a01c40503016907071070500640c10f00c103000c400d908004002000c140300b1018017501c104c100d401d420304038a50141c10716200b926403c44440c0d0118258800b03140071003580c2100da420042c40d41e00281105000c001443c070b821100b10281c02003285144c104840000d5000025407081c051b501d040c5802029203 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 392040224 1250 392038974 392039003
    0x3110a17030306030c24210106082202090a051e0a06081c05030402060a050d180605060d0308010b0903161d010617181006290c190807 59
    0x65640342c0080301d1291081c49031119512041c200050740c3c5491500c9051401e40b207108846038080560031484514100141c51010128140300404025000f00007548034036200e4201178249940303000f1040c001082c4840a00c0d030f1080140c80f5103952a83c0080e00190000b966154142030840c0380300d080181080c0359100205001003440381c0e078446008c940b0803504a0701c42001000350b505803494000c1c0707e81e001c200148009800740c14514000c040903019032074010b03e4040d4210b2a10111000c40b010744000c3c1d01c84800650401c8242d1003541d0f0403c4040352460110700c42d9130390080c1003080500555007011004070710400d85440403c400603195081e141e007010401e071500c181414208642c02d814410aa48000000e420390140c100b6008140c80030361504404d40e9407d0500884c1000380c20310070328601c00c1ca100340349030007054807850b4050320b0746152440740500c6001040042c000000905980c0b048100550780042d0703c0021501e6446444e060381c40742e04452400c1c8031001d130084181c040c00040340510300 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 392041474 1250 392040224 392040269
    0x906070809030604051606020c060417070f0905061e0d03030b010e0603180d05040303121e0203090a03020705010f170402061303080306030106230108060a050307120b0601051303110a 80
    0x34084401d07400d031165840a47d594400302c0e621150701700d000f908941d00f04010b01c2a11074040d80080082103010031200390790b94420320804c0e440003646c0a102d00c185d0b20000c0c44840c0c5495070701c1c0e0030340d20070100c0c00038803000d003110009201c000c00c0c220040500d541d030120822340f40d01500007420400e800600306616440c0000030115540660300400b1b10754020342c3c044441c3c00d4000c10070341e0141c81d056a82c8595007001aa2103100800c04100b25850f51070314440310482200c0540001c501c50410320003d05101011850041c0c9415016000b0606000c400510000820b500064090125090104006041e2128000f050043c030410140e1118010b07044d8012090003840c1004501607041500208400c540d550072015510b030b900c1100b004505031481c1515000e44c0b2400c511030b00910010310a050490741c580002e49045860340c07081c02d441e2106c1140600780852103d03115840380c000c0c24680d01d04111441c030525400001d0200038410071150007020f10780e440e141031800c094400c3d2000008600800d007003 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 392042724 1250 392041474 392041483
    0xa110f10090c090504030c060510180f200f031b0a02030c070609050618030c040f090b13170a0203070501050f0114010c0c050f06090d0308010e0c0708090607080903060405 75
    0x1003581c2e000921400010b800c8074500c101031045800d6581c10f5580701069941c000a8003025000c80055079a05070040740c06040a209800e44008111001407030380d4800d0a601c2c03e40d4040881751203480b40c04031007a03d84030110b004a50042c0e409100c529621b550360846107004035518194400b0010010600311001c42d0000000c0070351a480004554403242d07111030840780c52205000e4984c1001c0180021006d498501c0508290000001e00380e490048540011408072140800e02c004607a0700c2e492208207100003011101c2e0420f01c0301386403da0b0401d0a444a81500c00202e0070b0709014a00000c103154214070134016541c405511a0080c8a1070034034400e0040210002e025074080c590190004e01050341c01040301d030030915400144100d003d40307040100042c465140e1440e6410480030400701000740c0d1004245032419110b900c0e8030749294140440200c01400003031440d03000080402ca0400030070f40c08401d6404c404021905241c0d1202503207044605800707008840c1e43c0512400091100300705001c01c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 392043974 1250 392042724 392042741
    0xf01150317030910020721121a15030c0403080d050703052d06030a0f06020a020c032103180303070305060310020909010302060d060b1309140601050a110f10 69
    0x11051210030448190300d007454071050350740501660004198a21880243d000f401005000f0502800800e03d50202030498002d4100c4010002d0441188a10005018030400485840b20f03451100d0000030080842c0d0200740704d407814901e4140c084005540e00440c10102c5000d107902c005215116004890344002500041d0303640808a814600040c8030702042c0e02ca4180b680c0b02101c09030300b100b9000d9a141210650260840b50180684074002d00401c49140700d4204141c8600380043c0e540e40c0c680402420100c2146000340f103600b0100f00500c0055084810030030407000d001941d50350380c07114a50b141b005414024084c20502010081000315901507000c248034000070f801b558007800b40d1940c032100300d21a001c9469400506140140090300784180a0000000c58403000034840d038030391003099900d8102c10900c42c6803209503d0140800740b00d900801d0815025004240d81c1400e011002034800d002d034100c82c800b003010102c0c0c60030002000304140c012981c0e8820a41d801c003060101608003410003038 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 392045224 1250 392043974 392043983
    0x120804061202090d020d0212030c070306151203030e1e0c0f040b2d04090c14040501140d210e04060819080a12050c0c060906010e16020f011503 63
    0x940078028208803900031070718008001045142c586a5550801c0498000300409903044000103c004011040c00c000410b569a0050b00501e011480e40c601301043d11503c0050f404804118402000701107600c00da003480d815414200461100e40d405c08192a10b1000c909080ca403100e0350150f1064484049641040c05d082900c1e0404051090428001900d10654910750003208000544000700303c6840d80100315124401c0c11043c2801d2030000070240c50780d5850955400c4c0d883c1c1d80030080000140c0000c9001c00040e10284440c1d8036120110300c400d48100b1045008404100314181007122100403450100d4902d881d03118800116100208201609450140190b02d001d00110754500002006c0b0030300e0f007805810102050700b07591866480c0d00082c4480042c0a0082c90b101e912000c20f000d078038842c40e00070400030f03114a46043e04914240c0050080a240d4000d54014052081a1850160b01041c00301c00300e0440700701d8110803458903888284103020f0754a010710401c88820301d03075860310489014 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 392046474 1250 392045224 392045237
    0xe01081f030311061003020a150207090e01050f07020a0308041e060c110c060403320601030302030702090a020c0c06031f0906090c050c03030613020702060c0a050601080d080103061512080406 84
    0x3101d01c02c0005c00d0603400b02a502084403503003007001c5004500c080f0000544c43c4199001582d44003054403e648402d08882d00994546040106190031030003029803014680c80141880442c60300d001e01903074005080a03042e458000c03040280003410b550818082c942c0110300700401044040d00403d0301d550403450700d0580c00380716494030f403074503050041d40d05032608151640140281c000b06107005000740c10011304000c10b00240c01d8515201408024000c1d8000c2d00a51fa40314890300c10031482d000b000703001020647c41404a06121040000d041018003c240c46903980e0342c50716142d090111603c000c0451818170803a41c04600152150002c0c0100c82040c00c05000900400030180c0b01c50181c4075020304d00783d0080c400200d05c2c0c605907007050301c04c2d185500010f140568a401017411a4043e40481c0e8150384a14505400c0000c1003202d04d00601c0114060300d280d00c0020f134000c2085506100203411641c46000c2d25808100300c4004100803d0024940304c0010407603d0107418980182c490880031514 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 392047724 1250 392046474 392046481
    0x309090906040b060d031e1220030a02161515061403070809031303030c050c09071b020a090204090207020111030a170a0f060f0305071e0504090f051f1104060e01081f03031106 77
    0x100c2707200d07807900d078020007180c1c0c0c11030740e410014070002d42205a40b81e0031340a0181e842c50208010b15150117000c0f11448022610b45074581c1d03400300404595020300d04200c100c144c0f000c80d0980801c00d03241c008480e850403031440d450f1071045515500503003600e240d9406440d00b000040580100da40401c0342e1184040e11f08002d1003008210707800c0382c119007410200e1407450100d54030903960721003d60310b148003e007007104003900c41c1443e40481c6c12070b400c854a515800076030307442550707001200560701c000c40e0401186001310948000b0002100ca04002c180ea441c040b0118020045d15003000b08904000c0000304031090347c3d40300d65000c8586a1205880b00e0141e03040c0860610544041c00840d03003103240c4210011440c120038040141900842562200390040700c600c0081c1d800e0141d9100302000300c1102118058504200302255128560a8542402007000f00003580d0001c4544170707100d80900300010a6502d40c02d0b0858031001c1d5100c45108240e085001208040e00b1607402d4130b1410360181142c4c0b1565 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 392048974 1250 392047724 392047751
    0x210b1c11040e031b070801021207020c030a050705040b0609192309040807080c06010609060905091014120109061e0504020a171207050309090906040b060d031e12 71
    0x19a405003445940e00b040004d1110000000d03c25a04510204112050107541382540da007280c1004d000a501600e04605004441e6810800480c000320100d0107000051440e81d68a61341d900c0038400c650103691110310741c0c900e80e501e03007003a610b252901402c0c034100748484140f40d003040410341c01040d1000e1048000702d107035407800103402403041c60b000c0c108080984a030b032500011a086940119200001048002c10f054011b20140c0d00030b01d142c0c0c440c0d10425040c8100504200115004580a044030a0030010b42c0110a01e900049440100369543c207107840c48089091112500c0020f40650300380f07640c0300200500d80d40042d105041190803072400280035140c1c0380c161201076401950200306c500080c0301c00c3c50f49548072103e1405c150203c81910340108401c5a030390300112015640d0782c10129580c0f606090145500d036010039610003406840c0303001e42d40c200300480090301d070a0040d1103070b0661034109030140c01894002c0764540c011700026a4250801000009620704444405080400300002c11 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 392050224 1250 392048974 392048981
    0x60306060e0906041709042313031407020102010612030c0b100302011706010e0a060e030d08010b030703020a0909050112111c06022229040501210b1c1104 68
    0x42d800b074009002180c40340c0e162a56030301030030002915283c80c2084450410781c1e8510810302900544080140340c2c40041190301e8400000a04660b8950f81c4101c407840040c2e0300406048002c68200c26150310b80ea80c1c0d000403030040100d504101c0070035002010481c185600442c01c0c2c1841762180b00e051074550f48144070307115a80d9443c070001b0f021518401c40d000e205e04803030b00c015034071260616041c80003580140004600c0f40d02ca0b800392002c11500000c0c2805420180120502c0c880c41c1e09009905515101003110301c0d04c001000300b800c05601080c5c480a044c0324103641001411051b0007030200b0350b190034000e6945d0b840c12908480066500700d4081080c281015808540301e4089200c0102c4245504c1d40d80281d4400e102c402d0203000c004c0f41ca070008051082554010b022000d031070703484206014002d54410006203032003041c5e0f50002d020400007a07a1068080f0407010305081c3c051424908040c0b04009041c0d4041d10350350107400ca140c0c1011140e140300d144180d1034003c0c4209068440c0f0390082c80104c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 392051474 1250 392050224 392050231
    0x4030f1e080c1b0a060806040e01061701050a05040308060607060615110c18011208120412020d08060f0d1112030d0606090f03021207080303070905090f0f1602010f0f060306060e 78
    0x503155041088034040c81b281030b8010350191000c00c0c564071305d00b0701c6400c4a40c170740c004c480548143c5000c51b0400401348243c55000380d50210402083c202500d024000210050045128820000b0340204102454120200030016a1901c186040011001070510a0300d40d0600106e446010498901803030300c200308070740d540d114003082da04a90a0800e01d11458285400541d2451020001c0b904142510b001d03013885140a070290103984444504020704101c400301c0d81808002181040c400580c0d5101d01c405000381d021a00000345a0b180d1412008081c95880d4081d4040c0424111030b40710100880101542e0b2011030b0b041202035218182900d02280f14013400c290b00600703040178401400c0002d1500c0e0025510401c480c0c145035034414003440c56204541c0340740011104942000142070502403680c012294100006c0c4925181c4444003400390000c003021203201007484041c2c0658000c2d844449800000f06040c01039500180440740a805079100454001e031402d0000960000e400046500 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 392052724 1250 392051474 392051479
    0xf0d0818010f030c0816030209060c010606140406081f0503240901020408060a0207140a03030204050301051b07110109050307030318081609050601030b0603130201021b0604030f1e080c1b 82
    0x82512980035042c006d5501e6a400303400e1607820007028205540c3c52028001c414a51800810100d0600000500001c85180745000c081810700c8184034054201e03d4990b0b00c01050600b007c146030000b0780800e54030700340b54030282c1c050051410010100030100820f0440300c019000580d00780d218520380e91b080b407003188500350780c48c0c12501c0450303600700864000307101c00c0340a20100c06089a1001180341130042601088000c207500180410080c00e0a02031182e001c0ca000144500c404d00c15182c41a4034400c8413002080c080d03a480407040a81c0c02548400041c04010b0100c03440507881e45805420360703101640c0304c001b080c8041c0c00000c0c0e862000076058201c012a05825001c00d02e006030600c003420015100c6e9040c175440c0e00c800c100c581c40d5400035510507003000082482480060001904141c4540c0c005680600707500a5540c21340c031810f084408a941c0010b12110100c45414150482e11066490407018003458403113805100b00300014141c0744040c00c040d510442c4980d0100c07100a00341c002c440b034 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 392053974 1250 392052724 392052737
    0x30c011b020108060310050705030901060608060a0302040f15080d120605010507140708100207110102150c0703210b120c100f030b040e0d020d05030103110f0d0818010f030c 76
    0x40c01540f04819107600840040c0c00c49410401030800038050790780884007640011800300030003800c41d509024460080230070f400c100320309003001400b0a040c80014003004e4000d03070702d4124013a00040c00307610180072001010205a0380f503444d250260784400c0c04031841000600c13900d1803403103043d51500c25041203500503107640303182082503594441c4d43c07450a43c2d1103032140914800041c2d07142c8184880241c18582e4400140d681002e4504017a80f8001c820045045500041112000e03400e00c001958210a1b170300440c079214500d0b450221041c0a12004000032080d102034451200082d0380c0002428070003c680040040980342e4100740c0e1000f08219550f070203c1c001083c056401e008034886011500710b86008107214074900081403d0b500728107421040d9600c4a0b1072400d0499060100c84444416031410625552454a440c03908104480c0341d640302d200c13010340ca0500369440108103a8240d0340044880d4580382c2c0282074801000040c0c950300c1c04140c80d10034001f6907911a2180034445589500c410 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 392055224 1250 392053974 392054027
    0x30c0a0e07020f0d09060f0503090703060e0a080708071a0f0601080421090e060a0b0909090a020d0602030405010b01110d11030d2405010e030615010311030406020306030c01 76
    0xc0c21484016050a003540126892100d995a0512888070381503000d407aa65241407a00c10000d0820107049074000802400340b050181c1d099010400038120b94005402207041507890b80c1403401c103580e0050040c4080300000d8904200300440014088880c00b404012820f00c152442c40c800e450740c21600e100d0b0b40b071103210008400f58000c0b142c04e034105000e000c02e410320701000158900e200e0001d246400c04188840000c10101190840e01e9501c030000b40c80c8141ca0034903102c11a9080c0c011456030b03603c87c986038800a020344101308460f440454006203004444603103400c0000c001c0d40142c4c0d06075410b5080c189103da95500a81d014481c18000342c00801300d001c0029012519480101e40440c0240400c00291420071202d00070307100b016001042e1925080301d103000d42c00d00c07019540d01081c180041c410450516603000700c1c3c1e840e400a1820040405940c81500480041c110300070095800c9c90302005000c01d21007254091441a0001da04840f00e296807030b0019540f00d503050104202650884920 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 392056474 1250 392055224 392055239
    0x3040618061b051c021e06280b041112060103060f0b0708090a0f0905010503030304080301031b05040218030c0f0604230a0b120a05010503060c2224030213090b1f050901030b030c0a 79
    0x28030103113441100c002810402c0840022b060304d40440b400710400102003002100035900740c10464001609007810403000f403620200c040084001e10800d168441c0101c2c11405002000d0f0858406080c01014040c1c55526060710032030000d00e500a4084640c035060001c0f405040010881e80503e03004040141580e29503034658000758035402078001910700e00c00c2c0009030b035219800036100c03aa060f160030310100c2c1440e40500d4601421106010321039000300f04c11019580740c100c1142d094506086540004140130a400780100d45041100c2e500300d9183e0b80000745040b0301c00040c205079411508400903a441e00031000e0b007560800c0c0200750b030580100002ca0b2000c02c495000300036005400c50030703501d40c06511022600228040e0b001c070310f107810100c0d000b880440b5044590308100455090171401c1c812110f02e1002c0041c41030242050050f034501d6002801c3c1d440d041d100600d00c42c041d0100c1005004018003c0c0f140e00001d101d54042400d05109140ca440c01241c29100000c01030038400b0840d10f40402c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 392057724 1250 392056474 392056531
    0x1b02040b061210050f03060402061210080601030305192318060c21030c0315010c12030c120c02030f0a2003040618061b051c021e06 58
    0x4030a9881a010464408118190900c4902ca000c410100540c0707149040c0c184500d058984000d244260011801c0000682e166404d0329000d01032001122060703603507240100d00154550f00b02003003903c00c40c4000010594041c0041c408958601040b642c0901c40400540e038980b03003000501212036059458803d40090407019049640d00300d041c074400c03001c041d40170402c03a42c41040d6191040c1c1040c0006d503100c405080006000f020360b80c0259182d45404c90b01075400c1e0001910080a90703084103900072407a80303e4003140712481d8110f801b40300701d04407a51014000301064541c01000c03414000001d00d032051123204140750030b01c85030040c6141400305d001a041945c0060303d400b0510044954407000301050048401c2d015012500035a070b142c0c18403002803c0c032400720b00465509050018244501d95016444440424014420614031007140c64420306010659030b180c0342c0b845203040d140340003990000c5c1c0000507440404241e40d00c3c003405501691205400c03241b803065440c000b001c04030108000807 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 392058974 1250 392057724 392057741
    0xb091902220f020706091a0c121b0c0a020405070504080d1103071410050109110a0c03111009020a1203021c0e0924040c02060c07060204170a050601061b0204 69
    0xc0000b41c1c01030304249000c00ca82140e442078031296900d001d00010000000d64244442c8900c03074444019291001d6004c0c11446041c040f1002142d120009c2128007500790289095480c5004050b5290702004000700c0d035640c05d25800fa846030b030605010070340090064084800b0788601034017500e012401180240c076189040c29031700307680d484100b1416000c10002448408407a1100d005003400100002440e01500c006800100d4184c5ca00400a10020000e0040b40c06604660a0105d40700b4491f05017500d180c80d6000034210300f80220071117008800320640c080d101c22442100c0ca02681921015981d000500066004016030300000e41d0a00164a8046449030b03100b40e0302e000503e000b41136001c40c03110384080d102e03103038031400b259075400d04910403020002c40881c003520200a034150001000350307502c50250000303001c500005440024040241c04542c00747c89070071040d40840104880041d940c01c1d00c0705e01034565000b04000030a442d403203900e121001e000c1c0b4003c40d800320001c54003000014100710 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 392060224 1250 392058974 392059039
    0xc040509060a020c151003031403061003090501020d060810060608160c0f06060609180207030e0f040209090f070f090e15130e01091106040605041208070f0b091902 72
    0x611a440100185c0010321322400711901d4141c95503185140c054440c40c003007182180c00346801e204210060319000c28640c80c100c2c0703501c0d003c0317070b200c20504185009114100131b07840303964184100400c500000203188008000396010402040b50386807821140d40c1820359418400426090f8009550340c4074100c000f04444c05503942c419540815070745c0c00201d40c1076511240106200a000300414203a450744020340c2c000500c4250319051450740d008020150203211184120740d2800004485d807526410780350801c4007e0701900f06400c203d04402c08040e01160a5400200c0003072000340100c2c0b064854500319215a410f1442a480d940d801001907009030303903103a401201c19501c05010030500d00880c0c0b10521290b0000031076215604000d210a000000101e0040303a08001c100190f540c02801c83d0222813045101607441c072a540f034000c80e81d10680d2070203814003083d506c0400510862413056030080d11000110303058111501d01120003c03120311170181d070020507a100480307a401c4100704510b031051380d0b = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 392061474 1250 392060224 392060233
    0x50d0e0d0602390705060405030607120f0606020106030221030a0309020f090a0504021008010f05150c0312010603050a0c0518030a02030d020d090b03220c05030303070305090c040509060a020c 84
    0x642807060308882200d6036051099040038540c4816070141301c0840039000c00d449603440d003400c100100b03030f454001414900410101c0340c1e001001c00b1440e07010149180d41002c09011041d620711000740603003c1030000703910030080c6100c54816000310310300d18001401c40c403000c0c50402c52074010550003040307400f1084e604003c0b008112401c030b90f03640302058828404214001102e003810700502904021071500f110a0006c0400140500680880c207076080300c004030394646c1c40d05884080d002140c0a24030002201e0321000c2501c1c4e00014048800c0381c181d50b465681004190b84040d07001c1c0a6070301000061001c00c80402a010030030486178540010f010000c0c0840d00c180d9826804280307032490348420840182c01441c140c00744e107640704500ca4000d003c3c143c066421402c00c2c0300c2c05060354200c29408200c40300d00390101e008202c00c40140500901c0000c040d280c4038a8001c4001e405000201d440303124a000e2400c03120280c0c500b5101c0e080c0980000f500030046030b030380c80314400001d510044514045128 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 392062724 1250 392061474 392061517
    0xa0b04030c081917041e03090332120703030c030209030d050a030b011e32070c05100806011803050a081206010230121003050d0e0d0602 60
    0x194a0001c2c01c00c2d441c3ea6101215140e2031400040103504100b0090821011540600c004100307440700c80c0c0c01041c0c40e02210802e207101e6140a071209480c540c07005000320690701d40000018401726180041558104440d459209044020394076800d51031081d42030064140301c22000b20b0701c0703a8070000e521500d50500500d00a03910340000c1c0b03002d0305445402c1c001741c00050200c4180d585805119a115400e080810a040544582410319410b41070348208100e0008110745d80000d28400684e0312095807041d4032460506903400d01c015a1004800391540881d10600003818105001d421200c071241e036494080a03110b110044070121207000e1050100543e140001c00424800c1c0501242c0314410840c6507912110614034140f901e000916a41c103541002d420507556400c0605d2000d080b8904060440c0c120003401040001c2d03010700d03007060500000d11401c0140e03504005840c0c006803406501119001000c0d0081180c4410f14060b4039500921042045000283c854000d0b05080c0d00c4810b00300603850 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 392063974 1250 392062724 392062733
    0x20a0e01080604170c03160201021b06120417030103121404030b19020904060b1e131203051902060a360204020909071d0301021603080402030109140d180501020a0b04030c 75
    0x3040049035032044016981e20300119070f0102f05030025100614084400c0809020005149010791644220100c0031140064208401c01c1091104800345407804c0c0c3c0c036940c490800b0070491104000d4500480c0800034581d5181410340c090302d0807246e01100c0004103039107803d10007800a07200b04141d440b15400380a81d10483e50f550003060040c1c02400d14050b104d903007001040c0d1080921004001c1000010420541c4a00d61280302c0b0060f102420b42e00c1400243d2844d080342c41d482900441444001202c00c40c0001c10740c0400c03054026010b5550a0044660300c0500300001814403008246201da13010710301291a0900b1214610740d0b000501c01070420b104107010a903071403000c661010000300c0c2440341641c21080d182d000100b16105070300031420f00e22040a049440e00400e040030b0103008081d0002021507409400a0301010340c085c8035182d070664041440342c1d90328038108013600850340060700074880d107180b030402c4012100142d00900141c0b40607110a03003201d130041c0c802d03003c000d8407222500214 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 392065224 1250 392063974 392063977
    0x60b0d06051602101413150213030b1e160314010b040617060f0402031f0303030b210a0b09070905040c050907050702011e091d04020a0e01080604170c03 67
    0x70315089089080d140c10720b00c4024205043c060410701e9151420003000c07940c1a10300313103040d4020307001c00c0140809000d50400c58280300161456400d50750000450100d8080302468000440740314029002d070503254592664039800c1348280c0024103807251700014034102e24010040319484194240024045501c1c00c1e107014603d0309802c100c03041c2c100040c0c20404182e000a61030000c08070701000c408071382010000541d42d0340b60304081d203100301c0c1c0100124001407490417030484100c20310f09510350801e9407803402401414000c084a0b120302c1580404070b105050b01c1c1005040b040d0b100d40070b03021100c410386d1204040346000d016008288a250404504008148105030007140258000c0140c2441c01c420404d46000c000c4c480010070405211a80050360071813a0760102070440d0f024030480c00e074032520888440c2038a50048100303590701c01542e03842c40301000141d03000e140242c1d2400e11440c1c865506185808003031052100a5208030001004107405240c03810007142d204050610b0a00b0480c00c0c185076 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 392066474 1250 392065224 392065231
    0x1b053003010312020c18011202040b120a03080919060c020c19050a060f0c11040f021204050f030405031225060c02010e1c0e06040506040b07050106080a0f060b0d0605 73
    0xd58200d0b501054203e5010004a10310450480c0d1400c07054070044810f665919040c0324a00440b80945003210031541e039900000c8400e4800b50000840d55030441e14582d680c000d4020903230110f403100300490420140800d04900300080c0f1180550300b0003c641c3c514008005a4142500314080c40c600b030b1207903580e403201c1541030a41038032100d030300c40d0308250410807a9613071540100d0520407503090780150583c109402d2001c103074014030341d11071070341c1038001207030141c03010b401d10043c81d610000d00e03000090303004ad00d224080d032b01400441e90303010906006070b55640b1981c01100d03450751112580364003d01908000b00101400103410000d2880894854049241d1180e41114510340340c914200f4150360911036103203404840c0300101070440003040c01000c1e09100700b40103420403601014546858030313101c007200d0007440c000d0300c039581c0e81e42e40301b40c03850751a04012400c035510f500300309002441103800030f541989541c00140d0800403401d5580c2c1ca400030041d0765400c0e500140b02d0554100030881502c90f0610 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 392067724 1250 392066474 392066483
    0xc010e210114040506070302030f04020603070c081b010e0309060906030a06082b080105150a05091c02100206061c050a1410060e040503030106030518030d0209011b0530030103 77
    0xb0a08061a100e42000e03402045c10081600c140b040041001d0003154164000c0c0d019100290303261500e82c0c0c00c596000c401e0782c010f0000f0000040c07981456000e0f440d0300c481080000003c1000d190000a010740700d03c942030b812540002c043c00b41c2000c42c038144009642020482030f00259682e550300c4c0c501e04003200b9491800c41c07101c03072a07800d03070074407140301c4140d40d00808900e07009030381d076042c4000580344001401c40050945004255184480d028004840030600001d0a40703070301090702950050741c002a080101e01621a111244134814000100e00d409104010102e0420407c030307001041e89806000300070b176010300c2001c403100c02084541e21085c2c42c0c2d501d101d000c1c008110041540606403545d82d80440b805840755010800400c0c40801620b055450303624000c9100c1e240c3c2c070a507402006515196406501001071000c105071aa40c2c0140900c0c1c40a0f280c080c2c00c07001c01c820b00724141d024010050704642000b010841200408504000c00317122400c04401d06204e4110001c189130001d810448 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 392068974 1250 392067724 392067761
    0x705010510140a0b0d1503050f0a0c0b07030909150e0f0601030c05040f030f021f030501090e0c1f020a150204081912030c02031c05090606040219110c04140a0606020c010e2101 77
    0x800707204004c640341c8054684ce00721a46488185d580062100c04a44280341e145503a801002c83c240050780020030041030140c3e4940715030f04041090b110707840c106a034903c0c0401d140150501c6502c1c0140d058030203d9900c040301c0c2040520396218983e40b0035001208a03800042d5910007a207240b80d401c0d0f800f03e001e40540e40010300d0741c1024803030011210b01c2050f440d01c5130301c4805840165903c8051030300d00310542c0080b1070800c1c03103442002c0e4074040000200400d0103070b003075a030440d03450070301da02a2046032600000c40d108141c8001c0b02c44081c6260b02e40203003960404001c2c1645060003a00051b200b0301041c07040301d140030146c00d200307080310001d50720800c4070b540c9610502c0000c0a0402074560856000c41d021072a00c0c0141c6810b072220102e0309215424445c2021400d400d404040c004c6000c60b084c043c100707001c800e48030f02c02032054807400c850f2180d140e4900040030a03814400511340c01104010703103560500c01c0050007081600c400034900bd030590003000300450403e400a0041c0300c0c00100d40340170366 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 392070224 1250 392068974 392068993
    0x3120d0209032a0f0a0306020a0f02010c080f0c1809070909050a1109120106091401090e06010305032205030307030233010902070204020705010510140a0b0d1503050f 73
    0x341c182901e82403440c5140394030503e80d5010304642c81c034400901e4402c6030056200488400454017030031081c0d2014007031620200b11041d981d5001904800b02c0303c1c5035402000950f01e4840700783d49042c001d40d8045500d24034000000c0103e150b1200038007105659102e0f9032406110040012403035101203883c0e0f1300203010b022081194440303d00030355400070800340e0184050321408000144a000c4c0780c28442c400d00d4609900410b030ba4007035010801804002100740404001d450620f503040c0000c2c81074072600341c54040d950049035808110705051300c3d0b114015514201500a81421080c0100000c822034881c00b540081c06940c20402060028425005002c006800c860b08080018409010300c9861b141075003115171602603803240398151620b10300016141d180e00e0000c680240620400248a50300c2d280900c0360903c0b60049000c125183e68180f240f941d8120001d010070a034807485000c640d07000500140c0786070405a00606440d82404440c454000d9403922900d103400c9000340201d09640201c000b0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 392071474 1250 392070224 392070229
    0xc0a030608010b03190323120105060304110415120f1205030106020d080406020d05040f020f041404020405070507020607110108070914100e060406050c0607020c1e03120d0209 77
    0x4000003800070100800208100001190f01e032203018001350443d224980b400da0406004101e842c18002c1d22100204003030b840e00e5566a15584201e2100740c40070f08090002600d07141c10811684240d85c050501c1d504100050103100c05032500c0108032880344030b05000483d0105001c080449102c1c0600340304205400c403820204c21203080c0c1240b0800704a001c000600c140e5800064060006820740741a00d160360351420201c00078041c440392050024100014003051094803503d150000780204d031003031000c0e000c8000300070403994010700344d50003098050000f60162400b0b03440150b2003142410110f181c400903030b0000e0601e03031028030210b4100e2407020440040e96803159082d90300002034103140520710704102401c1c0c10300015500140c0304043c0f406189511600c40c58003c0d10601024040c85d0b19280c03100d80c0a451904a84100c00b0184241000105001d00c0050309030018071026200404015420b02d12807200d421080440f86c040c0b00b40c4200310884100c100003005e41c0c4031650300058440740403004 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 392072724 1250 392071474 392071481
    0x4151410050a0501081801020904091a01051903060b0a1a0a030e0d09030813030210020d120603080307110111030703090308070c05030904180204110301030b0115020309010f0c05060c0a03 82
    0x941e0080b402080180000e9070450b8020360490106880340411500341016140648034a07401c40d40c0250400741d031101000502100044200303103800782030015a80381e0382400005580041d0784512480310101c20004154a0f6001e840c44500103021888590b882302c040420035000c9441001384031070005014400035515124002030b02e01c20201420880652a100400000b02804064a060800200300c01500d95540d0507000444d400ba02d901c0d016480640081c0d10b480540c4400d01c04569100c241d4040700c1c2a502c64201039070340c0165418110385600710b0403120b40c00f0310000e4400c1036682d4100e518080e0020000395120340c1d40e50740c005c200802d0ba0b190050100d02c0103041e2400340b1111180300c1c03000401c04015100000740944000a16518851401076445480c1c903010750403d2402c1000c58010541000841c1070b07a00070401c0110503641c0b1003440d8060741e04e81003442c0040e001441010001d61085c0300b1043c007014149454a41c0c0103890316220b050400c01d45048804410000f10040303450780501 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 392073974 1250 392072724 392072729
    0x50901330e070c0b07050f190c050d09091a030a1103030d0501230118140607020603090114090a03170a02040305010507080103030e01110a080c15070302130e07020c01030504151410 79
    0xa005402d0214a10001f0304500510200104034210380300032854085c8601c07940762140750080211041ca0001400c041c068414500900104500f880f6500e01403403c1071988801d0104040c00a00300b19600351251034200240703c040a5040c04204142c0000b0091805058080c15130340b24200a08845100290100409000440c0c140900800b41c0c1e18a82500e603010000c035860080c01c8242036481c600001c3c1d1038420b08000a43c03040c804010700500100542c0624032405a8030818182500d0303510a10340c6e0340e84c401c0380040000d104003a400c0e00c0107145c1c400041d00300000c0300e005810310f901c030765076903081d03403c11204d10700003400400041007456486602211002c1003800c11a40c50390b40b44000540b100f816007c00707840c1010028100000d000300708810441d42c01170b861384035518280540000c0c003a60001d2503a407121407000d8804543c001035100c000b402000c054004000748c136440f00065000e804001c0c4140c901c0c1c00000705151042c0c5290090b0020303d84802c141d81c0300c43c034100050b0502811240c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 392075224 1250 392073974 392073977
    0xc07050306070216140108060d021309081905070b1503010b130e10020903031204020607060903081503010203010e0f1302060a0f181202060c101a0103050901330e070c0b07 75
    0x40fa85c43d071641c0069401d44c0101d02556661401c0c0042c3c00441d00241103140030210031441c1c48411802d100303491028000c00d44011104510020302c001040b90203004001e000b5100f03003000310120300c3c5180b140307055440d44e210107400071600c1d548903000144464072900300301d018151201c41034100c00b00e051029103142c42d036100d0110b007032a04882c08240e0f0380c0101070011812443c064081410744d40d48034192000b043e40034005105400381881c00900082050342c5403100345c0d4982c0d411110307074138040c02a20305951b5a110740b40307138564802d004000180405041c524640000b64026000760711800d0003006004526214000e100130312500041001d100d1190040d001c2e084100180000c0b845095890701c0a07070102c0d00d241e01d0b980384c1c40005013811410303002d81158615003000140001d041c1c0722006d0710164241ca0811135541d890103001c1c241c0e4215032110102c10011441c0e4101e6507544904c03e020703030b20034441d10501c0b25268400324000000542d0040081692000214100040790b401c495002015 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 392076474 1250 392075224 392075249
    0x6081501080616090b2104230114130311070608090f0f06010504110c0a050703060506031903211508010617030f0319050a0c0801050d0308010b0c07050306070216 71
    0x150100146007005900030f01030188000190400308141030100049941b4204014840904003031800c14020001c0b44201c51400141e4044002645018443c00b02c0c3e01861070841c0f80310f6a03c1e2404e4a0641d241c03c1d90440502200e541000039846040007810040c0c496515200401c0c200f41c2c1c0c2e0640703480300c14109024940e1115110020103e40450750504554060350f0100c2c03070a9055820781c07060700488510310405c0c4a42400441408400150002228020340e020401500c0d104203040c0c40d011001d1030080980409403428000074864152018020001e011031110030700d0a141c02000d50301d625100d02561140e003401400704100a100324001040007600d040c09039514101d10a807a409241a03181c3d240c000440050310130040d103000f080f41c1030303100d2400300242d02c0d00008403401049100032035400503800300300214031410300740c6804111030340603200d03244640e182c40b0314140340e40d002c034040300346500440100007403030340781041a42e000d0134080e00506000d1380660032004039906180d0064961119 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 392077724 1250 392076474 392076511
    0xa05160c1a0a021b01140d05041703060f0f130207050f160e01060503060409082b0507120f0b0d0c080d053907140a08010507051903060815010806 64
    0x3c000851494050342441c4052441c0894001a40e0409a1110380140002e0009110903800d41a0b07014620883c456075400080301d0403101044058001100c3c41030300100c105030b03d084146000c1940324072002d4020101e0010644000d0220181c2c0c2081d40c0403540c1b81d02070582107501e0b40342440b0301c180d15030820342d8105003240f4140d03000c0c1c0ca0f6641071191000b444400400310b000c94607260801d44410742c20403646a0382e40030700780c0c0181d4020400014005060100804421b1590070360050501440d0710f5503030411200b203001c0129000340307441690740709001d654004030000364482e08003080300745016521202c81e451800d20150b050082c201102c00800070104007034580d4040d400101c18802070b50750704a00006c200c0e598054000c149903900345005100c0c58200107041003a51084092600040d9a00c1407039139030b170781c2c482801d0b0343c0141e603503c010410070300100100c141a1112040300e44110b190220780c042c1c2d108002401c00d01d030341c4d600c18211a03e44005008204d4100501d54000d04000c445504c4c140 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 392078974 1250 392077724 392077727
    0x8280201020303060123030c0423061c0b0409030302030106110606011b24050601030c090807030803060a0911030402010905010807080c0f09041104030c05010c0b06060a05160c1a0a 79
    0x220041134036050107812001403140b4054113a5106546064908580c1d40342020340e0a02e01d80d40003849850300a091054024807a9402074618440410019060604001020034244940c034201910b03110a9540d8910307105007551f80d03002d041d940c64042d880050740c950400308006c1ca0010749840d9500c0d2030307200b2024000541d9011980f025820002d510090101d466440d1429091600c0d00c507000c0c07035090b44140c02a0403032095000034001c10007601d00300124040314006840c20b5180d4030405089801c4442d0030800b08134900300841c0e126100600d0392030f007561205100c0044a40c99210340d00c13800000700030403085581084640000d080d003401d00c91a18900a07100904144004001844030f400128000681c1d0480c801502c060280c020801d03c0031001e8450700d07a84942192005030380104407910009050b500621032500d64a40208002e452030740d034042030068580c000702d01030703041000130441c003808500f44a4071203100d40c3c461090140614a03001d045111140c0311a5082d2080d0800c110200c10503 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 392080224 1250 392078974 392078977
    0x6040803041512020a030b19030c1205030c03030c0304060501091e15090c0c0606060306080d05090112060b03040b060a050f040510170a0309090c0905040b0d0c082802010203 76
    0x68580074001c0508046a04003260741c8243c45842a11031030001c901c400350319400d504116000b0a00ba10700032202030f0101c600b00020200c2c1d200c082c000c004030450034031441c5144c0c83d13001030071070091040b039142440c0c00f00f4251441d03004543c2c003c06010003000b407208001c1039000781801444c45100074072140400491800410319030b00c40140486681d203c41a008440ea040081d008104405040000b0725003180003516403091b190342200c2d054134001e0041840741c000d04c01c0000b900d000a0045c10041c2c60750b0000e80d450f078010000c0c035042c8075400c0080900540d00d801840050302284c14026101e040501d010710034450064030640c400c44010409001c04e481e40b06540221402c200d90120303280d1107420902074041b04603048030101031110079005031118000101d0140b854825520b6000344e958416000b000c488884031020001a0008000c1080d403a058000e00d50ba20001440305609c0c2c10700d55121101d9050507480448181c0201900c024900b00503891100d10002c0100e82ca0310004442c0c3c0000c0d144e = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 392081474 1250 392080224 392080229
    0x25022a011205040606030510021b03070c0b070501110f040312020f032d18210601030b070201020d06081b04060b040905090717011b020309010815030102071509110604080304 76
    0x180da07540c0009080c1300c0303250030010086400200f5590600b09080030720029612449428150080216260b005c61500000700d41c241c0f600130b110042080d06011290600760300920003514603640311100715541010100050004126440300d90ba030342c5281d07203800c100359958010103005542000701d004513480307004801c888200035980d01c1061680008ac4070103034408401c4141000309880400e5810b00d200f0489058035600e503080b542d48540e5280c2d800000d8180c3e20140740d01c0e810f500410300400000303200c004131a8002910380009420020500c11000c1150a2584000301c241d20000c0750861607400e000346ca03c520841518103200290503e2092212441140b0800a005a56600003050203d0070f01440004d01003211b410207103036104d41c40030390280604041d91001c0c2009a005085a64000011641d0641042e10384141e10303070310250740c0708001c1c40070300805402d55002c00104000132501071084540784c2c54203400203513041140c18010081c00040f800c01d401040300f00002d01c07400200200b80e404 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 392082724 1250 392081474 392081507
    0xe0106170604180f062f0a050304060603120918020412150605060f0c0d08011409070e0a08010f0506060a0516110d14011a0109090525022a01 62
    0x500c0c1d119002140c01040c488100030301806240b401050801c5011b4221100c40d01d0380c0b0703007034101c10444521224210144d1048142c0d8940041002c010414061006544c1c40360040c40000703440c503660340342c1e0a5091070840e40301d000a81c903490244040b0414401c589a0345241d035904500381410402a0103060260310740182105e1508a07018100101540110b4060b04001c0c2c102a212030710000540c000750001400b020880c000c114200d12000d100751000b9040b5003980d1040c03c0c14940a505121103010041c0c13a0740c080140c0d01c1e84a00c501d44a42c02c91134001c040744000000c9200b003807052380d411920060500c0703100c3d51040140d810a941e020341500c4403901000016107050a16240c9a004520328203c0325030020901e010305010b10500b100384d4a40d00b400702009120381e0705503540309080080d042110f00e010480720b0350240103000940c1d1040b43d01140b0440c002c55a0b0802000952412040100903801680a80045107403c4400e11240d50800c00e0018522101c81c800d00000e0820702240d170300700a = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 392083974 1250 392082724 392082731
    0x7210b0d080c012d0e01051b070606080105090a03090806010e0610021906060608090109150207030e041a030d050a0906051c0c02010b031504150e1c090e0106170604 72
    0x5002da6081d8040b11044000e48128409110800c88500d045298124442c940d1031510000b000c03000418010244214010140288180c24594044819801014096500036a9020085641c0c402403041070301a140c0c60000b03080300c2455140040c07249900360801003003a0401401000341280d055841c580044080b0b6a1420324034890030100e1500e030001718200c5e15403181001e4070047c8143c903841242562404c1d581c0302d0143e60340940700303400c6c1d038864031005210242c204188918400f681c2d02401c5000d1191520300070041c0740c00f00040a64080030805010318401480344501864204030a00c51001c403810020308000d01c148018008031528810f003070500038005607040d0002d420704580c41d410303034151104010214132418001e000305001d40c3c18500a11a014448c2d06549094201c584500d61018a00d003a01c50a07040050240c82c0c002a0500103101d00c04d298012816903003244018100c095071640141490f0080d0b5460303a43c01a8407110501c56012a186000d08004c0c4000381d0048043c4c5012 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 392085224 1250 392083974 392083987
    0x120e0c090a1805061f060e03060c09040f0221011205060705090a08060f010609140d15110f0c0705060705060402010810091109040605060a02060714040e07210b0d08 72
    0x4100b44203190000400b140280c4080241a4148840d0f51201500d24216050f6458849400741c1d1003040075050642d1552000300059201d5040100810180c0070191020030100704c40f11910041c0c5e04604040c003c1004003060000400d040800380da8010704550035a101020300507110b00380c48074006080c6ea0b0822100040c02d189680352030000310300a003140411203003207250a4680c845044401c0c016500090842980014841039403010803c1c0c02d00010405081c9a1103035039505401040c10200c03503e0f440d29035840c2805071400001400940d0a02c2d40ca140e80e402005244504083c843e4100740c1c420b00007400814040346000072025401582801c014086481d07074444c414034511a603100e04034039828040726000802d07801001e005001d40603036042c81307281c2d101c0c802c1004a018035261702d8010307407014000501d958443c8400f0700741c0a00d0b142010b40b910b500ca40640c80414800c8400c0804541e008500303800010900300c000f2020300540c84204200841da0300004c440e10f0031004094600b08010904 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 392086330 1106 392085224 392085251
    0x6030c0f030c0613090612050c030d05030a02030403090302061605060615071b030501022b0b150a030b09010303032003010b0f03070c0605010303120e0c090a 69
    0x251041d240d040082c00f0084e00208841c4105104540001440c0000c1d0700c01c00b8060040440706120003061801d01d6441d07c3d11002d040c600980c01800c80c081600c0d07000e003c2da44c001e600d0712000342c2d994456080448044c40550800fa41c00f106c0001c13100d4041626160011001d442001510200d0703960004114880c8040000344401540421000001407c1d64603400303848040110001c86080d12904c1da5800c98004202c082c03c203000490b452a01e01040842c0720342e4a401219090086a00030b10200314a00700f20b1060003805240482c4400409010340c215841c2158080d000030240e613075901380140580342c09052038103290b2038804981d80310003602d0100c034181c0302d01d030f00c0c403031314000d0706071054609540018a560200b00511072080002255405494000e50090b954a0b01c002c101d8926002107581200000341c0b180d10007100580c0a440c0c045017154004d00140002900d40d900849 = true := by decide +kernel

theorem cover : BRFrame.Cov 391906474 392086330 := by
  have h0 := BRFrame.cov_init 391906474
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391906474 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 391906474 ≤ n) (h2 : n < 392086330) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
