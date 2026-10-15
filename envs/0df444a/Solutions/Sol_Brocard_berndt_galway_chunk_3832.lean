-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3832
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:48:42.351417+00:00
-- url     : https://prove2.me/submissions/11f07ce3-1d71-4aae-a0e8-ea9ffb008320

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 689028776 ≤ n < 689208633 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 689030026 1250 689028776 689028797
    0x306140402090a0b01050714030a030f0506030d03020903010b1908060c030c1605011e0e0f03210709030c090501050111010903051b19230c0a0302010503130c09020301141905010f 78
    0x80405001040c4823080311a0300006d091a03419506005100408500d072000340818201040000e0f200e84038205039204056020a03000510390302504007410100f0081e06020108003003041c1041182c15901503044944105070104000103080e80441c0d1040051414482c01c11642d44d00e40c8031120350f444415151992280400c1d007035178801e20070a290f210f25080000556017410505907040c0300750000344107429001800070444004c982110304070a03a90074500390321075076296002620a00c2c034036000900300c0ea035502c0c8003040381d50b1684e009030b0507174100742c0f03811040b080144290344c00d80b8003c0b80000c0000c1c070144604144603401041688000c000d08083e150715101440000902155007841550b04511002c01d07041d034180261400b01c2c00740003c4000d840741140b0b60020401058841c030000781040400000120300217054140e50700280d6221900d5640d69a0f07a003c2075000e50000c1c0a036025000312400c20b50110710700052911480c504107c00d00d802685000015255008142000014000d400c2032 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 689031276 1250 689030026 689030033
    0x50306060a0e0d170d06061412091006060309021509012f0109050715110303220212070302010e01030e0c040509030c030d140708251809060306140402090a0b010507 72
    0xd10a401c031011194007a10b60706005c10800507180181d2010b03050013405640070001d140000c04840344200d2052850206031125210280703404200181e0a54280c940340001c170b030842e032580180c50024000c850921645903030f81035103800303446403c040c1c601064907204400341c03265480c81c802051006d080d00501c04a0081c0203002d094440708901100c050b0049181804003401a80c4a00c0ba0b402d13451070440c5e030114640100658a00c0302038802c030311526004010340d4504003150821600198050b0414002414a0030b04641e60603c9000c124045505019002c0c0194828410b865403842c00f200100710383c410f901e080c44000d00000c0c1c1b080015001c200070f0126810000c00c010144201006000141a120031066044000c0003030680410014420144a410040301c0c0d0782c1902c0080840c11061100c004803000c3d115404035042c541144041d4960009809c04035030700110480780900000c4c00441c1340486c00c049041c00c100c40080d030100d03c80740402d0000c0f0090380007040008040c1400c42c036104050710b = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 689032526 1250 689031276 689031293
    0x1020f0d05040810050f2217030f010e091b130513060e0a0b010603050603070306060b040e0a02090a0618090f29010801060513180b10050306060a0e0d 66
    0x10320200350000703010484010100312410302c0b04034102081240f400d00403020100440043c00d0000e00351402d000c52a17101044c04401c41000d0740c482c0a0740110907030300101c0070a980084602c5013801d01c40c04000560141003111142c4211003206c05802e6059924400c40c2076803101890540d0440d644080b41a14921144100d034010003110032142e8200d0420326018080d50584c0c407a81d00c4035000035401d00001003100046505445a6007804183e5698010110f850416164005032800d418000005101c0c0042401031054902c2c00404911565800e404131050b44070b2007010a8110042800802045114101ca2078140c110741c0d90325800b86990300849010340b0010f07144808010b50b02ca185005480c40d4001e05c10240a50890740c1c150f68545100107800c0e0801445400140200040c00d8103400e002500240c02a21048403008600881c2d1442d03400107040f00c4802c10b0013024001c59000c0e606000340103492081000403d403d240c02020b500072241c402880c5003840c0c02c04140c0807a40001000103 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 689033776 1250 689032526 689032543
    0x9060213080a1209032d021008060a0501181e03051c1d10050306040b03100c0e090c0904020901050408030d0b1306080a020409031704030e09010b0c190201020f 70
    0xc4005010b0300c509424820204440f010900b01440720324182000000d1300e803201000c1c3d849a0b0000901c0c50360740200910100420280c009600a6042d492520460303080021540500410307160400046d84070001543c01200304400f1414020100c3c2c010030000f00c1c0c0c2d48824500a18818a48104039070700e44c0e40511b044800d40c4041e0711300b044c0681d00b80c0031603400003200c0309580d0302410290005486c54042244080a182100c04200c00080050305984690b0040035046001508440f10200d030380c0c103d40010076a580402c0006445580d0100940c81d1060109001d40c5491005515102210702004001e510010580381413060501000039120020700143c40c400d0000d08021440d00044410020000e03504c4884400343d500d0170605001502000440d005000e60513100021040c1c13180c1816214000200403c122084405040008050b0700581240803000c0c00d98100542d42d0720b41c01082502c0c01003c800b101c00e03501c10914050032000013001d0010140c0103005682c0c00c01910b01c1207a0402401 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 689035026 1250 689033776 689033789
    0x30c1c030903021c0b2809030e06040e10080a081b0705040615020715230702030106030f110103050417030a1104140f0a05030d050c0f061603050901060303050d09060213 74
    0x303d008180c180300d8004c204942c00502243c0d01c0351740d4912541c0810380b0700d0030706d9051250182c1d40c16861042502a103111030b00b0b20b1001b0101501c0e25950441c02440d0507003161b40f0300180c81e80010018003480001382e00744807280d100038035509180800d00d1250640c9050050203143d0b22640000007031076261882100094100e40040c50816400400b01030702d0801c030b6520070039a95025008140300507511000c221140c0c8401c9051149182114005c40e40d140500c0c00060340c5946803200000030440d0038511070b80021310800107803184000050040d012540b003260003816400d001196506030030804130045130321113406075000802d0011829000d640c0e82042c3c008205200d18008815400e150108941c005414200d500f404001e0030700d80400e0310748414101d2041444004070740d4102c0210240302c20450710b02e1201c11550f482c030f00003011104042070864010301180c41c00c0301050b80c2010601a820903aa01a21100e240000524005005080b2880181d03002036017403000070b1805021a1051008100313 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 689036276 1250 689035026 689035069
    0x20d090605180a03090605090103150b0703080a0519020306011e0906092709151a0117040c05010806040b0a0e0a270201120f02070c080c030c1c03090302 67
    0x10182c1912510b00ba5048445006a00101801001a03800016107050351000c3c5840d5807220901c100580c040c0440340942821040a903202168000c6010054040c1d240241d40785c9107161a01c00c3c01104854042e10380d01031501010043d41141001e54000350341044040c98a03c402e075480b20003c855480b04d8415290014420010400c00564041d140001400210070a0117248140d42540c4a88941c00f04c014505541c5440288041c00341036504603182d19500072050000043d801d2150310203044114003075001c198240b0310341e035044514441c4a44901d511144000f0741d10b0038034005495094005120940c4280c803203c1c040460303102d0001c06070003004000c24058160400c0303840c001c169000e6492a030b15800385a4000340f0344005c4076018039000d0f40c080c00d0032000c00d10540d13034280103010301d101300743e203054000a00d0108100c249a000001c9036016001e8440495100040549070024078144030750000315503100d0401c0c0f0901402c00d040c207030b110b414280506a42d076404030741e1490f95407007813204005 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 689037526 1250 689036276 689036281
    0x91d0c1c09020906030c0a0515070c30030806010305180111120c07051207060906020a210c02150a06051002240705040b0c12181c0c050d030201020d090605 68
    0x6000c2c0f038858101c14200d02604008103841d001c281000d074580701d034620628421139103009a21201013152250740c0c00c403244020030b5440c3c401d4441c1e20032000c0038403140c21001c0d115201e80d4130041c480124034076038543d03256142500e4003c01100a0310003c0c1080c0803840303065840f0440c43c0c2e02480345d80034420203620941e4a607103042e0388620350b40303c0c010280d0080107800c201c140005403020803102d442c803180388020381d250f41003818410004e01c00501c0080105200054019845400821140400d59204c1c64590a108090121016200042036000c00b5a101540d2810104407070501d8642c00071a00c40d000500c681d603070740020024150074024101503048014a00d2580d5544014007000c01c10070329500300380e810108802001440ba91044820740900401c10f000001000c2c4881c4d603165540c041c1180d115610000e200c45003c2d5160071040c86082040e41c07052943c400703219000c40e06a0801d55030704c50f6074500300500442c40c07a81d0ba000c03001c44d5401c111802c02205144039400d4801d00800c8005060b2 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 689038776 1250 689037526 689037529
    0x1602030a1e0225031e051e030c0a0309080607031406010311120109021224010c0f0209040302031c06050d1b0806101401022d12040308030412091d0c1c0902 68
    0x41c8064007600781381d1700c00c03000402e02080c80010301e1204101103481c0140856041c40d001410341c007980005683c40d01410214906069120192105072000b08059481c2da450314803040d0101c1302e400201a0440e0344c01e03030000b0201d40c001c0c4e00180b46058617500d4640740140158140d044e4107002d800c80040ca590100d40c41419010a402d519484000c406610424030340800d0010003800c414400141003140c11003030001040f982d8914864241da010741592440e0400380f4029480e40c110100c2002a1101d5040039241c0d41c000f80600c804aa1020346164840c1045448906901a140039030320340c410908400024a0002001030500c541902c5141d9a0300318189105138900704603050003d4110f40c00300b01c80d8a03a603110510004405000d02e00448001e1403405116420140c480303110260700383e00420000244034120b00190b110b140710f541ca00e501303003500e0788054031101010301510040d0314164480c05076100c044060340360052002000e25003003022004402c3c1c8044000d0b840212050385581444045 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 689040026 1250 689038776 689038793
    0x12011104170f030f03040311030d05060102011a011e030e0f0102041a030f070305100f030b0906130b0f040302030d090f1103120f0d0f0509061602030a1e022503 70
    0x40800302800e1500010806140d0304d016560180101c0c40000000c201050700801204091780303104801e44c2d403500b1070051300d2001000f044500a000d5420440c1c03200e01500341030041a00b8030016120754640d030112480c1d0040309200c0192090a0507525030b201041c800303081041c1d03000c1125620001d030799642490b61060000340440703411f0307181d201d00b8810706c022910001c0220341d000000d4540014159262210050158410703404042c1101d0041c10100034000720507a028031030414442141e070f00d40c0322a8031140c24400e00c07100190441c0a02800306a207100e290b13940ca60414002d04c100e90801511401440c101c440242e0b08440046d00d41000c04200400f20745403a0203403108034050885002010915143d9108200d8416144400001d0a4500c0f102c10703408030540d1103190400b001580340c040c00f681d60307a0b041903480f8001003a0300c0504051142c40081100e0507031140e955071202e01044c0130317401101d107043c7c0b12017202540540f00802c00b10300e506102542c00c031010140403105144c51030409450 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 689041276 1250 689040026 689040059
    0xe2a0910080c0109030b060105130902032d01030c06050d0b100c121404050d21050304150207110609180c04060f0503010b0f03060102250e150108070e12011104 70
    0x1803080c07030300c8104045012000080d501c22400c2c24115070344e00c01142c8ac0519050704c0e42141d42010310100034424910240c601200d480b0148281c0030f01441140d40d01003000d0318091000401c0c00800d0102401403e1003071001d0020604140c0010447c00c9501c000034039045500001100029605e1030b500050203d0702c41e64640149940c1000380d884840040a88002c0c0310314001c16004100c2c01144070300300401c0010b840350040984443d00028114032200426030b0f401a00e05840714113402d0508211008203200701c0310b070941e11041d0800c4030311020b0180316880d00082031040d07100c1c0c20482da02c01c13241300c88203d051041c0450302059680c0d80c2082c80180104003a1a2018100001400181f21440d140003c40d078107000e40544140d141e590340070040f403900340344070041008031101c00070780c0c0744c1400034001c600e040e95460110302e40503595003c1581e41c44400102c071240020607050114200a004180030041024050180d40d0b00210920b00c1e00c0c03d603464440041d186890018040103001c1001c485620f = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 689042526 1250 689041276 689041279
    0x20d0c0801020d0f140103030f0c05100507090602190605040807080c100f0b0a0e04111302090901060e010e09041e0b0a0b011103030c0306060d0612060f0e2a0910080c 73
    0x4001e031252290800c44117014007001b0140102010b410312114011283e0b20f80c4690f101003140d01041e05012800050541a1500320204500030710126880740045030000d59400c01c01c90f01070070808292500c001800c000380041e20040410800c840214509200925101c41d104004240d03100c0b504240904072180d04014000980c07501d03441c9007041da641c101c2002180d0134546e1882d21900c9a003410544004501c3d0142e601c000112000340c0c031040130350040d01c6220001c4500e920341b680d0f80d0728182c1d41029001c002c540011008040e600391071605104598100740100e4200f400400d02d020741e0075614901034030036a020f00c8440100603404401d800b0781b1460324028a000007c0007a4641d04540d68003014101c68a21007005c4001030a945a40007a03400029075100f040c040c45a82e1083c80c28458011401941c100d42040004c80071112607015801c00000f8202c001c2511201200f10302040300f031060a2030341c1c0d92003000c04440569840b19400f5000303285441c0c4c403000d00d6146c4400b561405100d410710b00d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 689043776 1250 689042526 689042531
    0xf0f0b0109110403030e03070509010e01150206060a03081806041202031b012c06040914151c02040603151509090f020909030c0609011d010605031009020d0c0801020d0f 74
    0x20310400d201410354081300d5060501003403420b00303a00080d0410382c15421041d0031030f1620000082c104620794103941250b0907141c50070481d682c024422030300c030702045802c19044901d40e4000c10000790b40400030060701050f2855900000740c0d500020307600d0b5000798009400000203400100a514040c000006440040b4240c8941010b501c00007a2400c115584404408484103c0f62100340c0700c40050070100140043c0382d503a07956101c0300c2c410003c10050790300001070300100b0001030b070120a0b811007142050004100201c08950808419030a001c2180100d801039218240003001500c103003490b0041c4203208002203070f041290760307007101804207913445a50100e00f07254982c404a0030303000e00301c01c10a40581d80014141d595004040c44c40c1b1a419012026100d000104040c2e444194003225004c036554441e4003c121000c0c01060136100745025069058000c4900c01020304115880f004d8848d2025045020780012515200000c103102e600070001070350005580c1001c0f550030b01c9114403803d0743d030004 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 689045026 1250 689043776 689043791
    0xc1103030103150905100501230f030a082505030d0c05030411060d0228090b0a051b0a1209050906010815010c0501150f0e061f1b0f0f0b0109 62
    0x14401a03410720f50981402540e60103250b0288941070090303041e18000c501c0c05100c1569500041d00b0390a54880716000c1081c139090690441740f40c400b0b175440e6441c10050041c4131241c01921265600e9118082101c201c410f40c1260503102e00b203480000455901031b4000e181c41e500b05140b6481a156500d0040f020020104100000110880c0c00d051820600b80d501d1521007940e11040402403084d1311019050640300da41c040c050307003004070001c20303a20220381c2e51031282907940d02e450005025104480000c0f4006204031440c6030f520450700f84140c8070a1040310380b06030140d120f400d00706003992503010010710f454000b401282006112960409005c0c80c00c010546459180d03c2210a500c1841da41000503c00c0350b28140803094000005501c0000e1030150850f60782c01c145030380109030b44540c003811420240055518505540340c0781e4003201300c031400810501004011a888508040c440d4540c2c01840c0001020942d40b80746942c0c0d0350322a041e9421401c0300c908240d0350600c3d05034840940351741440315 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 689046276 1250 689045026 689045033
    0x3270503060414010612060e01200a121103010b070309082109042018040203150111070e0403030605030618030405060d060510020c09070503070c0f060f0f0c1103030103 74
    0x70100e510641100043c2d480c119040012409448994403900710090344208040500000f5440100f00c0c0c0c0050000700082e252a800f00c007048480c0100310440000c1c14850803244900820700281e03200318861000556080c07504003108686c0080c2c02034400391501103901c1d410150800c0c40040513020400003819001d5001c4c420720a07140017003480d8010366002082e070fa880e6031103c2d040703460442c650310382480b07884940f120020000d400c04400303500c1c21000c1484000403401c0034400c42c0c1c042c0d210000c443d082059440c00556440800803201207103803107141800601000991001c9000381e21940c0c0100e4114070344070805240c01000350544484a510b00b1103122000000000c071002c48005031071260702c076032880d0100f01c0100b040c2e5003e5504000100004070781c00e41d006c00c41002c262002c031501d0074141c585400841c2c0c980411644240071031a01340d4400c020601c50070060034141e20520020030144055410346003920403042c0203c3c01903403505000c1905541083c41a0000c06800d0021425036141da03e = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 689047526 1250 689046276 689046283
    0x3282009011203031b030c0912020604051203040e0a050f090d1707030204180902030724080a0f020a0201090506060612061c08190e0405091b120a03270503 68
    0x8510008502c802c03500b2400c00d8000d801c0380c1c1d2885080c0c6069030f401d0303902180280c00342c500c08840c0d10010314165000309030706504010030301e02e40783c018082905040c10030052140c0e1015000030603000b0301c82408001090340481c8040740c800c040706100400c090402065605000c0030250840d22035400c02c03403510101c5640110158009005030410b1421901c030190240c00900c035540090a8a44000b100c502840001d50428001d8610135800c64140760f0ba1100c4550300b401d551002030300700354007860055800350301c48d110050b0001c0c65a000000c000310104681c004a030b1020841c080581d44a10a00003888028000103602c4103050b2100380c83c0402d01d0450300300e460801444284a0441c40141c00c2410011829880302d4a5115041941d03a20402c5601c41c081c0904822000010340c0e4400c0082d400d0409000d4036000c2c004400043c060242c1c4400c0d580303250b22800401d95040001c5c3c2103590b070060420810717401d0341030290301c0e02001950560000c940800c0070640c0000310204004c81009541ca000 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 689048776 1250 689047526 689047529
    0x50913020909040609141213050103060501021015120b04020306010905130215041703030a0b031c05091207090c0806040501030b070c03110607030f150b0301090b0328200901 76
    0xa464403107031038821403500d464035011030941f0440c101d042404540e03000400800806000240395107503034000441c00e56015000302c5006820000d03c4450f040c0654004d00800c1030240101203d681d282c0b0112400210015800c3d130700301d00650140010f50030180405809845000c9040c4964505240300e58001c403804400203005203800c84c1c14188218130042aa00984010250286e000a00511241d074a03041940c40040e032074900844007100e4a80041d074500f150710060084682c6d9402d405069a41e60801c682d8a038124102c1c05001c0e450181c10301c038080180072402c0001032060040030008000900c0100039038051480c010040c004280c2c0368074881c6c1e10030141d180101a006652800325110000d40c821940a845088280a10540c1581010341c030306041c40c80410903486122111451140c2a11590940403030800060004d112160002c01ca44e01000e021240c82042001c0700742c616424140c2d000c110b40b9000c001d800100401000315840002200d040d0019400c0020000b41034103106 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 689050026 1250 689048776 689048783
    0x1a0f010f050d03020f010f02091804020d0b0603010b31150302090c0d020c01061716090218060c0105010527060409032f0d020f030313020a0302060a05091302090904 72
    0x14020084200f41c820060321810320310b030b10000d00c9401c0b040e44025002e9080030745460b200300a180014030742041140300c81c078401c0e50020301400c2212501d894500000b00e0191010350903540704c119210b9607171a10203100750401045107100340c1c0080110b40d480f0352240e508582141c868180a00354240100b04281e08003030344d0b0122481c502a445074010841640b088035504a11903001154940041f0700641c440d034111160080114407101000080584032124581c1c011000c9220b00400d000c009190342c05004900c0341000c3c5803001140700c030000b40341c0b600900d1280030640e454400521403070509100904802440b004000314090384042c0c18040c0c0b07036006044034082c0381d50310540410300d842550484034810000d080b40311510300000714009110b1104084401c144620015512000d10000b5015a5042510099811351b02d031502d42010110705018140d0744400c4001011001da41d581c40204082c031550340702c6580c7d52956006208000e0020221000c0c000d20503c0310500c0c0b0389a8844080c0c0c0680d1 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 689051276 1250 689050026 689050039
    0x11120a381c0602090a09020c100c050c0f0c0a0b0702062d03071d061e030a0e060903040305010e06010302010c0b0a0e0111070204060503070303090e0901181a0f010f05 73
    0x4280c0d0209480000060780342038114103240c060030600c111035006240c00d60f42038960fa00c055031600c08400c00d078800d0042d2000b8550000d45c2da03010410300e540c0040008a59440c1141c079000d594101c05160911101d1001525007110b07504d819585891051f400080c03024505003804c010030390300007036180d0143e54031510844600c080a261040600c00c4081c04910040403031ba912801c0c8013000034042d03812105110042482085002071510300038080e00c41c4425031140143c04800040c10211041e04041c0012007056200d0440e8502108244031582c4078030392201c01140c81d03d145040160a54018001002040d08188014000360f40e00c40c403c0701816800100541898071110b14040060100c4003018645510b0001312260b046074441c001c1100c58021a403c0c82203a4035442010380754802884020041656917000304041055800c106034032010300800002d50031010000042c548000f90750440c0c5050340e441c6041400041711051540144504000069541c104900d0aa03c803444d40103c621480c0d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 689052526 1250 689051276 689051381
    0x50901272106020715050f0c040b090105070c0603050925090504031701060801091401080a030f200307020406090b030c0f060f041811030c0a0c0611120a 67
    0x401444107880c4103580954115030b00c1540d41042ca070021495114501e440b424200031400c1c0c1598411454052068050326500c2d143c40c110070034515900050a00341409414052a0082090840007000800842d20041a240b51840ea450b04080000060000c0c0d0115000500303c2000542074650944204140029240d22141000e4401c40468030000013216101800411540e521001e018100c07a0004800d00070045107500300302d132245090003400899031045a164011a2160b0b01000041e19241414583c900802c07600b00c000005080b0f603c401d0b50b10000e00c0b4401c50400e442040024400d03040c1c104175600c40f4000103919500380d42d10045c404c40910460002d41d0759040100e0320b10390103550441e035032035580d4010317100c40c104140c1c1105000340c41c00d40d07401503141c400001c8034411101694114a0803811a00c240d03007008000004bd10010340e1405a80540e400c1000244100b501c0d960003442c65144c242d22070001e1315a420038410701c41056019440740346400c00a01c000495220000d00c2004 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 689053776 1250 689052526 689052569
    0x2d07081c180b270303180609010509101d04180b0a06170a050c04090312050c040902070305132405180904081306050307050f0714060705090127 63
    0x1080382c00418400d580016002c02c9035903075841e20b007250303501c043e40321003210b800504041e1680240621a0110001400b260540c4e180c000e0040405900504003241081c104801280500c0e0f01000c5038004100503080c1c0c1c200740b810b01340a004140c001241d060010840e511042019000d00c0074009009915040110350031002d03503001800644281000715500380c455601c0325030303035010106054419001d0b01c030783c00780541054042c8039003441c0c0580364044e454038500990b400501004002c900e03200818400414400d015000800d1120f0081d51020749908904050145201c0da551001c501280309140700895030000f9040d10b0004151400c1c1107483d14112514114080d0581842079407180040c0d00b00001c0210500252245809100042e200c040d100d0005031481e00c002e541c51400305006020214400703002e400240069403141b03016424802180060750320b405810b0760240e010a80100e00300d8030b9541c2c4028641c6c601c800550101d0010101385051004e140345600a9851000341c201e0000c06a = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 689055026 1250 689053776 689053817
    0x4050f0d02100323101203110303040305121005031207060204030f050a05060a020309060610030207020301050a2403021008180a06021218100e2d07081c 67
    0x60380d0080c0412007010b00c0150010700802c680b00d42c00c11001c0550007000e014007a10460f45110303080c80c0f8816100e42e82400c1046800c401040c0c1c04408001c000c0a00c04c00980081c4003440c0281e109031545070700c80f000304d411050f1461004082007102003003000204465540022010010b14801003115501c0c5c0190a0060280c070568102078580178035194024208140000d41d21042805603080c0d81160321240a880d090344015110001310341c1c05400800d071903180c0240d980261520f5400c0052808090750b01180c2941c100321004c0c152603583c0c814400119080850324403410086900c03030f01c1003d040d9030004a03080324110b80c8000f00950200000c0c030800c45400c98140c0400403d0032640d100040c3d1600e24040c1d40701d480540c00114030307080803a079100e0503085000500300c0030801400340002c5d40c0c00741c00700404c1462541c9035140f04641c007500c013045000c844840060325030407070886040102100c0c54680812170b40400d80d03036488100024510030f40440c50f401c5403030641c9003c1c0c3e511284140030600 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 689056276 1250 689055026 689055049
    0x507020303120115091202091e15040c0c0c0b030c040807300206091909020711090c12040807020f06030c0a0906110706030e030c01150f050d0804050f 66
    0x10148070004400040355454003050b41240c0c4444d180b0341e90700032240021240507920b489081e4524500e10006001403400030440355101b100307600e141c0c82c10091f5500240d94081c0c00d0b1114840c050020705800340fa400c0500600b120880a400d11040b800c19036940c0c19003400309407240410480c07012020442c0c0c04405002c031001400a641140c0d40c05440b10180c1c412940c140c10b0101d1104c003244a0403003200e82c421000c09446800414075802c201040c0f042c005a40003015240d0300222224401242c005050320103040403a01922020900c0c1c1912400d100b00d1881c09400b61221920134004000300d80d000d901e0859120f548401903e403106480d00c00b041119420407181030f030005000c810800660200d001428091681d0f40d00c14150685c3d426040c0d84916800d031160301c25800424050041c50f009400101d4541070140442e807030020490002d6084030450080e165440f14104800c0002540b1689070300054101240c4982540f0300e0b0f613444407454800c9210781400390303003600c9180e141da5403005070001 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 689057526 1250 689056276 689056279
    0x605090c190b09060702030d170a05060d0303020903100612020102010e010e0726061905151c021809030a1404051e0409060e0607170910090f05031c06090c020616050702 74
    0x11804090340c00c0242406081c240c0c0c0e901541e1002d4000740300802c1d5409010300402010b093720f0490a10740d10100c010758400d20140d03401d481403014205030101c00f031040384010b19810340b425200400741d200090a5400340d50b6180700aa0504a10603041705010500302e088032040c610401280108005940d0845000700c1125414000c00080200000e40b1400014045911060401071550754601c0700d550340f2540700e1600e0700a9a84805600c0908695801440260008240c0744034a80c54030401c000c0390b4012a040c40d100c6d040401c201b00f1003604881d518034203031054070312141401d00b0007021803403450000407588101004120685000d455071761020410319003002d8103114590503601f40c1740d130b03807082034444d0000281e10103080342c815003075007650303600402c118005800706448400300b010207841c04200584000450b090150001042040185001246540302c0c03009005c040c51074070211540c580c084000e840c01d18083c01540755010403115849002d019440301e026600384000c640c0d40c019154000d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 689058776 1250 689057526 689057533
    0x316050c1002030703090c170a06050a0e10020a0e2b06111602100513151103070c03050c090f1b0903030a05180f0d0305180d0605090c190b0906070203 66
    0x3200969140d0441620b85016003000e1f00204d5441c08800074031701c1c5084202005402c44d00c0c03280009000c540055420030240a8003240280440c04031500700300300c80025405403a4000307000617141d600401070b160a1b41048440226881081c52048000303c4840307104014240082065802c10845501c40580184607450303054507010220b03900e014202646400b039114200501c2c01c2d080c8140300e04110f403415203070340200003515450b0050b9400107a8281807a0410b00c049030301c1c20541c11a040016064040c0101d0280141514604219042182080401d4003542d10305080160500f541d10036607800c07800d07802c403e00741c820300040e07805c90030700500c204035500d400000345618540d40e024001c0c241401443c95400d162040c098108600e00011440d00c40e0441407100f18800840d0151010380f0f560a401d000380194000c150f400901850f059190445405071b0352014008858400c002c0d10000d6002662100030403807950b40d40529032005440340d03023005007000900c40c00d151038100a4544640d409000c4 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 689060026 1250 689058776 689058781
    0x22418010603020a03151b0509180105150c0a02220e0106030b04020f0f1c03090e101203090902030c030103031d062a03041403060c0a1b030309050f1f020316050c100203 74
    0x8c2c119480b64400c144990010365501c07a1013050041c100381240c000910709200c041c9080544169130b0482540b852481c003400d0ba0300e202503142d803003092050411900e41d022078001d540d0629412074411042000d86071f8541703541480002c20116080d40c000b50100d80304100020044001100d048000320a00d07041242c0c01440c500c850002075100e1100382c482d4481160160303d40c2d42e4002440d40890300544408464503042200c2c14400e550071000390302078603001d4015912000c68000740d0f030042d2851640240d0000040081c50340c00034291008044030389003404c0c3c60b0b94000000720740740a0385030200702c1884c903900502c1074120302d004d41034484017420040c0d83e100da40d41c5c40b040001039004a1a540070740a000c000030302e0b134015030303088070100104d945440c10301101464a483d150001c021040707080c10b0351404950007240c0304102c0c51394140c50100c0200200348480c08100e42005c400c03614050b00500500c140020502014a461004e504614010742c485504052007458038030445071030049148004103 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 689061276 1250 689060026 689060081
    0x110d0c08060301181203050702030f0c03180603070915030b040e011b3b1801090b12060c0706021201080d020705060c03031501022418010603020a0315 66
    0x321203200c1c010481c000c0007410051034070002254640b000041c900400c0c100f03c550801e000354415070b00001075104403030030441c0740044540141d010302d89200050f071001c5400d0201d44c0b10080c01e000303202c1c01540c04a0542c1000540540418a507000305600c160341a0031041401d4407135841110051001002844119003c4020b540240140316280007000526441042c00ca03002c0c0303100c16521000240d0722030744094403414031548a4802410000308000c03c924034411a500d28000c41342403c1d110510b00f8803949000701003405c5079254140c0c5405040405000ba000e650b01003046a03114849400c150f030396100900e0440002d205d66802e90140719030442c00411780580005107402e03200700030f40803545440d403034808004207402140320200c1142e00402c0010301354040000003a80c1003d040c0105d449001d1112944450410070011f810803003440c240c20802100313800789007840d0503070040001b00130540c2941c0200c2c20038103032404098041c0c00b040c4612145001198000400401d5000e500a6609003044 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 689062526 1250 689061276 689061287
    0x80411040b042c0f030a26160801080601150c08160515130b0402010c0212060118061502030703050f0906040e07080a05090c121203010609050a0f05030a0204110d0c 72
    0x1d02c80c0d0710301c248411190000030b0002003104c00e950304d45000b181400e1180c00c2c03c5441c2d50000340d0100000e0380d24554250400b024682d61030251020410076402070a0851009021010590192045500c84001000583e15411400081956a2611000704402e03070030001c0346c520900c0b240611070085044030b00180704010070440d44274003007003e41d14031b2515010b00d103180d44441c6010150030300e8040c1010400541c054068030124030b101400c64403402c01a20401424540f090340b11000c903604009000c2c000076070b01d01c00c2d8806842400805135480c002208001d64038050000c0040c1441f20000788c04130040918000da84001200030849a681e98031a020003d0140e0207540b18004100141d0100300190181e0040c18410000d4400404414030300340100310058441c00928101c42c052800c2d40c1d2420710200340254080c02c1c4a80750034502c103180c40e0601200064640c403100b070024031050207200c50f94000c10507541030b40d0100c2e0017003082582c000c1c0145261182c0c0101d00c1c4520301c0d001d40294032030f8206 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 689063776 1250 689062526 689062571
    0x3040302010204051e0906040c030e01090308010f0506070c300302030a030501060507051b01110303010e040309051504050607030e0d0302011d03070c051302042d090c080411040b04 79
    0xa48809a100a80400d88841c8146168215038006c220301c0000b0143e041a50145003113002c903250100c3c50046140c11242150203004042d000183d60f240141701d12683d00340c0c8140101400d0703030b0031840c00101d910380b00b102c034209001360200c0701181420a601c0c04601c0318450900c02d50640054261343c2c0c01d26001c0c0d52603114035a5400400e0406c0000900c2c0b42c0200c00b510700d8036800001402c0c001440e800300004600c03e07400ca242c1400109280007000d642e003080070f14080d1006d020a00003600301400c0180c40100a680818030482c2c14140c124129150b10303007500c0403a030007512100c2d00e58240789016580020244406500000000b6000e4180355054019250480c541c0e084141008584c00030305403a03103d02030780a400e421008108003d00d080440c5210660001c20030010709042c0c4948070060284c00c01c012400c80700109403898810105981102401004c1c05e26007005006054030019001b040f0007000a04100c0310640c84001e80e884c3e0303402c0610310440045c410001e0700e5101e03550b039080080d003 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 689065026 1250 689063776 689063779
    0x1706010f120f1e150608012d120f020312090109090e100509010519060f0308030408071208010e070503010303091e0801112106011b240911030d080106140f0304030201020405 76
    0x30080052886d000301000c074183d80d0484a03428840f200100c200400b4801c0350850409420080070008415869103c50189180f25111046e46904503004061800440280840701c066040009908985e0414484001c8a900700c8005c2101040c0c1350b4040c1c1001000c002d483c11242c2090204261860190b00c0544260703600258500d101e0b00c1c1d281c0310421143c2c94014201c02c80940c09090004c01e01501c043d42e8418400e0103098131b408010f44d501c1300082c0c292200000030803240001407040d0b600500c496a4028410b283c642d007950314607100203181664601c60040d41e588155000d66038191f04901f100d014211a0000b809540400035020078a64061a03070f841c003d06190100d280803614800c203290040105a65403c0c4214500c1d885a03914030782040300729111552403840d84840e0f01511a030002000160303100041d101002d0030040b0360341080300c4090f4800d420034002811510307003218140d0b05440b254602074401802e0b000c840c03241c0c4c1c4900c0324001800d40300413007003004160b0b0540080064410 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 689066276 1250 689065026 689065061
    0x3030f0a0e0a081b0309030f0105060a0e060904240509070f050a030515060a1a120a140c130504090f060e031303121704031706010f120f1e 61
    0x100c00c0a1a4541d140b042c0028000d90081000c00340e5011044042e02c40400058280c0789400c0504000a2a014800000007441c0e5154001c005240c644840340d04002c0c00742c80711008280c940b034070001d110007000900040c200610120100011002d00f0241070303901d42d043d2010002800c1c400680c590380c040c2d034841c400a13072040602c0480c40b410401020380032641d001d401401d0350795864000c1c2e101000c0081040d6001500b1540000f503100606103ea000642034003200750751200c03031040e26000c2c18402825188018244282000145801c40007241c2c014090007400342ca0701c131681002440400c0c5a03104640c4542804032100c11300000b8032440921911031001080204420000c1607100d00444088440c580444002000480c4502002841c031504c00d1030125910802c003c4111080b12054030141c00260302c0402400f0321020311101e003034100109080a180e01c2d8078204008020031102c0c80751003c15901d800c00341c0c1c542c01d400d8110404548010403004c035a881c0b41c4090f54010800e00110810400 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 689067526 1250 689066276 689066291
    0x3105040b070c020a140d08130821090d02011103040b12060d0507140117010611070801060f031b0503060c0c0d09030b0402091015020115080105071b050f03030f0a 71
    0x501500c1c0da4040290b01518070180546002c14601d4861101490ba540011001a40800181f1804028040b03208040140f043c10350030806802c0c6842c007041041d11071841d01c1200c59072a51440c030152891034000703d65010a2030400d2004032191141a8001e20642c840801c01041469810000e08030800119500351900e46d9407034104014000500405406900041801e20206201c1011000059418144035880d140852101c41c40e0403026440780001864030b0050300c55001c0e09100c0c0d0030042c2a048000e20031142032640401c3e03100741a100c01092000310306012030380c2100e0341500500814000b0141c4403036203400807140788558050361074080c06005070301c0340c00c040b60300411590b4192900940140120b0380d0340c2d070a00c5001d21007e4440007040d1541030f400a4a0381a810313052003a0780c4141d0000c543d1144a0510007030000c2d05400500b40c69040c01c08101c3d28a030300000400301707001c40c0d000f0341c0415200390030410308207448086045840d0000008215403410032080523030260b00c1e42c40003008102e = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 689068776 1250 689067526 689067541
    0x302010b04180305030a0e0a060b131a04150e0f060901120b0a020309011503081c050609041b08030a03061a031b030718080d081003050a023105040b 65
    0x9a0080d480c410500b0070081255001c03900c0340d80550f81c050700001001403c01454a11307585451814003045030080d403070384c49441075820480841c5d290461410004e0180d5045048135003100342400d04e45034000c0b41d4640f080c0940b004c80e22052002001d10409040c2c0d00d00f40f14001003600d010468100d8041d2448400001c0d08a0540c65130b094a25004805241c41d9102e4140100c040d5201030203070655503484504065241d0200940070000b10301c01c140c40d50790742c400710340c00c8018080c02e0060308000514040401c4820303105c03821000c3d4002c2d8041a6088a94403081c1c000c06418142c3d00407242c28400410320a882d1381e050b50242060b545110300000d00101115050b1110740b02c2121641c60070401141d820703861558042c0a140c008a5904080c005c0081580c60170207255030300da101d80b5455004801541c042c0b5000700c80d05401c01000c0c428051100d0035915180d0341d85250714030080c0a40443e501c00d802d50040158200c030316200c20300c5140b80014850030004013512040d24243d030300d8074000c000b05130030 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 689070026 1250 689068776 689068781
    0x16060209040c090b040e0c07020418150b1e0105040b0c0303101505070311010e0102120a0605090412080c090d050a170313020603090c0d0f030e0f0109350a0302010b04 73
    0x71909103c0c9918505810240043d06142021f400c6d10440c21050001100503592405080001e90b00e03280204010700141c10000e881d09180f1106041c194a080003141d510784074040203040707500d079542c00310885a503481c004940b90b2240f9880480c089001080001c00c010001c0003c5000f401400380142c600c40d01c0e850294041101c10100902140e010041c0600007401008910901c0f056800001445101c0240c5c090a9900090f00401c510f081041001409161407040d0006010300340c1d091034042ca8180c0d074244a4003106600041440440000900c3c0e09550404070f40d4004c101500400581c4094a40302d0703558203035401c0c1100c200807036407a1b201191040c002602d00c074034100c8804400d4049250280301256102800c40d280a00039044200350395110359182007400c034400c61b003603240b100311814010400950521214400d02140f200c80515a90041030f140c00e6031740a0f60101020a4101d80000004a00003004802c1124104401514110100380c00d0006400380d0024003107035040c4001c2104 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 689071276 1250 689070026 689070029
    0x21509011a04090c18020a0809072d1d04211b02010306030605010b221a090d0c0305100c14070b040f1e02040b03060f1b16060209040c09 60
    0x2040c1035166010052605401121105004c3c04548800030f8486001d0404079542c1c4c500e00425030780001e01c2c020040da011780e80c141d00c109554040c000302414010180101c25200b500c4c0d4006140b00c0080e0300501d46010742d0310b0010704498184044000d040391108803509021102034034481c804452100003049821b4081d014407000340e546000700b91085002005400403c9404e9040503074503039020000031131b240b040303e02070311030b01808235140c07607408907070707840e512030b6484030072400207440004001142c81d02001490540c00752111985550455002c20790340c840a50000e00494410740001040c4980890b20041c8056465000c0c8464107503810141d8503051480c1800c881d480381040716901091a000a90360418461003080c20044600c0e2101c40e240c44a12a94200b01d11006401900b1803409200380c112212090700a400240340c180200c0c068400010461860b60f04071540c1a00e15020f1141282c0082c44036401100c122801414410002c1d0030191609000e6480d056941c0b550741d005101000 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 689072526 1250 689071276 689071301
    0x17060a06080901020417100b030a052107051b010e0a0f0506031b0304031d1c12050910020105061c080703050c070f0602100b15040306180209040302150901 68
    0x2925940341038421a10104000c01c0d92140b07560a0002146140b20500d440c018000c00000606448081603006000c6802d02a000d0303200303a001da00304100080d004206840440c884071b407020f1a074102421508860b224108009215001d003007034082400c0b440507a1010282420b0740e911540c5201e5400307001000c8158041c0c407461040003201085039143c144000c50703211240120341a1032040204144d0111340003581d0841c0410311440b56000c501021141c01201400215145e000101c0b41d047c0c0300d020003503101c00c090001e030340d00b5000103042d902a104680300c042e4040d207520a85400324030001c5c000c2c6001e903500c17845403a0b804860f032032100248129290280d080641640340c00020b94041d074550380100c2c800200c070700070300200244c0460703116400401000150090f20b0703070072211980d0718100c076034000209106141004c0300300c220041e00c50903941030f00c0e40448000703404041c03008000700800a02c2402544215460100010580c1c049001d0044184410807a2420303203402c0c0300c050a8910955440 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 689073776 1250 689072526 689072539
    0xf0406320a180f020d060c09080f06010b031801091e06060801090302120a0c02090f1501030c0e040c050702060d060303080f06030d0c1103010e0304140a050a06180b03070f1706 77
    0x200d050f080340610390300e00c003c1502e1400e540300d980741c00a40703070309054003808030300c5260742005000f0092180140031202039010781035640c1881ca00b245140000703880e400361060900210f04c1c0c1e03201c00f54000c5208a8001c2007800120003030310701c400014400510200c81090a00b8000503880c4014082d4240183c0d164001c0c0640d4400004001050f400049400c010841750b0354800c000741c2c41e4a090b0780e008000c285501e40345460800803444842010381030b0346041524060030003846503807140e8000c044500880d00440c1d603407e80740b4221028040d00384045e42c0124009480b0301c0b0b103002c60780b201045034802e0300c07124001d42d00c908a503079035854211406605600100310090105124081e036140c80da204540c501102c1000c000071a0850307104010050341075000007414419829000c245004908088603000348403400c01011540c4d04981d1b101300340a015038115825298a4004110005401300807100c54403860010402400b44000d0210800811280201c003020468201d2030726124280c0078000 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 689075026 1250 689073776 689073821
    0x60801020a11012c07090e030a0f08040b06130f0f09050c100e04150308220503070f09050601050705031c061a03360c1003060e0f0406320a 61
    0x35000140130700e0450a40c94003520300d021400c06814400e040300c040c4031000441d1203241201000d41884201d140880600c2011400c100014240400043d4407650540e0366201301c91003038880c4805454456080e409590402519400c1a01c80742c0c002c0700d00f18020021144090b8895040c445543e070710401c0b40002070181180d4607118242030304000b001e030386041102c12809580343c8940d54140c010780146e01e020090a010300710014151011031014040403405450300c140b51001e034120303140142c032500e156070391200c000a200d41e02030000c2d556110b410000703aa0781c071b01c07403c00c8140080c40305a00c031403d11850013030049001103007013400c8440322410f4a603040c5107884400181800001c0190740c0e0000300c00c1c1c00c010415404070701419003049180400201035035100c9904020400d401d42c0784c1ca60826142440c204060101c40c03040075005011070040f21003030b032241c0c18020050108031405420800c4050941469500c60002c50400040b408100c45000e450b802001c0090b40d1701d00c04548424080200ca = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 689076276 1250 689075026 689075081
    0x21c09240c171201080d02151305030307090e0903090a0618091508010e06070c020d0302032101060813031e03090605090c190501210f060801020a1101 66
    0x815814258080c01d10030305010745591120485029503041d20000351011460f040c01e8a02c1c0c03034145002d403070300c0005440700c04a01c950080d51102c5400ca049886e6402202250000012683c0d002c045078104064031b80e01c7c40d1419015103c11518487d4400c070350000d400250390b10340080140c0740800c100a01c3c0100143c1307800d0048070204041d82906c61960001e1200107a825000d111320000c1414001c04002c0b032074507000f221030868814698082c1a038100c10200701c15907900042c503d81090381203400004c480c00d40c0c1022440c0d40210503480c108516a10b0400240b80d030f01140d468107c48444da01c400d05030781c48180040d03040854500050106001011140c01d103d1101c01207241c00781245400200c520031919820180c03202a11401429007011a01d0840c5040410701108410110242d200c09c141c0740200003041c4000120481c00d90b014121140d421292290b0488007108200d10400d1148070385905c0c60034000c0d44242011404038886404040742e01030b06010709024a1103d00c80c10342d4095042c032 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 689077526 1250 689076276 689076329
    0xf050301260d020c0a060c32010504050c040c020312070f0e150a03110304050c061c02030406240e0a020c0106030512030a0b0409020d0201030f1803021c09 68
    0x807000100c9190700c0e000d04241200c10018031000c0c0c01c481e0f0003825000d818100344110031060350401030030021925149030202d520141814801c144842c41c80b0040e01d603a000340340d041d400b194038408843d42000213020900c4800a003840341020200c0302080078500e610b0040ea603074451a100042c0704801000012841030044842c440101000d05208280074070210000e806448400048901060041500b60015a051103075603c0c0c10303c100c07001c5256041070f131201a5182403000310240f040c2e07000946400300b5103661200d600000c00c8040c0564581c2030918094000e419865021030b215440c2c1214144000e009107140c2c0e0413906154801c0e5011f0311f45400440103540007104110380c964843d400000007903001c02a4624050a91070056241d0500840c0d440642d40c8594119105a040c40543c0d00903a03680980201c245909003000906d404103c0e070110080d00c2031810384400021482180800e164001c42c0c207011218a00420403069030391716905403103481c07940c09101c9000181d0b000f514541c0f001107 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 689078776 1250 689077526 689077559
    0x30f030b0d060e070b0c122101080c010212090d024f02070b07050d090503161e0b0105060a05070b100503010b011d130b0618010207060f050301 63
    0x18a00810a500d8020200d0104071644004070b82a0359500c840040c1010148001c80152180d5141c0c586040800580c0030781c0c4155020444c0303410702d40090051500902840c0d545101a10031f500d902d074a40c2d40da84516211f46000400c10302600614a0b0b2036002e03039071801191040329004294582c0000550240b010103102440c002601748041001403243d04a280884144200e801000d2040e02c0e40d0100e4142d0902505100e0520060050041000080044403a46e030310407160f1404584907019100503c01610b28a00003500c03e001c0014020b05142a900c3c3c5040c0d4207000e00500c1780503400a40c0440020500190040c050342c80380d10040c03200340303404d400402e00c9800318500319081401d2a01c5c0c0300340124094031135150340000c80350b08000e00d003402e026445c0b450009003401040380d180c54034151030766076520440c0d078810040502c00307242d0300c911540803000840f0040e2800b91681800b5401c600300c1d1030700c0b1800c01c3c003500c00c11300001092403060b00e052949002e1907844608591820303e024480c07142c3c0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 689080026 1250 689078776 689078807
    0xa090b120a0807030f0905030a03050325050c01061a0a03090311030301060306030b060306040510021c110301031406040f080f0c2d070515070204480c03 67
    0x101401158800d10802101041900400200b039035100246400f0344000448144a4240302e40240300300f12581c3c01090180e030540c3c0604010f503480c4c1c0c41d10000740f8807203803144000e0702145492001c1c501241c0d006000d4000440c444008100c5a5110b445d41c83c0c607103d201c0f070600b0500c40d003001020b030864465044045114030074100448450504501e150540c0c200b42c210310700295540340c040061141711105140c0101042c0d011b040e4a05182c2c9400b5290300c3c3e110075921082ea00020a0801140181090440c84802c03540400c05416102d12143c0030790300070f00c802d40312503030b074408407107401c2c4404038070301e40640da111000c0c01d0541810b80d2840c12541182c0400e02010030148000001404240301e440d08444400400000340840c05070761948504000c03004400301d5118040a01140e02d030060020281700300101c1132500e0304501e10000e0050300d0b94281000e01c0c0300d413183c0a4044c0e0106030b080310109010150045003509010400c81500f088410145400500300d0411500464010541404007080 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 689081276 1250 689080026 689080039
    0x903080415020a0b1911070f03110705060a05190e130c140a03020a02010e160501180b0c070f051f08061306080d1d091605130605040e090601050a090b 66
    0x401c1d8585440813038044500030b0b40d1881003894400248010b100f04070f0100c0c140c81066040c400c140d125241c0c4241100801030070f000b660604145004820030020008190081500742d5400c00140b0081058000142860040905030b03c40c5c0f00040c003c030321035140d13450050000d41e02c1140451050016004001502060101e100e55010f041000c000007402d2040c0c06860159940000407002400c44100c8122030000b034000701c00d031158880300710b00e02c4000c4a00928007a0540b45540c0005040000f2950180c020420000b40006210b00301250040c12030703216541026819541d1003c0c411035aa8400c0700038590b6000a0020202d2030244040e142c01c1000a0120091054641c0030308003151110341000070154000c001d001d815950185625001c030441d0107800c055803070402d021a1030242c016004600d15130040170a0500c0a10400039a11002d4400400140719584c2d41070180c4198041c0c01560040ca4a007000190550800100d4030304841000d010141c2c4d281c80d000402000f001c0b2038544952060 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 689082526 1250 689081276 689081293
    0x60f140c0d03090b0a0506060d0b120d02060f010602010c090e0903090909010b040e07180504020607120924020a0204020a181d0702060411010c1e030809060601090308041502 76
    0x80c0108a400c10700640d42e10001480340c40780c01c001d410140001d1200d000b0741d041404008640e100d0740c00f65402940c2a580c0450350300d1880d00001d200d0090803400c01c40920541060300303100c42c0d0000d80203004280340a6180040c8e622200d00701d0986006c4004180400e0301c850003000010546034100d41d00c0042c210079a410a48000000344a07803005459024180e91030700c203100001e241500c07503021041900c07070050078140c1c41e00103002c81c00c0306903d42c0c40b204503035201c0028003551201400c072904070b030340103141e004900f41c0103202801c6603c0e01d000390640070118258020810034100700304041284e0940041c01d080b622542080060f606c482410801c0005281e5804680e00f0410764400c060b0650b8040100c502c00e80c90150001400d005086008545c411001d01c0045460311360910110303502860114042012810021014500701c20a641c6c00080b0400030010f043d030001c5103a018a122400f41c6039642c45a4004694105041c04094620441007001b00140e951125082c6006003540c0151558036 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 689083776 1250 689082526 689082547
    0xf01030f240e07080a020102060118110d02120c07021807180b04030510051306050c070c14040e0c031f1503030f020f03030c120910020a090519060f14 66
    0x7119848070703003100e0980720280c2c1501408140480070192034140024204e040036500000d40e00c0c03406110b041c111016080e1a000581400d400c49011310101e40580c5541302003451452000794070626410710891a400c2c08070f10f20b4620307035044410442d00141404d0200840c040085074040300a4500c1c030602c00d89580ca00d4100154640490042000003040ba4845280d0706020707080c802420004038044c1d15240401031031015144501801a07008140090117541e01c070450082442401009000040d07a241c000601c000383d00390a50101209a43c1400080710304098507941c0e00c0301c4540e0307a074503803c090f1490742c51075204201c01014000c0c800000c01c490410b9411001003100a40054000801c0355000c0c03c039950b01084010040182000210325514060b040c1e405a40a2130a044801c0c01010010622026080150365500300100c1e40031569001d1966000d00003645a11074030b800380c0c1074062540640071801c0243c00c2124245d841d440e0b03180f07005440442d411495012101e05004041c0b1603520310 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 689085026 1250 689083776 689083823
    0x60f0905100e060115050a0c0804030204060f170d02060106050c01140403170f070c02040c03140c03150406241103120a0e06070c11060d0f0903170f01030f 68
    0x440c400050002014581c1c10b00380c0b400e01070140c00101810034000340d1a001254858101c0725904114179009020980a02d8a26941c0c41154006544203042c104003051201d410a4100e003150b4000e2182040a8100002d0380d849880510712480540c114000402c407850142c0000d002102240700002101030501c8400d07190f1b083c05a60035070006020019401070105000200e6400c0f140590b0294450300d45420300070100480754100900450310348070201030f92402a000a0322101e420035200f5070701e00c2c190a502509400881c0c1d04480c441c020f90101489003400d200e04002c1d58000d4901a4010264505544610a08080c64410000c0b50b144110541c2410700146c901c19806440985460824800020680e09102952181c80d003000b002d21a400d600070001045075640098100e0700320700b2443c00584203005241c2c60b034805505200000400e0031569200d8620b0314402c2c1c68010400c5810b14480310065012a42d035010070541c90010302c0410b48207500401e4140c400c1c4100000100c0105180c1c81 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 689086276 1250 689085026 689085043
    0x201020c0f1503090307030f050412080a11190512070c0b03100503030c0105090d09150c08090d0f050f0a0807151e02131406180d060903090e0a060e04060f0905 70
    0x344da040030400008055114014209060b018a0700c0d40c10203080c01901030481c03c070403034020801400001e203006128051034002601180000c01d40e00d203500c1001c45c00101190f2040e04072000d006550b074021600c103424090f0389811b034126201000711420068001c2c0a503001910b010401148001e0004641d9010001440d02d120000004102800c0c41c0290501d09403840e03c54005112108a003071100c401c0461075081c40b558285010325440c00b090030010b07994800c4100b016003190100c00e0260501544d220705080607442581150810140004050b48400c04481c1c0184201d0b4208550004613120714130312024018414400035051408060015440704200101007503950003007502c600b00c2e10601c100d90b0040c4141080031482185410014480b032144180c0c98042028500c185102c40c3c50314903a00505692050f02040464020304018001884c2440b820516440b0031000480141490060307204440c0f030741414903c1919959100c0024082558140c0803c950b03d00d020030101f00308015041 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 689087526 1250 689086276 689086291
    0xc01031a0d12030605041404021309020a081509010b0307061103250b07020c031c021504080c070816031401090c090b15071101031d01110a0305130201020c0f1503 71
    0x42c180c4150b8002034240e61555010702d10451402ca0701041c142c1c1229081640b00d541251140441c0b00050381d0000100351030800650031004448000ca1094400181020340c10361002d0b034030f143c0b60344401a1609841342e80b01e0298054224000400c162070007452100010600003003a41c0c2031405802c01c0704440e82c844142c804560b0b075011801c0d410711912100098200b54180301502c281c50118012a54035006002e807002030208224500c55118400d0122a610010039104441d09040074104121941c10102c1d640307000b8011140001a403c0c400103500ea07152003082020710200f0701d152034420950550742030300d81565488403004000100d81b964a00042c01c4003078000140102d410091091400d0080c2c4416840c02c41003145e000464074249403c60706940034a804127000d103941403030316040c0c03214003400307002c542c01c1050000b02920401d014204924007a9010440e69445044044d0709080012010f4003581000c0122501400d00c4a1031064030400030b09000341c0384030741c1140030302580e00c02c0360001c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 689088776 1250 689087526 689087543
    0x912030c1b0d171801020d0516080403170a110a09060305090307080f0c010e030c0d0201180b0a150503030a18060e0913170412020909010c020c01031a0d 67
    0x3040d101c03010750078480d0001100005140110b000c030700282000e0380d2060340c81003c400c0d90740003074a2800a007030488240700c030b60b40c000d640300c40c0b5a80d410006050700756090207011004d04120504588140401c0344520b40540d0751124442260100320700440000c0c10840400c0e844e8500d0380012543c090050101c01d64560751030882d40d143c00f90060840742d02030030300c800d5a00204140ba001c50188003d03540c0781c0d0302d640d10711503480c2d150018050040c40040781c2c4003094000803a45c4040c1203008139004488241640081c0308072400808007110031080b0080040c19660304002181069401e40d0054140d1004822400e191540b6440041e2a54110b25030700400201405060380215a130f6a9001000304440d00b060080c4841c0030b00011020200180703c03280c00040c910401041c0026003d113180c0d6100c103a030605076a0703920346400306441c00d44224146c0c00740700702c800401c3c0c0508d0148180d404498203603001e09600254000110090881c0710107280f2400c400a4070a0a40d503a034040980b00c00d403181601 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 689090026 1250 689088776 689088787
    0x16061503141509030406050d0e150f130201080a0207020411030a1509020a27030204110903010534020a02041b1b02150f0d050106020d02010e240912030c 67
    0xc1d02d0100210345810b10180381c2010300094007000400d035810f84000303051840c0c440b440010100010800144490964401d50070441c00403410030300b040f070141d8a08030703900c005a900c2d03c001000840c80c1d10300c000e001503400000156900e441e540034005d0325100a001003078078900b007a40e420361030b003045e6005100299103028203c588100c10200b1402450111030645c18100074220260851403140d0301600d442004d03200381900000c081034041e001d940e000300b0421020801e9030984c1c916800c8600100c1c029031034000031400c070103130364400f698810040e200a114001c1c0010140050900c0341c80c4100b0561082070002e0340165154094a40410a40030307010042c2050a000208900401107a40318040c401d84071400150710741041c1811410b450031300340d0355a01c85107034101d2024450006501ca8103860400003145066011a1500d0520020341c02805108100301d102501c4e074210122404801514800034100c3d080c1d40c0700c0c1550301ca03020100753f8450040800004916a10880c3c3e070035510b8500103803 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 689091276 1250 689090026 689090063
    0x50106020f07090501030206090402071a090a020f030307200a0504050901021809010b03041106040b0d0e07051c020f030f0a050c010f4b0815040203070516061503 71
    0x26500100b29003c0c2c18881549560003140c1107102d08032160740910780018900c014069006a090301c00000250b18110501e807500d41303103403a072550b000300701e214504c4001c40c3e800300e140010640c0c9070b0b581c010003030035100b01400e10401004152490040d8019100400005881e65030741704907481144844009a624080764070500c0c1c100e1200c0b56034500c10460320713005000c03460580b0160b95000b6440420001c110400000051050080364010f072100440000c2c0e221000021f42c11103c00c0d041d0b80401c40b07007111b844008204030300320340101c201003220040b54004090711b4030142c020880000603080d142c003501e110305c90300e00300b41d06180c041e00c40d5445512200401d50b1302c18035410942c0720901c5c01d00c004000640d02d0010b000408004003040490700102600a202107801c42d8012040d42182030f030400b400342c94007400540d0103c0b0312542000c9006280d85103800e0074005c60388075038541c0e500c05280c41d503100001c45102c0e41c80081505d80913542c020581e60a00e10406030070245004110341190b540c80e824 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 689092526 1250 689091276 689091283
    0x2c1e180f010603061211040615020d1d0f09060a1a0c0601060804030f210c0e03010e0f06132f0415080715050c03040b04061209030504180f050106020f 66
    0x2c1c00641003500e051070400c046084114a00601c40e4020910b01802150000140140c84281c06c40021170700301072401b0032407640008400440c440340381c444000d4000e00c50307034400e108603540e01d41a40110404034001a14504130300400c1e4031150041c41b51102e1070316604844200301e44a01503d030a0306001481c0b042038081003010500402c0c00b0b20340300400f0700d480e03079001389000040007841090244900c5203094a0340c2c99031800040c8038000c03001b0007090300ca03950010415040034068138025440d155403a80502004614180b864101c60000c185646855a8000402c14031701c03800d8403001c03e03441c012410308a08081d00160410a081244844100c000800040700d00051821030151140d07a000c110324500480c00d070080b168988011889070800c00b1095031188510b10f03101e403207400001004105418904040c1c010307120700342d07075149225503084109000c466100101501103a0148420400c940c4c81c07011411812045c0803010400800c00e0700303a42d00f034a10a8000c0c00250300300d0300304a448400b082 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 689093776 1250 689092526 689092529
    0x40b030a0c0912170702010309021806040624140d0c09150518061602031020030403080c0306040603021206010314160e0c0405030a122c1e180f01 64
    0x305503d106011640c0d2000302c40c076690054450501800320700041568001e500c5401400d4018100e807064901d5508811500981224a1032140313190440c0402c04280130420822207a4004c0c00c00c3d210260b2420081d40c2d2b2032800b44c0c101140f6682000946240078080c01202c0341030140d612158074443c03e0403001c80c03040aa010307142d42002004e0003450310103001080c004a1a90058410716030300d03520b040c0101e454040c91000030b03400d8855148030441d100000e0748054120082003403001d1407601d61500e038803410322065401400152100300481c0703442070a1401540c02c508010400592203a696000c21840360b404250480690000e034010414400282c894030b46245455001e090100c110040d2020018214054684100c40502c0002d03444140304c4100c801815008085840e45640c0b460407080441c0d00800d1840019001402034000d020304499000d0029442c2000701501e4207554240400b001c11401800541d22241482c040702e82c03160b10b004051011190704030a054905142c8481c140d9206 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 689095026 1250 689093776 689093789
    0x5070312050901021e1603150c140a0806030723090a0e0a15020f0309030d140609071101091509020a0b070c0b0f090604240e1f05040b030a0c09 63
    0x401031400144e0740441d07513022109503400e00403040d035001840b2615083c1140442c0b00072280480000c0300340409686003041c0002c0540c000d20141411100c11103015111a180d0f0950602c1800300385c0303045004101c55540070714050700300c4007050740d5945680b510a030341c0c00c6040e00791207144003540171a081c80c1680c60740c030a0301401c00f17000c8003000501480d0349a289036805000d41b4120104032290114a170100c2e03a58688044182da00d0342330482009490341d0000c00a024410318180c5180c15000854440c170380320b44801002d01080c1c0c1c5e541e04040d9031445030028480b0440d5030700c0c80554002001c1c480c24802014810800180969583c03040c40010700303440d0480442e0020074420440010500701d5050103464820580503100d03e4050501e0080f8002c0208130780e0304c0b000200740400d100710341803011000d060050a4100400103a81c205407149161100402e40150100c40c004413440c40c0f0110707240c018002d0389051880c00d40c0e910340425a41c6c0083d507400c55040c0d02d1300d03040b1304507980c00428070014054 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 689096276 1250 689095026 689095037
    0xc030b06031218030a06060b0306090109150e070c0c0608012d060e1801060221130306110c060910050c39010903080a0e030c0c06070c080a05070312 65
    0x10b4201c00c48580e801089034074144080e40904401050b20203001500c59154421801d00030f40b62554810b14103508112031260007416840c00004002416001e8500b59007070610b94180c9403400c1c003003240c40d000340081c602014400141c2c076600000d45040c104500401c0b241c0d40390b501950424601c084001c140076440031003014101921715011400d115030404440e801d080507041c1d151f030300e00841c02c0c80280540381000851400000a001500800c84013460303c0d09440145402e000c2a0541c1c650703000b0a1104c4180d130403541002e200080b01540300c086d13034800e10355003907040018a0b000315203880001c40c0e0000032034102c01b12000d1912600e00606070400c007003140302405c04032030b40328661640600c0e03089080c0801402e03414800c000b42d00b001780801e10128100900c018039241c00d01070094a01640c0300c26002d441d08407440d01024011040c0c0703905403e810050001c01e040b40040280c40c3c0c100c00020388540000307180004002504200b141c41041c82030002d4400713a891b5052082c4400c000c0c0c08094240311 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 689097526 1250 689096276 689096293
    0xb0f1e1c0c11030315030c03030d06090f020f0702040c031b09030203010e0601032a090f0c0e09010f0b0c120301030b090705090114091504021b0c0d0317220c030b0603 73
    0xc0120075245c0c000c0c0f0039441c2402d05801d85000a1030f025034401c6030780d051700001499002003441d0360044403c0c3c492121090000c03017041e0b43c40e4000c901c01d200890005502c18403605006190076080b00302c00d107441e441d0108109000d0580340400c00d02c22220b171404074003001000c00841c10300b80203c0745110014009002c041d8995111800449901d51250342c840b0b001d0600c40520849448444014100401d0104410007104007550014600f0603d00000309120007040c800918040201a05840d42081c1d03418919240c9140b06985030072142d03641d620341c041d450350a5607818822000c1c5000314029800e401d403d00f0203461280c2441c2040d000603004044510040c07284088009060000c0c0109496001d816a14151054000d150350071050364401e0000444526010a0500c0c80c220080101d00341e0703140c4424002009400d04c9180c500901060528554980c450b1085c61201d030300100000050040040e01c2080c0c041d4030061000032241c04a260b0350510520400030300c03d40e4002400d600400184 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 689098776 1250 689097526 689097557
    0x20109051005041a040f1b0315060b0406180503012408010e0606121e0319020105010509010302060c07030b07083c06010212030901020c0c09010b0f1e1c0c 68
    0xc140307400000003501c03a0f15010030b0030854650000000e961f0050110200035812003602c0a14100b20700c001e07039040440c040c1782040760180b889a0710880d0110082540f60500d061000e032104116213051000c110030310600003234161400e0107030540c0719100c1c40041d100035402c0326a50760a140c1070f41200e00941c0c905881c2c5400c0308400a1050741040007201c6a040c00c049858940346465403013804240200043d10540404010000c0a09001c00e0140401c0c009820028030032802c81c1d00c02d100f0554080840401000035042c550014101c00c2e000c641940c1016032031352550010b03c0700a03a4a800050844c0c8204100314020003040003000c08003c1156220304600c03107454509a40c003603d40b003041e10304400850a543c4c020416003030110f01800c074143d160715041041c54000e412405442c003040c00b034101b1a0445107400320005051b500c08521880c1003c40951180e5100e0b0030200d8050b898440342c0a00490344032440c0081c01d080303000c4506140c640821f4800600603981c400310100f05004a415040c2202c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 689100026 1250 689098776 689098793
    0x103061707060507081903050121020904140a0b0c0903011a010c1403040f08010504050d020f0307030f0e1c050d03020a050906030a0b04150f0602030406050406270602010905100504 79
    0x49071803034030308540c40f0340440c00d100304544201952074011010b00000e1b0301c0203541640156041303507c901035204a14442880d000c07803c12040c032000798801128400600014118840c400805500e40101c80380c1032920340e2a801c00b940b00391180c015002e03010130341c4443ca240901896454140c002014003039001c001c00040c00c0518070400040040000f5043c008400b0350070020303100200b0701d00036254105039a40c018a802420180d4054482e4011906441480c600000e01a500215450015480c01c0b6140e1421100d055034107070060208510044c2d43c044590f5607059221140b00420041180f81c00c4c2d62821518000d032005405040c10300500c00b008803250840251000e5410a0719103590701c2e41e48101f00380c010004911000ea1040ca414114403c2044042c4000c0940e6140b51003d4801c030740f601d00580e5240110b100c0c040c0001c0d810801809514440c00d40c80c84070b2411f50b804403240c040140d120040c6800d00341c0003174006170346d1005a4400d01908008096412481d2354080256003401c0d11040300 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 689101276 1250 689100026 689100029
    0x10302041a030a0e19030305060f0d0f030309020901030308010905150a090e07090603060603020307352e14040c14030a08030108100501151d01021204080c0103061707 73
    0x18044070202c001080343c41c8681068504c0c0d0200c6041e80c080190200104050842e21442030740040c0c03910002503414145a008800051300040c4842080c400690358030228411101c0e04404058480d0320360001a1504054903001c1d40c425201d503040d07981829540411103000400340341540310314030070300032503901d07845016003d5800000000c0f5400c80c000c5401071411407250b000707140140c60050300106200540c0c0c0074006907842102500c0d07055036141104d800c81046031910844002c10003694000c82d64105c140002a54000c0003540c0900700c0e107610881040114041c92a109a09a189002c002c02544104410310400400c0b186040c20309882d0b60300d01e070f8040e0140c4030300c2e43e0303400d4001031055900700301c1040c000e980005c02903902e40e190b504440d100e0440810340c0c400c807801e1000100300301115121928040b80705994101c0d982c20059100203d0f0b1006002c45810350180304042d6074030245070030003000900320520052629812400c001800c07074a1650091003500c20030500d0b181c00070408540a030 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 689102526 1250 689101276 689101319
    0x209090c03100f140f06030f1909021206270c090711070b0406020d050304200a080321070e03060c0f0409020c0a0c0527090307050607080f010501030204 67
    0x192240c0d1003068011800e4203942045400d60700f4600c0018044002c0030425500c2c95094410307940b034940382400d12403a0700054820001a0b0010400900c0710f4140f040d201d111a980d618010079658020f402040070860100032150254106004000495101c2c1a80340c0c402c2115402c050a1054041c0c07000b5194041420014410001d00010800082c030921002440640030300c2a508407036512040d030703003103640b2602c66080940500c041602c0c0c1c180c0035209980c8110f400c0007005042c00c8075050589010700115050303641c01540c3c14004100d04104201406c098604040215164002405540c00d01c800041c9004200050300d156200651404102c05130030242c0451855143c0c07840740e20fa801c01d4080c940111200b0340c40030400320340000c00052207002450043c05034401c150348034400d000032070b400010841c02080281c1540e14545411081031640000298184d9050000d41e554403810440140c1c0c440000496250601c100c0c02c90780700485005044c02d003411480c0616124009400b10485003050 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 689103776 1250 689102526 689102551
    0x60604120314041a0406090e01140409051005070c0b13020d020d0f0f0b071e050a0e04060f0305010903021b0307090504020105091810090b0a03020402070206070506040c051201020909 80
    0x3640000e1210984004d4031600a080c030685a60241c002c81542003445540c000540c0b80d0800a500c0f034040c80c42e82d0503220014000d20a000c010800c0c01301a200006040740d06229500b0168070306010362181a00448840d038854580b5409824101c01450001d070140315240b988900b480c0060340c0e664400742d9a15815140403595003c1810300004010320181c000d444901440f1020040040e5001910300c1403040362a08070440000203e40e1107043c0c0d03180c54520102ea020091400c07158003405ca91501c44800074400b15200d5114a40b4440001c5250300c00c6030f917691151b092030200342c0c051041204100340c40701e10702a81d05105002030b954030140d12402510b0740d0b0303541c081025644202c080710614080685000780d80c00340100410400c10044984100c52410184081801412030146020440c40240070312940c50171a000c0100941c00342034101e0340244100805000280203004c2c1078847c0d4051240d0000791440d20061085882d850300500c10a41d00c104440c42040d0703030b900700440d0000000f0318030 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 689105026 1250 689103776 689103797
    0xb030f030d1e0203070203070c060804020d03110f030f090406082a1f020c040506060c0a08090a0f06050301080c0d0f060504021c1b05010504030c090902010c080a05030a050606041203 80
    0x340003040540b4040b502095000104001165030000010b18841c1c0c80350666807540c983d5002c0454100d5002e4038001d601240c2c50300320340c000c41d102d10031556040d02e0040c00c7d58041100c6407046c80c55a40042501a1350400201e0001c00d03d00e482d01c14140148010000f85c401d0f8841e12400750811418850080c00356120159007100c00d84410018004071103010b101500c80380303443c1d0b03006985c440c90b400419111301d041000161003420180b003aa1161040c105c02041c4240007503482e24440e4000000e400d802c0822460005078000c1c10030b01c10700c0200105d8035007a0340c0f54100f0110a0a0440a4001d00d0182080f02e07141000284180c003140712050b0401c1c0000781c503072200e20003d5115004401c2c882c0d01500071408810920201e6090701e00c07103240050b80050b945698100540e0940074910001c0c1c140d80410400300141e80064102101d80da2052505d18000c004565034410030750050034241d000a040441041510f841d107125094002c03104691450500e46010303c4402103440307510780201042208401e = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 689106276 1250 689105026 689105051
    0x11030c0a0c15020f09090c1e0c0f0601120b0a06210314190e12060609070507060c0801060e0409080f0901110307081e090f100c060c0201050106030b030f030d 69
    0x441d25480d10b5500e0150f5481c12141c1100c9415008898100d2040503071101044d103207840d55088688206880318131560000d00a00807851a411a810114850180d0000390f5071141062000340d018200034028406081ca103030514020741c820090200310060300c1d0900500801d5084164140c8c0c000d48000f170f007840d001040c40c040710740200250390072444000c0402d01c3c4207020411440061000c01c0b07641c1e8540c0d440224400c101c01c90000c8005106550005004503180c2d0410609669022045060070744c0f80980560b41c0408503403c45030301e030b40051300401c010703c96a503109052980528084a003401900000c1e10307110a107214401810100c200c0014a4044590248407032440d182486400d6036280d40c150b0070f1001050f070089510760389008ca4480f40c520034980c20400d48250b14005001000c0c1d9000000034000700d0303250010070505101c9180030010000b17020b0300a01c04031400690000c02d180d454120041d042e00c00c0c03600607600c25040881d6852002d10300105441d1860006070012400207441030 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 689107526 1250 689106276 689106293
    0x1080a0e1528050c030a020a09180b0108160923120c010305180d0503040f140d020f0a080d0209010311030408030411040902060d050a0213060c050111030c0a0c 70
    0x7950420102401401c004108404591041688440c500c0309044030040684a800702c0d40c003102c0c0e01030498414808680410401d5001d08401140c1c1d040002416403504070300121001072085d00c0910544503642000a542d02c1005a034010f045500320702003406000038090314040d5a030042541d00b2203d00079070403116522241c80c0756800070113000c1039a10710001c0c0301142c0f02c108040d9180d010034100004103105000c660f0005540920040203000d2200c44444101d40542c0080c205440445c071410103e004102000e030307044e0680d0800402840c1000384243c001c0d0070300012000c0406150444c0c803210012900320421100d40200c60100107039545000340050f001000d080d4454444170a02004010410901d800210701550140c0f21528003040d842d001c2005a443c0e88500940124060062000b83c1d00b044d0403054029110242c00350900004130035a1451103115480364000035810041300d0184002031040b41c400e0040c01c85018034510b4400000c18452041c4041c05080000c903a80d03c01c240103400 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 689108776 1250 689107526 689107543
    0x10f09051903050106060509211509011a3703060e030406030e030f12071110140a0b010c080703020304081b010f11190c0b2a070501080a0e 61
    0x1d04000e5003990940102601d00001d010448081d0300c1c1c241c020030301a0080040e665200d0005001090b000e00221088040591847c0c802242d885403100f09001550240314462050700014000a00c090703a48040d052016262000035008130606401b140300059600351005000291440101d10300ca41a18001c900040d00e92010700454945180c1d400c58840c0840280200e40d240e580610900c000201c10700d40303c1c458000e417100d603003004220000030889800c012a40c40f9003035082c841032201034544074604180300b0746115491990754010303004080d408412140d40140c603041042084c00c24450000e484410303406000fa00d00140458441c04140c4200212070180c01c0280c250f4045034010400c4d40d15541800c000140812034004a4445040c13042c6142c001c8504820300500100154007510140c1035050304054800b00a007400214008020318010306032185491032000100c1e214100140024592890a0300389801415003085183e910801e030030b4000404500010b40034034600c0280385000140c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 689110026 1250 689108776 689108779
    0x1f1e030206030f0108120408060f0a0207020a0f0f09090503030402120a0f03020a1703040b1f090608160f060e01050310080d090513020f031b0405030703081809010308030402010f0905 80
    0x2003040003c00d6910281412940c0e000300f200d41c2100881145041c901507802560b00650160001800f40f040d001070079501312541030001850035030180c020800c094280d40111400300c0b2144410030020300d2400c80400100b414030810400f601842c2c0c1c5242d200c0c0310182010b40709842008001e50210001d105402443e40d02c28000c02c1e02181514000e500c9242c284c000392031118080c2d00306801d012084c07007100e104070392100d12000c032955004504c08040d22604a16401034103040000309015a00d441074401805141d4000c002e0002c1e8004500151480d94002a00c5d030415814208074154120583d05000702c0242051510b0340e841da01128a000c03159032044041e4400d4800c0c44900300d40140000341078036025200c80c98080024850041030740304584180170021420800900400311800076004000c03c05580e0a180a680e400000e1810080b0342041d00d44e80c1d0b00143d03081d5590800581d030b4200c2e00702500c1c445120362440d00e1700022804003d20281c18080022030443c1964401e12208018160 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 689111276 1250 689110026 689110039
    0x10b0d0f0813080a12050306030a0f0503090d05060603060108160e0415060e090d0206012115050108250f05040209220f0f060b0301260109060b091f1e0302 68
    0x1541c0d0603e80c1d0750843c011042e00c04502d214240501e65101e07104403482101c014001300003554460780c44001041814200359080d00050010b643e50390b444106904a1a004100915080c00c2c14001c1504008040e40705c13401a61005182c4841092003541040481c2e108044008141e601c905201e20002d01c4100b061b00740d0303483c044011400c6010400f80034064000c09027111400d0807540c800340e035034203028001c5544404c1c81e072480c4000e080c090441c07000010b100e0200480d0322106c00ca06002030781c1023a00920030540141034480c04a01c44030601103b0320b0442d03500008140e103003481d040003000d041c4c06614052500080c0003c01900c40300d2012140e40165501a44048110b281174001000400b0083d404903040c242030720018100c40c0144400d64084451241c034691801c03111202600c00340300304032000340e050f50035815208401c0c4242862903000c1c1350003184041e92a400c2126500c0018103500b41200c101944580341c04641c2009010303500080016411a41c1040380e8103100d914a0348001c0d031010 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 689112526 1250 689111276 689111279
    0x40305031515030a14040507090e01140f09190b01091107140106090b09010e0a02070f05061603060603021e0f2a1c0c1506180504030908010b0d0f0813 66
    0x5000942c42140500030820064807054080d409401068a0291003070b0303c03810081c4140102584400150001480001444035000ba1401c08000043780c01c040301c01401c40802c41400014000740c1411710f10a81c00700e6600c82d2650b680007100c18180581d4490355510181c0c600148030381021580301c59005050105001c105c888442d02030141800b03034078a00c0d81000714000e041e0505140e8a4180c0c0c03011500c00d80700780c0d42c205500c030094210445c196030310380c2142d0780100803980500000d80542c0100c910f6406440302d40c40040c1c00d48140b41c0c00b40b0105807040103d590b001000e0000001c941c4080c070803259460580345450222401007980000c2c48a04200c00380701ca041e085030342c0c150410848410790f10000000302820102d20505001d42001c00d22401910300000d0b1a01043e101880e1403a0380005c103151a074014052000050920301c03645956130050006040d01b000030503006155443c02402501e00c40008111481312500004280b8074070300440d001004990b01c162114035100003200900103 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 689113776 1250 689112526 689112559
    0x50c060a0b01020c10080402190b180301050606030f1605040b0409051b16031b060e0d1701061205182b172a03130c0b0903060403050315 60
    0x50007211603850140c451031000607524100b03560f00c402c04034007a40f2044800d0b0360319003c1c0580c02c18594003a01c2c520000c0c1c68003203400f460b440701800c10641641803940103035480c182032508681000d409148107a10520411a00410880005500400041046540e001c01c910165003500442d0065813003040b0201d000708503090181d0040e071061410001002c0060580500342ca100d210fa031041d11504150410000040b0b4020400c41400c400b90180e1007185055988510b4219804865003082541144101d2000381d94040c650128000c0b5240c9090140d52616038041c05604140080544158541001440d540d490054944040b080b11042d5241c0c1c51068040000c16001030707080d4080142c0020002142d184510514400b590401d4402d142030b03210302e440b00b40c00040554650744040d800c0400341907140c5684010311f024a100c520b0056405859103082a2441019080000f0f20001440700003001e5400242c129003007909410600d580f85c403088210f810b03072149d0300012508a940301d40f524402 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 689115026 1250 689113776 689113781
    0x905010501090e070b04080c0120101d070e0115020f01051f080c10140928050d0807020108071e020601090b06030601090e15150901080c07050a12050c060a 68
    0xf010080000e8500c12503c41c0d0700c26003240502d0041215551182e00d015038913501821814001c480c544240c15000218092401c1c51b01449440000c2c201e610341c1d5154100c2c400c105519070505e80c4504c0071b0950141801d003c0e003003401e014400c0d0340036090300300701d4404110b00070b20081c0900c880c0c0720001e021610309031052403c04560340d60b03509000c4036110400600c0e2030340454401428400144203802c6e59a1300c010441d0b02d80c00307001440030001003c020754030300350b650b6822041c1c5a00e25421031023034202c8010240300159030030f6440603019070014441d02001500703000482d84210390900380300e11075488640c0d00701c400c2d9034a0b1106210302d0140221400e0a0342d00010050b040b114008028020720b107150040c482c0e03600040d0759560201c4d0302341e0824404418120106a404412400102d01904801c1c0015101400c00c455502900c103000030b11850b55684105910750222441c000030f881c0c502c159032282d56a124000c03001d0a81000ca803810400a84070308101d880200c0710b070048403268200107250100 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 689116276 1250 689115026 689115041
    0xf1e1403010308090909190b06130f0f0b060a020a2a0b0c100b01080a050c160305090f04050129040e071806080c04180204030206120f010b0313060f090501050109 71
    0x4900e4000c0c0000c1c501030400950355646030418011101c008016695400e080400a8810742d8080c086901404004040b07100e12007405583c2040440c03400e0502433510220340b07640082d24010001081409079050b0001624203000d540700040ca04800c400d2900701800c80202c4951007603c0d030801c40c0005418802c040984007501e107540c00d9518200501e010b1a003200c0120106601184d131030030002322500c00f6644100d42c070100c1d0103007080c58582c2c82d080c21004c08c0e80f1604101c011400c0032540070100d04180c20007180f24181500c0c20070455040c0f4001c40504124407c840e20458170b001c0684d00406011400d580081c500c03008a29510b040404000c0e107a0000d2400280700d00c0800f80b40040c94500c0740003020b0240c1801207001d0300d041d01785100c503038411070011241c0b6103007502004008010303120f000007088030f07078078070b02c924540c130304112103155119441a071000b40c00701810b200303100001c125441c0c41e204480d44450002030b043d2000c6000006800716240142581d403030300e0000180c05106801091 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 689117526 1250 689116276 689116279
    0x1b0d020d1a010b1204020f0103090b010803040807090e030415020106050402030a05041509020f060a091701060e070c030203160203160306050702010e0303090312040213090606150f1e140301030809 86
    0x11582e01e0341c4000f0400c2c0902201880108840700100303025007003122100f07040003010f01d80800c0e2a20252981e0714412020780c4084840c1c2d20004082105a1041c80f44201400c00c40c0b506224010142e0645a600d0155000309214204000701506400b4000d40c0b20000405024100b035450780340000700c03c4020074044030b050703c00c0802400c80b0108151180300ba04541a402005008805a07a00074031146403c0001518107000c50707174002180d21500c04491903007224003800003040300da0914802c1928544040d010a0034880320010742c81c0003e40110544820f8030741c2401560100209000113482c0c40c545062079007000601d58000b10038807480343c1000703200d22000e40003400380307500769000a030740ca100407100c501c2960408c1c0240303000020001209908580001d04008004203241c25030000c03a011a034013140c1460766081d040254441d8003030a081000c0c10381c20b0800d850302409401a0950542400c40700d054010790f0550b0420900441c2c8410340d5804c1006060380740c0da1203260040003548004100d9 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 689118776 1250 689117526 689117573
    0xd0e0a0b0a0807030203330a08060712020d111305101b0f03141303110d021f1818060504020301080d050306061b1b01111b0d020d 57
    0x1280140c641011107001008954800e4150355400904400941001e01004101c200c4010f6840d18410403d03680046d062041d03803046415111300c810000e048e09240d00c14452500701604100c0c0750b0341c00c00044000b0484e0b500e800360b500c0c03005d11424002001c1940748001d800320f01084002d00c040180307502e40c0941e00c041d81d6944c081da000d60030940303c0707020004100c442c1141c03090310500010004001c1d540003500c070b810300c20520100c0c01515166a004203c1080c04154203580820074400c6c00905118801e0313081d03c40100c0b80302190003161018160b0307601c18000b5034000300700c1c0100034854118412480141e600c80400e054035811140d083d0105d00c0c00550704103003085004249841d041c401c80e030488298000400c5610301035113060b90300e0b400007040786912110a105401180100c4c9035000c9840045502900020f0b5101c40f01030400911502010704104039020904091800040c11402c0b402c5030500c40040b41004134001181c6548580000790400c418441031404c002c06100c0140c0f0007404013042 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 689120026 1250 689118776 689118779
    0x8180a18060f081213090c080f01050607150518070b0a03060803090a05150d110406020609060c1e0c011103061c02060406031d1c0e0a0510050a09080d0e0a 68
    0x3000142c2864040c0c8121a0014208002d03280b04ca10000e007082e030b80d510341400350030341d4400c110011a41e0500400011440e420304200c0715480d4032442d00d000d8003040300c8190904c00d040e156505007850444d99044039581c0c84021031101a4070b0905600500e8260b02152112070300c0712016500d5030081288140401c1c14140042000c034400700030b44000c1e0601800e00e000251805040111800170140d45002e0860208078115128405005862040d030b1156403845d504c0f89000070081c41c14400420320052074200d5130501c22201c80c441d04a544a03018544030074040500703400769420a11a51080509030340c0780040e14000d06103800e000e54807400d021101802c40084503c01242040e0032a40000e60100c1d00b00014019a800713648809c0258810301300b207048080021b01403614101c0c4c0c0c1c3d000c40300024610181b10b60030035404150304500381c5043e80c000303040620707010100703a500e0780040002d41481004038003101120710a003000d030700420191040b07840541501d4005002980412419405031501680 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 689121276 1250 689120026 689120039
    0x40e010620070305012405060d1509092f0108041212020d0c0e0901060503040303050a060902070605011406040b0708031518010810020301150807120204080c130504080708180a1806 79
    0x80c04000c0318005812a442c09c1880c5200e10010440c00e41200c0c0c10519070704010600500c0c43c0b09010026104030320b120040006180b210761600028041d6401d000c0c45070320740400a0342d00030a481d8005521aa9895030b03044100010388580c05021903181d6998408140803100c01e403a500051141c403c103403034001842c0f00e19002d004009800b40640340106000300b02080000744a503000941c004c00d84940095110303210384400060383d11482040c0d9400d510344005001d0319191a04130558944c00701e480c0c501c4d0030710305020700c2228010304a01428100700480045c5e081c00c074281c41c0740c1c8081001458000000312217205200410700038000e002051081d00303c907048240b00ba208582c165000001c0788844060000030440315070400408a004201000c12413020310743c0c060004d4405007004501900058428000b400010b0f0030a0f80c03c0c110540c10101400041010354003280d80c0301d070300035001d240e441c100c039907002c100080028039658011001a40c0040c50600d004030404151070341002c01c0c0465607480c0b0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 689122526 1250 689121276 689121341
    0x1e0a06051f2c091e150a180f0c08060a0e040f0618120309030c061a0a300c0612020f0f0702120a11010e04200309070b040e01062007030501 61
    0x184410204c200c000f240c426501c941050440c8680104a2003805807141032080a4441030411711003201c1e10344800c404004098051215842036924281c005031500b0300c00076820554904c600004150640042414081e40c4c24103088480c0e00004140400c0d200ca4004030b60b15184150709a070204001444050410701c00e000c0c04140541640c1e50754142d030b440780c413030000801c0420320b10503040102100700155600d4145110008004001540d44661500003c0450a0f04459915004d00c2040c106150014003043d035803009540d518a4481901b420a0f06500001c1c400c9194203000780c0c4020035101500c01e01040108941e82c401c0d40c1507003090b140d800d400c0c3c0e80c40d4100d2000521038890248149025485400141c150ba0002400400d15588123000c0d401c061080014190344410004208031100c0b0040100320014110704041e04e00d01442c00e2550300b590700c0306008090400c400005200005424000107080703000c1d250003910303400c550b40d10f04540240f607003003a071400c0081001000d070910102c14 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 689123776 1250 689122526 689122561
    0x1e060314010b180414010501110304030209070f02070b07050c040b0919051f030f0b0c04030b0118020409052e0303051806121e0a06051f2c09 62
    0x41040c001a90030405010301c980c01c00e07904900716200b8540c4440065a941c0560600c001c140c0d00200629418100018600d00082036a42c0301980200010001600c600d40302a034031444c545010404e185040c1c40c124108041d13980b01c06400341002c91502c00b409000310308440c42c144112400c00200401105002d207024040305da000140c110044003040805441e0051030307001c20048a0700300e00e1100c8140d2141b40007110340003600c10341200031401041081d803090b104c0d00040907050040c1040d155954541141c2c03c14080c810340d40108810000345007860341c040c0c4024200150341400b141c40c0c58400c429160324508a4040c10381c0c8940e01e24100300e030311082c014084c1c03601585c8503031528101c4480d49c081d0619241042d60401020010800e0b80c0031400d40740c41c0581c000c5216000256070350901d0640701c070000b500030800c103450710904000c560744041e401c1e1000f420480a01c003000f01d034080c1c141c0700038140c402843d8664104400010004048035011580d040c021101840161207580b41250303814200c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 689125026 1250 689123776 689123801
    0xd030b01031e092d14161202060d02030108010e010b0a0614031003060216120305220507030b0c0c01060b0301060c080705010b100f2c0d05161e0603 65
    0x1070004450105041c0c1c0c00481e4118020f00d4508628403480c0e5030b041c400074460741d00c01e604c1a941041441000840b540004400402c9401846901050001466200c50621035a44000c200c0707204c040071900c40c20280d600950b11030100319200d685d03a5000f140604000d1596620b25440e0606103085803405d00c03520420f940da00c0c0da030038040c0d590850300d4614950016080340310b0070b100e40e180000040e016000410702c0060802a00703030b01183c01d10304100d0300c1c41803184600505051004100be003500c00040b030350340d8078869116410340103000d08015042900c00d801c003030701126013002044140d0301144003c3c001030000000070403d059aa01100c4120b000a00400c000502e54408810104a100010701381940c041c10002401c5204140000d0300804d10f880c0303000c04680100300c0020400d401803104502a940b81c14030122801012b20459201d0300205181d9108207000c00c14541400010045406051480005582480c1d11035100e480082c0300321800400c5a80707403c0c000300e00140f0900a60a40251 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 689126276 1250 689125026 689125061
    0xb010f0212041403030d02040b1c021e0f13080f10090c050105070201091805010f0e1b0c031605030306030f0d08041101030207050a0b2a0706050711030c0d030b0103 72
    0x40210b50420f802d901c41d4039581c90700c81400352400030721003440140000c0005802d6950390310081c484164402803c4a01c1c056202e01c180424503401b1202c401240e00c1d0703407140d0881c568950540759202c0040c040d00940f0440c2c100700c01000700c0e41070700010b4400b207400811011031f01c01c07040242160301030760031032034005000c00440031040081d540254054903c403441414151201030311000c0c1c8403041070101011800b0282c6a400401105145104441c00b802c1014030204081c50101d00c194a68000481c0700700144a000800b2000f0301c1e418006c0e84c0e0750340034807402490008143d08009503284c200b42c802034483d01501c55406407100001a90141e150207980b51315040d96a5500c1c0c0300f82c070324540900307507041c10b400f002000c0001d0014084807501c94441c01121000342030000401c905014031410000d09814004c40c00000c016034041600d4030350303500c4000490690394001c41110085141c0c0b130200800d201c04242441d030450041000080d0140076a420000c0800c0100114180c80300c0c005460750b00da0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 689127526 1250 689126276 689126279
    0x901140f101403070e011b030c0f11060f091003020703020601120804030b1f091a0d05030403140a030f0201140403050d15060207030311010501030c27020a030b010f021204 75
    0x1d000c100610395010509003070070301c4120a99108040c1c1d10481c1c42c60000ba2103480c8100d060f40c0c01540845042810302401030300c0410302e50740504000e1084101400c410700780d58112040081c1410088029000541200d46032192110303854001d411030441584103810710000e040180d4070920949040700e4242d0300400c000d910740380684620401310032040d168143c08000103c0410001080300380540e02d079407500c08166502c41850380c468116030300314815584c1401103000d00301b92000840e04413120101c414070318030780c070903c3c140349140300b540d1000304194410400081c01e4600400d1403000d0b075010744c1392102c06105400040b400ca0f688101e610950760704c11804600864850805406201c4800340d0004801e001e051880c01c040c0d8840d401880180c1c0800c4050041681c4210000c0c0c440138407134000c3c4455411661050561940c50041c0c1047c0011410007414640480000e4008100340000c21952828a090000d004c0c1c0211040980450801411000c030310b4400a007a003003100c3c107011140e0605 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 689128776 1250 689127526 689127529
    0x6040501050c0f0a0b01050f120d21151e03030203042c090715031a2211030610020f060a0e16181113090b0a030b150901140f 55
    0x140c02940000b11940718080c00684040404c02a071602540070340314903201d0b5031401c41048000601a5002800f4007086100d070428290f0001c1d4002c1481c03581d0420802042c2924820144140c1c0c803601c0d03039401800d013424101c00003c81e5074a00306841f4980071101a174800580c0c170244551140c84010300603801004100403003140340711190740300000801d0f003061401000314041d20b010010f540005054000311002c200c0d10070050400001c4505034141401402c3c0c3c2c0d014201849440c1216150003198090080d1a00b1508040545a010300403501000030402910f0f010201e81c000300e0f03810740203510a02c0b00d103000c18000039001948401010050519603240c41c6502d0281c4003150107034800784107940034804c1e0042084c8250b0080c0c880000c1300c81e001054031043d002038030403a81e03d04e0054441003166000c20049005110113960b58100c02090107051100480d2060207a0390010f0240044002444030150300c207400c1c6901e4980c1202c880f000c41e40c9a609514410390403121550b40b006100150301c805 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 689130026 1250 689128776 689128787
    0x50a08040f060b1008090c010207080619060e07020d02010b011403040f050c100305040203061b041a0d06030f050c0901140f0402040503060429130605090f01060801090606120206040501 81
    0x581d44219004182501c962000c0b41d1010440c3c0051404125945d003000703443c000070071602001d44424401005024501481140c0b244406070000c5600c0c204040e46640c64210341c1c003c500201046200ca403807510f06818025116010600769100650804610360b41541c402c01c004844d514000410a14546840d62080038840103076000311843e0040e42c2903001d1613925880a85540d69080d200482c85103000d1041508040c402440c0001003054101c80c410543d803170405550544200f1032060340d51010717030114400d05000362030752039400c00e08000300842041404840815903610910844000c40403110400c22244000d01450a03040310380c1d460308141c1e2500c0b1600b504060710103070005240035111030101e400c00341d04a500740d8803034009140883e122203190881c98001100007400040604110300035120a4000800c040d0200d5200c40100c0c6030740e0b00501810041b07440c100020401c40307544d200b1280c040c005000c4265500f5141c080001040205030480d04215540288003900c0c1604000c0190785 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 689131276 1250 689130026 689130053
    0x20f12181017070906110706020c06030702150c1c0b010509040b0d170c0d020706080a2310080c0303030408090105212401020118060b030a0219060e01050a0804 70
    0x704546408420040c05440c10300358002d0516681341151181400c40240c030032141d80d0000c1089034448041040704617400714407040250421510f80c1d80d45d03160a00204c0c0b5020700b02c840070a40c52211014014600e00b002c0017070214550681c0c82c0300028903010880000c450606da0203c3c041101007180914034601a0702c01c0f05520002804100da80358180c0712510400c115801000020800080d01c4492040030461608812050300c010241c003814000018043e05014210fa116144c903102c204000d0494054444403400c46110650402d00d41244042e070035440310720a0500c07602078540c00e1807040c1008002c40b0321658000b2100303450410500011103c0c0d41c4921004501c04120780d43e0601740b000b8018106000d034030029448a1981c03c50260f0010352000c00001a055a2402008045031038000d0041984c0d1600078038000396050b0f20801007800c01c00c030780c18020f61104205140b45500700030718418000342ca201e50340b80004200385c076006580d035116040e1600d005c501450b00040c0000c800354520360303 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 689132526 1250 689131276 689131309
    0x110c0606060d0906020f180a1401030f0e0a030c02010e1507170c0a2001030504110d0215070b220213050c0d0e0f1018060209060c03030403020f1218 65
    0xa09004a84c41d103404030f81101c85500300342540001c40c05072402c61032045201d20b000441d400503002e407030102202c8180001c485ca0a05068a030035104d00240ca0a80c4982110850b513020364912a01624008104000340b29041703001c01d01c0401c03004624100145082551490300941928044960b01d0f402c2a2030103040c01c443d403543c0100450298644180b049a42191103090690741041c1c00f00018103040e00c0c44500d51381050315200800000c070740c0c09007021076503680c10b0710303440014052400801c1c815540c80807041d5603618005030740000c1149040d07c45104a004400c2040d25001c00480903040032a089000381d4001d80900204d8034540880d809103421511081c0494600701c1007070b140c030045d217502c140c0707449007a0007440003144009800c5c010390583c0c4580b40c9042115002c00e207542d07510088004005000b09501007081840c1d03854620031101c0000070441100c1c1c0740c4c6001d10b402940d0f8420181d0707141c044d0084c0140007000d40c0070002950002c07c560340a400000b00006d06100c11201d0026400 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 689133776 1250 689132526 689132531
    0xf121e05010606050a02100c080a0b04060509070905130513083f060306010f0603020a0c0807060b2106180316060e07060509150f0d02031009110c0606060d 68
    0x6403007446803100500842c0c40d4a43c4610110802030309000c105070202d5aa00c0c00e100b1880c480a50115032141d10200c00c000001e500100d0074040f6000f4081c640285402950403401c2c00100d0b90002920b200310340048a9100158400e0840d41080d95001e640c05008079108210701c1c00000c072094040d00700c0c45030068200c401e80e607800464203941c3c000d004842e86001c1c09042500d580710344d240d81907540004158000c0c801d40d4900000440b840704c1601c1450101980460850109403160600340007590b08100041d40701d101c20301709000107154003c449442444211200c2000f609200c4024060100c00340140019507681e092201203a40a801001480e01040041d02806111030441c5500140520000103004082c0c0c0452480c0150310b80100382441000e10000c0219616440c51440d60483d101c50140c0381c13550400c0d13007003145c0640d03040c240c2c8048c000701c1002003d10600c0e9150045509202e0280142c181c1820101e20600c06c60740345158641040c4005906400e0000042c4120070240100 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 689135026 1250 689133776 689133833
    0x1140105130e0c01050f0c0a1104180203150c13140a08060705040521190506100305250f06021015031e080d0c0c02100f0215071812020a0f12 62
    0x41506040302301c481100c050340c1c04c40300d076502c505240c8908020f80032204011030340e0003030315000a60b6410b5030038130406000900d034000502c00c50b2307108295020803c40e0300540c507503d916640c4801c0b62000c1d0301c1c9035500888025000007018800004c1a80c09001541c40c5e10b8038090410091008520900c2143c1d0000d500100301803044c0002004000301440d4404071071040110b00b49006070812602915001c40300c3d02d203c405002040002c501400c0c00a201400040008450b802c200a080142c5d030042c20315243c00703d800a4850f801151703150081880c4101045801d81c3c0300c840d0034148849000c003030b008013101554400c2e200d040304440246d0354003444c491800c0c000000c140784280c1e59443c00f840009020000c140b001c40c01c0856440f4030070000390904505111200e0b900942c3d8068a206d6510701075043c001180384140034440031400181d503c7c403560b0880d03403110000750b01d018003084120f0190030201ca0014602595807004826124072070b88620034000703075407118034002c0d441c07002112a00390b00312030 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 689136276 1250 689135026 689135047
    0xc110103110406050705011103011409060d0503040303080f010909200103090602131403120307080c070b160809160501230301080f06130b07050d0e01140105130e0c01050f 75
    0xd80020f01c2581d548555603161881c0940c2540d2085480001c80f0078140010711244001c2903003c0c1005809581d050940d68405000540f85141c8089c0a0850300001901005069000035014424080044240d01c5640d0341c4050508440000b078014020030004000c1e010841007181480034054014500444c1401031511a0b800b00c1c1d001110780c46000035004800c02240303620081d080c1000c50b0440150000c0414400130300c59070301c0018080c1042042c4e10000401c2c0c1d24200094072092500032a40715501d260034405118000b40c400d2980700070401200001329540c0d000600d004e03001d51224401a0310614000055070021096050303614641c2c40d041c2d2561200b48007501440c002c092401c01440c11030b61983c442030a241c1d000d4507802c400c070400e403421000701c1d007600403e5412041d00e181441e0ba6031000000200145854128044194206029200c01d0003610044505803042240d4055501c004075401004a500006040300e039a000080e00b002c49600031406000e01c2d188206113545402c48140 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 689137526 1250 689136276 689136311
    0xd1a010801020a030f050c09120f031611030c0d14010902060c06040314030c030c030c0904020a0f020f2107020a05090f0403090e07021b010905191503020306010c110103 74
    0x20080304003a0341c00314903a00c000703074036000e0980c1c00045100708002604120013107035440e00c210700015024008207100e40e0105c030020402e0b5104519008141c070380b5130035000310419010554080a461600d001900034042d41390124007404083e000500e141c5a241c81503030b911320f01840c016502c078443d540e0703072650f00c0c013680703481008008c40c00079000501101c0c41d00d41750240c5655041c00504000d00000d00800c00c0d02000d400441f82c03c40ea00802058032513880d6400805030388a80d21010350841e0000c14a40030050300040400c0000c84140c0075210000d880ca514551360b02c40c0000d84000d1001480f00640c07903402d00b9801090382500140c42c051600d6201c1c004030300c0c0700c0d0b000c2d54a215442414001c00c0145903115400e100581040303510301843e4109410001e5584903451032152400844020ba59800d078007910212005040161466503004550414600f040034544204241c1c6e80719125452810b44c4680700f12841048140c4426456400c2c0c0d03218809004d50640c4024103160b6a84810701d00d408030352 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 689138776 1250 689137526 689137529
    0xe0301060f091508160e0901060504090b0f01090b0102100902030c04110a180b09270c0a0e0604030506041b0e010e07020c03120f0c0a12171503030304020d1a01 70
    0x9503000c100f030301d0a03040988180704540d000ca202078100c45202050402c140403a401203032100c0000e070b4107a13251422124010003041c6d1016500500d801852020001284515407040d032805220418681c2e8038040c480581e18240b60441c01030b001020700d60318030f054035031000100314005001c44109800180100302110028507d80355400000708a4010340c541c4402d10f400c079000754540c0034041c40e2800e00c08110900a22602600c94400e44186004602c1c0f085085072000000d102d540855081060045100b680500e512800103040ca090001d00d41c10140129400c0b030350b201000300116910394850a91020302440174005070300407100001900c444c64030307105020f08584409034101e41800c0c200a4680942076421034040c0d0010002a000c104100d0142c6218143c0120f07010303511018522814180401098010020031600c40c011504903848006001d1582003c0c03980b0032140c603810f240501550300221300c164107910400c000344c010300b0300c8030b0a54480d03480b42c5040705035441003009824104609 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 689140026 1250 689138776 689138789
    0x2030c030a1e05092202090307030b090c0a051005030c0c0a030305100504290a120501020406230d1116030c03030f0c020c04021e0310080c010302040e070e0301060f 72
    0x200d0502e08000000d4002d454a520182400c0c0c0c07902c001c00001c12a60510407120000741401e80c500c00c02000055011100d030001c000f0140c82c000c5840c0c1c81c0035490b0301c0e07064030907041500ca09044110380d41400e05a030000c0d240020320845c8140d03851101295550300042039145150400e002074000a0020881201404c0c440d03100401c161518103014441061360b80d000c0c038821030a00d0209a44110200386d40c0384400700500c00050150f56070b0740070a00054003640051290004200c044003032143c1907020308240c400540c0c0300c1c2c661100080d0910302003504040380718400a42041460403000d00d90384104034544c07410701c0148c145030341340403201c0070034100e110103402150300072001808050340b5100316a17615080510403c0058507441d4025500c103011001e040c004ca9000850111610030300345981003502c9204010780d0350f89002e02901854a8061060b10190320844150788540d40c0607000b9581a01c039034140f81c8100d980e8445040781c2603440e00800c1030300b6560320f070300c0450300d180300c0c88040014004 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 689141276 1250 689140026 689140037
    0x160803040e0a02030601120b03120705011b23090d020a15020d0203031003140a051207060e0c060904020d1d150a050f040b0408220501030b01030507120c02030c030a 72
    0xe0180818078200c1c00900d820346580c030410401015030b82100080c2d8000210a42c00121a050000071030300c3c011103107a010300c0490000c10000c003008015040001c0c00d001d4420780a48000020405980700ca1419420307401619a0b41c01001800c8007440c09894a880010004607d07094240c0200c0c0e040301d0340b904526401d8540c00c004000d4984c040140003245041480151301c0c614114003598522010390200400500b4a01c0c590703d5850310801c21a90f2403904141994000301100703500300c40d103900000c0200c6000b814015849509080864441d40c4100081e0004c0d2922045508000c001d61003c0005041c0d50741c0c500021580108801144214140341c1005046d0411480000c01000000810103032030f0034108420031011074005507440780c1103948100c0c0f4604076191854603140c1401111a48000d5149420b410070003001c28800c1b02c8201c0300d0a0324100414603c00c001103050318002c403110004108406c010380040e009681c4200f0003a005032058034100010b840b015801c641c0300b0080c9900040 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 689142526 1250 689141276 689141279
    0x1e0923180103032c121e0708060a0501060e041107050106230904020d020411070b0f191b050c0f01020301090212060d050a1e0f050d0207050406031a040516080304 71
    0x40c2c0002810345030000e99031031003201034520340c43d00151880b01300040d40038280280400300c203643d040010311008010b003c80c041c0700a102104d110303543e17070309489104c030f00c1e1003844003107404e002d034910405060b9001941d40d5001400d0a04c280406090f40e6240542280c2d0104103200225800b8458180645190102070840076030100340c1c000042000034015214601b50b0b024003005983c1c482d45100441d6040d01e0100b1074158050a11000d030080728005020015103008109103c4007001c0140d00c141015403103104860a0040d45404403541165140f20b0381242c20080c1072514000d401505401d22001300308c43e241e80388220041d084e80c04c281d102184250b004071b001400701c00c0b0403240a910880542d1540c4070100345403946583c034a101d2001404c3d41504401c2140400002c5507100c0115401c82280d81007441c07240741041e603801d4007141c5080107005215010900f0701e0700d401594220303500584000d10f410345d144d404030080503002d0001c881c07a00c60000c0d411015440c50005d9001000c00d90069070b2241d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 689143776 1250 689142526 689142533
    0x40b041a0f0106201c091503060e15102709050103120216230a080307030306081903030e010b0301110703020d020a0c0b09031005090d1e0923180103 65
    0x4240d0000419241c84c0b00c8032078030311455000414681c0d00e00407024840c0c2800b2140740130780320082c540c3c204060000401400003000ba4058024004585101410030820341d0340c0c403403001400c0c0c2d03d00d0700c0c0c0c0e0384841403000340542c50f48078010304100400030310300052010500d0032002e18102c89a41c021038040d62207a0040003408480d160300311241045002600000e440140c004650308100c0c0145e8500c0544001c40b9150740d20b80350721001c1c201d000900030401c59500e560103590390350400d2404400003424110301080c0c420003c6205000e00c50f10030f4060080c20b80507903050b40504079280a2054541d600c00e003101c1c141da824040c01880884500d20140d4441035410000d0a111814000302c0c103560048041c90b0005080c180a003045030b010b20100340e110380501d00000c0c10036240c5a10140c00340e0910741808215000481c0307090071ba000a844010392014845603001144150f02c500b680400d4540b1030801c004640301c120301811035680c0d0440c0140c8510800001c40034020804158103000b0120018000c1 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 689145026 1250 689143776 689143787
    0x1d060a11070f170307050303010b030702010f0903050d1d19050f01150501110303010501090b16242a0309020102070e07050a03050604050402030a02100507022101061706040b041a0f0106 81
    0x1025001010311701d0100703e6110716a50b44018483e8076081ea10000000d00f840b071013940000103d44c010801841508001d00b0b0080a070f40000003884885407030150030700410310a0000300803036411408042c01e040a00b07500030180085100350251042d0140081c41003443c0801e12030321503480302c4e02850302d41160501000401c1505a0100940c590303208100511450fa0801007201c01c0b03134000305400d41da40c2410354608604214201e002040d15401c5e107182c40f03801c1005c0d0460302c01000062801c002a01d6101d485850801000002d04d0220800c141c030403c80303522a40080c540a0b0040c01110300c03103507403025110f0080104841b400c1c00a82d001ca001501d155050190343e400032070880e000c3c081402c094002a40f03031501050024459101c41150200c22070261042d520308030b400038002080c1d1501d03500140000c440c2e0383c910418551a00e80d0204070111542c00d0401c410014400074001662180d66458001b100078109072140c1000f1000014910654008103200d03080b444400103d9514211b0040c18 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 689146276 1250 689145026 689145059
    0x50c040e1905090f06151503090705040e0c0904140102070f0f02010801052707030b060c1615052203080a020d2042161d060a11070f 58
    0x480d904641c80340c4128141c0007442540010490682620700d1b1104000910403521903400400e00e041c0101c00c00200e0803011890004540081c2d8040c4075982c407a10202d0b0302c40c0590510f030341d40300b03510901180104144400c1000702c0082c000005103011030b42c1d1501075290302c412408a81c8035181003140300031564001c40303850041c20240c810040341071f42044603400000d0400300c1c00521141c41c4000500e0544240c000c400742d040040e10240c0d0f80c51505003026141c00e200605541990014103000424100c40c40d208900c040c226039072a07007094601007a1107800d4100d2044035502c085411400300100d0000401010380791610340090200c1c8902c0030700580840702d200144065034150010418207000c000c20104005079500d207002c00c0c19201b03c14130b4445c2d100500864410340c04886282d480340030740413001501810201503400351540c0c90903412110503a02c0b9007460b5100350441d10b903504506140004d8803002074281028044103040d42111403a01c4160740c030107500489101020001c80004500106 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 689147526 1250 689146276 689146291
    0x3030904020f1c060501050301090c0315082b021906020405131b02062502010608031b060c070519050c120303180307120c051c0302030f09010e0c04050c040e1905 71
    0x384e0785400000780070741c0014030480c0304a50b100c480da00020b501c2584079403417403504081804d018640711100281c5d0351740e10b810f0140c0c0034000e40030315a00c01c0c481101440340035a815401800b481604c0740c03506240401a0380f040300c0700c5400b4030000c903c2e5601c0324003074188203541040c0041c401032103008400c038821000b00c1b128250f410810078070124801d180d40c204102c0e2035600445954a500ca10205d00618207036001840900001c036900c0040444849410b01214401d4220f400d0341d16050f02c04151842180c00081c103e07408610000022403074100d5050300e6034040c07016143c0140944002c00c18000f101d81d8607100c40d0700300008010006403003581d100d080c050756900a604000c0a95510408501201411030034006035000081c208a001c0150443c2d22400e50311280c1400386c06a00034010790030036100340130018000400503050b868144502040d444400000f050b1150204041c4001030030050080542c4a10030040810141c6481c10b019028030646c40c2c80c0c00800700c0007000034040710320142110 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 689148776 1250 689147526 689147531
    0x105090a060612020f1c0501050406021b1612060609020c0a03021002040e04020402030903210a05070503070518060f0a11240a0b04020d0c0e01080108011b0e03030904020f1c 76
    0x244050303141c141a40e01c0c1084140c50b10001b446504d804000101c1984400a000798200750400c003c100b1a600035050b0304a9101403e60b07800d00700c03041e05482e110440d2080d410300000403170030019803040441c0e10702c0e07160140c500003c6041e2107008610503a0300105641146911196800042585c1008404011101d6500c1181000d08040d002a11290003900c068403c0e90007102062489005200715120b00803680c0ca42e9000c54010008040c1c2041c0403104c0b44c00d09450304000650305802542203074803c4e03545644041c0b91444080b02100c0c10032340e1109198010106002c02221303030403048000d1150045a450703640c0910582006145849030003024483c03100c21481e40300d0100c1c0841048103400190000e00800c8400844021600034010b0004004030f642c240340b0b041c201c1d2038001c07403400301c00c1d0420780c0d41888680e203424502d42600c40711465503500100e0300e204800810722591002c81d0050005045c1d910300300100d00028140c0c0c10504003810384040004034585003c807202000c03026440e011505 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 689150026 1250 689148776 689148809
    0x7201206100512160e16030216031209021002031b010e0d050c120d0e0f0f03041a0c0601030c1e0303020304090b0f030607030f0c0806030607050c0f0105090a0606 71
    0x603900e00d070a06215090090715612105810110240b001544140000d207800960716900c1c401000c0ca0340c0c00b55541d4584002c1221001c2d080c1d8402d000f02c42072203802c2559201e2002050798121029400c96804a402d00e55400c1c81c5030040c0d076401201240d10409a00460b00c9000101d0305225414030b8548542a50381b420199000125011802c08038202031410200d031038011841c2c1c080d040031800031000700581c0c0001161803003504203a0095804140704002c0741c00302c1d5080705040303a451105100102d4290b005000c1007241013004810381c0c1c10221040d80c45414040b0f641403451038001300303030421500d002400e01d00b484000850401940c030020030084a41510380b40d514042d45031b02c528000e034180c864a4081d082d00030f4403940a01c020214014003121118600008010000c00c030310000312030752608002619004501c1409110300400b0020701130111600e8902c0103650302d601811810307441c0e000e07003440d101c900b0000f0b2140c80e12404888024040f015480d280c1007085605540020b0740d0011078408 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 689151276 1250 689150026 689150041
    0xa02030c01141207020d0807030c09171f0c081e161b031101180c05060901020c06043b130204020d06090204030b010b040b03040b0c07201206 62
    0x35039100542003070030b090301148525181e40d82c40c0c0c46080e08251241e5000d00600a080d5800074804004400b2551503801640398480c0c101c4c191424580d17990002902001c0521010898440c81d9801e010040304171000f00d86490b40451420410341c84000106580706959854160050302c41c50340101810010036845042c0f40c8044a00e52026116070604000d4030302041105004030012480012068407140d00c20031603103401810b008018640a8107035092049071441140e241d500c81c514554004d10098000c0e040505225590704400c100b64118454545002102d4a50500030801b42007951070071103e581d42e44d88514080c0d0444028030f07441d0035030101e0b400c40201c4541ca665400441d02c2c0e00415a0f4401800001c0c003034051040c503021118940302c00021090110350007082103c3c4141c40c2081d4030780e618901c3c03d00b00c1c01688a4031078400010000940003d0034510b82550096142c4005400c08000d1b4682c0030b500241e05140d034041f00d0101006520f240760101d000982009c02600a001d02d251090307 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 689152526 1250 689151276 689151283
    0x8010c030c0c0318031a1f210f0f1401060506070b01120c0305010c021b0301180f06020f03010f061106040c21051507180f1a0d050406020306120a0203 66
    0x207810000105140000d41000441820046800c050005001c001c100c0c04506811710a64020b1f8070030045600012095a814606800300c4c0c0c2241e10803401c4e8a94050f00d0b100c00030300e105e012590496050340314000100c1442d4041c880c10b0290003c1c14003440c0c007145203401c5034120342140303204450500480c00040c0100340c1d01070658129031240c8608800500e03041d0581074031500010b00c5542840541d0301e034039500080340c00442d004e04048904818454092500301d50092241c420000000141200494030325555205802e10628006203803071200726903207999800c20303089011200203040d020404242d20400f4041107091240250502c4c1c1001d0b034400007510058420440340c12a82d401203101051002e0b03007050740a07003200c10f50345103c50302d8032469a801c00848416003c0381d03810b01900690f40c0b0100c0a01d055403010401c008101e820400c140c580c4104003403c1d0b81d100b80f0100003c1c902c1c01c01034080c5c24012407180001603140c1c14080204403601071407000b2280543c2c1b0600949000d640c000 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 689153776 1250 689152526 689152547
    0xb09010809060f0a0c02010219020309010906090b0f0307090f0305010b01030f18020909010f1515090b0913292701030b0916030524010509071d03070e0108010c030c 72
    0x240005000055260031b80c06800303850440341c0500c0071021807801054002c0004c7c00c410001360303074117a01d0f551242420707649003d05016400710950140100c5006a074030350001c6812a6803400c0c02d0b0403096a46040c46100d00141d042212165141c0b5a8500e05580500564903000300d894028400d521111419071140c210303515002e8842c4139100c010401c1541d0130b60001c2540081c44200348880c604d404d54007401460a071151801c1c803480c0d510032100c40761048802d8800d40e0071088185107450350501c10401e20440e928100d00c90150340e400c40e0305003030500152404015012480b002480d04050040001c0c00084442000030780c0c20140c032102e000c41d0400341c1503043d00c1d8014485032068940300340d62450b10032481100c1030200030b40c440c04424002e000980f4604810700300200c80090780701c00100000000207106964106120001141e4240c1c02101c544166001120303080824118030b0000905e002c03c01d510000c501d095030001880384200230f0203030120801e0b4600f81400b030010412002028062032 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 689155026 1250 689153776 689153791
    0x41517100c11190c050409060905060903071e15090302010e070605090d0822030506040b0c09010c02010e1503070302040303091502210c01050a0221010e240306010b09010809060f 78
    0x81d6001c3d004100c0401303141005010054020407404070a441c0500c000e002036002998980302d10400151410360020440302d410740c0c0160f5141c256001c9501d03000003848508801c4a00c081d11607aa800089046d11072104000d000c0c0e80080348040d40790040c2410080036822500c20000100034259150301c1e181010b4690780d40c0003da0341c0e5280810305406040300d40c0d00402c94501c03040d00d000081072000000314903010310300032010310340c0c1c54480140c00c90045c41040c038402c0c089480500f000e0301540c028031440b40290000381c007640280c140b0121050251740100c40d6000420380c00705060003410391001120000e0b1450a6101484c19132107030004e580c41782c181c1c020b8500681d140d10712024000c0c80c0d4081c0c8903a03658040080c00203013022015140a5005201450e640e082c0605040100524001030305040b20b241920302889512182954002000105030b00102140040d500e14010780741080850300030504d00034070b152585110000100300f13201c0600303207811710740c0454140030b00c048090344c0054010300f4 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 689156276 1250 689155026 689155063
    0xb060f010806010914130c0905010f0c02030712032d0908031e090a0911030417070c0611070f0308030403031d0303070c111e040501050103020a0806041517100c11 71
    0x32036400160310b0702240d16050415505040c01f120902d5000524003080d54803d03260700c00071092004c0100c603000703480100a0351607842820b0401001080b00411055280030745051400d0400120020b400503041003090749001440d40005a0801e5002d0400c5014040c994091440c255070721b103c0010900f84011100245140000c0340b101c075584400007000141030304002808000c0190880380543c1d0003ca505984480b18004443c1c030341c4150340c08540c0007550240e8015942810188103c500340c0c81045001982d2040000200702210390b0300d202c00056100d1180300d90303240780a1078003c0c1584c44a01b1018400004801140010f8070003105403503201045240602030106030b0300b8403180890b1081600e940261091254406d042c110141800c2c00d124141c400703014990361900110101d2149100c140001804840491161321b05a0003610781c0748020741c1000f5100e82c0395120400440090440c0d2304c000c0d401840260310501080c003c2e1a0100c80c01d0038800d03158030003a029543c44441e010a0f000f050f65 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 689157526 1250 689156276 689156309
    0xc0406060c02091518040b09070923040c2715080a0b070504030b090105090c090603031b0106051804060c092d0b0307030b1906050403140111070b060f0108060109 71
    0x440c1c0021400040681e050441780310300341818050204901580c00c41e00c58080d646c40494031150074000c4601c1580b130b00080c100380032441850480c42d4403003e0801c96280701090b20000f55031140b9101d007003540740c4000012008494160004040390010300c524543c414a0801c1084040310114509812581000200c9402c1c3d8441104035241c0c0304a400c010550024001400503181056006a12400c002c2003122261980601045801001116000e915030300030030901c603450380a00c450383d140b41640c00021178500d4842000521000c50400105c103454001000c10040c404640a01da46010050420030310207800c0c02e1701e46036444943c94070310a03205161800b149440840d0542c0c075008181c1807180d242c0344c1c180b100005014007001080c09100c2e80302c034000d25084440e88012039003221901d44441c0e01c2d01d480c40d6651888292041c1034486030f5562180100281203411000b8046240b25440302e88042c0351017810000010003528541e81004070b690200859a40c000c4070074001c0d80e0f80960f0001015 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 689158776 1250 689157526 689157529
    0x40e130b07200601120506071805040e011d06040c0e010302030a06110702031605151603200706080f011d040b0a0b061204052803032c0c0406060c020915 67
    0x2d4080c01014400383c4a060000038a500f01040010b05461045040e6481c40c0c4480d90b04403140746021419101e01100c04c3d504114070324099104a0f0345d04c0c9080700105000c5c0061102c1d0032401950304131110795802c40400c11040000f0109001c024283c940c010300159410340c0c020a90fa480b03120001804155100003170071fa688040001c0e02c4035207074000c0881b290140800300c40c080310040c502ca42d40c01924400e03403d00c80707091300200740c4031104c00300142c3d2074442a2035102122800300e08040007505035076007240f070320107200107000c61009005151152503590400300410030084005a21828410784402030b113000e501c00c04c030151504603420030320000d81500d940b2155001071403030706060f6500200000e200300c0c1281065081a1040303004001340d901d4100c20030300d007480004489400155100044882c100024045d5024040b9890445074090f641c1252095034010700c0c40d08810040301d9403080300d01d4101c41c80c150140802500d454684101c5240003540881c0441034082d0000e6000d1500465040301c0d03 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 689160026 1250 689158776 689158817
    0x140f060712030b04050a0209090f07030204150e1807080f04020a0f08010506031905030f0a0306050a1202130b0109050603040809030a0803040507080613030f140c03040e130b07 77
    0x103403600580514011085140080c00070030500b001c250145045c4400144560110310940e100d100b0003034080d100903074881c101c2003001300c0014500018580c1c03c1c400442d8001603c291008000d10544072034030080d4020081122030a1580f5281c800056803504002e02a503004403820341000501d440c2c98410340341c91000403c04103580e0016558000c000c200010b40013015001079000311300540a580c203400d48032007950f0b2072407000c000c05030507540104100700c2d00383c02c2500107040382400340c40c0005d205501c500004000b81000d500c0300c0e02c1400c840078001c0940c80c102e1105040740c40c5c0c00030104660721070b50f00043d08c100441d1140340d00c03850020000806105448040b204070600040944041d46694a0040c55a070030a40302a9200c2c81109004a5103480000706240140001d80d02d44889108650741140c80780c00e01c10040b4100658030b0100c81c90041c148000c0c02c440070140000c1c68403903040204e000d1586000910052040482e44212000306d0681c854040c1c01c2101c0e07191038082c000d900b0240003103 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 689161276 1250 689160026 689160037
    0x304050f03180f030d020706051803070e181501060e032134020f1f081f0b040b0c0a08030406021e12010504050601180e070f09140f06 59
    0x40d64080041e00b801c1c05000c240050100341021942c0104050f042d2080c103a44000111080e40907070700400f4244641c038002c0e409046498055680310500c0c400750404a41090190b90124124401440520640110740f401c0300e11120f01c1500205255600e45007000350005040c45588203201400d81c0d441d8075510300b4041d0a4040082840c3c00300607602d500d00184d102d41c003003d00d0b0104400741404003121041d41800000340c090f4241500410b95485400f001001c1d14076461540c3d0001008031405401c021a00c400e041d803450b90340b200d050620706000c0540c44606107040351410349683c00c03418444004400c060b01e040d030b41e08081c541c0d00c640907843c98506c2c3c03c0c0e00c13010140042c00007008002c10018150000d10807580c800414003540d500304034188250340035040b280c202000715400140f2160525901542d40040140340440c0030180e4801040781da80d903030707030411050540340c1410052204d0b0406e4100d84140c103a4600300c03030068581924614402c880b1002584a04141052a031059407200309a62 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 689162526 1250 689161276 689161303
    0x1b060913150303090803031302040b0609041e050106030e0a14010e0f0a020103060b04141005040b0a05040305010b150403080d020424020705040e0a0f050102071217010503060103110105030405 84
    0x810340c000312407014070200c18072048001525200010500c201e003c4250381c007520341900165040070315942000003a20403007072a580c0003442484040415030b101e0080340502400c2040380c20100465404607000d50354140c10031400c0c103042111560386010f000545582054010385403040540382d51440902407c0d11101000162050020520b4441c80200e214900c1700d00c02d0701d04211326039507101141140d00480c400c119010040c0c001501850400700301004500040380382146c54113071510b0340c1201d5500001c01c0900000c0d0040b40520400c40c0c24810700b0001c15007140c29050000042e15444080d10850000610003c00801e0021040324603405490207070004903e19110310381d00b05515002c031110320f41904014840c406002a103810140b007007060824060b005422181101c0d00d5035040d03a02001412162503508100100110309095484a16102d2a0391000c4400380340c0012400c2d0032078182c00040c800e0700701038010400101040852003054200303003072458503980c1c2c509065040c02004000740c03 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 689163776 1250 689162526 689162531
    0xd020715050603010234060606110d1b030302090102070803030a06080c2407291e07020c0d03090306061202090f0c040312050d05010906170a08030c130f0608181b060913 74
    0x2c00d0b00e0340c00132003109200074080e007150840380bc0c1c504100d420b00b088088103800200040300641c040b92094005042d80350060044824183d80d50301c0980c619403044030184421941c880703041c80041002d00c0148030880044900c8e80c0909075201c1c1c0304811001d0341d84041c00703801c1c001511600b0072000c80290442c007070341070441e014560010100303a030940c28200e84580048a1543d80800380100c510101d41c0242c0b0194010204060100103014010111402c19001e0000320040000003070304030700402c1e000d40000c88042150b52130782e205001c90f64601500742c00c01c11000380c04000c81303114500284d070100d94000000b50210102d0b88010b0743c140c0300b004000b0704c03070a042000209000c081030300b00000312103005928103800700310a4403c0f5101c50146c3c0300107005a1040010488078100400502032034a103400d200d00b541076440f90500704a4006500a50100f02a00b0030810704101540c1809410f80741913003d04039400b00132400841c43d42c00c91b503c0912408010812280c9a241c8964029818040c02c004 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 689165026 1250 689163776 689163779
    0x3090a0c0603050a18050c0108071106010906030c05012a11031b0111030a05030f15060d090615080d0c080c07140f030f061b0d0207150506030102340606 67
    0x5002c2c03c4115400940f0302d05207101c244001c0b003000000700080c0d1308140640007021108004640034603001d040300d400c02110720350030303490070005008250081c040d2401c00200b4500c0c1d41791a401e107405550110341807000c000c001003500050600c10b0a402204090807503042d07441c41c070386042c0d070400ca29a40c603010320484044d01070000c041441e15003900c800b40c0360f02041e4400d50381080e030f51f8482e0f074040b040003807803d001103801c908541c04a290444900c0110215040189020030000c0c1c00c20300c80c4405498450340800c05100744e9108003041440d1315090100190704000805540e0101c85611004006e824807003c030900004000342c601c2168034001380e1304010f81e55142c0502c441d0320380044074880c0840c10400c01c1c01b842e0004130130b83c0384000000035050300d54503440300b031003150b01c10401100b0b004e00800c6442c051032007134401408054850740c86801c03440c10401c0a8000c41314004c000c180680e10400c80d10340d042c00d01010f603c200c01e17a0f5280254526030041b4882c00110008030740100f215050810 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 689166276 1250 689165026 689165039
    0x1051c02070f08090f030c0d060504060e03030405030307030b01020601030c12030905060f21270a15020c0610080c04090813060c140313060813140c0307060c1703090a0c 74
    0x44c00100307000c90b00c800d11160b43c101003544a207100c0c90410307484190b60b13a1480025282d6000729620034010180000e00c00c206420f01c1e429076008450444040e0000800c0040c526010711440c031103101e080c03000f403200350704503503070072403019176501030281c2c802e03075114414041600c540345080180902a24190711425602c1506543da00310b010000010909a0b40310010700c203144040360310404070080503020a8100030003000f0400d001d209400c416004011008001c0b803d020903d80f81c02900700d50060342c40405095240c202280507112289540120108002c0d409002070000c00c140c030100c40c0090705445601e0804540d2280750b1440706608410a40011450340080e50510740070300032894414001c4502100b10340380e114000345000e4441c504201800360900c81d66031158002c00ca6000102d21500603169045e800d10f212024a50562001c10408bc0700e080500c2007500400c1c079414080080244c50f620301c0c40e040114102500b0300d81d000310014040010402002c8541c0343c000cc1e842005035181d00 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 689167526 1250 689166276 689166293
    0x50403060522030f0e0d0b150a092c0a03090b0901030e0f010504020a06050c10180206120106020d020a0507210b070f0801050a05010e10180608090706030b01051c02070f 74
    0xf004d4a001c5000303007403102e003d070801d01c01307011071103500c13030b48201c0d403503079401411500c1d283c29001194000301c3d0300038085074040c15442081c9004003411a401c017010000d031602d0111044011190300290000e2042500003a008200c3c8010358950300100380d1209034040040f0028401010045501d20413480b0004040b4810344c8214025402034820210480e128642600c041c841c00e080c1c03664940c04800e01080f4a40b05600c0040c44c01100400f14010004540004d1415081400c0f0744502d08024801000100e404201c4407403c00500e0010702000c1180d511165168203181c030480c0000c04011020551b0300c0100020505400c0c3c1c4028038818904000304014004030080e46801c0106942d603002003010303e44050300b03104a0380c05a4806280c1c13155502482a84502c2048020030b011403601074600e1183d4184034140900856a50340c10607103000640a490a1802e038004028546049424800c4c1d91f400000c85082c420000c241648002c4802e00d906c0092107214005003102c0120304540e0108103028 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 689168776 1250 689167526 689167547
    0x19030c261006050a0c110301021303210f051b120708030106081014040c0c0618110f0f0907052a01140921040306050f090f0d05040306052203 62
    0x211280c41d06107403a4141074450348a60615070002c103035144e101d4000100f995589014130f0320007038009800d05289510320091510250012140b541401400006069003000703520210201450100300760300315108040c0280c400d240c050101ea000100401d203c020301040a007821030040329001d507403903000b070030010303410340003030065030006000ca01c089201d080c040b4100100b581c613081c1078106184c040c14208001400440090028800394054030301c04140e051040d41c000c84808424466500360510f02104402003000103140700780311540c01d120302c0391543c0340b440213038000c00d5825900079150800c0554060140c4981620030001514076003894050001266440c86c01e00002403190007280000c3d102c030110110b58562090f4802d1614401c8080001e05041403a501d03406a0342c941500c81c0c03158000c2e50000c80d509426110742c0400e201e41501c040040603245100c0c00082c1191500c1e045005240c1d2080e4840a44240d886002060394000e0407440300c1c01c00d040c3c401744035604034900d140c082d1080904 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 689170026 1250 689168776 689168791
    0x18020f0307020102030402270a0507020118050d0e010311030406020306032b0908010e0d140d0204081e06040f0b0a06120c08010e0705030a2d06060905070519030c26 72
    0x4401804040b048d110b8910a20320000b945200b45990301c0c2042100202801000c2c401190b4030343c3c0900300e00e6070719241d080000601034000340012089056000e80b140a000e18001d0401d460041e42807a110145426281c1040d0301c5180503941391034035400645404407850f06004410a08064290500d229080001e909815612035003010b680ea840500d080300c1c5502d284040030b4001c4050109842e201d0f0075285103000ca40b4821606204034840000200c0e0020742041c01183c0c0000c00300e000011380000d072240f04054150041c500c030714007580c0d010491034004000030310032040d80303010620b10540c54025038090501d8001c0d142d24403a840c02c0044803100d0303501c1001d00c0c5501e0508519541c0340c0100c2c001c4151000a030080031400c0407a95003e40c3c101c0d19105440e221740428120384414144c1d105084076840c0903002c04107080d400c125403041110005000b81052140801c0520386e00080c26106a00c84081d50174000341e0348660981c15680c228140c0383c10b21518114058414010040603029400b9640 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 689171276 1250 689170026 689170039
    0x30913090201080601211e0f050603070f0b070b060a12050102030411100f080603070905070203071101050702090f0411030709020a0909060b0301170c030a1a070c030918020f0307020102030402 84
    0x160b100040d074102012040d03a00500204900d0f5030300311b0780e95411a04140d003507603010304450007408111108981009460072003c5131560107000844c5402c00c102c10240c48240c01e142c3e0502e20300f001064a41c40f5006009004100f80070009200b565060001d0004007122081c94588004510340f0324000c1d802250110760b90010003c007103816091000000918001581380c41e000a41c0e1200c040d20185001040303541d061043c6a030120b090301040c010305004110a030004c50703c400040c5401080300d00d4900c0124100b000a104540c00341c0d42d19007a040d0800c01b0301c0150714198540c6c0c00e00b92050344034504165014840d01b00b00203507000c4503034001c0c09000240e41d900300200d5110803000056400500c0b0303010240304240b006116821292140d048051054421545030180c800046400d1000309030781540d03200748000152300300c0070300d00b030999038010894640f0b090043c1140d070700036044180d03a004601c842140e0b40141b6500001507812120144403a0055a8030b0707140c0601300034040e40c0105c50883c01804d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 689172526 1250 689171276 689171281
    0x903030c020d08310f05060105132f12010303090f0819060509190c051005270102010b04052a030c0a0507020a050d030201050f2208070503091309020108 67
    0x82c458045240120004040306030701e0500d621810307401d81910140303c0020314100c4c190000080228000100b074a101d6800b80c03e00b5131400e42044070805903001640010707800c050002801403100521120b001d04c0c1c40100e010508405096060607004041001010b49600d80010003855000041e500882c1c5d042110420f04a4036000c00f0b9449101d2182902d5100c62480e118000140b070380d4010650110303121007100c520586288011082880810043d0b030307541c035030a0003070003030703007132940d0401001019401c00a20f0302ca00b0206c83d48180090100b231001c060356542850266a2003134010f03070001c0c01c005106201d1800d042d6038014a40002084134904c900c07030341100785000303100e010a40740f0841c03103401054144041d21106699683c86410100c0c1c1c401300010001c01d0075035a0764040081c460203a4000602490040c5c1125580c4801034600b0040312a06410500d413291807146020009912440b01030b1a80707058a0000d10718092400400d5000c41e108000d03658031080c0b45e00510000b4001d903240b24094 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 689173776 1250 689172526 689172553
    0x10b040b030a080a11030f030106180e18120c0708070e040b2e0803121b0a12020c010203090f0607090e040b1b16051501050a03150608010903030c02 65
    0xc0d40020100c5030160000800e610200341042e0203461403030110f040c03541d580c04034440d50380e04560100c840e840b540d001c0070006100d40741d07014000001c800314642104100c01e080030814500351900504504e210398000c14501240e80090100303114010080c04d41a4603840354000c0c40d40c44802601802d2a180b00740e46000607400f04e95030019000c0c0d03422001c1c0e442140c640b1119600003007101040d151505070141800c2c40f1070281400003000a00d201c81c041c54917092258491301c6011405000f0320b03420000c029201c1402c4950804488405c005400c000900029088441c03002e40038043c21409030394404010001605408160780c8258100001607a08a50307540f60207a0b8000064000c0040c0240a200014000b07048581c9061700000004950000703070400e810442903071ba105804019420f9481102c81c400c00804000011060510040800c4c0a6040102044601003180700240085400b6041ca480b200380d154018005080c0c1e0358001c4c00f882034527041c080e0203410202c5000c070040c450300720b82c02c000 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 689175026 1250 689173776 689173781
    0x70f080d0b031c0503010506070c0315090201110d08010512070e070e0a15080a020c10091113060b0f160b1f0b0a0903200604030b0f07051908100806040302010e010b04 73
    0x3140d03d140c59490a59080c5400e00c4099008100c0481e0342d0100341e0400302c082003c20188142e0540500400f00c1c6200051000400c1c0030f03c0b00d0400801c0364000880380b19106e8000f5a030506480381aa0001c0303c510643c42d038149040d001d6404940901103540504c4031403688550000c02641054032203d4001d603031f5018607641c400003d194200010104c4000c15005c4215030000e121021b55001100d00071030015200c8800c9a0401d00100ca441e0984201c9441a052809228200702d004d250204170051400c20050703418442c0f008601035101001034140c034075950f00c150707003505140c10401d01c01e45468422190074001251145643c1d40c800800c200094915246080790f00e06161940c0f02c0c040146542d50b5000561803880340350310307c01c801e4031031503040d40c5a54000d08011030050070002c8071410003010b0b000131120302030010020000c080102a9500045003268042170f042c03071416240f15602d507a541d020340c180b2074110b0a20f81c02490140018168150800004501240300805c04a181e44040108 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 689176276 1250 689175026 689175073
    0x512031006050d0e03160312060b030c0d021b06060f1c0209040302010605030318040c0f1b2d03081005211603050304031124070f080d0b03 61
    0x18030411280040c05094072410240c0900f480d411800305919122140050443e0071158041325418100ca501d14141580400541040c00c4030080801056040c415a4a00703403000500310000c0780c1b00060ba0180300241941200c0300803880d10020f80003d003400d940c043d00c1e404140e400c248141c0d0a8072042e00c29141c02c090713a20700e8132800e84404201d640c05038280320001c28006c1080d07096560b00c0c2c0c4001170035101170004002c4640d44440c08003c881c604820803040740c40f2420480100f1101d41c0007480d00e00c2d0406d5001e428035070110b00e2501070304c060b4030700070004403d070360300401000c0e40c10355009210780104201c84000c90310039114100b0651b64180f452074000018465540d01c100304481c40c815254119400d07018060511081d44e1a010302003012091f501c0b07680e4802c94444d840000c00f041403010700002c044000400300c5410788140c110034001c06029041e58405001380301c0000e803804c1004808030038643c0c02603000e100a40ca4000b070110340b40042070211100d83c000d0041400f00d0401c01005800b280 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 689177526 1250 689176276 689176291
    0xe010605070b04050c1c020405010e1b0d060918050d0804051f0e0a030801031205031302040b01020a020a150e120709090302030705120a0905060c0d0828020403051203 73
    0x505101c040c2d11808030310200a40191501e000342480501d140c0c80b20180d200780201042c003240c0d41c00410707205000807914168090b41892a0130420b0021425a203070304107906107080b4403c1074440d4140c20380000140400d510404065207408840914080580d0705107011500560903500700e40c0d01c48006a0740079400b01c0d0010441d170003c030f81281850030303080340d0610001d02c1c04400042403401c600c45586048072080e826004a200140100708000403022003000d801d26074030b0460300310b0410f01c21100d07882103e079100910582c0c561000d020f03107902c2081000c054540007400b020b0390384e6444000088030503020f51140c001030f040c000401e540341030a100d05051004043e0041c612140782021450050640310011000c601041200d0000f0920810950200d05003644c041903442c00782c0807014047e0101e1360b0010380070b0360040c8142c5408290100f01800a00840e0408066903582c000e454040b080c0121301410b0011003518161903148142d6000e4815240308004480c1c03c2c0f0040744241c401408112082c8 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 689178776 1250 689177526 689177537
    0x907050f0d23160b0c07060c0b040215091c0b0601050906030604020c151504060f080d03050601030213030f0b060103140c1e040e09070b0f0d0b0a0510090f0e0106 71
    0x3007402482d440400762140034402a10101d012a14166022611940c414102a00e0226880c000ea49090100c0700052681e410502008403040d50356004070840140080c0c0b0414548600d4850140b074107013116410800280400301070301c10028900c12010320340b80c3c184e500380c2c002400030303503554090003c86054440041c541811566054104806540260381124850240c01c41c1c0d02007101390146014028582c2000d144a415072082c1403004450255008054400326000104011000413690a288896a14000c51256603071001a0302a1003405640a40c0b125800400414001047c0341001240d100300c0f0030b0711076a100c400044003901da6515800306d65214540c0402ca04040903402850320f0b44882c142041e80c91308c0354000c00159003090340300000220401e01009560002030110002030541d503040e1508000407107440b008640039075a03050043d6690350313901400581d111085a002400000d140b0400e6200c18480145071002a10400030400b1040030042006000b007620f20341a14405c0d031b6403 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 689180026 1250 689178776 689178803
    0xb0604090f0b060a08011d0615030618010902040303110609190507120c1814060f06090a170d11030a030c050c0601080d1106090c06070503120907050f0d 67
    0x2820081c01c0040c40760045540d5000301e4601d6480780c03c050508182d440d140c40c00c0540c50401a4584616092031480ca00101801004103a554504107090f100c00d14240141c2c40ea65580013040510141c2d04164204600000001075158041d030000c2065038400e60310a07041d05691200f2658498003642d401c109904001072400c28801d00c001c021504074041c40840700300316a11113400f40c40743d141e25001e0b82c40902002040c041d031411501c8528880000310b03002c102c0304240c4444003422150140c00c6600c119401008806282d40e41e0080e6070894600800c85003c00369506160b01c6000c0d42a47d02c0159401601c1e0150703207041c0a00031447d030f000da0041c0510306d42a000c1e0f804400808403054034405000d0306101900321940200700c0203020701954030040c02c03030422102000d81109200c8112201070b0f400142000619180030494481780700007035545e03c0c0c03038010a08d403540c2980241a03448103800606030070420340d110f0000b514011074009492a0034128144401c0c000d25246448000d001d801035540e0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 689181276 1250 689180026 689180039
    0x602030a0b0910032a060e040501080d0e060904060e090d020c010f02071e17161415030417070b041a07170414010e010506041d190302101407020d030b0604 68
    0x101c0f0342035140140060382030170303220b14480d04180407a50840800901c94000c6c8400505042c4039480c00f41c01900d00038800a01ca4040c0200034100320046c65008410105a4111315101d03908640041d02ca02c5101501c0e501c4c0010742d076965038140b01c0e4018010300c1254042d00c500c1d4080d810840d041d01c9a41d000e81001820a00c009200b00d800d0351752390289656640c80020340981542801c00c0c1c1001960162220781601c0eaa400e01c1d46420f900314500150700818428a00e5480b140d40c40074007603001c49030030b40303039555401e0410540b8400785401070720b00d40000f241010004070740d443c103218a1041d058400425095020441c010320b045401d840816100c000e031034040d0202c145c4040d480380c0b0030038201c1c4840f10904445802e542e240f4410030070301d83d10f40d42486028a4680182c10b44100880320141c000c42002110540c0c841c1c1980d20001c2144254001c401032501c00c0c425407802e04400b08060003000b0300c80444404503102240c060005014005106503594800e004007403040000614682c02c1509001 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 689182526 1250 689181276 689181293
    0x12020702011701090c0206100506070219051906080a020304151a100f08090307030c080304061b090303031508121308010c0e1c020117041109040602030a0b091003 71
    0x164140250924000710702c4642c80e94440c06803480c0034001c11861802c0401902c2d040010300280381183c808003041c011078503064151100700303404a0348003890b5010758480c0348074000c464015542212441e40c048104111940020044906650304c03c1000d6462480c0d9000300c0c0410b60300181a0061a01c64600c00442a00b21504000e407003922100040c04240016280000b19003802010512490003803500d80d4102440603444042100594900820b03503400500b02030f400700000708071f20b101002007400d0223001d51015400900207030000989002d100c41c06429540140310440029003883c51002190048060010403654800d0062180200d22504443e2640004250b00400c01d040240001d003100240581610600301c3d49a2107107a100b103105100c1a888003030303244952032401141100050b40d0241e0149003218000004010755101c628110910071484524a58016401000e00050107a903900860260416480030846d0a000f101402001181110710020700c2000e044c0030404a407560 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 689183776 1250 689182526 689182537
    0x50a0302130e010f06090b0303040302061b10020c0604060f140610020f01051302030d020f060a0b1503071206080a0302030f0309070f0b090102070f18091115120c030103031202 77
    0x800d00442c82070b60908156013120100b40c61880710640341c0c4410480c03100c1070310038032500781c006501841c642803e54010810343d00c2548030141c15584580c031501079286042c00800c4a4080b260802d55a44003e42c0e065541e0301d00550b01503588500c0c10360042c164004500c100005100c512000d02501d0369400100910202107142041c00c0d80150100640b0707046080c8100341c82501d16070000004101d440c0141883c0084074102982554004c3d15030010360900020b4803940911034104c00318030202c415000c150b10701041f800c048440c003070101c1440700041e004000b207003403071001120400403195a4255103590b10103961000e40560010001e0f000c0d0008c0100056034020310810491780d0a0f07030785d000030000f521540e41c01294881c1020840f08525a0305002d41001056100108030f006810909811004502807481d81c480310740e01d4454a00300075121024600c801e0000b000c40125180040c25605150f1000105240d1948000000b403020700040c425607050b02d402da034410811500f110180070095000 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 689185026 1250 689183776 689183809
    0x902030a022b050a11060a0c0609030203070206030c0c011a06040608150604081b0a38030a0204030c05060301060504180612032006281508150a0501050a0302 69
    0x1c2c4040b040184450072240d0310300e14400c00007060082800e0070b2544411102c0d50035240300f00307020003840c030b0619071041d140c3e8035064000d00c000844101c24601a440c0d8414000000c2d04680302104100311a01c00c2c0001c2c1031480f04c00802440302100034040c111002102c510055071111003030009001d00c0388101440c7c1e5200540034400000d2100b03010000c0c1c20390b045603210841543c0020000d9000003462181144481419510a40c000d41803400e82c51205100c00710f020800e4604030040c84400c00280400214014400d400030b40e40e04103a040400030358024003042e120318070000c1001481d403c5c01002c0324129287e590f207042c10035007014510380c1e0021806503020b4009450b280c1c003080105140508100c018840d0b00c48001009401ca101083c00e40c0d8103090014a8100300c0c1009600341510440f40c0f40c1c6400c204038110105242a540c50007810300011302d8002a01a040108044000003441a259820300e401d000e42e40c0d0300d801c20041550003d015003a00180c07014010001414107076800d2640002 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 689186276 1250 689185026 689185069
    0x807201209031e07060f05040f03020103090206070f03091d010b0901030c0519090306050f090a03112103010e0907080c0618060313110102030c030f0a0201060b0307021c030902030a02 80
    0x2007200f11207440103211040c81c0d0304080010002690403112241001403641405801c1038031f8416008004d181c02d02c4003a040c542c91358981d0045585070001c07a0f92069114078050500c44403810000d11100c000d010304405a8100c0e406400301e901c601c90254125107181d44980c0c545403480004401821200d40c035103043c000288407030401210b4030032045089407855038a0308070f0f051035030401c03038156034002d4580300c1484501e03024410440360214900070700f02c0d01414441c1c801c28007000814500711103c0c00c4107100d90203080e00c0003410407004000f1412031b6211801110b140d103449200d140c84035402d100e9100d156221000f96146810034201400380d000d2070040c80e4034000e9042000c28900c3d0f10458030018400141741000003046410b00b81455111002c1c4010343c18400c4d2080c2441e0b0303c2c400c0d40010212410003140c6030241034401d401c05030103802100c9405849080114002c0d5a44d400b0001c80b884900881001c01c00192007440b40056042d0020300825520751103401344588545144410a075481 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 689187526 1250 689186276 689186293
    0xd0c032306130519120806060f0d150b0406020102040e0603010b090417120c0a0f020313180603020409050f010b010f0504090c2d02010609021e130801050403080720120903 75
    0x600a80c003429010300503001c002c0d030080d070060000e004000081c403482c4500001d00104a090944030103031001c2d422b00440025514540c41e9101f81042c2c00c03980311208514001802068903941900584210b951454442e44552605801c0500382c50414424035040f5500100050219400420344440c41c032003294058500351008480c6410818115450300303000702c0006154403000d40c07104141041d11901d10145081411803007125410002c1403082c0000494180c004000110a075884400156401082000301d2003071450600d48810542402d0046035180560140240d4004c00d821301d034154445d03407a10301d082d0521122000800741b5080d000d0801a40780c2078003c161422a005880c01c3c5214032501e87c10b0030301348800a09640850300080f085500600400705006001050360160500303884e8850f4590740e014203521505800365121003c4d0f903003004207100505421000890180d03041d550b40100d2807520b180e4140345201c4221000090342c0c410030420500700a000702600007070000509980d400c1c1c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 689188776 1250 689187526 689187553
    0x1051c05040c0e10030b0a0f2304151802060322080409200708300a0b0105070f2019060306122f0d0c0323061305 50
    0x2a001201c0c00c03101c40411000034030820007000d0043d68801143d60034209018115558800030030f078041c00145115880c1c0210440404190b00b140c1d05949000750801020900103561441064040d101940c103000d003c5603045011050340501c0c20f0000f9031403400640501c965003445865031005040000c07110b281076596001e802401c007000940c0b8060890103031078a0030004c008040f11145014410421004021202140d0145c800d589046410010313058941020021500020b442c000c1c100e0088504030811130082031644941c1c41c0100350382d40342040048640710064440d803088010140040811994460010b9948117510f4080c104586040b001c168413140441c90000390042d00822021360705009019031941441000000c14006132800031003449900d40281256626882d5200e0008202001c85c000741076801e82d56242c1000b504611803400a401c1c580c031403c44a004c12203101689800c11081c580d8419010640d10020704068183d13501e030300704062040c0d401c051003111140200d440d596030b81d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 689190026 1250 689188776 689188781
    0x5030313020111160e0c190804030e0108040b060d08090a081f050c0d02070c0f0909050106060504231215090f06010303050724060906032003060601051c 67
    0x240d0a08100041015451002400350080d03110001d2640c3d0002010102c841c58040031031040b01d502c0700d00012180c0700c0e80031004c01da100c0c1080d500540c0e103c900c1c200e07180c564000003080c03065010b070343c03100e0f0300c60300d10f0703004581800c81694050301c0000702e000403807550704d840091020a42d120b02d594070310705158403010560404079940507110680080c003a00042c0940125070320700c14565840c00b0130462406258107000303401a0300c1403c441950206043c01000340b8956404060030155520302106903446041300081c00c40500101c0c0c2d55400c00d100014518000d40030307502900c4e100c4868802440702da80000d0004840000c03100d80c13095141540f03400c0080180089134110204a1a18440385802c60500e854003903a2001000154894801000032a034018103680d142c81d4488801035040c0900803019100a0032130b044400303094608200094089075682c081401c1303d01c43d05101c2400b1511100610389001e000c1d400d1a09a0400c0f00055213940c803980040403a038020b41c429800c51004038180204 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 689191276 1250 689190026 689190031
    0x308010501052208210a020d05070602070606030c06260a2f1b030c0312090a0210050d060b030c0706020307050403060509010207021e0117063606030a0b0f0a09050303 73
    0x8154000032081707803100c151040c0c00c806a903c0c404070035140080d810802943c4608000803903082100102d0000d08112294045482180d0405814015a9124141050790340203c1c4500004101003e0f030074001c05c03507555002e200c00d5110103a01100c9a0301e03d500c40005e4088220140034001020740701362800b1003804c01080030700c114801c509854a9089141ca000c1045e01b02200140e44d00c1030202035052200002140c20b0b6542c0c00304020882c1e241d501c0054540100100d0096101002c2c80d0113640079030340100500b100c1c5031020070a000c03c80c1c0e10881d0202c68402900c20140b8076600300031400106507650011500710410386403940c5410356a8070b801c0e080710307001e0704d040e00780740d400181c81d0056203030102004403241000180f06090a600d0b41c0041d001300d0030200701d0343c5182c10300c000003411682d400e4100c011001d402c80c213480007408a070120440c030345164810740c0b4208191802140c1d06080004c0d05280095005030010b9944e16100c407886241400140919a40c42e02c0d410514001401030000c1c60 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 689192526 1250 689191276 689191289
    0xb03150f2407140a111806060d0603150b0907090b04050d03050408030a09150f08191d0303011e0509040803100b180102010501052d0d05030c060103030207050d03080105010522 77
    0x2524441c034150300b0b172983c48088030741300f00b0030000680058444081d21b660008403c451881d520818000040e001d06031523400500541741c1c158030002d20004640141c420f80000303d0b000c000555800304242c0b07901c011030041c0801c1104c203100c18040c5081003c1000700042c001e041c860304080d5180c8a00f407440c2d20010b500000520040000c0240c2150104900c9100215090240c0904a03148008003602d10040c19a0401b1014000b4189280400da1126074103141c0903891a0740b00384010700f2180c0c0c9510a00c030310420000a0140c0501c4c0800d5a0080c0b002c3e108000c00c08403154585031030b204441e0f040540b020300981c582c8a40003490703d400314018109404415044900010204006400c440c01640901d000d2160a200d00c3c004141c01100c03418155010b8803034031300b00c6003207070301064118409120080151100090100c09002c0c000f07a176a040387e2181e82241d00880d20350051101c1e5841c0540d004001c1100c00005000ea903000701c02420380050004007044c003e446003010541001c4180d80300c034 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 689193776 1250 689192526 689192533
    0x20705160326090d0c05060a0504140a1212030b100f0816020705010c050316063908190903120e011505060a090f0b03150f240714 57
    0x200100100b010005540c1a12502d110420b0301d100c8030320008034801d030107645104402d1484c030103040040045802c07003e00800fa000d541c450425020150150340075018803a08031080605442c01442c00b01040300c01d80e5542c9030903d000340c403180e5030843c540100c20300d60001e2580b22150113109440c0c0210001d01230081c0d0b6207804614514030340161010320042c0031030164140c0b5441a1000a400280c3c143c201c903428a000c4a00714500d0030300c1e0b42036008455400d002c0d8030a0400c144140105074101e180703102d02600301103100c2c10042a030104204200740041c40d40b81205035144412501131400075a10030b00101c01034030440d481950300e2003110794081003180410004008031200b064a17115800c1c20b078000300001c109454004040d050003550a1140e540300b0900010f011100611800c8403400901903100074221701d40d2940444445c64004650000340407041c074590309802d00e004100e03a0b604550141002800307c4031542402c00351840c00801710680c0350100945400140c6504c03100c02100c509174086c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 689195026 1250 689193776 689193779
    0x26091002070c121518020127171e07080d0203040e0c0706090b04050105070305072c0a0b0a0c1e02061605010209060703170703020f0a030509120f0901031b02120d02070516 75
    0x9440c6e200c3d81414101c40c00e6031780300c6040c1c200c1e1448c0414001d40c0c40e000c10b4490051000e621091800c1260156050a02e005075071740061024002250421384104005651001803400b4040b60741c2c1c0102e129524103180c5800125810800950007845c3da03500070b6078081010195a15a040c0f40300d0f0903982215169554810068900d6040c4645504980f10b45011071525403514078034841c29101e0401160020000b10f03d5403002d6541a07a280000c103100c02402d5181c040703108000d08182d005c03032001d5468201040f021000300289004d10f05202e0b80c0202050305100c43c070703d00400d039410791400440e9203650030030407189144d4656028140141c8207540300449109504907205581c00064004800c4c1401402106101c44250301070351050840384c43c0005065030380a0860346030154401d03a503010040001500c400c40702008006180b520020788050198081c000080312211000500000050f0003400d08407514200c800001e1011807105240582014016102d035800c101044a001140380c108600 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 689196276 1250 689195026 689195029
    0x1050f0115091a1c0515090a1527021c0c03060b0409060f08010e0601030b04031e0302040e16080a0c0c0b010b090909030a0207120326091002070c12151802 68
    0x5214480490983d0188030b2401c02d1040b00c11b100e0095822548207801c40c100281030085980c0c4040040c8800c0400500c04070394440d41d4054041d482c2000706141d000c0d40b103010400c9602030080b10721003a451000b40705a54030001d2060002c10016a070342d030030182c41d40d00004141d4070800180010300004100064500e180107031a40030941c59078000c200b143d050141c058208000428468110394200c12140016a91803604569130042d004403003a2007201500405800c603410f40c00741003a100d18085c1142c1c00d07160245d41d605200001300500c0000b50980e00090740f000800d0b00011030303020031030030110005683d50b5904155413209802c060048000403820b0b1180e4684885419041802c00014618100d4403540094030b40c030150060201c4d10b0030920901080505c110142d00d4103600744440e00032000c0343c01c0b120600010060350b00c3c408603c90803060130008070b250310031600300399880610450010324084004101207500350041d5100000e000c0c0c020341507007a030b020700c51003034418001038a03070401c1074030 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 689197526 1250 689196276 689196307
    0x705030c01110430080702011704230f07140f1509040501061e031d100903081608241c03140301050d0b09010f06062001050f0115091a 59
    0x250294071040010070380d082d10500310140c40800d504019526502d1201c1e00050350b15611203c8000c407885048020402400309400c10540720a4bc50420b4003a40013000310100d41e1100040c000300f0722900f21140411000c6001c0510110303001018048201008820b00001d018a561500402c240400040c0312413051801e8440c40340036200c1c40c00c10301900404802440c15000c0040e10240034075135100403d03c011010720728004102221a070445440e5840c03100306201500075598111f01080048010404000301c030451052001403a0380c41245a680704045800103e402c020b02c1071a200081c10b480910b80c840e0900f103407902c861810904142a8286401012810b44801c0b5510410303090005104036640c2c0b00007651a90b40018170f00c606070b200c10407200d00401c01191203000c103a16108001807840d410594055402e4000c00f101c0c50207200400303005003130700c81c225004c2c01c285112400500c000c103245507294000004030303d400141151a000130012b103610200d903403c140740b00450070940c1c030510b50 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 689198776 1250 689197526 689197559
    0xb0f06010906021b012309010f44010b041401030207080f211005090f04030801061b120329031e031905030402010f0905060d020705030c011104 63
    0x203103403000129181050013074813498a244140340741c8000c010041c2c07182e88940c010f001a01000e16441a8464414000040660001511a000c18119011002d00c80d0044950480d4901501410f0b1100b442d502100303080404820b48032500f41c171200c807403154240404070742d01d4003a081c840102079881303082c981c41286000d00403240a04240c010040140047c2810f8181c9049075840c034001a254400d03003600d40343c5d40400030b40d23040f46111440104206141d0101512080392010348054a1584a0050030a140c200445000c1d021900d04001044201d100d8810b80002c00408150b01c01d02403810f6484948071107607a100d180000751160312080441d001640c4194886140f40900d80407003982c000401d46880d944079004040700080d10703102048031800d00459051003400d10550715030114521020300580c04c151030907400940007001d240501e40c051007800741969001040a41001c009820b510f007c1e5112003c02c48480c0020300c590320342c0a0007400341d282d00d491032300c0455861768180400c11054540e003 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 689200026 1250 689198776 689198779
    0x1120207052104181109030a111302040302030714130920030115090e030d1407080108070303050301030215190806130b06030402040b010903020306100906090b0306070c020a050604030b0f06 83
    0x20481008411000d1030a100c024510b0341010480b8025208402d0441c0036055401f9014061201c016041060307010503410708000440382c441d20340030b0540b20300c8128019800000c5d01940004801c0c80721401c2e80801c4180301c0346c01404d150044c45840040025112424170803140c2114143c03210380014240302c4141c404210640003000401448a40d00040e001d02c1d11480b00201da989002040841080c02140c00c1903518803018422084211500b1414540403601c0342e000074410800418419404600c600469805540b07070381c04c41c1d080d43c003041401e0303c43e10704200281c402001802d1000e040c0f40c008074600364507516513500030300d00740317050100d01c820040c03108080714586070362411107aa07101c00760383e00075405a0b800200140030400584040b88140c00113941403040004000c00001d4824500094504400040c80817a1781c810b540d000703940070b0503140c42d45034022030001840384d4840e01c0c64040240c0020710725003005503a48045202c0750710030b40003610445808001c12001c07000c0140c8a5800100 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 689201276 1250 689200026 689200093
    0x3071706040614150d020f03070612060b0a090e130b0412080c09031b0303041a071208070504030219050402030a090c05030601060c0b1e150913020604050d020112020705 74
    0x5141c207104e181c03004888019480381c0325600a850a548901c410041d8030800a4112684503481d44005021240c090b1040607a036070914101051104107001501c001d01c1e201d403203180407141407003180c0061490003042031f114205a0214003001c507401a40450040f80901c10403d110b008043c0e000b8034108d4010140001c0540801c02e00b50b560320000756901c405071014810041d40e8181c2c10000303042d4801c40d8881c60950250b81800401c610030721000b0881c080c8980c143c100c0e0740c0c071402c900780c43c15101114031601040d81408100090f0628262102d0b00e0b402d0745204082107034943c00010100d030000e1343c0c0500d01075500d40e07241e801c000e114808400908030441c028100c56141140041107911403078001000040d0840104070348481002d18042000307040381052001d0300c0c218100f0149400a90076491045003c203003c1005030b10307254414112581c029052502d402c0c100014083e01c0d200c1008101d0421191041100c2c801806101034058248944040c140d4210005c40342950701c01c106500f0f407020700 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 689202526 1250 689201276 689201281
    0xf06061816020c100302270f0f0d02030714010206010603290d0203010608100f05010302031c021005040f151e3c0b060412030c0204090b0f04030206010f140d0203071706040614 77
    0x43d291038503110381900444a910000c100027020074107800d94800c000350148641f14001c41e5140c29100f05001070364081c1c0c00c0b1401680d81e03080c102d0070b80d90350651400034060500740750704044035032461509014070064842074140701103a001c0380c21510940e025040c41e412001e081403503140240904901c030501503006001d1541541c00003501d44000070040c2419545501110245070f00030712441400d0044407104211518003418002d820a15404088500341201e00c3c55150005207803040c808401e044807002460b6511048c0c20310000c0030440070085040521518216415140306044e607e40d800d2a00c040702a1109801d00009581104481c284070761002e02c010b00c0180c11f080c00c0b01c110035800d4542142401842d001003030051000c40809860b10070114100201d0208120481e8004e611940c01c840d91a039a82840b0034404405002d041208900003030442d004d860810307070306089140000c0554045e15078504d410700b4040040d11090a85421480410043c0602441041c610140043c251041e45c07 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 689203776 1250 689202526 689202529
    0x3a0902120a110906030a0b0c13030f060603020102013801050c07080a150203010302030a08070204140c0c0d1e141218060708070e09130203030c0f06061816020c10030227 74
    0x8007c01403c0042495004c2403118107428040b2001c001540c1107810f2880420b207500b40000600b260380402d038055828071902601e4909010005184404c40240c02c0040c40c045038000c803c000303111124203040020038030208006071002d201c0100202051030041c4035146241c5419040b091070b40c400d0700c2c2c1240c4103200400160300d01061801e0800e44c002c445943d0f840c2d041c40042c0040008080c00130541d1442c40410010fa100d501c000c190000c8044119425959820f404072258601c24140b0f403003100b44d540c0c1c2c0c24001070051003c0c5400c501c240c0400c9091100d002c0003420b12171b6045940e09000e100780210405651010310125421010a1500109a180071a006031503005001c940c503011303600800015070b070600f40d03482c50b100c555070003400d481c0d0740d9280c20f580300d03500d030000203442016005200214885140622042030400900340c0c500c59243d032084481d50190b480c4680707078800e40c041e1100418584d5902502c10040341140c0c1c5005071a0020f114010b04a00010b030080e41c003400c0c0210014000307 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 689205026 1250 689203776 689203793
    0x1508010509150702190c061b170a03022206140301080a0f03050705100b0f0f0f090709080d2a03020c0906150f3a0902120a110906030a 59
    0x80340740c8802d03603030a549803680101d00d4000a80054910050f18002032010007452045042c103c0710580c0d128040301119241c0100e000d103040750002e0030350819105000c078807840713040a400a40e001d41001801c0002414001017000140c072007043c26020440742c103001041d0005040803003e0080e0078124103560520044a0b0783d800070742c00240015a03100d280c902014890b004651940e0b03880401d07034030f00c100b007401c074000a480701507460f078400c0c0640a1113002600f0904604034103c10003c088040341520705052200c1903030040c15181c2042003030100412448010016008440c180313558224021030440c00c48001c0222003844480300c6400c0c3e90800011940c0010300d014000d40807500101c0c00e85a07000002c00d849901a900c000c5000045140710400c2d1080c00900841e144519100e00741071039008084524600b408100722054645078480742c44603604ae884124214406051800300c050790800c441d103048d0000c03d00300d814404000c054952810040139454108000390020b00c01d94121b940d40042 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 689206276 1250 689205026 689205043
    0x3120105100c03021b130219030c0e030c0f1504030b06010801060306030f0b0c160303020403060b03010b13021303140c01030c0e0303070602030c070f0b040b07051216140d1508010509 80
    0x5000c000080c88200c82d649000262540d022140c2e0300f19625230b01c546002c4135026130200501c011074549106040c9150180f0000200c00f10b000f0090559004240200103041c00c0c0c848055400c00040d401c07503c42c1c50074100090001c0e5000d22146503061410030001031169405801150805013030110400001c1e0700c900303880d05101d500c52a104100e40c2c0c0c0b40e2018003103000da0a40030065428070185003092580581c01481942d002d89d5007400500042c0c400d140c01d03103c0350720441c0c1d001140e0000c00362416520303601a00c0401c00e0400d000c984030b5a25120068078110508102c02c075504240a041001c0d0703058031503014a2a26400d0010700300807880002a241d00841030b000e0b140d03980000020f001c0703608881c00c035007046501c9003500c031074540c0c0ca0510716049030f03049a0444102001d200400c0080d0f0003407058603441c0b038402d51401896a01c280540034581c40c960311043c2803142a40035500000100c0b0081c1200780000705000522210400c0940d00c140c010b0f9002e0f5060703916010900185003004600e802 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 689207526 1250 689206276 689206303
    0x503192108130302152a04060504120503040503030a030b030606150a030c0c0210111005010803090f060d051f050111030a030b0a030b0906060108160c110105090303120105100c0302 79
    0x2e11000e034141a4100b1143e101d0049544074040b0410198000d1002070b82800104c01040180c48001003d115030a0300c114014800410014002082070400040541450a11a20a807804e269446022902c0c41e003000f420b0350080780d218801041c19003400c21440398400340440380d01180d05a001c0c1e5000442c482c0d1148842010b855080c1d500c24030b400351a00040003640503007820324003c1420001010181040030144060007661040f00000c0041d0040b02d042c1c0750380f10301541c40d2808400030402c00c81c00c01c40d5840d4201505102e8078644210910865204c0d04e4107007858548000345049400240c00190080d605100c1550042c500000b000010350300b81050074240021500341c09030004110408950000303000103c1d10f03041203040c001c0880c0e424060b5070280c80315801501c4600c414000405c3c10040341780003865190295000c02c038004001d51404406040803490128594046421940100c83c0c03030f03c504220304010802400c18585030140c202462030903020255070341d98002d464184020703009 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 689208633 1107 689207526 689207551
    0x9080c011d0601030309150905120c01110312010311011106090a05010606090803031f0b0a09030b0604050903070f03030f09030e0f03010c020d180503192108 69
    0x94181c9170b0648036001d116042210512410540c0d12402c810841c00d0803001a0742e4075180c00e002c00b44990039003d442803404280c0003604081142030101e0850b80304214401c2404298900581500c0d44000d18044015a12004a42680c0340c4c500742205e0740148000d0210a003000038a10000c0c612440090184641d140d00c2510482c00c0341c4144200c513041000001c0c0404140040c00132082c0e03190a0b502c804a881d08910100f60b008200b4070000706203500c4c418010310021034805a03000d41c08950078412450204802c1d130300ca00a5010003800302220f8806c42c01094081d81290346090411101000300a07020f0900901c031140b50b80c5003c0c000c2707250f203483c3c8801c2c0c11f060003000e418201c0758004084040740070f031341119004904c10000b02c400ca001100420240c0d0144840c8000c9900384203404041881d44c101003038030b1101003e508546951021900c1585500250826404144000030 = true := by decide +kernel

theorem cover : BRFrame.Cov 689028776 689208633 := by
  have h0 := BRFrame.cov_init 689028776
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689028776 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 689028776 ≤ n) (h2 : n < 689208633) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
