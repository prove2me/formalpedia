-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5548
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T16:13:51.569823+00:00
-- url     : https://prove2.me/submissions/ea711ccc-293b-4368-9f4a-50490ea85694

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 997661870 ≤ n < 997841726 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 997663120 1250 997661870 997661911
    0x40506041505060f060a02030f0f070201180f0e0c160b0106110d02060c0309010e0a0602030f0109020313140f0a030e09061005030c07020604050a031a0c0c10021810020304060206 78
    0x1401d2080d080780055070141c0d01d580c00c140302641140120400c4003052700000641c0c0302600108030040030000d2007600c03482d207150344440040080c84001d008400a00091080c24403924144d00300c61584401e07500e544c2860520301e003600601c0070891440885983c280080140402c40e0000403c140000c1c0d40d400804042102d800e000b90343e16805083c0002c0648000007062410780c0a401907030000c04040b003103407802d050381c0c40c00e5402588201d070401da181c45408004141001c0380c3c02201e0040304040540300c0c800c0c24580312010708500006c0c410090740f02d54044e103986140140060f880c528025250060980418030a003c1b40306002815079201300b00048070b4461864000040d281c020620410440d11500c10344080b50b407500c0342ea0409a40321801800010800007518a51030039120342d20404101601d9803021100b043c05005143c4603270b034001640a03840003c81e039010f0700035400991038014150b4100c20100701040030039280b8900580001400b8000707241c041150f82c3d0442043c214855503072505 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 997664370 1250 997663120 997663129
    0xc0108060f190b070305040e09011b0503070c170403230a1e151b0c05030414040f0509150f010806060f120105070f020c0109231804050604150506 64
    0x505250030702c281c4081e00c950585000402d400409000c0703400c04965168001d08014002e80c020341b1441c8110316200c1c001940b04036041c0038000150070032044500d1401230f0144c044e200d03034000604100811900421481c085101e02e000340301c0c81d4000449071655281181000c201c88007144212140c40d030001542c901803140002984510aa000800c12560440462002a0702c81c1c840c83d015059a01c5c08080c031400f00d5180d0700070b420030401000011003c0c1140d032000c2e200410b0000c8058010307007040c0810844a94210f074088103056008000240d4580244402c1049907400c1d690040c450780510b00f100c03804419030400307640100300465540c2040d0301d00006c140e52450b00a0941e4050b03040c00901c80f030783d5116000040c1002503800700a00c164078010720001c09507445034443c400148a0700d50362015550082a00b48191030201002c81812000d0804140320510007210305608a40440080070610030000d0041e4000e52060015220b24200303410000d01c50300da010302c0414054501300520501e0703510b = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 997665620 1250 997664370 997664389
    0x615030b131e09030e280303030b0406030c031110140427090614161b02120f01060620190302011b2006010b030c28030b030c010806 58
    0xc8020041900380010300040005502c1121080b4680d05026014007010b070400707001e8100307600c01c0c0c4a01324109a214450003a001e100385400320100320240b07090002c40e2281e00100c0001c40c0141010400b035a40b55140364400190340e00541d494030b8078054580c0145400d520060311f02c0f04070700c0c0110b00c1c0280069049107622503449120003c6211722280c0e800030904040d4080d19241c000010010481c00342089000f8000080603048410800700000c0c1841504000101b074480c0250b880840744a601c0e9441d4000c02407840082c0d0303210840329003811801004000411080214100102d0b281d4503000c40130300001407800a60070744000d05401d14020aa00148a81c11075401c0205007050000301e081c1a40140b4540341c0f4120250310703d52295690316000304400680c03d2035500d0810300c4034803503500b80b40c4a001c01e00038a140301408001081c186540c9070302411400392542d4601c0c40c009404114501180d500c0c2c2c050300c1c00309403100120046482c0c00c0c4080070420000b82001e0702c0511304100043d241c401c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 997666870 1250 997665620 997665649
    0xf050c03070501120b010201060b071a0a0510030f0203030f270a03030c11150d0e12030103113105010503010b030c010503071803050109030309051c0807031e0f0615030b 74
    0x260303501e003000c0d8a1ba100f50401c03c0106102c414240d40d030640d40c1445e044251590703064240380680b400c041100d40c641440742600c680d01c0c80501e030141038107543c2c60b40301e9101c0d10403050760305100500200391080060401410b000c44031980c803030075800c14613104190007603070021201d124000e1a401000481d41000456080541c014030f074401d050f010200140300034800051104241d0004602900b0359415580010020140a03044404030303c95008a05410f00c4240802803040440025086003418030007c0c8803880010f0045089100c540340c0d498001031151850845c4c800e54a800040080d41028460501e140380140d01a0030035040c6400080d00600c0003501100c10003d41c00100b200030100c540c40d0901541e0320000a00c121581828024080c0003442c0040ea21405040e0a00e500c0d21031701d04001038080d1440d00c482c165039036140016401001908040700307402c82002c040901a0350244154040d01c026483d000900a007001000c551200c451000e6605143c0341c000c02c50800c1d1340e150041402003 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 997668120 1250 997666870 997666907
    0x90e04080403110d0c031b09050105240f13050f06071a070207030204050405030403060b222c06100b040b16030e100806030d050f03161b0f050c03070501 67
    0x2a0043d1010407841801c5550181003401a04804010803400900c541414100203a4011220740c50726a0f04007260000e10540e40d01554045040f2424a43c5824031448090284416803d00d81d0000203400c140d07100e003080c1082200d08040500131840c02d15295a811582640c1d80303410940d160b41ca18441c031550502010312204541c0000740791520170000780000d50340c060400c0c082410281f0b05140d4079001350104445141c01c00b1070780081800c02c2e094800500d1403003a01e0400c00300a844120b40101410941c01901034403428207403c60000c05c010f141c003940c950718024910307440e00b001c40302040c941c1504003000c449010441001800c0c99034080da2882009000407e0104490b46400d44010004d8000c264200305040000042c07a508904051311840054041e240411150801141c440c4500e964085a2980c140040740c40c1e101100c4850791007502d2402d01100c84400741d855402c08038885c80301203543c0702c1c40c6170f4034100b000320900080d240d080040e0000c0c04094240700000c1d200341004819008034 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 997669370 1250 997668120 997668143
    0xa021320181203041e15031107060f060e040812060f21010e070e01060912020603010909050106050616020f04090f0b040804090c030c03231602100e030a090e04080403 73
    0x18070b428404c0f00c0040c07108600c03c0e144242c1c20318200300301c80c40714800c65000701c4001402c4080c3c24028002d07580700030791400c0c400d85455a10395a0307500400044e45008440340d03580c81d000c90050325901d150b50003a40135200c550384480700c1a100c000b6041700144443e008001e480c150903895107039001401d0309580d03619030040c11201d040a070030b40104945282540c40d8400c1d2070000825240028115050b01c0050f96181c0743c95484140610301c40d080c06000075004141000104061811a03006d800f1262003500041038055440000429942004c7c4060108454202c054030131071404224412048500351801d01118109440da11300c403041e101005401e0b071034101c001500301b20049007250083d04400c1820800d13104070550040c01040300080200202c0d00c2c0c84040d840955040c421400340f0311350018401010350b607503d084003a030090b800054055209914280441107042d003c0c00c3c1d04d0b040c044004640780c4500c0880140350034955130002103e100c229041c0800f05012400301c4007901c1c0c100c48040003 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 997670620 1250 997669370 997669399
    0x10020d02070602030a14010902030c04060507020d2a05040e0a03050a110115050a0b03090c01050a03110f0304021c031209110603041a010b0414040c020a02132018 71
    0x103445403641c000d0a2500c0042003025020840d07201165150441c02c0480c140e130380b251140012031100b070b540c0410001041c40204103540c4528001c2c04644c1c030280c400180d1420031b075140702c8000141c2c07040d801d2074500100805551600b1041000c0141002c44051120410b031001d140e8a800031040081c04002c40000d900203014050304040c441144000000c010380d41030212030070110f105a0040320711851000000144045070322040d41d01448201c0043d205601010006580c107911004121703080c142c50b00400385581c4c40e8100580203402d490300c201c0d5600c2c5424410080e01c5030013a00e0482d40000f0203c8208007290340700d50341081440455000243c104c1c124148044c03045003403e089a4440380c000200010000803042d8065104204c03091222180d80724a40400540510b020b2441d2001030351942d40c50394034141c0c00c0002a43c20500550f40c908040d41c0115504a8104540a24040e00c071005014080420052036000030f410152071410600d40c0d800c4003d0701c4902080f82803043c00d05096406 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 997671870 1250 997670620 997670647
    0xe10090f15110c0c0319050c0904060e0d02010f060803030115120b0d030c050d020606060d02031005090c1c050c030c130b0307020d081602060118060302040c0503091e1002 75
    0x1c082c0001d55010351551404210319544005111195029014610b1114030401c5000ca04c801002ea0080180c2240305080e418042c00700320040c011354000b900e41c44500801c2809101c10301581c20b55a00118400f5454510703803058489d40c2e40301000c81d9100f0001000000884c000c0011151281d10304112080c4c4141c06100c0540700004041d5409541000580e04160308800c2030b4030302c684141c080d10b00b002c178010802d1342c079401c00700c6016401001c1000600c2810750b0541c02507510101c1050124110741d210008603080c1710080301c0c891000300001500b00e08442b01c220750010245607080007400310346441b1100400c43d02015108130140200402d100200c84c178000300110203400e2010701d854480ca0403800c021340e41e090327040200c00807404d00004150844840c610700e02070034040340c009202a91070030350001d00200c1460041103009607980c074003000580e42ea02503540b240303074941d56441d00d0381042001c10b400e05081c0440090400c404808801280c100400c05a4800c200e911005880ea485140c150 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 997673120 1250 997671870 997671881
    0x1240804080d020a0c0219060801090c0507050703080715180f2a2612130807060206070f08090c0906180f0907061b0f0201050d050a0e10090f15 63
    0x2407512400031030902c8080303502c8541d9a050a008803261510035484000c1d410031f002c0a400764400186141005010003030b0f40390803c8820601515121303181c0203c0703481d4282403c250f50000c0b00c064400044030002e000f0840c070641c041070980c0900b00071140500300e503d403000d0060703070009181801124003c1c0c184460740c1d010081a0b80418180300191540c082013200c0583c0707502480a04160b0482c41c8441c1040c03890010040c00d066000034115000a180c0d0603c0da500a2016540041900c64011400c140c040c00b442c0c000302803640061882c0d040030328001e80200078115030401085042c1d010000400741c00650412021400c0d02c6003e01520b400020500e0036841d4241c0c0e800c904a15000d1052040c0c2d1a0710b09807045c40b18505031004035031a20400c9402500610b04000055989148078010031007410f004000144141400c3c3d10700144400380009465049500c0d4028070744d24070032040c0220050003030742014074401004100d6140a03985d034501c0c5107000340c405410612304807228001c041455018 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 997674370 1250 997673120 997673137
    0x1050c0324130218012a0f080c0304090207030807031b120608190c1d0103080319050c03040303060f15081830071518020406080c090124080408 63
    0x10b5540b41034030f401c0031030080c841041440c002007407000614404046603201b182c1303031400302c0010505046640c03210070440c1d06548042d644514100200c01078050104002d200420340d00f4000768a0302c0007804c0141a840f070041c0b00c1c0c401e143c2490190745480c610a182c04002d83d40e6414030445900c8440901da0042c51903403c0100c0f50302c1201300d12844118000300b203d0541d8859220690020345801c0d11040041c20b00f00d2444c0e824000300010320015699030091a8402c18014203c243c0141c01c5208a0554209031400344503040d000050009040c0c0c503004130f40140c207030484008045890421884d17010151805107900304640c81d40850300200c50800f81d0840341030bd030411201c50311503501c161500110100c610001ca243c00641403900d140c3c010042d1001660024071055a41c640c1c1712542c400740454001d942a8012080e4400005903070b24815a0040d14441e07004040c0c0190744018852010780c10380005480c00301024810364000d0f03c8440103001c1d0240c03403030020400d4499240105190044145 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 997675620 1250 997674370 997674409
    0x903020405010f0e09030408030301260604060504120f02061609050d141903050d020a05130b03093f07080f09010e040b09010308130b1b01050c0324 65
    0x20360f03218041c2c9441c1030320b8005901d0340b05078403202c1525540c1e00c142e00c1003c0c19600b080c401003002807022103900020b02d0b40741c100c5400c0505d40348122810322004503021074105540b0000e020901004005a51032052581840c6000420303041e4041d6036200001e10480d05030a00d201100c9001e0310178414400104800740216940602500d00141d600319000d042c05194802c5c0003051764000704e83c07000d42e008160952562403424044d0489800a9404a6854010312400300025010030489008000c02000c120041c5070310313030509240060900d0b484508105460303003842010f015a03280040954410150f0b4211030305102c004405002c01e40c0511580500803400100d44030201c0b02c03901009211043d0266281c4103000040000c2008603000a030300b40390071840140050001800000041c19100c1c142044c1f051080e40e44c42c80c01c01c02e40c0c083c068400044c034000117a0790b0741744024003949130007200200200e81140303411212210084411601581f0025804803068000c2c1c80c1d658480c0300c04030248a = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 997676870 1250 997675620 997675631
    0x3140906010e090f0a05030a030e0703080a0309061e06050a0914010509042109030209070c08030f0c09310e120a140d0b0a06030c02030d051f0602250609051009030204 73
    0x700030380c0381e030041018032300483c2c14056001c2000d40003250103029658003400c50341c20103143c41011402072040050840d01781359500010314a0441000d4815418040031a010880ca0b0401c400e001e40d030a070507480303c3c4885080500f01035031540035902103030568005440d44c5d07045a0350380c05e15888401044680d181005035541c0b0406082e6842011101500d0090f0745254207a01c40c06400c4610842d6000c024228000500100b94180781d20a10036401c45005078405080c100c40c0b00000f01186030752044103e00041e01c0001c0100074880c1e501c040304d501d86000c400c03c02c0c0202e0558840d22610b4030004440d03440c4000610b400c1e80740c05001c84c00c0d5a00c801c0b090b01500c8680c1010150010b100c032202092080c04651700018445102c0d0192150364400c540c0554207095a04a024014010190401c5801c03162000c4034200c1e401200b103c030004244a900505000500c0031364035180401410700c0b900e12050002040c00915009900030741121401d032102001d282002204072036180712130304002c0d4080d0804 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 997678120 1250 997676870 997676873
    0x20a0801030b0601051c0902041b02012708040e0a020f04031208161b1a0708100603181707060f1d01020415080c0f0d0c03140906010e090f0a 62
    0x114038140e030b11580080940e5216840103480600407140e5840f071050100020f1240c100182d0402c502c2148082c02c04100b204416040a48140540310b00a0043c0e41d60301100c00a0071072080700701c084040c0c400d180d4002c1c00c01d60700e07103204a02c5640110004050110041005a1019030444220030b08032466203171910789910340500701c0307500004600000b4a0102c04a03008100204480c01880c5041d145c1c070740200000c026031041e40043c21006d868150340001c1e0038019001c0012050701c6a9495079034641a850810242c040c06540e980122080515001c04c0e0003224251450521f0b400360005403c01e042c4807203641d140010300c0380c1800148410b040c003034a50813006082d002003207004013075541c008803100b00030811400c0b4002c500c20300502100e01c10741c8116641c0561003007608144040c01c4149018039a154201c031641c401e0844441640d52000700f444403960510034580310910001041c042400c20b40c80142d511b00060051181c500038500100e500164108420300030500d0084c1a5500c05540703 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 997679370 1250 997678120 997678127
    0x12080a0908010e073209060d1502040e011203090608060a03051b10030209031518070303021b060a08060915030a080714190618060e06100e070e040b0a09020a 69
    0x52207841c417a0004d0444a6003425862680c18035000d04a000c002a0f00c41940c00b00101584064001a041210144402c001c1002c03540500c2c2c405c0c88080026079102c0c50700c5001c83c14410140c0c8144401100145800000390303009140804484107480c1c01a1030380c4401c0300003042d28825520003016407103404819090340005070300c62503000c00200d034200a5425101d005509a00c2100c83c12a490303002080749114241078002c500d6001205900404500d2501c9005c0601c0d1902d50342050b005a800403007281c824114880c0e003000710b0741c000d03075003541465191a0050403d00c80034020301c6c460310303005000902d01b03545a80260426000101203820210850804414035444180d060702c2c900566090b80c2d070503460010b0a00300c0f441426283e10310001f05512070000419005001d04102c4480343e0341c2e107002c240140071390081d101146010386032070300b0301c8241c0c09090605035103d407568155450800c0407154000d00d4440c0c51100546022480600d44000684083c05942110000c140701040d05400c0a60 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 997680620 1250 997679370 997679383
    0x150a090e0105060916050f0d061706010909020f0d02030c041b03060b13060c0311160801050601082e0f060f1b0206030703020d09050d0f02070e0112080a0908010e 71
    0x40c0800070001c586450703081c0800450119211440286200c0424132510b00c5100249a081900c0d61501d00b41410010300c1020b6501c545e03c002c00d20300349400300d10400c2c00d0a102d25801041000b004201c01c1d036583d0f01264601c90074131105485490f13290f03408015902d081c0204403c50b500288200303c44620580c0118415501245800000346002c40100355081c04c1d80c00c503401d406c8502c02814109260680859582c40c1c408012010413469078500da840d16000c1000e404210080f000440c50a402d0070300040c2120001003100341005a400e06000701c42c1c40c0e06802900b0ba145070a204840d10451242c19028a07c4030740c84070102d6210f19400040003070b0b004071103000711109599002c0c0180020841d5900c41506904080d42c8584100049801c80c1c0c060b9004051b00c030700c189d0303011843c0e00603600e40c00e06001440e141000491501c11114070184c2c0d05103d0b00000d403210b03845003459035050007001c6001020040000b4001d41001941e10109070151003c10001d00500000784500c0355203003a6503440c2c00 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 997681870 1250 997680620 997680641
    0x60f0509060711030f18151603030f0209240c0a0516060503010f050d14010e01060315060b0f0c0c09040f0201030501060f0e040908090607030e13020a17150a09 70
    0x10b0104182d04180f00000c0120703400b1404201e0305909010348052012400078010100c95407040305160540022040c80d000762941c41c240c2c00541c03481f48158100170b010342e1007820344503042e58410414030b0006d0341c9000c140005008003451160f40d9040d04040d41019105503000d515141c800c0181600401c00c1c00943c0200c400680c070a4100003554480095440340401e010b0750400302051182480790342000b421360340341c060040070031181221700140e80b40d003155204040401c00d65141e60b02401800107070f4440d501081c0407410100801803600080e0001c0780142042080800d6000070182011002000043c10001000305020014200b030715000d0307441050158201d010a00700400000d00303500a541506130854180c0b070320110140444104001000c2e0081c3c1140c5014041c040c0300c18a4540e80d01400606102c0d48800700d0400e100800c03c502052003040700c0b0413050040042c1e4400035441804030b829880480740a0368240c032906445002c1280e82c0f00410382240702100c0000f000131003504640c013001d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 997683120 1250 997681870 997681877
    0x180b0d06050f040e06070c08070f14160f050f040204030203150f09010614011101140a090203010e010e030403080f07021e042003011214070605070209090109031704060f05090607 78
    0x2c41004184401c0e2105504090901d40211000848040c01500d540400d51701c55002e0a00d45411503448528640c3e002d0002c0e661003641c1510000d510801300200010340755420444150680b91455000310412140280781c002d0702018043e0b14985c41d19010348001d5a8024140e03480d421810103584c101e503800b11040508070790035801080c0c10a030184216000c1e01d1040c0c105c58a100700710340056882005410f6012419035880c0321742c5072001324015405018042c020004141c40e01e480c0101401e444160f04040703626403601c401441c141400104540c201d980c0300d44010303120000803001c3c1c0c07272034098400e001c0e401515414072583e0900b00c41ca111181c20000721010040081c42d840c0825002161000400c060442000103100075a503007000513942c1d0b40b0508182468024031840241040394580c400c00103d880481c0c02d00441c41c0c42614182e00a0303a880c000c10895002d910f0041005024401d80d41169400c8808641407001030307040820543c01e0140b00303101c40d00b8031401e01507541600302c6012001 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 997684370 1250 997683120 997683139
    0x50f0112020303070303050c0d090507051809060105091b0408060118051e0a0e1606020d02160303031107060914120c0a022b05030424050703180b0d0605 67
    0x18588140000203030301d401a00840c1401416603083e001032030003410648096100784540300d8200f650340a01e81526104002514201e03182405010503040318001500340c2c0d2042c4420000c00c1400029036a046900c00c4a0350801501d5103155203030001901850911109400180400d01e403900045050403140030003207600b1707896000955081103440940b82044144018980081845070006100d40c1200380b1100c0040d4000340d0194141c40c0541c850f440074124440e01904010340c54044c01240301c80c00283c00501481d00115403011822800303404000c0c1072599840068503c08090800d4818031a8000000c10400501e805c0010b030481e4404800204c602c5020407038440b0030075280c00e84401c60000c40080100542d00c0d400c02c4261006111040703280b80d000c88a4500c05440301030224203444c020005107030398504002030704440c002420000d01c8051170220240c40902d900c00c0448084c1074051030150100984400740c000c00380425805542405404600e013a078040d4103501031411558101c5000d0380b03 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 997685620 1250 997684370 997684379
    0x32407090302060913060f03051b0303030f041202150a05040c06090506070f060e0a0f2d2a0902091201050106081303090b12071d030d032a03050f01 65
    0x60000c201d010007034008005220704016414441c851400003581040d000c100d1a44138a03103210f15101d1948107540950012203180013120820254000001064010310f00d580b403c4071400b680b070031010b08014100c05441c1d0903c403125209002840341030081c8003158101d03050145490024040c1a602640c0152000c6000150140124907280840c0c1c0d014100d075040c1903c640f82c036030541d5038030403050390075985030300100300301c110705000d00ca070030758401c0c4071100c01c04801e820901c1d0702c0b0030120003001d41280906c11515681181031400d486d50ba0744041d414102200d0202140c0441440403035007191407940315000300e0001c0c5140c010f014802000c2d500b00d46003600401105003602c07070a200311008a071001c0301003419641580d0b0050341c0daa00900381484016501d804c1c440450703024001800380440740105015030b15501280041c110030b00f4518410380c44107424006070b21110b402218409044e900c810461101c04004440907040303082e5910461000c0000350082e000e481c00700d4010443e03081240003c82c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 997686870 1250 997685620 997685627
    0xc150b090601051e070c0e06040e061801060b120f1303140d0e010507050c1209090c0a0c120e120a23070503060c0a140c030d0b060706020c0f07091424032407 69
    0x41e90f403450701004242a88270000c504070310240e6914cc8040170354031503a0200f5064544d2000f0403105620300d1000d641d52401d1507906000d042c0c0980301c900201d01c00c4810b180800c1c0d10400b402100c1c2c003818180c961381c85c41c1c031403d03000515400c50200010b5013801c080107030032a0084c0152410101c40c9095a03929140c14050080300c1c46094000c0d40d201c0c4171b440c0450a265540300c054080000c450910040c114115220441200008500750f000901c280260100c20309025400303101720207404004180f0b8150942e681c0000034007140f0000001b032661040fa0710000d508121203802880080c3c02d8031041d0274441911842c40d40110440340100d07100f151105800301e8542e04503040d000c00c0b0030145060440214841028092840c030700b90f40410b080c00b0a001241c06417005200b840d24060060aa100920150600741141d5a0080c5086803034030a450a4100903044103076401345200c50862000c0d4841c6030391040300f43d008049140c06200d88802c0c024001860f03209a242c2c0410b2260300c00b42d9036500b0b10100c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 997688120 1250 997686870 997686881
    0xb090c03010c020712060204030b10080c0108090a03031a0d06050a0e07080604060c02011517010506220f021e0706240e060111010c0c150b090601051e070c0e0604 71
    0x2c801640070000802440001c40b035116001441008094070b41981d9440d5900c04c82e00640310800700b60103101d420410b4080401401b00d1241003800d002070b0702d1400001e0a0b880d840804005000d00d07483d512412805c810812000b40524002002200c01c4152030400c0c400426080342d210b20218035090440080700c10000d1194215181c800003801c103071f13a540d40c5076405011407068071015592603090800c5a110000324000c05018408460124081e0003000c803801d464003d80007034001d8003440440700341100140010344001001441c00b00b80740c11010042d42c020b200d00000c6540c10f55035a45081d0100d0ba090004000b807a00951051150f00210700a410381c1c4044401c3c41010fa50440c40c00b002803400003500f0b946e02c07500505211112a8039510840e00b51303030021051500066580800104010780c0310403414030150118000c1013103d4009011904808001d86544c2c14014041014000010340072002142d0680207a07205480344120b161503d003c00d85401780254001d81d890006825061500c82c0c0c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 997689370 1250 997688120 997688141
    0x605030601030231060b0a020d030501051c152a0806030c130e06011e080102090f1912060c08070c1101140c01052707080d0513030f0b090c0301 63
    0xc030303e0100359141e40710300a1402c0240c4070340300c0f03030400c0313206540c00007148038000080c4a0780c950107540320076580c0e0090809101640307071014035140c44014000b54654214403d442d111503150f00d01e8202132418203031071490300988402c00b041e041c0707105103142c544944074040e440c84290440c40c1090f414500259080c401c1200c0b01601580700645000003031030500074040c1039000940000914a40c41c05c02641420300981103003803120641109000303084011000c80700140b94010003103007040075020000d0300c01020600307400d204051564154000c00c04e10f19800000300540107060440b000d05203810000f401c0340d00365020221380004d001842d814001c90700c8030f1015920031400c2611120303080065803418540020420184c2d424480184840d200340f041c240030340c48112020700c0400700200e640c03000404001d01100300303400c101010840d61500007812803c100a5080194481c1c1404030b4540b5510303490360015005a5000300084148844042101c0c01090000700b5038a18840342024103080e10b003240034 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 997690620 1250 997689370 997689379
    0x1c020903010b03030c0c0f04060302100f23040308030c04080f0115050d0f12140a030e01060501050a020604030e01140403060c0206010e0c04030b13050a0b090c0406031109060d140c0406050306010302 87
    0x800c1607d240c08405101c403030500800018095481c2c0d00031070311040c4406c80d00c101107964001c000382a1500031841180042401c40ea0411022440000c28454056484020050a000700105030b8140340e50781550050a881e10445801c0402645c095020f0b1100c4060301a40748800400403c650400c50700c011038440e002082c2800c0d40d00b165036080040704505019100f0024407a0003580d200c2c0142001b0b02d8510360740e5402203841e0802c00c10040c01c4500d99804507041c010100001196a0380208001368015010700b48003c02518060050781d0040302c00700c0f20341d54885c0005000c801c20000b50300c18035a01140e6803c8070f0950783c80300501c05890380c013a114400c1d9a881440104005410340388010f91103100440100400d045561311607180c228480400c69202120000f0081e0448042101107015141100c0902c405441c5448245010401c200d0590050074844c0014508c0d8a89811500303100350301c1039542d101e00118095250b160464482e0131442641032050002c1e0b9841c0009503d41a60b400a0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 997691870 1250 997690620 997690633
    0x3030601200c130e0f1b1021050106030b0a05010219050312010e0103030f020d090e06010c140609011505091611010e0a03030b010f0c020f01051c020903010b03030c 72
    0xd120300210000c4101c280402d100b040001070380c548985403010203401c0600b002044000304145428101124009802d03455844240d500c80d000800b100200c805190a503282c0d801c0003c00482240c051070020114102c000c00882414410b1440358000c40c101e03103040e40c041005210a1040003c00029485180d0042e07101d82d04035032405c141c0000603044144200f003240c1c60010355030100078003c0380991000018120010040051580050500b49002e2540c80506694100208050042d103120b0280c2c40005c5030050000d03120b81d02480e0316005541d00302c1064112410b01414071651400201c509001950800d0940807140c40300000e000107841000f480100e440c0d48a1907119490400b6481741410000b64908503000c5810a11502c142100c4240107001d03100075a04006d400d40c1c041080341410001c1054070210300e145d01102000b103140e81144d24500c0441c140300101c072280199411380785003000c0f4030544034256031154010402414290000d02c403617064201050380300c1c09540040882d42e0041d2 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 997693120 1250 997691870 997691897
    0x1219030818060a0f020c1002040306060608010303091a09031b01030b060906120901020919050906090c16062c0c0a3609030f2304030206090612042303030601 69
    0x64115002c040101388005060103842d007045850300003038403946400642c3c00101803091103030718010f90001e01254105003149505d140e07801004c1c2c0b607285c0314681002c06e03a4442c4100e1120350204903070007000024226000c02c424402c01040c085a100000d0380400c0c900002d071030f00c030308200040e01c070000c40080c030060078103416016001c01400e00030079051940d54200500d40c4665242c411424140e01d80d1143c0d6900d04d07042a0a200c490700b400f6000c548111929010031910719101802c40303921141c0d20700ca219a0310704902d80080600b460100701e008101101a101440002040062701017a070242e00303c54082c9038070740901c042082a4043c2111000c11300c034600790b584200d1100350300d0b105040c80c500c42c0d550310324414040441c0d007446412030010f40900100440340d50300c40c00520700c0d1240c000c1d80c4060003801c101072202030301c01c1d484002d004080c0428000542c2c0d45082c2038409201d4840041045440c1c18508082100c0091344c01008104c154845c40c1d1840d800042039034070411040c3c40c1c064004181c03 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 997694370 1250 997693120 997693141
    0x60102010e1203090705090f1b0913020d060b04080318040b010c230307060608101103060d0f0b043912080c070608070f080408090f121903081806 64
    0x401340c050740c0c0724041000469403280001c0c1c0307201e025088081040c0c1d003010301444121001001150301e004c4814404101d555440d0800540e02000300200183e0380c880006208003c1c20300355100403240000454000f0b80c490703001c0f0040c40c0f074040240100c00d50b080314008010850742030809540c00144400c1a4030001030038001000b503450f480030300d280d14801410851301e165600218003100c2003500c0312401c01104800704240307580741c0481c11050103a0151750011041500008040d58030035076600c007080c0d0a01c06400188102584c01c800340e41036600d0310341404c5100200c060142160a400140142d141000701849400c10b43e161615402e0b2080c90098001d582c00445a0f081e18003890030040c064030341408101c448014a00c50b15881c089107030110014080b162008401d50074414681c00f000700140e40c0c4800c94404480840710341c0042e01910001c9440e8111070b160b1031070b042c800e080d07280c1a40b40341c07045e0380c0c041c2a100c0c2da20080c0d10b54400c3d001d251404920000c0b680320768052070100c0c1c0315921 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 997695620 1250 997694370 997694377
    0x308070602030415050c0a09080c03100b190f05010207061d0423100f0b0c100203100e071205160c0b04050c150903060903041a0c12040e0906060102010e12 68
    0x843c254000203c1c8904c0d21801c452080d655508141c5001484010700d03a0021100303001400b4000103880b4081032107010030703101c0070003810090b2055503403d410380e1550340d4540000e40c3c2d00c40840c0110850360311140050800e4119002d00c83c09071041080001c3c0692041c3c60b0a1445803440702000192031a00007400003134130308040d020f20349044045040e14541204030302c144c410070202c01000c3d4001d240040600081d500c41e0000b965181040209102413100040c20340014100c6c0d150060f940d603604480103201c06941e070010156042c0f14070074021542e910121101004401c01d00c204174039240d40c2e00601d28240c03a80303030f5507011503983c0281c003011820030000207078041d018000781c2d034102c2c00301c03800990607500400510314040c0001c0f601e040349040404c0025440500d11004600c0d050600ea41d2040700e030580c03184e0103114000040c211107090000c6c000500c0140720110390946690325040c07070724140541204e444c801c9208180c0001c02e190b00c14001c0300d44c0740004002401c03051400b118029a1a030 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 997696870 1250 997695620 997695623
    0xf120721020306010e03190f170a050c0f03070210031505150d0b0913120507080d06090f050c0a05070204020c070b130602060105030c040f1410080c0a03080706020304 73
    0x12503189002100381005108a1400403a90001a0b483c60480000b4000080c002441c0703000e640003c5100e02c00311003030f06610005581010075451100300f2803411119952004400500e6510b0105e8140078040d0094054100001c0e410b0640d42e00218051003e552401030f040040d511a90751000140324034007a03031003c117030760300c03c25100781c0d0464442000c907100c90110030142c1072640e400201d1090b2440c0511440f001088111600201410501036911588800160160180381003440181005014200321502e159009683d2900c41c80f0541d02d11006181c00e109201c212801c0c00e0040d210700906110301845a10181c5503e424144545403c5030b05810001007260000d608002c805541c02040000350000c108003250300384e40d00009034844081070810703440003040d54048001440543d8000c00c9a011013441a60001105146001450042c100c0c4e1a90500c4000c007240c20301c02c20780462502d55080c1c070341307410840760840c020805002100b41c03a8403010340604421700c40340700012440c0d00116080f0b07 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 997698120 1250 997696870 997696877
    0x2060717190c110106350706050918011d0901020a02100b0a0918062d0c0c1e0219050a140315010f030b160804030309060e300f1207 58
    0x3d808450440707085407416040000c481c4403801e001e140c820603110021225000940103e540d20b40e050101d69a204424041d050901c0740225040300300c0d450305994044241c034403504040b003d507564500c8984c61402e0440d0701101050400009001ca40c05000300c41402c60320b6030040ca01c0c0c04010784000c0041400070075030380e40040a5080007581c40c0c640d0195020600c100c0f43e1202c1c40302e01c10f00d400c108513600c50391180c2d075102c4908108109a000a43c0c2c1030107e200241c40402d01802e100c0048801031a0310100800c1415880c25002580113055410110726200360f901244008018125840345070039071141c15803201c5014800d03c4124081201c00014540180072600000030303074800010001000d07000410840140c01040090021034214650032a01302c1075040c0c64030300021070040100600500c0581890303100c01840c070401c056a400824182121420740e444100041c01d03010110415929004840c50900051004038482c0e4080700c0000588800642ca00402030b941110039007070040c400c9003071 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 997699370 1250 997698120 997698137
    0x3120b01020705060c1e15010612060302090a0b040c031b0c05030f03090a05150417030405070f14120c01020d1409030102041511062403030c0d02060717190c 69
    0x220340718031014081001984000d0700c998500c815090119120710750100b401d40c0c0c400d0110002c10107c08850034151051490850b5101040c0800c100c0941445d51000350003450900801c00c55031803641c0058000242198107021122a0080c110142e4041a5204883c01200106404640d0107500c500714000d00c40c20581c4d09044841c2c02c0100c1941044540c132005812a850240801070148005180c407200c035060400310b802d01c0c0e01c0ea0b00103000d04c0c0468448482c0004040340505c41c0801c800402003182d40411980140c0390000d01c080c04e00c0d842001c03401021021004c40c82000c010500030303400503042c0d00a00c484c85141d44125145150b400c0e8482084d1410850800350341c03420300080c00a41030b40848122500c100550091a01e501d09940c024141c010720144140440010407000442d81e00c0c2e00390f0801c1d03001303017000641184a40356480403a441407004814034540c002c900035204042070b4840c500c8100c800036152103000e10884841300410140f040308851104650b109082019003031520000 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 997700620 1250 997699370 997699379
    0x40605070918020d0e250e04050d120b040608010b0a051e0f0d12021c020d02070b1309021611121c030908031e070e031b040b0a0f06031803120b010207 66
    0x181207150640884c9001b080e0101140341d405040000014800c4180d504000c0ca0181c07104ca4481c201c905d00a004c000d01c201800300f1642c0d681c2c001c50038039100103204100c0341d6174440050340248141e0b510213018480c0c148000440d480e00302c021080140c071016004c0c81c1d13000040200039040803401c441c154042d550f0310001011078418412482102c440350004e0440c00b801400d0100015100d010810855200384c41c01048240e020480ca401c8500005400c4c3d00d5070700c401c9050000c001c154002d02c041910110394800304c010303001c0d02030105a02540d00340300c0944200301030101400b40c00c2c560500c164081d05403c041183c0c0d4203c1018060154503000401e211156144889544203540c1d02e1034a0030180e41d0303600241e6026842c1038200b600c50902440242d09000030a4444131983e004c1141d03c1807004110b40300340c440b030f004040203550040a100300b0795208c400b162010700d250b002d00b8000900e00489056103103042808500881d03010b860301f210000103200d0100141210900960450007510800034 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 997701870 1250 997700620 997700623
    0xf040c0302210403120c0e090c2101050a09090c06050309030d06150e0a14040f1b051c0b0a0e060307030503130824040b0c21040605070918020d0e 64
    0x1400c500d00240a101c1600386800c004020b40e030200c8519643c14a062420000c4582144030310300d001009881d08802c0ba90b818270031303940e540550070040c040c0d40140c0002c079202e611038008003810f8030022904914504c3c2c4075268a000c0303c1c0351b210000c001680801003071080754040c4003e15489070000c0b007183d1400204442d00d03800d460b07040d842101500d0701d20381419482e03900900f55422002c005e56603001018500109029404000380000b401140e0300d87d002096415950051003664000d007401444070f0300342803401485580201d00035007400301c1034a456800b00a04d409002e2011400520050409007020842c6013038090292800b945807140300d00c000001501030014045110422484600c414500a5000d00b00703403282c260440ca502116082154100710729081c0340c0c1081e041000803480341d0310b1040c20466445080d0075241d10682101d51461411849018588154442d400c107100e262601a010358100c2d00c0d50086800215103249030544e0b150a60b0701a101c45a404000420b65485449419 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 997703120 1250 997701870 997701907
    0x6060d05010f3603021b0109170703020a060201050f01090b041509060f0b032203090308070b19051006080603070302040f02030108060c0c1b01050c0115061b020f040c0302 75
    0x44640d465048250410f0300c400b0242c500805021483c40c101c2c21550750007910b8813024400d072980500c4541c40c02c04642d1103103040c2c4014184123040c0310322943da0345418590f21205c6201c200d10422449c0c501061080c81802143d0240d03903803001c45110750742800e9008020b88268001302e41c011303030b541036001c03900c3c40d40c0d41c1c00b003005000c4200c00180d131380c0c2854003180c1d4007507032a0031070382100e1810400c0c007200084901032400101401075402c0d4a60010340341c1124100310740e90020f404074101042402c180900800618020359441c40f10041e410644d200e07440540318100c40d000700305054420f0802110b4010564a60320110060aa5101d203450364009812200c1c0d03500743c0d100c120f9000c0010300c0041e20411a00b904804007a60301420002c400710a00e0751039050450b0300c9003144c40724100314030690054050b24a148088802405a11581c01d81c0da05903000030b1090030006000c0d1101c2a9080401220000d00c0c2d076005040201611417407001d100c041c0010100c031200f0142c0c200012000504400180b = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 997704370 1250 997703120 997703141
    0x516170f0604260a1d0a06350901020c060112030806120c120115050402091f120e1b0105030115030510050307060c05070e060f130b06030a151706060d05010f 69
    0x191175076945040250b4039580c0311105140d0094520802c1805800d40200c9603040c00002c01e1940580d002c02c601c00340c840006000c20180030750560000b4000144019006401c00c0d028420031191543e03641c0c15252511a80d00780c025000c510f4241c01b2808a0609148410410120314101c0790541d032000c001c200c040e03410340c0901d030103070755502d8400042250240d503c0c00140001c603825414401d07410300180203119104002c011600ca8200051045030040b5444907030b4540740300c8104141c1b5846440b140d220310300440c4039401c00a0700c9216183c00c3d03000310300341c9050f268145103440203100c4159064004201c080c00f10744460842d008000b0321540c08003d00740103070a081e600c070403270090070f454004d103003000704d400203042408490200b08668854034459291910700300c4030817002024210683c80102440104250072500c000b080002c02c0300141c2001031904203014110103055034945803410928801d42c1d81148581018010400514181c02c10b042084c1c018400060b4640c04054280b04031080d0198 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 997705620 1250 997704370 997704377
    0x90503070b0909160219030e0405070309112407020d0c060201024b120a02091e240d02030906010e010503010e07030201030f090516170f0604260a 64
    0xc2c203084a003007880105420550390107007000c69050354440a034848002503034040710440d15101150070705104da0b240303448900020b0802c028908118800801400451f981600c110409011540907414448041c40c0481c410748006001a10500d52414a81d44400b8007030782c0c06204403451002082d07180c0d400c0d40c01418103400040c4d030748100c5400c40c0c22070400100d00054050941c04496207e00c201060b0b011b00c1050f44051555460706034600314403074018506101d805040e044204505104180e004203e004811240310004107001c810807002d00c4104584160401061003003188540802c241d0104050046d60210703040c4000510351001700c5e003044600e0b80d108e500507401044211031400b800c038094441030b402846044568500c1c2da9840ea41d5200080c10180d0b0350791401840c2c00709600514070349520a054491240e9042507440c0c0b040024042e40098140f82c002408001c2c0000444900c0c0440c0f000180c80ba5954580307074100c1481000701030340ea245140184c090610802c0100038190083c4549 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 997706870 1250 997705620 997705627
    0x71d060103050709140409150c030c02010b03010221100e040812060a030b04030f0912062408060103060905150103120207080f070e0a09051203071e140a090503070b 72
    0x280010162400a00220140043c00c0020300614902400f1003090100c29100442c01c1d941924185002c204d0102d05d014803940750590500c604d55041e00003004504003540280244050481014201c0c0b2400003d10045483d0800c60b0050722808511158066580e4108010050781c0300c01c01900388108450440701030750002400e40110100074100c03a00a502030340c95512003400d560f5100e5801001410140901c46c840304015800c07481607060030040c1c0010840c0800e000554903068001d017100f208907240c10000401c4092046020085c840d044070511002022280d02c0c45c0c8800000300510305c001c0d10580600200e030411785965840c0d0358000c621601041d8140040d504000b402c10030745410510450f0420401418103070000211001600c0c90040703101c903aa00ca0300101c20003811780100c010011300826025003081030300340c0c002d180b09801c0740c1c0320303004916030000b01002d00301d03010440c20f404100e0f10f100300d850f0b01c1c0d07825001c0c3c10070790329909100102c10348070350000e40340c1880c560150b01030706c0000 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 997708120 1250 997706870 997706881
    0xd0e13090c1d0a0911060c0106033807020c09150d0b0910050c0a1115070f1b0201080103121211090f030303060a060f140307020d03060e060d0212071d 66
    0x142e015521511000e400c2180450b19079501201d15505007a417403051201081070040748100394088802940c2c000124140c110340e0440c021100c0c1020000009560884019100d1507081a410640714450540c080d0007404222010060f00600141803030300b4000c0e491101c0c040a031035550543d60118002c424240c3c4614201c00582d1911542d035810200450424041c4080a4200020380c0c42c0000341341043e9500b401881541c5191508100c5001c820184c40b4050100242d000302608640c0c2c2d04641c1e0b00d81000c2d0003100b180703082000382c140080c0000d1030080100b01050b44101081300d40c416074607040b41108400c0d2104000d40d005440c0c403d01c44040003815048a00d8090031510401c201a4055402d514050001810300202446660705100104150030581442130080011502000d121240c4905041e40000c0d40c4000d548404000700c2d2404034041a4098901c010354881c08000703190003040803aa5082c401241c0d802a80746941d0700c03030f00e03201040c1d0300c1e81d0320580210880f201104031401d1070314 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 997709370 1250 997708120 997708169
    0x4050409141b040501060513030b07050c060a0209090112050a0b1b071b30030c08040608010312050c031611180604050a020408071a1b0604050d020d0e13090c 69
    0x1030b4024411f01c0300400c42c910a1070f040c00e18580880307401c0a0505d4007950f0702c40307098880d807042911141c2140600c40400c513821f03206501400c00b4020640b520240c030303070307d4404d0100400d05424025003540e10070260171001801010000780d0204030342202c5801d00103074001c00780f51034104030400c0715031a050f106590322414416140300014020415824030703d0000e100400c100c500c0c105107105050030113100c04000e0601444030854803036803142080769101c0c2d031030400030403901007070104858030030790150201809480f0b0401e8038400c1c2c1c05000a14a400c1c1150546000c0b002441000c807540c4944c2001c0919039580d0a8000544071640c0c1e06030b0350706150100c1007004407400181010340551043c0001e020110300010102c0948024003021a00c0c0314440c900d224042c01018585896400301e00f8621000c0036011846500440c440e600b11019103490781d1044c0c0c0c403003c6032240c0000040c2d6082d24055285031196240c0c0242c50384020000f44100c1c103843d800035151658124042c8118064000e00a1854 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 997710620 1250 997709370 997709381
    0x9130e19030f020610050d0609020402070b0c0a121103070c031107080d0212040b03010537050f1807050a11060c070318060203040911090a14010f0c0804050409141b04 73
    0x2c017039102411190800b00061594891014080d140903942e41070501151619030455555923001099a090b5140484c130941d5580d10010030400041e0902d0a008401c90702e6025031010703500f4100e1004e0643e074505500f150340000070704050341081030000b1911550402404003101070040d510161112284e524070280c0b4111244003000c04a290410042144030503410540717054030011610810a9501c1070049803290801c1704040b80c410b11036505500c0005500d4101c1c00460f80183c0b00c0940ca02940010064061040c0301076610a120f024001a003041c8520000d26840c5a6405c04036040380742c116150380b41c900110340f1b4801c1c50200054100605402c0002181e1200c0c04051031141c003414540300a449001d84c0c81060390f9a0307280c0ca00c0c00058485401520014070010f401d0810880da00c1041d0040301c1d0350241218003094008d203040c9980b500c50804024a00e810a8880e440d091401040c08020541010141d5546002280014107840c050210a210440b60f20180f480a09042c081000310b90 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 997711870 1250 997710620 997710631
    0x807060f0c03020c12091809100c030b1305040f020f010521090c0a1805060402090d0309050a0b0c030405060310050d1a10061e3e0309130e19030f0206 66
    0x1100341b00703100c103a9403800c0f62000c929650610a52240d110785e51003610780b03071150320455031050800060900c0c055260707000010907030040301d840055281013900107088800645002e03142180b0f0084120150802c0c804100b42c0050615185c2e00e00382e103084488403685030344040c1040d00c000750014481c441070104150a0f4807a02282e410a5003031610071001e59000d10114680e011a4503040003884596841d810b441074010090001d00d0200923900c0c0041881006008041c8a01034070900410032802203000d4404100c5c0381c10045107050300b01000c1240c60780004105000740e840381c0304080341039164020204040c61291044c1034030140c40c5041e000452000400d060b1f14a42c2c0754400300074040e032101200700c0f100382c201600d078294940800d0031140c3c00403000012034169071b152403118039016450075002d942c10350414000b4a0710140c141d00b5071240f00e10031240d640418000ae07011004600c079170186126401d00001c9500d042c62200e5900e030101a407002c1a004981c0121625140c1901402041c0d13216 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 997713120 1250 997711870 997711903
    0x41d0106050a0f0804050a02150a0206010b18130b04090b041403091804050f0609030703020c0307030c1703040810050a1b1211041e060f0c0c030807060f0c03020c 71
    0x3600c00c400043c408006a40808200b10355540441e0921105000c1c0006c0315801400c03412180c00c0c4403c20702c10503444154220018800c60b03000045445d441360030358402d218210401c140002032141041808240348030004001581c0784da415a0036901c82c851218480e205001e000c10601e1700c0c1c2000b000c069200140e085a80c0c02c100440c0565640e40f2a01c8030803810b020040425949880c2003440c688101d556000c00c15200ea54188400400000b010304a2240300381e08aa84419541083c181c58421a00c030090400906e05c02c24007045c8a401c01da84803285c46542140e0500e0340c0e40c4c1e80300b807420181c149483e00d959665000d00019910318002c1d40803841d00c5040c40380081c5d000e9003000304035200c4113201c241c1d030581d034961407038090440d88201d500070941c500000804443c10f034841c8409c0c00881c130608012a00c00c00e04030341c1e42d500415100c6d010540120714801501c1c42c41d00c6090469014800413950f0507641d40001c14240068418034100342010f50b07005844080e5119040e240c0306001d881072601 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 997714370 1250 997713120 997713127
    0x3060f090509060c07050a06093f03090203030c060a05011d060f10030209190806100b07030e0103020c0303040c0503010501050409051209030a050a2006090d14070b041d010605 77
    0x420000203855034010030025860707681d80220382061401c1004400300204628205403640041c04000c2031460001092b071014061200c40c0c03405031001007191081000910311a052107a08042d000c3d51080320440c0c0050b09481c81d00300c800c04024200b410807901c200c131469984005000c5106004c03550680c900040c03034224440d04004002900c003c01c2100000d00c2011000b1003280440d101c0d8040c0d428940c8040d01003009442c175283e03038200000a80c000d0300202c0c41041d000600d00e90b079100d5a9401c0b2100c0c10703001407501055460864180d5404500c05042c10340030030040928900400080d44554003d90000c0c2c141d90900c401c041c2502c0701a40801d01c070354200000040800c00c046040c1c0c172a00c1809010707642c0c4656060111b420a0019240680381c1c0c010780180d4410b020401b10341000604002954030b02c801408410840c0d00d00a80f0380240d04490071000010000e0030070722051044561400448100c2a9541d80000e1640c0c4030307800c6600340d400349043d1468441060039642d409460282011420b = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 997715620 1250 997714370 997714381
    0x603150a1b09050906040f1d06162f1e0f10050108070e06040b2101180b0105041d062a03010308070b070e0d110f01090e0c1803010c03060f0905 63
    0x204c000e001e05403501c9a0345c3c40c1084000c414455208640100500c182841c0c41c0c024000b0841d29144121a0b00e120303106141d884804051142000307440104140f6116501c5003424440c44544807205120003000f8421080ca20030b4000102400042e0712420350000d140c01c2d440c1e803009604144804d0812074007039040000500c01104085010b1094801c0c4c0b465040942e911000014080c0c0303400e104698009000c0c1080c2d40c2a14030fa4400c81110750307070a0000f400b680201c0407d003002d88039008c20103072544c0003800051040e403800d50072001405200d4880b408a1184000c00d0f107040c10001c1e00c107800c1e4143c000c00701400c05c4041440c1000309510140c0c805095601d0b5445800c2c42e0311842100400c40f0300c5030000102c60347e0081269a0003141d0161544074800043c0c80c00d952840003603c401c078440d090400006086c4d61103112042c0a13201b0103082076545444403000758040381c101030a8901080d0800113580d66036142481088860280e0f40e4011400b030703181103003980a200403900249081c41c2041d08010 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 997716870 1250 997715620 997715629
    0xf0105070807030c03020f0a0305040c08061302040e0a050d09060315050a171c180509091b0f060f04030b010b25060902040f090b0601021b090603150a1b0905 69
    0x3070703000030b8906000c210804408011402407060801c11140c8040201e50141c55651517071145204d58800d6500f0000785454080d2503a48050480c1c03502202e556007440760005003410341103000000031450407200c3c0354400c0d50b501414074a140b4a00b000080b011901040019454022032540b0101e007010955807030b0420004c0303418150240500b02005039024546032a1090401c05446840e4015250382c0840510740401400c10500b07000091144100031780204440c6406400385010703640500081048040221594145885100c070383c1d540100c00c009100401c1d01c44200405003c00200b15983d03540307085180c241c044440680201f0340c00c85c81071002e0392121105c61451003608414044041b41d444007807400c0f030041d01c54010006c0d00141041810036044840346c100c541c01921520440c00c15545030001240d0340e803c0c0d500300b80903155101007443c5080c204840d030b060304018007070b043c0c4d0b10901d20300c1c001d0540038a007503418000039a84d4544035001d05614034102c0b004030605280c5210070502c2d140000c0c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 997718120 1250 997716870 997716887
    0x4140c0d0c0b09011107120309170c190504060605031e07051c1107050102070201032f300f060d020d1b0305160602120301080712060b210f010507 64
    0x1042c98000604460540c0c094802840c445c00c2440440e040561185448031910000900450224191207404a44a100c840e01614140d030031400610348400003c1c02c1184411202414140e0484819800704d0f00380c64a002e2103000c0c065640310140c3d6410407030840d1004403a1440d800402d00c100380300f40160207038032008441d081c2401010070380c1c0f5091103040c03210040c030120418502901c00020240c0402c1010f401900249001743c0301003002c3c0e03d0190000c94202060f03175500c40442d4903c00801c11030318105010700700f032481d804400d41c04005203c25407400c00d000191841c0f61401c00b502004050400c44a409034090019a40d403140700c6066400b241120442c1c1d0001042c5901807844a02c2048181c20200001c5402c60304680011505003003080941009005030320042c060001c8143c0e03005c9400044a04941c0314400400305940740510400f010040500c04540b8036440d10240d0034165190035203010421002000141420301190302c0354504016001c0440c5282d04160401001d2500900d65 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 997719370 1250 997718120 997718129
    0x1903110901080706051b0a0309031b1419050904060912110d030216051e07060e0d060c090f092c07090e120d0f060f03080403081b0604140c0d0c 63
    0xa403a96602c83e820146c0702c2c4c090b2100402442046032030b9051651100902d01102d0240c200903580301208260380380e0748246402165a204000f504e00d4802e81032880260040c1c07400d00b8000142651074a0004038140b506a8090f19015168100081444007070030000600b02c1a50421945661a000303025440b140000818818154049a0298000d800e522201070150780a4241c9050402d1610b0b682044014500589094824500c001c91528001d04e540900c0740d800414510520245a490030b020f032030340c3d08044042058000340001d151700502807a001030201e20a0202c1c401c481c0c5d1890f1005000c144d40741c100b400001820062240ca000318100003502c030751040100301039502e8a45245449603080b00100c04144c0040c0420018000d544401c1c0628401c400504c107207643c501c20083c48034500d000180405004000400c00160402c004041c07a02c140602c01c41c0301c14090509078141401201d01f585c5883e6110900400e034102880b158181407811a03081440b40d200380c0740c0e000300079594001d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 997720620 1250 997719370 997719377
    0x3030c0703080f04050306071101060f0e010b0c031b0a03021507120506040b1305040b0f01031208101208220807061b0c0815090714010804030306051903110901080706 73
    0x1c0f000b15503041c1e00119009094090704a4a00c2d0602400007043c0b40040b025440165190101c041550184041d000044650110700c040c0c440e403d0a5140c4050b0744254050f1120748401c1100740c21420142d1003400b2210502800381140c1425803d01a09146207032454442101000c0c0810031410f4014401c01c40111880c400003c8a64401d40454002c16042d0943d035488841041040000e000e0740d081644110312900c0140750740d842d0302c0d40c0e008420300b0138040103016070300c08220503900600c280d40d0036034050340740880c4003d603641d64828a05c040060140989102c000000c805001c102e8281c2c054001c07098a01c082007403503182121045e03e801090040c0c1040041e040c100c00b0302c4400c03042101213001c0d00704148034040d590742c01c0080d40e940c00c0c20348840450541e250028145030b02c0484d191b000c40b407a1041c41308458145500441d00078000510403801c2c56981c00004c1a1a141e4003500101c0c142ca8840c1d200d40181141001d10a00f030b000300c40c032071280d2a5000140941e090102e03400048a1413401c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 997721870 1250 997720620 997720627
    0x3190f081609030519210525020a030c080d0906050904110d060e0601021b010c060e0a05010e031b010b03030a0c1406070c1208070905010f030207140c0f03030c070308 73
    0x810448040d2030b250310140851085c1164000c0814640d46105000c520885203420a140c11a000003030701903070100b820010620034003041c540c2001d10071400e813810702c181c01d841445904660001e036500103d504161510140008148a4900c080041c440848500d0800412082c03424400829034820710b001d6502031501e4903001204080c070300041d51038500000d8010b01c00581c5403d019442508111442c1f4014807801884c9400307800c000304804111801a03650a00088460700d651010f4003c00a181c03030745101e0001034001096013031050740c050001800c05103aa50403070303108801883d8025090710003503034908134010000ea90b001003201c0c050306040c1400f840c1c8909a00740101c44500859119080b030050408110f9034981c4030440303c940d0340c8105980400c11174503420803100e04408481440200c1c41c0030314144025801003040d080000054603015150400c030f503403800c1c44a04100719014059000020541c0d080c0390a581c03064001c00c0a5004508250b90b0441c1156200440c0c40042d00e180e4002 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 997723120 1250 997721870 997721911
    0x1091d0711012a020d170103020f0604090e0703060b0307050109140d0807030509040c0c1112100c20060c1827040b100b0702010e040b04090503190f08 66
    0x3034000040001010b550310f12900e501c0c901e141c0d101403e0a0815006000f190101724403580039401341201c01c0e41d83e07040000242e08550900101c0c8212001c031544c00b071014880020061100c0c040c660022508030090725949245181500c1a100034010f80c40c4030350406101448103992145124007203810400d5210a02d00f11840401c1c4100b00c207001c0908005800030f14401403681000082141c07030429113040000d6284c2440843d800000d0440042c481c03010b0b42e05010240c900084003e0607040b20380b0070383e40940300e020300d0070040382ca8041028021a010a484403c0c07000c2c0c0583c42504481c206000d025289460000d00d40540b003500703080342884c246050800180d8642c12140b440800c50300c11f060b20540000c07402d900980b44201e4049603589008400101c000800320310b0b000881e00980d1001b42802c040d50700640717840e0810035003ea0410380c0c800c1100351070380d6a400b07440c010074001c0d4042c50342c07000c50080e0b40002640c425600024011244440c0c000c1e2070740409050b51000201e250010000c000c07 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 997724370 1250 997723120 997723123
    0x131205100501051c141905060f060d0204090203121602040506100c030c1b170f0a3c0b0103050607080105100e041d0d030b030601080a170d0c02060601091d0711 70
    0x42085856a51107942d1b115076034180c0041548800c98001e104441c0d0551364610040305480d4102c0d00b03c2d4000218a01450040c1015041b52110610040030307036040c000d00c00c0380c440e5550000b45080c10302412070700141081d4146481101c1c0c001e20181d500c09480c05845002070401005440c0040c200007018500000380420352604003400c504054501d140036039546180000c484041032180524040c0c0b40b890103441d000007424100c6039034050407040340241002000070003000e400300c004d44900b020710030000700c40040b1600755094510031841000399504508000346800c00090045040c0051136005200c0d035902d000154003200743c0341c40c210510215000200d001741c0140c20201021003148549489464004504000c4030001582d0800102004500f05942c40a0a105e050300d650010041170001c20901003000da41d40e2403600026240030b940c0482d5804503840f0b1451400180c2250091040c5e0b5a4800a03010003071080036400c1810400c2c003070510059a2010b004601030142142002d80580300 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 997725620 1250 997724370 997724393
    0x31b04080610050a1202100509030c041b080105011715010507021201050723040909050312070c020103050f01060f0c0311010921091a0a0203131205100501051c 70
    0x660003540d4490400c00d020311240082405118455030000c000810001e02d0000641151a0003c1101d011540020360a58907503000c210500cae014029002980186d807900c0c05800584101407c41014400d00208010102001031300654100003c05501c10249070040039129003184801032030f07100c114240f1006031410f100c2c1c6040250040d01c00800c80106081c10360110b84600c0c166101d52820b41100c50010660f031030600c4c2901003d00052205100100031588110055407080046915200d07803640d844191600441d001400101c14004140441d640f501942e5080010920b135080c165040c060040e01003103000402008111429000206045c410a00600c88024050003006803085505000b0084035420705064140e81007070003500484c5205003801c900300d8801400e07024010480003200e1200341e000c24102e0013144018400c003500181ca0180050080c4038204000b803016600d0700d4a40d080c4035800003201000f82c07400300100002e4607941000d00c0e0045001c240504a103010340b816030401003 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 997726870 1250 997725620 997725629
    0x70201120e011811090105060f0403140f03120907081b0409150606050903010e03120c07051f27050705040b040f0204030f051b03070e0c120403121808031b04 69
    0x9000038200c034280940040c00310b03d08107045d80e1a4109a072184180140d504c07d4016502c0e8440080008001055030012076a8001c82e441040c0c0e040720b0384280840d880c0d070700160703001c0290700c0c01c090902103100700800c20038004042c02005451601c0203010f03514850048820b0040c0946d0700c1c0c200320010018008034101141c4d4a6800410046441d0312000740560001080c44d8060b62821100807a003500c000305a84014819441021041e0b07104070345c0003a030747c001c0c5101310740900c50640501c114003904200d04003082d50f29000007501811050140c0141c1030920503403a030025030f0040d0000800e802141701000c3d0789041c0e0f00401d2440c00380c00481c0c01804070402581007144041404420090b843c01d01815840c040c0c41222180c0d5800490984400301000c10b07030f58554130808081101c038062041207030340010f114010900f0301094404403035101d1402c480c124000b0b4011800131511000b64494048500c501018140c280d158a91f541501ca11010b401c5828030103940c0c03d60514400008200d0b000342 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 997728120 1250 997726870 997726901
    0xc03030f0a02100c0f0e010306030c060f020307050d170c0310090209010903061a1809030d0504020604120b0a1b02060103020f0607050d0507110103050c1801090b0c1c05070201120e01 80
    0x1610340d12401031245c040d144030080042d42103a0360510f258480d01464090780c3d00070a940c1e00c001e00d8128103580c80c030452000b04042d80010702008002c41d805020860094825482e0446103100784000c0c0503890100401308144a4004d00520800350140c420351b105a400c60f04006030750352002401070320741200c0c0d644002c1c212807d00284050401401d180741034200c2080e07407400381c1e4603540c40f00802d40300002ca41011503944140601680303084c86400c1030350850300240c0321600d007689442d01c400343c40d40071203816604030b1800b02c14401140e000b8880c0c04108929004100f60703114410f031000792901418031019100d0703510300e202010150340b150100c60714158490100c5010784840708024141d0342240c07038150340740c41c801e900340e0482e035000780207462051f1011296246006110740ba004c1c00302c54009502030400081510100d031355130401e4001c1a80c12040801003a040c941030703031f40082d14000551580c0c10800305100c0080180d800040000c4502d44858000c600f01c00245074039801401c0350403900461 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 997729370 1250 997728120 997728131
    0x816050f0d110607050702100c0309050a0801020a120b030717012a020106050f13051e090a020a090c09260a0c1401020c130e122a0c03030f0a0210 64
    0x9060b007040ca90b54050280406a64650340e51003400d44007409038040180d08204d20000100c0024410a4a1800584a421303c6000307244c0350408500d07800e00b180c21030302141c0e50015254903456040750310405400b145100a0010018031008a40c0320703a4a807044e072100e1849030707004c1c801d40c1078207401006840005144655420008840011428001001140165217007c83c00300f12030600c0a074101344180084c2910182900c4405860000d0400500041d1058811460000102450016680030340a0f030380051450350354038010442d0341021035000007045440c010824210702d40240205040307803085041112164558821900d0510525031006468001c60314054200044013460009a0b10f400d00d48000c0e489008006a907140741041c10141d004001150f0203460f0b00254002d03442c0e000ca040140c0c1c0d0b54401540010101c2c1d002203140c100307a070b115407110741c4a1001600e0031106011440f001405074a6406c40820b440388907115805075402e4000030b615880c54003c01404003003038000f010411030f = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 997730620 1250 997729370 997729393
    0x60706110a090608090a0b0f0403120c050a0909151215150306060b0c0714180a02040305190f02090604060b19030c0c050c04020c21130603090816050f 66
    0x2d503020398016030f40800c2c60440400c405000024101181c540d0000c01484651901004030008010041088040008480010040c03007500d002e820000451500c51944510b40d800c0040c0282c0c9617070f040000090300c0d00c803035044c5c0182e59030702040803188284d0717504c20701c03505d5800c00b03400e0340902c012100f400030b05040c04181140000c010880c1102d006d4841048281e441d020030500e18403071071801d41883d42c040c0c0e4041c410200f500002c0d14140d2402051040c440b004100d0070308180f082203034040e04869000c40c0400c1031002c18006803080c00440d004911021001d170340c80b64078010034880c01a004045000000701c80b6115a0700c540043c214000100707446403c2d07010070401c5561132040260009003003030508850700340607040c08140386034880040c0c03002c0e440040030300000b50401300c6c4402c014840d103680154a40f100d12484611000ca03582e07030503a100c04000d80405c06880580c01041003504d40207100010030f061200384c8036009041d08140000405500300076140150302c0030160043d0051071040c12 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 997731870 1250 997730620 997730627
    0x1506030b092506021b03030421060f02030c03010e041e061a15090105071109091006050a051c0606170d0914060a0807020106030609080a0206060f030705060706110a 72
    0xe00100030840582c8400000c0c0542909819910480340564400c0441c100780810154204c1035000000e01280d051550b0780104640d044506024840d0365444199841e080c003490380a12003044003584401e41c03035410841010381440c4414898804007010100101c2c08201c8d1600b03004000100180c92100442c4060804100918092998048101c84034410240906010004011082e00f224003282031040380d1006480941c03107448112507101102e42445d100d13075218001203010f494018010503080680c24000b50407100d06401c41ca2007400e12600030400c640c0c070941cbe01003d2050035101da850000e02403410402a10054210764103c0b800ca203507003034040000107007410082032155500400e440e901c1144940a200c210a0107400040411031400800d00426100381c10481c94030001480301c1da60f407100c3c000c482007031340b0480e8500000582901000d0741000641d40050003110900a10030450303001070b039100b00904c200e074052a00810642e0074080c41da0b02020611502c11011682c070605080000e = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 997733120 1250 997731870 997731883
    0x90a0f080306090609010509060418060507090810110304021c0203011e060909080906070f050a03020d1d180a1401150f0206090303130f0f0c090b0d050a1506030b09 72
    0x1c3c0100b00c50000161a8601040c40714101e50018040340182c1c1ca50b40203000103880c80d041c00134009840c00d10380c40c0005105204551090083d540c450401c2414002118100380d035030031501c002c00303040003d00c0c100c22800030111b80d01301d1360407550707540005000f99039a08054412a000396055181c0f100004101400d034022401142e2200410001b26459501d0b0707100f2225000c4000d4181442442480d409050040c001c1030401c2c080c2c4865088807450755502442c141400208800607045180c00390002504000c0785000d55420b1000c6001c2001d2410208400419125000c854106150041008001c0703d0784500915000c400100d401582c48003403030040c080c41c01c40d9140000d00c0c5403c000711101d20100c1c290307000f092241c015503e1600c40c214480702c808c4412400b0742e0b04a01900041000070300042c5607003401480703095a040311703d14051a55040f220343c48046070040d4270054000c2e00240021400c40b807401c8d07000c0341e041018401c110101c0014001504020507086030381d4140907c011001505 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 997734370 1250 997733120 997733131
    0x6011412010f052a1803120a2c01080610110708010911150d0207080d0f05090f240c0c1501180b090703051513090209010b041409090a0f0803 62
    0x3c5056a074042500c2024043d02030582e1030081000b80309a0f190380c0c054840d42817001000400711840c44070808910806a80040400404103100940d50050300342502280880b00490300b500d460762000b00000030f45900c0c0000c180c10f214002c0c503074407050b00c44d0240040c0303900d0540d55412213291302e481e00b101e01c0c000c10324441c080e10b0503842c0b0280010f09113407001440381040c0314400d00b03504080145203090041d4000150031107200c07205200d400318200c4144120b680310049070fa008902c90401c1d040c51f905142d08407011090507080390a0040d01c000343c90520003940740c0c090b107150302c6640e1121000d9045000380400c0c00154054601c4407511943e800509905039006103c7d1400800103125883c0d0880c2c400c02004da40220506002800d800e001e07500c0079501c00b48051205011b0215032000480301c0740030440c01003900780c1d00c1c41e40c4025800d107503000300e000d00f0004c8441840c05003440201e061030003c400500c1d200340216000503502d51001e120390001c03650320844820303400e505450000025041101c0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 997735620 1250 997734370 997734391
    0x30204050a0c02030702060c010204082d1b191505031905090a060b040b040504051023010e060a080105070504050103110a120203070e030f010e060f070206011412010f05 74
    0x10620079403041c0b065500341e080390b80045190a206900f48482504000d82c0ca0341d09550030700c0002200c140c00c0c04900400e03000001008840e8000004109103102d050156012a601c600c1c0b99045000303c42d2600c0000d40d00c100c85030403900d8040c20101c807856059400203c4100d2010034107000706900700000d180220000c03140101c1d00c104c00c50858080380c0e0200c40120032030340320070071210204003240c1c440c0c01d05107006400415403140140c045006da83c0300f0384040320590711011407884504000d00c1018104148030300201c0042325481c040023016101030084035107101280b000b080d4076984031400c5000801d0040d002780028a404500130302690010710441d4080703400c0010794560410744104444024000ba201c407980c680b03400c11030030002d40006049c0b40900490002e03040d029030301006548403000c0d0581c00801c032a10408105810440082c01c20040445500f00740480183c000c1313181415907004505030102e0300e414030002880001801400d402d80d5180000c41411104aa04a0742c8070741110320 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 997736870 1250 997735620 997735631
    0x6110a0609141c0c2d030c03080901180632090d0504030b0a0b060d0f0e0706081b03090114070c051e070b0d09020402031f050301061511070f0f030204 66
    0x40020f02e5003031010a010005540c0701150780c00600120158030f480c0c60040703c1c401d09140748918480103403e0022003a8007080c0d06002d07c2c0c040550200b2a254420308840081c4495002d071310f01c20041001d8644018413054030782840c244c0b80c4071914a00c200079880682c10410f1006e40498008007002d003034881039454004c0743d04903e00940580100c0d070459034014107031406503413003011b01d00003011040135290303004804008100305a2064028550501c0c03004a001440d59407090b1001d2400440354894014030100c0400c00200c211070380091003001e90491803050792070313481c2c1008900411980e84d028900c05000d0f001d1007401c6501026003e0618800c408032580c0304402000c001c005540c14100303604640c45000d0600c500104a009803c001e80c1603a00400d2400072a40010141e13001103a60040316040f071400b081805040185842c0100401c0c2c000b000080d081400b106980d1403401da25409100810f00301607500002080400000c0c044103001e01c0c1d4203a1070b0081510190840c0c03100f64451400c1a = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 997738120 1250 997736870 997736893
    0x71706060609090703020c070b030709081c050702100509060f030105010f0e03060a0c0507020405091612021f0e0a1401030e01142d0f010302180601020706110a060914 73
    0x25021944040e0b0300070b10424007691400700072806940207070302114184c01046c10000f02403c00e0710145001d10020749030000018242141c0524102d211021914150f60780002000d880e0b8200040f40c0d209078054903102040c03c10640151010710820011581041e030014601402031149009141624000d03a03480450150b202d034221500c031120254070780d1641140010842c2c40302154481701c0542d04034180942440079a40010302101e03070490340280ca60300030140a004a070904252080648040005c02400d551540c01040c2c111a1001c08040c040504920301a100b030b018400e01840c120006000008160700c4400148002500c858442e0103c0c3c203101314107044030f2060083c624481e140700340a03e050385d680c2004008840c042d807100020850840701d005409c0724404800c522655174900500c000e94914030502c604610010034400d483e041250a00c030041ea808580c000440b40c0710314107510b54550341889907051007075402c0020443c500d0221a10704224056081402c1d004001d0b09032130500004 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 997739370 1250 997738120 997738129
    0x1020a0e190b03090a06051602010e0303160f090b071505010b0418090206121608010501050408060609090309120c09060a0e0403030203040302010227041a010c030e0f0307170606 78
    0x60340075101040701d0111081c011058000b002d10782c400c19980885903441000d07203406045403000c6d0b46019103010070744a4241c4a035024000d440720013071048015440c40c40d01510741680f205074070800c8410070090381c80c040e03036142c420f4031030101a146e00142240e035444245050241c0500b49440080c00a0825000240c0592124182d404681c0d0314010840c00780c1e0150201b40050207820000c0b80c0c0000c0502004160407411801c01d8800d42c44001040c132040c02040c0c028205450580c80350f8100842013000b8031914401040c1c1d01d03003082c004e0301d00d80940d813164036403035080d80101c0b0b401a401c08115025481d003550001462150440e00380d03040010307070302e9403000d1001c05840f0780113000c1e0600c134020100340020711a41c01540e10134001d1000500782b404440a403007101c10003070b50798000c039052103482c120b5a20b0180b14804503210b158054901051405001802901072100060140f105501c20900c071501e80100200c0e55000c01000d0352815078640360035200c1305190350401c254032710030000051000d040 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 997740620 1250 997739370 997739389
    0xb34020d0e0a14060c072103121a010f02120c030406120902010c1b09020d1a180106122c100c020a11222301050f04240801020a0e 57
    0x202e10f103503034210140d40f0303044c44980e078441e2002c0c440a00c42c001d40091100070341200c00c01804510000580180c1e580c2c240100302c00550002c00491070728040d1009a45069203001113140c0300c0a0900c0421010031920990030f00406070500d0144510005072040b10b100080300400c1540c40c1c0e138994944402000350760100302c03280c842000340803e502000c0c0311702154180d003c51802900f020f00008403203868260000076038002c4100c0180642e20f5184400c480755982610761b640740c01c1510345516210b583c824005d9414010312038201807003400000303402c002c031450f0050310b0306104098075080740d0341c6448005038402c00b4020795010b0710700860f032100d0800d011900503501440c515500405000840c0c1d01da0b8502d9800808a455000e10300030030300015903035601701c000d562850a0a00180f5070340d075a420090034800d00c0040100c030151841c0140100d0381e8482003a005401c00b80d40020f00b5416201810740c01c501240c140d001e00020042c0300040e02c0328150018540e981c82c907625000383c4412501070200388030 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 997741870 1250 997740620 997740629
    0x91406030307061508030a020c1e0d0605060f060304120810030503090907090e16030b0d020a0911070c1e0f0e1b0f160b010608040b34020d0e0a 63
    0x10001c00c20300340401c030305804c441d442d03240310351441500c10356880703040d461a0b009480107800340e08480d408403100d1400c40d070031030344240c1951b44090071010788400194900c0b9071410000c100c26595004a50f0070748031120111900d403809008203680c3c0c1400c1c1444820f07591110700d07007030010714440c0019900c80c49102d0054101ca81c00002103007014404e1007004800e0000400300c80800480d440300207442d40512003480d00030641940b19003164808008010203540403011050300420201c1c4201005881d038000b184200c0d070300340d080000c040b1003c00c481c0e03900703120340e01c1c010b8400402c07194045400d0705010b4401030720750762001c29861600c2ea6110b0020711010180316880d0003413288c0d07000071409150b03030320403401d0300c01020710851400c44001c00f241031a401840d031128003013250705041c1040203880300155014008a0410340030781e00c0c00d6034840b0864400249503104100301402d2844014070703103150006c1217003500c09003000e03060151040295103102c400020b1000a001070503200742d600341841c0810596 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 997743120 1250 997741870 997741873
    0x7170307050d03024e0601021002090a06051b030a08090d080f060f19180f020301030b0c07061401060815010e0127050d03050403020102060c03130f051f0609140603 72
    0x2818103103007080d408858100e000c0c0a00c08010348071005d84100860340d031080d094180d0000801d0500100080c60929083d1684011502c100600d50b295030b6082201011a140c620340190b81d4052807000100e103c42e080b0780da01d04c2e44030108500710f40f50342200a0611a403000c07012902c038028100001ca442400540d000b0f01c122420501103078443c24813600400303882c50007404200d203103024078403902c40c6104c00d5400310048000f01c008400c00706650f80100c0c0c3d0403010b6400150b045506503281c2a00c4683c001d42189072658002560344108861a04222200c3d00c01d1200703000550ba54071409024150211080d50303900d0813840021072a5030044410503131101041c0d403408000844c1c107100c07646401d862202c0349918040102c00241680d0381540600005129546041d00c032407640c8006881c105000e04541e05600003441080f900603900c4144500c1550050700c8194208140e0810a060030302d07060724501403440e904a007082032500b80d00607508a40c9070b403004101d155680032a90044100c1640c1840d810b = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 997744370 1250 997743120 997743157
    0xb13110313030e0a060e120a12111207081c0921050403170405100f120c0504050d060b1e3303070807140408150907170307050d0302 58
    0x41c514403402207000c620a040100c90342c9500d070000b0f0200d0405030b001030001450b801c0c00d907040f81040320001c058070000340028080040c10f5600c04003840e02c124100b80070014280111200ca120030000c82e0705110010300f00540e07a401506140361654840c01d403000482d00250b000b5030b880c0203548030b0482015041200b42e8800d404513451307800c4686100c403103901084800e22010000c205010715100c88580e0042003180d88d00e10300414080c0000d582d1054109216502c0181c0400c1600581d8400511041050000f03010703014107000e0b02d040c0141d0700308540225010350ba0200f00101503100c038041d02d0080700c00b01601d29020390303540b117811a40342e001608503910881486612002070341c80300c4a50401488850f00240703a00d105031054100311046e10028000b0014403042e103401c0420840722100100015123800d04111030380e42d40b03001000c041c0a100810400140c540c500030301141c40130341020201640c03403104000120790340350044642501c3c2741c001e0f01102c8180700d00074030884400340044100703000e1 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 997745620 1250 997744370 997744381
    0x30d091404050601052a1b0a060c020a0f060810080d1704060905010c1d0102010c14070606090203090d0206090604020f10030b0301050a0c03050f040305040b180a03060b131103 77
    0x34000c05003105051180900c042002080c0003005040500002c480c048a146e1503410312614004400d490210300c04108144058103494449610b0207075101414952552851440030074200456548403d0485180c0b01004c112958404c0c181e6000744440040950003c2e1070302d89464841c11440c40c503c02042d04015014051903403407944d00d0b4814010310000440d007030303151641400d40390390784411400203158030542c02c4010542100c840d8a98803c0c40200711030989000040c2007280b940030246516840481c0c14020010650000005040303520f10275501c90900b20070042e56000702c18100005400b030300c000500c4400d00000c80910a0303400504415840420100740002c2d0510807641200705a142c038089680c54909008040c0280c45aa50014a4141038500141100c0c00680b0b007000305c41c000014080866802800d850680d03003d00c11156030b400d00d0304008418108910f03201a0802800c43c00001404010b502450001d003041d115405040c400d040080700300c03410f80c603142c0d02c6100180f002c00c2 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 997746870 1250 997745620 997745629
    0xa0503031627060c0c1208220317030a0e01090843030c06060308090f0301050402010c060e0c1801060810060c03180518040302010c02030c060604110f0309010b030d0914 74
    0x804c14010a504002151210303410102c8002c4d9107402e480080c0002002c1e02001c020000b04180c0d4181c2a0401904031305541c0e524000300303c0d1078108680b9040201c04030301d108005601910700b00420380b000b00800901407600c1d0a0136008244400d00d00880da10809940c3c1c2c0b005400c0095203000b0464025006a55026407084050002d01c02d90400024201031000a283c0b40700d0b400140d800f940b0b0f525100e500d01c4080010f0000349204c0507020341d040c4001d0200503600005400080c552014000c5031140c0e103003818038507100e40700c2c26407540f081025201d0301000ba2400f624506239005036071001c0349503840b80040f10301d58005109201c0001c80120a00340864810f400c0210b403640c140c048030850076520b6000400703e90f41e42601100b001c80303031400c1c001010340911880d03491111074006141410340e125040c503260700300200351300d0089466031301d5078003600c54060444c0c0e92802070714900d030b4603070070803803192402880b260150300d01074481c0002010310140140540e00480362042c1c4900e00060602040c007 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 997748120 1250 997746870 997746887
    0x1090e071d040c031209031b0e070818070b0d0b0307081e0114090f0d0e01120b04060812030108071d010b0a0e030f1f0b0307170a050303162706 63
    0x10740d129940c3c4030703000c00090500841412409900c1d0b0b56880000d0031820103100000d82c501c031803600104000c908100c0c585d04040d0059011000f400e0054080d6506079035a02c04040480a001da14081e10b8800304808003d003004c0e0031b900038100410444003203071310103150b80e031000c0e4001c04169a02002c44030545420704810903c2c1c2d42c615000114078482c0b10301007500035580582c0e040b0002c0d04200c2c00c442480c0c0d0700b0800c0e120700031120318090071021500c0002801a14560208085880c0c0b00ca03400340850301c40d41c0001c0f0040481c4c0b81100d69643c1300d4003031074516400078010010f05020b4814000b41d54505201011703460310221501e01140d91800300140070a03444602d200007401003041443c80e0390781c3d05112028000310204050003648400344090320b84014104c0100000701d203448034100b00368400080c0b101c1503421000320042c0d0380980b40089440c0102609009000b0304c0000700300024110340503064051059982c441ca081501c0f9507075030808a46100303815140895500703004101d42e0b0301c5402c05 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 997749370 1250 997748120 997748123
    0x120f02130b070b16090e1e0a15051c17121006170a0905060a0c02010e06040507050126010b071101080411150c03030a02040f050a0e0f04240501090e071d04 68
    0x351303699032032100f010798100440e6045151103285640d54076031241072035101d80c40a140b000c00c20924030803101031240d030249c034011039014014180043c41d0303d94000c010040e41c0ba802179102d02280303200240c1c0aa066204201c000344c2441d981002c2a02007500c03032070b04010740b01d49403a0441c920341e000014080101004000000003522018004041360090000c4d81c02a4031040010a00e01800c0b24043d0030b44210141501050740304500300030208502290050980300240380c6050881d441403130164801541e0300640d03020520403000099509640710051034414428100301e43c070120071000540c1c64101c21500500300808907040c0400600d0580c1c003224400001c01c40309170800311310f81c001e185544c108403501d80d000c6070300050a00c01c2c1c2881040c1c14001b0001101c0141d002da042041a000311000a40743c1c44410070a10042010409102c525000000802801e440700d12100c080030800b0b01803e201e65001a0310b8452183c2d42014045503c0080d5210001140000b64440c900c559140500920 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 997750620 1250 997749370 997749377
    0x10308030415090302010516020c030a0219080607030e0705040b090a0908160302010e07120c091509090305091540120c0b07120c03120f02130b070b16 66
    0x2148800e034410343c412003842d5400b0b94000039541c60310950109500b5a00500076040d135114060701300599800055030620b040c1e06494001c0011011049140190400c0e0807929480c0034810801a0380e980c107a0000c03014030000e0048550039981c80c0240700c22580c80c00750703254002810700009508884181c1280c0c560502c02c9403c940761140201481540140d028000c41c011303515104201d039405030811140c0b000d4661240224a840703110b944030903005e50188215022143c5401204000219940c00c2d50014620404240300c4110545001440e6034042104544180144031303008100482101c1610090142510800000c1242900040203418a814a070709c3c00c2e6035580c409145540c41820b010f004051081503010310410520b848080707a6010340102482020600040004c100703810707018801c4c4106801c14500c0c042a82c00d044403500344030468411807904140110303c403000c0b654001e040769182e2218190301940c075064000700502c640c50380a480500014045000c4010086c0048058041400d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 997751870 1250 997750620 997750643
    0x6090f0b2812050f061030060e1819110a12031407111509100905100314040303050727150314071b080412020f12060103080304 56
    0x4210100d40c0440310700800020b0545612000702070024015181c200d005803060001a18080c4c0100c1c02064880c00b5620030002c04071050844c2200a1081018030b8800c0301d603800c0000d01801150019000d21b01c110f003051134940000911041c01c2171803008a280b80c15020303010705001600d0401400c04c44280c1951462031315041070090359500d03007a5070001c0c1060140395104200c1030401a15041d09807911819120b030811082c4000780c60000040440079048401003c3d942e40c0d9400391680303000d4189000d4211006070300981d8403640180440044940448501c6007842c2042d80071000e8400c03460701c1200c3c0348104030100b80041c0c029002654401d00c20710346100300340348090050707407060740c4409404410030340d1003001d21101c0c00480d40c910149001c0e080910040220b5a40000382446c020508000c1020002c045551044a1011000c9140e00164015144da8a9245162680d02d10301003c901c2403551218910301814240c420b903512680c41400b410690b840c0d503c0b414104c0d07100030022107041c0d0000f03 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 997753120 1250 997751870 997751917
    0x20405040e1506151e04050301091b060c0503030f07020c06070c0302040501091b0c0302030c070609080f0f0607030c0e06030a050402180606090f1c0f0302010606090f0b 74
    0x611805a072458010000d01c0000c614110040040002030300d224000c1c4800810084a44c460008948110002e00410a00040c1c00d4580003182c0c002d54200540c194206480c804c188a1140300354500940d142003c10301c0280e40c0d200c166501d0100c10301c018025042800010b60f001c2207500602da00c08400c1c016100061480030000c1ca503640708040455024000850500642c1094425103003d42203101c810040c0555141c004d001c1c40c5074641d83d0303508210140c030001d001c044c42401a2824225040205c440b2103841d6480076044410b107005440c414410f0740c074401103044000032464241d400c0b650161034140ca9080e0118013800004607800b0900001981d1555591202401948610101c035000501030030244100700c244000c203084400f8100140c41845080c0c0d6501040b621a08000caa218940100500200b1031085001044485200034068844180302c00b203003140440500c070307034000c025103a2107080a594404842c080d040501d0b0040d40305010601c4c4560041030a020ba40c1e007490504200c0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 997754370 1250 997753120 997753129
    0x60501022a031504050c01180b0a0c0b010f09050906060609011d0d030e01080a0e0601140406080102070b04140a120807031416021b030d032f0703120507120f020405 72
    0x1003c01240c50301c020404000503c101440032802001007440d00e000d1500304a05c0207410380c100c60081250404001900301c1d00b09014021801404d544001c00300565a03490030f40c40f040803518402c2412550500000404084000c211184a0790b00141440d040600907001109c05103540d211410075040c0c645080c80503075132000f40d03018400b403090b50307070107210501e040004003807640c00303440380707034111300702402100940b00c0070a406041d5440401401c0d1850328100000f400740041d031380559100d502c0080c0100500503202c1b02c0368480e50261403d4030f1000c00500c103541d61407400f83c1c3c0c06026180d406103145000c0c1d00c5080e01503000b00c1180350100300861103040c0d000b240901134400c0141e5240108201080580600c04140e8503418440341e0f1801012070004641c031a0302002c01c4104250b40c4a10500c400d03480c0c41000d002c0d2480441012a2403881815181c5c82a40416816070101c0e92419014601001c2030007502c2c4184050781d1403201d10401c140214024240d1a5141c2e48255000d00020070507884 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 997755620 1250 997754370 997754383
    0x1e030603070e1015170708090307020607060204140603010f060f050d020d0b0a08030c03340507061206060f111009080301050909010b03071413090321060501022a03 72
    0x44403c2ea1000b501e060003002465502184620600c15455a00c41c507000d0000c80841e441000380c141800181c0c0c03000c000a00b18071500d04002c0d400a40455a0f40c04d114650f4040c106865081c2000e44030424000f080001c0ea010034810660011401c407428000b40c3c0c03060501500c01c0c1d005013032243c00c02c0080b4030034000b0398202003d540113895985401d6203840c6024158a4020590603000e035103000c0c00c10f44a59140d01c648000c01c0f0204000818980a84074088000c69121541206890445459140c56074503030250b8071400e40042c0c4e07410012522012270344036101c00c864240e2100440925080c0e000d503100d510016041d081c0740a071400072028420940103800010344500c54855036581400200550200c002d0002910382c0c4c9410f240000540380050b628042d9801148046a1022404000b03407010410b0603903130081c2820140c01c802059000305103841c030501c4098441740c074144141d18403c00c44a041c8203250050744001c050b01c92242000310202d0b41751341081c0c0210a03030001d14020074545407 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 997756870 1250 997755620 997755631
    0x2130207081c02090f190603090809040c050d0b04060f030308071e030c021204150c0c080d09150f12090812070c051e120a110105070e04111e030603070e 67
    0x10f0300043c01101038035100300c52900d6507030120703101012400400c0e1049462082e6000707002c2411740d1660a00c080c001500190b420040c0000e000f800019400000180749421640c003600d03001e030410020380c16074a40780c02440b0030346d10711914503400d4a145032000c88440304044c0c9170708103018200d8480002500100700501103501c4685000c21425800310300245004c1c40c0b80d40b032045081c0c09110603c0070a08134803003152034480f1860510090201410040c402007860352024406114600e04401e4068200b01b8003811600f102031004052008000300b0b03190040441c205000042c2d001071001c942810f16480b1018060194420718240200311b407a00c01001401c3d6403c40118103071400030401c0200403c030001600b281e00340c5c9494822090201d1a607a90303800c0401440c11403002c034171440094402d030280c050180b5298001e0015042c0341d04003812041000000b14041c60070548500702044401c8129105012284035407000080c00120174015500080d08172541400f6007280002d0101300d040c00300340100d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 997758120 1250 997756870 997756927
    0x1305070902030108070e01080d0302091c0302061617010915030203010e1e0f0a080a03270c06023c12090f010c0803060904051c05031906030213020708 66
    0x2c3d41815415490036659510030503e107a140780060000010101d07800389508000e04000d6212810840014001002001000071114000a148040c19800511103005d01301c02034141002c0c0345001c44c211916104010a998001c880380010007000055a00c0b400c05540e0025002010b11b40702d070700003400c4d0303801303c6059900c50b44160107504a40c441800c080001408110042070420b0781203a103151a61446480501000004201c90702914082e4016100b007071980c40340311203000d5900804140d80f943d900b405035100c0c0e455032404540c441c000205d405d41c0e41c0403549104044510310302020501510004031000300000700c10020551201000200022030030781c0081501c480c003080a02c440d101c1c2000482d1b0401c55a0520703000071071460411131360400400d8035005081c0c1c3e02c1d81401894000130803600c207840072020560002c900d5000f03000d1030042211400c0c5254000c800094070707096500600010b58412818641c1558400950f401801200e124545841c04d050404c011880030040020424103079 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 997759370 1250 997758120 997758127
    0x50705042a050405010c0308071713030e1c021201090b1602120a120209030f07080f070e0708060618030703081c05190b06042d060906080705031305070902 68
    0x1040d601c42051421400107207400c9051615081c0002c02c0500d01410250038401888082141c4510840907400200914480d603540c60508041800001c10308403819000110700501030300191500c881d05d0b0700303c020801064190b401031303a0200484112030003c688150365070b4070546000905507114140c850070b640132440403410502031380681881c40b001c2151501e00010490200e459400120180241648010040e207890321500480d25040c1e40b01110042c0744143d02001500c2880005c01100c160b01d2202075a0b0480c0c1d503101d0014446400345ca00c0c0011484480c0000c1c42070601802400041c4101e030141d16540782c9031400f007030520f600d0b6041501d103400000b4110680540008820f4600c03a18071100304a20300d404d5005030303d6005003da040980c03d40b640040c1e6202e81d184003c1e50040c3c00d0704000ca2100005482c2b282502408110350340082403088580000c249002d60105000ca403410303290341c012070781c40d000115101c0d03200400c8001000d42041d1502e01080c0200a04801307130802000040c0d5 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 997760620 1250 997759370 997759421
    0x9022b0b0411100203120a2f1b070f12020612010602070306050f060d0210020102122a07050c0603311b05012307150605040b0904020f0d05070504 64
    0x10f8a0f922202e42c405542c4200000e0780c401400c0848180d102c3c254040016051001e05045518503400b54034022820790100c1700e1860000d4241d006000700301d040c0c05122520340411106949500d558810109083c0c0c4403402006039092018405014a2000b881c1c0f034a4542c2d80f14448444603020381220f80180e000140038020491240300721500820807070360a21103803400400091030041d4110000740241810319203100c0c10742c000d4054a1070390105c0e080a00c1d072440c05400000040007141c49001c0c1c02c0304101800409148400205c92155801c203000d40b40ea01c40980034403903030b075002034000031070b1400c8001c1810990b510301d00482c0c03c0c0d241503070309040c0e54582c5041821494107813411100c0007020f41c110410190b0780012400c441ca01c020110800c80b04070210010f41039000303c140241503079155545000d040c1e0380c25070003401903600c1101c2c01c10580079680280324401e6012a8000d4010780f500752110000c0c42c0010308640b236a80706400700c48203540c4aa01181c203949038040c09a00c25088410042c030b = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 997761870 1250 997760620 997760629
    0x10905060d2004110c01020702031e0303070503040507050d060203060f010e010f08040c0e09150106090e040b0402041b0c020a0e040209041e020a06090302010e010309022b0b0411 78
    0x140c1103401201c01d681c04200300d444201c00403034541c25100c2d25550610100ca0320342c0725504103280381031985821944503100e40e02c045000c0d6000c420308030721a001e401416840b0050f04002c05640c0001c6000450640d511030b4820744850b03001a100340ca152159a1000805566501c00703469854400d03040582c890034030b2400d0007464602d601001c0d040c00f00c40c980c42e1190380d0b4031100708400000e8030715111845441e103007044454051150040300c1c00c02d182034100001d100740002c0e00000c900b0080800c40316a80e0724602103030b1100e0a4001c070200d500c5244d0219000c541c0d8882104d4205000810004007564a21a0320380390300032110040c404030701d074403280d00d040d80b40c000c00040003032010300a280e00501d0164000752000c0c10040c03004010b04d95044008004c0c00c1800190390a1070760191201c0e026a4968802501074405880201d0000d0b0040c100441c042d4030901840302c08617806410404440302560b0422010702401c1075680d081e0340745110700d4001c92103081505014602908442160051580521 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 997763120 1250 997761870 997761881
    0x6080f070e1906110c0f010f0e0904030905150c0a0f030210140a0b010203281412010e01120309181806020d0506010c050a03030b0a0312080603210f090609180109 71
    0x80702c03c0c0c0c101300200704150303c510303080080c0c107102441c8c612440511004250340c64a140e444039904032011104100030940c118803108281c820403140a4001b6945030085003007032003030342d6514034241c12110f045e1001900c111201400300b446401a20348048280c0b0300e840403502001e00303000c0500c221350140049403d070392055094515007803001c1d514180304845282903110070450700c0d10f40c1d0766103400402031541c403920b4610002007417100f40c9913035440060660450ba40003030041c43c0740d404042c8000101101c0d048220180030b9803584417421010f2a1840c00134000d41d50b4806800d81c80d88403c26803410440e105800c500715881844016100c0036408030440440d1801458141401898111303403000c5400061090b0a02d903041c035000c6140c19a1002281341100c107584000c2c510314490b20060600c6421900e05442904150b0450b000b10180c912110282e140c0f01030440303c102c00801684440c4000c0b0402040c8031540502824a416110400305004007400000002080326410050080c0c544901a8 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 997764370 1250 997763120 997763147
    0x2330c180613050d080715051603020708250803090604060f06030b0403230d0906050c040f03080c0a02040e06092521021002071a0315040b040b04020a0215090706080f070e1906 77
    0x1141007001d3307aa200c600d5482260140019020039240030700400c00e080c480c0b1203500c0e920114254403420300310011540c0c0c0c04140c800303c4405003030000010345000240300301d2044a41081c01551503032a00d071819039800e02e03039283c101341580780c0d26040c4003404000001001e0300700e119500018035a881d410300300203c0e07202030401c0c0b204040400c81040344440c0c4c1c4620f5001d883c1c12940c5180c1d50300c0520690307464807040e801c00941003400d040d080880c5076800f0500a1140141400f510b500390f4a2a0310110aa244054a00c920003101c1400f400070f00700c41101c00c510881d0514803030901c000c4c0344d000110200c0c251078000c0300503402a481841506000c1d2001400c1d000250b48190540c04e00500303494585120b541d00c1e6008542e1402003a030144d541b60041040050090003c564038089900001d480303004098252100c0e40302c0c1d0000c140c010000044880844589030b80700c250940326070121584950018002008210740f03043c46001590700c583c08607200c5075200300c9114201d0f00c1d00c4000303040703024844d41 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 997765620 1250 997764370 997764377
    0x30c160b090c041a01020a1b0e18010507021c0f090e0103120207091104050103020a0203090904060213060509030307030e150406091505090102330c180613050d0807150516 75
    0x146451300380d8002a00310343c40c9a015064602404030b0703040c1455100f4565000c0c28201100a080c030070781940c040200e88810444a00900c4a962035800076a03440400403140e0300768031f41c40c1c48000d00b80380c8280c024001513107407442e150800c540e8580312030030360703000a800c280c40080300ba44034250f960b501045810010000d0900c00d000121061040300c040b0700603480303014180754000840c060310354403e06c122194010002d02c002c40d1420a07041440003500300601d900002d008030381002c124940180e0a03508400703c014001c6107469066601124100c44501450740c110800c04000c0060f8003011002e0006000d9598072000300b186050131010400012502d40030900200f0407826007180d038080340c6c1058480f031000c21150303e101000d031801c1d81409500e401d1035100401c0801d1000c0003410a0041240d44485ea00324400360401c002000690312074402c50480d1140200410032541c103010740c0011049024149181c06c20a0b00d403500c1c107441d1003030382c004100c0941e1401001700001a034440000c01c6001840c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 997766870 1250 997765620 997765661
    0xf03030a0c0906110604060f060803220603020f040b09011e1715030d0305070e03070902030406140112030e060f3007090501050c12040b040608010812030c160b090c04 73
    0x882994481c08040d1020f00400c0d11000308e191950302ca03400c4113004001560450380d03601c0c14085211580381a040141e09905100940002d8141c032a0003078400d0010015140c0b844e02d4600560a40c0651021100a0600c62441e10401d502401c02d1000c01c82d0709150745410450b11a8006100b820007001003c8009101c0142ca01000c1900d00040982140c40c00b4280002c1c1902d0795041513940c554003540130f980c0b621034004040f891400da07030003543c000ea1048605218080c0b1854a0501c1200240100901c0080350310168002c00e21614401c0c080440c0913103031a1070724102a003060442c2d0b0140c0b140ca550301d4100030403240b40c11401201c18101000008142c801d900f0800d000415140051182504000010400009092050086410000421480396640c2d55600400f0000d03402034881c100c0464540f0700009807640001c51288284007603520000e19580d182c040d01d44442e0040c81c1542c040c544664504000500b1280702c2c280241c00c07410060500d0000c0b0002c0100b640d03245030300d0320900c0c048403 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 997768120 1250 997766870 997766897
    0xb1507023f060c0706050403090506040f060908341a03010305060a09260c01020301033909090f231213030212030c10050703060501111005090f03030a0c0906 69
    0x110643e0b26040c0c5c0103501117010b49841c1070450b50b195454100f80e910480009001402c051030b0303880c980c21904140c5544000540d100c2c00e00e034444038040708828120b03410300001380401c500580b2156090000341c5001c40c4054403030192140c9000c10600e51525903030004010b00c188442048143d80c0011580d0301030043c0031555580030441030344580c0030703d8160b0009030b00540ba100a40d05a4015050003c0215103941e52814800c11003490302940481c0401d40550011020507001100c414040d0018040040686804100c00003003070b0ba00c2040d01c1d1008519850300015103413024140721856045807514815161011060401c00c54005000d501402044410f481003070544d201c80840382c04458200c01040940c204a0452250113241c5245004400e504414404968000b50250400b42e400700312440d1614010740f0b40080c01101139011741d1120101c24134031441c5400c80c5900c00040415a003402c4012100303180f640d081521443c00043d11601300741c070340780e9210f8411002803210349041303003000c0c012 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 997769370 1250 997768120 997768141
    0x150314030a0e100c0b090a0204050f2a0702060c0c2d1203130303020703030e011d0f041b02032101030305030c0304030207050d150606030b1507023f06 66
    0x49102c09401090742142000e03480b401481040d072031981003401d0341518640b9541e82c50b161039142c0801c07849a490070003c20304181030303414041c0c030032320211524102101300c100b8101e080c07030703604c2404e1000894100010b00040e00d55001400c00704840303000074035800c00d850041000202448101000c4240404540841b07122000c2c01c1d10454141a10304513101c100d01c004c00c90440c82071800780c0001a035440d000004242d40007503400101c901950310117681c160b4600044500480d1106846804200d0460f0000d1626111940c100000c400500005201103084502d0807072040d00840c1d80050703040454804140034190007c22424440305c121103a4541c11950064254000034100c1111180c0100020313007094000c00a80d00600320003443c010441e03500740b510440c00718104010b51a160704242c0c00148882c001c3c02013480140c40202043c1c05001e00d03051440c0550400a4180d902c50303401c1884040c0f6180c6030b8280d00310003400c01d21146081084406408400c5409500e0803000da1081e4100403084c80c1 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 997770620 1250 997769370 997769387
    0xf061d1b0f0d060e0a02150c060105191e030c090f05130f030c110306040b0106031a0f12030f0a0e0a0e130204051e070201020306030f0606060f1309150314030a 70
    0x81c8107000041181c4c242c8103041c6840980440250420820784800c1007800084000c2d1920014040440c4c683d6a01c9406006502e03112440307030710911000c800c0a101d0408035001006a1a5100ca51010302c20795a4451454060883d4010560075507200a815008072070390180a82c000c011304066010b240e401e41da1070146401c8080701608002955480e1030801c0309441c114a4903180082c00c94a203424103007480f4590b09428440d82000c02c1c940503020440440f00030711040e0300c400040031001028040c0051106a110301407005034030f404100021698200e030540504209046a603812400f100b0042c00d10852540e0b80c0c00000384400c1c1c1c0810080c0c400309070841e46288070350659020030140c03124400d000c000714030404078080c0703040420200213000368150f001e14850350085013114129080a924103032101310a80e040c43d0415401c0004007011000711004000400304201e08100c0240d03240c02c008110703401000d240c91a0203081c0303410028009259219402011110b0240d0318103891200040c0ca00750 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 997771870 1250 997770620 997770623
    0x5070b0307020f0a03020c0429041d07030b010303020d0903051908040e16031a0306042009130c21061a03030f03040c150503040f061d1b0f0d 62
    0x11002000401e00c52092100e03040c401108000c07909070070300a01d0702940360742401041c02d0041d4580b180c40125078190000000d8140600141d0f12000030000c0705200140500503a4040010f2408600903170b0114100050b1740114020118484103504615000b03040c6407241c9803800070041310301418004640301245803101600030398035100c2921003910389507100e40110383c81141d4540304402005441c203041590405400780300c0d503007000700400804c9415881c0804000154155209030f002074001011400241441030041407130920b11007440000606080c41214011b6401d0954403406040041901c68200504800c994041e42190300d4808000c5500000c000503012070344841642c441686d11945e01500c003c005420b807581c5000e5444011b16643c000d980480c2c40e031140080010340d1083c8248415484039041ea201e07442c0d51115251004050b1100b442500c3d02951030846407841100f420340c0341c030101c0107034001d4080c02e0003031040160040c0c803c00c000c83c040d5540741c200d8000c9039104008050340710b = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 997773120 1250 997771870 997771889
    0x2040e0a1a060d02180f0108010c020a061d0118110406120b040f06050c041403070b040b30090c09010b0a11150108030403152d02160803220507 63
    0x1682c44900052036640c10340c501940022658050401c80504403104511401601c00c0466050766150581c07400c940c40c5c407000364016001b11500e000010196045244503c00c1c000302c2900100c1c0e003503040c50850f45a41c03e925102d06262500034108001000840c0301c01c0d10440c4c0c07c0040da8580028a6408840f044e0020304e026622000501003003600004c2950b0960040c074204114602a140119a40d029004c2c050310103884a00c890135500c0c1c0000c11106071086040702608262800c0b182c00a5500162010005106800d0110360385000c5012a0703008420f8040c204842400e08005150401c501c0113503443c01011b981c00140300d4200000110703410707140785140c0351075005034208030f0500b4202c0302c401060b170705080000005100700c0000080e10170340707020f42030921555041c2000b903400c84201d00d40700c2c44207520900d00740214244a684804801074440c0d000b5140c0b60444c40407a0b1400d4070383d02c04035060303100442230010760300354130141000d04c1030a03c0c15141944031548034290341d40c0c07082c031404251 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 997774370 1250 997773120 997773173
    0x18060a05040302011803110c03011e0507121a040b2e02010204120507052d1012020d060305060106020307080f25080d0c0e010e0f0103021309050402040e0a 68
    0x2c06200354040000e60b4030585610000c0480da15000303042142e0b028840300f5900c9104440051450184655030700a540d07a0b94409880305502408009808014001400e11680720300350002da0340e030b6000d01c0c0e440c9003001d0020940e6584800400080702d00c0049002d01805800609130f124103010040c4501890302070040002d20415110100e01921854208600040030f154804042001c002140f03010748208658801d54007040e0800d078000200030402040a158107600e004441e4100040c11024031800d5140100a249180e05e00e50700786c0c3e10441080c501d580da03449040040c8201441603601402d4984083d41c60200700f0384481e80e041c01050000104c000c0d00064407466449002c4000d001e8066290360351042c0c7c0d2603414900d5a40e009030300704041050038444089a8188203809010320201c058480200698000061181040420350b03c60305040c2e0800444103c0022100c105005012071040441c6a1401d881480b0960381102e02101051744109100000180c1204440d03000c4080082c0384481e = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 997775620 1250 997774370 997774373
    0xa030b040b03150603010c0f140306031002040605031f122009090a0507140604060c140f03040501090e06011407080f032d040507090b010c05010606031418060a0504 72
    0x50403910039003641849010200361041000310f066512a5004600803c0501740d50714094640e611401c01020000c1c03031112200c0090070b0500051900808080e00316142c1c9840d038140d401c1260f100ea007228003c1940070017001445814400b0792009071003040741c0820101d160160042c405e4445801c0189250001107c0340740c1a2030100350700c0440712008068050600707140d0705c945d460f401c0040d0191064041e080303004c2071040030311410420540000d0121032406180800c00c455500440307604943c000030301c0d035611038a0034040000042800354440650341d82c525110000d00384020690100c08a030025008126007607802080b000c0c0c0c52810040c0e0390707584102d0303842c0850240c403a8429a403c0da441c04414003034a65848908800026040340e411410120b00101800910384226401002c561240c0030602c403600943e04407401320b003818100080c181c4503545d40c0070300b501c0e104d4000e040000d5032404c40391040c9150880071a0050a4104030034403991281d90f10342d496510040c40c0c043c51a84800c0401e0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 997776870 1250 997775620 997775629
    0x1103070506010f17060c07030e0609040e24010e06010302070f0506040602070605150d260c06040507290f07080c1501080111041715010f080610030201050a030b 70
    0x1114294080c0c1580c01941e107664043c80101442e018203070081c0e880c07040201860f400054158007401c8552a054217103e00e6035001c07200c0120080e0301c150801c205008047c215155030103030400380c8007000301410140303d00ca07805001c1404042400d480c1c04004c81d004001c48002c6410f403d410030400e28015070744a59500340f9201000c403141008041e0f104000401c01070000e141d0152000c50302c00c540501c400d46400c1154202c041c1c4e07603405103a21031021940640002c1304244800304114000201001e1108986400790ba070f41c01840c42c20100703801a10401c000c11900f4825040905a240001142c44074a1110014100d03490b4001e05810318001800b00c808006449c19107040d2584400007a075030703844046e400ca4a8020302130640016121680010507103c0040c051040c0003401091010305061410360614624603c81c05450168000c03180f0309554400c030078400354040c2440394191101146858412842d2080c02004031290b048070310824401030380d00204a440d890703000d140c003107482c066400009 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 997778120 1250 997776870 997776877
    0x112050708030c010606090506310b0721020f06070f12060605070c080607120f09080c0616050702060406120e071508130c03030f02010b030703030e121c1103 69
    0x140002d100105a40c0440641500700030144ca8140d5144007881d80e0310814002030340102c0301c0c0e00c42415481c01180ca401c0c5030380c4003902032149a48600c6000955105045041d81c0e00407142540c60b401d080500c00007251080520700c44080240c030003006503102c0385040c4c0e42c1301d1201070104010480d04203800030506102c2d02d01c640e04062058020061182c2c3e8882c050003a60044c1012250b40034141d600003440000442c10318031a01c416280c020101940c0f02c1c0f01c5000b03100541c03460341c1c0d1513074030307908507000c61060405020411400c000400c404e051241d40003040c88007081e0208108402003045600503221207040c0c030100c40c03180c20075881260b0300c065280013610031142800050710455100040d814040e01d40198036140c81c0d01c0d082c800ba2501400240c66405030000542100070760b120810000c1d10030050003d9980d03240c4000503800d030004001a0928100c3e91040c0c000032040d010f030910b54540050881198440f040042042d11221442d0302c070301010403640d40e0f0038444100451842008144200d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 997779370 1250 997778120 997778129
    0x1003060606080f1b0306060702060415091802030105010c12021f020a090509010b0f0306010c0803010e1e190507020a0f0510060602070303080615090d060c141201120507 74
    0x6000c6607454003030003400c001c0200d800080c641d44200104104440c11034104420520885a0a00e141d5440003031005030303440000300702d0300900100400120715040c45241c4400840c1592501003452500c2d00c00c0490002c00c0401c50f9540780704000412003030ba0020070081c0030951040a4401500c500242a4208010300c040f59511070400020703d0781300c55440e4014940c812071a198071200c0368440c4148981d00c0300901492400c90803c002a900032408070001e141e1000741498001c014000d02d594071003c9030020381c07100282a5441e410b10003034078440145080d00310445a8154120b00e8480c852540f108910800050816516404100f2981c0b00f8082d20305519040290540312038098502940d40c2c102c078100005915291520101e100e92000c41c40c0c0044030303015903c00010382c640101300032101d5802001101140c804004202150312428a043c10450260000144124030850040d10003080305045490072041001205054802c140c90141502c50141b44041548030a140941c54140603411 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 997780620 1250 997779370 997779383
    0x209360a0b0d1a01120c05040914030a11010f05190f0209060a08040204201210050d0f0b180307080d0207020405280c051801020a0b0703090209090f06010b031003 71
    0x2d00d10140828920b00c10305520710004921820717030740d586039400c1c40c05070f0080060298060100030081f5240503040078909074014459a2041541014207a1469000e8250742d00410307903606161003103960a215004c004604110184024a402e02c1d501900c10007450070300c80c00e0703036031520150300c0f05540e0350548503d41c0b000b4001503076852804401600b183c030100c030201d00c078a042180c61420b100f118501c100741c0d4108807100c142840300741801303842c0b2908001c024034034003042c00c1e8001803142e4500500b812480d02420f02c2c0c0000b540541404514014010710000e0407859200540c00030900000881c1d0049410110054862080f64081c00103449201c5000e580282441c2c20700c0b00c0c40d026980c81144007aaa4204000c0d5090709203000000d4800f4074001c0c5000c03500501188101c0c0b80c12407100785075203005106882c20004541d50702156800151018000241c0d103148400450804003401a00054400020204603440022441d40d41c1c41c14014589440c101002107102062150802d00195030b2000c1c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 997781870 1250 997780620 997780639
    0x4080d0f02030a020912030a320d05041209060e0d0303060b0d02090a1a120405030910050c010b0102010b0a03030c0804030c0e04120f080402090c040b0d0209360a0b 72
    0x152400f002c0d40000d07030f040d0310a2441c2d40500945082c00070440310044a19100c480b50309801e0200700102c98014888008a07130b164120541010300140010b01040c3c81d0708034001242c1c02c0508003403602e02e944541c40402c2c440e82403410b1009580007207510f845218103c8025040c0f40300341c90100e0180c0710a0784080841c100c04a00c00600092a80140c00510003d44001c00f5069450314040546840c0c40b008007440c04040242d880c00b1120722007003d0b4058002c808403498034005402007030030800d925401c080001da02140d4081c00c14000e02465148010910007489466000e17000989004941e1000505200d43c504901b007c100b05102a01c0c01990441118201c0d1680c400c94010071030021130f8105e642d20030740341c03a1180841c001c00c400410181640d4903001c69070766903030900c2201000a011107683c810300388030005400c0c4400e002010810030700c42d400750310f0307580600034051409000041d1128101521001c0f8000a102c4100b84002c0a800c14500b0190344034540f0170360090a01020064203c4e2543c03 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 997783120 1250 997781870 997781881
    0x1502031008011a0111070b03060904032001050f2d070c14060f10030f140c0a090e060a0203040b0f040201030b0a0e0423100905030d0c09060212040e04080d0f0203 71
    0x400e500300003807100780c035049034041100000d944c41c6c9220b13005040400c402480407440342e0070510301007684148030f0300b010710f00c04102c1e071039001640b0400280c0d062140c4d11007007000124000d0b0004550400070700070004003d50740710640222042e8510511072035241c3c13800002009640701c7ca680c208101c0c0c0100140e0f41049014003840d407200c004888008184140c5000304003290014036940084940064131569101c1907642c6d10f10200700408840311080c8601c4482031155501d0780442d40050108400015100420030551401e00000034025210f9030320504c00c000200d0003042803541c0c400f51121030325205582d68070059008041a10070b140d001076140b0404500c1c0d404103003035071340141c1c020303e03960b1a01c5849510f0303410650500b804034007c40d0000ba5554242071155040451014440c6064906005601c24180704454103040792074005542e00c00c081001c00c4d0140b00c0c1140142060914524041c1401c03101440b913080500010b0161100190074910800d081c0d0005214001240c4150360341e041c0b8 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 997784370 1250 997783120 997783151
    0x3050a090c060c030f180605130f08011505030a110907020312010303080a24270c0c0210030e0a080a0c1407060e090f01140a030c090507030513150203100801 69
    0xf40303001200030071707615012032034244c2c01010290341501d01aa012491a410700604448a41104119680c041009800407881003500c8041c280541034110000548016581d11000c904c0803d51041e4083c0d00050880004503d0006001c5d60501040c0c403252181e4880b01c1080785544034200d40c80f00f00141d0880040304040d40040b00c0c5010389000780c0240a090780442024035164003425612412026a200410405640f0380b1103502c010302094141c40444409a22407040e19000b6007940002044008d600085190100b0031141c024850b1408112182e1008011580c900c100301025004040c0882d040307590900c15129100265404103850385c050404007a031941d50440340c011400443c502d581c021510b802d18450b02c6100e0050f20302010502d0b441e118241c2040c1c80000031298010000e4000440481c202c1294580109407041d00010940307451500101100c0c0080e002c06030302001c00c0720186c0070403140d804000c0c1007108a000180d498550306400c8030f1520b1940d0043c080c1d54200060488100702 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 997785620 1250 997784370 997784387
    0xb07030e120d080f090f01020d020a27060c0f02210606030328090312051e1602040509011b0c200310090305070f0b0a0609110a03050a090c06 62
    0x503502081c080144a4241c0e8403032052022020015880c03e00292810030024005500420020103446201845060315030030387e8005d844400b18560006145200d0540c0100b24240d10717042c403805078410040135020301c003118126104090402200b1440d8000b8402424001c8400c0d560003032903074070461441d100b00842000c03000c0146002c0e018001c005040c0341004412a20f10f440320100800c1201d15402642c108010310200890404c848110080700150012003030031004820394480ca500d94450440840006c010061822144081400305030403e59455040c840900d504880c080b846507130303040303820f401410001d20364001070f20b8241d6210080d0340c0100916450500a0798810000c00a1450360b049804580b0503007a01980201e545080c00303051603000c40c00c0e061003442c1c01da20300b81c0d03d40ca4000f0001100310b020348500c00c1200a10074401d4a40c4103210041c90380c60014804c240e0131040c0d0034a5030058200a50a2584600025030120101c0c0d1254201507030100c04102c036691101c4004100703e6 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 997786870 1250 997785620 997785647
    0xf0a11041814010f0c020703060e03192109020109090515060a09051e03060c0703030e01020a0f11060601020d0c1502041403240402060f0c2b0e0a050402130b0703 71
    0x146013288403040b10549010340115100c0e03d4000b00386203455a13072800024010100340103014081403100c40311300c450403481080001940e0351750b15007400c0c94078506140c800705054812010f0b4a4902d8010040c1d07000000300080303600c1903a0016041c0d540d071040c424234640340d00100d1340c0104005500e640ea10b801c020710f4010380388155104080f200100f14906000d864080000342d0551028000030035007403540d0020010540301345008a00016000840c13401d81e0000400c18010075050810742c05500e034401d41c084081d070300000c0200103500346040040d440300a6404031804000d000085042800340030000d540d0b01c13058004045580320780c0c0360342c5e00c8004044038502074802c0c040d4840ba00c50214090214020000b00444e10308925140c0c1e40c2000415441281440c4048900b403200c0e03000180c0520200d00c41121480d54204040c42d042070f038518110300e03000c020090142183c61392005071103010029003911001ea0300180d440d01d8000220102c0d01a40d4094001d03500c000a208082691040901000740c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 997788120 1250 997786870 997786873
    0xe010602010b0411030f061801090506101d090a0e10060e06090403021b010c0b13020301051f03080906070f031107060c0b0f040c050a06020f0f0f0a11041814 69
    0x100c485104000a48003030140309203282c20180003150884910783c40854100d034004080608c03000007055940c00141c0264091400503585500300720349400c0400150701c2581c00c1e440e145003c0c3c1c440e04016990041c0d81d00505001740300781d800240c8201059400901d00d90b007244120f0700b0300f140700380a01e03014181038094240d41807042400300d18a4140030310030b58002d6034150044e040520300da805400c0c82980d4110018100b2540b00342d101c0101e035989a045008400090050b00042c41d00d0042c1402d4440141144014900e101d80c003c0080c8002c0d01e4800070740b0340c070203a404c0d41c40c9064800101c00d0f0003800400740466490000740c05c101500220190031030100c00060b0740c01c40c0d5866109a031120b203000d50240c0007140100010701403080101c00150304c50b03c9120391f800311700d841d100482c2e171404441d0408005a4410703100307800820420800701c2070613500400100203050070850707900d4681e1004100109003021926a00c206541c032600503152901200d1a110b400040d00e08220342d00d0565160310745a01e = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 997789370 1250 997788120 997788131
    0x60b04090e0c06030f07030207060c0f2c010819061e0506040b0306010c020a0f080d020c09270c04021809070e06040b130806070e09011d04030516020a0e01060201 71
    0x1c01011500c10200b107030041c03042d800d695848000249041c001810b00c01010780c2001940005049840303610103201141d0748607110207090701c0d0043c243e96845042031900c43c0000f100443c000c103410b03810313080b0a102840e20040a884005a1812110044070700c840e03040d060000c0420800e9403143c103483c1c1e0081c0c04d030803c41c6065550f81413103102e1156000d40201e050007080022a10350159030b140c0f46091025041ea0542c44c0d175408041b1019109400003856a082120764130440390b030402c40302c5074200084030f0b80c842c07c0c104550b48909409070b052100117844401500100d0303400d0140195220840013500955440d803801d20032152140368409080e114071741100100c0c043d1842900c1394080c0040107488589000e081034a400e8140d00030070201d284d10100c0000115a0740300900209004a440d5110400f444001d081003180c4080160010030204450701c01d4445040b52480c42d0035040754060070959503071012036840424042640b60007035006110000300050b0319400d00ca00300d04841465000300203 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 997790620 1250 997789370 997789391
    0x120504120206100b12040206070c090209040f02040518060315070e09010905090601091d150901051b03131a0702161502120310170a06060e060303071212060b0409 71
    0xf00290318001e0038991042408400c2040d074841c0c81c2c60341c2080c0010b0149042c01800c0d6203d211009082d0048a45190046440e8049080a02850303181c030079542000d40c10541400045600e4003510629010940c41a01c0407031450349060040c6285503100c00c030440d1941c80c012201a00c410100c6008a000d410325000000710050306110752402811002d0140840783d1912010002910100458040c8907a04030b0020603c044200645860004030010f8541d1a207000c50312142100c1c00100b228032000742c000411040d801d000c0040f01e60048003a030320003880302072500384065041075a41e00c42a94032420001c0c0201d45030001045c0c961080381900c200300c116151f070b0701d0f00008a01c0c0c44506001d0ba001201c1140305003849070246900c802d00a0000d102590b07100e9400104504c520407900343c0340c0001c0801802e201c42400350381c5c0905010081460a030a0034404666a8400c09001603c541003184600d0354071440380c4c050010811640c50140302c03254480708100c0044d4401d120310030b02e01c0c0c6403c84020 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 997791870 1250 997790620 997790641
    0x4051c1a071b0501020c030d090c05030d0215100b16060c140d0207171c0b01021b040b0310020d0606020f061003030f020a05010c1119080d0c120504120206 68
    0x5100d00c1ea10781c0c48941d420341112482c00b0115005500300c030701d55002d1101e2400b0510401c0074050303201d12044007080701006410403110b1038030b0503000320b0300a400c81c406214840d0b400180040b0105c052100c048074555411030b40c1842c1407810380200d1010400082c48408845d4a0071101800c0c1d0300a45042120310b10401e001e844500d404081700d070714040c05000d160303640422035001e01007850094240510304403042440720030701d50010103948820f0910307448540c0d0306c054a200303507840d0110030b0004040c2a805060a24035046186580d039201d5500c82c0b02d00f6a4644051007002e14400300010199180e8110894400140c80306024000c0107200314011002c2008000035a41e02030b484259804100d0390441d101146c0000c0304d4150f0a003035110311100f01d23000a90900c214040c002031303903a8000d45e40c444010200d082284105031a88400611160480030504500c01c644228000480000350705103495000d40324046480d0341100030501e08010041805080340d4041803802c41070b400d40340c4039035402d2001d0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 997793120 1250 997791870 997791923
    0x12120609010e01140f0a151206060219110301290301050420011709061006020307150e01111207020c01080c04050d0f0803070909060504110f0f04051c 66
    0xb00303503800c4100010050403c139032080c0800d40d1000303084442c10f042d00401241882d1410b030b1051180c0c04039842003059581c6c1c0894000c505e00540c02050060f2442c0c040004d55900400d000d01810761407074070f42d000821040d8040c0d11210040035000713000c40e0190400500c191800d03480c4400912140320318104c01c0d1300d01807040c80c0c400c0e5845100c510b01260f014502c0d4800028a40180341441003810306c0c00b0400c001520450701c910301da00001c002910703026040c040a007180c0d0740b015041d940244903076000141c0400f48402303c03010580c4000b80e007404000c1000d01410300d0111340c5d80241000031b403001c3d008a0610800384504940e400321440440f000c0d004441800c1c0443c0c2400c1d005805000034000c0d8500004682c81650085008001c15112600c580300300f50b00030f4031170070301241d0305440c108100d05490103540c0051804540400880d0640d200300380261080010031403645400266610410b5810b40a6501414024010703042c0d120409404007150781c61018190b0341c0414032414441d0001000010 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 997794370 1250 997793120 997793129
    0x527060103060203040f1709040c0c08070b04050c100215100e04060e15090105090616051e1308071a030c07060903020a2a090204060e120f1212060901 66
    0x204980c0e880c0d519400002e4101400c105c404c6100c03030700442c1c00b04009901c002c1c1904101300d8410b544800d110200b10131207404588810034411910001303004500c20405503041d454100140903203543d6185440d5040c62603e0a800d9409a0345a0740035550307a0f0f0000341d590802d644a840380007640c84071400040a000e00d80f25204258010700c1c0080e00044a980000e02c080c0650b808540802e01c480703000201d24042115204540e030b554108000441c44200909900021015429141180f40c0f28005185200341c02213526181c00c00d000d01a0a051110103c4403102c824401c088455a10740c100342d5101c0e0020302c5005e030303038800c0382c41450360310003001d070889020385030000302c0c240381c0704041c4d41d83c501800c0741610a900b903004000032013000c22614080d40000f072829110084800c1002240c01d002c42080f608400c0c55a44144000e002d120340200e1080f0603124202d030300080f58402100d8040c6408041101194207015150718644106050780203480d41d10007090b460800e50390b880c8103115414000f440b4 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 997795620 1250 997794370 997794373
    0xe120f030403171e16020406091a040c050307050901020c090a0903090611100e010f050408030612030c100b031f05011517191103010f030615030b0c1b0d02010527 71
    0x184d141c944081c4c0c40080c0000d08121001288600c0c003070b00002d003280c0d156848201400c0d160042d4048503210329002000b10101210304015085044100412a0100178068003d210303001521165aa0080016041348e90000b8071032402807506003c000c000d41164001100400d441c1d5001103400d50140b404550903680d400d00170901a000042c00e0340107001602c8010030b56551701c0140740201e004900889202c0c601911030301d0744d01d040400a00c1041d9409691144d0315407c10310105400d000089452008800d2489011500e0304500340020b040660340301111000e0381000d203080c2000560340e00514121918042c440305580a403071403c0d5004002c107100164419149000502e10040042c211440005840800100a0b0b558650b202c6658000c1e0087c80303480165180400130130031603001c0c4541d040090f0b004880380d5851aa107411170200017502030105807002150a081d10080c41551040d400c0201045407802c0100743d10203802400159000a048004014010b441c076007000ca4034490600d0280 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 997796870 1250 997795620 997795657
    0x60709120807140f0a0302070501020c0a030b0406020903030c0105072607110c030a0b10120206250c150e120d1b020a0b03070e19060e120f03040317 65
    0x41e1081c410741d0061400326015400c404004104000c1004140c0030400003000401c0c526030a420040c0c40c01103160300490466000907045881c0c2d4552804030f004503a070180304034285480310719010700a405040c4240d50140300200350aa40c50f041500a140a06c0058544103000c00d40f000501c3c040c40c0304440381611102200010850080c41a098075094070075000c10390b10040e0301d981c0028105820034100741c0c0c1c40c00c400c1081c480750001200c1498014651411030360300501e00c0764082016402000104200428801010013040300081289111240c0c0701c416804156154205807001c1840a03503010009042e00d1406c40c7d403801c1c00d08100721400001e1004043e80200140210380c5880d500603088600c10f5403584c0c02c001601d514200074082e1109160540e12880c00c80d10061104030b0324031903603118a00355400003032030f015000701c1c2605864503481d15941020104004c1a07181010342503c0303840d8414011207030a018008005031040e80c1c8580d9100c44624008180c100c800e008010504480380c0380c11 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 997798120 1250 997796870 997796873
    0x9010e07050a020a02060c0a0b132f042a0c030e190504022a1501030308071809020306010e0d02090606030601020a0506010b030415050709031407030f11010206070912 73
    0x64002c2d0005095910446121841d15800308040d50410b8041030342d280e0040c1320442c10070541d50300e040ea01107020008481d0100940d01c0e4103403004c1d0220403415107540c089100300381c030b101c8a00c2080d42011020300700340300701e0340c10704034500945954a22251a002e01c0d0200d4019191240f40140710450b0103940704110068000c0401201c40c03040ea00c050083c2881030303800030300d030340f9540082c00303403034552451900311100100350141038001035140a50054000710210100126001e0010741903a80514040c1801e5480701c02c00d4504015001803100c0480e5110400640b8036401d40003588101000e99411069500e0f05044c0a9150440350000303500000000c0040c00c1c50038280c01950344003030148100d403800380c8203481e203904000c404e80180c480544000104414044a150a404001c0003031604020078504650300502c3c1000c0382c0401044030b501040300d0965020100480e01c09582c00070b0102d002003809181c00380c03c0d019440743c400d0240c015031002071110b902445114048602240b000c0e00d00b21000d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 997799370 1250 997798120 997798127
    0x30f112e0c2f01050910140c0d050a0207060207060606090f0b03010b030702010b210c010c0302061501050d1103180109081603021e10060b0406020703020609030c06120406050609010e07 81
    0x25800c8207060388008840c0140b0001c0240550b60040100354098501c0b045445ca00d6800c1e508030042e0700c49481c52030018070001942c0041259007481d012200002d45440340102400603200b00300307014081074004101d00081c0201c1c0c1d48590225280c41d12114015682d41d0044d009049442c4038884c00c4070418001048000d046100440d8840d400b440001040560741c0b00081e00d507246e00310390382040c000c13105096880300400c00c00c41d0411030f02401c002c200c03020f0740d68009680d070a000b0007128006241b104640010b9014205545000191072703c14030000b0107020303010026410031900c0712010f6440a05810084406100785440d15800c203160602c4d0005100100c222980b240d4021411440307441d20703410b01d441525000c4410390705500d02400005501c42c980105854031a00100d0300d007042000700b0090242c0010b202c80c201c030360540c3c0d10703625144100d00080c10500007204a90300444002644d40c038050039284031500c90342c0b060b101002035880b008103204040400f40034141c071441481d800f0400a030302 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 997800620 1250 997799370 997799417
    0xa1b1103161b181103040f020d170d0b090c07050703021c02101e09080606100306090204062001020f120c13320607030f112e0c 56
    0x24035100542402c90000c0040c68072076507030242c64402050140990000c60f54040c11401842c0f0351140c0381142066140e040003600310110003442050244071000404c450131140700c05415800803559250840010070102505207820158401c1c160000000e400c0201d00058401a41c2c01c1001403075024115801c0c8001e4608041410050604030140880141d58140556880440b10790b100100b5154050007050302140d01001d4005001049009108440000070030551180c4120348400d82c1491280b001da0040c0040d0b04400112400040c0204034103801541c0120724240c40c0030303ca01c0b00c071110701c80a4201d001e6500280301411080100108003421503005c0b43e000000044101d00c0c0960000c2c424204254561200c0006000078254011250107044142d43c1221203600d82d4094440140c0059664400c4150050910850f442150105482507008a18404020080f00e0145450020710900c000000a402502c0350070007441480030071040c0030740080400c85440b2001150803444803643d4090 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 997801870 1250 997800620 997800623
    0x1403160e12010e03070b130b1b0c1005010806010b03100506030c040801230c1c05040c0f0b03060a1409150114040603021803120a08040203010b090a1b110316 69
    0x1c01001c003442000e000b03120382560354041800445c0d90350950b1401c411905c00c0106107020100042040343c0c08500f0b8040b2155215010241c0030141c0b50b004603200e80385008400d0806014401c10400b1407003480d0a5220380e0684090104940580c0c0e40c80300c000010b4842220226000c50b6007103410030507802c2a00165821600e074100c010304080d1100c41c006e00310f1b0340c2e010700020206c036444943c0e442104008026900078200402440c03800e800d40d0484401000c0c1d0051042031150364000003170901080b12250809803d00b0011030044c55501c601d403900941068410a1003444030701170004540810010341c040f5004040d011540a655031003401c04d800801b40c1080b418401341e40d514a440c910390000500180c810f90310f005031102d00b101e1200c02860208000b0a01950214583e402103000c2d070015580010286c4c40d00302c2c0c1958032840400d0240c200f0302c842580022484c404d1000b0f4444940014007a0307000ca0071800c1a103001807000b15480005900c4800060700100541280d5011402e10310403070343e = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 997803120 1250 997801870 997801879
    0x4060f020c100201020d2405010e1201050f070f0c12050702040e060709140a30122c010e1e090a0b010210020306150c1f0506011403160e 60
    0x80503820007160000b03200e8890a40140d600180c41580170a0500c95803100c2e00020030424114040c082d42211840c109014017414400f10b440c44080f5039560f41440014403016a000344003505082c007001543c0c0405860102c0425004184440240c6c40344000009498008410441400305040152145d62002005980150b152001090300c00307001c10801b40506001d507030b4040c580d031402408822442981c0041481070807083d000700085016500401d030801c1d220221040c03030385a0505415240c0c0540c2c00001c0c52201c540c405404519000f00a40810104801c00c451034400c800407040481d070701c0340b0141801300c0c01d1202190110300344040e0903400c0100c480341c2044042c150000141b2091822501130414035200e83c2d00b1040c035641070020030030f1155054010343c1141010000204e084194a000704026000414503a110b0202040321440c1000c042c0d403100f0045840318a03040c003170001162082d000c1600790043c865200d04274400c891003184000b540b0700105050100480d100d404510009074070 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 997804370 1250 997803120 997803133
    0xa0210051303110a05180708090f06070f080906040b041410110a020706180506091c030909060501020c01051b0c06120a050601030b010509040e030d180b010b0a020304060f02 76
    0x400d006051084003450041601260000d209000c04ca081c5082d6003080e030040c299915040c224592143c4280c6e041061403d04000541ea4030040620b01040032092548921488048c004015049040803282410594850740c1c180d841400c82c40c1e075610706070350043c9078941150008010841d01ca42d421000c6c180e25055920310700080701500c095801e124161100742030002443c2c041c1c80c1d01000040010043c40c1040300c138481e404d1240c041039030040c2c821781d401031000040a0b252540e030140c4800c2030180c10154004d1200d41400c005010346440d00491125500d03040001c2007560000900d038216520581d40c40d85064643e102505440c1c0404000361310314410380c000d801c03880d51841c0140000e5180400e801c403503403801d03890070800e4450242115062600d4400180c0c1e41d0791703228007201c10004e01560041011100c00d104a451442031580103801617103030143c0700ba040b0502c00f506078800c60040f405034419903258100c4162034800d404213175015903c10001002486d0081802c0145060180145c550 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 997805620 1250 997804370 997804387
    0xf020d030903120c0215090c0a03030c0201020321040201030b03010b0f01031a030a03021b09071205090f160e090304050f090a180303020a0f02070e01090b060d0c081909050a021005 79
    0x90b20f0079400c613140544c001505a0070244504d2031040d078416840c00090004d0307900301c4003152540c0781d20300024042001e07100c090b4055900030000c4600c1605102d50f03921387c90742103503400b1848010950307040340040d0500450040c1403a0500403005041c0340100000300e15198800158001c2442490300c5045605a10006286540602030100c8541c026009040d08214580040700320b0900e229105104030b840c10f060003895640828410410940445d000807242c4485900900e0412415480e5002c0d10461410302c4241d03800001d49001c44083d210001c105443d05d46c3d003039449028901406400000c0058102028501604620b82161911000040a904400c002842020b07a90000d5011a80000e84030611a50081c204501030314180301a040242c1003407074005c40085c0620441c5101e80d180c00c01304181d9510034040710a01401c40c10704003c0300b00d41c0300000e031451408844194407034140c41c0c211201d02c00980925080f095004000c0d0001051542c04c2110303040d590b00301141000401d1040301e8 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 997806870 1250 997805620 997805657
    0x20406080303090601030c0e0f0604111e0a020708060c070f0c031502090a06051812010e19030314011d07270302040f2a050c060f0708070f020d030903 66
    0x500681c4020f0290007158114102031840000c0380c1d005d014107050380400c120f0201c8803251256004401190049002408640740c0790803030289845440800c0d4000300c030b0b2090500300d08002c10f50b80b80581c084d1095070366030745483c039181c0004545030800311104020700b600081101014241c010322508c3d140005540360b40710081110000714001c205640d00003064200c51508c003d02100800d01071505a1030a60802d81c0901441110030011340134086030044103014905c203420203074040c41c50904542d400509002480c0a214403500d090300440e10f0406122120500342c00031070f0586601c0200305000f240c1c00501c1c2c400b190310040082040000f405022a41200032064040c90007a10640c2d111040c0e056004110450b10060400c0d80440e00c1c01c080106501c182d10452000c0c0251030340c482c4040d90360b0b00001d40d1903101d040e030106420301620040020012100303035014040c81084d520610b0719900ca210983d1700301c000d5012200035034040c0818600e218400d1f040854240c1c800d01d00404070542130701c0c1c002d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 997808120 1250 997806870 997806877
    0x6011e080313210210080406180308061009120b040c0e0c0d051f0b0d0b030102030708041202060606070602090103110a0c051902090f070302070203191401060b030a02070204060803 79
    0x10000c5030039a0b031040243d0000311180c5442c03603950b070108580050903039000615456210001605000690000500340a150790140000c28a0700d2040f061001003441e0060891004035165840703424041104591240b2480c602401d43d403a007140a00c0500a54451800001c4000c001b00c514541800c00811054604090b040c010680301c4001510399290101d000d042c1e0300c00800030a010600003040e0105070041182840c1282d80108030207a40b040078415450190048202ca150558000010300017000d501004041c4103034000c504418038070303c00400032030b2920750545803564000c01c00d0140c0360105080d503000b00f0641405050020743c4c41c92900c420700450300302d20111408500228104400d01c1418070412101c401000480c0c14501d00d00c2d80000ca4142c07014020380d1310501c240000800550007a41191940c603001800c907101d514079800f00d0444024070701c0381107801c04190225004104414002d0b50140c540c3d5840480c00c540c0d94050a00c000e4100718000d0f03134000d031141b1b00050b1009041c40123 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 997809370 1250 997808120 997808137
    0x3060d140304031a0a050a0b010509061c06030809121b01080a0b03150118050606040902030903071e0309080d121e050c19110706050d110c072606011e0803 68
    0x1000824501172400c20b045500060010690a00f4102410541e80c3d20504442015004842c840d03100d00710b020700200b03814507429418080500e42017020040c8100000a000620021a4025491818114056110000504240000c00c8100d040c900e8546c0621010396028a040748002003104c60740c0002490303d08151101115110781c0001440700c2060440303000d40c1f90345965014062400c04001040d86442140b02c0e00849650200c00b0801001c4184211812075030005020980e0038400315000c08942c03e030402c1200807411540c0001120307407001c200b84038103661a4a501c40003a01e10841c0e10043c01c25000028201c00c2d00201740c41d4100e01c035104460241c4000300e40c5544a04440466000040c0c2550002062102c0049594041c5e04c00145070750550f0341e1858201e0300c3c0c51b25503185001070604441143c0601d900451030307000b285230008080003203a59030307040c1c0c0404244440111140b40381c1040b80001d250031220050181c0c0114600b5044010700c2da440d420350042c0e03189281030279900716401 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 997810620 1250 997809370 997809413
    0x30c070605041211190f0507051f0801300c090c05030a230a1e09110114130b0f0c060108070806010806072a02031006090509010203060d14030403 64
    0x203168070413a807090115400042d084020000e1140b0540070849400880c2c0d00245070185805400303003040750602603200140750142035080f80108c840c03040700820600c0301c03414002540c440000510042c100e462540070040540c0c0c2800299040340d0081304180e00d00b80c4c1503509480103040054007a8482c40307800b0880792150b54140d03c07410074039902d01c00c1d648051000c0c8030303812800c0305a10301d2084c601605600403444880000302040e011400c0e40502180510403806d851801c0140020f00400742d921a02451003640d50802d0a0031780300d6031843c40d0140894540c80282507000c144290141d150040c204070784e030007403640c0c10440550f2240d460b040003600082c4003604000c604014118081104601500c5018050800b92400d40b4000f0007542d010b0031911500d03016219005040b40d444040c0069540d0040c05442ca00740740c18080d00d0103403101e07200d1140801c0c82c041c0050001306061080c0d038000c010090142420b00c065484503403c4546004080801d030004110002c00034414041100c0340c1d20024a = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 997811870 1250 997810620 997810643
    0xd0b1302040806060d05030f0d1b03021c06080705010f0504030b01032603060906091510030c022b0c1a010801050a0b0111120d09050118110a06080606030c07060504 72
    0x9a41c2400c1016020720b000e1044c45c3d2014000032004410798103c8480c8800381c94a900540822001512184010b00c1848000c100102c14a580c5a00100140214031401c0b50346401c1c06c80148048802910032500c494102c030790300303101c00d44c0f040c400740e1244191840c0c80e40c2890b40ba51510b440c072210130707401100d0314080c580d000101c1d05007454544030104c0c0400070080c114940280400c0400500400c55841983d0000015035124107010f180040100c002c2d01c3e06072080300c040ca015000f8040f079200e00000d481001039000e0000e052030f10b50315041c010102d407409000720741841558040e100d0031040720900c0514036059a020100c00003070703000744040c20001c00c050418a20000488101e500d4090404c180007c01c5c10b60b619000400203e0080058540b81e80c0e01c080381075000061121040040555003001a0003030b51010b050819a282c500078407048100d403208008000d4490301600c14040455038080006921349072000c050b42c0e011101c660f20b2450101c0d00d41c2c58a04403413046800301e89142800 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 997813120 1250 997811870 997811879
    0x23030f1b0306043201092303071709040e0a0c1509050d030809120403110a09050f13050a1202060403080c18060945010605030406020d0b130204 63
    0x440100a504001d9000d4406410280c5a4007203c4180301c1c4201a0100ea16141c0100040b07030031340351032421015000030800d01c403180c0b40c07080307110b40c000702854404500446c00043c2e078031021040741c46a65100600c200201580001410b0540004211a51055903408400400502401f103200b006219100e1010124180354913150298000e224080400069a40500007511107120b4141c801c2c0c3c01d418150740e2540c032880c0341c034900402c845480750300103c0420b0010401a1024119440000480300c8001c403946588950381101d1040f64802c0d607024008021681f004640c00c000c040b101e001d40256401202261901d9034440c20b1640064010390060f0100024150701c84103494205007600f60745450912118801c40c0780c00c8c2003000080c454440011042510340d03642103e901520300d84c09240c003407407404c501074103514904801d401e009081421190030f240c01c1e03005000c0341030b0342c0b041e201c850458503039490301c000075003201510084c804c0c0d4070003407045150780786002165904450f210140ea0f45040 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 997814370 1250 997813120 997813153
    0x307030c02010203070e0d050c0a0f05030730110a0f0504051008250e07170a020c280b0a0507020d030623030a0b0c180f090123030f 58
    0x180c28000c41103900c14010321001c5544849040e05140c006ca808409100346810490b00b03141300460900d51140e0304030300025212521101c40822294101d05035818130f903480140702c6138030200c1141003046408002e05840c2040d0718a61100d0742c6400740b40c42e0354a070640c12003c5559800d450704842480c0030940410403040c60305000f4140d1103900d1030a030410141ca4609055a900d10b04500100c402c1c0c0300040c20098050001400784c000c2c1442e4403244801d06000c4409070107040192182980c034000e1b440060040b1010340210f59411455a0040014044801d2600414007a034034250041d07038400c0003c03c1c081900c05000314015440700d200040c1c28100404064900300d54214081e05050a0100801c01a440c40304a1961891174110070032030b1284d80d000080c201942100c00607d061409000d10000d10940c602130085819050040c1b20000c02c1071042102040108001e0340d4071082c481c00600c18038112804122402c4200c00304039241000640000781000303030549816880c1e41c008503000003200d08 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 997815620 1250 997814370 997814381
    0xa0902040b0f01140927010302010f1103030408030c22170706050d0906060b070807020f04050c0702041517060f0c030609072109030c141b04052208030703 68
    0x101110b002c8100c012075000a0a0013a00c0c1042d0b2481e01c03808598500c5070707100c071000101c1001100303040c005284d01d0507015080b03a240071b010680c00942d5204000b030794140a0300000c0085803840b401542155038980d9501402d52005020840e0b0703040c1803100304030f05411600b00c00400c082070110048070b07500b01741c805000d400c40a80d510400d5440780c601001a02e4019044036007a0480c25000305180c041030074030b14040d046a6010960054000880c101030104840c00380460b14800c84000314038182c500704100540700c003074031400750681e0100248001880c0c10751111882c506c80d43c00b05240c0300c0d81d03040312419403000316020f04a150000801c02042e20b02a03000c641c6d0220103140c00c10b085007840350119420410041080042c4640d5010044031200311415024400759a90418055100c076441d000b001448031481c110b03015414074004941c8080d012801122500d0b402003481707056000d9404020240c00050b10002c0c814031004070701c00043d1494200f02014900036007107140ea0303040c8000001d04030f40 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 997816870 1250 997815620 997815641
    0x40e090109060207080c2514030f070312030507022e0906020f0702130e120d061a0a020f06160e04090804060206061f080a020c100f0b0a081207020907050c060a090204 73
    0x4141102c4a41d00180761095001501c230300644e820a801d859401180c544412803544501d1885120000800c0141c0025030414803182950144484e480350a4281d03540c04c544440e0300b078480c0c2c90000d14890054581d411603050304c40d58134085800062074440c274040768041c440505401000048c10340544c00d003038a9000e400305101404200165001e0041511038102d212103018820000607072105034102c6403c00c4001d4441c51141490b00f80c201040c00101c0da0000380603c001d4001e500035604090004101c25200e6040f004500410300466202250b000f280c4090a580c0555240d003164003041078000a04040c15a0703800820280c01d101d020000655200300800f2000c4060040840c1400c0d4400c003030a8004005040260f114444151100d080c04503500c1007140d0140b805e0681d241c4990b09030000c0100d034209a030b42c1c00020f91140681078945414802151340b2503810404034005042426801358801024580241020440075040d42041c605480c3c3d20856034851000d5070640c40c0c14424a201701 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 997818120 1250 997816870 997816903
    0xf0e01060b070b0f190501080106030c05040213050112200405010801080303150402090111060f010302090108120304020d2406140f01081501031805250b040e090109060207080c 77
    0x1e41a59950070100c43c01001402c0d2101d8110115801040c90190400c160021407403e005940e1986c0c100c0e4000c2c06244815a5007501040300041c050a061003154402245442c900e00c842c0c0c10440196003440140200c0444107903202402140b003004921154002016003101e60b81c0c5500d4140011b0240c2d1046e00490403580080060100700302036a42c2d602817040d400d440250300c2d0042000103843d26070403602c440040b40503083c100b1140300c0285a407503068a208032804031550340c80720341c2a903843c103103500c1c8050501d204101041c01340c40c100e400040c0282c40b035240c40e40001c03040000b0048886408505104454641009004000e031010f84510b010303400341d80760340c10342c02c44100003083c88101030603a1010800244d07079070034986d100b50000c5030441d440700380b5409107010a14040b6940d003042c0b90181c2a01c407200c8000c07020304c1500b800072000c81c0c0c0f0742c4c580181480e040062401c07040720050032600c02c0359070702c00301280003d9103400030308001d44c020285c154071000500200e90420b2001401c0c035249 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 997819370 1250 997818120 997818127
    0x1060f090b01090b120c0712020307050610060e060c0a08120415020a050d0f0623130e0a0201050c032a0d0f0915021f0506010f020703050d05090d02040f0e01060b 71
    0x140c4c0341003019240404100d000c11280fa4a071014070700a58410004050216401024005002c40c3c00100400c00c0602c944122a03c540da07645041d1018203203070048000284603000310a015181035806071a40040c04c4080d00c000f440c1d10742e9400615486203c5078441d50300760000300b2050061405240e020b4100c010000d510702000c2044c0100240709040105040ca6612621040b200000313510900103404031850019a201080c142c0f4080d0b100c160168a120f581d41d000e0022a5139140c0c080c2c1e0000000200c01030000e6081a40155149e03080f6031020641e40c03105001c5101540d03c0030900441c03544001c60592140140c171100f040c06c01410f04000070911103841200c15045501260181c1152200401a1190305d4040c60880c01c09202411184500d40b00c0413031a00c0041c007503800140207890980310752030004404071060b6169001840f01600c5900722032038805030180102e000f48042040200501811103041d400242203940722103085540550760b000c010340060007480381c88045c1c02007080c1c1604 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 997820620 1250 997819370 997819379
    0x6070302030f0714091002011e0209130236152704240906060c0809040203100b160605060604030c030210180e1b09010f2001060f090b0109 61
    0x660040a0624010030044d4075500585407000010341d10700c035100815464459110850082c060702d1180801d14030207110f01d1400c6003206151080f0361000c200908418090b5212607900e400070342002c0440e684980c142c0c09843d0001c09000c190400c141c41072140c1c1c40c13068900d00103200a1070015215610404000c02601c49a000ba0368521221603910b401c4c12109040170f0b20114028004002c034001060045880c000340071180171134000252104c02000b042400d550b2501260342d0600a200a0000b2404101540c51414550000e550040d8407a1079121129950303281c0c4215607000e0300450000695840d60381007001054000c42d50003060440e0181d04040c00c40c1c42c0c9060503207051000a20901107096400b010038042c440f0000c41031480403007070504580d14003034103096200454215640700908252020301c101c47e80c040e00e02c801010707500c81040c104442415160740b5103001e0340000c0021400030800007040c1c240107031005000d04500401c0f8991030003480350261140e04000d02d0500c081d6800600 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 997821870 1250 997820620 997820641
    0x2040608040f02030f01060b0903150424060b0703050c100608030f250c1701020a2a05011a040e12031f0503070e0106080f090304060e2209050607030203 67
    0x68215401041402c28403050f8400a840c184040700300400035400c0000004100d0f4800c005090306801c150191800c200d15103225080380c3e40d040310000d090b1034010b4200d018070700120200d1003400c0303009040050302c42d07260003002c0740640102e0000c80008400041003803da85040c084021108078000381400f8003421f0000081e10703801896010340c1480c0340801e0001241c48000724502e950329440038040311100c070a00b09a100c5010718014005400b4040d610402c01c018140f080fa59a0891941e40c0c00c880309070400c0c5489104000032412506901040d40034000c200203102e150455078401a442c1200c895440a000c10380c0d0402c15810345039005180107107102000c10307040325400a0a4011701c03814aa40790948100c040c0160405501442840404101038405107181c605030703141307601e81c068650303508000c0b80350200c1e048400900c95041808100b0855000b60a0800c0c000f00082039140500700e00721070751007920f00103115000281c1d220050f10061180034800e0a400c01614074082d45145800c910304d8 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 997823120 1250 997821870 997821887
    0x3070303081609031a161b08093d030203091203040218040b0103031202070c0302090712140105120604120e060c0a0b0a110c21070c090c12020406 64
    0x341c045500c0403181c190384601c10000300010315800700034003084140c485400b1702204003c6903a0150052401d503465044c0307000303440700743d020800100100401903080c1d4404a04d034101301300081e0401d18002000503e40d8a07403c800340c03130a020065051021450301480c4004c1d40046940e00c0c14180b040051002503040411008540c00c1c48000603942c984461002c02c201c03036030002000d00c40c003402c007003030200b007003d612581e9040300d0280d541c0000c00003594946030228840c1c100c00502046c01c1e00e07030802c01420140c1800740d00c00100e080a03200650003031214416210f070900c915900301c0294006000a29202030030001e2880f0b40c4004140c24541603540c2001c0c4801e9091210602805040e20941c590354581190707402c0008000343c4007580740e10310f000c001c10307001030f540343c0d540c01c0c03c0452125400048000f99840c00d10340c0c1c070041046201c11683c0c1d250740b0703d41030940d2201610400c10320001c0f030305002c000f60051280a200041d00300401d0b1000300380310042c2c414008101d004020406c90340780d014211 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 997824370 1250 997823120 997823131
    0x60105091008030a0804050c120c10020709020a030b030d1b0b0c16060c0806060a0f050903010f0c0909060b040302130b041506030902010810081c020c03070e150307030308 75
    0x20034054072204900305000c0c405620540c01c9200000b4512211035110010318007a40c031035021102a0b10385102080f2990010121642c85988041c950402c0c61034120300c0307041075200c2401030f90001a140d020440036680178481a0010a80b14881900c2c1c6040c03c001e01804142d880c50704149544003010003c513160b10000780508841d803c81c1c08103a0009800c0b0032146000041010301d84641a94030b4002e0142003140305280220712040c00060790703403c0c5030303088071040200c540d20800c01186429041d07541e5007050198075095941d410344644881c142d0b03c92030414280740e4860700c1032603142400c03a000f40e421a03001135013038400c144400c00050321084c0c8043c00982d0300c001c010440e200b03040042401480b10880b4500d040741c60703050020b24140c141c0d1280508a0003030b40c0344010f0307560386000c1c5142c4401c0f910414200354000440a11a100800b50880803103203184151004203814000003454074103c1d4005481e1403180d102407160480c0d48503048502d140064003d0011145035031030180003080c00900 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 997825620 1250 997824370 997824379
    0x7090513030f120929060108130614040605040c080c060f0a05160605070207090207020609040c020304080102041d070f120218030a0c090509030301080a1e060e01150f0305060105 78
    0x803545601030103042003d0b0b06406402c410403404060341410000d60b240140182100740300540c504049500364480e052042c9010385500f1060345134420325290945c00158252070860b0341e500280041c013111100140100d0007000082118106070409030350b020019408515168064900440d8a485810036035804030112040107480705080e12081d14180310b688080c010f1a2407800d045010414a075000d60f0094109500322079000c0c1e00d40440c40100d10910f140a540903105201c00521890282c02503801d44000c0d206a90a240d500c1d804142a038000c0c3c1c01c5500824940128a0811031029082680c4450589065400c283c11201d000d415000850f41c0d1210003900040c40c2c0c005a01c1c1007092076610800139003201d00c107070090308104107880e07014096007001c28240300c0480c0c41c0b230b200001501e0503a5003107809020a800b880e80d070811404401e107a9410010803401d0300c64040f8610348207060500441d5000820b54010105e03004c10040501e8000c4076030704610780c1007480461000503095040d140d040e039 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 997826870 1250 997825620 997825637
    0x20103020d0b1903060b06070209012918030d08070c2307171002090a061b08030412080106180e06060d11120604050103080a0509040b0a060e030709051303 68
    0x7980140605540c09a95030818a012400d00030080c021440743e0460780500000c00103d155042002118494204040d41c00710f10740d001485207a515800c100070f040c1c52444240e003010300740944a1f0594102407a5004c5908100116407014141403020109020141c1703840107140c50039050143c105d00c860300000d00013540e0300c4c0f9114003810110b580702c200b21318420105c600c6113a0340d0000301000c2c801c1d400c80d10003900a41c003401c000c221241c02501c4524800400800000d4100002154010003ca28002c0c5c40d2400c07800d41408504060020350042e4040d04140701c0760301c548400a44a042e060b0300087c00c02107131260740031151910600c00012b0f990010f502020b06e4454a000620f076010b9104124129854440c4501600200f41c0081403590f2010069004c0765860404103c219407003444040c03d0300008100d255003103071051006081e2800000d100117445201c0d00d0118030245c44070340029010801d80811aa034500d03040104500400210394280010301d02070408480d01205030780010148031501d07 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 997828120 1250 997826870 997826887
    0x30408070f080c0a0c080f2a0913020108132a0b0c0f0d11150604020c060a0c27050f150316031d070e09010624092102010302 55
    0x700884481650420080d0307403103580401c0e60a0301c903818180200c0e511110110000b440140128850001041000c09403003129400744403410203942604607141c0e483c14146001210740d45010703800340110348940e03000c04442aa072002418215001c0e2680450a110383e16507400981c07184101440d001d10540407010070032b031500442296481a407c0918003181c0441c9000d41d054001844040da160007600315a4840303083d003826107052034103408d800d01707a0300900f10070009150b240049a4010701e001d000145400c1039401c4190414005076000703a2916250002d043c0310341d50140c01d00908000846e045158407500f0107405100100c3c0b0b11516005e9141040e8001c2c081d604c030320b810340d95451001c41055492400001050301044154041808223192421080c8200c00c0f00c4540042410080b0050800d941414800400a9030007840e82d4032a6484210210703101c4194007445a4120420b84225102011a62301274a01040354001c500f0f485003900d543d4040402d822403512207030b502800c00690b510360a = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 997829370 1250 997828120 997828133
    0x1d0a240e010f05090705220b06040503010f0b040609020f09121e25030b0f0c1b07030606050d150906020d0c0c060f0203060f15120c130b040b03040807 66
    0xc2a54140855180000980d00c02d41550040e0740704808030001e071645152100b041140c041c1c035400079800010700980300c11a00740d8481e070140c0c44a55000b00f0403405d15070784200003400c2d83e40010060038000d40303c402c00400c60400b409450042d000c8244190705020390542582420b00900920300d20480400c0e5110780e501c0c02c2800712060302070f10b015841c004402d1680e1050354a080ca500705500090b05c44242d20922545440f0f540c041d250b004021843c2e580b1036007101050340c9000360444031700c0d2404100c03a43e0355007507041d840d480d0030003000007501030300e071640c01c150046581030341c0042e010780f0083c0c06840004031001d603603d850140310a000501e4400f64140840240903d0149618880c40c104104c4812900444001d0001d44550010300c02c822b41d104241090b40015101d55800c4500241000510325101310080005200c100c2c806040070320800b030303542010380c0940b040c0e1012080014104484141299020003070f080484465140c20b26180a402141c40003d0003d084401c021a91030100003e = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 997830620 1250 997829370 997829381
    0x3201f1103010807060e0616112805031212010506030703060503160e0601182705151e01020c0f19080c010207061803081b0307061d0a24 60
    0xd140c90481d880c0e60b11000a655076416a000700004140400f007070410b5450124200c03000300904070240c20500d006603495580605070314031000d902c620240288040c181c00c0c0c42c800500c3c14100303401e02d1000703403411050604102138102c00004a44040020042c10448060074a0464100750b48040d940d984941c0203c00601e016005142d0500803201c2000c003049a030118030041d14440b02d480340302a100e40e00152903074200d6161321240010107880801c0202c42e800000100e000b406400358844081d00c8134020203e40c01100d4004005240350690b42450030420034416002d41401c103070850180300c050010356503422044c40b0a01c5003602011161b50f5403184040d04003001c141e10307d0103076402d44451f451500e42e114184520b0040c400d0400c001040c42c40b03000310303080210782c0e40c40c5c030b17022607085460f125400c0d4821101c0700c1081045451100600300d0070001800303003e018550001c0d0800e41e060000121201c2184440344a5001c00d507010003141c5d00d448080c0d105070448041c066030160f500c00f000060207 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 997831870 1250 997830620 997830641
    0x408090105160b01050f0904050a022101150f0b0720040906020703090311060f041401030605121005010e0702100914100501030606150c0803220303020703201f 70
    0x1210395070b04400300015440d180d13050b00d80c03c45889084100c240e082c0074030240c1c1150003400c194840f680840c058180b50480810100300780ca20f14115070b10100c1c8850039511041180c8240c2602082c0800040700e03040118800342a403840100d00c1e0101075290501007442e540704c2400d40c44401c80e205c1c5190b559591201c0c43d00c6600640c1551149050b090150881c1c1513444262501c0340501e00c180c4e910715180307044172416101ca560b584d04050410413400c4e45005070145180c14541d4a10001c1110350318504901d0700c0c440d00070000c1441009108042040c2d8106a100c0c11100150700e081c80034a41c2c02041d03e55103c44402d10006209580342810440d80101c3c079a14a000d004883c4004100801e5400841c16240200024440e9039035031201450724a00d500400390009500103c1980061034040003181c0107241d010003400c141c202e030350040c0c42d01135001c0740031008070344c0c0001d00d0420141c006407210300c85035064182405d000a075040450701c17000c1c074200c4041f109081d0310a00194106580c000740256 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 997833120 1250 997831870 997831897
    0x30c040c09090b010c1208060f030705130b040608030c060412030507210f020f0901090b03090d320714010903320301270204270902191d040b0408090105 67
    0x10307400310018201c0e800640740c0c80c9c028910350481720b403d410300140e1441251000b81c800b0b658078042007504d100400b40a409194400c2c0c89103000078241c4010005040e079010741034080c10441c1480e1a000444c1b481d00110f441c141801c040c20044c140e03412101080401d60310159003040915801e5001c8024100d01d03680040303a52020402d104e004824202824502c5800c3e01d410b140e08c0c0d21404510300c43e0000702d87d4568151310050760250000c0c4207529803485862500c1e5404d04800940c4007100410b1922410a80b4580001c0360b072100f440049400903a4141414001300700004030b90300c1c010300b001e580590745800c06080c410364810011440e202500950215082203449584491022100c06140780001c3c0c01c0d1a858900000859030310300c03c0340d0445000038801c060b8119210419040c83c0380366407040214603543c90f0400c01507180c00400c440c3d0200601a40c807501401c1810f442d450705920384200f40b02840840c00c210020f030307580f06074680054201e140b041e100d44130140100c2e0b9a114051251412 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 997834370 1250 997833120 997833143
    0x1050424060f02071712070c090207080711060304050a030e060c0109110a1532120a1116300305010602100207050d0c05012009030c040c09090b010c 65
    0x40703552101604074422683d9082d94451542c588514510800241140109030001402030040c3c548580051800610507980d08a00319a640c0314078040748c0100c0303000d540340c1c0c00c0007400350100840074207a8408880c0449050741035040a444140c3e955441e044014140720352003141d0441503032508181c0f5a0201c58100900c10a8132524145a441c20014100e6005a10b00d81010a02d80842034a0402800d0f2503500c06c8529200f842a09242e105261054200d802450054140c0400d1900c01401400c0b450342c0107003a10705103000340000f1034024401c0038034524401d00c80d19004ca4001407401e03942d290481000107140800095004401a8414070400303004107038a0045086030f0540c200302d040716059001c0d12200f15030311142c1e40591003440c42c01419500101c8002241501424a038401c0c40e020310000540c6000030350b4429425650701e02c80504c6203070085003008907450300308003503182442c080d01c040c00080020403001d0070b55466401008442600e800e078540316a4454020410200d8000da0600351 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 997835620 1250 997834370 997834379
    0xf042307030b0a0b0705060603010207030f05091302030f160216030201030f0f021204060b0d020105070b191814210a12020f0a03050f1006031104030f0506010f0608090601050424 78
    0x21399020344000c0b04c2d5070098800280c4c1c0c5213010f1007501d4010341c064840800440d170380602140c0070f50241c12503d601c0320700c01d20a0b240d0000342d40702652148050006440032410207007a42450240c605000ba021503101401d842d0ba140010780f003c0041b26428280070031500003824040c006400c0314230602c03c40c0c61001c01d06000e0312aa50101030b0003980038210402002c000a818018030716041c0c40040e011134810006000015103043d8025400340841b1118040803480c508000241c3c0c007107450071005c906144006005010f510000015254502030062180090f60038060000301a080c3c800d1130141400324002030007134000d25144909412200c01155110346000324112550440103021002a1808001498541000c2e40c0d940c02030a596000c10b16107803401004801404000b44207032480740d070600c40040056118003031354040600c50009413040d1344c10718000d14145141544601c080204032820310041c860041340361419681d007510082140e00c007662103c080f80485124081089620060004 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 997836870 1250 997835620 997835639
    0x81c2004180e030a120e010501081c1812030c08070b0a0516021005070e030609010f1404080418090b0a0b090604090305160c030b01060e0f042307030b0a 67
    0x1d0315100c040c01820203075440d44103400c84100c8007041106900c1003101c032415900400c0009414480c00b840418030614400b0f00509691003a803001d80f85070310924500e0f8040b880220300041e07500742494865458000010700b01c121003da841490780300306a464180d010301d0301c91160480c0b4150000072540d90303060b00c1c1c07070554425603045610380c0449280c28040b895004044600031008982580103100d0040c1c0e00b80400700a100140940c01801094502c1c0c101d50786040c451580704580700000003a4050084658006a4002c00c1003102071007445410400003c003e41c05440503543c164503592950030910300314000820541c0400342513840c6417810058101c80c240c2104400643c140d40c40501c5489100501040c3c501c800c0c002030204006000c50442c08880540303100034280103601000d11641c0e2501e40d03030440202a00030800003112400070341e4090800c10031241800d02c0940307007040365a1031340214242c4c2c1e0b0070380024200700c4051040031601c00b606c00d40040d240c2c400006e0198078031990f141e0008 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 997838120 1250 997836870 997836877
    0x2306030f031209070b03041208060a050411090306060d02030a0615050409052b0c1e0f05030a081005090115140d09050105010902070c121e060b03061003081c20 70
    0x210030501c200000403410000314410751f806a039002c40394042c005049002a600400c00401c915000021104001095035960080d140a00380303800c009a0b4503c0180c2c149804c00c60001d14181c01410201100307401a1800504100000d80102001542245111107104414040d520090307126041c2041c0070306024010460b00c01111956041c448010789840307400203e4100e4484c200003007580c00c150303440860244144202940e0481d84082c214030b0780e641c0c0b104514020107900f40ca1590010804884860f00100c03c990005955040e09604519000000740c82500502900240b1081ca40212140600440400803c26000d03465244c40c0c0105010300001802d000e90281c1c1c070b0303600b080000a00505603208541041d81c0000035101c11031f040c88400c05c5069100315044a001442e120007a1b54108040c3c603800d0103d20985001c154110b00900305031400c04041d0000024103503e4800700000cc8028080322900d0b030349002042509010324001ca0014124254104030b64a020301c100143c0c0702800004 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 997839370 1250 997838120 997838131
    0x60305070311030f0c010e011407020d0f1a0411460e0c1603140c030a0801091503120c050105040503090109060c0b0f04060209030d212306030f0312 65
    0xc58403d0a480101d07143d443c5c80710005540400c0c45054030005551140481c00103000410a41604e004203e07800316140c0f4585c034505841c22019090181c041051101c0318051620400550030201d041584604c0414654561a01d12401c500d0749007041640d20600804c003d01c50302e8002c21008060b288104c900c005800d01e00c0c00e2401e001d8400030501d4084100160302030f00040f00b88604129021798040f84615820805a06125203c0e0862090600420080004000c40c2d00a1900d4903440c09019201c0301060300040b81c92414a40803001e03031380c03103444c80d50100d070b411aa510702c660390040c0050ba24008004805010355003098104030500c00000010b141115084c1d030780010940e07840e10b04544800700100003d11708441440807410706680302c02720035049401803200520306605d101c00280303407018101078503010032401c280c0c40c1c8950100100800c00c00850384002c0c00100020000150342c05000c1c40d902c0301d0011201c01080054904000760503841001c60105d0355581c00303540000300e049004581 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 997840620 1250 997839370 997839373
    0x1b061501030c0c050705120c130903031b0e371401110a08090310060905060306010e011a2a070e0723030703090b2a0309031c06030507031103 62
    0x503524201c0d10a505500c1e1042d0850301170603045003403008120609460043c1034185104042c41e00304551780303080400c080041d12500004010a041c60054240c40007680f11211844a100a0007100354005a0039042800100d0b4000c002080c00b0510f90702041042001f81c149004a402d41b0120340a00c1c006581580d10880000c41010910401120301903060b40c4880050742000e6a110009110440502003002c0001c0c2502c00f070138018010358044594580c01120026190018401282400e0000d00c0c00b41421000b8104950f0604640d074034922815401e03071084400011300c28400410102d908124001c5201241301446002c01c05265140e00741e0151207041c403031480205200307a01555200c0701d41c00304600d50608516604d082d206031a0801400303003003071544400c00c2e5000151015600d0740304a80d07110400101c0d141050180064144c00c0b07040e003101c04402c206000c5011000001da51305507941c60030300f030340c170a01a01c200d0b0003400310380c0e1008200b03204645010007000008103002d480b410043c1d0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 997841726 1106 997840620 997840631
    0x307290d140703050a0b040b011409040207020d0804081203070f0309030e09190b060405094b13030e0108060a0b04151106010803030604021b06150103 66
    0x10342c02c40010740e0390000c0010340001482808000e02c0240c4082040858003400600381600030819401c150101050032a415a40c94040b140a1a0b01800290b1b000176140340c4800d0b250441d0003100520700074442071908029540c42900d1042c070065a540c04804842c5134150300401e032016040e01080103400b4440c01e2a151502c0880c000d114604800c0e04643c400c0c035401048803c8000102d2103151708010070806d03a41c0b124407403a001030411403a0352903420066180c14070380d188030840f001d0b040312542003800204105106a4110190708807000010355801c5040c42228070605402404039903a100920301952044a074507a2103200a8810310003603444145510990704194040a040c204c4110340804031540603034a103115022182c01003105506203c010741d1a4000200810300882e4049a09804180c00c2418890b80c0380400003500c1e014101032080c4803910b6400001c950100b0f0408 = true := by decide +kernel

theorem cover : BRFrame.Cov 997661870 997841726 := by
  have h0 := BRFrame.cov_init 997661870
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997661870 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 997661870 ≤ n) (h2 : n < 997841726) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
