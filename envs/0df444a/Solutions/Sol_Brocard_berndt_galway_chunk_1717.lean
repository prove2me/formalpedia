-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1717
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:24:59.968978+00:00
-- url     : https://prove2.me/submissions/1560a11a-e401-442a-a5be-587fa427e3ad

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 308633093 ≤ n < 308812949 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 308634343 1250 308633093 308633107
    0x309120f0c01110c010b09240307170313050d03020c0603070311160b0610050409090c05030a1a01090b0f1306080a060b1503070206162c0f03030a1202090402 69
    0xb801d4500d6011040c44001c1c01265042c00c0180a00031003c050205072410300551400003000510188401b0950084c019010300c030042507203090200c3d40c02781149036101c442c940450a41a99203510403001040365962101c03010070580b4284d0b511000e1241c1542c01803004606984c01c200303c6900180c40c0c00e045c19038079148014541c400380c02903c001142c4d00648511205941480c43c1108402000e0601c603070714046410005ca80c00c4019681030f0741c038082c4001620030003494620708400c0f0f540c00c000e9040c8100d2600d482003028458021280d121101e40000d41079030b840ea0300805441001c4401640300a02140d000640e05005050f10144d414091300802c840c2d903a0610103060540c802d2040c3d034800d4039800d405070541008404480c403440040e20451130b514215400030b440302c101400d80c40031003120030740145140740326a814551340301d600a2005e00300380c280c805103485241c801c195940200c001505141c51498040705452100f481900c50700307140c50b80440f0307000007903210071445035215509111760 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 308635593 1250 308634343 308634367
    0xc05030304172a070e0c1b01060302060c011505011b0305090f060f13120c030f0317090f060903040617091014010303030e010903050d15090e0706140309120f 69
    0x184001c20140e400c081680070b42e691000b0b0800c0d4041e081442002c2c3c0450506c0a1150f6100448014100e14a4821204404020103074050031081e400607602c00c2000c039aa4104440650219a1842c82503a011156030350765030040d551490140c50750398200c5650311701070020a007e80002e1504000042030036016030030381c40000d205a00a03000e81da112200110302c000301c0d2040c00146002a210f0328040b40e0308041190f44421059140340002006c43c100d007590002010701076800f00b69011040550ac201910b007060302a031351a205012400c042c2d120326004188014230100840c0c0c140c40443da00c18019035003803d140d900104000c0d1551025105006c0d10401450381c0340700d030803182c1411180020503945141070040c00d44170125100040e6900d0030300414000b030382041c03c0307179401308000c2c0303011600e0401844a0071118000b5403100d4225410402a040201c001080d0042610010786505c01003510404041041e0700046492540d19031200b482d034030b120f08500d4080c140b5185501d000d60300c2c0421019030 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 308636843 1250 308635593 308635627
    0x2012031611030c0a1a0912090f130b040b0f09010915030605010b03060103060506090d060b011211030609070f0225170d020705010309020a12210815010c0503030417 72
    0x1a05031150080811441004131503a08845c41000b01410440035061200344a81c03a0705005411b1844918001005007180d16101c0f0b00c1441034200070304100723140c2e40e40c01294014281000f0b080b03124516103c0300d40303030743d2070881c1000902c000007414100d03140c0e0034001900e004042203213203032004501400c400000500a401000d010b0302d03600700495140d050400015041d286550801032003003030207000b01d1095456099410b440320307810900119151001c00c0040e5294180f180c0b68a450780d040140b00c420b4039050b03e00a501869003a900b665080d6031f090400c0360a109034843c0b170740050f003121106a000f0180b5584911203031b041003030100d202c169143c0b080b01101041c0400000f4a400807054543c10f03075018826040144070a00b414004101954000345400300180181303d41801c1e14054081404200e64141070300d68645e600b03003001e424550001030b100400841c0c50550241108503000350b90f5100f0103d034102c00b54000019401c603282c640c0c41885058008402c036100101c12b00a420885100c410 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 308638093 1250 308636843 308636857
    0x708070609030b04030e120f1c02030a0e01050c07030b04050d0305040206041415220504200d060e010f1e03020d03030504030e040c0c02180705091e0a06201203161103 73
    0x1c010315600c8020050340b800c012270608031080c03180d0400301e024101a008411036007213580c2890005001c81203a40180c1d580d0246e4000520b9901c40c404000c01001810000640254007440c2144d21004403148102c007070b07800888000750040b0040c402000801e0708103046092945004100d04c0d03641e400300342400000e802c040d0f161819528050901c00081a05d40d42100c05000b09136811b000d1800294100c0f40103d00b85100d00101c4040040c008084908580c440c0c406841c0c0001c24a90950f03546280c0400c0824500070018a02031808501c0070000101e0b8156045940c050301440d5a4001504d041d070090030014001c0e010f024020581212641d1140f24982c04802940c8804a5041c0ca030300611020b1980d100c620303100e0908810034045825000b006544490108481403039034050102c2e81c0709031050002030210340200319500c01264590f00445015140d2049111903c10340141c02c0959a45d11030759400711101d00350800104100109003103496003440e50a040c03c90340d50000b00c00741031079584009 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 308639343 1250 308638093 308638129
    0x1011010603060218100806030c12070b0304050c0109092f070c270b0d0809010507150b040c03020306150306060909040f030206010608041e060b1e01020708070609030b04030e 76
    0x50020149020f00020520402c5c91500300d501b071601e40046560b4042c050b124501c200482c901c4690304035010012500030302006001d0b6500c03030800d0b01c3c0c0150360308400b01c07005005c1303070542c800482c40c50103500c07812425860104084010b0790600c440b0080e04244002c04201081040013603c0101d4a04d000a000a1030204044011041300301894020b0700101100c0389040c03828800341c2e084036500c030742d404801c1540103201d807956480303800e0040c2e55910074440000e02c0d1100075614a07aa68039660b01c40c25030002c00391002d011905a41904508a101c101c4e0300640c84054560400319492010b009507501003000313880e41c1e2a10200900168025404640440d8003c80c0700307400f10304155051100c14014074180c1000309860a00c0d91fa002c0b00b101c0321103140310301103081113255414048150061111084094441c1c1d0203902900fa030b650101e0440755030540584140c2000280c0b100000a49804a605030342c0c82c2403d20b81160344906047c440a4001e400b000283c00b001c00e9180da683e91302d0f90540e0401 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 308640593 1250 308639343 308639377
    0x3040905060d140606130e060c03061f030902010806090717060f0612041a040b01061103040e2a0f070609060e010501270516030e0f07080a0b130210110106030602 71
    0x50403c00844106e1420403503000c030b082521401140030002040f50b042a8483d01550f243e80e6aa4046404401010206031050101c50624070150703401d0703405080d00078000e0f81c80741c2c01981c0703410612290807802d441c0140046c410301d6a03101e48915504100e034011200802c000d0311000d070240000d40c1c0340c000c5c03030b0350074100b20f8020148001c2004641412010900604140d291031030305403110062420140304840a112681c984c0781c2d84001c060080350040e00201803110254200b41c0241000d103120910040424224003410700c1c41c41d1218001e952208002c00d800070328044817a59100060000328404a41d01e81e122001101003210030700810b4040d00c15400c800d0002d00714070f05680d82d00c44688038030f00780b128600006d04c00c19120780c1c19038420048a50401081d615018500d2078030303000380d0040d00c240c540a2004080f4203a007021541b0408035005210803e03040d120815840c030700c10040500207600c0b2040c007108551190050005a08c3d52107444000a240c1c1d5894031484d09a070b109003540d913042c90031 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 308641843 1250 308640593 308640601
    0xc08100e010b0603040b101a1803011413050708070905060316030b040b271e01111b0708060405010b1c020108061c050a06151703040905060d1406 64
    0x41031003900c000c24200c0000303200c070090500104030184005080134014508080004e201c55054100a400500c11798811065141c1a00c0402d0301d40d40105050740740788071104043c841c9600d414000c845640380601c2c42c607120b9850300000b40500840d115800c8400380216200064681c0c002c2c00000020311300c1d16404503c1b442d14408250401300b403c1e0f865600c90020300b20900c00b00c4d10402c1c403242e0103036004444039116110f0003040044080c020b00805144030090141d015505c0001c41e542c0b58400342c6a28841c440d4018000507420384201940c41da00c14282441445014040b5085900e0107089220646134010b8490580c242002c2d02254140d03032581d1504c000d603c4070304004604201c4c0304101282c0c0901c03484250700013091a80701902c0a48119802001c0e521820403050322429141d60050440b060a0058907005010b81080740c48142907083d4040c002030641d003000b20179401e11402c3d00c040c2d40750601f01039014006120107449150070408200b0042e0003d46004c3c14090300c401400018100c600d8 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 308643093 1250 308641843 308641873
    0x801060f08030301080705010806010e0603040c0e100b120a0207050601030309080d050f16020a05030a03030f18050d0c03020a0803071d010e031218180901111215010c0c08 75
    0x61650700c2040a5801000104031400002c40c490302543d50901c0c3c01c00264075200012507210100c1c80c00c05900c4100002800204400110303044122094880d1020103a0740e00024400540140d20501c40b00b4102040000042c02920800551204090400500700811522a1498160240c000302c0120f04008800d00ca041410025140300540a18000d850044050034201c028000d0b20346c810102400c245114086603900926240a03020203412100210380701c0c100207001e008031a802e100002d2410340f907605406100820450b5454102c2c000f03054000b1900d00486200e400e454040d001c5000d00038401c4000740f400d02c021405500f05a45e041080d048040c16850079003900301256060150035441c1c841546c4001ca8400e1030300206c40b4045440300c14074805540c0358004845042c7c0c3c03291078070069808a0f5299014a8007800340007000304403a0000e0242d5100d00d100343c071205001c118180c0d0004020900e840b081d141c0c1c031a0180343c404a43c800603510500c89200a804c80740ba41d4019050006c60380e0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 308644343 1250 308643093 308643119
    0xf0e0a150605010905060a090b0f041a0405060318010e011802030d181a09040207050d0f1404090f090203060f1503060f0703050c041d010e070314181501080106 70
    0x203016041100c00d182a0001c1c01c0c1c00290b105850007200b02040c94040305d40520701d020b004161421400d542e035031090081074403a912034000c40b4030f48403200c0c0750408401c400d1420b0390140c42000e44142c0c51600d80d04020481c034004071002c0700d001d40d02c82d0054070041c0c60a016000f0f80b00b0604003034540c50b04c0d00f403041508100c915025141001003c8141c41540750000301d0800803a4218803650a004207031641c00c881d2803082901c40c3d900203000040080800100090b208807003100ca0b40c600d5403111117408100d450017021240d400104070240010301554100d64803044060607141c00000d0410340550100707040c000110741400c04c036820402001240042030100341e890f54002c40113007205207010420740000340c9020380490300b0141e41c5c10010320300d10301706400c640284c40038002e50344200840329903d0b016248240140c0e00c0e02644540802c6125000740104441d40315569581101951403d040c0035088820b04c0e4a05510721403090441e00044003008024082c142c518004502c041c180b000c8a1540 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 308645593 1250 308644343 308644373
    0x305010b0712030b01030e1f060816210f1b0b040806041b120807050d030207020f011d1c0b1302060d1806050a0b010801050f0609040f0f0e0a 62
    0x20300d410801c0e10300040d080006801242c010b420300064121400004a004081c00c80c480c0340148141c40200ca040300c4c4070141e8415255849909003c860b86900b4038507240e0021030890074039402241e02c03d02283d1554244010400f503121505440d000b07983d20345504101d4000c00c19918000c1b017100d0f545408013640d601c1d401908800d40200e03d858501a40240d030b034840204041c010030109107501d4000820f40300c05400070000c4024030b0322241032504009110768400e400442d500c1c4526503030480c580340240261162160024010300c405030300b407401903a285030741d000110702d03d03840e08080d000595181600301c54042005001c0310258289480c00000c0740101801900308015003100d01c0300103a4a900850344030f100c5403400800c0800302c0c3c0c081c2d030802c0c00c1d00510081c603a50608003003000b000a594003580134110b0903610307081c007030760b03120240242c940002d8640307900610104400300240c186070b0400102118101e00c0001d0507020264400c046440c080701e040c1183e0440c0480302c05000d8203200800c22 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 308646843 1250 308645593 308645609
    0x1230180606010c1118070f020f06060109030210021018060e190f0311030f0d1506050a0509120d030c09170d11011b0e01020f010203010b0f0705071505040501030501 72
    0x60a00d41c0001c1c0c44240f0701e01000300b04101c1c004a408058843d00061403654103080100c081908111002418180c11041c00000610418404c50070318000050342d1030080e441a11802120740c00c5170248558080030260440a52180c0f42c02004a240207102c2d6038510030a0f002c44144582045c500403041e10713950780300c0c6504c0384e01c204085940d83d601100c140914640c081c0d44400210000e1409940b0707050014442c09440c000400c10701010352824008140201062104116255407400a4008070b8450301403600019014402010800e008400030701364204000c1000481070007070701c5841d18000034808414000798445146036a010f07000f40111340940f1400c1d21410044c08402415991461440c2803201000b10700c2103c80c80340c1c0740a61050305801d48031064086038003904e9101524007040303401c4550062242d452141d440e50010305c29031b810384040c05181480d0800f082c114508070741010b4801e0300e441c010700c0b10020743d8440004500d401d4070203079140d45455500d13010000d0101d031030590060394 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 308648093 1250 308646843 308646853
    0x5130801060e0a15030506010f1d1e1308190906080c1606180b040c0501020133170619060602030a0804060605060a0503061c05123018 59
    0x1e0580b40c1201168084024007000910805190508800c0f1600d5880502207000da072001103143c0084140113010341e6800c4825550702524015000ca1908048801000c84002c11901209510300c4000d000d030804000381d00c102c465038043d100c00c443c2307a00a00c0c0c0c0405009174403140f4003032b07281c00503044c800a2515060001d0180b030218051451441100c4030207500a66150034401005095070000b40140c0d02e4548100070140365150403500105c040d101590b15000100001440c0d6105006030034112500c07000800f00000c0300382c0ba0310060710210040024120084101203044000075070210030508a100c0140020304081e50001041d030002809044c0c2942408000c0c403a20f03030004102d864040c8039250401640e86ea0b4200500148102c3d0002617101a00060002105070b0242c0614003c43c1c0445010050601224a401120340c45401c000c00c03907004520590b400510100c080c0c5001c100c0100c03a100704d6040fa012504a00e001600d10b10703405001035091000300129407054203580302624009003 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 308649343 1250 308648093 308648099
    0x50108010c02030a0c15061502010b0a26010b030a03050d24031b091506020105010f03050a03052203121b0b1503010b090109020a1b020d030f0c120513080106 69
    0x1e4aa202c0c880780381043c0001e02c1703003c1042100388451101006c0303002104002e46031311001145401407801c44180e005600740112030005207400c40308001201e800240f60480e001081424001c00c84040d6504040c40d542d903440c08001d900d00f40000e503201d0b4884c2d07070355590321048013003000f04581d10440b00c0150592000c16140040740300c8458a000d80740c020301c507481c03a201191142001001290401400182802e40510140d6101c00c081c83c241d9100b60000d118903038a070025011900c0300c074440504107600c007508500100c0d0250005103003181c140c02d81c0720703102d12541c441d081c0d0605c005da0044a800300006003070240142d10018054116060001c0852188020740710005220360143c044080c10703900314600ca246075802d41c400902000090000580ca41c7d41d0044407000390070a0100d01c0108200b0002002030810310010b40409a60081131040481c039907460441e0a244440038107000e106042ca28440458407000b403c03600b0501699400307544000c01140880c503a043d03940000d0581e81042c0c424 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 308650593 1250 308649343 308649347
    0x2040c09150807050306010c050c0a0806010f060c0c090e1e03030403030e010e0601050108070e1906020607050c121c2f041a03040609121d06070b060f0f03030a03050a050108010c 78
    0x4030b1b0013417401d1900500082650401c20f0070402c41040ba2988078042443c0020070520100d03000c0c1c101c4407140d440200c1c090f0303a100141c80030550b81100906103480d02a0030702003410031341d00a000c0e00060340700715444d10074204840d95000c0e400c0d040d4100143d10100c00c00c001c05925000c1c1c90842c07803588002740000d0160141c8a40d0783c0d881809498184419407001504051090381d002040d400018032040b842100c460070144010b811f070140c2d078018040d00c2c00203400d050060003140c60301a404002010204049444105942c2007841c20064400d00c2ca14507480000b007501426480200640f290340b000c21181d80440303052441c5d410031803520002480204400c07070340c10302e441c0303030305018200c845036640da60745411801891010350042405009410101125a106814004841c0160138201e03115070048204003060103180c41c0200b804140100042090130144920f403030148000d0305840711801100c0000e42190000561718002175540ca0412105003280c0c061203005000340d00080011000c04540 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 308651843 1250 308650593 308650597
    0x1b0f0c150d0b06160c03020a0501020c10030f0603020d080918010503070302010c110a17060a06150e030a0212031201050a0627050904080903010c0e01200a02040c0915080705 76
    0x5a141c2039564841c1a14a501d4200807180d01e44060f42c18050744011070b1504080d0f101c0385000c280c0c01012031410105095000090840100303d00070071018240301411000c501074140c00d56003c0182e0f494080000040c6c8070284450b03110b51080c50442d444072081410b01c0965006030070040c2d407402d0000010019514080790310016640c085c80c00402014150a11240800101c040d080c0c112844020006003141d0300c6801d0061090b00380180c5225849682e1120700340c0e020b03409400c132083d0080380640c40190240d146505c80080160a44e40039011640000700081e110640030f00340da806c00074201c0040c940c410800c81c050700c0111004070f000d5060240007440a0004418119510503801401c1804104a4280b400804000384a451070b17213410700e0100342c15004024600e000e903003040c415161040c0110280600e07204180e40e1088003035040c907515001c10b80002800116401131803585c0001d070701d8901038550b15080340d450319480342e45417070700c0032400b10310140c074050804c02c151040c04809a40700701 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 308653093 1250 308651843 308651857
    0x11040504150e071a0307090605071a0613091101110313050103050613060b371b061b11060106090902090f090403020109031b08070b040501021b0f0c15 66
    0x100000d802c50400100d0b854030076690440c40b01d4030440c0007400c001d0308110005512841d041d60340c20884035550081079a0a0040e030300010503406e15642180c1144207039102c201e5120750003e040d21959004480034000b242d000010648606031140be285d1282c0d600700d0031455609028000031460404200307440300c10b2240b00c3c004c980c10543c496000c14081da80302e10048100d4621500708108196850380b2070100c81d800a5080c4101c4001d0005001c080b154201400c3e42000444038003c610300c40c1201d0440c0c6500c4130801c2c0305c0c4e66a41880c0030310042000b500c42e59100b4000202c1400f5911015200640031004000030030899610000040c8140750b8416803500c210b070220000540c6a29a02c0001038000c1608900d05401c1445501007105250f415084196054000c4e19259001120009c008420301403801000d4401502001983c0004611455442c0d200d40030303100044c2070600051600d559034846030501150b03a40710440d40f00750480280104107043d60201ca040528500b54400c02040e402040 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 308654343 1250 308653093 308653133
    0x7150c0e0922120207090c031103060f03190b01140405070f1202120f0406050c0405031e0a0501090309060306080c0a0b0a0c1203200405030a0f14150411040504 70
    0x180a048405001100303111940f68015148480c060b4604002507888820380b01c1c040703000b030801882c000f2450091146d10f10a0698a05840c510b40d51002440785100d01481c01c6601840340d103345100e644044010611002c0c85944581c8107540b405c04128a00702c07410024a1085113400180414942c11842a030401ea4450500c005104100244480240a0400b04003041503043d4100b0643d2100089080e228512030041080151184491480c42c1e018034000e41e82c0551010020350320b440d699504c00070a500e49502150342a803815520700c0c1c04e5446015040340071848151040c000316405001c2c040182510b0401450301d9003050000030301841541c4590f0600b4040007501d4049a40301c1c1c841d013855160001503901a4807280c07403008009181d2031084d01c95081501101904030540e010440e0219480100202507892141d22600c0c0d07a80102036089600d107542d0902550001d0f810701498034488405041040035150a00348809069070b00c0428600c00c80c600780400002515403000480c401e2042 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 308655593 1250 308654343 308654371
    0xc0405010810050901060816110d14040312030507080f07020d0f02150c090f040509061f030c06120c020a03140d140115030e07030f08030a090807150c0e09 68
    0xb184004121040a0b0415070300480d8010010a080e40c10801e00c0d4000c4103201a80e8241078200c0d1000c8650b14079800c04080e4541000c40e1000385903118400c0040c10070262000c851070030341e8903941e0007020001000795001080d295000c100601e0f41010803503500455043d82240d0f1031504020080d00c0e03040b05c14030b00040c040844010340480e4801c02c040180d0003402c280000300e41c02c20403c003850540140320403a00c82c680d042da0880a40c00c00c0d00500307000f5250780c030062826403122041e02500c1d00342030410080f10b074840180040441c01b8040500024803058403014600000500c0c1c480560700d110311404217551040890100080c0c1c044842a9030740b0b03040311923585601d213011f1084041c00300000101c402152020001c16032443d020005944241291001c0001d490602c1e074498440b83c0501c0090301c80c407840c03180039000c2a002c1004540c094005030000800348000e6484040e640c000070f40030380e010000c0b16007000d95052035108034044036200f0305207070070782d09440302c0052012180100007500340a031b0703 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 308656843 1250 308655593 308655601
    0x101106040b0a020f07050a0210031a0d021203031501080a1a090403020102091509091621020f0708030402030f01021c02090a0302060703050a030b0409150c020a0b091b090c04050108 79
    0x1007035041d1074018000080344c582d2a2902c2c2400d0380e55403142402130b4402c4050064019801303005e84512004403d45003000380500c40c00c00208141514500b030140c0c2c00010740d802c48859184280015442072b407691014005900d481c1c8001040a40014540316072549088041d03031110301104001201c0101c00c5400144655443c5012070180c0507036419a134004140d2000e0345800c2c10220301600d89403005035100c00390381c0e43d03540d034030307100314046003c1100401c1da010030340580881d4000b81100c1a41030820094074005060b0b0140401e507101d03120030754806d80c0120074442185800c4c8040e0030b0a1034203900a60410035040e0100031500f482171025004164000303942469034407403414040c001d40c2c00070a0f030b0b17480e980c0740d041c042d041c3d40c4103240392400246400a407032100e141502c41c161300d05401071054806048a041888000c0c480320074144190311548182800050700142d120b4070401403c4013500c11034041c0600c1090312121150b0580c0f266004600304000c000214080e10304a41092901d900c694507 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 308658093 1250 308656843 308656861
    0x102070f261b010215070905010807050f0a0e040b030a031409030c030708060f10080a02040e03091f18120b040f06020a02070303081f060302090103020c0304090902101106040b 77
    0x95500c040711a50065040c000d40624102800d0312840c01e00f0303003e68502c00840071110302c0d91001100d01c2e4020900c0034a040c00107500c106841640200c00d818603614024082c0d080e042d0f181c0000030342c080000e100454800c0142050f000c0c42c03075460390940c0200315124156030050003041c09101855552400403034203400a660401200700700d42d1010382612000c80d240c4000c00d840d980100e4032000303161000b0010980440254202d04115a0681c2c040c10005900390300b08401303820380213851030302840180150201695801c0c10300318000aa00c4079801c41348501c01000e00882c0c00d17180c010b0200c4000070810820200c0106c5020019a0b000c03504d20401d540317516080c100070314005009440136101051114005800081d0501503a019848160455854203c2c49000e80c4041400501407450740e041005a14003980240040401c14103016081c00c400714100d610f540c01c2039215103d8076827a842506d055003020b042001d031903581480c4c40c02c0e143d400240842c2c0d0701c041c05040240f10384050070002c0d4080c2 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 308659343 1250 308658093 308658149
    0x706080907051e0f03070e0a02090d021c03090b0406051b120301270e0c0f03190c03120e01020a08070203010914160626090f030301080303150102070f 66
    0x402d0040403101884101c500381d00792480040b14841c01500780900b400c1c003910300040d400c001c860911a09803055a1900140c41c00b80d0031800030300707821a10b02a00400180c2c4e5031107042140c05980312160354440000d0900402c401801c2d80548501001088141b0002c4c5c3d1100c1100c11074071181e040640d034000c8100c0c205240540c00b880f00c0800e80004400414035001680301041d1001610004000b0b4580084c1d0306d100310355090f61065120b60203400ca94555060203115400f044c03034000e05a4081c103103843c0110340d15690710b10084840003500d80d018001c0003a95951800c13103000610713090088052070350001c2c0d030300c1c40c0c6100050301342c180100703c042c2152b03400d4001080344c5a0005407020001980da110940c0c2d4a403541c4511000100b0500216045100b1000300d4603900c4071540b000e0107455603030441c844000018010320100e0003641300b01032107054208001e40c0204155801140ea070b150800c20384403400104200141150020241000312440e40d00a8000351a0a14808010907640140707940e060 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 308660593 1250 308659343 308659349
    0x4030b15191a1b1c02071512050901060e090a050f06070c0201050304060e030406090302011205060a050d0c091107020a0b040e041202010b030a03030c09120c06050f0c030711210706080907 82
    0x94401e40811321076041c03108214044808054085030801902c8440101e00f0101c42e40d039001c0010841020000d81d00e0080c5c0020303402c119010300000788a52070380040c0c2802001181c58081d0390740151400700c02c0200400200d0001c01c45500a0a05420304c40001045000303400000780c100880400801e00344520303a4051040b04005100320303a512582e0341d402620048071440240c0c0450a15500003c08564500a0070320414001700401c00c142e04250401107000c14000040e06d02e04114400407403141c1107403103141f04441d03180c4112a00c440706132040160a010a811007c000302080c0400c00c844891103a4094010340d00440c039401322010004200e004005031100700741d040c070820a9620170300d41c150b440b06141d08069910b402005031101c1250451169440008004a0320a90200703c5c1501c02c6c80500018620910840d28055044104906d180c0003c8410781d03651001308101049440c100d1040c2a450540000c040c000034034040c202900c402c0140b02d10000d20080400141908205000039409 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 308661843 1250 308660593 308660647
    0x1403031905130201081f0338010312030b1509040c021c030f112706070807080705030906040902130905060102030706090201020f0d020609070b070f0f0804030b15191a 73
    0x900c0d0b03139003003580c0799030200d03c0703850709210004040091030950382d2308844042080203a40007141e4138503a51100c140208030000001c0680c1c40c10000455505c148504c04001c100401aa884201c0c1a040200320b44a01281134107550140c004011600118182d01c5041c512500300021b051040c1d16075000500004504041045000189200c030645545881100003c2081d605030518141d4030502c1098130039402c1c0540b0307002e001c0c0003041c0099402d00c0149011449902928200481100860310582150704080040c9030081020a040d40200001d40d00800c05007105011030308210001075140d00c10070394041c0c419070b02d42c403109082d64000c0004010140d9140c0c1103c14540a040d0001c2d2903c40558a1541a00800c2d9002130001c0700242543c0300150005210240c00304035030b99a5000d001500d00c104c84007401408000049402e5201c628400d4440c03001c000b0300640c00c0020400005441f0301026101d888400e400e20080020080b000011b0b1700741da1500703039a42030007101c07440d00c0c241013844988 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 308663093 1250 308661843 308661901
    0x150c20120c01021206010908192a031104230a0b060a02011a100819060b0714061317070305090310090c170c060d09140303190513020108 60
    0x5814036056009104c402130300108412207840380401101d0b8465540b080c01d005610440300d0541c8500c10b40d49100b012441038035154803003400010b4060100c05e801101001c0041049800c005100d0920b00c110f01401c42114104201c009001c110308600c10059408250b90840c640000d0182110754042001210001e0141d07880350741c20780000f80078049800c4c1083d0b4a0321407903200f03174103070801174001c1d0b85000d916118103005590741140c2c01c4001c55401c1044200c581c8503000003d080e81d0000040444038021403040e0526640400601e02d41034000d000d440c14580c05003241000310b0044c0300344400307031554003100769902c050a0070210303401d00840c02d44a5250280c1a01020700c1e0304070b43e01025509104060485e21556501c00b8000303141100c250749083e41d00002c0c2c041d4031900c0c081c40208441d14107020006041382da03030b44402114400440c00c850150340004184030b11800400c031030924252400c13909114515140390000001d03240443c000381401a58404605061042d020b245070509507900860 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 308664343 1250 308663093 308663107
    0x110d090501141f0503071d040f1704060914100509030307080309010c080c120103061805160f080102090307150314040c0e070c1e0201020f01020d0504150c2012 70
    0x2440c0d4065415440f02c2400100d8002a040c28003040880407181c0c0082856141c1640d96450320412070000d00c12079940b095808528005030300034141c0325469420106c2c094841d8202000a4000700d55030f002080400c030703507581301c007110f80e80c0010041c11b81003170307180c40c603140e0382d610000c00d20314041c040004102000c007004201604205500060394042030781d0703550545844100403490203119411501100483d4200144042402c075013268096259610400e0038005081d01c540e0708203c94104800818200b121041100041003070b05030000d010900000c5207020803820000b40c2c1d8540b03601c5070701a450b501841480301103000794010003140222201d0542c1e0b0b8035162074002c0100780140030304608825004042040d207842001d144181a03400361410414502100c495003603001000402c0341144210000415011400e001900c14a107080f01c0100382130401c0d2030a00c000d2543c8418112002e4034141848a007580d028528500b010392100301e0040d40003155080701d040140f042054241190006104 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 308665593 1250 308664343 308664361
    0x606040e0115240306050916021c0507020306071b110613030c060201060b031512011113081509030306100504030f0b041e05030901030c0c020a08070f060201110d09050114 75
    0x71205011540c3d02c2010340c8140044107408649060049940001076480000c100740042a80d42c00820060b004480105100c41100c00b80d00d00c400c45218001000890120214141004804e4101489082010b1031011845580140c00d00015015000c50540346e1004000c0d11803100319015060001d40803ca010f0f00d0341006080c450991040c480190710740f40f0002401400c181c02e030b902401941981c1804a5221802c01c03045a1030000412019561a2800c120001c4803074010020341030b0081c481c5005514086009060903403010381e4091102541080003a0404040202c0f036100c030080361032850b0255401c004803901d00450300001e01b90722100d541e04092045401807148124842e00c07034615051803021404800d0100b5071320040c03582d07005201101442d03029411148101c0810306c3c05140010880e000203218420591003180c480c0c00008003840041c003900c144c20054030300c42c0001c2c410386a81c46070088491041d036640503011582c5d4004541080029040307440080845200c044841c1003030300d20 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 308666843 1250 308665593 308665619
    0xa030b04050f0d09060f120e01060501110102120601180e101410020a0b06042301050f0a0f0b0a0c080a020115050a03020a030f170703080907170606040e0115 69
    0x107444a2141d00316080c54507000140f181038654195039892a941d1408005890002c0f400b800e0505114150429a40c0d0220600c943c0d00e200d1802800496034a182c1000942000c030b092554000c540d00400600071070311101c16545801c1942841c0c800400c540c080044892a40150000a2040400030600c907a0f505219042c0c001c3d80c8095a2034015440610704010000a900d452080582c0099420b5808540400d517415440f1001070710200394030f4542040e220700c8608446005514001c04c00041c03200d42011441c43c8007051080e03650790f084609100101046003e684500401802d001412040161082c56191a0340d54014003c0351100c1e511032019001e03040349500038907035081070300001600386008070703440040b242c000e8074400171903080d034444003010585100203403000001a03601122038410140140501806503803202c00c2410040b20782030034000c169222089403105441105840388000c5002034210302d040705c002442243d10b030f00b035502400d05001c000034001c0b50b2071000a060808000 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 308668093 1250 308666843 308666851
    0xc1005090606060a0f0e030f0a05010e0c01090503101e0f1d070f090e070509010e040303050c180907020a050613051c02030901050706140705070210020a17070f020a030b 74
    0x10070390380e0365580e4030140b0040b8044c0000c41d00008020300c07203141e105805421700d906c880c240901511140d18041001034500322420340106d820b41e41d5040b00354181507080c4003c5204101c01d01e401d401051804000940d1840340d80e80141500303540f105c0d44c40c5100c0092128180030b440d2010140074200500140d0f100409003100a1010b405650040c0b029924000c6050416a940c034441030340f10034100421240180f404041480280c4611040410507584106005009140720301e9103944600e464034005050b0344001e0000303d415202440042d86608049912404900d02950b85420380d40d1140310403441c4c4403011101800700c0c021001400780781e100d00c0e107080300074031300620440c0d50503c91107004003a5240003d0209006810500641000e58411002049028042c06011603418081180030000650070f0319924007088001070440110f080184404000d01c5440c000b5100c45c14158441032091008000c0c100428203000620400304074a100721899031a070045d00c143c59440d16450710b05181d0809071 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 308669343 1250 308668093 308668111
    0x10906030b07030e031b1603060b130c0f051c0519181a07170702060403090b0306100311070b31080f07060204090f0f0506030a0c0512030c1005 63
    0x200019840718004e01460702a55040c2c4001d5103000790301030515555808184403000346001c4c2c07006401d0580074034032400b006540036181c0081c82d038180c40d040146d02410829080c4500d402c1c4050034200540082c0c4ac180e500c03050781083ca589610b8000405800034800045110041c503142c14031004901c2c8440015603019100780400511022450741031221040810003441480d04818502c0d0f42d00030300a035035412040c54141011001c14184243c084c0001c111020b4006a200390100018994000f540b01c004003040f2881a123981440301c040b42800c0c480011003024143c5680b42d05481d46100b20403981501e0b00000c4598103802c00d60b0f40c0944440048a0102031000719945c01c496100da00c2500c0218507602c60341d00c601d400100100c03400c071a00221030030f80705940d09110000340251940240707280c00a102d400081c0b6054035919210403954007520660203680200590f0001071043c420744400c0ea002203c080d00c0305014003c10b5071030342c400c0147c000e070a13000b10f00021038410196045980034516030 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 308670593 1250 308669343 308669363
    0x40911040b1c02040e010207080a020a0c0b030f0a1a060c071701110d0b010c140d02101109120304151d0d02011d010207150f0813030c20040501090603 66
    0x240401c4204444410b000548000c0555920700619107a4841c10806140390009428a1065190411a074029180720009070f0400c600640c20000d0300b02d070318005048650a00e5082d402c008000002e03072400100100b101a40d01d040202010002081a1504020052200d60785015440d901611418940b00d165486061190401003461041c0a118090525030000300e00b081d942c4840d240180c072059101034103000049940d03001213555190046a0122000000c084d61801300300028078000e0f0022400319464604580c2790ba032030886008540154204031076090040784e103050264114400e551101d486503002100080d00c95800941c4070308000400b0b075640702d20380080c81c207000131110304100080c00074440102000007504c0840c610050454103104903503802d6120300d0800e103821907000121004c01c501100c0c0d90361090740080c4040c1c1c03084881d082d807507807081c20307540c09811908051002001c40034803003001a8505c1d0181d10301c40399558010030501495035594041d00080801d800309076640e00b09 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 308671843 1250 308670593 308670611
    0x20310020a1404050607031d0901061d010e031c051c06031e02030703031139120613082b05070206101505090405040b0108010b19030b0a020904091104 66
    0x30ba05850441d40c000d031289180c80c03101e640031900341c0034105400e40108184146c0c19070a44411168a0113010280c036400b40c0301c3c03071901c200b45003008090080d50410040441407103482d1004103440c0240d20010100051a4030520000c0c1c41c18082c0900c591010039540044044000c041d4020300304581c010328081c00056800900c4241525000c41d000e0b400d80e001e0102040080c3c810440210509040c41c259600030381814031001500704e00c0361010060070000b0300300e9041286407201c1c81c40311407002c0f03840960b03501e811544c1c00c1d02c1d5940180f24208070342e01d0640f50010b2044440445206854030040008121a080711545000070407031660b45040d40f5020014208a00000e00c450043e243d24811840c9a40740420100d8458103203d0b5010402005011024454441c1d0184034000d034402c0b040e0f4026581482d119508540030a04040d10400c904c0200c40e00c01c0c0c0b292110b403400e0340e0304100e8403061350752034125500182c460321b0002030f000761614490000340700b015401080d8a09088030244280e0380 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 308673093 1250 308671843 308671877
    0xd0e061b061e04030801062d0801050f27100312020d0306060e010e0d030306091a0f04020906030a020307090e0f040302010c02120a110a0602030903030108060a09121b020310020a 78
    0xd4203e0b4002d0100700d40000602c1303a140241c0c2000051408041e620303661700c14003c1070000840f5140303a0800450303c241d0041c800b0785040340403140d0207076040d20002d45500010f4183e40d1040146020b1140ea10403000204000c103000a0014006d160407042c2c480c0c2e2105059402991415400c04900c0042d1030400041365a610070842d08520a0050396500400104102003011304a45100b0032418181d5840700040c02040b54002e115100d800d0b18480480d00300305005000c0800004120300384103910401c0b41c00d00698800b4141c0c0d402c800c0440005031203035a0b00c83c013910800616000180104a171004010361ba401201e85288114030030782c009d0102060481e400c0e640c4042c60a1003200c0c0520602003151558800d40400540741194801c5503284041d42e103c0b02c041f6803003680c4401c0a50400801408642000c100c410740184110340204201d00060b2100c2075950450b80010303041160010310b00307049203900300048041c1c5400405483e901c2c0d812000c0341740294462041a000305032001d80e42000382c2 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 308674343 1250 308673093 308673151
    0x809040207200d0c0b030709080d05090109080c0a0b0c010e060a0b011b08030612100204030503040e090a11090c0c010e0705031531170706050105040e0d0e061b06 71
    0x9610003440c130103280c2802100341c096040100081c00b0483c14000001c1c0c5448100132410304d108041d1075650703541e2010700c0010003100b007641011110394000b8450b01203584445549100301c45488011030340f10f4128025590140214281020040c85141c00303006031501c0c03591041c6a00c81090b2203401010340c20101e009201140070f00040c021540500006800d8100719a6000000c0c0c1d1013800d030340407031500f075403580700301e03005a00203071425030000c1002e00c2030015001c01e4075004090f00c17000b000c070755905642e1200d4290380385201038040c000c0c60012980700034203041a5042101602c00030300c89105003a5141d6665820b903c00c182c86071082c4d41002c07419621425030b441c003542c2c0401c1008500310061000c0a80039060b4210b8000652940e804480420700740c14250b445a682801c509958481c582004005d881e41070300030f0340c800c3e4501461000d10f414000380c48061070202d401c0c1890300e54000d10026020b405108401d5000a601d120114485400401d1003803184003c0c2c080030309041200d01c0c20300042 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 308675593 1250 308674343 308674369
    0x40e100e0609060112060302030a0c03060c0908070302040c03060305030d2c030306041512031106010506160b09010609060306150602060c040603050903090a081507030b030c0607080904020720 84
    0x1140320030380452255403017501d0540100b070303100c1008120076540760301180c035080c0c8010059444510701e290610801000e4080c55010351050f10b4200940c60500c00d140e5112803d40c40028411a658442550014000d8018400554014040c0d81d103512002001c100a07101e24400311208462044501e02800755074a03440c0040710940c00294259601d01c1d080c400100710410072402c08000d40700000404004840301c20195511980c0c4032288401c1c4011202d00e0004183c10440c81400b040c40050341411a08040da2400d6411a031a02d0950320341e42c64103401003449810144001c1d0600300080140140c5070400020401d02c1d0104d031b07045070f6540b10100d89950064410303a580700f03000c010402056110360882e41c3c204400340185c038588505000082c00803036559200802d0781d00015201c00ca0828645101644030140e41814060008180002902d81e0301d1078201e60703c6a0004585d1500748183c58040d110318040242c001c55442d40c035800c010060440001c1d000025008282c2c0b0511642002000c048035 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 308676843 1250 308675593 308675599
    0x81206030607023307030e300f160f0308070e060702010c11090a06140a0302060f0304140a110301180b011e0504020a0201020309121227100e16030506220503040e100e06 74
    0x1c01401c4280c5242d240d10031460309c1d08a8101788584c102c1c2d80007103080500e4051107005a0b1656881e14038014041c080020f14800c01d01040d008020f4403603c950080b07e81690342480e003040c1c4507403203282410607078030405681500441c0701000c0183c4a1203c0d03020344203403810140009034008160042021142060000940105050106111650200d400745401ca03101c0c12040b100d06041030300075858008101010340303c031000ba400074403032403c0c20322036081c042c1e1041c4102c100c640360381d84a40d8002d810601c6089040561080c40d42007004051210303038081c140c010b106541da1041c042000f03000c4e40095403451124014181e05074141c04c0c00d40d0864240407006515165280d63b0840c401d814400b81d0f012a420320b10a2240c001842d4006010702901c00d1601100081ca00c01301c2d885042c5814601401ea1112024500040c0045000016107640c07240d000075000002008110803100c4192440034001c001f80b2011130301141c00585034440605c03d41080130f16402440ea10200307542c0001c03058071680c0e0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 308678093 1250 308676843 308676913
    0x801050c04050d030c0803040c05210c0f1215090606031609050705091f12090b040b060d05120307020c01050a051603051303081206030607023307030e 66
    0xc00c505082a42c1c09645000e4140319480d4111500c034103034207500c200c5049270240b5078030710244160300d858a04044110304000444038540b0403c840a82d41c1d10400c2c600318807a4a401400607403580e99107550341c50000b81001a03524881002554149080041d0340c0f03c4443c0c003881c00083d8441c00d00050140241211070110404c051600d541180101400b424100812030f007009000055242e00c240c100000c12918800f8414145000d0000c5c00381194500c201112420000000081000344a0745904960030052507040c50b02d40800044141c921454004c0c402d0007514143c50b2840345080280d481080c054081c2c60a5041040c01103030b80740705016a090200d1000e10000307840101d02d151aa40301d1b44681010b900d0320241d00c4162021442ea6482155036a60006606501c40742c2c4a55060704010241c00511050601d00b81c065210302401c5440c165101c5940c202118610120483c8640d0800091100c030140c2868980140a480c1e42046501648104a00310004003141036400d901140c404050354 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 308679343 1250 308678093 308678099
    0x6020109021e10030e010b0a060f110601050105070213020405040e06040303050115080c1305040f0f0b1f0815060d060503160305060601050c01110301062c01020618150403020708070801050c04 84
    0x500203043c4201d800700305d50f5aa054180c1c960310381e00c41e01d04c06002161140f000b1107000d0680104040200b1400c2a03d50300000010010340c0d030410180c4540e2035044070404d03030030107840383c100b0001d006a92006601600b000d811511182011685a0055000e0b941c18031250ba290303c0404591001d0020000000d407001001440109002c001713030031601188501110001d64600006080e00c408055818240c0c0d515003624030414aa441540041c00c019a428810041d48010405120a100520bd020312100c040002c90340009801a410b80789002002c1d80d894400c84602d080040640d0301509010f0320440f10415a4990143c89041c1103c4e4404014071180e9600070044a035500840800e51071b645d2507043d40030400607403d020354041d007034696500440c001d04682851a0700b0035500146440c0c8083d10010100e80da0100ba030660129500900d50902104900483e15000340c001424101c0c601030400c1c0010103501003003050407101f000049414003500d843e0070508854013502c0054115200b08010 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 308680593 1250 308679343 308679347
    0x40305030a0c1121190819050d06080303062716210509070501090e2a030403021005090304060228140c011d0105032e06020109021e10 59
    0x2e07055041c8a031108056200403800800c1d48408290284440c055600e204007400c2d40e41040300a071000845589070900c1c1c952901c440506106030300300355011403411424480c9440c090411648191070184081041c0c55907403501075201d8205586c0c45100b00d0300800c4c5980150080400405140101040300c002d50312040c0c000c0c800150414840c1060010259070039084041410211042e240c41941c08a40c80c60000301c024105244c0b40c02060500c00500d4090090032a1503a0700c42d417202e00031003400d40542c180500c414100e8107480380d80e04041c400000704010540e000c03512000c0e2000700501808152201d44c81d2685900581c06003200590020600040000f4000c1c80401000b00c0805c04441650044e02e865042d1012480c0000003607011030256407283d60b00c24454819031001c41202c582001d52000000d0441c440600260320503611580c4902484522591840c040c12031142903004c065903404010f4081c021403001a84603000803c03d070700080e00c0d501100c5444107030043c03500091150110003 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 308681843 1250 308680593 308680607
    0x403050105070327032a02180f010b030603011107061a0a050d06110f0406080106020f210304111002010902010e1c030c1e0b16031401061407150209120102040305030a 73
    0x30580800c45050344020403802451105c01c0c0300c501e500c800750101b42141c01030103046010180000d0300606048100400100c1110440d410340301208071440c3e60340c54120029000d40b09043c011141800700140b070f1410071084d03a00c2000002072014000758921641402c01802041c1340c4203568101500000680008009a11410f0368071003590780702d420965489805480d90b00b081c0c03c980042000040180456901044511428401180140440c00190000350a0108041694ac50780540032000c1020843d41313003c88409520b01601040c44503a400400902030b203502c01080e4041145100340341c2007810310800c0511f1003041020211611802c69808030b40e281d086a000f40c3d45400b903105800600318204060300601c0c0c1c003c0f104c4080900b81010b850901e00420883c00b001d1610f846c00c80611004412141c034116505800e00741801c1c4140001080640b04443c0f00400b554140f0703d070040c3c01c4425502a06000c6001e44143e000b264801002c0380c200e20903808040c040b6442400b05031515841540 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 308683093 1250 308681843 308681921
    0x2031c0207150501030201170709061d0d0b060f041a010503061504031109060102010b030a0221070803040f06080c1806120a0b03010b0301200a111204030501050703 72
    0x5001450440540c0710498545032034002d0380042a281c00040042d03603817142c2500c80f040c884200301600c0b420301d81800382801810340b00d2442448910140f5003910a8410154a80008080d00e113621854184c030700a109902e040f100288240100c413401d03241030406200c5c1c0038140340c12030741c1c8065903414440190f03800d4100030b1005900c10242d0a00501d129403070000307030000b50b100d0b034902003010445104005040c10010300e864116031500c0c5482c2200d1742c0025034508034907010303180010722510000da4000300540e03a01061905200348000003c1404001005004646034180c0504c0c2040d120300341250580000e0307070340c1c2d98000d0301400000c08440f10300980003400d40e4000d181c0c034a490300c01203d1396903030801100e28401465894046d004142828095491007802c100d00030010240c0b21600c440c880301131205000f6141d04041030f40840c09002d04054000400400121500c0030324110400059600c6400121015420704001c1074400c1d0103806105041e603080c014a41c1c03450400a03681003012a800 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 308684343 1250 308683093 308683147
    0x5041104060234080102070203010b150307121107050703050f07080303151804050d2a03080a09060509030319050705031f0f140301060b120c0c150f071e0203 69
    0x30424081e03c0c0b5049154001c020340e100240e242c1a2a004050850381e9800c0924000c503334486210002141d00d00c1102c0c0d00c60017506240744c0c40c0c0000c48003a8018914410074042e1004009011814040001580021030740f1810450300703000240064a074455400d4402c0fa9100d41c01440864034462001c802c2c2c0d505039402070202441440c62803804000114181c0e400d94242d0803510354512015840355810003268152284190383d80b40154045049628402020703040013540c0002c5000c551075604030700a281c3e0006030901203420f0013110070b030f1260b00594403d08000190807100c12424040d004c0c05104120300d803a0030f41150b41c0d00015502e40d43c80c1c60040002018695004036260306400000b4000c0d03c405c0c4140007200c100c507018542120f440d60000c25441000b4845400c040303040d8500c460b071000c1c11498068599500342c1040707103004020b04991705414110740800c101c125080c0034a40c8540101d83c1e401800300611080c441d00c108241d0008130045e0400c000c40024451989246081080c400b = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 308685593 1250 308684343 308684413
    0x90f1c0e0607080d050601090e0a021b0a11030d0206070801030b1801060902030106031808041205030d0207110405071107050919020705010b12030f070b130203030d06050411040602 79
    0x1000001e86942d00100302150320318004181c0345102c412510416034042c00a0030180409402e020075103101c14001404045540d0f000110100c03e890044141750000b1070007000c550000c1100d180840034664a20040b5012b0b2203414540f40c0140d03c0001c0d03c078001d02598564586690135602c074151044002400245d072503c50b42031504055009215020041502400043e141c0d410540024161810034004074800c04036030106402088546088504a80054440c607080d0105803510500314003e4400c1c9903507551010031400140b010700d078180303005000211810005a55030003000c0d640da510751903a080060780304450074001800c1051402d40c002c0400191441305051784281c0005980c0890000c0b54075035100d4509800c0c6050a14041c1d92840c280b8001d1401c05814154105190240520241a00c01e44602298120300c0d12407081e100150042c06495450341c004c9241c40c0500b942e4800d1501440c0341601f2160645d211006490513500980e014000707202c204000c14654030180c0d164560746102c5 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 308686843 1250 308685593 308685617
    0xb1602030303130210090b090402090f03030a0e0f0907080a090302010204090603050a060c09050d1203090605040f140303070e010c0203010b18011e060504090e01060b0c0f06090f1c 79
    0x4002031845111203590701008055544140300c4007031290f170107041c24400c07694001d201141c0000c3c02e4600c44403081d02c0050f12840100700085e02c807020080071507018000007801903002035020046188400c010b0b40d450038401010310a00121080813100940080e10f03150104565448030340200111078041c1c400075051548540d010300440360603620442d0103a000503000005c000c03440c0a1050f0b031000d28108118210b00d0040440c1c071200c040391004100e1069021194441c038000d91020b203005400100801051406181440b01030803100c8050303405610124481c07000c03810001c100c070b02c6504156501100c810b602c01c01955501001242242d1554071210b10302202d07200c43c010780c0d5120f11400801c01c080d5241030146020700300f0300d40340864800d1764004284a007039001011a0222840188001007041c508998140140003c1e0483d102070007000034100e0ba8102e0004003100c2d002000000c1d02c00381d407102c2c41400d41d50b410401c40900b00390004500380c080410200d0201000c1d14031400e0000d05409 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 308688093 1250 308686843 308686849
    0x513140604150309051009053f04030b100303170103020f0f041d011401080a0c06080702150108030c0d170a050903120a0f0b010807200c060403081e070b010b1602 71
    0x3c606e02c242d03540d4074201c160610008004042540e14151074070024845800402e03440c2c03042c0070b0310200000304800388542e908002c60081718011500111028030744c1c04c03d88801102a00b080c441500090200c01d0882400140c46000c581201d900901011480440e4402e020140d4a001e1240303078080d076103900c60001c898045088000716401c000c00010003809103519410903000c1030300b2817a040e90040040c50000750343d0f018204107450250610340a90394030380804a1800380303109c00d0700004c3d940d417000008101c04000040c14400c0c1ca101c040c1c8008100d1024119061902d0f0409005825000030109000081a522841e00b019401d42030301e260022144d4800642c01060b603d03824030310f0b0b540c01d000381c10071200d00c2280200d901c05d2924458600300804000e00c1c0708100f025069800500b00819410140c080141c4c1200c81400b800e29a12160f0f82e041c54019500201e4001109400032852042021032032030880790f035968450308102031a400c080d000303c580d400440060a04604003200340e00566 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 308689343 1250 308688093 308688103
    0x90501080723040915300807020a03060c20010c0915031401030f05191101030b040b0a060507060c0203091003090501021201080c0a0501050a021b030a020907051314060415030905 78
    0x216050501440b11460321241b00400340c04401803800410741c1c0d0414140210413844201c40d16904a1400c5884404500010301504ca0a070f10080c156403801d0290b000094010f81a245031200c218003560300903201003402800e80d280a211100000e18800c0309004000d48000c00901100301840d0001d45200c0010301055140002c0e00144d8000410650490030485e081245040d4880003005900356606160341d10304440400c1104513051544400b00d1844549441e0300c05040e00c42d0060000403550f035a560064440e9000050680d00142010140d890307030340c000401c444100308041e10f0042c4510705504114000d06400c40c04030744654003042021015940078204034060540300002c2d024040013001000080c884030380c00b0505011042c005c4d8041c07290042900200c800100540c41d0142e82d14800090410320b00ca80e000350b01140690900c0303945a03001018291104550290b070070042d03150121110b0103807001103960780c0410300b0001480000a9903420407000c4030302d401c01055084255031102c0c109 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 308690593 1250 308689343 308689361
    0x6030506010e01080f01020702090f040f0b07120e0601050d0f06140703020a0f0e01140a0905030a14071421010f110d0609020301050303030c07050a050304060305070905010807230409 80
    0xc42da0400502c0200c50600105008940b00d800071494000141e02007038000d14000c20383c0b4065003168000405004c1c4012401d107020b64025a8100c0070b24200b100500040d01e1510310051451822944945188000171061f042e260300a00c9882001103039a182c41ca202d00c14242260301a46903075008407101c140c018024051080740e1409a00c510745100010401f5400110400400c00f259442d54240d9800c10031450350542d8610146580c1c40400d01d042d101d10200c6d034011750b058464241c2c10001d101c0c0c40c1200e2800000e0b507400352540e0b81c0da00d807503190b180382c50400480ea00c0410403412400d00202d8072690360803444103200104003040700d001c0c101c2c01c03202d480d5514411740c10b001400303840000c0e407849000094102c08400314115414400402d1b038a00000f0945c00d4503107000100d10050040c20010030641c5c940c044101d9903640d407a840b000b406000184d5451001c541030203008500342d030103000b009208041c0340d92175200b10100c032102c0b11403132030300080341c444518401c0102040c101c00c18080c001031 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 308691843 1250 308690593 308690609
    0xb03030d060810240302011409060f070204140103050c010503042301050a05090109050a08090a0b03090c0a050d022404180203150d08070f02130c020c04110c0706120603050601 77
    0x14400783c0a284100f030340c0b00c00e242c0c2e41d020141448a0040781c000c0da500e580c181c82d028a80003103141c44103900092070b445201e190551000000c6000142603c0c598003c00c0d80c05c0c400e8806021036203207400c0c5a800c0000a000080031a0409400b0b002c40d0351060b805560700c203009400e441d07209003c4010b90045035443e10b10309501a51035008005c0340601a0084640101e0814000c0101c0025130315443d40310210038000034a82c3c82c0004014043da514102d806002d006001261941c07400c195101d1980c90b101552210b0107000c4614001805107000ca10b4003101c15000740c20032081c040e61440c41d079001c0c2003ca0400482410600c40072030401c0321083c60408031241964010303664200034244201e0603044031420741c440c240c0e04c006000014843d20039101309560105a464148415200050303110340c04954010303800317103820800200e01380c0c0003c10003003244007550304204400361150803140a10601808240301d5101c004100709041c0b1901890150360745604000076100c1c0c99507106828848207a1101074 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 308693093 1250 308691843 308691853
    0x1209030304051c050901031a061605010501080c0a0306050615130515030108031c0204230906190b07050118060c1418040b011e020714030303040c090b03030d0608 71
    0x42046410404200d48411540f1560801c1c51040f000504502c21010b0b0f0310b04050300d0700e41600384001c40c819074110081005120b9915101034100440b80d07a203c608050f00e444d1300382000040d0006011810440c10100540011507080c1583c8a0700041c10014200503005808000d0809031800c0b1100640100b0710b096190318030583c5405d0400804521102c03c3c0d9100d00e104000400407440700004482240d011009007024100c1024081c1000b8000d0760f1024040100402e040000746604c900c1d0380c40c0c2c18200720380d60455603d030341083c0034501d82d003100d1100420240090600205000360050b01039144140700102d030100400502200010101c1c100315100754464541c2d085158200302121501e002091101d07081656414074130403914441400a8000d030390f5031160344c007036074401d031030701c074000b81011560007404440d03820700075034802d05882454a00c02060110080d45c0c03034040200d034025504441e02810003400d120004004029100800794188001c10a01c0f046c4d48039805494020700161015007 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 308694343 1250 308693093 308693101
    0xa050a1206031b050619111e2a0d0308061c150b060309060f040309080d080703180503040b0a0309020d0507090516171b04260c2412090303 61
    0x71000318100d80055205e08410702420811807041e1a449842200340e140c000010308801002a0030900c161421010001c03004000b0301102c3c0300001c41009818103140301000130078801c02d103480a003101d801400da2115a150346080402c1c403540440350003440052541c0f000c82c4094850410f0310501d0001114070000004280341400b466101d424a400300c152003091441c54212716480d1605001020104500d01c401701103014984035840090280c0f00396822135040450500c400b9100041c02c0700c65500290078070304000d8a0780d0880704421045075102004604180c10041c1b901c03602e811142a001c101540c0b0031460015907103101c02460001d0198020f49400b904000d00d2000b071301c000030701124000c1548600718015961000300b455101c22600c0000c01e5a840d070102e8400c0e1000030401c5000b600780c3c00304000c00e8428403240084d02405c40c0c1c0c80c550260103400c66441792240c507030302502644490790781c5d03581c008101000b01c0b41c0e21a10800ea14685890000ca030000c0c0e08031015242115180e00200400c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 308695593 1250 308694343 308694383
    0xc11030703030605120309130c0309080d02030604060803040b0a030b0d1707030e1c06090f020a08010e190503120a02070210051803070b0406031e0603050a0b0a0e030a050a120603 78
    0x1a10155110101451031f02042101003850408807056005050f0366a144110100d4880d034800c5046507440507102c3e68404266040d4000b035001503403a284910f140803c00a100100042140c0840309800303034060a00003807684c154011710a511080e9007101e8410b442c5030000317032407404500b03c004406820548400301c500f0010000040800a94000c40c0b040d03140840c02c4000b480300c0300041d81d10400208149415240684150f0f201900007900800c00c524003160646064202e1500039100c84200c44141440c02850304200c1030400000c1d00e42d8204211800601060b8070460340c3c01040340c50007614061065010038150540722943c0000108041a8024001609006442e0b40d5004030f005201c1075080001d030710201c0c8194810300c000c0c595585482c00500da40130a540d0305645901d00200321607980ca00781a9165102c2a10440d4140504c200003121140148a5141c2a0380c80b64025401d00381916800e480d2940800b0200050212240c0f403d1000780107030240002540c8907140791100349601e5210 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 308696843 1250 308695593 308695609
    0xe1203040c0b2805071b060f02150f100e0a02030612340e0a09020114040f030803100e07020d0f0e01080406090204061212170402060a030c11030703030605 68
    0x40e0310b1820808a4070300c0c0ca070346142c3c803c0e0007001e461544600008180c152403034812a80010220070260381402c145000c0140800100e440036142d00310b04080c4101c0481c0c960851300c00c105264503180010844000701c1c1c40e202980000f40b10000c0390099240e002c0d0f18504441110201a1a41c002080140e00d0500c210b041c00c1d60f041c1000102403059a962003015203e0301038540300b40110340f00605030005282c20a6850007031101e6200c5620b0703810000516000b8100e8803506a01040f03104420403040701c0d900048404039861040110800f03400c2d6994401d40350304c040d04601030111003410202c1c4016424003614050308040c1c005000062220700d002d40040341e040f401c1c1042c421801030000c1c0b90390304071103560740c010340c020400650b001035440000d0007440300340c010070144400c405600b4200319041c1408080f2038021f0300c0e1060703000b0581030070601400044500942008040c0901c41c3c849000b50441e04082000e81890884035229802c52407560700f12020650000b03071a00c2041001e4207100003 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 308698093 1250 308696843 308696849
    0x60603120801080a030f031d07030c0609050901090906090b01060e0306070305100b07021903121107060c08072a03021e0306070c030c02030303040b061309050c12010e1203040c 77
    0x1040c41040d8036040f04540c442d500c0d4074024042c0840740c0b201402292103a44004410a05005107102c290400c03501280d9415031400704481d03c80400a0200d07925021b80c80387c5046400c010207205240c0e0800c00c00402404050808541c000d4407603122900080861511a020304040d036112415031001004040c03424102400715028103240006020300320100001d00b0044d5112400f00e1030380c84031140701040340c00503110300305a001d801d40c800110070844520302580e4050800ea5032100c0740301440c0300740343d00da0099201364000300d8410205140020900c001408805005414482c004070300c0301f518405c10b244007640c2c00d904103030380361081c0110315080f0809803040615804c0c44914140c08000319a940c140541484140300c6404400001c2520490b9400d17007090b03024040c0e94403820a840c0c601c06400041da20140300700c0360380324030355200f034101c2c801c2d42007454204005201411030042480342020340c0c22070241c1c59549507400081c03809020400352844442108003241d50b40f42ca0700340a00c081c05960 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 308699343 1250 308698093 308698097
    0x1805060909031b0304050907020c1f0e010804020616050303180601030f02012f0601141c03110309041d1501030c0501120b04090303091106070308041e0b0406060312 72
    0x14040301010000583d500291003100c1c0301c03041c000d00c10245283d40601d03400282d102e2014400c100d400795012a05c2503110405450300903514402512120f014002400c2490004100c8043d260740343d840f4050386078000d800900218500395460b0400d1040c0040d407078058625500c00418046a01183c4e001480002c03044806441594110b0b81c4000300d42456500183c100181d090383c0b404900010f40f01d11b0070441c083c0c03c10280040c82181560703103840c0c0174441c1004440d00d0048074412420011040300107500d5064818544e001c3d80d9074260345070050300040742c482d44800e0010940540751803084042c1d03903001c1008101c1c0700e041500341d40d01c2c05082d4031110500c6441c1d5001000041c140d503014001762042420031b40511209861894010a02c600c142d030307800b03424100380c4020306800d40e100840c154003944402030f0b000181002d004c117070b210780200103001403005000280403070020803103250300106c0c04010b07051604060311480d071000c1d000d0710143d5201da5078100400400c4004108003035410098 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 308700593 1250 308699343 308699359
    0x1060905060f09060f031608011a09040e03040911030a05010b072103022502031006050a03060b1302041706060102060601050703110115062a0206090d030306030c180506 74
    0x100012805034000c1165011005030301281c43c1905a035002c040e111903480c100009a01c914203042c00c0545100c07003802400214400000100d4460702d14101605405110005140781810110030300000346101010b403400e40c0414040400c48a085019400c000c80441c28000d40707074205400d0307400c210386060744040d0766104104900070020f0001c07241c0c1d8803d00d009a40c03014109210400950291062a90800c4a501000400e0303842964a03080d0644890081c4c00710f4003104e40903081e040c11240c2a0144940c00101c994042001403226045000d84400241850b19003000301512941031382c001b0341104d070820200321111041e00c401040070540c454001d1000b4203150401e6000600144a910750150401542946e80e0481d00800d4000d6180c00c88481040c0103050381d540d1000302000f0540c000000303450818405a00244150026100400d030010840c40c43d05161000b0819000d4003114210b003819100c0200102141c821020b0a0052007160051400c4414039031901041340c0c00141201c1c0304da428 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 308701843 1250 308700593 308700599
    0x313050a170414040209091f1d01150309021c02120706050316170a0203090f0d0e040f09020a120c12120305012102130212040f0201140307020624040c080609010609 72
    0x81c1250442c0c10620b0f407948c80c0240d11614803c6030366130200381c0144480182040c400c21048100014440c12241c075240303045480905202d0403800d407104c0c4140a540003542d80404800d031003420042010f081e00c0200030000008919540c00d00f40005a44402c4c04140c012042002d5107044c42e0160b11506204c0c50281f5400103115860341c041c0401501d5250200c0d4048000f40300c90104110507495042210200c80240d000300b40020140040030000c10b014a04026040e545024140942e41c0c1c01035004005d51800c0d424030094487d00b00c00300c43e00381c039484005040010215076402080d008240540c035103110030116002c0c0a0261241a405803481824140a04d420240c0410301c4c295004c0d412207142841005000b0140007030300510360041400e100540500080085403181350000074400c0c0c8070710002d0810301403030343c034103000440d00b00300580c00031400645c2c407004c0e01411501d4540d032150303035001140c048008a004c03640e0807251080407640e22000c2c80041d140c424207080c01012946081c50850341 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 308703093 1250 308701843 308701849
    0xb031515030a120807050909130c12030207050d020402160327050f120102090a0e010314060402060706180807030201020d05090318091003060905060a0f020a050313050a170414040209 80
    0xc1411840420080d031302c408980882e210300201d41c400700c0c00919200e101e043c61100c010090900c00e1048512041e401c100086043c001010340c540241c254000d00b40251522043c000b07940410102240d01a9081150100704c50068445c2c0c07480500035130303038001d013281c40c15604441c070b068207100110001801c01c41006966911894200ca40d80c040c2c51f407941d1806074010150190050f0519660300280c075001c0410601070b003181030350403a4010010418030f080c03003a00203071f1142c10645001c1d401400c10000840801d2558001300d582c1c098803000d14041561945600c80d00d5040501d00301d0041c1d40015030307410f10460354043c480d04000c002014500c2c01c1240101c00106890a40da600d001e49040c0d000070340c40c000e1001d505801150807010034003414101e8900f43c1d88030782044924280301d81c500402c07101d05d0407452085e501c0b00202501c0711465611a440700524405100000315054820242c0311000103085103182400d084044410507111070600030fa1041640720100c2c2c0e9030243d071050018416a0f9 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 308704343 1250 308703093 308703113
    0x31206060c07080d0e030c240c0307050303010b031501020105060a060309210302070b07090522090f0506061005070f060c0c0512130b13180b031515030a 67
    0x1580454180d035803003400d01e038140d0814069074041e900b10b00490b4045900c01d07401042249903c242141030b107070100141000c008c501a00b2401a0240d2103101d0300d1060301c4070041c0010100040d00700100c070704025044ea98079107154800d80101003030703007000300138461207400d444d42400e05500700740000d01c103601d40074003c86c0343c5a6152190104054503901188113105004131056409100c0e040094140c02c000007001d0044e5000050464114500d0000900058420ba50441c2500e1000701141076090440340001220300d070054a5441c0640c1c1c8101d680c0020b2088140070544502c144090506440e00408020031b8a81483c20141031100030013510340041c85110a000002e613000d0340000302e07100c3ca240704580e1070700e107030b440240248102e8006400000603032001d0030f28055175116480c0059107a00750311815001c0d00040b0101000500001c2c03004200400b61896200903000d40062503240000c0024940a0100384111810019605120309014201680c0703c007890309800070300306416079a54840540d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 308705593 1250 308704343 308704351
    0x10c020603130c03050309011e0207061206150801050307080c06160c17010204031502040302060702010e0609040213090c031803180f030305032715061305040b090d020312 75
    0x180a00100080240c404106540c2c40c89030000b041d500c0e940e49038540340781e590b03111419141c04500460041481c3c2801001c40010f200308030b0b0b015204151070048250f416240c8020580708040e2515030200d052413404d011001911100d94842c01194500303018141000e405400000442d041501c84607265114102210150501d801752011440c0c03040c00c1c1280303540c00540021001d1511446408000301c0c0c150080c0050300d02694540a03a080d8250011040f80305600c0000e4001030148a084003540c013078090f01c801c19001610191a0241040008049a000c24010303600a083c82c8401e01007500d60307104071011b903102800c0801018800c5214140b440030b01c02001420484603804510136070640c603032108001c00d842d51301d42840685924000d009900301300c0e0903052400d082c4002c854502d404051800c0c2c407102c5000a450002c4401c0502e10301240001c00b000e4210380020750b030700d60071a450b00c107280c883e6002e2601030081d810072950355400c04225041c3e000455009000700da00d4242139196250700 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 308706843 1250 308705593 308705599
    0x20703110303130e0901060504050601090b0a030f06090606110a020f0d0c18020c060708190e0109120e01120b150304050c040e010e0c1806061b0109080d050a0209010c02 74
    0x58032000000e01d584a42c84510b460b1215030080003072400c00b0300f214280100301d003c0c000d0048945840030b110840740d00b00d50300c074001164000e0421210400301c1c02044c0011307580c600424a200740c4107910060b50820340c400783c8085d55403c01002069800341d80c1c0389925240c40050403034900c068001501c44c626560442e8854000d820301281008540071900340103100510700503040c1240c2204443c001e4111440003086c601450f0300107a0320130b110341403052040e02d041c1c164a0301c420501d0745c900020082c0c0600c1100941d030740c8000c40c0c04034401044801c80d010103907517584001c402007800141100c00d01650f00011905004101000707685440c0240f40304103d030b030003494684c3d0322800e00d0340c540f150800c0306680140c81e100401c00c4082041d0012000104003004440b808050310b424030482c0120110207086044115000c50350f035251400c004d042104000280c080080c40004031103084450292048071400d00025401c3c441d00e5141c043c00b0303408904c4010850a09070100000b8201001841000348 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 308708093 1250 308706843 308706863
    0xf0c14010f2d050c07031b080a032703171305010f1e20060f090f06061903080f0a0e010903150c050c0f03120f0915070507150b0406090c020703 63
    0x10554030850130782d01e840c05203004861681e40d5a041038130306a82002c401c1940e01286010100f01c940700041e01411440e459503541800b01d0241401d5001070b02078041c0d102c0c080311428800401310340520520082501120394040d6a040040070404c0f043c0025404103040c084502281062182c00082110000c131000800382101e428802d0304882e84200e4288a139441c03040366031070a071105000184241300710340d100040c41541c1c0b1202e80166481e001d6044e24200c0e44d0205000461a0600300407031250101e280c3c1ca000c0383c19071039076500c0445800010030701c6001d020100b0300341303480350b0310000c0d00c1142c507001c1c00c101c00301c20706645541c9a00c0e00c242100d00b04c40b0341c6800680b221184568102c48008145506407010000448000d075101d40c880d0a0010282229074080340c00c590380142401d000300c45003801030130003108054216900c0e1000814020503c1030610846000c25400c0150a41c0c0f4050043c0009102001c4402c000413500d55400444256103000e40100302140c00040300001e41e034104d8841d00c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 308709343 1250 308708093 308708177
    0x62b0302100510260304050409060f0f02090d0807020604050909060a060b07020603070e01090b0a0e03060f0906010303140909012c010305102d1509090206040b070f0c14010f 76
    0x5171541c4200c0e88401c0d00b161078042c201d4244007055118250654590341c003800004900206c0005078001e200006d580200c0c1441090b000854110042070036500c003030011401c2c1680ea00000b295050200c1e240780154101d00d040007034220312441501c011782800ca904500340340f41c94021904a020090200d02800711661072512540e0207411a207000340707000480742d552080104402428101e034401d4260081c407599010803440900104224800c00c03090006214980c40e588044403800d0441b503924001490411003029280c40300d41c40c5038080c0032140d00c00540c403440b051403080c0c280001c0380c0d071000059181c00140005180400c5100b450a0340120100d000c1705100c12410f0580c10075101501e0b103001d440c000e408001e601e42c11a00803102841955185140e981496001b51405444000d41c054410401840300b1400503028050180c082c610026000780e1035501e000c01d2100355041030b0404080c00c0b07000b540942e070003194540303200e07440c0c0b03403240b6200d8022101d0f800c0000700e51288910102c00c60000 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 308710593 1250 308709343 308709419
    0x1b0301090f0302011a01050c100203100f0815160c030f050d050f06010905010f0c0b04031709011410051f021c1d1503062b0302100510 59
    0x201140d04106058080c84a600d400f900800d810b862141c03c0ca002607900342d00d50760081d800d8801c41e540c101b0180a2031003802c00c80c407000f0350000380100200f80100d10007286004001e01e140b80078040e15801412030300e044d807003904681c0e00c008111044007030906003030411055004042280c0c1c290b042c1041060841501001e4030a40940c1d00c100b220545000c040181000c0c01c40c440340d0180000f0f0321800412a203940045903840c28035103c60340460181414a0006a5000076580d80075001386003009110025a5040018407025140444143c0d103402c00a608040d50201e0315800000740000e90120f5460700e4040b81d022404a2201c1d003904000d100d80e00a16070081c4a510b403120082d00411445910326240585000202c030800c00355a07044582d0b9440300d040006000e2a5030381e20f4a081802d47d690030741040514211443c05090b07855844038138245c1001e000020007060341c482d40280160a10201032041228002840c0c040c40c01c0001d00200070707041022044035018081442e4412040d6071420003 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 308711843 1250 308710593 308710601
    0x30606021005060105070b181014070504060203031b0f07030e1003020c0d110102090d1407090501031707060905010509070302090f04020f131b110f060702030406120e0a03030207050d111b0301 84
    0x601202d004109086542403555800fa180c00c03007100f01c443c00352f40c0b00c080017100c060140b070241001690040020521401200d6011141d080c5c1d5040030314500301400c03040d1049500081021404a80300051800c1c261814480110408041c0c0c502142807030850080b039980c4e40010700211052103848600c401c8142070a404a510300c14001d0303c0d0824030041443d042d100c50090440c00f148500904c4e0703000c18044100c1c02054100d0750400c1c200141c1f41c40d80c0300350316907a61015400312140b5980710031420000e6402c0c003a461240d003550003c0c1c85000d10310300511440c071138010700400700c0e0403402c0100001030382c640e510080d07401402d0710035900d81000b00c40d05e68001c046865640e640110071060030440a6030080540341c10100e10800e4401411100b15040c0c0e8a1600b52207420168100740400c0c040c840c880c140626150024034004203014400554050510589050603000681c00044032000e0040400280320504101c1c549030500b03a040c4140e05440d15061001d1044481c000401852281c1d82508 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 308713093 1250 308711843 308711881
    0x90c0e06040f06080906040309060e0303090907020102370309081c02040515070f081c02030108030304020a1512050a060509090a0501051006090b130b0406030606021005060105070b 79
    0x321869407542c8450042d400c00c007a51288500090445001030007845010400da030141d5815101d06c0085800c110003624001c03000c600e5241c040c44244100b42d0542d40744c4460034028503142d00016a245010341c0f20000d4038140c500c051800341d8050035500340003c0988102c101c030714900d00d00020381c2d40140ca0300c11003d10400c2443d04d00050070041400e02403000c3e5008004480d01103d250075580300d002d8524500c0d00403070402600015200c4071650210360528003c0140c441694404d40c0d807001c10180040403a0400e81000c5041d61020040004509020013041c0c0585000380c58000c91380100b400007444106c1c4020409400c0d0b89403070100320f82201d00d1b00060301802d4000d2540c0801d290400b1003569600c441032040e9103130b40c00c1c1400705052131912000c0c0d205458490b6110300b0214206000d1204550000501102c18a40c1080000b2082c4a49014102516082ea00403d03441d14015009142184500c0701c0d1816503c2c0905012301e6a80010031a070020398030040c510700e41d540b03c1c10140c0022172600 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 308714343 1250 308713093 308713099
    0x20a060c091710060f0b0306090a021b0a050c01020f030a05071712071403060a051c120c060606080c04090902040b03030a12050f0103020d02131515020f0606010504090c0e 75
    0x103003180000c07500407078032110020103c802001256902c1c450940e0942242c400c1000c5440c00300003003403075804c0211829074040411030001d0b1900000828a42c8401e40074001c420b515004041c0500c204041403004d640c82035024401004050000310b40541c0380d00c5500401c1e0b082c00b400065042c204002950070030807140400c40c441f9101e00003c12507081c01c0030708503500710014000780c6d1440307a20705052013543e000c1c83c0040c1583c00700500f0a0103104034291317006400d030708200702c1c00039081c0020000100e840e1a1001d642d40c00aa410315441d00a0035541590401d4051012030030410102850800a8400300c1700b4450000ca020880c038000304004000443c84260140000910200591742045643c00362901804c02001981d42c0c48082c2141c1010070300000354801204111080503140c52440d00070b0041c0484400500240020b542071031480503135110041030308a80c000062030f15014000540030042840c0580b40b24501040000c1007407082740034031007030150744010b02050144500d42d21104c0040c0a = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 308715593 1250 308714343 308714369
    0xc0f08031e090106030308130c030210020c190518070507050d0e01020705011103090103091718010806031c05030702250302100c0c0302041812090312050406020a060c09 74
    0x11410001c00c003003500c0301000580d0007140882c030070503014807030007044907050381d141c3c5907070b8031412022082c810144005458056044030702002580e103242c401e00340601150010400c0030400018003075551905940201a1100d00d0010840c40d183c142c40e001c07d202080c00c01842c503039108603081d0740340d004d41500a040d604c1222021b0009039085255040030400c26000c441070325594100454105107107201d02e6206030014005140c103940030f9044041e16a115003c52450344010242d0011160084000915000d0020304000303011b50708840e02c2a04444103401404c000302038070081c0306c0c105140c03014070b40802c4000800240990310038080d903503845801c03800c0403441c0d1002d04401c4903101c0e22800164070401d0f902c0c40c06101c07540251050422aa40078180c00165842d6800b000010000c4030322903950300c0d43d200c40000016140764a180200c00046e06d9584015065050110303102c5501b01489050001c100810302010341c0001c0e240f09007d90206010848011800c0d0445201100b90b002e40e105443e8 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 308716843 1250 308715593 308715601
    0xf020f0a030b0a080a081206040e031801090f12021203040504060806010306110a120905100c0c0b0702010b060702042a090806090c0f1e0a081609050c04060c0f0803 72
    0x105800662410b01c0498400d4a0755807142070070b0307071a0300c4070040041c41608100145003c424017403150a80c00030005000185407141490060f04551100700c3d950400155004059500e60304a007129000c0c0500104220740300741000741c1d842310b0341200301c80a481482d11904940c102d41701001110301400303000d0002d01072240e403680d40d540d60b21401e01044038050308041580307c1c00c1440d942541c040035096a00e210740806400c964000801c1580400d4800740244d020520705c01e40c0301d00070b42540444603a20410781d6155810302c46aa0070016110030116414150034140c41c1d40c0b00c90076244003a404072400102140e03501a00210001840b82050302c5948030400311051a81100c40317071003141c0c0510143d0301103944ac6c030b030b00365251661041803070b5103d02080f040140300d0030511403028000c14100601e801e25118107000951001c0c10741d1010002d5480f00b40b44d001c0503440071419000424030880b0134440c07410070700c2c05400b00340240c0c01107904202804240030240820140050826031300708075034a5603428 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 308718093 1250 308716843 308716847
    0xb07020f120307150b09040b09070b030f04120903262505060745030c0501090b07020f06070206070803190c0e01120203100b0c03030603010b090114040f020f0a 70
    0x303003010341d242132182c40d100c1c240c29240d0040c00120800100491000d40e6180e481e10000705018111040c148030b000340218402840d54000c5000b0f54030740010504624061030541c80c04007181c0d00240410280b21020000110400e190300c00b0051f0704512a0501400d02001a085014803090500040a0f106500007400f18060000001d42d01940960f15503a0300e50109841c0d11f500740c1e40c0d21399050b4544042003807046545d02d0304551b9980030b41650b0000c0b42024440100d00074160000ea540802c20340b801c200542c1c002c02d110004000d4240c02038240585a000100c400030740580d0f144c040d5000240b21821035484408a5004952140c0b07100c2c0c9900b010b25200881000e016444003089252000641c0061301179441040080e41c142d40b0500350480105502010390009485030ba00d00c20110303c080360303502044001c1e1803140111002540c072032400d0420107003511504040580510005801400040d001c4049400b02c50710aa4000c12545101d8030102d00030b1040401c054006500420140c403916 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 308719343 1250 308718093 308718097
    0x103120c121d03030f0306091b030109020921060601030f060501020307080705070b0301060e090a020301140d0606080d0302130909120318020402040e07020d033c0905030a031a06040b07020f1203 85
    0x103181543c1c400300e95034545419042080c011210275650090910040100e48210b4008021601c030142149103840d0056218010001000c040780c8001e4019008210455034144a00d078500219000c082c84000d1504001035102d101d160405006000001420824880104550f00050071421103440c0c1c1e030b603500c101c000c14040807026003134420700d815030125000c1c070301d03a00130342c0c1c160b550980c5604a19002082040140c241c40002110003d0301c40c000020038400500c0066424846900e001d681d33034400c17060303045a05070a5000300600e80d24111840000c111500300c007119808140c1000039004036081503442c0d50007c1e00d10002d42c05400001c0100c1c04000020455000d2001e6400301c801446141e01c040d01500e080318584406800c104a01c59454602c2c0c0c0c1d0860545118140855082d02d00c002081d0103561442c54251080e6100240e8001025414805c000c050000040d04040c09000d20001032210710640c800c01c1030952010403040c0540d641c940c203902c0c1d074641c020001445002250340c1281ca83d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 308720593 1250 308719343 308719351
    0xf09020c2b081b13210c0608040f05031b010510060801180204121103010c080103110415051305061e090406020306061306090501031d0706110a0b040303050103120c121d03030f03 78
    0x4031000d1401c139030030300d07418171302040c800e0350300c0b4034000340407410100c00722140c0500400c01da030526001411034000c1501400101515480b15445600c00050301c604030782500c6c030142084c011550822800c0140c00d90041001e4156550000427038128030645011501034006c07508401ca240c00360304000c4081050703030b054501c5007107410b400a2107110349140e400d84c0c2003182440094a02d9465000c064228035295104144500c1c01082030980280c03908041110006208080b00696079a40180b10051a02e0282c1040c2070842004104030700c2c0c4610046120f41781d01500041c401c5802001090040e0740d4641a2000f0206241c50486002d07583e000041c1980d440340300300c50210380341c4801030402c1844406600e480d5403521004001d00c61501030220703090303e448050f010741c41c054405603800148664045a02660081d074020400c1e50450801c407160780c0c00e8001d8101031001800e200c00c005000365041b681100b80790300308000c0000100600150110800103881c1c1d140c00000b51000384151480040c1d40a = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 308721843 1250 308720593 308720609
    0x9180702101a1e0a05060d0929010b030c070f1106190f020316080c07030b0406020703020d031416140d06090b0d0203120a0302040f09020c2b081b13 65
    0x44010b00c050341c1c401c4148403d0b4030980020342c2c01004c1c06035003014001060350688410001410700f8880d06c3d1041c080329011000e802c11002c00d924050030009007032070035004d0034410300391500d9030620300c4146110f48948000101442c6505900c0c0c018010b11614070700e44814040c0005030340700e440303001c03400c021480002d402c400304002403a00080303644000b0035601c1d0030030b40c000700303228101064403100619080700115201901c503020001c40020b403c4414503005610821003d0f031130728030500d4080d0030030b002030123114200342c074044c859556010b180c1c001e941c0064120180b10000c00341620110f840d00050544c40d400b1040008105058111aa210500b1142011020412480008200b2070500b01038100030b0b40c16481880342a030048403175401842e008070745040c01031401c0d542d82646290b2a140e41d120b080f0075540820001c80c2c42c9014040980a202081c2c1c0000c90354194080d5000580e0b8114020000c1124000006441c1c0c042003c2e8855203c0340851003644940044000441383d03510342c01081c003 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 308723093 1250 308721843 308721859
    0x4150203031006111009060612150606050313020d0609080a050c01050c03040201050403080c010f060603050901050a1e0906090b012c04050706030c1206030309090b0609180702101a 79
    0x41c03043c803413100744070603090350005840180d880201d0840504452503054039400e0313440c2c6002403c51414a1500b00d03d0f8030402e00c28180380e0000141c0303801c4079080e80c032120501c6400c0040007403580849100e20009581101c1000d41c201c0c541c01d050000b01402c1c04014180c1d10002034140045401c0390151640440b084003d209030b41d5541c0900001d4042510000c1c0491020b010910018125001610510344480000034000340c180d0185010307180e0a90100c0c010036628401d00410600c00c0c099a54030200c4400148040007220442207200040000007000c0c080e554035a900c00c0003c0c9400c401d1060b500300011f00c81c84e503100c500071069035400c929044003034000c18501411540c440c440c1c4a00c122381000280100519000f0294007a0981041620420414101000070418075125150185001e0340d5241d11403410080038100701c1340d81d0342e2031500c6000140001d603010341d108251a0008084000444001c1c0c40d40a404d900d00100800c0c2c509100f4101028440c500c6049100c078400b440080b01c08031 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 308724343 1250 308723093 308723099
    0x1b0a05010c082a0d03150b03060a03080c100608070501020601080a03081302130e0705011215120f0506070806010f08010e0f27100c0302040f0e060402041502030310 72
    0x1460351401460000c2c0100e80500c0b2403003101c03a502000301507400088142840016886281c541441200985200800e50340c0008035110141642c404010f46104070a85246003403490005041811604c40202445800501505004418002998007001040b02407240544a081481e1906600c1c05041e006100f00000054141400a851990035405450390a05a00c07482c00d03000d040008400143d80200201103032942c2440244580305414070801c0c003504400c0d05290004000a5850590301b80340d50801c242c06042e014841003d030115108402140c80c001c140c0c6c0b5010f0611015005c0241503400340c541013140341600030140f14402c1009030303104520788408000c1541c2444c420f0003003104070500b80c00010228407070280400d410000710551911034245a007a510300b0741c4442d00c60010240c2181000304024000b5005422035445d103420150704090a1000c01c281c1e030fa01c54400c0c0c103102e0002d00e010500769140d55040701d014104034616001c10710348030480a541c0e40d02c1940c03e101010940c803000 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 308725593 1250 308724343 308724347
    0xc0d09150f1e02010612060b0a0501081b0d0b06040b3001031e120e0111010203010e192403030e10090b0d060e090a02010f02010507080403050703050c1b0a0501 70
    0x1c2008000da154072112003060705600c011149040082c8095640e1354001040e5240301d4104507100c98030404001c190310703902900340302c0c40703008a5000f80e0602c034019050248840d11074031003200c81104200200d4032000da205070702d0042d0540420046d04a40300080c08115504c0f80001040001c0589101e400c2c0051020a41103001440c900e1480000410500500010b0340c9000a82d001940c42302d415101003a042c0c54813800e14009403220008290108299011960081c6500e4210300c0440006c5040d50714040038044c01140044c084210594140307000d150140a6600038501d000c0c1c1c0c1883c1e10010441c0050152203003140d8001580400c190698003501e03032503c50610400c211050b511a4002c600e0884101c0301504a4003000c05d8003034413118045032410344c03c2000751040300100f00a02c80128180005883c660800320014110b904100801c004182c02281c0c040d0444c1d80341c90a1136442c561410221078501484600c0030b076034056072103401000d031020248031081c20340803920840103507030352001 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 308726843 1250 308725593 308725607
    0xc0306050103051e030f03090327030d03150e06122a06070507030605070903061103270d0503040201140a120f14040f0c0305030c06070201060f050102061b0c0d0915 72
    0x107040140e0348101b01716400041140091078219800804903401c0c44001c0c150100304000400c0400b0361060141d214900a03e420008000d90120b1410100240320600120004190307443c00390000220310a00810b100d03465613900d0390310003d03c25050301c0f101c44401c101e075041600e498251890001108121a1040c5486801c4400c0c440c1d000e8003c1401601c0c1d69200405860014088001e2000621000010404034021b4a04007200d903d0302e95901d1400503000400141148094410500d90303000c85a0782c100002516001c007402400e00648954070380c40100e8202d840c41d070008264041c041101da4825070041c3e0b0311003080030514000d201765840080e44030100d40c0b00c0d1030f180f1902a00c0101103030104454459071112140200604042b00303403203807030303823031a583c800d0b25100f1070340d407000c0100702d4041d40c281300c3e030000381200300c4103000e40b60f1601c00004d542c0c05014103406045046480c4002008544070100c075119440d81c0e054a5441807800d07030281c0100800d100390700a1240300325213480a1446205 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 308728093 1250 308726843 308726893
    0x4060b0103060b0918091011030f01090509070b030a110c0109031707230c030a08010905090a0312022d0c1002032203020708060f090c0103061518030c030605010305 72
    0x210540405a1700030240da131181024100404601442d040701003109168090b9102d62034400b075055a0720300302420040e0032140141d001c40c40613480c140501401040100f24281103500032010140c598030341044c02070052407000405d11503c140010804e40321601034000b14030703890017501d0740b05140a409400200703038030003141c960000880c01880804a140d2540c4200500011043c00c0c900b0800610a050324603805010b055010a460900402003142580145603000980313201401c3c004003640d070050480c208111541c94620b80115030141c1c0d180c0708440e100d0300b042e110a20040c04145018460a01794042c800740724030740c002c80c24004103070b820710f000300c9000702400d12170072901000081901c440890040780c128118068402c00042d00c402c1000801c2c05040c860144240034141130708424940f580d180c09007414141454020480d80e41c0040c0c11101c80e10b054100051264440d04c1c450802c1182a04010b0410306042004000d2202a40c00103068070300c60800c50313500c02c010412082141100300 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 308729343 1250 308728093 308728099
    0x309063a0e010f15090c050c06010609050a06090503030a050313062c0303040506040206071407181407021506120303040f0203160b03010312120e0a03021b01120c1704060b0103060b09 80
    0x1d0b0030880402150b000c0307400c50020b1f2501d0b504289412440d42d09042c403c0c1c0c06040040d1080304180143d250244c183d000400d41404c00b00181b500d028003090310707405032100d0001804004400079a50244403080580c040743c0c4820100034083c8015040c120411100000301503520064242c8410310100000f140d0282e5000401800503644990802c10030354084102100c1c40450f40000102100b42081158081d002000005403c04041c800140484aa0280011161001c0400e020840d5000f00c2c032050070362105078400ca51959510003250703001c44420258602844004104801d00c5900c0c0e00810307509108800340c8050303007100103001450013030324010803002c59400c000410009185444001080c20320b07041020000940340b1942044554800c24082d4a030040c003030003410190b0620102062081c051141c0040c0d20420000815030302e00d4800e05100266510741e05041640655040341d000342d14030040000620301890064080d01207807000c1401303e41080000300744500c0d600305031403034480c0c05 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 308730593 1250 308729343 308729381
    0x1a25050d031a090a020909040b07140403080d0522052d0303010605030601020109061a03120408030703052118060f0408071e050303070203070c05030309063a0e010f 72
    0x2c400308011510003500c2048582d50030080440d8684401d81c50b240300d540550b0820b001c614020001400010a0b24901800240104030600000310b01d4026940181d010500000c0d40340c1d62000c00035640c0300791000151400301002207040c20040b00244200404030840c01810f07903442030280850011154043c2d046081d007080c0010702c000d82c441c001465104105100224000002c0c0c0c80e4001200c105004032400340720b0070380c07414000d800c00300400904514189019840d2518020039245c8034000c8540080801ca00000c4d00d902c004e075024101003100d9402c000454180c10210030600f40c0d02813800c100c0c210380c01880c0000781440305612403d8840c640184442d03242c048996203441d000b020450066003e102541c04403400301d107003000594420801ea0b00119600c0c6010705001040060640c00241300e40e01c00c20001d5013988036041503500041028481c000c420741c0501c1003801c46035005841414041a10000244882e02a0041030700016010700800c228041e1188030806d039145607901140764030710 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 308731843 1250 308730593 308730641
    0x604030308040809090109060905060f010f11030d0609240501090e2a180d020d080f0c01050c130905060117060a0b0c0105010608010501020a0506011a25050d03 70
    0x40c12a076030b44640b00d071040740d02c0d01c0705400010310740d00c0080e0044006150b80d4842840b8210b452311841d504040c0c202c80700755028850340002407070010b80c0d0942500300044040c031288850b0040082c1c030f065035244842889400d44440701030700100291f00d10041e90b8400301002c0c47c1c8040260b040801650010395808100da810440d11008200010f0061040d0b000c510600c0241c0203002d0811880c4400040c82035961541c5c0024242507001a02d48441e2050344500001001655070002a0401c0c0d43e010510350340714003140ca42d0042600841e1080d1007a5400d01701003000801c0f520000b4044820144000e049079a1a074407210100d420407140340703011503d840003c0b46049000c58034640e0001c4000c00141d0143e46680c00552141c1202104100c6a07440d81d006001d402d4100c01c4181c0500001e10040545e0021500c0d00c99032424184078100c1460120294618404822400c0340d0a16244d049a8002e0401c09002410100d04c0e03c841070704d071800b8204515580511074001c4814a5072949030016082c00 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 308733093 1250 308731843 308731847
    0x40b0f071713020924040b240c0610030c0e0f0a1e090819030c0503160207170607091a0a080903160f03030c0206191d0105010801020a0e0301060506040303 68
    0x14001e0010b0b5840300c0480c24100c01a91012080c0b4810002e076010399032514810089007042c02c500c107600500c1142041c2d80c0d500103407954541c5480b000d604a04141c0010030401181c451362081d40310540b0340340a908200842c80c9800c4070303240200c0344107510440c030440c3d032904030011001d0140e807400003040b1800081985410150000c0c1c00c041d510a1540304103040000d503400c101c4600c49802c80300c212000c03c0013041100c41c540740c14004a034070305042c4420f11005c0001442c80c44020403554a840d06c0545c3c0840b168401c000c03110160401500f0309204018200d1025900c038400c4403620000740082d440800c24540507100300c07102c0d507611012107003054069841034071902d1000701030826034801803045080c0607081c00302800703402d40505040041c0328400d040003800c0d940641640f40542d0b110328213000c80b40029107050003031a0140034001550303800402a1186000c10042ea0042541c2003000116596206500400340c000a40d00d1706e00741405060149400d0383c00394412160300c25014841040400c1c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 308734343 1250 308733093 308733137
    0x115050d0221012003060d02130f14040525051027030302150f130201030e1f20030c03100801020d0c0f0804020f060a02010b18040b0f07 60
    0x1480103285070712907040c40c502c1e10a0400080035591540c0e4645007280c42c03d02c00d5030201001c0e01211040c1c80e240d894008049902446007241c02070003404040700400901c1c8640e0720017403c0201043c000d110889406100e510003030003d403020b031241c0c055408419401961600e00d5040080040c03021400a4070305402c00c4107450b2800b407030100303000c540c1c040098020b88161110000e805490500d4141da42503007030013032a2418850142214010391014803125081541034950b10400300d20b000d582500d82880103e001e0a070301101754009218180c170f407845e004400c1c1c02080344441705540410021125406100710b0910510020200303d02c00c0020030080740c850300055510402001d1300e820020382d21000142280d001d0008034000c031b0f540316a0010925401840040400141e180100c90b60030580c0003d40c4210320244200e120700c00009070810114001c0d0854621014000c1101d01400c01d01200c00045400880302210a00151000603800c000c0708071256002d6005035442000f41c041138000c40c07070b140c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 308735593 1250 308734343 308734369
    0x603171201150c050f070608010b16080d0b180103021302120a05100803130f0f060e100e0d050321071b030c02040e0f01150b070201030f06031a18011505 67
    0x9241d1080f440450000c00c00100b0f03070907002005203007203031400900419405040e0401039002c441004002c40442d4425968025240c104100a41e101e4150552030b00420300c0948050300640c00d8480c07043c5040e504041d8904890003a110b041c81440c903020640101e100343c005006001e030420740480c07800500e80c5c0c80141d00030034220003060195260341e011480c42d0806a0141510016407030140700d640401007424005043c00d030a1804424140710000e00008440c0c460180520b82c0c40206162651107018441a071450180913a00c02c84e06a00f085920382d844018403140c0d1818002c400140c000c03071505130511514055856030721081c035283c5010f610350300a00054003048030840b85400135075034030300c64050a0880c000041c0380034805080500d00395150650400000c0a02840c10012010302c442111035056091a00190112561442070001c251a8201822404c1210541d40518411100f054000c543e440e201c80100c568602a4500380d03600c440148242c82081841005181440600d070703011 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 308736843 1250 308735593 308735597
    0x40614030a0807020f1f020f0c01080a0f150f050301060f0e0c1b06180607020a082a190b010906031101030b01050c0d08100b041d0903160303060317120115 68
    0x1c031700403000010b5107060100c3c41500004043c800d0030304490740401c82100c2801c050005003042e10500380018040740401041d508416481e04c00c20510032090303601044403008541c8190030702c06c5e00c4101071b1046000d103026031402980b810a020a4880000001d00112800a4000f000036a00c9031417900054000c1c40c480c4004204550f004c24003d5403e000c40c0d48500d0071541e81040490a02d40014504100541a1010740d049589503c003c035450004607440200301c500707070502002c10141500010742c40300038001d01038081d0303400700050105140c216105c0d49000700444101070740c035080080308684540c40001c04a101a020402e4154042d070403001745c01c401410028207041c000c040b41c901340741901d0703800c00014001c0710030800101000c90b5000094200b0240c250305180c2041801c05c0c2010b000d0000001080347d00380020313290300040003103035a400010340c6124030780d660510b0060040c000d1800304496039001e6410000030380d1940800c7c0c540c1d8203e00e084800c156440c006410030014400c03078035202 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 308738093 1250 308736843 308736859
    0x140c071101050d06060305160f02101d190308180a0215040e040b0901051303020307060b03031603020303070e0d050d03090c050d0b01050918060106050307051b0309040614030a080702 80
    0x42202030902c541002043c1715140481c0c50701d400a80c980b20650316100c404103015000d8019803441d580001c02490030b04071b0b0140018500342c10251545c10314451405c1c050f0f144030fa40700280d5a141c480254000551003074580789220340b11100315108440c0350080c1c2c00200da10200f04400586030511107545821024640b280c941602c50780c01740d0060754100c6040e40c0c42080541401000e2071300340f040c00d522100c0c401c02c4d80c001019941e0000d403248148140a0f00d419196000e82c0242d40c4c0030300c01c45411307030000641070713141400a19019491303820480b15100440c01e081054a45810186108512035a120000e81054010700301c1c1540100740c5400c050754800e28000e13000c50203458509191b0140c40c00341e00c410701958074180801c01c441c43c000702080c1c2441d070b0300406829580d02c002001070540d42e00d4144561240d440700701c03c40c0c8a024a1041e49070328900041003803a94000440209800d01082da4144040d60700c1d014001010014a109540c240d8402602040401d1581c4007400d00315100414205d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 308739343 1250 308738093 308738107
    0x100c030e060313110301020f12040503092206080c37090609061205151905070e0316181a06030106020c120613030804020f0d03050d140c07110105 64
    0x750307007500200c450b201442d08004440c400c0c0304510b18420640c4074114000d514020116100d10f446000f8038110b038800000e8a008601009030500a55510b038901522a00e030110200618240c0d4414000b1130707a841d50f2522030049090000444d140301c51460250646e2584038070000003c0e00744a4600d13464008900020400741c485148810460090007401c1c1c021490f03904100e519012524142d10540741081c0142c07048001400c00b10b06a6481d40415406041691724400301c00b4000825800880000b40b400c1d080054950300b01d512019020000c3d005c42d600700000d02c21400750b000c3c190103400344214210815034000038140d006800a10000050982c2d180310000c0801c3c0184c1080c0c0102d805600060030022003410098296803000185000500ca50b041c0381c064511240007001c000350401c0a840e00040070f549942c81d880c80c00030b401803c1d00d0f400c2e20490400804507040311100305200e9080010350700c0c43c0051041c540307000341c2415a880307181600d0307542c0d40300c101e036884201c06046c08030600c064 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 308740593 1250 308739343 308739349
    0x2010e100324080d0819050109021902030901120b01120608030c21030a0c030e0d0c1e051e0a0506280501060203070609020f131e0902100c030e 63
    0x103124864107490124250541110754000e5400c14580381d440d860400d40200aa010001900c0d5107469050900c3c045585400314020b01e1004494440202c03107050000025820040764000d00c030004490880c44049584950202d8891080010003230000e4100c404504040c100369100d88444401414404040c550b401514015100b082d030007018031360408206a403000400340204080000c4110030b10480e4034a448010020b800302408140140f41c1d6443c4089819009900040300c41c030908045232000b10709150010178101c031604040355485084108202204400000810025800307000f074042d1510140340031301744025401c03000c91b02e0f01c81c071101400414406e1081f80d0044403800001c00c440c04032644088811003c100f440d034040351502c1c004101465000c81550111a0f0140b40403460040d01d00020b4014402d40307503400d9010307000c40400c00140b982c0c0d600440c12181c00e041d142000258400b1010b080b00c454030000b1307402000307051142190910850040c0036592107410800680b000322004 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 308741843 1250 308740593 308740609
    0x507030f090303050103020a120c0e070207032117010810020903191202060f070f05090a050402040b0405010e04060321020a05060f1807060e0105090604051c02151207080402010e 78
    0x7095003c250b50350014015814843c610f04041c00055210003100392942c2d49854074030089100d09007034038401c4000302d08441d01c00e011120046810510f16a40d51001440503c1951003184490700800c2c3c00c07001138000d10100e44142030489400401030310100700c0c0b03101d901e0080e5000301c0030030b03505020343c940e4444220707044800c106001d03000d0000304000500201c0003270301d045805801c0071480681d00040080480c1c0c01207600300494942e00c2c00544035000300c00499801e8070716400182e0302900200b0085074100400c0091310031a00242d807940340c11b0708114284001c5640c1408041d140f0300108914003c41c1c24041ca03110744054140c41220b110f8049910340d9400c00c1800d40d0700c15441c82e25a003c1c03001d0344059590480c0140c21940c050b00c40c00e0324080c406840011b403e2081814040f0205580380240d4460050b20014040500003074001001103030740c1f81d001846110700720301c22803a03a201501d60503040800e90b080098003299414050300d840b50161910341004104a04120384140e1010140d00ca6140d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 308743093 1250 308741843 308741861
    0x6090402040e0f090109020f01110307170309010f02130b0a1103070312050601030216170c07080a05010c0c051f020c03070303090b24060d150803041a040501120507030f 74
    0x5089440c90070700700c01054043c100508110302e607a04140701c59000d80d84842032922090002d08055020110803000302d4294081d556001d0706101010884403900300b040d4009500c2004080c00811071002146c41641c12401103030702042d1005024a170510902e4500c0e002003400c03000c00c0c140440140da10140d01ca14561040d0300450000306100018038040502d8010980c00c48000d003019401e11894000c9086400e81803031000e00030a88111900220182c5841141c145100000c141c52680303460755a89030741c460044070102e441c0d6207000e40b1303100b00030700c140c0e082c99017954010083c0c02c4610f4141c189440030000c0706043c10390907600b0400074601050400040c0703140e61098801040c0d040560130716403900d0900400b451b81d09441c0045d90980309000c61250918040c0451780c01d602d5402441d0014018812038887c090500c50407000418003100000c0500111154116000c281003151000c1251a00a40c400c4a02086045110300381a2142d074020940c0284107143c0010503031000103000301928080704e = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 308744343 1250 308743093 308743109
    0x11010207030215190923061b06100e010b0f0c0c04020c0c010e0603010807120f0f030c05010c0e062502030304121a01140d110306010315050601030e0c0105090609040204 74
    0x3410500c0300501391512040020b241050141d0740d241919609030103400c6803e41040320751045400d80e80d583d94000756901007070400702c40c030412211441000d50300c0d002503c10b50003c0240000000da4950078081250607208030004072410080c034000c80020700e4010020317085c128000c61070400042d403036510140a444180704020000d428a60340050f00000606181501030b43c02080140458500060074504650310808c0b000240030007410000250001000300074840340311040c040b820b06900690451515010b98020040e03034030f075118180c0341000900302460b000305007404220340488080d007034540920101c41481c55030218550000f401c5074402c1d008406c44029102c0c1e441c0920030501e607a552040090120881e142d4101040e141074410400044c6110b80340300084d080820100d00d4100c1c529000c0503085640c0c658403480d14074507107042d240f540700109140c0800202198440d008880580d086007020388010300500004503010380c082551160000020055400c10b0f44592004000501d540 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 308745593 1250 308744343 308744347
    0x8041a0c0301170a110d02011b050d110a0201081303020a170322170c0304030501060e04062301030312060b030406022d040504050a0906020c0d180e010311010207030215 74
    0x2040454000118031031443c901d540c0407140f00c4001070300c044a89440c152003200c02e104151131510040324036141880c041da0005160210342001c2000001e0655a0003c16441d201042c400d07103e615170303481030700d540c01038001788420700401d00030062102603135880e0f030103407064400820580d100c0159000480d0030b60a06050004100802c41d031070351a49100c4104c45a40100e00c003141c42c5c03180440604104050b035481500003c403031512410800803100210342c08070003072090941c2d912003a6040c4100725401c0d10558140800000d003909088008107080d0b4141003903108990035038400b10352841000b1000e012007550ba860129140441c0c0010750b200d035100720f42c0981ea43c40c84014204c0c0150f07900202d108a01c003041049040c4200840980341658816070300094980e41d210500005000c0c10a005010070b840000e44644074400880d0035000f420164440c3d101a03c0c600041004508040c440d019180c0414001400003454111107550030600520440752010345907000a20402045c0e22041e45803240 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 308746843 1250 308745593 308745599
    0x80909090a150920010302190203120a05010305031209010209041d010e0303010503030412030207030209011701060501050405010c06050a0605090112051c0c06090203100f0e070b030408070308041a0c0301 89
    0x14107048600c05010042405000c03659135030100390b204544034007051042c000801c6210f90744281c1c103031a080078070b42034005080c0800c0135010b52258040c60300720355803944c400c0020750143c6860040310f0403654840011468101e6094441c1001072010f450300e04155020000714080f40d031036000380c180140301000100310800c04030381024215a0038035041282c40d08240010440b0b90f07000701c00d8500b11200765010510a0003203260403800c014040d08000d5022400e000045010800100316168980c0900c000304501500d8130700555150243e0b00c40c40c1d00045d045844a03000401942101e074001702207400120307665803281c001440711842608a10405032030046440244002000120900400220307030040c1c00d080c07a6401012442520341c0a0003e0340c442407002e0854070108503e408035088c60700d08001983d00c00d01004003606070405940300303501c1156800304070005610100c901440e44591142d01d001801c0d038042c0c034010002002503c2550000075288080300003480e001d403003011403900391a078a44c1 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 308748093 1250 308746843 308746853
    0x315060e012c09070201020705010c0801150806060a120f05010801020c10050112020108180f0c011412011505160c150c021503150a0806010305010c11030a030504080909090a 76
    0x41d65203102d8920205201410191051140102804000740c0b0440780316641e443d0160702900c1400e800038000d610700040e0000c801d90014009060342c80c90808441c0164106504403400407065410a51064040144280c207500a80500c0c841c640d94003008180b01072110642022101c00f680f002645035000100c114402c2c0c03051060090040c40b040e41080503504215010015244105000303040c4240200425150348005100310b140d00b500c1d8040300c4140000d4411b00307403204140e01166001c100440e50032554a011002a20030071f4004d211001000d0303190000e81c84035603944880140603c5010040400c04543c00c142c05410749000e80b0b400c070030091520425243d038030705d1145840d04014100b010710006070b584040400741062940d10107900c940740c00d11002c0090404010031036000d8035210000544040109041d4102d901a1000300300030605002c065640d41b280c1c2c000c0c100b03581c00070050152803d0080d884a0f41090148841506004c03080d408079810b61000d0b00d00c01c1c5194084a171620800c2 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 308749343 1250 308748093 308748107
    0x919060b093102031503011e0e150a0b15030a0e0705060405010c02010c051204030b09010609020a020a03030510090525050a0c0b130b0c0315040b1806010315060e01 72
    0x8105005507896086039000040b2664802101d020b185a000004114891204005080c039140f005000f003007521140d1684102c601c0002d0b401c82c101d1402c0c80c44100b440c840110780800e140169004000307076540d80b42407200040901c0345007194042209603d8003110300c40c48010318421301c0300701c60006031071009420301032502c00ca030362100e8400c1134100b0040c0300c00d1764000d8500c50074642c203003040c82901c5d226240a60810b050a0004203403014045000024041c004540074050402e0000030081e860b180c0b4800016881021510300160380599050b50010380710740e000641c419a042c1e045440a92284a19015070b00152070b003440044642503492030314050810060058003441c1072a502c0e010396150f0240c040032188030301600c00300c800400101100300c000c1c01554a543c0c0070745201c10b41d1404020407481a0000d4962240c0f51869240d659040c2c101480b4004889400400c80303400c04c20f0b204446140e0410051401d4101034880c030703410102d00b800c03440b0344003e003440340ca400003c0004580014506 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 308750593 1250 308749343 308749369
    0x41403030103080f0306030c1309110306090307080c0f030d0e0d0e1c030c0204020307113009011b030905180f04080306010219050604020a08010903020c0919060b09 72
    0x5600200010400940e02c40c048500504001e161107440b59205400a400c040011100c03580081120031401503021035507000703c1c010703481140c82c0040c0e001844141540d1380c5c001c80e0354099a600030030118000c50621005840d09050701720031109900b01603010182190499008005050703240c408481d01c0903428041000200c02d6868083c01c02d070a95800503143d03051000040350710002c00688201814898407544000315000703802035650f403c16a0b401425124000240c42d841e020700c0c0e40300c20b0b0144000381c890f00440b85035000041c060040e00052000c0d83c1c05540041e0600c00355494286010304650000c080060094440843d0725180c40240529294481c04517004810002d040140d0029070004007900140c01005080e2079980e0350700143d14154500c60000c144401c007803890303400c1248c001071070351085209a683c54000f940c3c40b09074038243d600414000300581c002c030f803035001c2e1404e080c51003662000401440360300c8107001c401c14208584842c0c00c40c03105044005007500c800d0030948080044 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 308751843 1250 308750593 308750633
    0x90803070f030c090501120612082a0a02040b0d0b0a06030c09020903030f0f070b01030602030105030132091c0818070302030613060b04110a18080705120708030f0304 73
    0x41098003c00c01042c1401d1401100c1c14403111b49140c620690340366021001411130640e440080c40503c0c140444160000f840301444c64079429a0b40c0f04480c0c00010001c1c030070b26682c000f07203860300c0d041c3e080001901c000c00446030801901110600862000f82c0f40c240500c02e49200001c03004c0c10360426604486403500420b0003140104019211901d00204030f6502078070302504103844a40d43c0940312568802c440000d8210350b400030011041c411641d0086040704c0c070403402005048040401007001c03c100040361001030b25034442903507601402c42421036100c0000800c0d110a0f1552001c0303008141040c580c03600028840f0001c000c1c040c1806400d98624044100052000925690021b6990080100b1a114014048500c6c4082100310382101c0e064201c018070030320aa0712810580e1209030400b580650000b0b0a810130b0180e81c1824002d5042690318900150070640c2c02c0c613043c05141840c0c071040708c265106445002480032000d00141141d2420310101642d0303403c080c200020342c020300b1541150 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 308753093 1250 308751843 308751851
    0x109091101021f090503040503060103031d090112020f03010b131508030306150d09050d0c06140118020a11010e06010315110406030c0c0c0b0a1407080d150306090803070f03 76
    0xb070881d00076840f0766203c4036088004500003156160450850049500c655050301c100000071042640101f68040103c2d0b20104001d174044124041018601b4284191960341210042c10380c05400e02c0030585880d410040c0000c1780b00050b40010885400403d0301083d420303940c4002100803002c4254108005109480086003141850f0340010304400e480441240300341d100241c1504400e90030b070001500f550f0040c040d1280d11400d1701001d00382100b0745200300c5040b4500341403201c0e107480c9040c00c9416a0703080c1440e40c8000080d800750070000e40c00072001c1c00a01c01d50035810134020b1024092210a0b40510000d0000c5501d14a0410a0b0a0480100d40c910354102264014044c0501c010342d0704071038013450049501c026894007901c1004000702d0103048d070b803840040483c006284500901102c0d15907038540d00509400780c4401d48500840d0070041c20360001b00607001c2d19207540c4e0088141800c400b481005581da607961100102c40e8803c1c2d007211800c2c4003000b009002900050301031014099410180 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 308754343 1250 308753093 308753113
    0x91e10090509180f0303010b0d05010509090a060c020a1b060e0315160c0203031210060302040806040213060815090105060a2108040b04140406060905100507050c09010909110102 78
    0x785420704014591283c03560000c01c11140380908000700420304502905480e603a5840b01c40c400003945c0498082c541c010706101c00000d40d820950040d600c181c0115000d01040012070395014050400058040e0852040c881250041981c2d0070003200340840001c4203402c0b907403802d00040e0180200c0c0d5003407442030b04040801808104c0d034031700d042d034070400c607150429a461002800340e410750650350000c1e40500c804a0041600704074110501d020703034000006a0201685c40324220301b603103e940030385400c0360040400b143c0103040440c0c1e510546820380e84085400340d2500c00040c64420a081004550400c282c240a0305610a21030250440c03400e43d0184500c5040c84c00034405107000c02f102407500702c031100c0184240420001520040c005680b49541c1ea640d9a484c00d04641c040d008072030348281d1034030100142c0c00307009509a2007100c00c05030400d00c1d402003051094800380c002200640c0c0c1c074018581610f03500d98038189550301a01186800045119050500071801c0404070328860655209581134 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 308755593 1250 308754343 308754349
    0x907060503040605040812040302010f06050f061c0912080f060f0f1002100e240411120a0602040e0f240607020109050a0e04050f01151505091e100905 66
    0x1d0b03601030340007103001c1400c1c1c4a914008501d44214002805400d00310b1080c0b204140d419004082411000702d820310960751120b0402161540e1105403991154041090300c0b46407848428645070f90001781d2002440404076156a0a0500d10380100740004100000300300201d6144030455412580c1550120480d840010102d200301c03e101407410312075444c04814144a038420000100844030b403034818001030000608280d502c0b001e408441681d281841c1643c41054015a0b0991059421942903580100070b5401d03c0b4159141251205d03442c06603501440110303000740001d00c018200100044041e107005522640035040184c00e0f410080b210340e080c844540070001d00301ca00d9070401c072400c540d03810851005a03191184c540c00030f6008000c10701c0000b0031885c03e9400e103101d903008205803044582901030b224200d4100070000421100008405e0110011030803c1c0e0b80710080318203191f0314000c240e0700000c011030803421340311440120070405640c1600309001060343c81034060410b411520305041c00 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 308756843 1250 308755593 308755597
    0x14190206090d0207140301150905100504111e070c03030807030e0102090d020622030f02040b060a021b0d05060f070e0411070f020303040f080f071203081b0c2409070605 74
    0x45c3d03902d07400b81d8044008841c3d6080d4070405050340c0d9a002c142109940e02e01d4080644003c440c1c91080001c10100003d482c02c00d0300502b0010505030505034a441070700f54640241ca102004902c41c601000e101d1080082c44003100000030b1402604c600e2483c1c5028a030040c1501e10700030f100d022590050240d03c4290312142d031901005a0f04a1f80b0303d4403a0360483e030b000c83e0000181c140d03010340c525512001080c03201440c3c021034480d0098600340044849942440340d0b52041003101720040c0d0101c00f18220b90b03c5000581076400b82e0040100b000c1c440f19403500e500d018400d0f03a103003000c4100402441030b00c0350000c03001008140152003d000702280d01d42d0300e0480e40a8140c002d852003101c145620215507003841184d0240c000c280c0018001900c80440030354030b50312401005124865401c002c09c203410842040489958036664900c4140e40d00b24510228441d200d901166411052050110021051018449001c20491004105034a0311100c824075440909900c10540103e00306000c2c0300e6002d01 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 308758093 1250 308756843 308756849
    0x1021b01030209041508070603020f0d0207111e01090509011a090d08030115081e0103110a0312050c060c031302010c0809090a0504050618030a0f14190206090d0207 72
    0x2401400100010041e070280c03148610f0a0f41c06440c00c83d4198980c110048404143c82030071040740c5c0499140c2c0c000f42d08901c140f41c801041c4800500c40d0f9001548607400170003a05108810428441b001c410214551a0410440203420402d01010003010359121100100a040840d40440207500d4040e04241000703043c1c4504610781d4001951803034a44898505507500307540410901c3da250b07514865101000300c0126140300081590300801c0c10484c0c103002804001d5503081d80c42c070b0940d03e160340e0351740b21140c0c0c480c803c1d030020122140000490003038000c0d4482096561101c0d0f580349a48c80c0b019040c04001040c812003900d00b0700c2882080491411441d542c0c980c20309023144810b255042c400043d000302000242c1c005403410400101204a802c80307401584200101c0b80c0070b450b10585000c600002c80c1013071106600501201e0180c42c441d10fa4140d0b030003803d051480c052100002800c000350b11840c0c0c192184c010040501b05820b5042102e244d0100c00316015101e4003003c803000940380d1410b48 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 308759343 1250 308758093 308758123
    0xf051e0601031a090901020a1421040614190b0102011b0e031f0b0a15230d020c03071a0403090603020f16060605101713031e0c05070b04050102 63
    0x4038240c41d55403c40c0c00540c010000100b10525a2038000c072000c1c080c0d4040800c0380c0015403089010540002d00d001a1400d12400880440002c20f4850391982400030007403040d0352107511800264680d00e0102c800c03a0045080d8005aa10300c5e00b100903240550303071021811411a07141450040503480106501d2080ea0598644480b40d02041400a4a0408401903d00041005802c8406484256800b014240780e003512010b548543d0754042d40325801450349680007040504003040d90522540808904100304260082d00300801d03106418100c1e04800d44400c02d90707000044e10401e02140308511000301200300951000e500e4143d0b0020008441c2d0702c20035040c1500402c06205545480003500c4000894400030000b50707515040803c06004d0500c207803800748104100018486101c0c03025210300b0038114041c40001e80b00d5064966113090016030580c10070480404088200d0440c0451107050a140da41d8500d104000341000780c104905980f0000502c8820003080000c1e036008169040c0c40c00c048 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 308760593 1250 308759343 308759351
    0x607050a080f0906030a06030201120509100b06040f030615050402071208060406150503070909060b040b0714060f01080f0a02090a020304020f060c0102120105040b0a03121803060f051e060103 84
    0xb89500005809404205540584040300f0080f0350745482d0301c0039046034000d130b1343c1e44002d00c25a200c40003120010389810005401001032203001d504140c0040c6070512014290a280650706e20300d4032440e03007460b0000c4800780c0d00d81d5148040507401c141f03000d01405013161300b145050030b01e03500d5001612480c03421100f0b00030007200003046591240d002000400d1604000400d0f51843c210013001507000311401400300d0744204012031115800e101c2c6034141d810041071140b0302410040c4c154800c0e00042400c40d41c80790441c1e02c05ea0200c50501c1035901030040c9054440441d4100390500b400c0c0415041d039a00c031580484520b2000d40c0d2900c1c09550401014000141e40383c540d0f00200e04460f82f00c0c404070760070803800520450b44041c15802000700d4542c0b00c0000c00f0b141d0300e480800040d1101c0d030b9500350380104500b40a00100f651209000d03060380c21424118055441d40c09424884140f41d80103558281d504e50091000410300d00030664455100034564400030301c03c94003500810400b034401e50406a41d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 308761843 1250 308760593 308760607
    0x250602031c0b03030f03070305070c0209010506131d0402011706060904050411041a040606030b0f060c190f02040b04050f0406110c010e0a03140304200a09020c060a05060607050a08 79
    0x8694051070b180e91001d016aa40c9521280e80340d60198010780b80711000a16000c001172035244244000f0102039030080004c042a4607110811940f40c00030300c0404410a101240082e101d00c102c502c1c1e910300000c18288018526040c00050100501020583c2d00c0480c0d034420090340b60360710000c8486a203412070380014643c446040c010380520ba402c050b00d4110349400194406007900200160149000b103c0500c00d058550404a00791303064120402d400940001c0c01c54058980030014019140b0580b040f20050b042207a4094800310346194140e8200b41480e020801354241409011040a0281c40910507414501c0302c9003075000780100040c0145580d01d0301c05103868400011210200e8084009101c0a05103a01d403035254203103c3d0084003c10000340000c001030102c0070942c0e1113503030010240c0c106071010708400d0b201032100d964029840040154041410447c3c2c0c80900502c078203500040c10507103012000c4104540000d00150721600c400c0c0007800020b00d002400404040c0d1100c4c100ba26058 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 308763093 1250 308761843 308761897
    0x6090c1e09120105060406090c0203031b07020d081905181e13050a15050330040305060f42060403050604120c0201050a0318080c25060203 61
    0x7803065016031000c450450100c4070301054000c10702444089804200d550741e20440c038170484112219000250b003040c8001410812960300c2040c280b0003000d031a91034141241d0000700b8030a015a81110315200228030324411000385600111100300c0741c20420320300502c003440c1d003403031004a40d801481000f1080007081410143d604a0252500c0a04201c00d00102c01c07180c06e0181c0070480d04240040e2902c0b251a01c20b48031800e40000b1610080d000e024080a105104c000481c0e150448101d03104211081303009a020320b20061004601540192000f4142070b454802180c1000c2c1c2659840c01108000443c2034440c011405200b000001248810b042a10703441102c00058181496000038007080000c180280401d484d44103500c00e40d00289905481007089c3c13070307007840f174880070303001550038404811494002d0b8800b41040004910308010031840342e542da2403e62000c00c15405036040b160302070305146202800c10801d8880c02003486c42075810400c009507680101d080c0300d06a1010001c030818084 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 308764343 1250 308763093 308763097
    0x3020306220908030a200909010605070602121518070807050a02010608100603030f0c08090f030a0605150a06080606071101140403030e090c130b1b0609060402010806090c1e 76
    0x303684480f9503500da241450121008200c030310300a8075010748080900000c0600c04084070505d106c000c004c03500c1d0b6400c2060450b5650044001103c806608200c50740600d07225140d400d00c900f078005038a011500560b01406207a218805004400c105020244007a603904800f065601242c54940647c0310038241310300702e014000e65400704815006814005120940c0c503080f400a03680079458600d028858040c045551420046014041c170340705019036615403078092051015000001c2c02c40d02e140c000741d00e402c0202c0b501690f031425214041500c80b240d078100b0825882c004d050364141580c0300d01d84440481c0380c41c4295880180b0358030741c2d01c40f580c1072a17000d0180002c1e1409040710142c0c40c1d907201d24010301110070300c07902240328410900010b02400012011180d212074062116040c10386800609165a0815104200e0140000040c00303070350081000380c2c0d031040b40c400005009505040c000948450000740c84180642c84103420400300711b0700181110b60750310350320384d4070440802401c5c810f02d068 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 308765593 1250 308764343 308764361
    0xa1401090f21020f0606060d09150e06090a0f0b060d080403200402030c0a030e1e0307060e060403081810020414210d0c0204020904110a0f0302030622 66
    0x558001c45500c05020100251000700e801070050200708900300d0b44144da6451803500590801e601100004541c1d0030108003401d2200c00304803001c00c43c8002541c0d08201c180b03021404c190007545d183c80b00109881c04200d46600201c040e00500410ba06688a01101511081001d80810420008520140c07605a03848000540100d1255200d588070f01e032251110b10800d2260014040a00050142d46800c2c0700311303401091040b04e0306141482c0c208055014140007540104c00303014100382022504410400108003c2c001d80207036680e01040c0c54028200c50048034503031507660040b0104400aa088900301d5040002e400401c1910f4003904101850840711000209115002150010b401c2c50031117030b0800031a40c100c0c2d085440080d5001001c50f8038000c0c880c00c1c07109600004400e406036004006402c0c101d0b001a1001d450300c000351022500341c40000080805941d070000300101a81d9114070111900356442c5415440c50030328500280e00741109203450030b0104512140c4600c0308007243c1c890414 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 308766843 1250 308765593 308765603
    0x20c0105160803040f0501050a0501260705031f060909170309030904090606050108060f01020318062206020d090b120a0e0109062f0d1509140109110702030a140109 72
    0x15900d80345c44c240040d440b0035001245c140d820080407617200a03050103214103a9018012a0f00200072071a440e01994003c0d2005c07813814006e80b100400c103034074140300a00d00190310400021701e400c0c0c0c7c40d8105044501e264061030380645841d24880003e11008400640c2c3c404020015031a5120210594203610503000b8071903005161401e0201004001d40190048a2003600c440c0304940d242014483c07206074031448180181c000300203004032a0440340104078106000740c9403a041c00ca02404000e1001c1c00032022940e2008100c108009045d41003211140d12031481c80e01b280041d1a0030040c0c03060b402170350002d072501c043c01000150359140301e0707000108448524009101d6a02d042c1480002440002e07070020750781c3c0c426031283c1402d000780c80c5e05280c0c0050350900c0768502280501040000c1004078241500d00480722000548455140180202032108041c000c100e0b501d840301d05400c403000c0000141080c2030610448000d41d078049002680d060f00011914411461502c9241c014151420001e003 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 308768093 1250 308766843 308766847
    0x2120a051b061f080619050907030f0c0f0602190204050408090918060603010e0312070c1203050609071e0f0e0612010816050a060c030302040e0124090501020c01051608 74
    0x84140750303c911031081001101050b4586910b420049444070000c890b49a05034400403100082070080d5800766074843e1a800c11b45000d41c0d265030b9230384400c00580800381c8040070301c6041404564540840b02008028a000410860240307034900e591100914a02030311550b501c40004080c003000c03004540d440c010041440000b40f5150000440c64000480510007505c20b080001c1c1c41403d05214441c4010b6a110056080001041301d001c0c000e18000d04400420850039104030000c1c40c40e40c40700c0d802c030300e894902080a00d8a0f400f40001340c078000b84030408000f0120b05103141d501c0041c1304000c4500f0b0a11700346019401015059170041c07420280160400300006050000c069004480380c141e6a0302c038155051142c01c181c1440140106008455000600d648200003090140604100d1203100b820301500302540c0d0b035540600d15100760300400600711100c41c1103a000942c6c85c11600c0d88180380c01c108000c9814400000d44d0b601005200302e06101000034040d000c070311141d080003600399128148503 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 308769343 1250 308768093 308768101
    0x60305030d0b01030507140904020903010207081e13030b090703080c01150906050f101106011401020c01031104150c050d0207031b150807050904050114010f02120a051b06 75
    0x1664a920010319054801e01e8030b40c84181542c845c1c028540142c9081c0d40d0064041c200ca90442c805030720090078254085c1c1c0c2081010740c80d84080c005030841c28012205591107229606003008240c04401940341c0c0281d0401029802d85640e98800b015250446101a141e5a61303265240c6480503a400140101e81301103030401052405401494040e4600303100140c0c031554074812a02030750300324010a0b9101403d6503118600c1d0822a56900b6804981c0c03904040441d080d1000b5410300c1b0302070708140483c0034107640020b01c9580420020b202030030300703180410100b03c91b07410703644980c0518010010303210000019501030a11400c141d0301d0316a0884162200e83d121460069520038141c4021101030ba620258803080080e19101c0d1822502201516001c5200700c0340300721800324009000c4020301c5000d00000c000d40c1c50f50700c642c2d4040c04080b052110080403910014000c11882c1014400310b52040d0640400c0c500100c00703440e00034806003000c41c1c49140300b617540d00c400b41e02d0200490040c4903401c200 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 308770593 1250 308769343 308769353
    0x200105100819060c2d0e030a0c03140a1403280203030103110a0e070c02010e0301020a021b0424060f0f021e010f2901020c0d06021c0603 60
    0x590144800484151410707907245181502c0301e805400860521605241000c0401c882ea00b16a80403032841c03500f04190300780c0b8001003044075461409162500d035601011391003160025001c0109a00c110024040b83d602c0b079561030350403002400005c280c2000f40c01ca61400442c00c00c9071807552071b030040602c010004104034003030341d80d04100202003c2000340c40d404018000003105980c02da80360350740514a180e0131600d942030301a82580c01c564000c0d0449c80005004c50045808034090140d66542c00c2e90b100c0c4c0c50000401c0303421445403030752280e481044103c13841c50b000500041011685c076007540c12650004000350082014030340714009411a03014101420840050380000c4c1c0d40592600581500342030412203409202000f11805680801d184403200c00b1404d16142c040d507003141c00443e2144401c1000c5c4c00740d50f580c3e2a02c0710b481d0310103820a5810300d5102905550041e0030302c01400c0b4090644001000c0401485028101580c0000c1d4240c940c040480d24200c40303032400d101404029902c1c909 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 308771843 1250 308770593 308770601
    0x6010b03061e030f120717030c040303110c0a080a0c06080c090904110d0f0c06020a15020726071a0c19110d1e02010b1e060702040c030e060c0a050f09012001 69
    0x82243c45c0803503107c01e54810482da10a580c011240d501440d407d080c196a81a1009190703044070000e240700300b0420065590703a550380b0002070540d00700a03107020341c0a85084080e452030b030b070006030601900c10100040440442c1c242c0c1c0030f440c4102d41d0381e000d589850402c5000c0c0d030504480a0f41003036a80d04040c09002e4a040700012013803203564201029940c4440482e19032481c140300419141e444403210001260b0794014183c2d0f20f000d00091036a0b080d00c044910200c802c14600e144003c04081816001c0c4102025403002e000f901001043c10307403501c44844d030301905c101d00c0030300040c41c03405078200315070b07441013601010303411046003100d890f070000c0540540b8070040c141000c0c00400c005002c05107902e20601400c42d45030303c0a40316010043c14100d03c8002c1c60400b940c0c242d0042e034244034000250b941c5020303000301284e09480024010b14040c000b03500b458402083c44034480d0303007000901e100a91110444010f171131004145600e0f00314480c0100c560341c01400326003e0014038420b00d40d01000e410346c0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 308773093 1250 308771843 308771857
    0x6030c0b040e0a0903050307110c0918070b120a200301060203120901090209040209060111100c090b13180207300c030e0904031106011706010b03061e030f12 69
    0x40b80a10540d115030542003030703407052034000b40040c40501c04101c00310700440f0800013010892064603c2032007901c0108050bc881150a1511284c85107c0c0d0107811405102c0300d0040c240f924085885e1140f5401d14194525002d01003074003480d681ca190b41040088401083d0f40310107200303881e90703580d651141c009641c0d410540d240c49903144400041001001c052281144042e405004080c0da80d81c3d940803c400e458000b8070740c0341485000844c03081000d100b84904200c0e1800314030001010343d4280710003465625560403a0b041c411080264091f03100c2c2c0c1c5881e1100312030010078000343c030810325000603010f4043c84000414031540c0300401841c981d01c140310a1071004171801d030402429860384040312507000001015012646d01400e1144034102600540c0d4894000c0c1440e60640c060101a1740c6040341c00d030302c41c040d88080c02d4021401c41d00c01303001c0c540c01060303c0f20040d8250701300440003421602c01c00d482030b2281c000400e406101c940702803101c481c001c40c200c0250384031110079000900060740516 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 308774343 1250 308773093 308773109
    0x608070e0103061514011101020c0106061805030d021209030c0604090c030b03010204140d020409020d03091e0f060c14120702030c03060f0408070507050d080c010b03010c020c060d06030c0b04 84
    0x2c1c1900724025209541c1340c007210341c448070f10340100c80032100548240c481448aa41a0b5408002ca0300c42c0c2d0400340680d400400b481d940c0c2030743c58542c02c60038050450039900300038820303080000a102c00310781c0003440004404040d80c0346a90744000c140001e142c24002e5911a0700050040350004220039a648450031907881e945041c043d030700c08002054200c1c0325074040e8020300c0684000c0c080b10b40c2800369480d0b0640d84003034000680c1120580008214036500002140080c81c01902070045589000f06401040c52480b40340c0d41190030a4a0b00602e20090b004a10800a4042280c0c081c04900080800800004000d450800b5141500107426501c60f090a038060320441980319514103000031124031440981c1c3c1900c0b080d44540e910320f445a070000e00181c500344140a4080703030b5a0340c1e03da0030300c3c0708904c10420143d0b1804075600d5a401c0da5a182e2035a40f09900d03003502101d0180c0c02080d2a031741d801c8102c841c40e588204182003100100032a4001030000c010300c04010030520601802003042d140e2013 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 308775593 1250 308774343 308774351
    0x50a031208060102122b0203010b09120604020f100512180d050c0717030c01050901140106030513020405071211070201020105011e031e05030705070e34030608070e010306 75
    0x300b0010390361944a1904983d158904000006076441811030341400d000100790b0304a0340e43c20751090078041c1e03007003070308a501c1c070320400100002c0503c1d140841c0a001000200034051074501900090502c141c890440c41c0103000400034076100c144980304455680344c0c031003100c0c0d0850401c0c00c2144041d0040c501c01035107074411140300c004040e0140741a0780c216013462004000340c0e81840c040c0300c400940d0421501c2603120038852032305201030a000d403e02c102030400000404000c00c5141030f900389410ba003c02c040c5840c14091001c014071509001c0c05040e01503802190545030484104c1d0110300c5e403800c0f2a0348524002d50021041040d07402440058001d81c0284801d98031030540d03a000caa10340041600c030300b20b041c1b4200000340f070500c0100c160010f2500761032008800d984801d81140c0c03111808403401e410070ba20a00562080100c03480d00900410840707003015030380c140c030341da203a1083c0c41c04448000c88200c506180c503807081d003004014003010f03800d5845040d55000c5480e192042030008890240c10 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 308776843 1250 308775593 308775601
    0x21306030506090109050c100207150f090509040305030402090705090a0f0504060e07020712020d020d062408030f0d0902030a0b070e0d080405040203070e062a01020304111207050a031208 82
    0x14001c071700546412038003074070009507800c08021810034428180015405012000100f007280f10303854801d40b0019464250310340c0c0f0002c000414000741078000510650441c1d05104c0070030787c01415240c1c440e0b8182d034141d10f80e441d4001c00340c8040c0180e246940c0d00111803003000c80c40000121050307040782c0e4280c0e014401d254448000041305102141c00c440180c3c050001000218400b440304415180050886c10030b2046980101d60011942a0140c0d8440d48413603c000381880a10780100c401c11844100140d19410030ba109c0d602e91041079500042980041080042c003d103550001020340e60007000c80311514001d01e40b45448403401c4510724041241003008034010f06140d010480002d0380412458602402c5c0000c0000030740001d0200401c000c05480380d10607541749c01005184009850700b4052210000c0010804051075412900389180d0044c1b007440002440b045d00101070500403515980c551800417409880c3c0101544102d602c240517081c000180094428141c0040303589946041c10344c1d035 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 308778093 1250 308776843 308776861
    0x61a07021807120f06170d021f0b03010c0e0307060f0c230607051806090a12030c05161d07080a020f0d1416080c070305070f021306030506 61
    0x16000000e50012500511040286240160141e02481c1801e14210112500055400f190400704004c0e02d1955154030604c01841e018903006030300f141800060583c1c045e40d0000a4560b0b800c1c1040007030000c0c40d02441d9001401c950404011420007078001c00c0400c4849138028004007250081a0003400b0302c84010801900ca102c811191800c0c68035041c0705608180e50382079a41c1c0c848103001e19441c3d410034401484010500c04240158041c6d07864030b4450050180c503842c0c001030100c000d03100d007904004a41c06901c0303a1100108594200c1e042c07100100050409451048007450010200d0040c0a180514500e100318111300352440320b10b0008900c44400007810f2180f1065138804086a00d01001402c0307130240341c00804940080301512400c1084800e9440240d4440081c12065140400200003024011206a0f5184016490100701a00f40305401d0b41403442817a01c09400c0007400503030002880711034666555010707405024079400e2450500c1b020000c091034041114280200404181001f03 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 308779343 1250 308778093 308778097
    0x306040c0501110a11102601030c09060e0a09020103090b0c070b0f040f060c032705010b01020601030305180303090904060b0301110903100b03071e061823040b090109061a 75
    0xe44d000001710803000c10102000b07060a5003548201c10005030507210a00f9125698000307030318086011003c0c110b5410743c94070b0750750304c805074203c218500d07e8a10204030340c0c41c1c9006481d800c0004460001011405400100c0c080c02c4e04201c080c001c0d5880005001010030480001d180b6107004005058240e220048a280c0340f000c15035016040f450300740616008104207501025220303180e418000340c030419000024951100000c80308031012090706c50038080c84030a00620040752000d01c0a0007507903065650183c60f6004c0c15070440513106140100002c03d4508100300c0d807203100003c2c541c2280349050318005001d060034104460103542003500444044241c00f060b20340e4807200402402c0e401511200c443c0040640610180c3d0510a680c4001200c0034a229040443c0c95a00c0d0b101034220b040400140480b00001400c25450242e01740410500d8070010360a0a0111b4040005814280040018018003040d24040b54000110400040d0007036081d40702c803017181c0389052800d030900294202c0030418 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 308780593 1250 308779343 308779363
    0x10e060301050603100f0b09040e0f0a17041a09030c030a020604050d1e0b220f060b0301091202061b0903060f0603120d0b090a02270409020306040c050111 68
    0x85001800180200e2400a01940d4010403002c2c1c1c591603a551070340200c14290340e42c0d00c0710b5100c040005800ea1542454010300c904900d80d44010035200c0c8102c10b010396510302d0484040e00c5020035446501c40341f010001100c00a00425818010f0710744c200704110140d5100c901654880d1040c000c40c81098200841d24441440d001003803030742064030301014844945100401141c01465250700d400d080003800100c0b0046030302803400814246040001481180705003c0661800440d9010100c00203034205002c19249a1210000c00c10a0b92440464007406800c480103101e005212680d041c043ea002807068070400040e401c200200c18032406240841c07141c440d0090705a0071040006494059040140e0380150340601140c100c80380d00c2d40c41910a8000f1a0128040d42d00c03501401400d00d4015000d50700240241720841c41c056840301b0340c24480c1d24400a00c800c410500700102e4081c1e40d15444010165000b509540162a1519091411005a000301404903c1c42d0f103c10b00d81340e000190031401 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 308781843 1250 308780593 308780599
    0xa0e01140a0801050f150a0b121501110d03090c1d0f0109020c07090b150d020d05070f0f080c1309020d1109090a05060a0f140f04050919080d0e06010303020c010e 71
    0x646d02c0f803000c0541c28001d0b036143c0c0c540060001030700043c0f0754940c4000385102112040c8080d450300744050340b42003840c078907070b10941084101b42c900100d5500202d4000d601c1045800c000548852915005205100c25031000b00c5031103501c4402c1c60791078a40441144149405a410040d503a2a031001304100d02880c0003000007680003030f500b44903c0d0003a5000d4905c01d08014003455940f140f0102c141000ea1016540000b2203030082181034400005001d210740025040c04c0883c551442e0540042c00744204540010421064074046190103c0380802c940016441000d4108003035201d82000c0003a52010310500300c01c0f46000f1116041042d1081034400c91400281403240350f0b200d40c41b03401c01403d40584038540c030a0121000048a600041c0440000c0040c200c2c0c52024084810400c144803441e900745501071410142001802c2401207428080407a10224268000285040001e501d0060841c1f802640345444206c4941c2e450000704c0f203040340d210340e08881c4003041303c0c40110303091510140401e0b0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 308783093 1250 308781843 308781871
    0x30f04050d08150d06140903071a07050313060f0c0e0102070f080607050a0e0402070c090f0b061c09050102040621090305030711010f0510090e0c030d030504020a0e01140a080105 78
    0x40289460040313a08210301410010031400c0d481218004805000d94401030305a10009801c002c01806025048100004540401c020714103d040540139110007081880e80c40b000712003110811500361303c03120002d200032008200800400074080c0454a103010302501501c2960f00008401140089000c15903002030041c1107561640388082c3d40a07040034051400784207000c0041e0206880d10310242c04020f01401c0614280791808010200321007071803007202e1410b42000170314002c94035024100c80f20b050741d85102172005080c40c00040010b02c02c085c0c00806c0303035000003400656980c2c030407001c441449951443c0f421200c007052401c41203900c1000001e011500c00d00000d04200c0c0030ba03100701046401c05001141107a01f0100b807500b00d90040380c4500b00080c070750105102e600038500c1007040c0191144010f00303e50740e00380d0000365174091a507980790030592030b400080c04540b00c44089600905002203c02150358598100a9603108036070702c418041c2841c10380002d85000e0500565001d1082815000 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 308784343 1250 308783093 308783131
    0x9080318012310080f0106090c02031905090604090e0a030324030231141803040902071109090a11060301050f0f0103111318060b0a05130506030f04050d08 68
    0x4010001c0041a250f42800c07045030020f00b10805000c404452100100001030712402c1c9030041040750081ca44078800c55009210203000c8104046004625840c03d040107521004034100003000741c815a085800140e00300040c003030020350001401440f403886600c080c800403c01c0d030711345240844d180c2c280200240400c081000035085c0300318440c014280032131310110903505110f40c0c40b80007180f054410304041d540740345c0241101200c8500030340003050b000c0080462002401c00f103599000e58018150000d034005004000c022040103690502c2502070126001440c0201c4c0c2d064407501101e4007a2a250300c2004034103c0c5107800303021207050310300081144002c44100030502c03151040703020026040c5035490010746282030103c3c0241140c604074984124041d41032980c140260005c440500d00500d00b8540c0a106070010001591280c000a1900a48900000d07a007280502c8041d4000760b0082030020500800c50404600203200714080c0003294039890007560212002e81040b100c81601401404a071 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 308785593 1250 308784343 308784401
    0x515030a0c020a0f030c0c08030c0a1401020721020c010c020a1203030b03011814010204030512031009180b09060906070c03050c060906060306010806070c06090201050d0908031801 79
    0x881d01007151045a48500d450790780c2e02407a4550304010f0300400c882d854030380104086c00d07544a01400040b8003442c14100e544004960b00d010306140104404501e11884030400801d40c141e8906030b81102c2400a94007120781c0c0000740d0503040d6141c1e0010702032011061050b501510f05042165409800c1200c6203107001d101e4402d821643c0c50803410191242c110105aa801340100c9448040041c07070745c2040c0c191860840c40a00303207040c0c017040c1e0f42d005102c200082500400c2c4c101018560031416966030703031128624030a41d8215000341280c00e10b01035010f62811055905030150501c21403143c100340d140c440703030705540310011100c00f1390742d50180e00010f03503091140f1403c001c000e10904080d814075038000d903500d0038071000b110403141c13641c8a14208040361400704805801850b500000d80081d0808000007020340710f402c071010303006903180d114003811079100e0821100d0707540c0340a070104400c03c0b6500c0c00034519401910000d100c542c0150480407403403030600c60400000090003400b002c1d00427415030 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 308786843 1250 308785593 308785601
    0x50607020d030c0c030b18060f1b04030c0906090e210f09030601140f0909060705030705120a33091d070b0c010f0507051b0709020a0512010515030a 65
    0x1c02c82c00c00803001041000241c1129900c00650b21a185041c3c00340b13007001d88060050707a4540b1502c15540f2000c240035224103982c52058000c24845c40b000b80007240e18082d21804d115aa10041c4019510040020312a54992004040e140c2c5132000344280b0302c000440e40e545980034040d010224a070369a8185c4000d5904000303104042102e50380e90304003e601c0000a00301034090b44140300c079414080b601400c41c0303010561413044020480b0307090410b0074400031090350352378018200000d011000000c5080b1500a9066030190900d102004000785807151817030025103d604d104e0b280c5404024400040402d03070b9201a45c25105140141445915000d5400c0180c02c103403001818043c296104030307400752014040b1f2006002c00c81d000c40e982d540103a90080c01c40e49401d40054602d89403000344603040760312400305d8000120b002e20458508141ca032445092507015031000000501c0050201c0700d50360031130084c2606210040c2c03800074980c0d0740d40610409118003406d08180d007030200001050342c00f550b40 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 308788093 1250 308786843 308786869
    0x30518030705040603050f0111031012020d0c0303030b01020607080c1c02070803041208240f031507020a0308100e070c05010905070627050603060402073f0905060702 73
    0x3085600711551940481d00b103c0c0940c009403600c1e0004580c080e0180ca090050603c1c40c12920304040c40c5203004100840c4621541c045d000380a12003d41000c15565a04070120f4003e4002030342d469165643c2c0742c041c004180000809025003c0d0740b0001e440140101c444501c140110480c1c14602124074842410b0f5521b9050b4a90000d42c0c2403011002181710f01003c2c511451054140b440c18040160000d045070300700510240003003602c51801c02c132215070100d01c2c000314a42924000c400d001007500190400500c8416404204116802c1000c0282d0002e13155a503a400307521000540e031a003990741c141c40c54140c02401200856100401c8605200e00c941c840c03580d0240d000007405501c10b03613400b404d1003da90700510000d2650900300b50310200c520300081e5109018501d030344400e440d1031b01164207400001d10a6110b81c0d4086070340c9080c00882440d0107440c18000e40300d0400403002d50398191040300010100b0306a220fa01c05680d00c1c29000711240d1302500e0004140e2420200310303608109031102898 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 308789343 1250 308788093 308788099
    0x7020d1b020a0b0a030501050306010b13061b0f111002070f0b0307200106031103010b0d03210f050a0e0d020a080307120c03061707050901090b010e060f07110d030518 73
    0x2c2000610110600003a02c62a4004e917008162949400c0c200342c94400103801080c4441c0c01005200080311780301d81e07843e08503403403420302c11600400c9645807030b10340d2150200074100000220951040210b8a112543d103500100c2d00001881c01441b030403680e400c000e001b900b010044211050002c0c16842000d1a030201c260300d0417100724050311011072030f1400ca0b811404c080382e4564405000300840c4524090f003c400950080144801c0d200004c1c071045000c840140500240c0940741031800d49804009113909124402806501ca40401c501d00902c8125a5041054070f0070300c04100c61b0700080703100060700d0f8403030380102070040d4151580c03d803950005d003c040134070030341112080640b195409880004a03a9460004116207881c0751402d203501c00f040000c1041d00003400a010f1691107080d201d054401450000074107100b51401070b40c0d0b2541486101c0d5118001140603895049101e004003402e61150181d058513070010310611410024194000b00407403c180006000d82d803002c894188958002 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 308790593 1250 308789343 308789359
    0x81f06260d09120b09190b09070b0f0a080702070503070e0f09010b030a062f0316090803160c090204030b0412080f04020f0a0e0a020a0905060405010504050112060e1e07020d1b02 78
    0x501046c041360030300c50f00c119401c807101400c0089000d01441000f00130100780490300d14109c42001c046000303100c1d00442c0f038140310304100401d070802c0c401c12062000c0c1c6000f0f81120103143d25540812070402003182c010030001c40a03c00903241904c18001c01c3c40d11079000d002066190555581c40d4050030403c015400b1400240020b0140400000481075000c181c0d8200d95030f8074227000e0b03903010750344450361b042d582800400d00c010850106c00004607240414001c10300940358a141c54034504440b1160b102c0c04584d1300101d800b00078030907018011806140f08402080c90b03200c0400064551080465908a42d09070200006016081c80d0a1401e003e400c02040c8404039a282c3c2168a417003541943d41e55449580854005840c44d0021440740150508031003050400b454803000914621a6000b49410400405000108003d880c3c01c03d5001e0400c4000a030007900d0200d001d03041d481c01c191489240e0300c03141d40202d8941c40c0081010001c803200c5030390b0b0010b5421034198035455031000354012078104203d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 308791843 1250 308790593 308790613
    0xd080702150c0f0a260c03180a060809060402150903010c0e011b1203020f130b07061107200a0b0d09050d0207081f06260d09120b09 58
    0x801040a07070031086540050b45400e100301d060b5142c49062420749400394000d021340030104007070b0858400d488080c00d2054840000380d481011407805407013512101c07880040f40e0043d070034100c0d042d2003405d42819903000126542e01c0f1811204400103442d1071070349030441e80c017040c05410a1030101c00d0007016031b41d0f49441d003507205d80800d085400e00926a40000c1c42ca0f44aa07031250303485050200d61154407540c400040e0a50784514550364082c5074890203240c1c0c000740c030680660300c241c25224811141c403020030f24603503142500c04940e805100101c40151030483c04603024020041a101c0b916044801c65099034802e08520b0601580d111801e54030400705030380001d12030000d400070301d03400c2d54015012404031210300c1c14030f2408200e40b4481040d50411603042c001941c00240700c40c000000e141000e580f00303404002c914014650380e017020483c00003800082410080c0c2442d81d590700100d8508039040100d00100440d00340043d4059404520006100f400c0483c600d500e02035000401c0d007080d1148021 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 308793093 1250 308791843 308791849
    0x712030c1106280e03031503150906010504050a051603091407030f060507050901050748140109060e18160905040b0a09050414010501060e09090304140d080702 70
    0x10b03044401680c062800d0b8001c000801001119040c080c0010030b0501a044001150b6074881c000189201c03402405419050801c0d9010081030b14102d9019907a00141e040003200c0a89400003406901d000e1b900780700c046000030444d482054490103010320100c0c0341942c5090304501900c0c07902c00030348400503000c0400d10b00314018000f0b40b005520801d100c0060040d41c1c0303040780030b5410081c802c00031b02070288034098072a41c22004403000b156107c10098410325402c203241805001c6001c8805140b125034440b82c440b0301c15081e41d529500d040407601305c0065640e0340560b14101507105900d00250031150104440c80c080c08040f4101d010050003000103100c100200c000c0c5141c01c9410000406850011061841c0c101075070601030441520300384503001c109008940d1a40191265901c210742d101c00280500c01040012101c1401401c001e0207030b544d50303190081a0804000380c443c0301d000301d900032a074000c800000f11001c0311103454040020302a25010400a078100b40c50a80300801c0800c188401a9 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 308794343 1250 308793093 308793103
    0x509010c06181e0203060c0d02040b1c0e0a0507050d05070504110702012601150c060e0c0f0a0315151a03040b1e0a0e01090501060306140702030712030c11 68
    0x16840b8100788004120303a041095003850404610701801e4501e07401000543c07004515680d201c0000607485958248814502000344102d600c1141c0c044000304030f4894003955072011540e080c080040901076000009140c640750081c041c00184a98000f440800450810000a0342c000c0c2c050b5081d150110740d034401041c00c0d6411910011200708000035035100319a00300310403140e40140f105034a845c3c82c8031500d0295481d141800b07804015043d0a803040031152041110030507c0e64800420b00c21304803600f030420307628000d05031080c2c170440000a50303125034107001c03a414048030f401c90001c107a10b00f8201c2901004042090240101120010010502c2c0004100042030001201036466071b910b05814041d10600c00644200f80a020180f0160359144c218032110381c020800010019215903808501801001000c034010880d5080c41000414060f5035484925081e081030030200403551242c00481e228031911034021b000000c120b4912500354460303030040c0511940b605041c1c13180703050040400d180c8 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 308795593 1250 308794343 308794361
    0x3070b09090702060702060103110f1c060e0d050304060218060408070f09020301030f020108190f021213050d0c1509050607020f030c07031e0b10082505010509010c06 73
    0x210400145504060902010407540044030340b0143c0464240418002d4840b14184005001c114070506040041d0750f031400c4c50003800c034004090444086000e00c0c134106254103c2030503548949881440c114000300801c900c00300a40940e42c031451340c0e855582d904025040421416145242c2340580b00e044d4880c04020000360030754034010070708286451066800001e458125050031030041c00104001004c801401542d241d0908001400d5900d40e4106150701d421500e006818030b080485000c04442254014180b003410f145001c5829502d5402000c0f2564007204001c080340d014800300840c59104480e4005032510401403040c0c210f046c400300307809441d48890180c0d100e401c61420321128680402908030401d5415008c0c1d8180320907840d4079502c1c0c01c2d0174803020b00003125007041e00301c00e40c0e004d6181026480d4440b1310b508050070034048034950419140680c803018807500c51080d40b9420141c0c0032146c05404030f22880d4003142440d00450b00c41c0c00082841d03042c020b422040a002a81d14000c241d04 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 308796843 1250 308795593 308795609
    0x80408030f07110307030c03062a0f0908030306090f040c05030a0c090c080402090a020f091203190905060409090816140c090c0412020a08070308030106080105191403010b0307 77
    0x7070ba019414420040100700003010300ca60b000351401c10000760700c040031004803500010005002c03610310b000c0c0320800304020103250700074a81c406100c24543e00420810555070300e030340d5219800c5464800d03181d81c0740b001b503e00e550720001d04030000300e10070703005080644d0040c400e000710000aa55000821319002126a00300c1d4030003550001440444154862803101c0c40719031030219128180758020580e8107034003800c11203010750000360b084210b6140d001140c6013607402500c3c12035080305100c8241d459412006901c08140c423003880c42d100452081100109a030310080c02ea92500d841d20745010024100d002040318018814864106e4080010b002c145419022341021042c07111001801800c02e00080d94440c41840031405110200d24014240d60a0f1207441d074035410f548000740006840d0791482c3d4400001e91086c15400700400600300c000e54100c80e06034030b94207803070390300e8104111a0301d101c000094900d1304c07503840030010100805602000d20744054000186040c2e05800300341458070766003004d04 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 308798093 1250 308796843 308796847
    0x8010606031a01020c150904060b0f030405070e07120b01033207050a1d01021608030a020607031406040902150c07140102010219080703230603100c120207080408030f 73
    0x42d031000030356500c50000c0002d10150101500e04030006600c00080054024200d40100300e1801036280d41c1e1101015028101d580c40c0c465890302441c8425071b008840c201c2e0f44e80241c0303400142603589810824000c81d83c90b102c1301c00501036607044500410403403003101c0c105a2030702c0711603513a12880c411007a80201549902d24500840010207e140400500040c04200d420000d2a00e0254407840300d00c07004212807220340c120130403100100e03d0100d005110001056001c07000203011007000005102840750341e025034501d5602c4541c00d600300c5000c0c90030341c086003000c40002405450913a2100f0f040380d10040040f0b403141c4a003140c401c61a08400a00d009135408170f84180584c00c607400e50f460441500b40300035482c11000405980721642c01040c0842480002c8002ca01c1890103500002d01c441e4080706032013000580c2c1032404000d28019951b050090184502c41d40c0160724601904122003060707294030380c1c1c21490381d076140c0003540025825038054006000100350140d041c0020305003403c0c001005a = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 308799343 1250 308798093 308798111
    0x1109010b090109080d090e0c0c1204060306050a05150d2c0c090c1b030706020d05070810030c052206030809091003050c060d09020d03020d140c21040801060603 70
    0x5460f03500c00e9040041680d02281d02ca070215540100d4035402c0c0e994001d40c80700725132a0390b44e143c10240038038442e410031809052504083d84d842031001d80b080300c00d1b941e0309006007595035040c0300100b5801e01450b84c00419490103240050000001800d031068481000101940c0d514204045006000801440e985031005110240075003040010300c49035003115603150b030f81800c039040065807041903002c601d02c4607040c100d80424401441524409500b04000b50342e980f08a6400d040241822141038012440c0c400205407044030580525003561307800302d03817000300318202070800410b86408841680c2d108000c0c0c1c0384030b800050a0060310002c510401040d515920030b18100705a02100800390505500f80000030000300d00b0010340350801c0042580c009980d0200421040b01500a14101941281c840849081010350000b402c40401065580700c1c040703110283d034008100d01c5940458949a808840e904003142000303840b6182100386184241e15003a540c403801030039a00c281d1300950120350b0768811a = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 308800593 1250 308799343 308799347
    0x180e01060f0201110702040c05040306020c100c0507020907030e0c040221090f070501350a0b01171605130b04080705040507050304260414210304121109010b0901 71
    0x1800400c1c1d4500003030028030150190300d00d440c0104400644a90780382c1401c1e070041c84c021800c59000d540c01c0b0030f042d9940c200c00c105996590302410355002202d403801071807004041c40f0f0419152000c1d0f004203c190320f038031100011030107420007103111030fa140181003c1000980d100c0c4010550202c125000c000b0402d60036854200042c001401c3c000c803900700c0a207100c0d0411b03001c00c1800c02e4950908052802000d1100c0f103400c50b0805a08402e120b00710042c0300880b0100c1401d40c03a201d500c03442414020400e91500468409a005669521110846012400840d000030031116498a1454410b0400301b00078091403030f0302265130210940c6403002a042c0040e00c014488800606802d4409005a00385440300030603a110090000d000703000c444090130010148600443d84242c048a03403240c803640c036011640e0442000c0002d00b803250b011001d5804400c41201c040f441401d448001a600307042c036154001514a40800b021030708279920350365410140c2e80d50f035501b6001e028004005901c680f070507000 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 308801843 1250 308800593 308800607
    0x60405330f01020c031005190e03070506060415050402030a020705060106110c06030705090d0f050106080c01120902030d0c0c0e0c0910020105010b16020d0210180902040e0a020a180e0106 82
    0x20503030464101305203a14081c0c030006031074841001ca940000443d40e8131071001421a400c504000c210050410005a038804000000381c01c2c40b1340128161401510340100700800c41e030b041c030a011a070380c0402e80c2c03c10180c5420b03806580c0c4031000b02000b515000e065510341d0306000007604444041060405030300d808801c200704105080b02c0c26030b02e076861818245000f50482c01010851031040387c29080d140304014078071100180440c0c0c44002485001d0722984041c0e1121a5881c1e0b46000440401078071664904d503002d00d0110940103000340040c80c000800032100792200070400e840c02006800300141045540005503c15060b0080803519268142c04010030240c00300e0940e411a0b0520006114003100b40d070841d545000415217031840c00701c152000c14020308801c5000303540f0440c142c8800c280c0f65007016a80040c0301d000041c520200b916804140c08074001d90048545d080c00000004410014030b42c020122299a030408107110900c1080b5214000d5803500003041c1d2021840040001c0e43c5c00a070 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 308803093 1250 308801843 308801869
    0x30b01030b0903120a0b0f0a0f140102010605060d1512050109020909060423150c0309010e06040c050f062503030507031404120e1906230306040533 65
    0x10183d498000031600f40c0c081c0316400b500086616070394800100c92699420b00b0100780c000094405c07280c840d17035229001c9204000f0700c80c8900d056040c0f000d4400c41d41c8184680b0050b104000e2850303003400d481c440a80c1c0100040f0b00f01a040710010721012400c06004111094241d1050b000030410380c24610500c0014803018004003c40c2e481402840001600c00e20000d490203e4000d101300b0130328214260307d10f05220b45550400407040780e03090155009000e40298490307a041c20007071220b84a98112a0780e240e0045501410351030364840240207070310700f10031841d200b600001c02c0d050400d01c440f02030202c051703044d100802ca010340c0403103540100358241c0225681f20310503040c200803200826918040b62400100300500791031400e03a001c03d885003c1e5100210094010b88003550f050585005107031204114041c0101107408628040c2e100141c1e010928032101c0240705007401e52722540f0512014140152107841001c02440b24660015400c4d085030b000920600802c100081c5c0040c14000050000f43d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 308804343 1250 308803093 308803111
    0x51c050415060503030307032c06010e010b0a173103081b040302010c0503070c081f022b060312090e010b03090c0d03020c030d031d0c01090603020a0c0c030b01030b 72
    0x80803c003c50303035001c400d4030f52001281c01c0c00314654005840301401c1c24101c105200210303a1244000c00c43d0750001504d80d050f6029141d50002c1640c07205a000c07064029400c2e02000500c01e203207034000100840e025070b40c00400c40540449403991140c584000c8000403612813504c688080070701c10600d07a0007403c058200e108030820540701c903d840c181c04194800d6000107818040001c201200b000720800071554403640264500300000c0d1100529601d8030303140c0903903051501c400480298541c91520841d4204084201d00c1030404068000b400c1444601144440341503035120800004902c440d00070341507000b12a0b690026090402c0c030285030380383c410b8000c03880062080c01003100350381c000105980143e100301c401d0100b41c1050301e030480c545240000a02c0c2c244c002c0c07020106010b0380640003141c400b551550740c031004e10211f402841c1e40b00e0032002e0403400214131050801115000398020402d2b02028680b81d102d02c0311941b40c800c4a25030a42c421204105000010002d2220744c0103000d4011a6203 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 308805593 1250 308804343 308804351
    0x30f0f12110d0c05060c070206041e05190f0515130b220810020f040b07030e090f09070306053402121305060a2a05010b010e0102100c051c050415 64
    0x507444035a0765885c0200025908000050b01400399036564040e20020310400183c60301a00070350100ea4400b16062041034055010360410600003052502010300342c5410a0045071840d00d81010029100001d0101200b80340c0100070107171000d2000d40f0100081e102c03040c201507507109000c00c46074464020701c2e090f901d40b4940b008203114045011501d1030200c0521800580c03651810703410f08d0800c2c842d40d4003018180c08001003d008041c0c015500c6000402c08503002451603943c6100b24040b0718046501030a50303003001c0e2007170000030700650141c2d40201071003d17a481da0400c109284004196540c902c0f07018446002e04200d00d5940c100103a042c2001150030a6041443c0ca46d048c07181c81e801405090f100c1d14000c940a1907141c8200c28080c038100070000101448a502039030001143c8010000351180d50800540c3c2d2180d5000361500d5240120680c01040c0c1c0226100ca000000d1084408400401101b00000c038051006401503402a42601078001203505152805911040840c07416690781c6040c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 308806843 1250 308805593 308805617
    0xb011119020f27060a0b07060c03050c0703020a12090504150302040c030b310501030b090d1d091506030c1305091005100c140703052401030f0f12110d 66
    0x90728401c0c15019901003c250990b40310b5000042c0c0c540e8043c1c1110140e081c001c40e0385418042e0641012417103d100c4e490030480e581301d0000c913800300c0c4644407020340542e002000c00f000080e03002821400656003840c254803c1c5c1e4844d1f001a080e1481100d444c8000c00000760240b007503103044c1c440ca508100042c00d007040407127404c50215219071b1030750000c90340611a9103a0305880040981212908035894a000c001c1c40d0386910f0301203224401902c2014503841021803c600035400351404003840140441070f00d10240c0b450042091090005240c240086540d884a0042d030700d4a1018602400390941c416498010014082c400012541d00a0b8443d681410902c401400d65030000b1055880a03100e20380300d104110b030155030b0000141d00040440d090459818095030011170000240c031301c10340c156050168036a84411101e000322070518006071410004000143c1903c1105802034804d000e900c1c41c821840e145d0014513003846d052280401e03002e1507926003048040c01045200a0a41012000504 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 308808093 1250 308806843 308806879
    0xc09010806190f090218010801050603010b07060f09050f0d08070c020103110909010b0a111f0917030901020a0305070c0308160c051c022107060b011119020f 69
    0x240c06400c16000342c9480d080d15038581c400c030a0704806450140c9048100e160b4a08100009520111500c407004040e6440c991030796206190550407200000d01d054151b90903c118081c1d103078030495040324903a554641c000e529140a015504003180104003416802d8a010b10715400c01c03122041002c00c000e944e608010005410480042c01c0c07540a1178001070601c00d00444850350321503600d151394465017450001401d098500f0040100c0c0d00a6a5650315070703c07034881d14a0792403010340d802c940d4000440f415200718150396401210450701401281030049280304c4c102200382d0083d40c12001c80c0e500000d042172000d426025030342d0005401d02e010207a0501c02d403802400b01c00b0103400d1031050002c100700500001e01c51110101e81e25000301c140d030003082026800010122118103008050f00490341030b10b0804900e10102c207620102034490500d002c006507101c0e4010301548650300d0620031610034042c0064802c21254200b000025002d00f10303c600c6004200e290840d10141a1103000d4090550310055 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 308809343 1250 308808093 308808107
    0xb03040602090f310209030a14070b0f0316050c0307031107150c0b060d02010f0f0212040806042a1a0409050c0d050a02090609060901030f06080a0b0c0901 68
    0x1503084540181c403003085000040c4000080d0360800d601032803d80c83c03c4d070544c11009100c40c81940162081000c41c81040456069000c1c440c500c9502d90001c03044400483c2940519203050190704040d2217407161030301ca103030a10760403007801e00200003008010880002e43c54060554452154204541805040c410881d27a034840d00358000e00304907000991402c43c500410001c00075045403081600300d8541010000d050300300110064503944945c03001706665041152030300d5111034060790b4207418110089000e80d044001420200114842d04a08c00e00d2100e1003c050805098032402411240c1054100740c4070100f40d181849402c1488500c941c044400001480000ca0313041100c0c001424403000e0310402c0d28050f40e40242da050381490f041055034541c40004245030700240004001d83c0d1030b88000c1d14124040c0c00e130300741d4206030100101843c82c600000506400d15052401081030003803c80d00c50b05031011903100148951260300000b04000d07503034240c0e55101500505032401c11001c0b10008100f1 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 308810593 1250 308809343 308809351
    0x106150c0501061d15180903090a090507020d080c040b0a030f3812010504060e0601150906050906130803131e03030e15030403080618040c050f120a0f06060806010b03 73
    0x981c01d02d0070103071943c1c49100d006d1140304103040c010711141c54001300c80e035181d81c4017038600c5214801603103005c01c10001e548107070b900982c1c0380d034000e005074140c01e00700f503c01540280032054450000e209c001000d01d5000014082c042d0700340d0380441e00c60515240311003554050340300c0307544200c54520081602542c01c469038420111007080d4018008042c40421070518a64004240a5080c80304103c14041c0d02c1e04200111504801240d111340ea0b038000150b810911030b4a03050004041031001c2050710711445c05852010002411240b404e101c200b1000300000d0750b80d202104503003001c20000000b01d101c41000d0018080310081c5c0c01d01c6550b19501c580c800340300380001001e10061440000041e2144000301c124407810305030048d43d904050074082c0ca484030882d0034910410741c85080c00c09441c0b50410f8540141c2e4484050700c0090705040030007111403613640c0c215070040d11491a5004030402004405041809107682c1ea0703035007000e424241b007516095000500c03181c2c000001001000c0c41b40c02100d41c0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 308811843 1250 308810593 308810611
    0xc020303060f22020f0705060112050c06130e0a0603031b0218090c0d0c050405010909030203070f1b09020904050a110703030b010c080307120b010228050106150c0501061d 75
    0x1100f4240310041000706140301103100850b101040040640b8040e0001341000e034001c0382110700720381e62100300c03074402e50400350018555000200c45041e40d040000c040c20882604400c07020320b95842e40b103084072051085400d203541d140c482d1020001d154022448202c410410344d05882c03081c5040c2c0204d070440b5284800046000202c400040703225070103000c1e02c00803e100801044102000303080c00341c079940150007654402d51600000050000c90340c490784030011340c1034000d503040c000d003070311004601d0107005000e440e407444003401c51014800c0a202c041c0901408400140c550600314284000c841c0014580000c2c1454650a488030700c0201c400d50310865070500d00171400344c05410040710340c006900b0b8000c0420b8804410f03c0700c080d130030023492164141609010024038150000482c0d40d0814681e5031381e922031101c10300360300402c600000c4110880c050000490100c0c0e884006040710384030501d030213000034000082841041020b0203104000d00442100e8520000310740f50017070350300001405450f9 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 308812949 1106 308811843 308811859
    0xd0e0105010608040b04230d02120f031801061206020307020118080d02160c030b070801150f0507050a02090906150406030b060405090709060b0a030c020303060f 71
    0x204031811640c03241d0b0244c07165102c1c3c2505410207013065038440e62a858107159040484a000285081a00209480c51499000a050080d0f03c00519001c0108115001007271301140c080d00d4002040e4207007401600d1401042c80d005000c15030000400d103088601c034005016480c3d01540c42642103800a000740d030002c584034040404c0d4030038014440001801105800b0840d64050300340d060030145100020100b41c0c580d68040b032041e5000301da00700e0005003045001c640c04513125006000e01503403000c0010809102405416039030400c4410040e0105000c42030040810501d4161500500800000e0031300d141d025803500744c100da4442000030340203400002401d040c8a0360048a400400300182c80d00c40e001004050070024140d1130603445031120101b8101002d1155200800742000340c0f5961b0403034428043c0c280e03804544140190341041c010010261241540060300703842c2100c18103 = true := by decide +kernel

theorem cover : BRFrame.Cov 308633093 308812949 := by
  have h0 := BRFrame.cov_init 308633093
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308633093 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 308633093 ≤ n) (h2 : n < 308812949) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
