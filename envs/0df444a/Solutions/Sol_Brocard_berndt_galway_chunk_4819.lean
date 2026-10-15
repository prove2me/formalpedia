-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4819
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:50:27.727745+00:00
-- url     : https://prove2.me/submissions/17a665b4-9427-43e8-b6e4-67f0ee0b0447

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 866546762 ≤ n < 866726618 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 866548012 1250 866546762 866546773
    0x1060909050708070617040f05100f06051912080d0603080702090f0402030a02100e130608070f030302070306020706111827041101020a1506180203011404090c08070602 74
    0x20701508001410143c440030010380032182c500400602000002c5810142024450b00050180140074400e41200c68200003071f941140324400d0f004008040300b402248225207004004100c81c10803840c4500d184140400302d02845082c100040008060540704454500080250500d502824011320008501c0790315260380320300c541d00c10040e80c03950080c005c08200050781d0070400545e030001610101e440d01983c0d40d000d101ca4400f022502e0b245200c48050b0030142c0c10304049681100341e8004000c441800060310b4801d40c0321050070345089028480038006030b010180c2400031461580c001e00400d4440e0100144a01202c1c00d4003119802c01c154098003400100c04808481c10114680c401540c000301920f03400d49000001e40c000d1802c00b41001e03081000803a030400980c1d00801c00c203141c2507008a43d14041014150000024040c24043e1548030074803002030004e001254025281030b2b464107034003101c440c096007007880010100344c402620605a00361002990302001d00855010b484a1b50241a = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 866549262 1250 866548012 866548031
    0x12050106080a0303140f0f06090403120e03031006090303051b0709061202010801051f11100e160902030c1c110a121a01090501080727030506070215010b1605010609 72
    0x220207401448001c1d0402c010040041c47c41c01940d2480d400307501107801052135250703428229001e0344415201c0703810743d20b06251000c0240c0f001000d10300c42c030285070b4041d02840c0c503035a08272000941032000a0100d48144505400c00300d4583c51450f502051608076404580e03521410426030340a07034003150b95107005004440643d40e00c682410b024000030b80301c2807004c0000711120f401c400c001900c035404000c001445103080c07806c14406020500300c0c0c4042444261070351005151100319504400f03040004203900020180d90314001c5d02d1050201c10055400d040d00904110400d50100583c5000c02d41d441c21445003000609000e8682d81c54980c0e2400807660107100d0300c00403035002040d50300703038200808e21011950781e0103103404003920400e180c0079445868900301640d0b003240711980510300242030503090214004481c480030449008204941040d142c0b40400c0e130702d99854000c20206000408014848480c60134010721101c81285520030000000c0c0d180e090840c0c0460300913590240e161164403 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 866550512 1250 866549262 866549291
    0x30b0a0e16020a0c0501030e0c0a0914090115052b05030a27030611120a1b0e0109140a03050709020403020315240d02090702100e01060503030412050106080a0303 71
    0x107050402040c0000c000465258441020010b05845102d041589424022071041800e010311900068050208003610b07860740200d0707002e440c4024501a1080742e5800007602c524050151740c0d584030140c50034030402c4d4240020b00807014210078030805003d80c10852400040c440008810032140a00051500c03402c02e06030043c19182a807525904480504c0b128042c103204140c3c0307241c1282c0c0d0040b4000756402503903881182c5801502d0340d00300b50381c09032810000d03a250319030400462901c140c84070b070340c4c2d83c201c000042d140110149401800210500000e004980f100d81102070090001422000740942d2a0f4800d4a00103144d04285c1c0100d801190410850a042011001e04a0344101945003450b00c4c45651160383c42c204080c00c04030704000c041c5d41543d2110540c11071496005000c00b50a842c0074074019540d0072040e41e92102407031802d2400802410180300384403d4540c000e01851500e0301c1c1c02d410516880c3c00c204180c0311950780e01000209008100f04c03849003130b80300c1d0700d002c17403001e2080700c2c2c0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 866551762 1250 866550512 866550541
    0x50d031d010504031a18120a020d030e100b06192001050702190c12030f0806030105070516050f0607020624010f0309060f1805120711010f030b0a0e 65
    0x4036030601009101c01e2002a00140e0382e09062031030141e694011b642c078001d510003803490f8180340c14a2401a0044540081c41d908010702e407031001c40e00ac50b008030400b00011012500f0051000b0a142c0166458095400d102e130002d00903404010703c01c0b4100311801c8000c01030031605402442c00300301b182c4c1c40c0b603003080300b4034040d0041c42c0e02c1c0c3c00003040039250000707019483c0d64a0320810140c0c0903400020b801086004012080681592071413030180310a203180c0505a483c1c0c00c195034001c9103040002803c02c0c80c05002c1c0310700c6070519075185400d005100d1700350703141800350300000c5035540218600664504c02c10000540b161078668002d1500f03003007482035502c00961103501194001302101038201c05981050714840b070b140080ca40015041e210342090001442c03508040b49d10300303048c8507200d0102d503404682103100600407404c3c0d810b00c10381446041164868518018101804980e035504a503024070042200030006060101d440982d0b080010401182500206640c40066050150303016900c0f04 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 866553012 1250 866551762 866551817
    0x40203090c01030612120c030207030804170609070605090d02040f151a09030c060c03070c0e010515070b0c031b03010b032d010306020a090506030c07030e06040f12020a050d03 77
    0x460300c590440f151a51806c2c43c098050030f005001000c5450420117100f000041c00540e00100c00948880d200c6044501c5138502c1da40e650928803d1401154444002007141c0d021202161516443c0400319000c1c030121806014090740e100f9034a6000c070750307015000d0003420340d8019403003059460603051540014107441b501b06c490748409402e02c4255502d8900040418074890700f1114252203280f1126002c0c070354414281e000700014291080054142210040e07141030702c404941041d400d9030000031140803400340c0e130342c05000c404134240401c00a550480045d50807401441203003e8010190000041c00c1c0d000780e00c102d401c07140c0002000030510900200808080e45c040042c000c1610105032800c1c1c0300810300024005035030005a07403d01900569007040100b2000d000300d620307840c100c40182c01d10b800c4000158089018051028030500e0700b002103405480c421090054054200504102404410003040340c01901d8060081126641c80245e90075142c032a42c0c038034400c54001903220a04c61701090 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 866554262 1250 866553012 866553029
    0x304020a0b040e0a110c010e0606030c040c140306210c011206080c040b04150f03171216050d05040809120f0d0815090103031107050913021c02040203090c010306 71
    0xa0066040f4607a95603000307081c0ba00041042e80c130000c0b00407001c0c80340030003940c0550700c1c1500a0180704800714001e40314120407002c0e600200707011806d02081d518450204d4001503025030f0341410304007801000d16080031001d00141d01c0300482c038030703031002e90309417041c0381c540c0da40c00701040c9011580d01411460480a10340e8091040a250955281c0d0340c0414090042c8034a841c2e02141b034158841d548005040f8908a48004003940d03a00446854a00e0f40d0005803180318003c01080d1145602070200c807884841c04882200681c3c903000c03160104041410701604011082140b00d40c40400e900890b4002da01403034103555101c01507802c100c10700e844000203d038250000008500e0a030008100c20210716171a05020f1103542d80c4014440d800c0e490100141d511260510001c8103040d44200c11a28403801c0c0c80032034021688400400c80100001c44060501c40c1e8115208001070a1076400032200341c900340e800001e49043d50340003400783e820403100700c10141d01c600403150b100d40c0e03d4003420000304140d5 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 866555512 1250 866554262 866554267
    0xe060a06080a0c090b220b011413031202030f0f0405010f0206010602250f03060b010908010504080406032a1d04110d020702180c03161106270a06020304020a0b 70
    0xd641d2144030308094410b000044c0e980c0c00d820001510f4004920311032200c68142c03a5420481e404a01d00102400480b03180002c16101c58110142e002d142140c1d4070008801800e00e25a01c2c3d640d501690044141d20700c3c0442c013080c0324005102c49641c1c060b0180c0100d011116880e80d082400050440c001004050115485940100402900840c1c184140210140006100b03015940a55001002c070b80c03005500e40100000001480880e84c0300060040b000d1760703140d0070340c0d50b0340f50b40509076401601d014000c07070340030402001602d00035070100081502c1d400c905601c4010321407210b05000c01161100c0c1c04558000481e01070240c00121040070440c041310208026071800105014074001c4c007140e09550760b8005010700070340d9111800b1743c1d42c070020780507000e40350319010001510941042d03504002e07001030032000f050355a010f81c00040710004081c00800b05a070700d091100160100b40c000e50120110741300f842c2c0c4080b000901c826071281e0301614015a40c0c1c241413040c002c90000300e03031000544d500c0a = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 866556762 1250 866555512 866555533
    0x90b041703150f010203090909060604050c07030e010f0c061d100c0c1707120507061d1903110304080a0c051c030f02070e3301020307030318060e060a0608 68
    0x300b03000401602d400d694100d00103840c180181c1c0b45100c1c81e403000e40d00c181040200321182c640050000c0c4a03041c02d035030500140d116100c1310300c0c0c40d0081c0c0c6002800705a0f200301401740342d482038801c0b401030441c602d040c40401d00161919811034441000700c000d81c4c03120141c1c113812143c00300a00c012102080c10100204000500010210030b4040001003441d914914000e5030401d90100360341125400201141030400c1900001c0c0107903201600880c2c200d400c001002c1d98031440076104003014450390300540204014040002c401101c2d1450441c10b0100b00b036590b5141c1c0d4402c0001d0006001d0b07400080a25845600b452041c0b410a90b02491003145060101c1e0039a410085162465070b40c50304201050009100003641446d01c190804d215084102c01040b60140807014841040351400b0b007001043d151503e40250070801d900611405a4400c00c4407100291180d405000b0031015205040c90340c4d84c827542c0783d00c02c0c0c4500f95258680340d030126080c032040c81004d00c0340c08c0007012400001c02081c0803 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 866558012 1250 866556762 866556781
    0x50c090114162a0807060c0b060d080c030d050a0606091511011e0b04090305041a07021c030f020f060a0509030c0d26090307020603040f06090b041703 66
    0x200031504000d2584003090103601c00188040382c1e02c2e0140d01100c00300c541d1890744600403443d000c107071000b10403065007400003445641c04202081a10b0069803248480c040903140c03480070190182a43d80c02c5030310384034100c000c0f038030030700c060b1035200c0d00c540c05559195101420a419594054002e01c0c1440ca008020040c1c142c1260010f0b00f11000303151503200c0143d8001c1c0a440c0c2207072038035060515509010441284212541c8007a00d020350b000800c000d0800440280022600d1500004010481c10001801540d5003407040c004a413601c884201c1c60160341c1d0307001c1000c1480d269074010302c10110b40201c00401d90425404241040c4078401400110800022103503200d03406848980001e03907031004038080d40c03000e10841c0e0001c030404c0d080340c50991031000c00804d070012062030100c00c40c100c8dc00d40c0000c0c0010094081c0100c41d03010007036081c00a142c081294a9001810440c0c8480151200708001407250058615160084860764150f1402e800c10201c8028034080ca480d20b088100f081042010 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 866559262 1250 866558012 866558027
    0x1020c03070e07030f2f2506110c0a201801080606151804061e030b01080c1f05131203030f0903020a20030124060504030203150a0f0903020c04050c0901 67
    0x83c203440400e1048601c2c1b81413800e40744034000c0340c0c1c0c03c0542090303002c8581e02c03000651750b045188070310000c2098906000c81120345020341d0101b0100380e081500c07008003083c0c070705106002418181443c2d60584c095940002c0c50984240ca1440f003e020200c01005400800d000182e440320042c1c40385c00030030034000790640c02c5218158040100005280c91408941c54681c45039000d030103040c540d00490391001d039000b503c0b414144011242105034400200b40c01e01c02040359080b180c0702a0482582c0601420210f42e0f4070401d40e190350800809100d4000085034010129005007003050b0003400101d29070070014155514910041440e6007801000d0000a90000b90740154942007a0481040760b240e6490b40004603142206591560a120310780c03d4180e52901a22505040c0c8800460072a0f41c2d00010350b0036000d9844042e40c180c000f03c00f0704000d00e0352698404d60294195100140c0445c80c03510300c5084949108080d00180c0c0310290311000c03070816114054002c0c515014190070088000002000304 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 866560512 1250 866559262 866559311
    0x40f0f05042604061d060406020a02192105010b040c170c040f1503090212010b0406171f200307030b04060b030c0f0c1504033203040201020c03070e07030f 68
    0x12040280400b00c60b01c0ea003843c40e50407001b44050340e01e5942d40002540c582c4080c4050740b04100c090700200c2e07883e1801d040303007013100e00100218001c4440c0c0020841600b143c7e100c280c8065484441c400d2440c0c3d01c80c4a0030b0306200680d2203000304003030002c4061051140040804c14000d03800c110601084402200150484803c49071207030200069220443c0074040c0440020b400c01588505132102d66019044140c19240990f820080749079a26401c40440851080e1852113401c8010030040c038094201c03801081c26207080c808280d00d4003090b03200454408100f02c000002d480401032000280e0316000360901c802c42240c082c00340d02c2c18410000070911014150201c4042d0000d504001020003105030303401d004440301a1400301c1d017411110090040c04640841c0004c0300101c401c1070005d07880c1c00703080160a07402d00d81c0d400c015258021119503400035000764158418130840e440d4581d001c0144102500700d00f400c040c0d5508010802a040e14100403144643c50708010420342050304078602c002e840e = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 866561762 1250 866560512 866560517
    0x130c060806010c0f06021309020d1a09070c021207060203040f0909030e060310050604080307052a040506060c0607030e1b010203070602030406180302010c0206070512060f040f0f0504260406 83
    0x84c4d035a01c1c07800300300a00c211141c41011b03504c0010001140701075580509146003c00c0000d028041c241158925409004000c1d10391111f130041c042140548103a036656140351010f0804054100440b800d54a0880b81d940b0082c01a4000501401402865140000204000b903014840d0312091341e4050f00501780d00840794010580800091030480041e241030f0700808014084903601c603160790116032039a000410a40b2184104040b007a054155850010150b0b41c000b51860b07203016019081002038440900113981c000300a01c50141066070a0000c180038940036140001c80803100b0802c075003031030700c2d125105207845024904080310b41d130003000b202c902a622160059880d82c0303500d007480c0180110f556600400c040488000100350301507005030101c4820f502110a190b0b103d0350300711000d2148120213241c0c004c007200400c140e400c2040c88003c49420050010411221034481c0e0070403180940c5100c03005070b80701c08c140400d0209481c0030700c0160304450711580a4000318814044c907032059200380c00c00c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 866563012 1250 866561762 866561783
    0x31406032a0607060b2427150d06080607020304140d050111070506010e100e0403020109051c08060a060206010608043324140117130c060806010c 64
    0x1110086080c0d00c0710184000308020384495003424030100401e03403e010700d0700030b5121a250f6a400c2e4601041070080c1500c0f602074510342030314102d0480740c10900c00409240705240402c03031400303540d8a80e45000c4840250178444d469600c1e041007403055500d540d1006076260441004e0011842d4044110380c26105880c402140c000b20309004a4020404414054400c0d442c2030141440079041c0320003840e034140103c0c04c842c503a9880e916660340c040c009403500501c00392540740400c89007200032a9158000c0c000d0000246544075030319020f040c10747c00241008442240c01e88000903e40156030550450307829100e00b000c0f03034140702d0041d5030b40c1c4041c0035050500440500103030030070030344403000024841c00342c3c041e1503903100d40c0c0943d5003a0901d110603204068200100c900f01d220180300000c00303405c00c407022411300614002c00580300c0c619100541c0d0401007983c03003d1280b0024045030a0081d1041c008000c41941d241c00c0000742c00710fa68001d6401c000e0342009101103a82c1c0001c00482007a00910900f2 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 866564262 1250 866563012 866563063
    0x1b0b030a0c0917072d05040519051504060608090703020405190c030f1d0a1b030501061511030705070e07361401090b0318071503140603 60
    0x2a08906981d005160b4545401c03503180f018880070a00408658111034103158a00616510f0988108001c41011441d10800c004101c1031916411141c0c2000201102c002d203e00141c00391f40980c2c208036040203000304510300550303290520348124402002980350000c3d0b54280300101a40700c500c00d102c0a0b2045e0b423140081101040b1050750340d036610a80307080401508070f46007000340c00340c0700ea120061116032501e107400f4034503100c1d841b0400d11981040d01030100350029684244481000c01049001003204820100008000b441010064200e0000c96055080032140c002c004c6040c505920009810a10000c0c00160000a110302a103414441d031506130b9030703416000c940c005560101c0c503440d1040034107038000303200b07001101c120200090b14622030340d03075141d080c40c000c2c541c081c0a00034001641e0040400001c144c680182d03030458a000704848441d08401e10480c03401100350401e2030180b1440b202410780740d402d4400c0310407111055856403298644a80000d8442402c00c0030004041240740044 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 866565512 1250 866564262 866564267
    0xb01030f06110a0e04051005010c030311190201060504060b07020a06080604111b0c040c050a080a11040e011e1d070c0203010501080c281a04050a09091b0b030a0c 71
    0x3115088280b60264540681200c000e1441c543c20301004d000303031720700004607400e0300301c020300001500d07010b031900760070300c8810741e03007100101083d03228802e0700754050054502c84c000c40701910a0521940e40081034003400c003c1000304850302503101b2210309008000c100e0050301c40e468050201e074040d040610f101e41d0b801c07002c1009042c0f140001400c01c6000210640707450b15094610245a4510040307076941d1003500144801c4510411110300411420300c0301e41c1c0703850b110b0308030141d0081003200003141003001222001500c1d0420740010350f06000400060080250f07404202000e403a0490203104410318107801c00c0e018190903d8540080f00e44640010391a0303000d40341c202a0302d5400b5008019940c1e56065041c1c0700e5800031100341c802c1c5030992040c00c2401480da0000151343c60701580000151401c0248046900c441d070400b00c0410781800006110381d03814905000034945100c0101e0054918500402050319904622442c2c0c503d40401f800f001e10180203a070361201480e84002046411070320103 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 866566762 1250 866565512 866565521
    0x50f010f0314010b0a2006060d0c0b0309150a1103060f04200307111b0120061f0e1003080903010b03060a0209010e010906080a02030a1413030206060d0b01030f06 71
    0xb003040c1e03021002c00010310f160750000600d45525280c1d42d038000130307118600284414281401c0c0c0d240d95840740c40490321518001d036160311800e203d0031182031010340c2c031080600d03107400403038009040360044810b21018a407040001a440300d00b910041006022421204c0342c1800090000e50041000d2000150380384c07219800f4402802a1165200c0c1d06442d00c00300401503801100c02000042c5c60480440e113880001031540b403540600c0c054450b0035804040110340b1142c00001840e003042c0703c0708450340c2c120410301c615070040310401c507406103d040500d8072101355074007644800c0400e002501044200003610040c07034103980d840700c180d0365100715250019000d003040300e429662501400742441280301656009100d016000c0e00c07a280841000401510019114464400031807180c10028410141c283d00860b0302030024040041c09141c0c00006004008044943c244587e500200c600c041c107804200f011f52000f01102e0340d0421500503940d2280035034061100600b05a90a485041002804d410 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 866568012 1250 866566762 866566781
    0x180b04020702061209010f110f0a1b050a1a010303020c040c030e070803091f0c110406090614010809011b1d041e060f032f060f130f050f010f03 63
    0x115615160500003050030200245c41800c80c541c17801c0c03030462545445002e29880007454202c4a8102225100e044e0341a07448030b03100f082000880d00d401e6400312488a049480c1c68001c2c0001e000407401407600311403110840c0c40080f510910240100b0020b0f500049081c0441c0e002e90303020503003c481c540180c0160911007032544c2c440c041c441d00482c1034503001002c1e2200f90011074480703801d02c240e08240b46c400210b100b80d403000560030f014000c0103e14500d210f800300030b10141001446583c1c9024075000c1781c1e62038010036010a002145200795603840303480c540e04100d41c05d000700903085065800c822183c400386140c3d01481003030075602010045c0d40040101c90f034006081403203000302c000c0510a81900400c0107072403003460030b171001c64038100d1154030405480e4401181041d200c0040310049441c8002c2d212154603007080c00049180c0e45940001c0c208034120340140795111000b001600d202d0702041d801c6010703411488101000307240e03541510703110412800c1c2840d0080b5107220204402800b001c64 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 866569262 1250 866568012 866568019
    0x1203182a0914010506070b1b040503060f04030314390406051b0d140702060c070b0c070519030b0c0c0d0f080f041a100302120109060b01020304180b04020702 69
    0x20350008849403103030403031441c81c40790081c0e0701d80c5a130320f500800c41070b805035180c040c1103898000c0008110600c2070200c00019100349040b40d0801c0da407800020303c0d01c60116441c003901e420704000c0c041015094085c1a06501030141e81c0c05542c9016041d031410094441c0f2003801200b40c5003240800420100c4418282d842040040381d5215100d40019020742c2c4003c6800030118803589112620754004500f115660707031180da85201117020b002c802c204640080d80300341d0f4040010008402070ad0410800c580080ca4044003598454024a00e50f504240c1a0341c4018000c2c881090701d00c80740c0120b0301804c0b0580f54400c4500d00c143c1c4a0b2044c5c20083d0190442c450a2485500007064401d42c215200c0e4060b0005952211000c3e44c5081051091081c01d403401000404c60a010903e410180369038543e11040f1100202640c0381c3d80d400040800c5c4030b015410300c481c0d54803410f039030901500c3d0041655113a401c0c00110b01d86440e00940b01d400c0800d5080e82e0030b00b10356400d07076002c0c9565280c045a02603034006 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 866570512 1250 866569262 866569343
    0x50c03030901050702120a02070524180108060d1106070c23090a0c050d0c030f020d0518010506130525050c0f010e070e0618090a120318 60
    0x1c0c012940203040c1030352042c0141c030401a00d8000302000344100c5280415a07809003d40354a850240f100d079010314030301590308501a00d20b92141ca10400040c14800a80586078200c0b440b0f03620014200c02006031081c0e00516482c142c000205401c0001c0b8020030b80c09565440c0c0e900c0007418a00034561981d0880d80b00d40c0c0074049030500e9903024001d207416100c0203e442e441151540f804103012114035071199004240180300c3c1c1d40a01032140c0c03003004400c103c2c0c24003080c400000e0060508985c00130030b20f216281d0750f0704144011249003142042c170582c040402040241880d00026041910701052038500946075400a101660f05d40500328071741100140300d40c00250302c070f540034046401c040c4001070944506000340c84418414000e020002104201506909003083e41130140040028400d41c0c001072802d034040c00d000d0f0140380300d610410024001c1c000762405031070101c01c0401c0d03000610b000c150038400c1a42443c2442d01c0418411503004a070307060301900406925004003004401045a841c09 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 866571762 1250 866570512 866570521
    0x1003050a03090e100f0e0406060b0c1015050105030f09031c02031f03030e040c020f0706090e100617060d060906020c010e0a0f080a1e0c0606051804060c050c0303 71
    0x3800300c000e8a00d40d0030303c041d40da60f0b4040702c04095135040c4150100100d02a01c1000301120220007190818003a0002140150f00c503000c018a81c0c1c050b000403645a448002c0b40810201103110300105005030707000e581c1c621490603000900e6800040c01c41c8030f00384825004246810801c1048625080540442508182c00b18402200a40045a404d0400791000150f5100f428010a420017600d9140e1550024090514103100c001c01501c50074400f03512900c2000148000c0800c0850001c0803103a6540b49601c1c141680700185010161406543c60b04220041c814980c0002c00c4425080c01a0541d101c5ca5542a000885040298a02400d02480c05a8601c180321280d0000c100145100009001d094907a40c1150741c2e40c5030324a00508104020a5403a000a058400400c0d0700d607a41d213406059505029510281c10f1215500d650100f0b419600520400405000c0e00c401042d0440d059aa4201c2d204944001068002c10060440356114842c030b610790b000301e040e2403252029400b16500d0307140 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 866573012 1250 866571762 866571767
    0x50f07150207111c080903190b011502030f0403030c1e03080a06060906020a1103011d07080c090601020c091909151b0c03030915090501051510171003050a03 69
    0x4010400c3d01d400f0b003000354a0301541000720b80c0704161940000141c800303030031541300e03400c00da085843c3c01c0f0741c940103124549600340c40d4155030200043c001c0e80c615143c1c0d49004410003054950420301400d640040c0001c01e243d8020074203407401c40e50182004182d20304c06141030444500003400700c0300c0191416182c44141603200e01d405102d4814010200280350b221402607502c02c07100d204040051384a8501e02c030024981f00c09880c0050f0020b000801e80f10300d1001400c5071148845403891042d4031031402080b002c00200f01083e21a1006d40b10070b09207080c0400005e44420070350141d0f60040f60510302044a40b0a5a0000084d48424a07010071120301b01e46841203282000000c050300c45810001041d0103403003070320781030407164149c0e8642c10751030341c01ca42d1300b500682450002950780d003543d2620201d000c01103000b1000142e00c00c000000d16407034004d85881414094519844c0108070038890001e005400c025401c84202d82441c1d00c2d643d655a140700384031825800e400040c224084c4107000d01c201034 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 866574262 1250 866573012 866573017
    0xa06110c01060519141305042004050f0c0307020f010e0a030905041413050a060515011e0f140d02160b1f0504052d1b040f06050f071502 60
    0x406000c002d2101d2640c83c4100280c0304421441d5002040c05064200032990b645000c0d00c1c00010060102d00c070000c080500344007141e0084909542c405126801b20b007007810502c00e413481024003107804112604101111500350302d401443c80e101d50100001061030075008011050a50001c0300c024801e059000391007540314200702d1812400700340c45003008151031070503001e5400554507501c05a602542c40103100c0b5118600c036003040ea454018401040c000c50701a000744d51103a4100c034110000700c2c100300b00050031505c0700b0201d819880c1e40c2c000f1003004141c0c01614540c1116940c034010280311800d80170710140d80b0031000a014040e05c0051031010f4040040411a00e5902a0200b40e00c01e0b520401c03c81d0441408550280310180aa42c0500844c50260f103c0d6400c000303640700062030802400c100c1600c04c0c44181c07001c4040c0019004000d51203140b214a04400e0303001e44462b5007058602246131000390118003c0340c007071003808a1040d840080000503106c0b03c41d0004043d01d142010380341c10f00d000b035 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 866575512 1250 866574262 866574277
    0x5011b1b080d08090604020d0c080a0803061e01140c0124030b161e0c06140603070512190203030f040f090609021612050f0705060a051501090e090a0611 67
    0x80c050310700007941c2a03014584041c0f04040784d801034a01a0780b580c1c2001050920307071004513152250004080340050782048403500303031442103194660b42e00b004800c00108042502d40d85904e059088114081a680070401c94443c2294041cac40d520b440c2c0035409036000d0007410360322220503a001c2c00d0403265007500c00c40040407203006002490898a0f9180c0034030390036240050100c0440d5031355907aa03244266407030098440781540d00c0c100042c220b01d56118000da600c3c0c1c90034904085040810b11005c3d1030140505001080102d504002000e074140803180c4a490071310300701807010341d00e000c914159102481110020f49280303110035a501c0e02d60703411050000281c01114050703850a1004501d030b01c410b1003290804400f0640200394011107070740b034111114000080e181009020b010002400c45048040c00500f407241d0017514052a0005130074040b01c7d0300425120b00c821180408a04598011a5071401c0d1915168042a00e41d1491000d91a03c440120020941880c00d06000300000105001d031001 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 866576762 1250 866575512 866575529
    0x4020c0a110904080703050d0f02030406021206010e0a0e090118050a060b010c0c03060b0d02130204030303050c0711063106021614040b120102070b040b0f0103030905011b1b 76
    0x7000184a010300c0c04807030003032207804100604004a40500302421511503244400f00c5d84049400c41001aa04256402c83d441500410705240b4903c0c1c0e802002c0d4064400e190246000d043c410001c0c030389560600c00c4d10075510710f120128030240000e400c1116481c048404d01140d0411703a1500a41d90001c01c082a41c2d03aa142a901084d90342c4100f81d032450094028020f0640c4e1811a107564008040701140c050303100241c4013000c00142c9400d00380000ea00947c000050711075243d400e010b41031b54001004c5214020080142c0c0000601c074006000c0683e0054035000c0d01e44403c19034100840104241005a00d450380030000d112407035450113001030f40c8196080c0c8400b00f0102d50b01001e404940d010b180740306080d0061a030b0790360401e42e00c524240d10004100c110b4000060746c1075030032a8458030301903410203010303c02c00042c03010011601e0703004075a146003800c0c00c2d851518002c14854150113824100000d40c000b08001c40076007071050309660303000341c1e10b0b0843c40380f0403103400c0703000c5100d1185200 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 866578012 1250 866576762 866576783
    0x29091c051b030f010203130210110d020d020f03040b04032909030a1106071218020d0b10150509090c0408240604151a040e0106030504030201270212030904020c0a 71
    0x78083d018000c0da406034529014040f0403440350303403c100e005026501c0610810101889028107900d0400c213400c00e0080c00d401400c101c01e07200701c0007420420075182c40304050703000300070802c0030003c075000b26030840341c12001e0034441c80d01108183d05ca0500075000c003151026900141b052244e4040028001c904268540d1a10160b90031015601d031407044402c0004115080d183d128078221039002005101505020004440d1031030380050804a541ca4040e280c0b40104400c21140700f0030413080030b01620080002030590311200000030000d110f001c2d1a24011140c02010542c032090315020380b00542000401e9038200e0304a401e20025001ca503d0580700c0104140000c6030382d5003058411002940e0b19000d5101c8824245202c0000503050106c922903035040030400051103c4400c0042406800342e030b680030490341000e050007270960350000d1865502c4100c0f0502d8443c5281d02080741d0200744e905982c003021940e0008103136420350140004854001c1e000080e010383c512404142021001d104003000d00 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 866579262 1250 866578012 866578033
    0x16030e01030b0405150405090c040908040302040b060c0a111903062003060a09020702031207140d02011b0e0406030602160201120501080706050706020d060b0429091c051b03 76
    0x84d2103064404200c2d0041c001c102402c14203103908802da02c000300314100c3d0100f6550030041022209145403c0c4d4410401080c1802140344c14000d4406460b0125140303401e0603454815a81c58644100f4010440c45511054450315250300c241c00c041c44038140b0101c0c00c1c00c1c0d50b0f418014003800c124071000c0295150702941d80902d00c100030581c0d00032176016102028082c10459100000d40c02801c0c242e900d84904e402c130303083d142200001041c0c40791040220010401d0000883c0e0f142108040e941d80c25a4142201c0c0505500100d0910900f82c0d40d91814241140c007a02c0800c4c020b15050700040c002e9400060741c40704107100d046481481a100703a8502281c40c0c0c068603101c3c11180207000d050f074a0f801140c4204403940c03040340a0520280100c03001890050b500c02400c0c11901154022040c517600424200501038200c84411000c1420801c80d019408410501e841244603c038a03151103801d06900d40021403a417901c80440d0290b0000071610300c400c0c0c400c08101002200d0402c640309210300200c41 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 866580512 1250 866579262 866579269
    0xb0301080d210b0301020706090f050615030616050702040504030f09051203220e09060402100206160f1202030c040503071e0504021b1b041803080f0c16030e01030b 72
    0x1001c2140407040d078200c184810014003405404121580c0c1c4e455902800f810010903510722a81c1c4501d0311410103d843c0304607d01d4000d061940042011075921000e1102081c60340340440e8660b4003240100312880c2c019000702c010703030302401441801380d00140b60404020030140c101f0400005200180c072845e02055442c01007000c0d82c900c404030201140c00a018400480e881051805000d403c082c506a0b00b01340c03254802c51800c2401c5074410110340c071480a000c1541008010900c01e04103c0c8050700c00e41c0f500b20a080100952a105a810004503800c85849544a50054440c5c080c0440c820b42d41c9003840d10002000344c000c1c1c0285d03403207400b40e0840042e20130024110008400c01108604511600d41b104100c001d420105505144a08041603207000050921040c030100704842c030540365001005040c00216034a1840c44104048a10001d201080e0000200c075404080c11642d020155100300030081113024048108200760388001d01c039000c02d0f82008001c1905c0c042170780c0c01c0000402d2030707040 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 866581762 1250 866580512 866580527
    0x20f070b10030512160b0903071403040510080f13020f100e09010501020303011805150603010e1b03061c1b08070305150601050910021f02090406080a051e12040b0301080d 75
    0x50b031038110041c00d0340001200c462041f6404a608400e490404800c0e48900101c484801c1c0d415940313400016040c482e5140140e24000c0c02d0700035140c0390322289000c0960410f0140060000f0948107841a10340086544090044052040242c12520f400780107450181c00f8050269100d88551f400d80008a540c1d48000242d17812a20690070548240c4490b0030208000d00b03000e0107070032180302c405440e034502d0307103404000318003c3c1034522808540707141075482c200402c100c007618070030055070230018011141e640f150012261125042c4181940846190400341a0140c100a854158507000001002c840216081c01120702950940d030742001101da0100c11070320110740e002d001c00d000b4401c2c2403943c01c020f1841410075565004480c0426000d0601802c1d02c2e40508003060460f0700020301002504160103148000c0034050010b040100c0385503141500ca580c00c12960060740d940c6011018101003c010315460001c820300e526550380c0d02c0e0980d00d90158001d0058504500c40c0c3c000c10488644034245 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 866583012 1250 866581762 866581777
    0x51909060b0c15041b0e06030c0a0e01050f0f0a0905070807050a020706050304081b030306040c0201110409020f071a2401120e011413050601061d04020f070b10030512 73
    0x1411440003d6801d00311035000107001034403040000103c540189a07083c0403034001c0d21080d0714118003880d00108152800f0b1035588198010100580100a0462000a00f9040d680c04481a05d4030350f01c10340210301e0760306003115000e6002c00c100740c00059202c0198095401a80030b40c0c2d9050066803a0001912580b181400c440c0040e400380382c003080a2407240014581081c1308582c001d251a242d4100c80c47c15030842d51070413156030800014803020b4a00f51251404c0c0301d80c01e000901c1451402c082012040c000c0b4420b00b62500e400084400002510030102c0712000c0d8403e484c100998074282107603007614802c40741c1c3c104c10b8491117401201120394543e13040c036a800c16940c0f40304038402c925a090140802060910a0350f480e04013011003c0907141a55100e40285501e200030904a41002c600d40801030b80440284049080611045c21b105011054860000da80160b600c00ea84020fa40441c421410040d18404100d000e10030162140d5801c002102e000300111440c00080171031000c0c00b40324051 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 866584262 1250 866583012 866583037
    0x31107050c0607020d150606020705030f03180d0803040303020304150e03030a1d0a1b09060806130206041214010f020c1504020f1809060c0304020d0201080a06051909060b 75
    0x4044240901e0282c00406a0a1010f014806880035644c0c0f0000d010340e41000c0c0c05d5405844100078014aa8108001c000510048006010713030380c0c00040c21070b240c1c490040e259181103d090f505409030303180c0c1007428400c5c0341d04c050881d58030725150a00070000d4100b079504440204032901d01d0914410b443c000d028250030344402035840c64481c0140700006281d8003021031880d2801034503009904000f03011170490a8000c05640600d4401c05e0090302c1c46060035044000000c2c60244140aa03100009450707501410103400511030840754000500e103070186900c080e000a0103403029104010088c00071a2205c0c0601e002800038201c060200401c1c2e01500c49885816445080058001001740510b150040e0024100700c40b000080c101090b5900e003000302c433a51075910001031028480c4200704031903210110611007815410a0740c00111114298140030b4108091074000c681d0446250f03001000901004001a0300002c203c5550f006440061041c031012514208000501402200844030004000c0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 866585512 1250 866584262 866584273
    0x1e060e010806130509010f110406080105060d06030c0b0910030504112814010206070206091c0519020c03010b04020f090d0f080f03060a080a021e04092103110705 71
    0x60011100300400404080e032118104030803861070003c034490700b40920300c004000320700740c1d40110003d000d03907804600c00041c0c0002080204105580060f185040d101c0440d18079070b0310380700c1052144c003400603a040079001102814000444aa00b2030042c104270704103842902c0d1078074070348809500316034040b1801380940100c1c1300108100d107402400c1000c0305d03103101c003075080da4084110800b2510340b0640203003034020200ca90915a56070100302e40355020700c00e44010035091601c080140d45400f61041001688100400c24031880c502882c01c4d00e002d4005054a011151aa108000d541c0c0321440b0585000b03500c3e11040d030304e090415000301c0301c104108110062030300d000d0394140120060031741c0050740c142410707004200018120303800400b16034038400d41e0242c0f2818020304121001003958440f00c0f0a41c000e00e20200181c8ad0b040c040d02d905601c45c040106455004400314025000e00c0e180200180b070f00b0b124940c41785403401d9021280501981e0200001c0e82e201109118520421070041d1650703214 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 866586762 1250 866585512 866585537
    0x310050625120311070f0b0727030b0c040609140d051b040513051e190f0501050603011514211b01050a05042c09071e06 53
    0x528000d012101030302958021240d5080000c09901c4400403084420b60703a2021411019075040c02400c41c030402d100d110341d14007012683c0300b030f014144009000f404811a04001108640541075407000303140b0034546208202c0a42610981c4030505000c1141c002100700046882c1c00301500550b003d94107580c6982e0742240c20404001c646100e2007504c6540141e1000354100020340500c1081340c107140564103210007110540400040e901e008100803030800200040d42e011480004103100c18002c010b0121000e00f550744811800c00c8400c101c1a07230140340d4074000a040003140201c891a180c064802081a40c44000404d802c1e2a50360740d01000c03d502c034400074130001301000c0221840c0e0200070040385d41c1e02014494401c03142080703080146c880d00005141300400c070394448048468a000d1070014540002098040c041e030140d0b0051004510411403412a40314014869440e00145880040004c0c85c10811302581c500060240d05411140286040701002542c5c44210598503541c881310504041d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 866588012 1250 866586762 866586769
    0x5090f010c05010f020c0d0e041b05070501060504050702030706050a050105030a03260709061b020a140a08010219110601050a0636051e13020f211b031005 68
    0x194195100d560380c4903040d804c0501d51006064050040003d0030441e40d401c01c000e00407407201401350707000710f00b8006040e045810310322814909000301d0810303d44403c03650925a004060507002139400c28902424802c12a4002020b05145031080d842403149580d003006480c243c81081c4900342c0c040d8400c01c07401c1d000034050600e21144c0c05104d0340c40c200ca81070380c66200c00c05c884191103c00210301501c60a010240d80700c070702e5032043d2100341c6081c03000240a41c04164000c1c99407003a00e10b07000550308503003904e545110310710300201880c40007592038007411510a034202c61b00c28407076800301d11609105c0c0341184d0007182c040d0403a007005081d075030b990340381090994414540305000350100e40302c00400100350f20b100195101540100c150030341340a0a14062050b5131400c84600b5810014038801d040c96656120200541e10202c40005038450241d1a0350407510301441152128081100499081006c80440c88620515442110f00700301e8005201280d100c0c407003503a084c1e581004451050000e400e = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 866589262 1250 866588012 866588027
    0x22050601171c08070c0c0b03010510171602030f03100807050a030312090204110a200703080f070302070314010e1b0303072402040303091a090310110d09030c0501050705090f01 77
    0x80c00d003d15104286d9444090340303001d03500100c0e0582e1010005001e1424848484000c0e4002800c0a400c0c64006064801c500c4c500141802d080340c845112156480744240160f42c01c0390703000d4000031340740c0c20310051415441015000c3d400c46807103207010003e020301e1722034030030000c41e5015100e0f42e04d52070100441030040d1451040030f80e0010b403145103808011654000902d00c2d182c0581d01c801204d81800c50100c000300800818101c1036010980600200c1c05403c00c60b90600c0315014131035641c0285103020f07030401c03901e0b60019000300c0782012210000740701904034911130310081c0103440509445038016860b4541c1115800c0d0590300030300c40480000c92460500e01205100000180580c8140c04280c05903801900202c0000d00084401c01c840e0041c00d428bd407000740a40301703050401c1d4410b40441d0740c4058103600c4040590315421003108080c0c1042c110303442e000036100180f2225100e42000b80c503080441504031540e40c80c0c40002602d03d403099041d6443c0350401085440a140704000445092 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 866590512 1250 866589262 866589271
    0x7080712020f0a051209060601120203090c12030409060605071707061b0c0204053d082a0405010308030615091e03100203010b0405040522050601171c08 67
    0x507a82002105095a8044080c0c034032658a42e503050341d03c0c000034003010484c0101400001543d41306005001d000d07a04440d1f0b40d04134030010030b00141c0b2990b8094165140c9902c141c1000e810103c0341644010100c0c001c00203105840d601d5005000c0d182c2d4408007140d59207e484006010400d2120106e40c98101010040c9500c43c012076001c1542c141a50703180740441c9035000c0e02001300d4072038209101103041c54000c041e8864801c20107a0b46421042a503445140e801c51960200040f1001100f080c128003400d50f01c02900c080c400303c441141078043c0c0080c40301c240b000f600818101c80c4210b1340c907510702409087d041c2c03a171000c00c17181151250b00a01004606480100c0f48032081401510025110200d2031054020403000c2000014010014103041c607114900001485004000610070700b1519270840d81103810558000446e560b819030000d85d1a00c05407400203002c02070802c1103090100014115050780c41c11001002e078444040c680d15620b61b540d0607407060b03910041b155480c0250007441400e0b0710 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 866591762 1250 866590512 866590547
    0x140f150c0711091f06030e060703051812040608240415180f0b0d050c090717150103061d0103060b0609030d0201020c0c100219081909051008070807 65
    0x41d228000000c00150003100c2255110b440b1110780307100510340c103404c2c000a01c4141020001c0c4481e00440c20707142c00008203240141900d07070b0046450710f80d40e9a0b03a000e4200700d4100b07580100502e1400300041e903000e8800c200c000f44022001c50b03000901c1542c00c074014180c2103a0121500014014000500078181032900109515440020300501c0441240c249080000c0d000500d41480c0541004846c0b890103540c2c0a222504020710004d43c0005454022a1045888502c55038401c0030440b054840b0841e201254150002408040344070b4103c499150070b03098030148460360710f03011003181c8401422240301c0304207521001000405d100d40c3c08070407400b6000e8560361810340e01d000800e02d04020080203800503940000d0010020348240010085101e0807641451840780f00c4000035510441c1d105004e0501400342c905034108920340007101c00700c0c03c080c00c01e00140b4000340c502800030340c418403405000e803004030100c6410901c07889481c0e00c40c05d45612008816115000101c03000e8001e541c080d00c1 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 866593012 1250 866591762 866591783
    0x21b120c190f0801060e0106020d0c0809041d0c100f05040303120204051215010501030b100e180a0e06090a03021510030f06230921090d140f150c07 65
    0x20200299402c04010b007107403100100d440e9141580348400940164050011500b01602e5860846d600c54a04949690042c1099403540a840006001070001e50303200010020120003086890303a000c100b40b12800000c480d58500908550700548103c0e082ca0343c0040098002c00040c000079005185074690041e641d44c005003001e0f260808605180b00540721035845a010342c071503200380044a101503001d00340a2800f0b2050380c42c9100802e101e810103800e44800d1000d0103541d40300390b03242d114204d2060070b007110522107281041642580100000d5076014407034003a1400180302e80600182c50340186601d60b000f0b05c184210840c00002c0d40c07401138000c5000d508c1800d0004041030014806088090148100007040c8030902a26107524503840195054801901d003008550400403408030041141d0072031803025003000c589812000d01c03840c06500c2d400108050f2200a0011000150450580d84021540a00043c1020640d5070106107083c0c003048440000065682c04044058440b480c49901c1005 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 866594262 1250 866593012 866593019
    0x3020a0b0901140a0e0304060503060d021503070e0f3a0818011e03110f18120316170d0e06041101050a0503061c05070303021b120c19 59
    0x2202039602080681d1600000ca054600700ca16044d008250b03880300300071403101c1c1d089140e02c03070159100c3c640038010040001001c58486180b10410360b50300524080083c0da10b040700064032380058851400146c10041d05c000e140c107000b040b0700000d400c028000094420f0344408151012180c1c0b000c0e4481c041100b0b02006800c50107914110030758482c054058075140801c81d440c4a41c442e511011781040b006440c444400080a0042d901940b86403801250082e50100c020b10f25125112402c81d401e240051045010384101c07042e00303005142210303804031203822008126a2070044814403042c001d810580c038000180070301c0c5006010400303102c005092841e0405028101d58004008828a030046801c000070010701c030030f0052500c0340c01d090490400d1803a40c0c0003009408020600d600034060b10b039840c1c003400044000c480c001944801110642600d0b460000d40b01c401c1c01c03a150007101030510859040345094507290010420000007450304290079010040c2c0c4050001e400a8481248413010 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 866595512 1250 866594262 866594273
    0x9051e090a060e0403091401090323070b04061e03021e0315090f040b013812240f0f010e040f0c05040e1e04021e030a030c14072103020a 60
    0xc2c4c442d81c000d4a90a04c2980342c040d909034201d175541d5515040207131916040c40002d021505080d040449140f203580f41401d01540d542c5030403016040b40340c041001080001d0381603480306184c0b03585801c0c1c00344502859002501902a80689440c2609050010308143d8400030701038050344d482010b0302081c0e961031070781c0c001250145100791007000c0310b480e09508000501c0180b200312401484c8211402c010020a03840c0641e4007400110146165514003803090402c8071200107440e183d281c8680c0f0449541001c00c184110b5101c040020b0ba603200510340c001d1141d240c500001500031f000a440c0c00708003550140111010b010b0000e2460382f2603510303400710140310680d202c0c0c18103109058581c20707a900d05080e82908071403401040d060030700c1d16880700d45060385d205050341c542141d81564480b07108803d01140c50080048a48516007610990080c101410b5000c40780079030450181d150748420000d0901c0d0941c88134054050407400000c4d13644901d1080284486924116001c1c4c8151008001c180c1d95a = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 866596762 1250 866595512 866595539
    0x904050a0b010b0909061e0d050c210d09060e010302030703090507060206090f0c0f01050a140a0527010804140115030516150e09180a05010c09051e090a06 68
    0x111501441c080762101040c00c0501d9400d80180c0d00b21007d046031218003040291a03209520014080c2c519510b190080007401c22070003240a400030955a503026210b890140003601c002c040c3c025500ca903400e036000da9030241079190141e91140d40c440c6500400240158041d41c405001001051307039a046110202d01c081c0010f0f4054a0141d010300554140340c0081c1d0301c0c0c15440050b00480380c0044a40700310503a52070010105041007801c0c9562117254501c2c0542d00f03010144460582020700154094555074800002d08400450f844482002c0d14a164050141d440000e403603400720b1648000310b00801c11428118056011180010400250f0411000d40c02e11196000312103650001610031503d0b040c40c040c10000e04a0201f4211180001190080c80b4510040701c15015225040210f06000301d880e100d04100c038004030840d0080034491400600914208902c140040c4540d580810b581c07500810a4030f0740e00f00924984c0700204540c0400040c00c4000d410504c5880da903040c0060102e032240340 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 866598012 1250 866596762 866596769
    0x612011a0c24010f0b03220b2805090316110402160c211106090d08030a0e0309010e130e06071d0d081902010b152203050a020904050a0b01 61
    0x2003408000780c030741c4842d811040180c101c940e0400d2901010b000002d400b0082d0b0b40d00c072102c20b02c03140415003501c002c0440890070701000341480e020b2108100c603401038030385400300d0500d02070342602904030480500011030307000741e4a4030401d400c10400d01455a00013943c03800b42d80d01036a03a84241e507010b10000342c1240e000c84520244808258002c6080c4185000c3d024006c00b050480102c94a1003128504020b009400e401400e003440310300003007030948460080c0d44201c0700140c400d1046060034100301e2991b80040718401512030412980c01000800402075422529068643c1190200b003982000b00b15040c81c1c3c0c820319034661b2441c00711110002000403d01460407a2030310820140c010b820302c507081c1c440706561f50041000242020006030074004a9207102c80d00c50181202091104003240509140c05d0161b512120999441c5d4024544500812006442070381c101e280600001020b100304c2458130000d025038200c02c0803080581401d000159100348100242d8000c2c1c1101d0b600d498240e0030070780 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 866599262 1250 866598012 866598043
    0x606122a09301b030705040c020601180608030706091b06020601060c05030f0307050a090b07050a082203060510060c0203030301050120010501060f0311120417120903070302010b0612011a0c 83
    0x80b07074000c041c1014017210014141c01da60078001d074110004040d60310301c010b00c03e08041c2030208075000c008024640c0508060a110360940c1d6940e20b49040070000b40003044001c1e07031205e50f0071413810010320307603180110203e03042030b0050000e503032070640c05071032883c402602070320240420000c03040c22103c2c441c000c62103200035481d403903207500800703600a0508065800c942d101d0305041281101090000800000059000e0803403070350398807241a00b0b01000c1080500750b80301c0a03083e8010081040e1a006188500c11031045034100654602e8212114400044040d401d9042040113000552190400c64118940b003080b5403000c4e030600c07003150b084034000d0b800b0500144019a200a1880d810b015031080c1b00e082c200d0890903d0713125480452856000342009040c100010210811111414103652260b401200c2c0310790185011f40900340c5a61000c48120010f51030034039608050300e0701c2c505a400e41c0356165028425682050315142050510951103840301e4014031005100340d030200146100c1c020f206 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 866600512 1250 866599262 866599303
    0x1a0603040c1415042309010317090d050d0309020906190b0702030106030b040803041205091011010f06030f0218190c0201140403020109170309150606122a0930 70
    0x1074240130060254940940710b44100c400410103d4034882701c40484071400c0e03400541c1c540c0c0540000f20b5201a8480050460245910100120b03425900c520011030007078502d4449582d60108100310940f00a40c9100585c1c031000c0248005030b40c01015000d41440540001282e64417070f02d605854603012101265840c6001081000b04010080412210912800e020303081100800004000110f000410b03010880c0b810504407140d0000d40004c9078214401b0010080551241441030864044a50a0340594030b034051102e44007070300c062020b00c03604070304044c032500302c10051860001e44906001c0e241150748881503240c0c00c550042c89540258407070740001800c200a80380c0780e103200c1d5404810050400041c001c000d200324010a64511580c0340404c03440107a9200000200c440c06050052034100480e5004c01c40d441c00203030b4010ba030f001040001e10890030400325401c0e1482c072a01c80c0d0f140e0080f0f00801c900581c00b04a0044a05811401d5160403114003000700003868120440c45203041048103 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 866601762 1250 866600512 866600549
    0x22b27050c0a030c060c0203070306021b07050a0f0608040f02130c1b0b010b0f0c070605040302120106120609060e0d050a11070305150c07080d1a0603040c141504 71
    0x800401056040c19a02d0050461443c1c4800c9841d00061240c10b00303002c0c240a552085560610030030006d168440340440d1201100c5144004e0004c890f40030b40e00c02e104a8102089900e09124090115100c18040c0c0f6202410175100b210f0000028100725080f080015010b070059568071051a1442c1d0a024001032020351480010000b05011000300b502c44292003181c2e0124034580c00c0241500c101030085a50382206000c07184161050105540d4107014014000c540c0b03e6001005100302c2e4000c68112103050804a03049080302e100744501d40d01152217855000001c1e2840d0000b540081c050903000820303080d0020443e040009070001c040008100040f11031903103401c0600061000513070801000c1060841d0f503103030b540b041c80d40e00120801c803847e40060095006903044820103039200c0350300c58881506540480243c407402035801d074445c080065000302d0b4102038082c0d078800d64110040140151420002c200e900b1408a100c98100b030b41d01da058450610f8010080000380244000c110b0030702c00 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 866603012 1250 866601762 866601773
    0xb030a03270806220c4a06012003071b0b09041a03100f0f1e0f1d0607080a0506031b19080c0f0d020108071407060c020102130801022b27 60
    0x8404c880b0681c4030006242080d80103800c1105400d0703115045d50106d007030b032074200040c2e5040004c428506c1703081c12105502200310350080b0160411070b2207941c0005005aa0011001d0356403600c0c00346944624040c4480300040c500390f00080200c0c1400c1c010800c00c54510030100381000c034100303e0301074481c2c1c9602c1d42c0e0054a1292140e001c044500c42401c010f40b0070050720b00040c00211004400c10b0989804c8000c040784042d0380031300f44071104c50245022050f05400095190881200c03c84007080c4050000303900e9088a000d045c2c82000024080c101020601101c0c1d070780e1295132503203180c100c1a84007030040c52401c0d02c102c01e0040c006100c0103050400300d03401046403031014030380310500907800301c419140140d0700000f1082d0001914101510060584405101c841c007908a0140555080041d250b03001901036000303142d09040c3e00c11222040d6160f0020328283c0c86400440921250b48160700f00c1445a44038071001c0e2145007800200b03c400b601442c14048038901040c082e458806200e1302c108010 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 866604262 1250 866603012 866603069
    0x11a030706090e0c0c0f0a1a04030e01031d060a020d0f02090d02061c1401031209060f031d0304080708060f01210203010b030a03270806220c 62
    0x1100102411410448002c2050185100700c0d5100000703030380070442d102016016515a00d00610464010a80000d02c1c6580c48501d418260707408078561514074014170350f540c6070620031030701a118150b00100304001100200300c20b034080080c00d02500b0201c00d840a007031100701d005260400003d030720f501303107402c8000480d18208103001c0100c4c030410000045071190415400050307011626184c40d800590501c0b20300802805440403aa072501d06040c180240c00645a410389009000c90940b50f41c0351501a6080e0005004640104107400d043c5001d2074403e4024a550795040988806801c1c22981340341d00d160800d13001160940c10221342402950b00800c101640003081c21480a00303949858401500d00100c2ca2061070f120017241c9480d41592002d402507000d00e20017a0072550011514100200101e070502640041d040000400394000a406080785050b20209005080700d03403030314442d40c8002000400030041c2d1035681d40c0914081401e800c031080080103882514003164180420800100 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 866605512 1250 866604262 866604311
    0x100f060203030610141603050409050a021e0c0106050901030c03030f180b0a050f12040c171005101e150f0c0210090f03030203180607051f02070c060201 67
    0x6500500070001c0c03599621025040c2c4d8509400c2c42da07595400d01c69503c08612a001e04c3e0411003910308520720400d41c0c08401801140e5a200042086c3e494900c00401030f440b81d000c500c003200c1e1110004002106a100042003040c00410000580c15503460218010348026801a1800e03001c610b130400905800041b001210f1949140020103c5c001e20850701e04494140203c0825400109902d0040b9014204454011081a220b90703120000c1c1d1048500701ea004480440728010381d0b11001490026120000d078200040380043c100503500c4810050043c42c2c001d00d00110608404800528034180c101c2c0c1c5080c0c1007410a580c2c0c105420422408000c2201e13403006002c0100e2040769501700b5910070000c003c1554101c03a0f204c9680c02ca0581112240d4064000c03807415001218000205500040108010740c00c4000201a82a0007030401c01c0501420402a095400c080c14003210244150090020810700a00060401c510354031030305000121600700e007002d82e5503406849074409a6074520f2522 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 866606762 1250 866605512 866605517
    0x40f0305300403030c050c09150112180803060a0e04030203030f0c1201090b150f04050102010b060708092707081806041101050c010b0904050604020127030809040e06100f06 76
    0x400301c1032800e0380c948101d210103000c01058076a003008101050010b2207101c440105242494105640f12421156540c90303204c1c081002880c41640850b001c0c061300722030643c1d0462040302d10030b0a8a41c521107900003005958099050380001c6000715100c10560b005501a03801103490345840d400b801403210b00607100d80d10102c000d00401141c150b00041e05070642d0780d0060f000c00c1001d0600d0208900940140000d540f40c43e0101d04510000c40f000068401c583d002d03402400485d641806200407485006406003040800300400080c07402c2c0014402c150304454a0703841c081d10112080e401c8502c00564840001075110b206000a02b040c19404203a41d0960b4800b03441c00f4206940d0301c40400550501c118180800841d5040c0003140039403050244000c003600c000c180c2e1815181036a2a00000c03203003203020540f400e0084801c1c0c510314914045c52040c0564115056003140c441c3c2d072154101c0d400c0030742d1003a00d600012880410601200f8000c0e0500010304034810f007401c80440114070640c205004 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 866608012 1250 866606762 866606833
    0xf17030702130c110607051e090a14030703150b01030506060c070510020a0b04080903060903070507030213111309050901150308090103150e06030c10051806040f0305 73
    0x56666000e04034040d8114403030004408154840a07104941c2a240b02201390191030100003005412100509041e1401c60300e0000104161640300d5040c042c50210345d410101c60081407100300100c440c40105503a0080031601c420340c0d0380ea80c4050141c54614030104164031000c0000c0e00d940c06004140d005031080715aa81000700d500c113090f580f890075110303641c41800e0a020004105009100c8034400540140121482d40f0b081c3c140034816510000303a060082c460880000c138905404400d0790304041e401006440c44070f2540d002c2040d02c3c0d22511460041954410100d00030f0314a40e801803009201c80c44103205003e10f4804c0100c2103034030088c941300880c1d0500c0402c1c56034245840500060b2030380900419111044103004274020401c50107049000625008003007201002c4000d0310303114807030803021100c0c5010034900b070112406a40300890040f407014400c008400ac008992034465450280c6510309080d81d441302005045a036500a41c0c094000b080614003115000300c46501c903d0700c202c9600b0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 866609262 1250 866608012 866608027
    0xb0d1101081308161712010f0f1215111b1605030c0103180b01080f06010503010c142209060504062102210a030f11010e030d110d060f1703 61
    0x15a0344a5050514008a140c4d201441003000b01c2d002c0c2e00009520b0024035442d000a00b402c8401e403e028040e900644240080028581103140ca9002c1540e5880980007106420707541c480c40c4035038101004a41441c1c4440b030f105122182034015000c3c0e150ba0040d180410000d40c131460341810075a000d201401c680025081c030181d100041c511b807880401380f80000c3e01c0705044140926001c145c0740e0080080b004600001106000003566010301c50408064540301d90740d8404240c01c03903010a980c60085010401001303000340340003000d0508504803040f83e01d42e800c400c642644200800b0f80204600d2a070341d88050165040038800c1c40c002e0400000760562038041c5118403030b0200080f40009114101665030b216450b96500c604181d070746225400c58402156034130300502a44d10858070480014002c0d00c102e80100414020b64000251004c00f4518144500c0809005000e0a41c0701c1034088500300b2180c50010340302d2049400808408940303045890500900070400d01c5803885001d09030340148400d4 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 866610512 1250 866609262 866609273
    0x7050307080703050c0a120b0402040e100905090a120507050a06020c0d02071a1303060905030304031b0f02061e0d02070c060203070c1206060306020a021c020a03120c030b0d11010813 80
    0x40d071b501c0059080c071071516000103400c1c03000390541c4500140c100c0c1c00410006542c80d0b140a5041c0502030421a000032603480b040982c0443e078080b00c0c100440d500480120b0f0204094000d124104c42d06454228a00809034844a1904500c1d10013195415400038005220140c14811030032611114400313820300728680b20b841d45074100200c5d0941045640000e210080440c501750f940010360784030109015450583c106640c5035081140c0940100d035061401e10591030110303083d0111240d0180041e4401c041c99021300400740c106130801d030045400761506041000700340e00a050020020407000d81d0300c41c0c1924200f03031000d190b54065001e55000740020303030001c0c4124000000780c906200102e032900c4221306104000c0c100d994000f8003032604c001740700c509856000c1040d50680620380c907081c10503896180100c0e0754400034a4040c002401034088864500c6d8590040c50083c0340a00d00812107000c0040000c101c2c4103039060441309100d513401483c030306581083d242d544c0102c166002c110404003035180c0c0c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 866611762 1250 866610512 866610517
    0x3120914160623040e2701060801150e16050d060e06130522020d0f06020d0b03060702071403030903011404060c140706021c0501060528022d0607050307080703050c 72
    0x40580703417001980014070f2908032140c502c26440c1040b84038030046000f160b100f8002d03c0c0340d0043c0d003410350174400c8a800924801c060f450448841d000d207a103d03540c8502814007140160300c0c2c40030030044c04000c0317410510365502849001c0e02d4000d20741d11560412404211565078000000340e4224203101c100325048107006a070208080b10300a02d00c0825119200180031091100c070006d1003180340e0307131140301441803c0c2d010348004113003d4002c00c5050320781010540d032014100d404c000140d000308000d01c0202d2145282c0664540003504030b038209405c1500017803e5074085a50201000011000c210510100340100e10f4503030341504140403c0c01c814245513280c2d00c0340ca40041c0500c4d8000640c4140340706034001481c03011410000400042d40c680328003c00550102c002514080f0701044107600000d40a40d2020300030071160002e1203001c03010700505440207002112014509008400c010b009441444124412040782d964507035207150480d0040c02030a400340803542014580750401c01c0c140064405c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 866613012 1250 866611762 866611769
    0x1050f0307020705061801231b0c031209010e03010615050f04030605130b1303080133030615030204080304031b03050102030103051f050709090e12071202010e0a0312091416062304 79
    0x100c0c9424443d270701503050b2a06440821b05074251003182800303e0243d50380305c05059500d00907621184103191000802d8280d03042c80c0124002c1a105241403209503004000509012103c1103078130b401c03e0340c3e82e140e072800c03204100d44101b080c00411030711004018142c11095032016590405e031a14445a031401414044140110000781e0345e101c644004541c0b48035a2803a00a881ca00c94007a06001c108004000d4821449504201c9100b002d040180038003900030382c0e00b0340300003c0055041500c0c645805900c154100302d82c0120242400022001c00c0007800154013031030044008140c3d03580c0440c1440310001c1d1000070b00350f20707c1c42c120074410701550142c0c0c1282214010703080495840c0b114115141405c030500400c0b2484880018001c0030440741008844400001c0d0300200f050b0044441030f16103629281d40c008000076a600c07282185a11143e0204d00c9660081c9171400702604103000082c52700c5040c050005d41e00703020101c10410107610180130940b2401060385005540701c0c813031070034480c2c2c040c0f0301 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 866614262 1250 866613012 866613037
    0x1207080a08060429090115080a020304061d03071109010312080402030102040f062003030708011e1203031406040630020616150b01050f030702070506180123 69
    0x3000b207003450350781c0c1d0051420340d50200310000c919207002c40c2420602250000050049201c01d0001070b00b800254010042c803041c0c0e88400d8203a5486d100c00c54025400148100c450550701da250f007000410000300e024989403460021a90343c80542048003100c80b02341150740c401c06d21030707006000007003c43d201080840028202000583c80340e02c000b0f80603005580045400114480c0300051003944a50f0045601c0b181c21075410084801c611aa41c40384002c40e01e200c00314040a00402610711000b50405400703400922021100761500f03000719045800c414141c00082d242d15480f940742032881081504040d007100c04010031460420080c0040c0c21b4604402c003c04c0003280c01042030701c003160b0203004056004019542e140410041c00d00100140c0d0010786a625040d40e95002020740d610500d020884140c41b060b05202142c0f4401d00031b82d0008103000c007107000381c0d40006119190724014201854000c00341042d4034030444001442c142191009000c000504050021004005011213015030000b4 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 866615512 1250 866614262 866614277
    0x20c0f011202070c0e1023010c02060307210b1903050601090b1f030507020601090b0901120305160309050f041a040903110a200d050d0503060d020409060c021207080a 73
    0xb03082415182d13505070302a1034a1a0850208060400c00b03142210139500c02c0c22000c001e1803011504002d4640141d2030341c2303020070b88054006000d0320f0b03d4030140d5484496440c140c08107403c51240c4540101029452a840c84d031110403181207490300403110301c2d140581241000502d440c40c1ca8803641c8803010310503040c102d581c1d00103500c29030b1600c0c2003a41d080007d090b035864030089181c0000380113060498122005016440c008544626580594481c595000b0301b110b05076406c0104a1810000030380c0201c1c107218040000080f241030303160502f0884c0d03000b92284000380e4500024000301500032000700d4400e600d81400c40075401c3c09c411001004200986d17002400101e01d140503949030a80d1035006519206180d00c000c00c105c25680740b00480b41084d454003e040390a4414015000c00c06034004280303410404c90024003611600c00346510080017420802e01e090380d41c020a0460340c1c140f2042d54080e40703d03420404030707580401071180743e4903490050b44d203400003a886005c0c0d85c0c010324401d0020446031 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 866616762 1250 866615512 866615527
    0xf020d12020f0714070302040e1506090c070501050915010f080723090f0115050f030402010f0917060a1401080703060c09210210020c06040311270106020c0f011202 72
    0x1c10043c2ca040d40c1c1d000d41004280240052050394643c01480100d00c1607050940e400c003010004600401c0000c100e06004155480d481c041180712480248000c046d204140110804110b00b40180f600500d00000646002c0d10881d0380c0c5c6640c6481600100c2811240310020005041c0000b544422215081e9490450141c1c00e200c210400c3d840d5131031203a000b10b100090140a11030080300c241200c2c1c07600c031441c110404401081e03e89000300b400c1544451814800540507501641140318440034074640004110f450303d60110410840c9000354150354401e404008840a13640b090328200b000304680c1d06070943c5420b08940d655801400b00410440c1c580301c0713030001e01d8010f0000d4406000220000c24031895180072551403101e070404264484c00410700b00d000040d001180101052002500240c50176046840390740c0d100103018040c0d03400c001000c20034194440003c0741031980e0119003c00b0260795240140007840d25400c500e0282c4103200030381002c2801da8005080f01003400b02c0b001c025844401 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 866618012 1250 866616762 866616787
    0x807150f1d0c090a090b091e070f3807020108311e0f020306060f011b031707030204051206010f060f0c1205030915040b150d050f0109030f020d1202 65
    0x1030a02c0b005040411b101d040c030160200104090580c030341920341204e114480d0641a6582c7c640d24801c07440c0310042e1603001c1c49a51200300c0b808003404580251140c0c01010000c0d1441c461810902c640d02040c008a461001c5681c0100440d4003d03c0718040f4494001c0041003154061404d04c20112028041481c5407003081200c404125a880003981408000006400c210517071600410b4100d1080c081c05000650070301e00141c004c0c1d056803060356150358600801c442c9401c41c2c010701c1010340c203002511401810780344946550f0741c030644280c7d802580f170301e1400c000e0180d555402c0c40ea15030203420031801880318928140440b030850b90340b07181c80e41d082d940b080c5040d0303a04070040c00042c007e2032514651403090340c1c00c48010f5000d115500c00315103100d1a480600542c856042c1d40003040030403603401041201c0c20140f820000844000e2050200700c00c96618145030031011214541c031759465007051300505030803401480440d1894001b800c00884510710050030404113a5400a10302c3c1d010908103281c21 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 866619262 1250 866618012 866618021
    0x609120a0c0f050d080a021206151c0614120a0605040309050603070c030e0a03020d12031e15090c0c0f0312090b180106081203040807150f1d0c090a 65
    0x242c005111140342d409a003000750f110654801401c005c2410390000c110034200601c00c07203a02c903006603403400300798640e00d08201e20702c0030304006c002c03141c030b018080410380019500b00c01d025170b55142e83c005546850030b0302401c00f0b03984001102d4800c540c120b0001d41104008100311300d05541c070010000e55039072107242c29140c22405401c9940c01c030074040100140c8075000400c1d0b1052034060b0300c80d030141580a100300b0001003202e000c025045440500301d2030008090100458070b030a00d0b400c000c1100f001c91300c0070882450120b050f104110341c566802c609640014980c1c0c0001c1c2510881c1407001c0ca450320406482000e0000c401040341c8048002320040c5842426500303a40c000502c0b050008482c14103006449400903102c1c043d948102281620904405200b00e10888000070007400ca0000c5502c241c03140c2c0e40000f001610b00c800c04010780c8000805880c80d01c55144422600020f02104211600c800c031920074501c1070a0503203014a10001920000351840118000c840ca0394140e60b07401c0e010030182 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 866620512 1250 866619262 866619287
    0x50301030b220629060d0e0c04020c0706080a05040803190605030f03041a0a0804080c241e150f45010e070338120609120a 54
    0x242c85400d2254100b0600d50864070b0280856100e0000681c001c2c0c2c80c191040b001280030325480401000151201c6a5640168001c8101c220903510b00003c200d01050599000c4090505580c000040500c85190881c2500da00701e04504800c04c001e10b0107030703038036903062002030022098207204185030040111190810009840050196854070500e8488166a43c000e4081c01c4601c00400b542d10009408003425610083c04a503030b2041e2a8980e0f440f0044c0a13800240d075268280104034071280d9808164045d000d000403c100e00464501e0540c0302d0425050341350b2419100c8500f0300341131200d51828940300719a081c1c421201c06160150550005403041051590800100011034010308802e012042069a44014a0101c403811b0801802e400d1103820901483c25040320940c04207500c244207900001c440500c00f506403069100031041c0d9110040500600d0311062080008051541424a220183c00703061400800e4142000c190135900d400340c07440d045450392004110a141d50384600c107941070f203 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 866621762 1250 866620512 866620561
    0x6050903190605062e03180c03050a0c060f020a0204051f261c0305100806250e060d0203040807021e27040201181a070203010f020a050301030b 63
    0x41d041c0d28075080015080840e40b942c800c1c40414030800700c4044070b110300075074180000600005007004000903002084c00e954101080000c41c172044001a05c0000380c01d019501a83c0201203144541c504004c3c22035094106c0000c111100c90700a0a9903000100704e032040303504440c049415911845009070060040000e004c070400c07000300006203408020041c8064203034600304455034016007407140340c1c0c03410f03400e0f4607200d0103078000300b44031207584698840c9420001207400d865159071f41d0070140e894101c00340e40d56983c0c2c0e40c01c21030307401e0507035509039520034080710506106d821891040000f030200e02552411104e241e4000000808100009040300c3d8015070080c50030200c4082540b9074059554220080b900540f280d003000310030300162801280d071144103550005c465a50359801150400030450300013007000d01e01c0c40301151600c89800c24480450207130900c140c43d880070380109800d40f4418014050551302c10466249829440ba085070f040d04e030003004c0000ca540360090303000e00e84d0443d0400c6e01e48 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 866623012 1250 866621762 866621803
    0x180102090d060207060e0115030b130f121713031826010b010816030b040e010e0f160e010608040302100f020904150501050a030c09050409080306120d0906050903 71
    0x2001080d0f4081c0481d94080d43d170402140d00d6441c056030895641901c0343c0041c11290f4000c100180700d50480342e511890507120100c456216a03a038a103901c000da13408882c070a0640c04480540b80c0c0c0004810b2611814130b841c3c1070302c1e0920b002444081400c001024007004420301c000c03102510300300007040003000000a006081604050241da1010f920142e071a080c5d400c1c180c00c860658851014a4051001507041401c911400341055005210819079a60410b0b100c1c1c2005d00889401c1c400c0d0300b80312000c0c0b00502504c1d2940d10f085820028490107054800c580c41d081440700c1c4511014036810342d2001d050540064035241010f0b403400311490610b0704800c0c00c1c421840c040d0041c58000e003000c0c2e0b00270758013400300c00c070b02e4100340000b002d41d800f51710f00060041c0000052288070380c000040d452410701780722060b243c0702d00120f4103a4031081c3c003d440a00c8000140040b0381424001c1141500036000903007078bd60002500240700e0b148a220b05c0c001c20002080030f2285a0741400a00d202c000c0c01d031011134 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 866624262 1250 866623012 866623039
    0x9021f030e06070c150b010e0d2621090d140c010608101b0e0906010306030506040507051807020d12020c0d08090f0a1554020918010209 60
    0x103084203a1510101c4070305010f200e01c950f45c0d88050048005801d016115558006494002e2019003001640c0c141c0c1c40441c1c08954101d0803440e86034010340c4c0454014419070340e0001748000006100c2201c4040d200b01b011b0b03020810581c03408a5299094070591401071320060700b441d0902154083c51408110035480d0131800105100e000170580f80e800c4041a09006a10000c6000142d402080500c000451076441809440b49407180b0f060b82e104205050006200d43c4036215649440340403141107646038800a003c1c0030714540243e41c0e540350701c11145100801d24280e28000c0d1503c803061307001018803601d41500d0011100c0d94041c0c41c0c000e06440102e528582e00e26000603d4240243c4001665010313143e071216941d080170504000740c503080407540782e030500a0174001c001030409500e40e04c1d0b031610b10303103031050b80c24503411440150810040b80880004c40c01b0700109a80d000c1c102c3d118010030440400800161512040d2542c460300d144072a07010041e0810206001e48903183c05a40c0c060207641c5180c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 866625512 1250 866624262 866624267
    0x905030717040f0501090b0a0f02100c0c020f24070f08070b10050103110f0309030d02040b040e060904031b0c0e100e010e070801120516060e1309021f030e0607 70
    0x10000c40f0035150241212550755001915511018020300d0144107080000d40c07175175401906280b03410b24080c41200c150f5008500320200311380a400310400060320014540d401e40c0b0b0b10095800034004200e491106511085828540388408221000501000882c03107030180004062100c802c250030100260313466910b403900b48052030045510703a519082d4900003160f0703544680300300b145aa14039510540303801070b58882c00380a80c01c001c260000d10b10003081040f065100340d0000d0f00040c402d4030b00880c2c9640c2019100c3d0a01c51004100d00e000d9000b050400010a07400003400b40418030008889010384018100201d03040c0d0581c01105a85038100240a298114150158111040c090344811141d8a5041c1009254019210100001c01c00d000500c14050718551001c0070b14850740481d4120780d1405404001d641d4264031210106a038916030134083d04214400350821150f00d9410025141113074000b401b00107184203588107208203442900e0f0400e01036400042a11402c00032100b40e442c200200 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 866626762 1250 866625512 866625517
    0x7090515030121020310091704030602040f090239160602010e011812120f05040606121208090114041101030b010f1707030f020711010206090c0a05040905030717 71
    0xc5545082c3d91071100c00041120144040030b4990040240240390321825941018140444040d940041c0075940050001809001440110300c50940036031036a15140031401001000d50029113107074010412041d4001481005201035400d140c60201c40d1803401e94004ea203071811031000780f00761146012002d80240c07055401412189998028407190030740d811410300383c0f1000010030480128121003440000c2d030440a041509000746022a92036081610390019542401d0001c102941d036442030000b802200c1c003d10015002d0300950300100c10290b520000255100405030041103032800101d468800e00f900501502d11024112481d58242400e0080110000024640c0405e14000c03400c0042c1d4018540b1510440e8261110041c105140e20750340b80304080100101e01300769641041500b81038842c07000c0d203046801000d82e025005800400680781a5029003007058a9108000c09001d41d81c5403400003081d035005941c0410f8909003403a240c1e02d10302078040020840c805003a42141c1d600d000001 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 866628012 1250 866626762 866626769
    0x9020c0f060106090807120201021f05090706050301080619060515030a1d0316050307061d21070807020301060503150f010b090d110f0603070c030801080102031e070905150301 77
    0x80d640301e6681d0f00307000ea030561014481d102d050782000c0310401910320520a08907d0074018010750b003c00c217032007452450910f1031080794005103a5603800c0c000036807420032000c000b800003401c143e45154106101c0607982c150040c12404025030104c010300ca04c613000d0304003c001307081c041c12100381c5400c1c0150040460308203c039001c1b140c9180200c1c4942c4500c01d50a40554282000040c40c9032401e80903103030740c11980900741510203100400030b1500081091059429001010b0420404022101443c90812281601010146480100022400c84903004480340c080c0e001442d00d40d902458070220f400350446510041d41405401d84004401001c2c00a003071003007480169080f40380c0e0301e581c0ea0751120b010700b0307445641280140080d08001783c10b0a0081c400280300800d04075800c200344000454650007140c00d000041c2c03042034104101034010b002140500b2100d0025400c40c54044500c0f095580c400026900300307600b200215080394002c000500182c41d0180c0400390024600f0302c041007a600030710 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 866629262 1250 866628012 866628043
    0x10e03030a12050a0b1807030e0d0804060e150106051b07060203031609031e020301021207020f21070224071a06040515060309030405060d0b0301051012081309020c 72
    0xf0014040e001c05220700524590001c0c0301c021503010b030f41c9211110745801080071050643c2c1d64403a030b41c1c45900b04402084411582d80b0740145151134580382058820002c003000d01c562002e00ca01610b1080b1420b0507040d2022860043e484003504045940c42d01c030400311724030941c068090b000c200c01c0c0e4080700a5206400420031254296803050341102d0003141440043d00303000e03264a0710f42d032129000300060608d500040015047c01d0800c01c0702c2c41c2150f010748000e00941c4c85088480d165400c14054000c0b42c81b200020040c03c45021108011148507010f0005d01c07030138446803240420001c2000004020401066290f01c1c0e00e000d00c1c2002c1c01c0e41907902c0c1c030100700c00d9480000d12180351500603203105012074008081d0780e4850405000c034036040501503a12300d0100b440b020405894880242210400d54000410b11500c11010300d82126000b0341f2440b0000810902484103640404030a1000c561100ba500c0c0e441c480210440e042c8202e54006000c21400003644590012001424051482c1050f = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 866630512 1250 866629262 866629271
    0x111801122a110a0c05040c0309060507080f01080a050601050f0103090c08031c06061b0804051e0406060c02010f050a0e0604030b040506071d0111070504060b0c070806040b06040902010e03030a12 85
    0x221190390f2030070741c04018008414100188907a051070f40000321402810305020a101181780d0301c503419268210345d50000102c02000700025402e60b4a00503005040311409000e047d411511041d46411050058130b008820b0f500c1401885d034802e500056106800c0068881c005460705505505c2e03902000b0000e020004248509619061a20490301240d01c1910762700c008070721003228040e01440e542c8003540e80d41e000b40400119a201d0310011020704480000b015405005001040110350340354001c4406c201c2c00404800040c1d82003802c0004144590620300c0e190b0600d02422100d902c070240b030054104101007000420010041c08035801244a070303041d0f900560700d80e0300c00c5654140c8400702c1c107540345103d0080d1310154003d0001b0360041000d43c050359100783e207500c01310f42131740c507168808140754100181220b440314003401100041e01c00503018000508103500c60100c0c521001d803101c1d00c00c0e40d6030072482c002c680c010343d120066603a028050340d494000000d00500503d0000104000c0e05080 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 866631762 1250 866630512 866630537
    0xa030f03091a280c050609070603140609010b1b070617180303010902070819090503121305091302090c0c0f0604080d33050103111801122a 61
    0x54405032420781241c56a5401111045400340c803c50560140c80001d0001032061003000c0741c400d0010b1882251407034001c0000d40c0c90001c0007811034044e0424020400105014000160b6030012007504403001e820b01107445040d010351010561501011940c840c1c4a4500c00080c11a0050980a08203c4070300310700429668405101c50100100c103041502c1d50010001486500d0503507000d8481c00e801003542e20b0614080d015400c0307040300da540902000c5200c100c01007009140820801c40409503c55000307040c052980601c16003010715028581c03107110035100044155241d024255100e40c0c000700b194580b828100781c60700c09a80030144420b00c0f13006075201d81c6042c01c00050414041c2e90301000880c9007000445d999001440c4e00c2c80c01c000144500c2440b011410001403c01c10100b1160f07a07d01041b5240900150480b1000d58005000315001d00802c2a8501e2170080f00c1006117080c00d02040085910000100404001170b0805425810080c201c04040e440b1003420240f15503034030340c01d912503207 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 866633012 1250 866631762 866631809
    0x106020706111605010503090a05011e0e070b1c0f0f060f050a030515062419300b060c0a2a1a04030b0901050925140a030f0309 56
    0x403e0082d402c07090080e40042003654482c90007580e001c0002003c0d603c0464060b138841d400e66902840c0c4d206800302c44211007616901c1031085420106040c4001c10324289024481581402a007044032142045104540c00d5820f80350403c2e401c07441c940500f007102000c4880d14400505042c0501c200c04080c1d80d02c0032a01d410311014480a0302c0e00140185000c0c4100c640302744071344800410481c1c000c011112007096102c40381c1c013441c40658440e009943c9466000308015107000ea05000307101003003a166140130310b05c030b260f800344400c0b2500b411040c4a84441401c818000c0c2c101002915000700300001c0c4850a19401705590502912138038480c0c0d00300507007102001a02141d05403c50240f804444100100b40c202031140e80107402d4100300301c1c03c00c5c1e44d030344401051480448154106035110010060041c109200000c100320b0340300f460000142001401070410308046c040e022196039a42c42410f803560780c000e00140110fa01c680080c11107002c0b494003c001c2100c0d4400c2a50701282d64590410400c2c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 866634262 1250 866633012 866633023
    0x240203030c0d0902031005091c03090b0a0504050f0d050d060b07020a150c02040c11061810020d061503090c0b0c0303040f141501150201050c04061115010602070611 72
    0x4041c0911401c180307814a03200300404100c03038126418442c030146010221404d000d040c1c07007003520a000c1d04081d08004050603680e1080e40e9908209880c261000c00080c45110300c6030307005044002d00180b203541d9450b209107004d0138070758841c0c21032003202b982c1c3c00c969601800414000504000900142d6542c0060026a00800500039032124100e5401c1c000c02c800707480304171120406840e0400b240300c15034002c1000c807204401c5801c0022017028404042d05004c01003190800c009140254100022034200340d00d03540304000080d52940c00040e2451400c0d1542c0083c0003a00302940b03010074020201030054018888160201c850b44403040001803084040000e440c480b0345007030050342c51340e503540d41d60091055810b5822641c40b070a00d486090802c0041102d03401c50a88807003070f02c0c402d504000d46150307030125808514003160304100801c01202003250580b001c540c124180790548100340c462060070000442058003144007003a00000e601e544c0011000200c1c0c503a03440d20098165009019600c44 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 866635512 1250 866634262 866634271
    0x10201090f110120120a1b08030f0708060906190305030d02040f0f03120f030603060f0c08090c06070b060d0209070305100906080c010f050f0c1b030309010f120f0624020303 76
    0x6400201149164620180081194100b24904000700592031f1032115080702040b4400e81e0000c10120030052070090060285420201d2400c00e020303207140c010005000603d00400b801d015001c21101e44000072040003060307000e03560000c00e6030f1b00e4113607032180c442c0290058419010546145000054601d02102d005005d883e0800307005001461801420307503403011602400740070191384040c000041200c3d0b02c2102030210030481c0101c5c25420541c001858901c0142843e16140c0110501c0300d0503a031100111400d08d54014030742c900d04d549550004041030b901c241b010f500550007000300b00c07500354140e120714410a4000c48104900b03031940c02400c116941d5000361250780d44000325075802980103281c0e00ca4070103614580540391080340e1002017030702d4000c070496111582c0a2201410501c2454024192101c020b030000d509203c02040000e0403000040890707028050007426200c0e4040e503e801110682c851611b0511415030740b4200501c600a00c0107104565201144150481c40d202004a9020b13 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 866636762 1250 866635512 866635577
    0x40b1215070509061b0639070209100e28241202010e040e06040209190510080f0f0c0f0f04060608061519030b010201090f1101 56
    0x34404a1640014640605400300303100d400c0c0112900d0755a0500205440b0b10004524402c409510b90018940003028080401071104402e024014403039101780d0143c0c3c0c0d060700c51048001d40e0071280a0995224070b950280d089042c40701003012400c4480d20b00400c840c01041d1950b83c50392290b1341004200e50088401e0300541c400324148140c0070040d000b24840300d00ea000740400e040e2240720703118450380040d8411170710100844001da05560b008101c800342c110041e50240b29401c1c03070950442d2184002031009105d0313201100072580610f81111862924066400e00700400d040824401600316407034461400c042c8224040c252003440c000c03480c000000d400703400501c0c11269000400040d0800c89068540110090445d072080b0f43d2103004440041207079482c1c026050030410107110305403080500e006601d032800c00080050aa084550500d540d08078540060321194140c0101e000d42126034000d0555000c2e80604000c0c8a07900da141d03d542002600d6113030070007510944640c0f60344200040f1410 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 866638012 1250 866636762 866636773
    0xe06180303211e16020c09040b0a0e01060b1b12040801090c061106011a0f030c22030b01030f020d050a0309140102010c1e2d020c09151203040b18040b12 67
    0x2440c5072540c4c81034280d1202030040d1340b0010f40b540c01141d9000000c6606030b038404ca103241400300c0880d40784910301044045100a000c0030b42890041d150b284180d046481901c41800c207452280c1e581070214191011040450a50722a0744190381c078081c018050701074a68200d403880010b070302d900426031003030004003480140101ea8a09407400103444221188058801c0e010804640261807040046205a9011148903100c89000280342e4940280840750030380b01d803840b6014008a20303515403c80c112684020544000300d154404181608031006c0018a00c4c0306104000c030400d078012100b0740c1941e01c40c01d840d40c000078122004a007680c20414040c00402c01d5501d80603007620310701714030350a074184c030307083c00740c2c0210110620007640745040010f003500e400703682c06140f0b41d41d0381030289a027855001c8803070910340c1c100019580c030b4000750b88400f58810b030307207140c40004480e00c02e100740c8005094540c20075448280c40034000c4d04c800d9a11811503c40c9140c10444e06441c64416144945610312200400307 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 866639262 1250 866638012 866638021
    0x6030201081b0d0e0f070806240409020a060503090c01050f0409180203031308061f06050c0c090106050a1202070812070309020d080403051c0e06180303211e 69
    0xc1c10315001d40d40304000e442048400c940c001a4001d000c804135811008205550560301414102112078001080c2900010140b0001c808458003662002140d1070b02c081b4030b154510001380051900c0d09009400c1101d4107000500300e0b8101c400f45108501000680315181c40100c0115801d1060140380c1c482c0d960b0520050200440c2a80f0036803400d81400891101d80c012030700040e295030003101d12050903144036141032000340d0081c0041c07604210000100350819070340100c51780d4000c070f4501509081081c003107120942e641041000c0b000c1207a003c1d1040045507140c010040c020f60100d8110343c00f00c0d4900d44580494201c510803251500c1d045001c9908001400401e0002c1c15400f4044604060310b0b0a0040056900d5135019807100788030308104c44d607503855498041e0a22000072544412190001c40c0b031070b9107503040b0444c1c1101c00e030111b51036582e4143d0100070218a188580205070144804556490701040c180c510f4a403115610803086002d039644c515441c4025241d000319a031412850000c03c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 866640512 1250 866639262 866639281
    0xb061915050405041109150f0a03050601120c021b0a080604030e0114040b0d0b030d0806012708030306030f0f07090203060a0e0f1609031106280c0203010606030603020108 75
    0x1020650854070707266140641e100c0c00036054924003105c0ea10021030010b000503051030024404144d035441c8010079030416048035100d844501415080c0804d1546510000e061030707100d03450915590805d440100030040c071400b4003c0da04c08002042d4000101c5840c1c283c2c01078505800d0440484041000400300c0d41c1d01d964044410340c0219210714180021160000d0b5520000d03005080500f00420701a62500c950902c40826526402c888034000c1c0c02c070305a0b25805542c0079038500d900500a00b0000380c09094080440001e54004900580ba074881100114a1b0715012000303600411046003181c181102e18070300c00b616000f10140182041c3d000b60700c00c200c00d5842d6005181d0000300207001c5015996a5181500c1c1c000048800c0c0710301208520030466401c0d00302483d0b1011a4051901c10011030840d660740a00801c411102440741e18003150400358a0440c00d2844403800c4661204030746100b243c1d5016011a4031708808a100354200300380850389a11a1240604480d0142d540c08201e03280c8a04a = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 866641762 1250 866640512 866640539
    0x10050f0301090f0603020a0305030a260a050c0904061d1b031503011b0f03060e100302041d12030a1a09070318050105012c09030a0f020c100306030b0619 67
    0x1e910f580d403a01e030000096030f56000340000840c0184c0195542d183d05002c001d190340d080d0035030350b100c1c1040140f050840e0824124880e40c0314403441130004058880c1b1001c01064058038140b10b5201f401c0000118409030707142c11078480e010700f010340401103880e8950100071035070715462848001c05043c40020b0350b1403005080820b100b0000b800009001c031380c200c51320300051a4081c007000821100100849016410302c40d9600070705a0301c540f8001410560b03e5400c000c7d0492001034403d81d1240078607080d07131881280003042c564500e01111585004103050a62a42046400100c81c42c5451a40146108200022246618000c0948030280d07900d80003a80101a8000750120350b620044801300041c009100c0c0d140a04060804590401c02001a480c07011b0f0b07a241000032111120303c14080d000b88000142c414400032030414000c045002d0404900d06501c0d041440d82c0140020124803c054142d4040e1003940d020b42c201d640780b966040240003082500700002c02c00703090210010020302a46000707 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 866643012 1250 866641762 866641781
    0x1d040506040b0c1e1c0618110d0207050f15090705060c031201090f06090b0915061c1506020a0f080309010e0304140a080a080f03070908010c0201050610050f030109 72
    0x1205081000c0c030803d00820703400100a0740300b03440000500001e6100c85d09140c804606071040140401820401000c0c811030f1995142000315841e1044002d02e001c0c404203441214002c0c582c1152103190609080d40d4941110080b80341d9030060b08950740e02461220262485081407038010582c851601040c84960360003116401700b640001d019850150300d501c0002070003000b0308480410004109180340301100c580784c0c0520038940c170701f484100c41c9854a292859115643d4002d007aa0049808003081c840d218600c0b1b000c915009440000000c9865903001d521644100c41019501300e8840380241c2e503801c2c1e9100f000c1c00003940400044002128a4000c681c0700c0346c0440007080b04400840c6461a680068100701e01402d9200c00800c1541441d140300d8001780f000d1401800c3c22001e64807403240c2c61007518a41075071070f9000400500d406003d007171100028600c40c2d00821848200f641c00030300030401500d00b0741c0316001d103814442c02d141c401c0c415036095041c582280792461346010701d801c2c001c007035542 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 866644262 1250 866643012 866643031
    0x7150810030305090609030a030c020907030c081515120106030510080a02120309030d0203190f09150c0b0f091b0127150503010f060212070b0402190b041d040506040b 73
    0x341c41056202400240e403058800e03101c00300c80d2410be1041200c1c1c160020007000400d417400b040b00240550003500a5007103c0d4211420a5171300fa2900485d0000105081c1652030500020380311400d038807100703e624122402e40e50204101d8513031440304801494588540d071a42c1e4403a92105000d032030542c01c00c5040d8100c000882c3d01c0c100620340400d0a28078900703001e40141e040071a40588805031180582c3d40c1d02514a8507081b221203c10015041000901604140410943c414160715020b826012145a00001040c800c0d00d4800381c0401408002c035421200b81c005d861810b5250304401c80004103501058541200641d801d000340d00d000f01d000180c5840064600700002400c41560840320503416544d9680d41d5658180301c041100300c00306610103011948000c01041d076103100c200907291516032012000286890740d00014146044100140c924510000303400100441c2e0400240122100801d8903014030039131400310303400301104031030244c0140c01002c0003500142042c00707040d51190401 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 866645512 1250 866644262 866644267
    0x40e040b0a060e0a0605010e040209090106080a0e06190b0d02091902070b0408070c0e01030c180f0509010f180f1103071701060f05190e0a0e0a05071508100303050906 73
    0x1401103c85680041c0c41c2034200503910402441903590290300d0351301c803002c203540640c50f0850748030110341c503407605205001c100428900403c0504d02e0a401520808508604454403810901c0da00d110300c0c1c0d40303c246c1c2c1c81c92900e801720425403810192040c405003030f001044485169602da410071141824000302c00c60300d0b0b03800c003e007400007038a441601780100d00030310a082e156895403030280e8814a45030003560340403100900400000300d40070680802d444008030071410075055110390074080c05404070325500440c201000c000400300d0562044600000c5004188600c01c0b40902e22401d99070800000b0344484940704042c1c010480901c0f50502030000a012150b072196100094046a0301d1500040c00c540d46401c0f0800454000c0100038019040440d00343c140541d4170002400d084409218a5856092840000d033f800c08845d4040e00301c284045060341c042038017900d8019100d400d43d0050480d07a804058a84075103520030802940f0921001302541071240c01c0d91400d45141d040034507441d40c4007004 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 866646762 1250 866645512 866645519
    0x608240f0a0e0105120a080403111318030201051803030a0b0a08120702030709060b030406050703110f0304050d140f071b08030d0e161e0f06020303090c0303040e040b0a06 75
    0x1c859080700205080c103584100d030350500c000c100c400303281c010b403881959200c01e21401c081421202251b044079404558002043d1804002c2600c24807400d2950007190b28000c9a1084040800c04a80f503240c0b0a41c020001c0d0b0341c5220450203180c4c146104003599520510002d000c0c4402640001b80c001002000c190307215584125240ca440c18a01035481d181402050140c00c50808002c446e01504402c3c41c1400010b003410b0b100991030100400207083d103500c40001c0380e101c9001ea0b009803030300002d0b551003540d500c1c8044d1120b03646a0050700c0c03c441780e124819298802d6072141003180b01c4030406810b02481c00008903100f6855404c10502550b0704031090105484040e00d0300303e000c0060800c400a10b40b0340784148054011116030080700c4440d41c204da03030200b9035401003011031030503503c01d1044195000710f0403131080604855034214140381946410040f42458000014600c40c1005000f215516448a018107890303004078455070551010802c0824002085000785560241400500103001541d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 866648012 1250 866646762 866646769
    0x60f1802070c0b040609060e100507020f03030a0c0213140403050304110306070c0308070e01050417030d15030c060504081203060d0c03060501090605041407200a06150608240f 77
    0x19074405443c003000094100070450b00951000e00030300f030a05100a0f01c410080201c3c554001904080041141c00598402159500e03113403080c040002804032511140e24010191400120b01c0069101380907803150440001c1d10b5004440144000307542ca803803640c949030790542d055000a40202d0f0380d12500c00c10590f064900300f011301c1c070801ca86d030b80b00c02441615081c09081c5d68406001001001201c2100302c00d140d03048000c0b01d00b2179030784440341001d0f208540212030650041d404030390600c0f4280803402c04143d084140b260152401050780c01c0345150303505820b4034103101e2407080383c9494100d00410700d100b1040c070001e142d0100029044180520050352020582c0340c07650001c4554590b21307001070007520780c5803080e04c0c05040c05a030b0401071910300040c20548003100404220422911814403002c034816120303480c9030300c6c0c1c0d24001c8541400319454010301400c0b0560301c800402c1e0026000042451007003405034041d0358030200300d10000c21258041a03425440c1e00100d1740002011421440d581c4 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 866649262 1250 866648012 866648033
    0x2070513110a082a1c050709051302040e0c0301030203010c090e0604052502100f060317030c070206130303030b0d0f0f08090a0f0e07020106031a150d050f0d0201060f180207 76
    0x2400b91084c5944100c4400701000c0ca2014506002d5074502d00300401c20f5032070704804680203407a000c0b2285418090444d5200b0082e200380d4002c2800084803209004c4800d5a01000e0350581c0d01c01c500910040700d00700b40850307200140b407203588840d02e00e24002c1080c038107055010940000f5500d0340601000c50106000c204c00a5402c00302005070b0180d1502c001400d8184200903021000300740520010346503480c1c6800c4800041c1d2f48074511600000031900c41c5006104503160154094272b030f0707511516a02507000e40003415110a038040b90a01e402c0302c01a2500c0090300f82c00a610007842008141d45441c4d5410503104010100c54541e01040600f44c00d5691000c044010110001800440380c10070a00000c0c13500090103810942e03042240c14030000703060035002c10002c400444000f059a4a6411003108035100301c845c0c0341c0007500c0c1082c500501074042501388030641c084049803030040049104070300300c50140c070032054011910304043c4081ca4012481e41800c62081c40090b00340b9400780c03140d09014 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 866650512 1250 866649262 866649331
    0x80c120f030402030f01110708180405010f0e0c03130f0f02040509010903141207141306031b08160c0611030f040c0b130e09010e01060602070513110a08 67
    0x8000c1200f146403c00400035401c281400901200d4010300b144201400342d6440100290b501003400036290b4481468001c80d42c0300140300348102d594941d007100802c0158014a108803560a0001d0b509501310001c40c1c0c00381c102450241c03642c4203240c0741d5112103415000101c0e50b00059080b80070160303480340107580c0242161000010080130030300c0c01502808410301d88103030344902841456a5000403020b17070350780803480d420a1001065102c019468038410394144001303074802c00c6004140749502d580a6401c04c03810441003400d040c40031a090302e80030000c80e9800f40307006400c50031802c40c9200e101da11010512130720300454085d00421341c0001c1500708a5000c1c05105102d0108401d1001c20401003006003a000482464220742c0707512104004100d000744040128510f01190b06040300354004401c8002002c020800991107050094032038846120340c038071650204081c070026011a1041181700c4803401c0701240360121031001030364200c00040c614607101303040c20b14901c142d04c0790518030400d1 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 866651762 1250 866650512 866650537
    0xc020f01050a050604140f04082116080a15090b2e0201050105060a020703330501050a170a060b011b06061d071b05120d0204050a050603040b04080c12 66
    0x4c0c0341c240180000c03503c490142c0d905c90614001440b85569181c0d0515070420f40100515588140900c8084030232500d6150640c1841002e1007040741684207800b601148400b5036403005610b48605409009440c42c03c40035403c11a840001003100cac1419a009050280014003000320b40d000c3c1d10300c82240021508108000048829020154164284155809018110784090501500600095482e070440c0001450760030f147c000302503e03c02c0151080c40000310000088400074068041001a000a100711401185407002c04100c00c5590728512038104c114100038082500075440e0800a0070b5081c90282c1440038000038855031917100013140481034014180402d0b81481e0890100040d5020110100521030180a0080c5d80798018035150b0400701c034180039440443e45080050801150195a64000400003024000d03c0c080750090000c0358001c850004c1740c03070354070028080f551000302c80080030444200002000618001c000d0300781804844120761758180d030408054903a52000019102 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 866653012 1250 866651762 866651771
    0xe0a050c04050a11071b0302100512010503060c071509020402070822030c1512020a090f0531090c230a03030806011d101107060503010501020c040c020f01050a 70
    0x801c1c20a4014580c00c14102e90003007280c4440c3c400101c12034001e50400070304600c440f5007481c42407089802441c000c3c5030000c111000d25000300b00c014240c0d50101c000816080344a00000800d46400f142041c03285280011340c0307141c188256107031400403066014040c20036079507243c40f80c05a1107074400751022501c101800383c1d48042960301107100401800840c10b40c4100210140000340110180000300d54024001e40f0380420b0b5020f003541c0080f001100307203040e00d10124100c40541c1d84980f002c422115017800701d0074841d17111014840d210310314205c20700070259286903030302102504643c0000303560807640c000075140205a40d101c3c0d0103c241c1e844552a0641405042d8594140c04070240e03034004100c0d0b80c80740b15450b640d0b024007000001070405041c8489810b0720b2600c10300c1200421520380c0300802440c440302841501402c5103100340b0001c82c00340b04004020800320f001e031044a041e684142c004004070300407117003080090030700090000e0841c020192032000692007409503600440d000b01c0c001c038 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 866654262 1250 866653012 866653033
    0x30b15040e1008030910050307030f0e031c02070b0106141308030307030b0103090b06011b0f050601060f090e190608010507092108070b06030a0c080309040506011d130e0a05 76
    0x594078185400508861304100944140c5070740321850300071074442c0d44c284a5120361f072700b6905400410003450300c10507840c18101e40002c407010120040c101902001c0c2088840c910003d0000102c1c010030700000e0940d0040c1c0014480c0b0b9004145524030550142005032511140c03800602d088491917101034290ba2011003440b00b1160540601041000c2c207203000c02c401c0a280e1100501158003400b4141848800209a03204004084000d1203441c1c01103460302000b1308910344165100000d00c15440051000c00103d000b05118160300f800b260101400da946644802c102d41c0496002290940c04441c4c2e00c01000401c0502030103898130450007a1241c2c2c62491500e09800402c0d0011030540c075103052110410400100d407042074800007504000041c646a9402010902d45842100003500300c1503080e00000d1060f4002004201d0000280c0303050009440d190015140720801d80c401c8408100c12030b541440c89d040c001c030700c00810350582001142584d9240c00140c10030407507030010f44150700421a02d2 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 866655512 1250 866654262 866654281
    0x607080f06030a171608120c1204080903030d1d1507090e220c0317091503040201020a0611040e090607020307150e12071e020907030b15040e 62
    0x6035110480d182500c0d0355103803500010352500380e00d1030000c040c4004403c50b4440d040f0003609070f400c00b005021000e808081d440c1050f20064003c181d480c40980c9a080004690300d01d010183c3c1c20384861016961815110396548503c4c6421607003136a501480180a55151400c8a0051900e15030316165120420209280120704010f554090311840c41e582c2d106004231142d10284c0c01d0101c54030390360351020944544e403201080c2c040c803221100301080480d4009090100702d03500d04003183e200380040e0405c0700901c6080c1a06004204c419070380100c0030000c214500e1394200055078050300c14030544140810360740d0b56104170f54a071100c00040400201c0c0602101d407100b0101900040d1b841c006240c10b04d0030240095591041100003041d10012041e50b01c1001c8142d080b501d8402c0002c01136401800e03440c000685e080d08030110664400c1203200000346041507030754108803816000b40c251105070365041000c0e8040e1172040c3c029a0450342d1481d62103004c52042c4054006010040b054003c103043ca040c01 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 866656762 1250 866655512 866655527
    0x7030b211c1209020f060a051308011104270501030302060a0b01020303131b0e130303231b210a05060109080a02210f0d090605090a09020c010902060c0607 68
    0x40c075460220503012241440e400503000102c40030320201c0890318aa0a10200d200c405c004120b0741d401403030103d4607540c00c41c0c11401802c440380c1041070390545540c0d00d420880c01c0c0c400c41021000420390400080c442050300d0702d0300002c010848554200c07404e52000610703044900076841036005802c070005120341603186016448074200300b48001c50450620031a030110b501e00e4180020040301c034140b043c2c6410b41854840400500100150350303102d18000b045400d003100e000604500080c0781c4505000035207924840801c1c00c401e40c400142641d643d0190304110400082c001c0f06c1017090512521407413010380041e4400321224200e090280741001042030082e2840500382ca070610040600501c2075003400a20300e00300c1c9404840440390301f43c0300200c50b14444000c8002c283d860040c02a009a041000100001e0420259944401490761000111005d000e0f21290507070041e401c100812800d80e1035009403d9210740709000042303001c02580050300c581c0c81034280701b200781c215404202503507410245 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 866658012 1250 866656762 866656783
    0x5091212070e3c03070b03060f03191b030308070c020a1806051207080a11191215050702070302040e0312041b060c0210050d0e06011e080f03070b07030b21 68
    0x18030f865101961070002ea19800640210a20b4100120010705160f8a451401d901c102c0080c007951108200c072482a00058071041d015207007644200303480d100d01180060410304590705a80c1d047c3d40b5468240c1c00702e60991603082c09a03440840c0e01004600780709180000c1590300c400d00e2000071000d1600c4140a28076000c1c440032042c81d040140308000412001c40d4080728650310030ba000e07108000000020780751941881442c21503155680001c14402c01510090351058002c2182c501100459140401610310480e201801038000510410050916801c03100c0d242c3c5094080d03d080010107c000b05017080211800e4030352440842d4107580200c030100f40d81c00548410314102034118469004a808a01000030368020000d0000d03401d02049038030360206198102c801b0958500d540e44088115404590a1040985061188000514100000341140c4450400c400703181809515140d41001d1304008100d001031584405440005641b203205c0840d950208070101c1440c1441e070f080e071604e003204405 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 866659262 1250 866658012 866658109
    0x907030507080d180506031609180e0606041a011404031704050111070510140909190e01061a0703020f030a120b100c02100302040801020f04080105091212070e 70
    0x10610141c1c403480201c03540b1132401c07440b240311422542c504840502d0305600c0404020601ca5007002d2b1500650400c0300c1c03400299049585035142c83c0208821107549104201d91080a0705004680754001d282c0444400c54110509003010b0340d0ba03c504500d0582e02c2e0210550000000f030901096070802440e1804a50510092034802d0800000c64031607045020260306000200302001820b10f0a0406c031b8540000203081c110881c1410305005440c00d03048590f521502d0304083e008000988140b0030001114002010590003a400038925206d41d80b0040d01502140600d546100407507604000825000001e5038424842086000c0c50800f100c01d60940184521100d44082d6695a03118041134110f40c1c04032029084200d00c000141c00a1055920105044d4004280c818070601c1e00c002a10448101c500203111a6a4030700c4000d0301c132615100d00d07492100d41030003241c82458440300b14540c0b1a000c0c0c1003054082c0400070004010305a10640840c1044000c1c8201440351781040da210309440300359 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 866660512 1250 866659262 866659307
    0x507050a081b13060b0a020705130209212d0d0809030711031903080412020d0206040f030921030f030c020d1101140408030a060b160b0907030507080d 66
    0xb45030408074010701060901c2152410145201e580180d403004000b420355040090381e032100782074081d468400d9807103428814142111a0031103010365000311040440014905842040a421190070410340409400028452170f411600074003030380e000802c242981d08000c05164000850400d280403400c04000003000096000d0083c80f032000400c1d034180c42c1c4c0c0003145810101801000c607103004202101d0451400b10350846105143d0800c40d801d0103a030155181c04c408000d088416a555015540c02100607400b0b070000402043c8101212040244203142440c505d641e9030501240018003621400240d41c030713a4809504140e00b03c03555a200695a0070107111122511102079126a144000001070044070314482e024044294030030255181c901d4040909802c103420300d404941c00854800c41d90030329000001c95a0141e400c1600c0d021520012a80096240c40e6140c048181000d40101058811030b0004000103a05100480240003010001d249000e00a4401405041070b0380d031114285404 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 866661762 1250 866660512 866660533
    0x2c07120b030c0d02131104060f020f030403050d0c080702100f080f0126030c01090302030a0f03050f0402100507020915010f09030507060509031606030b041d06060103050606070c030507050a08 84
    0x12200b15203003444d0102e81d8040840381c000e101401403e06001802400040003030045040c0390450700a258408880d0b00300c411300d954100c400c2d0b82d02e200b41d00014000f40e1200c07030441c0819108162030316025100e4443ca50600c81ca51f800709034500d2001c2d00402c041f40002028602207907102600c1580040b071559000b00320752610f10004030400005003c99403510070801d404640d4001081140d29142607500208a0000f1908000f500c0340c005c400400d000403003101c5507100041c443d0044500581c00403c000b0440e03103565007001400302d40e0707e00784414400e0601c409405a42c50101c2d01c0c2c0304032a02c960b610385162041c00010300c03030000365600c20140071800e842880401c44c0024100203403100f17810002d5980d600712001a2800005001d01c85002c000e1030808654240c0c560802000380700c043d02d0500c807100c0c0400c4c1c018209240c910b0400099849000040d54540c800d4200c240c0007070014000768a800d200b80c40e140706581c030170382080e14203500c002810422800c0a00005000f040b0301c40c042c007041c03c0c0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 866663012 1250 866661762 866661769
    0x307091a0909150904030e01091221080702071203090305030a11010b0d050604020d0c360209031903050d090503090312130611190b07090602010b0a2c07120b030c 71
    0x7800b40011b800c000150729040d0142e400345140d4000352950700d04815000381e4615049402d01070b1802034000e03051010b08079801490190302581c1c01011250090310300e1500f0805911a504003411055040118044001012074001d000401e2025210740ea8640c204429600040c29266054840340c0980204221007010600c00324031103401c682d044450112450031410311428a0302550840c010b66010170185070003540844000c000c0780590035008116026040080c0c40880c015a1169030f01900301b243e45810656002801c0f609840c13007800c0035414a6500007040c01118903148080701e04e94800507150b01e0340e107030401030b00010002d400c818501d00101c1e0810800e424a00c2c1c41358800740709148114051609082c44404000c42d0022040c61110301c1c1410042020502034a120010503050030010414504c18060220f40c5500a07180c1d10110385080c03143c4e40152003919284900e41c03007a108840741510b50840d524020406552402066581d851000c003c27601c1002c14288203911100d1003c0d019107 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 866664262 1250 866663012 866663029
    0x50f070b0906160506251b0602030403140417071e1214030315042307120b03010c021507080f0103020402030c07050109120e0618060307091a090915 65
    0x1a010794105403204401c1e110180c1000c0c1201d4010250b002d0382c0700700030940441080c06c54941c6011100300c0f851056a41041d200d40d4070b0358080365100c01042c1001d002003184c40d001550020b100c0c0ca0411601000c2e10a003444503082504400407100741040010281e601c10015540544403005e440032a0b500e26080100c410059413240b2a00944080b104006100401c0c1445101652840030340390341e46050b42c4841810f0001c0d0000c54480c601e41100080b403541d1042c103106103081c1518894002ea160700c00e041d00c4248000000e13049481c0c45c0e1142c00110f45003805144030011326900280340b80ba85940304050100d4009044000f00a0080100300d0021203591116045a8054400507a01c1c1c0b942c00310301c030007449181e002070040c2d0b00b803d0b0754100308103103110b030415808910760341c800382407103090f04003d5144110401240d100720f1f0f01e55440001d281020045800605a00b40840e040740d9032912200811b244500802c4a2400070903e10448e04001c00a84d80c48840028800003020621b00094241d0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 866665512 1250 866664262 866664277
    0xd050f0301060e030a0b040318061d0906030f10020301170303090a0b0a180c0e01080c0d141609050601181521060e0114040608060c091318050f070b 65
    0x10a6480c100f0101da142405440c10150f0000f085090914190501074040304904070035800c01003240d10002482441801a0241e2090f200980403c5031910402c01103c400c01800550303150054407010025811f041228461001d013040015031203600d40703e040c400d000299240c04d4027035041081009107810001c0350342c080e41903020158120948602080500412a6142c403003000591a81d0030303414440141012800c40d000000800d040d6038803500004d48900c40050110303000307170f44903880d140080d07801051703004602e122004a0b540401009134150300e110255004100245e070302c90a00c140d650b070005940140a00c5030340401c2060307150840c03410814002e50a1181000701071005601980c0c007900340c2280202c5204024032856442c0d07412250510801e20620b0b07641c20580680800324100760084404842280014040e59a160000b2000591140604035840748030610751004e20340040c070403058034504501d04031b542d030300d018904107143c40e03007c0b001c4070201d510020702089004e244400700c1d03840c0c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 866666762 1250 866665512 866665517
    0x905060a0c0203090907271206110f12010303080c07021005180a18182301090b0a14090115051302090418020a0e070f03051302120706020d050f030106 66
    0x1081c801800490440c055080e0035603200e60b815040c02100c0b58407500e90180c401110050f90039000701075201c0d2031540b070b4512642c1560702280c40c510004c90aa6807125088000e205451441c2c05510515800d00350b00021005120b000b50100510906610205903035204265101062409141c0d07000a16008203901909040100008040d0040781481c5c403810001c52002d0100110360b030b2143d0000100e0078006d8030980d00585014645c00350320720f03091600429240c120204000300d100b405103500c07802d9104607610707030190348032110f420009802907100c92044140131000035419504a074044036460f00a800049127a05140d11a0007442e10201944110740080b038824000d01c15a11010000c1d01544080a0380a0703e0300c90700300c11000603402000d41241c800c0381c0d004048c0381c440c104d4100340102920a48002035252040004190003540b2103030700011701010001100110f0303400038200030030071402c1408540001c0010881c160f01046001c000761017a085c804d040a20080b44081e40e4041441340908 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 866668012 1250 866666762 866666771
    0xe100204031a06190320030a020a09230109020a0905090f0f09070e0c040e061503060609040603140d020d050a080408031b04321c0c0902070b0603010f0905060a 70
    0x9980d101041d2410301208106038210030350b96400c00c07198482e004038a039019840f002d840b11b181441c02241500074550b0080c019080c41d41010f01c000014084800039813854420050412443c00f001ca14180c000d180c2884050b9036181c0010005212441640c021809031811409119103080301c00d150560014005080c0d031190741ea0000d03060b103000c1c0c41c0d50124121200740e405120b04d8590580042041c0c0d41c4030602041252100d005000d580300300062411090358041c008180c140c07034428001c2c10300041c024000314503117840361913403106840465400751940d0301100e0343d0700c162901803103a182036203038074140513080c04c041120180400c1c8000340001c0090074000b00041645100c02103411600000d141515211515024003010559003900d101c86d8000100302c2249c031040c100e8055070700340354020b4410301d0791014501003c901c0901001c411a050319081402240d042c103140302411f48103000d06d2502c0014201101403500311107041c028141c5080c1009541c00105a0001d4602d4020304001000103 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 866669262 1250 866668012 866668021
    0x90209011706151215090403050409050709180f05011e0b07020301020d05070914240901140c0109020111070b1b07030c0b0306190807060f020f060a0e100204031a 71
    0x291410382000f0507070419180451100010828a58101c0c41038500c11260b4105000e0081044405042100c0080014800304414041a040c0750013503504040d160030400d5096444005001400100380440c0c4106941c81c8a4012034070554005c2e2070051140302d9007004442000c8481903421040d41c0100783c1c90200c00190384c01151001d504860003d60341d5002041075090440b03000340100c0c500d125160400c500d44050582c0351804202d010204816174400768000c802d0501200b0b510b03000b95082d07038180710049480d9100104400020500c03052408000151400e0500c0050a0250314030b071400b45940c013134142405021280030445600c514824004c03422078001e0310580b447c0c2483d60f08002c2c045070307040300c2c006189441c100185010703000c12901c011003c144c020300459610428800c1c041554804401008000c0c09059000c1c00740703881d441568000c000e8440018500201540c411a160350745800c44203101e041841030104555605d0825403529203141c507082030b00c0282860b4401180c10303410115 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 866670512 1250 866669262 866669269
    0x260d0b090121170f090114030c0a200109050609010c05090f010e060c030408010209120a03020c0111070819050d0c0308010905060d0b04030e0f0d02060708130806130c090209011706 79
    0xc4a1940400d580e90b83c50709404800f00c003e030005c0791400d0104607802140c402c0410075000340c9109094490080341054000c1104440c003a0700082c0480c01e030384040d00700e5030b0002020300a00c69030f14003510041c41203007401c075562400c4800c030040ca503042000600c0186015500c51010184155007460300d188000410740000d801c40c4600700d44941d003440002070000b540c0300190080c10440c141101c001200b80340c10341ca85e94940000b500c0c001d006030068a00c69105600500824003640d00300c000b150288d5450385000707482c0409262100403c405000380c4401000320404c044d104081492624542d031010707665020b09010018015011001d89030b100054031600d4a401044c1d815401c581a04528189070902400117100980b05034095000c10708071400c1810304030035800c81150b0241929160880c0c9407034080984c1c000e46000300216a004ca00010f40840402c03659000c2c0701000c404480d0780c12589080d010320030f1180d002ea00313a00d0050110010b1aa00040c600810381110000c40c00207540b030741e000 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 866671762 1250 866670512 866670533
    0x110a11010e1c060b0402040b1b120c070810020f032a0f03040b15030a02040f02070c0b190e0a03060207020f06040b1209030c06070c260d0b090121 64
    0x30150460081204401000d803490302ca80300441c0154000c101880e1140144026131007640219440481d0811102070381d0280503034609880c15101040e640200d054066034901b80e4011049209a60310004003400f500f60b045c0a2245032541041c2d00710302c1d02c0103c1d640b0700b003213000007040d083d00d035592240c2c03c0d00b402ea0222043c48a5015580c2c049a4881012040c0d9072542c1040d10b0076030710740c0640c600003220807080071400c1c1c1e15000014010403d1216503030030032024015407102654400c0d001e02001d400180d64024010107030018043c442d4440380350b00043d114200c085007004081008006215841f912501eaa51094038bc0200001d0390703480c03560010408806401240941180000500064400c246c0c0042c18042d0718540c0100e800703854102c110b954034040d800d0241441d80111001c2000b03a8050852844440c0c8910807854660358000c0b201030084994040d81c0c2040301001840159445040c42100e002d010101c9003c81c080d4101004000c90504540c0365200d501c201d820000b06000c0b20110 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 866673012 1250 866671762 866671787
    0xe0904050c27010b0a030c090b030a0f02120f01051c0f0308040f2301060608100b030910060902030a141003060e030c0118020108090712241b02060601110a1101 70
    0xc044034550351400310154660048a490001038544140c0c40c7c00c6501c00c06840c400ca0300300441080c00c648840302420010040000104005c0364208400c5002c2501e819883c5c1c8102c00e60804c042c038941c9007105001c2c0c100070b00e16998210720070419849002607442100352500382e03010300d0310144580da585442292500b040201412003102c0c106503103c500d1021140040d01c01080f4021302c81543d81d1a01034172910025100703201080000745013444024260409180d10140840880e44c8030b00c581d0780d034602265040d41100c408560000104100d4007401d016184031203250304640c5104d850060588580343c0500e020061800f0b884442d4101c0451040050f00e000300a050001c10800d96001100380305840b8506089000c20014400240103102c0410a0800c48906048040480105580d902d804c800d600d075142681070a80480c0c2d50524601d41700343d41004d840040505042a0700501c041d08c2c100006000310304000c0e4100200084940c0840c181e6a03190780b00030441c0101c1c584400503100e1140e5101c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 866674262 1250 866673012 866673079
    0xb030a14090d110a0c050d0618110f0a060206070c030207050a0b13060206070c0303020a02070b180a05040e0307060b04240609050f010e090402010e060c030a0e0904050c 74
    0x50510010210100b0140a000c40544641d0072681c030680c043c94903004c0b90b0703e010342400c80141080046041411000110030701c00e20300040d0041500d24414982180d50b4000e8611501018680380c0e503040c400c1301d070f0300c1300c12040301e02100b40791030701c08025030310440108140f08000115000c10704042c0200700e00d4000d003c0060007070b0041c40e202c180181868201c04602440403e40010004210780081600750003541c856450510050913900c0c282d001c2c4d40200c15190441c802c8501c00156100960040c02c85040c800c0070030102e010416041141c561500e030040b41c484c0b890440701004480001085400099104c2c00118008602100180007030881c01204489440040d04c1c041c0c1c42d410440c81041918001d84030708100940780d4041c071040408040c030141c0030403039040c8010200d250070782c151640284145001184d00d2120004103c050708259000e40b074076880480d40400c00340e00320038042080401038415001d241b60a407551076443c1200f640b02400f400c1003840e00c498405c0454604000d107041d80 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 866675512 1250 866674262 866674301
    0x13030c15090201031407020c0108070c0501050c0417121b0a0204060902030613060e0103080d020c010f02090f04140c16140c150705061f1a040521070b030a 68
    0x900c640000340c10180401c90010f490050110f8100191424141c003d0708103500401a444c5004015506407001500081c2404030046105000030800d002c0d0501c10003001c2c07400d81d20350f803406841140340d416082044000e6042001502e03a408240010307104074108502d1a4050341c1c1102402e40e0501c04405c1d00a074005041038408507038504d1640083d80641d6040da030030406801e514603054101c40190041031000d074441001000403070724034030150500414000c001407910b034008680030300b140c148000000042e600400c030300350f1034504000c030f40c035048809403010700a185500b901901202c00c010034400490b4404659a070303010724000042c4144940c840651000c01c144241c2807503440612502c0640b00d01416940954009a00d4060318006580030005061070740710740050b40164417010001d00d5400450314800a121112640e6040c44078030320450180c0d44a0914092000d04404a0000e00f0041d01021892808400000e40032013150a1318044603202e0321004900c03405001280b034900641e500e003 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 866676762 1250 866675512 866675543
    0x20405040e0610050d0b07080a0b0d050703060606050a091707030b0106030e12070f3908010b040c0f0c17040801140601020f0706031a0306091b1813030c 67
    0x184040c000c0d108100d000b4003c65445041003010181404000e010b8074003080811203280c0600d04641e04200040030205a000145002c142e04040d441e5055800d50b201d0038081081c80b0080c071600001d040d151502d240b4244900310054800700072b502c92031591170740f410004100d90741c0502c9070304041d5500a82620165079a51001000341812100b14081c0d400b41d076100c0c164041d2020101c5030784d40d500400c031840321412030700c030500e04a000c80c8240707202c08410313101c0b0840d0100c0400104490610703010302d1500070f414155801c3c2101e08540c0c0c00760107640b61903e0340e01400c0c2c1201400035100c20394548030700071608901d080c0c805884041398008103400c3c00306010921030340640261041c1400e5207066021359845030700482c0d5940c480e080281305904014014809148070740c00c4070600c00c85008000c501e45018401103032914038221401602500f196020240c0d03034030030511900740e40600b2140d40307031412003c0c80603036146500a4581100c0c2c26120709442c04041c01a8840205160081c1d01c00ca0413511 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 866678012 1250 866676762 866676791
    0x1020a171308031c0c0e120705040609091b030b0105060d0f060b09030c0103050606090607050c090c041a0c1c0c150c09050a03080a0c030513090c110a1a0a02040504 72
    0x14007299613082c8038039801d904200c07000d07106410740070b405e0390344103418901000e0500504218400044605010f0010086415210750140c00300070545414001202a0710f410415803c2c5200100600c8034011220104042409108100d05403001241d09580c0e40d0741190300e42004060640f00c04090714206900000c000c2c40d008003802c001123098081c2c401c1c1c805010b0044088580890b00e4540c85002400320030900d003011005820b40910540071100b068651a00203001240708903194856403200082c280590070f03007003120002541d0210803260411540150319602d0340034480c03049d0b01c002d03c0070070100441b40c400c0884001c803d411145c64000005caa280f03110103030131407590020204000f05000610350078000c003d1000c030b03500000002d0420f6510321080314900c216000650401506020450303071190103a030304000170a06110b0014100c0051400078140741d0b801c0b0822030300d640100341488041500c1d0082034203000c140f00380c0002c10f9614104484024042d81e005103400ca413070800391809902 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 866679262 1250 866678012 866678017
    0x2502160e010302040f18140304051e0316030b06010c030e2706060a0504090b0d02150307120b10111905070e09010c05072603040303020316090501020a17130803 70
    0x34000d584c20701c00503110001c0c10b000c1c0e56560305190121000911408003090510400c15284440d00f41a286400c0d50b40307001801c21840608612501c4001804008561400300003510b5032003d42c00e4200c02c180d241d5281c280401000822250510912640c280c0401d0300c10325000358054001003840141c0000040c142e10703412414011100301141403c08601c1c80c0c5020010341d41c41c14031b00d9440b581b900d410000312780003900da22200d554011640500700b00040e942c1c8144102058000190340d07440e4906094000c0651115059a0310040e24280c00c500090b00e991607000600c8406050070304031121100413041c0750000c50707425202c03120110f1a661040043c0424410122510310a141642e600c03001449400c842000301004040740c01044514000f03400c0003c035031807202c0f001c00700080c0016082209507503030780304960490010340e000080102c4180d40d0300400b14903c00700d00c0c050000500308030011f9507800f107100000c4c080001c0c1054134000340b11000115140d0103011150340c0403081d5251455540c94 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 866680512 1250 866679262 866679269
    0x3220503070620030702040e0114090f1f020405030d0210060509061503070908030c1b06161704050a030308090d080f0105040e190f12030509150603012a03142502160e01 74
    0x1c0c25032b20040340803c0c10003e280e000d46040913014100301b080751194140d941512200040c10542c09000001e4240c0d0140043c00d030515060f00a0003142e2598020082154001d401c001d1084840a007408000c3c1c80e14540c14001c40c442c50304969407603c42038400e072940d020580c06001240b20000300c0141c105000b0503101d95259006500c00340140c0020200049070041462007030003204500b05030408104840032003c244500300120a1901c1e8aa0000c500740d42744507002500440d4441007803200d102c1080103070031408030040c42c0c203107281e0500c0400c4a076262018420588201c0d20352000c4010081c0034400030760307051503085441d03021983d1460940b58a5101180a551003446940c1c0b88150034064001e492140c826000907049868195840700e01104010305550f07010f40d40c80741c41c0300c2152507005c81400c0c4180030b80c03011078000c0a1600020161441460080c0c640d0b0100c0007480030746144515203451001c900c2c0d03103004501d540100b04900d4101321070710b21101c9400300d280000f040114070101c3d9044c0c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 866681762 1250 866680512 866680541
    0x81209131a040f05011202040213030b010e011503023c0403290c070b07050c06070201050a0c030908030a18050d121109031c02030c03220503070620030702040e01 71
    0x1010043e02d452040f14400d200c1c000d80d440311080c001c0014902a8000c00c00e00048080302c01015880c0d4917080d003608000d801c001516030f80d4400520071040b0351480b1640980891800758034089160140c910350340c5107003000030340303520412016048a500c07141d500900e0010690310551502d95030306020504868213191301450040011a011401c0305080d8001d10441e45060180e1234140559100f55001d0301c001d0110007000810f101003551180180401386c02840e00b64000704103401c000752168201c03846150000c041c9440c1207424400100e00c502600e521203101c210003c3c040c1e1104100b04520884448000d0107800350320f82091049400040040d01d1710014172040099402240c1110118420703145c81e664903521019507800d0302c01443c4041c2031000803a206403030a200354041100d1842d0040010b013001c00ea1840615041092008050b100404044008010840c81c014000d401c462180380d181003070003c002e50b4070b142c0d000108201e8080c01e5010b0310402909804c0e0303000f45d00910364000c04801 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 866683012 1250 866681762 866681771
    0xc010209100216120501021e0c010506091306020c032206090506040311060a020f010e0f120316050d0204030b070e1c0819020a06060806061009081209131a04 69
    0x110314400600301c101140d200c241d0380203c905000c500e44080914082c100d8840d9001c01040c1e400a1204009031890007070100040d03201c0080c0050203094600041220b4050b0b000300b41080020303020052108000b5802000041e5103201d10100740d400d40c07240d429144c60400340510100e03613009600011600310b0709241c2e0b031041e07000d45031810400743d48141e100182100d001500d03103280902d8014010b00300c2d8101d50040381d2403600300024060942c1c89051a03803101d90840000201a000107205c1c00c4254031808441510350b15007403403404000009001d00600700300c400f0803e40d164030840d904503406190032503100b240780e01d071210008102c02c0c9800340c0180960f4140303040b800402c020945c4001440e500110b1300e8200741e50948580500410a045841144201030982c000314401c0d21030240581081c0700584032516005051228128561903a04100f21002004011343d5101240c0140140d4100c20070035960300c1701d070000811002d103440c4d441d0f101038a130842c0e070003034a0105000040d681e1000d880600 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 866684262 1250 866683012 866683039
    0x301031509020a060516330b09040303090c030525060c12140706020c0f010c020d020a0b2805150409050a020f0301090f030c0b1003030c1b09020c010209 67
    0x4068403441e100094100d001c407501805403d024202600d80c286090030540e0b0364031713580d8036800c080071110000f0b950920283c1c46c0b030070024011101e586610207c003100900240c04400301081002c2e000602c05000c0583d1410360800308400a542c0500075034100046a90581848a16115a034400c02071624404100600019030b24022201c0d020140d8211188040c40ca10742482a070b403910300c01e0101c00946404220040018a0780d10250003072154000081244040c404045400c4130b0754030142000b50752240d0220b0f06070310f9000a10030358266011014107010b03180c82c0c29141d40300c8148861041003030f42141d070210060740300f42d100381d2250074100031000c420440030040c082110503280d0090310540118002001500f440d0040d00720a0602800006400d03540391903c2c04d501c940142e0840001d0100d001120a0201c0340314030716009400d81d1002c0c082540f0303503540644280c1c141000202401507144e6103101d207140e21040400101881c03e002d558035080c006c4003d00071f60250340105d11880c0d1010046 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 866685512 1250 866684262 866684303
    0x70206060a082a19150509100c052a01180b090105070f080304081803010b0d0219030605100503012a12060506040e01080609010c050a050d060803040803030103 70
    0xc88140314040d00c0b4162903c070188901079060101c1c003800c4074080420702c0c0c0a440d02810350001000e18803038141e9542c24080341040394200195444200242030040101661f00c20800c150704004a080218034040349191003400c203080c140070303a00004196a0a4400101042c0100c016803000b6640c1c0f280c1a2498005202ea0070014080d0b01100101407203011b05c0740d400b450040940f14011008298060180e9482c1e01ca507a00c100c50480e40b849004c00c07035003418a0403010016071604110300078071201c0c80f1740022840d00f0380c001070003922400c242c40d440680303c142c60641001640d04000240064640056001c0c008041d6105481c025860020b0420505112000e00040002c4140420303c01c1840c0301d400300c40c11440c003121a61190791351880010540c0d50b541c01840100013a001106066140808860a00400802c400000d90408800b40340003580070040b94440c00e05030410279204d9512001600040c441c5405c094498400064046046040000614105ca20428039051f108a409909 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 866686762 1250 866685512 866685529
    0x5010e09090d1d060408070f080a120c080d09030e0114030411010c14030a02012c101508070e0a0509070b040504050408120718060302070803010e0a1d030307020606 72
    0x101e030403940202440d281d01610461010510f000d50b03040903e02c8000d80c000040e2035600c19448613805520800c0c2c100302c458100582c40c0700418011300509403d04160300d86c401c00451020f024407c01c03000300042010000d9040079918100e1403410100020007061a01500c0703010042c007400d000c0380700301d600c054110f0400c6048070310941e440100c0422070b8022000560f00340c41c204004072215800d402e00d18224a10403c05000058601d42c004204e003074021030b1903081844030402c000c0c2045900c100603600700c603000500f25891158420700140c1150707101c04221070040c164100b00b0940c0959100015030180002c4228010b00490358204010f480341402c40795140c01d2413217007024400c008d0104104600c0e01c0c4d444a6489030040c00841e1410703007400c003110154082260400041007030000960a68400b8154003030151680f03003002c61070200d10f80c5031841c0e58041482862100c46440c0c0c006075001d032aa40103000407080705441c2445d405040c05002d03450703410443e4040c005106c0e110018a9518040343c0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 866688012 1250 866686762 866686771
    0x320011803050309060a0c150603031709030306150912010921171510050a02120c100f0e06100e060f13090c030203101d0c0f011b08040e0105010e09 65
    0x9503c4d0134880000c0c00345a400c043c0b21141802031000342040415102c041503085c140400c040060010b055240207403208280d20303200107000000303604002c0a40340c00021a80c12601c11a010058007070520400301107481810702103504020071a100078018030054110403842d901c5450a0180d414403005101c01c49010156a07100280d0141031101e94000c0344140d454000d51032809a84040000301d001c213010105030140540040c0c0c00044007a19642e040c0b00b04203c004000400a180002c0414440d6441e2152104028003a607286044003070b4060a034001c00e20500d0f1801030303e60134681701745285071b4803000348180d8206000c03440c0002d5a42c81d086500c0b2100b43d00c01461980d022001c900f0100007071030510400ca038441654030340800076aa04210101e10100f41d0400414500b802803c841c0d090054000b030400079900c503510072001036449034642d1242c000c00b8680800007180320190204422548000608090800580420b80801d0740e010541a0303002a201c6130240c82109090011a200445 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 866689262 1250 866688012 866688023
    0x504021311091311090112020f040f031b14060a020f060708010f061704060207080d06080607090602062e0b03091c0c1709120f0a0615030c0b030c040320011803 70
    0x40007005c50f41c0240b1420b0310340359041301e005040481560320790b44242d01c244c112000d11260301070304200b005000b501c1c0609001e50340440200311840c0008404246c202c0c0e28210b172103500c000c5260604103108100b20001003140c0c108030f8001b42811100501000c800b0302824025890741200410150b010b0a07040700c500004100c41c0c0115607994803560001d4020711000c9070790800030422b920084080b8010200940001e0000d425a800c001030b000c3c10440700c41c0e02a20070754000e90100302c031201950f90094000030101e0f099190400da8054203180a440d940c224114804011003032000100300000d106c0c205028041c5822051540a03009480c5201c0045006141d00c48940d02c5040c1142d03145d002d00b48010703001d0283d05e4600080039400d820103441148200d1310f076208840c0e050a00c0b0060282004c480ea1450340350b0b070468107584416150703020074041c40030504000404510420545822503004507000509140e66596200160000660307145200340000c2c00007600d14010525015402c0440781d104 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 866690512 1250 866689262 866689267
    0x30206010605131203080f01170705062104050c01181809060e070902031b073c08030a05070912020d0503090d08120f06060406030504021311091311 65
    0x51070840321940301c0541c2c00c004420f403107800035440d00c0050305920303200d110392118901450a40d25441036034030164001c04034901c11402c5859a181e0206061080e1641030392011350712000d851041c05419019015408003060700c8040100788540031880c0c8101b8403099a4188d076841c10000c04a140d141140540700503015003101e840070b108a20780c0000800d501c0741d00b0100313032400001580c50814200d40d00217407913940c0000400c00715140c80ca1010014110320441107092000c40d85640c0c0100d40d030100c0310750660b0682407015900c0345030002c1e0540d4104041c0006060418a07103000c0c0425041603c094940d40d09100100b200c0310700496150381610402098681c01c81859000c00210720661401512940000c00041682d500c034401200c0e1958055403030305a0b80c00c41d43c04541502c090041ca15500798061009006c42a507800c400c450444010340760201c0c0311386850000820a608010100c2032003440c140708003c54610a0001d44550700040f90240b861113240a010130540348540480c4100d103c04 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 866691762 1250 866690512 866690519
    0x70209100801232d010b0409061a2205030307060c12060621060b040605131a180f100807111501030b090f0d0c0c240e0f060d0507080603060403020601 66
    0x1950140c041c03c1d10480c446465800044500030303134482a045091a50740009040c0300111b81d074040c0e100149078480c056945a49606003d08060141c1c104420802940c0540d80c00762010800381040580760080c1640d03a0340903140f81440017040301061b0100821008000b9190600c40d43c03040100f00c41e01e03501c83e00702101c0b20341e031021040512440d541161594558001c62601130800141024205988801d503440104047d07102c802c0303005d6441002e0200c2020241d901001300305080e2840703041c4550118545c951540f0010310810303034510109420800c40d860303007562154000c81c0a4001e180c2c0d92134010342e423284c0301c04c00d40d00c0790030703440c2414440a40b0900400c0040c00c0c0108595200105800f0780b000427000034005410704000300c0e000c800194118070307c8418403003105618030013800c5d6580d101a48a081001c050302c0ac0c4071090240e01400912840300c48903444e00040c2d18a20080101070079170300d000f02c01c50b05d40280350980e88040041d84400014485003400514503000f103405400030900c03a8078 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 866693012 1250 866691762 866691781
    0x510110d0507211407030221090f0111040807140409060203250e030c13090f060212010f150c0c050a351507140403030f0206071d041107020910080123 66
    0x10303034412559407074202d80d804004100c240200303009d5414a00035002000080954900f5165510030b03640406008000411a480e0000390000c1140d15001d01c603450283e91100040080801c1000078104030f00020070400c0c10002e61076490040400e40c5810030043c032160300120b40c50241a07440542641c04000c0c03190039860308400c90800b52002031800f00b51301e0381540c1d8203c0300c40d1309680215800c035004686500101040600e0300d000d424003010f280585458039001e6800c5441041c0c003401800712054a1303900303200e00300c61080003400c0c014210900340c1d6605c82c000e11000344488200d0321043d141d800984144a0040b10f4040502c03102001400d402004021400d40000c0141a58083c040b01d1441a034070046900e000d0b0009501a03200da420070f60001d14080e0030b0031002042d5034200210000c681c44141000f0002154246060714001002d500d85200e030030b0035110300316001c1d601c01d43d40010440103030300010a036804c0d01c00c030400034400031040411f915401c041000c1c07050070a282440009840c4031 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 866694262 1250 866693012 866693017
    0x307090902071103190c08010902090a0c1103040f030605090a020f120114042f130c2007031e0804060806030a0f110f01020303040510110d05072114070302 68
    0x1e00074003c920300da031160400a813402006004074002850480024020f10111000040090500000900450503240d00140c400b0390014014818079030784040703803060140b20f180185d444a0000d011a565240c07035040e07609120000c1e100840c1d40a040200043d1080c401003071101545601030181c00c90b41c041201013018490234000034613543c0d943e4446020b41a030a00911a0040d401041e2270909412800080c03071480c6020940807216000c0c240d00420291214042680060664800040e0540a1582c100d40400340c0080c19000c20488542c484c034000c00104aa008480c4100510850030007485000d6480c5640b1460143c881c0009000070092a406034045c5944105c0050a031207100229a442c4022800c0d4610240d4070848140c5800150741000003c424010710240000c42c1140f03056139070940d450028082c520030b40c070703101c1600303034400344120044d2011035800882c280b10340d18040e90014250782c0c50905101c69602010380064030b010880c864556202c8075241c804c9119541c05030194083d6 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 866695512 1250 866694262 866694277
    0xd061d0406091502180a29031321170c090409021c0c050108060118090c050f12070e040b0315060109090f090203010509070f1203030f060602210307090902 68
    0x86003103200703e9112040034402807aa0003211251005411a9401030100c0110180c100c0c5202140c0d1411840c1c6074100342c0441044440380c0703284c49a0382d42c0c3e03143c002d081c0e1810483c0010138410035002c00c040074450402102e000e00100b5542d00f03400780050141c1ca20002801d440381d0300020b00c201b000c00500e08140c4c04c94211076002901090500442503030328111451140010380f96180803503400d001d10360380203500c0f076008802440c0c01402c51440c1045400300d01c03090320503680220313640d0f1800c03001603010f0415103030441138240d109034030303048040200d84094000300d07000c0b070010301c41c40503d05e014500340c400d0320b2104401900528420400745500a5111000341860781070050b079040c002466000c0d4022180429180d200109255540c1e10605003522405031003c9a283c00c600418090382038003d40c904110ba04294104941c4007680c24294010a074a00d0285003160610001049040d00021065002900f001e2580042107441180b03982902003910702a001600030712080000040680150010 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 866696762 1250 866695512 866695523
    0xf010f120507151709121b010605091303030c0203070b0c0d0f111c0911060a030f0207240e060109020f0c01050a29030a0209071707050d061d040609 65
    0x1a80d40f1000340004038640b00c154100003a118021398507040354030000c115042928900101108644240d0081c0280600c050782d50350b10100704200c8003049425040b000c01424007900580c01c909018150700c4010300030346826408242008003c4011a100200b19100b8541080030030b1510385840d08a440705502541078401050307102e02c0080074015541c8500c4090a0130401e84c540e0b0303108642100480c00c2c841240c80c9142d280740c50480c0c40866400940801f040d40f0480304103598140e00442580101000e07014142028408900d0070104a003040e543d4030108141050600c603032040e94540c0d8140c41500800c0c040b03d0b0007180040000c00d0040e000740010944402c4e040381004c00c0010725508464040741d00300d1002d40c58101510146d0401510480c40740407206036000420604c9000c00c1d0340d4004210000d006040d802c0005600360f103e0744407000503540006248819007044403005100750401010064038034a4600b00181d88102243c052100104034900d00c6440d40c0c0306e032551001010301d01410381c1c8 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 866698012 1250 866696762 866696773
    0x90603040b04140616030b0a08030f03041b1401120b0d060c12110307110304140607021c0303240602070315110d0204210f15111b060f010f1205 63
    0x75443c40901015214030340d000410403142545050050a680612241502600c040d034014010f10002000b1a1040d580c071000740740d66500c803843c0c1400d40615154640d41c030313418540000b040c503d80305080e00110603826645c160341254190010303030403580740100381a03205040c01040300000700340c0c0d000350f01301240c0d500f007040180303040008440030b0b180004098400800300104114445801c50320750030305c40034044015402d01d42012003015400880e189110700c42c0354049924021580c54013002c49183c00001091041e590312860080d016016080301080303c010b2410b03410003e139108441140071030f2896802050034a1861722a031552440301e41320121166210008040f036450328400130002c070f51925600503a681d16040c4207440c51b000d02c03208d03446198640c0c0c0c0c101d000310700381074a84c51400d5000611904602c1a045250780240468441619186e0002c0b8066600f68522a4540040c842d0102640c0050b562010240d107910b109000d181e1511030104c01c01d0180c0858900030305400303440383d07040700c9 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 866699262 1250 866698012 866698043
    0x10e010c051b0303010302090c0f0d0c08090c0916050f130f03030f081e15090a020a030f090203030a0c03030e150414120a0c080904090b041403090603040b04 69
    0x50a40d1024003015010410001d054403003962048100c0d9240842c0324091401c2d0b5056500103542d140c0040d0078213946000c0411161420304421045030080e014194040041105482015000c114103d544509c0d034003071407604213600d081101d81c240c4954080005810440c1c2200001c0e50b080d08010030001e031010060000180ca121141c5002d03000d8000c2c0746407120142e1940c60010110400000d4010402003404240b00c800d0300400000e10640d40010380e910841e9507110040c0e26150f5103100d08980c8913038844203220038480c151303006004040255900b071244200840d88e41c415105050030080d0980d10030082d40844620484006903803034841e14001c518520404252407910300310544c1c80704401104810300003081302884400d020b1200100280507843c00c002c04118460182e011380e4001d00019542b446c0c10086018203d807a500c04c0100304004401541c140034007180001c4074119410364104108002e80c11000050b00c0d82b20341c0040507189181d54a0742c1f94003901d2320184c4121083c2d040029050b = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 866700512 1250 866699262 866699291
    0x30a1e050a1a04150903020309011d191404060302060f031306050411090a09030c0308060102030403140a03020c09010f14060f03040b0916050901030615050607110a1d0609060301 78
    0x1101c002c81c0807682c4906418a420000d8802c40781550000d40b991900110000183c7c0210070340b0004442400c102881500328161070030728080b100c1e101030307124113082030700e007141c0d100c4491104c1991000044105091842404e11040310220300001c2d41c01075043c81000e0107640403c0c01076901140c42650303580640f00d40c0e5100f4095a006076011602e6815080c85902581002a070f10b9500840c0581c00780285200341e2006003a40303001d0113000c0c1c00c102c413800c001815a4000c00403140110342c0008041a0b00d044031450316195503003000201c00500030040c08800c4c27450b01c0002141079a108215420340c00349003040320000c1c02051040160449070900464200c800ba00000d103116034041c1c540da681d83e107400c08040707003424912400d4401c2c15101c0f00051003142c41c1d00c8904e43c1035a511160010700f48603d52441c500c20003041c0c0c00745a10100008840c0c1c104a50380680410a002c1654800b180d00c1d240c5032a10040c007070380300032210f180e82140001101894012907158010102030000503481e024404503 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 866701762 1250 866700512 866700533
    0xc1c1b05060919081801030213080705030c010203030c0406080916031101120c0c02130b030703230304061e140d0204171b10031b0c11030a1e050a 64
    0x684007504103500704190820207004480700d89907001034200c00010035580b03880540c001c070104144580c040514444180e40254110b03000c05111002100030729982d2003d032580da05046c000c2d14024003070000c4040895000206403030007040340d5082217080900300f140444003841300801c110b1242c072401c1040000003401c81022009140030f03280c0c0080700c5081400250907140341008010b000d03440c0900c4403060551010075001000c0d8100d843e49880c21205c400140078110719440036030715008445001007000089042c0b1034500941d079441d840410ac031415219264021441001e0120340d5418420f0720072041a201d000309a801030903e5031030200000f102184d02e400002c4508125540007806001b6039242c82485503400964000501c0003003401d030845811424082140c1c0e004401c80007207440700b43e01a42101c80c01030591101070006110b01103004080c0704074110155640721816040c0e003a64140070411341e00258100e41c41d50b014110031541c50009080140c0c060711070340142d82d1110009001c4044 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 866703012 1250 866701762 866701817
    0x12c04020712030533120118050d030e121b06070809070b03060a0521030a020a0309060f020d050a23041a0703080a0c03140a09060506060c1c 62
    0x4001881060b2200c0c040c0841d54054511500000c40303280050413801694803108031785014200080c211355000000c0399401d01803c1101100354280300003441c10256000f0512080ca004074115980b000320034005508a8923a4020203400303801041c4516080e0307040d54010100444c003604410011880456a9030070702000740e800d0303170002d40244140020a18200448006043c00c401c50f94a5030270480f0010b510705026208a40c050729829041740030b10621821f03024403440380b03101600e42c2c440080d10020349a010300101140490b4680402040c003a03c00c40200701203000c030360010100300603d403205486c5900204504810000900d901000503800002003000440080304030544403828031103405030720150fa10440d01c41041c1800391401007584009091303000001c10000144010014900314081d0a5010b40341405071a20703c18082c03214a543c0c0540440d90060508004503241d0000700081840f070040304940303a6120a410381c41c9000d05408682c14900d0a00b031508a02c0c1000036a5a0002e80054 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 866704262 1250 866703012 866703023
    0x7050f0c010203282c0c0a03030e1f0c02040e1e060a1b0813050106211101020d0f030e0f120a020c041119090308031009060b09012c040207 61
    0x708004c0b44200034000300d4a6440c2c0101480604030810076800c801ca03001e042005045500c1c40750b081e02420034420b0419042c03001e0402e100c403a0b144c2c100600000c1600c2004c038000c2400d0048140d65110a447c0c00c0c481c4200c0c0c0e51101000319494082001034840c2904100e90f80c00707224806003021252140101000b13180720042d11107464040355041c1183c140c0d1322883c03817844028900554180e400602180d01a014203001540c0d055035042c80d80c014803a5401030009442c250f000180d148c014a0080788541d031080900700035100f981d40c01242c4a13044401c0800c04500b45400c44500c89000742c200b441c0700d00d036070421150609110390980d460306200c5014800f65440000300300a0307045d41800351008101c07059030300348030080d4502e40e10362041c0b0884040310000d9607940000450b55202e15000002181c202c8401a280c1c03c010200c0680610a0b200700c0450900e40b000c0020128242c00070b0380c80b030260503100d80d144a2003105400c05540c0350189a008000105c90400322151f9452024000a50052 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 866705512 1250 866704262 866704291
    0xb09131d060903030702060601120912030204050f012c120a110108091203040b0915091c0212040314030705010213030201030501141005090f040204030b060406060c0b07050f0c010203 80
    0x440505080101c0580307150742d190810810081440d400190711508460b080c070703004a004642081e21402000490402010ba10070024462483c0381c1c190013400c1555001c983c0c04081001401c01555007241007140c15008030b0301840200500d0b1003804141000c084060140d800c440542c00c4440d0400341d8805003107600346030b000c0080c4125603000018503405000000242200d1009107000f580b18000108000c00c0380d402c140006028800522480301e02c01140090300340c00e030a080c4101d607142c8084422044e00b400c0c4054103100490320010340d090b810340178404198681410364981d806a180e004500c0e142c540700800c40a0000703042440105405064486000403003815840010290f41040c0d010031b01e0064004818001079441c00c040c1003c02016062003071740d646c4079201248044560602155100344041800401d0200f2100c50310311600c001c8030100a40360701d074a0259501d442d8424040c100b030a86800180d183d5009000800c00e4001c6e0350016810025040000c9003640d10440b104034481251 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 866706762 1250 866705512 866705561
    0xb010e1807180b0a030b01030b071b0b0612011802060a03060b03190507030b0f0d02040b060705011b030905030409090c0905011712090102101e060803030f100509010b0913 75
    0x50780f14801c000c3e0021114040c0b1145180c94190603e14180401f8100c1420600450082e80c09800c02800480c003400c54121500c04a0914003403000040701c00c03e000b044c0c50300d40038100c0c24044c81489200c510781c4d0849207404c40c0b139400703000d400e400414904d4240355840001150341d903136850245109041920220f150388002d84941d205640001e0a020249804c0c41241f8190f0340c0c2d8802c000040c0c00050719070716105a05400001e002d40b00c88003542d03800c0003000910009002064022450720210401c0005e0340140c20b82046048804820010b01036400a000500220099400c440d8405014001220641d51260044002ca520a0344240da030012240c610104221382448540c460110340d0309514103050300c400000c0e41b110040410750b41c035156a24000075100c500303650303403220264074480200803080d01c4103900341d6071750b01c10380d41015200e01d02c0001845c0c0a80340b6403003100f9940c029090400c20391070403030b51120503000002c546500c4101911020032010715440b40f9150b41e50b445030b406034460070 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 866708012 1250 866706762 866706809
    0x11d03030d1506030b1e0418020a060c0b090c060307080a0204051323070905062b02040320060d0b031c0e040c030612021c050106060e09090a0b010e1807 67
    0x69514010740f0420741c01030303448400c0a186c42a00100b80c6001c10403d11100000b1801400075000030b43c44820000c0118150358001996204a845450448250f8941d2003c00395038450708000759521400400000709114032422400303811410000700503007042c2c0c03240001003a280e490701d15420003558403c585a407a144400385c0c000c03001c110b25098081401e00100003450500c05005850044030009040314054a0440b02e003041e000308c4143d141054480704e0b00e0301000e0343c0310b80302c1601c0840325840c1e02140300b596409108000a07004080503c1c1c11400e1700120060810410035640c503004281001c0240c032000c04a2840381c6003c1d03503581190030665000c0208603a03d504a107801c051800e2428044007000300e201c104034a4046941411107141910384034102d104d00b1000408550900074005034081d00200907e02c0d03900c0c200c07100c1e031840e9942c40e009561026050740290190078440b00420245607140071203a0404d48510000b8508841c5484041c03030b004c100c0d4405106031a40c0c2500a80110 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 866709262 1250 866708012 866708021
    0x60f120c070b070f0815030a0203010f0204030b0115021507031d010e01060611030d1a0a09060303030c030e0d0305060303040b040f1809050721060504030c060506030c011d03030d150603 81
    0x809041003c00c40b113240c54001d0807094010100c07460384c5c1070b9075440803c0b503508000100c46160300a00030700c111007022000c40003a4010f44400c4407507120000000c0303480c819801e018250416560700400f9100620010040800009030286d01816594160094000c10445540e090014200008a0400036034001030342143d41d254007540400c07400c1c9880c8015400d01004a650b1a0080d010110b10700355450b09140d41349880701c4a582d03100341c08000c00038010311680c022504503030080d22f04016452140c14190155442e080c410050368100c081c40d40c400707a010340d014981141001d4112410161200354500c840e030b00030341000b040b0202c4204108618008a0907003107501c94501400e0100341210356446555480301e01904220041c520583c40ea402c203002100054150041e01c280142d00305418080c103903a4040700c064400c103050a00081ca00e080c00244a4240141030303480c12803030030503445510800841c18000b254140020044500d446c110750041242c61481d0410005166103000800307002c54 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 866710512 1250 866709262 866709271
    0x90209010905040b010f051b0a031101050604110405040504031205070e19060903140f03040e061e0f0d02041d3004090504060b09150a081b060f120c070b 67
    0x444c240000521240d0380710740c1c2e51107900e4242c10000e8680160603490740100480f0b40c0651007038850040e01c20141a8000600d101d00c210070301c002c111944030203081c0800d54040c1e1845146070341c8200000c1105003026400b150f8010f00901c0c00c0b4402444a0884505a50054406c0320000c0c000d000540d94628080320701600e4050401c21801c01030b894110f01610511991001170b00250204a4090359403105202a180320849507041e60f0795030f91200c0d03c001210ba0141c41766805522041041c40c003981131b000b48800506070050000c1100c0f203c0d50f00b00200b0a8101404070380045d210702e882d010080601076001100c1030082c015242100b100c5200504851320740e54504e24010b0300089050540b0b4204013100c058901141021a040c1d866040100c041d080c4200c02d41d41000c5000c0c2080910444903181403030700041220f24519075596580c04540d520491400c44070006190700f0400c1d640e1500e00000d01d806079501170391504081d0080c3c03081c05048070445094140c08000a80c123001c009008028a510 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 866711762 1250 866710512 866710519
    0xc030509040c081f0812091909020d0606080603070302120109150605030120041a04080a0308061003140c03060a0302130501080c01090e040f061b0903060b030f030f090604030c090209010905 83
    0x202494603405d81c1d038540f060000355460f418001401d06050700c404001010003007500c58180241c0740e4898103400294000e0004582032890f00d00049241c603c240d183c0c0e80141801401400e01d03a0554003088052210300911100c0ca40d61102c120000403038000035948054200c9000180c0c0902c0c1000f45400d640c440701c4051400601071115402820b5441c1c1900c040d52540941121000803020812440c0d22507500012a544101a0f070542056480511248608030555140301e4500440c2003e0741941c5040402a210940110000f006501150041d540c0b00500412021451f5680e8000c02c0c00300d00d0311041d0354405508c4500501aa170420040492908801e107014420f451901d0030212401a01400040c00040310541f031205214090304031100410341a9169040c00e0782811001c1c0031000c003844200d4049007070110320041c500c0c0105051000700d0004014505e0a503d107044910303240d011040ca5544150240000b0011410b07007200c4d400502410240107030b4501c5124009407440d071255000c0f512 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 866713012 1250 866711762 866711821
    0x91206010e040f05010605060f0d0b091b130f0b0d0b1c0b090c09070c03020f060f01060804150504150506031204140319030f0f0509030d0c030509040c08 67
    0x1100d00384601c0258425084500181602d1403481c205000d000e07140d012903400303031020400200540c000380090a1004405000708504800340d801e00c412540111107480d00c076540400c0010075100c0c0c02e40100354840b2030941410740c042d202c01107400003031080d81200e00d2881002c03a100d00703134040768840d50203c1c040031281024110320044401914a10a410082ca03500407000400e059900410419030b41900c0100f040d1254502048010142c82100c00140d0040c1b0558840c5000d031180171442500410601c142c00c54240c1c20688180c5501801800c200d0b500000241d66944111080c401e5a004034030982e200c0c02108800d41c65241910400f81c030a40c402d403c4555480440406001101c0841d43d49a030601d440303440000001e82450b122800c8020b51040500d0807004165005041d290b5000b10341d150700c030703406802d102d04944a00400040a41680c841c1410390b09842c09104210191031103860305900d08527086c0081001d540d024660040803aa0200c02d20028858840d200342800d841e0382030180 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 866714262 1250 866713012 866713019
    0x9030e24030f0108061f210f0b0601020d1b0204110d061427070311070605040b0912070b0112020d230d05070209040f080f0c1b0d08030f090c0d050309120601 69
    0x896010b40300d81100b4200c0701c2460300107002805664070189400c200d03000c3c201c07823141c2810411204210b5245005006072100d000202e40240d824890900c4044d41a80076a01c0c560f003840014581c03e40f2860000d0005d02407150003103124041c10f030280c00c0c0c42156983c0e000407071007407140540c001c0d0385c508083c1d00140140c0c1441c0d81c0c01c0e0140ca0b4800700d280713004125444c0084e0410101c0c400c26101800c05400c09041100303010366a90404c5c0500400d10481c0c0080c050f001082c0d40c1c074000c0100080c8500701307c070700401c4002d4010f10360101707041c001004000090700030b907203151901c0511480325004803403a51240c81240c00600c07c0300300340032290902610b01001d981c0007401c40800108000e040020309015407081c810854259001161020b00c1c1d90360307503d05012002c0d81c80c0405440c5040c003a0207104455010700741480761200c0b40d980429058115160918010010580108003034054803611260750216036070320441c000701e00d000d04042c659a8030800240050345501c400c400c0c0103a44180c0042 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 866715512 1250 866714262 866714311
    0x20703020a0e071d150d091502091008060315090d20120705100207050312011e12020d020a12020306010801020c2e050708090c0409030e24030f010806 66
    0x605042642030701c90342c913005001c800500304080040f5a00104100403a90141040702c07030307002d10106800f070703106000c0d10160b05242c04283d10541d0b4100342c0094203440c0c07416640d8069004250410001800d0314050b10300c0c200c8a55a0107411280c104044d480071060714460b640110080e0724a0a41c040c42d42080c0c00303225403039a5031b40001411081442e40014200050107001c0c08984140c166210055547e0300c401e0900303a0743d0313070800817181e034100c0340c0c2800024400c1150f0740c000400d000d00e03540c0c880c0100d24145c042c0641010030241660445107048551005960700351440e005091001c01d420041200d6005061510074143c000b0f013426803040041880b8414000390540f054841140c9588085800a90324a0104080207469420506000a00061a411030031403807040e6052404c0303030b034154600da0401c000d0f1900280040c0201301e80c684e800249040a46081e10f6039802c1c03d164507800f80d01c0080492442d03204403001001d004030300340180400207091109503000910110800d400542102e8113 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 866716762 1250 866715512 866715527
    0x90b030f0601120305040302040212060307080f190f172104050606060f0403050d09090e190b18152a03010905151003092604120204020910020703020a0e07 68
    0x1102c1c03d14010910581c100f40c441c0080310091036010340700355180c40680345000317031310003040d40c41a102e4010320002003000c40b00069480217906200000700741140c001440f40c1c140b8084d1000c250f03511003004d09000042034220200e01c52200c400b00e080c1c1d540e881c41c81c40300c21000d0100c41c404c2c9074021954082c04045030b000145aa08494100c0d1aa941c0d6918170315104118031950340018081d005da50b0740f5400b42d0fa04500e000d41141c039104024423140000d021010340b01d00c4c4d06180c081080042c0741c0750002203242443c5141e8083c500100c0c98004038500c0798104d280c02c01038091041c0200c1410100400307009142170688600c508815020441818102400b01e580014020f0b0810a0390fa030001410761080c951002510342c2c0050a9140c003504500e100401a044946060300c0d07120140120b4140018031003000c04d8108000d85200b42014101421b0390f009078400ea6060381e00075001d0241e407003030340e03111450440c8541860300140310140c03561040c03040503c0594040e090002e0110108030499800104 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 866718012 1250 866716762 866716769
    0xc1106070306030830010801090201080a0219030b01051b0619090f08090105041505070515090c0103090c2d09050f060d02030a240b0306130f06020403021504090b030f0601 75
    0x603100d0700d4811720712090040f05c290301090f070042c03816400001040302040d4270208d82503001307a03501c000340d40d5040044010fa00c10b5425a5403011307809a02c03028114801d0b4080c2002ea141494401c0c50980c07980c1045110f11034051424059070401c0b42800441e541d0200d507006040c0041009200c410180d445540c0780d01500800507020314000205440f15a21890807640540000c62070400100542c54004016805c02c81c0b08407000c2c42400600c0c0c0100d80c0e150f60041c440d07c1e81c4c1009002e003032604401100902120501220050000003020400d02015580503c4031003440c600d16605065441550800310900d503c190ba0b00d40c0742c0303810b000c002c0311040700140d0311803010360b80c94001410b51310202e0726200d02014007070805520038100a1035011005d0301103d03d0200c9490510402241404046e02d401c1d05840d081c403d00d104941e400002099100d08a1100c0e000b22001030405a480c0c0100700242c0a00496140c0164002014400406644540f902401c8280d000704480380c16242c007039507035400600 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 866719262 1250 866718012 866718037
    0x100e060a0c090b0d2a0f031505101404060e01020d050405130207081201030605090f061e091f06060314040201141b12130509070804030509130c11060703060308 70
    0x1800f5140160580002100b0702d150301e840120461a00e0303241c0c17603058102c1505c500142c3e5800f01100d03e58443c2c000c40f10540c200546161145140804000510a00d040c1500502c580c0e4641080488000c0340604020100c039226003030720032601e0000a0030411002026000d0140c02d02042c411910b5040115036a0503190800682c1c03228642004cd109028050380e0401118260001104104981d0480340c00746e2003903012260040c5070b04c2c011503200e240403135a070043c2005211180320400980340e00369401a004406841a010881562641d00d01003c042046070369110307941000242e07850f10410aa40c02c003200550381034241940000c041304924190400c1c102808640f00b40c10300425012092000c002104958280030002c59050f120b80083c0644081c00d1901d28000a0b1410403060305031280416903034501450b0f490380c2c0d058a540e081040080d400c1400312583c005610094410041e50115549603c0c48001a407042146000740c01016107041504014081000442240a4828000c0d011 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 866720512 1250 866719262 866719267
    0x303060418020409061e060623070c0303020604020310110a1211040e180a350d02031b160312020706090b090f190b04050f100e060a0c090b 61
    0x71140d40c03100040503180650b00500d88201d400401020782e110b01c0660b40001901010f0100c460740740002c0711041e109200100d6083c1000d151481c030542d90b44041030480c5140f4504010281d01d903d82c68103880c0d04107c000d6030100c010301003549010081262450920340c020b020701000400001c480d4000c1e40080c2c000e200702560748080307001850304186007804140307034180d441c3c1e40e64041c040b201900070340c2c4081c007e90f04001414103070380000c121400815000320412100401d144c0160264041c24480ea041c25005030140748074441d0844028403018100d802e0140e128108104011040034181c2800346030700328200480e800880d005507840c2181038143c100310100e410f0654a801c00780c0710710b5030002c3c91286012003090030402c16600d2103026010103c00c41d480c1c014007046055541c45482080e4150903802a00c080000350b040c0300c007070b910074401d50035a40f1800700b5003e00d505d060f0030b000810a280e51151a0b01b429a01e0030040c03140e10860610f002e01503101310b801c028150300700a010b00c03803905000 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 866721762 1250 866720512 866720531
    0xd0213320f01020709110703030f0c090512070b03041a060102010605092d0c0a0f02010603020121020c1203060f06090604211209061b12050913141f060203030604 71
    0x1d000d0000180105c101c240180c401c03884880c2c0050f8840481203000c42c1c0703048901c0b1a50080b41c800c2d81940d4030b1030f1321450300803810300041003a000c50860318410300d0300c940d946c04111121201d000c1c5000c1c600c12102c0840402407a18580d0100300300801590442e07140020401c04d41d59242c0526421614030340020307105440355418180780e4076400b545480f80011071824004d440751042d00501070719440313684c0d9400558511070120b00341d0b501440084c2c00100604c460301a90ba2115444000024102c04018580f000828419041004105010042280110400c0418104000040104082210390a00e800b920800040040c0281d000f071243c0c40d0607510400f4000354070351441c00302d903d800c86035811f00350000d4800141400f04900030360000640c040c8030252006500044994496802001141c401c2c120510803030745500106225075001085c086501d04188c0d403442821a02c5001c0300d0104080d00d443d803000c9000300d407070b130344004c0e4118000c503010406e580d40401561b4101c441147c0200345c8100 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 866723012 1250 866721762 866721767
    0x6130510020f12040801060b0a0801030303020d06030b0708041103032809180203070210050103030e0111030d061d011d01030b0717073b060f0d0213320f01 68
    0x510001866120720f110602110408102420840f04040000c0c0300b410b440c1c4060a200d409401030f01c0700030880000051000901039000351101040d2802d0000360199a40c480c00420f04042d522003002c50700040c01c0c44180040e58140060b01c2c20140c004601c1c0560321b04d11990b07030841c01e900d81403820700220b220381406c7d0b00c140f84c03030702c0142440d88080c4040004d14203007100940c002d56010015226050b1a19210a0305001d540c3c12a501034480009442000c00152502454003c100f415800100301d510011002446040041c2011100200c4e80e40d003100a46100c03104c0607044980e00d001840e4501d0010352001901c0703410740e50301c1601003c403502e9812056844441010741c01144110701c208002589500102c1640c80300640c3ca0344440c202040190f0001e000010900c813120f10343d104440380c080e418400010700b43c2c400e00310181c51508024102d000f0881e040307502e07400c00390190320078100150040c462900b10603a0550f83d420711103607104010300700c0010200081e60300941950003040402ea0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 866724262 1250 866723012 866723023
    0x7020a080c0f0105010b1206010305040c260102030106020c0414041e080918071e020d0e0d0515070f1805041e052a040806010e040f1a0f060613051002 66
    0x2144000138000c95031035000c417103801d0b00083e01000c0340c10b100d080000d240d50301c00e01516018070b4100403244880c900348513696504000c041030f6a000003154081c0382c00c044600b440110f000305416805071400004910800c001e4914502d0400068990a410b00002c244031560103103554031401030002140425140101c058002c090f2940e6000302080c107201143c242c1c0c0e10400d44104070701c0c2c2d0780c00c2500d071003e00c140643c990081404001a030120300140e0302d030340c050f40001024a13401804004003c12a603211442c1c10b0b001d104040d516074a11050120154010801345200c1c0340904042120704142a00d0384010a5a44655480340d501d80064680250200f030070300c108400d503041c081c0040d1420340d5114407401c00d04600460002811407000d403a006510054030b00342c4101e180a46166440c100426040c0d40020b13006544482000c8480c0d4006411909048100c0039644503845003840c02818060064070018903450160f5810400078069084001002e03007510021155500d40c42c0da100300803850103 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 866725512 1250 866724262 866724283
    0x15140609011b1a06041a190321030507050f0d0504020f040203100302100215061002031b010506091308030403030f0e0d020f0105060f0907051e0d0c02070b0307020a080c 74
    0x3141069060041500c12022401400107140d0741d507403130b102d090100b00ea50b0140385c1000b14034400105041441d100800391010410113845010799502c0b520f900390300f480180d5640c6520070580f07c0e005d0b585505030080340c3c3d02804600304541821400c203100c504034400c42500e400090398690001e8115030b80c0f480781103264079014200315100c0c90f083c10201c0d65403c86000c01d91003420404014410035100080f414248150b12840d40242d80324070090018170b002c4008494290b01040c81416201e070307110705407c014542070800204a0303003003560034000d085038058820322004a0800044003c0341b80042100e411079403501d0000f81084800c0340502c0200756114040c1c000b4081c0307500c0c00600b9a80002c682542000e444020013242c0c40f14801c009080c0781841c4000c0e00180400700080c0745074081d00250407801215400c6c110000d03400d0120806035400001e65003481541d075105204e109a040205002600115904a10b5803d0900c0d01a6407101c4085005054100024404001e4081440f00d407280 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 866726618 1106 866725512 866725547
    0x1507180f050a1241031e0d1b17010509060f01081509040606150f020709090c0b0c06010317090f041107050f030a031514060901 56
    0x403d1100d0b03c1658081215024402001c000d01a8680b0b07002d002d03d424001c41ea4020025480280d10b6403450800c2d500510003100b130110001201080c40390b00750446600c0741e001086d410050508950311248120221011b034000c1504087c1709045c503480210307600c07403e80c0c9401c2032103c90f00d0304546483d400008050310b41e15950041c000290090b060800400041030342c130740401c2c5010415201200c0f5959582020842c158180440c00e0b16506545003241001203030900c0259598100d004200180b0b41e035524842c10441c2c44031011000340300e030600c041d031a6200000502e1325a0310911003030f00c1591040d0b0011014007a21022600c0194005204489054035801403000800c003040c105014842d08100001c0441c404200441c88142406e004581e0f41c0c0b01080024103070384e598516590700804101f01403141d41c82d080e4031079121b020305803907842d19540b01e1001240ca400400107503500c0c = true := by decide +kernel

theorem cover : BRFrame.Cov 866546762 866726618 := by
  have h0 := BRFrame.cov_init 866546762
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 866546762 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 866546762 ≤ n) (h2 : n < 866726618) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
