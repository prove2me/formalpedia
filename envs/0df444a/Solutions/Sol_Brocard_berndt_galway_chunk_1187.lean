-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1187
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:39:44.395847+00:00
-- url     : https://prove2.me/submissions/82c514c4-cb6d-4155-9106-a0260f2ba20e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 213309352 ≤ n < 213489208 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 213310602 1250 213309352 213309361
    0x804170403020a2c011202040e010207080306012d050a0206160e0103020f07080c010903080705030103050607050c0a1a180f07270c020a0614090a150b0a1d060108 71
    0x3c03000a0000c840030782010f441c1e01c4501c03403090500144030b103619002c00d1074000b0002c00e04146c854840101c0b984212020840200304a050718203038000d079000500340d003c0c1480001c00d0b65000e00e565002c0802005600d007014040c1d0409040720704034116403080007550208a41542503010040c440e000402d0f44d4480c02444122407004018240b088130700d5040507000318580e00040d82000a40da07010343d2000c5c1294880c2030008080d4000c141c074100a400140105011070815070081044038140d0750005d0241413182d071440c5090f995a4403407040b550341071003600c00700c0000ca91202000b861080904840c4101802c040c0100c113340c2647c0c00292117a1380000301d010111401c0011400101c40c0144e8440d5055030030786500c080044152031665045038242204a4000d50303020840516042c8660020803c000c6c0202d85404101402c40d0700300c0850340f00740558004241845404030404000c5180400e181a0010214220000075489001c16000c0d007a140e000d000c00c8900042d51001c02840c184803285030 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 213311852 1250 213310602 213310609
    0x90e0a0611120420030a0b0703050c030c0405013015080d0504050f01020109050f01052d0402040e0106080f060f07050306091f0b041806060207060c020f0d050706080417040302 77
    0x2c001e0300043c40039440005507a044940c1030780104452034000c1c02c0d42c1003110710341400d54001c41d048500c200040e2615000516900811060324000c02e01012158100ba0070f1400650740030b15504203840508100e401d60442d0941c3e0041080c01c544003101c4041200e01041c20520b80044913508050b00e40c0d0803408600104642c05410341e000ca50302160340700b0000b040d490050380181010f4002610724003c0c07040c40480308505400c9980101112603114851040443c6640c206880380d80600c5000100040801d01518180c0c00080c00f030240c0000014032695070b544810314140d850740003a0f1903600280304110038110340311030702548440300c8e0414921710300c5c10fa000180020002058440040241d00e0030064104103c40351344c01500b14a21036984d01d5484180c04410121240560780c0d0315401c01401052007031022030244c0444120351140310501d00d8503400c03c1001c42505042981040aa004c44000f10b1810005c0304010412521540fa160500e4240076004038044202c06110100c108010801a107 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 213313102 1250 213311852 213311887
    0x90c0103090c090203070f0f050405180a06210203011811060706090c0b19030b030c0d060f0207030827100e190302010204080708070302150a020304090e0a0611 70
    0x24030300003504051030300e8403180c0514190040b402c07461000c810003609039003011180502c08081d885e02d441016600d642142d0b18440c0e405034a41060120340820720315400711428681041c07800c5004140162600c00a20328040c1a038400780d140f04500c40d000040d070400b807140041007451900c0c225084241a01c518800d0000400954007910000803810b0a000c41a40000702d0158842c04055030f907943e880d0f445035280c200004500341d412819060302c4010307019128405181801801074010344a11504000786401c04110a5131121340f03501ca00700034040e070f030b200400c840c91103500d4182e41ca0a1058200d8204420140100410485018400b00c03414000401d100c40070094034000c24103041c20840306017000d40d51142600101c10901e83c0303104254045d0060004d840d0360008071201c0301d40d11125290303100614800a50030040340a95107018140c2c2900070003c1b07584600480780340c15a145078030400c03590000038201071500301c10f0307d0b03408016550041940c1626100650b03810720f00c80388402d40b1600e = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 213314352 1250 213313102 213313123
    0x7060522030f20190212010e06060a060206042018160908151b1204030806030d020d210908070c0e070302190c061b05180d15050705070f060c140309 65
    0x1040c044d8001c402c41d5116040d075014040c0850082c003c0e41825401550f6602e0140d50791441000c1c41b9030b010071183e00c0001d01601c5150000000c080e050444001c42e1804e40f1038140c0c0300c0d00403460788003100c00d04c00d00103070880c002c407803250300d003400d4007020725008001003080d801c105016000f0080d5250708104219070b10b81c0061310f825180c4000d0b1207c00c034a0b40c1a224402580300360105810410043c11b41050f10345205000035015241d504981c2d103012038603800f0f01801000822119814280c0011000d0300701d94215500e000b0000314440c103500e0ba00d0803078001020071501c1c041c0140045c40b004c8400f0810a130400c80900341942080c0003810300d543c541295255140801c0060030000c018004030360410303008082d81030340140c0f49940c441d01c001d080d0751207440307603045e041a01500d0300c009041900d0340360b5402d80c0050b000074000c9402034005020f010003911002c1017082c2400414003082c0ea050045000510885001840e1840300c10f01409180510003120540038042c4100500c400d80894500c104 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 213315602 1250 213314352 213314383
    0x1d0907030b070806010302041d09011b17040206040e091c0801030c0905040f0c060c0c0510050f030a06090219020c0f060415030f02160b0112020607060522030f20 71
    0x1951104e004070028002c90b405a01c41040d42c441580038540c044e40c505006040e075000034844240d06020710000304040e1403106000540140c0c03521201d01c00c000010381c100d0b1000701410315250381d540003011900010780d9104e004c1e03001144c0da040c4441c5001c07840103485110341001c0b51150b14544446006101603c194000315031540c00182c00c005103280c0002e407095001c1601850b55444120061016042c0b6404903007203009881c0200d41846c201c0440c10fa100b505a60312440c01e4000b40c1c02c0c4a803504041c01d540c0d889a01d0700e201080b1103000b800540b100008000103002050407644009182034103d5400d40c1c014030b0311010000d8540c0b90f8504907429200d100c04014030318040140d046004200d03203040302c5003484c13000c200082d142c03601c00c10400c0054007960b1034440076602ca00c0c2000e070305041080c000f940080c0801a404c0082d960b6046181d128242c64425800c040102c640080003a044000441c00900031617006c540c01500602890713120700c072010600b03103040ba80e48a0030303541c0c90702030f03814085 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 213316852 1250 213315602 213315617
    0x3120402030a0f0302062a19110a08210f01060e180f01080f060702030d090201110d090e01090204230303090a030609020a05010518010e010e0a1d0907030b07 69
    0x5545040255503100d6a00448600b043c0250382802512900242c580d0700c042e4550343c00310001c40f81c801e0703100000e006142d8415850094102c1030303d2400703000c9a2898041c001c2064041a10003424004a0003142c010902d1a5503400007400340a135900c613045004000480c4041804200000d035144a4150b90041c00d10309d108008c10000504a07108201070503c0b820041410823012842d80c0d244281200d11440480d900c140c3d5944111352500c50854501c0700580c4203000c60041021144c020248103401810302c01c8400c1940807019040095a02c502e81c0801c014180030008040ba00c01d500e0700400f10a14214101410101060340d005891000d010340d000ca003a911500c41d075006d0040340c0415000803c03241c0c10f16902c1c5031250240c0154403069100c1c01aa03040010316501038011101002c548000d01c69021000c140156122600c1c13140c3d090400803024114076240e101c4450a1020340303051507004a081a20800c88031558a009211180030340240340104001000300844540004003800c2012 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 213318102 1250 213316852 213316861
    0x108071d01050f0c010e1516050d09060204080c030c1005040315060801060807080c0108100909060b090c041e030201050f0a020c06190e040608060a0902010e04140108100c020312 78
    0xb201402070015109269400044000e0708401c150f009020007118070f8141c4440340f1114411040e1254200c8083c00c0c44c4a000310300400c010b100310010f142c841c1c1502e038000b0754840d403a1900c20403030300329401210b059441a0703150b00d0b981c90200102c1610400031a01108101030510004249018a100003440304500d1100d1071510103564200a02030301c159402040403c0c0d850204603990300c0d8a1207101c1c218007800b0740e017442551103a03400328401d50b1000b6a0303041c0d40e0b291003254801003503445819038101e5a41c4003074a03001e64400381801e001d250b522280541315801e2000e1508002c40b134615034011150091070400060340c111094070b40c01c0c008041842d8031840c0200c02039050404c02000c10b070740440001080940c4d52054241c00001200c190345400c0610042024401111040d0007403c2c1030381d10400014802c0c107082e81000c004a481894090309640c040c0707000c41e05641d480444540a00200d07801401020f10410580700440b0080c08107011150001d98040c0d220710814a142100035a1000000c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 213319352 1250 213318102 213318107
    0x10140a1a1b060717090316080d020903011401050307081c031d0a0f03030c0c20130504050304051c0f1b03080703080603102904060b030a0203010905060108071d01 71
    0x506100036a01c042e038000e450000d2004149000c4030660300c82e00700107030020401d00e0000009481c52100c0504102d400340c02c0540f00c1042e0303a00f0451071004115000c0000b920030f03860a00611404104081d41600b055040c10209414121144c1250b00c80e64003402d001581001b0346c003144201d1074000d0400282c524903803100c1c0c907030001c41d007120000c040c8108000a01041190414825420702170fa070204444910700764102c1d130746500410050240038074502c0b0a0075190035004c07210301c038080052840d110b00301c20305010410b98404030b50581711a00041400c01c0182400d0341801c2c004da407120b060843e826807036038507011006080100079200390700c04100c41c20b020400d00582009190007550ba10744039882c601c5c00078544070017100c8440c000c0c000c2480d55003040200b07006d11941108000100b88541507a84d2003400080c0b03600075171903402501e9120000da242c8418000318091000707031002517640e40c145440d50094a402511040c1002128000c000215920122003008034003100404a01000460b004 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 213320602 1250 213319352 213319387
    0x50301090201051c02191d1e01030e21040305010509030f1b07030221070b0a0203040b22080d08280c1419140703051204050708030310140a1a 62
    0x36541a0004100001c910b079410208841c43d0640e0550f005816908060601190380400216810000238400160a080d80240c109a0b00c101002c070454020305440d81d4010409070300d1500002e60600001000d1061140a0144591020941008502d0302550703032440c140c14030600850130743e00744102c030804070b03015010700c0040001c40d00241200750000110b4014103000b03c4000446d1700c18425020001203000055040d00e02c036106640185080900d05009942d503079100041301940d10b104420365480088120002c1400b6111000c0141401400d44401400d405409098644103100184800301c2e1000d00800740c0601d0701c0040707004140302c1d090110640f015074001004050b0070001090040096141c0d06428465032400d03641c401440c46104031880184c4071b0040081e002580030070000f14041908049a500948640708455071607035100402c0e42107800c2511418109140c1c1e003410000360904900c1840f00c160201d9030307441d14620b00f03065a00052064900386180000c041264114041003040 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 213321852 1250 213320602 213320617
    0x61b01020a030605040513052802030d09150309080901050c011404201203091908150109110a0801051c02060304050705030607080f0c1c020c06060406050301090201051c02 75
    0x25921085655009809070819000d00c0380507600e02000250150121243c07c65060303044006080e40c2c1f51001e107040318050300180e11084201c640d40509005071010001060090f00b01c2d9a064200b40c10304280700721000c04a0801010142002681001705d060f51080b980314400900700b5079501c2038a20849400341824001c00b000101e80704041006112003e0041081554250790280c0c40a0201d0100b00090440901c0440d0540c002e0001c0c11703803810041a1100c04205020200c4c207056540d58010385020071280d81c10350380c1e00041c0010004007900340030300c550700d028066101d424003444120003020010140710f0144141400688400600c0741280c800b8206500a8851a500c1c0b400e0b06000f59102c0c45440b0b007038000c0c03083d04c0001c0c3d041846204064055400e107841e206564540180e00314140d0005589a00e1120708000e1070000c00c1c005100a003c40107290002d40407600c0c0c80340801007158401d601042c020307414071a07040b00503a4030900b1120010380104100d10210080405003000340109070 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 213323102 1250 213321852 213321907
    0x5030a150f240303020c180609060f06030c04062a060b012102090901060302030c0313030215071e0201020c07050d1a070c060b0d02060d020d0f1a0109150801030206 72
    0xd40584024480e00ba25070540e4001d400303e40074904c48800380000344441c20b4820352a0b00d40c0704003080e55072602c00c3c0c0302504484000c00310390005020100142c0ca540c015124411100f00001d410040d0315003140f04403888202c0f900020034a8901038003000001144454002d10340d9a0b120030f185403d030700501400d9082410500492845041075000300c009500000d001c80c8140a14000051814424001c41c1d06c14a44078082c03505589800042c0100c50b4000e420031420350140303182130308050f0790310307503065100c0c01c0c0c1780c3c1e0362591144810489030041300c141500007085900410415500840000c0c079001122401d8a1500c000f040ea41400f1000020004c034030340e001c43c815000c1c001c400e640120b40c14007a50281c0e074208550200c060400800224214009400c02d505003c0070828014650140c1701e504444034001c21050031008454041b100e4040803400c0c1c0820041082c8403a5a0001102d005800d214068070081e0b819488041c01490341480020302c92580021001102c4103250b00e101230101101 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 213324352 1250 213323102 213323141
    0x206030702070810060e060a0f031704030812010905091c0f05040504110306120307020a030f08070212010204061713080309031b0105011701020a08010e0a0605090103120905030a150f 80
    0x30310301340d00508058442c51800380407030030200e0304520300510300604459130700003120002455035075031904e0750101580b9600c803404148030010104403e40000c16008000c500081001e605102c003240484030054a405031503440f8082011007005c0602800c81e028455040035043c00c08142c20885042c40b41c6e401417504142406201415180701c1c0300030350300a020460b5110000712000110303650724050310030040d61191002100b0030109075601e4402c40181d0150340300c00d141c28126004101c6e403c2050007141c0b0a40e50010f001c1082c19802148044105000712003030240b401c0030001020b90362100b50b000380c66818000081109c0b402c0800c02c07a03261503c0015000c403400041c00301e23030307009000c02d2040c0ea004003c031481c0d07880081410300c02c0700c03100807144d02d410f945a400c00300d4614808800521042c0100c0da607400c049600c0c1e5450318168002c1d48074080b04484404099802484d11486501c601d00941c03201c043d0000080e040d400d143e600c515034900c001000c4c000c00420304081c1c2101011942c44038443c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 213325602 1250 213324352 213324373
    0x9060e070806070c0503040608060105040503300412060b031c0906020d080708070e0102010e0a050604020a090902010c080f0409091209080705031f0f020a170c0a0c02060307020708 79
    0x81a200c0c00c80303030a4010b81e03006a41c0c80005491558402c00010419002044248115801404000c0e040b000601d80ad904241d00c075408203192200300b04000c00800c0c01241e00440300440654001840321207080100e00709440d04490003180c4c140190003d040320b449280c45002c64404200910355802c40c003810b0001c120040c08050244803e5001c0c0d42d0050043c05152000076000b034400d07902410b07150340c03445815911030404a6001c24070341c920504554a500b10232100c410200440001607006001070030042c20030744108083c1d01e016501104400741071401c181c016070b8025400c0c1801540008150741d0310b1030717000141e10051140f5002446a01d103090500014440e05609032064800311342ca800712110b48403175201c2d035070750407a1007043d0b8940d0210303030301c5005000001607140c442c51790020081441c10513800d440059810000c1480009000000c442030b44e81004182103800901114405280c174000d017000070640044c0d4103010340290300c00400300f07821601c200a0703000101201c1d41901d0700d1201 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 213326852 1250 213325602 213325631
    0x20d020304140c030102030403050a1d150a032405060d0b09070f1106010e060105090d05030a0c1e050c040e0312070203091801080604020d080d09053d050a0906 70
    0xc8a0003900310f4030603040c00b001c0504052007128000c1d13805407112403e2803134889040b078091140403501201502c44102c8110759403030352021740001400312001192204071410008080350401049160440f01d24220a105080c080380b00c44180c61003652010b9841501c112003001801c032445009400142c0740d02004040b5500c0304000301c141d016551039481d202c0321101c407256540c00a01400d0b40204010300030408644c00381c0002c000c1c01c2800380542c410103036180c0320176003950400700c017141c0070031074150306981002415408282c1020344010321111010064076002d90703a50404850a000315518494081342000800940d9440c900c40e03071180c0054500500001d40305e40084811a00440d50312a0110a200100c0c031500d06079500702c00280020703030f07070f580800915070070103071055030700420410158160303032014010200344030300590050025200707003980000c00340c201c44c880c103484904100ca9441c0c40c03008600010107500008402040c0c88e1101a110402881015030060600b46001c40045a41e074 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 213328102 1250 213326852 213326873
    0x302180f092719150e10021b010e010506090c0c100c0302070b0703150906061211090d0803010305070b0414010c110a0303030b09060a15050a1b061a010509030a030c0501020d020304 79
    0x900c5131401a0751411203024003000e40e114802c0640b2550062110f46402515075406080707051542d4207000b034403030500510182110606621400715035152410050703242024807040342c22240b030800c0c2d2440e240300c4018083d00c90300c0030301548041584490b11203141034426015164a0307504203889540f00d0414540140040c246000400040c0f0031100b00059507454070300c20503080703d12540314100708a81d000c000300014520703100d03e00042102408020225102c02c042a900d80348610807041d565419400c0c601c4c0f500c0116840242c80000801051203c000f151040a103189400c4c00d1848403007006117800c81d09015814506034214411440010925606820a0000b002c007628195425201c520034415034034039600038081c1d80e0b840705030300c1480288070f200100176425851501e950300c4506811a5400c5c003041d000d041c1c070f815445131200e41282c11010100c504104007400d20514181ca0f420100f0384581084c0005414071030754002a00900c1429011201c44212442d0704541c0c0b0310389840e1407407010 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 213329352 1250 213328102 213328153
    0xc04050708070212130b030612011d0c09061c02180702031305061201030b04060e070b0306091006090b070c050a0b120109020a0905060a0507120302180f0927 69
    0x41c85210030700c1d029000440200d5170000c0c0a0f82099403a40d0805e450300703240d544040d000d0b41d0040080360b041c0407180400e20600c007881c094a0034160384808a1944d0500d40345e148240544905104070520085039903065030300810001c400c4464074040b100f400010244518241c443d14019455030400ca10b6035400710003031046502803410048110384640501906002c2c0c07128245060620600500110700701200140d0300510440021a0700354004002600f400116032001500d280301205104440c50000c00310350344501d03510f110b20720103450f046000781003940b54880d08c80e0407680000c02030141b20b0000d021001800014000202e450303a00c4000030803540c092600200910400340c008241c0750400e0007140c004c080c0940e5400c031900d0400301000380951000d444c0c503007804020064400004e80404158940340304a86005032140400303d98154000e15002140344208490003803240c144c0e4641400941220800c101d80c072662824811131035422220207201e9015120b0301005483c61610340c07260a0b42e0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 213330602 1250 213329352 213329357
    0x60b0a0e06131b0302162f09060a0605090303090a0f03020307060914060d140414010605040c05070b070905131b0507110f0a0906030609050d020a02060406030e0c0405070807 76
    0x11082c0415060440e0100d4909510440218180d280568841e80240c0b00c000c40944480c461040e49994801d60039840c4c40f044d492509031511121100200080c103400304400230f403000d00c2e6500e402000200100818002d6030b0900c00003080981058604206079a804036014040140c0d094032150b060180340d00c1880120b210b4450044003042c41c500c240c2100044420484001c0d284420304810801250004581003116550303131881d0022140341d070900c1d5405117000d20034a07080e40c1c441a04031800e45601c3d03080b0f6070145044c03810b07480240d54000101d888060300503400c2001c548820004441d0403801d0b920055001da41c0d4502c907a00602e0540c0540000702610001030f5138040e45d00d805a41314021044003070101100404540c10038145880b8441e2801d40c0248419071054880a0b03000444900781c00988107180ea580c092000c0000800071280703031420707074001440200b9a9a002070854411030288004050711400ca0315000300003006440b0714200c0042040c01140f4150700f00418480b001c0320304900 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 213331852 1250 213330602 213330619
    0xa0c090506130305100e19080f03010b03041401050112030e310e0705060405042406030c09050402070c1e05130504030f18090b150c0c03061e13060b0a0e06 68
    0x3c125034880e4182c03c0d01c2210203410941c2e0451f4403021702c480e007820207a0343c0c00e40400102c00b018418074011800781007040f103546e40320300306810002d0100d642c100750282075a2502e401070028039000c851040d00f090303042c640f2481c0201010081440703540d0300480d155180d0200088124039805c01c190000031040003070401c210901068244036903c030010300c03034150011801c0205000314100764019103524100303407018100f131040c0c58180d880c030041142d0044000079942c0d044049a01e40c01020100280403c8030b080d803e0103090f4032801004502845001c446044800d03840611246441c103010051100038540d031007292200aa580241c403040b01d040380007981200070400002e02440300760741d1480303070641c00c0c180391400c21500000030502ca07100c0d02ea00620f0410b155402d003c4c01c6006088000c0c514003c1e145001180d41498a040707009810155a51054003003080740c8090707082d840c1c0e0302c481741000c035030400c01c41800d10380d00a04540f842c15030424040c0002192107407100c60346600600c0141c42651 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 213333102 1250 213331852 213331873
    0x3090901080105044b1b1a090906040b03070f060e0f030a0f020609010e0a08010222060c06090309030b1015020307020303120714120a1a0105030a0c090506130305 71
    0xe00f240d4a07402e4851648241714006003100745100c0d503045003480c1c140c9008108a00507203804c2d080c108200681c072004060002c00380304070009103807407904200a0f05d1016042c03040520000303d422600400c1300e0300540d41c41c3c1906074182e03000c018000080070144d1190b42203e841d03000c001c081100220729903010745101480c7c20301d00d080001c0c4603090b05801036004182102c4c135908100c615484a100c0c1c074104140100d00d0a640d0343c4c1d0710100c00040c01403600040e5200084210240c142200e000c1180f003c0c1d400081c200001070b00010850246c075882032000070351815620302507400d0ba016400c058082110001084200340200000d4000c0d100148003000300995003550403a0349106071403000b501a0414400d015903105800c040c1c5400803c10f0500c048102d4528815a030141c1146109144a80302c200a01280c06200e1003208803007031481130700080e110007102c00a42144000b4146c0d074041070742c81d1000d00c0c45031300c02c2403c4805020010030b4a0f42c0c5804510000c0b84640c110300043c1c40d01d000f50080d02 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 213334352 1250 213333102 213333143
    0x210312090f0c1203070303090203010605030d0305190b030a0602070611070303140a0203010b0412020a0b1c0c08010f06110f0f07031a040209010e0403020f0102160302060609010e180309090108010504 87
    0x5034051010f1030045141054541c2c0c104c001c1c00510008a82641d21818082200e035024851902c1c040180d45c1d0020702c07440c01d48030341004103880000340920340d45808114040e588020030410700c60b5400c804003594924440c60500024054030504112881b80403075884101035268000f1500c460207a000d4103035580300e03842d40344100d200038402c07903003000d100f00020010440c246001d0000e1900040c00d0050140d42e0300510000c80d841281070440600c1403545045500340b01e4818059222001c0c82c01001c4d540c144407003200a01c01502503141401890003200c00c03c007001b002440300c000f05c080240c0b1000c80c034040c150361395030456010848110306502c4851141c20ba1100c141d0380f103282c0040080803140d103094441c0b40c0200c40a4403e5086001d02c0c2c0b12400002c6003400144800710b80068400040e440c40d040c000e00308400a05105c0c403541e801d0004100c482000d0040381d030400d140d038800518510000e13452070700c0c500c51206219005100c800001400300419030241e8031030390242c2010103800c103840094 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 213335602 1250 213334352 213334369
    0xa150305090115050f010302040801140412030e0606120f0d02030307020d030b0d0605091905060105010e062a0a02040e0709060f0b0d09030e040216021c02210312090f0c 74
    0x81883c03000c5000b0050382c64003504522124006050042c6016116854031f801c0d00d142a29401500030500140300800800d40b0104c0400c10092408205100b074802c1580e440d0800a001207204551800c040700301d01c4003c1c000c501c1e417500c10204855a20401e6500603460f80c0080311154054000c00d07500102d043c3c02402013911010005055100c0d81000d5558900140409400703030b46e483c854088202030281d68180007859840c0940c00621030ba6140000040030440040c00080c085c1505011720800000c082d0404200260004050070705454854011031900852000c081d40c0607040c008a03040746100801c028080c1e03103142c0d100b40a5540c441c800394090207018482c5000b0000c0410418400b5803c43e07004205091091625608801d03020700000c0c140d8004841905660858100c034600711b1406141075000c4440300220202801456000a0403200d40d4641d101e0b03410710700c18559007020b2010b0003103414070709408a0103450b130b01700740480640d40c407403110032001144205181e451080c03400c42e14 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 213336852 1250 213335602 213335621
    0x70501270b04022106250327020f04090303020d06080a0b0c0f070c03080310060905030d0c0503120f040b010504020f1c150920090603071b020a1503050901 68
    0x6040c41c01e031180d50911400080d50860002140040581600c05202c107200c40ea00881c4a07030504500c0007907441640b01114091001ca509043c60411001200044443d800341100745490354861020040e001003001802a0a00281d003c1c1c0381c0ba12002c04c05405030b020740b00c0e0041c02c1d42d0412415490f00c082d540e40d610456000751200c1e600d5000201041800001400a0305030300c0c071014204800d5a03907140030005550400c442c00040803042042c2450400e421304000c1031030303280c28884030381341001003500c0c0c104001c07803801044009000304050020400440d07600042c030143c231140f0f91811420b2000caa0800391001c0b94804501800040d152a241c001c0c4d0382c0e000200c1c030b0344a01e00755101e2150700d00c900314110044c1d88141c50b0044240c40003640c0c81010001d10800300b0200c6c00501c461750000480300c10480400c1c0000007440300354455151202500c2e4481180d040c582a0303c1c01018018100200303881d40203612501100002c100b14544a2026400b00d0f1951000d120ae901d40115590076501c841c1c8 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 213338102 1250 213336852 213336863
    0xc05010216060f0506150a0c17190201060b0f0c030f040905010302090a0b0102151f1401140705030a08180304030f03030e0604050615040f060906051f090302131107050127 75
    0x12005402c2d10000d040e0f000c03607806d1480940e10a5030b83c1c00c5551a145049182c060408103904200040e2b004076009406c086200800816080c404c40440900405003003420039480441d03070802c8000b04000300da414108103035050340c9499840d2242400380c202408201c5c05900c6c0b03880455203820392802200d10701d09050300542812031404030307920b070003100003400c1d11020844c0c10000e90f5262100045c0070040c0100c00d09200d50030001600241c20020909200d1b5030a81c0100118804a540031003900c0580c070040c6094401c0d81c507452102c00c0644d101d0312800300140000074000080001089030240a507210361414882a03a42071805911400f046034007816036045040024869510031141c1501000c0041c00080c041d0000310000c03040720b038250842d80131555144024407042c645114012045e451901c8241c1810100000060810700a031000900030f9000505912900c0700c250445010520100c050917181e0015050460281c1050280c0c85c82500030030b0384440c3c0c5654009102c01d41680c100 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 213339352 1250 213338102 213338119
    0xc0906091409070314090c0307050102031c0507050705030a0c0507050f100804140307031d040903050a030f02300a02030114010c1103060c03040b010608060f0f010c05010216060f0506 80
    0xc1c000c1c00b52000c0014040420565108041045030496211450186014030001d0400445a50a052420b035041d040103044d917005021803681040310b03080402580b130b0342440101c0e507600d5455007900c880c02a0750005005020215101c985564803803d1201c2c024000c00845280d1652001403040214840d650355400062980c07080d80418010300c05190002d05c2081da135509018070800c00d5041d908200d000b1400620b0f841c0350004041c080f4140703002c12060443d401c022981880d5005801c920070320311000140740d00d80400c00d00d180025416119070722850451382c44401c034911024800040c2c00d107518607120716070401148070580c151003501e0603500d07124a12070f0b210054500541d01415003078400c4480c0d031038000c1151540d072814052503000d1075144488948904162506007400401600024108075280701048515540d03070031000c80d00203003503c6640302c21460f035004135501d401c42c04000d040c541c000101c14242c841188200361a06001e120208a428109204001030390020760719180d212a51 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 213340602 1250 213339352 213339389
    0xf01051905120a151a060a0827060a020405031c02120f0d02070804030302060c131403010e0105070801060e01110a030513092a030b010816050903060a0c090609 70
    0x84074200000010001110f140300c40664a00c07650700029a45004103d4a03080c44000c0d1081c1a1005030303018001705c035103074104200300c007005240c80b800416004a000041d6104c0e01d8030355032002c400f02074020460644025107041080d0b080a94440e105150080c41411442089842003c652484240c0a41d0203403010903409900303140c09401c003041c800050303c070407c00b807040c09145200134031490344030b43e459070b807102d1540c01c0c040d0074440c0003810885000001c2001078590603081d14440252400c3c01e2100e90300007880d8000c2401401e103620030741051761030701c802d10459a4101c81c00038100c4281d0b42c1c8203035884517180c1c01110032824400020344c4907400701c01898002030258028241c44a440a410706809513101e25045c180c520720800c08010580c460030300403809400040d009a0020103041c140711a84501c0700091040c00c1c01000e141706001c00c501050081885a002ca402080006046440d5420107441403801012458000800306101ea40c1c00036445c0e006032080c0c0101d410001801541d00d01 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 213341852 1250 213340602 213340609
    0x8040b04030807020c030f061b03040c0e0c09040c0e09090102130b0702010c0203070612051602060402010804050c030d120c080108030a1d09070e030105010501050315010302090d0c0605030f01051905 87
    0x2c025207a1019801750400c00740054030200022991a400c070001001c16060480107014540c019000010a1000801c1048042801404204201d80310305481c03185983e15102412040d000d030460199205080180b440880c0c0e502191140360b5140480310407009454105080d400c030321070641804060260103004004000d040b50140c0b0500e4018181550007545581c0040d05226064002a0210b90030503140e48aa2080303115155002081000d4507511501034a0065070340c110040000f410840020005400c011083c8002c0401c803802a0880d6103500c03031701a026204c14402010313011702500e040d001c40303ca00c1c860003056040b41d28240c0070b5443c2074a110021100d4028928627243e030700800740943c1c0000d40b5072002c0148034070385541d580160742d0709030002c050946406a0010741042400c4c0706000c00704100c1c00c54091201002d007801030b80da011031408074040c0c4070210b402a141e8451b40c1e000240b020380190041d0b00c5a0b41c07900f0b03c00300320384c0c0310410404c0b102407003040d2040842d04402c042c009804d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 213343102 1250 213341852 213341867
    0x120206090904050622020108060d020a03081902060f01031a070311030a09031101090c050103020d06050901031406010f0e040f06140109020d0b030a020d1b150810050108040b0403 78
    0x140060811890552010041039011900792022105540080108480c4000c1028040800c3c1c00102c5150b00190403900007d0241001602c2141f00741d540d40490011941c0c3c0c04201c2c0001c60f4441100c6883d0120003150000543c1804007240140c041d103800616070803180b00441d0706a80d4000740c044054400d013400401083e00041c410342c01e141d07a8038011201d485414002e9482449001008501b0761a20300d0b0040100070340000c09079080c0e0604031500d0000d01c02045140507108203180040e00ca40c0c00c0070100000d8581940300c9034010050400100501010b010956012031040049420f2641c0c0c0e0003100c0c0e030040c014814030301040c2c103210108000801214841c80020b015000120390340040f40101a1011000c1e4410150540e00103282d10000710580900400740400310301800301502583c001c268070400b8120018401201840744154842003c0076100c0900340d403c2c05200590300c000340241400601342e41c1e10401c03071074100700010391391302c00c8075468807850740246400f0040e1107903681942c220 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 213344352 1250 213343102 213343139
    0x92c01030807021813020a0914010b0903070315050403030b10050a0c020f12060f400b1e01170a0308090f10021306021c0503040201050909090105160e0a 67
    0x8403d20b2856201120348200c1400f0705a41714401a070505030b4810410b035804150f00c0b12040605100c02881110710311140c1504460000849654130130403a00040e04011050f00020450304026200b0191540b4a521941c421071182c1c0b82000300780006000c1101903071550b400c600c0002c808112240c2c07818481d9101361a11407010b8003601c1081400c00018001c0007003150a07803510b80c081e2081000714150618915007004010b40b24902d0b0301180c2c0122035030802d03100e80c0004060501e5480640c0c003500202d00454884d0401c60300451420070380b04140551040310712240c940704043d000402c2841c105e0b40e110a40c070b181030300204000c03040d03541c058032120801002030006001e41f40200c1b0100205012103182961000d500598400601403851946a9650050000c5501c08001c042071103152001301b4101103280c2c140f0039280d583d20710040350603100e40d04419810030402c50900014090540149004840401020303c031002c11800485a801120500f582d1100b42204200682c00054040c03d001 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 213345602 1250 213344352 213344359
    0xf0402161104060b0318010b0a0f051522090b06030c0307180e010602030a0306080d0207170c030307061e1a0f030a06090309060f02060112061d0a03092c0103080702 72
    0x1540c4103449161600211961041c204002180d520b50200030301c10442d800c04121407103040d45003400ac3c5000d00c0f000d640a0a80601900610f449501ca40d150940341850b42403150640c540f400307030440c040d15051b2031198035071090800c1440101440e013242620b02ca1010b1100d0503003183e6405c1402c84000b151341d1503018280c1061a008510a5581c4509902801c1e082e0000c550f00c1000e000000c044400540c000d40c06a0000c4208914566003c11301d2800c50f00c0304a200d075a80c224464926040c0000c0d0741080340c0c18400042e06500f0000140c0018540326400030010024099040301c4405507100c1010000716160203d0a9a5842c9410000c1d101c4904001e4100c581100403942c3d000c040b603110300001d5000c504c0c400c50400c01e5507800b000c0110306020620103032010b545091498144a0408240100003680310030302c0d5a8121300540b00200008920030071110045907508014000c0c02e054007810720f6050300b00c030070000101c2d000b1030448040d142c1c1c1040a5120381c6103840c0c0d1503254018031000c0385d0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 213346852 1250 213345602 213345611
    0xb2401050d0b1003061d04020604170f061509090d08011701200d1503050a020f1f08040606050f1c0609020603010e090d03050408031b0c010f06050f0402161104 70
    0x16511450a21081c3c20150340f00001c60505008241000c0b000c0c40c50b0100440d42804104001625482c054504840c3c0c1c40040758502585551014108519076048007594840ca20402c4840300300f071508030209800a8a034820240c6800d6000d0761030701d048541850200e002a001042245082c400454095044000008024176464a64501548188413a0307481c1000410131068106c070314481d840114100b600000d80b418034680d031315620740360a8038001e803203100b001020802507110141701d1851020080b11941c2000010b4401810618040c2c80c113503000b504c0c1c04004103080c244502030034a209001001c507914021070800c070301c11b05a811481261040e4460b8110801a103500f00514080c1040c2d2402441516009100d9894804100651000c043c241020301000c01d0801007140d800078040c1d41d41c0b100d103a001d51000c0c1420b12030140c0003500e40d03181c003d00003100078243d440042078881c01c440310010030f08000100f000303900440e58603012081c1001401c40005510441d8603840360300261000c00c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 213348102 1250 213346852 213346871
    0x40801060b03040c08030a1202210109020a020f01050c041a040f0308072d0803060a03050f0a03080603030901021e0712030c05010b18010b0d02070b070c0b2401050d 72
    0x182500c11950006100c114040140404c1118020629024140c882e001718206140d82d10000d110300d82c100101030b00d041e80003601d216020218600000704050580440b1031559491065100035840b600e2104014014020b120703020b91010b0046034080c0d01300030211030409051904101d5403210308400c2c404401b000b0000003841c0c0c140c10310304000031402104c486071204000c3c00c0c41c0b074038a190110060400c502c40101d40c0405890100070b5a01c20343c200c611203449070b8441000c10846103180d00060814032a914029420b100c0008100600910980e5980792035110078052594030300541340040c0c05a0001c44401000312040b100c082d0030020b1420840f03900703270b603106108140300860640980011311301002d0801404024050001202026075000c00c0b1064502254011400107000d900300b01140001c01c4150071056406460b40307250032408030041400c19007409088461a07460458240640400041c0c4106902c1032141e0304400614030300c40895844001126164420b01c003001e602a0b5460704071 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 213349352 1250 213348102 213348119
    0x101410050409060f031205030c030c07080706060e1504050f070c0302120a1e082403070905100614030f01211515081f0c11100218010309210504 63
    0x20002001d13844050b610543c15420942d4503400318107114404d201d0104103200846080c041201c1e80a145450020340b10320031860401110711805001078000d50404002154000c001e21469000742c00c1b013087d41040341e1941c0103000944e002110044140c0d0742000000c2c0c000b0340a06d00c85c1c3c0c496417103403050300c2c20500b451892801c0c5402c403c0c5072000281a4150b8080701c0b5018180410358100d20b802d0414013031070040100b000300342d0464003016100c02c00000d50842c1e47ca003000180c001c2c1054180c140603034500140084107220552084000043c0516040d08140000804890003101c6070841a00c860b820103440190100b0126014108201c0d030000107408101c0019178413038200301e4860040b583c0340e00300c100400c8200d003e81100c0d0032900f260164203054450b040d202000c0400c240804508460000e205036039085c0e078803102d4210760003402050400f1424070b500429040f204110380910000102c1c00440440d440b9206c018015289412400d81c00e46603048101003480c01c615110746040c2e10340000 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 213350602 1250 213349352 213349361
    0x3010e0603281b030807021011030706140721020c1f0c080709121e0804030f05070e01030803040803060d1b050f060c0717010b030a0c03020108101410050409 69
    0xa5806142011441c001c2141c0d014101100f03c40c02c01e0080c021508603150700041c0d1003801030003031240d01c26900c80144d207401102210805952403080d25200d401e6424054080c0880701900c114070724551000858941c001d40380070050a0500032190040d0010201c068000e40c000e068208007445424580310700501046090300c040c80c00c0e0748004c96441012840584410800f61a10041c400058801d106200c1c01c02c0840c0070300394011500000300584640d0355502420715440141030301b040000e01001303022150a410700c0e082d2140c0211740c40b45980d04803040d9242d0081c04028040f520030004140843d140700040c58000328024284210ba600c03686d43c28803166600c03007030141c2d0b80d5001482000186420074541e0311015060342c0d072a20380b0000c231103800d468107000c1c0070781c00850511080c0e504502100751b10410f80c0003000f1741181d00001460030301c16031556035440100c1c0040c8480c2c2c00a00cbd0784d2101c0350182d00301c41085242c40904c0e4803420801030403402c2140c20004100c8180300c0082c0405c01400f4 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 213351852 1250 213350602 213350653
    0xb0d0e030d060302120606030c011d0306040309030519020f01080403050909041101032a030504080c0a030806040501090903080601030203070e030615010f050403170f22050111011103010e0603 84
    0x100002c1940c0307184140f180800707800030510310700c0c1c00c400701701300e0300ea00c020488840c6110240792422101003154003098130182c2950481d501403044404200815800c12005802c2d00e0144040314070403481040800502c1c00d407100000d4100e1080303810401d0650144699540092082c14402d0402d41402c0200b40ca2410499066600e2032007103000d40e07065601485010b5480d44041c168402101d200501c4442c051800840c0608043d0768400150622000000392104044e10b40c0a4655005480c10001c0c151542660710078880c0d0b26080c0000341100c0740348241d00c0016490307203680c401a915000158000e400041041041c00303081b80303042c00f02d0b81d01440345c64400c101441002516050b001e00041110107864184410b2040401050020804044403042a02c1034803000315502e01030f1101c00c00c2c080c000c120190320800a101100009011618140826074000b0307a40c40124005206880e801c1c2e81388807680102e5008100014020103651f4000070b5408000501152900c00c1d08940d0b001003074040303c0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 213353102 1250 213351852 213351877
    0x9050d0c170a060b1503060d03260a060b040303081911040611010c080c03040f020609100e03101b0507060b0a180608120316090816080f0f06010b0d0e03 67
    0x4410b1000c100280c814210144801e9507186000c40c3d1011940007079110180580348a0f890440071203081504c01d0302d801f100030a03454507a103464024442105900881662803038100e41c101a0003264155a80068800f1a50150765507800e035207404119924040c00d190111010f9610f42c03e084d12040035000c010030050015540b40c0c008070a20420301800c5414081c8040308111500d000d100d562004607090340d17009904410352180d1910a4800603103c0d105070300445130040d03082c6080c201001c2d0003248603044075006038255402d449055032444100c0d074104d80400c1c0303107200440350761076114414400f92515500c100170000780f04111500041d030b81c1c0c1c103a41c8a10244007446681b516814040d00070f05004011550050074101c20308075981059000c0240140e03208a04030411081d0300d8810b00704000140300d410103603000181c44240000c059020340c0142407561182c00300d1582207802c000748880c1000b0606021301003d03402e10440e4a800d50000d213034050096250810f008090320b0920040c040b560b000f0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 213354352 1250 213353102 213353113
    0xf06020307200604030b0a0609050c0a12090224040308040f1509080318040f05010602100e03130e0916091d0a0b0606250501050a061509050d0c17 64
    0x500d020b10001d928000188442800070384241d06984504003600e040daa4850032510302d5541e0461140002c03c40ca43c02444868100000d000901c1c030b81d64000d11346031240f0358a8140c1c851112905400f614401d00c1d00039044071665200681341c0c24441c443c150b030f420900398100e20b4150340752101e0b1442d0f00030341c001503400f0074401e5003000b42d02c882c559080c041c0c00741428904100742c035115150b0b0f101e000740c00c0d075030040d021485c4c024560b999580d80b10311340c500c941006c20001540c40e4040255190319860800034117510b030650b0401c4500d0004107036a0070300490504402135a04180e10285510780c0070304450414490048001c0880c203524242c00d028054000002a0b460507841c45805c040300d0b02c82030b10810b9000754005801144004500ca54800304c15a401d0f6505c00840c031100281a0f0141108500d40c0e500e4103070a002c004040d00b0481c060607544c401030000350340b43e003450440c103c05c00c08940d0220f40e141c1e9080103207040c000d5420000b0350048c41d103445039559072250002c0d40f80509002002c1034001 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 213355602 1250 213354352 213354367
    0x31806010806040c15030603020301090b0604051b0f1b070306050402090f1501030c0e04090b101e060e040f061203020709020406020327150415170c03100f060203 71
    0x80000900500030a4010622030400303071036000700c221a41c000c0c2e40f0408000da0602c0700d0580260428002035502400812030058203080c501c0e206402518240d00c11803c1002140449491f190401240350440702d10074038201c0c840c6801c0c003040c1c3c0496801c0d030307018000c150710004100040c080e110045008400114140c5000c2c8108000081c004182125412444040c05281480c00d10000744003a404e0a0003d80d9a9460306d0030388170861000300060b44113003451448020002000810350245c2060035501c1005500e40b2a07a034650300102400f2110b900c503640701000000e10820203900e00450241c00040c5040c0c1011580b0140c0700e080d0454021128801135000406504000000c000c00004c001107040c94284030000b500d03032082c196203007445003201c01b40020940c030101400000107001858030301501d024010b00700c000d07040cc0c072840c10005159400304034001d0213040414400400e0411410156070b4040d454980303900040c143e103503288000040458140c480420140203412642c00541e240d8a4 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 213356852 1250 213355602 213355651
    0x9170a020c04050708131703190609020703020303041506090906060e070206060901060509040608030a030e1002040501020d080408070501050903030a0605030a0203030a0c03140a0c1205031014040603050303 90
    0x1800c01039000b580b40100700301510b0b500c240280c0d002000500b182048060700e050096034501000320b1080f4a10000050042d2080316000308030f1803c0440307a041c4621a55008002c04a003e0010003a02603081000050005601000702c121491100745e0b002070020b031504842000c43d040c0300c4088400c2c0b5620710051100b40039203080035501c440390b03100600461810703902050702d42e001031180005200307020504000c0c564458101c0000762043c4e6080360b031030310380719400200038140380c4128140300d010381e40040504c41454000c850039242c0c103030010010003251a80465520300001d10030355904406010142c0054401c3c00360f140603c403844020364407410702c5c3c07001c00101c90540e4131a41c8079600407502d50006031004070998040c03811303504101c00e00340e49038182690031042400a54400400018070200c110741c2099074007603070074050031070801d0740c0020480070744640c0305c01c1d074502d40d0700180303120708100f060b002d0140e400c0da440c006030010458030703601c0c2d48041c0b844e080ad4a082071411600285c0002c0c0c01c0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 213358102 1250 213356852 213356863
    0x409140106080f06030a0311010f0207060c0e0303040b04050112090506040303150f08120309071e080d091410020709020708031b0304200312030901051801150e0a09170a02 75
    0x1240070f0041021424907100090707907a070b0030040003014400700480c9041103020a500a080c80c0a401109541d152000e1801c60000e140c81481e2034085a90043d680c0c419050000544091b2002c0b405064170b064240320045d00c1190520103a040e0142d112061200007800078015140141d219450110f420f11803915a280c5c440101d8100c1c401c071480e00c400c200300c650400a250b11840e03c1c106140b541d2902d0f115420707410040160015410150702a07a40c4207000c90303c4c4010b1040f10307800c0003550b1f0300054180c17080303d521501d4800e0b10004460040342400502e4400541421062140100d49019944101c0030049c2c1e0002902511401800300400c0002c1088c21040f1120340f108008041c07135441c1a0342c0360b60003295000b540310543d6002c400002240e850402c01c903228180306100d00d0382c0381c1c5042e0454502803e000c4942043c035000210304030500d5a014000c200e400500070314000c6205051580c04084104010402458039464076452030124200d0150155112240000b4076a03030b450380b00000e423914 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 213359352 1250 213358102 213358111
    0xd0806060c07060e2b0b060d0308040228151209050a0308040501020f28020f0606010c060b0d1b0b03040803010e04080c0f0c0f0909061b040914010608 66
    0x1600200301809000c40c010501e44107942d02d608260102c5021440403505c0d4522034900c0d50016a506030780da00c116240300251468261050203001c40b1503507120140881014081c1c00103002c24440c20100340186008030f0044510b207258010a0440b8024000f10300c0165403075804540c90400c00c070040074001703911111040d0100d082d4841032200010550300d60390b0ba42c010319400341c00c12a03400041030404c1300070b40488221000501c00d81da1a40d034845560840e50310803041000c206c00c010340109000a0011510240d680b1582026000b0713555103900660b582020800300f100c45540d9170490260035a510b00c240f4070070502401d0720070501b403e07515415001c86100c0e0842074840100340708010010390041c04482c10340c3c0810f0110506502ea52400e0740c102c1c0201d803000c400c03902910f0790741107800d00001101c51140c802114400201c552000c14000948c03005d0301c10003440d0f000f61000072050803200079802022910307142c58600d040d50342c0060750101c54003a120360211500c6400108105075000d0b0700039400 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 213360602 1250 213359352 213359359
    0xc010f1b0e060c03030a0504020109030c030c050a08160501030f091e02030f0613031b08030f0f01090204060e040207032a03080c0901120f0f09050a02040c2c0a0b04080d0806 76
    0x20583c01180706540e9000060000408580b1080050210792080841304000d5a0001042181300c2d203d260004a54001d40034035801928051000200c00c0e00001d0404001c210000611001e14140300044020b402e20040c65252143c0740c1666400240041c2d900e250304508100203006010282e204040c1008500440c04409522900911403c407010515550249500d0f08200900601880c84001564079140000d0f20048000c4104118904032900b40c3d0321405001120131100e03a03e41c0104000c03809240122030008119800012886c2403540c0140403560103400c0070540000c7c0076256811000f0050302150350ba55070502200d0400d40c0158405800c020400d120074181005040001c107c1c0610300c3c2d440720020f1b01c414001c0f48003400342e4481003074200c40000c01e03c40d0350310508115503180d0003807104034060351500c140810715501c40c00c40c1400c0c042c10700c403058100c0131710402c810140020f000c020340c1c1d011007028400500044684020802081440c1c060304d054034000030060300f80c60000302031130701 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 213361852 1250 213360602 213360607
    0x1824060206070810030606060804230309040b0f1c060c020c01140a1205090a0c05030601050108040f0303020408010510090b09100605130510090e0106030b0603010303050c010f1b0e06 80
    0x4140e40116600703a101c61545000c0075541d0b030b6510001c041c2200c551000e00000d10748000800c1041d0301c64070302c40c800e50107038a10004035540c12103804001d44c199440d207a2560020f011800c507920309600000c2076198010000b4644080160000300c0f903101c041c0516040d1401d503401c19003004028020710000280d81c0c005006924000340c00039191994610700300a20b64400a200310489010f560041d030030303501001d0308200c40d1800840c240d9136554400001e8601070070ac828001010315001a003241030320300c103944540d141c1d01e46a480581034210101c003181170540030321021074a00780900c0750a2041814016044181e4a819070000c101c6110282d0b4a0280182000300646810340103201400c4503070510f480d0f56103c441e445504a002c1d000d03049550711200c0190b401500b660300001441c207841d440c0100220503661030f50700754100d5141003400354110005100400210b40100c002c0e01d914055800080f48030b07552701c4040e004441042c540894506101d40c03246082c10303448030049182031002e031081d92 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 213363102 1250 213361852 213361859
    0x1f0b120a110103020a200705010212032403070b0307120b0d32030301030b010f050102030a0e01030f180507060818071202030a020907090e1005100f05041824 69
    0x5420314402101c41d414190001214501584106071004443c00c2020000546603410f00d0201c0e01d581c49403040e280188181c80303041b2004a41a4126800b40c403c3c4000f4004507003040f03c0d1003040812804a065240c0142c1c0c000041080380300005502c102030b0f517541c4d514000b14040044d401c544050b24824040c400b603490744400190109000c1c0c65214800c160b040142d400c981403004011688291a03086000102c0000100454044240d050383d201c592019102e0707464400490740c0340100d041c40c80002d0f8500101c48103d500a40c028041d034903400c02d000c41d4026044001d0042e5003c80c10044580d54082078017003200c01c1c0c0c13161b585a00280e400c01280f03e4940000f01e95941d0740a6030280051152413003841008559081200a00190340901140082c1c80c0805000d06003a5040c480d91302305c090b0030400554883c2081505906681d030045c030388800021002e200311000c2c0c0d0b0036008030701800801c20020480c0c0d41d68602c131001c140309203203000c40c01d60b2055440340c840c03c800780040c40b10500484c0091 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 213364352 1250 213363102 213363113
    0xe07031803020a110f061803061f0308280f0210020310181d060114010203091f0c06061415040e0c3004050610080606010c03021f0b120a 60
    0x3542c3c40707811508000c8007507540c40005801c42c1c461030302030340e022000140741c03103090fa0b51100c1c0c3c0d404844220241c4505603030b60300340d002200d05a008007907103000d0010307002e01c0050084009044103949a11465002c6050200002c41c0041501f8440012907610b505c1d1103081607040002c1103103000100e900b5402c5040003c042d281000c51802407100d0180665401050001f459100004519802c40c4125405080b103913416150300080c02500940c003480340032000c40354000000c449500c000605004c00f0104c4101c1805402901009032400300840350b10700c900401c0b601d01511000d841024940f150800854042010641601c0349450341828140001c000750445030745500c0c0d00100342e0a13a165101880c450a41c000c0b041604520b8100d10040201500500c01c0c2c0c584500c9584200126205074036911520001001c1c2d44c41421056400a03000450715489030007008011072103801100c0a40b1400d541c2600142541c1c01c4215085a581070340c0c1c2002e103009401861507a031284058200303104d803510348 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 213365602 1250 213364352 213364363
    0x7060908031f05210109020a0f05100206090a08071b0602030c010b031f051314030912011404020f01140c0312070c03050406030908070f0f0203120a0903020d0303060803040e0703180302 81
    0x1100442d01c111341d0a503418010030740100780d80701e41c001e005828007500c40303007094000205801100d0080b556040600031441c00041c800b0300403008940200344507100c07131f036540005600c0b060003143d160035481c4c0301c02e840b14103651000c0d01401554001d1500c030380d0075a04060858940b031000900c0399121051100c0400c40b034054088012508071004585607680c5540d00120040340d840003468a812012840d80082010020305181d05e011603c00641c8030344c80c24254242c0d84001141c03c2c0c201c1a040114006107802054081140c40604000100aa5480c121540303500101c4e2a000d654000080c003802994220303454030f602c0450340c1444200d11030a034400400b580994081c0000349030307450811030709010003481500e4009920003d20b9131101c0340340c68203035040354031404101d001e0320030300b030020340ba00c03081b0700503511406000d42d80c25030860318507000c1043d440b072940d00c1030313060560781c0101141100040c8000e002603c484085020107060102004040b41c50000409400700d9401d00b1010001c0da01091 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 213366852 1250 213365602 213365629
    0x708090d090b0706230405010207050705060304350a03060f1d0f0a110403050c0102211602060c03120702070f0b0d050403030f1a01030612031407050307060908031f05 73
    0x200001c100701c0c50f1242c0415060204503000318081017008002c100300e0305400406005101d0380640d94015690710500ca12404103803801044054030502940030718001030034006801d01e0042d005881c0009011000c0c07041e500000c901c00020303455031000e005a580200c1110003c0000c90b0012000075480b440d4001d1141014003842042c017110000b2031400c2400350000588c04480301000340e950350f581c1c07400a5036950814095809401182c066008410345d44030354241242420090f5031074003040300d1890001200780f03d004c13640b140c0e05202040440c103041024111010740c1020321086400c01d071402030f107450f8203a0301180c42010701d0041408150718050030b4586600009401061584507490241c0c00f4002000007001e10510340300d40e2568038107075130400880d0720310280c03010010f440c0c8900142c060785600742e9010700480d03e0403100c448422024001040c20714011010749061614a660724004e41d040e0000644110202200784498051007400b10f10301c400c200315210228074034140c0403400c41c103410103 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 213368102 1250 213366852 213366863
    0xe120114130c120816050a0b0106120509070b0a050705160902030420031b060c0a03090501030c02150c0a0c0803010e04020f010309030e010e0d0c23010801120f0c0506030708090d090b07 81
    0xb05c40d0300c05c000c0c0400036116500e511542c8030010f580c5070040108920083c1d0006c54229040802040f08560042164016100c640004c240750078400300c07082c1c0e1142d002c0c500c2100d817407055002600d5040010f480100203003030010b00269580c00c050502c8444050351090319243c403a900018000647d40000346242b04140340c100100f50341d00840c00140e114000c070b040701e040c180650b4440c00101907000300d4400613510240c07000c010035004c041c0101c0c1d8034071a00c502402101014000b059940b440c0c60090700304c140152a08409050840e5100b9815400c2039019070215503904040c00210304d020041c4452a9400b032a04000320103050720010900c580c060042d0341408160080c1c0c003c0c076210ba00c200e0720b11b650411140182c1c5c40c1d840001c03d50080003212204000e0307100120a031169031060010034101c400009d900502019580c0380c074041e08446450032201d034844003c000900340c86403406035118400c02c0e261000245855480309086c0103c080450080020110050121140c10b600784c81a054104 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 213369352 1250 213368102 213368137
    0x12020f0a0c081203010e060f060c030a030c090f060c080f0c0d0203030114180402090415180b0a050f0f09011d030d05011403030d020c0102040305120301081605010e120114130c1208 79
    0x16009c12083e22030b501c000800381c0000954600f506030140c100401c02d543d19550032040c151f0b91082070842c03d045005505c00140180690307000700d119000a0401044130b00400352500a0b074a0600c1e10b001084500c0c5e0015810210042048201644010b14118010354400c01040107201a96090b0070000707000902c01c0c80300d82c02040901004c0c030701403038081c51040d001b04000740c080601049070004906081f52800748000000b411860b5030b0240c40e0151400503101082500c41c0c0c0390361011098000c040001c103660300e907000c400100304030100306143d1903110081c69507004414118811b07907005810101411703582501c07508241e2000800c462420301c1e004401619140c944440d24064402c541c401b50a51180b503000c03030590844a00258100c484c407100311960000400711804e518181e134414107002c1041c2030442c0340359003000140171404420210000510071010b1412002802c81a9041d81c15074051126400410a0510071030001e44004030a10304151025542d0901030b10940700016500d140c2c1 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 213370602 1250 213369352 213369379
    0xf090302041a0a0803070b0c070b0112050c0306070801060315050604090207060609020d0e0d03180b0601031506031b030509030301030f0f08041e0504090f12020f0a0c081203010e06 79
    0x40044102c249a070080c441a40345075a01c84140c0d50341c21031201960504000d501140e0307244003140c01c0f00c201580c049079007440d5070f29150400da0035881b171840c01d48180c010261456066070341881618401c07040c0b515620415410310310014201e0703500202c40304c80d4920540080c1f019035240c5041e034040710706c080c1025a5801c0d181c40c1880c090407980e481402e1341800400c420055032416044501603003503400c111142454110006c070191a070581c01a07000e0030b429000c54011035020701a81e54008018100401d045440000c0214561010f520106c00203983d00404c0340d007031b54054034000380c0200c03a140c14001800d007846410b840744010b10004140a040501140c00c0050307820303400300f045400084440d141c0e031b640d02c1d54084107480000d000241195a140115407132410744100c06040b500240808080c0500d50740d80d00398040b1042c061415440fa910016104030f404200d5812802d210f42800c80641d0b00d03040501e071601c1099104100384000500051101d403203c6942d0a40c000c0c2c00300c5600a08409 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 213371852 1250 213370602 213370631
    0x14060723130902070b0f040b0606070201030e0a1109010b07080912120f031f06080f04030e1507050f060705030a0903120c0c020306010905011202040f0b121c0f09030204 74
    0x24079414185404150080050302c458140e001d40f00b441c0c09612051016a2890034000c0c004808640007004c2c450500e001c00e229082400c0034110192040c10000b4203520140147c070f02d403c207030510854101110034010501030070140d090900501100d043c103820038a0544d00c18595000354099140111440350120401ca0410011800070b019421503803507030b42c84070481d4001c2e03945c4100d85150300d81c0401801280342c0b000c96180f46085591710f542d40c0b000d640340c5030001101c9900161081c1d08000d0115000c056981d54102140c0d101c05c0c1c4c0f52906581d40b2000e20381030703007003840d81051130701c007a0040e80c2004152a000400c4990140c40075800150b10b0701c0da4a4103642c411940d1a440c4001403915402019441d000030480d402d1714000c808a992681c1e940f0004419607900340214000704c541d007019040141000e030444442062968804911000d5039004101c405050090310009984003148403192980782d50751a01d17224581d4605001c061000d0080a0b01c1e4059501c40280030340d0f600c010f1401040d6 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 213373102 1250 213371852 213371857
    0x1030b0a0f0303020607020d0f0c021c02040c0504050f0904120c03050d150602010e010905030405041a03012c01050106080f0405010209150a0201320c2514060723 71
    0x14540301d001c10a42e0b02c9060003562444211100070240c40b54010b00d0100c03d00410040141d805103658a05000b00c0907420b01112600f24034002021020030360844c00141c0e26801200703030307240d480e584003a140d602d000104481040c442d41558081d10351030b0140030120b00e802c504181c05c80d50604000f410726441e850104c41c2c510402551982c190328211a071a052a0f19400c400d089480c1d5500900403041442007140c2201c0c4903c000900ca0743c0200000c21007414927401c12440c0c203020010a2801900e10f5010038207640c40098500c0e240241d051040f80015007800e000302400702800001c00c520f60400002800d8018050040702d601b0070740800080400000750101d4541b43c901501100580084030410304031031b00520003040140d400d182d1540804106600442e0000701120245030b00140c048800c0300c0404400360040c41c03801410030141c0e901d101120010100d0f010b0b026103900200d80c0e5400c0c455048110b4414000c10b070340141040c0312400b90300c00c41c40d040301c660503803410442c94990404407a00b803 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 213374352 1250 213373102 213373109
    0xc03050705060901060e09010e2d0304080a0308010f0b030604362609130603052a09060d03110127050c010e100807020312181b01090501030b0a 63
    0xa2180b0410060014410740050b4120750fa070b420079071515219a45014260350440550080c45d6200410304130a20702c020400440503900700f108511460b0300f041c0502d05680c0b00d90000c3d49075502051040e400c040e4480c0525004141140b080d01c08141010350b80c801030312000c0e0603903202c0d81c1c480001000c4000b20702c0d98110500700d403a0881d4807500c0c003005280002220100240d412241181400310800d4015624030341d40f03400700000501d813022403010031012202c861902090b682d0340700004130024804003c01f6400c100164034645180c5920031a4203a00e00d034400c10f0700d0081c18800188117040c1c85c0c1380505400c00e641420a01b24174102190720600624640302003c56000d1550284441e26401c04400901240980285c40b80c4c0c0300740c0e8006507100700c803c0d100580c000342e04510f001400d0780301b0030740150040303c14410740c2d140104166100341c00b5103041c1e8510081c080b80f050003080040042000d80c2d12805195045070300c0403084400030b46515564410b2038141621004c0c407100941d2000f880d00b025 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 213375602 1250 213374352 213374363
    0x5010c0b0a0c2006040b160207050108040501110412060c05041805061906051201080604020604030b10080703032d080c0f04080109030c0201020d1701170c040608060615040b0702010c030507 83
    0x30f004012a0842d61050151020fa518134450340104403050703404958040c0e40707805900100000e921300001110704200082054849540c2d444140301a0b913102e03001000200701048100c140a422420f011085490071460002440003c000810004607842450039801e01010b400146940e280000304410410503103204c0c0c03030f0240b000301c0881c0c0c8541000c042c0081103102074060181b070b80c03500856591284140d50207503000c00180002c0001500e512031081e4000c110018201600d951030a21038500003040c0c0045000c02c0c6c2845030b0905030603002d11001c1082495120f40144480958400303442c048001e03120440c1d20000085000d000d03140c400454005141542c020030031140f003424010413804081c00d04900600442011071116445040c0a09050a92800140e00f9910706050040d11000f8648000803d00600c2c0c0e90030b2280d43c0b00e101c0c640043c03460401802413031600030100801840300301141c088213481440148070349000c0909941180741e083c20034164a84040c107054403180030b0800020507 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 213376852 1250 213375602 213375647
    0x2010e010c0503100f0302030703020907050409050907030201140306090103120318060209270604090f0203030a080a18051005040f150c02060a0e06060f0a0510020102120105010c0b0a0c 81
    0x4000d42c2c0100190300ca040c0900f070800c042900d8a00041103420f4911000c0d50550100209001501d0610041504041d550504030302c1c0682d0b841c00c81e01924012520034200c1e40110b82d00300190350308070320358111441400d903826240d072400b42c00084500806000160080c9060354202d80740c039001e5403180e04040e44010740d0300316071591460100301940c058518036016100281c900701503119011005840302c0642c18210390189d88043c1484000c0004090030b07036407112110388050150700c06000418423100300c0e64400c0304a283c44103861081d500d102c190030007e00306080c2104049000072800555008101c1c45c0424261190b080002104041d44030203007040d0000c25103040b1030300f01a40410f800e807949800740c845a40d42c0780c44d02d00480d40000c074098015080500081d520b442d00482104000c04c0042c07000010711b40320030104036a59120081c02000d40c2d4001400101c184030108080e00419023480e00c1301c4070070255602c100f50740700094006402c031902e504002002601403212090308101c0e01c1800c00 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 213378102 1250 213376852 213376871
    0x8041e170427050115081b0705030702091008030403150605030102030106020304030605070207050109050f040f020c010605031509033c040e0f061f050c06070f09091e050702010e01 79
    0x2580801d6120b418204400041002d1501c140c0d000e40380c12201258251600c14808244c15241d05d0750050100e11004202c840c0b410841032804c003d4451140540b004507141d1116205001090b10040c3c540c500c031314582101001420400000c840c20780b540801000c40038001105c0942c0a41116002560716500100011458950000150040741d0040c0010b0006803102881030740c4030141402880c1c0000c1c5d104100b070140e41050310071140c4426019000041013603442144c103040ba004aa1a105280d4450008002c02e10301004020041c45190055103c41e082c80031210f036580c0f180c0d205000400140000483c07480008101c40301f8409096003600d01d2402004030a65019449400340030b4500080d1400700c0c0203104400320f00b80c801d20001d4002c02101e075035100c2c900d585030b94050805040010422000306070080600105004410b43c0d1943e15242400d40070141c103541c450741002010300e1030030610a840410201c41410084412240020079843e0400124050079250f0759642d80c2d0341c240210740 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 213379352 1250 213378102 213378119
    0x6060504060e0f070504081c02030705010f0509210d0506150403030918091104050604090f1101170403080103030e130504120f02190204111213050d08041e1704 70
    0x8510685002030300c0c3c0840c0e9a4a075081e11603010f14001e14040b544020100170a05102c0c00718030603c2003031401220b04000840d51801e09660070642c10008054881040c001d01600400000107100680c01c804c80b49a07084040d044080cbc0184104a02d890391a940450015114a032104e209022603058146c0c0e51074482c00c018101c010700d4450760408500c501f580306541d450318070410046580c4441441025070f031340c0c0200b00280ca80070340490303402942c4d007031a07400140c001c04150f55840e10404c2e184401d50aa000003401030928280c5c40300394110890200300020368400f5200c0d043d80c0d403609003140d2218400c40843c007241030809080d02d840389400c0900c4144103a03904511301e1a040c540c2c44102454989074200e848920140b00456040b1030302c5010801440e098200e00251070400310ba81c1d00f400c15200410080d40e6040c0c2c0c06d2411810070902c00d4092110501c14416804501d003003610f880d0400d0b580e0341404814140d80044840601c490200400546401418000c0c41600c206900c581e102c0c00a07 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 213380602 1250 213379352 213379379
    0xc150c020306060409020d1209232b08032203030906110a1715030102190216051e040b1e030f121e090d06050618060a09090606050406 59
    0x1a4420b109050014440b8982801402e46043c3e003c0c4c011481c490103940c030482d113003603c00035040030f100c41c041c1d0200f01c01140704c0b0854040c4d840e4185402e40406444180444601c82c1c0751100300411080704a484000700002200b507000d0ba00500e8699650b84088942c081e1810700072025401d040603400341d606140e8943c004034105402910b040003843c1160284008030b1042c00e1039030000c030b80d8846000d40b20b500e039000310b140c4c4444c26420300002d031f450403400039003282e118000c0c0b80002c00580103d03441540d410001c580c50301880ea804003010b181404006800c440c040440124000ca00140c03800c800e499642005003074440182108101da051500d010800c0082941841c4c044d01c1000341455050800082c090001e0080340c40300d600c0c10f0580100103c8810305100c1c0100c1044040000001c10b4a9400c00501d42d54040c40001410703007009030800c0511211030164043d2100340300c0a104041c1d0b20b0b10610804caa024041c0051010441d19100010704038941c0190b50040c40c041000440041001c078 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 213381852 1250 213380602 213380627
    0x31b0c060e06011a070501060506040e041505240103020702090a0522080711010504170114180d0f09050310020706240b0319020a03060f060314040f0c15 67
    0xc080c40616142a0803564a2109108410740e0407080f070903c04141120400074002e460213903002094103034990012503a503a00587c45528180804800c00003804502c015100c0d9441c1135034414401810269410749039140556032144100030401001042680079504980a0a40c00f0301110f00074680f85103040002c0c5012100d501da03c107000c00400740201c03140901c00307800729404a503642c2082480d84512001c40310680720a4184041004041040d0180f0306691f6014140340001084804040b4a020300c6000040d2500d104103e1024804001c1500800d842c1d14410340c80ca0628031f082c80400c0c08031904d140c503512070350f01801050703152084002250020a40355001c1c0c0010311009400c444809949403842c01e54291030f1100900070b00036504207000031a00000d054a10f64010b0b4031082031041264001c030301100109503181c50421902d114442400000d04590a0422480d40707003500305034014500403c014030072002c1071001d108000504510780c000d40140c00038850345001351407016100c0c10140301d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 213383102 1250 213381852 213381863
    0x1101092006040605040b1303021801150903030518061c0605030c0d050303071b02120606150a02030d1805060415060803041409090a0605091e0c031c031b0c 68
    0x103410485410808215011a40f00d40d03621480d1a00e801000e203025000a10380520a101600e0008096a180b1070600583e55a00703400000c0d40d450101c402011170134801400050080581003000482e030042e007502e1004202000b0141c0c1070b140940080c0b03c41c4a010344008110f2407a00301150b00e41303059846441510030903004c403411122081d0401c15252012040102540e1040000544c0b00d84102610680207440302840214810103030300161500544a203001031741e5104d2010000d00b0701d02012800800b00b12200001c2c0742001c0440005d40b01d00c20005400e5003149c40311044d15511b200c0a40c40c50f54590083e05843c52070601c3d181c813070010449049030f1100c05052900105011501000300c8040725a8a01001d142000e640d0a1016030300c0000c00ba541e440c011184100d010034181d000d46c0d4400c10155001c0c100d03050611a81c01103142028100041d07580c8904049040ca407400603072100c0346d101460415440e6003001e9412800307008140710b00d60603128218005c94a42c1d41084144801500c1503 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 213384352 1250 213383102 213383153
    0xc0d020d06150816080313120602040509010312020613080d090c0306060303091712040302010e010e210d0804020307060e060705160518190b191203030b030706050a030c110109 77
    0x2070700080da6034000c0031026110700c511490204800020801c3c00c23184107100c2d99002d400c06941c0c000103051103400f684240c40424454066400700c5030305104981e0700001e0312071120086e83c1e060711500035a015480d111014103075546804ea0a2100044401c4021030780040c080c0700c003d40b00c0c41d0007030050b00c041c442c05510007074100c05030106c0103000c44c2038810740001d4415203040601d5900112044160211510b050200d569446e00382510780450710745000256046403010404007062562078030000000c24020803544c002804016034010840c030303040300e101c2e141c0403005d03407200c000040d84be1281b03000007081403094160050301e50059004036011947e0071aa000c072521104410401112400c40c0c0e405030404a0401c808180d070460f911441c4103810203010180020194850480c0c60040d580122008220f0b05221408169150040956112043d4003070a0468641040540340c0d01a103aa40c1042c547c542c411183c18610690b0049415072616000b84608881803c000d202c10107041d01000198441 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 213385602 1250 213384352 213384359
    0xe030105090312010b030702120912010e1c0903080d050925030506060907020303070f0302160807060b03031c020d0f111314031f0204091d0601080c0d020d06150816 72
    0xc5c034040e03e10809698001c1c0c24502c80d0400c40c404141c0c800300c600e903848108a543c1d84d1032b1780024418140c450944000130480c0c2c190a0006003190b68a10300300208020440b8410304c0040c04000681d03a4000c1c05280118964596402c00b6003060f5242158840c2d5100f018003400640315015150801c0700d0240e42a58000c2e1101010301000c1726003103c0c140d0260b8001c00100e4245441a0282041c0845900e0018108007080100080007100c03a40c0c03d880c1c030302005c2100c5003445000c2c460307402d604404500075490b01407070001e0f420240b40001d5034021030a5000c90803034010445500b0400840703e84007420089a04060300c80740c5180c20045039038030742403c0b094020405490b641641c295189c0010f0051400e055040d0003801d112031001c00c1d850085809100006402449015600e025140c40d04059030f0f1007001c42046281c010146c0c46483c1941c0030529248190b2560f0380c02103001d40d01958044468061410040d0250401c054104e01000a4030f070006801030b00407842e01504211781c0d40c02d04a1555 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 213386852 1250 213385602 213385619
    0xb0411010318020906030a02030601080705040e03070f02090406020f0a0507060c030605010206010b0c011e02070213050c03060913200307090605090708041b03080405010f0507110f010e03010509031201 88
    0x4481e030000d2440b90300c0c1481c0c0c405450504000c940c4184003c04440c10b0410303940c00b01c0d042035000e9004190680c0200341c00e0055207098000c80750300140700c00c000d5041c0178031911020880042c07000301901071491320f00458140012501141e80039800505800c1d81c5401070030b802409580300140a40d14585071400450007030f84680a18070031110160f008000d00c0e42804c00369981d82d403200010f04000d660322a541d002c4104c80c00c04040000700c0c20302d001a00d801840c01405011140d103000079580b680b03400200004441200103681c1c002600b82c5009410790341e82e10104100d03210340d41c4050080740100c000810180314900c81019491000d40980301c0441e91560703a50181d5142d40111544503040100048442d84a0714400d0707800b500030f2010f14900680c1039140d01c04529a500705440303035000010103010658020980c1442420315250051809050340c5904c2004001d80960611804400b2900d851580c414885010f01c640010000c1089042894095950303901840141d81e41b0311451000042c03088 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 213388102 1250 213386852 213386861
    0x40203100b0c0a020a1401091a190905030a050703030e030c0604030b040305120117010c1b1202120f0304020a0503070e0c0703170109050f0f011a0705070902070b04110103 75
    0x80c440030000980c18030120040e240c00802404034180300d43d406080c09691648080801854264881c02c074075240003000401074040d940008242c040300d800310350700c203080ca0022156a01c0c41081001231690a1102c204c400d11425072059030705200e1140d00b54148440820000d044a00c244c690b448440a0107041c9070b03d0703000f107490080d40242d0500081000c04d1038800140c0e0300ca8440e240140c44d10201030010303080e0300303003e030445c01c0300700300e101800c4a01510034030078480102c040f81010310007150340c62002060307070f6940340c801040d017041c03030780c040b01da003402001303144141c541030840d403615030304001c0600b400c83c1c008480c103901c5405c181c3c5001400342800300b486003d4404002c91541260344000c1c42514960002c041203003088010490802181c111203d01e501802c0103490101e81411712003200408244041e00304002d0a15120041084000f9000e100249030850100180c55005138100681452503e50010030503600005403a003c000107100e1981c4114400d2081d60000e40d14a00110b0444 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 213389352 1250 213388102 213388111
    0x914090d09030308130b07050a031103060901050613240201060e010605030f100503030307050a080a0506011e0908010504050d0822140a05010e030408070501170f06010507060212010311040203 84
    0x30701c0d00002840480d00c100000c3d81c1c0120340701d0500720844041c1d1ba6a04c281141201c600c00020360201e400356400f40d0600070700e01003101030003d807411400d0a00c0040c40055040c801d00e44034a0000801480c070f000462000001000032404100c0b844484080790010748074409003180040d46025800b01d00680440c40d0384e410f0315070350398901e0700395650115a948000c101500841c2060454000016166420401140b00b03046603581e0540380c01d03005402070701d001d07000742c038601d5480d0070081003204a0340d20450350811004202c1e882d4425031a155810390380b0707203440c1e00f00c0c4030030754200350030031040c4100001c0b00500f4821540d211091a42c502e8141c882c8180c1868804100d80402451030300415036842d080c004900840b030503a113603031603a42e0315a030031500202001e0040c1e0300081000c10000d0800d00a21005000c00c1c20720380c0c0c140c003490441e85800c03a4004d0881220546000110700164416015140d885500010856407501d07110b00c44050380500340300c1120241e10400300992141414000c2c0d034000c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 213390602 1250 213389352 213389357
    0x1e091b041a011b05010204030c05090a09110603070e0306010803030105031e0303040314040b0d09050f0d050304140111041d070f0e10030f091a011707090e03070c0914090d 75
    0x1040704070401190741880511034040c0b00640f01003008045007003031004100451103411042003092501d02070110000d001404402c0251801c0700600106881030391400c0c8020048407000d030b9079910740c54142c548501045129070544a00800172502100c0000107505944c1c08800700c8220190034000402c04a1421044c8000c0e034200f8808100000e00482d440f0881456420416041ca900e0f650303900b00303d40143c1c4402c03000d5515406140240003080c05603810011190000d00700b5222503100180091001810003050034910400d41d5088100c2036000700800841e100102e50786598580000c00010601c2c81c05000241520000c200c0d500d010b01f00680c02015141c44005540380344008000c84040983e03202024140c840c1e80c2e03581d90040512900080d28450030144820085002c0d0190035102c050b00048400038580c4404904d00500045003421901880c40104452001111040c11402580c6008207080c1c80841d000c20b000744690000110464641c801d08a0f5940b608809a035442c03011040402 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 213391852 1250 213390602 213390641
    0x130201050408121c0e07030f051e0102030a1d120d020d020703050a170f0106080a06080303010906060e061206060310030609140613080d0c09211b031a1e091b04 70
    0x1040c0042c0000c0c411300032270a41f4030103c2c0c00e1955083c038582c0000c003a001c9940c00020401524003074405c0040118044454082d1460340508a41c5c0e0341424003030170712048101241224800046404940d00b800c0183c03029502c0f0b112034540039100f0342240100d240419091000210301e4188800d400744103005444218006d6481c20750b003a209654040c0507194260b449660102d02e07900300300300542c02411903400005031940380440c0144001801d0304c00350311801c3c080140d54000707202404500c0c0c04c001c08550302952071311000c40d44000e111007603000404103418482080305014915021000100504003a02c0b125038a110485c00d10344450480108210818400f8180111440d030290140052504220340c03200e450311481582603545101940c0748054145000c07040090706507220500c203901690402655081d0354641e003200c060a008580c07000202d00000d5121440c449014000d80d00204000740c0500340b802000e91100780554000c141c0318070001480341c07a1304152041c86e03c011101a003025 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 213393102 1250 213391852 213391859
    0x180b09010816120e031905032509080a0308040b060d05280c0305032203030912030306031b0e07110c0411040e191a0306130201050408121c0e07 63
    0x121002000341d82001000380420150807440b0f000d00c94000c164455900568407400d24260100c0440d03070050024041180074024040c0c0304081c0d04140410071007804201c03205a40e413030401c45550f0001d078440811807040703a00b2001030682060410b40207501500c5845a90340e03a003424403040201c0340e0030081050b8440042212042180c0d40100e281d8100c1a83e1495599580d4541c2c41c90001290020340707260f0000650f0030040c1b4060104c00700104a08009404140d2550301e028005044910070700b12161080c0c07203010704041c481c0d4050000b07190f02c41c0092a8403c0c0300541e0040252242c003d0104c2c00621a02246840b805000104101d180200c01006000c0d5410188805018032a040358082c0000707110104045403007021940c401c035258460081c599050421702e0003a1201d0041030500c0f00c5420000000780d13200410496401009801d8134181d068003440101c601d4070172607004028600400881c1c120200c4090300809050250303801c0700820725208000b101c00c5414445404881380c0c494581003 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 213394352 1250 213393102 213393121
    0x609140f0111010b0d1a06040501051f02070512030a030b0102060c220914070206071b0b1306060605070b0606090a17030c0607110d030501060503011a0f0a180b090108 73
    0x1114141d0ba00110b02003845001040780c840801c1c608651107801014902c0392596030200c103542c0800200c40900c041d51401001c1000e80c402c003414070509004224002001c14000c02c07004000300340280005040c4202e2190076501c0744c003d41d0741040081d0811100044c03e620000d1503500401c43d12000760b240030700900700c180d1128000c0040c0454809150310008000041d840303804143d4140401a40c11440c0602c002800e050000b0400700621604425101800d0307041d0600313502c0d035a03128100c0e502d00e07240c06004100808603500c004081909107480030a0707040e170010140404a110320401755180c0c80b4001001118040e0090103138011801071001c0041e40c0c110102070909170003640980307261213020849503007803910803106a0701003008040e40a41381482000940c1d900c0d1080d2400700029410141c00514503c818842c41801d403600300094400d14071550112115034074440004d5a5800301340d80007504240d8101c41c45409180c0c03072400003c0c4558454212154040169903c052580c0e030b0210380c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 213395602 1250 213394352 213394367
    0x2043b07022a09010905010e0903041202010305151306080c042a17090c0f0103020a080703240305010522030f0507060207020d031e03090f0212011e02040609140f01 72
    0x107120220300e0402c800d40301ca440300c6418034081c200c6482c0110781d9604000181c801c1d20360103000c401c06d0354010402000031241c00741d0f1141410b5424a00414a034507454100d0900440801060344c2c0000600416600b40d60306503c800200c403014415680340e014000e003004103d0700108004884100a1071440c500381156280540101205013132800800b00c0910100b00c285504880341c0f48164002044884a4039003c00c01c6082080240790540c50000c4035800100b0092018142905040d21080002c14944800061426500d01880005021550390819074042d0409072400c450b03000c030315400c00514820700301c9082c00282e0152150220800004021a9654040c1505a884540c01d110b48001640c0e15040201c2c1d503030090350307960000c5010100700a0805200b550b8102803500d00011480040c68401d9441442a0100c500320707040b403d9030151334054400014081100c844040d40c240c4c88000b6640900103640c0d640d51920f440740e840e10303d542e401c07282c014545a40401040d44051482d84030303181 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 213396852 1250 213395602 213395653
    0x712050f06040501020c16120b0a060812190531050a0303020d03050a1a060d0e01090c0618030305250204020a0e0411030112140102043b0702 62
    0x100c8100000103200d80d81411025942222581d4000811803441c000c00c002c0705074100c0741207404040051511142c0000e803003080c1c5004200e49410f02c001288482c0c16403140c401031076413409031015400303507088100d802e2b80170040d07074044014004075100702c1511860030b9075210b0401c2c598555400850a140d40215114a042038201703810328440452070383c40308a003020065102c1c1c1c000b020000070700c160207026288000c103900400d620382079880210b400355901c40d000001040e0341c255990a00040322901424820200d1011503003010380344420885100051411184c180e40e40d40d80b001585280d20460003040c0c8800380008030180207d07400d5407a0031400300350440e44044190600c01513640032400b030b600a0300405011441c04481d00f1000c1c142802448403001000091714519070420a1030b55041303001000103066008103542e41104954254111405000e0003a82c07620403014041c10708d840e02e4000c1000450500000c8440e1a1034034104881c5030240081d5000f400d894090500f04192800d001c40 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 213398102 1250 213396852 213396863
    0xf2a0c05070b0a0302030a0b1e040b0310060f0e01080109030e0f06090a0e10121203020901170a0614010e0901060e040207080408030304051c05090910150309020307050a080712 77
    0x481c006100035000000b042885010748003d40c032031030300e00c12000443c6c0ca5601e0b03240c00380d1184180d201d0680d81103140840781001c112000100c8902e1907011910f0000428043c0220520746000403410041d00c2584070112000c51a441d00360360f88800250b802e89180d040700901280403981543c04a1030312141c43c42c0c0c01d400c040e000038104045a000100400400d601100b9054407031030520503080c84600070303000540204003910003820b50703960752820351601c800a0380003003581c0072500d400c00b0f80c4a024102c51104c00801100b0103400c00f840c107200142079611541020030264500c00c40c5070b501030f0003400c680c0b0074000c10200702e603840d0840a460404042d020141d01541c20880d1100055018010f40f0103814200029512480c0518080d40341c18220768420003441c400302c003541042c941c40012158500c40c25206440607844a6003248410400ca810442080e4030741c03c0810802d650680c00620818000c41c125144260740d0402c1c07102e105018003030045142c01c912000d05c070010040601c44000352080 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 213399352 1250 213398102 213398113
    0x1512111203070c0f14010918020441061206040f0c110c06030c1b12030703021206090601051602030f071203080a050f010612060f06030f2a0c05 63
    0x11000386045501481d0308403401c1c584882c0a01c1050f5000004901804400f425580d4400265002a00020703080c0b2415802c00a80402d4180b0b051081e01600c0007400d840818440c10460903d0710078070782920415800c1030128401034040086a42d8404e1151000c0103428245031070360300000920005002045250496107170380c060034001c0315a05c101c0c44015080c0e07481c0c40c1820004410b0509010a152403140320705424000d00103045510003c03601b50000ea800070002c1c00601070282420640d02c404866020440441004a07098140e001050241c10120324002180e41e03210070401050741c00d85282e400140b05015401ca9038007900c80f8075a20304d0000b0105c4044403801c0b040b2600d003108542200820440d075140440416402c4a40150441c80d100c1e414440d80c50030600d59001400144118002c1000544000b10201100d40c0010058082131003915070b80c0e0380726030300900a424443c04001040d4a40911304008807041c0c600600c9102e2185500c003207030130340c400c0202c1b0020101c0c4001c3d91f1074001c0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 213400602 1250 213399352 213399379
    0xb0d05060109170c031903020304050d0f150f0f0c0f0c0201030609020d02041a0313080a0c0c060503090f0705060f090a09090b04030e040903020d050a0509030601080709151211 77
    0x2e182410083c00d1042c018401e14a40320b080c507003805100e110010340d81da040700c03540700003a070080103031000d840307003910842c05001c038a042a0310414040b4501a18003c80502800c5140c50300f0380140240100b1084180901003034a00c04000b00c0da4a0001940080c043e400d40507400c6d4410080f00140314014500441c2954445c9060340490b481401c0b05440d89500043c100300058491520303c40001e164074085095152040144070f4044004d031005090060010f040520940117152000203607401c040c100e10051384071080907242d64001d455941e140c2c454071820031070303044000840703e0946201070704030743c1060700e8420040c140750041c1626039803054081e1000318004d038191280d00fa40d140034101d6181581884e0501034900e44900d0040c0d40500d00740030211000c2500040c50306468079061608035600d8003803510844441c0140100d440e454040c00b00002800200050340201303035104114204440f103a03201d202a00e12065205d0f605164051780b00746004601008604903503a4400307441c1d4200b2041 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 213401852 1250 213400602 213400619
    0xd03050c0a170d05220b0402011205070801050307081b04050a020702060c15060603040809010c080c0a0b1006020304080601060c020a0e0c18030c031504020d02180a150b0d05060109 79
    0x1410045680800d802043d0984076107494054143c005c1051000728a1000903681080b443c0b006000000c1d21b0510030b04082421640b09a44001442c1c410000401903801c004900508421080c80380e40d100344121000400c8036500440c2051410785050304100740c0f00000700c140006804001d008001903582805a01d0158031040c0003013003440c0c500ba0107056102c4070440190f0380424090103003802075100b4010080003520000c00c503070161030700342407044d400382d45858070340c6240c80398840010b02805501100c10801c101152224051344042e1888101c0031340300d14040341c1d00e004030b110b8110742d84c0c4054010001c80c0c1c01030b450f41200500103403076040503036100c1c00b490003008810740b80301054040008510281c5541c80c004070840590850103000395502410000350340f94510003403a09164003803000700381195a442e100c0705c1c5899003c1c22020b400d4001044188454004a5401520b142003000c10300703a030794090b48044241c40000803001c0c1400d81328140c440c001c140082502e8144103030b0301d1010134980c1 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 213403102 1250 213401852 213401873
    0x2030a03020610060201061419090204140f04020a0c020d0503120124020105010b0d0b0301021e2a0a080c0c13061a040b03010306020c1f05010e13020d03050c0a 70
    0x140260002c10350790401040315108410980e02900c00c592419009004c64a0396042c5041c518101319042c1c03040c1505103030034600e80005a4001d00c1c45610019000804500d01c04171360841040440301102492414000d0200760300c6086401c00005004403a0080146000380908091500440407642400910340c21a4580070080c3c10421407000c50603100e9001001000c41c549000c0d40741d02c000e0003030b549840e8140427940201c038003030300c500f5460b007594160f941c03402d605403298140b20400300020058580c40750000c0b540314240c0d1400071030307180c803903400041040b1092402d10000c020052840e20b42c0c5072100c4586070040f007010f2509019962a20103d5a20003001103507025069100041844c90201e01b450b0385c01c900810803040c040c040c80b00b000a00b04031000c0d241101d800910160ba141400c20a85041c20320f000c0d8103802542d100718100300610616401681a5030703520102e411103488510107080b204050300c038025441404c001e400400284110042c2428004003c11a04180129aa01c64512 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 213404352 1250 213403102 213403123
    0x40305150106050703020d0e0d0503030f0f0609040b15060d050403174209011403010f0203090307150b030f010f0609050403020307060b0612090f010b030d0f030e0304030203 76
    0x1980200ca2060390001800c0d0150300400c25810100d16040c80d80d5000b940b6000d40b0311080080c003c0001444a00340c03210302550801d540d0250583e541e80c41c081c400380380100010786404041c0900100017840a041020300c190265400c150418080c2d9240c3c194100b01500112081c0c0c0c1001c420311400c860307a4024090180128826140d902c44900c007403014108440c00100b0081c0070307001c0003d10701180746203031542024003607810300f81c086202847c514500600d024a075038541c008403018000248070b207a01d4049500000200c000f8001400b08221110607808151041c0281f034208211200014078101640f080c9503081400101d40d03d4110350001e824041d82c0b24030107907542d454800ca09000442c038440c11028180d540020131107400d05440c02580c90081041c01040a5501e540c40f100680d26042500e1007183e0b11a40301d00b5a283c9810203540b109804401d000a560a0140c10003203458007140f103c1e03000f00540d0301c04240306058202180504058440000b840c01b0800000c03001d40c90900025018 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 213405602 1250 213404352 213404363
    0x1b02060918060907020d1d0315070f02010e0105060f060c150a0c02011401080706050a0216090e010f0c14090f060711090f0403142a060a0f021303020904080d020403 72
    0x4624154062103a01c00005100c3c4c02150406410a0354042e00040e00762406141003000420201380c42000c0392804440f084a501d6565817003080204881c0e100c1c8489541030601d9000380301c0c5030141402d442c00e0b6501a01c0069010780c1c1c6407641d146070300705600600311012070042281c02c10398406014203d624400e86a01240b940c076183c1441060780c09019603480303000441a6a2101d624281c28182c580d0340c0c42c0a0340003000000281603180a01c01c02c000e4138104400c60241007440d80e650f00001c000e02c16051046a694240446959090010301c1035912180568171580c2c80103c51410b6441e099001d070700c0700c1e64031a140a051740d071079864441c003504210703100306000d01c05159000304000c3c0c6180010194480420140d0821001907880070301248100e5940004076100c1807032000601d00e03030705c89020f000c0c08a1800101d08400c2e6400054050248001e010300300801d000e01040d01059115440f40301040034000c180800047c2841340700e0031362080c014000f880c2030101c584000c03000d81e07000340d0065a0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 213406852 1250 213405602 213405649
    0x20d15020a090e010509010e040507090e03190e10031121040b010807140d030e280603060b1617030c03070306140d06050603070906260d1b020609 64
    0x1885a00700710404090a50f12000b0a015894030300000c0007101d0501404001d01c03080d40c04907080000c00c202980280559001c244a1a195070302e80e955039400c07042c0382e807106400103001c4040d0b40340924640507a03140043c0841840180c0381006801510031030703c5d401c0e48040b00700704c01d60b0100001c4410303410043e208051f541c0303241040d0a00c0c41086006070051552038000c1030f000c01100114442c0c415022400780c5400c941b04205080a4170070000c20403505401c5444003820b03000c500f51303180b001010500001245205283c50f8101102211040e0146404141e0100485410800c020484040062107010021024103800000329100c0c1c205070f40c0600d0003000030051110445d00b500036080504a801e40c805040c01c808400280b1315000c6050181c14242d491010410350348060181d000a001010000d0083c180d442c540c01d000300988610601c1041014480d03e42e820750701080260a00d051503942c003c024a0380104c0451441060340104e901000801000301241ca130702018074800b11400300d4109 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 213408102 1250 213406852 213406867
    0x15081e0f070804210804051b01090e0606070b090a02040f0e03090114040801020a020a110d020d02040f0f1d010501170304060f0207030f0605063a030315170f0d12020304020d1502 78
    0x41c6041e0120413088c40290300316005500c0f82e640003003608100c07555104a001252145000705001384104c8a0282c454058201041404003000030b046504620130368040169160f100d000c1d80485076040581c0e0003a0300100402080c962084074514545040000b0641c90282d8422401d400c9a200c094030301c000d80c002010303402c18410f524500042204040d0b4000d41400000d40c00641b600b03010400007482155140341c4107203a54203a9209518180350f0180c2001210b884c80402504242c0340c1042065960800d000400c815640014150003a04d0717003002541071038201402501c21418800b001000c5100b4004000301041c056004040041e00510000400b41011004d10546040f2a80b242d50610342070303071908010b140001c07958042032024440b0318040c4400303803078110003074183c0d104400981c644c030200125135540140742ca1541c4c0c1000c1c2e41144d0b0310402900304d5680342d00c0c2e002c15000200d810881d641c13500140315001103600030300c01000b002c813019a41d550411000c191045019445a0104001 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 213409352 1250 213408102 213408113
    0xc03190905120606061c021c0608010608190210020a080d0207030e0301022a1002030405010c200703032f070f080109020d0807030915081e0f070804210804 68
    0xc40c10b50740840c0c00b6210b90718260000c20040d01c00c10300d40c03e02e180070b0440010321a0310140d05680e0750140b01e86001014a502156000c040d00702806025060352800b040002d0541001900d44408801524210054222502048403c1e000c0300d4000c820350040c40448400075241c0002010a11640c000068a403442810002d061580340c00040740241c0c4104a4681500d80b03e1090409018982600c0e0a05039a44a15141040c40711000c00540c5d50000c42403104000701074200640e00622540c5d8203140d1602c07104904618010640c004841c0d802284060012030300c0348100501e035070079403007000b00190b001c24070780300c00c1c9010706424444d04c0d0015001032080c010680c281500919141c0700a104043d0540c0008404405202d801013034200700080600405000740041c600900d00e1847c5d4822070104d070748000c2c1030000202d42c102e20305103050bc823000c8600820007041340180310317000d6040d4603a036400000392141c07407015105503072422010b202d03840b042401c0f9840c607013045a41d90729540b0600346803906 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 213410602 1250 213409352 213409369
    0x7020a1a0112061d0304060203041401030618050406021207020f0c01020f030d0e071d01060822030f030f0204080a030905100822020d0b010315060308040b0c03190905 73
    0x1402400d104004114512446803403182c5140c00c4840014070322148407805954010340001c401160001240c0041c2040c4c0100140045542081150030b542c200c103c0110100c503d240590580705140c0e550107400414550301c4a80c1c0540b01741c1c8010b10f4085915680e0200000c12514035005a029050700c00404c0d009021b60b01e410744003800180390010311111010b481340910000d0051450781c0f07148200d407140e0700300702520061007540140304009401e02482c034a00e01d0240a030b10041481c45000c180a480c4100d40c0300c401505400c2c0841a03410f05a500701c42c0c4c10254035000c01050744900a5022444540c4028001040154001c040b00c22051174041d281d070035551b011030b02c84c02d0301c03070f188000080c0c201c444164400480800d05410802c04003031400e04c20302992001c1c0d00032014070401010401c140812038140d034041d04200f40340c010712145c00002c0d200580401803a50001340b20810052050a02401e0364114a0080d00e091006560826402c40c0c2002a4a000640c00c4101004070382840e446 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 213411852 1250 213410602 213410633
    0x1e05060d023c210405031e09011b020612180f010908070204180c0b03060a05040c0f08280f240b030402061c0b1314040f02030a0b07020a 60
    0xc40031081d001041c0c40400b0640c000c014051504000505418119003a900c0300207000c0780325500c08514103043c20010759030b4009009180560403880a502d01c201da910043c2c894035041659410542c038500e400740c1c0307820082040c0403a0480d4051201c001e010703200442c454407a4011941411a00c1003c840705032030b010002061845c140d1401d00c2c0e400220f0480422901d000c1c0d01910045540740d0700203080300800c262400050581c0501f21004a081000c00e402180202e0040302c01c1c6500d0b503101d00800c0101d9011030840004903210307125070480c0500841c0210b80c09131111200844a255000f6000841c210000c03d80404d1781d51a099001c4490030351003915490400942501648801031030007041c0c82c0142e004508042501100081c110355611b4219208860703084c0100c550b51030141c00c0c410103001b400b0f1810b48113041c0701c00b40e105d04002900c2070303c80040959110303e00b1600c464442a07609140f04005980500403852030002003034020703480500540c403c0d80200100b1101c4d040060002d44500b0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 213413102 1250 213411852 213411907
    0x4290604030b04060213081b041d031b010b03030703030f1404050d0c2108040b0f070e12070b0c061806190c02011b09031406010509011e05060d02 64
    0x184042184018410340c0075078054001a50f406c2e403000403080c00d0060342c0c4074484504c0303110b807422040b094050f40ba520001064409000c0440c101400d40340c040d100d401d024480381d0091210450f42d00e111102c44081404510002540340d158034003007800c41d44070304010f8011035114030700c01c1a880034600c205901b0040000d007041c11810250345050306d60055420744020402031081c0b000030700c00001411540340302c00000d01031921803011809403916000700c8080c1c074109440750000b103c0f24200300f450b0344501c00d42d035102c244100c4e4000c1009269000c03420102c0041c40f90500100c4c1162400c40185030302c12092004001d01d1400a860b8410041400210011504501d041c010042c200c100425131840c0c4c05003000ca203d0348960f1003280184456413842c15003402007524000d100e03400140d100240c0c2d008079807038120080f001c0b0591b965450300f882015003011403400100081010419420700d0303a801100c0404210b640e0f100060000d4011b0110000869400541b40200e01c1654003401000d15100 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 213414352 1250 213413102 213413107
    0x304060f1418010c030201110301032312030a090309051011070807062102210604110c061605070501020324010e010f03110909130308070809060403031109042906 71
    0x1a020018404407800102d414001c102c140300041600079001070f540c03503140070000b584940c5d60303040840c0c01d0300100c102070b03403840403426400350400d00c01b15040340040003000e21a413540d06e440e5142402032810110680070484a0200031840b90707240000d10000301925034030300b61030b5101c000026080c15403076032160f58142d020110421444d0380000c00d20522029043c190320b040e4810a259001a1080340c1b00a621b44201c0c1d5000102015100c5045009007410741d0200200101544c10341d03140d2183c0741c292101c40c0d200c100060062078842c80208100d42a0f858100c0c00c15070b041c0d0380d07a42640c000791100c2a4240e903010030340303104120440e010396828000746000030b10020203100280c140001001d04034100b5031144040c4c0c8100e80c0c1001204c0140501405840252034a0f0102080704240e05004400042c2503d011902047c030031010b81c3d004101010181400c1d498070341e0158000d006514001d55601000e2101c2c52607030795944103220440008240a40b4480340340015014900c03041050705118000a = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 213415602 1250 213414352 213414367
    0x80114040c0312030e030a0903061503080f07021c1a0a0204030b07080c090a09051b07020a0b0307021501030807210c2004021c230601080411030304060f14 68
    0x34000360354102c9810010145100c1c002100450103001d062500c19514403002860341c14550740000302c0400c50340101d00400603600e4101c0081c950100621010f02592418000300c0079840c0c0100c000c1201d50310040803110000045051aa02141c1082d030649900c1c0b81182075103008040485030562002001c40118640b50031a0380f58080e60710090306030020425400001000441c902d02140c0c84264000c110100803592911020003801c41203a80000c1601211003003403206104009070307010150b00620b0a00c0881c01d251072110030ba003009010384114850071810482841e0856541d5002c2c50041d4809070b83e580050a060a076001c0c1c400c01030181c2c5580002409203141d00c4543c1d552026844445802c240741d1202d584005048080000c0c2c0d4460310000b004100b0311402034004542080382402402030020b040400d554071840000c0d0170502c3c12034100091465031040290f554458402d4414400340c0d104180400d03e150415086200854091401e401d42180c01c0440010b00031806d28405280142 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 213416852 1250 213415602 213415613
    0x130e0405010b010219030c0c08061006030b060708040315140c071103061018022109070b032406070f110a1221050d021603170601140f09061308011404 66
    0x4600f174042c0410640389000c0c01086010f41004c40140011011100380c0d05005081420784007041c803414010a243c900624040d04002040c1c1c0d18154001078902d00342461a00c0703500c2c20303111740100c04c042241e81714075029468000301000c034003400e400030080c2e44400c02d92501d00b1116010780c0c01c1512aa12400400c541d0010144650007911496104581c01450080580010340207410344000d10f840410502080601118106e5216138051b5089690056507659070388501d1005844030020b8144200310a540f15044859042c030b05900540101c0c0b80511940b02c055207009998400c4800305127071000d0984928203142100050302d60510b0741c001102c6603544580540d201c1d0710400190500307940ca00160507000b1030603941c028441d89810340d030b02d501c692560055003240301001c402003042c030807446172002c1c01005114403804060311804404008000d03003403865000b18450403c20700701085980d100b030722408040d2018110039410150041d0034501c2e40741c2583c005c2d0401d00b405405c2d881c10080481d2 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 213418102 1250 213416852 213416893
    0x6050f04121101022109190305090919050f060103110a090e0c0705060408031006030605030c19091802100806010c030302030402010e06030906070809160308090402130e0405010b0102 80
    0x300241080c03070300b084001899502a008803a43e400210510b00d080c82007440b00d45041902c5900040281d0b004a070501c6a140030450070550040c0c0080c80030b21a044860400c9413820750014030b0f00300140c800000e010301d0182941e20460ba1021031064100c14001903503094040e24000903958240e9601700710310100010a450418460122114203040101d12490180411580d10a030410282e4070b00f0301e0142002d507010307481640d20004280801100044c1c00e4070038070806042e500010094000f8021402c10800602d208608404003145c544000081040d068891001440e480051030410a0041d00400c08c00c1c880040c1c40e101403080700301c10403d4982e40311400458050b8181801a16501c49000407070343c0c199012031284d0000c00010510401070340000f18188070f05000c2d6145075269032081d100c203072120344664078101c070126103d0042c03001a1804003d015554000b5100500300040c1080c0c0259620181c1c0c0080350000720b601c10301051200a000d1016143c10a000408000100d00f08104146 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 213419352 1250 213418102 213418133
    0x91a01061112070213090c031103030403020114030403031e0e070911040501050c0304050310020318070302060a0c060f06030c080f070b030f071e020610210303020a0c0f0f06050f04 79
    0x2c41c0051008115601c01034000c400c052401d01c1008007030101d2601c5100c82ca41c0f80025038198904034031040303440c64004110740550b40d06075501d442800504a100c1800c0e00302400c11000d064031400d030303002a00d0494407001d111103c10701d408556030b0740c2d1003040c80c1020700340e8004100302810511551001c041032400c981c201d55080c40c02e55910220308900380d00754052900203640c50b009107010101c14000d40d80107180510a0440000c484031111000f9035078840107407100a401c5a014000325040b0f9000350a4824040e018aa000c00d640d00b1045051045582c01c0e04101c1d00035966110500001c1010004c060340c00d10b020000340f50403414610014402d00008290000450201000812642c8203092190318848103520f2110941c281d201d010351502300407100982c895100000000d00c0022842c0d519280c11030355009001c081d103c94600700d000c2d40c0808228424030602d2059680051f9012211118103401405910312000701c074580300741500d03000340800f140e002c260410b000201c2c0f040c1a0141c0f08 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 213420602 1250 213419352 213419383
    0x50604150f09031a070306050f0a0324091a01061b02040906020c060a0e0f01110706020703090e01060c060605040905030a0e0319110301050606250c09091a010611 71
    0x41c0d180ca070038100c948080700d400c000c1c000344420b104c0501008030355a20700c0c040c07010307514107120740ca48800601c80f5002c564189150f124925007800c1020a902c0000e240c40c085080140100c0b02000c40252025070b171150f1400c4544000e0026044c1d141e030102d950a030702418003031400c042200021065204010f41c40c14010b481140c0e1140c19104002480e4100e60700d245000c03040d40c049241c1100080300a28415901510902403044100ea0010041c42003000c400d0600b00354900340308040c1c9404000b50070440045045c0407054401143d10810b650703590f4002d200d19601c0318807101003450020160380055129500444c00c02d2040741c0020808001d448403102903141c60078001c01004002498000c001c40801e900c0c00e0000300e00da0600081c481024000c407000c0d80240310351b8645405000141c403800450314020103141c020104100d1700390740b0070f0100901030315003440c03056202d2002070100d03011110125089500740c5003d41c0b10103c820003041c01050282400c1070600c00004c41292140c003a203040218 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 213421852 1250 213420602 213420617
    0x30506131a0705040f0b0c0d03020c070608090309030102040b0c07090c14180a06171e0112080f0f03090c010903030f050a030e1902180610030b03190506010f05060415 73
    0xb001031081e42624010511802d10104d216902c0d109075107654050803405905000d02e00c69150560300074001c07549010780860050010b00c1ca803400444001601414422140c001001104006e80e401d0003d000a0301c014507269903a801c05103001458006954441c5948a050610007a011a001000000403c50000e8081e5440058410b801410f03e043c4c40f240ba40f200d000c16002c101c0c00c0e8080503450705c404071810200c08984440e044100550401c10301007660009250040c0400151000c070180450311641c0e145050400103080b9581a8200c800c141d10b081d80c022040101c014010020360304103031400c5c2414026241152801004148a002110b091140001e42d255495109900103aa00244442500c0f425020503c28071565401040e040c0d20500030040342103480f504200c000b6010b085e005045003020301400c0707420b4001e080344245482d818054640c6100b043c008003548017000c184100003030721301340d0704229a0303080320252a00014003402050201344503600c00c1603029002010319040800 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 213423102 1250 213421852 213421861
    0x8091f0e0f1306030302030a020f06060d020f01110a060506090115140912100c020d020609070504180b090705040e010b0303030a090507051f0f03090203150612070f030506131a 77
    0x1e855001840b580600300b460800004241503001c0302a00120041c3e07402c0e9680c129002038003d82e82c080640d42a039005140ca9074480c014640400aa80100f0341030603d019034200911301e079410550014419117000e030301da80c1080030a1809840190140c81c6c64038403d58600201c24000706150681c51425009000029195030650341c0e110700d075218100120200d4031a41c081c010400007920210103ca00035115150030f06940d07500104401e88143c028800400455141800b004041c3c0083d81315030f0f900041480a050208031098081c3e40b2600048000303040944c83c00c402e10003100c00428100d0202d9150100342c16183e603002c01142d80103400341e0404140a0794504066040085039809654000351101a4104d0601110601c4402c0312941c0c98007250b903000e10406030182d5806110080d4150001c6041f4511030319141ea095800c000c02034174105251401c4c05803640340081d150442c05803000307103d4040040041c1002840e520400e00c02d08643e02c00801d40d51400c00444000c40d210741440e0300300024 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 213424352 1250 213423102 213423109
    0xf04050106051302120a05040f15060510030c080106031112100803191b0b040320030a110105010b090315041406010e0412031407140f03010308091f0e0f 67
    0x140141400514a542003c0118540802540103100410002e0301240c00104501c0c03543c402c0b14802d03508013040700a0f8204a90b03c044038002a00c11a104940da0740801264944401000004400060b20005101c429070880506510350591240d401c06051001845103c80440e090300c1042c55100701001c40c58642c0301072106815030b0743c6c01c2918a4031011030350b02100a82c03400d1100d9194003d4032149282c0b02e2011051081d00703841d00014094140307800100d40040d103d9540c82c0385c10340710f6201032443c260340544074a08541c494210503000400486000d0b804000030310920340103240094044e8501040040460b4403070102e01d0500405000e504002070910041403035410320892200292040342da10394114000c10340c0c0540d07040e1040d041c5600000d07000c9002c0c2c03059800c82e114801e40007007151ba4600007191015011010704d104c812050215030401c81940d0b01441c0a1403241c01c1c05a140c002180500c024440c00c14801c000d0b100440f801341d0038032030708400c43c10640181541c01500c00369040e0040f = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 213425602 1250 213424352 213424361
    0x10c02031c020d051e070801062c0a06020609010f05190c050403060e0313060e0d110312030901050702010e0d050702041d1504020f0111120a03060e010806040203070905010e0f040501 80
    0x10f40200b107040108008080c02c0d80f0048201c400340400700b41c00c0c80e4550300021180ca090901070140890001c0c82010414000301d06182c1c2c80c0361403d6107041419132100c02281c50b1650b55402400942c1c410780520410110a0007825505040d8240c108098500042210110707298988409139503940c40340300c1241701e442881110007642c3c00801c1030000d00803114940f945d0f944144640391030f0700c04110f4042200c522492104450002c020b010032066041d68488180030000000d00583c1880f41000b05410302c03840c4800b451007500ea480c0001403a14120307001900f510068082d00e101601f02450303d458054100081c2c03104607806450010b55520801d04009e1400c0d8143c42005082c0b00d000e10f14940c07241400d021512803442a2030103d50b096a903001558419041d0790520500d81041e0285ca018140340c0b4003400c801003107494041603603903940c030641c0130004081e000310f40142c006404000c01e5090406c010801400d1310301c41040558502000c0b030031800c10150400c1500181c420120f42401400d401 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 213426852 1250 213425602 213425617
    0x1b1204061b05091503010b09040b120a05010b0a050609010801090f0b1c0c05240c0a0c030521040b0301050609010c020907050919060206040b0a15060f030e010c02031c02 74
    0x203080352044071820025240c1c2d00007108843c801c0034210020700c0c4c42915603050b03034100d60702d070440746042104900400c0081c200280c14079411420501480740101402c1001c904074500600002030300320352003021f000e68843c60713402036401050108000082d03640c0c880d454504441c1501e0001a0100c4160000d00142081d100d11681c030549001039040348040240c0754802c0b07544903901c0718604c2a6a0428401945c00620140d00d1940e4a05c600c220002e10440003459030007208019281022840e82c0e03915040d0200c0d400c20350359580040d1189904d01003411180b030f04c041c21000c00c2400e0915025044960307200500803940940c10104000c0703402d034086c0368030540303d0b54004c00030130342d528003000b00804680002028501c01c0f14004149000b00e1024210b18042d21019405050265580c1e1101c40361284007800c2d241171a5601d60300d50b0045881031103c00b004d00071070343c1c3d0301001d4103074401c4c000c0a031106d000c04080e181e40f400d40c0c00c481d0542c0000440d405400b100d03080070880d0302403110070700090142c1071 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 213428102 1250 213426852 213426881
    0x1e0510050a17040b010608060405040302100e03090901030803011701051005040e1501080619090803060d020a080109030207090c030209030c0f0d0602190f0513061206051e010201051b120406 83
    0x3e02041103840d84002d416114596540603041d136462080001b41e40d015038028015821401d01c05214055a81041c07440c2c2c00c49400f00d9180c14030341000b15400c2da4099209942401c0c0100040c000c42c20481c010303201d6410810028402c5003451031001d503200c002d502c00c491003190f962680c3d11292009100e00b080120051020104542c1d40e41c0300b8075241c0c40c00301e5081241218120400207810218460000bc2e1030b000020a82540d680005011400700c01140a0b6440582d0890000d580300c2d090240507210f0703119a001d03003141c41c0307860490380075a40c1c22492402414010f01495036070f0f841c00a000f60403000e0845814a51005038000300346900c2d9220409808035000160a49068595906040811903a42d590035030381a40c80804885501842fa001124200701880c20003e040c8030f070043c00410100c140b0300241c4256940c0019101015080140c460080c03d0000c0042640e028802c1c83da101240b207940088a0395035005004c039030300c1200440380340011003001140610075680e002003200708080 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 213429352 1250 213428102 213428147
    0x4090b070306060315030807060b0301021e0a1d180c09130b0f090714030a0f09030e091807050607381b030a2409061e0510050a 56
    0x2400c014003512941c055a004a81840d142030b0b01d43c00090004401c690300240d4060030000541d0b150320141a81c0900554199001e0094801910500700c5156000c2c480900d055903441c2954009400d202c9051504500e0fa1450200d000f80c68a40c0c5000e507602140500100c0324542e1284901d01c800d005020b00b49400601c0d40d4040c011019490b840101d03250000c607081401c42d16036104010003004210780a02c00078003940082c00021210002468001c0784540300480d2011190f9004822030f003518000343c0024421207161002800c1c00d404154200c01d04201a600c24a1002441c03680c6050a02c2014050400041c651040c0a50240e51200e4600207a00c4a24004e0000f0310944014143c529a414466000400720b008001c400c18049090304145e000a030a5640e41c1890400409604030b80041c166600140c82014640004443c405013400c407800040180c1890b6101d4492140802c808104c40740200d01402181c1d59581315150b200d000b480c00551300e00025404070360040000740b45141c0180c96 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 213430602 1250 213429352 213429361
    0x5070501110c0c03070b03090a02011103120c0a0e031b0d03030608030307020309010206130f03050a0c0501060f230603040809060706110d0b010f08061002031b0106050f270604090b 79
    0x203c1c030b04000140450869007095252600b0003018070003680c10050582c480901c942c019400f4200c100010082141620308115100d2001d1550000031204000c0a010014404480581100e80c1c0300d1400425002001440000c1e4281d00043c0c2c460060709205688604440e01050b101e5040040544050000d40746c0b40e0038240d0001e96281c00000340c050150040c1c100142000d07280804600300a500407044054228903520240c645500c1a08140d041202140c2c1d80030102c0e809000b8070000300000c00e2000251840c0410b981020740040c014038803610038040020125541d91004e50381c025401c04c0c00c503651800341400054040c4070f02500184520f0903d4001d015192410010f842040c03a018014000c40c0400c400468000c004e4821440200f21042c01240311400c03c40e0045000245600403a03140c280d034200204010403070321b41039800b160345030601840a41001d0b001d003034085e903003076445001000c60000702030300380e100c1303420490440d81811000800946c5c994100207207542d001000214203042 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 213431852 1250 213430602 213430627
    0x4110f040f02070201140f09060f12040c060e04020c03030604051503070305010c1805130f0b121f0b0a090c09091107060b010504120b0907151706040507050a0507050111 74
    0x2c12016800710350780c1c042d9250031b03001110884603060000a00d43c0d1802034490100481d603000b0081c01900d03402c0601074441d84e000001c180c03d008034080d40d14251194500f0300c0c0141484100f180b0940514010300c01c61481e04d0f80081a03e400c0541281c011642d541e4204069005418601c0c01c1941481401130000c02c0c004107512020000d005907481801d0311840c81030210080044e032003904e420014007500540c042c544d50340852101515114003003410220840040d600003482861441150028008a4089802e10201c40d080401e403140500c924060200020074800003417290040072074950082c0341100303105041d0a009041c00d95420800d00758411a003000340d40159104039440b6181440e44401c1e58000c906444c2140c03001c21001d21041d03542c0d95a405940300140c080741b503034401c081000c074910b0b201841020300040e0341da0700c4080c0200354081011026001510642c011403400c0288901160710404480404006017000350381c5030f84501d807840c01000d020014045c00d41010554841540 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 213433102 1250 213431852 213431857
    0x3080307032003040602031005060a0306091a0102060403050c0a060f02030402030d2a050a0512030906010e0601020a02061b0d0302130602013308030f03040201080f060904110f040f02 80
    0x1800c640e02000318040d110a0105440c0101c14034480800050002400061040d001181e100c0c0301a03c1202c080b6a4900c00b140700f50704a42e0050303020a440300e00a000c030318901c0c41140036144003100005a0300101c0c42c0080d4540301c01078070150400c10002218161030b4010030580e00d00550203003080005650102c4288002c0d04150b80072403083c040d5800f1002100d100c0c20352410304020052400344825001c0c5c58021250454940407a40d03401004200004180c06210034852905606d20341039491400074021814140d058200760390742401e00d01031000070390f80003d15144075a41070310025235071241d100302c882c1c03201003103186401c040c428441c00c40c00581d80754014041038510f64103402ea441e40c940000380c0c280da002031000d8482c0f02c00c0c142c50000c0902841101003062100d2a1087c001d00d45440782170782503610018031740d10440000424482156400150b44d9403060103a005a00701d17040100003d0b1084c0d1002d04042c20211010002d20300310b581c0c0840103100d000005004020204290700c8060294 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 213434352 1250 213433102 213433111
    0x80106050909010c02060115140c060106090518070c0206091017090706120c17010914060603010312120b060409060807080712120c06231b04050d020303090406030803 73
    0xa504140c0411891001400350024000c810f8004d011968200362340070944410340c000c078508010b01c20994510400e290802403002d01c600d18050a0698100a40584913608980c08035001c2d40c0b06041034900181242022500b1030030500d0b0032105101d90780006501c900079071040b1a441041d50414a517503a0700050910050036880b04105400d59602c0c603c183ca44e841c0344941c80118048200101500c03c00d80d001000f41c0c101800c0400090020300b03c07803200e0b00801d030040603030a641c80b24078009490080c40c08a501c14400c9681528540c11950349030940080c9a4803a070910000d0180034a14152680100704003c0c0080c0505032115a252900c0001d802c0b0b030300c10a2a24000e01ca0007042130040490341d1429200403440b0b1050f82822aa41c40700d0b12550500b45034204170b030005030540064614016502c086087c5000c0300014000c3d5440140001005090385c0000c48248191b48000c00b2041c0586040703070000c860070480c080090000c83d04500c42c502040e6805442d000d00882000300c6000071314006d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 213435602 1250 213434352 213434359
    0xf050a0b030d020102130e1015051b0102191803050105162607050a02010608070320090708060409110402031806070c230f010e07081b13230108010605 66
    0x140b80802d88241e080748150300411503c040884020300a19684000d001d0b0041072a108000352035641e900c07103062072020358803280d0000e400007138580c5034080c003201c1e00145000c0c03d030000c40c5800300c204000d00c600130106842c2d074203020952805926107803500380004002c5030420024890351074071109100d0b080c0115031b1840c000c5408010f000074040301e01d0803e250111403491400c22252124035007a030b034a401501102045640302c200202e541c8406000b4240210f01c94111441042c00d03200c0341e461220498641140918001e02c01c01808540c0301d50010740000058800140d0400c150074503410542000c2c1000d0b411600000511034049403c08500394514505070942c0d44580320050112078212580070301401c04070102e207041d045260460f0251041002c45411100041405282c46e820b440018410315074540200300200900c400a000c20348914050701c106155000221700040c1c01040c55040c410700c2c03c0c0d0784500302d100045880c0d02c02e50344000b003c10011801d6075554a802e0103010706004071800f = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 213436852 1250 213435602 213435613
    0x1b05010b040e03120411030a12080402010f050c0a080c10090c030b0601020f0a060c110d20010b031c0201060b03100807050409080703080415020d060504110f04180f050a0b03 76
    0x461541c0402034500d000c5040340c4c814025126502c2c0c440800c08840d0046034507006e4852004001660320766044c1e0311181c0c54940e901d20340760500000d01841015010041800300421141e460310340080b801c40c003510385c01043c16032108c0c4140d0040e4030300000a400c0c1c1d000c80d450100c0e08010701403001064005c41c2d1003200506515622000120f13190888040f0f10b8015510145500c80020b14640141c42a1a89450080d400c01c4031620307514903103000c4220410102d80600900106c0000400c45c400350002e1440003031010408503004655201e881c074601e10500c614030941400d107540b003900310038010b1100c001c070f00346c4a003023804045005000c40e100ea074034503103d0414002a1410f00380190038603103400201c43d070305008542c0c40603a54414001c004956441c4c10743c00407408610584040c0401c0550420005100f0381884103001c200c401007000d04080d041c003440300504544d2104119821749540c880c11041d0b901d00c0c2d117001005001c2031804070300f1309800c1a040000b1074046910903016941c0c100e00310b0700e = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 213438102 1250 213436852 213436871
    0x17041d0907080a050703080d09060507120608011e0e010209120f071203050405060304060e060a0e0c06030c040b0f0904091101201b0102120a0305011e15030c1b05010b04 74
    0x140d0f00d00e41e40368001c143d0303040399104202007000e003000b0380f4090f503001d0000b02c8c0c000c4050b500c1101701c80b400c45402001c26100400d4920b0481144140d8000d045181c001b041201182101d682e0245480c08030340c56400e0300d6158401d0395401c2901521680304000d0064502840d05d0b4610035101c03801c2002c1c0c10294030a80c0c000080e0a4032035801c140724640c0548445240a040105001f41c9900060003980d076540c0384d0482919084041180d180700b01000320000950b800c043c17034170340e041c5200200000d00c80d0304203109010340000e00c1c00c11202180c0c1020500c17541c2d51710350034003000ca0f401090500c0b503004d442d041d11042801040c030311002481100342c1e075008110601240c8403410111520042c40c00790b1041c2900c441c0c20661999802e07d0001c1401224000140105010b01c185d028840d4003000a854100400c61901c4041020661100120200c60b04a040410ba040b201c40f42d1002e41c0200343c3c883c00030740c000c503010f070b070454003c21f82c0c81280f07107656107050404a028120741214140a40c2c5080c0419 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 213439352 1250 213438102 213438119
    0x1080d0503060d350d060603060b031518070c14010c140f041e151b061a040504050c0f031501050d08090303030f040b0f1317041d0907 59
    0x1a4072480000345403460078071442e02d800240382c0c191003031102040110404a404c0d6143d800400c10080304d04a100c030754548000c4080b40c280c410682c007901c281800c0036030078428004140140c96005843c0520400024001c10029100111a404800068460405018405034000902a04540103c0d000f681403640800700790b00326003805c000f80e00007410700d4003680a1010b20b6070090a86606903500d9508090703e6111035142d164502940d0b146444900c20304100386256642c403803421088600703000a0b01520a50400c01c1c3c1d41c5660001000345030360740c1101c40c4584e40d280b010201c03220080c0c010000d07450070b0b240282d41c40405041e854441d400302800c21201b441c0000308070f00300300c0000c03600c4030380c41c0d207004240716140d404c0050440785d00105114003140b9403020070103984078507483c42e282c4006007002d0520104c2071348003402503c50034502104020f00361040d12030b01a5030560102078610755600c1c40c0303880e00f0a40219007141c11117004580081c0000403840c3d121a00808850003030b11074050f17890884 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 213440602 1250 213439352 213439357
    0xa0215130201050901032f04030605010501050a090e04051c02030d0b0f030a0308060a0306020a0c0308010609050a03122705010207050409230102120106031406040905060a180b010e01080d05 83
    0xb0300281c800c010b19146944030303811000415030b001001034000800c0b072809295054045124820508010604200f40440f0f4000d840c010182803c040d8039120841c20000c1a0803414055403410010303020100702006010841517100d1400749150010004d442d00c0000c0d144e40c09101d00d00070240c100701024150740b600382145194440014003d00d00480103990035102c160000b450715501c420215800408914580010100c8200769661a48401c7c101d00e80a0280c0406800680c20418504418049501c03070101d0001605d4004013800c82c04d2002000450305403151000c1c071f22140326034414400c260444000780c0c6003038800c00d1b029038075007030b49950a00c021900b4940010704095065842408000b1040712802d5443c0a04070002d441c0001c00d800f02442e000b000e0344108000380d900e1090014504007440a5a0414012501400130090700c0c9c50301652210050706060a032565110348a084d0907450000300d90407680550b481405681da0184003140d40800d11860a00c0c0c018104203850182c0719004 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 213441852 1250 213440602 213440641
    0x120e0a0e041a07120c020106030b09070f0602032104061e06050f03060603030d0509070b0403030806010e03010c0e04020d020c070e01061103070f03080a02041d01030c1409180a080a0215 81
    0x104c00741580c0442d010315001e44104291401503541c0d64101201240a03000e9051040c0e006500401c4860f1401c100321071480031035800101150024091401d03880c0c0b48030000c2c070114100025400d000d44441c01c2c488000c0110341c6207440d002115440c1031010302c1682c0c0160741110000c980e00c1a48040c000f05241e00d800c011240c450745900208034071045203401e9449541c0246401007151040b03038460f01c110015a0103a042900411940e8080005642c0d0000990388800010b500900c03007050b00350310103807401344000c01107449640c010030800c0e80c00318076a05580c40c3c0c800b01c004681e030051386c40c400c03401c201d0828003030800010703500d50740001c0e11480001100e0b4440e40c49006c10500d280343e0788080300c2844e4042d2103018095001c00c000100c1e442446445690040c3ca1404900a5451854071100c0725409510072030095030300b400c4840d0b031980c4003a070065104e0f00400e41c000a50344154000360501070042c000606041d40030134000c4000d64000b840c40104a00c6410342e140d0f9032205114913607801001c4c0b1 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 213443102 1250 213441852 213441857
    0x30f070311151b010e06090105100f0b0307081902070f0b070903020303030a0f09140c010e040c0210050c0903030c03070c0b07080703050a170c1c050108060103120e0a0e041a07 77
    0x108061081828410200a00100728000545e64100303208460403c0b505940c01c0344581e446400307000002c588003c0340c41c01401c404e00b00d03060992074011242c40320b0200508440510034008009554005803002c1c0703051202c1c01100440d030b00e001614016003000c4003900c0a4550801502c000741d4118020003460041c1ca4005006508598500c0313074280c0603007d0f05405401d80b40d16030400320300096031003114149100e00b1201900b0030f000c5120004000916900629115606002c1c8043c006a0003003009540e603a040680030409548104c01c0a00c107200d52605550140310000b100d09103920b000c00030b804078a2145004186d40d6a5410401c8a46d0052103800703449a01c0070800034002900540062040b6000340c2000d4000103042c0350b0b0707113000395001c640303911501c0000580400390400a8004032940110343c44200720b9541405003859840105010080c000c05106801401890041d032012140d54001803011403550f844000e110b844002c2524116002504030032040d070b900b88812140ca200740b0312a0b = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 213444352 1250 213443102 213443107
    0x2160e09120a0309081305120115061409060d060e0106030c09060c1a09010c021009050a1106120a0204050a140904030e0411030903090108010e090c04020304060605030f07031115 78
    0x1c8424040c40e40c440403407001851383d0703548650001041000604800218154122202840c21040c4842d00e0740004c0d4900940e450028007841300c3c4200da4000058030304e140b90410040c0890b500560301d0744902d40c10391fa44280045a407481c501c405e40c00c103209440c0ca0350344001060b40d0380c440070703400d0b030380c112400304085100204288001480703424481ea030640521038090700500340c0c1d40c40072405041942c000d4556519001d00c1c0c13807003580411490459003000c08041221180649415840790090030b0001e250100d0304805141c2d941c1d50100352074034101045003510190800d031a00340000e5029104590042e00380304400155041e51840460041001401c520b00568541e501150741082281c141640680d40310700c407145480c9110b010b10310801211004640d0341c80ea0400140100c503050740300303c01c4105c1d000200041c40002084030042c0803000d0b1005612525145000c1c4090241c85d008150144203135144c020f001c101c00680d10b021680030f0b070382d0002d04032010014803a80d06a510062031b40403030304 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 213445602 1250 213444352 213444373
    0x20f03060408180109090e06012d050f150d0e0d0804050d030c1209030201020409110309030a0507030507141f020906040b07060f020a11070b070210080a150602160e09 73
    0x264204203c0000051400c051280c0d11521110304590108018504c0c0d5032104005001f000c082c150001d000079006030440241d445c02c03060200801e151801094004c0500ca003140c00c0e6900c03420388481810b210f07900410780350b5140b964144000c1140a54000c80c901c501e400010300c10307000d150502e0055170840d0141c40c0c00c00b10010160003810b03541240b00c041090340c502c490520410784c07207000b0400d8400d83c005a5074030704d0b290030380003503c00c1892901d500040070010b004103404008101c601e22084c81c00c0940d200c6446090598940c040da94000e0540000c40c1500003a100c0e020a2102c000c2c0d441d1080c8041d00343c0041d01040c1280101d06500d50008000c00c003e102d10b80c201c6000c0c1038914401d420100380004e000080340184d0300551401c00109602d03013410b11580c1414000d803030241040c0301c01541081501c1d000107205064203000780c01400201004140c1c5404940c100d015590074000120a01c1555100700135607911840609802122194102144141c4400007403401a00e06500501c44940c0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 213446852 1250 213445602 213445627
    0x806091012210207230d0213020415053001061b050f03070309170604020405040f0c0303020607110c1f30060e060d0605091f020403020f03060408 64
    0x1014282d4000511180011182a01500030802032845501030b013031180c90000482521015820710302c14500c50005041c0306501c2d07440090218a404480c404d8401445905000081c462500007042c0002e051a060b610250010010045200306d01c4620074501081c9520b801e6048150f600c0d8102c0481c40c0c40104155846107801400009919040808015455603854a41070000f9451081900040b07401c0051541040d00b5100526102e210602143c0003105113948504005100900c0341e6924004201841030007109110007a92001001c00703000d40300c0c02d02959401044a200000030045052083c1003140031440100c903c00141000911110f144001c038000e40943c6080707010000c04040100b8802c0c0038141001c0300108901c1d4443c10128000080e0b17055a409800c03810300342c0108010701040c2c0d168204004031b043c1d001000003a6680341d10341c03a982800c088030041c15200b0442d50709250740300da181e4000c0003201d10807034680c1c109480306018584c6414044402501030002403001c401c0615 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 213448102 1250 213446852 213446879
    0x40c0509060114070b0115020601060207090903110105091b040c120903020127060f0509100c09151e08070c031112070b04060b0303130504020d0f091208060910 70
    0x50420f5101d140701108215000d400c070f508180c0b100003080004000d0a0b502c400c1a0081c45258406003000b5810504085d5880c021441402c04581d0f036520000c040c1849002d078488241c0103040244441d046c44809207503920503240d0503200d01d0000c01141980da1400d40b04044020150b5103d00500c9420f41d41c007900204614481a130940d5202c030035605500443c841e8040c0f50440c1c4178148407501510741420f100f00d500e680c0d203121030240b6000621280000c00625400305030b044402c041144200c40c0c0d001c844140d0654000c0b4080040c850440c3d82140e008903420003c1c1c4070242c00e0601c24035800718100c903a500d083e03400501145400c0646000301c2d00c078444da00f4180407401c0480d541701c1c01c04c05018103281d00c5800c00b9525514240d06010420009000c0d843c15004114000d609040c800018410003607801c1c4580792160398006a581c15020007600084803182c035407201040b104909041004030031802140800c005404200014400e24106c03000d41d001f8407161007142d40320f82c1001d11100010 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 213449352 1250 213448102 213448111
    0xc03030a0c0b13080310090c0912110a03050304081b0a05012307080316030e070803040527040602210f010e1806150a060c02181008030a0e0f010305040c0509 69
    0xf40c00704000008141020003c5004218261070b86000307900e00680321045601b400c101d8010800706007800c1060306000c1d402060b0903608003010076641c0744001b002484441d115400141903000100d0001501c84003c1001a803c0840808140c00c00c121101009000d013440e00403140030070121124403003000380699064a0080007482150310745a00c0783c03502001c98100b12940c2e1f0307041c180015014041645400707100c04e211080700c010075000341070081283e120b0040f17000346806425641c004554070880d11700c0d05c20a02c560350240a88030300300350802c01c0195011304d940d801d102c804408201480310a5181440c8112020318801101e6424181c03480103001c1c010380044507580c1c5180880e00f0403d014488d40313001f400b01d121420f4031454200d05005c600301441d40f003401400099050040962981540407400c080301e04581c048594506004040004c0c542d00030540c248000f01d204010503811040e003100d404c1d401c035084145602180011001d45100b150001c2513514209030400ca1420b1080e60590030 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 213450602 1250 213449352 213449371
    0x2070501020321100803030916080105090c040e010b0915040c051603050a03090813050307080c0906090406060305060108030a090e0403020c090606090d06092a0e041514090c03030a0c0b 81
    0x7845d58452166242d13401c11780e20455941c100841107012020240d160350014035020000340000e1900040d801d8683c0e03040400d403070159444078050300122400394000c9172031a500030400080b0b414006502813031170600071401030089140419400405006500341c072420083d003101c42040318640d43e821662030708503a560006264980a8802c00181d581002d00002c0380001c0002d0700081c0f0b4102010700c0d01c07202c1d90101036030381c0040c403c8004580714800c800c0d81c0107109440641e005d480b0b900d41350000f8a103560025001d4003070b00c000840e25003008001804003d4260340c81f200c0080c1c6500c4000d11201303003501d008000da031241d2866901400d04068150303020100800d0181020301440100785481e10b44e000440702556110710b02c03001c00207200c00400301d14200c03400202d8990b43c03503050220314019034000e4400d480712090000b400c10541c0d004d144186050751a0501194140003181c1d4106001954070120600900d02e00300c4d040c1c10000183c1c0c3d580389080da9050201c80c241c0d10b03030048030000508003042 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 213451852 1250 213450602 213450631
    0x6040311120a050a120c050a0e06040e0f040302060106020d090e1911070201080a0c0507140705041103010333020a0c05010e150a061203110a060c030b0102070501020321 74
    0x14141549018101000c000d44a003aa604d5403d000242901090199102010318002d08144101e500c0801d07108985002d080003440120440c0008205000d15440700421030031100412001c3c240400f1002e018904c203800311246643c80d80e02c16600c03042998001c0c0001041038204000218000360816045500600341210443d501d004a105607050043ca80010810000b4a9011542e01103047d9034400d4051030708020000c5101c0c0000d140d0721403034501030b02c0328860b032403589580281805a0001070000070f200300103500101d003654400b07400910050b600072940501220002030007000441c8a41d4600c0104c00400c0360500009000b034100d40c1159041007502c40040c0001203003403040c1040025148010a69440460b0640442d0040141201d28003410203d040000e00c803540400c408003a81414060a621000c0b4500762404c40401c101508050500070301d142c4030307900341d031001c0c0750b80030281d00741c030896500d0707800590350303481140b8210454500108030303174100d144121050742c0c0104011a4500 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 213453102 1250 213451852 213451873
    0x120a020721090803040e0601050a020f060a0f0b01050306010807120b12010f2a140d0510030c050d0507090b06040810020a020706090e04061505180103060c0201090506040311 76
    0x2149101d80c0981c1e00c0120300410300c8032921a0042d00c1600100f5a200041d4505800d02241843c2468081c101b581071107004a00400440d009100c00c0366201c48542c11502c00345081d0b60ba0002030705006854103000383c542020301825522842c1128850a0180c642e90a29201c00504840e2513070484541071481d07a0700c100d1503c880d9038001d01080c00441500000c140000d524108100301c451842c1c040350070301001c0200300030209c600d5401044810090900da00004141c1c1d142c21911302c22041041c00c072514007010083e00c01419410003090700d0094041000c6241ca070400e02c8440800020090301690089004001c081030a804c0a442c5990160034503052079610001d25103451411740140303101c6c5401240041305e40c3c0d410080b02004040074a04a40903a03d04116006000805040602026280d100b842c0d100d80300320600d00001e280c040c0501103550300b941d40000402c02c003070000300c4a0b40c2c144080404011f03c1406045011a0400c02504694a65680580340e440810221142d18000d40c245503 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 213454352 1250 213453102 213453113
    0x80402041e02030a05010602070602060a020c1603060e060105040510030602161b0806150d0308070e060f0d0513050d0503180102030112020306090109110f01090b03070c17030408120a0207 82
    0x1090701035078218001d038880c01c021035007005944050300240c04551001d0001c01949500082d00b64203d80800d00050341c2e100038258080c00e18021120454502c03540075000000c0001540c88403488ad00c00406840d0580d803510100f20681d00e0568040907142d141071401c1c00400c00c15030081c500400c20350580084690345550749018200402181e403003600c80440e041101072418485141d000c8100c00c22001c6204211340001c406004440000c1e01300815580002c2205010307084c84032255030010705040c0c0307c2d15100b00703c00c0a070b840400c0c9501440c1c10500401e8101c50318171100720340716a10030060040520100e008031510340001b4030045007042d0003035041c0c2e49201e0078401103002c0d0920f0943e0150f091a940181464240d010309101e60326032520040c94007042c0540c1480401400841d25171180010400040356690200d4002000844002003804004c82c0c01c050300c055614420898503045c504080d03002d0300580800c03500940f2a050070484441c005420210107607021800c2100142800c4564681 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 213455602 1250 213454352 213454391
    0x1e0319090f030c0f08030703050f1602031e010f0204080a02010e0613090b040501080a0309140310050c090f0a1406070303020c0d020105070e030a2006071202010b13060e0708040204 79
    0x150355510580f0010304c00703c56082510400f410090009510b4100e40c1e0364014160f21170b942c031f40783d10304101240d0001c01350441120400d089800400701e4284140e10000d4644552501d81d00c00310070b6282c03c42d610410000c50080d2801c680b040c0d0054411030400381c00540b200240c5042d00c4c1e030301a40802c1320020303a8008500b19070140504200c0091404015410300c8100d60068110f05020781c48003045400103580a5031440540e1103041c1240c08541c41400801c2ca00803030089600c0040b400c0401700b00b4545e1b0321a01a01380303890201c2d60803940e4031003031080c00484c01d00d902644403c035810710070000d200e0030081e0042000c144a441c2c01403901061500050400f42003900c51030042c1d45500c140250541c1c0402d003ca0300c143c04602405001321a6540d4400d03185034205172004805c0c40d41400421640c0ba0016511902d03081446180c0d206540031009000b071040c03090442c42440c8011415000355001c2c440c0009980389681086242d4032110419513203880700030003c90740152200300b6441075200d2041c0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 213456852 1250 213455602 213455609
    0x4020d06080601030c0f0e010506220504020f0712080708040803070c06020c0a060b1e0f030c03072c1e131e06050603010902060f180306010f06021e0319090f 69
    0x3100c641078140100c0005150a0380d0021f045407500ca4010b000941c5e03020b007226500078141c3e0001c2c030050800d00d0300e52100320f869030141d0ba01510200e0b080540540200051000d14494601d0389a810040e6078107a1f0013110a951207000610b24030000750001d04000015070f0419410308194420f99100d50303c04050b44e1140230644015004031001c5c400300403060240000051007211018400410b411551200c40101c0380518440e00e8590700c40d043c41c1d20b05010541d488003000d41510245a01d44000d0300c2080401c40800c0082d01454804800d0310030900e1410b80106110310740d462900360440701030003401e000a0161b60f407040c200101103000845030b0006010b26074001c0000004e0013000d042c09421288000c1c1202d0107139040c4000d07240140d0300c9800f155410421182003a464540150082c02045031415070b05425201e490004074429048144020896030507508880b9003085480c10040d51881e49110303040240e106001c0c03c008a0880a20703901d1041e860f24290f40141e0366461b00c628105203950 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 213458102 1250 213456852 213456863
    0x603091906061e05031f060314073201030b03100501030b06010e040603111c08070b1605090307050112110d0c0314010e0c030a0f020d1d0a08030604020d0608060103 72
    0x78010840c2d00c0c04090b108041c010b583c120350301030a24000c00701c0c3c0c442600c03a44020804c1c43e5040c1000c200000740d4404006181c11100f020341145144112659032a014080e180d43c0f0302e12285c01c0201c4280b054072216108002d1081c4540f500450070066000e0034010400680c1405204000b46420902d841403500a60042456880c1802d01c0d00c0050200d202d9440f46900980c1001c03018000700b50007607102c0940740400c0d240d40c08000840044c01980c61606000280181e200041d403106012000d10030138000c001c4d2404011030400750b00800c2e1201c0c0b08023807440f5096000401c08104a41c0181a408001e03816041e000c5000c0046000101c216804201403031001e40d0717541d00349034040d07a05200d04050080f01824401c1c640d4144511443d6180004181040094001000990020302900b000c100200012825916409201c403100090060341d081d84801c0480c1c410080da2705000040d031200e600750071000051441e151001400080d50100311100c13072094498200140d80c1400f04072150080d80242d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 213459352 1250 213458102 213458111
    0x160210030b01080c0a020318040902031b01021911010c0201030f060e10061404090c0e060f070b0c0306010c0602070203210c01140c04050d03180b07140304080c0603091906 75
    0x301c00074202c070b000900704004115003405595030560f00007003200c80d002e0f11004140300030001880020003400d00040020741502601c20f52101d14280069100071540c000d8003600d000c440c000c040081ca800107210042d1283d4000300c0103119070b5000b04e4503014280c0c011324000c46c02400d0f4040c00e00503a051075019400310141101044a12902c41c8507941c043e2800c0d14001150484041451015000e1030044580003603440603500515401a01d180e44a004003605407525801380e9a000c55094200b06006e03a1805403c2001503240d00c40070b0102c1e445004143c4a08503880103589a031002504080c20498041c0704000e942c1000c008441c900745030f0745407141421a610402d0402103070235038000692818010144109029422201e2001d8600b078400a481510306d214260a044444405000d11600c43c0c0c207001001085505003a070090a02c640501e02035002d9904400ca0340381d503807203140f181c03240580012100d0303149407410744011908800404100c90b031401d070342c50381138000160940041300d0a0b5034a = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 213460602 1250 213459352 213459371
    0x3150306010b0918070c050604030f0f090302090109020f0c01090b160e0f0603061305010f0501090e01080d0e0d12020a03080a0506130e010e03030408120603120f16021003 75
    0x10445036000d410302c240d0346410300c0061008a02c006400201e001c0d0307100c900900203400c851089844003515504071080f0f600d82d043c10304000c0e0445807009505c1700050005840754109034003443c02182202d5000d041e1300c20341c2c8c3c80c0000c000001d4101420b2400c039139004000584904e0400d006258202d409610618054107103045c3c0e101c01809500c101c03400340404203807411901d0752451a000788002080d41d0070b070b999949403070000d6001c241c16a011004680f40000115007086640c0a95058940a0b01d0f02c81d0615122210f404c4235400c240b24002595000c100c2000f2501d10070305d03550489980142540d024800c50360760301c08486901e40316500042c0c0c4600700d20802d06900141d629001034a01d90100102d09000000c52441c0041e0070a24503210b03128011200054001d52010f0171180959059030348a00b8030b4545260954000900c01c030b00c0c0700390080480c005250114115510041d01d025031407070b102910303c18a0701034016442c3d640508102940c02c1002d078403007041c0f064500e00c6e5a50000754030011b = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 213461852 1250 213460602 213460609
    0xb03160e010509010305120a0c0b0a06060f0207081e030412030305061309050c0f130603030c0b0a05010506030411010302040506070f05280303052509060f02160b0c0c060315 76
    0x503484684503800f070364010404207801289031114440682d07401a030f03507507034460f00740c900107000d6000400001c8440d0802150b24030380d038003c505844940d1358402c000300444030202da442c02c1e07900444506410078820350400158441008001746078079010f490400c1d698103031218400a840c0c1c01600401d40710b030204611440e0400754681801c48000c0300300050745854903003030b0380c40c607010360164003c001000000c2c0d101d603039040d014103014683c01800c2c0a407948a15008111300d00c100012580c2c0c600301740120380d01c901c4d940650342c10307034001401c0141199111b8a560b829161030500d0507060550800000c1001e031110001820b000d80a0105008444568a4404d00c2d02c280c0d185191145050140490700d0a130303100301b1104001e5018038001c03440c1d80b01c610141e00500540403451502c0040c26074585240c0e5008180d00086078610b03203409080701485202a07031030340203c50b020b649601000b00240300100f1240040c0c540c58500d101102c203041801400314405910a40b0b821704007428500c041c2680f841d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 213463102 1250 213461852 213461879
    0x2270109060b09090411040c030b0f10080c0d090803010e09190302071412060a140a09030509010c031101060b090f0126070c12030902010e06070c03080307030b0316 72
    0x2240340303081010700c2c58809410054028143c1180c070981c5004045810300906441500d42490010010086468070b840c020300100b030410316650040c880448582c02c5c3c0d203080c1c810314929441946a01c2119a1001d0000c1c98941c031510759031007401d03030350b11040012900c500095406071500018a001e02c3c1408102d040ca00b409000000c20207803480403803500004d6020560714111008604480d400c188041d0002d0701e14243d4821500303051044c00100118030106420100380010030440314141910341d40e4506080d580d0006014002c504200488000c5510901050a041d400b83c50201241e00048172042d080d40c01543c486020780340c0c00704c1c601b041442c145201e00511102400c00703907510341d02000003020740324181c60741c001303944007010025006a004042010019074071030707000300c0e05d615a00e00150050000c0c04060340020180b402c200d000c0e0602408940e011500300c150346c4501c81ca50ba03140401e6500041c00c0704105500c1d00d45030300c0d940d2002c024491650103805981412641003011002c3d084 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 213464352 1250 213463102 213463109
    0x2100c230c070b03090c060c0102180a080a120903051509120a0207090911031203011e06080a0b041d060412021204030305070611030906070f050906040e06030703022701 74
    0x800c02042a51034040001404004484003070307440a45076502d085100342024840224039410020003e0182e481440642c0289440090b0101e170704200d0b450801808140690750060200c3c640c001004000429a074580401800747c0c1403400350b407000d840e84d950782c0c10b1140311408c0f80078a0360b01f0401d02403a10700030b0100c4150a115121128100082940025902d0400384145001a950ba40c00a07050001d0b51002e041700d0b00c1c010f0704480c005035030010795620b598000d1280c1211081100382c0710402c200c422041e4821510142d40b070345090b450b200050300040074503020301540181d5885072880103640c0d01c2451134080710103c01820310f9143c0b600b003412940140108035403c5400c10401001050303040e0007a038042e02e40601c0c2c556190540c03440c0ac2c100400c45d401046107440f9011040054038480014611b00c01c00c2d01c2d42d54140328041c41e04065072140a110380556102d00103000c1440307104a201d915941c000001000c98044da1b0703491300412925115201110908060100c0312568600035402c0503005 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 213465602 1250 213464352 213464417
    0x20f0a03050601020c19290c1b0411180a17100b03060f07140409060b0a0e0f0a1505160b070f210b010e0301110c010c0305100b0a02100c 60
    0xa9807025200050046494001d44002513040b642c0c685608120450032030624602040c4a645c40c3d48641649907100c840310500c540d4081191480442428680220070145801d00d0015041459080c504105040300c0e000d4cca422061400d000558492540c44d104403108840000c0c00581541004000036942090304045c040e51006003400122102d141b0107503030214a0f49400d401c003103c0e42c2c0398141c00d40b0469000340345842c107004002c0b422075181d01c014042012541c40d209a42014103081c801c48030701603502c95a00c500f0540d4200030384000248200c0040641d0301d801441c1405071107903802d100440708801d940c40702000e010030507102e0300512618006103990408541046900a812085c0a00e1035000020541c035414090900d9001d9480b2880c6050020024401100325904200706600300c0252010b4940c20103402049103070092180754081c1e0650a0010120703070400c100c902c6641d001405030401c501ca000713031440610b46175128101c0c0c0e6a15a54841850407101001009442c1c84003135200003 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 213466852 1250 213465602 213465619
    0xc100f0909020304120c02030a0b0c090108012403020d020f030415050c042312060a0c09050f060d050417070606050f060306060703140405130e2e0b04020f0a03050601020c 75
    0x482c111074130361045c10805103000010043c142c400b190405410210051181d080102800050030070340b0050101d4001c20b03038502c0c44d140c0e43d50203200144011070040018545404803100d084500c13940043c10180c10a24000d45809183c410b9000550303c1202e007502c008400420041d00214240100b035041000c140c15981082d0400c0d8840a8907a550001c28071080c02d000d42007078580e140c6525810364614160103654442c5041402200503000721500b00c80000ca60502c042414a4688071114440001030f0000e0f044c20718036400c800c0104030140081d95075922403001d0a400c000c0d8074008207041d900c99400414460300e08014450b00c0307400f481c442413207203805000300b00c466101d076070943d5501030301454140c540e4040d4010601c1c0601c9160807150308461003202e282420085500541d0092200c402240c0f800c11030480003080d030318403d1802a1402c18a07200002e00b00d0b140750802000762000400041c540000311014444561201c540d00011940702c904020444d0f8052014170a00702c001d9401d0308 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 213468102 1250 213466852 213466861
    0x60608060a140409020402070803070320070b1905010602100e07060c0f031101020a0c03021e07060f050d0903090801050a0902031c0215090105010f0602030c0606040e0c100f09090203 80
    0x9014001c5402103241c1110003922035407a9a84a401858060742c010300304540d254154201491180d00465104c40406c1c1409203502e040c44501c610308451017107180d0500c0c1070426559031001105d4005c0d03d03840c00a0381c0c1e108040d100c0c01142c0711303181c02001c254000340014401440342d1300c213944a0860342500340e0000e080400c61560862290181e9603400784070007d81d00d1161801b503403140f1543c103100701c46600c0410306160300741d0030038580040c15000303030211400145801d5a6500400e517164120410340c00c400070400105000340c10169003140300781080c81c01c00c0400d84066044803c180d00c10341c0003403400542080444d000384034240d00408000310521034402300380c000c203588405060310001034200100c408002d1610a00103590b0062004800c0d6466090400285010705000c0c0600309041d03488810028100340000126652440c42d4009451690303140010803004103103051615010307000d552141002d03980d502c20f000e407090f4007580f200320100000b08001818030071503030070548240f8410418407 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 213469352 1250 213468102 213468109
    0x615031c02100209010c0615140301090809010c020a080322080a0c0308090a05090f0a1b0801050913021008010602010b04060602030d02030703020c12090915090f07090f14030106060806 81
    0x1002c0c8010700240c0e1355040703a1300403982680f90110240165182c021200c00041103444100c0c122106481d42040d55030341a42018200c8501700002000347c4000c00080d185e65004603400700020f80010500c0201543c0d81401d04e09640c4035860034880001070100c2000c01948092100c40509910300040650864030390300d42904000600000e04401c2000c14082d40319920086020050030000d461049181480425000542d0054600c20186d82c2041920740d81510101c0707048a40110507550758000e40d10f803100b408040003001d03040d40c0310030804402c21380160b11075070005d1941c3c03c1c8981d90140a9890440020f00311412070f0f100710301c07960034081c0030002e4a07400001c2d201804800030006950340c0342c000c0f069000b440b40071108620f500407030700103101241d02000941a07028064800800660f940110040c2940c3c00e001090341c4000b011000c00e4041c20016009684400c20b400d052905030b0300c038020b0405800e407581c0030071081c00e00c0c1d8040c07a55506081c01044000c10450030301103130600300980003 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 213470602 1250 213469352 213469363
    0x9090b010c1b05060f040e09060402010519051204030e040b010504080a0b0a020426070e010e07030504050a08220504050c1204151806050f010303051c0204080615031c02 74
    0x6400e003251180c61154542d0a4207500d0014000140425514141c20380c20420b0f40e00584580b08100c105000042c1f4525000301c0e10510a0364140c0d1103500e440c0d03c6410001e0076030000b21505081120500c20111402803869116000d14000d4a40c0e0b08142c100104010a84203418402c504111044c40100300b030000000e113030350016504c1805d5040607651500108024052540045c1880d6001001d420581c80e01c0880c05000510103002c0d201c0c03290311013110221110081c800c041807818010002195103210742d00a64010780f01d90107540741c00d00c1e1038990900c540c02c1390070707000d4240c3c081d60080e030b1400948580d01c1c001840c00713640078000f0389082582141c00c0e001d840044c00f4090300c3d140c00102044030742583c000c0700d22081001001641030035080708404c1900e001d400c0303400300d00d80000f04d00e0018140621034121395250b07865a190a400e401c0881d0640c1d5564030200c02241c0038040840c0c540381c140301052150742d2651280b1000c46e584000c00d40f034011020218140032450000048550340c1c007144 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 213471852 1250 213470602 213470627
    0xf01150207180b0f060301030f0b010f050109060c0816050102030a0e120301121406010303020c0a14031c050c0703060902010f110d050f0d1b03060f050904140a17030709090b01 77
    0x80010340541c074502140131102c45040880c0c2c4200e00000202c2000800c010000d003050240c11102e02582e01e49a4400b0700407814025103002c102469000c00c01c13a803165141d900b000d8802e05207141408544912609150070210044071507940110800c80060101d104451710390101301c0040c40c2c0c410041918000500c812300800c0c4080302038400304c206100c4034901d846060105034048824540e07482c1002511340c82e0401840d40f05e04199200080e1a01c41c0907003901d50200002d01a0001d4030b480000e03c005581e0000401007880800d1000c446190014490b06001b54011a808100544148001410041040c0d24a81409015030965120420000d150b0156200609145588891040b100c00e95401110078103120b40342401c9200a180441c035480e4800d1349030343d841c10300c255612100c408818240c580079107038220324040d000602040c5d103001200303005107070301007615600e002d40e07102d42c00328000503a48600c0a5900100b4441e10755070100184005181440c400c0050380c03807910000300031005058 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 213473102 1250 213471852 213471899
    0x19030608061302130e0304051201050f0c19030506011202040b0c01201b0c04020d150e3105010501030b04150b0a03060e010f0c0e01021006060e060c12030f01150207 72
    0x4a0145c104000c000f150701030b180c0105054048451410914042c02048907240507031020703080032481aa407000140e8545a800c0301c800071406c180a030088009210081c40c0c141000844804000780c0b00702440148040c1a200c0d0080c0e43c0c039941100d0f07030360a5901c0e031a9961983c0c40b1041d4440c4500c0900016078244800d52880c166003030391707006402441d140540c40b080742d1041c4002101c0048005070717031220890131141004c3c3d403800c95880c00c0d9118000300031039401071504010b011580d0003485482c41810b146001c0e0b80d04818400f11601d800d804c440c000d8204454400e21941440240000880c1c40d03041850714486c01c1c04130088002c0440c060510520000303000c682c4030088074101501c203411024580c1042042000b19900070341c0d00030031018407041424003500400c0404004110705020360300584d46191a9507480840b581c05120981d80301c83c0200340c00e401489000480180c000d4000d40c00b03000868410a601d5041141880152800d030102105562004c0f000300541c0340e103051420101e21820 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 213474352 1250 213473102 213473111
    0x140c0d020907020a0c0905061c020303030109090311030c06090f03130e0403110114011401020606030606010507050307140d030c0f090b030603010209030304080a05072102090a021903060806130213 86
    0x41416442e1444000c401028174041010200b1401003a81c880742c82817900712558030140c2807454200000c0a031484010390035400800c01400203030095040601e1f150f1103071a0442d145030380e506041d400c6401500b9480100c0e0130550074054125010022084130b661040c003e1071a14412000101c04807810f0310030301c0b214100c4440003e050500480314111a0300072803000380000141800c441d01c03452400d018010280e81620a81100e5510001d841445000e01800071314250302d5240055072943c000300070840300c0744410031003900041c032142c581681090019000f030030600000000641640e61050404042114180c480500598414900c000b00c40380711100342c2e40d03503c40502190181c81840d41a030b80610002400150b1600005480c14801740560305481303000c2c2c5c5480900194031040e8a420100d10048054035001d80303800c0e4404c580015212200603c0c0c860301d0b03650301410f030703038050a52004a59901c9040190080500040350f000d10049000a8503000d5540000c9440100a03910200c07182c0c3c5 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 213475602 1250 213474352 213474361
    0xa03020d053301271401030507090e100b0616030e030d030218120f030f1308030c030f0901020a12080a05010803030c180a05060f030117030a081801091e140c0d0209 72
    0x11450303501c0340e51190000034840c031510f0483d6801800400c0c401210380c2d00c40c6d600c001030143c0302b81c410203003100e202201424032409484600c102504002c810710f07521403003c00071003841404071401da00e00503101e45c031501103c2681d01c3c00c043c1085068a0325105240c01004001764802241d110180c500e5002c542201d0703010080d01907203151003840d48000015120002d409840c03030b0b2840028000e210480c2031440c041d29111071910b81c4a0040001070985640288502000d03100171030040c100900c410302c1140c103105541d4644d0b9840c0c001566100001c10140e005111100040e806a903000d854640b00661450804038104603003842035a00115415004140c1d12901e65a0411031500a010007400941c9440d0103226070921a4020320030403140c0015070304454140800802540c0321045c0c544c5038040c0e2680e030020980301c0c4803054a03a052465507500d1144002900709a0200c1002c202d041c0a03d0458032540707440400c542030f00d10421403550000d0600b41071b40d6510184170079496410786280d4810f449 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 213476852 1250 213475602 213475649
    0x305070518120c0306101406091008070e0d06060602010c080103230a05011401081c0e060309030c0703030f02010c18050d0c12060209090a0c090308090a03020d053301 73
    0x100043e405074075000711020b000c04c1d06104d582c80300a403178845440c135603886494405c0005c54400c2014440d0010800ca844c1400c20b4060520a42d00c05081e040c41d025081c810400503800c07003840541106d90950f0383c0d01c20303c80b40f642440b0318803c5250b10b044c221169415a1503040c0806030703221910380301481c0b00380c035145460740a1082c2e140c0158400000d00c000b00140001080f1030600b40070396005441380c2d0300d0b80d80740c003200d900742200a070b156a199400c4400d0100c090011030742c001024480944010001c404030340c031081001c100194007036680c401500c108004000e0a6175103a142507000c00c141c1f0024003102002c52181c40e41210803c03504040110312525084080c4040e82c3d01904008c0c96612084042c030081e0f8000f04000441101c48214641d9445038010444085030b005400250140e00144000b55400000b03000a110003015054065940e600283c44441040c0d0112656000000c150305401c40c2003602c1088102503905910700050140c0da4601c00350f5052089001641e041c01d00c0c15940c40 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 213478102 1250 213476852 213476863
    0x140405061f0e0d0b06010e090c090904020a0b0d05010314010e0c0f031e03030f0115050307140408011508010501050904021806010e0a03140d08090a060e1912030507051812 75
    0x40b0090b2161070182d4407030a014003440d03012104a07012444011a40d80c0b54a00400051b1084040f0070106080411020510180c030301c0c01002243c01404402022482d2128000036202400e115a0007048540c150315010510f000d1a00c0a61f00507810714411000510002c40c514603409415209411803001d86000241740640701d4000c0c990440052166500c3d1b99000301c0158800ca9005a0320034030f5980c1c0314481c6441d1070041213100006203050003c115400e11400c400b02204540072019800c00340c444041ea8210b0342c0c0e07070f540701c80307040c80121080140140038041c00780100001c40c0c0181d10351400e5008110030446d80890303d4800441000020410380c064100b10951041c003602c1f2a240d292a0300d4081101d1400b503044210313500c0741c40200c2d42150301c42c80f44180710310750341c802030024080f86075246000350501404508041c0600c40ca22400b00125404011016000f035012030300c0b500028002504490703000e481c0030200081000342040381c0003540030380881c1010540d01540c203821090905070806 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 213479352 1250 213478102 213478127
    0x80904020406020319020c0f060d11030a020421120c05070f06030b1903020604060f120f20030c0324040507030f0b030303040f0605060d06060f140405061f 68
    0x1900c0440c0c0854850360000141c03054a4508400b90422500c0c400141d0752149581462940f001c2080314030400d509040c00544401d00500e040400c0d8100002204c16090700101c95038104c0c2a404902005060b40401d149800c800c527a0714072108001540d00c0f1031020031070705000a004d20090007000c800f0400100b002074004c205003081080f1711a02e40a00a01030000009114881c4908290342c100390b105001028003100e90040199241c24540401501d1050001421f50248000000104024803190040b801040a40c6600059009920b0300111000ca5140d1281c10410b8007030042201c000070301e2007107030b4100b0404900d6840500220b400780ea2032513210300c055901709080c0380034484042c1d010b41045481e465962414403e450111007410341d240400c881c040e140c0d003018032207040030410030740c001500603c002c1c0590302c914440e03455100c1078524507405440c002480101c01c11001c40c044101007100101120240080d081c0f500010b18460000c0041c0781381c1c0000003803480b6045008104c041d0701c2 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 213480602 1250 213479352 213479359
    0xa06140a030c021c0f140c07090f0e0703120816050f0d110d0b031c02060c0a021203070512010b03070c140c040906050a0b150a0f051303150b03010b0a0e040809 70
    0x381c1000100030301720044501c2100100d1203498a144511020724207842201d61800c0043c52843d142010080c00351072240c0b00b03284180d9940c040d00080000c00d2041001460003900c1030703658036042100040003620300500227201c034900044400741d43c80e4000201c51303001840d641b8098803282c1c09102240208102c0042003500d82d400140d01a03000c0c525042105c0425040b02500c900c3ea843d03c5100e01c41d410700140020068102000159070000f541018000e0010244100d81001c401c03240700c17007075070750003074410760003103680030a80298201506d0311040c054441c01da190740c11030400ea000604200e8042d5001009206082001c2c00c410500300f06401c1c034100024020303c03404020341020030040c0002e442e083c1070b10741010b03007085042c100f02d042403c24482c10943c0528020b032040003252401c120030500d10801000b0840103d8100b80034440d00050340c01014580c002500c0c200f008001c4500342e07807086e4080d9060640310441036480c10758031001c03030314a0301c0000311969403460403003818072550500590 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 213481852 1250 213480602 213480643
    0x609020309060619050319110a0303020f06101a030714040902120a060b042313050901050f040206191b0605040c060903050606010c0602120a0b0a06140a030c02 70
    0x9071600002040c502440c01a03c8581d04070709201c100e400c1c0c802c0d650041c1c581640c003540c00c0e6603100014002c80b0814600400c0703110040380d80c001c0010100c180c2030380260010707881018001d0381d200040c81815080344680c040360007020b01d0310603040040c0c10201e280c5907240501000040c0118051488010364010284203103540c7c40e11003982c94000d4211003240088010401e0009011030020700c500301c16075070103a04590400e40741c94981801401c480c01401c140d00d0180061002e144c80d107000000f1128418a4003054915107018150b007140d8004000000304541c2c0d01c00c1c040542c8075601241c05095030103001c0c1b11030007900380090350322007801c0c0c40040c0b05d2440c9003024024009103038803141c0554810300403090503a50700c00041350500e089010180284e00f1a10101d400341d8020b084012181d0303c13072440503080c008030300800c02e144001121100741c82501c2e060040d01500d040813004010f4010b40c00c02d129030fa62242510200c50080e03107090024942d8400851715585d00130800c03600c100c010211103a1 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 213483102 1250 213481852 213481861
    0xb03100504120f030213050d050709090f0b062e1403040602030103030207050904051005060d0602130807060c0f020d0203030f0c0c040c03090f0f06060803040305011a010503060a0b07020406090203 86
    0x1442ea41d011094200028a503603240c80420b4841c0c000c407807000208159003410142400c2c1002000501181d04465901c5812000502800780f80501c5c200c03180140c24022400c00039007410100c00c00c0c014485845146501c580b640d02c15000034020b003440da2a5201a10342c0700440307105450076141007240c0c0500c6003000c0304001c108001c1d03400960690b4403960949104a680748140300d44040e0540f00100150002080c03180c0101c42c95100a90003280144100b000003461b46a41040744e00c1254280c0e0076680b0700c0400d200000041140d00c0013044103140c400c440300d41d039480c0d8a81d80c1c804041c000344540180d400d20020355508000b41c811041c0c1c41e00c4050368a21002a4655950043c60f41c52801035090900c0041002d000740304049840d504020040201410340d0740d42e643c10444000100c5030540d031418042640d18040018001840c030410000640303c001056203000101c902c0380c000c0c10020b0030020814680ca50202c11400c275424103801e251a03030b40510000d8040d110541003020302920200401 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 213484352 1250 213483102 213483113
    0xa0b040e0a05100605040b13020315101707020303060112090602070512030109060807060f08071e05130e15010c051f0603032303060d060f14270705040b03100504 71
    0x20f000e044140408011081d81c44017400203699000382400e510820808920302110200e030002c56001c1601c14a500d2210740312030011740140d80154181001441d00440109600c04440c4a541c1280c801e000550661a06e03000081c21141503040c004a55500c48403c042003200580560720029400416100d00024030000a401904248210601c0c64100740c4001011072003c076141c0e05541d4207980c1c41000c00290700041d0b83d41c1a01801d458204084145507900c1d007500b12000c6c00c592030f1103a81d103175614001c80703266000c2c00a95070172119a580e00c0d0414030010101b43c00001e04055001c0c205660f290000d8200380d814513068590ae0310b80001c0c01c50b0b00c039803000b0740b030340c0110156031194440001b8000640c40c800103601002c0c222041e50303141007011a610385041004003505034031551020603072012070800711741980e40d48207188540c5014001888140302d0301e203040810382000340f01c610800e0262220942d030b4070640c51240c54040d41c1e803811601825181400a00100c00d4a01800d1040d401d01c0d1505 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 213485602 1250 213484352 213484363
    0x11505071a0a240b0306330d0c020105102106050906040b0f070e010305060d170a030606050f030408181f031b0c11030f0d030f0f05040203060a0b040e0a05 68
    0x100a03c3c1d018a01480e540c8040b82e42040940300c03404c450034215034410f41803180c1d900550040303219500e0024010b03440c3d041c1291450070f560205c03403040ca4039401800641016a28601c0010b02564100802c1010000540a800c412a21510749403a08101c00d1250440c55180c0f0200140c411401e042c2000498500028124080d600c91618010749590b41000c8a42c0354105407032010001d0800b131002e5505d9840707a00700540040d0010424689000d40b80d581d40b04010285103c0c8030804800301e05d4a070000d03094407400b4020400e03828510b16080f4003941101f10361100800c0188a60b0000c2202c3c80000e038042001044024050510f03681803c00d541840c01001d0030346051000641446815140030680d0440e1340b041c40b0b5a0b8a41c8825101d2a54854100301501602d641c6c240c45072010180030071a0801c00e0902c1804540c4000480580091022041c2c1c0c5815003042841707410311090000585001801651110f415040060390001d001d00040181c14140c50300c00d56842000b0050060003808a207 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 213486852 1250 213485602 213485621
    0xc0903070617070c0f020922050a021507030203040603020d06051e0f04060503100f0e03040608070816140a02010615050d0609050103020a0509180d120f05011505071a0a 74
    0x10b05140e9607402c50204c562403990b0708000d100004010340c510041c10545290b039082034096140c0d071344002501c500b8941c2e103030811605a070039074801201081542802540c2040c000000d803d80f40c500411614040d40d070740708502c82c5004140d4005018000f090940d4060f80141c24020001c100c1003400f10142c03200c0f030394820502c41c41060310000c207248915143c4100d004450024000d00701c010000002c41c002040d141e000c00103400d40b296111107508000748000c0019100c40d8441081c40e00f0719602c000d01480c1c00400002691010020b00c001094000c81c400380c6428107000ea1030364030102c8240c12805004280d10824400c42800c0800800c41e401c00040c0c010081e840404010709980d40d003104003540c20a120194200d10034040030b00c85410041000340e8400500740a8ac1c4180c82009209803400d84400303082ca00103200e5003200481c449990240c15003070f1012010911182d410000e0042ca54441e4036485000d2003000a5402d0420a14032103030104080c0031555400a4600b070180b000c060a800c48 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 213488102 1250 213486852 213486887
    0x90d1203090b100e06061809040f151b0915030209030a020411040611031309051503060a2708090f120a080409050f0403021c11010218040e060103050c063603011808120c09030706 78
    0x182c180ca0700e00d1137082c281d02240e0043e0350307510386004c0480b0190300030740c0301040841d0140136421490f00541c940f0301401000c074605c00007081d03070360b4070b841001403440f942d818254809800402a01240010012a00080d0b0708001800226901c61003041042c0c054020405501030080404200f03140d00203611000020b0303050101840000480c004600b10000d03038050082c0440010f0104a0701402c1501020f10108000b5060000e0307080308121903071500e01c0d081002c940b1031000050900420096004164100d4044100451a402c060307801940701c6d000300303a440340031394a0b0000401d0042d02c01c903a000b181501c0c04008558840d8111803003110100a401c85070300030340c18800b022000401c0040c4c040d04036034100002c0c2030007110380344c20008158040c408185444101d80c80d00450f02598070101c4da2050710003000046110704540516081d16141040348071403002c4161000d002c41c0c6080102d40c1c281143c800818050313903c400c5c060805002c2d100c00c0d41d070103101e603142c08204142c000c0c800044458200 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 213489208 1106 213488102 213488141
    0x31c06050604090b0f0405090a0b06040b060408070f0b03040512070507050a0612060b090d020f0d1415010b090d1203090b100e06061809040f15 63
    0x160041c5004998810121010386000040445c2d050f6094400b07001c00d10300014515180d03c840c8030007030700481106000803002c0c0c1d01c9134889480b01c000288102d445c0d82c1c4400381c81d50b90310300c03501503050409010140401d45106d0315094a03c141c2e403000051840c3d1f48270130440c040d81e4001074000c40741c6201d41356000c81c4581d40c030418880a4012a40c1d00840403000e28150025100c440d449513810f1358041010342e01da5150b0700151125960155401c080f00c81e80e41c004920f00c89200000a00740d00042d84034540c0e49000424041419250102d101080d40d03210b0188000c01d01ca6580740943c401140d58840c400910b91120b8451403003002d04001035086001d0b2202c001d03041c0d0440305205440d00b80c0c14207001e8030710407002c07864120009880907410700c0d41415200e00301c40319040321580f141d0983c0000604002c0300701010740d0400e83c4206240c0c80e002844100700003900032440f04e14015401e5 = true := by decide +kernel

theorem cover : BRFrame.Cov 213309352 213489208 := by
  have h0 := BRFrame.cov_init 213309352
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213309352 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 213309352 ≤ n) (h2 : n < 213489208) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
