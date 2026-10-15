-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4172
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:46:59.604791+00:00
-- url     : https://prove2.me/submissions/407cbab5-76a4-4015-b0f9-985dc178ca0f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 750179856 ≤ n < 750359712 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 750181106 1250 750179856 750179873
    0x1017100e1606090b0304120309051024050307050f04091e030912120305040c1502010509060702010e1e0c0a1404060e1e0604111603030b03060c18010306150c 69
    0x5180d0b500d0000c80c0a840c203080000140320161018194125020740042ca15009801c007420250f40a402c4440e41420205900020408229003610302e803140307040418100c2090682c0d2098038802805130444038a04000c214000296048968100d9201c010070804518886d504c09090303141d1161030b00802076070380340c01000420190404000ca600d121f00d090007050700040f203050107000030f041c00204e0b41c99905141d011041164480c1c0c05964543c0032026150b0b9040d04072501804040782114410b44644000ba403c2e14405100940f06600413441078080188500c0c2118000c4482c00503a6402c00311400403415142150304205080710001042003920306252080b90f00400444507124a05c0c24409800c0c0b0a00c4908001c02c405505114045603091b0b65a03407115001000d010440e0380d4030b0b4030410078081c21007842c16040e40800e240c42c0c0d6017552400c000c182c052041c00740301075862804004200c0c1050040c0403503c0c081c10117968a801060007070004881d4984005991a07101211445190100c1c8 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 750182356 1250 750181106 750181109
    0x112401060f0c030f03050a1509020a110c0d1209030605010b070210030c021009030318110a140603190905151006030b151c1a0103141017100e16 63
    0x8212004030b110b00860b80c82500030101510354540440e00c2c0d214640d001000d0582c1a00202801c0460743c40000c420721154000c026a001544a4100240c68032005035103d007450112580c120b00401e070031100003242c07081011003110032410500141e40d200e444400031108260002103204600007000c10943c640b03003c11500c801c41d5450300340142c0c07040fa20b00070b403503400018681a62540316400403080600a820501d81c111550a00703180c04002810b2003460341d018071407605d0084000d15004144081c400e02070000b8840b000c0c25442c074603220204851002c81c8040001c120640d6103460341c0300000d07010300a1b0401600e5000321050075080050158960b80140da000d542854a811041034480d11400794098400e074115400c191100c0300d1040102e541061030801310240ca2030450203011038100c0c00c1c00072544030002e03a01082000449d0089452458064420600300e100c4800d0400c00840c8000c0050741c40da81c100c1c15510a00030308500c4106440303000710b040c1e005400100040520104107501c010 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 750183606 1250 750182356 750182387
    0x30201120b0d0308100e0c070614070e010e15120a0b0109080a17131d0c0405010e040f1e0b030c060703050a05131205251511240106 58
    0x400c80c8000014050320b10480300800b884024000103101d25004050b05000305148600340d1030034039042082203690380c007540d021500203240a885403d101ca21040003403043d6405d8a0b00422050740000555000005000c02e0340d0049001c0202900040d121016003152411550a005982802d1604005035402c02c0e2000b0f0400403101800c018020000491a500c50b81040703100a0100c42c0030301c408814441e0281d4a620b9a000301000145000a100c00c1d01c05580001c0000d80340c0e44460b800d500d0948168401c542c00142d86d181c040c0b082d0b1502d580314040849003140d000406c0703551a507502200075030010400b01d1566440050300400d007801c0c0903e80b0020001c0711206c0c81c2481c0350760301130072a0140b01c162508021000c1070b1540802408000200a00554281d1280c851401e01d8100d564401e41003000b00d1000940f40c00d520100d0000f48640c0a860701402e18090014010408942c141c044808400c96032003070000300d40070f5540800301d8101c544c0e1801e5844441e0b60501c2d001030100350440141c81c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 750184856 1250 750183606 750183611
    0x6050604061e06110331080d0c120e1e120f0303040f05160e09010c090302010f030e0a08030f1608060f04050402010216060302040603061d04030e0105070b1003020112 73
    0x201c0341c10103100c1e110b80956460307090a0810078490090f2900c0d40c015094500b0030f955014501d44d0003a1840c06200c1c41e074100307540340c00d00b043c2c1d1100c2c2102d407948080d280079000b01b546070b618500020002e03500381d51003226070700d481183d2291040000e90340b10090050340d00c1024840c440750b00707582404007114002c2e407a1007005243c2c2030540340d551a0780b0720004001804040c440800700d41000418040714102c0d005d0324084907407445d00d52058030b0b01030100b40e441203501d62801a070b4422803030142d000c6004503a0140c44002035255584802d802514098010f019039006c0c1e0410000014034040140d40150700001c103211503840e04141800620324524606814000e0400401042c2e90343c1c005000c00326001a034004c03c1c543c880c0c0c8010303481c01c0308540e0120541c4180e1400812141d80c15400380086a2050340c0034030181e961003c1c241340026602216514000d541000600400d001e40d0440500e480180751240c5480e100762682d441080c016a038030303044258800c90400c01d641e4400d507810701044154004 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 750186106 1250 750184856 750184889
    0x3010f0b0a030305160606080619200d060e180f06010f03170d09050610050604030c0b1605160518010509040b090c060a031b181811070605060406 64
    0x1410100701444001e0812000040f640420f803019610070508039031010301401420703211741215844031401c4032000c060410b803107942c603001c411901403611131803450070ba41383d00c0003100316058209034426920480740f940c41e100005030f1000303582240c3c0c5c4100718071030322006000c1c1c03800842400c00c410303010f903440158085c20041c08103820303800c4c1c00c02c226640001d804141a1901c080f1a9960140f81c055812052521070a981484404180d2034400d106c1e05502c0c0041c9170b01c5404001c00d900450101900c5821300117418816202c0807001040e80340246100000845015502c4901e400c110300307441042030700500c20030131007401c10400c102e64600508422001d15814900800c5d003a04000304007500c410075900104031110b0b810f03c0200e4000301c01520465844a1450000e0064104e501945007040590315110100301c0c800c510015a01d802c0084845010b4944010308264501c4094020b0690b6650310f000c284408444000b04640782c415040481e19243c8201080220360f0b46900510007000075211 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 750187356 1250 750186106 750186109
    0xd0807020414220302070b121e090a02040e010e0706090e01080601140103021305041506020c060c0a032105010311090a1a1e04020a0201020702030d020a20010c0c09020903010f0b 78
    0x119628255441600d56560020311300f0300f2481d00c0780d60f40c401400340d14009070031091120b4529201d48070703051a0040c10501d244200249028003401c440940f66908070b28080401864141c00c007040781c51140001144981030600d490340cc0504550042001c11503808041010f5503150480e140107040ea080074020315032410000140c07558030b42c6940c038100343e1b0004103100e10307000c4406140302919010b042000a011082c11103d03144411340100d00141c03080c0780c1c03030102d0780c5420011581c54640301009010703070b481c01e40d6081d02e541030040038004039030038000511010a031940c441e16009500490311740580803941000d0041c0b83d0300280c90700c0e07001c60620040d02013840d00840c2d5510003885c195801c0d44511503800351400442300e1a0801c81c1c1c4a80005503101e502c50b41500a0021980201c0907944810301e00a0140e903030f800d11441c010503042c02c070024801c5210f07821000003a030303c0c810f0400745480081995250102d03c26600504c0340d599001c036000340c1c01e00342403092400c2c84080640c03c010001c031080 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 750188606 1250 750187356 750187381
    0xa051005011a1c09030906090911121008060408071703070c03050901031104090c0f170403050f0f13080735030403080c01021806030606090409020102010b0d0807020414 74
    0x14484080e100c000030120f49603106001426180c01c0c140d41e0400109a8524009149054910a140020300041c0012806001c43d00c034594160400340f000600c0c03c0344040e03440c7d000f9000280340c04e00f0b0290740c050001e6608030030300c0b1b120710483c8613440c0380d030b5036905614040036010180c1c0002c845048050040151998104042c8030003d500742c20b259440e1080740004034054191050701c100a8000410002122500c2d6048030917102c40c1c0340c031340608021803400304880e500c2880ca0040c030030752045004540880c0c010030003001d21002c0394070201d01e031884c41220403029900c0b9a80c0d0ba1240d060001080207015014030401c0042c150010403405c202a0546032a0742914010066104807001900304a22208042040f2002107030301081081c2c80d5a010f01c040740c001e4101c40c029481c80106040c8510b13440c500503003105d1107140c0040c005801c000b521010700004050507602241590750b100407051140e650b0501e094107840c420301c001c0d66235146a2060105880700d00f22a81d0320a20181c0501c00804002d0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 750189856 1250 750188606 750188639
    0x1d0a0606140d0e28060c0509100509190b0a0206010501021b01030e070e0106091503060f03031d040204081b0f0f06070c03080a0e1c051b0301090b01080a05100501 71
    0x30400030a00000c5054407130300b00042007201042040c036101076080503501c4807082030200c9026280030810800d9040d429030707252003402e17003640c4e2024120095040d12030080015009254010f000928940410138101601198540280040f00300208180000c00d604000190142c80300b072004d4002c0c4075051050403c0840d05500c9a0306140d15409040540b40040003000c0080004070080001541d44510150420225000e40500a81181c58882845009015102c11204005404a80350b80307141c80031280c007003038591000d05150204074480c485a071540060400b50296801400c10f241070841d070541c0306400454018040d80302c041c00c82c1001c0c0e4640c3ca4004203400300341e8144d5913940861400c00c40d910038682009082c21000b007907100e901c1f58030080742401034200b81c400c0c00c0c22600b0305460f03403403024914100501940c4444c0c0b4031314080442110003481020064008211116035aa070240319001c02d0308800c40d00e900074913031001400b40410020340200840075040016504003100d815990014 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 750191106 1250 750189856 750189877
    0x140310050f0f09570316050f0c0a060b01020114060a0b030705070f0b04020f03031c0b0604121a010e040b070f050c0a031101050915060409020a1d0a060614 68
    0x441c00e5840a8100040003400c070300042c40f00c0b6001303408040c0d43c0704c03070040c04001110309909000054180940d560440f0b0042e0301c06011046148202101114958450f02500185480500100802c90b404000c1411854070441012a42c5081c1e00e00080c00c50b81041c1c5500e2184101200303120154440c403c1d2030042d614944c0c03006a4941d0341110a643d1842404002000030b884a00f940051101907103426020303c1c400c07940300c1014440101015503034010003046070700d81000001101c4401c606d40c0d10811a80201074003d5083c103507610303109182c82a035071105035180d50000881240c0f241180d06102d001d0242c0251440440c200b94448140c0700100a000005100701c3d040480d5400f4040c00550329071074400400c584884100b40740c00cd0846040442910316582005c0125801c0701011031034202030351011a9075140b96a4060400000c2e00030000d099802c07414501000c115404a0b060200c0308080c08a220320881c105104071804403250b90344201c08001a0140040d400c0c0300e960304680310001c1 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 750192356 1250 750191106 750191131
    0x1b150c0807110d080c0c0301110903030919080708011b0203041d0403050904051317090d031206030501060e160f140c15190f0509150403140310050f0f09 67
    0x2402c000c00c00400c00c00c0005040381c0004104007840c21000540100b1824080d4002e103d00e0030001d03090452405010131541d4103030000c0c482a05542081e000c110700c40c1200c1c2e0000d900d0ba0b81d840c03940c02d0030030302030f45c0050803e07944900d01800f640580740703142000c0c56640d00c020340c5000e01d48a030030381309809914004214001d40c0d4001c0313414035200750162500100c0080003040741d4101700e41c00300100801e0780000c98416000c00340b0360310703184146c000ba034000c8407020700502c480116940c1c0c00c8492520300070314204204c0c0c2d50b000100c0821801d02c2001d0141140100105143c1440c1110080410680140c103041104d100b41641029a01200300d9a6107105110842d46545100a0a504000881600103041c814080800c500c1405020001c400d1000f072100c00c00030440510340c058103803801101c0d1140194440031030600d100c441050002e500a0103464801210801d28443c049150320076159015035040f01e9605004510b4801040031621000721074103400398108602103409082c0041500c03a03c1d10 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 750193606 1250 750192356 750192383
    0x15010507140705130c080f0108121b0106031202060f0411150702040c0905040b0307031110170403053a0e0a230d2a0f1b150c0807 57
    0x70320802c07480001e0100240b506015034441c1000c0c07402001d5506000b00090030b4003002c941804660b1840c03605031b890440c064941c6910340000414a40e00035004010588000c8001408200080c4210006540709005a082c03100810b20000e01d041e4018100f007649450000502002441e500d1a1007502e140540c9d20b500c07001246070051029005885000e5002424040c00e0aa4198031400341010f80c1d104440400c1010812028155502c0882c04024500da45009c0502140d2801c02040c0f00003030f115280801c03030740b10010a000052001502c04a010420105003c8200307198079a40b901c1c822801c2e8168031011108840010120280d109202401d5030340e03404080d090107090280454035034111104d41e460340b00c15480952682c5903a608401c0794010802c0c800070f4188515545000e011102968540b44200d100740040b01e080702e140d0032075400803014040c1000450007400b501e0003084421a4181c82032a1003005101202d0058501e8200816060742000044c003003c1034504881e0440301c09400c20 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 750194856 1250 750193606 750193643
    0x7080406090305040503011d0d03020403020319020a0321170906130302031306180b03040203070e061c0b1801050115080a06050a2907031b060b130e0615010507 70
    0x1031041d40c110b6034055088c04451050449201400300ea41d0018204944510089c610110101d0085002c000c2d410f412040e803449228054107660b4408a000030a02e02099036241d6800e03210483e200c1408003610301266000f1b00250b0000f00c0f0440c014030b121595244d074a0120307251501c9080003010326168604d203500160501d03108005449001c01c641c440700515980362140030301150308145100f151000401e00110300c3e003088400b035a0003142d0180092060038208881c9852070300000f40006d4101480d091703941c5040b24040040424070f130041d200c1003640d041256140400390080c51100d11103a0403c401086045c90140c04040c49800501e000c1c541c6441d448012000382c0b00550100d507100e400c0700c2c0c012540404a01280e402209c41501b2510b5492013000301e200b240c0030707008002c0c0101b0b04000794111741c3d07040c155081d51224450540033611840403000103c1400c91400d50480c1c29030383d5003444200302810480d442e003007003c80050b02141905440020440e1040440051441010b03000c2c1c1e16a4 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 750196106 1250 750194856 750194867
    0x1511070809131b030617120f0c01090b0c070618030e0d02011b0b1009060602030d1a090f010906050d0210030e190f060605010c03120e031c0c0e0306070804060903 71
    0x10344000e41d240040300f40d8400200a09110700502e01c0c00c9180c0c0c280d03008501c0700081c4240201c81441222030420313039803400e00740803034100d107105032415520381041d04002030340d407484181b00b464006e44694850b13405040a5003110f880d00f00c1c02d040b40301000100740102750403400d0303070403452805c488211224440d40300403500541c51000c00c086100d21454400100040095661707c20980402500348541d82c0c0c802103006e48500380308080241c0c000308054801c82e50b0a4003c1c030040e04242a5880b1182000b001241d4283e108580850f203142e07091006005482c40d81c051400100001c441201002c03038180c0018030400101d204c0182816a204242d9402e00070a20007404840d200c90604003032120281418011071142d2070080703c406103401c1d4046040e48c007a001420707166800d030f5a40c07060a0640c22942000b4900000c0c0c0080921007401410329030141607000040c1a007130f036800440c40c141c00b460f001e130401900300c84440c4030ba00b004c000c00074840d9000d6640ca6005070048800b1520ba00581000d603003 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 750197356 1250 750196106 750196121
    0xc030c020f040e0313053a17193002031e01080f011503050d1d0a0b090405130f1203060306050a020a0206010509100b0c0c0409151107080913 62
    0x1070f600001c00e40200f1090654409000c40e1400e80d075542d400c1da030441100c2100c0408101c6428000070700742103d0030000030b02c1110502e140c8182c403a00006040c81c05035070410741244410b200e02ca1104281c2892150703000e10038188201601419031040603d03c2113415004040d03c2404858950120028103059541403140d0005070425042c0072084d41c56680064407640442810760940d03080104400154080301c8009040302d070010040c0107d2060b22108030340c1900385040806244032107984542c0f40d80d8400d51444010b00b01d134000965207541c0e91086c40107851303005040041c2c230b448107100b100100d42041c0690043c664003005450001d0302542007034000f022580c00240106145c10704101001c51b0701d600500a04000b502112080da980d0810821804801c80c0d0781c0c5040b208001d41048940342020251030100a00c005483e121f20102e004142201e00e03601041d0781800154000d60320440c5e16108481000c48a04061450240c0d00d40352885980301d0b580c44d0320700030314110958140e402000d42c802c01 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 750198606 1250 750197356 750197381
    0x32030d110d0501060210060503070302010e010e031c020312010b031b0f0705071202130c1202090409020904050604031103250201051204120f0c020a06140412030305160c030c020f04 79
    0x707513107a0360000d66607030f401ca1100030311360703d0600049902d141c001a828101c0b41c0c1655410881c00486004542110301c5010480e0180f18440d240d0328134002c02d0215440842296008580b01d00e101c0c0e000e084c0400e0306078820416450200180161004041326443c1c00b6100c0a10a80d562041c00d541c0b0a624442e03440058024019902c010501078840c404039920180200c40c003039105003e00c2070303070b60486014085140c04940c07000c0b6034102800d01034024000d815001040050304484a801003908000112822101034000c1810441090b0304a4161015100264000d60401440703000c0013800440d01107800081d031040909001c1160b12400803900100700c42603c0c035025051520300500c507080c2c0040114045140540d4041c11070784a0030204000b1030700101311140651034282c0a40c5c5400b50320509845160307003044082002d404080103010014801e50340003d8600e0321906104103120580090b84c20450034546280120b988140840b04180d0101c5805c000139202c0000280202800c40e0200e = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 750199856 1250 750198606 750198611
    0x402060f0a0306030c2408061206040503031015090302010c060f0207060b03060c0708070f02060c0d18050a03020603191d07080106050109050d0308070e0d32030d110d 73
    0x11030749540e1542140c011284a62280003082d611011842d07403260040c0b111a4444c24000c903080e40c40b9124079a80c40d0040d02c0541203001211141c4840d070306000c01100c05461b82c0d840003003845240ca4414034030030000c1450b080c0304120103803130f203200814508242c44041c3c108807038041900c040c45402d0344204820000800d0441d611b444c607181417405401010a1035219000c4c00c000102c5e000c151034200d403413103603000261618200c010303524800b04210642c000ea820420078016003404071410048020f00000d140c568200350300c4907410000325540c560708454004d0550950030070040c0c9071a030a50380c019002c409054051400034660000419100081110062048038445902d103008500c0c038040d00c90600c000d100b07968403140152520078581c0314190b003024641e8100c40109100d49078954201801d40b07000c0780c26400e8200050200618520140c0300281c8210882c80074060402401204c034088203401c640b0f150b048407156480380070310900040c03103c4c0c0f81c0400c006248501000c564501c80401c404 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 750201106 1250 750199856 750199867
    0x2703011b0c113006101712030708040b101203030f1b05072f0904050709090b07021504050705190b0a0215090a0f030f031803031a01030e070303080402060f 68
    0x5201c00442038a5048407142e1400f000b404000100707681e07104801c4594850540d074035181003900342040d032120b044003078043c041203600b05c0481c00d4011801040c865503560403030f08180c100300c5007030440600032540e08003c5440c20840c0e100d040155960180e0107080000d07a021310001c00b54054444810480412020007e440c41c03001d411201421810b0f000d0b0007071301c1088401d0f840380a003051201503120700c45480218100303461729054000d42d611512801c00d907003015a13600162030540f140184102c89042c01041040055a410000c5402c0741c1c031076030401100f504054440da5100c0402d4055280a41a12040c100c00341540d00c500e54010914990a40d640e10442c0b2402901e0705800b21800c0c88103540300020071408080001c50709811500404851030b0684160340076902c1119021101c000d241e15407144440f80b1003c0d403010f413003060203038030003050002201440314940d0b10b848181a0500d07140c401e42c00200307400021b83c0b000b03030b80d070504000340c05440e2400003c523940902c050380c0d140c0680c0003030b0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 750202356 1250 750201106 750201139
    0x6021009051f15050301050c0304080f0f0a2321070203040e090309011107030812062e0225170a0b0403020d0f0c260d022703011b0c11 59
    0x4410039002c03e0b01400440c01c0d881e035082500365001038078a80150b21040c404100130418440080c080900400c600758038140c40c6081940868002c1e10b4880041120f003808100903805510569485542080c1c4962600c1e800741c540b2a8511000c1c07841c00c900448032000105024000c1044130f001d008159400404e40c50100131207035486e4800c00d01240003810300c10464420001c00103003042641d43c06840c150400c114104140e04000004002e40d50011520000041c20f000c03456401c01c1c4400d0b52034403041d40324440c0c10082c0c506070102000381c54200100704114504000b0520302403c0d941120490f1450341030041860780340c200d0500026100e19002428002056000078454420540e02d442d005035224080d4800d032800c40000340d02404000251040400700b80d0750150810b81801185108c078140002c5143c100d080b81c0108a01c561241c2d00040040a0103424120210340f851045000b44000410088208000c90541c50030106001c903e2204a0400009060300c54004401506106481e0303500d15 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 750203606 1250 750202356 750202361
    0x1e0708031204050d020114070e0307121a06120705010e0307170d0212070b04020d030c170c01050c0403050c0607030912060504110a030b010605070c0306240b0406021009051f 76
    0x6408660504c611914540001d0040c010f68520b0803000c600311710241c2d1583e005403107003c000b0f5a8960b0500030b0000c04500312102048422015020308411800e440e400303000403844090282200340f284094420b10300a0080000b02c610070741d2000e1802d101051000008a45050b4150304948800c0d003806905441c40c88000940c1800c114085d821a40c0c035415040162060f07101d5001c018040000d154002000b506102d0084201c5500c603160005500d603064417050310f0700d10300380e010f050140c400040b80200303d0b00074003a9581041802c0503183c541455540d900da0b0300c01440660a02a40d004250103061500603421003004103048104000d03c4000d0b8070f0100010310b4210b07000c50300c4041d540c4024030302d030070410394000c180c136440380304114281d0806005680c40c1d0001c8404036004406c000000c0300203103940c012404e61344c441400441b80c510303032411102041d0340c140c1c000f0040f2240520040180307680c005066050030030403c0000078070318500c0c107000d810445032000200c5141c075440800501c40f801d07503 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 750204856 1250 750203606 750203611
    0xa110709090b0a051509090c13050604061409180a0602040308090a120b0c180409050a0c0e0c04091d0f1f1e0e0c0a1e0f06021e07080312 60
    0x400c81c4407280d6541d060f90314101c40c0103072008851803810b0398002000781440d88500340c00815200c202e07007080480e140002d2100725594070010105840d801844039a0070700b070049a015102030111207024140e281c0224052041c02820544540361602e00340004440a100380050260840c03c02d560f2a516410004503903404049914000d00b0b0b100703400604044180351000c015503000907012820b840da4400c02000c1d4200b44000c2800d2041c99481800d1a500c2d84503034100300b4803501c040c024142003804d00f6400200f4503401208803001a204118003060301a04a0782900c0440c1000209030512200550020001001301a0540304840d048903405000140314070982544d9580d026801c5031407403124055920961110303c003001311442072210040550030050b088075060701118032600e907001c00102c042246030b0140300801c02c00103020710b00d080c1c90f2200101501380000c10070500b5162050081d81d59101d610183ca41407010704490b451000c0c00e1100500920080d000c40b0780320100c02649040e400360a = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 750206106 1250 750204856 750204863
    0x408040f06051c1509020c0106050f101209030c061d39150a0503090c09010e04030c0c0803180102010e0d020a0b1f03060c08060306060a0501050a11070909 68
    0x110240010154868011112040f1071403485802d030306030041060019044110815003501c2110f000860ba5101900c050f1400d03404d48400031078060314110522100b24003284903140180c1e594501c01c48250b401401044031280200000910f11407681030032580803003a180014491420450051020540c0c458440c00140d40c44003030f298541446502d40702504040b4400448801c605041d031031002041855400000c1400382100413004c14400c100c1c2e00359031003201203101141e404014400b1928013008001e58007a420b4035101c1c003550400c01102007102000348020308004840f00d441b820040b14894020091442070304894560010b000309855041041d50709034011f40c41d102c949000c10200160009205150f5000380100750502d85070481c1d45e501c02071000b13a00aa40352108a941c118803020603000314000c05000401451088008190003c0508080d103c1d50086040c00216500d1354201805c82d002400c00c55035500b641e44054421064400c03041d450740c0500100042c800c62245c12242051f8403 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 750207356 1250 750206106 750206129
    0x9080f0304021905100f120e070602060132030118030201061505040e071803080a0806181b0315030616030e03040f031104020904180c06030b010512130209040804 71
    0x654000c0f02a8140c181d1007081c0e405070203040000c14403402480020b4400d0070b00d14007031600c51002414201503940b56400d40850740d12000301000059070500c81540903040a2502c4104c5240300d006e0020b0f00d61030242d810b0121081c03c601c45206503000d50180180041c1048000190051810064002e111038030415600d54052403c10070741520420448090700c800b41a0590a80c0395158103c4039440804400c1884140016001c00810740c584050290b407116542c41007000d160540902010005401102c0e645208003024080c81d01440307106069030032940360840341c40c2d0f510801148a90141d8000c080c2e0103004103014844000b40d0b85000b0340180c002c0b81c8051142500400c10f003542c0c2e114501c5800014540f011041c030004803080b804400000c00103101508000301400003500b2035074800b040f054003590342c5041d11b04000e0800c10200017004182003c01004182c840040c000703114a20750201070340254400901c40b01c46900341c0388030342a0054084102c0e450540f0b031a2003c1d52290103890149e02 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 750208606 1250 750207356 750207379
    0x702180a0b030a0305250b16030b0103020f0712050f0f03090f0607301a01020c03071401050f07080a020a05150705120405070e09070315020f030c070609080f030402 72
    0xc0005001903030584c1661224a4480c044003442c10610303071000c0031001c00d001c1011a0010030440c0c0c0b02d05000d404411248680c244c48004d0140c1140c0c204494070741854010310455034001111000e450551b0303080025008a545081c1c4101c0d07040c07207560500c80e901d0402140d00c0d8064102070001e14400c1201d00300f211600c085d05543c2c030340d403002c040758001d00080c00054041212094400c03026010300d035491040c0c5103c4130720102c240503506580f0035020074501e820a003058a40c1d04000704d00f68610b080c0c1c05400010b003404180460040c62040207414060001008181d030030002044580d000d0b000031f000c0343c480101b400c0c029100c4912040a44aa100b02e0521159202564820703074007411494403202d01d05941c0854062091030002d000f0345140c050f01000082105d07004403030520550741000608400e0b030552400d40704019461204003145841809903a031911007810450703030012210f81c0c0c00f5440300714519000c030240003038080090140b00302040459908219101450045108132048120708 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 750209856 1250 750208606 750208609
    0x3020a0b040f0902070c05060c010f2a03061a07080d2f0901020304060c0f0b010b041e0503061315021201030605010b09180a090215070c0b1c020d020702180a0b 70
    0x5d00403404060f1441c14103200030003242c501140240700e0070040000100e00ca10340404d4a00071607090701800c3c55509a0030001d07030030f074028000f910180d80c802402c00700000c604004801081c0000b2055000c040c040c009410030901c0154401c0d100011103100c014044256110111012505401c0c48800240000902c403442408040180d5100031070680c021820070f854900f04661202c41070f82c0c26102500012241004540302c0c0e00058040c0016541d6030703640e03901d80381010800c08410103001c800011004028000e6a501142c400e401258462107000300240c076040c0340e180304206003034200307809200040c501c0c0c4c500300c0e0340702090499010b404100400d80e41c81c3e1030035007640b080c400c40135407064000b1404103e110300b5503c001c1c1c001d071001a00280b80509540414054001c405204e55900b40210b1403108202454812030f001d400b400800c54104040c107141f5045241c100441000c009401040d1407002d0003190b41a00d00d20754008152900110b80310003040d03d035103425a9002041828000c1c1002103 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 750211106 1250 750209856 750209861
    0x130f1202101109150705060c0d110c0c190303021b01050c030d0506180702030703110f0307050c1903121101140109020c21160c0b070812160503010b1303020a0b040f09 73
    0x5c1604800503014540d9210192440e651180c605143c41075654000c00c1e07401c01c040f40c080d0908041c030301c2c000d20f403002720b6008000210300314028032000301c50b50744000d0000a60119899003c0c0802441d201145203000c40161014000c90340000d215200100c0c501208501640200d40526020b6500360304000707190040708540710b400c4035101c001d6401003115a0019110f66444103c0d446c00d0816103486504066803281158080070090790540c0c8091105a0585424210030f41014075500300014118555502ca1541c2084803012a05101500141c1da8031100e0a42050450201e501d81e405070561312071640f200207400c018450782d0940b29040c00ea02d0f1150000035880311a00600c043e0b2400c2014001d2410170b00880150121014400001d00003018820280a82151481100500d1712004104804012003200900c0345d0310b1100030341503400700a60083c1c11a13041d2200315903c80c0c1d65030040b00c4440350022441d0303c000d4021005d4200065940a41406130041d201908820503500e039030f07110000c05 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 750212356 1250 750211106 750211117
    0xa0b0405243001090804140a080a020a060f05190c1a01050109140f06040b30040204051e24190b0702030a15060e130f120210110915 58
    0x42180440318090a0842c9036102c041c1c20a12160000c2902e9019a50f00d030311a03080350340500701c07280c8101c03003184681c60011b8140380501410780c01415110b01c0ca400089804174144a045c05104500d010350f12650b00c00c07012900541494001d01c03150b102c000c00c00415505176000142c40b411083d0904000c2c0a62651050303040300c005940356590107060a0002c440e849810b41e41941c400c00d6400100003641358900544001d0501c00c10300751311026100154501d5403e40100c8065940e909a0b100c100e00144091884d00a40c041d50001219540c0610310550b101c503902d5102c641c00c00340010003c840c0900159801c0c2c1000b020408000e40341e03944280019023441099007208110a0314090108030a55009003000600081c00c89801d10700e6500c0b100803031f8920140c50b041e400d440750411720500484c00c0000e500403011039114040b131019a00c41001d520001d5070000c100300c0c0310800701c500c15031080101e02d0600701440b00400940d04050f50a20955204a1a031800380c20116242609090380350103544 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 750213606 1250 750212356 750212389
    0x903070b04110d060e010b0f0102030a050a0315030b090a0c08150a0e03090604090f0507080f3402030c070b07020901140607120201050403030501050405010b0d050a0b040524 76
    0x504640740da9681d80380b0030340103254070340d002040708940801040d01409500844410580002815540b5105106078101e8120b65a415584100600c071642d039404021200c404600303140000e07081d90311002030624003060b6800a01462200c02c1400248000070401d895414843e001c0c10444c669a002c41d5600c07071300b081c1c2d03290500501800c00030785581079a0b08020b003070301410390a880ca0300302400d00244076900603030801c1989aa8854000e91b8510041c4102c54001c00141404903492421000c0c5821032a0010b0111985880a0240e440b26892080202c0b060103001100385080810880000750390780c00801d02007481d842103000c001140c0c1419000c0304c40c4940c0203000a042a03080550f407000b01302516000b143c012030304029100103e9048410b0072a003103284e500101e0907007040e040080c241d540c103800c40e9105a10380401001200598011100344250020001c0b0f4507540d01c2e01c07070701c00400102c0e40054205040008005900b4401d101709804c546098440c0f41c0c5036020300c0c05015000d03051107481c0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 750214856 1250 750213606 750213623
    0x61219030e030c1507050105090102032e030b0c0903010f0606020c10180e010303021515010e04060f0b190f0c11210723100f091d0f090307 61
    0x6802003407103000ca8200c648400b038101c0740030000d000081590a0003040540041c0c070340100c2c4a10400c14207005150f0001e02c000025425802d00303885016103200340741c0301c0b04401d00101002408942200e6001c1c4000c0d500110600120704c7c00e40c03d0030501da0b00070651039120b5464010019036062062045400380d54041e4003c11082103000c00b8130400b81000024802400b41d10010516441c40c049100300c0034124805004c0c41c1e0354914600a80341098042c150007180038948100241075600c000d05040120302407804200c41420580032074014081038201004289045030301003501e1859900504600b064900000940707100e141e001c58060407414442e00008000120900110360301010604040f0720003001d0095516507501c01e40f5074205100c1040b1302a03004802d0412403192031140119490341c00e08a481802d011000004003e5281042c1100030311081925410030240300701020740c040c1c0855a00000b1103001c14814210050f81190031034400c2d8008400074118080100c1039580c00d80e801800c1 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 750216106 1250 750214856 750214903
    0x6030c09020319090302010b01110c150d0b191d04240e16081b0d0813170709110922020f04030f0b01080601030816020f12060612 57
    0x20030001c0d501c0a410102500c5a64503641c0c0024414410090290301c00e0300005503100350000007401c18503090b95280d0954100550100403521070f2880e40354400401500d2558030b4845c000d0039802014204281e40d0010300c0942010010a00400108141c0342040314081405040e05201c094045085078001d041000a504500403070784100d0075042c9042e00c8640202d4400c88541c2e10600e00483e14248211071340400004122003031083c00310860142840d04580c0c0395000300030101d000441d502c0340051107850001941981c2010914400014100351485510701c111030b2484c10340d89216030b00074402c400740f070004503004101d1076508032a500d20010f004829003000400c03210f54400b00703c0700c40a945076020862403a40405180042014511a800110351401942480006828160051600b0f907001030010700100b41c008045d1020b2111850341c0a0a9014a2002c61503450011032016000026034480108440c000b08171184035120645480070090145010a640c80e501c01d80010000034034110b5 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 750217356 1250 750216106 750216119
    0x1180501121e0204020d0914060601021b1207030b01031101020a0309090e070e240303090306180f07090222030b130c030b130b0c0421030c060e030903010f06030c 71
    0x1c080158070b02d0491900c24000940218060340c1c072505081d580950b0b160000c0303041292014000170b01c540c1c01c6000308201d150210000c0e595500401d0031580310304a0301249001c0c0d0b614207a0529000500d2016200025624a0042c590400138042100e50a906001c90f0269520014200c0a2075800da513503610700da89417400c148010f00f4a101c880c0003a0051040120b40c10140c14000c07401207112604030b9080500c000d0184c1440d0341c101288503c66082001030700740541e00024800d4100816044160072440e080d54058600a48000d210384c45000c1c8180c002041030459015103007040480c2c0c0141100076405521411901590100030918060314000c23800c3c08142d40654500c00b442091904032050712522703804140b400c00c43d181c4c82d01090312101581000030403d170403600700da030680c1040d00f8a0f0a00c2c040700c40c10010381c003480704040201a03a02d81030521070b01900350240d0b0042d104011710600300d0300d0940c4030b42c00081000c1c080d42c2024403020080c2001e00c12041143d410662043d0324604110 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 750218606 1250 750217356 750217373
    0x91d07030203092104080f070b030a0c11060c04031a1009050a0f0f020307140414040c120203091e1f05060307211a040218070203041d0118050112 64
    0x100300d01818070a0800c4013401050b18445040340414401c1000c0d1103a15000d41d592501d4072440c0400110382003510100b041006503000c1d80d41202108401055102c840b044c2103402c1c0e078540003042554452102484104440031004109aa01480c0112124440440c00c43c2180000b9a81d07050800d428060411684c152a4007060b04801070003400300d400014289200140c030081ca00c2c800381030754004107009101c0e40000403000c101d080454000d080616040b85d504100c42084001b600490700e55040411045c4204180d01c0201c01e595821512814007501c19940e0f00050a51510513010110f021489044002449484030308600c401004444141b00c9860242501503d440d4052040100103d02c9803001040003903070082030314440042c0c0c034040c149400240d8105032900da407100341d8018003001d0b80b03d980c1080e40108034407451010300e80328201e00328507511031903001488048100c405a100c20380d28680b0307a8101d03889031101200090310054000101c034030a11900f0b040d1104003501c4400a10b412 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 750219856 1250 750218606 750218611
    0x13030b06041a010f142709060d030305090325020a0611190f050a03080a051f060c0c030c150806040b01091e230102010c0f02060c0705010207050a060c091d07030203 72
    0x52900d5400c000041c60a5170782c54004410004542c0f00c00342c1c0c45004101c46c0900c242203002c0031240c01c2e0381810004045010404000030280030103440d8400a02003010030011521043c201503811a0466020b1001c402c50390030900c0200c1c40784521440018804d8852191810501010000f5105900d51541804050802414111002512450300c1d0f400b04100780807a00815010341c40f06181c5207041110b0030120781c001000910b0b804950600d659056002c14400c8040e0703041c0d42003178440f00303c0c10304004900000396070008285200038840031032007403020030a4203002000b40d25490b5150301c0715010002a0f40703540706001d0000d01010340420801d908034502c012a401d003808410007031503c0d003080c05854101c00c0e4903040c030040c0411115219580c2403048a6216030170f0716103106130004002c80251205009040d4040708103011981e03109101003035046804d41680f2030221104c4002626100015212448442002c40c54428001640c00f5141d442c10f090940d6440302e022107a5189101940290400b = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 750221106 1250 750219856 750219887
    0x50a061e090e0a1d01020c0d091203020d0807021603030e0a060809060609071403160e0306090606041509090f0b0f09030901080703140f01030209090c1509010c0813030b06041a01 78
    0xb26100065200c284014070100c01180f0150800c0c40040c071000d807620381c0715401560010b000d001c86001003680400c5466a014051609200e0b039110204101c2c904100c11c0758090400762007c0f400000c068000102000500c0152081c1c402075035034117015155000c04550000c07140e041400041c1c014035140c42180d030300007042c0c03c050b141c42c8117908c0000d1142d04115000e00d41c1c056506072001215820540c3c50059500c124010680c518100700d503503407a048042c00c00c5000c4d540301d9084940e01001d00008034060481c800301041ba030342e400d003001ea0b00744030012406e44001301c140e40410064200b041d0340714801c00d60400218504550b503001102c840783e0040220080650b42c05005124040401240c1d025030b403100d0b0a4100c80d41140108194600701070203001059008205e820081c0c0c480d080034041c0c10400b545840d48400c41c3e1001170700d68107100c60004041c00c10004046c225209800c010340141c0e402000d074080c1c3d030b9450b02c1c184400c5035507150744940000045690307103889610583e1000d401002 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 750222356 1250 750221106 750221141
    0x61e03030e100314090304060801051507060504031407030e044502090a020703020111090f0112090b0f090d020d080c030901090b010b120609061503040507050a061e090e0a 75
    0x3100030f40a52100e005540c5e01074540c00015003009802e50090f0498054030084500d044580a540c005102500c01e01000804841e00e81c8005014140920380040d10b02180380e02140c0e848031700d8078004003001d105580c0684503a00c1e246640b00904181405400b0003402141c064480a5800a00080d09a0418403804e41c22b0442c400340c10040c0c403194038040c0a00304051002d40c41e1040303031a0290a641800303e0b03035003600c0c006000440842d9a5120b00c000030283c00c0c00c00582e10b501c0920400d002c1d002d95900075000741c03c0c420a0214080d0302c8110688174865180903a0131800040f48120385070604110010000781844000c40c00b1104043c00444e040f08124000203103896096959010406e426409140154404150001119004507825074050740807524031a035450460001780c0700605008010403030340070220006040010402c00d46000d0003008206001c2c7c15641c0400a0120710b403a01e600c40004803a4070320010301c038050101700c0d0680e200c0402419165a403009224018008010300c1410800f = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 750223606 1250 750222356 750222371
    0x6010314030910081e3c04030e0102070614030601050a110f0345271006030c020a020103020903030904060906051c050a0f02010918061e03030e1003 65
    0x2581c410701c06410f0301c0030761105080c034a0513140340e40b07130b481ca03201040e00000c0000b810050070ba0081c840701117010341e111b00070340b00180241844100d21444800003030481991132051100313264001e002000e044000b41d084a0410740c031810210f80c554407011103180c9820083c00860283d6000d140134103402c004a2400803181c0105445680c500000d59901381819000010a106485101c0d4041d141c0c0f088400c50501c0302c0e41060b07003460084a1102a15010311070a00000100b0b03a9503611419200c40c02000c4d18503928007580401040c00100760341e403881451210308001a200d0190003040940340480d00903100c0d0300300701d13001580a580900c10156050108000b401e109a44500c41c40d030150003441d000007846401c00040c0002c039040a280d0b821007a42854030b51000510006400c01700c5c940c400c2c0758450500c070a20043e42e0b120780700d40044030301170242e0001054124066000f001243e201003991540b00041291040070024140005400125a4047c500755400c003280110640c2240d4900000c010 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 750224856 1250 750223606 750223609
    0x50712030521010918020a050f040908030108060105010807090501020a1113110c0c010504121502041203020a1209051302030c13240305060105030613060503031909120302060103140309 81
    0x42e01c004a10b501402001001409411800e204880c43c80040620040c0940490380000b48600070074800e252280300408003070901c03070300d40d90440125540d00c030680c6500ea50710384c04401d0710360784c00b400350074006406500020240ca115640300e404481042c1c01070610240c240c1c480e0200d0300314100150381c102008050350b1030b15203403611903440055400303516542c407030450311a040c1c184000c3c00c0c1c0c010f0400c10144803e0210098202d00311b180c0c6681700e000a904001c0403e00c0001a00440e44032038001000c0410480a041d000708021103580d209a000b01e00c2086110002e4414000501826800c894008210305110031254011a000107000c84103904228102c0c07a039900c444d4131500135606003650320907000e20103100c06c4124000b00c0d107d41014001d519080000919901005086a10800d42c0300da039a4030007007859101d00040d00024059030750700c1e045409504000040001108006001c50b4400940c0b42d41c011000412540d05502a101991958452038a101c1034041500354500007081518006d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 750226106 1250 750224856 750224887
    0x305221502070e15120a08070606031115040b090f210d0f050306150903010906020c0c0301090b040201300c030506040207020307150c1b031e0507120305 67
    0x800e803036149680d03201a4040c0090400100d940403000d807002d0b9a00380001c0d042d014011407102c03001a9490500c040b00418a14502150b003500a40413031000143c400074809113401400940c0d000c4c1400310007100b40d650038070080d202014003284030040e052109202c08030170440280840e1038010024440010f00500003802031004119021100d0054035010602403400c2c03001c48072494141c20610102c2d43c40b440c01806510000300343c94820740c0b80242109100000342c0a80c0c0c01008043c0003000298184d03c0c0c0440294040140d188082c4603050000d00c4c2440c050042481059100312a8401c2c0d071102d60064480710000d0702080c00030302c0320184211070480b001021002594541d00701264001507454003801f182c1d030250400c4e018a00411403900942c40c001102011100b02107185880058258412500500052001406149203000e6501042d80400c9641f080c1c034001c12200c200c4400c019044419050f554100401c2070301320541c2081350241e015403020380c150080c107000340390806449503c0303003 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 750227356 1250 750226106 750226109
    0x3051b0c0a11010903030f12060b1207111207020405090316060507030b040605030d080c09040c031a010207060c11010c0b0702010e01050c130902090f030d050c010c0813030522 77
    0xd2907030042a000c028021031000e41810141c0a083c1004250300f1910014028007016010406000319982040e00f81e0b0007517480080180520084951200001c2e03d00d080301c98010385070280050380c034980d8444a00d401060000f1000b004445140c501403040c0d0910028020040134030080340000d100d0b1b408908818031801c40010b00c6a0000209440d00501c09800c648100602d20301591520b80244455100003920812008640c01c0c034408950341c415400c40a8880c041c00a904182080004c164550b0180c000c0c007600e03c0c0002409001140a400490791000644210310020303800d60025004160608803c00007801c06261042e1600321a45440b44901e40c107441c0ca80060b0f56401ca01c0384030503428495076030441100c444407803078214405c0400f56070b100c1d0750003207489003680003407004002d40d14000c03074038038a901c003405071541c00484200c0a80341e1782102203044455424154146110f81c81892a07520590000c400c0d80301060158031b0444294000011603031404202580c0c01910b0081100c0820 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 750228606 1250 750227356 750227377
    0x52a030c01051e090a0b151311090a0902030c0307120902040203270d050a050a02010912030c1403011d060d0b0f0106030e0604020a0515070f0305030a06141003051b 72
    0x5040303030140c0d00800e4a54400400c05803081c0c0010390060001069406d0300e84c0c10008110101a008203000300041802c0c0c1c01c03154081c081442c02c8402141c04c12964040c041c0038004858400f00566111548802e0b0700c000c0720024251502000000e80d03007402464100d486020b00e83c00018110700d2a400700f01280e0041d6551034004000c1647c0002125603130700001703d820318280103040c1e03004501b200a8824010001080144900030034a0000b041c401d622160715945c03c0400d0303240c0a502613102900512906c03445c04005803a442c80483c8482094048030304807000585001e0745012541031101e00f070400a04101d40c850030600f001c00102c0c0350301d0041d80c002c00000c90314444d254506200038003210064505000305070017000030030016940d410141d41c1290001c0c1e03800120840d1102542d159407080110081101d40300d05465070504d50311201131841680003002c200840c6480710703000080003103014481076000c5000070081c04014071070740000e608401811000d1081001404070420b107900040c1c000b4 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 750229856 1250 750228606 750228631
    0x4050c012006010f0f08010e070b0d290108060a060807120e24011e051903050f0106150504030503030a0b03100e0a0b070c08040902070503120108011407052a030c0105 73
    0x510031400190417800081c40b004000f042140201c5030700755180c01e154480e06c8580000400d010042c0001c981044103103541e0307280000a04002c00a00317032808080b0481441c0090220b00000700d40c0e007040030450b4156020352b100c40401ea030ba482c0049509104290340904540d4440340100c00c441c008108411403451018200341282103c1d815440d004076050b0b1060151600d401c8031241440d028403000419180c054400c006002c1d403405094424409541c0b00828a100340c5a502070800d106500c0041a82c4042d0070000010100301d004441e40d000e580006446d0360000c0001c100c21070226440441c80007800380c01c0d0f07581140072034180310480d070b55042d24039010742043c01070030100001c61101680c00890790800e004011103a481d0300c44540154020f1103000c682c000b0320cc905021040050b56418000703010f10b4025580c40b0326695001c0c140703451103003901da01840d0100d84200d00030000d643c8449010480025505c180c82e5424018034448910141e040c04100807081500754280105072240390881c846 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 750231106 1250 750229856 750229859
    0xe01120203010f0b1c0203120f040e060103020a0f050c0114130605090102032e03021e09060f061801170403030e070b0a0503040609060e0f0601091404050c012006010f 73
    0x145425030318110107400c43c0e0391800c40e211a60703681d40100b03207400c10208140568600c5440c80406d240c051a40501070f2017190104012226424410081040d01d080e00e1407003d5075180c580054041c1c0c02040c40f0180403401340c050b044040c5110b140540306c002c400c8000480c0c0015440c184841d030032015501c29110000499050f400d01200d4000d241d00091036000851079441c0024200740721400841041140081d401d040d502c9540c007494001c009075400034020042c01e104082607000001c000d0b545c03d40a514003600290591400144071000c01002502580c0340c22040c0c150710101100e00d140759810f00120b2890003d4030715071520603030701c02c074800e45000868000351180c1900e07200c101e03440441000c104010b02d403009503000f0b090700d801c60b51218020030395480a19002c3c02400d07402003586641d100340ea10212800f040024254100c6061501c20401e6034410000000482c0d401c580140680c0c3c46007a4410095100703181610340c0445402401c04000d80032401142000c0c4280d00c60340342406801c10 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 750232356 1250 750231106 750231109
    0x30e0f0a03030f033902030c01020a02011a1e060a0908100b1c051002131e230306180f07080f121215040f090b10120c1a040e011202 58
    0x401130140e41c8807814000300000c480103054402d04044170304c40c201c4036001070b162085e0700070800d490726902c0400080d5218079603004002d0003801180c96a0750203000c0d14000c0c01c80d60800d00196003004040f4a40164540716440603c81290300848019081050301000040d6403e8144003149002d1482400030035661640300400c4090003203000c2c40300340300b04034001c01c070f001070300000309403a130b4044454004d42c44219000e00c000003c4690750020400b0304048240106141c0b821500a06541d00c401da4103480302c5074800c4e155118561076003c40c2c1c26500c464042116620f484201e480e03007401140c12030740041c42c8144c0359410041c06078488801613003c0702c403a098101040c0300410790303911201c01309410030340c0350400c0041c1d5a90242502041c0e0068004804c3c2a850b1900200d01c0e03602044001c0c04006006d1801c061102006c840301c00031502c001c0c00c042100201420510011500301d565000c0b402c0c2044808119080c0c0d608001041040070040007a580042010082c0201042d84015600e00781500 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 750233606 1250 750232356 750232361
    0x712030c050601090216060507020705100302120c040f120c0f080d11031204060504020d0b090705040516080403140403050d0c03120920060d0e03040602100e0604030e0f0a03030f03 79
    0x1c101c4c10f4298010b2111005085003a10903a00d220f420907404904c6031220a802c1c1c0c206130b01a0041034120704c40e00d1000011a0f099001485510300c0d1042c92581a03803005600141c5014602501d034000856400802c038a00707030b120784055004d014881d20099a50340d0f403040b143c0c1146030360020300960042c0c0e802c1141103401c03020f0440e45071890009507141c54400541c510f5240da008000501043c4d603003001c2010354690207002801d413580b00103070b1000d505140500035030f80c05040c400d2911480c200000204244100b00c441c4e0012031003074842040740c2e191a641629901510344510959030f40030b1000202180040120094694003510390a000940c0f03428010a001e840d41607140a282c1407002c17100c0041c0d882840c203c4c150341c4c502610700000038804000342e40c610491018010b041c1c00c1c0284001001d101100030021222140c084805054140c1180020746081c1280740d40503420850000340880d028600290100c0c078014148070350421440d001503401081070700103a00103001080f1802c0602d4062 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 750234856 1250 750233606 750233609
    0x21306090807060206010614180d1104060501021c031e0f020406090e090709020f12010801051e150915040f050420090103060c05070f0f020310060b0a110712030c050601 74
    0x41c130182c40198141200588a42ea40025002d034000001070108085011907100f103050f4407000349000000700907800c100e110680401e0a0a00c01d520b0860001203d6000003401c000450b0761200120707210315100400d4004000c9101c0b075249a00ea05070360007940e811144200c0c4100300c00d2400c0162101c1c10003034010004911900f00286403010041401f0000000207809030403910301060160341d0720004242d400d504e014144c6102c1e03003003a9050022950140c1900202d1007085c2d001d9260704507200e601041c8101a10582c0d4030002598010f0340f00e5028284012003d900524a41c04210301403450000324003224280c00340100c0d1165904280030810214891440759140040d4908c050743d000d04000420908042c0300c02060181c0e52444034070007501400131307509190b81105002c196043c0c94140f0280e10107090104900c07900854082c181451124480c040076244031403d09400c110444800707456110f40c41414880b244641d1000003900e0110303881c01044240b090307982c05010955450110301d0b14070103 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 750236106 1250 750234856 750234869
    0x1030c080115050d0212031b0604060f090c031205071203020a180b0a080415020304050609250e06042c0712050c0105210106080906070f21021306090807 67
    0x82c00c104076600c16103c11416034040350554504001c041c20203141d8410030b184484c41c18440c003109901c904010660500c211f00440c000d204500d4980e03003003411540004001400da42c241d1100f48041000c0d80c90003051060139040441c41e00c000e9841e400d409010426100d40000c0c0c00040c003100d80c652180c000100c071180c60b0044d414480c10140100c0160090140c85401c02480000143c203001c1c04c0c80078481d10000380c400456076405c140c104203442e0f030000c0b00c8071003242c80b41c001c520141c0100c5074413803c0c0d2000000326076a10b90303003814042604018007030140c5074450707203072103c5000e001301e43d0300d042806403583e080c80144079449104c0182098030070341c849610500c290304014003041c404100100e050300e092a10954520b49105942400c401c50120007000d4050307040080342840d000b43e00760707002c0e202c400112500c60381d80304000c4038400f9003c0d00d9903001541040714404041c102000d0114043d0a5400140c00d000c1c0078160103070400d080b079004a00140c100c04d0104030722078003400300c000600b84 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 750237356 1250 750236106 750236141
    0x31209300c0a200102060702120c030f0c070f0b0702091803070605010905010f0905011a0318100b010305012412090212060f100b180d0602071a09150f04140601030c0801 74
    0x703013090040e44803011427001e54119100010b111202110a008030307009100c1c45413031640c40344079161200c4d9403060b0314000c03801d50300c40d1450041211b2100ea03059529845d03000348494400d580d091600b041c1d22034a107aa076603ca1009210720b4000508600407240a0300b0500c0f00000c0540c5403819129958000b64803604207603103800c1c01446040c01c024440900c40b450307441015541d80b2040007200081003c40c100009a024000740700c1001e20b6181c2049904001c2642c044c0016601e6842500c10100803c44240303100c160800c407034034201d0240102c5007070780008803030000700036a4580204114600081c1c540780250442c4080241c02d43d0100d400c01d4010010302d4404900390300308841501c86204000300c2c60070318040001c2c01d031107c0c2d44800f507030350105a01c04400e5403106e085260030781e00d8800880043c090a01c0400002e110f0050026003100c3d45020b5000a441c291036540f0300c4500144080c1060341d0403002c0c03e000e07000340c0b03a007080301c00d00070348c840d40700120704d20310f0411100e0031a810380b80740084120 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 750238606 1250 750237356 750237361
    0x70806062106220c020c04020f0910090f030b0a0c0e1c0206042706060e1e0402130803070507090603020105030610020c12031209300c0a20010206 64
    0x154011240500d110100841085502c1d5140040c0d4021020400400a03140070203000c12404215009143c13001ea05408890b03c00031000200b0040e03005100035040e600c0801c0c04405050324013141685c1c01c074140c1d4180741e001c85840d0000420605090340051781c10341c0c881d4051003032509461260728940213180ca0180800741010002901441580140303803506803403c0011415076540000b214014604008203458042000610b0001164034034803e14440d89451f20024807035001e40050000b80e040101031010761411009158141000d681940342c009038240107240c056013080c4461390151400c2001941c803101c43d407505515120103608415000344c2080010001030340c11000780c0343801c00310440310107030711043e80340d000c910f481c0007840002e03400441d10f035070158842c0000c0028502e041e0407107408000307590f400c040c1c00d984404400c3c44d80031528a10510038a900c41203070110b05d840c05500a4286004c4600d140145006141001550a001504d16520000600200010300f8030003c0c0090205032 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 750239856 1250 750238606 750238627
    0x607050d08041b0905070807020a170705010f050406020418020405060d0c2634180803030c0904230a05090718050f070903050712030c061407080606 65
    0x11109a11010180540003020400700303c0380a0300c02882c1062039090940b00d03955218074038050407003603592102044d884000b00b21101d2000c1280c00502e0780241c0c0100380380e074005044800320f034840c0000b5515556980c401c103101500070b0044034040c44c0145c50243e01d65040c50024055054038110752440c040c0304010411081d121001600e8132880d410b54009282c60716242e003038070003085040e50701c3d9401705d90004204034005120617140c058440f00680c04085e080c01919440d0224a1204030010004040e9003000c0380741c81900c3c10050702d002c400404c1b001d10b2b40c0d002c00511f942c00541d220000340c20003080d21009401c1c144182c006504242121804072080b003805a000f241000d02802080c603158000920560400c0011000420544212074012603980340c84070000c1000382c80074180c3d50602000701c2c1c8418465404203080d2034021700500721082c1341800240401010f10030407030501000d0203118000c64404d00c1011100003503203030a58054a8040e1005020a00c005c7c41d892141030188244410b2 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 750241106 1250 750239856 750239863
    0x2030403051b0d06020c070303270b030c1902010501230d0318150c02030c0d030519020c0603041110021b06030405030d020a020a2028030501060f14060705 68
    0x440300c2c0407002c4050102e07032010500800c12800003401142c0002550030400c3c40010318807048902990f00c0111000440a6004c50291844140e00b00128151b0381803141c1c030480780082d50000c0d41030f90060724004003100280301c120203040980340581d544078010070a00c00c41104900c81754003510034035030600f4103c0d00010340c81000c242000d01045074600c0d282c1e1015172172858290240040d1016044c000150360f0006180c00000f01d401c030700a0060400c032581504007400c405c0d2203c0c0d456200d03941060340804491940c0d5480c0700101c1d0440c86104502d50303490716450001c500a600541c25200004441014406030103040d160007011540a4101c520790f1034444441c0c90780e1900c0880311175035070352201d0a0441c958068171030a030402d11b2000a01808031500040e855901c01d216585410300156200c0721615942e052a442c2d640010b03004040c1070803010101c3d14060404080c00088442948944031720342103411640040a141c002d42d607080c08440c00e0030301c0c0e00300044000c03a042480d01d801a0380761600d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 750242356 1250 750241106 750241123
    0x909030f0c030e060f1b0a0525260d080106050a0c060603051501030b1315020c150a021803070f03080f1e04031103010c02070e060f0303180306070203040305 69
    0x2044030081005041611030818000c101c3c000401c1a902c640752545075001131340c03161014070203040c01c540ca01840f003d00400c000845a410138050404850a409107444d01d02003000654141000303884041440c2c28981003501340d038a08030103a00002043c40b052180360140c048070403428001e8002c01080781590150403903d00481d14070304003070b00d0031a81c581000601301c25003008000b0f0050900c200d20301810048894100c0e809201070030050384501c3d031444d4944083d0400608440300e514a0000d003c0001e0300200302e508401b070215681032403a5030f8003280c2c036030381520018141900024581004041e041c98459403010840182c0340891030008002c421694501c401000c4201c04281c001c0e140004400303886c403800c01e49036010130340380e42c12690900e40d5000d404222a403405546c4074031114141441601e080c01c0c0c50350010480241001d4407100c07002c00c01840107500a00300c01c80d50320544c400740007503c1c140042070320000100c1012001c060a28800a09800840d4030a01003040810b40024a820 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 750243606 1250 750242356 750242387
    0xc120103020f0a0803040e0a1506021002160501090f020306071d0d17070305040306050a1a090903191805010c0203060c0d02160b040c090e0a2003070807060801090903 73
    0x10882d00600c000300d002024030f0760003c219030101160000701010140d210500c41d00f09231004008505c00940b00c42c54148082c0103107001030f8081000c0601c0600c1c01d50061030107009081404107003c000790340710b5096510050f011210810300e800154114101041800c0d04581e040c2800c0708140c49180f4503110340424118600e21035135242010030144051130b280c10070801c12020119594a81608001e0302c5031b4011300c41110098500b900140b1860074034456091150044541225141010420086039103409421806c00d40030400c5246107600311003600c61201c150580307609100706100081411201c00070382c01141030154041d2803100607a00443c140380e000c018908010303156180b007140c010003401800225403c054660401d4020f1040300700b00c451280d40314001600c500e984a40118040e5604400e6606440d030015030724100003800340410041455080780500213414801001a1a002c140d91200481303810410091107141e60091160b405070551003014400f0400d26a0003c00c10300312000c0c0c02 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 750244856 1250 750243606 750243619
    0x30a021906090f050a0b07020c0901120203011e0e010e0c03120d23040506181902030313030614091902120f010c090602010c0207050f040b010c06061d0c12010302 71
    0x39040204a92010340c0c0381c0c1d080040368032400f0840c50102e9031000d00c4501079904807079842c0081d001e1880040c2080b07045901804058040e440e044006054582c1010101c0e40755403100b000383e400d001c54480050322160310707400125000f009101c00d2400c440e0a81c803402c105402c09006c2600d0b0b0744001569000c100b06503180156540c0240903820010210300308030954410203004600c98854118243c41d0059005100b5502c503038454040d100f010845030f2942090a400141165402d000c001c0441305880c2d0001c2c043d640340c009542982c0c1c18240d81a08220f5425a4400d030040080c0c03090340c3d400341c1c080b0b01c15000348010710125030003030340000025078000c1c4200c182001e01504000c0504c480d0b0786050001000f44032007250703460003620282d164021480158071381001d000e0424400075050040340c3c8090005000512500305100c090545042018148602c0005080024030b051055000a0010401f4008641e6800f031036412400700181c040c0b02499800c1c070043c20301e002c20b12a41c50450764102e440 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 750246106 1250 750244856 750244903
    0x3090603060d050f060a0612170d0605040f020a0206060607112101050a0506010f1809020d06030f03050a08100308031315020403061a040621030203120106051b030a02 73
    0x28030705203490a401409070003101c258030400344c2c2c002101c034001d035502c400a0010700d0711190886448040388402806010708441b07001d210050341c400401c00d61030681c2e404984203480300041010f4948803c3d9403c01698009284549c0f550305018040d00841e0846406180064035180e195550b010003071924480c1e080120818550030381d4001000707284050708000d200070315103d0592401008101c4059010582514001004520071104040002c03540000440b6942c207041c9420000c0d001034803404081980c0d0403012012400c0329481094a0f0f00c20340c0d8071560b40201d198010a41345c80a0240d9015500c030040070300c00070390404240c903030101c803001c01002c1040b000e0a001084400382c210768035115100280200c00d1001075009400782c00150321030500000e0380034040c007085030290300c107503050403608140c44600005550301b4003004900a104886c1442da03000c108080206086c1d1210011500000380c1107074803001003641700e60801e03502c0003a43c20f041e034800c8065107441d201d200e80000082c2c0003c0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 750247356 1250 750246106 750246109
    0x18150a0c030b131a060319020c0a050a0f050d090308070803091608010b010e09060321070204050c0c0c040608070b0912030c0601180c0c02060a0519030204140103020c0309060306 78
    0x200078402c0d00280005000444070301c280000382605000c203c854071303001d00c90501604050b8112401910445a462002c0c00e41c801110020340050b0440c0c480382c06003003140c4010400400800c0c40481c0203040100002100e07141080c83d02102c01917602c00e000c5113807002c10200d203029051350a500d411440855482e030f1008a098100100d24a00303400c45d02d141c002c0440c0c00756056012003000c01c0280c84200301503840604010103100200d6016515501402e40350520448091207540010080d0021a00b0200154001015124101c4004101842c0821036044c50030003000041110881900c08012180c107102403651a102c69005018414030000303000d04032900c0d441c01616000d00340b00e05072520b4986070448107071100001e120304d071245040d444070070000303000c03500c160480306209803111050260359130300703020841e00031554040c04e0000910852014144040d11030000c840c480e6401696075041c2503011410300f0350050682e041601c14403c20f45210130001c101d81d03103000225140c580301d42e200390 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 750248606 1250 750247356 750247361
    0x60a0c050319050c0c040b09060d022421160809100908070b2203140c0a0501060501022505120705130c0306150219210818150a0c03 58
    0x40e0341d6107581100c0202c420503032010142140d13103101c4050304c5001c0030220800c4207075001d81400c0360380a489400880c8243c5010034130441200d03c0903000b203491501c41b80706001000003690024003ca00001101c4040c100d040180c0303d084030340440a0881c90a0540c401c000c100e910704481014422080c0200c0c4da12a010082414191900ca60510201c01300b4074111000750040481110701c030300301e03401180c2d025003210000c01a482c80f608001035604000e44044800d502e43c0611580b040300d080007003110120060007030b074152502610000c11050701d400002864644821050701d81c41d82c1010400c42e40c21440d10400003203d0040744c6404d106450130102c141004601d602c0268814600603071549444c100b90031291040e80c09480070805603680e88400000c1c012160b00fa0401a04201c2400c0602c01c0c0040c030020030503000d00040d40119440240a00d603444c40423030420003080c6000c0400c10142d10701d4109180c01d580c0200a04070351680c140c02d03130000ba4400707000303444129203c6403c00f4555100746d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 750249856 1250 750248606 750248617
    0x1208030a090501112106060901021c1b05030a0210020307272402061513051003020301050108010603230706120912120b1225080a05031902010b060a0c0503 68
    0x3540c4994171480c0608050103541483c07007030900003c1001c00111545065826516666410b0700900300c400e4640c00215140340032072505500f400800702c4070b007a4178101c041d1400140c61040300216a2504010b0010345454003201f0040c101900400030441c0050b8001c00248000140c8109c1e91402e03150a082d5410070f140c10303005800a00c201d400c4600b20841a01d00108804649400340c82190316800485a046443d07801c400f0341200c1c03510305035000c0b00c54a510041d40040c0c5c0d071500e040615101d84c0000d080d103000f07a20032000780e91107200500600c00e010450a11510003050304040d1303e4000c402041c0c80320050312801090103052401401c035041e00d50001b4442a40c0003a494590324000305014041d9215801043e0341c4c6880d000d0910550700b0912203a4280d607661b03000401c2c0c1d084d591000690981003d100142c00f28000003800110040100020201c2c0c0384900060360302c54000113090352101e0b9004141104682c1010014521501c42c40304503400c8010620b80102c00d559503042841c45c61155 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 750251106 1250 750249856 750249881
    0xf0402071a0c04030c0f0e190f090309061202090a06080601050d060f0311010c03170c09040615030b090c07031416030e0114090f190806070504030c1208030a090501 72
    0x350401001c2e10b0000300030820f9074032500d820815162078822807848030301ca90040107480894100814002c003244440f0142000c4101c901042001203102d40d8030a07248071036011004198441d03018000b05400103401521140c40302411401c1c041ca480000b2008440f5100310011302c4000d41c04642d450b4071a05c102e0725200181041070020a60300c150540500c81701d0303c0255418031480c5002900b56100300e02c0800003681580d40c081441c0504100c1100c100030241070723199400c0042180d00c0b07035600d4034010780c00200f01007811003001400000024058801d40d0008ca0701c60000c12081041080c881d100b641c0386240c051074280d04104210350070070406e100391100c14035600901c3c402074042640c40b90080f68403600030f03078504224101000d440e040c54001d5002c3d00754421200d031501c40c0181483c1d5617181c0c40004d40041d0b0401d0903511500c003414202e007960a040014400034042c01802000c3c1d071254000c08010050300350100507505c40c001c00c4e00000d40842540d0b600c80e031420085c8a400d4014060400c034 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 750252356 1250 750251106 750251153
    0x7030e0d0c030c0e04050319020705040c17090a050d080a09060f0506030c09060d0305070c03080307020708012004060e0f0907320909040c080604060b1309020f040207 73
    0x242071258038a5600d200032104114040400700b130124071010701500441c1d01c10004e43c10080e401c3c042c03500d01c249141c140d804611482d40300041c00e40d213901402903c0780241d220711746102c03a800b81e95000310400815190072607100940c40c44c00504000351548038072490385429012a01c3e0080c040e03019107000344000d0040e9050111003040003c0f030b1351009000310310403070448416080b80c0060040c0321104075980c9034050f4801a17000c011074050002400d40511070404c034014a40c5031703a16841da0b0741040d82c01c07100582c04400c050008820901c00e4a109400000c0c1c41c4403108910000c1f48654461409000c0421036502c588881540350101e55010035400181403450915101c500100484202201e10300000c40075240e4001e080c0d02030407071035040005140801d2a0840c0d01003441203140001c1c0045484a0505c540020280c0741800f505c1c0c040e0f44202404203000c19400700f08600205c07080c0c070700c01c405440d00c3c0c110401a91201c01c00d007080603082d070300541c84040a09040b59292240e01c14047c1561 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 750253606 1250 750252356 750252379
    0x60a051b0d051210030b060111010b060301090902030709090809010324083003040b06011826030a08220b0a0504020a1d0a05040c03050d080f060f060f07030e 69
    0xa8000303028091840c14150003c1c80703541c68941d10f10412045210250214039a00040f840390b51040f00c103004d41c0c2c0381c030030f0000c103140d400d00c0042402c3c4e910076800300c509156141400030451a040c8620002400102810f0050303034504c0e00c075a2203078842c1e000118141a0340307003000d00420140c01d0700c08040d00c646841c0090a26540c5181c40e4440380103d005444020528002d440e0706240c071070006800038200602c0b03030301f107507240d41c0c4010f041003001d8045418405491409a0340440d50032620000d41840750300d100100c5004c03680c00300c1015100c480d5038040e800a01a880c0e51540c002402680a07200441c0842002d4a5001100c0c1e003642e2588040d200c0d0003104200b00c075442c803c2d0003c6004030310a0b01c0e200b1045a6980ea143c01410740e00a841d200740d00d012020a441e0001030704013640081c014000c04d0398090f56903984a182c42d540c41c0640011038218010010200541d61105501640503600002c0040c0700c02c001501600c162050100728820110f00001498420450f8000900000d001041100e = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 750254856 1250 750253606 750253633
    0xd02030d080106020721060c0509030a140d0905010f0e12070905010503070e100b091306031a060411040317190203070510090201050711150d02040501140702060a051b 73
    0x1e040900808026105604001884006c00c098481211221140c26010003100303640c1c07400a008001c00d0301003000001c0c0302140140d6028480081c04511601051000c02c0c040b607140c60504034030005a10030722a80b402e0810443c1d070010f9100f140681c0d0351824400707410445001488640d1030321490300719849446000300f40c1e440c02d6400b9a060312000c40881c1c09441c1d903a10164881c1c1340c105c410b0b845030000c2003410040705503854060f140004000b80a184040c3c0f212a90b10219052540196552040c58004486108643e4041c1c1c0e08118256424031019030352071a901c80b41c9c441c1380b00c014590126840b0f0740f0183c0c01000151078603070100b40a1070004400201000303583c3d401003003064985008100008002010034410708210941c181c64050034201303187c644082c9170441c10001a04983d02c1485580f4004e4003900500401c0c096441c0181c40da42480001031400c0d003123080c020811038007006a540560b41300d200f61040c802c91850b00640c0d80010041890301d8110350726400005114900c01e51a02 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 750256106 1250 750254856 750254867
    0x18030c0c0913030e120c0301020315040f150527011d010b03060a03031202071b1511300c03070b060f010c0602220f06030b010503240d02030d 62
    0x100e04200ca4404640d241e0b6241d20101102c82e42008000c030780711804945003402d101070500c000301d00c038000751105030301101d000c41c1c20f990040740c40c000c2d00150000c848165291034031820f2004400070750104134007010540f261482810501480e4030403001c50038184540d41c00600a009682c4d4407a40940c0d135540c2d100f40c4454860320300b035a640501a03200c1c00200702d44d00c0420980e8884c20000344516010b034a90786040e10004441488221019000c01c41c440c04555022941951102ca543ca070310700b80c0c1c0c9040c0d440e40074039402c030055400300440b118000f01c1603840056442101007001c02c00c00f60b000c1400d04d062071803852201409105800100d2090144070740800076015680c0640f2504a1955405040010036104824a58007107004922a40e010400640c090070410540403065400104051070088894180b54040314100d15903c10900c20203615021f0840711100c2030800c14214108800c5145003004078025800c205540ba00510300d0710b0f910030400746029900a0306a4859000304e1000130007 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 750257356 1250 750256106 750256123
    0xf0c021c180306021315050c250801051501090918060f02160605161407150b0a03150e1603081317011b0801050612060406030804060807270e18030c 65
    0x74592446040000303003a0113071f408c6540704142d22014040c0961522680a54402c0c001c0f01443c601001420204d0714180074070035203009030701c0d4101c03400c194030314080014042051a04001c00881c00c00d4025104004000b12110b101580040086581d140d05514400207000e071101303140741d41e10282114803d012450740114011000c041c00301542c0500b2100c282c0728860b2026031000d48590400c454400320301d08211407050101907200c0400d07800e005000041c03d0310002c0d041520994a205080744441501c0c0c4103c0070f10000880c00b402c00c01c61201c0b4248140c80e410311010705241e5002a561403508004031100c00a001c810b00030300300d2401c0d03080030b25000300356080180001c00d500a01100099000340c071114100c1340020221031400152400704280b041d40503201c0e82d001a240c2340d02100040080703000e00f0150000340d580300c60610342590020121320104113045801e243c26100146140841d070100340c01c1d50400712714020580c8440c00b20307000526105c0314480b1507000200d06c01d103100303a02040214 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 750258606 1250 750257356 750257369
    0x1715030a150b1f03050603100510050a091503020d080f03040b010306141b0d090206030702031314150c0c04060305030901022a040506010c05070303030f0c021c1803060213 75
    0x1c02c20a0712070502c50110160140c403211001080c0c8100911846900000c1c0e202d4000b0f41550132600c00c0b440758030300380c51066071560303020600c00b00180800e0402c001c9803001400044001c0c04600c00a00e501300c0e007000c20740000b82c0525025000c0c603040c0700c1400100e43c2445c086030740d516960302c0e1a08003074a61a100b03020890300c0a0a20b21404420183c10508074050124040341c000443c0703100084c01c00540c40809130796070441d26001c0310b2016036a003601551046c00d007500550303924900a81600c068070200e410504440980300003505080e1295485034101c0750b9004411982e0b2460410510300e0052072001c4daa80c4141000c801004000010020f499540c1080e000c0b204940c449503241e086201407005081e251540082112003903140075000103400c01c4060500700400005070322405e0070110b0942054001c41d071120b46921040041340304403500c050451015211140070404a00c00520501c030701601000403070001603c6083c40803000000440d4400030856607090010a40d218107031241c800d00 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 750259856 1250 750258606 750258611
    0x601111603031706010f2003040e1008060c0703050d020c030c010b0a0503120711010e06030901020a0e150a030c091502070905060d0816081902010e06090d1715030a15 73
    0x30320300d848400d60343ca0300aa405849082400c00401c00c11540312a40d007c40c2d0b040c0320131003507200702c01d0f440c02c3c0010809420b41701000b5145140c80c0761039a1044546a125400e00d501000030070402000c00c1d810b5403105a450b06c0c01640c0c4e206605c41c002c01074018203a0000c4640800540c0400109055000184041041da0440c030550b5440c000c242d00c80d10040034903603d200040001c180080c0380c0083c1ca86442c441410041120170303121000c980c640e0421a02c00d00241c0d40021303980c1240e50888100040014129031075451205003030400c8901d801540f01840c00d264580c1240c08034640250f403410301400b024181c00c2442c50a102000b543c4481d14416a1b0746d42d8500710214007a800c0c100090304106070017058aa241003074160000c001c1110030f02c400d440310038092140c0602c0e0122800d05011001a95002042da580e402d00c2c0141410350280c42c410b2241c0c415900705140f25040800181c0ea0040302d120003503196a01086500f41c2c0a400c0c005070b602d03004650446080142c15801004a03c241c00c0c1d04 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 750261106 1250 750259856 750259877
    0x1107061a030f12090d0219031a0a020403082203170703110a080a050a020c1806090a1b140409050403030e060106050a05161506030302060603161a03060111160303 71
    0x40e03e03102c0e100110701940b041d0080021968505203002d42c00c00092000d4441071203464000500e00c0c0b0034006400460740c1c26842c49203201c944449003500d54100499120451421b49555101d84d00c0744202c4089030611032140d60854040c150601c1d8003001941c01110882d0030000601e04624643d110000440200740c00b00c40c20380c0704040020b844614590f10103422480c00c0008441a039198220300c2480e4114030910010810750f84808a0041e64020b50151014280c1845410400721540c01484410a140345c11400701c0c10141c0c031000c0d081e02d09000d0810050740345100760000c07050300c41c070b42200002900784004d22040561660250f40c85a1090090b80d445980340d5104441c2e510034548a80300064003400301e2410360060300d02407040e0324801d14504a4000c0d1039a450020745085608c10741c05a0088001c002d0319003810b1211040561000e54003c0d4042d05045001d6002642400349030440769012001906590203402d08151381007401040340c4120340050303a005444503080c00101c000881c800754 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 750262356 1250 750261106 750261133
    0x50c130509030d02130f0f050901050d020108010b090105070503130608010608070f0e01110a0b06090c041a0702120a14101e05070203221e181107061a03 67
    0x103514041c5202102a5140a520511990181d001130170244007080c5411800030351a010042100020801081c0424803240b0340f0301000500b0700d05a2080340108036520030400140c0e80301c0d50050641e888650b11750b03140c2c2421070040340c0901481d54024006d01c0300065a4811004c1d1400700005c5426994500c400b84ea03c820045644400a980c10b0011a040c15400d6802901406003a99139880601d03240c0414000d081d41da501e407082e401015100440f2030018050b01d800c0411480794010f0f0000200e0346800e19141201804086c402069880000007085070005c540e41d0800c1031960020301800c95600d0b00d01410000c01b01c1314421910700040c441c1e0108424030321440d0181c46050034908202c140d0b00804d034030145002d8100105814214001041002000c0c0c0180780840d0241c401f0900900c482030601f04a0700c0c1241c5490810340c504240c0c0da01c1004440d03120102c4040c0344140810100e09000440741000140c0100c1100600c081e0505500600b41c4000300e00e403480c164012000c0700d90350700390440b = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 750263606 1250 750262356 750262361
    0xa030804110307062a0c030f030e060c030a0305090c061210091107120c0602190e060f03042003031207030f0506210a05100204150801051008060616050c13 68
    0x402c0b01c010400744034550659000701c0c140c80d505c00900c0301c014881009103554400c1e07041d00a8104446405600110720103150380000e0751034480780706890052802c640041c0b0f045c0d0302e01880443c10201034851000546a90b0107200c2d031821000e0180c43c0f59160300345007040c56030350700088030030314183c8802d400c001a00ea0180c0c0502c220302900e6a080070b14080180d20f03105107209003201518244900c1c0b400740700002c0c8140c4010f064103c00340786544414000720320300401620b02d03440158412441031005030320702c1c016041100e0300964403041c031842100403030a0646c80840001c01c0c2590501011600007103011140801500c80d8110796010803118140303c240104880c02511480d401c542019520b840b408600c462524420300c042048a021190550743d940c60301c202101e03a902d1142e00854200640d000602c8503540c0c0040358109410550705045c081007c0d201c94100c42401c0001d040301051441c0c442008030380710307110200d03d811003c07405814419903c0660300b03d80c41c0103108441c0055410820792 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 750264856 1250 750263606 750263609
    0xf0e03040b220e010e090a140706020f030c03040b03060a09020a0210061d0604020307020a1b0303090e09060613020f0c06060f0d02030a0204050a060512100f0507080412020c030a030804110307 84
    0x20f102070700b0507400c1180c000c40382d070402410801a40326200c0040e02081d4640d0a02e00640134040041c504a424410024100b0b0080700e0451665403040c8401201d01c0c10201c291016101081c2d040c0e62260707507180c000784072225213034000010a031001030440f01d856800b082e4030810407003014090103103580c0e440065009400c185441030b40c207945503011400e2460950011504130f80c1341c1c41114030311121500d940000646504040308081d0010604208050308510341e0b00007043c3c4440c802d1843d02d040c20f11251228001003041f840f46401307402055100030550305941c480715a00784501d4407070313201011043d44ca00303050343d1061040100041c000d010f840d00c82c07402d00e4440e9001c1c010301440c468035421b00020b0000604007849650704e6103008504c9480740035001d0213a6a00d40c009200c52212201403c0480317480c0511200341908200410003041c0d04082c0054100ba4801040002c11005420803828107580700c038090b5240c02801d42078014194080b6211340118003952a480290581408041d0f543c6c545 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 750266106 1250 750264856 750264869
    0x3070b0c09030d0c062c150717040804030f05010e07080318010309210c031842030204030309140a0e0c1e0a02160e01090f0e03040b22 59
    0x81d4840c2c0c0c9005114480813200548900004120544004040ba0005030390f442c14071015a03900d0182c280c250710402c000b107171304030040700201c050b424918002440000b140e01450107411001000c1001c1084c400121002182c214114001680b12890094043c08000803e2522440381d0350700800c101c8000300c11248072052007640c10140400650064014000300b14007030302d00d02d0f89074075038803154038406d9544440c1c400c140c1d8440391280e070f051502411603049407110b20021454082e05110390020071540d800c50300306003004185e048110032054106180c0c1c0d07500e0701e25507a0176460944501d580503005003054a100751968002c031034841039008558801132403680d50080000e6400c0000007840b080035500b006050f00842e06c3c0c0a10341186210241d04c1344c2c1c002100c5007002500d1040360394103004140200b1450060720f5000d0303141061800894106000381500b0503502c04c41c1d140070707003116484a8074069061303003600e84440d541d0500441e1074100b925417609440c031040c00b40d0080508848003105a841 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 750267356 1250 750266106 750266113
    0x62503120e0d200a080c0a1208010e04060b04020c01060806180f06010e183018091801060b0409050702070f120c050913051e1b2103070b0c0903 63
    0x7070b06628080c652103150040d043e80107405051020070420f60080041500d030400400d6038a00d185000312071001c0441c01d0f039041050110040c0200311036058802c0c2c00c50b40005010135440362900000d0024403900341002d92541c0f0301000003d42d0b40d400b181a1340701d01e0b184010032181c8140e882189490f0741c0194003c41158101c43d0042c8201412410510741000c0380b000c841c1e1944600e88a480d103001c01e0a00e028040c991040d004107001c000e00d00c1e603904c5d001d1452000e00d00780000a200030b00b0b4007101443c024840c0004600051001081004070012802032100030301195507969800c48003070b8000e01442c010507041c880096945400012440d00b110280301ca0086182d250449541c403c0800303440482d440484204002081d0380d4100c02c181c0928120301300007900385d1441c600145456148084816140305080340402c0c1d42e4404111500b45019545040802e46804030001d80405400b882400500c81071806603035960030004060103045124450203802138442004094080c024600380c0d035855403 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 750268606 1250 750267356 750267377
    0x20601120c26030a03020d06170a061a0a120212210c120301080102090a05041e270506070e0301140103080a0e0301021605010b06090906062503120e0d 66
    0x22038140d29104070840100c40880781280c1407141504681c444002000007a1b004101400250901d101c2d0400400300826070f1481d40802c042c1464461841d11405461243e40d040700344c484010914050088020080c215004551215010b11400d41003100980c00303003010101e4400001c00004411500c10030f055031039074041307403d0000d070f10450b804004105603038020032008a2120745041d0145028152040006d84c4546903401404154600c1e58071a520540c00c0c400c06040008601d440303400807070540c1d103000c601142ca6030541e1500e2142c00c0c1c0803104c88100d030054113090010206039240913034003550b502c1505c1c41070401094240d50003080605a41c20000c001040000e010b00b000f00048010782c140290039808a100007402ca81001c8241c804004010191108000c402e210303a190451089410605103e071107400b082d03061000030500e034000d070000182001c080c1011148c078080380c40b010f681d07500c40d1134040ca0020000c0d0f00340c264a880050038620400a41c40c000300d0300e8040c04d03180d59104011038 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 750269856 1250 750268606 750268619
    0x2070507051c0501180302190b0114040e0601120c0902031009021602030a11010f02060c07080708040909030c060f020a1e1824020303070f120b0d12020601120c 70
    0xb001100ca000d150b00b04022081002480a001d10441c0008861050054011a0401a052021109952102c1002c2000c0c5a0014104100c45030540344120705013403800e413403000801c0080c039618210305080d00c04c0000001e810008005000b00316803081000c8109280c0d01c0e00e8007070607800152004840240700502c2070001c03041c15405030a041c0c21030440f8036203c000326001300f8204110000261001c031103808a0040d65600041100c05089082c801020145000c00503010030380100d1000900701a000110942130001580565011b041c145c2001c004034405c6180203042030131781650407108a810210301c028188a40e20079101c5110b0143c46e04150004001005404810810158428012186407103080c50314552940c402403c1001c5080485100c2d514804ca0f420004000f904210b500c00c008200c003955200c41c0f400d60030429410002d245010780542d040140548400392034000c803943c00c6172000d2000000e00c00310703144150b80968072940d07292290501c0c2c032051400080d000c0402e49100b000754 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 750271106 1250 750269856 750269869
    0x1e12070602040e100905090f15040f1a06010e040e1005063007090905030430050d080c03010b1b0102090d0c140937020a0c0309090207050705 62
    0x1031040500516282e215189403188941c29503840010301c078000d82c184840641c0c2e00c5180e400a0800c0001c0400903018112141d41d03601c078048007102000818082020000028124444d0a40c003034403102c8040c0c0c4000c0d05142c0317801d08440c583d0008000b0040030409050511441c6c584290110260441540e02040080903101c00341085030040c1d02000102a0380110300c41e84503004417940790798007411101c500500d161a00d0350700300c3c0c444186040c0d141c0b4002500002100c0480d14505c14a81441906040c0c3d503007003413440341130402849012a00340d0200030000c80d52406203001921540355585805555050602013405100c50b80d01c001c020300040107403503103c00300a07031112400152070216034402203001d0082e21300c003c81d4004800301c000d02846000108100d1a0803095074034814074a04005107000c1035019500100d51710208582ca015806c6155505240d001c000070ba080d07503a50044c105c020404c0e407103040194009410a43d02148000f40e9008691020390040010481c80f42420304002c503 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 750272356 1250 750271106 750271117
    0x91e0603120406050901090b040f12030306090c090305160b1b0a1509020319032001230106030605030307110424030f2306040311070305100501081e12 66
    0x6161041507068103860003604000d201401080c2d44094440001000242c41900c80d600b0125010750309010611400c10b180007084100d642210880d0010300440c201900101403c0d040280b8041c02d1841518219801c0307948101224403803070880320004800038690800c40700750300640a614204224050b8010601004c03500b0350049001079610760441d9903582c14000d1a5482000c1c4140d4580700c41100b503181c280480b200c0ca580c03c07583d0a01c1d07144c103a41c000340706842c004240c0e8490141000c10480110096001c0362070010049580700880600b40e480d4841d00d8000d00c58100041d051900c045118100801a05d541903171016420360040340b1402000007a180664100300320510480b010361030039011100410041d402800a80c0c015034007410035651030117012240e0301e00c48002050008078410001035003540700743c040c40e1030f094040103008500c0c14100c2640c4054418810f4075580e041c0310300c0a03030206040fa000c41d01205e100203c41c40da40d141c44190320150340d48030340184108003c1c06031038000614 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 750273606 1250 750272356 750272359
    0x70c15030204170604050106050108010f2304020a0e0a080a0b131a0705070203010c0f05030f0612101a0d03050304030f0c080f0309010c0302160201120b10020a0c05091e06 75
    0x40c103150f15811005507100724043c4034840d40e80180103010901c6002e2040c58060329080c80c00390800d605141046055808a01c12020901004014038822407007460080320403420040c0203640d00c207605c60004000d0800103e405101d9207005000107203480c0000350000361198000c24800d6079580c1c03100d00d09042c442d900c806684801019122160390040040041e100c1d0300d40d5101c0d5a20303000180141402c5403025080d400030310500c640d0b44108642c008041d0383d40907442c20110803440d82c0c2e00022510040840d240b2100c1c52007400790310011300303800d504040b00117080c0b02d03161000d0190400030002600b003e16030140204400300003081c0401e106400c40201c0040c80c4c24520100e09142c0c0e00c6601541c484004124015404402e2040d15982801007201c501031600d070039401c0c20f0f100355101000310b9030840f0003414040c413054540d021060310b81105840d07200040c89044d42c1c81c0c1185001c1c1d191148280103c40c483ca0074000800c00d4030307214941500451031070300e80c41c503040c004c103c0b8410701c08400381166 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 750274856 1250 750273606 750273611
    0x9070905090a020406030c0923060d02010e030318040e0109031b110306010e0403110109020a1509050a030602041a0a091203050c010c0e030106060c0b04021c0609050c1005070c1503 79
    0x1031003da03c0d203014043c0203621030700c01c00540a1500351070300700302c07051300d01c0b10f690b4203d03503031840d042904141c482c441d0031200c101e0300d6450300f018502c010f0382d2108041701020703014000822064100a00d0458000300fa072800d407010f00c0419090030000c2c7c22102c03560740050100300854206848449144205001103219100c4294412030a20000745400740c268041184501c02c40100010150720190090100034158020b2144101c2070b40040c110346901d008548603000c8201c4c0c1110183d1040308060010300000d81010b50f19038507410b00d54043d51060048000a076981c081c18124155400200e481e000c0b05a5107003000d050400d0305100140415500603020018184191046001d0a21814001d490103442d00500707030401d8420306d402d54100d98407030820300490b0700100b00071444490340c0d554070990464104080e8280046008041e600c030310000340440740703002508020044001020341102074202c3c2d0380460b1407070b4908120380a1181d0340340181803000d052010004518054101d0b8494181d41c20f01 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 750276106 1250 750274856 750274873
    0x304170c031201080102090406051e1201140435071205071b06020c0d05030f030c041a0c122a0111073906050903010204030b0702031c050907090509 65
    0xc1c80c0d0007202078000c0c4240340d40c00111f4404178034251107003400512050b0f811002c0320140700442a80d60307402c40c80c400d000d202081c01c01805404294410081014091a0f808260506c0d080c00480f9202006105041811050525105140c180300742c1841c1046080341c1c42c5011080d981c1c01c05c5001120301d00109100701070088034001102480306444100714048800c140a140400080c0f60110601d0f606001d03290300003070400403070002b00c205c1e1030031000240165665110f000740510030703100302c0d4400c0341941c100031204c403240203003e002082c618040c03404481c83d00c045110810860310a4030741e5110001040651a035850700704000e6107041201c20b8000250882c0c804610700c019500110089410710304402d0f8100e032081c6d1032446910980b912030040d104580284400701e100c2e000030b0045c5018400301284600603a50700b50100c60141d9480300410800c1d00f00032102941c1c03608400c03c6e511341c5c000c1e00502403005005d81c2c45082d03c504002001014054a085e0340320300240f4000c1c001010301d0161000 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 750277356 1250 750276106 750276127
    0x5131203141311010819022a10060519060e010e04050903041a090906010c0f05121903290f03030c1513021f12050703020a140304170c03 60
    0x1c0007489000008500b501e103040c01d00e41542d0448941c42950b05000da0b074010300c01102070070f41c040740082802c03a0006a403068403c03102d55007880070480341515401585552001c05002050100304034440c0d210602c00d06890300200544800c1c2c000100044440e046001c10005200d0b01c860b02007458103043c101043c0d602000420213907101140e005031641d000080c104010240f00726048074016680c0f408030708084400340012109840602450f0420004011103014088030682400039145e00c83c0c200d50118490110129075504051030754001c0201a0040348522030203801116003a6506030a00011100c4018030701038266851104941c010006040720305107920b00300000c3c1281107607840141821007000b80190071017000140001d011104807004940107803209a09000c1010b4107042c5121042d441d0101169007c2d28044809161802c3c00248514960540d008000e100d800d80d81e030195007140c03014200308911059800902c29a81c149080c024a2100400350450740201e00a03645000a040d0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 750278606 1250 750277356 750277391
    0xa0f140103060c0e010801050d1101120c18140d080a0e0301110c0618070608151e101719150b040f090b0102060612032b06080105131203 60
    0x1c0040b20b40c1540c079120410100e8014a5842c0000c0003481c0c50907080d8100800f06402810080008001154030940200582e000300c69a040b04c0010036800c0002551900004010f074054805201c08840188030204040d00d0745e410740f902c215005004c0c90355884580d03659008940c03005000204110301703c207900026076000e01807184072522a50741340380c03201d0035018498201000642201c61400c08019082903001c4085901001c482080c180003c4503640c00f0187d48a84224080040c0c1c0040b0050070340c2c1c140880ea120203011880300351001b01034414003200c161204d2580e0201e20201002007800030340d62031224840342c025003218800106580e414406900f146007860340080b040a5001b05003405280004200340b0001d184c510403d010b5040d510780081e442d40c9020b01030382d0040c0816080a04441410400c454007140d000208507829031794100d414400d01240d00503040d0f15800d040700001d0300f4805005183c01801540c0442100c6005aa01c903201d0400e08d21801c1d00b80754030740006420301d55050 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 750279856 1250 750278606 750278609
    0x306010f230a0801030b0709030201090b0c03040504020c030a1d0f040b0609040219020c04061206020d0605030d030207110405011401110a330507140f090402041421060a0f1401 77
    0xd8480f8071265042d813070036074082c40d40105a02d0400c1051482000540c4e481400c1c030b01180c051000c02503645403440c00003400c510903074001c0c5070424000107010b00d62090000040410820f41c0e034803e43c010180b448144098045010080d500505406a5005518107584540d201c024000c0c401442d15682c0008a801c0c0d80120103039440c84101050b424410a405100004240703008860030485030303042140c00c0c6001310007054080c1c0710503404503000581034901c1d8410030181400074200c0719140103000d0010065404100200d5004030f5007401000d07282403501903941038481d454a41000788101000440e000c4003d400b10f03c16070302c03d044491002c6a03807150140c10040b0107502ca030214901c841c4280f413011580300804a00e1520f02005c0100460f071110000180e202807802c02c6540700440300510519000300410345902038800200024042903010303002c4040780040d105082c217040090090091309200c0c1940311255000480020700f20798003a840440036018210002036200391002e801a01d00109 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 750281106 1250 750279856 750279877
    0x15092705030a110601180e03090a0e010f0501080f0a02280314011205070501032c060a0506030f03030613020412050a0308011502030412030309080d150501050306010f23 74
    0x1d00c100002d40c2c4402c58000032407182c00103140a500d06500c01302000c20061003005019920801ca03441074500b481160200c0000400350f031205a2102403514000c4130a03c034412600082800006255000340305061280c44144880b0055030744550100c00694440c05603909680040702212603424080615440781e00101d0354001500024044a441d4080068100745400150185040001100001d900d020b841c402e180118903c40c40e012111102d910f1803415204034001914601c0900c400001d20f24842c1c0d080310028072541c0c8850302455100d582c0c114140c203007a001000010b03407505003980001400c83e400b072401494240d803089040d10000c02c6c03440444042d040810300c00103150340910700b0b1307000d00014990302c2030781800390501035900c1c440d605c0355800068520803c80140760107940701d141850307003005006a07252140c800210041c9010088400c80002e00e17000414103502c0f90703040d64441c80d010385546070b1407071000f10161204071043c202d0318a00916101b140c7c01201c4c3c8803000e00503540742c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 750282356 1250 750281106 750281113
    0x1b0b031306051803031602120c0c240301120c0308040b12070302090a0512010e250b1e16020a060c030e030d0c2d031d010315092705 58
    0x400e864840e050310000750080000800320f140d501543c1c14088222904056650703402c100089050790181d003002026607505a01060206280c800c5500200e0301c0540c2204c2281e011190294019000c181402e0035001c520013844140014000417082c0c020b0400954041e11403c03c1aa41d40d0350386c000c940d0701640160448480204508507055520a403403600401903040a40c00e00c40c1c00808900b00007940c3c800c49118070070700b0200d411010030a40c000c41c8030409940035100c4288041c0204038030308072600301c80741842130041d00008501201405881440d181980701c90386d048405c20f446c40c041e4020708003106800c500001c2500c0165070300d1a0000003494142c880000d185020305000c0c0024920000583c040c0c1c2040400300d081551003480078440b280e100a40946080415450002e0120015401e52050310400c1c8884207142c1c0210001344d02d1352001507101c0303581900c0c50046080d03440b41a600840d1050140d014000e106080d00520f8070000303410a2a038880c80091000303641064007107801e64140c0c1 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 750283606 1250 750282356 750282391
    0x1815090313170d0e03030a030f0b0301090c0510054608074d060c040515181003241d040b060d0201110d090e060a03020d1b0b03 56
    0x400780140c1e10743c44141d0502039154400d00c004a0303102c0c1b040c50581010150b44007000b101c0f00c4c01c0c99000da0f031010303000380007000707001100d25094800c4520782c020a841020244100031100e8419000c40d0420081c210380144c0100e110014050404130484121484000100b0702500c40d00c0031003c07200003492242d0791140701c1c1c1085500035102180e500070035109030001154100f030421418a01e505040840305031030743c00444452000301d0b203800300b1000740340354000c3c1300c04d00c400c49903114040c06c180c0e48200c96215803e520b4a011510520615104d00030384424411320291074030340050000c0810a80d800c0124802040a50b81e00c441a00300c09031500140d989078044c80f500e03c80055025001314400041c0191b0308090700c8806200700000e100078802ca850300c807100116481402c01c24041c040c4042110846001c50300702400c04d16031805a0701000091030009007007807030708200d07000459402a0034070f0500085516001e050000701e120211100524001c0001c1d01400d040003188600c007403c07008485c1c0c4 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 750284856 1250 750283606 750283649
    0x1505010909060e131b060e100c0b0f060a080102270405010503060c160b01060c03031401140112140705120106081009020c0109020402030a060503061815090313 70
    0x2200641c01040009180a10510410f03468503c1c03243c002490b1010345680c1d650a190002540340c21400c0c030041d10300200e500060880d0000d06000000300c00322050010311011040c02c8416286802014221011324404120340740c0c5402d0300c55030070950281080840503161203000342660302c5822410748042d9002c2940311145024a07503c0301c070940031202800194503240c0001e41d299405002014200c0000070103000d0440003001750140c00342e100080c0d4a5540c0d40d22400b514040c05a0421b40100382000d00d00301c9494103074003240341660300140c1c0100114005e1001141c582200385040118550394804500c920099240c3d0f03548074008603910680c0e211010941044840c0060740030310f0a11840c101070026103602c505400f42644c56407030b0700503200c0c1e0079185040e01500d0203903006500144000b041c0525115590030160980303d041e811034613680c41d201c0c15580b81020074034440f410b03a0000e200305441c04001d01a000c2d001949841120b042244405004c1d83c1c03000300780d2010903044130800013001c1e00c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 750286106 1250 750284856 750284867
    0x304080708070327050f04050912031f0f091b02123108160b0f0a0e15030604060f12030c020d12031d0a031d03150c090319110f0f04150501 61
    0xd60400d803008d00040c1450507016031b58070107540b09108500000720019900361500e21b203001e101e021501403180a1a41c07500c0d107481c1040c0e50b005018000782000c01c0500d0710031041d041d114160000c0d500400c02a0105038001049401c8280100300142074903a4114220348240c0c2a10741c0e201020000e108064641501d152410809100030400512107400402256a001080d5807a01e4030014200c1c9d40c4410490b0100c4480c8952225194414000d400d5001c050f128440518490201031f80d0800110742c0702c03000c80713500c2c02c070511850800c4020090b0400c0064858100c20580c68800344c0301d400426100d0b600c41c007814610442510000396115a008404000c0a40c2c4068081141d00034200005030b54400400b0320924826110500b603110115412030b880030800c0285c515a01c09001d644d1f800c020028040c9640b00000b1a840380c4206541c070004407950404903a1001ea0207202401c040502c2c4081c4002a111071804580c03018500b0400c520f40d40b074901400e02c0740080c2d80c00420b540c0c5e0600001400 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 750287356 1250 750286106 750286129
    0x1030216120e0a0f2105031204110609060405040b04020c0d080402040f0c02100c0e030304030302011401361415010206100b040608090f0f030a030b06030408070807032705 75
    0x100f00c4030440200164180d48544a00b603600103400d22504084040103206003c01a02004015110000704080f00d40c841c5002c1500a0384036880300f1b25211810410422940070700d401d200e5200b5801c110820451420342d00c40104008064805800c1c02c54096440342400042c840340004075264000704001c6281c02c0c41a01011040e40c101003000201e483e800944c1c9650404490704001c1d514420144060b0150007a10314201004003103a5540d03442e860024080c200910b22003c0301e520010001c40d081109106512594000b034810248000119503e000c0030078000389404400f0b80d8540c4040405030110340168806e007001000c0b01011151368000a15184005145841100f26001c1c1402040c2180084500303d600900d06480503403140705000d41800c42d030100340b915038820402011462070010010b0700c4174001135202000701410f548140442e03440200c400800082042012600045100e03001d004068001e14212050001000301c2c0c0b2000e80b0344030401c001441004c0300411051400401100 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 750288606 1250 750287356 750287359
    0x21f060f060f030b061315091e09060e01080319120204030c051008010b090126010306090c0b0a0906031a09010801050108010c05070b070f021212012115050601030216120e 75
    0x10f18000180700c801210541c3c030301540d07100c1083c1000340e1f05102d1040c4441c1002d01003003a20342c802e9900c005140100811244150100b450804100041006203d03184c24101c44495001e940703402038010401c040c2c040c50380c1156081c800c02d41582800c018251000c0c0001d1407140d031245810368240010401400e40d80308400d0108505840103001e0036903107901341e5290010a0904180102a00300b041c00c891210030307111840c0f8580440000705005554102d81c202c81e0003056031490180d15051a81c0f00c42c803407000342c500420040c1104104032480f943c0100c607010485040c0380014112070000424038802a40011450ba440380014440d4440a01c02c040602050f81403081c5450020742e20f201d1500c10080c000c0c42230103045da460212040c002c0c00062030000030750000580d5007400440e14031a010082c050303440c03c400000161508503210031403c89c0150b07001034148079070340300c0a840407006c3d000003080141015001d10900054036820408081030324070074042007610022421000300118041d40245 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 750289856 1250 750288606 750288619
    0x60509150304200d150c08071112180d0609060b030c0d02040f06031401060e130b0a05060a051201020414010323091504110a090c021f060f060f030b 65
    0x24140c060b280c0b006541d06911a15038021440000d00101320404090b02c17402d10030102a0104442d644205040078841c1c07541e080c281c0b1285003c41d0040e1110090180e20b03401080304200c030340341040c06001507604003d0181d03031a1b01c031140451018080340d4000c81c0c1803501d80d4500b400300324460281481619069006000380810030000a50070061600081d0060b03646290300c4a1002c0c461300214051504090401040403000d8200782c001d120310321a800c02c000080c00420713010081c01a25040719504a54050255200c00111000814002e0802c80c0e00c81c01802c0001403035151178941e484030310f01c0c0e00001a03c0e1031a260101c00d105088090060426140c0031080764081104d019120b828092869807054564940441034901102c42d985095200c0f9071030100400c1060100010003014000c6c7d44001ca0107a03281101e0096850184981001d6001519046811181d1010709072a8a442d43c80101358103039034007039404240406070032020004044c80c0c2c254800a4160256199002040d60b80c1e = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 750291106 1250 750289856 750289861
    0xe1906052121040302010c050106080109080d11121807051f020f010221040314180f37050603070807090f050102060103060b130c020304080c03150115050408070605091503 75
    0x5401040c0f00b1404001e041c1700c000d041a5062105c00d602000207441808000c118246460030028129088138003520340e51414a00742114840310f04094440042070720310224103640b644005030030074051504e0995142e2062200011303c0356a210000e0b40340e42c2d540e142e030703105050811800a041074504030000301130368010407016414240007004a17240c400c1c01842001661668a0111145c026a03803401c6200c40d00802c6001c0c40303601d011840c0b8135005c812202ca541c641d1a0200781f00700500c2c1ca9013920004080b81d00000300c2c00c588070185d03210504131001e00c2441c090f189c0d00000c034183c000781c0b07208000604080400c0340311303900308031640c000c0e04003102c010300c1552800d03000075520b01050000030070603511042e02c12242e071610f8107407a80c0140c1506084c00460185072009581f07030854030940d0214803804003403080b141004105515915007803003a5000e036030300b441c101300c3c410096925a14100102000005518102407214201511041da942c55495038503d080080d440c06da04006000141304001f03 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 750292356 1250 750291106 750291163
    0xc020303031305070902180909011802060d090204090807110d0521091c050c12030304060e0a0c122f0f01020319090914010e19060521 59
    0xd4a0703201401c0485100000b042c0c0c5409810039016600903400c0500124409445184503c842102c2c0601a20000c0301651600d00c811309882a003443d194180c13021000040241c10500010039122000314400300e1082510350100303044500c43c2d0303000e69141078049124010829041a0024042c4e8100e030000801105078882680b28141288188a051400c1103d0350340c0c1a00387d020342d1100040109100f201e0804804104400c02c0d440c1400c4845018445580380c20746020110031604402800065040d60b9545c1d6174180105062803003d10310b44103586080c800201000e8010b805460000ca03802c820281c540f03800b0b241c130a02404c29a0500444504003030b03004140204076028943c003103500c0c43c240c9848a0050303055100703100001c4000c808101515186035004889841100c41d08101004411000700c07451420030401c0c0140300000540d0400f05841c1144500a00074265800e03030009001541e402c001080060910b544d0021050000b460b034120030410301c010484a850605c881c51031440644 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 750293606 1250 750292356 750292363
    0x10e070302060d02220303050d0b010206150906030a02121e0105070f031802100e01081f030b0a1e0b09090105013008040806011809050303010e06030a0203070b190c0203 74
    0x103011028079502084420000784c050030022070801702c1c1c910000c0095220b0034000c0455100038081a04a410010115095480051114407a080314104407150208030001c00003800f4014200e26858883d11600c1405642c07904a00b600319a401d40041030a03580014039101110420000c0b812580d151008010340103030008132806140c0c1d0036280001d50f01c1c400c84443c48901c0b641e41000394101c229005000141e80d044294000f01e00d40980f00d0000701d40c2e0b0a160304003032822074030030180c8100c451a400c05c00521100d001d40c0d0050312054007c01d4070707001103100da00c00c00c11550624100035250100d40c8040e007800340003940c03c0042000284801d60420f0b552001c0801c2103602581c90442c0000b401e0005a00744a1844400d035020000a541742d0340c40410075034400f0280680c41e010f8880341c86014161413684511000c140e80040a9403c2d41e280800b02d5400c1080184090382500510154000581e0180800000390000f4103140d921503040a500038540d450304207540051001602a00300581d4002 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 750294856 1250 750293606 750293617
    0xe040f0209070522050102070803071208061518010f17040b09160f210c060309020a05090a09030e040e100c051b0a050d210b0f03070e0405010e07030206 67
    0x1070314404401c2d191500d044403a803150070258203500000f00b4042610710603040340902103400c00da00701e8000644500d16540c80b072003403034002070201e8040d06c402d001183c020300c0610380c0260010000d400b484110302e401207995201c0e8184100307500340c100c245c086a68100c1a481d035495080e1a00600310800c12034400c100f0000070b800a001d10300303d00001542c8460400038055210004100d90031810383d5954031880385100c81c040c40d8100050060101c10300c40c03064000706045034100410425507480e00d8001d40060070b0702d403070a0b81c0001200202203010f4660161040c007424222900043c0751240d42402451358581502843c82241047c1e07240008079400207514140c0074407800000f0f10030103a22015202e6129084150140a510641c04249094080b8080380c0003405502910703804480500b04641041c54204d4020100c02c0c20103400068003e668861409a4000b600d1039907589031100000749011145d134000446d240b070070400c200400c1400e004000d9210307140360060001a0030350780003840c01d0080 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 750296106 1250 750294856 750294859
    0x20718020304110f0f060d020c010f0203060105121e180d02010606050403150905011103070e0d0b070507031202040f03140102031b1309090b0f060a030209070507031202130602070e040f02 82
    0x207144c9158031652401c0500c26050401800180e8500000c01858041e40007100e034400355510b018039a01d0002018021a880f920050351918540003e0400300005000d0140608041594a42c03950007403c01c40c84049000304415006054510b03104540c482c0f4104480c5800421a41841d20400c0499000f60071b03176055a60090421080602c1083c11000801d44c803800a0515030030040700e02d0b101404900114010095980d503400038890303030424020845543e40004220b00c4900b800110310b988580080c101d41407003860112031504040d8206410381e04150000b820000e0441c1c0d08004100c5408992a4a11009002941185001c151015840d882842c0261869400081100c0c440400c03480040c0a420b400034104115001414222080842100c1d21070320705421601203074082c07424115100890350f00404c1900640c6d01d51030b0880d050341102c802201809180d80c0500e50303800460024225402c24040010a410300e0220020f140c030b8006e03444208108001410f01003c180180900b2041d140c0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 750297356 1250 750296106 750296119
    0x90606010c0c14060d090c03021905060901210905070f0602120d05061207030503120f150103020c0102130b070203250302040b0a0b270f09151503040302071802030411 73
    0xc01d0400309401e885101c401e246032a103401b86040c1040301e18811101aa40280c5030341c84095083d034002941034205015041c1d001c0000d01c003004840d8481c14850110300100c0c0000004040d103000c1e5003060703c0d00078404503481d0300500030a0122101418403d801450241b00600b003848002e10707460f201e8880ca100444481703491354000382680d1280c629881411495004858032641d582c100184c4903000400101e503020018000b05d07a00496040310355019001089031400700c0e1501c0c100640003580035901c40d440954080c8500c1d4215080f4010510040c0031482c40c059546041313104040c04c0201c0d01c1122200840e44000c204030303424601142009032a8140e60004100d0707074090000d5103044596100c0001248006070402c1c000080b84000c8103c50900c40080c1c0c0f100c0601c10800a0b00030756075841c03582000b20800041c06d0407400700e0031f03015041000380c00d801300b66018008085440c0e200312001c1d00564012202003007516030003a038010b00444101e03011800c6090994038071403403401c0200c1981c400c00 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 750298606 1250 750297356 750297389
    0xb2710081302010c020907050c012a032d020912070305070303050a14030106020d030b041e0906110304050d02061b09010819050a0c0e04111204050304051503090606010c0c 75
    0x900131411038500c0b80e00140508854a4080002002944010403000b5a035003041c03200e40f9903104c2d40c48500440d00000c0c1203074407000200303d0102c00900e120004242c00c448034050708951140030b50000095484000c401507503403d203900a014003c1b21801301c4400b90b60000b8001c0001c1a0003045a0f0b0a80fa81490826507402910300700b1a07160010000c107450b80d0700000000034009800003400c42a9a02d561014051141c407203003000111100c480d10082d903110107042010900402c0c3d880001000d01c00d02c00000c00518510140d00705400032101200c143c1e020340c8103441c20580400026502072042e144020003114001d03c3e6401c0d40c050b485440d41407021802c0426424600709170781361100e2064400401c0145400c2240002030f1000e901e060010540c200e2200b5601d0a05002d08011200a081402e1600001d03d9041c6c40254005100303031424081444080741c6940c400326076050000c1a0340055403203042c065103050074028060485410311240d43e0303003540001c0706241d043c07088078182031030340d105070 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 750299856 1250 750298606 750298609
    0x403030815060313150c1e09030b070201050f0c090303160212011e2412030c080a2604150c03060f0b03070306080d050702190b2710081302 61
    0x4201c0d1103101540041c010080120b2151110369184c0214000c5442c0c00b071a03d4994164011107801001e494001243c01e041e00800901400628290802e04d10b00040207175665114940c070b0440503101640181d4450b41401054107050b5030a5801c80107030119213140228610001c2c0e23403441030b03150364a40d0a0a0030700070400e542d103180500f00c0c90385030700000340041764000d2100701c4001e86400910380070b50310b01039841c110701d416010349151921800d81901c0303c00f8200f5031280d1a03104140f10450401a9003c0e1040000d03041c10302620f98400b1545a810704101b00c40c501c0340c40200b01d50500c031040c0104004210120308081c0002421403154075002440100b50001100941a04e0300007040148814200141c1c503035044000314801c55103039404104d035980310308031540c44040080a001c0055420300c0558003501d42410003c1804100748020310a9698402118909810203940e00040070180c01c4281c5c4018500920b403c002c150841d030b00b546080083d81c0c0a00071080c090591000c0218503c01c04045 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 750301106 1250 750299856 750299881
    0x260307061a0d230a0201080411190f1a090105072d0b04050105010509010b1b1c0f03050f011815030b0c070302010b0117041e38040804030308 62
    0x288031010740342041d501c00078241019039003040100803001c4070385210303c0050b0b0100800d28000035941603441012980750740c0c490305c66241007821401d48c4040007901c480032003804041711600500380805c03074081c010710744490600c0e46041d407a08000458030400c071071601a81d1180803031740c0031075001440d0280301b9087c003c03260400009200c912181c80c0c4c000f03141400d1102d04050944940d10030310081c0034581c1c84a041c844214028812030240840c18413016000c0000080c41c5460380201c002113030540c0310700410b1620040310061003840402d0740e00c07840d01c0d80154075010320303903200142c0300c0481190351624003024030900d00349149041085d6120752005c8540e05400c4c20328015608071200952a051041c030388802588a80d000f10059864450684140d5004212110b103048040c0c09103040ba542d140c480508001a0103041c017441c031421618480050010040c0030442c07a0b0304450a1500907545103404985000801c0408402c07002400f0407002400074400c40c3c059036410314007403025843e600100c252 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 750302356 1250 750301106 750301151
    0x110c03030301080a0c09180807062301180b01020303311a01060306050d030503070c02030703060c0f020304080319051b0d0306090b24040801020708030126030706 71
    0x6250200000001e56402c0000310005028000d03c5080c608503941c032000c6003241c8058620304500c1c1103d651356000306a0709005823030014052840410050361200c00480309480080d04080c040c03102000502584030481201c20f2004001541042070098090000c0e41d02d000c000e0071a0448052041c0220011400c1a2403101e4000101e580d126403072418074081c261030342c0e03079005009030f4080b88000207500781c4680125000c0300d40c0a403040440000340d0f01c04540030b03400244200300340b01a202030303e07006031820030054008500488000131543c0441c1e00051060303241c1d0803104119481480140034100d00401102d200000c801190605125100001d49240c00781c24441c000c5500a140d107941d007104041000c2c00d000389542e90800c000c81d20380328072200700c82c01900308503004210080d1008040701c3c1101d4040459100c031664a0410b545c84d0768041c00d90303010307070b41c00c490307940d00840108018541001d10708149421106242c07941c203250011250b8a010b880c0f00546010740341c2c0d052900801050101a0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 750303606 1250 750302356 750302359
    0x2031608031e1611120d05041110020115090606050d020a21061e14101209050a0203010c090e28021206031002041a030405010e010501060801031101090e07110c 70
    0x4519081640441c0d11030b0904050f00801c411061300300014802180d4815110b0349040780341d0500300e0455584004180c0104102c540c91240c0c03141d480542d0700c4680144048205600115992042030308000c0461746075440500b1340750400701d0a009194002c0107461100002c14401619588120f10466184c2445040c205100000810300ea56603003070341c3c1003c4251a201100250301401391000459908500e2080c0000041d0005004207189003401084106102c5440c0801d910070440d0b601030200c800f142030803240396121034482411420207004910180101781804c026680c6410084030400c00000d010704440050038460952100920400701800380320113100710348072244000301d8460420195a9140700c6d128104185941d51700728001c0b1016184181c41c10441041c140c203d91030349401c0034000700c03555500d411080400d442c00b44034040c002c182c1c980c1c0d0401154914180040351040c04c0c00d00604000040c0001e00001094014454202a00e4a401c0f0240d0504c3d4181c0c03420040d81c520800d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 750304856 1250 750303606 750303661
    0x1c0204050a180f0b07051312110a0909060506121f140c0a020c0301050402130b030102040531090803010317090d08031b04050307030227190c0203160803 67
    0x44140500d5a01e0f01c3d40d994414030303072480380391540501510b543c02241111300d40341c0f0b00002c0620100000505032442907220320011061804000c1c0041c0c040150350b04500c0015a48010003410b0104501400780c000900380c0e0101e0140658041003900d0f0700d0180c42c00382d030080c9010013045002e00b00d40e0242c0b04421010a0494041c00c1002c04040964481c504060040c8584140c0140302d242c10300c102070007203900030290300c50f103285001c505014000011400354195400d0200003165150446210f100347d2081c80101e181030041e000084083d100003000711001841d00101400082c2c0c8002201e054035040400c8860303000f82544a803060f449185c0307940f600820030b94080c008022410000d180205403011404100517580d0300128400d011700d01c512949030380104010030140c20410030100c441c0440c00c2c505520312421181d4010b01010a4420b10000c0d000004040d2404005c2d2040030208141c520185150501c01c03142d020041e912140d000e0700802000005c038403204034101d5040100d40500008 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 750306106 1250 750304856 750304901
    0xf06180111030d1b11010b0d0303050c0909010f09110304150b0d06020d0e07050102121c0204270c050301030809012f070f090c09120c03020604080c010e1c0204050a 72
    0x10f401813026008405000c29200d02c0c8a840f0028180540c032000d04028103001086082600c040f809480040e05403012a0410040c00e88140c0f200103425010b021031300b01c0c50552926203581c0c24211520b170030243e405200e041c414800044ea410301010f03000b80044034007240806510001401000d0b1001000701080d02c0090342241c6e510f6613400008214260700d090764159a80c440c0160380364402c040903c4042c00080001e280c0a4000d2b00074985241d000f040e00604058032201070701d01d8200101e2031b44218640e8103d01800d0394095014503c0441820b250260565155950f40510b600034940da240c103110925409000c2e0203c118075800c0d90116400d00b07846141a04160b9075141ca00d5030250300c40c1205862008182c0c50441e004103130318083c042d90b80462082c81c0012200d52102e02c002c00303c4061008940000140c0d9544020b80050610640034049114490f0001750003890510b958501800682640049d10309000002d0035201b5015940400c3d240d032401d40d404001e2030f60551264039103848581 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 750307356 1250 750306106 750306131
    0xe0a0213091d0c030714130608061008071a1801030f18200a1505070c0f15020a050c0d03090302040609020304050f0a02030601030f030c05010507030203060f06180111030d 75
    0xc01074861908080c3d40d0812150414162035581900400150311030110344140181042000b6401250f0194000919a500c903a1841d04290043d100310040c0c1010b030000b8088600180003c2c40140348880854051214042c0945520f01625440841155404500e080143d000e6000030300d00104545c0200a0042007540340580303d80710308015a01d40a0082c17483d2030080b41110b0302d0b20080e0005004c402d51620b4040350300241c46842c56a0130801c0070074040d0307400050110224a003c0c001d009050b196280c01c20707607150306a844110703c5400b1980b040e8640b1002c91070100d007080381808151459804c5a50b40d080c1070328862481e91009400910b0b24000082e002042c0c1c1c0654081c80c800c10a0b11498640080020781e646200d0700007a51540040b00104002400111801e0b201407003414107007000805621900d00f1920216004004290000200612482c0c600000300c1e0207c402c4403040d042441c60f280907004100352142c5a411301c007485515070100b207420019a0aa8004a00244980c0b1510036 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 750308606 1250 750307356 750307391
    0x30302071d0402210a05010212180d0c0b0a1d0106090c0504210614070207050a0b181002010b19050f060f09190812030f100e0a021309 59
    0x215000c00300704149000d00c103844924507168010b0b80c000b00180c0d0042200009910001c00f42035a03401140714100013440003c000380094001a8500307158950549000d41c4044050701c00030301c5141c1a0b0300004543d080c0e0340c0d0840c09000c1c4260b0071001d800c042c1e030755444800d40148100e254140168030b50310126000100150440019184080750078080c0418290040d00d0034000d6006005c580c90502e136000e042070b240500c00e103c80901a8101080e65042d0111448040d54142d0f92400141c0117038900f80180e0070520301c51070041a00e00f0321140703000881d0070302c6140c8400592070284907207030214520034141d1003500030340c425203002440b20701d2094005030b2030f041812075803003924094142d14810001ca031038030000362603d024002070400c0c0380c012280104055803443d61041100b10400400110700540b04220b01d5070200042d0282e9540d0381450b4801c124032650007071159101124804c8141f1640c00c640300c4603500403a040c0405030f107070689150744000c0b00c8565000001c410340741c0590803040d00c6951 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 750309856 1250 750308606 750308609
    0x15050a0b0409060e04031407050106030812061e01020c090c04030b240d020937020703022a090c0f190e0d0c06140d090602120702010e070b0304031803030207 69
    0xb40e604000080c0e030f500a80e00c80c45030071a40600842c869141d00d805c2040540010007942d0711030030001424a88075130b5441d490b40c11490f9503030640c414003010071205040c03820407503500000d0f0b4286c1404011b180070000307596124885419000d000108045042c41d8820070944018503403041280e880e920304000c000c2c8a04900340c0e89604103800c0b110341c113006400d01c02d16170407841d0f4025008403401d0b503560100e0040c1d4000340002c0c03000d2844100f020412400c0300f24245600a4101700b0161f135900ca0360400a1400368080d00720014100349404102444040096400c60710321b05039017a10341a07803036514440c8640100408401581c0d070004079000e0701d0360317080d03d1142d0841c5143c071415045074450b01400215070058070002d00010301c01c01c05001c0140038100002032140f1540c41c480c0380c03a10f013038204015502d8900007203c01c540c01051842e500c000e104000b0384c0c4600c6901c000c1000d0300a40c2100f50b614002d0784100110300ca070000110382454800c50380740003c180c241d10f00a45007135903440d0003961201d1a = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 750311106 1250 750309856 750309869
    0x180e011e2c070903020d06020f071202030a1d0a05091906060207152c030f0709060e0f0f010b0a0903060c0f0201050c0a020303010311041b18050f03060a15050a0b04 72
    0xe00c400202c07894041c4048105807a000f5181c9902050565104d500a5002401c100c070509028003080d80060005201940031085940c05151038150a9074043c08000000b0180402e0002c0d140101c1e4141d11005581e004403102100c49409648944981d80c201c4c480102c980350041c5d05155012030081e1b0002508005c40d220703034400c6d0340c002c5030101e001c42e031034205500030400880190302ca580d20042c0b40c40340030224481c01802d4484282c0b04041043c90300340540e100b075005d04d440d0101005080740d5444920307444000b490508241745415404540c40304414050311140e00004281003c200341325a0340c0c0360141d9880881007207146032a540150a02c4401180b580042d030818000840074000c030f00955514402580040d03041d6400c655400d03c08540241110f500181d07250005550b000c01c5d508840307282c0d036540c1c903403400400c0c00b1105030703040c2402da400040c01414035000c08a40344c1ca0000f40b013a840350703440d00001189510310807801c00e20501c0e50b028582c49104018003040c84040c1074002d20807542c0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 750312356 1250 750311106 750311189
    0x708030c040b0c0f0d2d050418060918120f0507080703080a0b040c02121b03270117010302220f0c110601030f020d030207050d1101180e011e 62
    0x10462401c1b00c94140341814107007541504049085030700d45030759040b2040d20300e03410080d08040c2c680084642010300444101841601c2d42001c0061106a10a122400c55003031129400f0100544a2440c41000d5144c54000c01c00301c514948000c51090007a50b15503680003180664440b0107007030003031840a05403403401e0340503d031210a154a14151083d0305e84031440d0307005000d0180e0b14501124081d0081a84499007948941100140c100244014248171040d00b543c00c034620700700c40c1f1402c2c0c1d00b81c0d4031700c0041c1031000c5d00b041080b000760444140c50449074100d07189802084c04284d90405a0000100003c043d81441c54195403c0c0ea9a041100445040c1e41ca10038040005455a07075590400c4c0b0001e0000c1500301581009401c0c071140800c4078030b0290040b00c00300c542d52004a20645600d01c2c051b515400d0b48001c40d202e41da844807003081c4507100f8240c0e0a00c03140c20b02d40c091030140070600c200d00804101c2001366503015905040c603002030070001c1007034401d8043c4800c1c074588401c07124210803a007607 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 750313606 1250 750312356 750312373
    0x307090810090b0a1e1119030c020d021f02311403060c0a27080a0b011706060f030a0606240203190309060b03030d0608010e120708030c040b0c0f 64
    0x2a402d21403c3c49000e0504000203041d000468803100030300b03c16103441e81b070000070400c401c1d0520518032021024400c90f41c00242c5000c858500904185103c1d0440007190099010b800100d50490b1129010402d44000140c2c0c0b030000000d0750754100700f001c003800030702003118074401c40e0070340344050310b40450312044c15607003801c1350a60401d03481e860101c6256240003c10b1101c40e0a41e4820001510402451907424041400041c00041500e509601113072580c2e009602200800c40f685d0101d500400c4251082c414840414020a488000003080030303010382c5907101408082da400700b04080c4800d4210004012a644403001d01e0004911065051081810300e80810162440002140c01e5514184220000c02081080850281410743c00a85589440d000d000c030065805000800048109201c0080c50914050b801030940346101d504142e86c5c1c00a20300d00414041042c1142c901e40e0340840203c0c1c1d42d039a209007047c3c2c1401681c009014480000c540142c1c61540092012041c5821004403034100 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 750314856 1250 750313606 750313621
    0x903051e010f06120b0612100219092607090606090f080d0804082a030c071703040306020f130330091203030902120304050a1212050307090810090b 65
    0x4a049100c2e1081050600d614640410b902140346504601b00910709601d00070481111450258403003216200181d002800c40e04484020042650254036810240a0b00e0300d050640407200c408200d0944032250300b038424000c640800c2c81090050031901c20100180341e00c0b0038004000d080940101c03004e00c40d80d210b0214185600240c01c661141869880c0c1400e592170f540c1d50f02142e00900c00c2540b04c2600c1082080041d10740d030304281c80b5034180800440e119896402d000f45411566840501500e00e00000d040d50404084221000d80f170f00710324003582d030702d0042d81080514401c180001ca8945145000401082007030312107480c4603081a5011024a5400414140005080c1e00d4100100d00b00000400108071045815000b0720300134100052005400e0300440c0c01c00d441c2c08050b144075003000034148000c1ca01440100c01400120012030886401aa11401140303841c40202044c0500840001c1d81540304d10102e01c007601a0100750362071003141c2c4422001030a0003040c1114103144040020343e04 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 750316106 1250 750314856 750314861
    0x110402040803041a040806010605070615152a0b04030807030203060f1e15130803031504390f08070903110f0607050d081b09100903051e010f 62
    0x10703511070401451034185440c00900c50348161a00c46007002505000000c0c001105001700343c0200f040380c898554480c01031400004849030481d0840c0d088220f000d0a000390346000881d0022950070381008807019510b01401e03c1d601444030040c607030b0354003c2061701d804c00001401c11030203180f0984a20400b0744518909405a000c22a842500302d0411318204020340740c402010861202c503200300c240400c041e01c001c0f94020215103840c082546000841c2440545000076130002407102002031405c609103280e1851300003510151281c0b04544817205c0350040d154414140300d801429001038071106501c580d00062551501c0f07014004950b404c00c03000401e9005242c01803040c9041e0391007014907030543c0c0d614058008014080c640107040d0001420071601e82800038050b00f80100004c01020002950003031690400800007240d610030403021200550010301540e4054500301c4817001c00240120b0121498522944082c10038464510b9601a083c40b413440c20700f80800c041c000f88500c00c44145041d06 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 750317356 1250 750316106 750316109
    0x40209090901241d1b0c0c100507030e0409140307050a0606090c08070f0311040b070b0603120d0f0b09040f060e030c0d0e0f1504080c010e0f0d06090b0a0911040204 72
    0x8691307816030440309149660b40080344c0c040042052100d9244d20304145031255048202490095448002c84440c10f02e000b40c1c10b4141442a460494a454042c0d5001000800111012030256442c0c921410800c10001c0128442c3c0101008803038a40c4200e0601a580d01003654003600e50301e01d04a40442d0300c1c0d0050040d142059140d80b640c41c90f0351102e2074222241d40d0940005010140d072404c507820705054290050000340807429040762101c091f0300700804c1c10000902003034071950001d10600c0c51401c162082e00d01008451030300003030b4401400c011002800c1c501c2d4607141e106030010208020071040f040041007140c01820100040c06459112039541d1150100b02404c641c007226041e2242071081b00f030b854443c00094aa01d120022110102d603100c1c900c072400c00340111000c00c041c00074a4080128400c1c0d00700034680703900c03940000c2002c1803900d012000b80a0003840c0040014040c011281c2200500d42d60280075178a561601a640314001c00040400b156441e4071000c50988502d07260003504e0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 750318606 1250 750317356 750317369
    0x609080c010c030c060f0c20190f0507050301060605040305150712091e030302030403020f0a0f0b060d0b090c010914031504020102070b13141f0e04020909090124 71
    0x21400c182c10348003912502d1403604110f90454030390500880100ca140149442c051194032425a9200b07201c07400c1c851012400c00a9002e80d02c10001080e0150800c007075141607071b0b0420b050311410049400c1660404010381c000c1d03074040d800c0c0140040c2caa5800700041040300c0c051015602a20028102d4425030070041d02d20000290030a007030305001064651011203524400d11202644155a00707e90b4202442d9071010303030110754003000b007005140e018400802d01003603034030240c4050b40b990f40d99043350300446c000107418a0740b00000114940c0303d0046a441164200e00a40007a14201d01400e0b81c610070102c0c2c0c5400229000360000b207103403500e1820000d545008014200006143c0701103928864010010b038114840c135a400110024514018414441250340d07002c03c050400d0081401505100703043c5006081000418000315a11190201c0046503407070401c0c560340c014030002c4c02030f0092502d456480035514081c4072100c40154020042c00007504020001e0500d0302c0c2110344203441d14443e00 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 750319856 1250 750318606 750318617
    0x50d021008150d0b060f0d1a0a06170d0908070e041205071a040210080f040b09010b10030501090c0c05030403030806031005070e010207050a181d0a0b010609080c01 72
    0x14031040c01280da03240d012511a210304510441c071400520412004101500c030003444109028850405500c070100250f41a101490004142e940e40c008148405101c5010743c0c5044c0d000c580c02c80300c0c64000030010300090620324070418010384c01e0f503164003c591941e008110250800215254086100c100f25000b46c8400912540e031600c0783c0e0b88683c124003010003003100400160000800c409400549005250b0340d10071145070a02c1401480410710ba480010311002c40100054480c034130400e181e01542c8500810381e103031900c40200c3d0141c54140105076100d1903c0d04103071201c50385980f1260403246820b1f011700c0744002110741a00c545900403005401c9400800050001c80d0040003182c3d00500042c088440740400107222004649040d1810000074010150980341580d042213200f02410045401002061810145050501c880b0440103112034035400c4120074003800c0c07890509a00c0180080d20750b076820310310303000302c184400f4020100031650074030000c10b4085001485100108068465 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 750321106 1250 750319856 750319879
    0x100602070501050c0106050301020403140706080c03072003032d0402030309060a09030b0114030c03012705030415080f18060f040206130306021c0522080d0e0303010906050d02 77
    0x440c3c07664800c0544489641d02e9800004a50b1024402000214040c16030103525600d6141d24905141080d44014208091282801480744900003201c0c2c1010750ba0a2000602a540c0c90510303021491504401150201108022280030b0414003490940d035000309506588110260b40c0321100340a4402a40541c001d01c40d000701400c0000091403202890300704030565907a2951a140d0040007600b045800f04450301b550919414100030144100c20220024410414421581e40c6000e41e148805d20815440e24071103002d00c1014422200a031810b911855046280da40c40030f40204d001b44c50320382089808200081c0602c0c01e03140d0f100140000100a000300352256001c0e0f90300382c000940181d0740304604211140321440c0e00d1080741c0056216260250b103c2c410940f0b055264110740c8158031341c950a003c00c20010a07040640c5a829400e080f005610f4040c9505040200340200b0000044141c40c01010b01c0c070051002010314100d03428864144101601c031418045003001d860002908001d02141 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 750322356 1250 750321106 750321109
    0xf060a1d0115021005010303020a03090b0304021e01050d0216050f1218061626070b0f041e06090b01050406150806191d10060909020f042303061006020705 68
    0x8080301d200042d48100d42e50030580440710302c01c070340b400c2e0300860150744466941d44c105134200c0c0c410f00052030b00c0c4420b10308524140d00031821000b80c01c450424858602400c0400703a038005c00c2070b11075011606c4811500d071000060100fa0703618001e18180c806204001c03104000520000d9000c01029901100c0c1c0d04040c640d4103180d0780d000c014600580e02403001c1c000c0020000c6401c1e0122603540c020300c05169840d01c0411101c01d0310b121010a4541410200015000300d48031000303680d0000c0c1c8a4180042a80d903e090140281c84000300d40c81000805160388070912810313802506103c1d00600001440d640d0710020001100e083e407140e0b80210140c0c21030603510300c2c01a807410703600050243c160b01c07d1001c2240c900302d0f4101e564000021811103586031148280d9006071066210343c5100044121604100c13020b00b0104051085c511f003a5000201d5110a0300c5400c180d50050004c1e404102d407000c400070002c3c41c00903046a14034000c3c4034030340002d442c00303402c001a40b0880300c00d50098501d0505200 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 750323606 1250 750322356 750322379
    0x110303160f0218090607031a061206151c0e19030c0f020907022b020729030f0901050f04110f060705100605030f0d090605031801050f060a1d01 63
    0x100d060340e0090f00d424008416109000941d8490469503000c1c1006141040d4003800312141c3d40e510001e10000150600c026440d400704a410014a0070001036240d50b507140010581c1c4145a40022580804900b003804494000d4000307102400852040c0001c0e0300c2e12401641da15051014400000b4000d1407140100740207000e4286040d00401e46040d8110680d00841d5001000303030380150041c3c0c880b80691700c22030b0310124804182145814000c404070718130b05009650311203600a1400e030403042000f81602c0d1498403041c88601c220500b801780c80c2c1c540b002d420000120308481045540d402c0c00300082005c00c0301c0c000c0e244296400110b03800052486400e102c800106ea00c2d0440d0024030030040007001c1a41000300d180c0000200078041000c0d401c000a05051210721450289103074045115203088039080341000040d21715501d0429201c0d6501c10302404404988500d00840d5480d10060092041001d00c50170b11a4000362111100c0720781c3c4a0001411444c25000d41c01c8a015881c0148048003152 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 750324856 1250 750323606 750323633
    0x121e0905030909040305030a11030603060106030c02030c07030b27060106080601020a06140403021c0e060319090303050402010e030a03091715070801080d09151101020409060306050411030316 84
    0x803400c807800e0000020100e01180c0040d6025404100007004100900c0c1c4180201401e03841440b60b140d0030b5081c10408a03076514018041e40081c10b0720344060700c6804d131080080c1c0c0c1d882c80000c1c4c00c607110706039a803c0c0515404401d0b103a2294040c5500d02056150303146000848455403620000d129a81c604441110381031000703803415046014140c2d824000c62440e0241e9a12105c12000c0da40c4542010b00c0c0c041d203881e00100d4020305ca103580c820419040b0b40c22030700c40464a6002d807a800e9a9944218060a80480091203112542d19003d90ba00c185a070560015110340e100b0b80f01d00c4c0000090604140c1e503091000740080001e41d45880074019001d00707102625100c003501d8212041c401c6a2040852240d100f26810720008010381c2c0104042001000429650005400c044507040d05002080c50001c8555101034107200b05244130044047d000d504840003071802180030481c6585924043c000f91109840039540e5903d40340c000101c92030f011049484a0044c4000c140d400401555801e0003688803 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 750326106 1250 750324856 750324863
    0x190617070516110d05060108010506030a0312090f020604080c01080901060b07061d0106180f02210717070201020a17070c0308093a090b1e0d0e01020a121e09 69
    0x1a148454a44c40d01e41d1140c40841c0f051015001c15070601c8541c5084503001401a84664440442e0201094001e0140e040680c9800c0001c5134150b6581000318100a00c810700a41090000030009000c903000716011140800036650325120f070702c6254031942031b54601c0c05906150b00d03040103241e002031030301d070300880031152440000360040701030b25051401c403510380d403199920003c40c1c14002103104042c841e415411165020031828409410342541e4404c440c0398040c0041403103200800ca86500801e030701e6402c880f20080a480700c0c0f03800000203000c5e401110405003c110b1040700f100788801100600e84c4182070558941000310718a0302c0495005c00040c1865219004540703081d940b08a01d41070013a20b0440c240380b1603428203800c4d0003509400d60b00c46601400c02120540501c8a400c425088a00c4c510008041c1c501060b200d1040000c64030a0b503085400507817510025049101064028103d5107169881d00e03503030821072815840a0b02d40e0021201c00000c0c0d02204501e5072071050307100080c071500 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 750327356 1250 750326106 750326123
    0x100b0a1107080f0c01120203190e0c030f07080706090e0f070c06020f0909090c030703150f06081c080f070c060e03220504140a0203060f190617070516 66
    0x1d880400c10f0800c00c00d2951a59550032410454850f0350704214000c1c400d1248403011861842e09143e40d080e641e003400d040005440c1c8841c081e04103050100300c40c000e0000c0c01002d44d4021802ca81c99140d5460448c49810141c0c003c0300d030700103525801384e038a4070f080725851507101100c0e5032902c601c0c1c0c001c0000244000c0034480d42e110403a020500c1c62000d0940d40a5007414240c4d02c1840408214070000003c02400031640860380e031a0450320081503c0c0d0490382d103c040703a0b00e40c555414904016010341e400706090189010800110f01600040701c0000712908080c5201040c4100d204449611044078040c03003000036940400c10107403003040d26a21781806654002180780c441d0b14180d080d584107280e003070006007800d00c00e41010785c00e911380c807002040110f4040065182607030b140101c08070010100b286c501e03030100c00103400b9112900611b0700e50b04014803548880030a03161103c0310400b01c4c0206d2000421494220004101c03080c4c04900850150300d81e24140300c040090b68074480d03c0c04608981411 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 750328606 1250 750327356 750327359
    0x803090d170c0a08030f060a05030a060c030608010f02120a06120b0c1308010b120d020a030e040905060f040515010303211d1e03210a02040506070812100b0a1107 71
    0x48083c0000b07006984030300b021954030b0174001400907440502400305446401ca4550410466400046024a20382e105401007044900081c0680080501c1c1e03020041d2035003403d802c8140901d8907401401c1c080390511112280e44c0300d03d2001411100b140c0655980c0154a41c115000324443c01b001300d510010300300c102403802e100420360800c103200651003e10161345a4030000c415160050081c40ca17001c40750000d054521791007900a40d950f180a8000d0280510030582081c140c466801c00810710703800c0000c40e6003a003440d041d506602402100c2c1565140105a062201000600c80e458100d80d01030307542410180092100582103812042803401207039441e5003243e42d801441d13180c0f02001001c20044d1003c40b01d118110600d402d121008440140c004103c10804503c8800441075440c2002403141c01560350036100c04001e10840d040694005c8007c1078800070070500d80c00074014003200c0d007903c00752902c0d440042e0508000b1801801107030348050200341c0d666840fa42c40c01c0c0650f0495400c0b1891103 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 750329856 1250 750328606 750328627
    0x90d0b0c0d060e0103050f0a0519060204081b1e010806010f0302070b01060203090a140907050708071b171c180509091005090d09050114091c020a0803090d17 69
    0x70b03100c07a80111140000a0010000c6c00030034081c030415103030040003500034440300c0d645ea940c6070040701000c0d003c0c1c0000e041c3c41c4428840240d040d50702402c0304900b21010b50002c0741b140a10b184110041c0f500c603500c0b103a442a003616594010503061305040c0c503408102e444100040d652141c20b210f0200405500384020400700d4841070005000300442c0d0003960340e0322032131781c14080400425040840e550410001030149600c40044690f03005401e46001c68a414582c42c1c258903d2051a5010f80000150502074203549407400303280d811101400141c94070641071000e207613140ca10351a075040707200480045146043d4051020310308079600141c0b040140715210000900380200a85168042d030740003103070152109016104807500305014074000d24000c40440401045c0341120b004490401034100e0105029420180a54055180c0140b62540790902e0807000c50300c0000b9000c4c10b900c1180e6400001826000120850344074103001b500002041c0313090744540d9000500c0e0310369540304842c00c00004442 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 750331106 1250 750329856 750329861
    0xb1912061419050a09022101140c0a0905010801031e0204110c161d04030c0503120403030e1005010f030f082503030e031c0b1f12060902090d0b0c0d 65
    0x70311078045225110040d00919038100c400050602c403d59250103402e0001d40d864030441403540040b040190b1001d1101030881e07009d0504040c409aa846102060000e407080e80000f401d402c00080d84c6403284a603561004441c40e94082c84060f0011462890209034903048404a6001c98005400440d000d40e0003420442107600c142c80c04e01c0300390003c6040220301020800c601c00201b000403401c0d00d0788001d190500c1c40c0c9840150004040c8000107002a08000c028410b0307450b034481298111805103411308019016040e0494604070720300600584100b40348091003042e05860450b0705c1c1c01020380c21a547d40103290f4001000b0794407540180981050000d41d1031060504508103400d41c0d0b40d80c2d8a629015043d9080e1034006000c507081841520740111082c0440b0610902070b06001c640c0359006c0d0080f402907104542c0d8207861400c090305844c2d846030081c5040001c0134425274200202c42c0d48486050490203494007a81d401101aa40c1c200818500481c0c16040794007440040d10f84200030300c84004 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 750332356 1250 750331106 750331111
    0x918071205010801060e06060a02100612020117090d0c02061201030606050a0906060c030503061215220f140724030c0e012304050a1403010b19120614 66
    0x1520486100c40d15900900030140100f01e040002e01045040880c2c0000c00b4600030b0015014210102e84842c2c820301c00c00a1241c0b0401000c000c01c80251150031089170340c8921107090380440d2000b01d0070141c0e6080e0400313061003007503400094000320a009070121200882d014040ea440542844000c00b07a500c500d0b14280214495040040c44170f140600b8001360300e100d6440880c483c2d113080d5041100d1600015500f104941c145042130b500c0e910903000501030100302d02200502e1050881c801707801224041e180340105803c2d410203083c1c00200c01c1c2440c100d0039039440180005a41001d0800195400b03520192100051041d0707030074aa100c6a4030010045c0313001604441480c0c2c50304490070035825104072079004905140c000e04a020700da001030302103504940644603211a41880908a03401001550050640200415801a07407410001c7c10aa0303c905c1192080d4070744500800940380c280c031600844034040c1540c0b0107191504040c080355246600d0161001a110b03040309402003010000a031 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 750333606 1250 750332356 750332371
    0x1106010806010302031c080a020d06080105070309061a0f06030405030c0f01061a090f0d1104090f0b0f0f04060b0d02060409091a091002160515070f0503041101050918 73
    0x9a10340c0f46004151030400c01048076a031501c086c44035076008541c400101da900110707600000d80d6404080161100034400b5501c081d2a5505c1c21301848001d990581005003c103000701c00130301a00200d0791400c000196400c00441e802a0f05203460b4030070381025400717558807501071015a81043c0000b900e950070804003156a503143d9646080a11040e410160044107050300e41d802d031810608008081849c00e04000d410314498a144100b1004100d00385001401010014209204100e03451030410719403203a46030221118003908000900e40940a85190312840451124041b20344664998800518084401540100b00c5004135400342c2c5800700107000800b07800c240010f1000711800c0c032139501d1962040e103d4424201100307018041c08001421803030049100001a079a403900b11400e100f40003511801441d601408a003803554041c8109941e11950454a84480c2c800401e44101c0b100c0c8001c03a0000c4c5968010052010301b948100040e01202c540940303598440aa00c411980c4d051000b1640d05 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 750334856 1250 750333606 750333613
    0x1109060d1e0912020706020d0909020c0c03030a0e0f04050402030c01050307020a020a1d2815050a090204081903050a0c230d1b050309011404170c091e01030b0711060108 74
    0x2622444e0341007002400030b0500d440600002e00401c03c000345018114891008015008503901707034442e00501041c403403200020b040704d0744c8402c0742001401e200b4030503207203034451a50001c45101d5420a80078541c407841d80103015003030b090051300040d00c45800261a40302103201d603518040050321145010005003c215445041d8082070800d80740c69034800400109280044071140303021106844505c1d0001e0482c0b0030042140c4c606205640d0345501c4540c0903550041a074400080c040d041c82d0300802c1a90202c800713689070000c0c201d5204907000702e0240000c0000310200012103c4511409144401500c5140000d00740c0d040100801403540c40c0008620301034004612800c54a900102440c0c101707a00c0e1801e0300d010f0503880e01c0301a2a030145489050500c0340000111101d42c121504440c05044686040b486111840c1d030401d80c1d8004000c8454000c1d007441c000f1580e8000d0030040305194102c0c01c030700341c1c500368210360710300022102c003401d00700c244080020741030407032a414091940a000844002c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 750336106 1250 750334856 750334883
    0x60f0305101125060e160b03091f06030204151409060d05030a0206010e090a0b04060b01090512060a15080307021e0a06020105061f14090310140403031109060d1e09 72
    0x104c0454004e40c00c40c504503442038152024818181c4900f208807803008140c00e840c0c0d0303078a1101030700382108010080c0000011140310b801244865000401340da000707482c10000240c007044001008503040c007403402045001e0441400724581442c6403980841e02409a0440b02400d640b81d900e15000744480c240560807000041c0060b51840002d03961015560000304213490a40d00c1340441544c0140c0080e00d01520b03420507502a90069807844000e100c040c0980b1030016841c810700b40c546409507050380340c2604120b20940d03c1c009006494040e19000c0015519012a6a08105461202c0a007040450307414040d541c1040c0c2e50b44415000824450700045014034295040108400b03502c083c100840005036503c9040c9548251141c5030319000521182d5661940380001b0703e0a480070140c0e800050804c1d20043c0340070030f4010381d0b41c0104e129850034000400501c807440e1a074050b580300b80390000003e200d001202070840d00325902c4140c5182426803840c1c8400030300c07c01e42d00c0e584415074464030322102 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 750337356 1250 750336106 750336113
    0x901090b062a1005070507080d0b060c0a15090c0603230c0a09050d0305041a0c0109060c0806030d020c06160203070602030a02150f04020907020313061101060f0305101125 75
    0x4400040f19024002c00061400c040098242c0c000e8200281122101040c904c00e8900c103a40400304140c0010400e54995a00206441c3e461a805900b100c0000e0700070001101d501940c003400e561198008803100b034050800104400414850500c00c030300201601540c180c418003000388501a060140c0c0f11691031000c00400b401c08074145d030042d8040c1550a0088012075400825202900c2c490b55802a01c2120303900010000d009500a00c401075207031a01d0302c0d040002590104041041940703d0503850b0b13840500301610740b4040b0369403034056000315a1504651a201c070042c0781034422000c91100c201c08c15000701e0b141c25019045800507910001e001170245404001e032060081c105c5d00000c40614040000702401c00c00500001d010700d46610100d1350460091042d0b0b80c070105030840e00c1c4611942c40000810510688103e0310040d480d00c04081081000d01803c40b0070f4903000b00090055154105000008004040045003041000d110300d4880510000c0b009440c00c0a41c0640c1d10800300328207 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 750338606 1250 750337356 750337363
    0x1211100f03060b120c0708191806050a12151e03061d030a3c090503030703140708131d1806040605060f04091b0f050901090b062a 57
    0x4001e00e00c403003030611002e980c041584d059140c3c01940a09407541704c0600c0d00c0c1c0254240107510a4a85844110080c0c1d000f171a4460500c1a0f601c00004e44401e603a99210401d468034441d40c00c0303240010300c4000e4a040e02c81e10315002940c5c10051200706909856443c0310460303064840d45050f400c14a0414000c0080c441103010b6188010b0310300f011a1540395042140581d01d209900341601803080e00b05170414000c0780d00c61804079080810302a000003102050a89003614040e180400204101080c00b0529060001c2640d01a5905844d04803503485031024803400c0d03410800702110000002c00c0300712496030b900b9114200504100c2105080607038a0341441c0c0c41a100200324804c20000e61210782d00c04200094060b40144d0008800942501ca0901142016051030b180c10380040c00c01101c3e00401c61f14000e40262000b0001c4d02d00c00468507080c2118081c0141d21600b0b80c4828203000610600325181e1140703502d41c2c0d00610061800700004804e14000c4820051003100c5412800101708088060 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 750339856 1250 750338606 750338609
    0x303070804081221060d02090108010b01020f0c060a0e210609010b0d0f0b071404060905010e0907200a05060a05090d0e0303030a0b04020c15061206101211100f0306 72
    0x42d421418005004542d020312198014548648113004011900703d44859200c0d002d119005000c645032580c4070f007a2103000c0c0c45040301c1540144240c56100107000e101140c00e034213100000301290f247c0039a64004465020780b014a0035802703507022070004006c1c00c070081c01c5513080b5041800743c6002d04d484200642101d800b0030040340175034880100c5a0004800f690000e40160b0300114002182d200c1d8441181d070b61400c40f1600101c03c200013004542e89410903500c00031507400f640d85141d60040304080c00a050010b036000d401040c0b02e00c0e0512500b01031341406d111450460700840304070041a480740b501e8054160b80030a00649d40360248007400b10140201d04e410052800c1c41c0c81036072200f0780429500e1000801c00e81001769141014042d03039803185c040b01d51200d00241142c5846024011211034210152a03052140d0723480e45068410301c401040711441489011640c00b000303440c0c410051546510580d0490b401d16440401c50304a03030701d052170752850300210345d03d40344000c046800141c11200709 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 750341106 1250 750339856 750339883
    0x906020606030706050c01092f04140f1815040b06041406010518090c04170601030804090f061e03030f2d030b06160b0a06060815030705030307080408 66
    0x290108401d5440000c0c00b9003c541c91450480c0d501c80340791071714600400e40c07100001e00c00120300004032800e00c100d004034802c1ca100c6000001c6403400c000c0030030044841351007424110107502800689003480b011f880701d910070f40c10301c03168049128540005081401c0403940b1001d001e50715052000740000142010f500c00c400761070070068510041c1050040750b4004000604206000441030f40b0108114040c01c0c5104002d40301e4003690600c50806a1070f5007140c000c912020600450640348640c0004019049a400140c0c00f843d050902140f000a001000c00000d40151620f01c00544610451280c0100568054054150364214500146200440000b410800c602d802154508040409480d9041c40c4d80c4c0ca48403201072282c040990280034a0600c0951040011404140c02d001002d28500b405120b00c001c5480d580d5000c10100881c0d0780c60180c2400508480005003450800c02c03270411844000504a0701074554601c0040d1441e44103900483c1c0100021504105614081000c0140d4580 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 750342356 1250 750341106 750341113
    0x1181e030c150f0c0e0303070f05120c0114160503041b051e100f020c012d11010c0206070c0204180507090c08010f0e06150c06130506071715011b03080601090602 71
    0x80c450001782c7d403805000b801814066405418008000e8200b007084c4118108000013601c600d020704d059402066290a05c818103414040060440d15004500e012008515225039007191a107869010408094a1080c48a82e2282001003500d13a54014940d050741d4070700520f01c189040c1d51051003035015214880005000c5203211981c9a10740100350031008641c00c1ca403034a048001c000e03c21440c550554106140460704ca41c00c480d1031507003c4682c10040c41528001c2c0402a006c01040340d44a104448110009014169007001031820340c01249807611312010003c1c2c680e150341c03541402d2000540c00034444c82d0f940c0b03592104441e004070403140180000300304141c81c00e2410803c180126401005035101e0200004c1c000b0341c841c04401034510252105044409910388141c8a80400e41c00c070750151401e100d004001500b26210382e59103a020240184d0b04401c1e40c48600092807054461420744e414041840021003600c504031094903803c0380203070740703031b10707241c2010b00014190f000642c000e08110340 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 750343606 1250 750342356 750342377
    0x140a0b09101203021e010603030906170c0309100f061d01140d0f170a0909020a020d0509131109120a080f09040e03071401181e030c150f0c 61
    0x7201c64044000325000388000c0c0070040c00ca031800b20304204440030010100d042c0c0c48042c00300014150701040a8030301c03980320a0310440d00ca03901070303821280040321441491080b1001588100b00040559040b10383c10342202e040402c0c02181e43c050745c5000004007070166070703001c0400c01c0303a4010581030070700380e1180142c04071035041c844100807843c202c07980c650142d00c5041d001420812403d40001034980c100d10b00700515255004a800d2540c450a034140006640c1100490741490910869008504e02e8004022a4007604400e031070039000362400a610841640c4010621595070003001075011000e45c446035101e10480401c20f0120380314101004680c04061244001200c1e9022598440c0030f000c01ca50311070780322038006005080c1c03541120101c0d0002003401c0c4100407071030908030066031580001b0700c602948210008416051003001910b61130f5020a0762a01c0c01e24691440182402458500c0c40c900300350301c0d00c403c04208200380f007800e0f41d41d0f0a02d111103000144907850605a8900d0034500b0306 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 750344856 1250 750343606 750343621
    0xc030204030b060f211507030b0f010804080f040909140114131b062f0c06030c0409060b0408010f02040b191e050c0c06130b0d0e01140a0b09 62
    0x420043c4803501829582c48042d40c103035039104010a4503200b000742400340c0440c00144039200c0c040184050103095a050205150b58001c2c0220040242c010b09002004c0c01080e004684001e400340040d68062810429403403041010300c01400600f80e07900d00031520404901c0c0459503010150071a070030301d900d032050007580c419504100710303003100c03444071690b4005851f070a0040121001d00c2400100d410210400141160840c040c41480c019461420034150109032860b0341e0105040680030054010100c1c4000f141b4042d006160040d040c11700d80350030300782c035200c2100c211a07154001c0c0100c100045401c000898090003181c0e1a44e0300d03540250704003072400c020304d109030042d120010f41014003910342009040c40f800341181800c40b03490f107615440c010341802a150303034810407200c441d6005080b08a81d890501804036070030303e0702c0400003403155403030411401465040040401442134440042802c4080d0901418441052507400740e15070341002d00a5000310382a5006141c091031b541c03410003611 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 750346106 1250 750344856 750344873
    0x60604150f02030c060106200a0804051306120807210206040807083c0405060a0c03090305070803030f150d02040203060d0b010b0304020906010813030e0604180f0c03020403 76
    0x80250350810001510845109a046020341242e181c4d0a00c510000051a0355020840f80540804900c81c40d00039151003641c1a11030440040140039040d080204014a007010b030041002d00c0d000d020000350b881e40300c2200c1c1d003810074519003c1e5080c00c000f2030254240452801c169126039180207224040c0c0200c104060344501004102401002010074600c040c0f20510381112140103140301d042e2660803110040307240071a501c0900789038820051a0820315011100c00710f406481e1300a02990400040320001c96020200c488210100700b4817100020001d441000650041c19014000d0754603841c080e1481020003030002c06501041d02c4404170541c5c1e985401e001c546065805403000b6980342d0315036020804910036484001c144940000000882000c0d60000d54007a620030ac03800b4103280c0300d000c0119070040c019500409074008040c0220002400b0b45800384580d070000e00803500b0181d6800d404403211400d0202090341c1c9454403807110350703034081d4440c64000c1d10f910f080c00c608190454540080e03 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 750347356 1250 750346106 750346139
    0x114010507020103020f0a0306090b040b011b14030705060f0a06030b0403141b071a0403150e240f1f030b0a11040b07050c0a0b0a03090f02040203130506060604 70
    0x5110340010311078290792080d0115040d10301d01e134886039651050000018000c000520842c86502d10f8008084400c0c6014000c84002d818142d50303070340748990748900642c01c280e00503501b00c41d800d010000076225401c0610242c90114000d202404c02072810005448040710002c101d0f43c84985060414800903e0040d82c3c00c3d006a01f5192502024041d040224101e11540b407928241d040840c0000b045071070009041c405590206800815410306184004c541380a54040244a049aa1800c690040c441d60007018100c02d260308490075401c05c482c15950746161020b4491149030010204880740b580c102e100e80d000000d80240700303485142004820030f9603c0900006103030f03d40c0000818001551a000041807101d03060415640300c4d80c4684007a1250302030235040340d01d401010361980304c61901202040444054415540c5840d1a640c000c6005110006049402110100803070002d62902d01c040c0d449040030a441c1070340a08a030514524043c8000c0c000340c445c0c00304000520074041015484c40 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 750348606 1250 750347356 750347359
    0xb010801230a0f061101050c25060f050103062d20030702030c120c1b0d2310090507090b0d0503190e06130303081b0412050d02060114 59
    0x300a49815003440700d01e114038150320740d44200040e8012500e64140f6240b4011103031552503200601e00c401004500380c1d08100d840d0040004140701e98030303000c204040752407a5088241c05000c01a001070741c80e0004c4650110701441620b54550060082002a00c42c1c002c590141c004100c0180c40da80d02e00400040e0391034469007c0c0e5440d0200d4000504c800a060001244003071409601c91401050095036900132031a10015403040281e41c00090b0300301c0c02161002001e00d0040c0400594582141c47c010349960101d542001000006001007094009801203100e0701035032680c44281e900040341e2078500100703070311040640b411201720300140b400540c01080352190100801c8400e040c0b00000c0c010005800060300d1030000140c0e11550400da04501280c001480d25a11071010712a024081303a0f01911f5400c040300c0984160500219014090281c1e12006600d006a4040c9189102c3c1002d60015401071210030501d600c28810001d0512100354040054401001c0540c50030a40380c3c00c000c020444d0740d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 750349856 1250 750348606 750348629
    0x303061017041b0803030c091804050303011a0912011b09140f0109050d0302010b01090b04030f0b0a11040602010e0709050603120f090a140a060302210603030d051f0503010b010801 79
    0x101c20f80c001200c0b01100400190050b652249054102c50585502c580d54503481655035801d141350705105081490300070391b000001542142e080403012080040344c1d0701540d900d103400b030002400c280d6602062090120003180041104240f508821149000c4290384030b05100c02c1c030b2018402c014658400700e0032048101e03410a01070f1501d07030041e02c1401c00da03040280c025403007460317001c2807680541160402450a03230756042c030a0307500c601c00c407003d020701e0000815030b84155000d01e021071108000103030000d11511001924084107000104a0342c0981d01c10805030351280c0c078441440c40d007441040000c180d03202043c8001e22346200000e4451980b603201f200c0741c500118007016a00d100700c042d44d00669000d4010390a030758645011800303c00610380141d124002002c40814801d01c240243e500e84c2640300501000c803050f00c00e0b40f08007110300400547e007621050004000000b0540607041c010a121a01d03508103900e800040d0110381d0103070b04038a0003a81414070600c2243d03800009681110785180a1 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 750351106 1250 750349856 750349883
    0xb13021e010c030c021203030f100b0a0e040b12031306021203150d03022a120115090b01170406021903060503030a05070f0609031d0d020d080a0917030306101704 71
    0x15910401a10a411b4911000c000c124403904500c4406020310556441c00c2d114175560380503014117105460410000440d100e41142850925811000e808900140b00b02131441d1500c0d0034918640182d926004202d105d076408202082e018000840380480c82d5101c4e0340b039803030106103401024140c0164540246400480c0c101454406e10902e1004120b01c05403081c3d0244919049404c8045140f01710310034400e9000040d81a0700500c80c141c82584428440d02d4040e00d0440404010400c12100e10706212000509442c003040340390701e0b50b12807481381c0c0c40140c44010a440160011450780030440034507191090600103994000243d070701044241c68550340c2c48611f860003000100c02d8400041c002414000d503441015002545841405049510001d04441100400c82c2c40c4814480107500030414241003001b29800c14010301e0f41e003c00e810300041550b41e400465440110300c0c42203c0ca03a80000c42800003d18007450010080301c0d0fa4541042031110070903030b1000304c0c200a400240840217a054 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 750352356 1250 750351106 750351109
    0x20d09060c053409090b010602061530010207030f090f03170403021201051902070206070b06010e0603090a02010810060206130204150609030b06031c18030b13021e010c030c02 77
    0x700f102c40d1203c904004400d035143d002e0000f401c1c507504115404410354001150040c40052464812001030300fa990582c2c1e040014040c0d141600078a52001428400c541110180c1040400412a02540005a0b02c45c01c81c100103202c520509a180304000d016801006501e980c038140360152078015010f21204052a4444045480355a100940205d50304034010454407044d4440703031140c0740301b821115800181001d2a0101d2055200096200d0302c00d0003144c000c611420301d0786520080604040d2041c0f904100003035056041226011410b5019524240455a000c0052900328181d44590b404450803c50082e485040080110040c10f450364411015566203401c007540b0034248040c080c011981700c1c20001c0c27445030030380000d40e0288501408500c1300d003000101c44114041c211003040705c84c00403440440340a100000e802a00d1b1486420110100d10003d250324003682ca80e801102c4020b1952051100c20703111120340c0c02c00302c0031000c03051000b641c1241c0364075a9140d15180a040d101104d10 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 750353606 1250 750352356 750352423
    0x15020a020102250e040b150f060a08090102040e091014040209040201320903060c040e06010507061512030806040e0601050d060e010e1e010e12030a0207020907020d09060c05 76
    0x90041c200c03542581c0900c000e0024829a4034001c220f040e8102c010380000c0340078007205000300c1a002744c12460400201020368032421000c1d0f0031600120000d407410b03507100c2039150706d1310081e5424176207074103c1d00004452a90038070446500c0041409814003525060700003800c1c070f5000034400b03070503c08003d80c2c0222201c1c48205001d21201d0740548014004040d092011031394101c03010060085c4582c402088283c0c0302c0314141c80844011003002402544c030400111441d13003007000110f80b4241c4a40100d60758030500d0407824090002440380d84900314107814001c005101c05018140554035105440a046101042c010b054a206840c4540c1e800c4581c64440c0003090440290880c951808094202c00a000b1a458038001080c0084041550501d00072908035a24034501400344d605c4586c41c891840390050255a0007029000014101140303500481d044003022960100140c01100803540c04540010b001005060a03140c0008064420f03941c440d81daa10845003450315040668001d004c500148 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 750354856 1250 750353606 750353609
    0x4050a05060f06010306170a170c12090a05120c041e0f0504020117070503150d0609030206060111010204081009021c0f030215150415050a0b030115020a02010225 71
    0x5030407940e1614100924410744801950f40500190a107480010704080a100d03240590036a60003815081316240c0d142d05074071050b01200102c0c240184000d01004070240b011011041007845015076803107096003048120000c90b00640d00c501c4100300580107450000070700386105013041e0385c0014640510303400024800b6800d440038403a0b60802085980c40d0402c2d41200c2d010301c0c401e8840e1071004c1c42150a8000313142c8103d41c41c0c0005081440054100d220300313042100d5050024062801c02403293322004280c45240e501600560f1000040c81500c0d640300818009480035000210304150420408540715295242d010300050303207030404242955240c90008640c840d1106034580c00c21101e28001425050307003401030f0003600a07c0804000c2282c1040f4080c440c066010310305029110300d104000042c040144032200c4c1b0101c1150200d480d0b100c2e208000080c001c076084998603507140019a040c1d514040f95070381d00b190005c452100050341c0002e01d81d40280094201c402007074942031095409203809 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 750356106 1250 750354856 750354863
    0x90309040204180b010309031b0f0611090a08030a09060521190e010c08180109060e0a17070807020904050a050304030f02040b04060b04290a0e01020d0e0a030b04050a 73
    0x340010740c490307554540045500c5043e505000c442c110030015401c80b2181c4a010f408944420220000704000110002c0e060b442038000f980d410604d500c804027107413400d800c0201e868a00282e91b10303c61900009140040110a0003545444e41030000201050100c0c400c0c081400b0307000c207008141c0310480490000300c1c0c050004001481ca400c0d41c3c007000500500300d41200c82da150401c002500141801134617420b070105d4036104921344900321200042c00142942140c1035584039082000129075000e5291481030304001807034441840c1c1064014400c5030b84010055100800030f001c0051043d0703054818154040300c181c0110340e40c034141282845400300000740720380400180807080080b1028104079031130080e00c041084c02454800e000803a0710741d001d03a00450009020410000380241c0b07100100711600130444a2651198903d90407a0300622000c501080300721031108d46c02d59040114450b0000c603498140c03140001c20000c1b03000c1181c03d000c050300060f0b08100140500c0000c1207040d001c07960 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 750357356 1250 750356106 750356111
    0x110d200f1201021909050a0302062203031d040614091003080324040b2b06061401031407090b160b070e0a06091406090121051f08030a0809030904 64
    0x34038450307603000350300070520107400000c0412941c0300706103d106240e0079941c01078006a400b5045808000658000300d41c80c207121050356817103804002e150094040154429150850041090f80b2001c83c1d031302c3c5043d00c690286207401020004006c10000740b603070518040d40c20480381d480b1400d8031400890709400242500f90000203016203450b44071004000d480c05000b80d2054141c0c0b100c10441070f103562038603150303100d82d040c1c000020750640000c0c088103000200000410031b5440c5d03a141410b41c0c4903076110801240e0982c0f440d07801d0f546c250160a1441d0140580c21040b458102c0028102811034080c4401003100810b1440005a104001c0c3c1ca0141e040350502c0c4032403401460007052007000004840c023a0380100b42c001035083c025910b0314255840c00503d412114001c4040c0710301604000001d50400140d010202d0b88424800d0040300c40c0c1001000c007161070324043c01d050810708001c44141d02c00c610301306030130031542ca0084142d5070130183c60b1030544c40700d44840050a245004010341c0941c05032 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 750358606 1250 750357356 750357379
    0x30c051204170412530c12030405011104080d0f050418020304020109080c0d0f171b151302240d0c02011808030610120f0603110d200f 59
    0x3144001c0600c039401072141d07511300b0130b5a4407446008001242024250501d05204c4410300d16101201030a5601d00c5c0d032203080c4030002103043d00e07114a4915585150800206100034454207008840d000720801c1c40c2980341c01c0c68030048581c0c074110200601c017003082c01000340d55032501c80c070112401460b880e424603102141d040c1c071080080d403041d541280482c3c0c0c0f044000407a00c80c0070624940e1040c0080c640c03020040d0075228054450a04502180d442c103241c060103190001d0308018101e00610b081e2000700c200c00308000640317841081079400d03090360303040001c0103814022069000d00d9181d040e24103801c44281e00c00094481112070584009025000c03880400c00c0b0200d40c4050307001d5080340c0c02031000240040074035440c0c0041d5040074080f1102000061400d080a071200c990703103946458400d4031840040c100340200c4410241c403000840d1615801c10a1081c6000c0c0560850001c0303840714902500ca40c3c1d142c10743d03054920003c85411078003126400640e02e041240000c5400500924900c0e37 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 750359712 1106 750358606 750358613
    0xf09010b091e030d0c230d050a110105091024030f02030307050102040f3204051005060c06040515010f050108040206040b19030c051204170412 63
    0x8030020001d241d546082001041031040d40c1d413032907007044807483c00803801b070300ca0550105a0180c0300200c0035010800310f07034241442e40300c3c286a5510b031b0b000d1005482c04154000383c1e607002d510740f100700030075039001007043c204540f0648400c000d1168151603418070714500403a500e00030404200c051000408501c043e000c03182c001800c403810a5140d07a6080c0c2079a000360420038402e03610f000104000d1500342107a683c0c1e54010032024500c9444401601c4031224611206881203486c0d4001c206c9007940340e01d400c0c0c06042d0150140c0e6540000f591643d0740ca100541c2d04840b2032250514081101c442c5514242c1070301c01114072004201c2c80c00004550040300035100381d900400410001171545072060080c261102c0b04056180c414540d15005030455440300d460906100341040317a06100c528403603c0d1030b4001d40c001c0340006603c54240780504140200c0e0071188079024280d503c541030 = true := by decide +kernel

theorem cover : BRFrame.Cov 750179856 750359712 := by
  have h0 := BRFrame.cov_init 750179856
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750179856 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 750179856 ≤ n) (h2 : n < 750359712) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
