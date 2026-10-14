-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1199
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:43:33.724793+00:00
-- url     : https://prove2.me/submissions/e8c70faf-e82c-4f26-b61e-3b19e83939e5

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 215467625 ≤ n < 215647482 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 215468875 1250 215467625 215467627
    0x140a03020d06200403061404111201020d020d270308180a081204020f0a270e0d11061f05040203040212120403140c060f030901060f17011506020d23 65
    0xf5504441c1030940c040d21045d9920740c1400c00ca04003945d1124180c030f0099900600080410030b28a080c0005c540907030841c242103541c28451a0802600c0303000800761202ca203200015545c400303040001428001e000703065009034802d07107aa400240c008080c03076041801b070f80000c140c183d08000c0c520f2a11800441c000e015050100301c03841c210f42207030321a6004034800c617011000d1a8011044c001592014410341c0e0480604406d408640300280c042007106203000040468074030740408906240c000c040d804240052800e0011400c0041c050090a80000300c6442c100d00c035480d510340040e5191094091280314a6000011504650351f5000714120312881600791003141003203459044054104c0e1000381d03400d02c5100f90300c0407024808680501e07019030090101c0c0c00c0030241e450b241d07400d402c002c2000c85c480d9030710403010400710024140750b030040504d106803020f2002c0788110325013950082130340500f90300d00d41c60701840015004200000d500300303503280402d50f80d4000074540350310b0f0520104491036164 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 215470125 1250 215468875 215468921
    0x31210f020d0c08010f0c1b030c0605011401141206101e030e1b10031107053003060d0b06060d023c04090203040f020909011401140a03020d06 62
    0x180e40b80148086a81c1100208a81c035180398044003522103407140ca50008074080d801d81c2103480300480802c40c2c5030192a242614001540d903100442d135082c0c100603041c640203603154103250f91002c030650010481c001c1e411b052000c0a0441c5542c840040c017824031413083d500002c0ca50a12508040c2903540d00781d1031004060300c1000000d0300500080f0b2203c1b00c00d004400d500104246c0d1502210004400500b00e04400900b084c0e0440041080220302c008ae11004c0180f00081407080114100e45840d2080b001c80100e02c4100c211000c14402c20a0844610188100001ca59130080f4040c8102e8114883d031100e6543d80d0005003080c8504440c1d2450540301003980030032440c0400c4400310030744800140700d500b03554401d50300c08210080001a040c402c03040009000391034254002e190414804d1540440c01100b0354000380710010101c803c139110343c0d075070040700c0048074a0f00803280c01800808046000814100003203480c4240600005c0e025004881340081008010b60140024884211204d2804a = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 215471375 1250 215470125 215470133
    0xb06070f0b0114060702090406020c01020c1c0f0e03100f0e010903081009151707050405040501150b0309070611070905160f140d09030903050331210f020d 68
    0x20020b008072440591100354140d03c0d4100034084030106600140307050017903643d40e52003601030340c010b00b1146c003255024400105483c2c404c0101c01c440202c0704d49525141000070800801e00b854404be00d10402c048015810510303140850408016000307140d000c01c0c071042600030000540f624843c041c00c20b43c6800c2000b000c0c150b000006d01d0083c0baa110b0014003060307031007403468103803801da00c45480362440840c8208522226410800c107a410076030292000503a07100005401c032101207030190383d180d4442d60740e94452485141a00044e010f481169429400c0c019006542e903031080c00b0f039406101c0c0d003c504280d000c0c020020070307004040100d0140014508915402e612818070751014000c038070180c0340d01c0c1c0c3c414081c4404201604d8000b040d05e04103075411040c1005407a0000c0e05800703201076030341c0120200350144000c051a20f200d079000700d00106450207e00107842d0300f00424444a0400d40d050080ca52110680e0100d1524110555200881810003440102c5502c200a51288800ca5950108 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 215472625 1250 215471375 215471393
    0x6030a081812030c03030609100801060311030d0207150f0311130302030d08040b070827161d060d020307080d03050a0c030e070e071209060608010b0a03030801090b06070f 75
    0x900c02070b61220700c42c00b89661019981d005013031031340140d50801d00015159013440316415500508d041c01c03002e4500c1e9034143c0107003140e03503941082d545840c201c0401ca58505082001d6581d8040600c020a01d0034945000d0f0190041c1a003e210100405442c00201c3c41d4442e401506071001081c8406644200190f03400c110b0f80140d1004038000c3c010076030000030050280e405203208940141e407041040d43c03a08821034040500401c4d00d5188003000c0e080d0650004180100f500641807240103040600100e5059502d55031240e0040410704003003e404014040d032004d03130a42100e41071b01d104442581d03a00c0000d0404085410500c19840f8a8804409050b4190410742c011905c043c2d080001c41507048085050301d81d01400703a55554821a002c119400200c9440b9034401c0d0035140c44501c40b00d41c41d0000f001e070703480824103641440d00ea585c00e102002d400c1c4074a2065030000c8a0182149140d84c1c0c003e07102d10b50520851802d1035498400807001c1d16050201e42c030741540b103c2800b109241c2d6140000c51 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 215473875 1250 215472625 215472667
    0x70e21070501080411040c120c09050306010f030503090d02060c0a081305060a08041203230a050c28050405101814061c0b0307060207030501050f130b06030a08 70
    0x440c852000005055400340340360780e002d1a005020420300c0b13800381d0f091002812900003041c04004000d11000ba10031040c3c0315040c4601440da44149039a45031808051920740c040e005146200d010950400004000004035042c407a02030300d58041202c4580002040c5000d08622b440d40e81c00303018080c004004003140109030b02444401c100c40c1460b103d20501c0100d020345030002001c68000d101140100308107074a0000001d0141c600030844200514040324400c1106600c0755150440c03a051217840185401031603801164290b0642c24164240c82c1d00b40000102c0001d0540301541042e441e5006102d84200c40203081c01900008500d0404100208100d85400c504c403140b544035100460440b01440400c696194001c000900700780f600081c0111440360010340e144044d5550112600d603450611a5030020a1582c000d40900c0d45581041c40c20741e88003c000310b400e1030001d02001440c0d0702c0900c001000c60b4100002c82d2566442c4004286012000c8101401d291800b1900c51401000181c000103 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 215475125 1250 215473875 215473939
    0x1c0e0f030c1020031201030609260706050604020c1203100306050c03060f090408030604110d0e011515020d03050a14090c040f020f030f041e051507020a020a0b03070e 73
    0x2803c2c03403480c1c1e2900d0f402444400c40d40050540010800b040e59600200e07541800307030314400300410804001056520b03c003c12100519000b0070b0200602c03407180700b07080e44013100761390541c513020071800c08540f12803101c6202180d40c6404008130f00614005078841020f907900c070000b0071082c1040000441c0300d42040b03418074890740151075081803606143e407200e4001d03903020b030500b8195125042008050a00008814144039060000c5801d0f00407900480c83c1141c0721a000280c01801848061420a0507030040390440402c042e12070300241e0300140707a4008000c9890001410707251001c204002d03002d0310400d0b00c4801d0000051005068000c103c1c0c0d03c100b1411202040b0945200c0c000030241c2c00350820b1400518030034000142002c54100e82c07103078050b1188090580c00c1010040345075504000c504c064840758421030380d400202d0301c4040c031185c214006000a010011507540003402480f201d0080703200c0d000011001c115014007074100080f00001c014080c110750341800740c87c808076140b0402030030 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 215476375 1250 215475125 215475167
    0x100c0501180c050619030203070216090b011722030c0f0b07080114030c0d0201090b030a0b030d0525030e1206150603130609080708160201021c0e0f030c10 68
    0xf0340fa142c00c81c12207801096049800c2e6000c082c00b00180c00940009040d03400303501502503041c00d450180c216000c0174041140d4006060b083d840300041c080507102c034101c8031807040c0e01c05018040c1c852018000100030540c0d84110041000c0c0b40032184204a900002c0440082069400400c41c510000c40e00ca542e003070340c075076540e0b07030b0794080901200c2800d01c80e650f0550001c903020a49814819500c0562034010704191000c20341c0c82c25180d070705038005c03540c1c0c06045613555a402428034052011158404240c6080d904142c01c1c3c140301041d00d00000c2500f00c113020100300400406005108503070f600c1400401d82c902c480b4060800303a0300d44108441c1220b01400414079005c81d483c1c060260303401a02c2102603404900055a01c010081a044e50705903050b00d0140545c4001942b0700c1c00400369022650100c040315804c0340300192078103c074185102a0042c0d46d020000780254800c55400095800311780030101e500c1030340003081c28a0030800d81c040d01302c0d550b1200350103403c0d0840b00840c00c006000c0009 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 215477625 1250 215476375 215476379
    0xd0f0b060f0a0e040c1707060f030b0108010608090a060219090806010602031603050903100902040c0305010b031603140702030307020f24151801050406060309050c100c0501180c 78
    0x186519040825030024440b50140700d1001040c0303100e40d0107403181241d0341c0c0f602d0703d4031a9084c010b04c0c240b0300c860856000da01c05210840c0d0214075000240b10034141807000000c0c560001e488868140600010441c9920005040200402450281c2d513000a400c5664055480c5180030b1a02840a40e0f800314080c2180041c064100151641c121400760b4007450070070382d0801e0a420040c45101c400d9040201c14048503119680601070340e040c10002081c0050100700b144140026903450402070000e00d45000d0040044c0e82000d421250700540c243d60410951007850310075002018003054402441079423004001c00325400200035405400503408850700a80500f68083c0c3d030b441034000140c5083d91020511900c26a41c480180e00400b411407140201c52909002c01e100000c40d144850f08008030030300410843c105440b9810241016240a005000c0c084c2c8071650703211030041c94503005034050aa6032000e103120741c0e0000d4001d03a1050003404400c802c021301500e45010800103540007401c070800 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 215478875 1250 215477625 215477629
    0x7050904060f1a070f08071b08030912030a020a0303152d05101205060414090106030b070f0e1c021e0301050610120e0f010e010203090105090304030c0e0402010e0d0f0b06 75
    0x80da0951381d40300601000c0694981d540304241e03003203071008440c04008a042e66804c881010100e60181817880300441c1c4503488242000382452000c010ae40f01c9400401041d500140c0c0815011410340d0581404240d40d0051007010803850150740c03100e81c003001d00340744950502100890301d4441c1c00b2003000000801346c46104100b07143d40e16500580110301c900a140580e1529500015408000240f0015280d130315010101c201c41c100316146045030355204014410000c00300d4460f44c12079801d2404d903491040040c40501340741c0d00020154400c40080e00d21140c0024444040100036901801640500082e46040d403420035060060034030a508000029500d0304000c0110080c06029556507140080707101d9499004001520003e0b42a0058555221401c0c0d024001c1c041007448080005a40e841e200c50701310700b1500040d2041c01e41d900100400c2000c1f400c11f104040a0314401c04141011351540d100513030780e00c0000c110312030700510655411010b00001e143c90320f030900d0040b08880396540d58070003 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 215480125 1250 215478875 215478877
    0xa050c040e0703060b03031903020a0228140733050f0301050f0109080316170310031209081509010c17150301020919060212031603020307050904060f1a 67
    0x507095000c0e5100a4040010030480d800603076950314040d060740e00d030465008130112001400146800882c0e00040c030b50f450603904101803002e400840e03010941590a400220380400d1240e840038090051054003101c0e112403d00c07460000382451001e4220b5406041140d002e02038080c20003e40e0651081c04002d21540290104c03040c1540003034040e8a583c1c00c0038200640984682c440904000002c0d07000b254160302040182001c01380d281450b0548480f03854200860b07620f60300300c071440e90300910600c0341c411800c0c901d1400b501d0340702c0c94200340601650000c40e4261415400100c2c0e07442540c030f000c58140d01c100510390044184000a0101e892072003400c2e42c0002007003c80700034400a04000503c3c0385a108401800103000500262416607103200042e40c07500710601d2010110303a0044204001c64040003600c00c0c2c00080042c00307045107010307001481d080c441601e101c81810b40000000d00e40c0b9104004035414001e000303000b00301c610344404205640180380d00a185043c4058019055804142c0c0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 215481375 1250 215480125 215480141
    0x4060f0503070f0b040513090b0403120f02070f06051e0103080a0924050d02070c0f050414130f02060d0203091f02040e1909050f06160507350a020a050c04 68
    0x300304d8910381413a00b005d0041c11601886131119490755160800001405260503074000c03800b80d5680103040968800c4007048800b80e0460094a034030403c408000102140400d032030298000d03d001809544e40e144d09102030070741100949100c20340c04004010003403c00041c1030101c44a0b03856600d030b00e40711615100c3c1d02a00c8904504011491040e88a545214400521045001d441d02500340034840d41c900760301000c107411140e40d120000740244164141485085841c1450b005444a035050900c1040822408540d02a081d0380311304602c1801d40d1202400c80e03c00f0003030381c0c4c411952850100802c3e40ca0b064615480f0745820081400c0200c801424020b0b5800d8482c1548107800c0b42e1503c0c203200d000e640c0740e00d6180420b9a1039002c00c42c040750041c455114008103140140120f49440d091164410650205000a10400340710440c04580700740c00f6140e854100221841d809400388802d414040c0940c9034107501980006026903040340e01180100c8090310420840340c808101c101040306aa85030 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 215482625 1250 215481375 215481389
    0xa02060a0507050306040908040801020703020f010e150114011e0e12030c0322030f0b0106030507140405060c0f0f010b030708070b030f07030b1509090f0907050402071104060f0503070f 81
    0x3440405c049141950103042c540e4424041c861070035680302d605500f0390b0406038017500035800106004403100c0080c00b0b4464100b000b1000307000d044030301c442986419803044c020250303801440041e031560350340502c650358080c00e002401c003039014034136140003003071a40449202805040818500d02c5884400800d503400244c0f004051400d1401008184c40c442d00c141075180000410300c1c2002000c0313401c81080c510421b00074040d0050039814071002909170360b1302820700c200700510810008000491002a102650400c803250380d59000c0c0003601c41e2820420503000c070000e005400c4429815071055112008000068043e42e00c400d544072507031070300c590340303481144110340c0c0c108001241c0060448500c2c2e441542404e002907826000004151a140d003401e21480c0c0d2240040d1070112447d00385031840c1d111035003d14444041c030b81200c00a07104c100b076203e058011a00411035400b084284401082c104501810805c1511796542c44212000d56501c80d81b8001e0041403008500784c65500341c6e01041e2000303 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 215483875 1250 215482625 215482627
    0xb01020c06090f04090b1f080c1c02220e12030f010303080403050c0d1206090c4505090709030309030201080601031103072003040e0a1a0909030a02060a050705 70
    0x10b038001d20000d400050101d0f944103680361124800152540c0c00280140c007912048041e4000d0400103c40194007a040786ca5150710013000713094607540c1c07580c10203c103100f04000005001174900c085501790550b041d1010b0303902900b0b50200c9047d8500e0f800000103c074400100c6e1520200460300504038441035030500c3c4890b07050401480442c1c069000160030038440c0c6042c078906800a841e842c10304451072130240000c2c4001700d20f1020405580209000f900b00c2030002c120000401001504841c40016002d42d024030051486c0c941c0000300c1595184180c0c00110720b0020000788e10340c12103400c0940252441080000c010958840c0714200301c2c03003601d03415200ea501d42800c540064400c41401060941019287c2100340b000c0d513072540166010301440d44920900c0e07901c82001c0710b24108940302c05101c42e0300c1844208244040035111541000c0809000240703c41d040d0301c01410184007070042500301440a0900580c110004010f1446503070a41c05d5448948900010303130160b49083d9148400924 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 215485125 1250 215483875 215483887
    0x405060705030702060d02030718050d03080901060b0a050c01060609080303042607030c12020d020c01050c0703080309100f09020d03050d0b09010f0302040e07050306041e05060a020301090b01020c06 87
    0x10424000c1030160301075012242007048940c00030703a00c3d0f0f10003000c80c00c641c1d40220034440341e1500020840c0003401c80174580c03a601414000816120300500801400700803010000c2070801c0400c2d80700e10050079104000300d40c0d9084c3c03008040c0196024120381c07a5690b280581c006031051041c01d207003041d00d04d802c01441c69512951200b58800300c0242403c1c40700310510030145c00b042100b4000f032110754465229246114a2410490f5107440c14182d00810b540010364544419a40810f990071440ba007400d040751510400c0b507410307250031402d400c0106908800002d00c4003000c2e0010360741c0703142c520a980910185105812038400e880302800b000350414030f01c1a0700b2001a000740e02810031040d001100188011500002880581d820790081e200e02e18101014415410701c1d02a07024642c01c1c0340000c0c42060326000200b5955200240050101620101401c00c2034042c1030f41081c009401404444803410300c5007980700294820710820350058070b01000c03003480c3d500200f102c0103001c000903c0c0f942015 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 215486375 1250 215485125 215485129
    0x403020c010f0e04020301030b07110a021f091208040e0a0e030f030c0d09060f0b1c111f02030a1b0309060302031e090f0d020f060412110a06090b06010e060405 70
    0x50460b03a600014880300395074a2481d41c4440c4043c1d8000c50259040ea00c1d41e0a0124000d440c000c900d082c04006c0303401c5000280c0168440d00340342c6003e14900c000c40001821008822199011650884104a00400411030600c0f80701c070b0141060340c900d10340e25407003074880e40d12030300c05c5a004250350801c079041445024456400c05000d5588a00720300c012915200d5044005412528800c41c00c980d03540d40e030380040452003800e215140b000c5c00c0c00e48501001e100d885c0c0b080e4500e402030142c004d11080c0c02c5c050b202801c0c0c45180c05d02e002101d103048078084510b00c1d201e000c0c0d103e82211810500040312000341c007589d8410301d81c070042002c0c1c058454000b003e0814030200c002e940020850140d4001c1c0600103511006500c618610480c0e546010700441c942c03d034001c03800c01d400250a13030115030108900c80c403805008281c4940103507102e061a4151380c0480e10079a980c603440720016405028010212050181030b0b040f10007014410782c0b43d003000340e98040c015aa6410b07800350594026001748030a005038 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 215487625 1250 215486375 215486387
    0x201110601121101110d020f0105130507030b04020301230103031b110405040819050405121513030e0d0f0b01060f050d090c03020627061602012609030a170403020c01 73
    0x14207810314001706078007408029107282004170314003080180e0281c44d025004100a108043d04905110344015a0081c0d60b1601640c40d6824007020302030103049000700d0119038096100480340240c4000c01e060400c002d0402c505002400d100960202e604041c4401c0201c1c0c4000103154210792200c1402803284a4005010060900410071512001c1c10001d0240f0707080301c16004190031101d6560349548504000921880003840d14000840e035110220014806042c84001d640c4008010203000742c0003404e0500700c903070131408a07c0d581c00c955055195024030500e00035510a02e4014059031007541d0340c941c01102e0a076074002070322001030003c0c4281030307010b0060b4001e0104540540d1011038481e84a4000030701c954084411101e200041100340c90983c0f14140909450b07e40c11070b00c01e400c005078111441c07461a104100241002010800200c1348100c80042d22235691020982412901d4170164141e501c0d4002c89059000c03d0070882180c4902840c0d0541e180b180c4e03496030107003514402000064804e = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 215488875 1250 215487625 215487653
    0x503120901230403020c04060f050f04060302030c190302150a031b0e0f130f1509020a020318120105010303110c0307031104330e0705030708041101050f0c0109020111060112 76
    0x8500031b0403940010340c0e44a01454001e004c80c0421003c4017881c201c204018040c0011070079000b541001810000742e07802040385008450280c0c0c510700980c2c0b00d03a003020010182904001c1d809245a0f0b41440003208840c09040340701c644e41c6040050071000c800e294188000040c8170340c0004c041d000e500303446003002c007611000c0e4040580741071a4061414200c1055079030034110311035020340e21090110030040032024000280860341d003c40c030b803440d0010000e4403485030300390401801960020310030703851b06d5003404000b65440820081055503180c1c40c00401400100000c00300d540724000e055500340c0f6000c104030080380c1e841035020280001d030380188009030480c080c0301040c22282840914414002c4242d003e40c50f00d50002c518100c40c2041244049004007802010401c10180304200d059030300080940c2d08240c0100803030080d528443c004907174032311a4000c02001502c0c041801240400150451826070380300b622807081040688041c6951500c0034411948011048642c06011420383c28074029 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 215490125 1250 215488875 215488877
    0x10e0303250201020606101202091f0305070305090712060b010c0c1e0e010608070c0c050d0809030d0509090f04050118030c03030b01030e070303050c03160503120901230403 76
    0x10030710106404032801d1100d04091108101081d4104208541c1d0500030958410402c845508502e042d14500402c0b40404144010206a0004020b00e20342d55800301580041003240c5011141084c00400801418080d02c1407000b090801c0b022420101010500a080e182c1114003010b102c40700b0744605014198146a44c2c0c103021502100c1c1020034410010301d005070241e1a242d500318040c030560642c504041c3d0f03000a07071200c0754200610013550b1040102d81c10101070b181c869002d5810781042c442011841d480710382e20240050940e0300b000346220240810100c12426201455440c960030b075401d1181e4500154044202d0380094108c1c4d01c28020242c0042c02040000350300f01010000200d149501c0c4c03800d4000c80c44a00d80d9500300f5505000c0c0142c0c1c80d40c05c1c6424030000900d01d65040d0b503070029010040503c030020409030001c1c28100190780b40070786080e800c2c494040381c07410702c80e07226400100f060401d80720000011301d0400050042c54101000082480c44000140e00004d40a00340500110 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 215491375 1250 215490125 215490127
    0x201081e010312080a020702150c010f0608100e0d020717010603060212180708100221010b1e030c0316031b12180c060e1203070f021302090a0302010e0303 68
    0x1520031003400041078040e40c4206410001c100d480c020182407103000400348114640101300e40401602c401c070705901c07500c1d007034400c03680c45030402e1311010b024150fa018241829460b103540017440100004031403507111444035003002402e590207199602c500490b2200760144e4803c4108000d00c00f010200034480c0d4000100006030182ca0343d4074141642c1c024400c40e560103c9100501c01581c0c0c1b004441504c50780150001e001c194507043c0c105490720082074000e4107043c0e0100c0c0388600001021030410050f07074a0404000950303155048807816400c0460048941010088081d141c0c80b694000c80b8040d0441052541c1544d589c40140c0c201032900622003010982c8038003000c0c02e10100c40140990b490041d85400041c104158089004c40300110304500da4200702c0600740b00411646842c4409840f10380c078100c802c1c0b012000c04229036089030240d4078014400010110306001d4801c2c061441e00d8400c036900da00310031710749c0040404d030f0150000071a8002c03200c400420056008800c034804180001c1c06433 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 215492625 1250 215491375 215491411
    0x6031a07020a08040f060905040c0c08030a0b04060e0907060504061202090406091406040f0902090619080604030807020106050105040b271302072907230f0c06010f060c020108 77
    0xe40e0f00750f0405c0c1d00c1030085030051201805001e4015a000b03024002c00e503400c10030351007840001403840b00005030143c01c0d0b910000200d03200c01d0050700b10304840c28002d0001e1000d01c1d076a0790103982c07200044620341d499000b1404003041d490321034402c8030215481c542da105090722040082200a42c00300f11155401a5942c0000801c4920ba0090170f800005c13111240d401b52400340180005d5460510b1400c02d10703482d1482c05001a42c80e132810b03075001041907440c400e50b82881078080c1e2015102d6008006144680d03020441050782c003411030384c4203d42c1540240049540d0704015255805030340101c802c400342c10705c03901c00802d48046200c1c480c8550118014009540c1c40c000c01c56003c4908110070407280c00280c44810700103031860040342e42114445080c019500050080c03e00b00016107060100140704070344d0a240c00421828000303882402c0c1c403055032030001140d0f10034540d00c6001c980080b80036600c000140030808400708030445201e40c46018640b502a070044408000c0100700c99240c039000804 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 215493875 1250 215492625 215492633
    0x703020c0d0f03060312030515010503010609030b0c0d181e030903150b06030c0706050c09010921060f050609061002033106020a031d0d11182806031a07020a 69
    0x2490007201d261f4400103440d0810700080300001d40041001c606011041004204a6034400398240449420030307801c0c07105880d0041e8800b100d1054070003e068850030000d80818500d1966081c0481b540b05040d0702c10700d0306c02e032200094100006880600443c1d60700038208013041d803075441c2400b0f07201d00034000070f6506480c1c00082d1039074009641d40800e4a00110f004410448503100e00c9801c200c050b00030300d04014000700000c01d603040c0c90280b40d2088040307021380c9803031600c017444e190070040d4054818000d80c0c400c040da08000780f200302c800d184607106100102c0c40c5828500364400c100001c80d0b001e5032800344038031310920505e40a0f5a64285031900030428001c100b020307400590280000c0e074098456a061030400038003a03101803c1c0410408100c0b925071015a68075000380015680c0814070400500b0503e0000781c45801c07a600764010351850004004008003242c8441d0b58402c001b0742d80707510400116075038a040312103a0100600c0a8642e03003500040400c840d200b280d1041d10307032044600c2d12080c4e940d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 215495125 1250 215493875 215493893
    0x80c010509130b0a030803100e0105030c150409020315090a02070201020a0602130b0d0203040b010b0c03071b0e04060905010501120203032703030d0f0f0209030616030608071403060703020c0d0f030603 88
    0x8001d8072506004008d100f0041c0ca40c0111200030032000440c48000d5040000003621078440c843e80c2031003907002d10114401181007409a60050101a000b152603181c0090103203054041c582c2e100d8490045840001c11889051007650706030342d0180d00400b2861415078440300294044900301707000844c2c042c1f00040700e010900003020381e074070043c40258a80c01d141c82d1800c06550103030071003005040b01b403080160827034000090ba190150412015158040500c2600e05007030780750342054112409039020403052103c150084801031784103c0082000b40c0c0e070340c0e01000c000c25512000a515030020070009000c800ea80c006000e500e44a10030320300844400d48006451540400030700700e85240c85245800c6407400381d10a513108810501410362902420701c00098031000d0040c2030304140510140d114200c103110f5030000d00030704100001c90781d03440c0d00c90f002c091508105c110b0b41c510034491403001604c00740c480d000740c03100142542d008103600e4025181c15994200201c0c046030030141e6448000021031025a = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 215496375 1250 215495125 215495129
    0x3030203070b0105032407122901090501050906030604110a12061a07060e0a080d06050406090e0c010c0302011b08041a070206010510090e010608060a080c010509130b0a 74
    0x5001036686421514007054402c205a1040d4401d4101040b01c1014408604d00e42e8070b002c9841c0404809079691413025102c0700041206540020300d4222802042c00c40d003800c0c4500e42044035076129400030003d00448428807640216400250103204001d0700341420001303581c0080300203102140394000b10480702160b070802802c0c1d00010710b8501d1380050203a102c0c45140701a00341051f01100188074051040e25521406400622a50352a4010460328a081c08a510300715402074800742d0728001c802c03000300505014001e1501c25441c1c02000a40c81c407042c480d00100000110140c884060600015100c2002d44c46041d42035541310300201048080d5040c803146800c9581d00c41400a0070030341026003030100e1901d5000200b000c59001c1c0a00d440c2c0004900703044070400c803401e03281402c07919012503c10f400c640c000741c0c410078594000b00d0301d103800c58441c134400d03042500e4080400d503a422000e42d489103d0110140032683c00c002113002400d0030f090b440b5118510440c046564480b140115100780307556 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 215497625 1250 215496375 215496377
    0x7050a0b04110a060806010e060706150303031b05130e06061606060306050105011803061a1201020a081012020405042103091217130c031202031e12070e0310060303 72
    0x41c010a620703c3d00703150000180905140c040d07060310300345001904c04103074056040d1064001040c1181040440d4001d03042c10422000e482094940e40d01d0050301070104880c0341c40740901c0244500001c0ba100d801a0340647c941d0380302801d602403a00c00802c40082018141e260020001c1120480c40414140c0c460f8026114003800580c140c51418007604460041c1c200c00d04005454098120102070b02c00380074150b9402c040b0000d0301da601444903611a038250240c56170844540a0382c5211920103601920401506448045990b501d0b401d1201101009000d0710ba0b00074000c901c140b0150501c1c0e8001540203100340d92182c0749488080d0350784003400c940080d900000380c9680f5003504000010303045480c641c643d8100103820075002d049019810301d004080034210f21003441d1a9040c01300144100c3c1c0110741090310200b0705001084001e40745d90108800c01803d006004520b03200300301000c210354034a40301550800d115112200112500e00d00001e00907498132801500003001c264501c1440010b50ac2 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 215498875 1250 215497625 215497643
    0xb0307260a0c03060f0203040b0a110d0e0705180705032412030a030c050c030405152808010e040b070305130203060a06050418230703050109080705161a07050a0b04 72
    0x503510b402810f030303981c3d10b0000b02506d00520501001a6165102a4008010201c041400c0040400365039890180c901c00081a90804007403901c04440454101c09940c0207640c00544000e803504080072040e4207803102e07030025100b0000540301d20f070b2944000b5841e2001110800526104c0c000240e4134518003010140030b90000647c440b01140c240c803400318600c109042c02400c088121002d10307180d0044e4400d00c5d000d0541d800c80801c0a07820031041b83c55001d82e00701510081e070010316944000001540c420004503805000211340c1844080f01c2c5031143e544241204080d0740d8802d4110301a200107072003503107003103080301d503000043c0e505101942c803501040f10700049140c502010001a9200c2203400480d5031201f1040d80d01003100f80d248940b60300746c40035241500582c90315126107003a00f46d80c00500340e5440e25004204200d900d40c002e104190240d03045400e48280d102e0401414101842103540c2e040303078008409a40354048000e84400340c0503005441154005469011040204582c00c540300a0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 215500125 1250 215498875 215498879
    0xc070f0303090e090f0304051309020604080a1e02030d0f1e020d0f0914060304020d080304050303040b0f0708011a0c15090d110c0f040e01020a08060a08010b0307260a0c 74
    0x45005940d440b020400c01440608040340c0026107903c6580600c9000b402d07900b03aa90301d6180e094000c42b000544c06003440c1da0b1259108051030b1296802c50003200d14032440c450801072500d04122400000b40c0003400b4004040454405030b0301c17141c1c1014440700b403140c1c80d000c1e40e1410144141c40d281e2854a9006060f601300c01d510000c043c891034881c0301d8288011504c00740201c3c800c2d00401c0100f0304040d9405903580c0c8440c00000c3d0440e03510b00300101480c20000c100003c110002c40918000c900c500d01c1c1040603111000d52201106d012146400064144001002442c02c4070342c0c07520000c100034400758074044a00e4562800c00c0d841644d407003408a0707030906000d0300c202c0400401b40b10200600d0419182c80550502c1038035075200c1040c480c440c040303501d90b0f09402da9a41e0b110190260b0454021503075401c21080280c610340b41210683d110302d0700c0200c0010300c580d040c00751510f2071030000c01402107107080c0b407005842070001900c5d11382645c0c940c6c04d144141050411100f22881d00030403442162038 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 215501375 1250 215500125 215500139
    0x8030a11010615021b0402090d21080c0901080a0e0307060e07051203160201090e07020c01030e0c010c02010c1e0503040e0a1415030a021504030c05090112080c070f030309 75
    0x94643d4000c40314940303152030001000303038007103031003454004088150003807401d6034000500640119801140c2c4503405118400401c801341420b01c20b82141600321010001103c003007541c500c07408450590401071b04119411541d807140386415800300e600c40c1d0004a00b042544d0f020701d035400181c0e08039040c0b9660402c03201c800310704110150060a0454600d6840045070141c0e0b138481c018a90742c0d10600c0c2c05601c000341168064440c1401400810912421030310302140004d5482c082d01074a0740c00301c3d03e00380ca109228000452070300c66841d01a181c0c100340d010564011a01488020801c4da0208054440c20542c001014218401a07000d00011900c5170308000b01c0c0c0f4001880a00410030301d81c80e01440045060780c002c1d5003139111b1440c01706400030070740030000f10307040c002030a800035800011508000125a90800507001f41c07400f036000b0000898030f5030300b481409982030090440c0d040c82412540d0005070444002d1a0050000080d5000159181421540211241c000300c0c04102010b034140030300 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 215502625 1250 215501375 215501381
    0x14150f07021c030c020d031110020d0b100509010f0512010f0e09070501080621060a050703230c07080403060509011a01020c01080f1e090703021512011e08030a1101 72
    0x3a1003490035102c1140d0195a010b030250310f000e43c00038040c8010b6003a14080c5806038030500181e103520320a5460060240341c400000b0f50200400b088424070302582204c0a08181e40b0005a42301140c07509860014080019901483d40d0440c110800204201c81c850768801e20f81c002e0b000b04240d41c0d0610000703003032803110355000d0002858590340b54020242007182d80e84c000ea03110382004090311035015803503260300c1d0342da801031494072a4401481080e0074000340a1080d40130034440d076550381e0100000007500548000200c0c0f01c1c81c000346c0a40e03540007c1070001c071588004005151046030703460b284ca5030300d903108401d90fa0121091051769566144060009092402c0d4100d9803030248003422500080c540040d00701c0d00007411200316040480d00140304001400707140c030361121440e0318080052410f80034150b5107410900049000d40f4103030750100000d081d241e00f621310202c22a941c04802d1b81c00d08101000d00c16440100448241602341d00043c0d44000340000c020020039942c80018041040c1e80142c00c1d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 215503875 1250 215502625 215502649
    0x120708070e040f12110613020102120a05090609041d0109021504030807060c051b03070203071401022505060a0e09060609010212030a1103010b0c0105010f03030914150f0702 76
    0xd054a05020840028503819a0381030f410b90190825000840e1100100c0d142c540c40381410240c0e04c10300092005041007030003824503141c0300742e01300d030300c00301d02802c0e401502c4c05130f1390600020801c14410b0895602d05600035066a001c080c1000603803001c040c028822400300d000d04100540d64511511080d400c00c0001c0300e80c15030711040310134907051a5913940c08003407186c150301409035a40c40207070a0959101d5400c03160341d0001c182d6062401c04060b81c08035260361101908038440c1c42402c8001940540d103183d00c04040b20160054460000e030700e0b80001c0048501b40d60844114400780010850342c0e039040190241c0b88043c2d03284003000c2040c0003031201240020f8122841880706001d2144142e070b001580c803d11594030850542c4a459946000015107038180d084c11200c90040004261003010402034014003100d5802402540d0380d42c40c419010052900002d00002c403007580901065180d191403491419001d05511200f40341d0028642c20341d002030050640c10750001560701e0a5150005074004 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 215505125 1250 215503875 215503889
    0xf150b01021c0f09030804090c020c09100b0d020403080423010c05030f0c010b060409020a0f080112121209060605040605010504230d050105070207060305090d17100512070807 77
    0x1014884075a0800d140b20441015041080311030b01040399501c16488035000f19030085d41e030394841d41c403a4100b00207800300850315401403052030181c5803241f410b600780038003500d07600d02100102800c101342440b445c3d1010b9210b00049408000010000c2c0c6804020f0000300b801c0c0e084030003a00640720323046e210204a124024100f05450000c0c901094000c0103c981504180741c0d0300b0b80c0c841031100a2400b500c07603520700700c1d8043c0c0c000c64001681e22064004120046813591040e11030b59020b04141d075160000c0c01004030a03180045401c0c0020b10804007034502c0181070a00b681c3d0041164005002d6070703801d480c215040c81d103481041100b810030380226000ba202c24244181018201200e44100d00c001c00c41141d0010780c0b0403c90011074944404405020390048002e220701c3c0390481010f9910100351240100181c5840b0000310405000310300c44040714080d554019400000440c95445498003400c0d90000325190100041d080d03940260000d042c40a020140c06600e28000c0c11500700075071030303001d55 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 215506375 1250 215505125 215505133
    0x7200303090705130f0203010e040308010e0112020402090409050a050a030f0f120c053a05010303080f0603280b0601050313080f12180105090c1003090f0f150b0102 72
    0x1a08600104440064400c165224a04c070048510b42e14080c1141424000810340b0010000c04e08401c0b022682d0b10440c0252038a010a036a5000d140341c5a06092003100c481c03180000321000140781c160014214240018000b00d606106902c44908115003e60100c500d85c1c0407215240c1090741015001440c060a0300b020038148480200c00b0704401c0c1e99008120f038440e40e607030341600c40740c0c002e5050724000448100071060b01c40c240389500d07071158041d8821080c50b000c0c0303944409034511540a21070580307600d03a850000d81e8880c032050900d8001c01405d40c3d5854021902820402250904000402c62019601810500d100e007444c0c81184800b070042410081c0400402c81000142ca1a401c1c6260307010307172101d07640c04a41e500e600440c09601c251030546208c841c1032080d112407180c00d4140100d0f64000820a5894103180340c1d83d41c1145444007a0001c03031203642083d07807030b0003548214182e5001e4548000e8885850343e512104844603401156501c000100c40303101101203101c0c18111010031300080c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 215507625 1250 215506375 215506381
    0x40f0c1214070f0e030109060e07032a0e04230312060301140609040501201c0c0e190306090b070f0e010909050601020f070305010f2003010909170307200303 69
    0x1095540b10600ea0024011450200c1c13040351425441075072200c0d0000d500b04008900e01180a491741c519201c1580d1640c1005169403a44100100100303005a101100f18000c5113055035044e076221008005480e40318041805462012040d0240c480b504403001c0a550f0728a244000e1220350440504030341c1c0280e00d010401200c4c115202d9065400c50b604403004001c030794842c40d00d24090003007024500742c603810640d00c0300900f8844070007402da10700c8100309194030240c0d1244c000c42183e001c00c041c500050000c64040c08a401c149883c4004034141903846410b0707581780e449050569151040840c1c01c900540100450b69034084041040882240740c98400062081e0000b00840c4103030180703007070030b66461002c10810781c000c002c4011802185030540744002da0b00d007003160003424210290b1284504001c900c0050110f1648124443e041c00712086041da420b111280e4003c25030000225624040b060031030b80481c25800242d03126070099a20308446034030303040b841102c81308034100c0aa49580f081c414 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 215508875 1250 215507625 215507627
    0x2702030f15030a12090302010305090c220209060301030c0f0b04081b0414040516080a050a11010e0a1401020c060a120905211b0c130b040f0c121407 65
    0x35400010826642032000c101400180c01c16844140081440b00c5215880210340d07088013a4070100d0303000344c034108104d0f9201c040d19034550440442265001140402103010200f0358602030999090140c001030500c0d040d9804030f01290710030380050302c4c10781c40d60108000c0030458940f8400070340801c002c480c2c1064602001556215195249862000e81c1301e1043d5803035460710b034408084200715540450b014185810030b2a225400c1b07080603038104585810210300d80000289280c12950301c080200080852612a150311040d000b18540c1040490b190459984c1d0f20b2040000180c840828030307450360030900c2d001a01c0c042800301054020001031000014054201c01d408040101c900004543d01c40585042406d0203025068040409030711907284110a9203040500640f005401088075410381000240d5030754540c2c03900042d804595281054601d003445d401014030314a0181c00417902010156081d401c5c1c0d86541c0031440080c0c0c80704402901c0d075005003e080004602c1d500100210309207418 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 215510125 1250 215508875 215508901
    0xa0b040503070608090c0409060b0a06021204060503190608100c03050106120c09050909070f08060603071a04030c0314061312030c260105180919030302070507270203 73
    0x3180f82d080c000c52800040006500744214020704100501c2001000500d04e40040108030000310703107000c0d03e906240815454000520050305d48052001c42d401c03d403402201b224079500007410107000480314010070301918070350700401001c1d02c8180080c21000040d8020780781121444110001054103140040011540203482d43c0c00034208040007056200100034151070781d042d5039002d66000840c01c0d082000303520010a070801680c2440090440d9182c5d50308a03142d030f440341543c92a5054002220400c07440444507803407036001c49400782c1c5600702580e0380c0f55942d00070f15981c01a03c170070001d5105088448810f201d4140d0100482d488400d45902944075654180e142041300024180e40300c240c008402d029150403943c102e440305405d8203103801e01c11150311141080c0700b0240160051a01c90013442401c07001c0a101e115420014000c05207410000b42e0310303110405064051540c00c11844021030300500c05034001e848000b01180c0c2da00f2090b803524080c055101100c0300420702c18000d102c4201e0b1003c03 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 215511375 1250 215510125 215510129
    0x4080406270515071a010f0803120c0705070810060f050303070f0201030b03070504050408071e0f0308040c0e041a010909021e010302120708040308073f15050a0b04050307 75
    0x1c1d5103080d40c907601d032010000a20822401500c5c1c0841e216150180100b0020001c0c1070340da00760b880b620380561320008151b59003d00458846880407202c00108159201d00c0a07214a50160703040740c0107581d40b180710900349280f2501000600d07480b08820302004e8070350031085006000640080d46428115210348a58048102d0001c2c1015203d1807401001d90f800c101c600c000d440c00500411040c2070503d03100c0040da020700305c121004440b10030040004010b0b0111212565000b200400d41a2242e90381200d010100403c1103d42c00040320700800c1d002a80910148079078400c058400910144d0700108800c410b0503404044442d017480c04420050f201d00c5000c200b85000f000100b502c0117107500040e4041c0c080c8260344112040261308211905a200d100d80f40910300035141e603000303510b400340e0031500585401d00030681003445140c100b004d41d102d40b410140a0086012900000744190341c10b40c00d44103803800d49442c400c034400c8140550300d8003140300030051020341d01030340c41e142c6404042501d5050038 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 215512625 1250 215511375 215511379
    0x2130510060c2f0a170c03010504080414030715020609070e10030b0a061e090b0a0506040e06030109050708010c09080d0e09040c0510090303120b130902030f0105040804062705 77
    0x204403103000e00784500341d4210341450000e0004c0e590f030783ca03100683c00042c0c4001e101031482c0314800b0080c080c1d09040c40f0b42401903400c4002d5a107000c0c10101800f051141d003c01e01501441008800a8943c0d20103900c540c41501307070340c091711081c10048a12441d000030354001c040180c0d41e2806018500742d0107200c078002c40394065106429661118001e000030103069120b5290622031260700c06202000c40080e20945079001001c100c03503480d800c1480040c0b462400390380e030891820032090010750202c0c542c07245c1c455801400460315101a40c0c030182852202e500203c1b05030f4442d05090100c60b00106481c001e0841e42005140311815150002c00880c2d03009e59440c0100070f81c4001c10203000c1481a860302405c8041c266601c00c028154000b0210040c1c1c1c40140d0016080101442c000921801650320030340f070041c50741301080550200ca00c000e00024a08980c940700b440090420460b00303004d80d0780b169014010860b1214038001005c2c02442d1000e42184050a86e00107646c1e003811600807080c07d80e03000b = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 215513875 1250 215512625 215512673
    0x7030b0915040e0a08071205030c0a0507050c04090c0513050f0708040512190807020c0306010509181506040e0f120313080313110a030f02090408040302130510060c 72
    0x4000c01240c02000c2499243c00c040c0242c12094040c4001c840040036560300c030f046200003406480204803041c0c00b00b60303a00111401e00f0060903540c10301c03490141010900981c1990481c6105d000010116400c4800c125103807050340000301f0503480c00c10b01c0c580c001400c165061040e89400300484040d594000c0c030020504c2903040120f402d1040802103003400e401c000c0c410b9941c4515102d0355079145007031181c44000150010002640b0030b4400b2036aa494140098000e0041d84d007413804211103000000c184101c1200072841d14030040c1c00c00c00141d40103c2400d00c2c4603001382014001d00056030400c00c3c4629081d03120b2079417440000c20004842171046172000000d5101d0300d810980b0704142e01e4a11029140b0b031b0011091050ba414090800c05200f403080e40301c07041d8070005000380442e0341680e201c003400110014852001504040203c5580a4440c0310000d24241e00d960000c0c900c1d14031580c29809142d80c0d4000c10542002c0003112340090030203400d0103c440201f0340d0b1004111201c0955206441d50 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 215515125 1250 215513875 215513911
    0x806190515040515030f101d0624030415200307020a150e160b04060509060c06040827280905070507062406050c0a05011d0607030b09 59
    0x880703500b80e0740a00b000500d01c055500d603441c100d031a1038101795103490009400c00301003045000100c074600d0456140b1200c070315804011116000164800130105508181140706408802542c0710814688402d1908039580328240740c140400d805058660040600c0e1801c091901801c1c1e88044100e0952100c2c01010b0b6256147c1000728100320400100615009800041011880300c90f0041c1810500c40000c50f481c1006003a1421449010740c8190280402c0403c001d10440c0c0c490001484003160141059181c100140242c0c2d02e0890b044170300384c0d17201c80701144072404403c50342401908940000300c600d80758200d00000821603004c442c05c800c040101603102d100d16030220448000103245940c0f080146181542d4080e01c1c591103440111846844c01d09014950007409aa00c621400300190b2400c48500b48642030711107910800c1504c0ca80e2044400c6040010024021601120441a000103c032013110803620318084c000780194040c5800c1c0201e44960740c40e222221031b1300c03035507400003044409 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 215516375 1250 215515125 215515159
    0x50109051b1309050c0909070201090c090c050408240c040b0322150c02250b0304020a0b040803040302040f0e060f1b07060515010804080d02130e1608061905 69
    0x10b401d03840395041c2801c0804212a0704860005407101c2141501c20020030364030407200b2822074440320002003880c1b80c0d0240c207009090240e4010821407586082141c0307095156014645010711100110228131104070f43c102c4200768a844894000141200c0242403038201003282c6094000102010020340c100d112004d508581450400d1a241c1c1107101800d03440720400d00c08002c2c1985104400240c413070340040c0380c1c0749003002e840840808110b480c6824901e0a05150b217125500103042030b0f03481a420704020078501c6a00c0c0c000c10080441800039681c0706e00d0351041c801950116860845600e01c0d004602901004c0800d02540c0914880500100740d82ca080360440039078401c1412207207402001c507c000421030a82e00580c0031385012071200f80d140c10b4a01c01103070030782d008607801030071900f05005180d0040055005002010411050110700c99164000111451403c40780740c45038000244603202c100c0d400c14406500100240c50f00910440301e000f1410442c580c030300c202d5001d02030044800a900e = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 215517625 1250 215516375 215516407
    0x120102070c080d14091c03020601050306060f1302090303120a1a12031b01150b120a0903090605030406092a1e051c08041e0602060f0601050c070f1503050109051b 71
    0x5120b032030100e01d081b01c400303090007503136082c0074069a030003446142c0200e941c41c03a00c2100c1201812008001c0c40103c00001c0c1404043e40020070415010702c018094180c1140f284000d06100d0284180005458105103a02d00c8422900c081107030300403c1250044020f00700007000304c407d064120481010b081001b07000080c0180040c0960740076000c58100085403480c0f00720300600c841800300f07424200320f403250780282003120340b003c80042c0801c00079a0200b005a015030042c5912030300409001401c00c1c0b03551100c0d00c080301d080481040008844554403074500103202102c3c003802035203124000e40c641301c0d091a0f004581e94000d86100d1508201c50981c6c8280138920001030b540d114801c00c0d00c1d5070740c8540c06180d00d09802da40c01c489803220000440c0e0b651002940c18410810303018103070720640310700c8015100381d03008207003400e1680607241010640e440b8844407070000b411134209080034864541401011548183c01141b41c40e41020240311400e0005000481c1c41c41042c4883c40e03131a0210401d41c1d00d0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 215518875 1250 215517625 215517649
    0x806010207090c030c0809010c020a17040f03060203060117010e0105060705030f0427021206041107140f100e03041a0c01060b0405010f020a02090f15120102070c080d1409 75
    0x406403c06600f961080c2e8950494a4a40d01039221032501d525450b0806090710044050200140e1201803400d002c126800b001081a0741404102c42c505a110030340003001d483d060b0000d03141c040d00001800785a503445140803020a0240c0c4d4001c41d29418030144003c2444181b045921403907001c01d46106000b01481210007810b05889401c4c1d0395669102e2103c203a54000400c4142d29041c080310f42ca01c00c803103000b144c048011550882401c0c0d0780301820407000344240c031680401603d0610040c0002840101e4111280c44850000c00080c1144d104d01480c0c00d00315600807055034104400078000b007200105490036034030250070f50901d04180c1c200f050b0f0140947c400003031566090040000e95040448018400e854080c1d94006410300300700401d0ba520811014000e42101d80c01e03000501d000c201012140c2c21443c6800c0040f11010f0b203800180480004000005032a5070001c3d640c41041202d01c04003000f4154240076154541d100c5030301629203244241048608040052183c0565440c0c0c0c0c0c4101c5 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 215520125 1250 215518875 215518889
    0x9050a020c1606020c010518010503040804091401031110050405150705060f01090c050301150e012303010503010c0908060a0504050114090d020f0c0303180d080424031a010806010207 80
    0x2e02224800c29801d00c2c02d01a11540000d4050b804500c05c880d403094088035441004050314118808000004403400d4bc8024403c1d5203040f028440071030390402034090182585081c0140c1c0500d5411818a07510940b2a0f18425102d900394000444126402209a07411100222040c41e8101200c2d17011020038400c008000349940200400c00003108210450319050b100c282d4003c00100c003200c1c500303660502c82800f0324520000e008000301e0080307200e0b0703400c1c1101e507206140844131ba80e50008103011000e016036811000401c00b000500c070700d040c24811380910300220302c0c1040d042840c19001c3e507100c0c48064030265000b5103880016050000940040840110110b400c51087c90007018070340c1c5805000d4907800041c040d030744081e1003048001419171001403000300614a0421611184201188103100342c40d00303e4200289031001c1501c0c10b025000030b11414041d01645210f04881c0c2c4200140c10078283c0506182c0810030301c24282034275902c3d0000200b8200440700c0c1d2140d50050b4545617196009103 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 215521375 1250 215520125 215520133
    0x20310033c0b19110f1b010504030504031506050907050d1d07091e0608010c0207060c03050f0c100504210c0b0f070513090603020a091509050a020c 65
    0x3006894140c00207403031000015400480c4101d9084240c2800c00041005000046640082000c0e60074583c504030040070300050009038000c2d114914810381e00408070a8000400c0801c6008852512001d00c0110781c030100700070081c0b40f50554010f80b10740502c0c0400303400c07501410074000705200c2940c032140180c007000f001c0c203110385050307078000385035034403c400000d01603080c110f48420304601c11050700303200c0248c04040c0c0781c107e00341240700b0300030000201c000045102c0a00b00000080b02c6104a40140c0300d01c0c000810307502c1401d40c0181c0b608145178004001c0000d00c024400200742c0c400c06640c800450304102035600c03031110f42c40b42d141c8540c40400e00c11280c50724003808200200e03003284486034040d90380000000401a1030545d188075181c540a0400c40140c7d0000b0a148400c02d221a07101c40207007440f82c00d040c0710311410314078400542c0005003402e13910003060056240c44216100101805481400300c3d41c00d60725401c1c10720240744500c00d5015260b901190a03102150150354000800c03808503 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 215522625 1250 215521375 215521403
    0x415050f040e04020f0301020703021b030709090c030302060c031006030b010509031b0306100e0a0507230403051209060a210e060a050601081e060105040302120322050a03030302031003 81
    0x18072a8030042e54200c5c410751003190a810103040c10300a4030900e5405070090820384907100c6030030440300425940c4543c18040d040003c1000c2c4440d204090496005d200080b151034103526019103040006403a40020040c14001c01c50803c80d0b804050007900d06030300c0c0202d550301c0d045006031035171301880d680c6a5140c0500d2686446c002d08010290580a808404a80031500c2c0c0550440629540d03012380d0301c5004140c00090070718001034000c00c0d0804140d01d441035507101152841d1403c9401070054551070000010300304140f142c100921103810704400705107440c00f280c08000070000d1003029034100c00d00000324018040780c5600011044441e242c0700b8103202c0802c0b00c046072901c54604449085c0c3d000c1c9080003007a4a0351284401611a008030b4005015680d410030525030380300001400301d4100a4100804001038580518104003111144011500c4121001c0042c1902840411101e00064050403c20081d9a404e050f40d085980604005030b803074a90520400e41d044140c0c0025191070140111 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 215523875 1250 215522625 215522639
    0xf11060708040e04032d080411031f0c08150d1104050c0403031b170c03041e2d090e0705031c090f0806010306020c0c09180c06030c0415050f04 63
    0xd943d04c00c03440b071740d106403046c005810b42000f996420081400312a504400a0800d28001c0e281680c00a01886518a42100c0c4d50006807034961404481641a41d0921540f0810001c174060380d00011191300f0900703203900c1c250a0f2142030300350456046200301031703c865420a1081c3c0b20040146442c002e0802e12aa2810404030401640244402c90000b403200200341c00c0c1c91f204800c0031000f2039119079030305484040c0e10703131034003080e000301103251502d0004100001d07005d03c0075144a4007030b000040c2425402440c0034211000c80000100020b072058405c021640340340d00400040701a10151200000c51280485590340361071600d4010702d030184140c245a20904400b100d544907840f01301e94400c0d184944035401e0010811451289464541c080300c01440020f000d034025000102006044030344403554034000400e182e80945810301c0c0c0000c1c041e24420480001d0100100181c0309850103480d600b452440c43c0b0301440ba900c1000030440d9001050001c061151080f15192107520113030a45403034445032 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 215525125 1250 215523875 215523899
    0x8061306230903190509090105010c1b090603020f0d0213020c07081e0c0a06140d11030a0b0f01140301152007080d030614090604060b070b04051006030f1106070804 72
    0x1c0c040141000d0851215221788110700319001e003000a803c80110b40d1070310006488106107076000300c070409070040d41c01c605829420103010041505400c0801c8062560060200d810b05041d600f034011b102c00440040549c03184980c0c5100d48029500041c0e83e108440d007034504012050300240603d005401618050b48181c0754941c4111408400740d845420046042040081580c410b08001c07420311041c002610600c180907000118202102044960380c1c001881182d070302c202c41c1d25000c46d60314400010341c1e040503907880720302c6072081c00d241000c0d40c940c504005541c0030510428545500c540c0c149101203200ea400c4000315410b01188480745000010405d80320b10042c090382501d8400e0380894100c55201b0b004000450b8042440c0100201003902070000380c1200818068200792130b00d500044075642c1d10001d01700503009924070b081134189842e01908040d0a055101d650740d04010090002c04c2d1030103280c180c50341c2d003c110180c02a80740e00c0403401c0d038003401001502d949008078000422103c118 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 215526375 1250 215525125 215525137
    0x6060201020705010e0d0206070c0320150c0f04030209130602031003061505060a030e0f0709090c0b0306210a020901032901030809040216020a0f0e0108061306230903 73
    0x1e00281700290000540d5540c0f400c1c0b1020000059002c00041604a4003c0380003001c00ca000e86446c441c443d10b40e03021492110741d04003a480303445d4004a206580355003110326458020355101c1c001071502c51840180c4a240c09140400380c49014494045004007103207800805140e50b00c01c03010754a074500b4100454000c141d81c0301c15240a030402c4c403000d03043c194140031502500c41c001d0041d070600745d051a0840090026540c4c004062140001070141c81400f00b054030001d10000c280030481560910303106801791030960018035244002c3c02440420f0b5600e1040808040c01c081c1d04020001d000c15445e0314050304108041c1d0811501c02c008028084048880283c41450900710201c800c80c102c041040c41c4403d100c054144071085c0141021440c2c290001d261084c0b080d80d50411203000d81d00019a901e10a41c080c184288031000c04020401d81444107500612baa440501f00602d05072240b0081ca4401050003040b8a6030b50202e442d000d000b0300000407950347c580714260040c0c034060b06060fa880d8010 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 215527625 1250 215526375 215526383
    0x504060603021c02030108061303110f07090b09060319080d05040b060a12030e04150b12011401050c070605090d060507090e0606040303170423030711040212131401060602010207 78
    0x24443d8881c0295035008680c102d8150030024103980d50b49403442e84030450111011805c1081d00103104540e001c080043c000201c0031040a06046407510960700c04a50441030080c0c01442c404040242e50b81c0e000c030701d0b00540701c91102190b08043c1e1903e001e040703d1040504c3c1d400841d207800248024801105c80700e911540068030000c4010b40c0303850303c54005009a0100400142124145c54114109a044522541c030710326401c4042949610030b90106802141d440961000740b00d00401048d088440c1e0504107420038201140b030a40035442054940e0442c0c0614424054000303038444554690802e210034071034010710100102d013800310004000c0c44851045400d4050342d02c0c040b0b801c0e0703c1d200c1d040704d08695064442c01c003124110610001502002401940c07826045800041520b40980310b110002c55941c0143d41e6031700c1245404d40c1100900d0343c01c40d02480c814003000c0ca8041c0b10468050700b007030701c005001030f10000c036161017a5452070007044280301d03500f402c500284040c0c05401501342c461007 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 215528875 1250 215527625 215527657
    0x7030f0507270e030c0d0203030f06010807020a030513050a0b09010906140a0819020703090e01091a0f0d020402130527040206070302010605100906080718140a050406060302 76
    0x42c0b80500003005092021a403002c10507030b0800c94459840c2d501c0381c03c072070410000783d03801c15440750351450800e002c0f0030210000d43c000104001045540455865010000342040034a5007481c520080d907440c0740c29802414409d001401e80360840145101703d009100050000c5001030711000a880c2d583c0220b800340d80413451004c00801c516015400680c4c003100d9041d8070f281030001046084a1147d0090300407515018840700c00004030316030740001d012503406515105076007460581c5801802605a204884140c6084062236070704103c0d5403640001082101c1d1052440310041c0010b42880c42d03250000d500c07910004040ba0344004680956048541c02c035036100c24110300c402c80d03450010102100104030075000d400500107180c030700c01400c0d909000b440001280c54682000c10f00b0940139441701004100142c2042017402d03402100d4940c0003415141900700310311125070f042d081036200d009200070b141c40d01240200e80d4a800c034441d80100b000401c2440110341c2e8450181c000d5004928020790003513 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 215530125 1250 215528875 215528879
    0xa080703120504080a050d1e090c09110a140c100507030606020307020f060f07050105010308120603010c0e01120f02180a0f06080109110706021c15180203041407030f0507 75
    0x586100b40e610481e0801505854141c90113001c03181503100000c0c0c00d43c41a62a82c88950030740c01203000d01c0207400c4006000030050087e0601c0441078115034440e11b181c9042c0000d00702540300c000191449201c0504042e0b559404914440b601400346d403080e04000e1007800c82d01a00f08010f9001030f03000c1ca85603101040000e4403102c04980300e1042d4007000e5080213801c0040f850605003200201000b9501a0015041c812103664503825200c003a80141c1d5055400b0460540360050105401c2d00650114000c0110029044001d01103511400082e41403040071145030007140e407180c0086850f181842c03030842d6514180070a14010001d0901c0060007004100008640c000b404100d810942c0c50f1038803040040d80c03070042e00710003500d075032100d030449082c051091380002a41400a089156900406113840340040d9440c04200c484001040700c0000017407104001500920101c1c3e0704140100b500581d40b50380368107107031070715540c0c5810b410810310a2110000501c401014002d0001d88910705441c450703a = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 215531375 1250 215530125 215530157
    0xa0b1e150a0c121404080f06070302090d060b01030f0e0105010f05090108100213030602040e0a0509071d06060c06010b0301030b010801020307140901020c0303040f03111c0b07110a080703 82
    0x8050501d580011600005003480810822081560792218a26244000036074141030310721180c005a1113401d06a11042d49500281814868070740d010361680b07400c600301070384100002d9034a013880c0c10142103540e558032000308d103905c40d402801c05200001414001c030194108482c2c0209024070504080c030322129004500e9140c401d5026049540c0c6074010103a07500705c122010020740c01303031006800100b2500000000038005001800081011108480007440c041303000c68240c0d072008003090481e80104106102c18030b070403900751000064000e007649140c2d03109001b0401921400300d5400b00352082c00700000d407108406000714103a83c82400702c480c641c0d81e260600c900381c0c0415501c0784040b456102030440c0e44c41d10b101c060f2080d81700c14812214260340860119080d68855080b04084a184801c24014815480c1450301141b006503445500088419030001c80b001c0c0f0a20002c0c25461044003245c0d40a22801c2c1c417800c01c043c00c505540b0304c1582407426002607070282000b10702044103958184284 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 215532625 1250 215531375 215531377
    0x23010e0a0305070327060801061206030302070620060114030d05040f03020f2701090c0203040803090603100801020c06070801170705060c0709090606030611040b09090a0b1e15 77
    0x40e0349074850b03034104002030750142c40300026005d00d9080004040400400d00310700410100c018103050711030b240c083d410000000c180010400c041c800c0e40e428110f041001130345c0000c04008803026890315a1f14100003d501c000d02d10b0310310b00d01c0c400922aa000214070000c4034035000916200440c1200ca011613051800d40d4580910704c07402c1580b12150000304003600346008082c2c0364080042c0f061002d0408103d05c1b280d8610303c0082c440c000b0b240700d0700500003011944285010315071140000c50a051400c40c1030b035502d01c554005503000d05804004a007500d000403684001501c003a034000e548a40607a541181e0b1000d0403074030324000540380350000481c0c0000011507606c0d501c144000c1c2c144642010280600c590100c003041400707106241c400140c404040c850781001c4d0b403081401140c450b185051a03015540d80c082034122080342000700704000704406040720b000c0d0b881602d40707284960340c7c10140720041124080e0141c000e81e2560f4100c0c01010403c484051012084440c0c200310039541c4686105 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 215533875 1250 215532625 215532643
    0x1306080c150306010c0602090409050a020102121213020a030b040602180f1008040507050d051e030a05160f0209150909010218060c0c10050a1b0f06020c010923010e 72
    0xc0d80310802c04211554420000b402c0702d6405641c0c00346c605500324000c20100c03110b07903000b03407003640042142804569048c480003005007000404981012494060184103100c064800c07403122011602010440d01c61030b40310030055800c1518145030380782504081010b58401c42e58001081c0d0701184904140c84c01401d85085c84c00b01a00032001c0c1c411021064606090260056629100c1c03c00d0000b0306503a050007511006100e14042e0021044d100816030a884c0090b0703600005070020f102c00b25075160f005081d03ca1904c40301c8000e03205201c0030304112200540079040650081100401c11220022032440508039101c25900e04d02140e46400300b0324201e0140c0001c00c5032030503609002883c1c51030140068084a070520083d240e5580d600c40000350000356440006010900214510307082e503801480340980300800c1d12614900c00000d907284d00003404100802091075a01040c12240d10318258072142000e0342c40701c14902416482d044070303122030403191400e070025820702c080900341130804215842 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 215535125 1250 215533875 215533909
    0x6050103151e09020c010e12040303020d052803020711030c01021b0a15030905240601120b120708101406040519050f07080106110601140109051306080c 67
    0x41042e007010700900312408030120391a00c21903518400300e00300d4464401829084840b80001404c0381e250300c0042c0c10600003000311030940100380b02c1000440c0e000303d92590510041e261882d5030b034800354004040d400b65018600d0786400000e050300c1c266505a8000c00030b0038022a105a002c101501c01c06076642898200180140c000802d2a40c2c490400c1004040002c0000c2080700895110440034a000c0d408405c8840001e80f035004140078000103105482e005081108483c09400303070502c0140080344003400203410003854003403520b5408202d80c00001303400401886080c003040e15188030f0f55552010b00550629010300c11840090030410310500745140009000c500e82990f41000300030003800003e24001802c02420503c86400c2c2c01d0740300d041d204035081c22400e18a41071640009160801c1600190305000d01070b100440529000219281129644c1107a0441d40b01140c1c0101c1d0b040c0c8690744015085035802d00801207406081e0459015104080100d41c4881500c1003005107001c8454880c0c5 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 215536375 1250 215535125 215535161
    0x1e060903201c030f0906060f0e0c090108060d050a11090717060d0c080a03051e2104050106050a0807090c0e0a060f03090b0906090c09101202030f0105070207080106050103 75
    0x886548006094400b0000d0107060005001410001290a0700d1380780e5030445089940351000e0148060506201028089900c94503040d850040c407038822921a42c0d8009051042c0140015510b0780c5e0980a5160301d40e00c0300c01c5e1010300e00c00f4078020110114440381144030b401c1d660009020b0610601c410402c94007114155485501c4002c2849940b1008060a40b206e0130640b001207120401001040a0284030303585c3c5659038116002c0b1300d180015040b0200301804420004581040c0c40030000c003415a05191540302d040e240d070310300240104100d6001c960402d07000000007c1185011881c0b07011501d00b004240300260302c881c412150000c250b041c0383e600a42c010418880309100343c10071500752415040001e1035000644910000700011660039007d640124104400701c901440403070880041514400d006081c0454070080740d02e001c0c0100080d01468040c0c1303106654041122a0111960000070489410500802500c40f00c4500400c0c0340340d801c1942c0010030b03510921134480c0e4585180a02 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 215537625 1250 215536375 215536393
    0xb04050703180f080705070b030106090b16140f0105150a12020307151110020a030b030705150a091e15050702090103060f0905100501050a05120c010305041e06090320 73
    0x24080948407150035200315901744003100000d102002070002404075140081e03103a41c0f41100040c00705010307800c500b02051040c010581c4e08482512054115940440540c1c1d041300b003008901d190140307100d0340200310360906003031044050b0160714010744600c050b00c9184103a62034044608000e011030100075015448820100040380c0e081c0c600011021140c13810400d00d503c0c0522961402003422040301c1020340c000b2360410050307050321075107159240c140d0151261914040000e04000e24451040216402c00511414060321544d00c40c4041c4c205a850342a9041c81c0c04078180010565000327040c02e503c0420681c030040f50145d02034070341d1a80d0080400078560f08560b03d41c40500150782c1d040045540751100701c0005003040c0816001080d1040c80090103625040400204500940c40140504c0d00c0c946041001800851061005402800e01281c180c84a20303021001c00242001e403111208610191020802e85d508015107050095440401c0040c0c0c409050010f44079407000d103821075004045d0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 215538875 1250 215537625 215537633
    0x80609070303030c02070806010b130e06011e0e04020706050a05010e04050337030f062705040f020909010b01090b0307050a030504050309030a0b1801060302181017010b0405070318 79
    0x20b4461134282d20565060079a68039020786044802e0f0000d080f005008038203081006441c2071070000030401c45050b141181440d00029019405480141c80182810301e10011a98098940c0e0702c0d005401074030466a948590500d0380003020269015103c0320f00701000082d11803100880340340684d4000c4082c0d840c04a8a8400941b07185440610040001c045082d5610311080402412050310190303d000c0fa2500030f241c4007004a0301250801a200d248031006409980070000b01a8205806110001410385840c20035035003941510a000303610490344810402c1501064016000b900001e0722545c4c0030390344440c0040c01a01003104c43c0307000500b040c0310000d00540310f078104540140c01b07071082d2441d0141d0103020a082a101c51810707624214100b06100c0f81c40ca24403144070300403a44070000c100a80c119030018003030800038224401500d41544c085644038a150740ca800040c21080901d16030742d004e544429018024801c0300300d110714139050000e0001c502901840d1200d00710307800140a0491581ea13 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 215540125 1250 215538875 215538881
    0x60e0108072d03030c06051f1208090a060c05010501080304051302090d060e0115080d050720030d0804060b0409081c02121005120d02060f06120703031808060907030303 74
    0x40108800c07010b5400d070420703200300007110341c000d5406a0b6030483d400c401c50404005440014000c0b0f1108150410304100030f20b00f070900d40c4282c4440c90402d01d48004542011020340c0110203509600500e4002c000462980007400c1490721403155000b40017980c0d913042c603241c6a004e1881200d40181019000801031f110981c010075040c4001042c100d0350003980d40720041121150890844941e40d9525100301510644800c400100303443c0700180054044414020a2406240401001d0045100340c80c900c54564010b0001c00107006012648107502d400e01c0100098400e41c1c00361112481c228a0f4201400c21b402040007041c0c01502262404000c40c0840744001103550311680c13900d900b8441d400e0311100007007085028054140c10441218140020441c541b00b011030f450007542c2c004a4403002094010030700c02c0d0b0020107106c4201e000d40d43d8a0100d050b9040c4140d50404034007030540d01000b00f542280a42081a0901032020180c9480b0246540d40340401e07a40c41c007480d0310401c02080000d100c2d030 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 215541375 1250 215540125 215540159
    0x2040608060d1b0b0d06051c030309050a05120318062701063b0915040c0e090706110c01120f1409010c020c090f0f0702030f0f0d060e010807 62
    0x40483e10b00c00d05182c0f09108821029000504141070002e80202009a02d0240ca0080d190480e01500744508508151a507503042a03001001d06403203951303550601506104040000e604401522400782c0c100e80203000d56032086a49124150113070031170ba1050800010b410703102c0d0030010382c8583c140311b0091110307401204c58102408031399240c180115070040800d00000346064907840b84803810136108070440b48040c200c000303000007120f41c5003001444080000c1181341d8485040b203da0990f1a182404c1c022082c284d008040c00f01d04a60a005d48290001500006c89a8603558400c0720520792180c580c9408041004500248075074101040f1484a0b9000203125034252000040c0360311290f420f00d102d000300315a41017840c1d540d08001cac40081c1d0180f14480708a0000c460454040c42c1800003007805020142910440d40002400949064020022510409142c2070041e8648142101203021340c0c1c400e1f4584010141460b100282c0c1e82c86240c500c5045c1e540d5240035042c42c50418185d81c180301c03a02 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 215542625 1250 215541375 215541383
    0x2030d050c0d0606030209030c030a1e02150711030106060f05041e0305070b0a0305010906030c0b0318030c0a020f0a030803010e1e0103080901030b030d0503010b0d0603021002031c02040608060d 85
    0x10092030441000034450f1200500c043d441c0542c540b442c4074109414003085201103400703a0403000c4c1e40d400081d00b50f0581111500154186a401202800464200c54100129001c4408000b50803002c1c405803264203a0300c0b440880c000e105060b1108421101014490720b0325010a200344018444040307002d40c0206809409404100a6a600d0f11000c0c039161807540440510b420000b080700015a0500425000d03082c0c4060512640e440c554545020010601c198007000c803010000c00c0e248070f4080404000600d070740003141d440c0d084282c1141e88070b080565040703214001034403000700c00c1c1c10040b5000040b603030014a52800e41e0700e80103116080c18001810301e58200200388410440032006117800d0b01950160b4003440d100d61800c0005011030f00e45004491080d8070014250103003c0d8454110380c103480f40c4221440d04c1e441c102c2e19003800350507107070802544608100e000c1d0180560010182001620b09400104c0107284110004100e12a07030144200050310740b00041c1090030038008003c4c249200b = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 215543875 1250 215542625 215542627
    0x1005030c1806030408040305120304020f040203040303150f14011d040902030f010903080f0105040209090403230f0706050708040309050d0f230d020c030a1103030f030c09010306060f02030d050c 85
    0x154030000b902c551086601301c1d41503002040031700030f021080010003030031001c8041541c0303181040d40001d00c4a000c112191841140c0000001d81014801e801001c0c0f00503c210020706950b4941701400403080342800340c4240c41d9041c000c810510342c883d10b1042100c20801c61402590300d00402800b01900000c0020781e09440b8001c0c8900344c0380ba0901c96414494000d5640903420704050321244410101039108070f120354014081c6d0342056459501c15a042549400c000001c03988080e0704144009030240186c0c100740700800e0076026040104d00920943d0310904081289565103d01520032034415280a00001c0f40302c28140044d04042e000b15030f445009164100b01c2c000580e50b01c40030190403034004c1c84d50800d00080040b6103802004421540c1561740040d10b646488000465990160941c0280869940c0308426076561814002c403003103001d01150043d81c80c60900780110090b84044001e0b070001e032918000082042c416800301c2c043c41c03591b0340a549440c04071101140070b400c2c003030070010721000 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 215545125 1250 215543875 215543917
    0x40b0d09050a0f0c0303080708010e0a0c09050d060b04050a020418020a0c02120a0c050301231b0c0615150301050d050f011a1203040b041a040b0403030306141005030c 73
    0x8a018007011505100700b480f04c0700b29080d80340017000b280c8042e10756400d10141c0401805407211300e48146600904000c00041c904407a0001120b0b01d040a9011581201d1130540c40400d101c51500b0108d90200251420301441d155800503004a20662240008034096141c0415043e0016002096580b440386411460950309400280304140203c103444000e41c06079082c41d003006003d1342c1c010000e00d0304400800840045003245080c0340c034030356000d056219a18000400e540940f1071107611408400150a44482c800c070003495584c0303000d6594000902502510219502d4034a5030240c0700800410b896065134030b00400d00c10101078204003119035000301090b585c2c21000910a4440301ca01081e803181d00c40e0070b0401441101d010b05201c0b020f841d0010482448621006000c1320b08890b005025802c601c1407002603500d0078001e0743c00c0700588003c000b40000c10b142e4950422829500701c1c42d45602d00e542444200301130b03601e030f00030307180c01191081c00016400b214100262944420000004030600 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 215546375 1250 215545125 215545133
    0x10c1e0f111213030605180d0e060f0409020405131104060807050702030109210c02030c090402010207030b010e06040c0203160b1e0408030f060306040b0105220c030c0e06040b0d09050a 81
    0x90010f024a00042940400820903c02240a03035900011001c412031100f05032080d404d034482c03004845810601821518901060f03c1e028121010881e6880c0f0f1035803115100c4481101a60191081a1190405540c0342e00031244038855040500440c40c11545018038010302030700d4440c0020510010b00c9424014840544c5081c0548101648100c04c055403d010380d88201030943c0c0c0c5211003601b00f085540391940103071800030b810020780c042140d41c0c1c109540c8a10040303113004c02c1c541006002a54500000900103d04d1507060b00460003240c061024141c1d00008070303a42d0003078104480301e501d04443c02c81d011496044150f90418500400b40801400d0f80c4c03941e14481400381c60440d00c901c1d00000b0018075035000304440381c0190045000d4491401c1c1030b1220781740b0b520706000b030902c42c912100d031111968030a03155001850100c21011702c580340a40001800a00240d0110004160a01102c414a00d013410840301500d03203843e2000e0410300580c1d10300004022042d0201c17110b104a4240340042 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 215547625 1250 215546375 215546377
    0x1404020403021e04110903100203061c0f0309050607080d05060307120813050906090a0e010209040912090e01180e070506041e0905040807030c1a0108010c1e0f1112 72
    0x103a405020f49078100b00382d041400304680510540200e4070205020303d500342e039400300f000305104c203046001607103948036000001c80d030421b02100c20103d4111360603070004000e20444250340b4280241c0740c000c2c0352507490091200364825240000c183e040c041248014440599108640080c0702070111503a460315502c1981015000c02015580c000c004540510764854226401001d4a401c0d03820020b82c2c2080404a48140e03400b5200c003803101e850707541d4101d007000254159290104010001c0c801d450003410a810140e07500b1070000f00046100ca0b0101e8203502c0705824604039078180079020042c407103180c4074000a10103030b48540752074080c403040000d0b41d9654001607c007410141d20101c01c419200b17441e00901c0c3d426a804511407504040406c400724820f103068135003c40d003609202d07400c01c12500e0048a2501180754803040201460008540d0420552001c0d040e1259912403c0300d07000c40300f04020001d107500002000080005010000d010320840c3c18401584030715040320320541c641c804282c06 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 215548875 1250 215547625 215547649
    0x60a09030b042111100b03030f210114041503050d050d060f0927030804020f030c15180901080307140709020a02100f050f060f01020c1306060e10020304140402040302 73
    0xc0c2c2012204e080f504050000f18600b10382010100124000300c00880c1c2c032402000d0081500c80004181c2ca6103000700c914140544e04c01000c0000c80960315840b4900c4982030704d60289004030320f070207100e18401c070414441009582d00070001381042040ea001c1181e495110f8845201e085883c0c100c0028040995618034002e003601e40804101103045089054000d0540e142040403030510000c1c10f400300e500801441c1c0c0044d01030300c00c01341e04520307007012034030f80b0101c0420b031508105540383c07210450351807101074007241070240144510003100303400704180790f1000e0040900c00d8004021090000782c0b050700040100444405031034003165100b42890480e08038030a004007580064a091401d1881841545200c4581da081044141806407000700416401441d99002d9600008001401d1703000308400802408010708a90078070b841075100002501481c426035000c2241d20301c50321003d20300540260500500c6600a605052424090800110ba010788083c0c01950801000c000350303c407850300c510f03 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 215550125 1250 215548875 215548877
    0x1021c1e02031518010806070816080621060402010801080a0209010b0c0123040308070914040905030c030a1805040605030a060b04090b070f020d080106021e100504120806060a09030b0421 82
    0x30b0151b00d000c900314144180204000308028040c010801c1e40401040109a80c040b10f00e000d80c165a00c1401240c644c162074200f800f041600e0030202402d0005c001000e620491007a81ca42c0c150b80d98480700b07640d44550800000350310410000050102403e407601500101c2080400130038204041c001c0d1500400c1d045401c0a144104101000240f50700050301c0d0380c1003102441d20500081c6072040840d08580c0016038140302d00c2d2295a09400d1000800684803135403e980b003a0ba6a450183c01c0240556101480c007050551113508000341a00e050f10401003100d1010380a069403550582c3d400e030041582a419035031007a56001c43c1000b01751641100c5103d0042030329120071a80c070700340f0003a20b41607110440500b000700c0040107000c0d8548c0400c000c0b014070f011500020221503503c004908110070030210b41d5056203840e0802c000d002c02c20a40103040303843c0740c0b5104401e803a04424000b15100780012440480d15103e41040061007100100790f116000e40001c02c0b0403600c0c400380500704406449040 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 215551375 1250 215550125 215550169
    0xa05040306050705030f04080d2a0e06070209010b0319060314010b030105070f05070c080a0303140c030103210507060c0207140613062001090501021c1e020315 70
    0x22080010714030810790410354a0600798103614200d45050301c3ca84004100074040c0b034012890295100003504000540c40c00200c0c0062051144048080382074220400000062810f136008411401c0c00d0007260452600501100344581c201205a0420f9001500c1c0000b061110101d14200c1415441600c1c06940300d18107100008560611030ba00351422900d16912a91624051209846c1c00410340d4101c17044a0602c0c1d5101c0d00b42d4142802800d0459101e4846409903500038410141e040c3d0140e101a01035204801d400e07162120380000900003408020803c21159a111811a60340103090030780c0b071180c0c40c1003840c007803035a0340340360070f0714210245075000da40030100c1400041622154854500800c2c1d902c035040c001840140000004da0340304e9042030100c00004206d040c000c1100c03a4010f002110001e01040400d071422500035403260054440c1c26174440401001a000303130082c08220b90740d03480c0345c18641030301c20b40388002540090030010189090140d514410b0711020400450260500e002c5 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 215552625 1250 215551375 215551379
    0x9030506070507030909141902090a0311030f120405060f04081504110303090d020415050a030f030f0309020102030912010f0e03041502120a0c0f170309010605031b010e150a0504 78
    0x141007117640e03030417807082c0d2800d02aa1800c2942420349aa5200580301506544501c9083d000341c001d100d01c6030216088907122201009004141b1400e00141d14154101e403006c42011460607101d003080110020500010072003000b40b0701c6d015020307100b0035030004003082c81d240d5075098161a06c0482c0480c1140c0d42c0c0144200000d1100d4018070101d01c120680107940343c40c88200002d0310740d60325080700034450b42d034682e41c40f1801c1c11158a01801741c03001a100d0840d0343d481c0c4c109200e08000308402140000c400040c2010b009100c0d020b44000340b54181c005504056840c0c0030091452884023003a0318942d070713801941c0030034141401020f007519100406150303a2418410034002c0c810000041005550001400c11000c1aa440031641c0c40140c1e40307422070142c05686055041c042450341d01410403540c080c510901c03c19144001c1d4040c14016000b08030040d6250309141d110280e10b11900c80404032407074905050350250340300c092040d00050a0264844011444000355000303801c448d0700240c6c001c181 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 215553875 1250 215552625 215552627
    0xc0105040c060228050f01110714010b010905010c060f050c070314121b0c012a090e1b0c0f1c1416081b0d090603020c0304150903050607050703 63
    0x407028003024400f070803200c0390b004013410480b100640990090280d41d0b07200018071109010b580b450829100080c4103480742ea114441c0035400070714003900d000d0030b02100d810050005114a4820715010384a1400c0701c2c4c9403400568900403a442c00381c81c002e403200d207560300d185d010b4400c0a00c1a020401c8041d1500c0460130003c0080c1e4403090603a00c0b08400704842c0700c1d244038626641c0d901c5207022202c03400b0348030b18030700940a030b008400c2e130040d1941c00c0c080d4030507a03240c820f51020440040503c0f0400000d0001308202c0c1c0440203031244400961000e4040b4a070600c0f642940c13010f44c8500348400d451305215010745c515190034a202c8031016000500a40f900852600311b2520100407071420498103106016564564400c0402010114602100001c1040340703490540310210315100c0d84060032108d4140039500c034505044000002070030280c000c20864020710a40340c410446d40011410b140c184001414164030707460f48941802825900040050000c1003564403680c46a918641ca41c1103034a0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 215555125 1250 215553875 215553893
    0x91008070519080a0f1e0c021f020d05061c2303030a09140a150b010c021804020102010608010c05090415050a06030605090115020604020405180a2307060f050705030f0c010504 77
    0x3803200d03014180f00c0d215107000f0351b490b551841e8056540700005c04580c00b0400f40d1506420040030341201002d2403200780380138102d074090414009040400e0001c1c5c0e4800c001c1121450038100200c01e00b00b44403020501050303011151041c9404d109040008401520440d540303590000c4818481480e00c030142070081081c91002c0710411150340f00104541005583c56205034216101c9004800395141b40d5545c440c4c3c07044207440f040380e0f00503000d084840d07481f00309000c0c90581201c0c280e02640c20203100140c50141441081d00d10f22407695124200341100d010000036228a1040c003101045200b40412140e0740d003200800100202d0300c00080041c07a241c180952140142d003c40340201d00d5445040802d50086a200e510581c103d40004090352080c006a140301c400300c4110102c0c0c8601e0642e40c003000415910031074010482a203070101d45124510103555001903000c0c140029038a548180415402007024040715441007095a080c401088241a400c0c0c01495184001c0d0b07444a0911091100d000 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 215556375 1250 215555125 215555141
    0x204060b0c101d030307050c010b0a090b03070803030114090c09040c0801030317010e0a0507090801110703090f050303071509061a1306060e01050c0106030605070c031202091008070519080a 83
    0x320700f40c8841d00c03030503508a032203000040c10001030180002d04820740450070342c404941007400821480d41c1907115540c14000b854603100c01400b91242c1c40000c6044003000060324126401d103544040e00e11040e00c140101c03514046c00c2807141c1c11051003607882d5940c450241e854492526690709043c1e40c07450800074003401c0b101014036034003404100144000c40d07242c403445074480941d10300450b642d02e81003000c484504480c0d000031b01c15481c0158a00018074032800500f0f000f800f076511060382c0d5880c2e03030754003500040600c660303a0300d07034002c200450019994a4214500c800f82000001d0350b5220744c2c541c0c00c140d60700200d220030404840c008600301b500d008203011480c1100c00c0e8040113840e0600c900541201603024940307040c418042185c0300b41110940000c00510350010302440030b4106403a016211300c2c02c4c00c100710003145d45041143c2d0341303484510a8400008006140d03011119a241d020b883d4008040c000342c0803c00200b0809030043c001141113041e000d6280c0e222070720b0b40342409441045803008 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 215557625 1250 215556375 215556401
    0xc051e0403120503181c0e030616030b0d0c08010b1003090f0b09030d1103100503150c0a031d0703020102100902031c051902031305010801120b040204060b0c10 70
    0xd220500110314103078920200a0309600340180d84e03403941050100c500342000a141c02c0c9120ba000384040d4507805085a08a001c41d5031a51603200d0032000c1010345810045420b070440e9442d100303914009600c40d4000b0943e070000608a011030500d592070f50a00120325401c680b589a440d01c9901140c0d04210050707a4448800d032030100f168002039510303180e11000d00320025106075208000714110280500868107036200740e5004101e4000f030489400d4454104903403c0d03030b001001800001742814007280540541010f030601d130829583d0308805038107940003408401c1c10560380c1c1094080020061041c900000342c100000c188880c45e5100080c41c01e0300001903181400e09020300301d00143c070001a51840300c692070740300b0540c0040041e002c90325809400615080103c8040402844a40200c01001c100e860540040c0e100c1d82c6900064900003401c1c815400b1081558003a0b034081400e0344642ca0300039200600115031103070740f481e110019401070541c030f5000c5d805c5119074410380c3c00c4500c2542c90781000 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 215558875 1250 215557625 215557627
    0x19031d1c17040f1802041d04020a081005010e0f0402060d05070507080c1005100f18180f051203243105090c030c090915040b0702061e0c0702040209040c051e 69
    0x1c288071824031f1300f040e8014a100c038440340b000ca03086558449a81000d408000201c4002c15100303501c19000c4e10782840b9244460080d0808180607281000344188504e4014200c50310f41041d80e100b0200401006000008000c0107000240009031498000c180f00650b8000500640e11a000c10380d0850350003600d0f107180068800c07006c108400b29210301104542c8801c09024141070000018801b43c002d1101c0c07440c04103010704007a0204a450302d04003809a0080c400c64041c0c0741c151403080d90501c42500c0f0000c401d1111280410345813500c0c40a095401000340090101c6019070340d0380c41ca551095040002c1c07100070041c0103811600d1a00c070301680401c00c04000c140c00c01001e0f000c61380300c598059465004032000c4001501040f410404012842d18800c0c0e1101c4610b46810314507050313103042c0c0f00da1006000d10808181d0000e145007072450381003901c0410f00b2507602d42c0104c2c9181648048012a0002d03001d014002c55aa030f140303e061254422038441a076139030082c0c030085980e15443c0030060307d8524 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 215560125 1250 215558875 215558879
    0x10306090b130201020d030c03060b070b070f02030307021b1305091c05130506160503070f060b0111060601110703061e060b190503060d0519031d1c17040f180204 71
    0x2c5e00086c49542e400d2641000280b003400820100c0103002c8540007120900300c001b407017008100c44000014800d80c241e5840039111400e0b107504980381d11050b58800c2c016030110001d01c401412443d929003030024000c00f0389052646803c02141950012181c000180d0071450b03080c0746080030300429014400d00d601d07002b4503040241d1200500e42d070302c60140314003402e80414421051420241b00e41426a040300c100c2e47c643c034080c0b4119440708003801044590721300784a640a007650181d0314450707070045208003500d102c0e41d5800045a41d140114160000c0b4407079110f000012988a21440c10300410080780d4142c4101a030041030142c42007036108444510b0200080410241c80602c0d49804c180b592030903e0740c030340300c4c14001004010744003009001130065000303c9071001d0601001c1d04900f4401d4480c02d601c2056510840d9149405244c1c1d40e1b0000030840700d1001d40e1200d09032260703000d4842c4826100807148002040000d030001e40241b401c000c0c82d00000d02c020401185020341e0316809190a40c6000c3c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 215561375 1250 215560125 215560127
    0x302030c030a0c090e0a020d060b0a091118040f060602011a0102030f0d05100302090f0a050a1107030c061b02030301030302010e07060507030e0a0e2d070f180806010306090b130201 79
    0x19850310840ca811390351401107017070140040c402c04840c540c00920704014100641002c03001441d15040141c4101e02041001440030000c0c025a00400c07142c0e20a00c0c141800c00c0002160013450070502a4040d66412540800319014441c040191125500001e0041c040e50b000d42406074000c000b26040d944140b1401d042003440e0411140c00350801d081c00302e00e2752109038100b0001155608000d522200300700030010045a040c80c01c82c0300340500f40091110351240c502001c1200d111900ca900daa2408000311030110340109025041c06100c1c010000300c0c0c040c03041a00e020300c1c00721030325000107810010040091550901545900c04075007400707006018500b00c03000d007041c0703d1880c0090902000528104542e034401d405100200320410302200c6520f8803c2600320701e4403030603645050320f80001c01d6940b41811140d000d6845245540c40e04038886075940001e0750300904a10704000b4403900b0b0b01000c00c4014040c805a8003e501c55400803c0b1140249828244004024900000481c000682c0c001503 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 215562625 1250 215561375 215561393
    0x605120624040507120b0a24090b030f091203160806011806020c04061409011a0c030721020a0203060a020a17130606050d17250c0302030c030a 63
    0x1094100c1c00c091020412003261150105849480301ea1241c5450200030000c2d4004400c54202d031003e40041207004c03100070030030040c424a80216402c40034001c071945080d0554482840502d03400b030601c82003041d0381d100c0c036052a620885945082459641c14040d8290f0200324420707480001c40e46203400c2d440d01c102154032140105001c1800c001c1c520300400c00c564000c0c162003100109a401191000f40c444030040e540c0d5070120340b5a40507500d40603000908000303c02035500035000013802d50b407560b40f0740039030a10082c03840e0700304441100c0100000c08030304800700000c1c000c0da0700c1800050130f60001050346100c9504605100015500252607a0005075800309003c0da0007402228011707100c0081800441c3c084001070445180381c0d01100c1440082e001d0040340d0360100c1d1060105000c89511001030003202000c08030010300707060408030582d041c11003500c05007080148101340e08007001d501d5a07052210040058042d9445294080c0900640c24144600032561805070002c001d04c2d501ca0741c40000c0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 215563875 1250 215562625 215562631
    0xe131205030601051b0a050c06070302060c0a03290103060f05030624030a210e010203030c0d09120c0606060306080c0904060e1204090506030a021c05070e01090f06051206 75
    0x800c00000002201d5a025070192149103039845a903503090b80301e110f1003550702c3d0448141660707a413045813840e5555190150072903007410380c15070240c4031070b0321200080800340e003001e06480145612000142e5901c00c0c2d41e8401000300409420744900012036000140841d0021b800945901d240c004c000d200584001035510380201002000200654000900361041d0201524080d414015000030000b4081e00040022030040c2e40c42c2d00740201101c9a0b020f46000c00b074516004c0c00340e0400e01c006440b6040307a40241401d21034074480030407050001d9842580c1c6100003245040030507600c03009841481000c3c4905006000b80e4103040252a0600b07114a50f0b4109c82405d0901c590b401200103402c00c00541c01070120015840c084075a04402e803144500302e0341180c02500e00c07031071410000845520300020502943c6030094280c844c1c0d01c8800c1e00302c2d18004080d0b80705854174801c81c034000030f8a019903030f691340c002d00100c0e00000b05402c05c2c1014809a0b805030703100c18810001190f01c050740d540c0100716590 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 215565125 1250 215563875 215563877
    0x604120f11030607020307110901031e03140a08041406010b1c0e01020c03120f0103030818031902030405030f010908041403070b0d141f140d0602040f0e1312 69
    0xd00304a03103103403241c06155421a01c642500515090002507a0000081c19403544558440003990002e10180001400248000f038011555180150a08900907404071013450191074240013420314039030303102066400129018002040350702008144140100842c440700c03035000280505502d0080303000c2c1c0c0ca0103440f485091300f42c01d00c21f55650460700381d07000c065030040541c001c0d03484601031000309450307402c1034810702000080304001400182000002d075040c0c0f50300d512020351a4648594641c000c081100010401c0d10040100405289071002800400041c3c0c1c1d00940d41d40e4100000d140c14201c5542c2110916030411100200091446058409540030525128280414840040e00e02001c0b50b00c0300c0504200054901071204854000440c491115404100180c40c3c0d541c000b80250484c1522034503103403040100740314285903044003110405c0c00509101e04036403152119012a809a07024034002142c14030100f0007034000b00d0300e89500100c40d2281110b00e00302c40d140c0500c10300c00540482c0c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 215566375 1250 215565125 215565143
    0x15040209040b1507020406050d05060c1803190c06050c030301030215121801050c04080607030b0f120a0b010501030c0f03090f080301081614010c110a09050420060412 73
    0x20030030707454a41c00b510034000010701644034203803480d03031100255000c00026402241004804522400e248148041069100300201031a589241030000542c00400c0c150302d680c1d0444112503903c0e90204a9025441d4020b040024140e08901e0020881300d40c0394040002e010301440018046900802520b04403501500c0071000140200d010600c81d20450300c03000e2864120500340301c8003031118003601e403581e10004001c120b40d440e90380c1c21080a00607841119880d910990000c0c0c191803007034100d03203602e4502401c0091031220000000c0d00c89417201160201030703400303a0581018481411007450040a0a0804000d2a0280c035070007440c950b03000d40644107064845800d84100b0640852030701529400c888030948075611020f20a840364401280000d078a41203403c003240382c048190342c55010140c161201c648080c2190780701050b99008002190380080101000500740343c1c903014851060b440b40c4260b407040001c6d2203180740c0701c2d1400104580905424001030003440f9103000c0700301010303400c85089 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 215567625 1250 215566375 215566387
    0x50a1404020705010501080601031415130c080615030601140102060408221401080f280b1003020a0206070206010f140f030706080115080610030e032101030c0503010203150402 77
    0x20401074403039200b00618540c80d02c03000140074407000c60194140c0388582c0700f200c800b4003443d60042d075070303030454491030301214105001c2180349a8034001e40700c516100fa5080c5402c21340e54980b140c2000c10456030ba5601600070003400d4440e207018480303c1e0142c012400120055900a00001d5031000002d00041138140009003107114001c08091002c00d10a00c0120381000390784960b038030ba158002c1100424080390303403c000300d0040c03010302c19601c2c407842d410b420b1305519000d1824942100300a0241c04400c00c2c2d80c80b449106642c0b102c4601c0c401805450f1405039072000c00d14002441d105004000d901103401c480c005100d03a1810001d03001c12100080c0072007040454020005400541000655900d4417070600700050491704886280e04940e610724085040b881120416039542d8000c50b0200d0740190703000000c801e0fa5000313034040b000c02030710481141c0c108140c800e010210704a107403028805003803884004204000440005030080d04042c0e00035420b45c01d000c92181d1841c1e00010b501072107260045a8 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 215568875 1250 215567625 215567629
    0xb03040302030c0a15060e16033303050d0908060c07210c15020412170717070605070309081215130501050415030b070c08070f120315050a14 62
    0x40d01c9040f42c554041d039482481d0703842d01e0400d0320700e02848400c1c880d09001002640b54110291180701d0803405060711884081d07004100c00420401034549800c441c10030070700070030841140b4500c0e800400b86035002c180d81c1c01c0d81425481d100c0440c81605c10444204002c2c010340c04c1c0494602e030804040d0b1002c98aa01c07080c07424208034042c0d0540e04150703594500392209121b41c01200c0b03031384c42d03802443e8000708001030700380e4101a072041e405030480052120103080006454084d00840700d0352a107442a003490303904ea4495928460504104400032000b00306001031010912400e500060241020040800c103660380005078081c80c00707003040040c41d5070001195024000301d20044c0c803000400400300e0704162032210006000c20b0013040e000ea0315020021034070380092840102a21380201c0316070b413180d6a8090440e40340d01c0000c012168000203001038000a2018162441c01c0c3c2d204000802014002490040850341a076030030b080c00e040351980030842074481d60b21410070746850b000050404810b102c0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 215570125 1250 215568875 215568877
    0x9180209090322060c0308150301020f07110a180c020f060a090611090123090d080a0f21020d09020a030c031a0108030d0b0f0904150605190b0304030203 67
    0x10080d41115540342048110207011004200d0b5856820441c1100303c1a505207001040c194080c20021403800650000030074011071200380e000c5450a0b02d0309490380008003107400c0e070b000701d14420490180071803e0820859050010b400c40790b802c2c2e55410305e003464076100e0030900c21100e1103d1200b40e503c19400000c00c1c401d01c5031004001e510021070b40e003420003401700002040f4615083c0d620901d055524500900c2000c100c401d0034a0594502d01d030350790401045404440402c1c44d641106104000d006015105c1c4103116060b41e0180c40703c161603550401018200c0b882c1e60f22140204202103000320103001c6941c0402d0040b00d40c010340161900421340c0d00c4e0004102943c006540244181400001c001c1c855000380e0550b84925481c80752244020b540c0c0344440028094203c0e140c109100e41c4201d4140c544c0000e90340d520041510710400f1003900850107080302580e003640c403112000c02c004d49110b147e010302c2001b40001ea44401181890f4040c12002d41707860f0240120100c4008041070515100f00 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 215571375 1250 215570125 215570171
    0xe06092107060f0b0d0809031b0d0206090d050a0308040b0105010c0f14030412060b0a0b030f0604230a0606180b042d06021f020405010e1003021902010f0e030309030409 74
    0x14020424505e1a403c103c1c04642116800b0345c42881146007000c000d201d884080004c8103001743c018100b96140f0f0f07080065030f0300141a01078220040b03505040100d0700400c405a8100c0c001e840d05c0ca0542481d051090382441d058000d281403000b51401840000c0b01c11140070756140d040712014041444944050f415031080e0740c40072040070034800440045c8101a400300c121a00201d5072000c44070f42d550584a0b42c0c3c00119000401006031400288044c2040c3d000030440c02800340d03200044a030f0450b0200703042c800c191000d08115998a6040c070007950441000004200049110080c00f1700d040002e071128800c9000d003c8541e0302030342240f04480b82c0d64405d4450380d50480b006112007170310761200a568a414001594509080c411010031001c007500c211030903100107035981040c54907100b081c00342058118003907a04050742040440da203400100100342c48205240d001241441c0352903d55400e036261820450b6140e0010801d1105500c0000102c03401c0b1911402d01041604072005100300d884409 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 215572625 1250 215571375 215571379
    0xa0543060608030c071404050f13050304050603240a08071a0f04080a0b0609130303020a110102030a0b0108060402131a0c0a1a100f0b070f060e06092107060f0b 70
    0x100c1c0c804c0c80f034080444c100b01510078295031034144030041001c10058803030940d040301551002c0c50100314240542254086250700500449180030340e65230120b140e0b9031085070014000c000001806081306811301e1440d01d0b010741101d041660354241001d44c3e44901c00b130b00c12071404861500c07e0b06580784440c000e565020704080c07200c90300c0e15074820810341c0704e4101074800c0f561510a10001450303494018001350041820807614185916103a60590095010081c1c0388140f00000d8030006040310b0074001584510701401c07004c220b03102510000351003484090301052041d40103004491003441c0d80000301044550440070b000c2030341ca550300010503a1007060313495140780c05562040401d200100314201d01701040881000c1c0a0750303450281060480d680d0148500351010b00e81d003001000c000e88081c00380300c0c4c0070f80b02040d0704004558413102115010b40d010314060300311504203c4010020b100c10350030019400a82000601d00f03c1120020344581e220060072950b13030304803443c201c01c0070f507002100304140 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 215573875 1250 215572625 215572627
    0x30c07020f060301030b07020d090f090f0209310b0d020d081e0a080601031509150b04121101020f06040f06021b010501150903020303071709060a054306060803 70
    0x103909080c002400704607002002341c824183d08862041c450b58a85085450b2a03200d020b100d07050010b0100a00b2050b40840f6440b5000d0000720019501ca01004121300403c2202d0080383c05c001c101400d018002d05036050340b20385000c08110322602d41002d5100e041e541120404142281480e00c0170090144103480400681a001c00f02760150002004001030019615003141c0da5641030011070984620f420070b00346810410038208814541500100000171a10941c0380d90280c65010484aa40042e84800f0542caa4104e000052203410407844014540a201030b021481418459507950f240c0a40010503074034045904501384243c550585e401c20006010360603a100c042c200030ba0107081c0a00500c0c454046401c03188800c08d000b6104503003102d5000c0d001d107003064060f131900442880302440002e441401080140402c2c0d176442c00425004a498480036292000c049070425607030401047d80c22070352449481c8159078202e00c0d15010300302903018115402c0344224a420000b6062742e620500c940d03c8 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 215575125 1250 215573875 215573879
    0x5120c0a1b0c030303110408031c0b0d060b040501140d29241f030e10140f0a05070503060607020f0405090d11010b0f010c030306080a060912080903030c07020f060301 73
    0x1007160b103a101103e000c1d0340c06110300e15500d00b80d40054030481c8942c04180e07104021404a5105a0400b41070700705030b6800c005200160078000c20204003c0f2142265060f60340d172020303052442c10b4801c2501400c43e4011803080d0006000100b1395614051030081c2a2009041d412070700301031210800b10000a101c109031a03e824144d102d044d903945000e03001d00c2070141c130072900d10040c202040406500c5a00c244e060f4511a480f00059006042c1d2a000d0b5140b4001c1d0310a0318900387d058002c1c0c0c502c601030441d0b000f00c28500310351414401c04020780036040b00303030405041c00344050b4414103494001000326500c2e913544110b840051203032909072292540040c20b1804100600e1000b20b5410201407483e294081c050070740181903800c0b20f004500e0554061501c031020709455100b015207000355032090400082564a0b10091440c040481c2400c94200d80c0780d60440c410409041c0b880e001b52201e60406600034200b500c61a40c40380002010303289500400720340d0a09655a00a03501040c42d806090355513256 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 215576375 1250 215575125 215575133
    0x10213090605090f10170c03060907081c020a1502090307091d0a0f0f0c0b12010f06020604170f0d09060207111503071d0310090b010605120c0a1b 64
    0x1000c0c6210320b41c818460900040c00108141d40383e43c0c850107401021190321420000c031040001140060b01c40c8500c1440c50840315618100301442c001c10514000700320b0035140003410341c60580340c404106940034078080d2242d64107400042070318403d54850202c5030b20300d8220003280300074095200c07001d5240c440c44c03400050302a03c540c41640c54800242c0c0c44445005503c4202d542d40081080080c205c0b41040340420200380d0020780c4a4166116502508910b0390303c488424098110089522004010800402247e41c0e03054540300107150500140800b440c16449030746c1c10000b180d01a1010100014224401c0e042000483d000102e845070104a003c41500f851030003500090412102114034035104205440c01c11f42111000d0800c44090345195a019000c0b1070845141c00c0513030600c00e0300c03501c000c2140c0c2c0602108041d040041000154080c50381407500d804241039001c001407200c20484a80e201c144851b10300c1c1e1000c12004d0781c40d0388409006c0200e80611307c08400b9140fa202040e4940104 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 215577625 1250 215576375 215576381
    0x90f03030c020105060406050a05060a050906030708010807060f05030f100503030418060b28050909013201140c160b0403060e010506100c0501110a09060206091b1201021309 76
    0x1c500754002c00a65403000140012182180926640318541d00801c004901c1c00034003d0602045c00d260081c10241c070200854141e4005860f440c0120751110018812520200000340042c08586000c13182d2384c01c10280984107220181078000000d403074900103006d100313500e60342c8001098044c0440e03558503580c10100703080c1544a040c00020604001000940051480941c6c0b0305031810050705484c55822105007a940c1c3c0c5102d082d00c00c0c06001d00c020615580c0340f03003045009011510055112807c00b12807803200d4422504200320380411440792545076640100509a2540e1441010b540e0302080400b007484d14241505881003207901074404984c2a1940000d081181d101c1c8078288601c1c940c0b011aa030a071203045410320342048074070007541c00042c0308070004034105016800000d00150358450402d4140c0c0b104003400c0c04603540400c10408180d0401029610148580160006240b4020420262130022210500c107010400300c0d491144020740c100c8401d1150314403165180d41d6130750407820103 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 215578875 1250 215577625 215577641
    0x81215060406030b120115051009051c03030c030c0f0c08040f0b0a1d010f2106030305130501020105040503030a090c0906080a0215031e09240901150b1804090f0303 72
    0xa031030030185d44c450510140100740b0010780f5914100d50a508010070302c0070301c4022038200010400c00050004841c0c6032405103100c000c0389204524010b106505000c0c0a45600c42c0d4004201441d0050010310380354840c2d00f400d1b01ca1074034a40860300440c1801c002c2a140119040a040000c5042d170004218040600500d91003546454400d5400102420301d410109074402c0940070404640000019a10825000180d0742d54100700350320307011620313449104544103600200c0104000045010b58080907240c0751000304400d00c001d02040c17400cde075900e945078040034010310380d425103950401d401c0041e036403043e02c080d000150080104c160b1b1441c42565810b18044140e029041141410340b0b000507580440740700d01c0310241c2c0e109800410000b00319034808010321a008c03034081c45d20080540c2c40c92126100030440c00405007221810074400003802c441ca0f0b294070254031107041c002004214034541c0ac0c0d800721f0002c0e65030480c550320030501080c041d0410050003054010103550741d03010550507900c4105 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 215580125 1250 215578875 215578879
    0x2303090703022103040e07031803021b04020c0703080310080d0909050c03060102300a05040305070b0a02100207050111030702010507080f1e091603050619020304081215060406030b 79
    0x100c01c0c4610003039040c5964441803281c01c03a0400c03c800e111100c4100c0e542900000341e031400003064004a001e06031904264274003140142c001c0c0e80c2d104410f907610300750707918102c104680440c40c004030540c0a0b47d0706e4200384001000c00360080000307a03050aa8150250050401c035040e05d41024001d03400030042103281c06000606450710b07010402095409040e44c6c07140d8010380040c0343c08920658504810415080064014150660403260b80501240a402c00015980b96592280d08500d0081e05003107083e0411401250184000c0c02a541e000800514418240f44016034440041c1040c5000d022042011008103500005010310b40340e05500c000d1046816a554151a44808060446a0200b55414424211070049d40b003908410005a19004a601d101700c0e007840d80c0e4842d550700c1c08841c641c415909900954100414042204003183c1c091200d82800c501d586050f607a008814003a2064038201d4039030b007800013000e100300180f103510201340c020079a51321aa40c2c1c000c000e0143c205455014 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 215581375 1250 215580125 215580139
    0x6020d0f0306150509040e010c021b090408030f040f0602040e060f0901060e04020c0f0a08071b03020d1514100501030b0906062506020c0607080105061603230309070302 74
    0x34000c0c407034422001a10b850104105410400200c02c440c1a004003884580c01507072010740704100e0a00344243d01e440040354001c0c066641d1040c02500e80884240039040c0a480c103401000005101e040440c0c1d40000d4800c4020201c2d00c1d141000b504542281c40014041403000802060307021000041512462040301c4008400d024070040c0540204288076043c0803840d196846c02d443c2c54503070050b0424502c07034800ca6652400749044613244c0034a0103016142c1c0c031000100901031004028406041103008110369442da455903000c40d01c03003048104050700110300c01600e481944580e40250701ca0290b04014580f55080113840e4006401d040e100c1d20f40070900d045824815400c0402019102ea031000b0300703880c10300245070540b001801003003009142a018010005000841900c0503110341c449a40041c031769450304002c003604901c2c2c10380001d40b00b20700500403a0300d080c4510500d140711079032515000150b803545440c08030b500c003021240c0303645405000c400c000040c2000038501c0f080b64021580c074 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 215582625 1250 215581375 215581397
    0x10311040b0a030305090102030c2409030c1c0908060703050f1302061215090118060f0b09010e01030f020409090c1d070e011e0e030106061404060c060207050706020d 73
    0x11184115078103600080b0741d0404101003401440500001c03007060041c1d80c43d003c0c01a8000e4108907011007890f240001c22220f03419109600701c115030b4803869400040d40307801888800c0710b40d22400307400c00b42c411501c0d8809001c103031381c03150f503200d4010f003088400c8898a0030401c0d0054064002100c1c50507001c410b5100117141000c080540c0380c0e0841d000752003640b90140e9410039130040c10300280300070900f00341c080031045240c41d2400400d0081020134500400400d60000e0b40045d1002d5900980b1100ca010805200c04101e01c0e040b10510a03007424409071480d05040160003408011881c80400c1d44007080c0003440f03407920303002a55003c0c4140c0000150750303201d4901c0c100d8141d010110380c811014000000b031411740900a1001009414100b149420201d207085410b40110b840340d180010741105594205410300f406103002524550528003004040d5a0903d8a14082c3c1d2040d0410402240c04000038001d0641c1203e44a44d08102035840383d03a200c09004c0c0d9a101200003160000b44a4001 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 215583875 1250 215582625 215582629
    0x40b04180f0605060412080903060702150708100b0a02070509090c0a210b1012031707080c0d110c0d05030603070603060b040905040302030c0a051e03033d06030203010311 75
    0x2400b0070b84034004c0c101811316003060038007400301c14030000403a00c3da0707010002483e40381e40804c9224843d0301e039a80100420441e4860148240b40b01070620018001a0024040b036440191111000da50030442d281d52120403c0030101e26044c16a400960080e825106010000354045032181c23500d88240c8a188105a4542500c21050700303d2503050720110601a1800004070f15402d1140c000703200340c0c20149030a45613050071003055039074002207010421187d245d041182070304101d25800409820960780500e080f160001c62440b442e000203200741e0345e0b00305918101c504242501e54005d60320045683c001c00810f00034015600580340c0c50721a00c00e2020000301a407280c000c60040d5519483d03064200351402d0191400340501820840c290f0005102086910794100702e2051594051001010040030f0303100034000f114280c4040845580041041280c800000c5d04844c04001c07140341c040800d20101100c1260760b8850b03018403100b00d40c0e202000031320a54181c000d0741c1680c2c01908402a5040da40003 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 215585125 1250 215583875 215583881
    0x902191d15040902010c1b090614101b050a0b040b06060309030f0904060b03090607030606030c05310303020c0a06050a0e010c02011202270306040c1505040b04180f 72
    0x24040070380341d150300d09422803030400f03820440401c0e2040c103007880300204607650b00700c4006585c1152030341034031000c100300f04400460142c400145040e03906c4c80514007003200840c1c1ca0300d1078441c8403030504c8203a1412014107180420b54251050700282541c803050114586488880c0050340c041c0e500304803147c080f481a00d032000032a4040c2c48140011440c02d200c03400000156006081500c0c1c3c425034440700000c0440c2303010010362041101c0d030040c0040340782c603002c0602140d0b080e411110400d45051a940e00e01d0b5000401c8030052411071881890540302228001d0070a8401040c0003141c0e00401d0001081640015005465200448843d000d65072241421150380c010304c141c1c5800100d10802c00d048075409948542c90309030040c5485009048186005030a9a100c01d501c5084201c16100369a2201421040380d244908110040e000b1030416403602190003102e401403010720b01d020785159030780b03500907070442c1c008020081240b902ca40c0c0d00d446203010101c04000507040b040c200304036402d40f1a1548 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 215586375 1250 215585125 215585131
    0xc030705030628060b090406080c0a0918020312030a0507020d1202090f04060f05040b0402181e09070e13092004060906090501030201090e0c1c0902191d 67
    0x74005004a58440016000400c0f20070124403808100964280c400c040d81d000341e01c044d00c4064803807940c407401c102c10301048900c198000421a00081d00c070006507560036812204403401030b00c0200f030b114061003100c076040c0329540c0025030611428000a006242100c044c0d0711803c4c0b03070b1300c04001c00e0351142000d0340c84006c00c0345038000244d403400d60f2105403002607001d840d040b1005440300c00b81c04031180105045481d59005580e103a034022208000626044c059815805015241503003044188100350040c0303980054158810300d119500300745000410206805031640090038881c841c14096405000708014a1000d4041d40c8910300e0300144240c107000342e800c2e06600c000010390420200203480006441070f019a030740310781c60f420002038841e554052000030308115070000486500d035100160040b0000c0c1e001c440c900c610001000f80501c1d2250640d69103100001020f0b100f0280c401d0544000c00954000a41c00030014440098000e4800058020380303810f074003801d0800c0190201042c42003011 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 215587625 1250 215586375 215586379
    0x724020705030a06020a1701090204150912030f14070c0f05220b012c10020706050f0703030b10092309010b0a0c1e03030605150a08040809041d0c030705 67
    0x4101843c0010041c0c0e0080070218120300e402c40e410b50660f02492070b41e280030380c840340400350040780a00455000d1104006415441d0a019490740e2034410306801d00281c0c0d403800b400307021840b0407481c1c3c03c0f4003a1a13588070051204510b6550790b2010310b02150105018000c50021004120000c560703400c0400d10300134141101c0c20340c07a2800d02c880029402609031010264100001404ea07601042005861130703010165603211142301d007405005001d1100c0a4014900466104180410890382c214080340d003030f600c5200740e455895086003019400340c200a000150084900e80035051031552001010b426204c0030102c030070460380040c8035021541e0814160302e5021690030010801c4100b980010704055220382001002940300b80c480418465144582d547c1003038011540404269151107444082c00045503013100340403c0e41000d44050203950000341c10322584402050502001900340d07a001d0400900501081001104c0c2c98420220380000400510aa1030103041518011a07010251040 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 215588875 1250 215587625 215587633
    0xb0306100201020c0d0801031704030210030e120a030f0c0e18090114041202060105010c11060307090503190c08070303140d06031a060907080105060306040903030b03072402070503 79
    0x148004002245a4020540056640c200415052a0300c203224504044484c1d80b1440d803150300d50f082c0315904030486030f01c2c9285400f00b00014001a510810785c104100701d2454002082950196410b24184100802e50552880860020002c07030f45a00300a5072081c00c2e00c018841419524001e1301d00240c0c4111203540044020039107000090178440c0b00e0742c44071941c800403491400207039525480e000c0c16241526142070b030380c050301c0603e0380400246006000030320300b14418550360b48680148808454100d4030175000040801c1985104051103006000300030160707505004298002648000d09900c111940c1d00c2502000401c80400b041d208212a0580c50b0840300303640d000348160156010041c0d10050700e5403041d02201043e00582c0e001d515900b111000c8480703081007000c014100700014144030420180c2d10040c4051385412044e00d42002003510046002c082520301030b00548580404950188900400001d00c14807520034642e4080304c4400361303402c080d648001245c507a010b9000b11501584 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 215590125 1250 215588875 215588881
    0x90a23190606182708090603010f0e0c030702070311010e040608030309010e1b01050f0d0c021b030a031e02150c041d04110f1c06090201020f0c0a03170f0705010603030909060b03 78
    0x138055211050f100e00c1200103511700005000010b040745c00a810813400f03a00900300602a240c85410b61030f030418202040c1d1411403428480080d81c42d052800020000c04c4c2e8485c541720164041c0d031103041ca000303008200f40441d0351240480e5907aa0001c13aa003004030340c00c0425040080d0400f107001006009200c845c0c8122445a800640d00d90707106100c0061b20520030013400f54220220312a080e5003452a034040c1805503140c2c4e894030f620420031000d42e4443e40003002003800094203d0f07090405400d0506204625070010901030742070a01c46000d8103065450130003003008418181c0f005105892119000342c00c0088d03104558031011608a81c024102c851503031402c156403900d543c01a040480003860b40303009101c13109580c81104071701c4c1400c903206070315103405404540c1c042c00386031501081140100b42e00700764000040d002003000e100280401444100501c04004802c04444080c441403104a40e038541c240b520500800492000760005404008003040c80d2034035020b00d1045451460015043d03403 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 215591375 1250 215590125 215590181
    0xa0206040803100b1206040b0916030c1101231806010e040c15031d010506030c0603040602090a15080702031306032d0b0405090a2319060618 62
    0x644090b0000c0d10007507541030b0006400d03c1c420001c012044080034060f031282024001d0002390f071a02003065100e500d0403410000303043d00b4034141c6803100b8136610300854580890301081da495078141c80c000041d5401d01c0c40c0c5000c0740130914a0204643c84001c0d00c0b006a03920030f46035071862900000e40108030b40180380100310058164484a410600408641c80b1441d69920f0080c2040f0a015041022035203800c0a44940305945a50303120300c0b03c2c158002c0c8054a0901e000030303101d1920441d014850031011022030305020a540c15200607400103402d0666094031140c1700c030702045c4082c0641740081d0702c090000703031091700c080b0684030400c681450700c0c4d9003a41010419030261102442d81c079110000f070f00801000d4080d4007080480040d403c000082d074141042d085c00300381c0da001000d40600e680090703075180019030100013182d048503108038034404002c40c42c3c45260910003d000c45584040c4a425000180200e03a0300c1641140c41000e0b1401100c00e00c900c80c002a21884195a5a040303504d00e8809946 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 215592625 1250 215591375 215591377
    0x306090a0b1605120f07200316060f02040609030b130506040b04020301020706050c03060a320d0b0a0c080a050709030b0c040503030f07030f0507080d1503050a0f0201020705060a02060408 82
    0x402050b00740a82801e10201c03100c12400303c1140c43c0c179408002c0000780301495400c0a000200c0241c02c620044141c12034034002a0389118810511042ea02c04000b000180909507001c00003083c1005419982d40341c0d103034002040244c0f14001515041c0010700880d24040781c45420a98032a4403030050807c0c0d581c1e9484041040c0300042003a42c040d502040200005090761040602c200c0182c0e034003583f41c0c100701c4188141009541c0100c0500360000c3e00c601030100d2117005c2d000700e03200b91469840441c850380d40458405080d400004021400d6003082c00000e140c140c10141b07441031300359a00c2c90156130392081d810903101d0030740b50741c00400c11080d428030106807130b0110a0344c040c1d20000b5407840d1a40e5040030a01d50b5204940500001c0000b08288041603448500d40d81072803004d00c0c0440c00e010854a4170a003901c00d00346112101d950b02d407560380403c444c40702100e0003550030005503046a861400e01800f10340300400f0407801030094460105042c035210702600d151580715030040c170305a40c41360780308032903 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 215593875 1250 215592625 215592661
    0x60203061503040f0c05010f0e0d050102040807080607142514120c1005010b220b0403080d15060f0305091e070611010209060706090c0f080109020306090a0b 69
    0x8241000a601103007000803000314000e61050341c04400380c40d8181401540001542c02c030794100600311a80714030b1583d01404081140074212080100101c80d0b1070328078024442c40e440101940100040004c81200c04540f85100304951b403150103410781600081c1107644109410600011201d5424529200d08003c14880051080103021003544055a0040c035180305c20903125452138002404566806050001070480c90300c44000340f01c2c6504000901c082e90040c0380380094044220350701e0501c101d032501013503001852024205582c2c0d50b01d03801c005506506c49190034a00d02d0509202c6410180c4a10b02c0d84220b900075a034111903510490b4044000e400040c00d042c0c480d22546109021041c066201ea01888034013100030080c5524110f00682110005500351066902c1400703483e049495100c1115607003603010b100050840801c1c5440c281d0410381e500038106c40c001440011841c884150300406080e8001c6044030381d184e4035045007a0340c0301905c050081007800100003040d40c100d81744d0f80e20700c0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 215595125 1250 215593875 215593879
    0x21807032004031b0311090a0f020d021b07050306060120010f05070801120510271101090e10050f03030f030901090c06180e1302030312040203150f0406020306 70
    0x4404905100e07200380c1c41144210400750800c0010200b040000301402070f103400d84144130304140540f5507121003800c20114220140105c03030000018002c1910356001e070350030040303030042191034a01d01c031100300c020341001e501c200300e080c03150309801d220600000d806000c54000400a1000b9a40c0c0c800448429203006840d2400e40103c0079940e400607428080c4001f8410f45000c006100d05d8058001441403d040e8070050800c0300c010461f001142001c91030b100c1d0000c072141301003820f0f80070440d008468071624640030b1402d080001039100708030801e2110a807940090f40d0304400680c42d40e0880ca070290040d1107406480140742003c0046080500b01d01100f400002c0c2aa410205081240c0d15107500c12924401142d64802c00003040200c06542100602414541481030004494500400700102c0c060014a01e43e5040020b54404600c08031802c0b00c1d50180c00d0b26100d80303507036446140c00042a0303000ca209000316031022006d821001102ca20170a107141070301c0407071345454071000300950001e03011301c2d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 215596375 1250 215595125 215595131
    0x308090616110c0612070e060403050616090806040302160603060501090515040e0406091a0105010e120f0304030501150e0402030d0c0c0b03250201020a020c1903021503070e010c02180703 82
    0xa83e43d644070b0140c00541880c149101c40707442d1070f0000030318080701444118403407071052005001158001a0b10b5500007284e10b4140c1c6039802c14041601d0003004ca0340003194074440e0108020401d0340c0031403240c0c0d40c0d10701540818040e40d2110800c1c0c0540300b02d401980d0000e03640c49070401040c0b4000c003000d034a030704000c20040e00e455118101d48115040c102c6041d16041d4440b0400000c0042c2c441250fa880066170300002c2042d418080002c120030718180c0300910414110303141106500d40ad10200603d2120101143d03a200c0d5a07183c43c03806420810a0742c01082030184000542d00d0880390042e1050f54024080c003d1070365014400c0d90500c52004068512180c1d403080443c03200c19480085018408500c3c04580c1050840d0390f500540c0c000082c110116401032101c0c550158001070700388039841045814000c0004c0d0445494200300195002943c000340844140b01c003102504019030003188541d9441c5c41e4800d50b000103450308809580001e41100030300058070080310a02c0f0303407590040c070103203008 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 215597625 1250 215596375 215596393
    0x2190204090b160f05090604060810090f0e0f01060602030412050c100e100c110f0102030c030706020406080108030405060d050a0207050d050310050103050f01270e0a030809061611 79
    0x100b00107002120a0403503421003030344240e410384c0c200b5074030801d00a0500c1c00340d14017440400480c200303024502c00c88050140200109010207041804d2202801b40e00710204a1140c5caa00c2d00c8000c4c1400c1d403020cc50398080e000d0a18242c43c01030040c001607031050f070025031034140341481c01d1102540c5450169150f000381c41d0014459a41d44600500c52082995000d01480045042140c0340001a20a00034000744821f480000307802044007200c0194116640c2c40c9060300c500042c1d0440c03103581c050680a00000818004201d1a80c3c054016101603a4848000d40e132140644e568920072801202d6002000788a40140f4110a404c21680035103070704009810301807250340c0e1500e0080001e08500c04104084204148246a108043c0c0140800d203800d003c2c07401e0550201140c0503060154030400132101a600c00315480c000501140b0741d80c400e1040000c50444000691141d8000e4002c1f8005403028003c903c4615000907402e0003135000321001403202201c848152604803040003c800c41c0c1c01103c01d8 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 215598875 1250 215597625 215597633
    0x5060705060c0304021309240507020706050c0a0b040b0a0507111507090b030f04140c1c060204180f05070f270801020f040806090313030b1e04080d0c0e010219020409 73
    0x2a140740e403403189614082040a20038046e0200171804040d4230300500d4201042a0a540000d0700f000f2540242045543c50142010103800c00348001e9001e80801420802c1c401005245022284103aa024800304404d485002d012500d00510610b000d13402d5000c682000301c98484282d0340c9402145505122002540d02c07006107440b500101c51849841c10300d1001c01003071000441a8100102e010800391001c54501400a10302c244d0010303100f240d4941d11068103040250a90449000d070882c40c884c4250960f506142e20b010704a03485010b01ea450401000c1fa00c4c107801400c0d4043c881d410303620350f0000440c4424031007080b071f50081c2a40c44985441400040d0100d001c1c4000c242c02d00740d8030401540d55003451103250ad40700707000d4003d0101c0d902c00c1041284900ca041440c0c016a0751040700d24020f511020143d05081c8040781502c00d16140300380501040112280090406110007036050040306001202510704181c8200316a003d03810100b6520a2841c0e46480ca4064510041c40010300512a0711 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 215600125 1250 215598875 215598881
    0x305090a0f08010f141603020f160f030e030318040b03071a040f080c06030403050d0b0604060503010513050105150d0905010c0206060306181b03010906091b05060705060c03040213 79
    0x1100c051180d54400610900b90a20300030394114040035000203039142080d0b00009030746c58981c1036500415a000c240c01c2d00ba5241541102d104000b9410954910301781420041400303120002c0490115280110000c86403c000c010b0360042a020b00c800d290841c150800e0001924404000d603525004007900403607940d4658070250308511110200c0d98031281003082600e011800c58204040d95400394035000041c0d920b032030840380c0c400d600d85485920781c851840d40c48080c1160b482d410782d2200011801140d143e0f4800c02840c100c843c1150801110150151140708075202802011f4006440030111000001c020300142030760202000005000b44103034980c0e80c21100b82d944000d00680044e400e00c02d16103010460030390001c00000e0061000884207016540d50710780411620001da50782040104103980070352200454982000341448422003603d0a032070400241303240c414400011440120702d508003582540c00c4507601c50000d000b030340c80740b10940f00c081e0401041203a0040044460000d901c403540 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 215601375 1250 215600125 215600129
    0x90403120b2d0303040e040f020307030c120b010905091e0c130207020a0611101d0f0c0a270207140708010504060b10081305030d14040c051c0305090a0f 67
    0x440d1442c405074104102d104155501080180300b030b07006100600224102c4203486401c1070b40551646002061480464204002d40e40060444404464001030303a03180204030000c6d451003507001c103109a072603894a204554090355852690380c050141c03068a1002c00300b4125540022078115044403034024005029100380a00007600d1130740115443c8114144040107502400d41c50504007006203601c4001691005a801b5000c103280e150403a582c158544004010002c1c0b8000041d59100300480c0c80d800e40e1104d540c00440c1c080c010380c4900044502d243e0031580002d50082142103542000b000c4e81d1000781d0081c0805031a03100c41c2444403000440308109500c0180312200000c1014505810148200c6508450301c1e402120005501090b450340890707080e42c01080c0c80074a1030341d030505040803441d5000c1d8402c000f060b940b60612000703c40008120f81482148070710307248075a14ad280d10070321010003c0841c3d17106000c00d035400c000b0006401358000d880022005000500110360f20800300c05039040d15 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 215602625 1250 215601375 215601409
    0x60b07060f0c030203060105070f11061b073809060a020607090e1b1c050a140a11042306040902030421020c10030204030605040503030f090c090403120b 67
    0x402850701c000c50640101e410403071aa08086041d444c1103c0082d080b4800c80d04001c0070710411441c0030040221618000c4451030000e0400c90303c030031a10445030741d980115000d080c00e80c800c0440008072240122182011540755078480c903540030201d005817016806000040140c0c8109011140041e120807003d0229036041d540240500d0400000c05014800c560700312541c01410b0f54100543c40d092941d00110107890301c02019690042500c5005100700d8402c0780d4542d0605200500120a900ba04565460340c1290190b0407191070b140c141000b26000007948a420346002d000420081e41e6120400e81c0461040743c0200c1c4c1e00380c4480000e0455805900b1524416070b000c402d010602c5803411060401d0b20740c032010109500160400a90341e071030550303045c0348102d594964203200213110341c05440085610a034180708909091400d0368494008803402d40eaa4864000001c0120800141d039600840c4040c01c0700d8400d0b204c5450840f100754618041c0030f0344948504606495480c2c40b0241107480242d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 215603875 1250 215602625 215602631
    0xa0504200d0f0614070306030302030f210a05090f06090706140f0c0102041703090a030204020a03090b040501090b132103090b070e1c050312060a031403090907171306060b0706 77
    0x51013001c002d550402500a5040601e0002e05200180e0000f0440d82808507050101b030702d500300d10798685c0d40100c29101c612240082101400603031410b50700f04c14051004082694080c5e0f201ca48055500c15084400702810b602c0000208001c0b03006440104102071803000442ca40315860345040c80c142d00054903140c85a6000504101040074110f03240070f2520078101640c41d007040e06001030210010350202278481c42e4006000e0310b50314041e03804440e003964080501560b40c0740904010340240800c420540302c3c0728000c00002c00d107800c0310b1100038029502c5218a0080b006196200000c13042c510201c1c414180d82d040000c01140414040c0c42c403171049a17880300c3c0c0012900c0240540b005015010036540080c007228000041c4001c4180d499004000c0e41000c0c0301d54480300025104c003ca40c3c40034140d081d0742c1c641d201c10500003100901c9019025500c84405440d06501100c60101e4203010301c491a1130705000c40c0340300c90700914413011540100030100d0156150040c03000345501042c800c95034156 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 215605125 1250 215603875 215603891
    0x501020906070822080d080a0f090303150f0e24060325030e0d03050c0403020a120605010f0311010323010816080f0d260c030402090a0504200d0f06 65
    0x21a0400000e0505103503a40101413a2500550b15600c803468807103a020702004400180c41a41d07641d01070940368102e000140b110000b1410060010003041911280304030b0711500104860504000e654100d0f844180384400341c2e0394403501e00615404890f9055991010601e42c001550713200700145005082282ea400d41c10a0821b480e0b000f419032050940051600b02181745c00c40302804640d102c0c407002e80c1d003008902c903074842e00020a40d00c910b402c02580000e6134600070480444150012086912030441004140d03280c0c00109a00c00807480010f0000d008503911049030b520075080354680b804100381748006030309401d20040640009070800c100710381c48000030340c14245142c0c44600017084500c01510265102a02050322107440c000a0fa05010350304404000403c505659540507010100102216003003c4180d086194000e880a900c6080500d0108011900c2c0b4030035940280d5000030703450003100c40d09442029041c0308440860340080c92030400400f003642c0e1403c0040c06885007000194140c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 215606375 1250 215605125 215605147
    0x30d0c08120a0b041d0c120f0f1501120c03080706021e1e12010b030403020a0b0c04030c0501020c0906040b060d11072d06020d0608030a11070602030703081305010209060708 76
    0x11780380e500816424110000c000c4483c40b011075000c042e0f14050300c94a11036040200301d5880d0642c01d4803010a148100e048800410601240c820b00c401c0c10f40107446032590380c46900b4114154402e030094180d00b84102c04000142da14001814a50b103d00390150510034900c8400701c0411103c88016604080001c58040c000c891094884804440105480c00e0441d503410015250105020740c8000c00d4002002c9130074113000708044540c0503848900b1207060b10b01400841403640061004071100040b84101103110343c00031403035841003803019000380c9260741c03000d04200280600e240340540202041010b11061034542c0160300017048074040782075480e140c0f032400c00e83c2e80c040c928000384244e000124401485241e080740b00f91a81e00401e0160f1121809100381d001004254070240d22840300103441c0e403e03141c00428028881c2c20560644440382d42d110801d980303a2168003001400148040c00282e640e614840310070ac011402400011708120407030010070b02c16889003500752403150000c00c42c85901 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 215607625 1250 215606375 215606381
    0x903080a05100308030420120a03022a01080720070e280f060e041211010204060903020402221d07090e04030e150d020408070f0302030d0c08120a0b04 66
    0x80d05241440320940c0f468035440e90a020160004060441008841c218040c254454000c0207000400001d1400601610203655814582c0c00300c0141c052140c0700c0000f08600200340c407814000289030864007201000440d0002c40c01401082489106000c0c611640e02e452501244800f4180003001c1180c14000d0030302199200400c400b8045641c0c0001000a0b150049144084030040740c002ca12110111013110140000740c014050b01c036404010842444004811007010b4015620760b00a0b926110521500780e2040780224004210501410401400c2903030081c5000410041403c41460049520060041d051b070300407044540d140c6903039a0440070549041c0d401103501d0a0170001c591514203081c0c0000c6006001400703000e13800c202c0d40e40707544a90f0360b202003078005030a1032036076210586540350080d00240100d464510034548041640410b900c80d1406407030300100100382141c2c0e011421903001428550860714001c0c02d0044002c01d1007490090750003503a03a0000803c1e610080c000344421 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 215608875 1250 215607625 215607631
    0xf15021306120903170a0204050d03030902010e010201092607080d06080d091505070203030921101112040302030d02030a06090506010c0c0b0a050903030d0e06090a0506070e040b03010903080a05 85
    0x9454501c6540c0026003011121303128004c4240b0185e200c0c3d4610300a403000f401241d00190300250310101d00c10404d0303072641c0681c801a10036210303030307008440e100012400c0f103500341c034024030040b0f1601100d401980c85414450040c0b501c0c0a61610300550b954400d1616082244041c045584400701401440b00c1407107403406d42c00c02450421805403074a040d0a01e030383e00c1c90b800b51080c0301000030040c0654509008882e0304a0001d40600002c00e0381c9500d10340400300342c40e540074850048030f417801c1062806010b04500c130210081110308008040c00400c10030035010f001282544000c0046034114a05070001e18894000e05c4800541c982c034089008065902c01002c85041080c2c6c0c3c1c00a0340003c1e0308909030016a2600c3c0145500c4089005007901c0a100d0900f003140e140c400400d0001404425400151070114002e060301c056407607800030b060b9142e801c904001e140ba08283e0009000d21b02c907842c140f030404001003010805651500200b42164079164065000800607001c10528801a0180c960 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 215610125 1250 215608875 215608907
    0x50f0f04030905060307050706020703080117010902011e020f0615093304060819050d02070302150c0106150f17060d030302030405070b0415090602010504080301030f15021306 77
    0x441850107690007080c8000034003c0c1803061101001050b6494814803c1e2a2002c0d0700c060115500c030500d00300640311520134414511b0b01e2090100117006200180a00b48449031b0684501c1c01d80200c0c903a2110035001c200741e1400c1103104078070350410414400c20131a4090400c0401441d100c1d000442403001c0c9010041041340c0540c5007509802401c41448501c0000307002c0ca086800701c81c41c00f1400200500010346c400c00b120720550850503040d00e030446840d01c111b445402140d24030010014240d0b102d002912010354070080b2410304051249010b401000c0e6100b40f1000005c1450b241c1908607190120041c0e8000060f040e151090f08441d00306440c1c011311400010010420f2400100041000505d4070008041540220105040100401104000c3c004490034951a01d1712510300000901505080c0e1300044e03940034000030002e0040c400c87c3d00454001313059501e076070b00f0b649a03107401e8288540200c84d040d10700541401d6905941c80074040000307000d41600c40b0585050b400400c182c000240e402 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 215611375 1250 215610125 215610151
    0x8011406090402011b140102090301140403090512010f2306030a1110230903060f01050a0302041812050901020c150409050601210209090a0912030e030913050f 70
    0x5507540c820020380e0040d030920344140d00480203200e440c883c98502d007004000540054043c0d20307061040d0068402070b030b4107800801a0243c00c0c00c6100304010195801b4011800007082030140f03007040042e45040201c040700103e644000c1106100c01c668061100b00750030340c0f0061241c4216410902000d40101c0304070014966103600c2e450384180346082c555194802c4001d4000d1404180c011b4070203003c00c58141c80c402056030038040210003158840d01840744070340180400220a140b40b141c0302c80c1a501d02508500540d41591b09010040c910500400464a60020320700005030210650702ca0f42c404603642c00b520f4500360000a440c1141419049100310a10440307106c0200f03032070054070700f1998906008140f40d100c91005898001004229902420070480c00c500103580c40c0d0014a0b4040c0c041c0e45200c090b95407881c030340ac2280e401d25401050014814654143c052298225800900682d01528944940000040c00f035080314400d60884a0701e8000b04682040918049a40004892890 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 215612625 1250 215611375 215611381
    0x3030e060903060a0b28030b090706020a021c12031b1b02130b03060a0e0d031b080604180507030b070201090b0109150e1801050c0f07111c0c080114 65
    0x281c032444000c1c113541d181e42e92003c00078011b43d20084503544c062142c1205e0045c07485118200c400d888102d0006841841100303000c2042464001200d504035513155002c0c2c00c1200c2c0303640c01c1201240c4102d003080c0100d10101c06042c04501c04810313003c49455285c0300001c0050306000f14038060b00d51700900f0014444640307828210605048001c00009504a40c074280102ca94a944401400548451074141c4510340400465101032381c40220802c0c4518203c401c454205401242500c40c0e40001088040c1800072001010b4001e002158103c1002030000c50b00301030300180e0f00104500000305035440d600400c41001030000d001441508486c80388024080203007913072513940100303074184a0000c0003680d40500c521681c28081681e006002e80703d02e09906400e0001c50a5100d0318100e204018951a110224401c1c48500c000c681c10002d900441f2801c3c134443c1e8607129442001190265000110004c0c03403280866204050b204040c0304a2580400500f407400c2c0a08640000740c10013860040b480034 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 215613875 1250 215612625 215612629
    0x201021501050310020c01060b1b0c0d02100305090f0d03140112021513080316050d020a03080a020d060807030804031a0402060d0f0e011406010e03070b03070f02071205010603030e0609 81
    0x856000448004091b94801d0000005401041c481e40460400700000c01d22a0310100c1c015418218500c0c008112066a43e50004200c6002001003000358000020034214a050340a508015030044041e010b035a00105449881400c24540b0040c541c0040d07039401c030207052601d105200502426048420030a40056503001c68280520a0503401540c000810345249034a03001040320060564481a2525440c0d42c0030013810300f40c080725044032580224102d0301c000b14070000701c54401c0c0743c040d5120340494541e500164001d501210003684820f46450001c500000d081064000541c4250b045960b6a0720718100340703105040748005c1007141020f100512002d40e03603020680b42c91300501000029041814500308004240b44255130806500303111660108410700d500c0340e031240c00c080e2a50031100081c0c40401d0b49a40e514080c0009080060000c10700b054403a40359004a00102c0c01100c001c5a107440b00043d4103038083d00c0499044e915900d0034820198403401480c8034040a0f1103a504200189c80 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 215615125 1250 215613875 215613883
    0x627030201030b03160e060901060203270f0d050f07240f050405130501030c080118060c020f07030b090c0d0809012f0303150105070308071407120c02010215010503 72
    0x80081d04040d01c0350044280380c1c1e8240032458a03c0808a09105815605c8152261030b132000c40e8258421350621000041c000e002001b2101142026440c1c00341c1c0015100f60200c6032030010b1465034101ea0030078840c004035100c4080c1e681500c2e02030001004030f00c2101c43ca0928000c020b0b00180c5082d903240045222804250220b0309605085042c2441e00b89240a0f08880f640035075441168001c0c02d100c0800c8002c07030290b1105041e82d015045442c04503031203400c20b900781c40003035198104001e628140c1d81c0c041051035200d58204480f500c10784105114682c84a0b280580d00d07001a12480754010a0290b10301d01040707440032680c4207a483c004048140c0d2601c803294020307452500d06101410701c2064001241e4820104200d00c103280f0b03003411101d6100c0c819030701e800403107030300c0c4040d40c021b09460501e40c000c0007500e10307096040d80c501aa03170b9a11001110710031440006098045400d001050005207000421980460545e0314a00443c5041c0002890400d503c12080719035544040117202e0b07511f004c5 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 215616375 1250 215615125 215615129
    0x150406081509210c011503060b0109050103060f0302061e1314010903150507020f010c0e040b06040503030901262e0602030f07050307050a0b04030915020304030303050429010627 78
    0x15604d45402e4401e0383c060141c160b4055800200c4a00d00f004000c0042c1c503800f103030110b04285daa0544643e110350056048505601901c544418a0b1000f00014a0014000c00000c0d02c103080203829000c161070369901c1034104803207040303e0f1040c00070140000720080c401342c00034120920300480d02e1480c6485600c0c0c464054040c822025840700e0001d0089802004541421003e6400800450481102c01003020b07402c40f841078400c508007402e400c514036002042e0703070503505d0044c09589884115401501c20701c0c0d0340d9030f1101c42c1480d00740741188082042004d89215107040c6400541c103102e0012020f100d1200c032031510022141d10807051114650001c02d41e010480107085a660f00c1902e0705001d407441c01248001803403403081640e1701040040580b42140118400e1700c421080030b88500851a444c5594210100103a00500c420000700340310344c10154209028064003180d207038080061112202410f01000c00c0504000010040036511000c1648200c0204201151146400140618811283c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 215617625 1250 215616375 215616433
    0x803010f170d08070f11060103030206090d08100918140102210906220f0c050a080a080304020d1106030412200705150c0303070306060306090605090708150406081509 73
    0x5c0d20100d1511130003400c8002c4004002412a0745542c0d40f441d000f90345107001c0b1030f400028040c0c0354038a40e101e8001c3c14100d00405100130050229410401c42c10001c0130382c40c1d9100e0000804290400100b0740d60065040560008800540d9908031010800300a0b205182c140c2d00c1c0604107801c00540c030602082003608280d80210344031311060220521200f60002c448041d21101c2d1030b0402c5020401c0014500c0d0444806954690302c10355900082a00c82a03050070140c01481c04000060041c41c0c0301c1006d001544c0306910404420002001040d8a900304980444242c0d9200a96049054009103070091041c0c02c400715071070b500740305880c0b6915800d1920400b4010080203104000402c5000181d0f0910940c00080725101e20f4503800c014061300d06d0748542804285020000f00f03480280b030250360700b5104041c0c2025200d494040f001c40703244100034017410610036102240c2020b5580d9006500040042100604044170704204003800658068810602c991204082c101891201540c120310615a = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 215618875 1250 215617625 215617637
    0x1020714090a0c14120a0e0606012106090c120b0603090a06050411100f0801080303011422020a030204050f0402130506030408070f08030711010e0c0d08070803010f170d0807 76
    0x100c03c081d00c82042164921208010102e140c0e09000403042c00702d44a02c0c0c01c542e0502100e120711b07003407039214401501d0b524000b80600d9420403241d0034000748400101c070f01100000b4001e6032454002c0c00c6032a000d4881d4001b501485404850003400d009002c14100102d41c01481c504042c404150746162000000700341c03644800010f0148050f89400861801000c4e02910340801c803014010000e0440250301c030041040140041680070001081e241600c0d820310580c2111301c84030040090121590001c0f80b00b2510702d0405281c0d1b4101030000d000e54a40a46015072240e0810040241c41c12041c3d9802d4040c0d48140038185001c41c1501c0f054085542c05d80341c00d40c0c0d0f40c0380e905100d1998810785034003130480c401400c46402003009240085100d10749550b11441c403009200c41460a80d08290207111080c1e0100c40d92415a24011182080301c0c1c3c4282640e5241000947da00300c0190800d80c4988098650a02c04110041c0e034600003204c05041d10000c0c1482800d4018050241d11317001d040f510401c06 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 215620125 1250 215618875 215618891
    0x36070909152601060f08032d0d0b061c0501060f030b030606041e02030702030703140a2001020c10050414031c15050d050d0201060504060e0a020a020712050c01020714090a 75
    0xc01e600a20217031020700180c500b0562694002c560b00d50001502d00720015402c0c490001900c084010400030351610b8603124a0107882c0900c2001400507500410b50011042004584a8035a044010801c181c8000302055940c50010050040c1013284116414103091806118481d0340105801d940060102d03400142104441c402e084550000940132000510010034400c005400001074070140e1300caa91203440910441d03000c0302582c0212004070011801c20008001e842440c40355110200b80d59038001800c3c005c05000c0b692419a04131075201c01c1641d02d00900c414483c1103908503840302c15500046280140b00555003040040001240088542d00c4800040090f8403046103001003000400b9807200c10900e041543c1c8171003c0c01c0ca450301540ca800710002e01d0f82854000e910849200220b0382e8515034640418001030f40c031940c902401c500400c14046050751f0844c1d9208211030150b00100900e01030880003a00d061250741206020219400721411142d440d65a2a80d2044c071500c030110b4485d03 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 215621375 1250 215620125 215620199
    0x507033c02031515071101030920060d06060c050d0c080d0c0e04240524130305070312031a0904020f04090506010b0702091003023607090915 62
    0xc0d207460700700c03a4444d8004401c2444000390300054109a0700400b103008500702d035000150215009810010301200c80c0ea410001c4401c01d100c0c02000d1400068a410325001116040c5c200301c4950f5001030021455028000b028000100511341c5103410343e040607a444442520343c001c0f030307000b2400a50280342d11402cac00500c2c98416140c01480c000050018003a50305a03c14a07000611110303058680d103015007400003042c1c0b8010f80c0d941e41014140d01c03401d41065046500c0342a9a00400c02254106050b940000000e00c0c10040b03c1e0003940a007040b2803d48001e410b00805031503040107129404529038141641030383d5800e030030a80040d41180c2c092541c50012000c14003619504a0190603400358400019a000703a0000501025108a81c81120395640004d01098100c0d01d00000e50040c0b0600351041000007080d82200142e20320141340741045880804620a103801102c0744000030700941d01c10804090103025601c0c029400c1c1d44030290344c904148140c4131144004045505040091320158640c0d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 215622625 1250 215621375 215621401
    0x12c0411030a03030509061f09091b17060f04020102070b1c050f09070b03040c0308031f080a14190602031803071109130c09020703090503010507033c0203 68
    0x110348054103941c0940428200070300100001c070f6083c103441c040c044c0002c010b00710b00182c004660410003105803006062080500040c41c410401321420200c0110003040d40a1009401004144050f0168074880340d052482d81040006024108c54407840c00a00c80140c0c0c0205002040c0d5410509907030b25030010950200c819020341d4158a8518901003c1c042e0740d41e00b51560506c24400d07001102c600954850800700c0e80e200840e0040c1c0041900c2d40700384000348000d0000c0d0b410900006002d8400c1030004c5504881d05142d9015104030342c00500f0000400c02c0203108801c800a200010340b03000c0c16405c44004041921b610000c0c0650742c00000980e28160103079400694a007543d0880380c4070300a500d001510b108603510510b204441040015180c91011000007102035804040c08420a04c1c015404019404c034500480512403d6000450700d0788003480b4151181e241c6035008a1000b6445102500a010b404e00304d00d0003031002000141d41040b0391883d00424121441c00581c0c1b40d9a0344403040003 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 215623875 1250 215622625 215622653
    0x1c020a0c060905010e12070c1211100924050702090402061e03190b0616050a060c0309060b01030b0f1201060317040801060806010f0302060a090302150a08012c04 71
    0x642403510500000f44001540400c0c0c0d040d980c202200d40014403081c540e8418041e1041c028121802c41070240144030914410300c0159108806000448c40b0b01e43c0021600c5001600c0c002c00034201010400c0010891841900e5940035038058844100c0388582c01406071281d440c001c0d00543c2c40c10f002c80c003192600b00032540c0400461840d2064200c020110f14555401940c01074980b841d4682c00c901e00e07480d030b48545d00c030309031000382150326042080e0504203011426120a96242c0100c050403004120f41303014804c01d000c1c00d680c0000b90b80d0307850324040341100d0841d0b00c0e00f4101440c0400c4901c907901e400340030f0042c4200c11110140100140c007121405050f10390001042021000860b43c15415090003a00584041000900c001515031703a100d030b5103110912801da12141c01c84030410240c00e02200402080c440c0c1e1078069481612a000b1500d18441100b018100312800100f89002540c004145405845480ca49443c07840341c0b40b010001c11584d24060110513000380e00410704008502c0c0d103d9803 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 215625125 1250 215623875 215623883
    0x62d0e0d020f03160603050c0301050d022403071e09180e0102190810060c08070b090f0f07050301060e010302060906030601270501171006050901091a19051c020a0c 72
    0x2d204d60a18101d869091803034400d06000c603007004041a114000901640d050301c20140102104d109141c003082580007400202c0e000b1428035981d050341500700400214400d0100d078803074a40c8141e0f05a528011506026447d10070001d28000510070b200b429210700131103111045021551289100d044c03802807040d510441c8036800300d404490051608548114410020201000d40c00380d81e4510a980815440304000c1c08540100180070000d042c00350360340c0d0411504c80407220256183c641003407400d40c0c40e802c041c4a03030b440031004000c146001d000741c2c0080d0801c104075181551456001c14114003500c05014403c050100c00901d140e4850740b02d01c100f03148070718030004040480034266540707030615004050000f40030380380c00e9150050b640140fa00074072503041c00540c0b1030300c0c000c0102d070319401020301c0c241001600d48002034504d01c00c0014a00e030141d00006503550702d441c960080602480392401a080c00001e01562240e035000344c40f0400000c0740301501582d10042180e046421000f0703c84020 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 215626375 1250 215625125 215625133
    0x2070b04030c170609070b0a031b0801050a090b03031801030b0607080702030607030c2c12010e07050f0a120305210414030f040603091b062d0e0d020f03 67
    0x2081c4801c201240342152260000300a000030161820f9454500884013901c05501c0160104000f990301001003284205914001802d1070040c18103080042e400750403080000c500d0300c014040c07480d2510b1850b00501d94280c04004401444000c41c0d260302a6250502c90203620010301001a4040e070401500e0740c3c0000c041a680d600079240051440e0803000043e40640315080005041c00e0007842400c0d07035564a41c80382c10742a10440c0d414180b000035210208858480340700301c1c41c0c01e6200c41090503c880c80c88000030492403018108940741044c5036103c18802d800310710031081240c807200e11550550391901d00300c0d0840401801c0c20b0384c4d584502c0c400d03010882c148451032156242c0410902c2e020b103210305c1014291003c1114656500d020f00f41030801c80400030401002614041c1d80300522462081440610383c13034003015070403c061803952040010400c3c0c407188190b000c100e07881140e2001c40d200c01400c440c0e0188180180301d04512a02240902d00034810301042d599026002d0035650310040807a = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 215627625 1250 215626375 215626379
    0x60307170d020f0604020a090f140c09120601051008090f0613060f060b09040902030a080304080304120f080a02220915050108060d12120903081e04120e0102070b04 72
    0x456030380004103103050050241c80d001c4111040040b8680340551b03001490a02a9801d22450034010b010541003020425900d41d0410003c092401a040c829480501d002c1d482d4114003040c41941030a00e40e1100031a04840014810b503900d4417041900d6040502d8060302654039a01140d00d0100c40b14624120b501c5004100403d201040d40c83c2c40c4c00c1849210140306860700444804c1c1905c1c5079000303548082c0e0341400081014107240e80482c10b028001000c843d5118026190340f08568810b81d8152102070780042008140071003462810341c0c070060f41c0343c2250880c6d00300b00000e003040c0c0068011307070b046a0001064468100090819040f40204402d090681507840c06010020080c0c5a20b00e0740c01112040d00141960144000e18400c3d2009005660301e02c60940d61607803403c515005030030511440e0210fa001100045c0705028030070b417194454040c10305100101804c040e00f0101400d0314040007a0420001907213160490710001603a0400045c040020300060303090120b02d4001c010a03200c08540 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 215628875 1250 215627625 215627669
    0x516080a06110c0604060e071d1b071109040c0518010f05011115090a0f0804080c040903020c0f130c030b04050601050a0207211211010c0203041a03060307 68
    0x8a4a40d8410318040040707180010304210705000c0c1c00101c6510782c12460010740800d10316001114a40c11020940780c5c49070f10b03061100300403481b95195400c1d0045120410100c40c10407504100c100c1c500609143c28074680d5a50b03031b05a1099208a00c0c00307080c0000128080040481038030001c3c000062041a005913182c02541d4021024400c5440d2010711030700000d200e5004412401d09030100101070040d900074100200301058019001d091103119000401022442c141420821103110340900756583d482d184003c2e24000b01040000d1145140088500000e80c001520b41400841503c010b600f406102c0000307491341015942c90000e060911203000e40e40d60349540100c0079940d080303404001c651a8070004449c1402010b03090005640300140030b000001800c001c4000c0070040010030345120003d55501140400c1c41d020100c00328098600360811424280a038000c1410144000c60405107000d1240f40420141c24421002101c00800300c0c1d0381d0380301888600040d2105040c2c00d400740f512405 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 215630125 1250 215628875 215628883
    0x12090307050c0114070605040c0b0301030f060501152109020919050114010f05030c07021806010f08040809130209030601121e030f0509031c020d09050613030f051608 73
    0x40c00ca038240034014008580d076001e503210064106041048900f024503d035a820000c06010f0820b40d40c00409190004078a40600003c0d80603605c50380e4440c0015001d03141600980e541a084802039495940a08190030b522041288180407441d03e40329040c50034202082c002d15140c0700c0a904440d02100700b00410428680b08003100c60700040401c542da903503881020042c60511001800a012405092900d41c41100070b1a0409082c08205142c407030158001030f182035400384908049205482004032030341c0c1082062022140600307003801285482c1e50398503414450b00c0c2c640e038401d201c1001c0b040900082503050b9614920040c0848825584442c0d1500303060324299021940408038440d525803044c02420882d4030258152aa4050619010b00c10b840b25040046441d815204120300d412042000003010400c841c042d0700501a40450304100900c05241174008030702881c01040040081e80d54400e0b04021203800003401e5082c0141d5151690502e115200e80c02c2940c9900074000c210b5040100d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 215631375 1250 215630125 215630137
    0xd050408040f08071202063004030801090203100b0d18051e0f10050c07060218030d03021c020334031401081b01140d0207150207020a031106120903 65
    0x40d85002c5503940c1ea08210381d40d20f000b40140e40c40c0004200e02000142040c00c0a400340b1480b51148492003003d803081000043e400011100390315904c14140410326030404041e40c05082454801d510350300d410b20010460034514403890f01269400540044105060b0744440e04400e66040322a40e1302d549401d11079a510300284030011a00c410300000710b024000047e04040003940403000d84031000400d41c004000745401410356100c96000c010800c00030f1213b00c000c0515020030320782841d4500d000c40c01c4c1441d210241c420700d81490305c10801c00d0200d0007100c2044283c440d00302d0016030750307603940d01000002b118040c0c0b012180d500340800001e820480c2c900007140c10b0301c160303030200881200003288600781d0f40d080c440c0c0030079600104244c2c01003141c4d442c032000e8003a506041801c00c4403801c185080c1c0d40c0d400181044900d1340d02190341005c1001c0d0542003594424001019828001c01d50005507540344540300041542c10f044030982d0a94840c00241e82c1d100c0c124107007003000e610300071020503180e40c454 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 215632625 1250 215631375 215631389
    0x702120a0c02041116060f1d0d090623090f0a06170c0708030606070f0212010902030f0f0c01080702120d05180a0b0c070f061d0d050f07030e0103020d05040804 70
    0x850383e510f02e480480917124440303409020020080065280c000040000d200c80101140c2c58480c0703010f429109022402c00d1024440c001c0070290800c05000745042426000300003001101c07000c40040e0501c6194170158242400000c0b0703074131640c201c00100301d1059003406581200c03603c04d0000c2d00d29001342010200040d088400c5085c3c1d6070b4215110784d94820080001d001804c00d102040075401d000003c0c0205030720030030042d40c41035000e0f0006a0740c2e8007100700300400360713445070f0600003107003014040c10311046071000c0241210345c0301c9149242c50b011a030501a04005070140040c1549108001584003200140980c0d079440a000079110701521048854038032100e10b40c4460b88417500b000a103280c54030b030400b0000d005501d8410000301c1c00c2d801800141c5000c402481d2031400314010744101001201520700c0010542100c0c501241040e264508a00a001042c02002d40307024450044450b5580d0500e01000c0100d80c1c800164001d00580700640260b910b0170781004100000b480080c0103503441 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 215633875 1250 215632625 215632631
    0x1106180d05030702031b0c0d060203090c0102010902060301170a0f030f030e16030b1305030d0905060702062202060c010515040b0f0109050f0315130c050901120b0702120a0c0204 78
    0x440300540d142c1c8001d80d000380042e40100184160046c00e0580d040c0d032451003100742c480e850079550004404e0048130038265100c41d400001d001c9a100e04011b510001c80081c0001d0011080c5c90b0000341c1c882c0014800c00c24040c01841f001c814469083c08081c400c1c542c000032002040a403030500038900d00f0103142c124046803409030003e5800d1030020304c1c04407440c0c01c42c0d001642e40382542d8402c991004c004e808809480000300720080000d0341800544906c1c0ea40359000a590106400c0061034600090003400954002c17605001c041301c0002c106055020100032a559014076500c04a0403600c1050051881c5500c1c04050100650b00040040110034080350b06000707040c000010020306c586610451404100440404c00071810f08820180120b40b00805980c481c00c0f032505c52110241040b40c10001049051540030304200050714a64064034003620350007200c2d81880741c1c841000044540c050083c2e0258000281140d00c20800c200c0701c00100c00080f901e40561100c0035102c50030240c030492080742 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 215635125 1250 215633875 215633893
    0x10050904050c04030f14070b070b0f0c03100e04030c02060c010510060315090b0a0803040308030712020403031205040507030c15120b01050f1b011104181406010e01110618 75
    0x402c0b40151001d4035000007131142080001e40e682c1404c6907030b9030700703000c114050044001122002c050103864024007415100b412482e281032511001c0300700411581c0060780c28401c0c044050f08070304690056640c03032003201003e6151414203590386510108000c1d440300300080c03541c8680c0011f40006000700a05003032040c8241e101c180a80940d2500071100302a1035005504200540254106030f040060140401c0d40041c2c0324101241990300030f8000341c5090300000203021420354458207440c80010341900440c106130860307600410a000082c0381450746a142c101003000c0c060140030f60801194882e0408000e20b90b02d10010208200c0b644608000c1010521200041c1489004070b0700482c60580d03c41c0d1801161203441c1c803c607089410b410038003800601d0600f12400c001d200e030240d10010300510944845c6407460b0429500c91003000402821305003641c41c200301a169040941001d03003401d01c040386e0f030854001240c4002805015804034803581c0f06000080780d1b04120400e0b43e03d2800d055400001c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 215636375 1250 215635125 215635141
    0x50301050601111b0d020d030f08010b0a0905091f090b03010f021e0a02031201060201050a0b010e01020a14010207080d0f0e0d050a031104081605030c190b07020406051005090405 78
    0x10091100743c0c1c4241c100302d0004070b8010401008001503840105030450800542d000716822400400302140803920400a0b401c5a58014020500515411007039601c0c2581c8008010100d4035a88a00c0d4003913075040340402c075051010004080c2145028000150307159850300c80d01e000e404140c0905029520742101c0b00d11500c1c13240225119200d92042d0711400c42c0c00e104400c003d035813000d44208114001071007602c8880c003544d080c1c80c1c02044a41d0000c1810b08100080c1070840d00d402541c9810310400074900c2c0c005036000310303602ca2107e03046622100d5900d209907032940a4410407000400380400004d0050050103640d00c4a43e614245c0c007010001c139100d02d5291555400710400c0800410000c0c070444414510075040842c000410280403030400703640309283c1c1d20b003001110400010048414003440182010003503050f00007421204440d03c42c00c2084c2009040c015030095a41404c03002482a0943d10303176400050041402800310840140300000080040d0803121110f4812030800c0e01081e651 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 215637625 1250 215636375 215636387
    0x140412110910081b030f0706020604030e0414070309050705030102070503270303040909051504080702011413090b04090b0106180801021207080a0e1608071e03030809010209090a06050301050601 85
    0xc2d800700001041c0c1040e03404030704224402040811340e0705118206500c00e040c030082c0010f000a140c00c0c0c0040c501400c02d407030003070304442d084503445010741d00c3d04400c0741c610306601240c00d0f08a0310b00c0c240010441c0705410020300300318440c0c0029402d0340c0001a061308003d400070041104200c100b100c00e1282c211340240a40c0c80c49600c01203945503006020901010340c0c20b6110200140c841c07800c442c3c20300c180d807400015180e4200c605490809000c51200e0a55070007043c8400080311810202d85480f61130688140e80420341e02984004070741d500c4d145211a120307030b400414419080310007400c0310360752000001c00310182209140c80340c0c2c50f40b8000040b0fa075014000d0780c80140451000503055074403080d0884a440000304044901c03502c0b60f1030304501c0c110601003000c1902c0d50a4142049500305941c191804070b45503c10110b690080d45600c200c01076200200060782d9041c541998191078107500076019000700b4004961243b020b4091101c0207245910150031070b070041e402071285a40e004015908 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 215638875 1250 215637625 215637629
    0x10b12090708070b03070302040302030d05430302030f030f10060201090201020304030816120509040b090c091020100b040b130c030e010216020a08060c0a140412110910 74
    0x2d168800c181c18800800c45001a592207145460010f04141e6240c000030f10307025001c0082c03808640300150800302c200d00800c840e4880e82548480c02104581040c264403c2d0b400041c2a440310342d075640c90710701010310070f00c100d900c1d04e003a1404060700d0b810203500b414100d0006036480c440d4002041c10004403540180603000100386c05802560500346103403561f900591200440240d01a045403400001403134024081c00d00b201e065680a84501c07201d81404200c0c2d0907400c1d100e204401041c100640d2194410450340011015a0502024100c0782e10640c2e040c00c00000c110040580c1455400219a0010f00d030800c04880110034800216801d00b0300c02200c41d80f40c50f4580004908145842e1018583c00c00103d441d52071038000713590201303036007506e0890300a02e400c0c40da03d049002ca02020341ca0500624409400d00d10042c0441c4d0405032291101c2380304103c0400c09000e40036129200e5022040241c40051600c5400140c20080c42c0c070b0300500c00f0400c0c16407280305100d10404500018401460001 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 215640125 1250 215638875 215638889
    0x5060301090b040c1401020d05040b0714030d1d030408070302040f09021e031006050123040b040605120903030c0d0e07050a030f120206070518240310140f101205010b120907 76
    0x4502b901f0500e241d2001d904c0154240c40c11110130120800d9010700300001c28400c00490350024001140b170b1710819129024810555031507200748020b12410301e0106000d030850345c0c111400540408003454240160112050107544100985070303020318000e82c2d501c11150710f0f4044007a100038500b50400d01741255000d014070f500060640071000c2d1014140d0900c01da6900da01e450613400c26a0b20080d48219a025401c5440081c1c0b011940758070340050400103540007604803000d14158034204c90940c065014451000e91403036111003440d16810018400c400142001070f15015900d0303100e0600303440000c0516001c442c81076580b00248886131000c02c030b0354060380303540c1d40319450003543c0b0415503a42000f440b140c1c0d9000e1483d030b6440321000203807050000144040b111098803460001d5540c6c2800d1360f15845020540000b00041140e40d40340805880140400c4442e404880c0e00381904490115a000c07154001c4c0d8a4400081380e202960006003000e4411044c403005266a50038203036403507451a214440d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 215641375 1250 215640125 215640127
    0x102030f04080a1404120c05040501030f020d1401060605070b090c030c22180c230d0317090714060c15070507050706080403200c0405060301090b040c1401020d05 71
    0x16000030861402081e511203e0f01e01000b20006004404845a2003a400910f40b2005840c1034005c001d29046402e00901084800b000349615588502d1b12480311000028400c00c041c1c41c0134801c001058207200c0d485e4000c00b0080000307580314400581240d0045009503a0003407a01c0004503c01030000325680820740142c00b80214000100a00400140410400300d42c0d030700d040c80c1a002c4c004079100c0c3ca000c12841c54000002c0340450709000f140c1101035040301c505012a249080001c2103c042c0d00c400504c800d0303e0008028130281000c40d01e000c0700b540e8072202000100c080c40124a00098801c0540f54100e1008100b812104100440384c0f1552111008a8115480303c4038902d9280100c19844400e500301a0320308035007035442d02e0a1242541000c5c01144516042c030090543c441401074005148920900c0c00c4046032110541c2d03811841c100038031a40c0c07034800190b07030ba850039001307401702c21340c040603003005810305142c194040d0b0540e010307164031803144481030101507200044440300002d443d1035903 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 215642625 1250 215641375 215641381
    0x3010e1005062407120212070f0c0503060f01030209010906030203190c0810050106140a2c130b1201050708040f0201050906072402040506090910090513030305090102030f 75
    0x3a030140a00600a5a10a2565984a8425125080e2540002a07410340ba642c0c480d000d03d420030850190180c82400c6600c04409440301c03c100004403019035800c039030180d6105a03c0d2138044013841c15034014503058002c490a00c5000140360f400c080c103a03407089840410583e00c559000c5c00725002c0303100c00381d8507501280e4422501c00e070541100c03510034080e0300040076903501d8000b01e03498010810214141c5950720307401004043d500c0045c800f508219081c0852401054080080800308000302b080024103080f200000c8100f41c23911401c000100261901004400c1980544000d10380c074400c840c000c242012845c0110441845039910510603912142000d454548070300c4500401141d08030f042c0707d010084882d080e81c40301f02402000303104403580f04c5100309802c2aa051b0000650180d10110300512040c003842ea03403281503c0d1402c80035170310581c99513244075124810a403a0350180000f02d1a28041c0004a81c4101724600d11034029102403005844100c0c00342d00b00e10040f0b0300c40d1a00e000d44804 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 215643875 1250 215642625 215642653
    0x1506010c1403070203010516081302131d070b040303030614090c0304050f030f030a150b03070e01030603080f070302061003050c120f0d09080d1d04020702220b01030b03010e 76
    0x1541030081400c040743c2c00d1001d03903800b103421504c0555007060800c940c0955038200a6004000991114004246287c0145954041298900c0c1d207510303030071141d07100e2545200001d0181c00100701c003100203003140c06c55552420405035039401804182e001034141300740840d5020610440032081034018005151580c0c0b640c0764032407250800741045440c0c0c02180703125481d02000300090710349441c04a201541d68141503041c0b031308803220004005542c2d01100401c016004107041902d41c000744600b08800c8170950f02c40101e004003002e810040c08544081400c03220b800c1c09402030b0009510980881341c0c40d44034941c1d8950809480e1200400c2c0354826807105400741043c030103e09a03c0c0c007000890b0450001a132103507040042c804400c60000d85400c3c8208164007081220f01c404102c68240000100c1d44060070b0071051901c20240d40c01b0316000190401151241303201f25103244501065111003503401d031030001c0036041040321940040e06144105c565450f0604c15130440b02d40b07220052040c01c80c0159 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 215645125 1250 215643875 215643893
    0x606030c0613090204061e080708061002010b0a030b0a0513081c022808150f040507210507080604180609080f0408150c030106170604020415030e1506010c 68
    0x1119010102c03441000103140002e038000f50015000c135440b00403901c0c01103a18812000003802d18002000140f00034090841d801441d80d0780c22490a4a0603010035540c200168050007504441c15004041c0c00400000d00100c12951800703640c0044041c001900ca00e00c1c4095544481314000e40b0b00c510400064200d00d100440c1e0200031511400302506001101c0800d9803038010311240d4030131245003e5950840140d020348c8c1240d012198505448801500341e01240c29070307804601e0070780a01e0b540d4000c6000c460003051250506c8001080c0d44840e1611804414041c0405560000100c1c0d15080400d0f41482d060280c10309142c40300b9000d04402d03040d51590000307020359036400d8440c10000c0014056001d4001c00030320150484200030071140f0703810341c20300c100080020514034075030009000510580d60310030050515500032144c040400d46400c00068024491075000c0c1c4510450740c407002902d00c1d0182c01c04040448504143e604500d0426441c1c503e0510484803140043c192aa5000014400c85 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 215646375 1250 215645125 215645137
    0x3204090308181e0c01030e1603081c0920010807050a0503060a030c080115090504050601050909010b0603010905161706011b200a0f1802030c09040606090f080606030c06 74
    0x80c04480351078412003c0b10141c802c1480e0300c6400c5410041034111039507014003a04103198003080c0141032502000200c1003210446000060080500103201c0b00c040e411094011f03070510003084100031124451904a1007101c6c11070000b0711121894071005919070080401d14815506500d0780b40c07500181040172034080e40300500183c1d02c401d6103000400403c50002d400c80c0901104400020012082c4048121a091a6010b0b40100d42030a042000040c80881d0460440c0c00c02d503003004080d1990307010903014044018805800080c0403000041100181e0400c0e40141e002078525208420341e40d0084071140306100a0064581d0f41d4004515594480e1044440c04601c442120380742002c01d1baa010340d41e0000c1c80c8615121900242c40c68454545040382e44020034180c100201058036120170880c40030f01e50482c40d94202d9010000950392900d01c2c1c21926400e400030020450241c0310440a031025249008101c9c2140c020000454550300c006005d07030040724018018841d0314201d03401c2101543c040 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 215647482 1107 215646375 215646421
    0x50105091b06070215041a0a0e01080907060819050c030708060616020d0317041202190f12020304150302030702011407120e03043204090308 62
    0x9000c1203076012a8181c1e0401100b12002c0d00d007505d0350149901441e0040c0b110004440d9403610b0300010301d02d40e585501c507482c10350f202500440b282e50b070032640404564030076007041c002c65010b00603155010000483c0a0740346140c139030055007610700a03105804480300c00700a02401039040925154005801d4420034244980014045443e0340030010107070003441c50011030301c1890320640c0c4401c4000c00b2214080d1050030325103812500701c0e24281d412001030180c2951000781c168020f0007210020703004001c0203d055960781716007516154284a0f60154403040000182d865503505483c9100d00b42610010b0b241c2c80d00900117400d4a00e09041c10091400d14810800002c0c0c000c0e104245443c03280e0400540544c403c0160b03451849160042c2002e1641c07280900310018110341540c000b02e6544098594600881041c0001d441008800130081848200003c910303201c0c182c1000310071808 = true := by decide +kernel

theorem cover : BRFrame.Cov 215467625 215647482 := by
  have h0 := BRFrame.cov_init 215467625
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215467625 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 215467625 ≤ n) (h2 : n < 215647482) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
