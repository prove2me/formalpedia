-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3681
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:22:19.664114+00:00
-- url     : https://prove2.me/submissions/2d4d6102-3111-4ab7-957d-081292988cf0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 661870503 ≤ n < 662050359 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 661871753 1250 661870503 661870507
    0x81f021308030f070c0b0304030c11012601150804030c11060f04030f050c0f060909130b0c19032d0605313c021810030606050414030a0503 61
    0x401e14800d0389a2011504645e0344481c0a004a1175950300c4051720310507036050f101c3c404070b00001d0320380c1550104a850b010703040003104c5402c0300b041d0496140d140ea220103610070682c010b5040c09044d0b100a440c51101d441080070300010840400d510079075039000c1c150040d000000d0b0b0b11100011032a14401c1c013004011401002900008100c0c0380001c40540034007031029690684060070402108480b00307954103034007a1051107500100e141140300250840611424041c480300181d0740c00c40001801c0b0380015003900c000c104140100404009a444c41006140070020203034101541c5016900f0b50b1110101b04114001d10b0102e5075490380450080c001c0105000034604280c07500303c0c140c0e015407201d09182c0f880e407120f1007840384190046081c4074802111030740c0ba11444103080510440c144480d04404000341c00c0101504c850b900c000c213540c0b2400070a03010804403040900c0724200b0180303542e4082500d00f0508200e4250701900b80c0b4107444010300718010102d07080700000e1901c84000e2020b0018000 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 661873003 1250 661871753 661871767
    0x408270607030914010207050f060a170a090318050102070317211e100b030910022205030d0e0112020f030a050601080c0c1902060c16050406081f02130803 68
    0x2c83c05082c216588400d1602101e59400e004a80b1100305109098100e582850880384c40c0c40e000010303000001c014602103652007500c5c881c0c0042c0d59000d41e8010ba4980d40c8032090400e243d0b0011200e000e00501214102d540c03850070000075a10712941c400604085004c0c05114803042208007111050710b0005c3e1001c8070303104007081c50b07036481e08142c1c0c20750220500c441031a00302c800400820b6225081c00910105441e28018080041e5072000b0141c82c3d182c003d80302040a5410f244c4068071030308040c500b925000d0944c1207261294889940c019500c01e40c814000d600d40540c0c484602032072444280382c11b45201c203034110060080c0c0120322034002c9600d070110410250b158241d000e02c0c0b0646007680d4070703081c40d00c4001e0354a4482c0304608819540b504244007000302021400c1085101034400750545103010402e81e900e90520742008041e054920740c0e00c00800582c50b0038001c03a405844414040e02c3c0740c250b44006404510401004000b605d80c01003105040003000d050b80d074009104100c15203903030b004 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 661874253 1250 661873003 661873007
    0xb0f010609060c020d110102120319050106140324120303060310271109041103010c050306030c010e21100f060f050d0f02061603080f040827060703 65
    0x1000d000310800112081030000d040c1d48900340383c5a10b950007400c881401103681d2034203a822841d100d8000d0551213080c2d0300c0300480174514001c510513198500342103208030300b04903d402691010780c01403081011042da40e5015800324000c4a0704810912a100c2a01e0b80e07541c048002c229515103e50345c00000d02025403a820404001507100d000200c041d2004200391b0707164002140da0307a600740000c0ca2038100c00817042520040d0003c18417802134141021030038411000a008140483d0100e0b0000380c20408040c140c1000d0080d12001d00d03079401e1060079480c000c2d0210355601e450074082c0707040041d002da4030f146580350b0030204085150b0100c80c0303003032080c540d5150566410700c020000787e800d840c00b00d04030380c0e002c420320925003691f255649050a0628000404c110801d840e0001d44621007a9400440180d540c0001410000c02000e8601030a01c9241400350046e00014109030f00c140c1c5500400c8009070b0010111103076039400000c04a00d4001a00303100010303030403490080780c0041002030302109141d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 661875503 1250 661874253 661874281
    0x5060a020d05130f080a030e100c0807030e06060607031101090f0b070230120103060b1c02060406140c011a09011e1a09090c1801050a140a03090b 64
    0x103000321014466600d070f045820b40507644221018003c2030281810800140450008005c001031070314003c00d940149101040c20103581c9141c9010542e03032189900d0b500340e0000d2400d03500800354201008800405640191180001000341e481900b0008000b010580100c90119034a4884002000940d001d03141841480c00d940300c1c15262444c001e8002401c40344000b803c18410005001d000c1100942c4032480345041d1100842c443d6095028032600055280c5040741a0086008070750108901406005000060140b00c0312110310250400220026032502400c41e13049a0141c80d2240d045610306044c00520300850340c0404917542810f4984865100480000b240e41000325071400e441d03662046040a02c14004860002c174411190080016000e500c018000c481c2d01c046501e031901d10aa00015482102140e040044000214281c414103120043c3d041454100782082e904d00701c00340784007034212810f1402079004c01000080031084140310f50410310036a640002d0341c0700d02e801c110041403041 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 661876753 1250 661875503 661875517
    0xc01120c0903060e1513110904080705061501080601140405060306040b030729280918271713050409062a050a050c21040603060602280f05060a02 64
    0x28458400100300044401e446041c03406e5401440100b01e0400002441501c0703038000c005460003041800004e020450070b110882c030545014800994003e1524005880c0b4140600b14078100085074111a102954000440c7c1c00c0d40d0702112003540700e548400001d00607011010460f40c02d070040c1340b00003c0c4001039001c040780c001d0060100e050140c484a03140c003014020b5a5500303444100101c5002c0662401c0c2045040b001c1c1c8614103141055104d007901c0300c24400c420b4a07210040d9030751019240700550140042c0b01443c91003c119141003103510703466860b28201220044031003001030800078220032045054001c041c060428091903220b070610714024a451000c100d41180220307203c01d0f44038503881d07544800309a00e4a440d03084c41c030b01c1c0b40700700e80075002128203841520131080081916000000703c2150000d41d05c4185603903a051503001030549036294050819588040714030315000304081d4500412900110f0303080c900e10740c2824007114050001d40046e002d80110824400600311580040c00d40d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 661878003 1250 661876753 661876783
    0xc060115031a091b040f05130203280b0a06120506220b1801150f030e21090a06110c09010509070305060d1416080c01120c0903060e 58
    0x190038418081d0103691903644586250602c119a8503201e10b010403d00d0b0b0420f0704a2201004500c1d10400d04000342d0064100031850000907408100c0d620300285c5103c00314051036010760650800c2d0016900ca030181b5501415000e4940741ba00c1201c041d141d05c012502d03040100350780c407507654413000585001070140a0213903180c24240000c01509014868004140481045140b1200d0001520006000c86805580c0c402e416a04100400c00494403250107880c0030340e00d8046100703c8820242c40f00c1184d030813100c249801d14030643c08204000c544105000141148040c400e61040600181d51140d01d01c0264003d4441c1d40100704154001781a0500702c541d0800c80d0140c280020030464841d13424447c03180d1018001000911152098010756004940035007500b8900d01c40741e480d410103452415039000707140d00034040d00840214840109006144480c0030305010302c0100002001c0911120108200b561162810b05042d0b01c900d07802c01c0110340000301005a050b56440080d05c400745c2e446440c0b0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 661879253 1250 661878003 661878029
    0x12030103150506030d1211091f030e060f06091801020a0801050114130308090303040e04030509030105060108010302010c2004090c2301050d051b180109061b11040e030c0601 76
    0x10244c1000105001180704d140c81e0100c801c403c6240c808003406200700c40004110007404214240c1c0c6900d22101e410407280340c0042c0a07003100220080844d0104070717241a840c0c2c41041070007007407212044d200f608458161004525030307481444c00c4861110381200440e09610001c4e0788a40150b1007021203040e500240c0e00c4a100c0c0a0540e40d40015005140000c01003c500041c1000020242c900034a2007000240650342859a030700c1141494481c01c94007500402e5000600780414035080c031680d0383c0840b007420b10881d0380d4110b4000a140c08030b4000010403060f55811800003200c2e100f42d80150800d0001d200b03108421080c074160458500c14400c0500d21841d4501d10480c4600020000400c4101a940e650421120b42c20100c094400500034206c030b82041042600007455900081c001000c16440004001c003007000014404190760f8000c008000412241c2c001d24107a1005540001c1d400030342e0800703994080800100104002400341045101c0014105815540401c0c568100d5100c20b420344 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 661880503 1250 661879253 661879261
    0x301080c090c25051c0801060314160f121a0a080312310f140708030f0a020f0f060708090303090705040f0f0f1d0c130e120301031505 59
    0x41c09401410450310002501c05030703c03840406101202958140220125403201d203100300705d1050390035501800d60001d80c80f00010b12029405004428035100d078829628010b281c002943c0c00c09138800c030708440c10000000181104648584081c00d580d0612050030820540c200e10503020000744544c0050107a95410360005d5440e4000c0180e4003e40c044132141d150340c4c1ea80c41303408070300f041000c0072201196014003400419120701100c24402a441103d0850509c05c0c1030402460310000007030304941c1071344030340014807400d00040295406220285003890b1140c0200b441030741050365044a00c0802d1042d0715080c480755000160090040d20340c2e4455104584030640b40d2030702e0f444203e41c084a80e41c00000104007a041030b5004001c80701c02081c00040001691040d00140c1c3d103440d0b0030030320703c1c0d403580f400e0408540c1e0401c0d24903011503484020b01e140a031450101e13001c0c444400b11000c140359550403944918006004814492500d69000d03075482d030712494138040981c03441ea0701c051b840b03207080009 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 661881753 1250 661880503 661880521
    0x6030b0f090103051b12070902071104091a0a0605091e1806060d111f0305070509010801121e150b09010513051017030405040f0506150d110301080c09 66
    0x20758140e9400c04003070181140800d0060b000030300104081e0f90400718194003c10105070610901001e81180c14000da0f40e9440b50808402c040035401c41684501e150000f40c600042c0400c40056a480300040c104010b030744d030510154004e152550209800c504070b5001c001380f070303146603080c4c28007400b40c1c000400e0a0744821500f4000c4a8450035905802c1d03015102041803840d00c0144107505611480e543c0b82c00c00340d6131021030940454501c40180050002403022982c64040c041d0540c008094540313030341026440c0e03000030700c8500d040c801d60003041e000c2c440e004203100b80721038640c2004805005560701d5881c5481c3c56a070690000281400e15803410000100c1850103101190403120010901c80c0c5018260b10350390000d010160a001c0d683c0d000060000f915080d625501d5010491312024503205d62078001400103441d94100f003000214684010084903540d2186c0c100c1d40c0e521544103e5031100c441c003144000400030214211502100031000040014001411a86201c4103442c611141d031180000c0c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 661883003 1250 661881753 661881769
    0xe03042309102303011b0206090607050a020a110f1005120a0603030503071209021201020403031e050a26010311040e010519090809060a111b030d050a030f050106030b0f 74
    0x11003200c0b620079825100d400003e40700d051103100c0014000910342d103900039500042d030075107468180580c100600b00000d0b0705052001c9075021a95041891a181454800170340b102c0f90f440004241202601c029909501c900350032548032400030f0221000d85c090404040d055420968800c1152001c7e9070001d030041341c05000750782c102d0741c0c0350f01d84500303607145c006040d240881d800c80d9040310344d992802c030380e800340e034030842441c0359030038910300040c1d5480c21410001d18a05921a03982c03420025031400c5485c0c41c2d07005040b42d100d1211807030540c070301480741c60b501c410103c0590480304003205620004000d00002405130070201c4811241001400d0f0000421030990b101111a113009414807401c122600c0441e401c48040184650700c2d892a080104d000074403036070440b0f80400c0000311201e000715400b40e0b0030040c00c5004548009119201103003d00080e40d141c02842d08002040380105003c1d104a0113500082d8845908039028403440d83c441c04000c3c020100440200e11840c0038000460b014142020 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 661884253 1250 661883003 661883009
    0xe100302070b0705160209190e060f1f080d0207240c0623040c03060b06190315030203010e100c050f0d090809030303010807030c06030219030e0304230910 68
    0x51107000b40d0f42c0038003c0e91160801c02d9034107244880741a1100040c0e54810900340710b07111100401c402c0300fa00f95000000c0b1514003444124580c0b21409208502d905075000541c0500b1281c6183d8030818128415050424103620004141c45101000a1060f8003c196501521910b150031002c003420349940d020000d040300b030340c4008920045c4640000c14001e402021184400c09020062400b00f9074059200d080d04031015503d204005000b4803c0103040d00965a0300f00d01101d019052240210403c0c0c2101001d80090042c542d44111070650442d82d00e010300000c40e0000c00801c5081d40c42c0303a2440d1039003540031602094900c1c120381d85410314003d070291003c3c40000000d107420f090710100400c0003000748180981d1800d00c05d002d0170356103503020001175001e029103a02400850f0310b586013602032900180c00c15010b1500620100800c0d9004080c20b0a488a5a01d8003040130321215244908502c5036810001c090200e22103002c070602070800030079a04d0001a500020340390307948140040b0380d8031240 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 661885503 1250 661884253 661884263
    0xb160c03030b011b0b041202010c020303070305061504120605072a020301091b0807060509010c0201081b030901140a02160b100b03040c03051b01080610090f060e10030207 75
    0x20005408244290302030710760b661040c14041e00301810a6000ba03001c1d030340c0d084100c480c480b02d641008100220350004000380306c05030001703200c10106044082d45130f00005150104056568001030f83c59544c0609510105954088190351030b51513540d6100f403041c0c440c00c02e9030f07910704140100b90140e10606207201c1c208402d1003420740901d0140d00d0010300190f10a002d0340c0c19074840400d0f00c00b045a09290204445145140c1c1e0349162030401c05504109403603004a040c000d050000000f9641c0ac0411030744000d0342460a1070702607448550186014402c0781c1901082d5a000c010000800e0056001038000041c684c00400326580c0d00440605034498000302c40c800e261410a0000041e41d40c3d61029088450081030280031a100c2c00c1452280d00102d8081e01c685800c0d00c010014004180051020302e20340c01601100c25014400203441088080c003803600400021114032401407040103440080d0514511107503030b030f0383d032510000c250815a4240c584151303140b14016000901038400c682072035501c4 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 661886753 1250 661885503 661885517
    0x10905091c051c14010902040f09060612050711060a02130e0115030e030c100605040f1803051e04090c020d091a181815040c091802190c0b16 62
    0x6142c040314951a070b1902c0b0204103460b40c180c09126a404d100c1c45001e45001c1e103005880d145030004a00480307280e0f42c8090402072501200340300a0354412220185800502008225500c1b90b5004072081c0c50942001038040c09500284840b1461540081c59605290911820066241c0781c0b012a20f01082c81240c049402400d5003829203802a00103070b5904800300c0c2628244040c18043c0e03400d11031504880308219581d010284130601c0c00703100e02c10418000b88002c10669800c0d628010b06106109405010300c81c01080303290b2120725890a00d8055070400a1194036581c1e51003100002e0111541c1840c0540079903000300006a00c58400301c0104d0f1403400e0004d180000001d000381c440d501c2440b45c280f641c0103542801040b600d98404030751f90a01078070310440251402405410707100c0c9150440c00d1044d42441d4603480d4456103c41e07008203461040c1003408180d1580e0704000b0080c407a54044110001c0c1c207080020714160800c3c4807010040c02010f205140355a1800e5031701b20040480c0300c400100320343d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 661888003 1250 661886753 661886767
    0xd020705130c0c0804060c0c0f06051c02160501090605070c03080a0c09050406080d0206010605090303120c1b0703050607030b09010b03060307032a14010503040b04110603010905091c05 81
    0x103039400008903100b407814000c0e058160b640b209141944290032020100f01000c101c807042088124401e40103000310780188100a0801c03600030120310500c1d84101140300a14056128000c5a030b0441b52082880810100c0400c22450507502a08682405030b52040c64500001c40803401001c1100d00c150b070541e0307240d8856444401d5100240a6221000f0410583c0f0301c001c1840d07115480b40a01034040b5500a0609419000e402442c00405030042401c2050900c00300026450000544006000012085045a803003840c0c020441c0500043c080302c000312440c5685d121507020480000366400b4209a4606a483c142c003642502c132001c2d0026000780c202e1004006407000c400285810041c01001d541100d944d13a180e5009000001404000c600c40840c19080204d22006c0f0444c01800c2010314107002038005000a06240402032025042e0f043c21f0000034104010b03042000e288140003029075440e940c5908200c402008110b80003003492103080c020840107244452141e030303d2081d540e611440c04107 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 661889253 1250 661888003 661888039
    0x30903360f082109061c090b0f340c0602070605070210050606041701090f0b0118060e01091e060f0509010b180f1306080609060721090807020616050d020705 69
    0x403003046500d80ea0f006d2884182411109405120502c40c050b1421068078242198940400d01c0301800300403030080d4041c0c0c2c0741c094501300021916241c4240010110300740100d5003d4440c8a002c000040101d440018010100009580054040c2c3c65980c21241e07040c1500340500200c404c00d468142c0d1141060100f0403111548581c3c0b070005d4032039a0000300c8d8844159031000496003450004803088401c0302c005101c1c1c901403c91906000d10300d814144040d600d80318202c106200b06001d03c90080e40c503030030081c181c0c0d0700203444e030001001508400c12525503100c40c280c0050301c10303000d0148074111450000503600c2400c42030b82d1401901402c000c0d04001840108406812003100300781c0c0094040030400da41c1c80c13062003468000d12000010b0304803071604007689414a64002c040d6130a005a280c841d0784003480c002c8190031084455000042c2108103401c182c40c4500603c40001c2d40880002100d071050030304940310a06084c400e03c101c4500d07286e0224140d0b10340c803403170042c0c0d50051100e07201212003036 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 661890503 1250 661889253 661889257
    0x7060504030f0821040209480d0203090105070504050618040e070b0403021206041e030c080a050d0b03010513030509040b03010903020604050c01030903360f08210906 73
    0x40c0f1a2041e1840c00031031400b0444818021074000701c00d000c81c0070800042d41080340c1c00a40c001d41c3c090f0510103644100101a15004143c8030300b003c100180760311100b803039004650119150403041e40e455115070340c4407041c0020b0f620480c3d421407113500700300201e20303141e00800641d0203403080205400c2c00c0481e036000d083c05103e20a8081d03680140c4410b2241e04d0b01c0418000c02c0003800004013180d596600318018000b100c40da950300411594880000c12010614843c04121000d885000c440f0f640307a4941400ca900000c3c110001c0d001800c0002e2174002980c00c180204030500f0344450600c020041d140c1014202e802c21100c1040c419500c1201c0e00c00a0312890040a140000400004442c020b410100e8211404940c04401583c0280e0600013489820070000b0740183c0c003441e0501510440e5a4010117a02184510204400c0120300000341c030318050340740e03500307164006204445180d6280d40c0c46001120328415401d2a0040c48401c0b45403400d0503001c00016a618865107103000300341d03000d00001d5 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 661891753 1250 661890503 661890533
    0x230306090d030605100c062a0302070c140a231c030f0c05030f090105280909021305061605010e06101a03070e0a0306020f030609330a0506070c030b07020706050403 72
    0x140d030511810050080c4013046401230300025903401078441007d8a041e8a0348805034016412512107400c41600c540d80f4086200180e50008042454520100003009206543e905445c0e6100c803c034410f400540e2020a0b41904d9140a0ba80f01d801000310440d003603c98071403509010340960010044c840d070750040d41c4028103101c4410b25045240c500c0c042d420319100440b601050b2003071000b1820009105600a034130201404a91804500c0c010001d20004800a21440f40a00950010601030070702c4011a4804801c04d41007030080c4000a64241c025860788421035440044103004080441c4009114141c158544200c060301d5141d134581e10740c1034607036020f001c07845940900c981c80c000c0005003860000d0300104101803000d84e182d040840411110350402030598a40c1172035540d8075070020028010b26035003105075030401c80e01202e43c2d0001c9031081140340c201c035400803170004e42d61003000011003c040c12032b80a00a04822615881000c0340c0301c011902c51500001d005000500c046000d0031b4420840d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 661893003 1250 661891753 661891781
    0x207031b110f0a0504060906080c06160b1306090312051518060406150e0a170a0f020307050a08061509040b04080d060e15030d020115230306090d030605100c06 70
    0x10f0300e41d490002070300717440d12900300f0070080c0e440703000401c08203004200c007042714802194054284060381c19025449107a8403409481400c0040108082c0314040040d40105600001c040c0070b10382803800d0103007540220444503803400c0c2c90180000d00b400e9004160310428440108010001c45541101074441040070300300c282d1040d80c805000031030028500c4031192204098075080303c0f006207401081400070156000d2408a942c10300c0c4081c150001003106070246a0081401c0a207000e030740042450800707030303400c44c613000450280046440c10b070003d00c0ca0701c158421076400001480c20750a0041255081d90028001d541d40000b00c3c1c0020016000340800855038074001030800c3e0396003021216908251030002c101561030070b1040003402c0030b2160f00b001c141580003c0c00540d050181e41134031490244150313444000e0a00c188041440c800c4011850300b400241243c056003441060640c4507440f145685010a01e413010000d810706084142194812098850004903143c6417108000b0300003004500c00 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 661894253 1250 661893003 661893019
    0x302030a0b0307080708071a03010b0307030b030d030906050115020307080a0c061508060f010b0a05090301110d050f09061303030203071106090f01140c0a050c07090e010207031b110f 80
    0x1d5140c508004143c000c104102c000e0a481d807904030002c1c1404004e402c141e451620035559080f54202c4181240e04440107100b040380d59076180c210803030003011400e41169240c00f90042d8050000c0d4107401c5110030f1030140e20304000720b03665903202e41090420250b5101c0507030010721080000c06c1c00c51001c0c1120f1a054106000fa0889a41d92a821160340d2070000c0e03400000300b5000d025414042214a1b0302583d43c1403180401e5040146c018103074080c030203c581c1000000030701000c0e07545081d0462a158805000d40396196030400041d200940310894031251500140000503100e10700014003103000d007481c3c42c0842003071109034400300d000c0e5000404403010b0101207a00c1c0c3c15510b10410125206901800280c44903681c0c42c0c800c136003900c614211010442441505000c41010010215040c941040c04d1607546e40c00d05038200c5040c4012980503400303040c41e00d981c4a2000b0819001080d0b050b2203591740340b480246500c1d00c0342c0e440c4070000001c1e00b0403522602c05256803d04c4010801080c2c00140712070 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 661895503 1250 661894253 661894271
    0x112107110703081b0a03020c090c040b04080a060c0914090c070b090a0507090c1704031404030807020108010b12150f13060305120405091902090d0303020a08010b03060a060302030a 79
    0x3072078800c0981c0115507075100013580407a0380c005280c0c404640340d800000b602d0700c68010307280250b95600c0b8485843c42031943d02d010034050341d40c0200b04c4008140788100785448a035100c40b200d4a030551540240c8445040c010742034542842035440c4403e907842c040d01002442d56070414040d001c03e005000c2c03803101c1d00803c40c0794040f0312032034406441a02c02c2c600a02c0c2c002d000d89440c0d0305140f01a4000452035003090052196290801c42c54400c1c1008980201b0103030342d85040849840c0107080340c00e004010009808814411142e005040690027030303c68448699a591612003144210043d8001c04403000f00070a05007040b887c1c48110051004007001860141400050f95100160510200c0256924010420403409010301070080d900004510308261800d808175890403c014084c0101c0703d00301c010303090291210ba05171809844041c00e100f084501038900540294020b0103500007080d40707400005034543ca134900301d900c659005044d0b00c28051030450158081d42001e048008881d8540c5060 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 661896753 1250 661895503 661895537
    0xf031b0804142d0c04111c061a0c0a0b010605071a010b040302040e0703060f14060609030d2d0f021009081b0c0d0804180b1c020f030a0b010504112107 66
    0x4440b100c03d41006c0650700c580400704195840008400070020a0811000b0412090000180050381c0d211080080d0744000c081e03169803c01055a0b002003072a041040086100303030307120002e059407910803c0350a082c1c0700018016140380c04244a910b860181c00c21041c001400e19811114116109900321090b5684079510001540e034001c642050132540c41c3d0700944110f00400c2c50503003040c000c0d82c14034606007000c404280c444006030080d205100d642080d5800d03501d80507064810310b0817450101c031544603d2610060405000c1d6501a0041c410080f80842c0c4030494800c000b6590740c4101c02c1490020600c04144000300da1601e1403455020300303402c0400c1601c444519580d07284c4a1126075030ba450138610044102d00c0c43e2100903036800d00e0030150718402c1d00e5a031b8412840b00b80c21101300004a803584005982d01e14040082030301800380010701c0c2d08004800308a80e069400c116401e00c801c0c1004050030400e8010005040000390f8080d01c42021030040c403c0c140d4204150f881e100f02c3d01ea0380c007070340 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 661898003 1250 661896753 661896761
    0x705010f05060406060e0d0b090a0b0109020904240e070306050324010605070c090203180d120b01020d050415050f0703080103061a030606010f031b0804142d0c04 71
    0x21080c103140c4980810055141611541d030142c899420322900600c0ca1034041400010004401400c24943c07030049070102a081091905043d03200550b00500d40e1186521006908103900c020b000f80c2c20940c440000c0c440c0d0b0f581c2501440d03103020268007214a4106100c090840c050000d00c1819959003001c5030548082c86484000e000780a5560a1180503803000d03030200c1c83c160f0100c01045418002140020030811000040b101e0003840513803a6205c4050f04c00c42003040002c180028812aaa26201150040580d00b03404004120800440f000c1d0300043e61909008030307a00c800190200400c0c40888026aa401f1855200d40f500301e003071409200c00d0075850f40c410380342034000c1064000108200010380c01041c058800c0e101c41a001c01c622600842e58542c409010581072010103525644004c0c800d80c4464040c0360604104414141981c00103403060909842c2543c00025031003441d0442130000071607221407603144000c808207034010002c10b0304111380c40c0c1820405000d00c0b81855081d030307500c2c01 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 661899253 1250 661898003 661898021
    0x2215030803012309070c06060504060914010b0306060f0310030b070207140102030a1b0609020915010e030c01020d08041103030d0b0108060d0519242c07030f0503070501 74
    0x42080e5507541010f031400740d1602030100c0f15041c44820344002c3c80c40d80311001c0140c3c105540c0d09119540302e54a103416009440146c01c0282c02c50b14001d8000346080c0c60f82c00c0b4007500d020f040c58011080c0d1301c038030b0011a107110440d07509130050800c1099003140e00c184001503900500d1030074841003503070b280c4d500c030708811009079010001680a45028044031200790f6140031504000d00045162000505003c0d0040b4201d01d00140d115110340817171802d01c4032540101d41d845a0007450380040f494180b0010080803008850240082c5000c480d214041c140041d14180a02d4145c0040045032004003085400c8a0000e03c100d6400d01d945c00016041e44080000d40145100c214010a40b1490040010301c0b0900060503a0700c1840c8a80c10003001c50b00c00b0403101c4040c3e110814812850f801c42c1071000744c44144c22500e0b002c0c035070a8201121500003c3c3d0150038600080001c0c0c48020424034502e0311003440b2410000a690080031080000407003d800c803030105480380c02542d041000d11b403102800c40f19154 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 661900503 1250 661899253 661899263
    0x2030405030310080105011202220c110f06130b100305060a060e0c0a0c0303050615040806040c0f0e011412060f040c05220b04141f0b09221503 63
    0x10052183da50703404546003015107810002002190314246001c40401500c1c40080e01410b00c1c4403041150314025120391109080400041c040725051100090003007160b840722100c140101c14001d143d00b00003081c4203001e44491215000c0b80c20240e10b0f040003168019009c81141d425060f400000030b00c040c440e41d031107201d13400c50004421f85041c140703070500741000706994400f00e000c002c0141480c0d08440e0500195400d460001025075455001c10f488c00010200c1e01e0340c0041c0814002a00a000242c00707108da4458910101010340e00d40d0b2040e1804454021810035181344801031142c410f00400350407040e034004080400d040321100c07060b42410800e403090032017601c8903010401880600c1c50a4030003402e0039035038500c2001e024140f102c0c40040c4903036008117050f210a0944865030b180e4000c1c080204004241120720704145054942c51410701103254800521090300060181d00441a5900c400011f4034405480a09540280d1200e00c82041800e906540d03000d40301154401d41c00d510040c51082d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 661901753 1250 661900503 661900507
    0xa020a0b0c070c09062301090503100e010e030403150f1517060f06060a030908070b0108070801112107030e01050a0b0114190c060e010f020306011b0201091214010203040503 76
    0x281800840c6090f107800154165041400030804640c1c0c1d0160482482d43c0c01041c0d00d101c03001480120b508100b55400345a1520800505900407581548884d0030100500003c00c02d410910041c16260f000b580300c05031182c0d0641c0404c1d12042500c0d08100c80540950000141c80d1500400343c265480071501b0501031940358a5070349410350320130854990010004850300b41d55250850009000784180040c000405403503024072000c10001c0b0050f5980542e021716918500d40e1034822240d0b445a45120390440c1d9030070103c48006000d00a07045403490504120110307117411a40307802140c5a100941400d00b015560090018205000e2059134000e01c114080480e400c422003000401120340203d1082c0e40e0702c0104071110440c50007242c148034008043c24400f82c02a46030524400904403803403144295403d09510f051484d1180d40190320503e0700b42c0340d41c0000716000b064006c01c1101900000c2c04540380c00d900b8002104000e02c02c000300384c411904001c100320100c12090990304241e0b0129426800 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 661903003 1250 661901753 661901767
    0x150f100f170d2102090406030203100212180304030305090d020d120e01140702040504020d05010218011b030e13021303150617030307030c030b0301150e071b0204020a020a0b0c 77
    0x401e000c095000b004515246420400f055085200070000303002c540803440e400a15841a900c0d0354011200454000f0251420105201680000f81d400014882504080800050107080f200c40179040c01c03525007001541004d0860394182c5080d48880485940b0040498003200169a0061740c1c200c1c4a100780300400b00428080409014003282e91040383c14004440b807154500c040001c20b40f1921034045402107000d0310b0704c1c00840c010b40035052007d84994000600d0480d05050b0f8410384481800a98a544403681a0324803417102100e90355000780061010072130a00d02e4585034111144c10040b1540042c60850491300c69214039140354812902d0b02600203070000e50a61600c030341c0340203004c1c20700c00c1d03012041c04403030f50ba842c2d21009110b030080c19600c0c0f07200e0000381d100350b00007100650050001c10003601800c0030011050140d00c14480c3c0342c042d40c0d0004085600c20403200000c0303200b038408503800480315820031019410480d510b00462040da60100c2c0071034518441701d40110030220095540d485 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 661904253 1250 661903003 661903049
    0x18060c01060806090c0d0b0403170a020406020c09040b15030304080a0b1008010e03070807031209080702090606130608040f0c0609061409181b03010b090a0503150f100f 74
    0x880140302c4c48403908075143c3c1d5907590712a040324095160380494030080568403490144c440c0e4004021490540701d14000f08500b52185500400c269031007070f001c0b20b00c11900d2604004440a04840050800f510200480d0100d0031104108039880703c001c05681c101034032024010710307003040c44405903003e018410034402c0f08444020204090b00341c2000a0116144003640e0542e00d200e2107030010070080001a000d418140701c3c0c400340b100208141402d0095444030308210382146c0085405034802c0d04101d01182880c81d10200301c0d02003028904e08c5e84c1b441c030300d800010366881c84020800c1c2e03240f210002034100020100308585019060176100c0000c2d65082c00c000804c0489002101d07007490004000c0e52005070f8500c90320310f80c440108a9429a07076984d002c1d5011000e061030640034911034000c000803a52501c181c024200044081e14415100c958941c10141c0d541481c4a1003a505907a00c1d000c11740c40c800c80f03d01d095001400d2409005901e075030322040004104164440404181c83d60343c4150b07141 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 661905503 1250 661904253 661904263
    0x6040b090618040e070317040828150e0105060a05030607210504060504170301030c170c090703021806040b04260a0c05011409010e1002010609090b060a05030f0c0618060c010608 78
    0x148a00380f0290512741880046a51441294121030403261800c18040b40b41c0c1c0030700704250603c0d52068241c2c7c0003048100e6a500030b400c0c14036a05050f54208400a02d95041c0382e10034408840d0024020043d41d165580c0559844c035218980f02c4814440c3c105091148146018090045110701c0d800a91b6242c2802d002100000da404800b503046000c000400204480c09860002da03014200e035208040030440d4040e1a02600031006e40e0040c3c0e9180401c080da64050380a88101c2d4089210703500e502203c0c004004117486075008000d070340c03c0d003444103002c0000d0b10003120441265420580c089141070b0304a96141442c200011211070390729a405000a5034000841c4c4050311014503401d081c21029000600300f03180f404001801410a0800c1060551003508100700602c042d140030008d0406074103001501c500d080328a02d010b801c2090000541d41000127022404404c5200a084001c03012800c0112541c089038000b800800003100420055440d10010000fa0307107183c000084940c0381c078004500b08 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 661906753 1250 661905503 661905533
    0x30803090304290301030b1e040302070e0a0603080706110714013810090b0a08040c0b1e03040c090507050304050c09070e010c06060e0c07060b06040b090618040e0703 73
    0x201c001080450f102800f0035094030f041d240d1010319000d0703903501d60300510b040040d050800012060305a09000a141c0c0218a500545c0d155030407055180c0c1d00c015002d4207a4015120041c80c0d1142003020b600402c20540c081d408501e03c404034189031407400d842e072000c8514903d4264460b80d5466440031000c400e850005516800040383c6c490504910a600c01690581445014001c0800d10707501303404280f0401c5050090700340c50304025215104254010402c410840d000c81d001602030750081451020681a6148190514240030501007003000b80c80c0d05810240044a01e80d281c0f004c080391000722401010300c10142c6664542d1245000d04140e480d04040101c0c6c03501441c03d20741840304065001001003072a410030b0800750780c0c41c0014a000c3c0020001540800000e00b105003d003c1804e03c00001440c1d2940291001d01008070f1640821101e0710592084105a00d000c02581d6210700313101e07028001a1020441c81ca41c5058003038081016568980348103036803500004002e008000860b003540d405 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 661908003 1250 661906753 661906799
    0x8060d061a0a0605270d0f0212060106090e060604140d05030f3610030b0d020a0b1e0a02032505070e0a0c02030414010c3f020c01090501080907030803090304 69
    0x4815014801b04500044409018042003801c04010080d5140c0e075602e4a500c1d14a0021696150303511440140030303c56a00400d000a07900c0f0012403460715201042e5815107c00100040070f1800705010001d1280d0710b0002203545000034088400404038081c00740c5040b8124103942042d2000388001d030f01802c032205104800250365090469101d407240310303003910300e0316050800140000701040010b4089102072402035110fa0080c1000c02d1031a4a04007401d01c0c070300d42640c1c140c42d5101c0100d503180301d409081240b03001a8801d1064030842100440c0c04400720708039021100304000743d602c03030a080c0f14450300328482c0d00403800c044c41201c10441c4101010103515201441c2480d0070319082c1e040e50592652544d04004400c0c4080f4140400303140c1080f84100001409400e1410f400b54080100d0158040c2403009c2203102d4044114600211380e0241802051f03580360721085c14000150b070001400740c43c000c424800c03601d002c40000e042000a6004281980040d603c461408020050188511a121070 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 661909253 1250 661908003 661908067
    0x60e0405091b040b010e030f0d1106160f031b03051501031107060b0a08060f071206031a1b0f040e07091809080f2808060d061a0a0605 59
    0x4215404070200d140202c004681c0854070500260040b11010300d962090355140c0644211141012800104504c2208940e12850b081d68a242091a200c0b90200c1c0c0039942129880320903001d85101302c0106040451718100011114500e40c80c041c0329400c03441c04e07007000ca90707550244207441e400e103c0e094241321800d00c2c05100d040000c00e071340c484600440000074045078681d2610380541e84d400700711401500d0500121141d501c0c08601004030400b05442e00c201240c0c485c00d8444000042e4080c80701580c1e0003c00104030300310070b401207166400f402031040854a0800401503800040c0500600c04e6460300e5400a8403203050911840d07a81c003001e00b00a05121030f40342c0c10440741d840c910b4082e00101001d2800161910b4034108046284600c01005084903c002884602182004110b0707a03002c1c1241d041004032074103440700750380042041e1040d692000c0908a2203001800d680c0115501d8201040a00c00702410341c0082030101c0d030a600050007180c00800c00c0c144141c20144213800c2844c007124941 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 661910503 1250 661909253 661909273
    0x105060c03180409080a05071a0c0f03041b080709060b09030a1403070501060b0c0616050f210708191a10210203090114040c1502100501060e040509 65
    0x36076039100364003481e42e201000001d401050350b10383d80034407689900310480d5035848a19810082541d40110011a000441c19800781070200090384440d102d1015054400d00c3c4c104100f030440c48540008104030b8580d410b8005e1316460f200c000003101d00a1942d00c0041010b41e00f4050f6420a032003854110b915850014803600c002d6075000903000c071203940c0005000c01c00d044801c45580c01c0d4841c0c014050003641c00c0039070010310843d8000091200d100700c03205540b610b032903000041502080004a84000401c10300c800744540400400070b110604814650054078200b018440001d11411900500400e180c3c00401c208101038801d005070700d403450041001000103004a40f00c0c07a503400c480d180c0c0504c0c11150141002405241c120b554000820428080190354400f031074003a50044440d55804d50900b80400c65000c2010aa0360180fa4000d001c0031405080080040c001d942a5040e0002c43c82450342c41113201354240329490103000d06950341c0e01c1811a020501064cc0d50180681e000e9600000ba20 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 661911753 1250 661910503 661910527
    0x402070f020d02030312160e030d350405100c02060f0a020319091203150303080c0a0e10050a030513120e010e13060510050903030301060e060f07050c09010506 70
    0x14039080307034101c50058407001540040392840c042d0604180082d9603240c10b2000c0003e44070b041084c03112166484a04800d460002d142e00d880414030044045504443c0c80e96102c502e200b82484d50007141c0d40741c4001e0321440c1c4030380700107e00b0550341516150400c1b1060003900d4640e0191a605104600050840303003040c0803081101704000708240d0b5507a0b404004581402c400c01c80d003910540e2040030a2028003520b09100740440303901a03544011078981a075511003000041d281904690b01500e9902081d5180b143c610641c0c3d001c0d109600c1080344030440d511444e52800c0050041118071740d2003903141e000044001d0101e40e0b02070090040d09411a40340b2000618130400c0c501c00740210f2400c9514241284016541042340125180d0310941000e40e0800802940c1c1c8800101d40017119907070b032580040710058445106180c80f090709a0000c1006003c110b024544148900001402e4280740c50320144060686800c8070408440c260000c2c003030f100c101e00c0c210000c01e0260808894080c07078100d440401d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 661913003 1250 661911753 661911773
    0x20f070c0b04050907050c030426010e0606010c0303020c010e1204030c0b16120201270308150105190207051503010e090f060109090302030909040305120108070b04060318021809010b040207 83
    0x20003000c1000001d00d61f84200c4d81403050740c1c024001c801c0320389040d003240900e03844501c03444d1481c0c0718198680104c0e0030b0402c0c030002c1c05902440d0180c549402107009902d04074003a510001d0041050b64a50301e941c560588108458040d8811040800c1d88490031490914040041580580c070307540ca080c05148504000203000302c0640da8818860321840079034a10682c054550007410b448000c0621034094a985081c110141c1983d10940d00d00d00661b84941d07000300c11003030a030000c90010b40c041c00300d040b6907001c4200120041d02c0d40e004468050b991500000d010b1601801d020200c10b0011004001200010344031a40004840d03000d45210f2001400e0079a41e9401449940311403501c9007403040506009100305d40d00c05a0151101c3d2242c40d0504014007180d225040003480400201c0c000581c810002c00c03583c050310003007041940750501d4164201d01500f84440d003c051031008803482c4006954038246107080503020b880c406018544030a1031421140441700f1140564010044080002c3d02505 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 661914253 1250 661913003 661913011
    0x110706030e0a15020a02010605010309050706080702252c04020603060f04180c060906020304030b06120a03030509120c0c061806040e060f04060b0d0c12020f070c0b040509 75
    0xd00064804039604026150641008000d032801494185205000c00c09070010040d94249400906c50a603032400110103c40c0b451070090b01c0b503003040005218862103000b089410140610407503104030b11250000d040c141503038103021409101003c00300503100001c03c4406a1954503c0c0c900c11501c00d805031641c000200800c000d101d05e00c0040010110f641e49142030308031100c080c0040014445584009600a2510b80f00b07641d42944180005242f0384505500d00660301a039010b1428145940d0303842092201c09041c0560100340300c103014041c02070401c6400f13020f50003913502142900300300080608250140e01c5100a295040002d10f480203c0080c20003425070007602c8060351541d18007045a510788414444503400440010001a000c1c03000c021940245c004403070340075240c42c140040004850b124450f010310b001c4144208032905026510a403140101d40c100705c598580380b00200d00407684030114072000d800000c280031003880300c8000c44d240038040c40e15a041c0350605120001c1c59601e0014 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 661915503 1250 661914253 661914257
    0x10b074e1209020411070b06130e0307060f0b0904080a080907050616051603141b0109140102150106090e01090b0a050603100b340b01060e180a020316110706 69
    0x710040b41151201da220038a540b005204840e00d8100381c0c60306003800c7c031094800038894408240c03151046222440340a5111070000300451a1404c00c1c1d43d64805000c9441c66813004a5503030900340352039110720030218400e51040c0d1803c1e649030039058000d03080c00d8001d8031000b030541c8599010301041d21120212000303584c4507408103140b40f0386450098034040d8210101c80e035900c40403000000300141400c2000c124001c00040e2a402d010003030400307105c84480100c40340041c8030368004105104085d545c00c05089018419112211900005004c00400a90226000440b4900100f1181d41401900c1f401750038184018000b03610b9800000d15182503030f01480f032003800c1c0080411006e61040c00c1c0c1200030400080e0302d0791900c52030300d100101c2c030010400380e070b05044000404003007a0f80d0800c114038010760310200d00300340782c0d0801c1022031f04c0740015030902d038000320700203603041c1508038030045984607000b146030141c0d592030001c80007501c90320250144000d01c680f0180d40e18440c0070200e0f465058410038 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 661916753 1250 661915503 661915511
    0x30a0c1404120c05040e0d021005040c150201140411010314010b1b03131509060e090703020a0201020906220f0303080f04022205071103090306010b074e12 68
    0x40e003007103c90301c28290f1140f81d100d482d1880100c802e05000ca902e010104160b000e030781c5120180541c01c42070324403c55008240400f0750005200c1c0c00060500800c0b00703e40c610000850866074030012701c2d500800d45042d41c551002c0a094034246d03a08d40903c4052015a40000c050b55141880443c403501405007004600c254080c40c00340d500f201007050340c0f81e4000c80a08809416a101980c0030104001450600003800d84440441c141d4000c0803c01c0c0e8990000d040400c0ca0396940d0001ca000390480a01f020455408010041c101ea503460090032440e811001a1044080d41e040c030084000c82c1540712206601c1c0390b420400c04290032441d42a44003415a08003035156899100140580c1d803c590501401000504c500e40b1140e81c44d0300181c4100e90345e48455900c0042540919524011038403580c1e41580008018010032100c3e001404410748904a01c210010070351184400650781070388108110700d44450300076a07045100c21009000e0016603820b00c46134082080007040c00c00301c03041900405403a = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 661918003 1250 661916753 661916789
    0x1210314212d37050405010b010c15090228090c170412051e03101e03080f0d0504051b09071b0f15060807080705090f0a0f09030302030a0c1404 63
    0x2d03007503c0001c003800b6040381000820a912a000103001c1503e06507174945c6040c103121007550103041501681900442e40e215500c89441d0400c020300044101281c00c41c1c50b19151411208041111290b240b0038480100702a50802c1c2c071000413604003824403420002c2440340c807005e6640707400b20a60400c0e00840c0b05c550320b8000c50015503141c85441c40d840040c0000c10a004000c150030000740d8003075101800b0f1803100603590b2001c81800b01c24140100c087d00e589510402c001610180105020480400d6142c200750400c0641e408542e012901a00e450b0030440422040401c6ca10700580c0d1380d2303c02c4030400083d0030038010043c45806401150f8528000190080f8240645440042005540848800c403a0441c0700e806a01a01a80c410003415106484000c40d14900110b61001a1b45010f050880700395140f250146030b09034050f0601c54225074900c8402c001c4845030245c442214000e4070090381d641442e05905046034648182001040b1149c2050070300b440030081124111140110217542c7c01031 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 661919253 1250 661918003 661918051
    0xf0f090106030f060b0f011719091a0609010e0c04051201020d0c030b030708030c0309060f0f0406090303170601020705010f020c190e01210314212d 65
    0x3080c2d000039003c0030301d01001c01c1c104401070300002d10784841552404241010040152042d1501a40c100b10421210000070300011080c20705e4140705058140c0401c1d419280d03116004078881c61650304901168000030410541440304c3c0032801021080d24040084c41c2c9418051301d14051030080314820404210f161030041000d40569203142a40341081104d50369500303010b0028640c400406000b801604c0c40000e4601c80402540c1400d84c0d684051440c0001540c00c000e29036110b0410031046640a00c61804005000800340003e0400c6443d641d40741e50030b40c00d01925039100401001d28034001c07a41044842d982c0404d00c641110800c0c00c0116520030900300907410440c81c1c550454200c101000b151004e00940d00386001103c0465184007900c0e602c4091080c1100310042c11500c059082207a840d00091003a103aa03002420ba02807120b05220303011f941807001c04000c20f013001780302c410441807080340e11a64020022401c0003804680340c40300012002c01807900001c042042089a002c1940b440d12 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 661920503 1250 661919253 661919261
    0x15030126120a0c1a0f150904020f061605100f0c0e040c03020d09080d1a010c080304030210060b1b0319180801060602030c0c0319062013030302150f0f0901 68
    0x81e90150000003000c202113154280c1c100200d4881141e0101080401d41c071950000707100000420103090807400d555240c00384803124105c12403da410110030486041404030b00c40652110501c00c1018210f80e0100c01402c3c8261804c0c1c50410300d01d90f140075a001901c035000803040e0135102c01620041030a0b0701070135064000340500c0c0458010380b404c7c00c40d03204c100941d0380c00070641c00d03124403c1008110040301c01071080b4405541010b0106071002401e2020400d8103001d0356100d0310074411070304c0b003c0d06407040800b924555807055000c00310115a919440754201c03110801d03403c100000b1400c100e83c800800e10101c041804c00410310100c2850700750141d0f81c0000309070180c42820b00030b10202e5603901c0005d40e2a40f040007408080d0240d8642e10003503160200310426401c100700080b40122450342c03070301c0b0018002c42c4002c90042103a44040c40310180c034000a018000381c2150b40900d8545141000303070a0170450580c3c0c1b0220f8048508114260074412030303454000c444480592170355070710401024010 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 661921753 1250 661920503 661920527
    0x30506030c040f230f040b090f07270e030414040b0604030b0712020403030903021c06050408220e04030c03050403051912050a0206180c15030126120a 66
    0x20341030141c041c40800c100d030000c512403d4660b60130381c45110340c0030300080007081c140c4440030b440c400c09000c9070100381103000c0e490b0044c0c404c0c001e4620300c00108407440d1030810a944008070041204084c6031102c9520400c4459042c503650040c0f003144421904140c581c0320701d020f040c003030581030b00220129440d158000010074200dd009560380d9070b164200400d5003801107400744009503000480c003100852500988040340d50640785c04c4034890442d070030000994403401200491003401c040000c04650b040c003400b8000c9000740c00c1c0c0b56454039442041c102e4540c0c0004980382e020030700d510070400145007546084d40190545410003d0380601d01d02280c1912540d84007810610503400c003000800c0c9508011000984620300c4280010350082095500d8010032100318096003200c2d000510084a07601d50707a015640020a60f070b1003031a5040003500c401550259022403040200040c0000c1428190b199001069140e983c6141415000fa0075a03418940c010200040310104040048a001e10035003089 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 661923003 1250 661921753 661921759
    0x906170d1b051005060a05030a12030902010509061602010809030a020a15021210061b0b13110303160210020a150f06050d050a03030b010905242a010e060105010807030506030c 77
    0x103c070700c0d40803108041c0405a90031032207603c0d0038000040790715000403200d00300c40d4099204040e84410300d0054000341500c22041c4d040c040c0800c07604d4400c1c0c0d03481c0010301030300340500300741e4045e04060f0000500c1200020440c0740503904c2082411403054001501c00901a800b0b005400c0400c412003800c00a401281c910501320340184090069102501c1c04102c01e0380d62669501c103e032408896120542440c4840141c42021030318042030104010320461141140211f0340c1383c541d0460032010a2865001c01c4003410145e0110341481c08516005060550341e80d200e2004180e0303183c654540d240c03070341500031030411030a41d5910308041100c0c03075810580040c40000e05100782e003522030034650340b00c0000b29000c0700002d03c0d040940c1c03c9580101c0342d10040d114098024284501d40440c0003626205030311669143c00410f01c80781009843c2e108c004000015110214005071003403074801ca00b0350390140c0c586500354104000510040c0d034080d0320035611412a18011817952100320110f030a0050031000c1c290 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 661924253 1250 661923003 661923013
    0x71401020c0f0718150509060111030a03020d05010e040305030c0711030703080c0f0d09060c0c05100c0b1305030304020402070f14071806080d030b280906170d1b05 72
    0x10a112003ca0300404440700c0d008a6541c00d6114456002280d20440010701486071142c400c0c44141444509168040c04c1810b15040c010f90501f201861500802d24620000e9000180c2d9100c00c4200d0166500519820050301d80300c1c18242d0340a4014040144010080781c40030491405000e07540d0f020704240c80002e01959066a00c904002c00c3c550f206403040906da11a05ca008074410304006910305d101e00d45980d4511409040900454008070f0b480c4042c0d81d1460402c00c003042c030b031f90f03515100c400300310039502d82d6100503041d0701c0e04400c5008018045c901e0101e000300c00c14007154001c000c03250720990443c0c00507640c000b2441e00508010380c840003c0c10a02607000c040c10091302c00600c00341a10100001d001c0b2a0903559107030b505075940350040515a800c03006800000900075046000c0e5a82c0c01840d130700d0209480903111000810031200319001480d0507070100302c4a400f92165802a1016007070004225030701040b072641e2032011030f91410400c0704164500a80e03603205107206018031707070140641d0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 661925503 1250 661924253 661924273
    0x606071b0e01092406080a060803180f091302010302480c060403060e070e0703020403200906100201110c01090b070912080d110f0316090b071401020c 66
    0xc05448824098400c00500d8103c0c4c1c21283ea0300c420028003a0320035040e2240b207290804000326000800a000c44102c107486003030214405509002400c0b40014203103040e002e600d0f948007084200c6251aa00740c0c040c2c09000d061142021160185001081c2c0a0802680e10b8031403280450385c5c0c0030365006128028001c070703910450190305030325840f40350700c0d505904101280e01d8010319905e450000c0b201a91040080200b0000241c00340c00024843c0000e8013a5205150b440100b0854175000300c5503140000d0b80042c0a0003045500c3e00002c3d41600b10700c0200e40d20407a9040403440d41e0001606252143c03000d091010b0f81d842c400d402c4440c0141c0740704bc443c3d844001103400240030700010300d01212140c0c9408005032115104040460807180014810f443ca49040e4071404c20f00d90200010701c250fa5119004900e400680c03600801103050001e900e1666442c10000e40300007407489150300b07006c11000c1401001001079102c2500d00f50380d0070013044519402c100540500a21400c3d80c0340e02c4500a0b20405 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 661926753 1250 661925503 661925519
    0x2060d0e06072706080c0c011b0807080c09040b192601020307021906060e0709210819020c19150f0f0809030d110c010c170606071b 58
    0x50052002e6107403c0240703075040210181850452600c400c04150315882008050b119056480d08409503410a91510380c040c04100d00392030411028042c0342621401168415501c007822950000b01440d1070400360400790340f480c4643c1700e0010307150301c51511081222100e9071043d40c40003084a1840310015042d50782c840100c090450340011b503125850980c80408011018000c5030710403030b016405002160900c240e0005000f01c88041600c226903103040101d14142d803005901d01500e1945c5424259078608060018114448090480c503403c040c807145000400d010203481c114080300c03181c802000e40300e02c001c0346440441d0042e554071603800c00031002c910a10b00345680c11303202c0b0103064001c01c10b4000015502100c2d44800400040d0400c60503180c201e100d402c5460b0418081c505507440c003a81c00e550b08050b02c282c4034451a041e10300281d54051c952092142441550450424520b21291f803c8000c00c260802841103010301800a010002c001200009141044030b25501c411140e46520320 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 661928003 1250 661926753 661926763
    0x60c0302101a13050405031b030c07090506130b09180f01240b0f090d060906020c061f0602030f03130f0b0907050f09070e0f0d06091a04080f0702060d0e 67
    0x18000c6501c0b941c0f003030091401d4050300e0720568204005600e0070300c0405196111444c0c2509080b1392703001c1030000000702041482010000c004e001e9011032541484820000e6041c02061111031052500351001401c1c0c448850716070788095007040128080c0003c03042079040407001d2020901340e518101e4031041132010414800813035040542440d00c00d5484e00564189807250210140034128144036515051821000c0020ba0b944134040214034002c0704d0780c0e068281e810421250071079400000070820500810507680308507410820703030041e07020726240b00651244640341003000d2200001000809482081803600ca4003a48001002910019802c0c2510f00d804113448164050203903020005540c80d05503403003103928800800c0540b454481034800c0e11140300c1c0c00300254001c00d100d03103424940c1d511014242c07840c40c09446c02003251110b500d0503649440b000f10400065203e503000f07020100e003410007600c1d4545541759500385d0f81e40315400001d1b50380c05954034940049080c05a0401c4040000c25 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 661929253 1250 661928003 661928051
    0x1903170705030603060a0b040b06030f09210f030907170706030b01050315010503070c060e070305100213030209040c0b070809010e010e03030d020a180e070216030c060c030210 77
    0x581116500d032a60100c6a610003900c29640c140c0c412000301d061810f19078021a00031030014000580224038102140d40e0b5001121080c51500c10441041110003060001c0b44403440a22807251006080c68121216070003080d6200040d40c00c080001610110100510310140ca08403008200c1030350040381290ba2051207000364000281003103075030304465003d03c00740d9000b07a850401d01110491034000440c0e5640008040008000080700980301040f40c0c1d202d900604000b103005840c24034110b0400601d0f1011040031050010320421600f04110b681000c042e098030360403035520720f203030322230741011071515000b03801020100900050840c01c2001d1140100040c03c0282c0b00d02814226203c010f6a461001c55a50381d0190000c0004a036080c02560060023114154108601d03501c03000205d4482040341c81c0c220850b010740d2002804041034040100f110058500b2045a15080c03c40d911490203418511031507082c0540041c8407001c042c004d00421950590b0b0714020400000314015580400210034 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 661930503 1250 661929253 661929287
    0x120d0609020d091a0403051b010213090213050105071104090c0305030a03090308060d02030a0602031f09150e0c0f031302090f010302091f05090703020708030112020906040e0d0f021903 81
    0x2410300c0f5000001c4e8501c0071320458040e100d0300d040202d10b090300308035800e040c101c89a080d5806c11400b8800c4550350f10000c040c090300f220040e122445915040429000e60704038605012081c01b00700009141d0b8542030b03285031000e407808140c1c110a0325000042001542004001e800042103078200968140e203d40d8850340603684415903a21114280403541e014080003a4040d0480d0315001d021409a030000c54100a01a000307404510b0103c007050141c4409400c040c1d0100d4603100840ca207030503104500c03000b07008215400398160404001241c3d0034803802c2d01d0307088096070100c005000c0c240b0801c0103c41080d005041681c851814031080c034911301c82400224881c04000e004103c00702500f00024140e14206042d504040c3d00702810840d9601004000d501010303000c000c0c95002036a10f0300558000c000a00c07017100c84003040d104001503d4802841c00f80100d00e0041904440c11002500c0300b2803100600b0244111462464100d00b0050010781e00d10008011114030010140d110321000100c07a904 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 661931753 1250 661930503 661930523
    0x5131e0f05061b0c0a0f0807091104090902010e0a0801051605130501110c03030c15010b0a0815010908010e030c0c03060103170f07060c080103020f09010602120d0609020d09 76
    0x9001215080a031801181e40200041c8101d41075889007940643c10140420100c801c6510303100002456654150043c0c40e40203800c210410074507004110000280a109100f0320124060b204612003601480c407501c1801034540480d4002c0d6409180a891507900c040e0180c0c8201d0303100c8401c00d010700002e846a41030419510043c541d01449541030702c80015040000b8a80720b480d0000450b85c450b03107003020020900a0b40812441a0f030104001c1460780341c92005060605c0d20b075100703003180810580c003000308010200315000d6469807125109511010316401d0501917400000101e5a481e16504181c1d6150b1070702c280c89002107000400303081c080c52100e081301c04220354841403640342e1000384001484000b45d07080c0746207201c1d112005001d50ba08406c1c0700c075042041e5a1904070a031a034040c4000301291840b0014419800c10812000006409841055165241800007952099198180104c0d42c00c081080d000d0300c011904528010802d1038015901c1d0000d58a51000034a0740400c111648208 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 661933003 1250 661931753 661931759
    0x50f030103032604020a05040b0f03030a26010608010e091c0914040912030b030a1b14040c0e090c1611010e0a03030206070521130308010603022805131e 67
    0x4103c9228404c5901821100741c2c1c61800060001810600e13986590040c1c11500d0049651000c0020f0b148000f000d5a4640b0b10100c14814a131b080208208098070743c9a18034014846d00f60084c804604540c1c0c0700081ea048c07540c407141500e00348070b01c03000e02842100d5840041b0b01010303400030120042c1d0309100d850411982d1000208421250503490040c04514505443d00c1054025407002000c1c92001d01510094601592002d0595035000d441a9001d94040f505002d04090500da0703200128058a04004100030280701a200608002c0c0301c0c1c0c803806a0718000b400c0074038450280c422107406c0c052164030850701403901880c2d010750b0000e07071400038801c40000c90785842c2c10500c02c42180e4041d00684060b417200d4074100c81d103074082080c10f414880c0480139002204040c842c528030440c0c00842868100e010f514006050500607844041058014032006020400c1c00303005800e1820b54500030107020118040c1174800340103400007808003034084c131f1001031035521090b00310b1a01014198844180c5031 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 661934253 1250 661933003 661933067
    0x10603020405150307030603020a0806161103030412110102040b030a0b03240403031b050a080c18010c063905130923070c0303050f0402010c0210050f03010303 70
    0x181c0c0c850154070800c3c220025200700c50300310095030458228600400d03441e4580d000706402c0c01141d40810700356440f40042040c2681d5004403580b269029181c0a900e40c003100c00496a613010140c002340100a0541d2091309050094019503a1708120314002d548032643d50641442c69002103840c25083c900b0103520204130b150209000d0f02c00380804d03520562001c0000c000f9580d40000a2045091642d00da0044509403003080c03503c06500400e9484942e255001c0100030700c0034101801c40c84404d03000f80500c0091005032440e6a450400c00e19110740400054200307000500424500c6071708101651000c1359030b108010f0701c02090108040d0020000c0808000110307186c6c0300f070040d0b00d0483d1003142d81c01e01c0080040d410110002c0d40101240417541150007440c25090800d480f03c1c1c3c045011103031342808041d058001d4a50141000664058501c2c00b0f0700040d2103401c12038002403044000c989041c150900030400d85050014078006281c0365a1a0b14010309600300d0401e1081c810000060004183c031 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 661935503 1250 661934253 661934257
    0x41410091a091603090c030b01051903020a0504020d090605040605011e03080a0318120e0111010501050f010503041a091f05091015180603211707110a03120501060302 73
    0x1a80180120030565541030b010b1141c0d9000f405120308045d140c44d04007002c83c0038a017810006e18042e61099030340d549020104a0210710403030004260264480d410400750350b031400d15030308841c1c040c3da0150369490070b122590020030300c3c000002c000303901d01020b120500c605a030100d81601c5140c0410000d8040d62000c0030009500d5210083c02c1c040c0400414075072a00c03d401c00c241070940803036026409002580c03841c91001004480e0400145541c030f1741c00f02980e00a44c0b0754032449208000b084994180808601540905880e0794103100d2300001240400504550014501101d00011041400c0030132081d51118120501c00c2d1380e001541707019000242c00ad00c034071401013010000401c03141c5425060304c4040c141c2e0483c41c03640011050800075850460245103d0000c0c4e80402c0040c400b81180340021201e07505125000341c04d2a6806a004440d821124040d4240c81c20301da101a10b40e103110040b01c81d0902d135a071328501401214500c2d000c02da0000004043c01f428440b05101c81d0703807100e000714224 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 661936753 1250 661935503 661935551
    0x1303020f011b061505210607050c070b0306180403020304081212130204110a020303060a150819150b0702010207080d090909080c0a030203040305010f151404141009 72
    0x50300b14400004850f41e2000526440076440c2c0b9034040c3c2e5500000e080010442091002e021145640005a06d014007040e94010510f08109d030034109803e803025654107003402104200c1c03500001090b480d40c1c0d503003552204100c40130808100703460540f80081d265042441090904e20076515802e4502a044040d5030b003040c0003021501859848070354004c04192100c20680c0c0082d554145031b405010080001c000c00c00542c1c00855907420500280705c8a00f505a210070302080e4111181a040c0c0d510080c050381010008056155240540540b080204281180e1640b100218040059001300c0e040103024518003d80075501c03000ea8800d00c280c0c4a00300401c00c0b60028507205418466540d25511901103e401004000d050a1007440800d2a14808006c290301680c0003040400801200b40a100500d004850040c040340ca030480c00b000d4540b11038094400180001201c881ca541c0362548480b029100402c40702c0100d080042c4038541c025501e00444590b41d092202c032085145000130740e041c40c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 661938003 1250 661936753 661936787
    0x1209060a050d0e060106020d080603060906070c08040504090f0b090d0806010c06140705130b0a0509010e0303071506151d06070302070e070f08061c080f09061303020f01 74
    0x190011000088071280e100260802d100c0d03a5500350359039100020001c0c1d60182c44a50001c28204040d200c02504102008100c0b038420340c00300c1c0400800500c04222030390003522a09010060101500d4807911138022074010503000703450048504240b10602a54001d124051941600661121950503450394200d8001350049941c8002069a0754458084403445601a140014110000030700c03441041c101940c0510018a022035480502d076900b101000041c000c007005280b0b0101100000b42c03460058032125070500c0012103c000d083c1d03e0a10840d441158040c070304004c24940700100710010700d254000c0a01040760746855000c6140628030042d03002c0c40249285811a918004006a0303a201400403400c6000b510342c000b45c10301e510f9907254010000c2d6251030705a1913003d40020056000188100c0c814150008001000a440701c7d4503608a60810082a994150690011685d104019071035410100001e686030f00340d01d001c0c1042080d03e108039489482c1100090046400141c91902d0901c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 661939253 1250 661938003 661938007
    0x30c020f061f052d10170c250c0f030c090e0a08070302011e05130f210306092417100504111f020a061a0a030311120906 53
    0x204000c2d040d002c14030200d662008103807180362075402090035003003060040f0380075490480448240e5207401075004565035054070808407030001c90340001c000c0480b5400004031710390307110041a50042c6410454212000500405c41d0189410000f21f60005050006851000d1414404184154400b0103502142d030011020005d20b400c00c014840200307c60b0040300404d01c600d01c0100000740302e450203048860f02903000020f100450000100e6a02d02c131038a600001d0b86004200940558807201081c1c01641100e20b01e10079030054a00030f040c010414007440b42e2a40407031400342c10650306400c0340c002e94800c600203000b00d6180c103110501c4a00300403074034003000f502880180600a00004c50b108203000c2101211f80d80b8607540400300844d17030280e80940d400c6140340703040c45a90401e002400151103569802004d6603038480f600070f4071580860401032034141c40e024103400c040e1301114296185000180742c0b0a110b5524507010b40941c0649010030307a80d000f03029004400b030316800d09079500e120018040714 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 661940503 1250 661939253 661939261
    0x90c03121309020c07030b040f0605060301090b010b0c0a02031e0f010b0d14150a050612060402011e1e0512100f17160b031b030c0a0c0c091407030c020f06 68
    0x480030350802084c0000522a100300040800d10403840c0601403801b0380204d801689403414640e0a4a00c0101424041d0f0f041040c02000501c0400d401350442c1c00e148481906c036a50164107605061020201a5151289610b081d8480e60701000d6041040003540803201030b80c041809141c00e9521070030710180c0c00800408044081440300825407520350452090f901100031480c9400d011030402c0d9011810b0315641d40030440d2604088482842c06000000207102a250950000300003a00c96170030740c500401e40030520300700e080c082c06118176081c0b101070b4024000b500d40e0400802e550040080030314444009400315081000c44030300340040e00c103020380c0703503400c82d050104c8045c900f017130560504c030588180340c084000e02504044490213806003d4559940e82802400c01c01240307056034041544080400521005914910448004000d213041481308140c04d400d11980c0b5540b5540403540003030a01010601e10b441b045407851140a82ea00e04000d82c00c51080120ba55000b04440c401c581d500c00d0001c1 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 661941753 1250 661940503 661940519
    0x121e190f0201120f0605040f0231030503040e0a05130f0201051b0307050c010f030b06070f03020123100f060f081b07030503091e0d081509090c031213 66
    0x1115503801030601c0c002c0160f005240000700d9038481150070b001a99500c0600062415000b900d9040004040c15405d142072042c8410680b00b01c1448034072800c410050040c1704030719402d42ca500640c4c00c113042d681c4855440495038411071003141d030324456070b2510b80020011082000058804c681100030128207059943c01541c4e564401d1700480005010100d4648040c10200014440c05110720701410074419003100260000c1420411340049c0350030540d40f072107a42c58400c246d581494000c002041d280441e82000d03401804c0f048800801e82600d515002e08945100f8400e030b014030708500c1c00c0846c07181c1e01c6000c078511011a0150788001541d5150301045680300e030300d580750001c1001c06e1580c3c2c8504c90303010703c40659001c0b00342200481c10100400492603000d1040c02029920f00751982d050144c000d0f1100d450381030070129034062210201c0032900ba40b940d041c044498a5001c0c00b00f21160030300b00109a52a2040300f04a40729105040051038882c00c64401e4800c585d0a404003684824140141 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 661943003 1250 661941753 661941773
    0xe060c01021b070b0a0c03090f08100e010b01270e0f0108060c040302060d0b0415230901030f020909031e04090b04090b07140c030406030212090a0b0c030402010e121e19 74
    0x429410410001723004118041003081c03010080000900502d0b1a01c540d25501c019240c070070091a4a40c5d00d000300982d46a60004603910841a150091000300f407400c400c40680311032142c1004103a01c03405420007007207403070751b500103410703948401c08a071469950410254050300c43d81c04000e41045084c81100345810703054000000401c2c1c0140040b03543c62281445a10b4412290b000314030040e0040c800c0081c081500500600031203080d501400151704548038010740458041009001d02c0000001803045c500900589030f03100644080120200c0701e1401c4941580c22900411803d1442c22000350814541485000354440d07110800c00700c0d0f692401d170180c401c511852012074800740208640d05110f80c00b40300900182449880068560f0000854190148001002c83c24140e01003107100b000305620483d401d80c840101684140d803035541c0c0c80101c07143c4054500040c0c0149608248500b16034004c20444444000741285005003500c40740c0581e90364005130440c08806030080794400106481c100 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 661944253 1250 661943003 661943027
    0x905070308070639090503060c0a1812030e040903080a02030606090303030c030717070930050c15120103171201031101170c0306100e060c01021b070b0a 67
    0x80c00280f01030301c0124108501503003010003144c420282c0c40d400d103004261114229045035417803c203004504040110f07580d0100900200101100440d43d4101742e4400c2d190580c0da804d101084030800f03540c4088405a141c4442c2d0101e022030540007240259007428442d4504884d09a59040070545802010100943c4060000b507005a0f0030445146692030420045004641c00c23200b01d070381da15051a000f0101e0403000d5600300c41c0c481c5003041c040234036881200c120596180a510801058680c1d4a500f010b952142100032400405007aa030103200010079110010780e41a07a500715038204003951841310b0b2084c0f544000990100400510101c0d0f820040700e06445107034420075203000343c4480302c1401c2000076803003110382440300400300070507513030001000690301e800f040e41044d207040c10544c078516400300610450040702d10b407004002c0715104603042aa80e04015049598550a1052140c017039484600000c42c03130101c41425203130f0200300040200440b60088001c4e41040030074403044a00a0f1021 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 661945503 1250 661944253 661944263
    0x103050c2a100612050c150d15050d0b071e020322050603010b0d06051e011b0c14010915052502060a080103110103090b130c08030c0a15090507030807 66
    0x2a02c0c2c1d0800d549a101da44003420000f444100c3c00c0d84240b409038504011000b000d030042c0000e50f14151070b94016401c5d43c0b9074000000012940324240104911600d1582c3d1106920104400c8a070b02408107004281d40078003019503c1184102c81440041c42c00703c200648013006904c20420f0310f124910040b2081500d140d02c14a80110554990004801ea0002c1e0000048080002443d65203541544101d100601341551310001e0750000d20310b20440070030b00f000820f040c0001c1e034240e00c40c005c00d810b22403280c4c1c541c84001c6285450701d440d011070205401e5447d41e03010416401300404c1c80340b000f841c01102440a17603185854005030b00c030b206c1e11a00503080c071051000e500310201c44c010f0390360001400710b0405540c0c0d400074035851030900880358841440d0b1a41818541088000401d1000040c03030303170124899004014004482c0751070044d000180c2d0007a2800e000200d120241010b001c40c4c1e4280860003801c40b845940d5042c001c1c18100d27116400e00401c65404004104005207007030014103a024010 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 661946753 1250 661945503 661945513
    0x10b0d08042d090e061e040b25110d0203190e130c03050f010b070f140a0f060504030905031219030204210c090c1b110a080304050103050c2a 62
    0x224160205040d00390858080710b91107520071020a44200b0000703034043c100c000300c1d49452040400c80c0c8007001b0007a10241248803a40001240000d00c0703562101c04520b41e801464050700028001003441c0e2016014046034010350103510a2188004161001030f00e0301548102480b00804007610801c2501a2407500150300e400612140011482214203816160b24042094500302c0066054400b05030051a9164800d21420f004603000311a800c04507a800300540780d03515000c440444c030b018024903005001d011a0140003040100c02e42160340034070321948641016649460800d502e408500781d035400203c1e010700c020072101c445000c4808a5460504006162644889040d80c0ca8030007094482d101c0712210080a041140194511004100140040161043d0309030002c11001c2c00124403103080080c000d2030810b0003c0d4405040c20007500030a01070220341d480c3c0d030440e1242c0042c8112400300f0b19080014100403911402c940d034442e0040c1300710100c1e551164220185c1c0b0742401e94080e4074070030 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 661948003 1250 661946753 661946819
    0x409021e0f130212060108040f0605070905040906021b1216031704060509060c090a0515120f071d152a070801060503070305150c070c0b0309010b0d0804 67
    0x441100c1d0440071445000903030780d898032140703a13201400050511810048018100800b080b440038104200360b134090740c08243c07902c3d620340c03c4918146e00d40020354402d1416509034100f1605600602440c1c1108011144403840d0117051f0ba12101803503c40d0281c55010842121500c104ae811428143d11030b0614501c50020070042c00040c40e021035003121840e46d0796040c0300300d02e84200503881c0d20054065445190004c65408255100c0035031040f5401785250010075910103409a0903503a4008810326410b0461800343d00c001c2000c9026201c00c00810981e0b50b0481c06015240d00070020ba04011b8010342154200c21807816207a03000d080541d80100d0003407070b03041054040c00100703c030300a0300c10024a210f50414100c1c43c212400c030340c003c910030f80c803c80d007c000040011403403003030a140016108140390382d1115400c15a1160b03e00044c25066111000319604a410300039600921510000300001380b1010140490040c3c800350207001004184400c2000c8000058024244011100e020b102c0f225 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 661949253 1250 661948003 661948009
    0x60a0504080d0801094203050a0303021e070507180e010501170708070e010605032d040b011205150702070e0c07030f05040b03010311010c12090807050409021e0f 71
    0x82001d0400b00244051004120303030b0903036014840da00700d1030341c0c0d00801040d1032000142802103a070724460003502080c24401021024020000010350300803007503400321249490002c00035031105040300c60f803c5c0310040048011926006440023140c0c428000c011540c01d01c9802202e015081d001c02c18101d444030b850340381404080c01490300030070746002040c00c1c03189031400c101e0170154075810034001580306140c2049040d0340b010480e4110786c0b50b424581d80d6074460300459032012060265003990700c01c035049803a411901940c9a244198050810b002903640c80310302b80400e41620100241c165800a98410200000d40e03000c03d810140c1d81c012181000d0752002958190001140d000b5042070010aa4400f451342160340800c10b00990321f41a4078040c1003c8100c0700c180418000580143d00040c400d02c0b0703a900a901d140507498002042e2494804003060051001d0028060700405004905c00012039003801e000d81500194002c00070255076220600e03000889044442d2541c0c0b0540101440006072 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 661950503 1250 661949253 661949263
    0x70807290304080d150f05041401050d1e0503042c0402010f110a030903150603120806030a0b09012f07110303120f1e01060504050904060f15081b0f060a050408 70
    0x301d1680800c5c0c2c0d8280c41c04842c10240c1c0050b41c015400723a81840240304000801e501c915040d036a045914410242c04e0b800d2110040c11041524080030110030254014404000040d008482c141d10305508041400f045800f030401e216803040080320550408240158010f10780c0842200e294038101c030340c81408140052500030310340c40c01d40c0490703c240c5c41403040c040100e402c814503240801c0d0a001061030b40d62136520f09001c0a15200c10004650085000c543d4144080e500c9541c0040001003581412004c0c1030080c00420754008040c138070180060340703921070344141e0018030765801202e41c103010003521b96844143d4a42c0003554940020420400f00701800f00180d0302450300310302c2004043c034106007c0607540350ba045540800c80251001001034a91100440313060750401e40300c0040545aa2404001400345441c0b410002ea091501000700300c0c1290401d00201c503401400c0b00c9a241849101c0c0c5020340e080148540c01c40a41d40c0e00c1000d070709240004196802c07071454003919040d40c86190328105 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 661951753 1250 661950503 661950521
    0x7180c0e150a020c04060b0a14090d0c080c1203090d020604031b1d0c04090b18090d0f0e09010504020a091505070b09012a020c060309070807290304080d 67
    0x7800c00710761010300b20750422601c1e4542400f0307101009407904102418005000c0c038103c1100300b1000b030245001c6e800398542900d43c1384a018095004140b5145800102030880d0700602c0400d200d00300725480c0c5807800880c420310a003e1302015500d007148c602c0c05d20845801000007a40c004508000000008000c0a0790041307141d2104161b818060406c1da090151400c1ea00c030b090b011005030028000800c1502089404440309401c0000d1422410b4001c0740c0d41c0400001b41401007190390003080180c007004144044a50403551f90894160040f900540e00b05842c1103440b40c00c0401075005000d681441d5004004050060802081c05a601c0104031701c42c1410041e80c50001d46d000c600c80c4108195010703c00e42081281009000d0181040006106101d451001814821600c40d00741c5402d802030000380700c844405030009a80e80303041c0440541c0c80342d040c802c0504034401c103a0b00060004c082d840d0040c003c60480c40845080d032864031000c0240d0005401600c40030700410884034464040c1c4900907103 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 661953003 1250 661951753 661951789
    0x2010e0a030f08130609030803011203030603050a03080106021006080604020906040905100b01090617040b041401020a2015010e040c090617120a0c0204051306140f01060207180c0e 79
    0x44c0d44e5550f2482e003070078103513644034105200503d4024800130390610281e0341950940a1781214469490401b140901859800500301d4018010045c1c1855405032a142c180e904076000c880a00b40300391028001c444041c0f04494183d080380000c1801441c00858003500140024000b00c2e0056858441c07505202c0711044c02c07a00c2a41e10000d0851558010901c5401882142465005407100451442000300020001841030a07101c002504009460b50b064660190388002151a80c803452400ba0200b4502c82030b0000030403102d60080f46922000840350769a615200400d6046e074a4200c0c4840b035200e024004072802e0410b520b001c1500c1140b4403d001c004d003400b007101d079000c0114540c03840c00c200c04070b00c001002003030400c01102100d80205031640c00302d0303040d030f000a01a5a00441c8811030303045100300500040c2800f005c00c0ba010284a92180603014611300070342180d070f90307440680e80c580040c803a40c41b0141802e40d0a44100d106a48034070504111030602d400303500036404c00a28080342c1031540c565 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 661954253 1250 661953003 661953007
    0x9051606021b031b0603090109200f190302060304080702150307081006080c09030a0c090209090a091101121407180f08121606290301090c0302010e0a030f08 69
    0x31603038058000c2c400c125042e4060a4031a020031000b08060b410204132600605002012420520f42581701039680e640040200d41740c2060001850a94900340078041c0c0b190b0780c518201451440c00350708031307101040d212221a010529550a00c625500024030a80388050305001c14800358449610090848800c800300c42d0707991920103805403c00001620b40300190030903440620446400550b119044141040307815281e8254100080c60107144910081c5403081060001682c0e8180d5006002c0b1648221800315280d0761701d50b4100112040d02170040e0103502851040742035035008010104c0f4004082001050030202c4c00071b0560f402d20255103443c000381024400e10700d10007840d03c465024100c040c90b03400450340b80100240d90344010100b418081080000e020514008005400811a6000000303001550048400f4841d14070514001c403184c00a010f0855000d02e010322442c07041690106120143e14159001160101c0944031030b5600003000300e20100218540107005490710703114000c4d20fa = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 661955503 1250 661954253 661954273
    0x5030301031502090a0b220f03052104180905031b06010602010608060a0f1821080f160504080a05010b0307062303090111160605060603060609040905160602 69
    0xc2003011494040c80b00500c107100c90f11141d03403400c180e5070807208030000e803d031907061041c40000860000644004045c10421000900005c61400700040780e009109684692003007150b00c00402d0318110361081924020042441814102215182c880ba54900c00080381c16260361102e14581c44000c031910078103a20700000e00b8507070003045030078050310051000707205d05031808010650b01c1c880684040e103460303100c07011058015100e6002100952481c1e15034100f035200c5040a8095a40c0424820070303480c3ca100c2250403003270080c030f546401f840d640c81c0700c010180c0c0d400a280c2c0d1101c1d00f500c405410003804010024400b40c0421041120074081c4000098116140b0101032426900e40e00400c10710501601d0720800744903025501c18070040d103417402c5580e90f43c3d4403405401841c1480b0307200400e84000c90119001d0b001400510000c5200e40750800054560004000040c0007c840302035004d64104200c44003418184c1104070030511a03c1115802c0e080c0e05620241030b00281c2104006078007400000c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 661956753 1250 661955503 661955513
    0x12052a010b0f0a0602120702360f07050405041509053c061306050d120e010c05190309090f0b1311160813030305031005040b130c090b070503030103 65
    0x2a8a20401c88506000f64070303080001c2c0d03d034500b892150b02e180d42c2c04120300e025512a0101c1c1c0802485844000500f009416001994040000100c01d9a4280f03000019240d40551450901070341a41d207400d400c1070b10302800c10002d081c420007040741581c0d401d140025440103900800d401522070a0b109c0181c540440700d9142d06480029418040c101d500101880b5941c000705002d07005102602c40342c1f060381c0641060005030040d07074007035034103d906032107408140a1100f45441210030700c0d6940000168040c0700448510200d20f03400f51160300300e003105400d4004010b00c00f64a40707100e17040100300260748144803011540d4214800303048940741d400591040ca0403030424800720201c00002c200b084c40c0d283c180161800b9410302e120284584604030404c1c0040003003507400142041c81180d081d15220725000b8010382058401c01c03007140f034021000c40c0503d000c0c0a06070b000c040242006011140d440c40480291011503c9001030115004020441040080003050000d0003500115900e514501d84 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 661958003 1250 661956753 661956769
    0x3060112020f0403030507050f07060302030601170613020a02010f0e010c02150c090d02010c200a05014b0e010219050d030915060f1502030712052a010b 67
    0x34048041c41000411803940703144040d00c081d00d4041c50902e40710380b5603160141c0342121118429207c0e204640000407120342c1900203502c250420398802da8580799540c88541c103042c0c142d9100e6070046110242d400c0c801c125501034900312099200124000d10340007080001c6030f401540d41c2c1003d945807000e0140540e01003010004101103107089000d030b440d0801211007035004180d2054419440d60441e0025a842001c1c0c0c4045141c0100c449050204070801052586184222181c010748064500142c80d40c01000207a01c00d081c0c100c150010201c000c055076600760f41405602d074071250122505009403900c0d4094aa80d52860b844564810605800181c545441040081d0f0f40003c0a0049400a400401c9480c0b90b8002800c0103e00f5650526000440c004041174031142a446c104c0c001410351203810b801822115800c001d21407148500c07004a840f4412050054510300e0a03c1030740041e1441180204201202d420800794030311245101c44266141c1d0030030f182e1103691504902d00c0d96140c0440 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 661959253 1250 661958003 661958027
    0x518010e0903040803180307030b0a15050103420b13080102030720011e0c110c090402010c050f01020f0a1101061809081c0615110c06070f0b0c030601 66
    0x700650800345411310311a600d2050742c02583c000405068402480e403410400f5201569100100c0c00d22450450380720001008020051203095051400014055000b40303e0506103e85071030748a01652070344400c07005690303404003806c0501401000e80045206000344140701402004102641d18440c010000c113a00046400031042d9920400510600d950844bc111554504d060004648084030705000ca00400d0585594014400c03c400c10324001800751b4401500242141c80343c14250011505107030380d070b04030340c0c5447d900404450701050141d80034030020300f455031089003154410101c1d09113072801d81e0003603031803408103040103d900c0300216007242412917100ca1a20013040b1030f40c0381c1a0321460f01c002074120070b0040e83e510007a107420b07c01000121540e010402e140307001601070b012641401071410303200318500d800f9440c03000d0410b03911840f842c0189684420041c071114024000304010396000c03010444154204108000010b1a00101148900040c0300040d03141d1520400242203640254 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 661960503 1250 661959253 661959271
    0xf051906081f020c0d050a02070f050d02040209060c0a06290307030305030615072d050d2f1f061a09060c060c070303140705160c0518010e 61
    0x1062201000024510981d96400c1c00102c03588007992812000903c10300e400c80000b800f0b81c00c0001c09a641120082000f036210f50301b251348180d9203100705034003683e8500503d17600c00058500ba40240c58103801800d07030280b00410721072a000780c40340180e2a14604120441e07030b0503100c83d00c03a001c040d01030100d01c00c031546a1206041c0d011350203002949961282c0001018004040301290458441200580d01c0301d4040490f03507501c02c0c441c2448004284c4821041031020003c05200c1d2288e0700d04103c2c6d03410280d10200808110425410540b44410607958100300d41c040b040c40c01484803810341250038030807100009001c51014485001c0e50103c80088561326441c100740781040356001100070030300384490000e030070b03611810742d800094214421500d01f00e0b124450441409914900b8500900c4003030310030b0310100030711069030205000b000c03401c5403e1004100240b00c003110304204451700310300746489900780c2c00038980c90b00001484e2020003255468801c0080340188080c290105103690421088 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 661961753 1250 661960503 661960511
    0xf10140112030f03050901150f0f0b07031b03180306050a050702032119060f0e1308040e040212030406020d1b0b060d210806030d08070203040b1c0f0519 67
    0x103520702821100f840b145020800d0f40c2c550000300640c80c2980074050f8802080990407540d603a80c2c500c000e000c002402140c80b101c07204400054004a900c04485840744c2c140c480160800701c000c1c0303a03c0c12180400c800d9061007900c000c4030040e03405202290700030f544030700340004440c1850004482142c00c01064017042d94070400c0140e080c4200c44081c601c84840b00e61040042c2e83d40c080080c0e460305c1001c0307481c50010341810f0010800c8001002c0394829241da02e050951075aa8021503c4140d44040d0006420500108014480020201e01c2c05078001e001402c4ec10010034080c0c1d900b450f5900550180d4010381029680010090b8807080605009000c2c0502030011780d89c546550002020240c125442400011510001c0214850190040007540840b5078207079030034a01c014082c01e404a070038603ca8001d80f0310f9013a0b0607028146045c09541d86078000c608003030070300d40c00004c25442404800440102402c07501351a81b5107020710400406a150041900d0404048001c1da4403545411007050a084c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 661963003 1250 661961753 661961789
    0x15030b0105030a18050613120804030c142a0112090c0605070f080d1508060f060f010302070203061003061d0a06150e090d140f0d09050f101401 63
    0x8032000b500c0d00f000042d03400003040700a1040c0354460b07081d40e5100030503d0054504104c041742c1c04034041d00030b00d4011700350300d000303110000401c5581d05400c89006000c108000c0e816804150820354013089100c01c1821510342c0f03040c4002c0c0c8010380c0700f0b131906604520b6038501c0100c480c1d43e02828038031030039100701d200340401c0140340c1d00c20901000c10701030341c01001008501e0314180403075040407003000742c0c100c141c0716500c181c0c1d40e4208020340f040001c0d09481d0410454000b4040c100003130f03481d11440c1a64440c070000d4130362601300012118542c05050405400780320000243e03405019081c0220a1428484111465840d0400c266030300081d824201d40310b00384d13010094620218105e1320f01c60b8489400160f041003404c00b04038986c030035001840c04104480400c05610400202c044190b82c02d0b4a0340315003548400e10401c000c0c071072002c80d17110200082c444441d085e1459085a11502d01c2203064440103011220140d11300b00c04001c01325480d546805090070090680d40381c850140c1000d01001c0f40201e0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 661964253 1250 661963003 661963007
    0x302010e01060501050405060f1606020c0c180a0e121b060a060308071b030f0302010207060b040b0d0305092106010f241808060c0c15010303140307050c0703060615030b01 75
    0x154403415008c1d2100003000c1810400c44800c480d4441401240c8240c00446030520030002d401440340c0011a20480e5030004035450070201c074001c9903285050592455440704014406005c4140500050348a07004034031080c044180060620070b0483c0c41d0980007005c41d80070440c54888007404e15900246130050900c00b040c034407400c580355103030000e41281e0b0007501c04007921401c0c0d00a5002030948421080c10604041c0d0640040034503501030030007840b841d51540d0402c0100c4040511150344508035204c9840003900420240c0502c0000402c5010a450111814881c00e1011401c0d0100c5411500c0180a20b129022807000034284249011101401142c0408040c0d07510a64641c2441308030003100d44070341d48942840d8081c0c94000300741c0d400c0342002c0c0d52148143d0440c050024081c01464144080500c0d648403060490340c050307442c0f00c9a5180590040890781c0007070010002c01000b00200340c11a00100000c02c021171040b130340014000e01d0150080c1c2001308040710002014244140761080b0b03030b = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 661965503 1250 661964253 661964257
    0x2030301031e0c0e04020405250f050f070b1f14010c0510060e101205060606030c0712020c0a080c0d02040c09261507120506180f01030302010e0106050105 68
    0x258040701d20b1030345180c0c0c04801c81003904900742c01448546102008a106403220b00f0103809680700742c80034840d541340c5051440103021076807038103400050250301d098502d0380300d00c0c107203903142c081410110318103485648106000c1c1c2c4060816124240c030301e414022601000d03802c801603a5010b4041c0d070700943c14108200307683c1000170f081c03504101d100010311060000500c061024800100c104029071680c2e42603902100c42e003154054030801c3c0c007a000080380c40040720282007042e8000d0140c28a81c0d101001c00c1240d030800b40204840070710900400c00045e4008c110040e24680640080080c1d00c1c0400401450152039000b042e184e40110300481c5043c1c80d02210b041c0303001d034101c1e004103040d1402e440c1190803400c0c0780c0c41090400f420b004100c4181e01c070030903840d0705c00c1c100e07506455203402250444a00c01500b600c4020005507440840c0c1002001648a031307421460084c103003624131807510306801054a00352049540c04180740010000c243d0244034180322460141e0003440700030310f01000a005c0d4 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 661966753 1250 661965503 661965509
    0x6050f09062505040b0c07060e060a090e270a11060703020c01081f09150b030103050304060c082107110708070303121416030c03051b070c090c0c111002030301 70
    0x10307000401d04040c058001c0044d20017410301c0c1c448054070b46007401e40180d070315031140c4698804559840000c1046080c0103045030b400e214141c0392000958a040c2ca040048075000307043c1001d9007580c05030384a000010030f40040d1114460001848200e1990404c0e048814118603034a11401042004000198001c2121000605d0900b000143c50740e50b4844441d8002c2038a0290003090f5500e240440d040c0d241c2da0000ca00b1080070403000b082a038460120b01002d12080c0400b0300745910503c01044441e101d01c0066450740d1240c4117550070422901c0320000300744200a00003142c1c002402c104104564000b603000140e601c480000c040d4186003600040d142d004502020b0100990f1000807009000d080d00036103412580c50074407a05c40e24110410401c084080d4000d079000a0a04034000c6160b0f01c2401500d0107100c10344c1c81289001d0840c0e104110f07907408404100c4501401480c0018525031600c00d03040002555150010365051529144516207441070405108501d43c8100d8021640e000043d2815 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 661968003 1250 661966753 661966801
    0xd03111212011401020f16030326010b070503090402030a050613090320070f03050703150c080114040f0f0b1009120201030207260a1b030f0806180406050f0906 70
    0x70481c2e10f400103d003070850041d84159607100e181070352444030109114640c1182e00a50302c0c400444030000750342d100307840f40250b080c403c003400c4401071001c3c641210040a000c1d20803404c0341d24004402020030140c0e0400c031140183c483ea0782e010040181081b034440b0010046003203040107251035594002e4030004207104404000312402c8080c4592600800c1004c014041500a5403107855803490055542c1d440d9000c00c0f40e681168600300450204c0c680500003201445031940c0e202c40e0b0030700e0040b08950402c0d8059543c000e4841c0250101420540320305503110544171000f14010120320244815031600c003c2660810043e00d50030400080d4120381a01c9c12582464050b0751a030303a40c01c200c1c0042d0110b05c80500203c245840c1103550490a60091204604544500c1021400000c68000101d4001c4002d07010802c061004110f041c81030b010203a11200042c9411a44000c02c00c00798600c0e03800312800ca0707a8035502e40034440042800c503a01588029144010200c5141820110040144017901118 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 661969253 1250 661968003 661968029
    0x51513090b06040801050a0e010c170112210903050106080f06040204090206280e040b06070605190c03140606030601140a02030f0a02030904050606031b16020d0311121201 75
    0x407107540ca540448005000c1400244880e0038035081c0140103003000d0b01c1140f0301d0362a00d445c3e80d010900411070425181401c10000080da841d00c00e08941c6010f141008442d4203184003080207070401d00795100c210341030702070355080440b60461500034211746441d003000100390b21900d403007042c1440008040c0d80c400e0341954041001c0f8103030302c0030030301901072022007040c0c00d144182ea6000104000781c1c110034450301d581e0f440380800c80b0312050100f15801c4400c03040d0400000c001e80d4010540c0ca1700041d42040415030000a4440030302c030402c0480300680440c0b4001707921800f1031011541c075031841c140c0080701220b41c1451030500f400044c00388111860301841e103036004540c00000b0780c000c1c0182c034802c452410420f80e9454420b0002501c82e80705600c40c6104138503040c00b25130a410040c007964812038150460388003c000d40300211249400244101c55110160100d2100684402c1c1000385090b201b40c541c00b4940301140303002c50401040440010a40b101841804603608299425504551142400c94 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 661970503 1250 661969253 661969271
    0x120501080d1b02030109150f0605010504050f120d0507020111010e0c0d030512010b0714120f0c01091a010e01090504020609010c060207210f080f0402010e0d1b05151309 74
    0x4a891030b0a4002070f40c1540303041c0c199010300c0300c154014480001320900403c000901081407030304403545801100c3c005001480140240c1c10a01c606101c041002403003034060307041c6400001d19002e610307000d080010f20007207548411035802200c04088101003070028450582981c03506c55070f035140e50030014400e045d040681002d05001d502148c5000c400640c0400d0700e582c4884d070004e0b2560014008a03101c101c0100f6806001c40d012645c149a81000260b01d0315005802009158a0300301d121036110035542c800024000400100032100c0001e10030304103941d50f44c0341113040411118141e2000c50881d04040c2004010307544e0318102c5564071006d013007101a03040c450034a080240112034009000000c0780340009085500954070b804540420756841e0b081c603041c450110342025080e900000750540c0e040201c0c005602907015440c079010040c1c050900e02481e0740f13031140c2c2c0001e4540c0300c044030113510300148880d0420b2600000580102080c052401102d5200c0d500c209005104040000342d40b03004072 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 661971753 1250 661970503 661970537
    0x11416050a050c03270603070e061305040f0b040c020a0b07050d020906030403120e01021804020d0e0313050901060e130b03100609290a030303180b0a0c120501080d 72
    0x2d07402c1810114121307034a5851600900c009140c036001620704101080c4603a01c2c0a01d003142c02c482c802d00c0e683d81c542c1d40c00041441840b0868000d00844981c07030342e0110000c6401c5e2503a22032100c003105851802301d01c00d07025605100454010001120071500b02a1030480401c03580b081c0b1941005180c81c283d17a0303030030b506c004810090003020300030359010f040001840241a840702203c107000412a1040151021030741816080303101b48024050410003e03262002c191800d1b60180210b1150741074003040340202c080c009815076022040ca003440914400051101d402c00c400041c0c0501141e0511030000ca902e41c00103039000e00f0006105003041e440c0d4240c030806840030301c50100e01402840d41813042d15102c04104000e010204054540e51820b4142d010a403112204000013071440030b0300c82d101c6981103490032409003510303511a0300312000c21030042c40061884040144520340b400c0b00022441480388001309405881c4444048890070704005100741c0002084124495001c4d007803107040d01940d0340304 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 661973003 1250 661971753 661971757
    0xf0601050d05130507061806110106080618010605030606363102060708031e0c030103020102010c0c050309100905120d020f0a0308040602031e010f08011416050a05 72
    0x1c4078880781850107000ca03a0304840d032500f0100d0b100d403090710010398075048116003840d280700d00b0001014400380c08102c228052248000e501203094004100c413a107914416140590070b88a0880146080e10f810854500030b201c3c08014003011800b50150342444000200740c000070680c8200400030310051804908680340d4140b1a030f03850002d5580300d03490a1036640c90064a10101100754101071075a0a10403d004210922200d60083c07200341803844580b210982a08005d16407884103401c3c00c031050b034408070032080910400c0644403066603503040d0310009082d1940d03940081c007400454144135000802c04420346030317119003e540004150149003000c95840070194455500030045004041100c0c0e0081003c1210903a42c2e02141c05d141d00c803201e080c2d0b80304401c11700500011724800203d4002820b0303070000c0d900090300b54030b50000d500c180c09030300321072080c00c0e40074041c1103003484800c000400080c000c03418001007505050495190000c07410441c508035101c3c0008000000418070f540d0740c01002 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 661974253 1250 661973003 661973017
    0x100f09050f0606010f0207030c060804170720010c020d1203020409020315181e1005060c0a03030b01050c03190507080d200703020d18082d070b030f060105 68
    0x11141801e400d003460310380750402907407001d000a00c20a4007401d0340340006600c50880e40d0011030011300c5403416404841c2982e015204581c081d52a05c003042c0d0f900d607c1d9000d00441406503400381c00640080820005602c9448082030500260140b0340c4050fa44003000107000383d4011441d03942098042004034001e00c6a03801034000c0780c1c4003000b4440640356a0700c0c140d9410304281c0c1c1c0c3d01368001081c0010002e0340c90896030440701c04146410016001d401c01034032078001e00240107840b8455102c00000f4010703040b50100c0405980302d91a8001816458001c03940980000e00b41903162001c0018004d480b84200c0280380d40344010240007481041c41032007110503a641149170241c03140c040721600000b60411010302a2030700030110840c00d100d000c0b00201c880003a4103400411417041051130035200104a1705201d038410200b1200060500024009a4094102c06070003614078030700c0900e0b0302d2608a2100f14813100740d10581d010b122051090048a410400703c05c0c10090355960800101e03540c1c46810 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 661975503 1250 661974253 661974263
    0x501241110020a0306090513150c0e06040b0304050616020d0c05160305030307020105061914031615080c04030b07080a02072112090201081920130906030203100f09 72
    0x143c00060315a26510400650700c40090a00050705c0d400e03100f071980c01044801a142c40700384214240540442d5000420582090a0071000305220038000b56513130300940e10525410000000700000c0180134024158032810707522030b505a0301880c1078020b43d260300140c1d050307051001441220b000d0210422410314240d10103911020507946a14026860707800c142c442e00090341c20326000c283d86107001d06010700411940d8043d040c18500e4014a0100450400a02c941500440c00d030810002041075015000e081800b1458102004402d00140401c0d0000d001c048840c809000038000560344450068200b4868a0140c2c01510b9000007000203104440000b001820301012500150001c005101a00c2ca10ba03110001d0780c0034082051800e40f807040100a00050185d40007030307030010000ea20158401048003001034450401c98040e20f0400c0f0005407400c247c000410020705242620280002414140e90b0602000d0311b1540400da94003545000c2c2d00c1e000d500c0d00005020002a60700091140d1707081 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 661976753 1250 661975503 661975507
    0x2710022d06090307150605062b0c03150e0f01032a03030903061d0717010216051507020a0c050f0103020904051006081501051909050d080409050124111002 68
    0x70b5410301e5940e5014039000ca812140f088110246000705200351001c0700d1000d00f40301c0c50807441066030141d0351850f17041c0c0102c10f2002922542c3c0401640b20b1021015482e0701c00180164101080d0010328009131721101d010350b0107030208805001c803480e8090440307600004203042c00103a20320301e140481c4d007108240198240602d0020516a1002d610300449000302c030100002000c0d480105a4460580c1440c604da5100346004c08c242500c0c80c50556443d180b20000501308540b45c0310049482c501d862060b5050750090001e42001c0e01006c180b036030402d5032030004010680c0f01c1d0f81c03458505845072107038500c56a440c50703564020742d01a070121400c542008108001358a00150760341c0311140c081c052040000d544400040702c0011603120042c002030140c543d02d040c50300264142e00d28480d0100b241c1c080005840d0001041d40f07520344440011445450384507281c1d4102800e06049400503405203100c0148508030350050804c2d9505083d0080d414900500d4003050041d40914205200303200b08002c03440 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 661978003 1250 661976753 661976761
    0x20f0d15090c03240c090b1803010b1207050a0909020102280c030b070e0a0614030402060702040c11010f0501030c0b030907031b03031b03020d0c15022710022d06 71
    0x441c0d0190203213281140d10410880c02d03031120440300102c1c103008003403102c07004015021112000b102001201b0b0702c0100049204600b46005c540f0180000d5038211040e0700002c4103109902c0c04c14031101c00b400516004000d0100c203900000d40d504e0490a900110250050762102c44150759488491030b1034200c4942ca0200e580d80c6080c66100c031003245c170b01c0001000350414410030310b860140d03e000c4860513620040001558800c074a032991001c0c04c1240e00440800000300180c80c3c500404042c0704443d12039803140c4030321035260387c20750b040041c0d08032441d440c02c4010b20001300500400802d48107801ea08070740366a6104001032801c05240c001a003420f04004d40300281d03000d01212582540e100307598518441403000c159101f03200f885030008015800595050384464420303284103507154001c000c104822410450400c003242d00403400e1200c1012207a0601c189020081c1d0f245811172029100c82c02d140b0140c48000b50ac03120301e0002d000004041010f40750b031030951240a4080b025810096807410300b8 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 661979253 1250 661978003 661978043
    0x9080309011b211e09032303273307150e060907060201021e0304021807020c010809030304020904030e0d0606120c081c030c03090605070c020f0d15090c03 68
    0x1146000815044540400440c0070b4811042441145d80c042d11921014120703084903803c5a081d400b0340b001c40e21044c483d003107034108079060b005125038501130519000c4205d01c02b8008071100d0441e54000380c5680700f407007075448800040d0800030000c16030400c0f51192614078000407448040c4030010704150400c10307a920031140203d04903000c1c01001084074076084c2d941030160302340e0181e4204c2050403103078001d0000d90710851400850f401403008092009403000c0c9103003084003103015200c941c0140e0101c0c56015803541c0006070780c3d0f0000c00100c0150305600d42640001c240b424000e00043c200402d100c80c03407000e0b45a40b4204110340340d11030002e05c00c0399250507a648911101c1a030a0f18424840500020071ba600494054864004015800241210180283c0c00b40215011080c201582c508030800458014410103020b801d00360794402c5000b1560040051407030244a00b944608d2f00c0b5075500000407002e055003e8a1420f41c4008201b9072024208100c00188075840601008a09901c00075198 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 661980503 1250 661979253 661979267
    0x60b220c030b04090b0106030f0c050910020a08030c0d0c030212040f06061a03190216110d0c1206060603020313140705030a050f071410050c0c04060902090109080309011b21 76
    0x6401d590b08100410004e40e0000552b42d4413290710010403410440803403241010b26540c080190903004807180450715a480c0081030317100300d907070421908000c125000c841c0d10b00d0140c2d0002840616003542005c82880c070070920f0280140000744500f040c01c80b000708000c000e8000c03c00a01106000d44c081d0500d4016003a5164022a10307181c007806c0f0f201d88405540780310710031780f07907207034000d0140c8d86d6454680d6890035180d00c0d1071004e4907803040182c5c101c40001341c0f200c00b5a2005c0c010702403100c80141d40900d01007059910581090051600610401c51041704103000805240d41205d0313001d403011000404103007059107030b0304425014011900d15500b4072000107114000708a030b0900f2910304903074030b05000404465090315580d0010384520401409445030b4050710301020310409031407146080200090441d409640415030340b54000c51001c20070740e003200e0341d01d000b407907800003451400311080e000030f0810071400000501c800c0da0102e4101840040b01e401d490103c1410000078400c0c800290207400340c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 661981753 1250 661980503 661980509
    0x30c1b031809060d0803061e0402161b230d02041505120a110f0f04090b06120115120c08070b03100605190503070c0c0e04060b220c030b04090b01 64
    0x103110b010380800c00c00d0070f14500460205410090060840d201e0703104115107140704041d6000251001044913006a8591004001001206042c018220310519010ac0d51015860301c03455803400d02c400c100300c0d0404100548000c1d891965410007418075600000f51309040001002c1e4000307240400022769202600d8a03081554030031120003402c295242441e42e6503615500b03006140c40720b03040e895000c5082188040491410090035142000e00c103030081402c0b101400d4003641c81c2d40050342030200d94100341c0c21103007555107420028440c05180c00002540000140318141202d520820308109200e4489860b401a04001c0152003600d940c0b1008260140c100340c07100c0c0c034044007290b8009180c80c025001c403180c940800350100c802e60120340050780e407908014808401c0c001c460555900160801d00080060b140c0c880d01801c1c1c074200350422608039251112000c0c0039024400c03000c000c174469442c800d011500d05ca540401c080d0703c80d2808a0281a60181c02900103081c404520708210741d10782c0d0f550503 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 661983003 1250 661981753 661981759
    0xf030906090304030507060c02060d1a0f010f0c14030c030a050705120306090a0504080c100207053f091314060114040905040602120c0726030c1b0318 66
    0x660300d071180c1c4240c0701e00c5240f000505a50084c00e007042220b005441c001860b60009002a01308001c55280f8803d65035601d1f0781103d00c4072440d01a004518151129020614080c07800c41444070886c540641020000350001d00140340c5140309034440c59003002110b0502c629001078a88030600d541018229800801084400380220b40080000500c030310242e0b449034400a01450854451403543c0c070040070050710a4a01403801c10602c000c81c6010400101003005003180140c1e241f51074100b141c2801480ac1600c0d103003581c10880b107249000700645502c100d0344400c00c001e0100e1a4000041028484c0d00d0009070040c03806000c800013a010b0f980b201d00351841400c140c0f903e55441d80011262420907000f9041e0380101480184050b00c083c3e80043d03400f51099900505e4041b20409600c4500b400b121441c45007000080d00008000e0001c182401ca40d40c0913001028405030600c40c0c0143d400000c10b1099203510103d08682c03121100520304007824051010340c0c1e958000145090107941d800e45440c1c0c0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 661984253 1250 661983003 661983013
    0x1030f060f1229010f090504080d0c0c02060c0706030506040209100f0203121810111b0c040906050108070905090303070f031e0c020120040b0f0f1603030501150c022101020f0309 78
    0xb03945a150148502c502c0c1e000d070f184ae01d000401d021000042c0841e460342402c01c18141191401a105c640c010281781c0030b0308004140d154904440241907410042046004500511400b0340980324902e22000400740c600f4404038600b40700908074503600802d07012410b44074100c1d06000040d00d0029440d207001e0100e43c1540e402d40005000c0300c0035941d09558070910b000c010001c00b0001d08c05031180201483c5200140c503001805440002c0503500801402c0e00c5007682e80d001040742c05801c02c0070304003c050500e0140900d140210740740c2c2d2a80002402e0509000020300220fa00314803982c040340460850401c0c0070303a205420403021004044212541c0c015600c0c1c20b1f80c4009902100d26190040900d16204078602410004e100300791342c002c501000b01008051003021035510951024189400c001c20032110b08036010b0400909654040e40410110056014001c840c158465980a41a40c05480310b205c800c01100b0340481030380c0c523120125025480840d600d61074585d902c00941c002d06441e02115 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 661985503 1250 661984253 661984259
    0xd02040b1b1507050c0f100b03070f0b09060f0403020409030206040203010f0e03031b1b0d02070e070c2312070507050105030709091503020d030e01030f060f1229010f 73
    0x2d585425101c0500001e110000014607583d1042d4020b11848161a040e01c18403c2164082c030b140001d81d00108200684030364804d40142001c1203040000c0680b8040e104e111807800e0610348040c0f2400c2902030084170000b449020145c040e1b01117070005d6a028208014078496410025184c070f40070742c1c040348a9401c00104e00b100c10000e000e030131102c40c000f002462035621070200a0750760020001c080c1c18080c20522540380b076401e503400f8205803608080003400390024400c83c002e0030002203030480664004080d0a005111342d01000d0a1b00c0c4a901584640f440902010f95072031038692420360340c106200301c5440da01c040010601615180780f0400858400d03640350360065440f404110703036000c0010001c881c10007590349540c0210200e080c1d9407243c1c07240b01e0340b00d4010070b950851000069001c21355455100c1701c02e5900d441000e810020300c520800000f4100b00702103000701c0e070301c0c4a100594403d00702c41e8014001400e2140202505400384002e03558551944400c4101c800d220343c003034810600c0800 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 661986753 1250 661985503 661985557
    0x18150e040b180a0902030105010b031008012007021210020c0106360b13020304140a150207110604031a07080f0106080414060a05160e0303030402040506060d02040b 72
    0x164418010060000300784141440c021440510000c1401d802c0304d443c0e107002000b42e207081c440e0b2406031104031962940c0f881c200c286032a4101780c590010300c09a141031140056003160011507442d442c3c001003100e654001e98000650300201c0618510018010740315104001500c41d40181b00c3c15042038028010036a40343c00c190b02c000181c842e00030f50940c0c0329040490010303004407042032030507a0342400182074065002041d080c6100000c075807250395000051005114044602c0f8043c01c9409008081982581e81e170f001c1d00e46502c81171401c07041e4000c90700034100031104d401e000304040301030006621540d590920004001050043d011440d24520210f80481d1054100d6403050480341e003500311503441c191003101c854800034015120a200d09064124561302402304074000e80310301d900840c03541008412482303c509031a60540a000d0b800c40c15071141d483c0481030382d40c0103804580000d02a41c070540419003520441b030961403028800500420003140310001b82042030103100725820302d60015482 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 661988003 1250 661986753 661986761
    0x606030c0e0306060310050417040b070c090902211009050109140604030509130e06091b01020d0c11010318120206010609050f0d050c040e0708100204060807030c18150e04 75
    0x15260550003a103840103070f140587e008903400c10f00c150240b540118454200701c2140d0000e4008805c80c200c000317050310a1004800000c8050104550300304158001540007444058a6240a4000010150203004c054600780000d591880071140148120310440c03800314000c06021a00302c5d4162400800c400c401503001605901c1580c1c103440d42480e00c1c40d0704040019005034441400d00c140c0e20340e28a5101000706201300350081c070300c100042034844c0c06001100c0400f05410310703243c11176001c54110f42e4055823100301c2003a450341207480075001c480c013240101c1c05408a031703000f26402c00a001d441020885140324001d10300000364296991a40c03585411101c401c02da12519500ca0101d000325540740c035103080d400c0a02c81c460001c50701060f41107000324065418000c26440b00742c20140040007002001d21415108240e480d00031031500c0d080000282c200e04018192908140c4e807521806040c900490f0450042c840c9201c1d00504159076282800d0180300c0103c9500000d41c21100d641c0d46800c10b806 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 661989253 1250 661988003 661988011
    0xc0b07080603033118050a2009150406021e061303030b0a0e1302030c04020306012a050a0b012603030705071e03020c180108070e0601050705010606030c0e0306 70
    0x201940c54141c550300c0c0700104050200d081d01d541920501c0e1180540701c4d0360011350042030000100030321150000040000c6403002020b501c8541e040c2100c039034048400c0c1090500c001c0251500315111406000801c0141a080c503041c100740d800000e000c500e49400182c0070b248401c0c40d07801401e10300c2055030550784501043c0c541d900d40c2d902d80401900002e0080c2c00c548100c3d100a8000300303125641c0d08270860050025a1303000c0c01003070408211000c0d420248880c01c6400e506032810343c070318200080001d000f210405807410b611a14025045200d60350b80c1c2000e0394003600700b01210040000381c02c00c0142d00100b8880e2803049080c16420040c071828500c070010000c0c0408028500f036984004c002d07502c070380c414501250b1604200910950200140a0b607500c880c1c0203078001d0030034404203010700803031052111031501c480308850010000d40034002006025140e0821020726243c66030340040e111030150000003002942445c402261903030b803640c003543c6c0c1144030342e8403481c42886180a2584803c0140c03 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 661990503 1250 661989253 661989259
    0x1b021f0c080c030c0c060106180803090d0605191b0e030604050703140708030c07030c050109030c2102040219080a090305030c03090c0a0824090d180f060c0b070806 72
    0xc000258a9407114001c0d42e400440325103a01d2910300c2041d0540c0c203150098008d400071607000c1d900c000c110356900f180040a40b502400852400c140580002d403542441c45000380b001d83c40f840044e8810a000151020b16044801c0c00c0c400400314a10381c207000c1308403a4080d00060b180304824920b900d00010030a000d01e41120203844543e042d611420011b00800c2440c141c2403107101e9000441000401c002c00321090f003070000e4000340d030940c506031403c0f000650082d41003014101040c00402d0448400c10b0850384186840101c10240ca24440003039405090060350240c400b01d0160080c0741400030200b0000c0b03160391043d84550b00d0000e014112100c0706005400182d0500025107540307807000085030840101000c44141ca85081c000038440032003a044601d00d500070b41c00c0c40ca500d102c0d00d90303036403c070044545500c00c2e949016244540c1e5030800fa500c4000b003050f000c0c1418900341e0a400054050a080640c90b45640e0f203411010b80140710280c002c480d40c0700d0880000c1d0002c0d00c20032619014101c01 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 661991753 1250 661990503 661990517
    0x3010c0822020f1804061b020706050c01060506030906090c1002030a08040c03050304030c0e130f0206130506040b070308060a0e01050d060e1b01030c0801030b060607061b021f0c 78
    0x310052075100e501004120303045103800400412580c0d9043c10b03100300038158911103525241c645440350654040501c0000c2074481c0e60009020b0540224024050720010701d801f50b2140c4040c50ba46024103020303071205802200c00002d100c0b00c401e01159044c404d01c3c0c4803040b6028420342034103204001c005260075400580083c018035200c1d500c60001035821900801c1640c582540b00d032106030641d4000d51040310a03109900040000600d80407849620000600040100302c41980350a4800003103210300a100d0b00b00003449000c00010500898081c102c094003c944580d100c1400c3c4c100c3c5d1380305d140d00303401042401e40040c156141400801d4141c4280941c032a41c540d1074403060000803800e804003120b01a4540c1c908036070b165010048841340c0d100b900c00c0d404116010500140031284964820b50402c2110760050010564903440260884030640300690b0300c80050800000400103a104214500402d4003080707019030740041c01803a4002e1641c07003610101c1c4010115422150074442c2600410030b1 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 661993003 1250 661991753 661991791
    0x6050d3224040e0304031703010e0f0412080a02070c03060e280b090f0318090a052401020312040503070b0c070c0308030604020c160603061707030f0c05030607030b03010c08 76
    0x2c650825518000c082080301c3c01d050b00c0766901c00b110010140c3e420480400840100043c0b2401c1d040541c0010240c4600b000074209501c07034040729095000d158040c0503000000c104e408200b40d0465a13980d4100289480c3c09449150010240c4820940d81600b0f204201800910540e100b84d85210ac590708584020340c81d100740d64a01100c000201014454000d202424031a200107000030310f9101080300811341e075006a1002c2082c40c0c2e40c05460711100780d240c00c0c00c02141c80c0f01c041c03092140c003d01e0348101003081c01c0440100d20b540f15056040020b400c00c4c00610041007030000107460f81600c105001c0c071403641c07940c132036805500800402030103001c1c58900400c0428080401544c100c84050005450070807403a040c1c500c0e01c0c2202c4000c002200f08058104105503044c0700d020041c00e4076001d0943c4840040c1c3c506135442c1a68000a800c001d66112845c003000410250040280400303429600389240c882da01400038018010181d00070350030003e26810041c401d880f0144a840840e04c0586a042 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 661994253 1250 661993003 661993009
    0xb06040f1419120303061508041709031b040b01050906031504060302040c081f1d0a060906060c1119060c02120102030a020d1a0a06050d3224 62
    0x8001e2464202c0310700303085090855001201100a480b0700c4914100354240340c54002d080303412950001100c940c21000c195807650b031000030f15030896042861103054144000d80520316201704010668148144032010410f01d44405541d2400b0904440c00c00043c011200195240d104180c81607a1091042000407100801400b000420580140001500a880780e0206045500c0a0b01c00b101080b074800410101c1d41a441c0c50308449181b200700785e2409494501c40d01642c941850705000070810100c0010b0a0300c280c0c2e4003050081000d85400d20445507079603400350500071481001e446020321344446c40150304009800c2403804a4501640903003600d41041162a1070748080120791004403640000c0400000b40055800344080c19001a618041074011104480075242102d801204805c00c1c4155a078455444030111505424299642d032040d03219403000300030783c10710810b9032240404020044101d0081e501c20b04c02e4010785000b55510f8031580d4481c1c0602c0404000c4001c0c1a28044400e281 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 661995503 1250 661994253 661994279
    0x6010b0316030b060a0c060c0c080d24030f0507090e03120703020c07080601050415050616020a09061509060314060f03030c01051806070503010b0a08130b041202010b06040f 76
    0x700c603250000c0c1c1e004940c0c1c00121964000c000320720008a003a051030040c000741b80304041d1a81d0139030401c103030000c502d03a4840e5200d019108480c1c1440c0d0780c610411a8422a0800054610421501c0c21100c00e8480c50b2580745024420002d48052042d1400818000301c03510480d40310740300303440084d400d042540101003500c2c500180303024101602071180d080452401c002c8080640103400142105604120522081b80d40010b80100301a503070441c10081c0391079408c03c8501101c2d030000350480e000c0580c0040b40b02410543d1000042a1401100044928440061807650f042907680d119007250354240c03c038280c610788540607584601c603102055039481c4c880c02100d40a08040d003640c0c00e06084a07946400c4800845184001c5510e041000341440e01c180886988410f4600b011802c40d410842903140c54000ca9032000240501200400c0c450b484020301581c01aa2240c1500e00a20b018941171481c1c41d030011a00c00998207281c810506454203406440c03e681c04e143c1030f45c501a2901c40070480b84 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 661996753 1250 661995503 661995541
    0x30b0606030f0127090606050f1518180403090801050f064b030f01020a0c260a03020901090602010515090c04080703030c12030606080c090f0603090c030f06010b03 72
    0x104d40c050300d400b02c800705a00400da1a9405500c0000d00d15213024140710319500c4d41441c2c1482408012501910303040c11b4800d5441c4845619000032050f42040041000b141b2207100e00307148594240100700415510244500594074400024003050300c50211143e688070064400b80e5128408100480d401030584c06904150040016044989105800041d400029480d414001c4060318550308170380b410704202005100300400c0c0218038210306680024045101f55100908401082032010003207242420f81d41d00c1e10006110b035964812802d44041c00135440245180e002c20f5803244001600c41c01803061910802c01c81551b0a480c1b0340c51000c01080501c01407450301940c100313101c0480d505202304240c070091442621401041e80c1c00e4100007510f00e2044034440101801d022060140c0d07a44050096080f160f00c10b44070b601c81810f04005044801d0040040c1c0d00540c000c41001102200050003800f1110140c094618070600c815640d521780740309000f0504051001c101107210762078820025130038 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 661998003 1250 661996753 661996799
    0x908040510031d010603030e09041707260406031406130e0a0f0318080d0c03050901030e01110405040c03090f080a0207151e051804020306030312040606030b0606030f01 74
    0x4010403042c0034a8000300e0f184140c008a039540c000070300030150000450301c80680219040615071070507654194603c00300c1d0364003400d40400840c10034104010500d040b00c003c00c1d80c24050f043c848100e4145072040d0440c0c4500c00000341060340c10300022583c0c600c407034003404010b40703503100d046074024445003d00a904884050351280c9882d4001149000181c1c04403103209a072488031074584000900a641902d40200c445c40c0c002d4008a01e0203170308403003070780b10065041c28050f448a08190041e00141032901c0681c07015400c140700c2c1041440408018000d0390401c8404110110300d01c5012021503509110042910f2100305000300400c1c505806001365074103620494044503144d407140800000980d211170041110005512068031801080c03e03c071351070b1441c080341048210301c4420ba0f0030803015507050189038008080303116a14144119151202d01c101c0702cbc01c9a041601e8510002c226a20060302ca0010b89008203040b8074200040b6405111403201311802c907400d100c0405000240400345402e = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 661999253 1250 661998003 661998011
    0x70203060f15040219030c0f020c090423100c0309020a090f06080d030507030c031e051b040308091509010c3c11010203030c0d241e09090804051003 65
    0x340b02c3d03886000a05010258103d02c09008800f038401805035800c444c401000d010310031100d411142da0020302d02c8041c010480b607151817500c07581807925002a0001150b030700500c8140c0c400c1c0c05604c00291030405188034a00400c6241200301c0c040b806c48032000d40007503001903a01d900b0004101250032280d00c0e4000340d140002c003d585e44403d60724020100d00c02c0004079231104200300c242038041c480c001483c8410304050110070100c2c1c103402101e03001c100401d000181d5485c0030460440e000c000c0d209401d0a50014a6039a81c0c8905100881d0303007001d00d016105200c424801180401480140c03860320354103031140403049160f507440c003020b00f0708103da001c0ca5144e0850324003901005005001002e00d412100252050300c40c2c2000300400c002e2002c0c0074195801081804024100c10040f41c0c0c4048800d580090649044280c03125002003500355006888002c1e00b020544101d1100e105420040b08544c131000c00741c0d174a08550a0300c0c038845015041c24424002000f290400383c10f0b401d6172003089d1900003 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 662000503 1250 661999253 661999291
    0x14060d151805060711030310051345030c030809101d06090d020303010b0c030903070f0905090703110f03011103180d030605100311070b01091a03120313030212040803130506070203060f 81
    0x200c6100410600b080c07148000c408440324100812002a414510a80c503030301c4141c9803330203001801c0a6800a0170082654000f8076054010f11084807001e1038004280010781c6d9440250421032a00448941c16006e00b10102d00030110028070b104106001c0e4014604682c07038a006c220854008002640350b40c0030400c075100b4559400e0020502600e55620b90041c018144a260811280010040c0405500841d400d1011030401c4081c031002c15003c0740c80c507048494010100c0d0161446082c0d0300700600000c400d2041c01d00d840702d400008010050201c0d551044200000c4003501c0c520711175280c00c00c000b080041e05c2544640c01910041442035034503881c211059480480091090784090718455550740d003401d12400c04101c000c8041811002040710303031600325041e100384c44040c084000b138a0b44210320004040c000d0018a80c068110302040e5200d9541750b8a6540f40c1d4422645c082022162040100f4286050b50580c1e030819000340c010300d015aa01e1110203a0240b002e4410408010742c42001 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 662001753 1250 662000503 662000531
    0x1031b090e010603110f03151b03090a05060f0c030106081b031e010605090a26030703031a0907120b19060c050114060d1518050607110303100513 64
    0x19074419400840006001c40c51824007010500704181c60501c5140b04040c03900c860381d0f0008040031010041005102180c40e080d454401062903030410000d09840030080111440000c6990b5040a001740c00760b401e550364889560304c030303098215500d044004050005016180c400c021040e401900b9001c074040d016001c2c900000030f0740044980c1070000341c85079031005010100480040c010105410309c64105454940003514002c0140034021049031201c1c3e00038840b0f059480c0e112180d00e840404d032a91810281402000341081e0f50444400350030165070044a809c0500e400b034860121551106006840d25075290090004502419400661940d0000490445032118401040c4a0315109203100c054600340b400d50302182d5183c144bc400c14000c02140d900e4440a103005517610401007107891984410403001401129005000c0c0e0007411600ae0402800058050141010340c03905242205032007047daa403480100c0d090142d942c0e85640c10803841c2031000800048500405001c5a11420350181c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 662003003 1250 662001753 662001761
    0xc1e010c0c030f060615050901030e0c04050c12010803040614070c051309030e10090b0d0f021c0b040b0f010f050702151b030903030f0304060b120c040e0a020901031b09 74
    0x200b0f590350031405014900b0000c0c68440c610081c007101040b14510038141c0d002410601503200414140350b00c1d0100903071100001d20400031911002030007000700c0c1c1004a801e10756a00000c0134044182950030001c12000d000200751021142d5541d654800e5015500f190010350b040001c0c11101e0401c11480402c0d21345d2104401c9403da0410100024001d0710b501340100700c040309081440c0241c01d994102e08100794040d40580c151041c0d6238150f40c0e40d030900d221910060a1410030441145d2010a403195184c446a4003821080030302d02c41031280b00320b040104001c8450200e06240d20140790007071000c42d54090b000c480070012a500b84641000c100f0740203e002c1c511b400201032807100e400114451944c42c459040d030400d21045005605083c0f040c00480e54a200b1f110802c8040000400050b042010581100000b40c20103800c03803c00d0000f4841c81503070360342e10711070316449241802001040c2d1440014515100c0e90014155401d59280d038407203502c00c0106607464035180d40b040c0008146101d43d805 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 662004253 1250 662003003 662003009
    0x7050f0a1b0e010f03080a020f030c070e06041e0e0304050301020d0b03011508060a0209130906060501260402060f0f0a08090c0d0302060a1521140c1e010c0c 69
    0xc20241d58041001c2440c0100700e41021154031a4240180a040400c03010682903e5014003490ba8032030b00004113a180000003d2045543d00c400281051110b00108010080301ea80707054098440d12490200802d641020b02c0803580351030500300c00e0040701c11941003030309a044100140ca07d803d0700c500c046407d90f8030012035812625103500521229090910031240100b045500f08181c0c20f06103c2440d4550002608150103990041180c01440d03540c01034240301114050400c06c100d4601e03141c502e01034006445840d011590a04075518608003c84018060401c0d205804006030749903801c004031500883c411031341070070061004040000c401c0008242040da140c9403013446240030519545041001ca8409005030b07411590130000030340015a8030342280780b150010845a055103420411a45264010041c4649500d18640c50031000104c0701d41b0180103000c401440010050b007a503850f002c0080032500041101604040c0c85221b4080d42c10b1b1805c1403610030800d11040d21214140901c9170 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 662005503 1250 662004253 662004263
    0x103020915120612192111070902090315190203190b01140306010f1e0f02120a0c03081b07030f030f0e0d0e0102011e020c16030c06030207050f0a 64
    0x18888140c20341c0c411049a01c040102d44210051545806458480040ca0103021401070301e54030344c0c01007101501d286c0b0031410041c0150703141105c158200601d07080c0c403503800d00035034000c1110208802143e4004c4440d0340c02c02500030080b40100d201c0d01040100700600461075000c1e43c0c0c40d0540300810600042d4001d541c0184ca291241060441d480125090318980302d05000c480d03449a1022051841560303030183d0309080605134590484402c0d10b1030003c080d411840122284000c24000c4d40180345c100e50805554211420a440d08281d40841c1c400c0c00c0c02e44d03020a02c2c81c40d40c400020700c02d0307410aa005861440040b2407011100a558164002c9102100410860011040303e25898441c080d1500c902807070908c41c140f880c40c0c03000d440c4c24811030840100120440e1b012140c3c0d0007504214030b0440384190b003004c00d6a412400f003000390403a000300c00d0b00b4058940503401100c812650302c0c00741c1340c00c0444042e00501d080740540c0254051002200c0d980140002510315030810b001e52070049001d4 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 662006753 1250 662005503 662005507
    0xf03030f020f0c180c09100306080c15071b080703080d050a05060d02100e1215090303040507090f090f0c060905030a050c090403030231151b020103020915 68
    0x1000029050a49041c28014280e0241c0b511070030a03521804900d004c603507038821140c0d09440e201004045441926111504000741710a00d454165155206104075130340317002070310710f0351744a841000b400d0142444055100d80c000d010500c0800c4200c1ca003030300000c4560710500c0c00c0c1c0303546040c2c60707043c4491944180c45284004c0341c0311a206045000d420307408600ca190070001440c00d0360006554403a4644040d0080d94a40140c0405901802801c060002c000309003001a108010610b69560381403079054181d00c140d0b00224102d9580001600d00440c2d008001c0c0038198101829140103146610301e59515a0b168009940404d0f02e075150b03d017901e400b0300c001064403410711102401103869984400c0c001d5100f15603031000310300c020031000d040c40c004560000075911282802c40280c0941c0030313503084e00703c130125000c401c540c540010100609420444083d080343e499500d20b01001c03006541ca804142101c80031030034101000e035203041d054414180107080c0410319010035080f0303080000e105840080 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 662008003 1250 662006753 662006777
    0x90315140106052b06050411070501060506210c090a030303050708161b02040e0d050309010b04200a120f060617010506040308031003020607060b1c0201081f0f0303 72
    0x803852541e0142c100d41c1403c03490034007107640303403400300c2130540300d20f0000c500362291031010a109070810030080030700810600185601c0342a044981c1c0c4402c00444543d80317044c80000c0c140c100101079070340050b1307490312110821508400e9500303c101e004000d5480007000304000c0e021640c0c0c1141141c05107000c1e40d00043c0324501000c0c003034440c50b07016240610070072008005c0c40c06194444910480e8000201c103508804240c1c3c40401c0152050b0745507080240110302c1301c030740c105600001441c426001e03240284107401c0000d05002c02c44521600c14450b8085100b000b410700a4000300070650400341c0e1a10002042c0c00306c4500080710410926500c1441c0c03586800c200f0254842d603101142c404d0401c007000c465161400040d914802c7c6c0c0310051030381c800807000400b4040841c001100541c0c000d810140d45064914002c030080c01c1c02d0307140034420741014403d11a80c4076a5280c1090003a07060b1516141525803e65040280300c07180c0d150400c04e0340108012130100001d403820001035109498526511702 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 662009253 1250 662008003 662008031
    0x30705040801150324020c19031209080d0207021201050106091401090b1e120702030301030c0b0c0601140301092003010c0f08070c020a0b2a0c010203030412090315 72
    0x9407100010303d912071215040c00405c5400c1030307102e21580c2440740a204210b1000c4c2c0f210181c0180c11042c146801061042e06406918041081c0350301d04c242c0d03c00c211619020786810880b01c0b0b03030f0b4001e0000902031112600c603440e0382d0f0050100d140000d01c030500c880701c0b1006203401d44034241c000d00b00044007424104003222440704114202c410074241007403001d0410000d5081d85c000c01d40c010b00071000c100c5000350100001c02c00c460b0525030707601010314640352540000c1d580754021f10003103c4018410320005a5440144290354081d24904081c00c0181d00e4500704001034501c10f14843c2d0305550faa0801e1000881d503101c9180c00c10015446640d8100e9071000301400c5504001824050220284001c00c80913030000800b0750016013030610035002c02e140d00200f070b0f034422260490048020005404009681505030000c01001d2003a103541c00502120941c40d10f81c00f0000c41035015902c1440400e0003e1100c40c0e0804003000d080c905803011598030f441c4c1c1c140240e8000c0d8080490343c1d6402880414203 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 662010503 1250 662009253 662009261
    0x90c010f020a0206070615080708070f090b0f040f0b0d03030b040507080106020a032f1e070f030b040510060b0304030801050d21030617070815040c05060a0212030705040801 76
    0x1400d01d001070026400310f80c021035410f00c1003078001410541d55440302071030050b220912074090f1110310300701d403501074590760f03811360700c403135a00483c0ba1a410f00030b0005440011409040d0318404003a20302c9407100d081408cc0b0010709480d505d00501c40d034845003600082d8440c000c0605589010b5500494002102014441120f9016150004010381000140941d036000a04e20794415494a401001c907400c044803008140042041008600c001106208107640e002500e007045a111130740380ca545900359442c05949140d9403045000c0e0120b603c9081021502c400212a840340c01001580d01300d00b4444d409104842c65500407081136007020003031209242d40030000c2409000b055845040c200d03840c0c2c0b549402d03031351016141d5040d400740c08031113190244240c00ca80010400290b840c3d0040f940c003907036592101e160340030351480c920540c1c0a0030101401e00d1340103806160000b00ca03a400c070f070600041c00706640c0704480231020f6109821074514100b007200001d511a0403d50b4030161a41d09201e0303028252 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 662011753 1250 662010503 662010527
    0x33130306050a051b1602060313030216141002011407050703090b0c0c0409060b0d080c01151802160516030204050705070b0a05090a02090109050f0f010605040e060d0605090c01 77
    0x1d94607080420810071800300101d8a81c0d80c240000ca1703100d00600c40e2044c25400c0ca00d00081d0040c4000c000e04c003005a1401170301c0ca500d48690203844081840c0e220380d9903130540703034400c0c980d000b9000c0000e482c44d424601c0310803086101c40c2c400490440c00c1480192454501074884400007400010300d8003d055204030311f08054016400c0042c60600c800029a9a0701d01000320540720360b5030348000d40300700000c42d401070903500c9000d07000e07003145605030500b089181c00900b071146840d4200802c01c01245005030b100e0041c1c0314100c100d0040d0800707160610009400014000c01100c08020342e0b0070100f40200501110869819040100075040d88180400d840c0c01806040c2070103814004c0300c00143e4002850f5500440342138002a096443c05000d51411a10349006074000f1040070012800b40c4458000c01d22880c40700100725843d445002d1042c00301d110074800c1000140f0144000e0011031028001d25402507801444241c403c00f035529075104940080c1c4003542d099005c400005159600715040c0c00d44 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 662013003 1250 662011753 662011771
    0x21305070c1b0501021c210905011409010c051204140a1a1609050d1b1d041109012d1a12090c0a030b060319030f090b093313030605 58
    0x8030039298402a01007c190500d01d00710401c100c1181841d0141030740403a9940703420000a0101414815983d00c0302441603c45001d20350030130409182c110b010710102c1b4070300c00d41c44003c1c044558454544000409841600441500405603e04082944e40301d0007407400d07008250741000381c10700c01640e500700c00f4207428240603c600c03203c08224907601c9182c03041089070002c1500328400240b86c0c0502d01d010180c1c001d0f8500440800d01448241104440c280c4924485ea030b103c02400c401e4020017400c82000d1144903580702ca2004104c010410300c5850700d90300404040d1400c011a1600829261300e46060005244c17184049406c1c3c240341060b07402550851103600140101517510400305010008900015040402d00404200592410002130352a8010040004003901051600910400c001d0740c5090018400e800c003c540c6a148070202d13140c1580052103255030644004007030340f0f0390b0207180811890090050f40e0100440d441d5004101a04880e0401d007002030541c178140048034070203801902 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 662014253 1250 662013003 662013043
    0x211605070810092003010902060406090303030f0e0a02060d0212281505040221010b0705060f070e0f010e0d03080a0c0302070809190902070b18010504021305070c1b050102 75
    0x80811010340da1640c900804c10007001d502c8003034030b010034003400324240000d4215000060010707000e81d01404040603244690750920032120310020080507200c210076451203940103200307880c005142100007064540500350000d4100900e601d8040340700a01220b0790101e030b400c1141541ca69041c0000c0d4a1242d000b2944108441c081030300003050403402d43d01403070b0302541d4005000c182c810008034003882c0810780608034890641e10f5a40c412030982103020210752510401e804034500d40520711105220b2242550f406040c3c0002d68200300b030380c1980485035414000001c0c0003014503280c960070740190300e0103515110040d00b810051281104c200409841c100351045c480080002e00210440700003c1c01222004040d401c00002d00f69500200e40c007000c3d80300e1000400604000c03071047c00a100d82000004082d1419a00c04590300f80c840c00c0f100254094040c8a01d880140402d6101c0c50300500245440440e502c896528254280c02409254180325048601000550b81c1000440e6040d810920904 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 662015503 1250 662014253 662014271
    0xc0304180e06070e150d06080d050a08040b0613180b01080c060f07060e0f0106050102010b1e1516050a0b061c060b01140a051801050c211605070810 65
    0x42e1034440c080c2014003004401c5840030040e94402010011a2062040607a52207410002d10700c000c2156225001e800e0180301d14603c1c0c018061400d07a11a070303841d078440c115141d4444e640c260041c07000414046c0e216040ca42c10799943d00e22441646491044903005024020311420200070005050f40005160b501180001c81140c4818081d17070716a080000c112510358000789802d4000c0c049107060b4107480c1c07168031201d18050605400c20400c550b008c1e0000c100d4150084207004a0035088401d600740f08a540c40d280c4441c1c10032141100600048018480c203003a1401086941d41910389415036041c2e00c0083c100c001d100603290080d1308404103c50748807440c800c0446007030041d0151540500000e95949208480740d000e108000321558007500d5a555505040c0c0d8060255009100306991074001c2c1041d2000720b5014808403410700c032401c401040b801d03048950b4800c9526805603140d410650600941d000761890400d54006684984045c20801d801d21603818074051803544542d500b5070401c0841 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 662016753 1250 662015503 662015531
    0xe06031f0b0315190506060a0c03020a060203190501090b15070614040b010e0a050c0409020703030f06080105091b09070e0d0516090c0c0812040c08030c030418 70
    0x2140000450390a0358400c55500304004000300030249031640c06000e4998031800f2a51420243d902c00d400c2d5461802c072404045080100b00c80c000c07030345950011030130041800024001d401852035039100f841150140409035aa26050b030b00180d070220780e0541411a50f0075941c3c103d010301809841805420031410344c1c2880001c1701043e48202043e0300310700020702d010038484030f600581490040aa0075000c1030500703140000402d0340903c41d22000c000c030080031032403011362805464001c040c004000ba0a1508282e228402507103c181c08505041d174840310410003001c1ca0068800922407400006850724208180c541000c2c0140c10070703040700c0341081000c0c034250360344200d15070088882c1c90258425a044404501000b6090102800c07038440d9092003101c6c2c054031a8503000740c401d0883d060145d405040f505445890700042c0013001ca940510040c5200041d210040f40d00602034040c0312501c56a0303d51090031503001560b400038541001500340418040000600c402060f510700410500c8100008 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 662018003 1250 662016753 662016763
    0x1b0311130501030e03070b0702060402090a051302010302181e0a05180a0b06071406060f0a030332040b03041b050d020f031e150702070b03160c0c080a06060e0603 71
    0x70036050580c0d07200140c00842c81003040d103903819409030101c0901d0400810295a64000f1076080b403241c0c2e0781c200050584c0360326019044c041c907503440740400c00550359801900a5048511482004101b080381c0401030b5440c1018900080120074203070629400c52801c0c0701b0a40a10780200d0700a003843c100229511904418107a40880914000074000d076110000900c0c51013118000f4004042e08c218110b8246c00100d1000c0c01000c048880800c2014102c0034401041824400a8040b600c551404421001e08000300600c1039942c03602c103034034040e289407400f11076041a081000d0b028008410442001508414583e892407054160201e852070303e4000f07035204100100080c090f4890380d0f051245514104000e640c8824506285130b24040b007518519070f240d000403200203091a248010404490000c107031f150070740342085d85617072456a621140d00f040c0c49102050f482000040d40b80c1e00d0100c0c844001510107003518402904146955003840005d9840541128164075078240074044d45a0b00061 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 662019253 1250 662018003 662018009
    0x40c030203100b070305070204050c0910020708030f07060e06190b061c020a17151c080a0f0e03060f073f110403030302120901020412170d1b031113 65
    0x3e40c0c4c4011a01e0110b9450085000003034003e400d006c284003070941c5a101909240300b043e42d030784c1c4c00120302c0e06040b80c0c1c50360107110b0100c05401c1001504030070140c0c2c1d0001c0004034002c1c900400c001c0201058185804011035485d001008041d0fa81000350310a405001c64600c4c0840d640343c10810359051180c00c1ca4001451001031541c0060304d6140d8078000d00a02909107000024856640f4001c20315105400c94150141c0c4a1100074219442d00381014081e031640320b40148100c0d0a00969040070f541e012520702031140bc0c0f2100c10710140480c5d030100300d043e01c110300407580c4020a08152001822000741800e00c2100f01140d00d0403020004640c05030700006030102c5982c245071000a21303802d0002c18050040d0300e03031114001340100c141034164006007880d609040342080c00d0740d1104c120500700d01982c0500702c41c0120a9042c0c4010851801d8040c02d0b94041c00341c42490101c0340ca0b08401200c000502d90781d00c48541208603d00c05405200b800f88149403010140e14060100c0e004d030720840c0d1580 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 662020503 1250 662019253 662019269
    0x90708010b150c0c030f0d18030b01050906130e0a17031e070924080c0c0616030209040203040b1501023403080406080f0c040e0403030c020c030a0c05040c03020310 72
    0x403c21504480d81080007000c4414040c040d01d07185440090000c2d00d035082d00d1500c0b00810000c11a40203802c00b00007180c4101c1790488034070039403a400c09040100140d0054032050740a826401d205c0f074445030a01c00c0114a0f00c10500400380c158462811180d0610b44940707564421005004010401100540805001444450042480d0fa5544055804444c00d81001645000142120103046500000c09405202030f444120040c0d4401c0c005001502ca40080300481e50460008651040880283c81c422540c00381409070801e0f01e4403010400303d030001c4038284c6041e41c1d80802d00ca1444020050b4000a06081c400ba0507002c024401030f840c0407420f12407001400c0e4680305e1079402140918887c4000e943c0c030403261940c945e82d0f500d00030464803064a0701d1034240c840e180401c0e25020744008960468100000581d043d0352544c074103900500007401808254014010301c0501c0782c0c2c0900a92031018420034000410300d0a08081c007040349e140c0f0380345000307141c81001030214116184100c001221000 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 662021753 1250 662020503 662020507
    0x10819110d1b0b0309010509070b0f031302091608070f1709030d020319050907060c02010f0903050f0a1424040c03050d0503041e02061c150e090708010b15 68
    0x24580302c415070b8a0181e0025070640103090100e003510303040008501407401000280642c3c3c44d510403040e151581ea10032842c0080081124505441011004e15800414440000186031942d0003046102c40100c07080f000246240d81c00c1400a80c204580c1e60300040c0da171800b41e203201e40d00040500800722842c00300ea010100400003400f10072040003250140000e10000b99101d0801d10940b01e5070720840021042d40608103000200c040c800050614104e43e8190388824900c00150011b480d100c25410000c401c00c5640c03031010000c00c408002500d4072aaa9000500201a0506084185003512401c001940d0000b150303110b0014000003030324104020f01440c3e00110340b2a881c01c441c9820b22540014018010150002c1a00350000003441c807030340c0500021500742c4c4c02d1300c104107405128008029480303041403105000745529a03c3d25040c3e1070710b48400080d90031001600406503ca164040790310000c49070204445004c003848200014620079000341700b0f03500c003000042c0046e07050b4400c4c10343c0b810300 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 662023003 1250 662021753 662021779
    0x18170f0d0e0d020604120b07091212030b0d23280b330a060503240f030303040c030c050307060e04390305010602070e01090e0a0203070e01081911 64
    0x2804c0443c0d000346040e504000c0380b0342c4189000f920520f000c43d0707002c01040c0c5040c0001184030310050341400031603112400100035074107400144c00401a42c000981c0040303140b500d910028261280400d0103083c12103640d4000c0c0708a514451070b06031450042402d03858500c10a03010700302c0210a580803580e00101900e001c0d500d0300c49689100441100003240300c141110128800680740703100c650b1900c01910b01154447e00c0d4a01600d070f038402174552001d082545d006074900300d09104140112107000030045211012045e0009103980c000740c5d000e44030b404140200b0410040c0a401e82401000c040d406801101d14004024018031601c0d10494084e5440302884108481d60128810840c5a06185007244044e5403041c180c1c1e0501c030010410120b0300e02000416824000219401240e082c0e00350552968205103029024080710307000f8031f030148112031600340141d6007406040b01410300c00c1101411903140000b12840c0080c8894600c0700540c407400c0d0300010445680300548810403c2d21040d080444c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 662024253 1250 662023003 662023009
    0x60418020906070b0c09010f080c03130507180e010c030c211e0c020c033415050319090f02040213080708010911120307021018170f0d0e0d02 62
    0x458458000c0060304d0b0b45040001c03041c846006040c82400071b82e10300e01ca10301c010f4001c0c1c1d401c000603207110b0720300c040620000f9156100c805000c03800611690603118040e95604800d05220404400c80043c02e40310003491000807424403540144104a107024015401070b41400743c02e07107007043d40e42070601e07441864807440100035410644140c00d40b00040c09000c14103628801c010303d000c14a2000600640707403910301624000420301d0b940c05021248060b1001403044081c000910300c4540704115035203990029070340c0d06240381d041c21000191201d07941d03842c01340f00780b407046e00c4140c612a076414500244000403c5028100e100c41b681d055034010380c0c0b6040a41c1c190710200c45540128a5032050350000f00e075040d0190000000903100d22500100c5004940400c07080391110680c03090a0382c02841000003628244622000d0b031002e83c10002442061075401d1301500305290403ca609070203c09011045040070009941c001c519800034060101c48000c000340711071400302c8018071070500d0070b5065042d55 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 662025503 1250 662024253 662024257
    0x30503070e0a0605040305190c121707030c210e0906030a0c061214010e060118031208040b09191203060b030a150e01080d03020a0905030f01090c05060418020906 71
    0x180005002d10b010340e41c1d98400920940c05404126443c4c0584a02c66541045000c07901c0c1416074081c0110324814141050504200c1c0c2112055078428400010001d42c40d19400043c03404502a0b81e6089202d0800d00380302124100c5132901d50701401d11012a286a5513000d40fa92600714000c8880c603a280c0c031010006450888600800782c61070005100010340e980d04000101c04003c90450240072041b21860043e00149007489280c2e84101401c000801641c800c01e05040a6545c40910454698482c1c0302d50b0200310082882101085016060105108640c2e5503680e100d00040000c00038109030b507044444c6404410320041101c84004014410503000b80c00210103003101d000b0365510392403d0381d02c52000d4400c05941d01280a50114003051001c011010340341070f1804030303008203103580b5000c000714000d40c0041071400030441041d001141d5558103211000b10b024802001044940c2103003403203031500b40340780e0150344030701d208103c20004103d000310740070501c00006500503282c004d0400070807464 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 662026753 1250 662025503 662025527
    0x40608011d150a0e18010e011413020d0f03031e06051e04020d0c030b0406140306071103070f030c060b01020c0d0f05120a090603060b0f07020d15020f1b0d0c03050307 73
    0x2da42c0d40030000c40700a107601d0301760703000110b03c000d109400e04404924222043c940310f04501108800014003840c842c001c03002c6031503201604100e800c2d582c0c2d0700c600c0089441c1e80c1c0110300103038035050002c007075401f03542003080b101c0041001040050315100000d030140d9070184042814408516900e0040e076502d078165803050010210030301026285a500500504c0320780c01e228400e13031600c2d00101e444694880e20b01c2c055a005002821151030f010415150f00c3c280501d074005a20003000410300041c0c80d60141c41d43d4604c40d45030810b0096043c43d1190540302004040c9046500400c14180540d55038551400c0840e004421042d4051340d07810100e041c515001c660300362818001a8281c2210f03444042c5000719101c540c5d003005003d4444100e00300c24418480031511300340040c0244005440c0c80005041d10a2082c1c0c0707002c0354211014080801d9811628281500751700c00300f0340808104011880a0840380c2d1380340907042c40c0402801c06810303c051090007070f040020100006403428080c40300c4042c1 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 662028003 1250 662026753 662026769
    0xd020a1a0f01052e09240206010b0c19060b120609030f0a02071a030417030f1501030209041a030c090c0a08071b081e0703020a020402180603010902040608011d150a 72
    0x1d007103001000c0c01c080118071840036050384816665411714410100c40d01340381544c0c0c1c088c0019920305821074032141c1100800301c1c200d000d606000490240110262180d05104e40c07404942c6103103400420800381042c21416145e50004d20070040031701ca0100888424406081215072640110a0b040f032070b01c07495401c1084041020030240c0421030041c405580309512560000200c145100143c219600068030002c0180f680c0c0000315400515510706c5105012040c5401410700c1c035810002003c0e51001000542c05d0f0032820304007845800c06000f4507140c01c83c00d49000c42c80e03003414540402c4501c1080402d0742000552030114003080d124500241680701c10301044a009031950a000016a001d11000c64003101c0007207104041c0e044031003e032810b1903016005080a40302a80901010303600802d00000c00c06194940c039051a680c0c100a1800381808190050311141404c4014095140680082a0960b65810510040c50440942e0b6902018401c01380400e0300e0000082001103080e130b008030b4a = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 662029253 1250 662028003 662028079
    0x3020718061d06100219020f01140a09031104022d041814070c0b040b04140106121401200c070b0c01050708060a050d140a050d020a1a0f0105 62
    0x2d42e611680192001c4a01c020b051400f035800b40c0e607030039001d200f00031100e52194500b0b01614220403035100c0c90f24103041221401d802d00ea0701300341e141d00c941841000715402c060103006002d4400c1c0707071403000d01d41614114a41144800c0c0f01d200409842007496018641030005c4e003131424005c091710300400080da10303044902c0004030040064004400940940b120440004180070b00c00c5001c1018181c00160f1a4511b85554841a07003c5200910644140115801200035000700344144001031849100c1d21108449130315061000360303e03036000c2d0314503a0b0400d20034001401c031480d100c481881c0340001441ea0b8200c03060121717041c00040d85c006100c0da0000b00e881d002129064001c1c1d403180420fa901c1c440c40c0d030b449504006071520311b40940c076005501c5901c3c00d00018503034a2170070311021489084441500180d03030b44620b0045054503140040e001000110200604841200501c0000e40328003203081c94810035036011140140700d00c0f807107002d1403608002625444a414031019a940d00c1c100 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 662030503 1250 662029253 662029289
    0x15130b0301060806090105060301120609020901170709020f0901110c0405070314060114030604020c0a0803040302010c140301080d030c0e09180d03140628030b010e090a0302071806 79
    0x125154100748a81ea01144111000031101e207000c80703105040c0c0314020260b5080d40d0801030751022044002d141118100c0c0c0e0741c411031000d641e55a003101c0c0244640b08050940e1030b034070a140d90801e9111b80c0701d812003500510440e1807042c0c2c00c5041e00d901500a103803020a00c042c0084c2c1ea4544001424071507000340c5858240284654560007161080340e43d4881046661900c07801118032a4550005558402007800412111310b0315070010b00352604000101c03101c0b581c1340d0320740031085d5009130b400b180540c0d0346641c030145050b040055814194105020b007815903160445a540f2031608007801401c042c2d0300c01c605d04402e405190300ea181c5000c003503c000f00350f2400c00c4011500071030085442c401c40c0f041e444140700d901d2003802641d1801034000c0692286480d004240074207001c585034010000d104d46822102d038500e0004101000b10302641580c2d8065251109404031058007520080f80c0b80c108140f55030200e900002c0340310444101e0703000320386400d80a0420b280200700c039070051200c4244041d03040f = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 662031753 1250 662030503 662030519
    0x206091815120a0b070315030209152707030914010516090902091f0c0b0c070303060b120f1504060909050c0d2d2a08010c0e1513 57
    0x7010320340e816516440d01c011074405140e5150b01407140144030b607907841c00041c80c2c148613400c0b601486031494918a013043c0c4076030001e0b00c600c408072120540d400c1814042c01c00d034a0300417403410302500c0c0c01c8101201100300521071103129100801800502d070315240300d2020424008800c110350b015010080280341000d0780a406203c800880314000510100000724244801d40300311b8602910061601c0407401007459052030528018100c8024000082080c00111b0b100d0340d002d610800d2542c1c03100daa501c1c020f04e07014048131045e400000c0c42e004180078013420150300b41c5c20030350088141154150f45a4034203034140c1241002e504100d800c2428450001100c0c4880d0300300050641c85030055504140501c014001e0100381c011014180e00302524040304459021880104070b0071500d000030401c00d29503250b400608680d074240c440441002101070b948a1004a070340e9001d459600001d1000310060000180540f18028665114010300000020751820078012110300b15031128000b01140d90310884 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 662033003 1250 662031753 662031781
    0x60a03020d0f15050c0a0c02040b04022809120b0402040b10210507050910090b180f0108040302061803040e041a0c071a0c1c061505130302060918 64
    0x82201c8160410803030305070030701444c0500e038400c9107800b0045040c0800118111428290740c10142d8125507a078001280c41d031102c2c00180701410000e030500c1400064680c0c100f201000b00c81401c1c040000d100c0c0c040c0065601c951010758402d401441444080d142d5000090003081c1c181c68540e800307604800901800c0b508072800f00201c3d45500e403280915124081040c0c1510b1044030281c00090f07081050002070314080d61480c4218600b03243c90482c0946414910301c0703d03400032846030b075a201502d1880c9202e11707000c6d10f1072040000a1800c40e900d403c01d0b5401035980c10003d480080918407a8a01c2040c1050400a440c024041c00c24089400c0c1864100444086170380b900e580a01c2c00a00c00150f280c0c00400c4c100d6040e80d45c414006d5598041c0e541c982441e07508007400d000000d8038104503c0100304211901602d6420b00030320b00080c0c0c80d28100e044403100440590080a005082c4041c0905040349051358017103e405641013940d0b5241c0c07000090f800303c000300e1121140303104001404090307070352081 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 662034253 1250 662033003 662033033
    0x313060b2107060206090303070f170c04050405130312112203060507020f0a032d030608061b251b060215160e0406050d030210060905040317060a03020d 67
    0xc180c2c0c00c0035480f43e80490301c804044848061942c4100041005103104400c2903403114158038006040000244040c0310101041d240000f80103400b01e403c1c4610318084c8560f5070000c00d404010b401c100e20b503640240921032140c02c0c0316200b070758070480465995141404c0f0746403442c401c0c011620364492050700c401d66895500080d10701034503010024003c0c900000f03010a42c1da219000502031000f803554100d408a400640c0700400a200641c4105400c21040d01a425600c0584020696074204841305203003007002001485204511040c00621884c80d108841042c3c00c20388141c8603a20003040303180004281c0d50401005480d40030a6020030060502100c015a0390075400d40d4039002c0f9a44a600d074080080e94003d5114a8a0240e8201503000e01c0e00c2500ba10005032011400d150383d10b00080020b6449003099003d604038502400c2c20803064841d0002404180790100440c0c01d0944005202100e08446c443c01e81e210312010840554401244d00000c50f401010324050b14800e240445284829072 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 662035503 1250 662034253 662034319
    0x3020403051006030b04110102011409010e062424130e0703020322020a05030102181c21030e011802090a0621031103040b040612020f0313060b 63
    0x3200954440d026003c1e610890741c002c82d80d03000c5901d540d01d41003519002c18032510f0566589130211100380f90500106482140100000281544005907090030403030014840760740e0100302e40003459040c180611440d51600180c600c0c1c8060403100e10313080030004134001030501001010690b80760800c117012084007510002c1107032900300d890f21402502640025100d81d048070102800302c04030003080f90140e508444c00100788806259803800440c1c01caa0000c04400070b00001284100000d050400680308200182d513001d0740e26141980303d60b01c04102503110040c50480314499003c42c58407941110b040125410001c010400c07521040d051140e50741c80d001c038080c0b64400d00213000500c4500c00c1c80e0407540b80a0740e001d00c0e0404044520321603041180c003141408280c2c0b01f003c2025508102410141c613100745c40b542e460741000300161106020b403c0c0c1c0d10b004e60042007a185a4840309007078940001d80741070044201201803403c4400b800510312041e1b00b00580400c0148010a01c05031407038400508 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 662036753 1250 662035503 662035513
    0x102090d2102190807020102150a06051008060303221809030f110d030c030e0a050607080105090705040506090f0315060a05030d0801030f1a04111504051e13020a0302040305 76
    0x40c501c26a00c8001200201c140c5101e0605100081034500005155681c4141b0640340f14581303484400080481c16104085265940d03003003403065040c0304803c00740550391400c00100360305d030103400a6605c3c0318401041105040c58140803034050280c01815002c3c1c8800d5001450310700e20300c0246801040c1e216000c1d4000360200c1a58401320740601c4244800c50780442c040c0060440390394007070380500b0071302140808043d9245d03038a0854070341c248031090281c2e2040c070140c0100c2c00d2012005000600603000180b00300074150901045135044422101111403e59015468a00081c0080c12a50580d407940d6003500a10b10350008841d11030340d40e6840387c45c2c02c0741d21001c160b85590a1599030002901d191001c20700300001800460500c03044ca82d5441d01c6642a2840038005541180a036002039404440306007004805a4451404a844030840e4420b0b1024508140c07506000600d607003012400b01545c44908805002c00352034040140005504d40745040d03555400341c0c2c1004000b980309210566081c055 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 662038003 1250 662036753 662036813
    0x406030504120c02031c09050607050a050105010503010e30030c1224040209061e03010e0a02070c0312170705090f040b150f04150c02120105091e0102090d 68
    0x1d11031074000b01380c0203001006080c0201c0b174403100c00d9013008001414400758038000509580c1d403c0081620900c03c202501c01c8042515241c2d00f55041030300028440e9040000d28903030719000040d660912080e0039080c1207c622400c2c1a400103c0018805001c0c0000000802201c9190078004081894684c0d2020084d03984036100450816011a02c40350b0800b4100c61491040c90182c01038045520020000c9141100d40302188801c144680120720480c500030004220342c0c50751024450707000201040541c0740411603070310501c0001480c0402840f0250102c440002240720b0818180d02c0c1c980c2e05042c465a083c41e80d8084d14507042802c07428403400d901c0005e1811420140103081c0320b00009007202c800d05130b601a20b08480e03040007040b0a4001414840040c2e490201b019200d841803c9443d4010f0240140c0180900031810407051410b61307050070144460840002402e00e240c04030b1481c0340714400074108510b4064070960714502d60102e60320754681c080c401402e070101610b45070482e800c080d8500c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 662039253 1250 662038003 662038007
    0x3a12080402010807030f021c050403080c0f030106080a02071b18110a030207050a3c0c03020906030c09041119080705010e040b0904140706020304081c03090503040603050412 76
    0x2908440007070001d0050b0021a95441c000c0e000b0b20014100d2000160914030100c100310002009070500107901d98840d01800705150b0040d41c06608402400295032074161850321800f1144018401e5504019100c80000c031085220b6041e102855403080380c241140c1d02d84164000703010074038050f00f043c1401340400d44c0c120f020544140640ca014400750b16050181424080d0f0080d040b0600a590500950101c4400110005042c1d0800b036015052611407844511020321400f0602c0e02000301b1300e031002d10880114400e18500d408407541180d8220302e5903034080110b410064007070102c0703800c080c504060208005101c8402c03000414103803540240c1d4500c04240300011001c0340300e903c680350482202030213a54410603031941d2501001d840481c001200070003042600c0703c11502036514580308040d4000c0e454080c0007500080080d4070095040c40e051229458484071500d00324031452250001e480840f0303029402c01c0c015180c001c020b403511a40c0d24240a009484103c038111480106d0b200c2400b6154 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 662040503 1250 662039253 662039267
    0x1d06072a0b0714131a090328211b02031005040606080102040e09010b0603010609030b0703020f0406021014090d0305091c05070327030b150301150e0a0501060e3a12 72
    0x206c40140100802828507884003201c005160112007588041c0c3c00742c601050024200441d04160024402c10340c1c1c440fa40010115050450f60a036000440b00c0e00c50096600041c0d05920284050800109600d6510742600140817a500c00205035001060009840a501c4515031044080c20003d000f0021400c04202e460711003401044040350181c681803000c80e403015121076103c0400c1c2401032038940004000102c2d80c2150384007100603445400400400345440c01403501c1c2c150044941543c9060800b03003142c55081851300082010759500c00104403400c01c0054501a400d0660f0032003454142e041d0003001360b84006026004514140704a00d003011011182c800c40958104420a4650440c0e685601012025260380313140744002c0321700c40302c696080c030955000103601c0101c1c01d4910700d000c0495a071a000240030f0300c0d60b07030301c3d1400400c59150400102542c95204803160104490f50020b598080103011204441c90080807840846078000105d0b090220b50140000407070710620103804035546 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 662041753 1250 662040503 662040517
    0xe01030b0f03060115050903010203010f031e0302120f0f030103050c01090e040305070b07050702041a0406060302040f03020f0d050102030a091a04030c030e03011d06072a0b0714131a 80
    0x3550200f4010000d0010325944842218010700d80741e4540000c0d0350003c1d003aa002a000b14900c15041340d01001004840d0f80c0494541000300403290001416403000380d165201890032441344080000c0700d0310480e00341030868400c10000380545885c1d507143d017000703a91170285003d43c1d40804d600f100013140c9080310329035691080e9410341d1001c2c03a00d44169525032103440050719600c01d010301440301c90016602c500410407a0062450407400c0075013014100030a95640354041d81c20703d4410007061121110080f19507040d0703901615115207521401e00890210805c1b024060000d52000c01800810600c94106111050140790f8034a95100021034820003100e041c0c800a0115035210040d200103401009030405a900c0100001120101d03940008441c0740ca240c0034034030300e0708000c04000300346411005c1e02e01c0050354503d1640d2502c41c200d07080740302500b0781180501205202130001c1c1189216803082d441075110110025107440e04400c0d611140703249800340e141c01d80182200280c04040d00c03410f413410 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 662043003 1250 662041753 662041759
    0x1050105010206090a0f0f0305040305060a05042003191a0a0506040b01050a0f110102040b04080109140609060a0e03041802070c0e10051c060e070e100f060f020c100e01030b0f 77
    0x106006d44d94800441460088003201480b906002c0000400c8041c00100c5c4101c4840c80c006c146480c052624001202c04021407403520301e203480c0c0040b481d4800098005032000750010515071122a401c0c00344651a4404820018011003010403c0401080d0092802031500340ca041c4022010840152414040d04d043c24000034602005207010300d107d160000d004080381000140340540f06e50b0203c400307911680204529a464a501d002000751401401400c0000385c1c0c0900040e00701110103a450f5080500f401003016100d00d121200c0e1002031080f02c0080580342104000c101c0d032122848041e402c5440c00f5299000759030000a814003a01c0f64041c41031890f0202042c11508020030401c64104504905404042c440810400260705200715000721140e6001009000c0ca001d0040c255003e0042401049000d0080e04121001007852800705407001e505045040c5030819408900d0f0140c23030424194070811034401c0d80340e0300d5004101020854801e0740e05121b140d000505201138640c1d04070071250 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 662044253 1250 662043003 662043023
    0x8010906150807090b0414120c01080408220e0708070f120e160303200102091c02180123120a12120906050609060f0a030209100f0801050105010206090a 67
    0x860341c1d100301c103456801190390810200700b940b0340c44281040e0700a90803d02d20002c030741c220007031540382c0407200100e44903513840201000b00034640001c000f88006070001b00500c1011610024880700d01f00e00707051118480d180d000d105035440700446841c1e5402e40d002804030f5a18404100060b216250303042440e4450f0725850303424500c0100f00402440c1c9138170701c0d4000303002e04c0221880100030700c42204001c6000b13070b0380c403102c10035018006500b5900303980060300d140e84100084442e946500e003c4c00e84d40d01d0482080046c0105900200700c0001110030000b984200e510004280d01e0f6031812010035001c41e0f49890030000070100300f80020f001e1015028100d90f0b1180181070005441c4000003110b0310070610300115580c200e8541740095401d25042114020b07120400c209044c28400b20490b40400701310307200b803c0e031950740002c03428100e92404040e00411011300000c1030980c1c20322480300104103c0c030600d0226a07a0300e01c054028602030260070b005000300c1003c910300ca81d0000741c0740c03a003603000340c8501 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 662045503 1250 662044253 662044289
    0x1e0c1e1c0e03010f0e010c0f020a05120f0c030304151802031e01060509040302150601030b090411061c0906110f0a030209010e0414041505010b090d020409080c0d08010906 75
    0x29490081107051603501d9900e681900c2c44500c0b0900403071501c2c109040c0042004c000001c000f40c1083c010410100c00c40d071040d45810089440013811800348420030200b550344440450803081c0c0c0d84618004640284800403e102c10882c0103c0c844012009640d8100545811401c0d5826141c0b8482c00c0603600d40d00c110b60081e00742401070400d5101a0080b8000603500380d40ba0081041520111810360160300501078000b880740ea02c0c4070169104c1d03024a010442680000001004140d0152000d420b520201a031180380d82c40ea0801c440040d007125050f19140b81c0e98001c0072b00503100c80da400301d61150030011007040544200060700d4a50001210460070900c04260480c002d4016041d0705040222001c540b40d8141c4551250828140d01400400100d24040c00d040c040301c070314079280c41d00242c6010010044c030000030f415100d500c1422500540305288900000d00640000d080141542030002080f00e2140b0000032071030584400e945950b01c681c0c0e0780c1c0004a04075155442410091035800300c1c48 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 662046753 1250 662045503 662045507
    0x3061406041703040f080d02162421020417010603081b07031502040905070c0818040f020409020301030b0703050c0703080903070c060815040e07030303021e0c1e1c 72
    0x181d480d9202c03150031a401c0c02e540301c101c54460080c90f0b10074242c9401c600349910001d54140a815000f030000c617401c8040e90324003003810140024003c3c401c2c6140421140c9011050b10a0110000c000d9042c0c4048803000c0d1607680800c0254000d21030341c014083c560b60840c0300c41d074041c05018200c07500010300c0350502c0b07040e1020342c2c610b031f00010120549014820001c800600348900340c00c4180f8240d4030040c1c46900341160704044810241c0100b051200e01411140000c08110898882c1d03032100362524401c8600c5004980589441100b5181803400403a0204100b1599409581220700032500c882d81501e55040076003c984c3d086c0c070384c0c203030007001006100301080c0680a080d4000c17090710200c92404009489200e02d22810783c01090028649005020a40b941000c9600c41c1403011a410007544500c16371941d076a01141c40000c040c19004929441c80b500c260408062040c5ea10f05201d0742c40410741c0d0b005880d82c0044130850390043c60a81e03041c0300602c0c00225034024404560130306101001003001 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 662048003 1250 662046753 662046779
    0x4050402060d0903020313090b0f01110c0306010314010501060f0c080f070803070e120c01080411011b0f03081b070213321e240618010306140604 64
    0x181d8005a0400c801c50050805104020f41c0502950103141c0700c018448070a150012540c0c000c045850401c02c00aa00d50340c0c00b000081e8110003420079040300d031290076000d400c001444100a6042c06500000000e01c04504600400d40c1d604200800050f80c03504c0050b00d410725084c0c1034000207040403441c0c10000e40c1d82402403281e4010021105c3c10000e00341ea820a9903071003100c07c42c0c0000c1d41801b28103003504019030500d00250214014105204517500000c004110003003019195205910f0f403941d01d80d009441005040602005140542e4001d09040d40000201d80741100051060000282d0031a038840310300c620042208003192805a55400704080146205e8412108607a40c0700034001c0078106801d802006114108043d1031000200024012544002c0c2880e404e0340e0f48482c07001807211a4990958480049420401d901c0c081c1101c3e49250f4151400c059042040000e142c92101740180368111441c1c401d07a8140003050301c0c0c1741d01c1500030242c4100f0a0b0014030500051003101c041d005 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 662049253 1250 662048003 662048011
    0x61d011d13120203070b04030e030f010605010e210601080d020c100c06020d060509101a072307030606060806040b04060b3a05191b0c03030e010e030a020106061701050405 75
    0x104031390510420b81c807291100d070400d4401320041801c03265105058202444000101e400040081104070320f0900064914408441014801d402e8510b41201a0180d00d04002018a011003150300668442c219150f4810b403013980603001d0b104400c0d065445140c040e08068500030581d850300ea4101440e518180030350041422048443d0304e84c80d005c24140c039980043c903c207040e074140c1c582a2900d0150343e00350082403600c17080c405d0300c8204004008070320f5080540007424840500030011640c403880c0c0d0b85c1451040d8000410090401100186a940c054251070003600c044a0070080b00d650402080304640c0e0a104523010100103100092800501c50626481c0c0c4203060545038a0361007028a482c001d503aa1078240340b4840d03a40e000c2c882400750700030074000c02c82d580c1201000820f0101400c00044600d8100c40010000c0c1442d0309400c041c0300342c10040101006c0c1c8024030480f450300128a84907080381c0e1001c0c00561a00c00d0026181740309012007040b00b219005100010303400c140600010b084020 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 662050359 1106 662049253 662049257
    0x102180f090103020904080d11070606080f0d0f050903150714071a1e0403030905191703072303010e15031b0301061d011d1312 56
    0x1e49040e041d6601150300021998541c0f900154074820001e0502505080180880d1081d40d40e0b0040c1030300a214450038807400303032180f054596488a54180d00340325440401c042296900a10804900900300e242c0589040c0d1071301c0c082807070900e107485490945541503042141083e8002c45005103186008980303031070950729440ea06240e031000c0000d03201c0c09010001140085e0039250100c204003102c4002000c0b40d1419040c06401802c0350340064440b4040e085801c4560070a0151140036154444c1d4814402d20089552000580008000070244104103070b02d0a0800250464803030700354100000c1d1940c035030401246400fa010043d00101010f05080b503226125940440c4102d0b030b100030140b0307010344c030f00d194400603000d441e40d0391201c00310782c000740007844801c1980d0352194142c800c4082281a080b0b000000d503a60520100d603199504100740032080006000d400007440380f21214 = true := by decide +kernel

theorem cover : BRFrame.Cov 661870503 662050359 := by
  have h0 := BRFrame.cov_init 661870503
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661870503 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 661870503 ≤ n) (h2 : n < 662050359) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
