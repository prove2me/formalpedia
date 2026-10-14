-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1735
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:28:52.748717+00:00
-- url     : https://prove2.me/submissions/2504629d-a81f-4b7e-a71e-4cadcb9c5f4e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 311870503 ≤ n < 312050359 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 311871753 1250 311870503 311870513
    0x503030712030f05040506040c0506030c1e0c070b0a020106122001030b09010b09090f0f041217010e0103140a0804050d1a09030304020a0909030f030e0102091f0f0306030f 75
    0x90401241520300010f2020000d110340b8280d03074007550300340d03201c0e0020010301c014005d41c4c8032900080c0006446941c9981003490b6007200620640b1901884420701800000404140d2001c0f100c02d0090a800c44950300d48035a8500003e5004030011800340d071030000d002914900c403600b1701da402604a0500700000d0094a880c4002c499000c900c0360425907114003260450f5513940741d85000c2c110007985143c4800701c9005012030b080d409421302da0060500c10400c681076000392201940180e01582e00d100c080c2002005540c10710846000818030341140001181c040717400c1018a04a0b801400714060080011100c1c5440b0301142801800802e002c00080c00281018140740e02060705c660801d1101000303aa84407e112901a40ea10607541c1002052000394507000c4040009481c440900b00314940d150390700648014640c8201c0014942c0322180c16991074401e5054503500c034400f80c203450340d819108500500c6c0e807001e084118045080624000300140c40b0b071050100b92603001501c80c0c40690a6110 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 311873003 1250 311871753 311871773
    0xe01061202180a0e0108010c08040f03030b0114070308190c0f08090a050a0c050a0803040608130f060905060405010c020c0609040b0a050d0b04050c0105090f042c030712030605030307 80
    0x3020403050b49418000407183c039074100c50300c001c0100811000055052424250a55444c440e40c6002c0001810910011940e05060703480480e40c1420002244408000142c40f06c40100d840089a041c0204e80c1c0c00c00e041c2c1103071405100c0e50840240c41c03035481984501d0000c0300c09030191007002605980d031802d041c9015103401504603242004603405803004e91b907010702c1e04004210031580080e4901c0c0c00c12041c10005144009000f0800246003010b08040004103c9400145601100070b0182d07413400601c01d1210401408907000401484035075000d0800326920b04050714104d446602c3c0c6080c42034264400701c1c00740c40b440801040e252400d4021000c100180040300d407800d5200d01c0210000445580f0f030007680b01058802c0903501224034090030300030709040300301123000d050040410030703104550381e40354801010700f10844002036400901d0507100180c0d4141588100c0d2a005512586079440001000d883c150340b140003c001c010711244003c40a4403050f221303181d050342c41484408002031030fa946e = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 311874253 1250 311873003 311873017
    0x304020f030f030d0b150406050d1a060307020a03020c0f01020a0f0528110307050f04090609060e101a0102070e15030a150e0c1309020f0303030f100e01061202 70
    0x2203504003200010b41506690002c031a80c550301c1e980326161703121414040110408407201005a9081900c1c0c040060054891a56980c24007540c49085102004d0101010041a076010b40090707140d02e0f1104d400783d80c0d174a1011068000d4440c076580020b1074517000202c0c0007400740c1a07001d010040140d07502d440078854107010403501070244010002c2e6000000001140701d05200b116805184054184510108010101d043c000d80140380280a0303501d0350221118400c2d0166400202058542828002400c0c40c081c000e005a0800d035030b0050030b49000624803d2440200c10400420407070340b01107500e407091031416a015801c01482007002d00645141180e1050905841d075400310b0034840042d06201040344110f4104000f18540d10381d04807103120300d4028507810401408115101400942161350800c00780c0d008645400c0401e0464542007107040180d000541100c2c1c4038200101403e0030644101e0700c84100010f10080010300e200c4050f4024105d0364035848410000306403900d082c0207980801 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 311875503 1250 311874253 311874259
    0x30405150f030906011e08150a0b04050709180501081209031606080f072c180c03040203060c18040b0d1506031203020703020c061327061a0304020f 65
    0x10041c003161800c1007009511541c1808042c1c0440c0d07041a0700151383c80321140d282c4c2c5845aa000040c002510001030006402200c00120300280c2e992a007a00d000d007110441441e0010b0902090001041d0003032100000d94200c0440c800e901d801c0c840800d412140c00344101d0220350310428083c101c2c585648001c1c10419000350950700350030a201c020b1202c15903580e0082001a00007020080b00450030805d10740c000741d003481c0c210b8001208903440340300c102500344100114500000e95803540e41d255180b1040d0080b840703068490501d000b01c0c80c0d48058200b12016402801910f0028101400c00740031074a4403800000b94011400380c003410700000700311840760541c0011070000000003244010340c2e24402110704c07135004100103041d0301d0134425007585030b1503100525005002c0100003d4001c40e00c1c00901e4021b549003522081c800c1f10144030002d21387c0c410041c590b00c0803449444d0340c0d085411841d484030204024030038135688441a0124a08061204022920a101050042c42e020780110b030320440c01 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 311876753 1250 311875503 311875507
    0xf080a0512010b0403050105070306050d11060d0e16050a0303170a090605010b03070914010504090908130305031305091506031003060f0e16030b0414011506121503020303040515 78
    0x1070300800116000a0308111003014002c0380030820000c0900030341d54807040d585030511040e0300e080081203802480070700c01003006000c140080010385a11040e24030050309907a0520403196011540c1e030f02e9040d150440c01c61f52050410228450418007071640032aa455581c8015444840815002800001d45690a055100c8181e600460968080e2030b002e000b60000095172404c20100103080d001780c039131181100c03004940c8150310343d030b03041000c0c0c03812603404040120b120300c4a89400307001c41c41010001d025200006001100380880040074000710706407505001e0041b51074008204041c1d00071682150600700031000000c00d410f110018580140381500d00c071000315141c0d036412068070310700e00c4000c050542c1c90b11260f00d040c1040281d890045500785400060074190307101c0040c0ca04000700094008600f501c4401c0c6420000d610010000016400c00510243c584000034a0340440c0a608407a090500e65841c5441d2a19415141100d60041c000c0d0710b028500814089003510180742203e4461341 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 311878003 1250 311876753 311876767
    0xe010b030c030702121201091808030a090515010b04050108010602060603070504020a020a020a0608090106050a080c0103051b0304080a031113140d02060c0c0a0b0c0a0f0206040b0a02070f060c0f080a05 88
    0x1204000d00b02c6c0408010f820040b0350305101da424116014100103110f908101e070021030120740c05a00f180d401607107640c0003103801d0509041c01450141000725403407600c5543e00c00010541556009041514000d0380c4807219030f683c2c0c2c00102e03952802540c8066240e0448003040207545059801450001d85070300546600241e1900090711000c65a400840410402c0f41081401c000a200e41006000b0403280c1252642c01c0205103640c0c0c108604a0324103260f6524041080300c0c14000f000d1103c40916040d490b580e151900c0c0c60403058018044150100c1c2c103043c1d1040c00b01d40b041307080d200030b54503617840c044895180c40e030075080444101c07030542c0e0030860925252016840f9000104480c8901c03100411700451080300b03100d40d00415512914010805102200000304045882802990001e80082400c006030002919500c07036039201c801600b10000d4111b02c1e650300802c0c40c9080314a8000000b8040c0e41c1e860013034030280d01002c0004c050340a0703003100000280c0d07003101420121055140250034041 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 311879253 1250 311878003 311878033
    0x609040609020d0c0f111f02070b04030f09090501060206072304090608060a0501061e020c0603090c0108070905150313050d0507170708040909060905060a0e070e010b030c030702 78
    0x8041510043c1c503648580102c6541d541280d0310307140a03021890f1840225481c0840039031200c50303508080c5134000501003030034100415601520a810f401c101c246141c1d0801c0c0c1340107402c00c003098080402240281a0004104100c0d00c41d00c1e04032625074000d8015544e074180210b5500c84000300500c070400301a0140304440481c2c80141010308051100000d0700c50410300362606e803500082010140ca820300c801445055404018803000c10f16030282e0400d8940321800c1030f400c1402402c200d60300080f0100400c501480f002a4811242c1001c0c0c850400b65110640100d8814683c1d02541c0c0d085403814140b80340000030b130304c001c5901c5507a2142c2e150301d20005030307a01c03410404601c01c0040011008910002484540139900c15424032000015240c003840d9995105c040c016880780a05072652424600140102500502c00155002e001d039800b500d4100d807e80d0050070303080f20700d94032803240701d0001c61408844e00d07940307042c0c512842c01141980d0b117000c030301d0059510060480f03085008110040c00c0e295 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 311880503 1250 311879253 311879257
    0x5060a0305070f0f140105041a09100309150506011d040e03070506010e0906070c06020c03120406020417150103141603030201020d050603150606210103110102120c0c060904060902 79
    0x4600c0d94908845141c03004c6028040269000004000e0345400002c006030b8102c0103c8003115880004241c112845514002c41d034090003d119402c0081741c000304108d941e0552050880e284100311002d24145031555440c119a41128554045014603501040450000317054840e4000001d0000c6030060600d0540f0f030960300035a8080310b050340820010b0000112550380c03198040b0100005200340c1c548044000c0003000b121303002078800b0742d00140c283d140700e0051048602c0440d141840500c54101450400001d41c82403061035100fa41181180c400c100c000300b03042c0f00303441c54107401103030390b23401c50700c070342d5080402d44000310114810400c80d450743d800d035034182100460098000603142c10b084880c1c042600c500500c8644070b41c0040d010071400720405104c4a820030300c00d650341a11917005030181090350030f510b00d0710003003212440000801c0100c1080181e4540c10b0a9099915940030003480d030b00f84d07004507200503800380c10003c1b83c42c205050400c0605075070305004102140c1550349290180890b = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 311881753 1250 311880503 311880509
    0x70801030204272001080c04180609090c09061d0f0709050d08030103030f050403020d030e0f030f10061205031813050f060a0803030c0901050304020a3507050a0905060a030507 77
    0x342c4442c44d180d07030104441000603220030401c1c03c200040c1e20740080d04409074452806144036101c4107040e401164606984040302520002108022102c000d05040f4403002d100d21600b02414106a80800c00e50150990200642d010302d01d07107007039502c4040708003508820081400040141d10322000a15940d100000d00015000314880c0380d0784d5055044c01045580c80349002d90612400b01b100308010f03200e00f510419000d405182491600800300e00080034040d070308055030303414850580c00702010b1501045194401c05034420030090350383e42d01500d0710100d60100002d44907400a1003a1031581c002c00404141c1258018400038400f400c9480340c00850750240e035618a80c0a03000200441c0d418034000000241290304000c1d81540f5007140b00040038821034001c0c83c1000000300201d0110348560440e17401030400c1a003c3c114000b0710511a03082072004134410341c0c0d2810708207054140e074240072401100b521009003c2c0880740d0b09106d841405000302624407500010b0140d40080400c4017070200d0805 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 311883003 1250 311881753 311881763
    0xe0a0506091917120f090c01090303080f0604140a020c010506150403021201090c0f06110a05060109091a01030b0f130218060117090309030d030605090112230a020103110307080103020427 82
    0x5c030b030038084075503031511686030802d5061040c03217102031001c40d4210480d580e004030101d9640341185d450f10041800b80c001400e040070388183d00c41c107001d41e1510903005000300f03104c400700070401a6254401c00c4015240f0394048207080340200814005401c28a09460070074007000004201c00d070890751901c400075025440300304001e1384e24006200d441d500c000e64801ca80051001003066084079141c1d0b6840e5641881400b0b2103d545210309010445038800c4d5440c1890300140c03401081da0b490404c6420703140110744e41e06040c81d200002410026403000041c102540150050f000102440c0c1c0502003500081c00302818080007001d420741580400c4505445801c0880185848144007000d142ca4038501042000a05081c048140901d45030100018116111582d00644840c03036030501901e0141e0800da440720007914151210754a03e8001000c0d80003038402e913003c1050b070014030b6134481c140c001942c0c1c0f080050000700041015107407640001da14802841c6c61101c4484209000844502d520402210 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 311884253 1250 311883003 311883031
    0x3010608041a04200906150307020106080610050a0b030405030d0b0f060d0e010b0a120f06020c0d080114090115080a0b06070606050906090606040603020703020c040e0a050609191712 80
    0xc10600009210104c404059a43c0d0902d4200030000803450200c000c05006480c0c000300005160610035000b40008020503000c2d00e8503820484258440d40304d00e030107124054000024009004291603044074071036a0000050360034008245071403000381c003010580e203070300411500252800d591404014410000459000507031145464049800c1d80c4042c3e10b81c80c805c0715500410040e10400c55040300312117501052124003941c4070300e030900084c01800406034003442038803009001d143d00280807a050302e907080d0a0325910001401081500701d402d01554000c2d85940c1c085c0074045010f0365106801080a18000c941854600e000c101c20ba046101e064480035141c0c5803c10081c01d0a00c1c4a94000074140c0300c0c1404d0f07141105c0495002d100c1c0b44110fa041590025900050620034885103203202d200030014000b1142d034411544da00c10f10b540c1c0a5440f80100e20105010190008a0318680c1c20050700c1001451200d8840701c01c2240341500614101800304407a8561040c0200300034802c0558030740c1c00f2 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 311885503 1250 311884253 311884283
    0x1608240312120a0c0f0c06090602070f08040815040218040c080d02030a0e0a0806162a11030d020c0f04150602250b03130f02030a050607020f01090803010608041a04 72
    0x30040c1c515904d085000d01c00ca1400030507900783d0165101c0071607a0085000314060500c1d142c404028418110090510030640f00d0b44010000c2d06130003007084480300c0d0120f404081c008582c49004820958009502980014544045c400001c4450b80d101c0d008041c0c0c0483c5079640d02d040c504201412000303c00680002410100890b0012611002c640d002c2d40c840c03043d541484c42c00ca58621002d403031842200b0296070110010340c4124000e03510140b5515040c2100180c90360071544038695110b04454841e441042541c413401d00240d015441c1c0001c0d0300816001408100380000e200441c0681d64110741c84041c0e020086020401c29030082c0320a07030040400850100200f20041111032001d022502902010496034560506413a0001c20a50041400469070315020b2000303004940000e4060084c0511481171007408100c1c00c1c8540001d400366101e01000024207422601400002000c5810910061180354404c2400e1907029114445030038174100c01420f140038203501203904a174071041d441044 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 311886753 1250 311885503 311885521
    0x20307120509030127140f0a0606090f02030603150c090a080715050a0e04020f07120c11030d021b010215040506010510210f020d0212160824031212 65
    0x45c032003651011700c1382001e07440012262007004802403805000080d40065890014800b0702c5a803404848080031030350300c5543c1d450810060000ea2240303814845c40c10001c3c110006182c0202c038407580004018280441622120000440c00580b82c42090310041c8031103059034a501c022440030349003a2005000302481c14410721050021740340180c0c00c205060100e8050140c100c00003c7c0d08034030840300943c0710249400c00d11038600582070003520803c0c0099640c41d20b142c2064211740b04a000c0e8050300350680c01c0c00281580c40118a40c1100180e00c020015101c60b0104a0000c280640501c141c485c020951385041c1941c002c10350b003d40e529000240100f0440c42c004408078103200341800c000000503410206552840c0c035070490031419a403104101107114049504944807640e06903011500e961903001c0c80d120702c7ca0129040800c08000da08160503290141726424400c0b904580032054030b50829030b1104110340c2100e07641d60984603140180c0d0402c4001005041180ba26280c25a1986840d40c91 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 311888003 1250 311886753 311886761
    0x6150504111206130204230103020405030a03080406090b0106020d030b1806010804060608030406210e1f14070503062d060f13030f0312051e04030203071205090301 72
    0x2195219500c0c1c03400144400d04490709864440c01020302010aa607104000304181005010340401d13403a100060105085484e200d086081c0c001c220745004c007803450540158124421400344d207600d50f0044604200180c070030100d06601034405c200100301d02c18a607903484000c030b0082e0402009a00724110910107580d15118208500c0000c0307074045580c80c01c2590f035024086000d46483c0c100101e240029042c006580c02000042604204907aa01e954800d4002d01c85002c207074083d01070300380c0c00c0341c1d6440c0ea08150144204031030b5100003401200a41062040d48106045068418cc03070f25071610401d1640c0302441c1601c108829124a9901d282c8002009070b0703a0a0707500c12100c240030045d440c2c812912600c00103098540190380d09070341c92140100c0181580111132801e2002c10184502000700840c1c132101110041c400d03190009a4600c0ca00743c02c05480081300e01d07441c0c98503c3c5010301c010700c80d03803c0c03c00d030014082d00540e860700d2095102c600040119a640002044002460241c5030809120f = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 311889253 1250 311888003 311888009
    0x1303060603060e21030408160b09010e1002030103110f1305100f08031804020d1d030a020618280206070b01050f0604050915010201150810110304030f21090615 70
    0x21500c01415641c031440080b070700010b0009445447d000c136000c42d542d410510149055500302c2c0c000a541e24008038010301915154042c00154094804940710a0503903009403410b0340d40c40149140d851892030709101178400c804030490345c001090301c0d40c00d02c004c10901c6214021211340000030b4009050071709415248001d648075200b103034010441101d02d0004c0102c903800b00c042c22100544d13180c100303d5800024040382e44088000e981d100600d142c00650000c0103240701c040c84e800340c0e500e61f61030744141c0740007244041c401000da03000444072010041d407078081d2a0300d00c6000c503852014010541c020a8094114410844212504170014895031400c8031a0004d2400d085074251b00d894103100c042084c1c820027929426503585c1c2070030350315030980c000e41180552500b209050f4503041e0390340403050b55a0707011a81040d0b4442c07030680d001036611140403c4901c9143c00d81c0341c0c0304c40c00e00e05032000c0b1411900b283c001c40021000b10001240884a40230f540c8070329010b141c02103800f062040d128400310020b98 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 311890503 1250 311889253 311889283
    0x306060e060a05070b0c0906040603020318030423061c02210105030d080613020a02030307090609150f200304080601090621031407140c10141303060603060e 69
    0xc0014402d040e8050b04443e4a40da2000002560b070710344280440c030a020b0700300501e6004801041c049002a4582d004e54400e0f9800050390f103101d070603102d81c00d0300d80c800c0b40580c7d4901401e071040c1d50f0100c052507a84410060000e0030306441c140700a5140014a0000b0f9a2509025000294003402048205050b011103203076050758481549840c000036612120890000240500040018a00d03a5106d55a2000a064500642d0386001c0600025180d074401c869007800329500341804501d8a1007080f9680503200c003412148581d41c0002e20980305039158050080030805142c3d60603001e2175101e40440b00d900755810080d6101c9040146142c10240141c0002403614034003107040102c1100340210100d81044254048422200c80c2401c4a01195000754640b469000141f0b640801c03164402c0c032000d04866605980040b946c1404110403508040c4003103001440103225104082540001800300003020300710f10585e16540d9507010140d401719402603a042c0e650300940c0050303034001c0c411184080c03088 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 311891753 1250 311890503 311890507
    0xf070506010f2d12030201021b01021308011a060c0a0c03080c101509150806100906050d0b06271e010506030c0a14091c06290f030307120306060e06 65
    0x800d4103010300320424421300d41d000d2030204411007854001c1d4119440740c2c0307401c10003280c0401780c0c2484502079032010300e00711211040c0040000d00404188144140072201001c00400c1403c55410080c0030b07081070300d01100314001d041c00140003070764144000c001540300c2d00303166840342190501503041003a110640640349091220b201300c00000510b15805035841040009048613040404640404a82d005107005118110900c40060100d01203003003100c2130389174184040d9454100b0b102e151140780b10001d01042d207003008071710369180400101160a500c2d1a0f8101d1509a00e201819140b90640305030808201e06066418401c41a401040c09848151580351450074081c25800383c51181c0722050007002491280310105015950450310000401801c01e882c003100070042d80b140c507001c0c0d00122a6140743c42c800c403081d0198041c000190603040010486107401003418080090900001c007035040c00304104280020b91221164207842209680000d015070070f000c4003030030f20307424200294898002 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 311893003 1250 311891753 311891819
    0x70302030606040b010c12170f161b0f02130204030605040204061710020d110403061b02070b0d092102030d0b010206130602090103060305030d0b0a0b04050906060f070506010f 77
    0x284406002c0d5032007c4840062000d62008840c2e0500c3ca0051800e00f282e00c1003441201c0c20404103c1c2d000380e0b40b1a504001c40e8400100c20307105126181d5140c5901c4101003048000305e03100d0310080d50705a002810039890400b0400090080b83d200790402c640329603a0358207000540c189480388102030100f509000030310440360301e8038581d200342a1407040e80094001440c03a414a510381c0010401c150440d601e03030f444a45038902000a0015122034800c008200b0451400091000510804440e41c0c200468a001c2180c4140009025100026505042540035001c03091800502403007410440d0750241d500c1d0a805a400703400c0e0303050010502d04543c09038084c0205040e101b1111540f95510030801a030f144071480050f0083d10b15540054041e020119150412601c10b80040050103012203159201035151898082103005502503d44c10000711000500313182801c80007401c06242c00da4a29041c4851070303990070b1620f4001d0304410782e00f02c030340442046480401000c145404000d801c0d01d4030015a = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 311894253 1250 311893003 311893007
    0xd0e06040e01030803040f050d0903061407050301062307030c0b10030515090a0f03020f010b011107031b12050d08090a050a03080c040e160e010207080a030806150309070302030606040b01 82
    0x7410300000d00a0f80c1c0000205007084517104100340081d038010250f50080ca601c480141480300c140c4004e0f184141400003103001904c112610034810f640c82e480e900d0840e400e049041307230741a01150a494102e101e0850f0000324003009800b0384202c6100b9a41d4805202061924101c54a0050b06020625040c8902807000440204055908030b0300e10881c1e000c141e45904460340740c104007201c00343c02e40c1001000e840907d0360110786506058402c100034032081c40c040004468000140f01401400d80041200340300141e40760828441d03801d2204090030007a0385a412170460000591001c403a6a03101c00489100950860300711790b8044124406061090300681715140c4800400c0001004c2001c10000181c0c1141c40c07005031030151030010550b500600c2d0100301c0c550b8202c000d00058000c40c48118400c1e050703610019038a8140c5070080d01400c60f008140c0d40c19550020040e0a45038450500b030300c2c46501c0b013441401b551294440c2002005002d1440c0103140c10f0500261205c1d000710b0618841103103e036 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 311895503 1250 311894253 311894279
    0x41109010b03130f152408030d200a02070303030b0103090b04020d0303110a0c060b101706010e0d150c110d0e0d020607030c38060102010b120d0e0604 66
    0x880d03c8203410045004030319000c00d20a25050006213400c80d501000032411074664401d0508005050f0044204000f4403280e4041c00e0041c800d0394400e900c200284119808242c001000c50002400d1164005643e2581c2004035003003444070000590145404005055050168200024003070904010180c0a5200d039150010010006405846164020002c01d4440da10540c2d40c0c0081e048400e0301c071049200000d0454050000070b558007828200b64114503d000d80c00c5050805154548045401c0650780307080302d0400041200d814080407403a00d60403600d400420310342c0d06200703c5c00a00f1520f03911348800300b15a0340c20901410404004180046180700282094888085080200010360741c00c0015603003c82e5101c00a420903c046100c3d010580c00420101105102e500c100c0f146141e070400d20b201c039071018650712503c90741d0b40c01c1c032003204240c21015980000d030610010a03641c59000111702c4007100d041007400613901040d000b05a09621151041000d10101c50740d038601450300345003100c0e032 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 311896753 1250 311895503 311895511
    0xa050a0b07080c0313020d120e0a0f050918010603020307090c020f0115170705040906020901022e09111203030919020f0411040f1202040507020606091501140d05041109010b03 77
    0xa45e01003440f440640d59031560f0700c602541d00140340d0070828681d00c0300820760300c252044580264012500880e41c20980f91121050319000b50141d4202e9541008001d814155001c0d840e20a5507242004400350309c05201c1240584a0908042941c4c001c0d46002490088e100040c034501c0d074500282d4081291645204904075920a0707a1441207440203031940e410020039902c040e40c410310f854840760410800d0380140c138111500342c080c0c8194107140c0030786030651840305490b0104070a01c103c0c50554040c1a9104c01c0c0c88034043c80500f03914ad16050081002c001c41c400101c0401d42c800b100300102c6c1041080b868840340742c3d10142c40c0d1ba5250a0703001c03c1c41403a06250440c484e5444440d40c60390b1100b444140c6000740344140a41ea0f81a660301c6e8000a940350004041e0300484c20000080d48041c0002000b0303002c0c0360060100303042c5644a000e0360702c2c0854504001d82c1080801214000e982c071810014180365007080c180003440703003050703d0041c41c04040c40d29039134002c000c55001000000d280c501620b0740 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 311898003 1250 311896753 311896771
    0xa05010807021005090f0f0706020d172a1c06081f0b04020702130501090b091e04050c0d0c0510080103080a0c02060d09050d091a0702011404080a050a0b07080c03 71
    0x1612a00d85c0142001c52605641c8002d01c60088030785900f0728000340c02c4e801c841c0d142d001e8036000c4800040450b220703050f102090028090704070105207100d20301018003800391701000034068601e45516440c0b81c5640701d1100c0050000d0f420111070f414401a100ea08001c0800000405044210748200c0940c1a04900002a040e90b610480f80c101d03101c0344c0440b85002da0040617154184003c5034418003e100038020a0080761a100c0801101d0402d004074030b02440c3d5000d061880c081d820401006130f00001030085a4500401c5080d04847d2540000901c00c0d51003041c812500c82e0400003401409802e1400740b404000704c14004002281110084680d00d03200f5240a02110040d4000f08a984c40b4000c50000070526020b4401c040c0711000c02c0000c01341d4100d94480c2e840e256512510143c9040b940b4041113074507001c000c1c40700158010400d0b00c202a000c900140d082950340c2900354180100101c05944903042500b085040004c10a4442e0b44103d184c01e06d8422400c03c907482480340e0200820090b4 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 311899253 1250 311898003 311898011
    0x6020106080c13150e01150309020d060c2d140a05090d030c150501080c03070b0406050a0309020406031a22031202120907140d08070f0c0f140a050108070210 69
    0x60b283c01e1070300400c8040000c2c1c01140075480c0d98a00c8620104001d104196400854403001d000c070718468001d800440340c000b442c00307a103a809903ca4100401c4a442004107000c22820a2800b10305800e07068107010070400c60100c91f100460b000034000c0300c9242c4001510440070491076107059000703020f07a81000425998801c2520713051a003980e4902403014081c08007450a041003031b500341180c110b141a82e182100b52001a418041855030307681103400b8015074040c0c144814040d26124002400340b28101e46004241c8001035008241200d1194000342c40c0b1000f00740713415100c0c0a2810003290081910659050b1456440401100300c0304814001020841c0402c0c0401500d40e194055030000411707105110f07400c0c2005800310745c0d901028840c0400700010180842440e1911880c040c0e010b80d04111440d00d0714010b5694a0300550b40754004a403014a8002c000c1410f0003001619070140c00002c1001d6090301004040003940881f55100d2410041c1010420403113603030108240f171030304000c450f000c2 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 311900503 1250 311899253 311899279
    0x2010e0102130e0622020415020d020d0315091d010b061305060708090405090c130204080303010e04230a020411030402130c0509030109030c0204110903061b040e130204050106020106080c 82
    0x3520b8900b02140a16205c000c0000d240c0d02e05400d0b401442100c1445040001104815030241d03101c00104e840c207800740e0000d03070711242c2c094000d40003111348280000040d40302c00e1f2124141d01c102c0b10560325484a10b00706280c4100380640034824040208011600d4a007854a0401000301d5941030f802a24094070300403446004000245042da400500020024041481c1103030015a880c502107407801c3c03040c0c4820f807103600030310480d00c211020b54002e000514034503802c0ca08c0c0c0c1031070201c000c2c1040b1014a500005507800302081c0c040d1503407a124080241004560b00e0041205070351998132002c24402040060000607581c4420f8801e02000c401030104080d0036221059a0900803c5042070301542803450510805520603994007038103100725030070400c68000e04040d4556028000d45a42c040c0c0c007140124030a02c0d40101461100242c15000714909501c0c0c1050b1100c0001c1030322802c800200900e50001140382c6070240c2c0340580030510080007100d0ad401046aa03c00300c0003042805a561034605c0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 311901753 1250 311900503 311900509
    0x5031603020702030a170c1c050409090c0b07031d0a180b040b0604061710030309061116060c020f0405091209031e030304020907080402090a021c05010b0a02010e0102130e06 76
    0x8000e17003507001a11288031004424000314a607012001c103021500496071001c2400210282055490034075580e9079041c14100300d000c000515208030207840c2007040400004134401b11360000c01f15603209548625229049003500c4601300d5012542a00c0760007030550510003000520825051611240e0020908075480c4011900070031903042c0362508800002008904250070180700c04001074070092680e410f0341c80c519698803161007401700500043c0341c20b50405c100c0d071159241000640941040d40e15800e95540a00540d200070303404800070501c003440210644c500000260304484080d203007070003545003103260b0f140c46101407580b00e100c43c940443d0400441d1803c0100403041907000c03a400781d9481400440303603a241c10440e01284030741c0e8000005114944541403450041e50b0143c0803c40580b11480c44030b0203500b114180b060b81c1c000d616110f030400304003030050364000c000c3c603488170b40d96801e000e8009003940c2c08200c0c01e945c643e00400200d1560903000f41580d080707400843c52024641c07240400 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 311903003 1250 311901753 311901763
    0x15020f07020a081f0207170a02030c0304091b030e07170102041d0129190c1a09060108070503070b0d06050306040c0807050a0b0a0c030e0612010e070503160302070203 73
    0x3010390082c0384001d0108043c100020381c41c5075180610013015081640d080381c0403e91044000041440c203090101c83c2c0210034200142400718641d00540b070800341d90b0901c0c185941c000780d01030010507460352103000c00750b01d8214035808560324a1a085c021010001d00d415610b511038803e0006080c152145400c6402003076041e10302602e44c01a2400c88040c23a10092484201d0a0007035040c082c11202c503242600c030030400c0d144904500c84184e24101f80c0c0f49011070100080d04070014040c0f110090340341d030000d42d031b00408040070100c04030038017111300f84003086920741141600030721115485004140a250790000340b85049480480000d41d0381c650000409000c1d05035940080e405108020131b0004000500301d00505459542c0200c0c0c0207582d41d041041312804c0d1504c10710081e0441042100c88091140c00d44d2171025000382003d0f00c02d0801d070740210b5070f01e030310407003412801550660042c003140c054a11115001800c525049007582807604090003007095000d046000d26500042c0781046441c2801 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 311904253 1250 311903003 311903017
    0x3091005090906061c270302010203070e0306100e09010621050c0607030914040e0f030a080a050403020706180f230415050d1401150303180315020f 65
    0x21085101842000010302150490801c0310b1003460800c0000e8004c0c1842c0381558000e18002c60f401d195049014140801050800011001901081c906407060b1704920822010f640c803d60005a032864180d900800031403412051520980049040c040c9074089810008240c810f1102850060f8603410402401080944c0c400e560007001e605010480c106803507000e180305030280e026200700014540401c0700301e125080c0c0040128150407401d0042d050040318486070000040c00000b10031078010300c29840c00c420040d4005c03280d8800601019455444900703c0d8100440c0349003441503003040d0340c0c0a9110545c030b004242c00c001e8040603070210b040f00000d6181c001c203c004020101d55449143c2080c00c1000284117249100c5c01408001003401c06104281c40b04004420f490785441c200420401d11601c20344040e950700311407280c0380302203c0e802e1003001c852668088070303009564a1490060600318440ba034852119041c20410004101e0001d02c1008803200351000603036442d104114080c603801085 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 311905503 1250 311904253 311904259
    0x521010e071706090a0308010927080d2412050712030504090509060601091701020d0617072c07030e190501050c0705070308160b040501020d23180309 66
    0x31a0001e0761070041c0500c0525100008180c64096440c004256178030201c5e45001000160241c00420030051103030702040c00c094808042d84004084210441c500c640f50880c1a07e0050002500c40c10300390746403081801240c400200c130f0504014102880503960140c0c8610003040742c01020307101c00c200e024014840908260b41c2e5100780381d00941402002070700a8010b0204182c41c2c034000c61200030002907103510488050351503038156070038007810920440c40c0c001208070664090040461440d034030300804001c0e0500c08110070540d0308a0b504030b40303011081d62002815038001d185d110b40c12840d1081c0071510340304d2036064840607160408210300404000341d000c141c074060003a4081a128040c45181e00e040e004900912880e151442600324901c82c4c10001411540200404c00014100341c0103000f180390441c1607040c40711450344a02615201c1140d0845142c0d41c009840321240c0d01c0c9100715039010000b09495000c118000b04d0030b50b2008800b500c2c0940d0300c0e0034440900c000314400c00450f08224070103 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 311906753 1250 311905503 311905513
    0x302040f03050a050c0a081f0221091002030103020d140304030b040f06150b07030c05010e03040f0303020106090605010804023a230304031202030d020406050702040c08010521010e 79
    0x2c0c242a62200c000740c0341144c0074041d0214032a41c2d0326184591030180c1d04504085d00e1500b0302035143e5503400b0040382051182c41c0e001d00101c4a107548074160038421424030b813148000d51500ca25180d0a00da0141c10600903184107200600140e11011680700505a0018507a41305112007440d00d481e601071a400100311003000b070108401c11101ca0311b52100d044c4184e00500642100800d0801c9074a0305010b40e034500001489101c01007407191880d1030b040c60044000280349440b1810b8035040d0780c800c2e08101c2c07880c1607540302041019030900c1190300038052440c04000306410440024071174203018001a02c41c8500c00703011100c02d03058540308000410b24000b100c3d40301d4000080c04160840d420803e44110442a50f0047c0b0240e0409030350f21511280009140380c00e0460ba503490302c41c3c03501d134100411448140a90b0941d21501d02c02070020744981d4588588441052040005648402088404029110004010544070065903600c0e403100084c8901800703041b01d0120380180b1b04001c0c400818401d03 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 311908003 1250 311906753 311906759
    0x6050f0d0f0209011806021209040b09040c03020a0f0b07030e0301020c160527061002070b030c0310121208060d02040f060806220b060a05090702010e06070c0308040809010302040f 79
    0x1c19030081000c00000e03224080b0030460350400805141d030a125070005038104180c440b4110448000500f054400140002800d140b140089141110200c504842400c12880140194030704120300400800641800b0b0040a082014135081802088002030a01602d0b020385940b55500f03406540e440c0c1070860881d24801d0300089000e061101c035214060083e501102403008038500031001e100002e214224102c220b86801080c170450000406900c021030080c4000410030049103030065001c1c100a81c10b41e81c032400c2c51081c484002c4a6544201e00343ea810f05481000140043c00035640e0355800d042080c1e555a03002c0109500d8094110001d501030b16100020040003d00d6003c6019210141c04688559403061164038103075131010f242c0140c10500044d21800619200100390f4021707400b41c0507103955903039407002c01c440381c8040c2c9500015175111203201c03d07104000c0251a41c00035075450f0800781c800b05a00d000c3c00310b100c00740c00500b41d40c030001458111a40a038048900819200c0300100030035503 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 311909253 1250 311908003 311908031
    0xd110f061c09110102120301030b06060903030712030b0d020904021302040b13230117070302160b1b0306010c08030604092306010b130b0a181d06030102040f06050f0d 73
    0x4000380b011100078012250149455100041160380c11101078a6130b03180d079085071103803040b200005220f40c0d4045d50400692401d503e0074409002140c0c880c00032003040641c0308001405641c10030307409901404c00303035080c4000350b60390300f51085d006601030750004d400035202032170400648216000100c1f01e007800035200c2c400400c04241c00080711100d0242c10b01c1a844079041d42903c1054641d03840c006a15035011000c1060780500c02900200541001464803903c146610700078114541d040d0be0a201c001c0030008003190075035801010391108000c241c918035000380040c200000f089005001a0b0012002800342c0d01c56a111601964010f607641141c4004214502414168240b48000c14000d020000801d18800d2050729059144c3c01003d07518141004004043c5400c8102c0c00010001c0841250080700022072102e0003500e40100b0b1040032005240c1c0c16402007c2c041c0c01310740640c0c0304200030010250b280714007500381c6845180040d907480c0050343d594000e0013002e8044d45401d20349104115108 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 311910503 1250 311909253 311909261
    0xf12060a092d050606040315060e07030912020a05030f0c010902030f030a0f02011b050a02100e010b01031d10090302030f03011508010501030b090a0506060c011a01020c0d110f061c 79
    0x30b401d949110040c0c400502024041e01d0050384c0351608140e05000c1400054540d43d9501003c52240c0c400207500350f51824058500702003914000c000c06d558040110900c0001d145403418030725035000170070f018410355440741d039284208110015912000300e8100c40b007404c01c2d0440306e4102d4004080311100000810726607100d920484d058004544211107055403980103000c0c07200c02804410f000d03021004145d10a0301d0a5011081d240114041e1600c00300940e001446260301c40d500c51030000504084513000501200c0c900c401c00c000740900e6440c0547d0b00100040c0f00c6501194401c0301203189400c6140992440c0510401410b07002e40100c00801c2d0b84140d5507000120000b140c0e6035060710799850f8015001c80710030302501034011034500e001030440d8115400081d0482c0c8081c203880d2500400c50381c005d007141d40725000c02d50a0040d10558582c15a810000498206402c848800030020155110a40d1000e100b0a0a018440c0189001c04540e00c1100f6120403070540c4a00ca0923009000d90910300034 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 311911753 1250 311910503 311910551
    0x9060603061a09010608010302090c0903010c020c0910030b01090e0a020d0506070905060f1815040f0f060e130c020109060c2f0c13060f0602030318030f12060a09 71
    0x2d00c0c0c68504420052a0a44009040342c9071070311026056403e513000d08c03207131a00040041c8c11110041240308002c4d2800d00c075100442016a003e05030984141d001c1180001c4003074100f02c01081046004d10126010044040c1102d0724002c0028200c0c1429480d6410a20f000f4006503110f6065152002484404034000340324002c1a5608512181c484041281c80d001e400612079191005000403a08440781c4017502d003003040c004000010b50741030038041c034541d64403580001c080c03091041000c0042d010b095140340041d01302814280d0400c49000003146100f0741d5000e44030340c2c00d03884400c0f030103440d8000c0d8042240383d40c10010520246906020181a1551142c45001041c84042d5500441011108268484401007000e00b4030401840b0411202041d0494542c900c296598400503005070f4040c2e80c40000c0c03d6a4001d140ca83c9051040d00c2001400340c00040340c40e400c1040000085c40c1c04804030f855400c4002c1078084540c80340d2021403400e61040d008407a906181c00a04101c0124140d0302d4045 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 311913003 1250 311911753 311911781
    0xf030801030b06061213021f02070311040b030a031d06040905011805090c011d1f0906050c070b03041b08060a180b01060507022b14060f0a0509010906060306 69
    0x10307194101880818031983e200c0c44010790001c0085a0900d61711b1485100160008040c0312410400441c074000743e9038030036000405030b40200010804c001000d24039a09041c42168104407400c621804280c80781507400009040205139042c0c20301d001e02010314a80da1200c0585204c1d100d6407100c120200801080c040c1c05001121b5800c141103802850103050311031808103000e4590b0360703013542c010f41c0c03052010006200f0320350b0a002c03030449a40344c10180d15105c0004010444a407155000064104140c98214a0401030100305581c41c80e40c00041600c121000b0b8006599a0741c0d440c10003000c4000748494800035480306103400200000c0000382c05015103d004030401910074400e80311400e00c4014040244030300402001003020501031400b6014040c0080c01c3d04d454001c1681881c506100d16414419001514a81c1607040c810400c1e9203a80d8006000000d1196040c8036031021040e100090404801d142c407071307000a245040a401c2150040d901a030700f0b12090b43c0701c0c688100580340303003015418 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 311914253 1250 311913003 311913023
    0x60c0708060703381207120503091f05040b0a090803120108120405090c0c0109080406110606010c03080613110d020d0f0506090c091f050706050903030705160f0f03080103 75
    0x103984144008010064540c09a161301c60304a02d0180000c0880c01800440640610b000000300d0051280d003480b9070038402c1002e1a600c0840d40c0c100503068210b100105603854140300061440b0b60004100c800ba10301040c3c1240d01c3d00e0012000300d66074811604050b000f4000403131091070860402d69454140c0311600252241b06440f040440c072640240e02c80d041c1e10419040100395400400401410400322860010810819a03228160990310a07408030f00017a50030f1010702c110200601046400420910382144c504800341c41c0208401805061213202e07031071021241c0050740107a8041410401000007103511000d80d02484d50094000440952000b4240000d8402400300d611440d84204401855403015480b061030220319074220500c000d030040c0142c2680d404280c0c0610b8010582a0340d60b40c0c01c1d0b0344802c40d180000590307402800303446042e4020700600c40015080410b1b90340700d240440b02e68003042440d040080320b0000d10640603140d0380640300d155051552010045040e01e00982e1102 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 311915503 1250 311914253 311914301
    0xe16080607090e0c160f1712060303030c0d18020a0f060e04090203060f10120804060e0d05420103051603020f04020f0c01141609030c05060c0708060703 67
    0x1641410f0115800407400d04e0030811583c40710156a179041440d4007414600c039007007030b21365606910340b8040561840035034008110070302d40040350782803554002c105501440c25400c00c402a2407050149040000304991035002d00614082c00341030114500350020500450b040d641d54402003003240078000c400002d81035010420150074180200100b03079502500400c0b00750341d2031100c41e00c09078000c2c110403482e84c1d21190028941c48000d210f510401e000e1490641c1c1e5501e00800940300704c280c1c01c40c3c1406803045003044400320b00c2c0071814644000f0303001116400040280701146000c5001041c200d2100262000300c444551041d501074140c034460021111007104020041c4c01001c801d100c000d600400c04000d4200310300303254014001c51044585803506211110001c1070a681c41501c0100d010010302d410440749528110841c44c415255040c030701c000c1130850711031120022a500401340030f10000200300400d41c2040124500409440f01660355034244510020041c09044c4020100254103070041 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 311916753 1250 311915503 311915519
    0x180b0310021b160915031202010606080f0405060403030506040902030f1c05190c060b030d020d12090309090908040e010f050901090203061e1207030303150e04030c060e1608060709 79
    0x243d02840307450307603944003501d02e8665154080c1c071210ba01541d08800488002001403604481c1003030380e61281c3c0000c1007840c1440e000a1003458003e00b50308990a941d000e00001c00c40100d8410703001509481d005c1601d90f99000403c0280c60030440003501803150100c02c2007000700104252007010841c02c00301207005100c1134115250f014003039212600c03c2d40c0f6000c2030000c40c0203071018200c040c401c520105070b1f0b815401c002804d00e001d0700d00d4480540c00403000040d50325800602c950450030001010050500c0c3e644004010700c0041c018510a645d444c66000c0038001c0c41c00079640240500001e05507550385450003820545000d100e4940164180c81c00070840780c0c20b034000d0302d00c11103015080381040712118019003030f10b801d220b100c0e50300805521030b16414510203002c40d0024500039180450000041e400201410b22190b00c20b1030b814280d81e040c000007030b900010300c00640d03030071820124205002122040c140007051580045a10300d003400011800307408200580300c0c01d16510781458441d40c40a603 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 311918003 1250 311916753 311916763
    0x209030304090c020a0b0a020306010f030c05040b0d150314060601051806070f0c0609050a0b0a080c0f0f0304210206040213110f0408070f140604180b0310021b 70
    0x650681040c0410301c1005000c2e0300c049001a140d1044815004080c3c5030003002c50029200d1000e40340e00001080349950304000d4108085003203103010045500c02550043c094003075401002a0b4650001c0e80e084150500c1d0440108d4000141180c14140d50b40c0c501100c000b1500b900c65103081c004e080006030658010419110104120404a402c0112010410400b603120900868032143c1c0145008040390039485101e000c1c05c45600c2d04001c150410f41040655905a4080380e0301c0b000030080c0d01c00060f400701c840f036000101100501d89440c1803c210050074091015440c0c65190040108020f010020302581844041500b00903c0c0720360002080761284030443c2c01a41101c4407000441d4030002c583e01c10001c00300000041810700c4c80d140017562a0790b21550081e801c90307002501c05d02c0700301c031094561070041040040282200720038101003800c501030b80c41032009090801610b82041e0724190001509503070000c0a803803101107040002c00c001e41042442c81c0313500c107041d030200b101d0701070003e4 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 311919253 1250 311918003 311918017
    0x3030c0a021519050903010f060e1f1805060105070615030b0108150f060d02122b0e040b0d0602030703050117010c0c0809010903050d0201061d0121062405040f02 71
    0x3450300e25808044405035210317030269140e140c2540d0b03241c01c550403601151049502a04442c03400340c4460501e42c0781c55500c0485020380c9920401107030410450540103480000075002900000f0500d03603100d0300181c0d00c0703000700700c2c0c09420141001e00350344111410342800d8050324454400b03001141d803502140c9903600c111100710743c0b8010001000c50b06c03801c0d0b10f0121641c0200001c0442071001913580c0407503040c4001401003a4103610000f20b40c074401b2081d00411664600301e03600d50030708a540e64402400f00141c007581500641c0c3e01e159446041d215182a20740a81c0c1000080d9a24100781000600402003441105099591031030901c40025040c0100d100003203882c1d40d0a0000c0034145c40341c074103540c0304640c2c0c64180104024000001102441080c000c40010340000412600d04002030082d01c1001a0001e6032210b9a030040c8003000310007020008041c0c10b0302c1400c4c42c245043c50524000c02017142210441c5016800a01d614541c0c0e0720050706440c41039070244030f9201c50070144070070b0b809880 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 311920503 1250 311919253 311919277
    0x501210302030703120204170a0b06180708091e0c0109061b020603090c03070303021506010912080d0623121212190218090f01061e020c03030c0a0215 66
    0x11880012034850b1a281100c01591000107141555034582301c1180f180340441100c0715045892920309111501415a80c07000c410b80e00c0a11301c0c0044494521000e10003007241007403080300c40c0800d044070010005041141409005803000c1120b080d0040d07a901e0b04600d1090020b500c081d40851540e02c00d402401e00e041a42d14401030354840f9031b01308040d40d0401401c5410070710904551440f6540c041110400850094010300a03540e05101c0c1284a11401403809060042c8404200003601d200d04003d1141b40d0040c4900f80c6801603010094007404884c4c0c05601c000d4406110540c169101e116100822201200c85186001c048401d15480f500e8501d002402080148103103260b0302c1510b040e40f03a003c40c0000c01c0d0200c00c1e1126002804a0300a01c20a03489100c140250310203030708011f040c19800c2140480510f02543c0740c044010844514815211519007000d800120340d54020031480350012002000c3e40d8580600e00350346035071400e004009030301c40e584204841040301980b10071189100c0e282 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 311921753 1250 311920503 311920507
    0x2190e01061b050106032d0201080103022b050f160e0103030e030708030d021903020915210a0f14012d0b0705060615180d0c18050121030203 62
    0xc141e0580341d8046405075484507212200c80000018002c2c810303a0040c0d44500d14105640104c3e060380f01c0002440c4c45004489603240845101603070b0801000d9044030740c11509a401c074840c0021180e11101301003289021014500c8070241040300c00b15402d608c2c0e0a42508544071500d21103c52100c044075071081000d407088034001032004c40d11600b0050b103001009000c9518032a594520325285030f00410480c8445940807504100861140c0e140c0804840149002d50511080c0000299190070f503000c151405100010001d0410200c501841103400500c4040f1705ca40c40d05944c1d260142407101d100c1c0e04040e00e80b0540c3c5e07024100070070640d81a01c40070000702c540140c500c0c02034a0100512848050200f196880000d40d51007420000c00841c0d1186c0e002c0c0c4528104030050142030008582c11076215242800709998030b490340c1e8070b20740352a01c0890742ca03502104281005c400c007005a4000542c1401d0014041004030400d4000718103c400c188100c40308240350320701d041704003a40392400a0040e001 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 311923003 1250 311921753 311921759
    0x6070c02012c0d03090b04060507110108090d080411060c01020715150b0c010b0a06030c1205070e04020f07060e030c0f0c010f051c0614010905120c2103030a050402190e01 75
    0xc0740340341d03ca1182c141008180d07220030480c0f000350010f500140005100003568000c0100c800903c03415a8420308085040781004e80d80c040d1a8401d483d501000c0008020000b000d00081c980170b10656080545075a54038010200c0407230103503100300c01c1a603a10500c4065240c100120b0303c07407880b22480c1d00090800060134460030103203580c000c02e11107a29640740e40480016944004841c4014a17040d240083c0c25649408064580e50384030403c000300a20f4042002565908410022100c00040b500140d40d10b4150540365441c0c003ca40028148519001104070707249030000007042a04069000c4421003050902d07070031790350707910b00c1c46140c0090807100d040c4c880540a00e0162110300c3d46c11251850101c5540c0e0b0200494280d5030043c812030500b60306059895812281400c0942000d440282032190b2121031240d0781e9140d1091a07024246042810700241950941280e05000a07000e0302d5984c200f403e1030301c001d480c0560707003a48280c03042141000c00400c9000c402c012181114240c50260f0702e = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 311924253 1250 311923003 311923009
    0x1a0a2909060a080915190e07050a120f051005091204150c050f0d02030d0b0409050309010e060f0c0d090501030b030a1202032b05011a09090402010306030506070c02012c 74
    0x100030300b004e0740a00c074a0b03401c50103002c03206225a118200310b03000ea44501100c0e18000c01a14007020781100700c2d4008040511460f01c0301140741d0103450045125520201715460005010f80d03070428050400c0c040c10a0301d8100142076003010303000703045090885420194030720604441384078601c20401810070407180441d113a4010310301880320038000d20941c0c465002c43d20b0040c1c10b2030004003000c00103800014020201044500c1660007542080d11304010452035543c61503a24465400380605010a0b010298495554032048443c417075607242540b07485480b801c5260f5a01c1301a000c014012880e80707440422194424802d840a1040040c0203296100150b22071a9a00d0303002e000000442c0400c10a040b508030460400710b00900c0b1a1400b5081041d80d1404002140e0701a00150004a600c1000607407242000301a1584110304403035049250710307a03200580052403142c1c4024580d000e08020072409903004011022194001c0e280d40e07000324141217a01100500d8840320a950301c854102d07000140c2 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 311925503 1250 311924253 311924267
    0x7080d0203250609050f0d020c0f06070519030509090703090b241e120a0203071401120606020606030c010e031f02070b091e010501181a0a2909060a 65
    0xe64590000040c2c0701e0551070348010340d00c0103c41611180d0210051441d03595081219517602c007000e1015100740d0940c0000100b8002982d1100ca10a500c08184041440414810091011301d9031a010030680068900900540c00110300d141c461035281000640003400790103420000c503030010340896281d0320300c2200040c00000850040c46900010a114683e0f01e41c4d40c107010420ba0181152203070300c9a00780800c007898640540d907001c603802030031418005840011725402940d0700d5271504080800410012910b22031040c070896a45418135800103426900824130a0084406406179031023505c0950040d1005410a009a9003550018000c140e418404449040240d040f0f002c0c05441c050b46070b01c40803103400080e18803c845400004005c0d0154001d40b1a09404041900003800958900b900b0b6203494008000c290454940742d64801010230360401030720404000c010311070101103840d840000d85da8100707485000f041680b0251074504a070600c60940b1a0540001c0500346850742d41c1d18111405 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 311926753 1250 311925503 311925547
    0x60703020f0301051002330a0e120a0e0315091905102403050303010e22022e08060102010608030408030304020409020a08010c020604060c050c0c012102040803040807080d0203 77
    0x50003440c900c400e4113002c0b47c41413007a440180d60455141c5265040961241c4400b80000013030501d40894604104801b18002c1d1401294803c0f25854059400302964144462084198103000b082c660800c1c5801d40b0300c41c94050380d80070084681c0040046886c4100002c8400060159846010341c0900e14116400c44a0301c03269202f5841f507210b40c250b0121000302c1564104841582000c001030010078050074041758489008081400481c2412203018044609854040c1c01040310007040d08004040004051000e81c0c440c90b80300050102090040c0140401e8030705600650820350300150b1280c000058400380d0b20319001075840e64440303500300401402d13100c4040342c204d5144840042c1034007081c0b10780c402c428025005400189880e14190045543c500554010b100c006e000288120000180001e800f16003070800b6a404107005440c90641d401c11180d0140e11800000c02040d5000044054005c07240040122001e05885003890382c1c580100e0081540103038414402410028040c2c0e10941e82 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 311928003 1250 311926753 311926757
    0x5040903090b0a0203090904110108070203041d06040612150c14031611030c060129030f070302091009080c0301050103080d05040620180a0b16020301021303050f060703020f03010510 80
    0x1b5048600c2d002c035008841c00c6400307440745602640310200071350308441d034154060102e1015525090400b041d0191102000c94141d40d4019010002469501e903035000700050900300741c40080780750707c41ca070203500003c21052841fa150705228481208a008a0f0386a0402e02d07442c22680c210340c0c805000c6448120000060010044a0030440d24407000c1170004000c13002903c03000e0034096042c2400b0062205031140c481072001c1140e444401d0b0f0400e11700c10380b900b0a070820201401c3d6103540341c084000e802024051036100d03110080088587e90841da5010440755110107680810b20032808040c202c840910000d00508020803800460082c1a8422a44188142c100052601d10701340e507501c2c900c00743c0e01d05500b42200051003205400c2d5061040e40c00d070300b048698416081c1405015405406183d03190f07000d48004581b07000071944e0a4054072651000f840180311025500d051095984410b602403802d90700944c408203403070b14424000c445480c0d20900c1c2051440c2d00c0c0c03400b400f058402a0807140c00b = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 311929253 1250 311928003 311928007
    0x2030603070e0f070207060f0f050a090314010b03060a0506010906110304091109030c040b130911061810030504030804030e0d171c0213140604030b1f05040903090b0a0203 75
    0x5600c02145921900540c0001261941d1349007074600a0300d00326180c0c00c60001c0c0062070842c0c070030040d80700c1e6041c0001e104918181e92200f00441c000d0320200310b2500006d00903030301c0d41c60300030310340d4015030090818450481c115040390302c458140c1d0082310b01c11b46200d80040c4400c101808400d000d41d00e19000b1007038074004c403450603070786240745400c40d51100d0601e0b07030030900001d0001441c9400c0040c049840c804690400c010f804002c0042d0910b602041075041840d2100c1c4841f080c408903001d03080040501400a030741d1002901c0201c83c00e403602810070b03440f8a1042040080045c881d01c2740500c225815101e00400c1c1e181c0c4e403000c0e08c041c0880d0034200d62010400c4502c000180800d0b11403100307102164446900d07042c601012080c54060000500070543c0706020501c400c02d14400c1c080100c0d45900340c0c04088041000c0407822a200c0c9420240580e5407402c02e00060078a0003442d40340c051888421581500c0c1c40750f0070401a205001006000604021402e11180c1c810000400daa20381e40c1c01103c1c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 311930503 1250 311929253 311929259
    0x90221060111061006030c02030c0a030f0212070b0103031701031509080903030703021e1b090a0902060a0f090b09010f1107120b040c090203090303040f03121415030106050d060203060307 82
    0x251030540f003214488145400030074108802a054003501084000030700296060801c2c006c02d455031400144009801c0050b181d0254450034001d0029601042841d804265241401e0800304184202031108900107240d4100d50b4003000c0f4001e030014180c9500541a001d088003160a4001820050405842c100c00c2080380080c0c80e5403c00c001c003801c0e4840d40140180d60b0124001c4d80003078004440318030302d6800c00ca482d890002ca6001a03407881803011503a600140d201c0e075424030003c0c400c500c4007c1d08900d000800c458a039811a23021b0444031f18940d1034810081d00c41d000050301d8007405c250b05022400c01b04213000e0b01030044841000c031607400411a23040e15650b07a1140d1480e00701c0c100669501078000300740070034000000c5a0201400d480d030010352030341c182450440d950307100041001d442403000749084070816100f110301e0a0601c1050801b80048a900c00c200030100b10255403442c0702032160f80740703c0d042c0d0506002e400d0450b500240400510340c0356460380f6000c1c1d0b01c0200307983d503d0f010381c60000c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 311931753 1250 311930503 311930537
    0x20702040b09011212030c0e041107020402030126030403021302030a090516060305130c0302010c031110022107051b070302130c02060f01150c05010b0d03180902210601 74
    0x460080c1030051075034419020909106000c403217002200300c00c142c14441c0d01942607801250701c0c000610207075070004001c10606440c2e1420300a55030000d5110340004000604280f4501104805201d422030300003c29400701140d0780d8900c5144402504407000c0c1e601076604407640e40c05164409405100421400b040c0d580c0c46080a10b900000e0b01e101d20090301c1030090300d81c18031615900038014565070a85094544403948005418840281088082c1c0150b07001c1510541007c10100403810484d202402556060304c040d40084010300754182150200c02c000360304803401c041c01780100d41c58081c03401d9181c102a04180d00940a41c49052280010020041e118000b9203138522a04600004480005d000000d062040107010321078554141d034010700806601d5440c0f01d24500d62403c0c010842404ea1030014050b003040481d2642c440b844052403c18160040c13005400c1009103000c003241c150b140c00e03600049028058614500002c0c846401d15509070480c0401d8000380141021340c5c0200c901162 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 311933003 1250 311931753 311931769
    0xf1101060e07180302060409090813080a120320030c040b03090a020901120b13060603051f1104241701060e1005030c070b10080a050303040507060201020c10020702040b 74
    0x520032071100030200301e03445034069081e500920302c50354401e0120740346400003041390040c0c0c0503028800d03039200c580c0010042e042d0700b1903880d201e4400710841c00b1940c444000d40c072540c840000352010000140100c000034030a11800c41140442e6080c2c01d02c40524506a40040d000100304000600e800c00006ca20b0701c0a0102540c03203030303425400070102c141c1c0c0c231b1051120784241a80040407002c480c0050718009000c42c0007141d481100541c4c220010006804c0180180440790b001902ca07010364114800706841c40e0700010840340350305c0000d02074041d02a200c2c01d9a0304c264407a1058802c1c400008403554005402d003003290b0748203444e20503262803100440c030812200030782c407ca0214610b80d640340314505040c03001401403041410901e04520309903074180060700c102c00c030003130601c050f42c40000c0d624051400c1000190400208441d0182900d20308550781307130710030f84090f603140c414144006403403803050003154410081100504941003d404251029402c02d600c00caa0003a02c030781c401d101c0703610344201c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 311934253 1250 311933003 311933009
    0x3070f0306020c010b01020f0601062615010e0f0f0105070c0b030c0a0201141b0c07090e0d03150501020c060a0519210b0f060901030b06390a030f110106 67
    0x100160f903610f04800d00750031162280300700c41c15504444c0002c04074100100341380781111703101e0074100442c201c1110140c442005a40b0244484502d003018802c40078460140940c030340c0001e807100c501c4204007108000800360120f00c283d40c418032003e9034032000d501c940c0140540c40e00c00d1440d010200d868504000e11500100c40c10318030201d01081c011160343d4240218200640b04480d4244d29041003009140d00701c8440c02075003021000090481c6011404200600081004480401c482081d0400041d16491410f0403180000d080c443c20380e0a040e04503c1b82000c41d00140c0042404403180c605110f5540c1011290000f400b00034441d25034075a8140418a400361410f50300d000d0303045621a1046c0b428182c2c046201c0e4018070700414442d460300c40c2d0002d15111181119402e03101d58500700102e0160404002850300100c01049101400b0500c4020014110503100d880791680184540d054008801503506101d9503c14103091000c03900940c0700704540d04080c980a810000c03558507050030b484081e4 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 311935503 1250 311934253 311934263
    0xf1015020a05010525080403080105060a270609050316060311040e010f030210110a08090607021503040b090609030f1602030303071709010b03030702190e0411090a050f1503070f03 79
    0xa205c030503666009950f82080030840c108141746050945008003051814098580202d0340041d41d6002503018a404481c0300c11200d00e042000002c01d034501b04280e8151103604042041c6840110f800d1401064805030300078210495840c1d185401c000320050510800351580c080d10411001c51003000e08020340d40a07040b040032f02c0300c0241c690320500c5050242d000e031035000c010400c00c148c000c030840442e200c0c0c1125042583c46460700d100c1e0000520920408000940c05508210402c0300c02ea135080280d1321450003202c15185a94800d091f5580b1004112894829500300308502c030b8041c0410f6001d03202c42a075882030816501e609601003842e5074801e58805010861070003001070814034003026039600c10344110003409501c1c0c03203801003540c5c0c1c09040c5c0d00a2080d101c1d0703e0f140310004100e846410007400c00540340c849504040c00c10816880402c64000d02800c0c0840010b002c144a501a9034000c40d0f84074a0384510780e80e82035628250384003005072180e00d40a41000050f00c04240d1003e00081d501039 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 311936753 1250 311935503 311935531
    0xe060a0206011a0a021b060c0106061e050403020a120c0f0e040b15030c12101803230f09040605120102180f030a080f04030c06030c03050f1015020a050105 68
    0x700c201c018007480d12500d8844035040400015521319400704540000380e22150360f40c14105012800104a401111480d16041d864680c0000b04240c2c04003041c0e0290403c1a80b150480003d00d0f022a00791095010180d001170340300c20300308900038042185503401e90040d441c80303858980303d07280c03155402072503404004e040910500748810302c000c014000d03401c034440c1e404000c40c0071000030109844c3e1003010301451243d5850780c50569110000d20180340095154807082002001c00c0c14131442800201d034041d07000851664001c0e100c80300032240c030b80450080950007030506000c9005494260300940d61240c002e5203400b4006141c0d11011541846900603200268545040d500c1c2e442480403501d080307a10418400d2000e08181c1c40204058410a4111003c10b948040302c03440e40c00e161103191300060980d00c940d0000260329601d60302c0048040500d80c0d0500c0251190707008007120040a0710354861000840804111440300c0804120f4400d8042c0199407029946031205030031100c040710301c0c0c5c031403183c5 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 311938003 1250 311936753 311936759
    0xe040302010209090403200f0d0c03020c1507120e090c0a02010207051f0b010c1707030c050709020a0905040209130b1503041518031d1f02160b04140409030e060a020601 74
    0x802d965100007c1c014006040c1092600c10075641d0b00d200d4680f03141400700c0c088c541d4082c5442440701528068001c0c10801c0c87c4005048040c03001e82c40098184d5010880909810741140701d640780d0b6090301c2000b44240c007903458400c00300265500c0b0580400c150365081083c40d000034002d000c00104540602242040300010704003080940d280d0400c130340d04002c180304101001407403030b420841c80001300511050300d508044c6002c0d03459400c4410054100d100342c01303001840382ca55400400c49480035580c0d09008a55460600c403d0740194075100d903108540b103294080c1700c00180d02402d0014401041020200340c41a030400c00c56209440950750401010b82c2103814032503500540c4001e06100a18825458494400400c06480c02d4810742c450100302e00c1d29911903403100440000022002114120300f02103840c040d544506200c0700c2030801d1410400000c46000c85070a54044540c0102c11400e00c2e0103c00c1000700034400024110140490041e00c00080e8840e113020b4400c0400c02d400800140d41 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 311939253 1250 311938003 311938037
    0x50d240f06090b03011e0e090a0c0e040b062206030609020312071a1527060a12030e030102040306090b1b0f04150c020916090806010e010e040302010209090403 70
    0x41076000314003884074942d010001c0b04010320072641103502d45402d1b206455144034004021041300e41c450145100c134074080c4540540c01141e070341441703407003030b64440407960750ba0000e001070b2007045034041c000c28403e02c0040d00c1c3d4185000d001003990030540d11643e03141c80c0024828100d4901d50030540d20b5a9032800660b0845c2003c000c156443e844000d007203410800c4e103640340144240203280369480b40300c00c1c202003601c0c0c440d5025036202800c40100619019001103401e00300350482c0c4c10b25440380c0807082c008145e01d410490083c009032a58001c0c1c16011000a4805940c20034030042c003d80c1540d401c00002020520b207216140100d841650907a4640c1048507107089454000125180301000400140d158080312908540803142142c080b140340c07914540007500d03220356000010350807501e0b003020440d10380b03400000e94641e0f8150f078680004494890034401e40e00c800c24019414400103800c014006285102d141a0b0310511a03c00503140a031841d002c1402c06105071421001302d9000808040c40d20 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 311940503 1250 311939253 311939279
    0x105010902041410020705060f0304020306061518120709020307120b0f09090a021f1209080a110a05011b0806030a050c010806010e0d0819051207050d24 67
    0x2048800039070a250922251140c000700d19602c0f0703880798425440984041d0b0091000800400c0c0003049103807a001590301c03505055008440803071090042ca40002c9091800700c08102d100203921440a0401103124000201ca0f141d10307480c260310041442c00254580720400602000d401d4001015840f400c1001010b000980e00c2e40e994168181070500100d06602d40d211512224001140c01c00c0458070355620040c00c00b8259030300070b07400c41604604800322502178107006001c01110740e04c180301e00d942c600401d004c81c0c2144100400494007000b0041405206804040541c200f24081d114901400e0b940e0608460400310703c0c503881c00e507521a090003260011405035000300254060142408039607222500d816640150f64103003c03060300030034030700d903c108529400c0140c00b60000142c6d0416040c50030440e04032100c01c103952414610030003102c0d4442d0080e58036202108072103910541314241d050761300d50401000550b010340d440030100d0400d07500130201d1081c3c3c40c03000f1840540a0500111080007 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 311941753 1250 311940503 311940509
    0xf010e0a031e0e0907110a0309051516080702010302041e0504060b03062805060703030608012a0f0c1e030905040e070524030106050d06080a0f08070f050d0f02010501 73
    0x1a440b84801e0410b440c1c01200d00080c410048522000685c0c5044d8192070043d00c1c00c21254a030321400801c41c080541010705102506c0046074070061801b620310002000d403140310200300790143c030240c0d8440092007135405000c08602c141800b46c10503407220103994a5250340c0003926810b40c0e0102e01003199080c00c2c8281405800c40d043c2e004e14504d0b040d00494808840c0ae110001500c40a107401d2551954100f6a5005800010b001556403a000d080003009800c42d401118490f503c0c201c81104c0071001d000002d2024249600621002c00100209443c2404103201c410148a0507400110014402c04c400c10b034034145240380000c0150a904000b403164056803c00c0b8051490404038070189800040c22504a4004954540c5440003000c11000386181420f4030003014600440041211900940a083d5650b5120710404c00766580322030055442c12195400b40031400c0d414000c2d0085201407009044450058445000d80411030782d42034500154041d0031400101d51000d0b078102ca582c280915401 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 311943003 1250 311941753 311941787
    0x209060c010c08010e01090902060a050a1e052503020a0213060f030f0515240f060c0d0f09030803060103020a0309020a0e011d0108060c0304020a0e01080604030e031903030e0f010e0a03 81
    0x1400225030110322b66100e1102a402840004100381040900c10706450105030810b40603e4030341c0b91000b44c081e206810012540c0da401c64034164089410001e8074411035002d4041d402003590110302c2e000e000c807003148601105543e1703455a0303002c500001c01c840b488004600c200c40d0013501000904005082074004030b4100a12504081440310612110445800305101c0241103a10a0028400507d0300109085015004040464003004035070020481250005150311049440b0402c1d410440d24112507002c01451840180040350b0107510079030103448040c2e41418002140300c0b45800080e0410403951100142c5e000d058014070992101414590070249445803807100b65050589090700c42030014205007190300084002070035562039406200c018622500480d5403561140c40325034072080b089074140c000c00d009880c41e005600b0f000940451150f405401c006003a8041d9070201c0c060308202c84c00701d032584100e040d51811a9021322030740c10072129003001403005400703a18010b80140400302017029 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 311944253 1250 311943003 311943011
    0x7110d150506030f0a06020903010b09100b030a0603050f01050108070501050408030306041113090c0e010f02061b13060e09090d020312071e020f070915090209060c010c08010e0109 79
    0x45814803a00d6900c000640e0109941c0c2e154400300b0302d8001800e43e440c00501c5290055001d100e6280e0080c00f02042c154024003500d00c01105106001805441449444c00d10b24010081220440d02554206420810110300c03160f9030340343d092801e4044441c0c100d49940d100d0041048640401c030100040c1401e0034001d061074545542680c5900000303104502894944002429890103501140c59940b1105000705125481d1903044009140a103401c03000303c1c8025808000c19800b0b00c0c0c4402034040583d005100f590340e0b0720001243c0c452104001da0b40058184095014000c2d1030007600050320b580d99844202030000e204000c1e4004000d031034040a41c00061281e80c120390301008403102861a24000002a21005000c84907182495400d01c81c1545180035003003040d41c04511304103e02803000c100c0f4201c0d03071100703207040880700c00259625807015000e40c104403d00450700580703040d400040000e410036010440e280d00f560402441e100004401d00c0052094240c000c1201c2d01518031040100 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 311945503 1250 311944253 311944279
    0x403081305010e220b1207150822030e030318090c1207050f13030c0302091005210304080d03060501170903030103030c020d20011205090a06021e0c030711 68
    0x798603040d44000c48074802c2c1d020610620388145940000d0228000071b0310307902e00c07001001d00050700c84426000d4616202030401800355003903c20240240500180c60684d410080505441c0a5540c110002242481504508444207950600240001912010021401c0e80c00380c0100040d01d02d00601c05481c0381c1e01803020b40802103801c600b10358019042c0c1809591144000143e1800703014200682c000074466010101c204141a8210001c4031320a54011145403508400d50001d0b110b64001d080c1c1007950340c4030620340040c2990724004100d194006482c07910b81c6400d411070034a5000311805012039100d00e4200841c1d42c0c019989403124a40f6040d4445e0703820700fa00c140d510b170b1006100c0501004a0340340300b1015907443ca880005c5140d1322800d0300c0c00d003403c40030b2404003400387c000c80c090101d402c405480005d20501d0050078440e080c5680640007800d0103603100030094008070030f40d040180e4000c1d0300c1911003400500401094102800560701c4090900d06000489880a0024010b500041d0300c1 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 311946753 1250 311945503 311945509
    0x24010206010e01030b100305070305100c03050412050f0c0102121605031b09150a031a0d0203100f0b1c05120405090624160501050604020403150209010c080403081305010e 75
    0xa6040d00c2d400b817404242520b600650076602c0081d0b410192207800741001c000100b00000030045210402010184003040d00c0c03450640880d002200c01501380c0304030207040c80d40300c0c0c0f2030002801401c0c1c04400d082d06000f4070410031400c9821901e40c4080d800045400c0c41503c666154007844040e01d030307241ca90320f107207411042e10341601448590110420408603100c140c40e5144140ca00c95100034100300742d12542c118100a01500a40a80340701001d0100500390503420003408100295401070010444009001f1042000303000c0600c2011321207644100c2c1c0d640a580f941c1e4070184a00700d110020f4164034090424506106861059111415080000308410b4850040c107607848007040350702e041c66940c401050030358220201401003105800042038519007400704520307a501801b40d0300811440d5209002e000807031007140805003c2d5032140c0800740c00300c034564009001d050010300d02051025490f64400c4440e40090300115010440405d030362289c81a0707a02c1280c01442e0929040110070f8022001c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 311948003 1250 311946753 311946779
    0x218040b010c1106090405090c0f01050c0726060106090305060c070b01030209070c12051305030105010605090607140d03051603151217030a06030203060a140c0903152401020601 78
    0x8001d00c0f2040c03090703142e1915550241a81d10124010303105000c245018014151a80d12440030140b00703000a0700810b047d54440d04c2680c0b4180f007842c006002903800c150b1158048400341c000140d100c8840e2840d241c8090341440514003c02e80d40e21121529403c62074401c5c1440b0005100c0e031041c00c4e0900c08400425001d4045074112a01a586254192130f581070855020120820151070704800b00850010b19501000900181c0c080112540401d0346441c00c2500f40d6a00b84655400500c0c00d102d204078074504440144006849000b02014080e20b41080e2418103a0509820340030036640c80030000619000310742500c50170110f00c0c0c100190368800b4007200313000003103000c1c2d80c940c01d050300800070410404102c691815140c80072541d40380d241807002140941000e0008900074003a5002140d60b402e0b540c015512a103019400e2106e40d40e41d100c0381c034002a0454091950f03d4408d104c070749400722152041443c0210070288240d154501651580c110351f0700300c1c5001c1411940008010002c480072018 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 311949253 1250 311948003 311948027
    0xe1e0d06020a0513030b061903051e03040801050c0d0f05070f0f050c0f060402040c020303240a050603041532040f0b09060103060b041b0c0201020118060218040b01 72
    0x840103881d1000c2d80000c442c1409118155010208001008000d01c0000c5441c06d01c00c0d20110303503820a8804075039200310b803441741d440020b0050303104603e50000c0f41980f01c2d040220b050000100c0f070510703540f00005403e407002a01c120001000025400c110054640100c1048070900d402c00d0140d410000b41c003d100403569042c003c1045024490700c2c1c807051090080718800040e040440c1c000c041c000810340c0d2121402e032800c030311551600f14214400350010007524401c010000da40342000705050004900300100c042c140b684004404400b04081d502ca40203580514014240e4106c10a0783c0c641d00c4003100d50300c3c040160300802c1703403800080d500c0030501d0481c1c0c0300c400d980d500d802c10f494618003032008445001005204030b00740000c10000b120009180740c1203a018880500001004c401400200e454001e409296285807120074403807076000f0354500d990248180700014840795440d81d8114040d50860003101c2c1642c001a2060904071840400301018030211400c0007038084500018000c14040780d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 311950503 1250 311949253 311949263
    0xd0b010f02151929030a0c06050304030c080a080417270307090501060206240d0b0423150610080f0406020c0a03120e0f1213080d0e1e0d 60
    0x44000744100500001505030121400014005040e1642640004d21034690f110901800300394030210b06460001850010705d600644d00c00e0403282480400c90301980000c1003030702031028116a40300090107000040220086a50342c04056091038941120000034850440c0c200603014001ca1a1310301d89001c074242c41d440d6100c2403103000f00303481d40860308118503a80401c0c2d80358500302c0005422a00400c00c2c0e449420100485600181045005d00da0165490025070f04800b000c030f031450001d00c03030701c0d280e58020340581008803440c1c1c000c1c4a80200380405c214841c00d2900308468884242030556445a04180101e8069200805e29180105841c4d001040102c1c2c0e010400d001c64248000d603411204000ca0315801c0c2c0f4116400c0342130182c81d64241a14006089151084c01c81c000d200c0407550488500002c00a000d4990b52100c4154403900013504c2c0e4603082d0f01480d40010b1442c410840308a00c04601e80350014914000803c01900d003410b445040d8800000b02d1900800755502e0404403581540a = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 311951753 1250 311950503 311950543
    0x31e0905220203070302040302090f090a030f050c011b0311090d0f17040b030105130b0906190f0e010603061505070303020307050d0f05010e0705070302030304110f0604030303020d0b010f02 83
    0xa1650800c0700c1d200e4640c02a10000501c418554180c00400c10b40c0c2c0252107540c010b031a00110b81c0ca0b40c00c401c0740c9c80071850700561444e1000a10403585075020858a15100d400e04800d030300c00c01e007100d130721812100b0001b60020382403000c00d0f01070044220020800001609000b500d034041003407490880402045118085034040401041c00d00c070704807000442e1302007500c0c0d036101e00c5280328a91003802283c0c4100ca20003034114172000c55005450b1b0801002d00303458101d0312800103000700d000c041c440c0346031280b054050108140032000c0d070020061000c0c03502c0d07902ca0352400c0c1d0050200c0e40f60f6001903081440303500084100c3c0c1e03004811990f49550600e40169607a54120040314280030355a00940580d04110680320a103c40d170304058180c03103d20041c003042e5240c04006860314460258014096041440001c010070452459911007a4021300482050802040050f03002d80c45500102c3c0403990100700702e18030303105a10904c600c83c102800e1011616050000107991a000e40030110603403054 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 311953003 1250 311951753 311951779
    0x1603170a0903080a050301030204060f0602030715060506360303030c0d020d020c010f0509010507270806040804090507091d070e031b031011070f060b03030d09031e0905 74
    0x8212000710045400c00001901d6055480c8000c04581c800c1c401a48200d0074a2800b250f220b0182c42400c04581c8a0740045140c207910b1365807038646001c0e28000342506507031000c0c00201038442c04010001c40c21450440c0d0b201c402080c040c00c46c40040c1d0707180700021480b42c18524072151000421250464440e1001580b148880e00750403000c0d02c82d0740d005810003400401c110241c004150000240707050224002e1025a4501d80414200e5400300c07017010010b1116105185044c0c0c0109856101e4400352080074803050b228202c4600c3c042d801d48080707a1f01c1c0300024040120030312510699400c0702107860f00c964854900a520007501c0501e0031103070b141003004d00114100a000b88003007003506e840507059401b9000041019030a02210140c0309019001c2c04c80c068490103507034410808040b04064406050001584902104800c03441003120301680d1600d1548036690b042000d0302e0600040080400e81144c98900181240040a1165101e0003900900405a900880d12405503070041d42c0d45446146 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 311954253 1250 311953003 311953007
    0xb040308070c030f12081b0316030f05040c03050f0c0303090f1f030e0705010302070507030f020d080f030115030221090c060c0105090d2a020d0501050703050601021603170a 76
    0x300d80d031000f0440d82e207032111142001400317402584a90030301d40b103116060307480d20650351003024801d00f074460301e901c10000102038003268040303080e1001c40c0b8030b800217040e030f41c1e4400b02d41100c1081c1d40c280d0b000700401c00204100542002600d4107040b030310016114003040740c00400d030380740250503000e0310031450300f00c840750319441e04210074481000b01007590008620040703020700204910034120301e4600642d000421a54001c1c0200c03400650b102e002004a40c1c6562602500554504d004980c09030303840e8011804154544040c2070300200900440b41d0301e5242a1160056861901148040c5030040c02021280034000c0c0c4004450300b45000484440d96800520b05d003800d0003903003000d030300041c0800c0564408105502c17007803103101050102c4416920a2005035120300540d280c0b16542410403001300410413001b00b0f00016148054141842429a07542d118295401156a24002607030359080000541e4100010251080e03441020911941161107440c50064088190203c5242c00103800031380c4d83c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 311955503 1250 311954253 311954273
    0xf01020d1706060f030f1009090510090302010b060a050901030605010e1c0201052104060608150a0c050d0c02060f1b041406070c030308090c1e0103051801051009050a060b04030807 79
    0x103000c00c10f03450750307880c1c1140d20fa0709150381611f461140c2d2038296000b00b91b008580c0300740c01089030810000c081c0c20b1100320400b80a0081d86004400315500c0b00d00f43d45140c0c4407103003d00404107581e203540f92561460760005084501c1c90388403604200103640302414a4948180d100c8d40c15882c0d08038545c00c101c4c5070006a9992151200c5100c0700080c245121100100420540b40502e114040c28007002ea91501101d91b5001000e01d2010403e42c03220200f40d4042090348111000151401c0150500307403440c07041b000325014903500c0c1000d40c11207010040300d10740e041c01c0250b0100d50036041c1c0c0e4540d025601c50b00414025030207809000e500060301c0300d00341e03903603601a0780c0d401e980624002346054680c64010907400d0b0545807c601d602c00e103011690189010700c05c0b0910340300c0649801c241607104da80110082c09024ac1500c4500e00d480c400881c0d851800c0c0621132242113a100711700f0b4000d190100f100100d401c010072420440e03150401c140700c415241000c80c0e040b02e8009549540701c41590420420704 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 311956753 1250 311955503 311955517
    0x604200a051e1908010608060402090609131b08061b0a0302070c1a070c0b12060d020d060c031e02040f0509181603020f09090d08100e0c0403020f01020d170606 70
    0x3039103c2d5181e82c11203120305421000d48028a00038060a0b584000c40350fa10300e0117407002907000003031400280e020b00348a5001d035031200450b00d450702c10b50001d446211010980d203454000d0130001280600034240d0400a058210285040901711044404211903841c081c8110702410036400060920a000741005210060310341c19980c0d0308a07028405407503145a124580484050700030402c0056010901803c0d00e03031f1080040b9800c10b0310707610802040b040200203502241e1141010400c8004240644100f40f0f07041002c0d1400204800308038042d4001c582c0d01c484501950340100001d01107400d0100c810003c540050b10182225150408100007403981075030510507a03c10039441d0112007070399000143c1200d000751810341000355680f050100c0131074100c948100703503444003100303040080c8034000782988840a250350584040d1a80c4144d800c8000c1682c502c3c80c6040040350500a6162007030002c0e00d0328409000524007003400d0040a45a000c1c41300c08106208482000900b0588035001102e280d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 311958003 1250 311956753 311956759
    0x20a0203090405090304080d140d0f180308011e0617090102210f01050103090f0f0203010216051b0108011802070302120316120b0109030b1503010e0604200a051e 71
    0x100d85001c1c03001540da5045440f51f501c152040082102c2e5042c0592a035040350120f0084840c40d00040c000444054144480610304140e554561603200003403205a034145284245c1e2081070303c0d4501916420719960608600c00b0126034801e003086000d0300310211125000303600c1c207010210355400114500a0055103c10040c0c6140680900704502d8084881889900c0750f42400480386d0321040110100c0b07650301c0c4002c000201c4190141c010880003c1f0a030900361005002518120942d010b030558486050421103246d40b0044402040b00529004031841030020310b0044082d62400149892028400200380c0265034002520414584240860600384004014081c0d070790600802d84603698414402400c001032a40999010901c51070041c80300342201603541c3d800c07803130440d1120030175050081c08015012843d414000c1c0140c50a01440c21b45100b51802746c110741c0b40030b0920081d040e040078032003500c46602809500c825a65180c50a050301d00c00d58102d0700241240c0e40c010084014500108e42c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 311959253 1250 311958003 311958011
    0xa0506280f030f1202010b06070303091704080c1c03080612070b0f0309061807060f11060103210c0c06120f0f05060f0a1a090303250b06090712020a02030904 69
    0xb0500102400100b100c030b01c55008880b103d02200812130895004003c041d9108404000c0240440d01c0f075045207002500525520b91400c40340c2c1000c45056006901c0340b50181c01001d0342441d6480c1c404001c0540c14040c0780078409240c40f035603008080b03081c028041c2d40700b10010350144000c114100034280250600903025681d070310a0f5020305900b5001211452942e21411001034190200c600c0e982c1c40780e0403604002c01015081102c16101012500c0744c503010031141040160300031100704089030007140209981d0501c0100c20251028202040403103030301f40b02e2151142c1001075001030b038030400c58015250940090003d007200c640900118010500081e08024089031a42c1c15680214042c2c141290321504c00c248043c18022400c09904c00c00d42c155442d0180791007000324030002400c3c0c842e4001c060717900d05802c03038810792001421076a516940118501281d1f00300030f81c8000c2150081c80c1110151400d01d0300c041c00070519410040c01c650f041e500440c95541450003041a9a0200c1c40180140 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 311960503 1250 311959253 311959259
    0x1d06060a1205131403090d060b0d0c1202030d0c0c1a070b0403110c01020a0b0f040302070816060806060c030318071505120c0309060103140a0204021c050a0506280f 72
    0x36400c10700070841600d411340420904508408004200d5924042c064160480c4401e55114400205031031121160840039000d15000000c0c65945100c028200b02000002280214014546801d8038a0310300001e0180c03034080d1501140302c1460301c008490680161145465406004041d54090b001c802404289202c0c00e0004040e041009070104110602c11101c1c440c19000049039140c40c42c48000e448502140c0201c2c8881c0741c1c4281c80707948540240100d800c05030356000c026190040c0359500030480042c550091240d5a8007903007046c1c000c00100c0d60b00c0d0030711100d0f40c0714503241d02c40a070205030402090410403a024a041c4078000060071051900c02c0002c0c01d08101612580c80080d0050700f04580700005861234184005403030091032044010b0540307a0840d507644bc4040ca805040074113510441d0300020041c0c0d9507000620300150b041c03100031801c0700a00e05550981d02e000d448124440e0800c4100101911025807160006030200840c0c241e4000f841d00402201e61281c225010216603010b000c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 311961753 1250 311960503 311960521
    0x601120f02032a0f011404030609020d0b040302030a0e0301020421170d020406120e0c150c1006060e01020703080313020607021c02091f0605070503090405071101061d06060a1205 78
    0xc02d0a600241c504a40b51301d0454011a120100c201501092800902013800407904035800302d0115032018041a4110140740c40301480c14000312000c80c0180d100180484955030700403910800702e101640294100343c108082c0d1040f0040b80000101402d100000030317018401180c145801800500d0810b9565110000345000694818002c000115400c00c051405959080c801c0404600c200300c007a1024080c55400c0001d409000307202c03601d030308000703208070804a4010700c0081c400010165002490f03c1c5880d6003d0b00c0e10042c510224150b4000841c20004070300c0200c2103079805071181c10150307020381d46480000d42c58058040040d4005001c0c3c5041c203030124400100c110b40500032511082c0030307600e03014803800e00e1100503521142c1040180d8204411401540a030440034411000d49082907444804501207810880d1894000f03202c00d048102064001c0c8035500281000b0020128143e0740d003410181d040c076000e404540184800685082d00c14495a504242640746084c248a00e007003030809 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 311963003 1250 311961753 311961823
    0xc02060105030118050c010e01200c10031b1206030803040f0b0906130201080703060e041a07020706020c060a0509031015120201020d03090311030a0507050f0601120f0203 75
    0x160714000e41c642100d82c56805000900034913241c0e1300400078454042c0b164011a02d28011502040c140003551009500398026a0100d200d40d1648a00805285a1510400003105004103442081c58a049125002c217007100121074440c464a080c80000d00d2a4051b034076000b40740750360021b040d41c60080b0138031081048000c13078030f100c00b8010005034201e9220001082e454000036a004080c5007032b0140c400c1c1c0103501540e21158400300f03038200003450a5482007910340407030080358102e41e2100d10406444d941c4a56020058100c02039100a01c1d0460514001964840041894900c0b8003c00b14660b242c0501c81c03c01c4940910002d402e48150709100c04c42c0358007400c0000b41c2e00e4903559401c070011030703e04032401108840c550164020942d510460f00203800401101314240c2c20060204031078138000504100801e030030038503581c071503550741c92070306006042000081c1c603540710313801480042102012820f030f01c520b000c0e00030303440100000c018800240b0700b1140000c04c61000e96054952104202c600718 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 311964253 1250 311963003 311963009
    0x1180308030a050709051c020a0905040302060a0c0504060c0b0c070602191211090918120a08011202180a0b0301090606060e0d02060d0c0302070503030a020705190c060f02010b040c020601 82
    0x11090195484100d0285c40b801641d010b0990400c0c10303000c18a44910040c0401e001803400134101c40032460300e44402c00241c07501140e050303026a00071000d12120758514891034142c81c14030320301f103410a400d02000034500e1940c08005822001c41170b01060700c03890104200d90201d64440390856442c142d10490000300340740001490003081e1240d86c0c3d42502030282c091000d02e84084060f25103030858a000b00300151401400d10500d0210781c0c540d00c01440000c0194042c0c503d4041c040744e0300d810001034002d00b00003050b08504c42c44e00109066400684034110118484012490913440d2a607540640d50014410346850540c0b40d801c0010f00c5007403000b82d521a1040d110555516080d16000c4014400e040044000007174101c0c8003003120b041021000e511144c40d000c1310f03142c050b1405180d9299145180c10a40d8071600701a80056584100401008010b40f06007030400da0320f01c0140192552504001c89105603014003c5404454130760350b100794042400c5800061080000c0c90121000941e035200c240 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 311965503 1250 311964253 311964271
    0x90f05060a05010f05040522030503190e070302010e1815090c0306130b190306020c01061203021f140a0501060f0c0f0204022203151b020a020405060118030803 70
    0x1022a84020301400b96034180c40f569070b0000c000d549084188001400000e180320400c64102500001d03000c0c006860649060180c1e503456103e0400341c4420780003050403e9882c0d03465142075040e104800307021860700122a024204a84400414030100b00c04e03540e0100e6a070707009484441009002007803858841c010b10b50076603484010f075403126138000d003d22003034070f100c0c2d0300c80b4a00d9002c115000b1544c22160a0010142526082e544d540c600f40c40149500d80040300d100c0c1d004102d0340e4246109200d000001d0030b0000000d48041d4403510060b4070340290482c001ea00c00d14000c01e828a0380f0302d98201011100c0c4031000c2e6081c500c0c065451100411083c000c03480020f04c0058164040c034403a88208200c250001203600d03c5082c00e41c02c2200a600101c10201d85510300055241d0300d41181300505c00440c010611510000380c000880c00894980410129072525550041404241d000403041e00c2d8030b0b415500050291201d0006031074030701550350601281c1079810404420000d0600286024001170 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 311966753 1250 311965503 311965513
    0x20301030506070c0b16030f020a020c13021e0c011116050c03070b0406230a0f030c05030709030206091f030606020c0f0121110f0909060108091b13090f05 68
    0xa0104c841d0b0001c03520141000c520035010880308080003680780c841400034240081d681d16400039003000d0f40c1152480e000960402402d582ca075007030411024141c117107140d030110f1a03d0b401c2205551040600c05419100303d03004240c03d03052801c02d621410307158040003103490702c0c0c25100d41018940a140e2404861600520040b03034030b03904000a480041e5084402d4460605091810844402500e061403001d180c01e20409040d8464143d80206403a410740d66849204243e40c18001e070a840c24410b010081000c10010002c10030360200414040d25811142c2c56500c2c090440020000b0022849103040320500600700507207030703405522140c02c484017502030702d070310611860400c003010301d000c1d107a0b80c0800c20100740380c0440c15480e4141d02c3c0d0007121807800103503011210628141900071100490109400061030010f0380390444d40c0c55032041c400d1802e250b15241c014010b6454440b042d502e821894000b040c0030000341d650945070b41e5580c603904da00700b0800c1035034100b640b403080c01d00c10142c03010f01038 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 311968003 1250 311966753 311966761
    0x61b12010923010e070c0305090d0b180616051b0709021e12130f0507030b1504150b03090a02090405100e0307210c061a0f042703030b09010801020301030506 69
    0x10075200c54103e42840080712590340ea002411b4566941c840303800c50030003004010340203495079a00c407800010fa0145428244503c1c00c03007886008a860351a07511580d0340310600700a510b000308070350444103100d40d00c2c0007510b407900d903010030039a5401c81c80184002d015100020a00864035806041103845003074480b204040b203000502d026116102802c4008003007a4006120f000030071310504078643c810221200c2d40d500741d13140d0608100390394004880003e01d03042400450038003540b8280441c1c40480d001c004104c2d1401d46001181000c0c400c0004402c070210010b559039100784a04000309030007501b64102c0b8540303860543c3e02c415503035501013130082c5000469588002c0000c10b54490550040d102000780c03c4200c00c1408018500303c5140800090244000c00a005401455074100d0880c065180e480d086104000062218581c202d004a1a2648607202540d40303c2006100c00b06444540350220b8050038114042c000300081c164010302c030349000156980055000354103c03030103078099407110f0b12 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 311969253 1250 311968003 311968061
    0x60d0e010b030706110c040b0f03060703020c01230f0405070b040609080609060c220909050a060e030a0207180f06170d0302040b0a08190501170c12061b120109 70
    0x8160240e042c51b40c0100515015420940d00403540c150004140c1300e5100b04a0000030302e0031000312841800290007142100c0444024003130b26910a06106590041c5050300c0818034503100024003106090100901140074050306001c00c001404034107500682c0c85841d5200034080000c540301d40000c510803000003d4060741c01084d0380d40500a1001c00e18a0641076400d0342c1901c01c14119083c000c4000c00c500010083d0b41c03440740614851040c00603220b0070b40c403403c100e01202c0c15811454525007041000c0100c40d5400f00390306055800200d1424038407000034034080010085600f40d1030040e890801c0c0421330880103141152a424250200c0380007000c5418120281d0240384640036400d40140712030403803140210380c0c15a00141610311006030711900ca03200020b035030013a40804007603c0508640100070b001400046079482c41612581c40a0301e01c08000c983d03482005005240c0008082c0a407400c0d40e0151701110b45413714494070f040fa6503103d0201800500390100c2e240c2203c2c5241002251402c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 311970503 1250 311969253 311969267
    0x120105130b0f060d030f141c1409100e07080d110601080a020307051002010b040f0204050109050102010b090708060a15020106050103270201080612061e060627060d0e010b030706 78
    0x41006400130000030410b039410781d039a02c000000a0180258500500b19070302c2c0d528040d1145a0700000d09034072520038a01d14034110b5996568080710741221404101342d4010008007400d903544c0410000a500131400403060901c210368000c0d22850240e13101c440c160036801017600307869204074425902c6699031140e0250780c5c0c0c488110000d40641142c0010055803501c400d40b4001c541740382c000418414030000028085801c1080d9401c0403a07804101842996400701c3c10310b0142500380000c0128a00d400000740c0d610760010030007801c1111200000d03012380c032003001c080000d20001c1911506980c8160003e400f030403460252900081c5803074069418a1a04542090f440008502c028180740030b070740046401c40300c010b124503082003c04040b5005000e08100841c4204004e01c01d81300c119507804e40c19184980c02902e103510500052240004054915003141410107400014410b08841d05010490a000380c032094603201c0d142c01345a696040c3c040d00203600a580c01c40a4440c0380f92520016a911 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 311971753 1250 311970503 311970511
    0x1008010608040623090a05120f180d1203230103081903180303090605060d08030f1306020d05100905011404020c01060905010b04170114060f120105130b0f 68
    0x6007181002c40c0100d1025400043c001d44030001c2c82c2600c1404c20a5410a980261a02903203503110100d00c0f0705000b418400c610000c0026000346103890101a40140c060189502c52001080100904403283d919038502030881507000d480003454068240001d0300070207e624004c484000e861000c002010001131301c3c24103996005400500b4540b20b02c2900302640d004071041018503a40d001d00b40c0c4291511a01c6c1c02080d8425640403035410f2852074034030166100030301644d000d10407600f0984009003140702a690300c0301e0b5031024820b0b156504001c41d420782110310005007540c0c0c80040c081001c07243d5608240d10458900020303103040d0382e0b02c1017272000300c6000b481482c200010010550381f8030300c1d040d00100091400840049075094485400908072038083c1c7c0071210120000a040042c418050080e800d0403039018020081da0310000f2020b1900c1100400c0907104010000480035117035a54010612140b030b410000300309a00d4907001c940a161700c1c3c8082603412a000e140007a0342309501c02c4c251441 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 311973003 1250 311971753 311971757
    0x50f0601032001141314060421060b0d080307021b0616081b0c0102060c0711010509011205090f011a0f0613031709130207021509030a080d05040210080106 68
    0x61014640800d11025090b40d0a00f0304021040c0140e42d26650018003a04081d41220044405207241800d0b2030003840c502c1c01c3d1103000300c01c280802c124000501d6440c20680e482c121280c8168000780ca04140100403090080d6132082d07200048105001d41030b8051441540641c00315010504e0040d07007185241a00120300307910120070020700d66a1a903600c01600002d00c65960541003003294040d068100ca00c0c2c45e0810740341d5203c81c213402201e60b0f04104283e00050f25403c1c4500d41191501c828a2041d00d0384205070511000041c61540c1c0c0e44907456008494201980c10001400e1078400d450304c1c4e142162508461b0360802070b410010441003004c041d1074902c01003000c0c64000c00b0030203201c8650405181c0f41205611003c0000100b80b82c0191040d031961000071a0390b54022032420022901c1a4144e0515814414000384005883d10210f00c10080700c4001d40756102d00054001a01e00040680c004000080110ba91201d500d4141c120502861003150304850b48440f4080403141e8020074410000 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 311974253 1250 311973003 311973023
    0x150115110a2418060903180602030a03020a05040512010507030b0609030c04180503180a0906031211160620010e0307080a0912140709051302041e0c080103050f060103 73
    0x1210441802e00841d902c5200100403d04452042c00c81c000d1512104007951800c0d16844840200b642c4401e042c040c1c000846101c425140c10700c840207540f4010703581d890b424998005000d030300e418003e60a603402090001d14000c186103011103658080d12042e9084d10111342843d1084600e4904601511004580680201105480203003003002070030700070130004007071850a03020102040081c0300901820440d009400c040c000303d4814040c0d00d900603030100380744c2803400030140f0001d2060041d005210013686050100a260000a00d04080306003147d500000041040050007540104425500080d0144440d003c4c0001c0387e4502c1c240d40008144444540080191500050354100600662a581e2500d404156119180e4101d00e50300c0030381c1900c01c140d6034402c01c040d00d1313010016070700502038580041c0301504140c005019030b6218403034000e11441c1c403081c1210341445c0030022045c90b01803086d024801000781c0f001c06003004900f070200b910f560003201e21110356568002031035412a80c0c8800031103 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 311975503 1250 311974253 311974283
    0x705060123011412041209060f0816021509150c04030803010302060a03020c0d110607090e0c0c0a06060b070c0609060503131a090115060305100b0a02150115110a 71
    0x121500c0c1c03046800543d2003003c0c80300c20f009100d590b454078031980c4950450b4909520140018041c10aa03038000c90802c80c201110620259004a0b1030303400c011103c1c50001044410b110581c14469800900725680344c80c03104000d540200041c400c003d0411880b2a951282c4a00201c501c4030b1107603000c017401402c0d0820040005050240083c40500b11603e07005003042010800781c1c0c20000d100e0249000907090100400d015a000d100d041d41007042c07410201c40321440c2024211100b84010180c20042c1030110321440c502c9001c0c4a08000c1c02c0d44000e0421015868401c820340f9031308005001e032003c0a6034200450618090350b80c0400395503d649a50f402c0d5580c4030122f194100e90400700715601c828100000030101d95418000340150b9442d800494901800285803100d4803e0b0b5004030205810103040c03002c0548204001c200740c030100740c0b000380e0310600480c050749480300300d80c90300186500c0a40002095036103520401c0312090660b642800070303000c003403910756070b803004a1010342810031822402c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 311976753 1250 311975503 311975507
    0x501170c150a050f0d06093c020c01090c080d2a02040b12010c030506040b0a05060306040b100503060112110a030911030706030203040b181b0f15070506012301 70
    0x240510402524001e0304c0c181c0914810021078218000c0036007055142c10302032200901074040c181601880c44001c4038040c1d10400056082007400c81ca04003201410a2007840902d160b40444580e141480c0090141d950585040c0400035903038481c404d414040c01803540c030708511074510040090411308140e4400800b2051400350301890a9040b680103588190301402d030b8961184120000c40c11400010b08d0408989014003500c0004141d148030714504100050b442c0e603401e0440e400e4450079034240ea12a0b5811002c10010003051a1590b8085102d1035010380c0303a54050001c611500081c0d07641000d6500440100b01607607400a00b00210b145d0078068252524483d50100c003581d4018000b5000f0020b0900103c1e080c20701c0d175044071001940010030030007071103245e81076641c000e15401e1402c00880e003010092500c81d82219042800422260740401c902c3d503407500d4107440310400800542603464003c41c8030a05521503d002c40e09400398900002d40300f203d07114480d02c4030f150300d54450000300d248001 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 311978003 1250 311976753 311976757
    0x18050c060c060a05190507050d060906150804110405090604120504030f2a0f08010e06040506040b0406020702031506180f06060c070f090b0306010f1a09060702130501170c15 76
    0x301781d1034103103050b400260780e1076005560041c8442d403280c60307170b03441d914940d5015512103801024a4138180305c03042020a40b65201c0b20460650f614181c2903d0b121031400b90010303601291540d07801030420f170a011500d000458081c0c0254803411000c542da07600840c0c161024001d511024007020f05480940707020541c0240b01c81d214614a944511f00c02c04080040e428011403a004080741da840d42a09102c2c00c41c0900c00c43d034422a00800a1034280360030f50310300d96a1030004000501138142074000c0b8040240e960107a0301b1540c0d008043e40c404c40980b007000c0702404411101144501c0c401801c040b0003448422449014480d964071800346941d4a2060082d507a2086c504c0d000217104083e00018055025864580900904c000114003825500200342ca8030300c040e004160300c0010103030100f00c5c0a05052900440324880c046080d202c0c000c2200055950190398030180d00100e80003001040303c80f1542c8100e042e200b44015826801c510340c030080780c1d5807205d0302c00207030070641c01044034000c0354800300 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 311979253 1250 311978003 311978011
    0x20301051305130b280e07051504060e0a030c09020306012010050910050c04051f020304120201120203041b060201020702060702060306150408060405011b020a110f0418050c060c060a05 81
    0x904522035001701c200305601410b440048500d05e50b41c031003125500c840705204020052a00b200c0c0d4a014455070001942d062150b4480c40061048404a120036501c444074061300464108c8100142e169844481c140690f00c229090b50004454144c00c004c0c1c4401c0b07003201d011034001c05c0010325501810700641c50042c240900306040d103210340b1025858400690017850320a078018165107446516200c1400750000b54664024001c641240b10041040c2c0e000080d1022121800b080440f1256640016100d5100c40c8442c80b034203900000801c010310290b411000d50441e0031850b80070801d82d0700c0804a00300c0c024130b640258008c20400809000d4644500650b0300700c04002c103105084070b00c0300b5540001d540f01d03a014081e42c3d0030010400c01842402e1042d5491075030300608040702d0340c013100c0000351240c4440400900742d9041644102d280d80342d1120604203031501410400c14020b401171222145c042191045841c2e109000e1101d07240d04200d000d403a81d290401d070082c03170103444050740715020303000041c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 311980503 1250 311979253 311979271
    0xa02030a0e0f060d09050f030306030a080a05070605270d0509040906022a16030b01030201050a11010507210c08180328020d080103030818030d0906020301051305130b 73
    0x10340e03804655500d40007001d04c40d2003050005440307042480c06904200303a0705208625034005104100894501091012106511000490351102c5800c4255002e0155290107041945403404005842c0300102402c05000d0480101c0b1242c1d690900350720b43ea0b808c1c0000c520000890500c003000090a09800610400c0d00c01c100141c100407040c0e0840100028101d05d03c504e2180007032400c40840b0b0709110015240c40c040f010300780c000341143c80d19000b940d410320000b4100000000c5000ea858403a10000701f00754041d10003417107541820034004000441c0c4c00c400010411405411715100950b900c182c01d1007a02644444c0701c039641c1c6c085140301c0e12425503044800e500003008080b5582501c170064403088a182d40004404400e03c1c00020b00d4100c1c200b0780e82c4140f00e5540014004290040c01050b4091200209400e05d081d94841a6086004241c89108503e040030b03914010021150040e5040ea035059600d060009400e09881c0709940e41541d907081c1000004140b01c01082043c0e440310361120240e = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 311981753 1250 311980503 311980519
    0x12060b040c03020301030314041410021e0609011103130602090a080327040902010c080c01090c090e060c040b070b0709170109031d0604050d0314030103060b10050a02030a0e 76
    0x2400104055520031599003000907800001031040641101c01c080640c2000480d03241080c0c1801300c20031002c500104443e02c29128400455441e0b8400c105402c15090040c0014405030b14140000303580382e6044d50400110350821000d04141b540780010b4030f00c17500c4683e07803400b1904203a03214031000707500446025410042403100801e1417141000101040030b9000742d440c1d400b01000c0c001c105085d4203242094030442c00d02da00c200250303901444848015400a002980d07032060461100d00401c03940400804030b80308904006441201c0f0341c000105205644103488840d500d8100c1e001051145005440080c00c2c284940701c0465851a83c80c0e5200c01182003090340745444030f550100d20384202c202103100342c4d120034101d810954005a001080c81f10400d8070b0200e500b042c400207070680220f0080328050b070404000b480c1030500c0740234184a030064880c0030659070350312030034a040542404507403a4055142600e410391550b210340100c07550210613901460401d1030b90b00c0111112640c050300d442d4031a141c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 311983003 1250 311981753 311981771
    0x10e0408041a07021c0f11040b0d1b150819180818011d04050a0b040905060f0f010308030115180f0821090907021501170c03161206 58
    0x44500200059a0700000540b10380b0340b881006545440107202c00302282002c802c000001c0c0840d0244080f031b591050088109401c2c06005c20000d024a80590b5886003410300700c80140404003041d9003040303899034a40342480e901d0340142c0788070b50b01d4140e6a0000aa00000107480c103c040400c000300340c03800060100d100906101802071040810b83c0640e6444d0000403000c0d21021051142700c80700400f8200f280f81c004040702d18030242d500f581d03503060185448000142e000603041e407001c080082c004004014000d064240f566640c002203427580c400d0481c010100b85600560150641207a81c000843d03841c5a003030407103440380b4071400c1c04400c0900c59074251602080d40200c0b6020081d24045486001503480d014000e403130182003d14801c40d40315038000d40c0e80711405503c1220400c0000b41c51076000d548039040101c0c50a01501d81200d045010b6000202d403e07049014001e41e5000c0f240101c1d0803405c480010180c54990b01147c400450030b19800030020707008548081494640211000209840 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 311984253 1250 311983003 311983019
    0xc0108070c21030f060506190302071203090b0a02090609040e0a0506070f1d0a0506071e12030615020c0f01020c1206010501111506010507082a0d0512010e040804 71
    0x200c0c1c0d04081d44000307441641c40e29055414851051301d51140c04042c060b451a060100d40140b10f513128407101c0ba0300031105240d0300d6010303804031011107600140301c001c0e024031024014020580003e044400c601d559000c00c280841c240250381140c03500900c4c9a15103592002000b005000d40d1078110200d0103403102c034001007203050003410310942071512a50500140d2000040243c1d241c8400100907940b0920034440329101c0c10034000c191141501e50701e5a07032101d030410100500e410b90303060a800001504a008008134800d048502500c80c1d00c041c0000f030744403054041802d1224200c1d000590bc4102002e03001c0c0351000c8086c0001c141030054494032507003840420190501207407034400581c13003540100815640194034491011442001d0031106820311444401a040980303503604000000c01c0c80d506000b007050403aa020804030046055203803400e01200c040368103c68182e00c45015101c400544507004400300c5840040c44c9609203042e0b0f08001c484020000c000d00203544440d41030202103031440c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 311985503 1250 311984253 311984273
    0x15012103440402040b010c0f020d03090b0a0f090e06012c0411070c050d0f06020f130320040209060a23030117070602150703051905130201030e030c0c0108070c 70
    0x1018808000400c2c58240140020f6a01203403e0504101c61040240c004c070751100240594140d04550ba15042c0304070b420111020300c0181c03c020600d001c0042c40c200b80c0c5030001258100b1000313035222180036a58907003035256030710750445055000c2503103a0b0303101120801a0032003004140c801c2d50214021001000850b08030760040041d454020707030024103a07060184400082000b0700d81240c0c2002c040a0310b545504004002d1500284030580115801600d100c085094540d01201840c3c11540c07d070b6641452000b9445141c10040b642e40f80d01c08098031810710f8000c4900d1141d0281455241101c0007070704a82480152210701701034070000d10ad805484440100540c000c152501340032004800c0c4103215414942e0f0f80d4408800c2d903008142003424800c0b10400d041d4400170380d05001445035103810003020032400041d01035a65034501010400302c0f407412030700030040b40d000380d81c10014010040304080e5070703100b501c91400c1c41c0d074010f0300410f10540c81104070300d5001a45140c00d5420303100030380c1c0b100d04030 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 311986753 1250 311985503 311985617
    0x31b0f111002040f05030c0a080d0c050a120914010206091b0f19030308180715050c100e07050a0302030601050402030c0408030c0606181303120e15012103 68
    0x7000c2c4c030181000300b032600708100c0e0f102d040101c0d080d15040d0b01c0d03e0030940d82c0f100c01003512010312030105d09102c2030000074450110302a030824a90f20444070142d02c000d200c003600740a840e6a12110080c04150ba500c0050403901c200c905800030550f015500714080020020080c14075032050101d000465036444803242d89043c0b04121060003446815454050904100149290303451000c80c1c0d003800001800094140890300744a4011078014a401d078215810720600c04140210300c03c480c000001390031a42e200c607203911000415285c041c0e03103410806c03520b05414070010750b06034403d034014051840d141d4010350b04070903100c2903130f85401c1d0340e00003140c107540220443d960150004070401280e400c00c503002e4240c00560090307200c0b0a00c0c18881600280e40750710000307010400003d00389482c507034182d4020700080d1440c80c1260b041c1c2000e46070700c100c520424000c8513400b0420071241e0a83c1080c070b1001c881c03003e60644440907040c3d14040900c1003040240c03803e6582c0e800034106450300b10b400040902742 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 311988003 1250 311986753 311986769
    0x31020702040612080904050601030207060c0e010207141e03030403020d0c05150910030506011b230a081215060403050604030306080601050310020705240403031b0f11100204 76
    0x4450050040000b214500c0d881080602c0c0114001c8001424190031181c41801c01c07074000130f15071a0000100c0080c0100f20b0300400c03261401c602c1002d0140c0020002c80300308400d9088920700764540c9001218001c060164641141d07501c4100340b081403010a10069020024007144d00f8130f50f40c1e800244c0240040707982a42d0903070070348070184a10308111003100700c4041c6210081d880c0115100206182801401e400010140d650340402c0c0f96078407800c40c1d03d6001d04c0740f0b6000c403032400d01c41c20500c007200783c035465a1101c03018103040070075891001328204491070382112405041c20350f00368850500c404003c125500800511414a40d01c0d6900390140016600490048c081d502e001d10f00a400c0b11401c1d00b0011641d0300c9140101710300e07a00010035900405d009440942c81e0802494840d1604042c102101d2055142074081c045504d540103145118034081d99042c8500f008443d4be0403402d0400d40341810004400820710b080c154020388040c01001000342c101c4241d4008180c418040b41c01030380080070 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 311989253 1250 311988003 311988007
    0x20a060506150a0f031b0915030b060d0b030f010b03190f020307030b0603010b0420070c0f0303111203040f02010f11100213240e061e30063102 63
    0x140540c0c5481348418417080309a00c1242546c3d900b0300174152100340d104844540c0010700c81566002e200f50080d902007000541000d0700c6484890b0004040e1000010705130103031140b070301d52b24400c0505015441111b00050050b0070159041003d642040160131030a4ad1a0043c01d04860b0050300c00b0401000194001c02040c9868140a02014207417840310030414807540c100b1401c001100304c003c0000c0c10404001c44855514040d03450b0004088200d039101a10803011010300205150b04514604002a411700070350356846900740c2001d100740808e440190020803e402c80710010750044462120b420b98070300340582914503080c01203142c44504001030040940100e60b400303044d0040c00411002c0c107000e4040e0902d18401c200080c3c0b41861030a0020208001c1000c10451502c510045514071090401d151400351020700d451503942d88458501e02a540c2072644003030510802d0342810700c0c0069138000004035515124100300a000e1240c80110503520608210190b070320b01504100a0b1507150728001d6 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 311990503 1250 311989253 311989277
    0x1703180d05030f0c07030926030d060302040c080c0d05070507050105130b2404090609020a0602060114040b030a0213180507050901090506010f030c05040f0315110901020a060506150a 80
    0x66005401030004e4100910911200300025080b03404c010079146500000c0c510b00880b020b20328400316010400c403166000008012481c95443d810003401d6a000343c3d4180029921a84d00f03c507491000c4a02c0180103509100b4480010b06913080b5a8001002c2d00d05941800a151a07090840340282d80040c1f400b40c1d9011443d00300041d0002d030701d510224916450034101c0d65500108011141913140f40d200f155910940c200700b08440d40800100f5402030007502586403105c0d40a03603110307402e001700d5640c640c0e1150301207801d25240c0601981c055000e0040d2076103400322340c248201584002034112200ba10385002e010014412140e10400501510042c05003510b003406003c084001a045429034a0070a010444180d0300443c5200b060700751031800042c4600d10302001c594500442e00212180c0d45d0301c0c80000240043c40c070802c0710044a04408004a40302c05101140511400d150380c1c1c05030f041003041b0404108140c2c030903984841e0107080700c00681600240d0a14560000d4000c00c04141022045 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 311991753 1250 311990503 311990521
    0xf0f040b0f0a020705150403061d06090f010b0301090f031b05061e0606031e0703150e040203010b120d12020405040c0c05060f0915041b03140d0203071703180d0503 72
    0x400020041580c0e10600341c2048004451b4900c61404050610313070700c4030000d0185403100e02c1d840c440074400e1020340341d490034400761040e00c4e4138004440d0462580bc040d9120072502d0103205803103117170b944010840541040c940d000c1c1d03400c864809429448803807550160703001c03500a0000901c00c400d02155000c0078400c1a01c402d51681d07010b880f480c0034003401d00412600325000c00d80d85a1258244e02e0f440010350340c5030701c101d020b002c10044070181c4a468400010b880c814203442e042c01917108500910400b0b20002c10b200751040951203400c02944500b114100e03c0740110803c2c0050203036014003520b401d40b1140810180c803103540c206000100e07105207440078004103018007600920001030325612800d0010a4580c1d5074032403191587c4400c5d505020604104a0319410029110012801d800c0d140e41c07810061000100d007480c0300468017550b086520303e80d2003c01118000ca030f10030398030b801000c0840c021501542006061121a002d075801108001104014401d1002091f95549599140040790 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 311993003 1250 311991753 311991763
    0xb040f0213060c0209131b03110909010903021b042a080f13110112090f0c0602010c050301121406040b01050a050402040e061009050a0b0d0b10050f0f040b0f0a02 71
    0x50700f00000d1500620043c1d42c0c0b0880070317811501080f12103400340c0d0036042c00340400c1070949600c11040b0748014000100031620500f2440e004040724940c41d00d5030f0314086a400e80722465401001a00801449010100b10300201c501200014100241c500486100070440301c2c3c0080032104407140b1255030200b250790052443d0b500c11400702c101c840c1400d104c642c1003101d94401d6401403138008001c451030b019034450390000c46d00310003100080c4400300c0709051007828101c1006083c1c07420060104040ba42600500814002e03c0e0305655080c0703560710f06600e07071001020043d0215511140c2203030804403038008200017401907005e00340c034602c0c035490039040101c00e901c55400240114014031080100180343d1014070f6000c4026119140740300a10310003110300340e0746ca80003d54803e80c0030b940840d51042401c040c0c81c00090780070b0104000303105003080040d80e40d403c584c2d54000607000c001c200040000100a008a41080b070f00d101d041c25146c1c0c8000944e50000d0056202101002c208504042c1c0c0c1004 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 311994253 1250 311993003 311993009
    0x2040f050411070b0a0203072a0b1f03110d140d0f090b0702010806030f120903010f060308031306060b16020423060f0d0f03090807080706080f0a0b040f0213 69
    0x81c1c0a40390090b1561a60720b06080140b000c09406e0b0301000103030394180100404140c0c3d40020942011000324030802d2200600a003200ba1091a40140007900307030784031b440410b682094040c900e4024140345580f41c030364080c3d4902515811204409900380010040450040300317074034503800381c2001c41c0d1500d401400400548600c07030030003100e40010070508001d10100e801043d020701e440303001690b0b1000860720b00100030008540c9442800c4003405103468040c054100781c1d004500074441070046080641c203a94507404023038804213041010510307040c44462824003192107048003040c02d44c1d41303820070007450704015032410b42d000c110200501103103001c2c41a95541d505100d025400714002c0820207a0310321000302168000c0c940c4007214200740c1d0b03900108105003030740555182c40001092900034090b44c4179102d16011803240f0309001ca2802c01c04202c80083d01c07041c1d903034043c0c150b561820303201c0f0106010780380441c482d036105203024191310356006940c522002810301507a612028608020369446c154 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 311995503 1250 311994253 311994281
    0x60a060e07090311040b060c0d08100806010806060904030c0f0c090501061803020112022a06010f120602030a0b0d0c08060a0207351b010c0807021e03040902040f0504 73
    0xc1c2c0c10700024131001941070b101c16065400040100305200421041d11902d10b0740c640c81d21540207080c000d0350307111840720304c118150844054039640c0d03441c910360389181c00c1c0134240c5150803450024907203003441020958024000d1600c09004c00c01a101c16820fa0a42ea2041e12000458102441240ca080c0201801041e003442d011041c5000229025881d00741404001d041214410415503007034056010303501d040c00c00554140301c00c1a00300c408107101d54502e0442445005040002504205c00e04808049a4941d4201601e40415543c0c000c0250f000900b40035805503542e5440c10a9220002c400c40d02500c110065014581894102807070218000d15040306d2600410946001500304c101d091108500300f004080d0b0080601c81d9154241c0c2e90799008540b83c500459256010816217a101400311040d000070000d508650783e003200d0a10007141d80c2c90147e031081e091042d144442c5019114410440c07001d681c185615601884240da0090b03010f03101802580400744050b2030284500c4590611030 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 311996753 1250 311995503 311995517
    0xf06150a030f121e08040212010f0e06150402030705030c0306130903050c01050f010b091909052404020406141303050f030703020f03131503060b0403080c060a0515060705030705060a060e07 83
    0x10704c00080003140002d000131301801c2c1c54180c001c5080e03401d401084400309029401d00c4101e00b1070f0f581a55804048549090b5806c8100b401401340c14980b003200d0040c40241e403607a02d15912400a0940359001521207a00032800008840c2114441d224040c40745100380c0d00c01c0ea070381070102c1c5a1405d4840c0581301c0e0707000c1c46518004102d189006400c40d42022010795801c455000703c0101c07003001e007005030b001c1d054440c104420045540820940c4540d50341010070b1080b840c510000500049000e0b41c01a03101003800059010121501180503010a00380303580480740c0d46490380e407058108012518030610725030000c40c5280c20540c0521041021260700c0b001181802c9180c95020440c4070380b0310074110704010100028801600c6138000c000908103c215403550789644e4548481694041075140e5101c1c010800420410701d050300405001d4030808404821a4640c1001c0003401d0340f1469080304c00340b10810050000038030a21000c1c0c414030150100003200c0307140c0380c80a465440010890010000e01d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 311998003 1250 311996753 311996807
    0x70b0a11071d062e051201064118040c081902030f0f0709030f120905060c120a0e040e0733140d1407020f0f06150a030f12 54
    0x4201d040700c0c0700b20030b074801c99000c840c0030080694080c0318806d07812801501000000c01c500b0341004009091915001c0c6010300da207900801c0b04060340c0111015040c4265000380c030407801407800094407003640b04421550004003a10002001c49480301d4041c030200c0c0c520380c10001d00701107060741210091440300c825865071410607150060b07140c000f8210190f1000500201d04000e200307e0500d03001c0e66001c1032003259140a4149078100604452070a400a000e14901096500300136007518102c000b54801401742440a02c0650f0898115034010004c00800c044024142e81d6a4000e0030b1208904001800310f041c140440905182000102c0810404140041b560f000c1079800d6040b94800f410710304081d108204000b07882c11ba00c119110b0100307803410302c148404054005445c1c1802007955400300c480240c00500ca440d110340e400b180c01c00700c40c3c10940000300803062181400031b08010003404103070603948a5440c45000010880140c3e01e007582d41042d5a03a05401c1900b4448610483c05d6082010b25 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 311999253 1250 311998003 311998039
    0x613062d060603091518020603090606040c140a120e071d070201180b0a0b060c030c063303030c0a030203040e060f0a03080a020a02090a0b090a05040302070b0a11071d06 74
    0xc5e075640304c1d030b00d0030340c6c40703100521801c07103141490003060b07004000558a00b00010000d80e152410b4402034030403486c021201000da4052151424000300310036110f42416540b11095a5041e101c4054000350354648046071803100c1c0600140003d8600700c510b82d081e0b808055060119200c0090400c0d065a00d0413003c41000040040d024060f96807100500140303035102490b48024192024035250490800300305020704041c040b010703108080d03a1100b201d40c15036542406101c1e00b40c000c4c2c00780851700380081c00340545060141c04968400c0c005811280b61610001c8842d03e0066200001d50044c0c001003414000c1c80326180340207802c08000c5a0403103480ba850750006010a20300d1000070320107840056208481802400b0380c0f4001c80e001003c3c6c07002850a00c9000340500385242c800c5208030740d040c0000d100001284181c41c09660103500902d429410040186881d902140700107007480b8031941312105112041190002402c01c0800c7c1101c00c0a850b032900c2440300f000f0705600e00c6008480107482d0450307 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 312000503 1250 311999253 311999273
    0x30103022112071406040b060d050109050f030408120f0a08060409020a090c090b030c03060f030703060204032d0b0606030a02040f090603050c06030403020613062d06060309 76
    0x180d011201d088128512a844540c8503101841c500c080e4061a9400010301e50300c84080c00c00513004105100001c40701100c041d44442086400a22280c42e03070340494074505180d50601c0c0c245100c0d000002c1e281415440f0720341f4050b11610314030621b41c000078060010010500024280341c0c00c00714003504140403a120315100d030085043c88402c01810000041c95982d59401903207100d50080c040a54683d2240580c4014007040211000442d5224000254503451001203e10034000214614255210341003045440e42c0c2d100d645507454031502401001081c4284000d0008601c0b85019a08000d6030320114460f42060040810003801000c182102043e44600c4a42c1c1c00001103602e260741e9034400d6103a800902942d004000b440011840c003156290003507100340103480c000e2003243c1d1002022000c209251000321402001070300200040b804c0040341120030080c0d41c1c818034021807808181424a88070000341d203255041c541541800c1421080d06200e410f01814940c50140030280017512154404 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 312001753 1250 312000503 312000509
    0x307030515060a0309030f05090a09020d24030209010b120f27010f0501051c030f02010b0d030e0a08030a1b050a020405010806011d0402011b020a0f0b04090e120301 72
    0x1158903200010765141071001449807411004055903211050b101000707004003582842200417038600c40c01d00780f00c180a20f09484208200601460166003000c2940000e5085816400303185900d518941440300301c01458001500380204103011014503500400c20145010f901055451004000c0503010524202000764000c0b60b076100320b0000e40758400d5402004040e840d40c005802c04d01e011290b0400300640085d084e01560440c00c0c8140e0740c03140100f084038010b10001d081c0b00d407020040800064000c9001e0684160b860000207021000d14000c59140240340c1400c40004810b402e80320000d18194941e50060040c0031300440c100008075801501c00080c0705040c811400f0b86e51000740401c001003151800007980a0418040c40d40d5560559680e01c0003070064040c0f0381420280f5540c00c03603c0749166481250140d644803042014810200c041c08174814080c2d8110080100106540c001c0c0305041e0003c00244000650310b42c81d00300648111100c20b9a25892134100c5620501440d11400a50703040d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 312003003 1250 312001753 312001757
    0x70206030f1302121e1902011202070206040308040603050a0911150c030d0e07060f050d0507111b100806030c1002030d0e0304091a0307030825050d0906140307 70
    0x40d1101c0b100d0a10154203100002c0d031280c0300d80401e0340c260b10003288090b49203840a6001c043d000840080039142c10300201e0302d0040040807142c00004d5072194000341040c00c03908000520f007079507039004249668080e41041c1c0359017200203420000d0f41d9140c0b1500c0c1d4840304c0c0030410420000165522403c0484c581d04040c4510010f28250300c6a00c8090111032510807064102c9a0710840c110009000c1c1c0a007a0220029000b0140e00141c3e0500070000340f84411050b0b5a01c2d450100c80900b820000d060141c400b20030040405200545117100b0400c120142c8560340900120407045810811901503d20381c08080040aa05104640d20000769061951104031b400380305003070010404a10758092540715802607418683c070714030003180200003442600e151220a10031628084080d4090380c04105005d90140d11504c0208046800180500364a041c0d80c0e00000d600c002200540004091000041d83c1c40e40120032284650b68010040724000c054030709201104030301d105240d030b00c0d0303010050009003 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 312004253 1250 312003003 312003031
    0xf04020306060f0c0c010905030a0c06080703092910031509050c06030403111507050d050604110c010b0909070e01120201170c030609010e06060405150c0307200607020603 75
    0x1982d600d04080d503007144141d1075116116000702c0701c0c0035961014070654501081c10b10601044604001c00c4034520b0382d0300640b4121441d840c140c2d0823034500f4001080d0b20209651040000001007450900d0450950f0713101c4152102c60403a5008a0142d6001e404144000400002000091380c91680d0040b400c0e60400b0018038400307035050550900040c0013485603c41e42c00810041095000b41085c000a00e001e812503442e0350000701d14050001c010b46807500811004e004541604245800c03480d030241e4042c0010500c60034200c6004281c0d00b000744c4484460351030b00c100303046500f0501035541d03005084100404007585451564051070b0410300405d0710821180100388250790149034002e482001c44200031115244c5030f080c89195030420764145200c3d003ea080005211b00a03a0041402a02c00500c81c42c0340528140401083d00320f1b10303090001c02c0341c090001010070b8100380080d00c1120701400c1c0a00c0c40f07291658406030000919030b0110701c0740300b040c000440980c51f40d1050301d42c803030760044a103e = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 312005503 1250 312004253 312004261
    0x30e15040501110c0714040c0504030f0f05030f04051903030c0b0c121003020f030f07060c03020a050d030e070b030c09130f06060f031404110130140708060f040203 72
    0x760240c0710484024011450020f40b44542901c002010b07422508000041d40ca00c4000c0f0042105540c584500b1400103a8180014808668001140c44c00340d88228860982840150384050441d00400307459509094089002c200340d0a002e2501c40c40d282ca402000707d04142941ea02510401c480c51000d06a461000d0014203243e08880031200100c401075440001c500e0301c04125040e003441400124003664030590960914100000d6410392010118040d180482c14108110b0b410503c001069003103210b018682000b0840c14041d095a42e1141d5501103454500350055134a0620f4590062861190800803c00c21440f5081551700200f41121000e1001001c02d40d510094000d042c585480c00c2d20301031000403251b821a07003045182440c0d44040c0401e103c006001104884126406030803d4107441c501e07d500d6201c1d4000e410b2a00d0611043c3e81c102903c0c55100c81106c400d407078295809507071034079941c98508046520030740c0b180381c3e45010562440c00340041240c8a2012151900031a0040041 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 312006753 1250 312005503 312005513
    0x40803040605100f0801020403060b04020712050d1104080705090705030118020a031e090204051006020604120306150203070516120201030b0a05060d090614061f03060b0309100507030e1504 83
    0x50402130410400c1000c82d15140c561050003503020380300c12141123140a03c40305442c2058000d4808094100d1010401e280c11524181c41d268001001d844205646079403444002048101800140c503c010092041504020902c001d00e03c000d403412080c46024001003281c41c80441841c0c0074000301440141e10f42100b03c505030040d041e20042082c1c525a05500891110541e0340040030360b50085400b8000742c0c4410501194000845c082d0700c4c016000107000501082c0c5000500504144500d000901d00e03a40c3c02c00c0280f55040441d00c0c90040e040090780780e0034060300700055070304440c03180301e9027a540d4901040c0a000e010b00140c000c0c18542c030b40200000a07501c24a001004142c0034101a03a84c0440d0f100f00c50060030b040c00d085820900d0302121900e060450258184601d40140c541080c104282c00c01350550001603080c00304040e2691408038407003030080040e5024101910092074a01a50712809095580c0107114008041c41e05107000201d030800506082d400004600d1078003140c68604003 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 312008003 1250 312006753 312006781
    0x510090503160f0f210f0e090408040e010303050406080c09090106210614130c0f08090a02030102040603020304060b010e09010b0d110f1902011404080306030a02030607120b0108040803040605 84
    0x3e0004130201c100720040c00441000f560070524949000c0c00c11020800090741d11701c91001c10800051201c0c0c42d200007609241c000d858120b40103404650605503241249014000c0980048000400121f81008440d0300603c0c0395401c002420b950f541000343d07440100748070300d0b01403082d0000c00c00094016507080b44620910b6581c21503800c414050aa1515110340400c820410801d01032150991804c002d41e06034030036201c101c2110385c0ca02c1c1d0b0b0041e1020f005c9540140252180025002c1e0701000c0c001a0b07800d2000308001c0c0b82603100981c40f481c1c2801d010b001c450090750a203050141d03009044038141d03940c004880c19180c004d1803098440ca13081d07103074a00070b00d642d1892001601000840384000107030380001d0010410b071002140c1700e42013400c0089007600c5022003250200640100842d000502c500d0266601c00d2000c1e0807102209000e800080c5410f10556110001c5400c42454800c103084600231390411003006c0c2400400c500b00386d03803055000e100080c00a13052582d00c1c40480c0503400c40b120 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 312009253 1250 312008003 312008033
    0x319060902030f070f06020718150f031208010b09010206010e130519020306010b13050f180403120b1002060a0902010c0c0902043303051b0403060207051009050316 72
    0x200b20f03554076030a0302e40b281d6141c1ca103000340d80002030000000159a403000540c3d40030f8032041815440304102d910100c1d03002e4003249503013005201003924082050007215150b030008601a0f040300380b042c41e200c10013034688201a005034070b45104c00c011121090740c00185890440346041d05994555031488000200001c4198004001d806000d88200b0710f08035503d000b1303030800c2c001c0701075401d01c0e42e840884640340d03c202901012261881202000140740404248451550191402d10991100710140e088440c0480d000c030007107600007040303809190852241041d1100b003914a80790820715007070081d5941d58028600d070001602c55801e1011644901d44204103140d00605036440a0707100c0ca40c1601a4005005a9680000c41583d520881443c00c4102406007009203242143e110b44041c00c60240000601030074201803012807180e03c80d100b540042c401940078000042c5c0341c041902d0140c0c00c0c1000d6400d040106400e00303003408041031001c001c42d980d01848209094086401d45052484030a1841c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 312010503 1250 312009253 312009259
    0x6210c122412030304120804021f120507020604030311030c0f0d020d02070803071e0e091005130c0905030706090b1303230c1815210f0d0309020319060902 68
    0x142c00311180c00b10000c061800f5512a5610002c81c04034064104d420803411240a544008061042d4145000d070305107801c5815154540408200031044155050314030684101005a00c000b0412050540c188a19450441d040c41500d10f1400e04014900d104d001e101d0038034101210000320008000c0300c5c1e034100d40e02410715040a43d1500020709100606070000c80f052070224502803208131150461060300400304140b82c444d407030303040310220034401c034244001c1040d01d0305110300c40040703075907035030703d00c0d411840b1110300e4004c1011070800f50018600495a40287e0090784000428000381e0703009668042681d20b041209502c8900b0362007103141c108400d42c000b2300510704109000c089007c0040341407982081a008941600c07040c14280903800516030007418080103444040b80c11860320a580b454001c4000b01510040750301c0c02107030b000c08071880c94090f0450b4421442002841c07010b1041140780c401d582404c011582190b000b1a80703a040109040294200b0456036504020941d8004070310700d070300030b = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 312011753 1250 312010503 312010519
    0x60f010608071215080601061701060206040f0510091203110f07140a0b010b0405040e03160312110d090c0e01030503040605031b0d060801061a090d030e06210c1224 72
    0x85e220480d02c0b040300380503180024160325880700110900c1c40f0804e0403901d95600a00181d604d0b5101c1c100148217081c0112114010003640c840f0540380340c001c0311041d03030080380880c0d440c07559210041c0883e00d44180c01c5404101c14050fa04280d000501138409207900034074800708415140c131809007052500c4000401c90006000045402844080900181c0e00c045c0d400300018000403500b83e03a20700038242000e44008610004000082c0b052160003403102096001184140010f0502102900708a00031030030030350340c0d650300018010700c0d2034903000030301100c19039071019411520740395200e00c120b004d90310a101c0000041400c0142c080c0d50b401c1c07400501c180e210344507151900c0300c00c003401c00c1e403103160195070a0034004150001600e520502d8950090f200614200c0380c10184188141030340d5040e014400b0000d40b11041d92183d070010700103041685640c8001880341b4a400358004401341c4840c0c4514414403030107040409403c00c898000441e00705144001c0707890070300506107a0144e0b2045401c2170507 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 312013003 1250 312011753 312011759
    0x40f051501081006080a061e060314061006020d2d0c020108010515091c050a0b010603060803030c0d150504020c0106051e0a06110f0618060f010608071215 68
    0x180c002514169103000040d5841d401e0301c40d5a50050307940d6409480e10303d8200e5001040004d134581e01203d06030200680d10b4401120040c000d0044440703075401540d40310441c61750680722050a009031036100c0040c0610520b024101480290380c0c2510340c140c0c0091000810440030503a0031010700818a001400300e9040954100360002c06021081e00d00305d0209502d0070000c1814504500744203421041044c0190a040b040010010380c0c00000b00c11109904021180002080701031100c4440d90340103140b80c1280c3d515117000203040720b1140d07115104541052090100001c0f00000700c5911243c04d901c04507903100085100e803540c919a501c0b450340306100040e03414101d0019081241110f0b011150035420700d1000c0e81c3c80d01600710f4503001941c0300d10010020700c0030300c1c02101e260f680f08043c0300840702d0214101400c40e24181042c0c0c4d450070070000382c01c80c0042c0e140c020481c095104124a80c0c2ea0b80c11351424a01a005a00240401051001500340551500010790210844541c034107041c4e858a03035 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 312014253 1250 312013003 312013033
    0xe0301052e05030d0f0c0c0b03091605010c080304020f0306070906030c141b12030c030a050703090b060907050d090c0609080a030c020618060d0501080c1c0209040f05 73
    0x20004030101d01560345a00d040c944a46861a0804840d0098094007048410500449540c00d00c22079000901071400060404151664070b108081c00c0c18000680d500d04258001d280345c004042e8426a8480d01a01c0a0005076070141da00c60340141d100d02d909442b03444070300c0000c80311461420280e4061240c3c408200e03466502040317200803210541c5040041c0c82e0f0907042120241d203120648010b480e802c0060500346801007d14980800c04141500d20500846420b001158001c1e01e10501c00c032701c040140150220103200d85c076040602420104581806542c6071380424000410145c49000c803c40000c5400d4094001c640003c0b1815400700608811803820051a038404c2c000e0100103100e0740390104140d4000a20001d01d10340507200c1c034008040550801203164031000c2001c003694094611500c5070780754040500104514034002142543c10141e1592a101400020b948034000c104a000310000001c92440d42e9140c0569080c031040c0c0d911f0806480c0b14901200082c054130403903c03081a000 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 312015503 1250 312014253 312014281
    0x4110607050d08011e0512030f040305031305010804030806191a030916030f060513020a080102030f060a180506061201030f0b10030b0c09030f1603020a0e091c0e030105 74
    0x52140c03030344601a40c0354402c0b5140b51000000c503c04170100340c00c050105140c0101c500207040e00e508212490142c07403888140c01030300701e035000b117421341e10100d25894022070a081c43c002500007032806084070f00e05600c0007030203100007402040c001c07083d00304030314041e52103200c80c000500710780010880030304c00712503002055600445100d0303050301a100c4101075441e10540d00500f100d1300800c1100600b10b8540303420006000280c02404c000805030f020000689400994800405000d400180c0f00d141c00002c3c00702e1486c0c01490540300d00c80d01881130004862905031000800801d100018881d0380d40c2000c103004d0b00c01c0f0184100311602000c000800c2000c28100c00200f144240750800c9240c0b9121001034803c1024080100f8010010001800c41d450a01c041c1c07500703c0c0002c0846607102030200165080040000b50742c8007040c03040300c0620541c1019200d41c0c00605035a44007003102e1500c480420348031850303a0040466044180000341d8203071701c10b920043c00c40200900030099801c1000c0d44103e04 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 312016753 1250 312015503 312015523
    0x1215180507080a0b070f030b10050703020615060f0f1605030a1124041a1512030903030301090506132c03090d080f040803041e0b0a090e0411060705 65
    0x40e1007185004600040c01003031026280ba40310412003d180c0380c4013000d4842600340700a41c01010742e079845d01070280e07032101c81c404c06800c0c6580318265240c515040081c00c04034000c0200241c0b400458224440e07407200c00445084e0501c6005181d12222800c0c403208440c442d06e0068442145106040800e00c01c011000300443d070b406031100105203419001168681406d50b9403803c510103018180c501c105003102c2c41582c031500c100c0792070701c00d9000c5060341c070411102517440c0090810342844c81074440c10041402219500100000e5042001180000360743e031105000312107590383c94a020070940c4d01c4216058080c094500028000300c2c01400318403c4540390f042d003880d440044d01c3c40780b480c050000310413141502805070200148250070340301c600080e80107052032124803030100800181140c0500103400680009480c0344441c0e010f01c50000d034100281c7d001681012010000d00000b1600403450104641c000c107103452260359207090680e00010b0400f02c2c50341191001031448100080411003800c1 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 312018003 1250 312016753 312016763
    0x30a06020c01150e150a0e04150c02120415030b030d030507080601050304050a1226010f0812160303060909080d0e01051909060609060e0a05010e060109121518 70
    0x10f401d800714840e20584416126107046490920702080d580320506400c040788690191988588a590f00d00013281c400003150251182250b0305800b03107214800b40075180d100602880146180d50300801030100612645c880e1156007408180114503c40c003a8104e5003030710030b00a060b1045031943c514050050075046600303000140110f4001122580101c1c10380340201d400200400c1c05421640d10f5955468a40d8291028450b40641036041400c00308000c0451a25070309032022694580100f07010755038070300d40190107207400034040b5441904102c400d80d00d103200caa18612080f013440f81416801819260812a604c6060060390014030905d10300821441c4088107080040206100c007040c00c9920544804038404070010b110751450146811102c03000d40161000030341503603101e0b1103401300c0c1d006074071085000fa043d10400221031010b104090042c450700345110402d141c004002000801700d8010000d01418404198050020b101a82c004414803000d0400503001c002491500350001a0341c200e075 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 312019253 1250 312018003 312018011
    0x906050303030712020a03091b03020307121a1504020409060618060509040b0a05090a09021302031501111507050306040e011803030b06070605071e0825020309030a06020c01 76
    0x466003000401c50348984065039070300c1900900d0000c8080a54000c40320041007544821020703020591007140f03401c980340d071507540f441d00d40e2452040c5400c080b016404511291600d03071204002c0b8880006e58413203003102c080444030f255694984e9134090101c1d0000a07400910204000c5403a64040d48102e06940080c0caa00405c441005082041c0c000d0f14010040003071020b001c80c082c1d81c1440c0e08826070614008102c0da000300c4d19540031546041c0201c0b0940300b49038507544c1c220250f04104031601036509103040154a507151105103002c500c801800c0c0541040303c018461400c051090100b040c40e12401400020141070071540104190001ea401d984114071b0070011b0b6103401c90520559800da00303039811401407110192825002450a401696000807003040720400041c150b05c10940304280a40b07d6011442140c05a41342665981807550241b000590500c8409000b04045009400381520000000302000c5e501f2030640c0650300e00940c0501c54000c81c1d004110640e00500300820222000700 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 312020503 1250 312019253 312019259
    0x807020f030c030d031503170a230a0c06020d09060b01020601060314060603060d0b040501090b0105100818030c0d11100c0807030b040b06030411210c040f0b1503010906 74
    0x540700c181c1c0c10b8441e54181e00c6803800290b9940aa081841100e561998086180f9030300c2e102c1500c0f90b50040e10700541c2c0300b00001c0040705141c1003030340c00200c413800c0300141d400040c2c84121030085128807100c5005001c204e007080c41c05c1102e01e070112842445031150610644070585001d0010b811443c5c079903405400f4070800410303c0c910901c1000207824001e0005000e5448030000c1c0141c41d4000f038403682d0440040202100401c20000c08140140d1168000140e04a1a414601d0700100180c002a1007400089440d15030240d01c80351240d0040240c001541c144225400c03030b24a10700c640804a04035000d07140031640e2403900a10815007050b80324080d20007c0308002400e1040716841c404000c0820f1400022441c054441e074001105400e014000041c04180040001d20f0b41e0011903080303520f6030680701140c40c05d003003105501c4000200e0400c840c004243c0340904503169100b03805642d000f079503580d0080900c011640c0252051940c0640141c1424907042020300d1194824000c0b070003160b041c19400 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 312021753 1250 312020503 312020509
    0x6051503010e0a111f0512010f03080304030f0c170904050a020c060f0405070b0d0c020c0301140a020d0b0d210e100f1112040602070902090f1009120807020f 69
    0x2040241e55900041d02243c609640c0d0210b0601040003090b4000540480560842d001011003403801c0030142c40311501c6181d4000e40344ca88042c1600b100001c000070940820010794281c090380c1c8c0040d450304052015031000381048074450a00c52018160080041542900720200c0c402003885040560381880543d070340304186010380c031a00c880100f1a9210500003241d10700020364150b046486042030712200c50340c0e00b02c41ea51070f402041d02018500e55460400208039010081b04100c40d00c194001d00900031000116180d240c03004008500c503c0c0c0001e062040c503041680300480f44100103110700500003503402c0c80b50408030300b051306041c4489075540c00c0a000d03008440022250500400c0c0410480c210f00c41162400520fa80d900e007402050000341d88014000c1c0802c1094400c017044050b29039140690080c1f0f464201d610000d9854410040b11005890721031300c059000c8001d45016a03220f007071071401c4480c96442e40c0602410b1466245010400010100400788203008039415091070070800300f0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 312023003 1250 312021753 312021761
    0x7030c090308090f13020c0c0a1d06130207020a030f020f0307140607080c150a201902190b1509070c02010309060605120f012f0f040f030605150301 65
    0x241030b2140c01c0c0000642403504a480f04582c001c09001e080b85070a0100120090740c0104490410300d03000001e0485031818484a940020181000850b01d8080040f601802841010301440c4c020002403003404483c0d20141c04856070664058400d02126640b800c22026201e070303480d0200e1003940400b003400110310b40010890140c0f0a600c0442c2c03180002c0c08100189544250811070b90700d4402d200f0f84459490900c055414804982c21562a071300e4449801d200f140d4464080c200403050024824901300140410b84440076182c04445041e543d210100381d01e810040c0c284480c0703020f608040d50081141c0c0b006298090458000c05003046072031401000f00c081c0c0c00b2118440060342844070400503611030381010020300e01800c40081c0c2d01c1d44540120301c0101210f01490303500d510114800340080024451001641d00210f441c0f0403540b1501482c00f03481d40c3c0e03040d80d088a45004188121000101c4040314002c3c1419680c0e514541d50f81d113011006018204c60b2545960280c1c1c85420304d80c00c040c02 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 312024253 1250 312023003 312023009
    0x1209060315041805010219050c0d051c1d0c030d0c031805100e0a0f3507060c0b0f010f0909050f0a030e1212030115020c1807030c09 58
    0x2240c11070351250040c50030094504059680580c40b05034a0b040700000700400d41c0c655018100150b5501036400d00d00c06a10b2402d8640b4040000030015500d8040c3c0114109240d080545800e07690350201484040004e004600034007034032846c04440b01c14070b08400301700040b95841c280949070314014120070140c4440141c5446008154200102000a4440c16142e20340b400c00b44d024031a5642c071003010441003090000305601040d03154240342c86034a40310f80c1d840c004098484c4404601428006ca5480c0b080121180c0561a1190301c03050744420015405864040d044004803260345558000040c50204038450a6500611003404100258204541d41e410303514140415103096150007010801400441015100341c000d950303080c1d09244040c4800080c0b80d002e651144003000186003040300d0b4100200c2d0030200d643c0200080d40300800910240d90440b00c40c2d01c401c240d2070078810016070030b00e07011016540d48601e00201d01d25488542d9020940580072a82d0200030b5054074880a07500d040c486c0c0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 312025503 1250 312024253 312024259
    0xf02060a0c0e040b04150605130905100911041205030301050a0608090604030f03060801060b030a05162703080703080406050a020405032113080102030402031c05120414070305030405031209 83
    0x8490002d541002c3c3c100908203000500002008512030b08500f41d000316542051000a07000142c000440c442581c480d00603200305c00c800c000ca420007551015810340c0c0341c403400100c0c60f00c802c0d11107034800203401503500504004c0c030440800c402031710f822501c1742c1c0240982da20030807000317002191740e511503420300f44184c458400038a140d4070342c0d0f1010390b20040c4159400b020035031501c40c085a020001c1c02000000c01100301d80075200d0501c00102015100c0003001003048850003000c4c0c070445580f0030000304542c0302e08000c04110800038207413106104210741000d400c0c5040011190101903028465510403402004104107070b0f220607200d101070740310f28441c07950705902295000c00002c3c500311412020030b0000340214036040300e680380c0031140000b40c0d000b002540d6000c402c10041d42000d201060b20048140c400a0701076850b4000a40180140c80301d0b00c40110f00d031400241002a030068800c0403102e08021200307040e5880c50507958a038454050140640030f0404c800141c00d070a0025200081002 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 312026753 1250 312025503 312025517
    0x10c03270206190509030c15270d0b0f06091003060e030d0507020a03030b0406030f0803060f1207030606080303091e0c0409060605031b06040b0d09080a0f02060a0c 72
    0x10004000000e056441664404000c100c8808050f691012a00410300c081c0c4400b9203408000c0c04140c280304034092906d0081008140036080030a421046404203030305c844440146180d0642c2c1703424444404181c03690441c52100075032080c0000f15003898441c604200122589036144800d102001d5012740c1c00340c40d0310485000500c0020320707030b03045118041b41e04004c40c2d0802c02041c051001f9114150f9a00026030460500e182c02d250f854045d02c0441ea40030340303007444440d142d981c0d0410b00c5a070340b0102428844c80400800c00d0350351000c014400210008029405400724014040e03180c043c944022902c80e4540301f00001e41c044080141c0e882184035001801c242c1d1544840c04001004401c0381d00c02900410070702030041c0e41d40f482090300981c020040011080e08110915140c40003020794219081c00704410504240e5441c0e0881e030039a420b03200010b880b000c1ca0f00700c0720054503002000401c84500410642807182e07000d401c0703003002207580d4200c0c2c28949501d04003d0495410300078a1001902d8 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 312028003 1250 312026753 312026801
    0x1170c0306010501030216020a0e160201050106080601050a021006240305010e22050d05070314091311160f02012a12090302030a1b05060408031806070c17010c03 71
    0x20360251a11806c01f405c0e480d0304100640c0052045202c076004100704030300f100709000944001e1f0603081254030071400204801d506141001d4008030b0002c0c1084c2c100500042c1c0981043d10a10004103480320301d0302d09129054452607503c1501c142031725183c080c0781100121070030f0184240107841c100e4008008040041d203604c02c80c403203107245240000e820148044102400100104907178500040301c0c0d502c1d140c41e4035540c07800802210324104428103149051240100c01e035134001c51f58900e20641c1000040c10f801080c000822390042c000c16020290004c0860710501c0480704080d19058401d9981c05107142c83d404030082c0740e482645a0030b001c502d400c4c4110000540c0d030070007002da091050a00040459995002924140140c242159640000a1701c81614406482e01c280a0901211490b081c282003080184d62070003200310030403007407803030b0b400b420303455210300c0129010150000b40c060151510b0b100c10500613020341e034890b41e0540c0303040c12078503901e4424031030080d000d000d00c0c4807000601d003 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 312029253 1250 312028003 312028007
    0x301140c090a0b0409050609061e040e120d0603050f0d090306020c0a14010f050c03010602030d1a0a030b0f0f1b0306011707021e010501060801150909020d0501170c0306010501 77
    0x204010301900b060b000040865040014406000100320680740030030305140007024401072400c060328450080910504601408203010942d88003000141c80010b080d503c101c60341031900c10300c914180f1131030000184e1100700b0030680d0444000c1e00c0c021421110402160942e059440032800c500200141c241a01480049c0b90340c0c000301305401041040750094202505c4481da030038a0f52040c25601e80d501c6008480481441c046c440c6d00007000981c00b42950b141c82130182d12449103c0b2000000c550b514507561020010070500219064042c2103910b00701d8591903e1501d5000940b2490142d0050500054000c141e040c10607205d50205040075081002c83c055032601900060f06550500103144c2c16241643d0001c556107204505560041c0381c404240400b0500b410108604040584d05040040c082e282d08101642c1c111a100d10b03101c41c0b07880942000705d41035440303030700724954003400081c0d000c078011001d41042d03040e99410a0116880c09035030811664558401c603110307030190000001081780c1d40c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 312030503 1250 312029253 312029257
    0x60c0c0a1407080d030501032105180d1a0403020613240f050c03100605070f0209090f0312060f0316090b042007030305130308010b13030b1005040b0301140c 69
    0x4086101100c070b680d51644801c03802c3c4118001c0941c0044c1e61200100705112903841c00340d01541614000c0c0a188107c3c010081851040400408040340c0c124140c99194607a4640703041e803180c2020705251281c51007014885800030585040d4014845d52004c200011402d1900d08200c960211030880d0001e496508107006002c2da94244240c65964034880c0e120090501403903200d10400781c0803d07904d2805030380c1d4200d1182e0700e402c8201040402c0c4100c43c0054964103104940640481c1d07487c04507581ca4031312610b4502e0128080c44e441c0000b00d0744c140321044100c005805040116032610714a1684028107076030707007010a05c0842e4214134550400485070340e64000320042c1d41c00342011410b07940c0c0d1a04410245c2c84199118a00c1100181d00030601d42c0c035102e4241c1102c0801c800144081850301c00400061060103440e0341d0410000d0b00d25107003903848c095071000b50f501800310381442c904401d241c140c00380b0310300c90b180c050b070b05064040001786818413a50b0140c00c0c0e45010044280c85040c40d0360125 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 312031753 1250 312030503 312030533
    0x40504091104020a200102071509060b030f0a02030c090f04200406030c140103020c070303123e0c031b01060b0c0304170a08090f040f1a0102060c0c0a 66
    0x1500e201c4094500c0303031110f00050036810b50545a40300c03401c1c00c80300079101401030420548a140d1040c449800040d40c83c5c0e401e4406904810001703e03044e086070401d04018076582d00701c258188924810260000d80108901c40c2c524021010703500c001d0b4091060140382c820866074110b1100d555800540011810745c080066280266800603150411001041c1162625001590546940a4108003070fa100105500d00d4003c00c1c0f90a50070000c28181541d5103940900004082c000d8103070118080341000d601485106d03403803560a0144400212580c568800c3c0700b02c207400700c448001c400440d491683c104480781009003d0085140840c20400c98186100d60402d88045540710f00002544120400143c825606510095561940740c103024130318020024800c401c071900b1240300c0c200880e815030281c2d000500d0595050030303a40c4084000070010400c4817200b8101510b00b000d008103134110b51060303e0070800e0a800b150715a48400c0c001082e030740038000101c00c9a911145070301000030070060908600c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 312033003 1250 312031753 312031763
    0x603011a0a020c270a20250b06030f151f090603031e02010e0d031e05070203031905010312050705031308011b0f0225050306090109060501060f0504050409 68
    0x3200300b04000313411510711109030b0580c0c201c50750305032a107003c8000019401c10341d09001080302c20004641503040860041c04d468070300e08045804003d0340c60f440048030348a2a428100800510585408a62408180c4039503010b44106040d02000507000142c240c00380c207103c00c4141c0c80e9580c1480f904da40036a01580c0b90020900c45000049030340c0e881c09203030080c0d442509d030000700d2000b2000c0c00740410b81462012003103a041c041c8007015000040b480001c040914600402e1040010241511210100400c03880440c500f0082112030faa000c00514092b094280c2c1d14076244003a2001c02098075028000502174081d04d200010780d190142e00104180e42c03043c400c0d64140304002c0c401058076500360780050848d075100c14004844041d12002c0c074030414218108500f000071249002540d0380e00210200c810b5107000011560008080c01c4404001c01009040b0f52040c034105038154007074a00100100e1300c260601d07002280316400f420514100f9443c55a880303061902c0c0c4810030010701021074082d2a = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 312034253 1250 312033003 312033013
    0x60318010905010e0d0206100303140c1005070801060e06040b0a17010e0709090e030a0810080a052401030f0b04021305090d0210020901050706090204020c030a090e060603011a0a02 79
    0x4646002800303080e00040c0103000000300c40820202075403d003444050702c0411908840100b00c5c101c0c00c0c8101c0c00c0160798140c5006507111030031141541d4a0320558105000741d01c241c40d021083c40201781c10a600c10456641c030b109459980380390549000a1076030300f5591101062009001210060000e000b5450546c07400031540c010307103844006540740030f800c0100740c42040c400308910705030008034980041805000400400007421010394480c042c5000042c2040924400304841e60b00390130407603020700010381c00c0d1120030040d03180a5650342034644113000c60344400e0f07a8030306010f20190040b03812070390011800e5003644500e80d1030341041d600c0140202d034441a07074041c030404010300388600e1f8402da41c0c044c000c1000c002e034480040e14200d854100b02419034010448801c950344d000301680c00140c0d018a0102d10700080d0320004001c0c0c00380b42d010350360391300c0041440524a81e00130751000445e0303c02d244000d201e03260f9100340140c91009001c0c2600b0740300c802441052610f10700009181c0c440c124410f5030 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 312035503 1250 312034253 312034291
    0x4030311070506041205010c050a08010905040213020a210204061e0c1b032319030302070b0901020901090909020d020618100242100801020c03180118050603 69
    0x1480c5501319820010842c0381c3d1003903210400c0002d115035100600d0303d0500c03500780400c9840c000c01d406014000c0c512629240d502290031511141d680c2001c19000e140190349850245070000d20040012a88801c20301c0865031121915001e442194283c0300a42e40720b1400071045100180c8040401d4642000c01c00c0030700321400454070224a00c600310680c45940301d080c2c1e14606103203144481c00006001d42c000d05005002c4210800140040822000341440c14130080b82c2c03e041d4020b00404001401d98007a12040016840040d40142036a28003600c414200a0b2508040b82c01c80340c106000035000f13440c14110b00058a018809810070721400442e4013a59103196010031541d00c00d00400345c026a00082100d01a00e1398440c0d0142e40200324400c1d00002c1c600d00d03400b050800000b00c05215600660008a042c018100a609000e040464001d40d602c031043d00b08a540e960194031343e51121081c818a940d2158031451080340c1c2030341000741c9141d82e1810714003004420b5001405407413a01101000e41 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 312036753 1250 312035503 312035509
    0xf09080a03090501030f0e0a031116080105061503100e0621011d0c030a080d15030507060810080c0415050d03031509090807080904062d080f03040303110705 69
    0x4146103101e50740700720980e454107002505903039148100c800b03013508103d5464041000010b1600740243c0515101000300034943e02c0780c3c1080140d180714150004440404201507405403c200d000301c20079103d00c10103000405801a06001c00d4030b140c042e207562004104001ca8010302060b03001080145a58100701c484011a5200240b4400009880c0d4407403200c4070109034800c501c15030024410f4003a2904a8003c40003a4903001c0350480100303203410200c1c5504040e02103501c409131000316105002183e40c0c807400c0c66943e03450b56101c2e034000691010001641c1e019041c41340c00440714003c006200c01e00c03108040001800c0201c10b0806031200d02ca900090941e00d802c0040710060003514001402d280100c21804101066003021040307034140100d11001071035200458120076000140301d5101c10110340020003034a929488003d02c80c0b2030b404160800c13814281603005004c52180450740007517541c030340c2070780301c0d021170f203410325586c00038072040000c41c2c014410003e07044000b07825074543e640c0f54800 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 312038003 1250 312036753 312036763
    0x5092d01140d0e100509150702160605160203010908041505090904330b01090b0703020c150c06150102010b010e060f0705010609091209060206040b010302060a0c053306060a0f0908 79
    0x1140303a551f1001c58025080c00603010f50507042003203480034202003655411030400b089044d115100804c50001070092100c1800440040301550080003440b4442135818401c0d8071341c00a000d09141044170004070100d81b4001d8046413020b0782d001c0c1c40100c545e5605c0d1a20b00c2030810701040d40740340301030744c000700010343c85802c00896255005500001d00403421100042c5400f40b90307004494030b14010804000800e4002403190020842100e00780812040320340240218010f00c9404001031080009100c40503800c40100d500e49042a4003c00035400340400440b107900c14a002036411050400801228506480007400300500980010074960707074400200048841d0712800303442403250110301004030b907808140d031030042213507100078501801c0c9600c4007201c4160601c0000c2c881ca00006d25100352501440074101c10b1030b00141920207003050b022a2110300c2a00419030000c10181c52810100e104000c20340c2070150300040c02d502e0400c031040030207036030741c1e2083c00030751007400b1851000044601c01005 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 312039253 1250 312038003 312038011
    0x90702070f0b07230a0807030f0e03060f0f0703061d0103031106010810090f06020a0914100e0906040b03030d090b0a0501060c02010e0105092d01140d0e1005 69
    0x10041240c0d40c544046284100d800d5001002054010401140829191294085070001c81c01c880c2030807850384c0c00d000f8a414000c0320004c1c0b02c024045004c0c414181c001d01d4086140a6546a0710b04d0301e40c03070008054480100300c1d52007114120103800b041e1a07000b00324195a2107141400c000681c1e40c0c40d448500e8898801403402104401d0407001402019404120204400c850000502c8554100040c16441d0500d0341e005601d259519000c1600384044001c42c0d10940c2c1d0082d808541d101c07000d00380200a01e0840c00380580483d00241c0901c541d007050490555000480e907500301410b00e0b61400c1010341c17640504229886034a130f9042d5800c82d9001d00051180c14940f602c00110a42249001103030030400400d482d81c100c2c41c20004020998100301d00400169091814007103520010740161102d005a9140d031750007051402c200040911100c6407402c44075100d07000b00000400c804011903817003c0302980349046007028460001c00d1036560300030f007441d1581501a01c00c0c0c0c8100700007005c200c4400319 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 312040503 1250 312039253 312039257
    0x70b25110307140f060a0804081303120806040606110c0103020304080705060f07030c0c0201050a08091609020a080a0b1f020709020a0c11010906140c0a171309090209010e0402010e0907 81
    0x5010340710395240c8880304c0181c4400584207207040441d540005000d40707400400207490f2842c0001c0c01040d400c2d4100d000e070040c5501050001c40203c08540060803514101d0310035000310301c4d107800480c00c1801403103100a8501d4110085c81c00c07a40e4000110042e4001820840d8843e50501c01080000c0090103020b100e2603400e00c8200742031030091401015200001c14040034802194640030250768010f08441940b0158101000c041c4c40e400e0f401d92810f41c0c40702c0c1c3e0f020a01400f85010408000035002091180c00c2d036540c40405403036514030403003103c411031107103680050342c6080d160900b1264001c41c202140640140c0c1c8409669000e164242d03070004040a00007824004190b04003c03002c103c070a00c4080a10b0700e001160f040800180c010042d01c29046007145000c40c10280202c410002c40f00825400890190240507114016015400c078854074190601007510100b12404548100d000150700180f61403a40d9180004a81d20560302800c00c1e410001001c00803112611602c20080c01502e940e = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 312041753 1250 312040503 312040529
    0x506030901051b0301140904050c120708070e090a0f0f0b070c0c0602030a0c0b1503100606080c070c030303050a0209180405010507180e06011817070b25110307 70
    0x1414a0f04140a203100f031501510a052006000c00c08800d0000e140008081d502c0600b181c441d801c11a1400b21442c100c1c50344421001c100d500f801d040450008200c52801048a00a5803038613071319521400c007213804881d1517008204041c00b0072007031520341c1030490080701684420074141d19208032003002140d041c0041188501c1c13920400096015100080209101440c107080705400014107038004c80002802c90400080415448254544c428440d180010300311051981c0c41c017015070181c00c0f24454400410251340009020003110740494410641c4148600c07141400c650303080e40282805444500f040e54248030001c8182ca929500d241c03101060750540c052854103203491800d641d4010040401c01c88200051112081c4900428056811a031001145c0f41d80745001211078202c0b030b00d001c0000b400110000101c08042072441c0c43e4090b80c100075a03a00e00d440d82c2d030300e0070315214110040301e042c0250140580c181290b0304204180034420021961852403000009140c0300e545c1c1c1007072400d6101 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 312043003 1250 312041753 312041761
    0x100c0b0a110c031c0203091f15061701060201111210050d03020f160609030b0c390d210b1215060f0d020909030906070b01031a0c0a0e010207050603090105 68
    0x20100c1c4c0c0c1907500444520039450361030080061511021600340002d00c040042c240700d2840d011a40000456014201400180b95502c9600034040d01404040d50700040d41ca41c0041040b62040c001c0c0d40009c0d0010341c0381e501c1c10205810180c3c619100a11303140340c0c48001d82000c50340703039030344002d0065882c02540200383c01400600e0840c10040a80308500b005044045e041010f00e4204030002c040342e0308201049141d60702e0a681c440b241c82060a0f03030064280c800c070083c051100884540c04000310701d80211754000d060034142d03940c40410406d9000030540799030381440d020305000f8003002e41c040c40340b501090110384039002c5008850402d80706480c94005140c41100040700c4400b03d680040104c0300704ac181e410f420f01040c900c000e120400b82c0500000c0001031440c400400844a042c2c074040c120603036580a609080307140040c20f0204070340640b5601113142014100300751721402107610300142480c103080d8900960b042c4880aa416065006503000040e09907140c0c0d020b1442003180400105e02464 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 312044253 1250 312043003 312043027
    0xe0604080301051806030607050c010b0301020409150801020906092b060c0f020105100b0f040f12020909030a02100b030703080c0f0105010f15120e0307030c0b06100c0b0a110c03 78
    0x140e0254402500b04d60411015070b6001544580062607400c01d02c1da50311301001ca031030240c01008803083c5c00d98000103000500f0f1180342e0020003901c82c1c400c400c07100c113511804101d080c1d208030304072150301003800c0c400f41c0390a240c0506031005205101502d45401d043c07032010003a001013010402c0d03a0450341c644050404a412000170001520340344001c00c2a80f40000360404201102d0003110100400810052440580481140e009d4000704000c000c16a40c0ca403e24603540b01000c00c01c90007107031182c0109044441c00001e88903809441e401a090076003c4002c048020070340c0075072031503151081c1103000000c9040e040c014080401414003034072030040200449400d440041e804114400110b10b0b041020107449402440301020520b07089100d0700c031540c2c401b4040d008203840d070342d13003800001020304c10540c0040c20a494144103c0b0000700c00c1d031b1500c007017200c20241001c43c0c2021440d0682020002002c00e070000d80c0c486150b50300001d0320006030513110105e4001c642d1034401507100184a592b240 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 312045503 1250 312044253 312044269
    0xa0602070b0a1b050a200a0e0406020c0f12041e050d0b101e08150105031e1c03090203060a0b03072105030318120f2a06161e050a0507060e060408030105 67
    0x1c901f5a0100d040b103144c01c4c0101c00c1d40c0b800500c0546400d41c08118080302a600788500e88803c010300c4101e910700c5143ca042c100300343d0b0040c80703a240b0150b2040015203801c10030000b1003003200c10003041e80000e2141929800345454005141c3e2415030003481001c04d0b00810b18080d4842d601610201e00821401c0c90394051910b80075081c14582d0440140c0104070700d0b0f80003e2005810103480c513880760950480c400c540e1400c40b40111002100b445865224103540d810750250000303034000c6044a1040d00c03040b01590444191540b8507405401c504000e000070781912a201303c009803446460710750b20510780c444609580080d110401c910b040c00c0c4081c0c00040e000c12010014201e0307084694601800504500703240d21903102684450344d80c0000a070071024002c0107203000c5e103500c10190f032642d140c001202c005402041502001084008000801c080c0402061240c6000c2603255075280504c15081a2281d81201c1d20841e081529459480d41c0c0c8001031110038021441031a41c1c1e500d95051504000c800 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 312046753 1250 312045503 312045563
    0xe15131d0c0d050d050a03060302060409051906030507061407020603090102190305060102030a08061801081c050f090d081603050d0c021507050c10060e04020a0602070b0a1b050a 78
    0x102c2c0a440c0307682c00300354007207401c000e4088a41000c0382e8a55200c0310a030090071030355002070740c070a03808507002032600721a401091240c0c0c4c1c0c3c903641c900c0c1d07c001402e018045401c075000c0078195600c040703014001940216450f6140d00c250042c11070034000303d40d0006aa55100711540345041c2d4000c218030100144500004646200a050501881c941100000d41e00d0107401d08501c1001000760120b08542ca88999180c040040641c04400039a148c04040740c1d2b419115400344040500d003080c8001c03c0d84140c080e11160340c0d090100c14982185241005800c8006510a8990140800c007202c200c070000100d451a1900ca91107041c0c41d90140891002100c24020f90201503402c445005100300041245180c0d01050728106280c942c521024594600020740541034400742c41d203030020514132048581c0e00d110302e03c05c580100240307481e07603000c9890307858070710915010300b43c01c2c0054002d09000da00d582d0041030f0f4444c0c10321041c15898440328a81005400309071108144040c07450900f000b850119005 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 312048003 1250 312046753 312046759
    0x7080d0e0d0e040c0306081b0108010501050403021509011b0b01181815020c010c031d031903050405031c0911040b030703020103020d06030c030309080d090e15131d0c 73
    0x11810075480094401c0d042180e8580c03049a5540600386130700c2c041e5010300c010300300e403c3c12160303003c2c000e0141041c202c1d01c0164081c04510740400000d030540c401d000319801da0307030302070f0001d004074044000031f02c00b68200000d41c605006441c1041c8204640f4400c0140080b4007880040640303501d40030003820780d12a1a900454040d00b800c600c000c00c04072040f00b000300e541c0c1c030015008212400e02c104d14002c1c0107011200c0c01a5092401c03104c42c1c00d915400c05145516045110b00c20201c0c580d201c955031b840b0b07001034180080c0c22106074500042c002d900060740a402541070340d10301443d10181d400300010b007800a11806544000c07400a10580701540c007000301007641c2c200850010400001d60b10140b900c002410550002800d80c214070356a04900c00940c0e0012a00562503100d1602820154850292100c1ca1060818522115102d4800042211031404548001e5214010700f1301d000080001d080d41c00200c0c254045140450a00c0740c00345c2c903011650100b001c07005941c22181405201101c8130300c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 312049253 1250 312048003 312048013
    0x2101110a02031e0406210b0a0b0d050108030306010c0f150204060512090a1e030c02060a0207050306090303040b04030c021207080c040e060f010909170301031506270e0f0307080d0e 79
    0x2007026001440c0e89019030198504174110b070249a034000c0548184201c00380c0000235003c0c00100248040041c21686500b51014841a038031481c029560f8002102c0d454001b82d110400b9001040443d003c1c10403150103443e03a44174404101c40b03e4030aa0f402503021a00180d00061264940d0b18407844068110b0a100040c140448160700c48089080d80100301ea00c00c038520512140c100340c060310a00c040350360701500c42c4c1e03210200c0e500065164299481054020f02611001540c100404822280328650000c0160015140c9403402c4405500340708040b030304400310441401d60030104200b40030040108a004110445582e4244010b40340000c120004036071214082c0400c00c1d031007030380076815607511a5000a016500c0c3c1050040ca41804021401c0240004000310902c040c000759141100310400c418844159a550300c2a09800c00190b40039071840d4014055140041c15007010580d104620200e0f01202c054180260840c0d1000c2402c4a00050000305480d514030745000f8843c40040e0352020342 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 312050359 1106 312049253 312049259
    0xa120f02071208090f1212030c071b2402060610140c0304240c03270e04060f0e06150d08070311010f0204052101110a02031e04 56
    0x360040a6040c0c01c003100e07041c0455201c43d03c6da403003c002c1c00b40c50504a40c0f100290000741c04044920000c00035a408210481d000541201204c50410101454000f18040520303404400740d08031820705050b210749c00d4021130580d503c030b40d0030780b1442e44001c0c04043c100d5101c81040891000b0f21404030701041c030144000060400e96603007031040107841c1540496401085401300300d40c00083c0c000c1c4c0001d0000382c4580d000114080058030308440b51865991092078843d0250070078180701202c0d004004c1440750b075020b108030110003994100100440c40030300d1030701c03554010400c1801070740b500355a07601c640754008411181c3e600001d410b521500c031468000c00c800450209000700750700703002c1504c0030202c80d4402c80d011102d004014241155000314080c10340110300e05203060315540c0384050005041064020420600640e000c0c60ba60140d205650030000307822081c2e602006070501c014 = true := by decide +kernel

theorem cover : BRFrame.Cov 311870503 312050359 := by
  have h0 := BRFrame.cov_init 311870503
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311870503 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 311870503 ≤ n) (h2 : n < 312050359) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
