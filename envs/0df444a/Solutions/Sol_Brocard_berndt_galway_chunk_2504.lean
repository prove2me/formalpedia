-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2504
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:54:45.790614+00:00
-- url     : https://prove2.me/submissions/421d458c-7b3e-49fd-9bc2-f82c0d961398

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 450179856 ≤ n < 450359712 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 450181106 1250 450179856 450179887
    0xc0a0c020928060311041817041701051e0903040e09101119091202130f0c080a061a04030818030f0312010e01032607060507030e10090503 61
    0x41d02c40ca110540308105032188051018050720440242a5101024005d0010381d0f01c019514290407a03003481000e08695820940c201501d4009062032202c03c414135102003203900350b03030141040c0300349403040501d035891f040d000e030000b0307100d00180d070080303502c074950b02c109821040744039410420086103403926000c01c40f000210700420719001d42c081c0c100128040c503414080d1444042e0002080b0b6101c20f0288094188440f400c59004180400030170200110880c441402940e29011912700c00b0800300503125802a210007202c9880041c030300212601050780040e850b40c000c403c2c0709000c0011039103411800003070580f01207030348403a11814030041000a46840050107103003a140ca2003a541d80080000c6444d2881d01d41483d00150401300344100300350074524074540180a034140440880d4034545441003d404042d1140d040100c00c40030704003450320445e049070043e07940480d01700414a00064010011b040c1c60100a5450060446d1544110154050110081e802401071482c4c450f807031802820 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 450182356 1250 450181106 450181111
    0x709030204270f140604030807020105070e012f100212090a020d110f150318071401030c1803080a09050306151e041406010912050307032610050102060c0a0c0209 71
    0x15204c16400280401090511903a80514441d4903524814108500082c0c2541c0c0014088010400c10b880b0700180b6030307031040074088401140c8070007440601c07040c0c20701e1030b442c1c1800640e404140324a00300c07a40c0c8103180c0d60041c500752942c0303000006a51a1000c8090300d500c00c03013502941c00105a00c420b804a62a0440940c4200005088800705003602002c50020700d2002c80b48400082c0210800200141f090554040480050040c0c07059a04102000d40000c3c02c0244090405030b0b0b40c01a05841405030140e2807c400b4403104095070142d917403070700e803101e1b41c40007000e100050b00099000030300d070600284450089002040d080c0304299100d0a0041d8188541d01401030442c402083d09090341343d9104d0581454002080340e82e403441c14400140c0303206280d03400b20342d1050f4850080380109a012083d58441030341490151003104200c9038034180741301c01c9881ca260803e1580140843e40454038440c0084800030780a460107962041b486400601809071150045050b03500e0b40801803500340401e40d13 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 450183606 1250 450182356 450182363
    0x7021b0402071e020a0f0602121e070807110d02090a0b010201020d2306010e011e03020403060c021f020310050904050319090f0f230d0b0709030204270f 67
    0x5081c0b107010b48990042d8000500c600350b03851160355005041d402d000c150710300a0145410005041860000020764400b032010110640e000c010a001c00d0009509d404c04442072078640c005600e40d8030500348450181d000c0402254240a203516641c1c4504201c038401d0080c41d002012840c0c1035803125218000b900d01c00d000c10b411035500708841c9040b0b44036480791442e1840a00d4943c0c08840e0074407241f05d034101c40a84002d05000103000c5060440e81d108046128600100f5100d1071800c403159000e4010b4001ca40005244a0800d41c034030200350390000e1a0084895a080000803405c4019011801c91000351760520031041500e2003070180e400c2c216010781e00580704100b1245003440400e403d044450500e185000011841e060400c000b12030642460041d00c41c0070640b010052078181c41c0101060300004e00440e0045100f50604695290400d20000c0c907009002200c1500d40050014569810340c04224411454129281e01c442020494955451480c1c04449008205a01c420034200c0103120201c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 450184856 1250 450183606 450183611
    0x3021e1501230312071a0402030c1e060a0c0605150f04021606060f0305060912160201110d02010509010c0c02031b0a08100606030c030509060103030f0c0507240807021b04 75
    0x210141c400700b201c11085804c4000c1141c44400629102402e1107042c40e060881250a4040c8009a5070108111841d002e048910140141c00c98000b100b2006141c00901c0e8082004103100c0d00a80d040b099420003540307c1e080070003842e0340d8001c1031800350b501701680c280c11840304582410103082942c0184119203c1d05010034a050195842100340c1d01c10303402001c048256003c0c100200142007005607081002c140280c1125209003142480c18000d0341c09403079116010038123a00a590250a0007209203920b01c05840c220455464081e01800c0e0a882c000c0b03e0358179020b010003119201d44a40b507001c9034010003038500c031710742da016060f040c45d250445240d1204510000040d1220204031000d519103150b0008200c1902e011005822140aa0010010b060420302040180311021400c503040d268141403030080081011011200c00203600c200409510942e4004076200e40380300400114140310141ca5481c030201c1402c22100010292444005640414003003030100443c6407038400c11303047c082d000 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 450186106 1250 450184856 450184919
    0x605030c0c01050103050d02010c05030c0f0a030608030d050106110d02060c030702010e07091b0e06070b04060b1c050c0111063412140601050a0e040e0a03021e1501 72
    0x101d8211802a40101c42540c460003100c2c0300c06030203010340b404100135410700c44d0171841c00106002c000c0c81030854010300d20600203440488540203a02030000340c1010000c1f00d41b200c00c1400c20740c00038803017802035501141c04686440e002c02000130341004d042c0000d50140c2103d4641c25143c90440d08060145429075490350050311828404112171001040b95030404100c2040c4c4541c07c4100c280000703012800c03ca4250218880c5031510801c032100b169004903a958a41d0b5603040180040482c1341142c3d6000f41c6071401003402000d40c400d01d8904500600585401c14640001541d00450322030a03039a1035000382d0300144842e005c8031100c000c001d2000882d0420190400e100e87c00ca622900300460209030890140c881d5443d20344101c502d1032801d41806402400d00600282081c01145115000c00c5034903c04d0310a02d0b01c0f150000710005010400310350012109207400382d120f6a400b010a240408035a071400c0740f0000c00180c0030034081c11400041126420111005200311102a600c9280c2c2030f000780 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 450187356 1250 450186106 450186127
    0x303010803270907020d090e0c0414131a040e030c07170703120504180b0f0d02010e040f140a022502030a1505100e01032a0e0703050a0b090906010605030c 68
    0x10028421100c2d5409401c440c0751b2140d01030185104c5402420051059004004018982c202201c0c151402812a600041e122000082c041c01c05001c4909a0314106602d044494650038030045030701c80121400d2001401c130400c01560b0340503842d4020003d0344085810800101904500c0e00480855801d4901c02e540320b40751204400e5810201100041c000a0100807500d040703000080300c40e6180034140822110040060f9082078171a40207881503421000c00c000f1a8052000d8601d0b814001d8014401d918101000790010030035482411001c130203040008000115070700c00c440100d94040c00510708990442c1c034103480e01030200300c201e800d40705100b416004140304c98048400c07201c2d11000442c045c034001211303c0c015182c5034054032062142e0001840080c0b80c0083e80c003803c03088000c03000c0d0044450305030120310f146250b01264a80c5206800d024002c3d9040e08514491200c0e0703801886011151001c0c041c0d80b110482e81038a081e0884401030040c641324000854201d64071000c401d040014005 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 450188606 1250 450187356 450187369
    0x1f020f0f0c0d090522050c13092004030c0303081b0309010510120c090e030f070506041b14010c060605040c17010b0309060a09170d0506030f030301080327 68
    0x1a540b1920b00c2d032556651150f0000302501050302c0c249000c07161440b44218041000e0700e81c110150300c3e2000103100b0700d00b102c2074036000301c40d207000807500f43c0d501c1c0343d00740c01421448034010000000c11007006049905000300c50480c1d07070080c00602410b11b180c0f000c56040601401c100300c00300c2d0035030203420040d450a02840c014490640005840d0805000b15039180303143e0360144803800301441100380460b170010210300480328400400b0901d2149010041d0440c4284003e0010f40c20340861080144100000d00134400d52248241c07040039540795000a00c4115280f040b0341c100000c62140c2c0c449548035450142050b4426100443c00300d031070740d00040507914010202030000e401000441d940d50052703030685004201c0500007900d0360070311403203090f12110003c00d201c0040307072900703c0e410800c0000c100c1c0b101800c07006000c042d12484441080380203010300b502d4007032003449143c203040421a40031041b20b040314550fa00461503c004110510101003c1c0e0004030040d04800e00940556117401 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 450189856 1250 450188606 450188617
    0x190c0203070e07090b0325022802060412120908010b1e0f030304091e0e1e030403060204060e04140601020c0f130908130608090a0f050118050f0f1f020f0f 68
    0x11888900c04019440141c0ba0110900c421fa20441d4003181582c46c0200440150b4801c0d00e4440328562140c400c54000700b111807040344c2c858004503e0180d18003040c00101280b008050b20310707550718100c040e0b9401105003070351000e074130403a4000300c40c60781c030b2920b411401488205208064041014003403060006419074005500c12500035440d5010289148842100781410354201c05081081a00c1d141155556400002c3c0e98201c0300c4d00500320010b0000704100350b400940c0c0c020030555a8039101d0600400c030001c2c107840203025508182d0a030a482084441c00d03032060b034043c0c1c0105440000c043c10002c40c2100180f140303411400d403020351a0685000d0040c01c103080d006521b015600c4006982c0d641f141c4010340d2024080003604d0003400360700900840c1c002c0503181c001d90341c1e00d01c0440c5801d1890045c10005030b0140700011035500300b003c024010a0015071042e11030180d8080c40c5a60034440c1d180c01804544403007104030011351401c0380d07031740303174060180051001c00042c202106902203000d5580030 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 450191106 1250 450189856 450189871
    0x203030604060b07080412030219110901060206070225080114010302150f191b150501090b131d0a060209100507050a0f020f15190c0203070e07090b03 66
    0x20812205040c00c0c0504030080c81d0b800b00c05482c0903c10b0320f55006078095401014452424140c04200b4103108114000c80320104a0188942800c2031801100180000200321f029124620002070a180082030b464482e1509801074290340c044a1070220401d01c031181d040c02c0280c0c441c5030101c0c2c000d8003485028000700c000721120700e0fa541107004200e5540d0f480602e161540608102d841700f0518410156401c1d4504203481075a00d41c018003058076454125091103010b090800414814000780c0d003c0d1204080740564100816600c59000d0415902d1101c00c154101440c030115240e0507000740e00c20070495101e40340f20042c241040b850541800301d0400c041d01d40580110b00300c00d83d8548008a01c842042d43c0c104240740c06099178a140d02c0310480040609802d01c400d000d48255101d0103800d503403810f0000c10302500f482c8a118200241d4114002603151020280710001c1c895004141a924032900140182039051800c2030441024100907c00c00c100400300d9030005d10103076890302860042c2103 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 450192356 1250 450191106 450191113
    0xd0204061709070303090303050706110703020105190606020c06211003050c0a06080f040204060509070c0b1003020f090a0f0204060c030f18170c060c030309070b07150f0f060602 78
    0xe04014a07000000050212903254020840030000a5008a00c01c03044070f50500b0880d88440c01401d0040042c11001b8a40e05614000600b0208043e410341c4a00c3c410191070101c1c0c1070200304083c00004079422405550056070110103c4c010030320301702003c0c0582c00c102600c4010b250001c0241c0c1d5852100540b89000c00d40100c080078000c01909010b08850b54006070384002e01c0500d400c070000d1400178003a003410000e191b04004503055440d250052006801e0140c19248241810040202206c51041c0b09403001c42c4550041003944512000120460b42c0061000d401800400304003c030151001d00590640c3c0d9850300041c60410007030019000500d004c0c0c850f107034590b10604003d00401520185d0208000a000c460311904410000001c10b0340d945040c007021000c59408480d103007044034901035900590209810420745400001144580c4c2450140c0d00311070354801c03503100140114040200320f00c8a41d408803400301d0003507009210a40400402107041da1200d0300000803290300340c100c80300580 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 450193606 1250 450192356 450192377
    0x10318060c0c0b0c0304030905040c024204050a0b060612041b150801170c0a0f1a0703050f07060b061603030c02160315021201080c01021e0a030c03050d020406 70
    0x11002c8001d0b60304c000500da0ba14034501e45503800030320841807030045a00c50740d61503a02c161564400c2000c03c0c824501c1e600c0c0d0380113000204603009400c960301e28008021045001d00160104003140301d140c09603078450010401130301a540c5000d8024002400290403010030720030808890b030f03161200c90007140a200f05107016404403a400e05684482d401c0703607020500241804600301c1d440b03d030b00d50448800b0140291500320841400341840888020305034440c04101000c501210105c1c40e58040317034a2a69003c3e001484007050880034001d2110207400b280b0107001d00414010003900400b0034512482c80000c0101c0c1900c00607510f038205401c0001560109401001010340600c1052403d61316030002b840c071401801445031411000b404014103001450040b40c4100720507405540540b40a1104c01e0740c0e660311055540c0d82c0d0504004003d0051040c2c0403500b0200044e50b80628011403030740b0141c0201c40d0b40c0e4505840c5411000d13811010000e0800c60b0403001c00c81403000e000948020b5503480c4018 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 450194856 1250 450193606 450193613
    0xa0e030a081605041202010e061306030e07060906050a0c050705060301030b0915060f041d01020712020c09060a050415091a090117030a0f03020f13030b10050906010318060c0c 77
    0x40c901401c490b0038040104000d1040701d0080780d24004c0c65038240380a5640d44042c0010504501602d040e1201c414011940030a0030742e0035800c2503c4e0b034400181250480d0360380c0d040880d040b050318407030b01000c0b840070440c44001d64402c2031301010040c010390440385115501e1010884640c07003688151510b6250000f0320914800501440281550350500f002490425a0000e101d160110184034400c0b5039800f992440c0d9000c403440349081c044900001c5486006a0400e2650303a0700180e040001400341280760b04807450641081801240003900114450b0f09100030300c4001e11482d1860300b090fa1f4401c90002e4084054050020104941300314504038030602c0040c00098031040e0043c07080c1c5251682041c90701000002030f03d0b02e500062600c0510103202d69001e500034030030140b44942d080c01c0021500d4840800d14481c1c0101c900c00c0c50f60583c2030343c42c502c50b07000c0340303810780501a841070320715010454640c800d03046060040800d0008002441c859500c0808445032100c681001c140e44468050030b0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 450196106 1250 450194856 450194881
    0x2120a050702041802030c060901021509060717160c061506120b0603010305030a03020306011b121e0903030315051f0207120c1a0c06090714040917030a0e030a08 71
    0x191030303150071400d21303800d00e0340020b444a242849890150001107820300303c980c0300304043d48000901440c6100070303040110395103886201c02c96100d00442d030954155036030000e2408032244078018940c00a1102568460104d451107060003003910003d4450501c0030101009844507030003031010761500b4480300494401201914203081c0101e00c158024801000400c3c404002c41d10001058070307005a4903990180107962142c40001c48410340085414000104901c102c103030350440c00e4a84508011400c01035220b10310703081b10301540c0c000403210042000080d002e50000c1c178040901061200740c941d141c1c030204158503c05662503404040310f90b02e003841d02d40c060001c08040d204d240002000c6400e1a105c58401040300c4c49695800304540c1480c2400900000c107680d01304048000307403440703070500c4182d007a0741c1c040341c0c018516496015200d0440704d02d401d200b1260740030b80c4140080700081404d007504001e500020001c040090320f4003070308009010148000c12035030202c0d860b00344250801c2e031209001e = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 450197356 1250 450196106 450196121
    0x9170a1b05030703060216050708030703020c270c0c01090606050405060f240702060d0e0114060a0b090a081501080c041806090f0602041d0a02130b03040302120a05070204 75
    0x3144014400e0025860215000040e00e82100c4090781d11701c0310480d65a014403031038070060241c3c002d6403800702c0c01c4000400203000c0c1d41e019a080b0780240002c601003000c85070b04a01c0c1060144c10580c0e50b080c0c0d00000e050100da03c94103e03006581002d1303407822011701391402c90f1011a40a951244107000030b207001e12605400c10345c1074440c244d000e02c1d580041400d624441e03203c89202041140c91141d580495005c4401c51540501800d44441c04c2e03406e40805020205001e84c065420010001050035008801d5031007003000900b140c240b1850000e40745211b81c40800c080e0740160700031001040d42070701004039034400110300e002c1007820761401103210301302880c0802c0fa81c4a01e04090062801808003820400c0c0c0701e4010f0340001d000e0103507140c060200030016100920701070002c580010308001400d04401248a070503451042c0d43e0719556144101e100c0e42103020f030740190300c000c04c0c0b001e000d00001941d44503110340100c2e03901501048054500c0d8110034548000200005a22821401c1c140200c06 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 450198606 1250 450197356 450197393
    0xf15050a08011503080f04030512093c1c03021f020a0509061c09050102032406030f1807030b06040c020d020606190e01080d0f0503010e041209170a 65
    0x8000812403203000c00c480f40070300c009014000d020898030b0352240d091b070032075008551142c200d5800c81601030407801781e82c1260280e288603c03404160224060f0070910211021126440900d100c00b200d050090068160710315941c0c0c0240305c1210707071003002042d944d101014a000c1d0f001851140345541a2106041c01c002502e030880780188480c4d0503041c0c100096407042c6400301d42c550344603000c2582e15645d0300c028600000b01c590405070400d003404410b6000310701032030080006841c101481001c0fa070350890f0403030045800c07040404c00034241041340c0318442c0d0010090902034400c0a00402c5880c600340c215001a200c3c0c6210340103001461500703100701d04100495001078040060050006900c49000802190098242254419102d083d041035038000c1c1010401100082d611030214503551400f07070302440082025000340350321076400780b425203049407205c42142c05070f661a40c0d148008103c0d03854484062002c2440d01080c6002c2804403480030024103401007040c0c00040c20071003201c102c01c2100c00c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 450199856 1250 450198606 450198611
    0xa0506090702070b0702090703020d0c12060803120103080711061206011d1f03062c0a02190f1812030e01050f0f070819051804021602090a0f15050a0801 67
    0x1000b130014000d042d240e9064044a9880309581c0c2c0d000c0c250040d00c107150100d019149000d20011540780c0041502e1082449030208100098a840c00b5668a2140c85600101380a0303040042002034002e90080c100940302da0300202c521100b0501040550f08a0081c141c0001e01103000c0055030b5070301020358454442807210940400000001145d035980e003a103603c181c0c01c801808803100b1a40207400042c01821501e5044000040c019040c01e20750341c1503042c1401e002d8200000c02c111480e10300903105a2460348014800441c0001029150600c071a28146d050164048090000f83c0311403602500908120765030140400302c5140c01800b20703d400f489607050010a01440304186080c03000e580c10164031400040c3e031004503081c03807840390151030b02800314050030400c044980c44c1d000307002d00722244440c00511a0102d5440400084e80200d200c2100700301c0c10100d016000d40350030100c07150021f0889000181e40303502c0c3c03001001524030805884402d20142c4c00b04100c3c03410240618801442c000c8001c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 450201106 1250 450199856 450199859
    0xf090b18060108060d080408030a1403060105250209100315110a0c03050921100b09040204050606070c08072c0408090a0803040f0302100201091101050c01020f030a050609070207 78
    0x3448684005403007981003080440008115441e2800181040380d00031801944a40e0344454941d40ca0340412000d100141740c10080700485a0f0b03510903a802158161a49820582c080a8000314000195005406206002c2501e1b0150b15002c2d0b8550003601141034008203181075091901d1038504809440400a1625040c604c26101c1c0d807042e50194200d134500302c0c54078483c50504449501a80311f07040d0340840e121f42c21000c00341e41c120040d0003191200007901d201e03100c41059001101c1c488a11550803010000000d001860b1980c800d6a11039002004203003021810b07200e0b2034810380d46811800c80f0717a01c114414003158440c00e603d041035500c082c4140481008801e000b00d901c10f00034100802551005c268131440303a4a10316284c0261003210200c0792241e03a61012204168242c1c40282d01688003c12941c0e080e52040c01003051240d0402402c084c070352240c031700440e041e40c003581c0d002649550a01c803400b840e103810707402980034150581012405003007290070031001510240c9454150340c0003a00 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 450202356 1250 450201106 450201139
    0x10b180c04090609290f0f181003050606120a030513210b0a02071502090f0d060c090b0408060f07090f09050f01090212040f03050d050403020307350c03090a0f090b 72
    0x6443c102020180c0310561f50720710701408114500007040b401f03a02076807220104114465602c5c0b01d201141e01030740c21121162561340170300c40d0080680090302c40507080b00340c8071800700340502c0003409200340002418168941e03403040c00f031f2240204e0b030200c5080d1030340328440802d0041d2548541d030403000c510003c520b420341c01d94031100003840c50350090100e1303500810008040ea55002d0022001302000d0007081c0d800c081403410313000030450080400701058680b030f80810105a0203043d034059a1054000703002e282c55402028821440041554040010b19440480d40300e003808018002803892150200301400c00704002c0c0c0e1140340580001c441e1510510205000d000d8501000e6041908401140583c1e007533400e00b2901442050402501d25040009110425500000038401d41d07003d94400d81740c4164038002c0607a10000381e10b00d0081c1c03441e03100f0080012120301009011004000c01203c1c9810303c4403000c41e2001c40581c0c4101c6611582e08010000c11910340501d401c4c042017203d517421045074402 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 450203606 1250 450202356 450202369
    0x105091516082d0106020d03050c040303030e0708030c0c0f0607021c060e1f0e0105040c0b0c03130b030105120304060206011413060905060111010b180c0409060929 72
    0x1c0d40404020001d00881c100c85040c1603003125400b01841c00f0300b0400c6040f044803070300100038404c0100501c100d440c11b251641c802c1c418903020710881c43c103082c13400d071441c0c0b022000303030403840b2103009075009461001654010400c010030918412078060400140308500704803400050b10001c50180800300039803801a41d90317a80740c2004590000b0304007094103141c14000003c1020b640e11940c24031501004212001c240f07544105480221041400901d0032001124284e520542d00244641a50081803001100740c1000e4869a0704080880f810050315220035204100c165201085e41540003005000074141030700b81911034840344c0d000f1843c00d861f19078025940d500501c80c9a42094114000411075582c0754070080c0c61996481c030a0202e13139251002440204410394221380480d41c1c04900d030100103010b000d0324403654801006010f0018108001c1c0c0121480100000343c00b000800011070038078190b1103644041c001c04071002582c00206041040211640c0148402288003040d8000c40c640d21034 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 450204856 1250 450203606 450203641
    0xf050405060a031107050d05070b06010c02030a1e081207180605180409060c03240308030103020f03070e0405030310061409040b0303042616060c0b2701050915 70
    0x786400103140c4c110240002a030300842100800d1400307840c084008a590141c09083c25070300480f01d40815803204801951403d2304403070300030340540150006101064542900f109100c1c02440058910380440e5110034103540b100115101c0440190207001c40e05501ca101c517000803046120036031a050800c500500b0300d00a850001c000c00c14800c2d140c0f80e00d0380b10341d0041c0d00000e074020700c240206c490410003d005850400d519603003901c0130f40e42c0c145520304500c1129003100d4200000d0b51a59085400f4030100100b000006038051050520000e5104044024203105500800c0516141c0c10051195980311600da400f01c0100043c844c0e0350a50b102440e41100c6c01003100b01c8000840c0e11801c00400e0860140e07902c0400c40301d04403038541820020042058122265000540b0010b00741c114014060718403d01651000540054810000590721b40c005c036045191203401c1e40c0414061003500039400d44001d00100c142e5183c0303040c421220010010001044040000300c1c52900c2c04100340c40509145 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 450206106 1250 450204856 450204877
    0x6181103011208120109020309010c05090d030e120a08030103030806010f1d130f0b030c06030708011e05030a0812070305090d0c0c080607022b09091a0405160f05040506 74
    0x14203a001c02000104000ca860132004507803514143e41e0360740c44000003904102c50700340065080141707041910748907100b1169401801480031283c801652011101c154807910840d4000da10700c0841404803038100800c030011440b50030203d07581c0d81145001040500043c000341d042c041d02c409041030980c1c00600811812142070b1110340504003003c00900c0072000c0a101d42d0701545007d09400c26456150400544003c00341d00322800480c5607000d1201e61700c8210760302c900050030342d0018007525860b40300b0b0000110700d81c0d224545150310340c40003e0030302d0781c0c1540480b0460400241140d0111000d03c03419405940e40c01d040005281050382c40f510741300e070300071444c0410161604510411140d071075000c0103000c514045520700d1400a130069650031040c0a501000d0071114a9140a01a80340c80840707040d4407680d4102146192001e6076000d01030250101d11250400030400015894a03c1024490180e00c0450f06030080788442c01303000c900b405088502005010401840103895000807114019a0b = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 450207356 1250 450206106 450206129
    0x21302090d0809030a020d0b270304090902061e0301180b0f090a02040f030b010602060f0106210f0216060506030307021f020a050d030603150501060c020d080d0f0618110301 76
    0x45800c0000d0808402190095200c4401e0300e03140d05200f502c00b0442c1c8031309c00900c402840b00340014552002d01d0409810a5210f600070081400601050340150018030b02c0a00001e01740b0703032030b0650141d040d000d60342d0a201101c408001007001c031200c1f908205c1d0020b11640100404131030600801c19050700a5a09030113001544049841e0840c0c030b41c1140e006084c12004e9000e400d4903858002408003007880341a00502c520301c0826034440c1d803104501d040f98910b403203088a00014481400d041c0c5080244048940c0d6100c841c4400f00c6481d0001b401c8a0a2220308032580c0503581c0303402c90894401400c114001d074410300050006031a005400850480305041600110381c0300002280b9050311010300400f1802041c01d0380401c1030f055040141903d11a6407207280d21207080725007a00f00e410900c00c50001174020581000941000400c2c3d9200760f006100c00c600c1c242d1030501401c280c5441182c00324800d076507901c08100070510f8028050014005000a01456403c01e207913855502041c010481401d4 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 450208606 1250 450207356 450207367
    0x90b09030c0904030e030f01020c0f010506180405011515020d0813030e03010e0304120c050f21161502011103070e090919080a02011404080d0209040213030807021302090d08 76
    0x1402101c01c2405d80da002800c86000403010811503000c1d40084281d0340681c42100c2048242000c1030162034810302e0041d100d00c03c0090b00042c9000000c46c05081030710f00e9561150880d10b6541002204000761040b54400c18214104640c024501102503034210200640201808200484e41d120104829014903001101c403101e000041d00406041d05641620b1100050001d00498000c0800c11140c4c040c41100c8540d55a800070f00008502c11340710b46a020000013205039098582ca000c51441000000072035069100c84c0002d0034802c2c6254000b0745c503406803024082c4500394240500a00c0e2442028080c1c207508000101510150320100b5503440b0707040010001f00c134140100040c00703c80180c61410a0200c40604120b00d050340301244038401542401810b03500d8141c10b00c102801a5444202d051070b0011240490f4000d41280c280750303602a40806c401d00003c0f80611804014501654450ba55000c9520421400900710f111100400f8010701010843d42d564904101e50550400907450341c0c0d4 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 450209856 1250 450208606 450208613
    0x506060d0c09060e07110a1203020c0a0f03020f0708011803051c06030b1005040c0206070302160203030d15050d03050a03050c07060510060909090b220c06030c090b09030c0904 77
    0x1103841d034120300c428624100340000c2114500088500a8038580c4491490b02c484404a03902c68180e010050200e5100c240544110b901c258002c0490700620026200b54401c2540d910219941c0c1502c10340040e8401781c40c18610b04c40c1400341c00c004014244c0200034a032110b078111b400d012540e00380541400804690420350131408066030311004030a880c20032146442e03103821142e103001074a052618250a65000c5520f040c41d116070781c00025150020610b607640d0260440c007942c0420151078a070b0700780b18071701801030b142040075154492240b0004904184414804075640000703600080c032414450714400c01181c0c01400300c918540103841d0124103a5546010050f4920a158008000c0f030301d4041001a500e038142d030102c058030266591116001d55501210381690100c0c0809810b400c0d890022607461400002c0103a8818a1080040444030320f503100d0906041c01644000f01194130b4060601d8650b500c003445c40081c12a10020314144445607011070fa4400340d1140300f41c0a420200c012030f062 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 450211106 1250 450209856 450209873
    0x203071203050712050d0609020a02061f180b030105071716030b090a0b04060503070605040b03060a1203170105030a03200c040e0a150b06070213180b010602190506060d 74
    0x890350444c4240c4001c03208450020401e900c01c1d040780d0401407500d80d02040e061000d00031070303400401982c000e021640300c84041402c0c6c0c0254143c41084d0000311840090303080003a00e201d400c000c14132240000c180004c03105160075900c00410301300411100c07202d5820601e2444041540005440300010328510070903100340c00401a0070f240c10380c070121030002c01ca000c0b51213411520801d0742c20340e01880543d984400745540e4602602903103011400c1400180407a0301d400d070107142d20140007058042125900c4040f100ea8100d501401e80009054207480d0900c400950030080c014401030f00140b0f068115500d0042c10f01b429000c1072080c81c0746100a1840650782001441540c01000700104012407200840942c0e5440020301240d00c008220880781b5000382074414180c4054015011524003880d5908104102d0751007440141c490780d0303d030444040c0c10300b07104550312500e02c18003040c05113504008029150020b480c007103034a420443e8400d440000c10108010b508154103460910f01d00c102860319102 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 450212356 1250 450211106 450211117
    0x703110a0c0e070216080c060d0f06170706052109010e0d0801060f1d060306031203040b0f090c030a0210142703030f120403090b0a0c05100603020307120305 69
    0x9007851000045206030058940c107003d44015000c44404002204a00e500b00c1072030300c517011032500030b100c10343d40900303000b001050302d8146d070f4200141050b45070f4141412910b0640103071200780f84070702046040110401c4810b0107044641841410020b0394848a07081010341c500c0c0a0f24400c0d440040396400000b50071985444900c042541c0d03850721002d5004103910000d02c10200094209203421096a02460f00b40d400d590a48119411000b800c409100d4194006401507405101e441550011182c601001e1401144a03032018102030030b04c080c550b8000310028040310520f4100c041d0004d920348d800178442441d0366050f2080100780080c1c000c00d9400507030114101900000020b184c9c150100c021003002c180001841c91000385c004414107160342e9016440c800300d10071070100905d406150551030f490364811b100f49081607255884680380384198010b81e0041000c2138200c11278004018060000f0b40b054050f050302005460714680000f03940300021300c10080070200d4a8036000515105000702c0c1c4 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 450213606 1250 450212356 450212363
    0x40302100804050601051903121701150f0e010503060d0606090207060204150903021e060f0a05070b0a2705010209060304050a0b010f0308040e150a0807050a09110703110a 75
    0xc40e80c035644041c01550381202e0407a8240591000030805207416205241032003c04203050440d207086580d294465009440c1d44001d000300060b041e0b88031183e20211901078886000548456a903440c00074065411048002040c41404040c0306400d9902c01c054940c4480212900c1d100ea2040f8144039000b4980e0760040140c03035000094003428814181c0040041780c418503050030b582c4049a5089820300c800d070200a5001e4008514a02d600030022040741760948001c2103079160440f220840e0005a1200e001e0700040380011401e0f00c2030280c81c2040a0303101c03074141030a000c480c0030b00030045152481c0a070b89401044a003540402440000d40c141c800ba00da003c2c090302ea49040c40c0c104103a079400311080c1103d00035951000400c089084c20022021250f03c00500b60130301d420201c000107031280c002e00c6500745e51102c0d00040c000350f50703c10400c00148010340103001d500b401d00c414050000c41e01c2d0415203605003048004070780300351a070382120000754141c0307000410502108a001d04242038070402a = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 450214856 1250 450213606 450213619
    0x1b05130c0915030221090c0d0302011418150105031020030112052b0c021c2012030d110f030108030d0e0a110f2806030605150307050906040302 63
    0x1c03003071030783c05030300820303040340b04070900c40080340c540408116158040f030b0300c400c2d650858a007007a110b0401150001f100c41c881c0c0004111208481c1550b682090201c624400a180d84d0740074404075003081c00501e0500b007046100000560400010a0741c4080d103542c001800f959402c00320301c04007140a450b802500b2461400340d507a5940342040700022070102c0c1c05840030b009541a410300c680509994004221200007020f0351589540c106590309811000300341c6c4c00007420b40003403001040d02d47d8243c0c0118458481030390000951081020310b82c1c00c04410301e02903400c1080032001c504001040c0d030701e240d13149c05020800401003075024042e03026011a03000c4c1040048004540520040050061700d19924010000c21480d0901d89684507411040504032501c8500700310014181240303401c00c083c40c040d00c0c0801081d40030545041c0031003503403103043c03100c1c030406001d21220b549801420020801140d14841140d01460718160724400641560280880012000f446803a05400e8500850f0014040e = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 450216106 1250 450214856 450214889
    0x306130c090510020c0604091506080106090302130f05130501270822060903030201140f07030507050c2b0504150f0e060d090b1602190516121b05130c09 67
    0x205d4010b461440009c8441580c0c403071010035080c2c41100380e0f034103da070b0903034960380403e1840e000d001490040714440d860494a40038140b45110045c000c2da80101911b034007105a84d40320b400c0a0742140c041803900c0140b00c96540c1d00d00701c082409402c2410440c1c018555544d80c04c031600000c080c000700c50180101395540000000758041d0002d0081013101e000341c0082c0014903840041c87c145490484444840d0300203c00441c41c400e104c1c6c0e1050382c0c020068200540344c40213048803140b411038050380f071410701000e00c02ca1800c041c0380f940350941800c03810b080150403d81481c0e001040c0d00840d0740364108010070300e204d8051a40c1729a02e1010045009080d4568a0f245150024041c01c00e8038000c1c0e8100d01c04001095140244042e154807030181980a80b010003102044901d01c801d8000c403d90701c91046682404012003028554001800c840308007021134440361030452040e07034104240380d101e00523850301002079495891056440350140e603070002d500c020414080d1040c24082d00100e00c1c0c0c4038072041 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 450217356 1250 450216106 450216119
    0x105060a12051e13031124060f1c1103060705090108041b06080106030c0903030206191b02061902091e032a13050402130e0703170306130c090510020c0604 68
    0x28160300314002e956000c501c1c4a4081c045642e161003d619038800440c2c03007c1901d03140344410207941c1103280101140340b620702e8440095020148140d540c0100d030300c0128002c08105004688807003818040d000380000b46007a46000e4140c0c0207201c00d140c14030490308009420026408542015136280008001c00c1540310075008110310024000d20b000f01e03182504050300540100109012290f255000380b034076541b610309146d500741c0c00c1400888140d48654040035505a010285141250203074014039581c98402c050190030500c6802c00d48095204202da1038484e21080240412610700b4010b030480314500001092030040303c044030302c0311444090341c0c007003910744600d80d080421201240c0b031152041c0c0c0c0d48000f0003101e030190360003503000c1044e2442d949184103a800860340c0d030902d80199a4030560340d458500100c0d070b94050402000000000300404c62a1485540b0462240c040c401c014220403000040c000041600456115116240c034110000e4420811841036240140c0304548681c1e03950f0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 450218606 1250 450217356 450217381
    0xf0f1201020f07140a020a03170f0714061305030406030c120c030605030c01020d08010e0403090b0408210a0509040504110415150509060d02090402090a030311060105060a12051e 78
    0x600c201d40200d8600c0b90030490341000105e1030380f043d0700240800d10b140c4c03541e074a400d030040d0000c0c900f28012030706104243e502403c80c00034100b124060440300103001c0358440814104100240311400c6000c440c0a4000840c00c00025a001d4401c02c1c140042c00d1102c0345030548404184079850640e540c2800da08284440d070680140c07003142c90079801c5a141d0043d0030010398842d5203003c000700029a42030010412041401c2c8020b4002d4000d0401e11482503d901a82400c2d0784543c002d8141036000c0c0c0007a00c4110340c3e210108142c1c08100c06207030b040c00c0e00540f00030480d110f9904894410381d112004182400728541194030100b030000c0042000804031402c8070140c00d280d2044820480000c000030403440c1c0a0401c403800040020040b520f040000c0840c3d034003d40004810581280d420f101481a54480b1071200b00990301a494007071414034011055490811705030402806544180b00751001c40d60080900c507091500203c01152981d102c1c115205480b0182c0941e03040c00d0740990600c9001031400 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 450219856 1250 450218606 450218617
    0x15060d0902030d03020f0a1808010507110601080304030c030221031b1b151c1103220308012108040308131203021e0f0a1b06020106050f0f1201020f 65
    0x35801d440d5610f5080c0c0065089000d1b042c141d844490041050f0a001362007103c41c00504080c8007403404250751150041400c481d0112207010100c1c4104c8070103a40c015040005074010915a070045241c42e040d03607a22042d55080381300080c0141b0a41e11803c000303411040d424855054a14200e0742c0300d44403d003c3d204400c444111441c00b5000e144240c0c150b0071000036240c0e84111028144050440c003503403940c0101c1c5c0c0700641c0340da5469207409030741076450714902456100358080d80010b44c0301d003448000c21940d01100005411880c0700440e9a80019422542e01411282418801c00102d440303051000d100500d00300303000b494950002004020000c0d080d010300102c01d03888401454154541514001c1c0e0f4603108405805a8041c0081040210481806080192940c4152048401c0a0413500d24046032800d00b111b8121208440400590031480060020050362000380011440c010200c0c04c41000d003000340e8000c1a60681c3c0b05d0450302c0d9011601d00d556100710003199541200d0b6140ca83d40c1d04070 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 450221106 1250 450219856 450219859
    0x90309040f0f0c2c0310020307090e250f110a050307030315030812101502070302031c0503060409111005030406050c04270e0a050609060f1e15060d0902 67
    0x3058642c1045502c55507040c4840641c90139440d540c64401c0c4003d10502021103051641440f60038094a900000c50010b14081c940e2519071401c000d0428110010021005021044182c000e81106401681034100084c001000d42016002055030031000c83c1c403100c81e00341142d81e600c01d00450804014000000b8035440b4000c2d03034200032110702108620f624050381c0c880501014800e00c0983c900b000364110b4160800400c041c07880d40c43c1c1c0e44007074600411120340c4032500580c00c100010800e5080c14002c4088001080600a004a0702100041c205000203040c00740a16500d500c0c035420001c0f07400e11000400401060840c18040c8042c00a220790b000320303005c4400c182490302041c00038400c102510182c0760190089001ca5003180c0810240080e00d4000f50360498807a442070030030079010b01c5010701d1240140090715291500040c018504a009010625292030003810448071102181280c840300305140c030440015220078452287d02580340700d00c1a40304100051003500032055500c2a040c0a10 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 450222356 1250 450221106 450221111
    0xc0a0c1a07020303030c0a1e02010e010b0402130e0a020d0212011502010207080f030901142e0b03010b03070302040e0a0903030e010908041a0415030203090609160b03090309040f0f 79
    0x1100034505100340901e181c000d41540c02480801c40c014617003c081c00212045150032000c1080c40001d088449450120006c0981d5490f200145030080030b004211b014038043d60194503201d070907420440d5029031845050740d0002c0b800c01040c090a40383d0100e80503501076040039500e030710451054614030502031003104103106039001c3c0440032034018001c0c2d40798103404c151000e0600e9100518404698802007031004255a40d80040c450131501d007104501516581d010b031001d9001400b0305c0240d0110360b0310200e920f4840c0320010406480c1c02c40132603066850030318002d0745945440c4000e50290040d9004100c034910814100000c50000d5032180300340074041d03038041c410000540d18050032203803000c00180030303a0000c00090240740c045051030503025a01007400b80c035050ba54140d0b40038030300d041c60316180040d0700013061192001c0c2c10440c0a4000d40d4882c00707003000c0004001440c145009030300c01c03000082008000105007443c2030042e10410b100142c030034001c0c820f0541d844801001400b401d101200d2 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 450223606 1250 450222356 450222389
    0x40302070e010e0702060606070317090c04060905010e040f03020f0a050c010311031005120a050a1b0509251b060501090612020321070215030a0f0905061501050c0a0c 73
    0x1440c2ca03000d038003030328950700071b400c5940320701003402031941c0415010350a10180314040001c191444002e03074403842424004d4081091100108400d903000c0e94800303034113241031100501481a242c041181c000b40e201c40c543e10b11010525081c1d042131981100c00549011760701025081c8180401e0b00050003000343d07420820109041070103c0640804d40e414821030350f01000520803801d05419040010300c4000848450071070307582d1000d241c881c3c591030444041e0744d9450000c80070070721301046002500c400c50350490f0502d40244520b401e55000c10480038100380c900114500b042c00b448000030030702449103108a442c401d80c00d22a0240c0b03028850f1024551800301d0000700c0c1011240c00d110031943c001d01401115030903001d42d0411103400008c4140c5404204040c030f0060742c405581c0010100201c030344c01d480e45040c8586a00b2101e44a4403000040d0507c44040c0c000b41c2c0118500ba4001d100f0340e142401280600c004850a01608410f21711034800e0240e1a4203124100920300211500409480c4540 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 450224856 1250 450223606 450223619
    0x804030e01110c0d03051905090f09061005031b0f070308100b120a0b06190f090f12050c03011d06130210050d231f0806060f01020109050105040302070e01 68
    0x2290005000c840740c1002e003100c48546001c00340100140c2c02854602d0400174400c1c81c040c605008a05114042800002c0c0343e0000d0420261040ae40703a011202c0360340300c1c501600881d0040c5107030400c220800c2070000c0000c070340c0fa0000042c401e810181214807a124240e00d20180855880064103801080e03200000800841d81c141c480d01c140c0d440e41550303604184035010410303403801d806008082035035140c5200e00070740d03118000036011320008460300301000d21550002078400030300c1c83c500200b00490401c00340654502c0f04400002c0f541085441c50419643d410118207040940e40342c10703855401d0051b00420140d440344060035402d8810141c6010f030f02c594105071b50503256040c000790440c00c440b06601841d0b016101500c00500032900100c4c003181d00480e12070490905501881040404d18280b0860907d498603820495030380e01c4e0741040366410065200d9071340e100200000d204505102e200c84040c0d2003900038041850744000248034509040c80c0207519154503004583d65650040000540f2 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 450226106 1250 450224856 450224867
    0xf020f09090c01050a030f150f0806090607050702030c1503010819050c0d050a0f120305070318020f0a1a0c210301060e120303040c2102180a1b0804030e01 68
    0x16031400002841c1d80c1190b0001590036802648010003499514804140030300c10a004090410224544010714982064070504113280c60f9008001683e0003d400c128080c03400040054000740c4034200142c030f450007440041e14055030100c080303030024a80544021604c03140700203141612250f40548200c0c030000c0214540c0c91007100030241041d400241110389a050021041d00f403180160140c4104480603100d458800940c50070440b0300305a0301080c1c0003619414428550000d00d586401d000012065602c035051800e10b05010f0720400031003031005510354400b0780b080c00034121610070f201e24515010500810780c22810150200e030064024100014020ba0140c041304000503810b80d041da42421801c80304203284040d055041407030284030305024141080550310440c4140051030280c0d08103d01680c50220104a1000c0c40c0c03000604600141c1c0d81d4803030b20b480d09164000c1d0042aa0311820802d0240020b4141400d0b11120441e101082e603501034071103489a8003030f0b02c403040615140c400442c0e0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 450227356 1250 450226106 450226111
    0x8190e10030221060a081203100617041203020d1104091b05030406090201020307230d0503010503120904060306020f030708130b012c0108010605120102031605070c080a0f020f09 78
    0x6420604041500c0c000c001d5080f50f0b80c000101500c0c00e420580c50b200000d2a19400f000400d1508501008210380d094120f05140040d044902e00850340d6242a001c1c4880034602420062040f50303074021140d040c034843d606071111720080c2d070014001400c92403802030242d030142c015014201d09010170760083c070791401e0f003907080030445582d02481e603039654440354001c4c5281c0c00c1c00ca04500080100d0390204d50856102442d9510b4014003521800080007140c0c42c068840d80c0020501009100401880d07074040307071080100c8003a8a4003565000e0080014004110030740004200c04d1000c17604a25030703035040c4086e51041c04143c461a5803030302c400e1002d807030800701194003d1400f4420001400108011141500200c182c07040030b0b601c00300700114003941180b00f60401080b90703655400c1000a841c03d10319140206580c13500851039814001050105001c0310202081409070000f144410010038294110040c555107080d91041c1469140c501c0c61180002c6051384580782c54041c2514a2803d03040c01c50 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 450228606 1250 450227356 450227377
    0x60801110f0f0408060a0204091d030a030e01060e012418180f09061a090c091005040320040c0516061104050405010b0a020607181208190e100302 64
    0x40c1010700284204805078004842e03015814000c1c0800942813000300709903402200c0c0c0000240c0c4482c1003112a00803603080d41d42040310300181d0072071740c28005004001c41d86c21590700e03d0041811001404218003406481e400201d0203012800001020b0701c4500048000c00031084600e0b600c0d003200310084032080d410025500f00784058181c10443c1d20b810010100a4907258030002c1081161060040111381140105407455626425500e0b48200308841036030010a04075480081806c011070b00c607900d8000c469445004480b103220b13103a0070030700840a0b00c2c010b41c1c1c4160701031001240c041454504644284900e40102d0902c0100c2032540d00907000d4070141c0810400c40b400240080c3c0350140a4020710110380314002c400c0102107035944481c0a840c1c0a01000c0c80d8031a9100341400c00246001002004c00f801c202c62850418048801301c40702d0400c03101c810b0340800310002c40d400c10320003904c00d9a002002420b0240c200d1400c0c0f9402c442500954001290022028107070a14258160b106024005 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 450229856 1250 450228606 450228641
    0x313031e0f0f0908031b0c04020a1403040c08060c09010e0a0303050307141c060e060409020901060c02031903020a0506071e030f090206131701110403140f07061101060801 75
    0x1082603030b1103500c07403640710199403900e4202c00c0d03900c400d103504541c02078074141c6855a200d04090340444080240c03180551041c0e404615200440b00010a905c8444005030380710360780040810240110b00410b5006064114103403007aa0510700749296042c5e100f00c1c4a03c2c0881c00c5010b50200d50b190143c120812240c040d113440f49190f4a804044592070b00000e1004500e05003401220740e10a071030030710b5180035005000e0000c1c03010300b011044540d400300140300d1441070f41400c0c018030050703c90068290444295003020a807207002480001e00b0001cdc1d402060b250200040d11a40038940d000455142c518040d00c00d403416134850020031180440400d00b10301c1d900c440f018140c1c1c501071103580b2084000700c103103400080900b031a50015003594040c0d02d0601c580d51aa135000c4c4034400c14070840569404076600204503904050302050441d004070310003c0d00b41c4800d609140c0322403005125040c03000c9020020f4641d125240d40000d00300c1031624000304040c0d0f20b812404200d94105100702d4159243c004800d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 450231106 1250 450229856 450229877
    0x90507050c0606040c120207020411160501050121120507080d1a040522020d0803010308030f01120b070e120706030509100203010e04080a140c0a02040b010302070c18110313031e 78
    0x21b501a43c850710b0304070b03042a40c41e440740035841a900083c0290342050b20f98140310701c010f4203142e803c0d00c0c010303006018412062101a01e481e00c4464108401e9a03100500076000401810140c0d014050342e00090040040003075203082940e00340e888614072a0500700c414405142010600044a070b00712440c841b074810004130841f6003014015102c1c4590310040001c0c412944c1c2d070784e4050b05600207034011210000084140040c80900d200030902400000c022010030702d43ca41c4400c81741143c00b8000c03906011034801c001100d916224040300f6808022001c4404940d903449000f070062104840c910690b02500d8114102c0050324002c84c0d04031f030102044e000b604d8541d500c40042540c040b444100502c102c804030307000007200d0700001d40a81c264190241c0241c40f171034010300007690340e01e82d41c0d03c1c101441003081500190003070840c1803d4510b142a40748600000c010b00c1d4005040e900013100c03902c1404410401c4901d68149918180c43c4655600b05100c001402940340840ca070245480100d13440068 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 450232356 1250 450231106 450231137
    0xb0f0d0516080a05090106170a11060307050307080a02041224110f0919030302150711150403050d181a060a03061802120303100f2d090507050c0606040c 67
    0xc2c5d42000e810000012041d582e501d6030041c915001c01c502c0c0ca250041a140e4051142c004503207040890b0580e0864a1450902001041488004c2c92101407040000100d601451503134199000b50540300314103c0e4070031003030400300883c100e0300d007403410460000c41e50000300e48500c0c003030b4180560200344403c0c2010002ca101800541154500d140c00002120000c00c010402d40c000200550003500a82a001c28080c40c3e002c62040041005050009246411480c42000944040307401c102c40721070a0b042d1034503e01140c180c450385202294807800e010180080c0743d500003070200740310701ca450110b401c0603440081500046007111a140d119011075410004a4507d82100c0340c0d81502c4103030103421010b103500182e0030074440c00d8109010390004c400c0010000f82540319002511528550300d0b1402e2801800891001c009919140c41000880c0e10400e8030250f1481c0d030300500b002d0071052140c0d1a08120052150f04102c528440e02e100f140c0c0800c207035003018070800c900034034160f6031082d10541050 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 450233606 1250 450232356 450232361
    0x30d020304020d1718010819090c03021522060c080706090503042c090d0c050a080f031909020102030421020904110f0306010e0103021002070b0f0d0516080a 69
    0x100107a0b00040c1468210000540811071090f00c503050342c0c03006489401280005c400c3c440303240b50490601c041c240a00589000da0341d641d032062510080c0114501c480ba245c038004214540d40005c0d0010200386030804041300c1072015020358a1000c1507080c03400d5178031103e0001606184a180702240c00b10551602242601c4014100a405950086100840b55036400e1455010340c1c0b042c04000300e110980d811141e039000301c44d00324041005002d1a03074148810310545504802280c0c10500c10820004410094144000520650003207011a2a1542c410700341c101a801200d8490305500108440c580054807407140c00091034060b4010740c00d181c20032440e034402d1145400b102200600d000e2205005960b0b02201c030384914810607011a5915040007401045030300e071402c0354441c2d008078006104140c2d00c0001d01d81183d8044500c1c04200c03680b500c2c140e082805a411241483c100018204203e1b554200180304e42030560000300902c1e40c440800c6e0100da40a0b01e00c544c000b07400341021464140c0c194 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 450234856 1250 450233606 450233611
    0x4170a020f0a0605061809060105040b1c0c030c052707140304050c0109050a14300c1503090d031109040c0e1806060f0c15010b0327030d0203 62
    0xd0048032551518120854503100014504440d62138441e41081110300700310000c00301401d04240070070101c3c20207000954030742105000d200e0203280d40d54503070f580959131784003501c041d80d813a0700044107403000900707280b08218010f002c25200355003401e000089038185050842c0701c00d003440301e6010000c0e40c0d5000e640380070300020b409003040006904113603000d005014002c40c012442403008040519540002400055565100600c541d0400b002045035401a40c1e03580b60840307040303c034180340d002140440d40c120f40ca08120541c001c20398000401c14108001644a101d150071182c05d1a154840821400248401c071800c899940243c1f84030b0007400c1c041d8121001d08283d500307150f801d085518001c00c0c00c403003007640c003180007400b0300e48402460700741400c0c007064401381001440c419180440101b50588034900e00340f1580071000a01d164090b10070704c440e615622800120450a594840700400c064205071425400b0012091201d40c15071b440c10b1005000d620a41d02460070608803030308103402074100 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 450236106 1250 450234856 450234877
    0x30e011205070e03060105030f072904180e160302060307030e16091d070e15040903030903020c011701060309060b1f0909060b0d0507030f0908040614030417 69
    0x810011594032099004951040d07440d0b9a031444900c1c900c40806180120680c45140aa008000d81d070a00020100d810f074141c42c10494003080940d02d050300203d80c101191240c205c003074808a00800c2c898001059820324290081080c00400045403a143e00d07a40320340d50000c0200e850001c10001400c08a020b140e00c84030608000804070003011966040c80050700181c12500c5903501d051013112501e10604c2954601d038051402e102090b42c030880d0351040da501070000e020000f80000351503480c00150b231084500c4060810b01c80c1e91050719001d00600080d280c1100540510380000401d544a5248106190004030070050703d40d02e0b090058006143d103460580741103440e03002035541c0b915113458041400c4402c803151014005501d00c02410b20f0159003209070034608001d01040382c03034603550503583c00030b45140b00001d40d9125a901034000b40800c001182c482c5003040d11040c00e200394100540103d50300341e1603402da0381010440c001c2c035500c0100c40041060301582d80c1e02c0a80103168000c1c0517640e01c03 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 450237356 1250 450236106 450236117
    0x30412030e1b010906030203010b18130c020c211e0c04050108061803030c0702060a030902130b0a120b040f0c17010c0f08040f0b0907051201050103120219030e01 71
    0x8140301c11600704018401d15084a0200d041c42d0b00302568800c80c03030801040503103421030030341d4140380407158544a01924507030101ca8900c000c0d40341e0b50302e2a041000e219a20442000040f0140401039100c0030340c5075185c0c2c071410425140c00100c5d2401e01d1041c241002c5c20740034011401700c030a50420b400700ca4210b00f42d03007849509124400c5031550b20649010f07100004c0200b0592404c0d0b584100c450f46144c0350340070290401c1c800e00620320040d0003030715100350303040f602c10b61524124003088009001109010398840f8080308080301c0e20069500001100000741e950403035507a102c4d0380700084c80480c2440213103039014200000303010030096164503c0c0540b1424142803000d5a40745800742e118049080d41050383d561701080d40c1044e80003005594240e1071814244900e103456110200880012800540401540800150407c00034000040580001409604403400322100980289802d0001300c1e108411001006069800040c80c40701c1d2460f5260f42104510b1242c0d811929506058001ea06221 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 450238606 1250 450237356 450237371
    0x9030c0b0a02090303161203090506011a1e18060301060f12060e090313120c0501030c0908070b1b0c0a0b070c030f0803040209070c080d020f0903010903110d0801050603041203 77
    0x142c4c00d100401043d50061116000100309050180c0344601300b46a40c0d052505e40408000054004100c1504494400001030312a50000c5d04045d5184100c1c9110301c450340940f90030758110030014000c1c4c4040c00700c0300c80d450000180e4000f40483c1d44800c1c080e00e0040f038405c81448680c1c0d40b280c45490107103040301f440401ca06669071045c04000c1c0003076070421425040401c0031704001030700300540c170b0084c43d00c4511524140119110683c2c400000c0c0035207810036841d980e422050f60b00580b00e510007840600c0c00c96514941c0c0e85107145180c4c00001c81d202d0b5607c2d10910704402c4200014100c2104038004151502e80d514084401c013190348002400c51360f0030403500c800804076100307005400c4500d01844c0c0b0765a036482d1910401044076001003800302801101c410501c0840c0b0b0910a5940c540d00d1450010790390f880c48070030700100d401041c100e80c2e403540c284152503080540c010001205140e803481218040010000c040c0c4002409000311500701009000050200b0700705e24070039101103240d040005402 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 450239856 1250 450238606 450238609
    0x40513151125140604031103090901090903020109050708030d0614090a02070203071203030b0f010318020f1c0f0501050105010503160f05040b16050d0c2f0a03050c0108010909030c0b0a0209 83
    0x520400d090f40d41070b43c102804100a15130064a000b00c403075201350245160038000303800200500f00c18050354060035501c6845a0405000f5488001c4454005040710030555031406c00e5580c9a0000c1844200d17079051040001d4214405100b09002040c014104200c03999200300b0360000b034004640980e0305114071500083c900d400d44461040643c06541e002c07907011814010f11400b46588006141054a01103880c841841c2e5585c607442d00b640c1c1100c0b9402108010700000e40c03110811148a002582080f04c107100304480503120b080c06a1145000380001e0ba030b1807006403003500007140c5e2110300054410702e06100510480b2000590f0007541407050405407100c8110005030010404109030790f1421209806002d01007010100c1c003100d0b840c00f0781d003282903030360342226408400b48a924082c00040f400c10001c0d04254071015040d1018081c281074590701e0401c195214240c0f1341590101c2e50480001c6140c8580303008009900e42c060710781d0340500445584d001683e03540180640003441d8207202c4203896 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 450241106 1250 450239856 450239873
    0x3020d02183103080411040b0622090605060f030a0212090309010e190b0d09061509060e07140a140c07060810080705011b02040513151125 61
    0x4600da9010302c0c07111152100079400209a03240710301d000c8101e48000750000713a807003400241c0c01540100c03c914017518400101d00901599a0f0039a4000000b080c400b40740540246042c94001c1540190007025035207018100459000340145038100d079007044105054101d4500450b00544c010b200107140039501c5039a8001d0a8050311007242c1c0741c10006082c03a5541c1d028007000e05d044030072143d4160503450038208a05035100d500c10400070300c002140200f00044c07680e014103055a04643d0610413618050380e07034102540c150043c16481498a80702194600d09214601e101f440140c44100001d680411005582c0d0486100e1000300914000f02000c40700da490b0140000b542030100800344242824000361629900034003100310302d25003c1080045400014410080342c0082c20600c14503501454180707400b55a110012390014240010310050f14480f080202015005801241102404803d0300c2d05035201d810390003180b48000d014940805010001304440842e0900c81c240030400c15580c0c8820 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 450242356 1250 450241106 450241111
    0x3140309161401021b061605011e020702030f06090c0d0f1b090f0e120c0a0b1e0a0e1506030a14030c0607021207060209040621020f0d0c03020d0218 65
    0x20318002107044040350350f01080220307031080d58805c10310b4205801401140c8907001d01d03e200108100f41c0507030315003440029403202c0c1c09000002d44214100003100d510b100603600c0903608a000344500700c9a04005940401c1c914025003e141c058826a500035003046807100010005440801c85001684001401198480100c6144800c071072010351505c0c0104040380c00c0c1d8240f854800c1d00341030125056100110f068600c441e01074a00030345404142c14401d00d0041180b8004046140b40c00038081a1603580c40b1040d0300c503000001107061030f9104081c0c541602c220003851000c55115480782060030b2001c9011650068000d4110b07408800140ca48000454600103262006e0f00005101c502411060116035484082e50008000d550060b0303a042010384036104002c4d20080c0e000c00c00c01c07003568440d00300600074510407040b82500b0011b440c403140114103500081340300d400d0300c4030b20008074244a001c0c1c914040e04040000200c515507000d01082d500b10043c12640f01d80038032007204001d02442041030 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 450243606 1250 450242356 450242369
    0x3010810110f0a0804030801050a05010e1509090406020d0c091202210a030c02210706180f060809062d0406020c0102040e091603230106080111090a0b03040314030916 73
    0x7040717802d2134140903000b035006800040c02030840300301c20700c010b036006044002c1c01d18003600d44c80c01c89000c12440101c94018210aa03911840c14004d1106004558010345900003003070360104481401e4182c10341c0c0e0701c95203101d02c62094108007008400341c0b410300400d00300006185481250084c051040030b05040382124110b000c15031030065441076050140c2d280c0c054900b1072108042200c10448940d90340d0314203200e00070801008003a400300318501071131036070300510010000c0e181c001e48401001d013401d101184c20a4040c4200ca00162802d13401101806203902e5859a21512180c821800c8020703e000400aa806d9502000001c0394181f0910050000344280521501b00741091309266007094003071036410408240607075050012403d424503000c210160413511410b0f0080380c0b61040d0140c88140d00020080d482e0041042d115001d9500803d94102d00302d8483c07082548800395032500e0301054402400040d09801e5031005c04941d08011034024100c01c0032608801c0742e003071a40603691903680016 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 450244856 1250 450243606 450243617
    0x1120b040c0c0606210206070507080a030f2d0c050733170609041a0405010b0f03161e12052b020d0e040617060411010503010810110f0a 60
    0x2d00c0302130700c1240054a40c8004148650080400100482d108414064030a40000400b80c04214041040000030a543c0e002d44000300355505000d0600a0300040f100302003807104120040056020210f502c0f41c00b900a003c12640e44104011141107005102c119654801d490011800d500001d20489170044181510707150285860075000b002031180304c954007401041c40c070805480c0203407551944d0003502540d801c412a90303030f8109030040c3c40c00c0c440382c018020301c05401c2c08244201034002000c0741300d00f56090100100c21006240d0b40d44440380c01d0b40310707042000000340640d0346458801119000407102a04800f41c582145120014103640120344640c0800d8060b8101001e07515582c0b02070807910180441d83c0140c450194550946860300001c10107001003900d131941d10395001402a004c40035506a40103400309240d035031848140c8081d01c1800c2403c60b8a40150b00c148100e82c1030720941d40113007140e100c08080e60406410108490310070702c0c105001c40448441800054410003601e42d450 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 450246106 1250 450244856 450244877
    0x130303020705030d08011a09040f0b0a140607080307140c03070308011d072d030e120403030909020d11030f1b0a140f0c01180302060a1a01120b040c 65
    0x64505805035001d58000e8028140c02d01070131390030901107811600b61000f074078072107a806085100944540100694001c4c50400381c03215861450380174201c0001c0941c0d60803e1562510540d40c8103c01d03010091364001801c00c1601d00040c80c100143d5080200c6d8180803000c141c0d80105070003260026400f910380e0768000300700c8100349507111030301c903004140a0150840c0c201c088016540d004600034030788010722800209240c0c880c919694500c0c01204448100c0030fa0318403826006024012a1742c05415921595040000860342d034030407101125131644400200519109100e00a03410858040b814550b4642c0d1400340002038200651003803e40018019040c41c00443d50341d82810410200407000700240111401682c2001c064240c1038045100d59407681024911071000b40b01346070310004c843d420200500c60759016110700c0d0040510a80a890191b40c031780200138100d401c1d417100700d5601284081c51000c01d50107414800380c240c503d0790000c80d4040080f8082001e03038a07050b1072180040e00780d110 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 450247356 1250 450246106 450246113
    0x807120302040b040501050711060f0c01140621030403050a0b010816051513030807050106050111010c09060806040e070e1e061513031203020a031a0d081e1303 70
    0x254250910460608600307190529001d2031460095000751818001e0024031002407090754074500102c3c1c01c0041103980c1d81d0b03a6218003698950000c24209505600700041030985100101e0058483d050242c06800149030b41c1e030102c000004030385020803150008000c044081102030140c0b11120340902c1001d0644d514010300f06207070600d000083c5058040c0800144007956614000d00b0f0201110001c0e961200e50311601030300c18143d10340c0002e207507840004843d03042203810741000c0c04650702601c4825804200ca10200d00341d400d241c0c40f01000408030f150503ca0240100388850300190701410000b0340e00603041450b494107d668000884134001c072000c00c01c8040c0c00b5007542c4000c6440c50b40c01c001c0b40c01c00300081585c1c003003411488400f407100070410034206002d180c40a402107030024825080040b140394047c00035846001d2010002c4d06003140c075184030800381d9083c02d80a80190140402c06400d03182c0703a0441d01320540c0d40f0b4044051002902c0045295400b4102094400541c0c400062030b40c603 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 450248606 1250 450247356 450247373
    0x1050f010509100b030718080604110a0305100f09020402030901061a13150216030602130902030112060f0e011a102a1e03110f030c0a0219030b040807 66
    0x1d00c518030903020078080224059141c44901c3c01c807108654a03988948400e40c051b200107259070458010803003038000001d1880c500149450080340200312280031045640d09010859505000180171a448050441c10040c6641c1c4027074035441030701c5000a416232843d400542a64016504141c442c0e440d40e4003440715880e00c0c4400030804190040403440c10f4201304084c80c40c14010702c5141d078094903041d11103032624000d121041d011070000c2548a025926450000c0007900540203403041d080b805180403d0003442407088074181d6000103080c42401d0a40e030b0740d01c03020f4070f041c6900150b1207803103013014503003c0000d0041da901070042921090580c04100144240040c0340300766035040020441d0b2000d0310260345491100c8072495034a00d2145403207182000782040c0d81428200400b40301185001043c90b500541c940c003081c00900135562026585039081c0d6490040e442d10032220f401240c07030340b0010714140c0000d045200304131201e08507172541d07501d508100f518201c0c0c1c180d40010700050644100080030307 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 450249856 1250 450248606 450248609
    0x30b0a0b0d14041104050f2a040b040b030f060604030c0e130b0106022a0d140109080a050309100501180e0c0306010305030a0206071403010905093c0102041a0a090b070501050f01 78
    0x3078407800751514215080c2c80e044152410362322041131002a040704072008850449000d06050804a40e807a540ca40100c1008c0d803080352042000100c00000c14003603e0020112008c41e5004152840c64a04080c40007149800150400c600241034404007000074401d0381080c2d00070513598002d040022074140300c040c08020443d0022013004a4000d815031650f42e10440750501a4011350001600c0b20b013030445a0040c0300da110007406011000c500d0b8604540e1080041d881942c100342900d40c2d081c0d03035611510a482083c0a13040198240c5440100c4407903541d4812600c0040803000c88000442d000c020a0504034207820a136459000054160303082c54040000f160447e100b840c05075651442030b103640390380340018040c180c407841d1198042003d0303000070481004454604502c03003450420b130808240000309034203003040c0c20220540366081d101c1010310940e82211941000c085d24404042045400c1d94405e0151400781300e044440460014000c5d4041d005071031185000140506250070f400b00d030705405 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 450251106 1250 450249856 450249871
    0x180f030c0114090d05070201050c010e0601050a0501020a0308060616080c0102040f0f06090909020406081c081f1406160303090c0b0901052d0a02070e07030b0a0b0d1404110405 77
    0x10410f001c0c3c5032500003004000d0358014034245445e61064801210984034040c0c000590390b00b0404030750f001d0000421031a048800480e4403201180e6200c006980b22030545074050081007040d0002541e0342801c4005000c40e40c00c0300345003100d01c901c03a039a40382c10f82c0151584802c1698040350178401040080711100c041c4c107000c0c0c600c04a103864094020001c51030303401112005620381d031540c2c045440d0354210f1800b500058041e030b0b03048091410105c40320003440c03a4820024903540007044c0240058140d0041614116541c1c402c000d0070a0344005040d4070084003190410070810400240c80d46129007030919500c82e41d4080389541c40350800540703100e0745030082c4082c0c060820104140b61703044012103200d0201152030200300221101983c000e81101d4800403194403001034060071440d03000caa00e0090710040081e055407038581410880844011128403031300841c8000f000d1280c4c91456004d4580000c0c078080124010f00c0e00229400e00040948040f01c00c1298180288440d240c9409800c0d0300005 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 450252356 1250 450251106 450251141
    0x190f0605101e0302160b070c020906011e180806071107050f0d030305093309010c0503040b1f03150c1416031205151809070e180f030c01 60
    0x41c0510055816802c40e01454181503000500d2058901c45002040380c1c107400c400380c1e181030704d400c0901401403061844203d1140c80c0f90000541c15600a10402e05078241181c8135000c0713004089070039542c42c00008102c00c0c040c00100800520460100183c0b403103501242d5515800c489412203081c0ba1504640006100f8030f0000d46480c400d17140c04c201c3e00034a50301403601203519180e000e0f40904050030020750640c00001420301c860800080500318104000305a0460324690b45ca02c2820300301d400b0070b07004c0e9000030300400118020801d001c0009800460042010004590540003003030200700702e510407101d0078001c500400b2400307114894450324072081c1c18211009504c40510500c50710034030030300c18055040201c69000385403003201100300c0882c00303a000300704e40e0811020007014448060806031080710002d10b040310b000000c0340b040707010b40c00c90001400d407582422001c65003090002d0100c4801a6644c460414003101007140c0c0f0340d0801c100d0055903482c0125582d190070344010041c1c1800e0341a = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 450253606 1250 450252356 450252377
    0x12070f090908030703020d0207060c05030601090801020301050a05060304080408071e080d0c06230a0b040605030a120c02011407060c030e030a0905090405190501060501170c070b190f060510 83
    0x2c15200850754490254500165030b518a050b1000081c06000707800f5050a1914941001d10340c0c210b00114050442601c031696001c1e078078100d040c242c5c40240141500210582c4080106003081806036800a114031100c6080c59110600399181403003d41c44048201010400003030f0003108103800a020304908030240c0650b40b084040030f070824107034020040182d031b6214400506064500300c0c10500c064042c20b00302c2c9900b800e00d10310307020303001d0140300c51310aa240c070000044501d0005603103070b070f043d40c03010107030441c40c00c0d201c01690070b541031003800da0500903a0703900d015183d03034000b00400032184143c900190382003446000408446681c1e10001d00c80d802002a583da80341c114a40008446040b0303120b410640e41c1d86402401c00f02e5400e254920044442003440c02c000e8103420040a8032800ea880701610000c0300d5010f0f081c0181070728088c592003410403d0b0001300d41560442079001c10810304c04034282c1d030140407041c11500c44003000300049581d00d000b4445840c003400a4038400c4076910340006005c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 450254856 1250 450253606 450253613
    0x2100c03020618010213170706030c17060d0606030605162f10020301060f0e0a14041d060a02040e0606130e0a06050a09020705060f010e07030c0c0212070f0909 70
    0xc50001e000760705904042c2d070b900f801e030f1002501166242d06100e080c0c11191640c03421180240d034144c40d07014441d40034a2002003841c070722901c118610309003103503103904640c1240161a51203c0c0080c000941103004180130f900420101d010740002103201e03040016691828401ea030340050fa0100343e013410041c05035003c003042000d0140030750010252030700000344007907511a5149007003c4040134070b200cd030021000060303094011862844500d00786e29100f00340d104a40030492800818056400d26030500c1d00307110010308241c0e10142d2196180b0201195003201100d0407454844120f611010041d00040c090001208140b040340d0007000a40f2a030b4104410101e1560f000b443c0343c09140708078082c400c005250703004250401c000a080c05000ca50005032074555650283d80168019156446072002180780301035450a0141258901c910f008503c1e154840118040d004d42c0e000e01c400c10202e0103c0034050b0780e6136841068003200000082950074506111240b200255520901d0740601e000c1524011 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 450256106 1250 450254856 450254863
    0xa05070206010b2208070510030209030d0e0103090f140c030a0b15011403040501020d05070c0201020c040c03020d020d060515031003111c1a0c040302010903060c050705120702100c0302 81
    0x540d200c0c462500c3e184d11450f140c0704101e041c0c0440809103440248000140064081021000d941c815600c503080c0c00040c4c01c0a0b0107a208a001d2160107520103004021410300c510004a40088145404900190192240f40301030040d442c040e5200703a1a0300384005000410090300860382c2c2c0650250000c1d50f00d540f41d1440d588002809095020550340303803801070380c0c4100050208100c480c8402a100e003040e050081c002c1d0000d44030300302080e19000108a180e401140e0758840564140d00405000c3c01030414840507101e0b183c0c0f080c05140d0280018416151107001504602440201c0020907a10b80810805400c085210b0b12010000c100140b089000344044031500352500486500c510802d2003002c10003091507500941d150640c14000c00d004c000e14004504541c2540101544158680030481c2031544954400280818803030b6200300005003858001c41010f4180381892400c05010303864007828011660303020003c100e40040d00b28114980903104d070414603990f240018038201319a501959 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 450257356 1250 450256106 450256109
    0x9010e160e010905040519030c110d050c010c110334050109091112040503120c03010f0918020d0506010e100b12060d020406060c050709092109090618050a0507020601 73
    0xc3c040e00c3c1d80c00502409030800405824100d4100b20303030846541d6040040c40090004402c0b665041c0c81c2d48030751020314000703084000c1c958000c405400c1c810ba0ba500151340e5100d90000071110202520301d5805180d4040c012102006032506864000c0b2031440714000030032503841c01c407e01d96080020144881d0764800141000e9540440b030000700300c0800003a6100384d008080749000d0107081c110405c41080f00c0400908094891400342c000d540e1289120801907000034020403140b1a1480001c001031901d91b00f004410b0340421200d80c08191484d0080b0304040801601503a00303030b12600040200303042c00380c0395903071201c00d00e603401c1e8455080850b0110070388030300d41400200c030012101280c065a00c1e1500703848142d600a0080096030340e00d1001509400402009131540c0c0100640011427241e140640310102d80c4c0034998200030320301250030700c0300d03680b400012204120f60070101050901040c801e0202620b04500041c0141c21351803290820340d10010319042c4001e00b40300c10302c88040c3d0000b91090 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 450258606 1250 450257356 450257369
    0x6021006230607060f0903030608010b0312030a1a030717100e0c0f0f0901080d0906030e060402100c080d1d0c01020a11010c0206030406020703080601020f19031709010e160e01 77
    0x29680c091a0030b04d80d0103010320000340001145468031000800d50194000703001c69034017400900c10b40c0b040c03200301519036504043c60300011108000140d05510349900890540c03198120b0604200e40d401c0c042850b046040d00f207410910034004080148417403c201d034400b40c20609100340301c1041c1015026031164100740d2003034050b0307030a007000300079554442544c444088400760440e95950f0792201c003c5d6440021111100100300d0b808130103d41d040c820300031b180806003180000c00b09902c0320350034000044246c610aa08024405480320001150b000050480310b04440e0003050f030405c0c416a20108411840c1c0d042c1c45580008200c00041c2d030085034054801c1e07001003500c520010101c00580340b080034003000940c00140001040200030302035028040c06070182e51a400b840c1c1d82c00f001a40c3c1c9411544000a80b54410040c54528104d00d8140e9042c413403003032030900070960750b1082010f04a44265154440c5946840945550030000c00890702124a010508600945000d0724480d031481d060240b01c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 450259856 1250 450258606 450258619
    0xc051509040221070e010e030703020f0f240414101d0a08030a0507051e060c030403032913020f0406050d02160b01061b0c0e04020d020a0602100623 65
    0x100101e030281d4220310400d04500750f500d80340c6003d0000812031928800e4840c0440d001d03085903541400c00040580942e40d0103408036500703048800030020079034110490654450607540405400105480b110183d44101c042d00c030352100d081004090044580c42c28140c000c0e504400c5215800340c0c440403080d00c0240c245008400c0c024070700b003c54914440740e080f80d03406103c002282c03e80301e40d0090040c00298000c0742652440c81a8107542d54802040c0304040c00c1e2580800e0210728401d0503c0000c5401910900f000194202b6003055580d40340d281300364441d900c6041d07482c060b4507820180380b0b1510701c1485520840c60403000c3c180117000b500444c020501007203400300741c56802204550458082ea0308206900340555000c1c9050081c55909004600000e6801c820650a40b8000300c00508083d90114400d96110305059100e0441c4078000c1040e64000c3c0e2200c080c2015840c1c400c0c950010703003030315400382c039242c010786a036030040e90800d80c04983d001c2c13400b01c013070149101c041a1580543c003045410 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 450261106 1250 450259856 450259867
    0x705060f0a180503061806010801061203081e0f010e090607020616050403050a230106030507060503070e040e010e010c080f0c0721050310050d0c17010e01180c0515090402 75
    0x460b800220345420068251141e40f003486034050006400d200380c1515041150310686c2c8480f03400b42a26420710405d0780641c03402881900080c0281c82d03041d40441c440c4480074403d000b00b025440ea0030003d0780d401d0007501b020f200600c903420904044c207500540810062510f4240200c009549800080900d4502400b403e641c0300300798400c408850081d80c02074200e800548145c180340c60341d030200030760094450207000340503000c0ac0018003420080700e0304a006040c1c00c901d400820b03545507100038410310402c8040700c0e42d040955a43d204940c2e0024041000141021048001300c1c01c40388401c10203400d21010f0002c100018046608142e402828440d019840b03400d00c1c9070854007070740d506050b4151080444540504103a10101440c440d41301d01c8105010b45988034244010510f4001c4041c1034120f4004007805554480a0150b40c81c9001030000103400e1070141e1050f003181d5440c010440031005552801c1d0600c020184400042c25040703585c4100c542118018014511a0403a50f80c080d90300404c0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 450262356 1250 450261106 450261137
    0x11b030c080a02072705060319150216050d030f0905070b0f2a070609060203030708090f0f0a1103010209012309040e1c030213030201320c0705060f0a 66
    0x13030398020702d815006071660800c10078801032021800c4210140807842c000000c0e07020310780012104d00c2031b0225442840600b01940b11608001c4000d01c1381c80580d90204407a0758005c41071b210b440300c0d09000d5400340900d007954050050030f89100c041010303841c60070518980041100030860508841501c040e0541c1c400c1c0250603201036010788050100d03a800343ca565058890154241030f81c074130f910501a1480191142802c1c2d403110520700819005910910004080901411000c1c1d00040700004460032100d09001c00c92400e80c00d005010301790703003041c1d00d00ca0401044480c50700c0701e010101c1c020350034058890700003030840d0500341e02c001d9070300600c1000c0e40701c8055000031640c1466016109202081c03d0341c05442d51600c0d400d00041242049000c515515842882554034400681c041ca10080b455074004407100505aa46040c0981240300c2c0c1d02d10300710100e881410101b10f003104040d00c603061140b505080c036a0300d5106900401c07041059141080c0007108070390001165061003102d20644c000e = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 450263606 1250 450262356 450262363
    0x506010e0622170114070f0f0c0219050f04020c030f18060a030204031506030201020c15210103030f0201060e010918060f24050a0905071e030605011b030c080a02 71
    0x44441005009021011801840d90314000103e8880c40000f070180641d0100301041d1000c00f200d0a4000448680450300714601c07400c81d02d50122003510b04050b80100c5500002d501c80c5000d8241c0004594180f8100080c4c2820510f07511100c1007220114200400c0b0029030751130b40714940c0d04260032038000506d802c03214640d515100d08410b001d0a16512900b080001034001d6220f80010b03201540c000da5402400701d102c2c007940e819030394180e0280c00302e030701038100344101d10103070b1400c2d0781d680341c41409158403001c2c240601802c0c40f1900d44400059501d1410f000e04201030b098009005c5904283c1d042c00040c00c6504018115040f2080004000d14a2401c0280503002c4c1c0b0b60062461342800c003d001183c6442c0c001408500080700040d41c980c04004115203031289a1164503007000c2c42d01c00c20041061941d004581c480d01c0d81c200540080c0d14a8400e494480c00c42c0203880102c0d550702c000f808156841540e90111027802e82c082ca41c20b8070a0344001d40441c100240040424030001a5030304824800d1 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 450264856 1250 450263606 450263647
    0x50a03080702120a020c010909051003080d0b060304050d0f0810060c0303060b16020906030c130504050102480c0f0301060803070c1707230102121c0b040506010e06 72
    0x83d15416240d811516009440c0d481c07008800d400074514030004508500d19100b11802004800d5040030254039640c3c41c1d010940085406155045e50b803c0c48032041e48802e001103124510540181030f404507190300c0a000c0f0021328039880e041160007000c0004420b801584102a200c3d40e050485100c0f019240480c080d10070341c1c000c070081180c00b00c0c801c0d90f007401490006500c0f901c200c1e2a104981d403110301b4160348020000800303a1089001c9240c4a03111241e43c041d41e0014002c000251428025007855040041ea401c09000c00b4240d581c3c04021b00c060482c50340021000b00207040c00701c40f014118141d51518001c0b4910f110b1407121503052420b81e000d5024100810040060b40e440d0100e40c10060300d50b00d52841407040080e21074010310011000400d0a00642c0c42e000300c41d403084001501c00894400c9c040e80c1160542c0300310117045040031a0170003c0c0140c000d06900c11103410b40f01020340d4060700c50291805000b14100401e00085a810401c4003221800a43c0da1640314401e000d8282001c1200 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 450266106 1250 450264856 450264883
    0x50702190c0b0c010e0706030209010f1d0306090a03140313080d0e06091e0c03152208090310060b031303030f05090c0a06020a0807060218040e030a090b0403050a03080702 75
    0x8001003520f0040d04a00b0713a420421007a904010344c4d401c0103178160f01ca0801807600040018110803d00c0c1c0c090803c2e61000a00c51a155810740806004240303480d0080d242107070f5941c0802744400405030701c0035404503401c038000225829810452907080d598081c0040c010201140445c0c04c58030a00b42d60b001040c241591821030b28141000c2000e03e0702d91022640c00213011403042e28000c81c0e2040059001080c05018000300482c24442213100c06518004d4607850368000e01424890380598001724144005000b029110b5680701c090040501d049040b0b103511003d80d05007001008041c0000d03099030342c8403c04418440d28020706180440c02000441e051920503440c01041c000d03c00c20000c1c0102c4c084d07000740d550520f21610f400060307907030302e503101030041010004100d1500060362940241c613038407015840d407041e004100c00006d8262101d80d159040140d00101d040a0b11651142c030000c010300120a100b4a02815a00d45d075071920301d072140c041e050014910101d41c40a00c00c00c01811024003 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 450267356 1250 450266106 450266129
    0x609080a121815090e0f01060804050f0f0d08130b0c0a1b0b0702010e0304080c0f06042d0f0810020a0c0b0c0a0e1005070b0613020c010506040609050702190c 69
    0x884504451100702d104074400009103244034017080c4400d01e4a0401d01904141c1821100d40e803a0180448000900400450b03480c0180b03020420040760400451100040300d0028004070840514000e110b480020841e0703c1341c0090301404000310b130001e00441c1e00305059001140d9900030f0b6120627504070380d201d1544002403e580e00310b0320900510100c00c03070083c84164001d00003103110802507552405a80030342000394003d4880007505250207510828003450143ca140c0c1010703543c04e0910001c6111201610140c0d8142c40604014110106440040c1004150710090a414800d400303664911004444071031940c000f590300e400034094100da00c02c0c2036208044942c2440c0240c0d4100039501b2885c07900000ca04500f05c021007034a020f00ca0003401003940d0f0388082c00e000e401c1c3c66143c0003a9010741020340008110f45400ca074440a4001840890007240010840e0f04018003440219940c59000904091404041c0180191301140b440c00240c9186030492000034142054605052240d01c089a03140c1c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 450268606 1250 450267356 450267359
    0x5042106110426010203160f200d020c031b09060f0d03020f010506100f120b0307120b0105100e1e040c0309030806030a03050d0218030703050f070609080a1218 70
    0x42c1c0540b0001c043e03800e90a00c10014010480105090380819680b24242503004c24003094190300c0380e481c40c140c007081c0746404580302c40d407404000d07941303c0c03140740006540d00300050385030700305804002c01c180c620807e90060089803101703191081d1085690120a00c01c214a10124189603290300481e86000d0340185192542006490041c0d0b81e0451100b48048a5003030000040c4145000002e10608180c00c0e01e4a00a1102104048914a00d01010110700b581d958241c1500d5840401c04a4040c2480180717403c070002190914180c5040141d00c8540306081441400f06020790181c0c0c94612068243c80350146c0c000303561134440d11121882c522507001490045400c5d10b466140d04404401d5010741c81c0e0000d551251814151108461400600840c4040001c1c0c41000300980c0286001140000b0380c286020180c80081c1c1000301951054519500101d24880c04000a00c0144010451b900349100e0b128502908182c403403104040103040c020603015000e0609015050300c5001c65100c1150741c9030107 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 450269856 1250 450268606 450268619
    0x1e080a1e0609051b0703120902030102070506100612020f0f090a360203132310091b0f301506050301020f0d180203030403061a01050421061104 63
    0x100070440b01d8298480701c0009802c81c6013480000c455280d501603907100d80456903d05030102a001000040b40c0565080101e00041403044c003040303001c0c00b0241d8071040e0062414500134280c0c0003c90a8500080c03041105028400c8034204071101c42c513005810a40303415940d40024000541031780000c00b00700030601c85d404584036507010808414040074001011030389100703584c0128003045a42074001c92007800214045940000c080e4900307001010209009028441c210341400c020100002714a42c440c85040200004000d001c003015400052906500e0b16200c4070b5482901148038030b40d00d01900d002c400000501c0c070860fa83c1c3ca075900c80444118521507284c0386091161407003952841e03501d01100440d0314a4103000311440c21025480c03131828166151451402068142d61140042100001d200010384007403000c0c00c0154010310b0006208421000b154552001c800d684504015003040244110400840b0030000e4102c4803000601000a510705500206900c07220024610b41c0800d002403078 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 450271106 1250 450269856 450269861
    0x3020d24061a0c0c0d060f0204030f020f04050408040b0304080409060b120703021303173009070b0f09031614030c0d050705102d1e080a1e0609 63
    0x31128160910000d2025840c0b10044034020301c80e80b00303050f4201400d05501494030107043e07040e00d40143c00002e40c0001e800c107000e049038041e50046071015403807145002507150401c0b049a081d0780c01d550501491070300b55211030b4544118001e510541d20003001050134004800255405049010000c00103038ae143c1400c4017551b0856100c840303c010084001540982c424025204580300d4200d0341e03049103003140e5415089a515020480c24041e052003042c8240b20324416440b1301107500300040d07441d8820b074201c0d0012014000c000c28a80c0e41b00c0c0b00108503143c1303507000312101c51600411160321060b20500082c20110304580011142d00c40e901c020503024250214885401c000b00c084880864510007440f080f010a650054466007200004000d00d00388800350007903000c001e107800740704210513a220b1800260003081204d0403108100034100e400b83c0109a0507118140702d143c204004c000e240004000307101c0108030800c2c2c943c0300c07000789400c0e096031441407110010303d4400b800030a4172502006e00 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 450272356 1250 450271106 450271109
    0x40303090c0f032105090d03021011220b07030c112d03010e0307060c2a061109090a1d030d050906010518070e0a0506030403031d07060903020d2406 65
    0x1d100981d403c40d825402410392003000620b00d543c5421b400c04030300004100c2d0346842c0e030f4400d500390b000308400b440160100c2d100f41c0c1e0aa44101103080e03210460030300d150165074644819001c86030aa14030070300103400b4440503184070301e40c1490501c1c40000725180c0b030707002d03450507450b4190020b408002114040a80740c176940360b500700c5c0c88000840081c1210070142038451300001d850454004114003000305005811000b581030003410052241d8016240803000030300003142400707121103552203035010040c0300e0240700060095100540c4c02c140c0084002425400c001d04003801d290f0360386c2c100158408800300e800501d02c4100007030740d48078880302d03c2100180a0440c0c0440d030f107001d108000304403031800084241e450326450f055000c030340d60742c1c01054521440e00c0450070750280040380006210354400b001503106e98425035020850710f6007102c01200c45868081da9406a030800403043c070443e0742c4000c03564102c035011038924014002a0a0008480160342000d51004003030041c40d00802e59503400210 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 450273606 1250 450272356 450272363
    0xc0613020907030b0a050d0602040503070603153302011e05010e16140904110f0a09050108010b0d1113030b160306060e040c110303070909140402060a08040303090c0f03 74
    0x80c0d591102c20880445291402c000e0303204499520901c100e052503241a412a440b136103006203000d84410009192805903481070700020348440440441c144555a41e40080034255448600c0c01790044104104034100180c5001002c0b01c0c02003220660b10075040a43c13140c114600c8506035440d40030010004e04401d00074a1501401d400100d58401207501c88002c0b6440390760f581140c00890740079400150ba120380b11890b03000c0d40b144002c010701c0103114000c01c4540b1001042541c0c0707190195001e400140743c0e50025041c4080300004004500c1000d088600d2818200400035481a40c2e0010300041e0180441290304110038401c08010000744607160b0b1b001c1d02d042d0003c1200700d01607880c110b00342c550f14019280000c0c9003000701441424240c000450303402c07203400e0140d04100715000702481d64004599160014031108010030604810384034201c80d040396450240d00e44c1c5825000b089480c820303446420108040c80380080d007454460b600199015a01c84d01e240034140e91091024034040d560300054 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 450274856 1250 450273606 450273619
    0x110901080a2f21090319020c0303041508071e0c0204140c030f151806013b19060c020a0e040807120c170904090b0f04060c0c0b0f0c0c061302 62
    0x4100b050022105610a004132401903141c0006800c0000320002c02d00c840034154854540c645030142d50a0018002070703c0800e070900341216550304000c01c00c01014250b9818000307a800300c100b20030b9003210858040e61041c10400518207003480071500070300c500c640b9511540c0d0000b00384a00000501d00450040c9039601002e846034071940c1041d1200894041c185502c0034890341000c0914082c0291369510040c141088016140054841c0705101044e001d02c82030311403800c60074a030f02c1d003d050f03004c85401c10907500010741d0700b004ca50070181084207000795420b10144481081c1195a06010385000d04107801c1000a10b00303003403400c0c48064201c0c04086880454594070111180c0c481c468202401c0d80049880f848142c2a010542c0d0960181074040d4000c5c2d144d465070808911940c60040c020710b00011014030301e01d4541000d0b802c8901a054520800ca81861400c2c08510390b0301000c2d400441030a086545a00c42104031000ba20a043c40c3c240300d27005140421000139080e1000040060007502e40 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 450276106 1250 450274856 450274897
    0x1208220c08010e030a081501050903150f01060906091703040b0c060f07170412030e0d110613080415050d060602010b0414060a0303030b03010605090415110901080a2f 73
    0x313600c0e409100804000515648002010240454011401030f1418180b5030301c0d0101e03020109040003030007184441d60702000002d0002054503080c6a40c01441d051625602140c180721000300680004c2c414a090740780043c80c100880c800500803200101810b94055a0b200c0d4640126920345204481850f240b040307490000f0002c41c05140003038030101c81780c1a0303880b003695a996101c0b040c01c1d400c0c12890425549030030648646000b080885880b041e20385804501c62000c0750000d2501034001e10350f03920b602c2018030a20000d00c2231401d8800399855200c008022495542d800c0300c85005090094030580d003000800181c1e682c06601003c0003a00585081c0060203007901c150281c5d00c0262600d50708600b40c583d080020a2080c1e03c0503094110050002c2100c5070340c2c9000400440c1c0a89003074a0710b01c4445000301c0b0351589481000208001c00c0b040c2d5003448103107400a41500c00040c0300c10141900ca801d035007201c050b2145142c02c2030800b200c101e0412050481684590340081c60b9404030342e292002c0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 450277356 1250 450276106 450276131
    0x1409100605041e0e01061e03020f0414010e0c090402040f050f010e1e01051e27091603090b01080c01090807030803150604090609090c060c1208220c0801 67
    0x1801070f0241c1d961502d55101d6007040148401410b103046141280c1d50b07030300d030b010400310b408049442d24040710f0140107040c14114010084a6042e2524951180b450141100380300840c0100403411200d101c83c2c00c41599948060f0700c2414407030002119409480081d01103200c02420343c0000c182e80c0165aa01c6d072464070031006590480e140e2a4650303001015140305140c43d250a01128181c20f410303d401410041c0c0c600d58100760640c0940e20048a240108080c0f1801c03c8448070840010610880600e840c0d025001140480c41d024201901c04030881001ca040507010b0b41000c09410350144c1901c2e025a56082c00035260013280d2441800105a11400581c2d910001020810b40750800c070891f10b03684440548004a2044417041601700101f4070000880001034814007005100720a0302082c07030b2599250000342000d03d42c1150b42441250049a404901c101c038144403048060708240ca05d546071030020355007000418a100792001d000d40780a504200c0550610b000300e886030402401448210f61 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 450278606 1250 450277356 450277361
    0x822080a0b0a020c07051801031208011a091503070305010819030207091d030a030906050a050412080411040908070c090212040809191211040b061b01140910060504 72
    0x4101030040c1c100c407004900710380c102d507009200d00c0d0014004c40e01a1a0344401040d408540c40082d0b00690210070010801d024036400c8001c0005550700c2d0a51003903060151684000d2802001400c0104001c500c0c00406e44803150108030100c2c041240c07036101c0c40c1c420303c000d01422090240390f03958003c6040700718421014580a1101c15030580250001b01c2c1803514000080036045014020054a000d82a0400034180010181154580d5011038001c2c44c500348070080e540042c010b4407138203141200b0040803540d002121081000245000b150f25152410b180003196030255460360300c60710b0a03881c5010410004000e00a0030320440e04c80e9281030b80c880e040022401480f0103e118030300307444001000640c00c0f500410310500000c08011070509a07124014600060350048d2a05040c05801882448040c070400600120212400d000c0000d10001003806802042241602040c0160300303220588000c0d0042c10720103e00d2040507845280c00302030700f036036a03d46c030080411103441e05002148034246030 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 450279856 1250 450278606 450278623
    0x30c0305100e0303060f01210608060129031611060a06030b1302010c02100c08030f010305010f060b09012604050c0117010b0304020907031d16050105031b1303082208 73
    0xe21b001080c0c0c0c18440150f8035841e4040c0d4000c1c410311150f08141c0342c0300d128450540600a6000244269070410303001219060701014031152080814410464040490080302da1002940440000e4441e09100c1500c440e80d0041202d00107024180802c00400c00b154010380844c2e010b41c21150390382d1100051200c1d1610000d2001c2d002070807400088000d4105100310001541c12403a040c1411010b40e1501402c940041e1038024003001030400410510209003d82d01d07e13440c20810400026140c1032840c11035108100200c0c0c14401040401c0034420300300244035281d45140c000584491909242c0b0310746625810302014041050304882c4201c0b00c05880d18030b8144c8020600340c900d56200d6400b04098424018020402c040c1c8500c0800c040c41a03030308548584e98004001464240a111706c00038100d200c030b03006141000014000c00203404503200c440060640703036044003951004041c00740d2101401e160001740a405e00050942010001100c009070494904a008800d641e00c0d000c0041d218443c2 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 450281106 1250 450279856 450279859
    0x50f09030f0d2703021210240519090e010905030c070303110a0b01120807021009080601210f03021518010c080f060111011506110d090308070b060a030c0305100e030306 74
    0x103d01c0a200609004005141c00202a0101c400b56100100d05106548070818992030080d06e910344c0102c40c001ca41402006800b0803682e08000d507210304801400c020807480707107100090b211038410b203490714290f224068080d00401906d0707a800d40254400c3e59a907071884108c00203990300c1c9912002036004110002000d520031242140c0307074603240c5c01303400005840c00b041d94102010030002c5e0059892142c9040300c064191904807480b85005402400c21340b050f408810260141711480c0558040d4042da50030991f44018400a00025824220b1030122050728440c00e80352407500348642c01029180e445100500c00d0000d02c4031142030841114008800e4801d100c2890a003c04981150301540c0c0d00c1c00301003020000003a0300e6640200580580c40700340d000d130b408503005004e150080c1c1c00078040c1d40c803600c1c030500f4520403052442d80d50000714400c810010f0305142c52800800c6459035103840c10ba000716003119605190684030304060340c50700c0340c2d8400c0d80505440d01544580e402c1010098a214803070 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 450282356 1250 450281106 450281177
    0x1d03040e010308180d030c03170601021e0f161403010902011202030402040e0d033207050c030c010504081c0c09270e010209010f080c040303050f09030f0d 68
    0xa103542c1c0148540060b00e20610f21360030020139115030f8503003404040c0920b01a1380e0b0211403540310709028140310820008690b09401a82c200300c2540d0300050440c0c004881c12040c4078911124880a0f8184031140c21032034264091942042000d0303010842103810780d1041c01001c0c224280c24000c05088800d0050024041040c2e050007500c1101564080e55005002800204008007030700c9855003000c1d884074041e000710355520a140010700502b01000d99410510400c101c1c580001e40c42da103104080108502c00700080007501c400703c084244203882107400c09100170f01c42405c02d40390100e450f420141c00324410400c032171401042c1d0300003402a03900071320403a15000a002d09064070f0702070341d50300c907030070807022548845d5400c1142c5254440c43d50003003544c2d40010384030f100740c600061405450070b4a5070100f0a102d42480741010703214007203c00f202d40c03500348240c0c0c42c41c0700c5502503514020928050f616006560b0780c420340304c0000c41c00990003031065640ac07140c01203041b25500c4c0a603a41005004440 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 450283606 1250 450282356 450282359
    0x3081e010b070303020c010906200408100c05120408031e060d03030b01090b13050a050607050c010c02180916050402040311100509060f0d0f09150b0112020703031d03040e01 76
    0x6440500802c540c901a2130098600646902c5c03182c25903010903c101c8501d5643c4400c24505220901c6100e0f85807854110146401e25181c900340e80d849900c0d1802c0d40050f074503c4134911150281c1c048501401e1b180c4001c030001d181c1400c00e4074181e00200d03000320402940c011626001e003000304000c0d224110040103c0045000c40e10110f00501d14174007940d050128580d40410500003501c06041502d1302e0707c030130080c0c40d8107110071700071144125804035000c1d0364140011000604049098204c5400030b2a24003810010344c00024804100c2802401c0518484401d0000905001c1581408041e5500e10710150340d82d200c2c01e1108170312561001405043d00040c09415038a0300c094400076444062500a0420414500240d80e030740c400741c408680c4284c0094031110b0581e05000d9030040da10925000c112040094aa44a01070718210000ea000c5550b6040e0b003030103a0144a40d022181c1c4600ca04540f20b5500e480e01800510a07003155205210a903844421840340001c01c50701514228602103400d48d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 450284856 1250 450283606 450283619
    0x6060c0d08090f16140d03080c130317030603060702070f091e0204080f060106020607080402300304050910031a070c20040f1a060a030902030601030f03081e01 70
    0x1420701901055050003042d00c607040004040249a10030351000000070542c0340381020041c11000b9850080e40075a012075500800720360007110300383c3c0c4219400c3d086542e0f584085009040790320745810003000030381032040305400c0022080240d4411141502181c40c83d0701c44600c143d0703481c0c01511400d03d0113107001c042801447c0300c0f504001d2421140d508414410005214076100340c1e0003580000166510124020140100401c241b9004041a0015141605141384004d00b24180200080e020342000050404212071401c03c00200c04c02d28190b00c1c0104000c491003948a50192041074494240000814280841007282c03d0859900000c142222070880c4950314401c60000c1500701404080307103050b0b021032300952100003140b007221900f064809034401007100311026003800030a040c0c5441202d20440303814850400070075400b00c405544440c46500c0840141180c114029010701503500000108000d00124240c00ea100703445155072176480c1d45081c1111000001110030885001c00100a00c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 450286106 1250 450284856 450284867
    0xb060301090209040e010501030f020a090c0c03030b1801031b06080c1206030a0b3111090c16080a08090d120507121b090906030c1806030f030903050606060c0d 70
    0x2c40f400904081100c4521500c400d003100c0099000340d0301b200d02076880c40214a80381d0202c4002c3d100c041000c00c0002c0354110010111408403a0080915541d808203800070754603c0c43e1400b4160202d5415241c1c1d607124580490103603000f8098241c40c0750840d0000c1071103402925450b11039500d804c4003074149105a8101c101500c0003409040c0c00d800b032202c0500100d092a41e070548100c000e90403918419031000212501c103400c84d2072511602a4211302c050000348140812911000f04465003985503c1d01040940140700312200422044a074502490822412802901d803858080d1500313038440e5a00c01c1c04035125510b00c00c001c000156185038260840010f031b07101903003050f0213141074400000f0b004480340407a8101d2407107010319401c44480c00c42059000131000040c01f0881c800780402840d40c1e840181450243c060181406071036283d40041c2400d81c0d01c80320003150401456030040c1d840e800d000c0d00441043c0403d0f550750041000141441c2068030403141076052010091140f00b402c03a800700d88 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 450287356 1250 450286106 450286117
    0x30206090d17041203090608010602060a27050703050706030b0916090b03040308040c060e03030706240e0f0a0b0d020103091a07180914160e0402030a0207060e010b0603010902 77
    0x80b800d001c03000d141c1c1c07a04440c0d000382026058440c00680300049604018000d02c2d00e6a0141c0200701d8810018895103501080755500402d0702c1c1804504214803541d43c061002c00b44d4134452002244910101c14000000b81c49000c690041c0f09071011315859041c1201510f4010281e540c00c00400300210b0000105403c60401242451822100654803952902e0b40c0d5071096900f07070b000625104c244801d1200c2c0800c44401882c0700e00b02402c2090642c40800d403070b4040c0001c0038060a54903a4128120107000400d50722209005200c0604c3ca91a6041515402c100340c4265001d95804000580a03581030b1049031040d0700014106030100324a42c0c011005081541403c0300c1244030045140c00d03d02c0c0c01131695000b8001d540700c2d940190314480c0e6a80c04e0014030b038000e20986080109079580031480b00122078011450800e004418198601c0c10740c1d64881d001c0c2c0186d0803510000c02c101800c2c02a501500c10740d03102e100144884192407a0f81c601783e0300b80074035190b4041020401004105030713070f500400c03 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 450288606 1250 450287356 450287363
    0x80a030204030222050a091203020a0c12050301260a06091505010b09040b0312070228030602090a090b01090b0310050607050a02180405190204060b0d060602070f030206090d 76
    0x145015243da02080c030f13807048640003814415100f444000c9240701405943c0d840418001d04006400f002e0b02c0701400c0f1660100300b1010300d6400141c01c546144a2052242c040f6003007007644600018035003006006610920031001c0081c107080c04480118064886244080c808200600704d02440340c4545009000094048070080304107100320480491030302a550080a949840c179444640782e03c180801d8a03178240c1264401d80000781c1d0400300f108a0825038130340980595482070a0242015000440c03400d1418400d50158100d400208008298000304603101040d21000551503481903502c050fa80d0b42102c02d030100d50110380078030038281c105000d540d10111844003c1e4034070b41d4401c0803503859401145c041c3c2c0d40e40c0040c400b107400c0d804c28440701c0b032900c10b80300c074005a070345002d4452325120f4802c0da0030103260100b240c114200355500d41c1c2121010f001106e104030360380c03000390b503491005181c0c4d8454040903000381100010034041010f0b1260450307402401c054a0001e010301007012039250100200c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 450289856 1250 450288606 450288611
    0x1005040806070c02280b09040605120c010906170a0f1b020c0a060e0a1503020d0203150102060702074415150a05120c03060c0a1e0c080a03 61
    0x503000004001190041007240c4901c200c510781801030000594000200d01c415888204844016841e00020503080701d45210800c0e0302c5038a100002005482c41d42d01c01c50b485500c0310004c48203828007241442c2d40d183d090304c90b08071003540d44506403a850350b9451800c0607418414000f46400c60541c00000500a20b101c0010310038070454a80300141d95400e00c0c08005904c015503104150038280e40c2032001d400d850420128908850300000c96a28960041d5040d107014021914000c90080d01580c801d0608218103540300d140440c800643c800ca0764548078018841c2d203020034407417400490940e06a544c0c01020107100f203107082c030015400c80c00001030600700c20351441c0c2108000c41404400c10403410007000e0000c18400c5250809401009400b800d4581d16244020040e99583c030300302030450710b040d04d20040704e00000e00a41c0c1000d0008400941602500081240c0e02000c1d03c020040740c3c005c0d071079113403803100c80c2c03450306440c0303110300c0390503804107c4c0c044400c00840c56090142182114a1601 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 450291106 1250 450289856 450289859
    0x8011b140a030b0613080709020316121116050d18121104020a022b02061311030d05041503050609070c2d200f01120b03061e0609090c100504 62
    0xc030300d69a002115003610b1917401101440620b8080c420440102950307101075083d82000ca103402c4508502c00a110f0134440a40711009041003140c108a40045029090340d46483e00861080c4448009030822100e500612181c40301c02d601858880c2412500356543c032286c2403c200c00c1c2c00c100840381da0140c80c24a40c0351800b091075a12400100100c00041c0c2c080c00110701401c04c1145054410300c9841003043c8030062400a0311b60000300c05a110f00410710315403140310217040172069003054500c19074050044c144a88401c81e0428001c104072414040c940c2500350f20b003d030450486109440b0503601145500114040380c1c032400c0074010450181c10382c80384c607401c20b1020307414100040704a0300c00c6140702d240200074420318140c01c0d00500070042482c20700d14040c50000e4408820301d18003e040c003490b8901c00564101ca9404843d1144002c0c04556007418100307202103c400440740c603103a40d101c4840001c0ea990500000f41030140104a000782844021320040005842c8190517900400038107000 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 450292356 1250 450291106 450291109
    0x405090f06101d1918150b01200309060901020c0a030606030512030c0901080a021c0605130603030503071b171b0714060c1002040e0108011b140a030b 66
    0x5100e002d140c07150140c048107807609448401d01c602000d03501e20851009010000240000b119414101c0d100481c00140704500c0c0c82444c1280c156040b010b00010304e000d00307407101282d8550211050f808245c8606089036450300041e446a001001100d500c0e4105110103143c0341021009443c0c003403014015100c404a130000852030003070740e0764000d40702280c88076030400074000c040c0061100c0a01014000b03103545401c246402482c864410319904011100c00081c03101101c1e581915803d81c6540a50000701418100700300c0a00194014141308002c003840314079010600d88100c070b007100e92689925007103980b8010243d9890304003180d0303c40c04440c030404140c00561040144c13640008142c80701600d6030034081d100641c4001d1070050802c0c95000a100307002c0401003c4d04501c0c030703003021203080f0340d81d00a030800c950410310b410402c50100c40c00420041444a0060b0300c0e981a034446100802099040503403160302d00317000804202c0400d207480072206000002c04000c145403031795030a010403880c10090 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 450293606 1250 450292356 450292363
    0x501020c1507021f0e011e08060d053405090712090209010b041d01061d060415020a0213050c0a110a050d1d03280c0803030c181903020405090f 63
    0x4840c1c1118400a00f10161303819000780942c0e480c50421300c1c050354103400d6010b034050b1a000d01026201072041d0a000980d80799120f10002121a522609441e04000e00c002581004003031031050448180c001501d108142418034212130407150700a1800b00c030b98545840c19a0412403205040040c075440d2000c0402503104c102d0818001c0c44028000395903249400744c81306819510306103400140e61004010442e103540300c400d11300032020541c00341202080080c0050454411648030801c2180410740800d0b0141e004102e4503042c900030741d040141d901c0000c40304400c41e90212846a1404824003091480c2d5201e0500e01032110691012a00803824545959140c411944c40c000300244480c00c00d2040000c064040303100e064019401008045480250848900401c841c540f00c1c010781c5030080c000380151003040c480180f03042001d981da00e06159403035200079400848940d045c80c2e00c03000070b00c0e40c500380011511a0140320708501f65900f4250b0742000058000900405a644258009910071000a0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 450294856 1250 450293606 450293629
    0x30c06020a0b0703020327011e0c09151403040c05220f0606170606041a04091a0121020c0d080906011502060f060406030b01080a1b0501020c150702 65
    0x68004000d80000c82c5000c4018000041840701014010710502c10000002c02545149002c11020070045030491400d55005088100190f145043c0f050200705200c9180c0d4415000f0790881c1e911400f105460f0402c2019000ca002102d0000551036120501d44400361001365030420710451041003c59075a07000650b00e44021440068040000c203808044411144269a05028001c42c207000b142d141c40800f61201a9a4000c94201610400025a181c0c0c4200496010f082d813804503400749221139a503c403158202e03000303281c02103141800828018a002c0e20b60320140398165a05000300c2c6005140724142640c004480c01310940902c80c01555000c02d0000c00812074840e5210f454502d0182c0340b20b4500030341170307120203030128041c01c903048420790200b9603550090f0b00305041001521000b020030010511039202800c0407511900103d5003507000320750402071301e011380309011902034172501300c6051701618482d550250348403000401c0a0305241d07081d150f01624410000d41410040e801003604032100 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 450296106 1250 450294856 450294869
    0xa0804080918060a06021606081305010608061801050103020a060509041e0b1906020303071b0221010c021203060409110406030501091502090607020f0301180b06010e0904020306070302030c04030c 86
    0x3180b00304001424100240b90043c841440108503800300900d041c5e4400c010303802a00c007044107100c0001c481005180c04248007540c00b034000c00c0040d559000b40c5440d6001591103a4003448940c0225581400501810741070f02d80003000088140d26219043e11168000c03040260441d45a001d15000b00803005050781c1c006000050114841408130308010840c0ca0100301d20350f046400c4038041c0314259001050300d07484480390400d10311070b0810b83c0c546201c3c4d4050345402940721402001803034500e1308425032041d265000074001e10078101c01002c02e0381c9566592103807d03406c0e8400c7c00041c2442c64035400920607240140006240100040c3c04902070b034540340c0058941d6919001c4007000c0041000d150034050080310011401c204812001903036510030503e02038425400f4208106c03250360290f01c0181100c61414a00038044401e1400c503454100489840d408605813256142460420030381e680d00c219402005041140c0d64004250000d40000e40b0090289400b40070200001e00e4061007540600748 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 450297356 1250 450296106 450296149
    0xb070302031e2505040f050f120706050711060306030a0b180f07030212070803040303030911100306030b0105180a0203070207030803070c0b0a1a040b03012c010b04110a08040809 78
    0x40c000042d0a00f40d102c41040010031104210400190706081802e40c10344038100c42c480f407510010400154000c803004030222990003081000078107030fa0007400070707c40a0f10400c2a40d070a03850345801c200e020b000440781181c054001c0c0c1410320000705200c1c150b07940210044549103201d42c10040d0300703107130420381e59040d80ba55001d04d0050040d490030b1011034030300b0f0401304002c00c201c0c2d080a41e0107450f4050f5110040074951500808000c2250401d00d41c44607500180910004036076465005000c2c0c1100c0c4001d0320b1175030ba1080003107603030305140131010120000c2a081802c262124204040250f000030300c400214001d4800100014020320011401448240c0d2401c030341c0390080c181038101c90f8000d01062049441c00c1d10f4000d8074403131400d8009150b04d04136000240c0e0580500480d014080040c80745802e08007000c2240784a407041e10190401260301c034004c0010310084001d004c1203840600c1e010800031740c10b00248540601c40c0310060340c03142c40782415030f0070707c00da9501080d00000101d004004405 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 450298606 1250 450297356 450297391
    0x4060b120a111309170a05040b0a05030a06090605061b100e0607080109060303140705070906060309050f010207020603010302130605181f0303091a0903030c03040509070c0b070302031e 81
    0x64503d00b01000c807a910003007009009540c0ea903103095001440c0c1019141d20001c581c9141950061080d1030081c2110821039545111322907004106134800c42e010a1032034038000010440c0345ca1442001b040d00c1c1c0141c001850100424050000d014800b0140c80d11489496150300e0360303103001d0140c10304540101d401400f080c1800b803405022000140c0020407550315081c1c1c100040ba0744040a089507400724202581d07621068100300d818140c8039004610814100b05002078120350650040508074051002d4950304106122454240c0c440d10b03030302944c4030038280014005480d1404200b00107503d00800003c1051303032000400c65491510101e01c075900e41341c604020701c011010380444480b91644010400040c115038003d04982c040f401210200001407458000c40448001101c00101b40241281e07242c4401a150954130f9000b8004d45000d202c1c81000702e00d5150260030341844036944603d20280035607402c14120001d4200a084240d41c4a05404885044003d002c8050040300550311081550 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 450299856 1250 450298606 450298609
    0xa051c021f0906051c140105030d090f03110d0506010608040b060303191b0507080703060c08010602030409020913050a05150117010302040e030f120f06010c050604060b120a11 77
    0x504408005034071111880601c16600d0b640015201c0555945050054442089940c000880b10040603c28191454080070442c40a58010b496049890480880d06080006402226990068410582003602c0d520080c00058000c607008001139101410252000915450300d0b0315000c403e0740070401046418085c40140f01000c529141e1052090300118034203c3c0c0301418085411101401808100c00c4400c86003c0d50261540303081501c0d0060304840c98180c8510042d91a44032030705c4221945480e050b04c0802e000c0c010701410b41250400e40240d0705181c03030040103070003a45c021850150300c02200000a15404130358071606004070006c01c40040d407440d124100d140c06110750b40c222414400300003010603122102130300b00c1d4152941038601040b5040440c4840745140030f0071246504174a40400c46901c2d907001c0c121400d00c580a1100c04405545481005440c0d060b40400098690b82160f00014085001134100f90082c0c1d60190691140260030f90140d800c00403603800c1161045c03000521034109 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 450301106 1250 450299856 450299869
    0x21060e011b050723162c060603130516090f060608040c290d020a0306050109121e0b070807090518070e2b02030705040b0306181501060c0b0a290a051c02 67
    0x8040f81c0000600c02410b01200082300c2d030100905022031103401d40d155608100701440302c4114240c0d07417411000240d0700c0da100300010740b55482221510b00e103040b600007042442105407030b004a030005500c0401c213042010b1080d1090344175009400303020480607401c1d407071a24400240303580d808568005807500361030b40009042e42c0b400e510031070400203445414400c0101c00c032070707002403607a02c030311080800543c01d04014480e280601c0c011b801a0070341c81c10000e8050f080100d20b440782e2600e64a032000c0a445208100480172035401c151040070b094000101c1240c003138000c90340c3c0e01d03034020040c0c070300601d41c02001040140401c9800c06041c0180591800310308003000401d000d003000703c41c10b01415100d040400c0d601c1030020894440c0f42200038044011040902c034000c8030440c51f40040d5100c0d07858040c0644610405d0b0001c4505102ca28005002116a4030482d1400c40000d1a58486c01c0c9104541035400720840410660000340c40d100000c00750f5521108200348152040d04142510f03050040014 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 450302356 1250 450301106 450301169
    0x602060a0b0303191b060203011d04050309010302210a0e120319020a090e040c180207020a051e03100f0c0c0b0121060e011b05072316 59
    0x5850805000074400c0d40c010080c0c4030842d40180c00141c0c0f001c20340004031203400343d4010004c0d400c010545500c042c003882d07800131030580f4056515108844c03500c0c14884113071041154007034a40d0304140813649096210ba00203191440302c010413038a0024010b9440d080c0c20505a031138440c42c84c0d8503002284808020f022071809400ea2981150031803520004041a0000301041c01c034009a00040e000d0305580903401c19400703002d07240d602081a00c1d140c074180d40350008902560494000e0b000d043c41090301d840c0208c3c0e100c0342e409080d0741034403031608041c000b0b581c0714103030000304881030300d03211112a8400b0804100c0f00da011480c041490284500c69500b1202041e86203010400c0250304c6801145500d0035090454a00e82e46100e10220301c801a40d040c030702c09800050403241481401030300c0c030405420503145409940d5050780e0300c0c43d2008082e1890710907480000c0c01c8024420002b45503098107181e54503480110810358180b4110280e1600c0582996008200152071060a5a01c043c074010400213 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 450303606 1250 450302356 450302371
    0x105061f0503041514070c050c0a03150e0c060d0227210109080c0c0102060c130504180f0b01030b0106020d050405040b0a03061a0108090c01171e0709060206 69
    0x1414560100030042442c800140040d0050200c01035007000c1c09140c0d40800c0418140406050181c180701500410903801a58290ba10f4840d02c200042030f86810070b21401107a41c007102c50b01d8400d451700206000f6091800c00042c480c02113513251440b540b82d190080003144d42d02c401c0180c3c0d503d1946c92900000c40149441c80d081064410409030f00d48400c0814030310104540c1400b07060b90000c100c07260140130340d0100141a0f020100301e02e00900d80005048071310356000d800351b40686c5c4c0d0b442caa13481c4a01419119000151881908200508017640b0150024800100404440440e41c1325108600c0c00751108503022031351200100248070700603200a0140c9480e1000e0580918199001003940c011801141d2045650f4140400c0c43d40d200f49943d40110fa000c03000344035646c40f0000c1a1b14a4002c1d40c00a4003041b454800181d5084010501000c662016110620002e810b8000300c00e504900810702e0404200d104da080154040140103584140c000d82d60342040c40b400c2c0a8000c0c01e1400c0a0080c0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 450304856 1250 450303606 450303649
    0x301141e031e01150f03060b10020d030903090f082a0901090c020f010e030a020705032a060417070302040c020f1f0213080a05070605040b2a0f010506 66
    0x2003030580c0d030109819401c101e4158803403040e070101030a02e500408500200c05589083e407000004c4507290303400c5607412a40640d404000c07201401c001e211040d1a002020401a000300040540c07840c0203602c03140d0042d00a181c240641d42d1074548000011049410900035031380103141c80c0021582c0e0002c6200028144d00702e80041150034000702e2403028060203030072041c94032521609807103842040b550094104001c008e01c8000b400e40c1e004d5840b0340c4a4007003640103004129001c123a90400203001008210100d000d00748001580800244082084e518968005010000020b558000c0e40403404080d005501030000b82d440d520403c8205e0b02080300c02d02c10b40d0401c0c00304036000e11001c1802c61422407400b5005288022900e020341c000d00c1440c41c000d1240e0442c0382e004c42c401c0c1c2c3c001250541079100d1070403104103607110001504e03075006603c41d11805c0c02082010030b107110340c42a4070001d100c500d0302894501010940000c1e04080d0b00e0010982e00d603543c1c0742046030380e15280e00480fa16101c0032500c07 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 450306106 1250 450304856 450304909
    0xc02030d11072f06072d0302060c0c03040b0a0c0c06030b03150103020904031103130906050a0b0403120c05240a20040501050304050a02040c0c140102121911030114 72
    0x521440d8000d54003513103d0300c0b012507100300384041c05054450501c076107000d80b141c8140340303504071154034403105081d8010320401d4005100542c1c4a411150400380501c0111300349460700803101103a502c40502841001035100c01140015428446040035215607100403604803612000d16280449601103039035000206401013016807107203a1140e8126030507103401d03641542c6094051307246118806030442803142d0b80c400060400c0301c036803050003a60700840e0116016651303201c030b244860040780806004500c0c1c07840780510b82030142250005161246054510600704205000c889500d103100d80c101c0440e80c0400c0042041040c41580d00c0c9000803420b520010040000a0700e041c0198026241032200020114082c004100844110154010000e004041100c90000e00032040c0c0e0f403044541081c501c050034003116040c0283d9079621105c0071000d080f9961080611860322445c03001010030382e91400e0004460b60140002c42c00f800e01111810f00131000b15003803107050300e00044504640c8001c80392 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 450307356 1250 450306106 450306173
    0x14010905010c08070f081b010e0102031e040507050409030f080a0c0212090a080d0f080711060f0711010c080106090902090f2404060c1e150c02030d1107 67
    0x40b0550309680200100d034440c0102c1c50964150410041c014000050110b44e5003030311a2600e0780700c0403072010a0002d119080b40c44949030300b40d0201380d6004450b64446105d900250022900ca00c0c2e10a000d40101c0d2000796681002c0f5044584020094001441200700709041c10341011440b60058138065080095030312010009440383d5140090501c42d04002403800429a52000c51801500015040d100084940b03a405071620302c16106810225010340005951140a45030081c001052080070f4009a92070801035481da02c40201044184036607074603200d9a080c0244102184002c0f60b440384400e03941424006441c480f850f61200541a00400281c2e900e51260ba0302c11441c0042543c44e54030300d8000070031020f0322041c00010300500d050041400602d45610080d070300812401520348a0444039140b000805070070400c00003418407070b00644110381c80100355000c41c0d83c81c800c6106407070820200b00314820964000420701e036007101000c100c03e42031118951a01848422011500400500600 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 450308606 1250 450307356 450307367
    0x606050108250513141927021908010e010f03052521020f060c0d0c0203010f060b040e0906090a03030b040207023106050d060207050a0503070c1401090501 68
    0x1e140e0b400d00d20704210010009800303982134401105039607401c4000c507901c40c0ba030b04107110f031042c0515104208842c10710603c50340520f10318042c1e66100784000c2088405515400c1c500d00724280c04094142c0c02c0106044450345d040c110280c80000d6900c607035641d458143e407031041001c181c00448040e00801010000601c000503400201800c4150b8400b60b020b080f0041c0e02811000d0748000d215460001000d4180300051114812148c4202d4850b1801c190714410b00c807583c0a440b4030900302c0d600035a8000c551a00401c01034590910003400450300070100d48840003511910740c08002c0988000c80e080c4051051a042035030301858401c001c00d000c0c904440c03280d56509400101405041d0340346c03412609520345404803100e41d43c01030a984544641c01c05e401100b580d050300480f42c0c03a40c881920b1040300c00c580c0a03203002c403280100034001c0c00b841c41d01c424001750301c044c2c0111610711440c0b62150000c1e1040c00030700324160052a02601c0d55184c660b5001c02c03c49413001d26410055000b80501550f078100 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 450309856 1250 450308606 450308641
    0x30702011101180f08120c1c1e1e150302031e06010e090a061a1801030804060e1207030b0f0f010803070f081b010b0a0608010f0e060315070c0606050108 67
    0x800840c80306134203404d2800c0340344240d041d9150b203034139000200728014061800505424a480b20ba1610314442e088c800011500c1c0078a0300d12400b0560315003080c0804254001c607011100a0200c6500484004d1641c001c584070109403000010140c2c0c010020344c1b03428090030442c1c0815004524600c0c4135400030b5910780c5c605010304035180031080d0204800d2a420464407071060782c01341c0300700500c0e130b511410702105440c3c0c01710440c0700f00ca10500c0d03031200071101850f0a040b82c0d8011041402c15003481c1c402e07104049001100c41d040718001a208007520b80802c4620001e6010b00c0424032281030000316101440300060219050703000a10040000250003c12200d415400c403c185000038402c1c1b400c2e004500c81c41043c885030f400004c5100d06002019405980c200c81e08840c0246a196240416902d03c18248034005103070482900403c801d2801d0040c90383c6c0858000c007581d2043d041d0541007142a441550b0139000200c16100b0007007084024030400b03000d040f0034203008110703146c00c3d41011503448aa = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 450311106 1250 450309856 450309863
    0xc01120b0a0501110a0602030709050f042c0a1b05011e0801030204020d0e16091a0a03020f03030405030607030501260d03091415100b07120e01050906070503070201110118 75
    0x3c001a030715808410322400340c034207500481c159609e040c40c001c01000089a405810310031102001140300031300d05403048070410340310840c40300107801d103100806920341301a16400d41c2d68020b503400c45000038105916003582482d0706085403407681c14603000422201800203412403281003507100030443c80d0041803890441c1d9048070050703910240d00b02ca4001900311040404520b10450444002c400350354041402601c030005801c202082481c003008400352940349003190014180e00c814005403e022031003003011540030f0200d9240c07036504c00101c2e261440c21602c480c0000ea40d41b00610288104100400c2d07800512140283c010080302c21141e01c403800d00594505043d65640305030200310700407041c2d000c0c00100d8015526007030701c800c290303103001001142c0c0c0daa883d841869001c0f0316403800784140d4404541200e03a40380d50b40310400701a58014000d0f90a6070500c2014008503015955002c0189404c2e07120384040c42d1104154400074200c040c3d40303540400140d04121540102c2001d030002d1400c08c581 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 450312356 1250 450311106 450311117
    0xa0501120812040c0e0a05041407380a02030703020d030c090501180506031302132018030319031b080a020702040905010c020d0206010f05010f0809031b0c01120b0a0501 74
    0x60f28a02014050b03450341c44034510140707420800c00710110310b5000074480ca004d0a5071545503508180ea075900e071140b5008440c050700400b40e08400c41c03552441c0b40012072014000803002d5002c030b05401155600010021001030b4000a021000c066051040c9003840301241000d01c00385c0d0f0450300c00341c8080c0c5680540c0313040054040ca55198462001c814100078000030b00401c0e540c1c00e03e28941112040362590907400760508500c1410005042d105520300340341e042c2c9040407000038548084901d944202510607061000b10658095950240000e1408412003904180514040b0002a007a210103041d5540e010100c00540c0d07210980241501c0d500091412006036035021520005005141003130010709258138000112103100d40002e0740d4100c40c0101e40031641642e0b038441d540140070b41d40f0300906001500303581825000901920301c2d03941000101058a05060948410503000710007006502984d5110900182c0c065800a110b410035800802c402e111101442d8042001501c891044d1810401c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 450313606 1250 450312356 450312361
    0x610050f030c040e0c150f03181e0606040c030203100b0c010f09060905060c1903020306120a060c0809280201021f09210e101b0303050a0501120812 65
    0x1c0c0c09005101c145100180704208039260001e8250b694108000342e5401507142040c1003d2200703c0000f41c8180c8030038054146e1459840548a485510210345010080d20840034000610401c40d4154211503844e01c0060174a45400e804200655920309003600c02d1510400a02c0800f20181c041c0c2801c0c2e07001400e05507590700c83c42200c1030061940c20001001a468500308804100780d5800900b0204d0094048508a032203a83c00c1003860b10078002c000710b4040606028025190082d0060f60340664000c104100300d03500c4800042c240000414111489a5035007020140300da0411402d40d0000340c01c070002c02d04c0c0981031007103113081c108003804e800154040c25581021a0310810002e034400103401c94460101c0c1c1890001c0c00541003071a02150381000b408018950344c000c10361032144040c0c09903540406a044802840141007101e800c0780200042d10141c4007281100180c1c0700d034018441d540000b0185070076500b5408960060b0071140700103981c400a2404584500c0640399440302c4940e0708241d64 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 450314856 1250 450313606 450313609
    0x103030c020f1f05070c14030303010306050405030d0c17010f0602072d060c050d080c030f070905061803060903190f09050d0606060f0c12030b01200703050f0610050f 73
    0x4030074a0503c949204541d02005449551000c0a011483c0c07245003140609601c94010010032040460356a0700750b4803c0c00100049803058002c5600300c0c0c002c10942c1e29040030702c0c00f050103031103581d40620041080840326039295528881124014001130200d01c00490a00c0c20094030380015109000700c2d001c0c103400810040c044030190000804101e481c507018a52341e00e90240c47c5020280c025180c50003481c4000c40481c2c01959203e12603e0b40b011402c2c59075844400045030b805001c0d1510b0104048600c011a82d03881d540020400b9622160102500c180b81d102098074190004180c00101d81040c400d07950f000d9494a036405145c011402d10680d106041c0c041260711107025406154840003480a00c02030180507446041074921a41c2c4150440103882026250442c00071402810560a18030b1203103032900c01e62010780d00100524016004170303020040301c0703800054511020f155410a980800403c002041005408002c03040580346a00d00075091805056a0388540c5019a6018a081106 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 450316106 1250 450314856 450314869
    0x610120216030e03060702120405010c0f0c0905060a08010204080a020423070c030e06031005010311070c030818010c0807230a150608210a03060323060f0103030c020f 73
    0x1c41c1603400c4581d00140c1da42801001c482d03484000a00178000d0b0400b0640c468808140294501d031a0a103a40c0362500d08001120400c48203881030303d41050b01c4010074002841403810740c0082402e0340001c6880d040c403070104440001b15074015100303a0701c100400c101115000c5100720070303503030125000265032601c12411000d070a0342100590700f00160000b080042d941080d20052628020b035500c00355110040300b480000e20003941c42e00391003075510710304000542c465006280340d1804e00601a040c2010384d030b110040d80880c2c1c3c000302c400d1200802c0c0030342a80030070f5185a146e10802d180c0303401d40344681e4880e40751500c100e0a001c3d04601b1145002486c94101c3c801202101070403c048801080d907134109501d0515996403400038040c2801400680008001101035440811481e142c04e112815007050a80741d0007040da241c1850b44550000010401c1204040c40030845000f050020090b0707800810f082c85402800c1c4040394032144c00600109900164414140c2d50503190007100d1079100000070b12 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 450317356 1250 450316106 450316117
    0xc0309010e0634080612010f09080c1015230907050901140408030a0e15040803120c04300507140f120c010f1103030a021c0506101202 59
    0x814860b000911040c00003003890780580006020310510300e0994512604809822441504000344083c4040b54007840c050f282c5042100b080030000800e16017030b4a0b007805894510800343c6500c1c070301154003640700d48140001200086114400c1182041001c00c10822027a6070081c0c1c070221210b008040380d203e049800c042a80a401000000c0f81d1510b00d100400380d600404407c0e001030887c50803c40721008100030b07142902c0740d4001450402e00300300011150313003c4070010164080000d030360280d40f01464500030005002cbc0540910b98901240c51740a0600d14050456020f5000030001000402c000c4000c4074140078950703c2114800c51071042410700c0030b0305094041c1207070240c200005106142c6952043c3c01210903105e648070038854030100219140c0a160b6402c194001100442c5079612443c00740301c00b0704c00c078201400860210a400c61440d0011154060050790000c0c4105d091044c001c0705500c0c0d90604c510078080e91902e0030214134007041e000c00080620410545c4500c214100e03406650 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 450318606 1250 450317356 450317381
    0xc03041b080111041d07120903090308070807050f0f03040b03090c0405160e0f0d14070f030c0609090b0a0306050c0c060a0603030318031704060f020c010c140a080c030901 75
    0x4040480c0c4600f41181d0302a11801e0012000101c59420309114881c84510859694803105500c44074054641c0c0900083d100440401c2240c403c0400013480f500c0141c6001401500080d450740d050b46000c41c681850004540000c0d0700c0a100d0910104c8000201c0b010f0310540060640c880c4c8a02181528001040c12029402401e1400300906125484030f00c1e544030000c0d0340d469458220344000e10131030900441d94940c21426088811020410007016a54001035450454003401d50301c086080c51240c80382c05c203d6408640040c10800c007680040500003074649880104402c210020001c0c2110b00320b0b100c0248840d8840000809401d10340c02a520010078900640d8001d14005003000010411408200c020910b44201d900001c05101044a90240d25440308409040d607048101c601d4580100122040e546031520b1344801405030025201c00e07001840046800c0310b0b6940044c1c4800021202100a80700902c43c041c1490303400f10515030080d2240708000d580c0e8495000300c0340580a030070140e8 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 450319856 1250 450318606 450318611
    0xc05070317040902031305121e130e09060a140f070809010605100309120c0f0b0a090614070e030f07060809070e0c120a0212190609181403030c03041b0801 68
    0x703482e0141b120040003140c07068080e581c22440d5609103410501640d8001459805100384554940402c0070003400e03c0f941e1001c900c20a9942d55001c1080418222841c04860f0080c6041c0041c1443da07000e960500800d64261680c24580304840021000008104408210310a00469120003007035115801030722002d00b40c0400ba100340070001d0068500c50508031029103030354980c100c84511940d0040d000a92100000c940000d8030f46800701454809081851039558440300c480005981e8800c9048004101c0390300b80c05842c00740c0b006270800c0b200480190081e081600240342c981008226582580d4860820410030344071402164940f100c0c5411580d800003d400c00d00800c49202c03006408900300120461180382c0d40c51001034168001c1d1010340d09421b40746070100c1c1085541003201040c0d41c070b030408006240c83c0da03264810181c8030b500c0b1740c40b80130b021450b01040520030a0f04117000c031500410021440c50030034401c484824807004202800703495602c111006007540900501e0010035841c0002e = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 450321106 1250 450319856 450319861
    0x60406051002010e0c061603051819031e0221030702040608012703020303040204090f15060503010b010c0b0103030e190609060306090903020d030b0418060203090606010c0507031704090203 83
    0x40e008000808410250380b003117240d46026440c0180868075078070720b14000c4207044902c42d5406e8565400c144941e00010440780d04450041d15407900704510079840b05141e04000d031660a1014405d03409640c0d052a41c4511a0103e000da20343d42111444030082c401c3c40640004010002070443c020384100950207410400c000440b5a015082002051102d00303440511103124500742d0505155200000d0250700180005005841c2c0355004c0483d0f0741c0030707a200d10216a0345580324460508030409a1180c1a030f50142840f00e42001d118111000b542800c00e0b1005040588030140c00c82814400201040703034652181d04262143c0010b00c0d070003400305c92890801c6499000107400100d02e4000c7c140042d280030000107021205019a10960343c054000d81200101c041044011f03048015038a40c204c3d032650204c9005654064404035950f00502d00181c40e070421280480c01d04102030401c41c1049882284823002ca00b0200f0b4100484c0c3e0300c501001040104841504014041c5502050400b4400b008 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 450322356 1250 450321106 450321139
    0xe0907050f030a140601020d0906030c0c051501030c1a04051002030f07140d14120402060c070b0d11130b0903190b0f011509121509030507060b010509150306040605 72
    0x100d00f01d4070401c2003144e41d5031a0401284e840b40c290072040b00007600840100020f5010f42c0c00300454590034600545c201c001901c0386032038443d83c190104480060040100240040c01e4108005131010004a0800388844400d01c041400360b4090700307204220b92025011501c0c000c2041301c400c1c9166080c01501c031031603401c240c03442646560a044540c051540c001d5010352095115100c00480070401c41d0901c0807002c94800790391740060040b40c1100c0c04210503c0282c004000c3d000082815180d101ea8908914041606483e020b04612071a514140151340000b41e039146001c06031800b1051190b261680800002d16215040b0141c803151a0005500410310000c91405440f9003980580401c40343d03a41c0c01c04503000720b1944c1c032140c00611a5901032050b810340c00120708080e40200ea1100030b03401c8003c00d40040740c1c400031084020460001d41e80c400c110b41030003501d0625200f42821400c20101001240d4514124800480c9400e400400651a42d45503031240c4098030000e071041016018010 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 450323606 1250 450322356 450322361
    0x140604030204320405150613050415050c04090605150306060d06030b070f021c0f0c0203070b0307020c10180308030a0e010603080a0207081b060a1101091b05010c030e0907050f030a 79
    0x22400e51707a50007541082803103007100b01c8500b8042c1102074100300100040c000d5131030040c203010300220761a17081c40e50725584104450240034010751901c40c4880d40c5920b0302100c10225001035104502400c0d000d184030620b41481410349512450070f0750380c0c6941320b0414181c00000c24203500010507040c0c403a802d005000f51f02c54640e80403103444d07400703c07030b03400c8811403021001384c40e90704501d000035a0035801002a244181c091201c090302c01f50403121460740b215401b0003d50022689440103074001c601c50607441c83c0421103066030104070f0810846648060400401c80c088078000945862000404203a00c8150b640c00700040e030080d40002c010301500d030714028405501002c0d0150040c4100b9030003240800000c529100202c16018081c00c11003242c400f4401103400146c07407a0244440140d0105400600380541d00d00644291545454412080b07007810090345260005070400c4062221200040c1c0c011007100100c1c0401c0f524411140c0d40c1010494007071207010104c0303041540c048107010422400f43c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 450324856 1250 450323606 450323611
    0x106030c0303091e030221060f04020a17150403110a0b150f06040510020f0706080604050f0c0d090c09060f080c0301050f070c05070e0415050114060403020432 70
    0x203503101c122051391010003910309504d21960044a509985041006203020340b611341c42d194884600038144000340d80c030300c3d041902c101d9141c65a04003240c208421445c1031300c24100030788140e000c45450404e100049607500c04a038020642c20702d8170040450f0030305018024801070060140100c8841503490720b0b1070f190b0100e0660710504582105d40850015281142280c60340354005415d8034101480c10040140f0200521500d41c10340c00f5a04603105500814800c41025188503201c410b13060805e6014482220790052880403074100385010700100301700f44403c40d00100a914400b103040141d030b050126885003554800701182e0700d403010010b807035040c4003210f070704a604e80d03010313149456078084c00d050030f90703108440b050b121740060702c0080e14180c007031380400c002680288110b4140075110685400c0440040c0c5080d40c0510002038a8107003441280240ea02500c3e41c0e01c0c080032085032050204645005d18000203100e01d48407100110010180c140d100c011f01841c001e07407100d040c08101c80c0d03020002c0a = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 450326106 1250 450324856 450324863
    0xb16021002041d010b0405030a0807021c0f0317370507020703060e010e0717010207082715030601140903060a1d0d090308030604091505071b020901030809120106030c03 74
    0x20000042103e400301c1176408480c1c014000d0242a075056444403041d60001c401241cdc0450132080c0c107080209100e880300c180790b00c12031001c4160303a058280a07126501243c211034038030036200204001400309120496030601e404480210040c0200003c24810038a426240d01c41460328040144072540000c80d0030450340586400c100e8074900506481c02e8546a41285136241e100440c100f0012100c0c000b44552080102c00042c14060969101c050300d52182c049103880c01e10040e00001d4040312508854a0b00c0e60890300c852984c0e400103160041400003e002a052044114aa000144514080f1901800c0003000e80d0544c3c0340c01480c5000419001d80600e40011180348110301d01c9100290144404070340380c450700f495034034682d038501281e40001c081a03006510b40070340b007000680104001c400c41c80c0d0980f000c90145003140000f0607200d21070340c8100d165215440b140000d601d41201c4213054030340118410f5a60001c0c0004a0100d040141042c40158a0604c0000074810300344a0042075a11 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 450327356 1250 450326106 450326159
    0x31d030a0609150f052e05091305030403060501140907020c1012050c03010801141902070f0503130509331f0203030906070e03100b0a05041103041406040b1602100204 73
    0x502e001c00c0c41c80890b904200c011100540078090007540b0781900c42300e5004507000c0c1c06802c984030654801c0e0458000e94811103605481d0b200612503241004010b1446060640b2440440e10700007200030341e84e540b802980b074050a0441603800c0d035584551201d2240101024080c0b015003031203928036081e80d0003449511419481e03c0d51103140520020f5403036000c1ca10580103401503000c8128050000e41c08000c04444016003203c01100050003840504641d0381040c07500d03031307035140f4050a10440302c40040c0303c105c00d640d85610b0301c5560310403284d02070b20400c1c007029803000383d01b00800403a100048821500c0d2401c0080741d0282400d5500100442c40f6040b07903001d8500d6034441c9403043da2045242c840781d0364160010030030310388030107429030154044850040041c421140d40740082022552440300c0382c445250300000b04414024128820100300d60700c14020182c0749029119642c44a40142480320040c10b08c5049100f00c0d1710810190989103d20b14003159250781d078030450a01e6000680c02d0120320203 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 450328606 1250 450327356 450327391
    0xa020906010309030c0311150708040303062103080a0b03030301080303071115060105030912040803040905010e0106080402061b161403060405100c05041809031d030a0609150f05 78
    0x144240103520f2100e80c03584400c40c00031010b0b0343c181c4690a01040b070810600c91101c0300c803070015030b014089002e40c0349500c4022003400c0508004040d60362a0b040a070055142c5a545586002e0b0349580c00340d02030b0517140100664660b000c2c60805010030741706495040c480440003140b4010040000c5004d91001d859040c8029450035070700c1d448000c2000c02c0c0d900c41003100002110f0b540a070005651040c1e00c0e0050300c00710180280b2907400c540094204140c1c69102040c20b00c03006503030b80320f018007401800c00030028030361500030000c0000e0002000207004000200d07012500c01c440e0042a04000d15a074141e130741800101c049581104182d00c1102203110b80c0030501c0005040109015000e29000006048000d03a0380c800000585101c950304010000c040000291082242e00f01035074012007d4008503a400950800900c10b01c194140450203840b0380c0d000038101d0340d00180c1c40c980a40d1103100814060750314100894280c0045200c050b80b54184030461206165a40c0641e1042103141200103001 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 450329856 1250 450328606 450328609
    0x4030803101205030301090f0207020406240306080309010e01020f240601051c18150f050c31170c0a0b13030f0206160302070e011505120c0f0c0a020906 67
    0x1010b40c03202c040c01e0f60300100018803074004550002c04032a50b8240b800340ca000e4040d800705044035402d1f0300180c10100c40400140c03440c1d002c01500140070a15207400d01c243c9003082c0b03d598481c401e4046550500a0400644900c1e0b402803046146201d03101040d2440c40607800b030742080238040c042d0182d2602c41260000f13942503020b034086c0ca0a0741034111020302400911b0b00c0e41d500800c084000201c200d110465900c0003c6d829280614461a50b00d1b40881c01c0c03400c043e80401941d80150104910300070a0282c41e211030004c03004c1c02c807000000741e90590716424a400b000c003500d4050b04072991340000050800220000001e4503508800156040300c40b250b50341490501c60f01540003810001004d04404001117001e41454a110701d0000303040c1c91400d00008850b140107800000100d0140e003041e102000042d50b103082160040c42c0b240c022030300000d943d0340300410380d100d90144e0030035020510010031240a124020b44214441d940002c0c1d030b903005503000e100d54803420b40e2801c81c0f0804020300050034a = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 450331106 1250 450329856 450329879
    0x2011206080a0209041511130603141b040f061709061b030406022115010f090b13050310060911040308040b07030c0f03030902011b08031302060c030403080310 70
    0x49030080c030007502644100d40d0800c0382860010700f080e1802902561144038983e1a1f114503240b004070311030b000f40c0c0e400c0c2c81d412004d120241588a0b02c2030520708520540c0c010b5488002c141e0041c00c400c01c5555120a00309030715564042c1780c00940c548110b40d500454225003102030002020b01c414103400d05603403042951903480720b040b2039121502616a407504185c501c01d401564015100e1103000d42070030321250307001844410110040c10480016424008402c811146600c8529002c1c80d000d4040101618081c003481550311a0b03103004030780000c9241c1003688404403c8042c09004040c0c03071100b040751000307201800c1b803401210311052505c8540c04024000c001240e0480e9805a1a44c1c00d091030b2000c1c60030301d904920300075001e200c00c411444001072148181c07040060721984001a21410b5800010200616103003d01d003c080070040c064007203081d0030b0036681d1101040b1341c29031608240744003060f45c0d030003264080c4945200104002c003c125041000d944901c0c5502e0340b03009043da582d0505490f = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 450332356 1250 450331106 450331109
    0x40c06020f062403030405100905121209010503150907110709230405071e170d17060105091e040b060f090907050705030a080a15030309050603040f050601080a02011206 74
    0xc1c3d54652050510b03182c018a0801800790700e00405583c1881e9407240031800d81410007a540d000142d14201c01d22552400e45281800b07254144014020401480100d161520907030120740d05010000c400901e004a42500c80301c0400806000d00709035060040024208610383c40740a04180201c0c3d001142d42d0f207442c0f080c1d5460044845e071584a01410300c3c001300d99448081e106513043d0141e0f42c1c01142e0850b10600e9900e420141c007445035580c514004000c402000c1d010003a50300c40d0408001c050ba4146d2001c194060030f40000d00c08501a01e940d80140e500c1e1191000e010341110302010b07204010030214075402110300d4103850620440b1012420400203218107038400018800a01040406082045c141644200c45003015450306000352203580c9150092036951b00041c08070020440c1c000b0321400350041c8403c0d48210703c4105401c50380e000d410341d0300f10b000f2036008010100006042c049000302020320380340c02c101038547c03d513120841243c860014150990202d03c1da60001c40340c0f05240e01c114070 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 450333606 1250 450332356 450332371
    0x13020d14090114191103010803070309050a03081905360102060f0705132412061202060f070b13052506110c041107061401050906011206030b040c06020f06 68
    0x5400e0350740c40f4004d40b03110080c0b080b00d04519513280880003140c08410000c43c040c004140c000d6459507100d19000f40721000c940c004c42d00031550140c0410025041c1c3e01070b0b139a5405026400760007410303036100c22100c501900c3c41c100c40c3c0341480300403e03103100b520418114040f0a82d010b03801c0c40d00340100043e680c2d1803050b40c0a80c0f1075080c0400151001c3d10400203428140a0180a6200d007643c50111051150708804800081c120441646c10041d0f0440001c1180c803d441c5410301c0803610340822165003461601c1c010b405040300082142c016131603003080700c03281c81d48585140b4044c10510380d007400380d079207200e82265207105190820702100f00c078405041c0012459081c103001c290030700e24110307503180410304214540d100391500c0c5116a0307907600606a200c07800b845a00d84482c0b140c18007402351000c05080200c004c599200600081e1a12901c45030b000d44d081c204448031000150380d0800500a03544044c101c15120010701c0100000c62030f12000311145a03089a40d40030b06c0801098403040c0944400 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 450334856 1250 450333606 450333641
    0x6030b010e130803070c0b040c08010f06060212090d020a03050d080106020f06010911070f03031a010306050d110a090905012c060610090906080106050103180804120213020d140901 79
    0x2c009083c04009690004070f40c50b005400a00903a9807000c0c0c800706407011640c01003462014410802e0034070441e2000944441c052084915010b0080c0d00da061810215000080c000741e01c01e41511080343d8440c4542e030140881400e10354a00707100380c65140c5511120b001078505030001510a1000400400808031503000d404664a0480c07240010500c04c0055426010b05104103c082649400b00703503013450090320013003913400c082074150003081c0701415028103140c03410509000c00c0d144d40350410302080c1d0240d60204150158000103860004a5010003031003070421588104100064002030b092130314950b0f080103114002c2e0107003000c2540980203040c0552141000905a2400c6824449040d00d1030500000d140e0b15840c0360000c0e03403215001320a0170782d1240030800242d641803266401604d40c100b86a1601603c41c0d4814078a4401c51180d07840b490310300400031040d96100c20416220b050010021940c2e00c0b5441e442c100a4038801c54001c08000e2840b002489102d018055094407a4003654072 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 450336106 1250 450334856 450334891
    0x1033c0c230306010c0210180501180308030603030c0706020c151c0b041b081902030c1b01021c090c0f060903080f0706110c070b0f04090c0c020301020a0306030b010e 73
    0x103100c94200400913410841c00f19800310145c1ca4405c04140c001280799100e10010700012007520060f101c5a0210341000768040d00f0303c50100b40308981e00306a941c04031440c1c1d030b20344a03200004c5c81c3d4001c50071800414021000009030b032907000100c480c6240001c0c1c850020606212000070381501441281542c002a45103171400c159210f58088503020301c004000140f0700c00a801c80d800207440d60490b000109039164140a14040b0300030301c0031070b06d0141c0c3d80154a5031400c400e2006d46809000d0700203888031f1140030350f0401c0380800c0d0155011a5a0300c0300816620003919120009059002c000356000c1400f6000850091100380d440800d0764499102e030024245995a20340f4203a0008140221182051000ea40004c119000c0d07072102d4202e50601c1c40d00d0b0981e0f5085030b0f081402c80c0c0d01102200004100b100c02540c480b42c01d59040310080d944c0000d101c0d10145003030707038000115100251b265100141c03000081d5010303031001090b030703014459480f4542c0e200d990a54142c001510714444007803c0c01e05 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 450337356 1250 450336106 450336167
    0x703140d2c10030915090c090b0a030219030206030705180d080301120c0b03040804030201020d030603020f1c060e03030106030f0b09043003141f0501033c0c 69
    0x1144031601d0b40c5000101400310361a0007101c200d03844003040342d0b5501c580c103035018842120040800341a2070301b01001000c9642d00007925020140c03100134001c505600000d401d4600c443c1c3e108005540184c0343c260b6916055000614a600500001c624402443c4007290700382000b069460810754012001403a6034284240c0311440c0e01c0d0407401720303100441c2c9100428020f4589000d540554031903d8415100e90542c8000b905100417071010b83c00305844c0100820160751460103041904009903024010751504408807500201c4100c0d0141046003440110701b492440000118100d90855601304510402082c004060710702c00202c0369406004000400c0101d81c8a41c409002c4290181e200c002140d0a07854405040c1602419038000c41d90310018501480c492650031a0312001118009c41d0392252682c0003c0c40c0e42480c06502e040558030802c1c0038109080c080140900484a101002c00c041c0e15040928510030008009030102d0074001c3c440481381c041c22118030480704108020592550109 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 450338606 1250 450337356 450337369
    0x60402090c090d2f0613090203181e060a0c12020f090d0501020306011d0607060c02031303051c020c0102060112150603030806031b0d0201110703140d2c 67
    0x4200c00d40c4002007900700400151040200075944404030240000e420380042c403e00c03c040040d00c150b0251004110302c07988000321b00013070002e4031030301c1500680fa40c0b24448030b550032410031184103150f40310b0351402000b42c210030160390210070207600450f0004d40d030309924082594052454540400c0641506032520081ca8016001000d81d04507104d041065000000301c0000d6412415a8181d500105100b10340d40c1c0001c9a43c8007a0302044c900441004550124100d845846009040302d80d031030440070300300c1d0720910445a641e040011f20341955a103034240b00c2c0e1550398010611521048a03040b448400303001050011200d030058002e0000c582ca000c1e10786c0d1004140d26007c4601c2d100038280544040e000f807081e00007450103641c0740740061408006061070134500038800c84450f450a00c00d90001e0b035410703040f8001640d0a2805e010001b030240d14440c507100240e040184010012058000300c0f5000281c030110b4019503548180f0802c566100b244504600700200d55407903107801c04250708908100 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 450339856 1250 450338606 450338617
    0x90109020c01471005130519030201030506010c0204020301081506030715181e090b030f070501140408010c050a0215090c0d110301091532040201050c0d0c0212060402090c 75
    0x20f056034118810541c00500e1105050b03100d80c01003000401c50040d5003002c080240e002d0a015203000f112800e20700d00c511400a12440001c2c101600d8a001851380d9110b090081c210f0380d8007920554503541c46070b000310307201c000340085032400c941c3d8080060141d243c0001c3d800308440314008011450b0f401c844040350481490205007080002c079020005030346105401411402205084034001c2d40c0c105241c010680c0c104c4c2c0401d0f07200742e1080c62440c04103540403031900100d4a00b4204444001ea03c0130042c9501d002d2584000a95442c0120000416400030300428825040d642a14910750036140c10a500b5001501c1000407680001580b05982c108410b4100b004c500460010200c003040350000390945c0e8003040c00302c4940c650140c1c041140da07014061086404414001600d41001c07100100700f04070358800c00c9080b410102c1001c0340a69000748115000c03c0b01c0501590010080000050420801c00000305e004251945c40b9051281010910900a0703a001b41602200d031a0040c4800d9681c128 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 450341106 1250 450339856 450339971
    0x702010e030a0b100f090903021e01090203010516090e07050304120c0203060405070609080106050102030319020702031605032a040f060b120a061a0d0218090109020c01 74
    0xc20148401190f00107114900c100fa0075208803d5050400c41400c1080c80c0651250700005d0410680300000f0b44c01085014903440b0308040c803944440702100c0c035805003182c0ca0010350554641021300c0920100d0240e80c580720421901c500360301aa45a450305804801285c00c0b070002102440498001900319810b0b0308809034a1400c11005912600042d0070403038107940882e060f1b0b0003075000b0000c060300610700800415822008015030b900c0d1000203522031100400c2c201d000d610103900d444a410f034030f90543d0b501e280c001d01211074000070800384500d1203c082c002c0e50710a120340000b44032810201c0400072070089420200301e0400a8000c140f0029112070704401c81041d07124200415800380e5100900041c5800e20403201040c1002d8100108980c82c1350000c007180801101c902c400260b00c4021501d03113402103800103a543c240c085401d0b091038614807895510542c14800010200100e402514a00207690300030401000800000380304640318584012102d4081d6408004c038410103030041410380b0381e = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 450342356 1250 450341106 450341113
    0x712020409080a050a110105071d030307241401060c02121c050d1407090b070813030309150c03120e0111030a05180c01090902031306110c010f09080702010e03 70
    0x716074422599070410800c1e030001580210b54401030030382c44402080c11070f803100001c01190510100082013910070341d4801c443d070100740e459a41aa1000c1003103a2155401000b120801241c103803000004080782094581d21900304881c80f00c0113420558400d048810b151202400a40990300303201c0d0340c20b0205c044994900550514280f4884031000801c2e20500315501c581c0d4a42454140104a03003101c2c064100c2002c0341c0007009101500004400300f565003900c0c1c0f0b02d448407094548100240300b401d940350f4900b64140d00000401d900310800f031040d503040b03262500401601400445150420348006000251511480800f1200a80c03211200303503503150001c1100142518240095442130300c0c000b0300190f03101c00300700b030004000240c0720741c0089590150407039000d2000000c004908038000d90350413560000100e0300041d0700380414035625601c000c0c1442019181c0c00e500c0903d801007c0c4007800380d400d101010b041c5419a10941e580650712402d920b00f008a147c00440303070802c40d414029050320 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 450343606 1250 450342356 450342371
    0x70206070c1d180c0411090a080105180304050307030b2203020d2601031203020405030a0807020a0602031c270f03030c0c0f080c01060e0408070201090b27010e19151107120204 77
    0x448d0450000c01030300d01d036000400c2d0360402c0c09a027600515910700c0d50780140c0061005010554010442c035080329000b0484c003443e901c50700441a041125000c0302e9805001f07007185c00c02050303004200d42c0044005a20349001c80407910b45218034040a038426241c00d01141801480003807104a01c50360882820310300141400d8035080843d01c0c205242000b035540410100e0100c2c110301d0607083c1c0101404140c40990304000752100c0301d1912440401e4074800c440d0300c510010042d030400706501c0081d8003020b0451a4041450f06201c002e6660390481640003908202c40700d004140507492402401d036010680069809141d1140c0340315400c0311b400b1030800d5490b000d000400c84030107100940240c1c011040c0d10399550351480054190782644c2c0c4010860712090011003411030b105200c103142c81100042c0c80004100312001218440c904003421540010340100b60038120410030f81c01c01c1a500f102c12140aa00b40b041c0b0181e40c0b040c08501c110265900245c42401003000583c00224554030141002c03031002d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 450344856 1250 450343606 450343609
    0xe09071404081f0612020a0e061f03150f0b070308090c03071805060108060901030209060406090c0302040503010b030f06220c150e04050c030606070206070c1d180c041109 75
    0x81c0f81c42500190206501030600b18550382482454000c0c688036155689880c116404160301c1c3c41180310303408044e450880054296110b02d0f0040c030342214041d01d40c081c0d01c07030300607000343c01044400c00005440012020208004218848510688900d401294140b88044da411500c0a00040510f00240288010786807036840070061000541004000c64900d401030001c900c040360340040c007c41c10040b034002030200545442c078266040d00e40503102544244e40b15004180940540d600c1025200c0c80c1c01c001c4105554151b0103441641c034120002e021602481c0300301966214810030384c1c5400d401880204151a0f0444850510021000010384c0d0f00700883c0c449a5828529a000309445003150303000781d8240ea0b0203481150038040482e400c101d00d09029101c0032003030200601c0d0b113004d90310000d013030000c0d5919041a070b15600d03400b0416628843c2c540c40d540315060f03000544003243c58407201c04680001c0c4055244140500a60000c01021411504000103800c00d039047d10390f049402c000c611080d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 450346106 1250 450344856 450344863
    0x1b0c08060106090e33030118140709050f0c090d05030a0203030a05072f070504060306060801050c0f1602060d0e0c01020d030902090f0c0f0a02010c0f0e0907140408 72
    0x304225103c8040b00d40c44e203850b100c8111401080400c520010304c03440221706000001841d070074008445030001180d950004280100700d0442c00312100601d191040b400c0010001c00c5880d034100d13410076248101d0b61010244180c0b00b09603070510b814032130170000480c80049072001e00081d0000510072101070610f074032140d08551081404000503003000007001041d007014011243c001c040e6241403c48030f100340400d50511000c602d1a0041c1860402c4880d151050403c03108015220040c41004115901d10f414002020707140301d0b9242c15420200096a6000084207030342c02d940001d2a40c0340307000107020442d0544040c6020032a8400020b000b400503c22040c4680159000385500500e01060b260002a207080109100c00c8100750070180468016101c0d4003a0b075420941d02c8815404030307111039141d4201402421210701065001084a00354113505401048105241d03031070b049026113a2860494103100e0000e07410b5000315200c03011442c054410104c5841c5003081308003984c1460703107500b5003031300303 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 450347356 1250 450346106 450346109
    0x6090a0b070c0e0405030a140d0e011505010203040b04180603140102091e060a2d02031306030552020f0607080c0309030c0610030b0a050103031b0c080601 68
    0x2440c00c4086180d00401001c03200d10806007000d14410750480c5041c0e43c0b455668410b0b00244401c00030398001b403000b220b030300300180e540083e04440c060004400b1034481d00d0007060080c85102449004060003d0b555001004407010358004d01c216170b15090908201d4003203401c100010003400c5503102400000f05030301d1969072075204080e50001d43e42d43c0c541c10400ca82610800790402d9920700344400c00c0159950202101e222040904002c1500002c400c80d01d003400c1485103491031043c041600010059078044010100c904030a40c001036225220300049044074011a030846112101020142038801e0751021074204020a10351145a48052608690b40917490700c004841d00d041603111400054040c042c8001020b08940100001d1501c00350040c98400080c04418444a001001c52541381c824011900074040800494003a41022108112440503910045c1d905081400c0426000e508600556040f2a05551001c510302c04c1e21005000d50820840e00312010040740ea8001107808092280e85e0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 450348606 1250 450347356 450347369
    0x705010603062309030d15170105010806150607030e06090a0b0a120b031e070b1c1b1409130e01051b03072307140a02150705190206090a 60
    0x10f030002c943c02c1075104031000000034224546140301044a028400025a14030451024003ca424003902c25086001d4403150030810091809880849031544150040b50407100700e8400c0311956941c4021220b40c030080449003d60012042100c20042446101c0300d543d158002011545000b08410016146a509a000480464003c144000070a420044142c140000300704280841c8000302c0c0043d031528912101031410b024000100d00300c514042000034007600c03c2c40d2100350b68200d041c00c1268640c0804569242c07560402c4090a84200c02d1842c1d031904040648440100c0e0b0004807400b111900842c0e1710076001081100c100c06088182c0c02a00194101c00d800082c50b402d046040002c040802140518050740c01c00500c0301c1103902a05520002141510700c4c11007541c0100001d61500c103800015041c110409a8a032000e030010650301c140920884941101000228030215580610b640242407504240780c0920700011400c0300952003032000300114500200d07940010040c4826400c40e0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 450349856 1250 450348606 450348611
    0x12030306260c060f1603050f0a03020301030611040e18030906070809040b150d090f1a06030c0103052215051303080606120408090d120c1709010f0f05070501060306 72
    0x14000a502801450b0707030100300740c1d401407030702c0081301006400d445181542003000303149481d05014140b2442c15100f1450700c644080c1d41c6c480024200030b020790020300082d104185408a0710a07003600380c1e002c40d41100c1900c0f103000515034810b0408800303400399a0013200180400c0044900c83d81d030700d00003001070358804e11a070340c0c8410b160001e000c200c9a10640d041d01030b41c00b640c619640c0802c40d01c00c1d1081034032604004a0105200e140c500c603c40650240201601c0c01c3d1746804940700040c1303866911450303081e0b04581c4a00f0303105004401382c4034190380b440143c0d80180440526010000c00300003200c0d001e0640d540c603074000001d0715000c588084640b0b0344280040b1446004250f882040c3d20740003e800c0311880d060401610aa40c003010700504000d00103000010b0043c0143c5803602c0c1060525000062a0700c1815401c0001e041c5141e020802c98088804003144002e034034540c410b503003c041c410303902c400c07030000d5801060b0741e050800c000c51028040c050221100160090007844003070761051002 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 450351106 1250 450349856 450349919
    0x724020a05161415070b1003061b0305070c0209061005040f0b03240121090f0503030717100501081b030a06050a0b0a1d0d0218060a1205060112030306 66
    0x2c00103240c1c206051944a0f420000c0425115030304d481c10740300301c01d401005144142d21940303d11038801c00c03694001882e1605101d26480382c0f4000c100c840203a1105501c09008943e00c07c1001c4a5400030804020341c01194100811603a003442801c000c2c610b4104e0900310f140c039813900c210442c21b20441c0d0115a05607000070800c01412051241c800120380c80c0e556000d01c00407044006020101e12a08000844c00100041d00900b1001e40011490700e80061a178040c032401ca0420580303c0d41f00b00c4c0c0f2000407910090030b005041ea044502c2c14460601c110756605503502305001125010b201a140d030116580c0c070304c0140b4401200a0040d0b01680600c2000a91103241400b4802e1300c2c0504d5008841d4808180b2000c40240d0f00710030b003400c11101c400c1090741c8190281c0009441d0044061011750000c0300b000b1840040c440b2001e80d1401014210b038003a14065071840f03580c00004601500034455008a00100003104091b41c4000c0401c0c42400c1c04103240352901482a1007443e40d10604c030544404046 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 450352356 1250 450351106 450351119
    0x1050108070f0305030a05281e0c021503070507020a061d06040303051c061802030a2a0f120e0604020907181a09040606080a0b030724020a0516 63
    0x56000100807500340002c4440c5980c48141d181d0180d6a801c4040c0000020320b20035501e030040e15400241d04110101c0215140c26100030200d85400d04541e50030721004c12031000c6c4a000d2801e02000946c0101f007038070008500181c200391900f000d88448144079091007a5001a51044100030150005030ba42c01490203800741040041120005c031980200000c000c2031000c02d83c00400c9800500701d04c00000600b4150300c1c008001000b043c3d01a050b00e00c1084203c041c0c1e4801d5070015400307420103000900c00700b12820740340f14050750340000300d55076421000341000c00c0b60701507800710304c2c602d0081c18488400304c401640c9a0549504c01c5e401c403150f0300514100011890980000354221501c0d00d030500e100c1200030040b2090000231b0048440808040c4a03a6404801e190300b2501e44c0200900300344106640c40c08050b1400c2415103540c0151414072550050310b080000d03103803041b44d1504070101e00400045041000c4028209209c3d0214040d110081020480030426941c43c100d09001c180c0700c1603e03204 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 450353606 1250 450352356 450352363
    0x60a060c1b1e060302190c02010e03070b0a0201110405060405132a020f0a0209071b050106090c020f0307020d030305040203030c0706050c01060602160611190c030201081302130e010b090901050108 86
    0x104004141340c03041c80720000040c06202050218405c0d4200809031528a00050700c04001040003580d140c0700f01c03035001c54250f11400c054050304103250001d04c0740c2e070304a400c1808140520301910750400c800f48410041407a004460503031090741104001018041d8400401401c201d2a4014801d090050000485250b0420060013800c403080e0180858500c29800035003c0c1c20050300313500401040c03600641c000c20401c0b900d40f010640c0039000b0001e03d5a641d5001c0064442d151192016000c0e40c11107240d020f0b408001c4235111a801031800c880036000d0340d4250020303c8040d02c280d80611042c80b03500c03810f8400300312032005800940c4946840d103000308822420340b80150401c41c119084240da0415a03041c1d01034842c02e40d2100c2c10902e80780050010354902d040c5100202c001c0c0d1540f13445d00d401c14488900300c41c1007903900031303aa48100380d9121010405405800003000f508002941d40c0340d40361480580c0300304104003100780040341c1c01c024040000e6800340c0548013070446035901d400406c1205000c1 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 450354856 1250 450353606 450353609
    0x111010207050303010f090509070620010e060403080601090305190c1d01050901210f0602071a0a060b0306030307200d0605011701050405120a090b0d09030f08060a060c1b1e 76
    0xb000c03c1c0094602000d90642b155024441c0e4803c2c072901d9810700094a10781300b24400e000b00800020008802c40c0030403199103503803d032415801f00d180800801d180354402e2000b01d080e07075002402820500c00364080e4990301000703a03400b5180d401080101041260580c2c58854164014010003015541804104404051306a010104810301c29401c15080c0350750028a01845401c070304c1000e0602d03100e04207240a8400e9107c001c0c0b0504051000d003081c1c0120b1005c40f1301840d094501003101c6034a07076102055038407068940d0307581540207000358000640c1580191030140c1031417410710144458000810442c0b0301c00c04007221078544550050200e07640e5000e00746520541c1c02c0c002d002c1410580c8425480308000900074190300700009016000e0b074029140200244400040556116907400c802001848811401c4001404a00034000c080f480b80122a00450006101d801220314100b81038034032401400e4211038892480761110040d64110304440002c0110440c17a6400403603075603220680030940d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 450356106 1250 450354856 450354869
    0x3060702070501020c0904020a0f0303090e0a09170d0e030a0c050c1905280303030b030613020609120c21060108030a0527030604030e04230a0b0111010207050303010f 73
    0x401d0400c0103a0f030018404034800802e8401000540340d40c00411583c4109410150403031402c00400020103a000c4600e60440300115884840e60b01c40406d40d600b580c005034009070810b0025503c2d03054034046000200521719092500103039032034050b070340c10b8110b030081110314000c03409c000014405d114084c4140140200105c940c950300e4032214415055018031405154003d6100401800c03040c10340200881907400301d02001a10f490341c9142c0200034001c4490a18000d020b03020115401844a0b03402c1c02000d41d00616050038289180144612070621000e222000e12901a60781c40c0c5450360b0b035410321302c42036004507021450701945809180a4040c5d0210096a1041000421160307120091b00e07032000c0b00f03200f0029102c2034a04c413055030f0b0911800b080e41c140181410b200826810010880800a080d81c00788400c5042201c000c1201d1014010403000a010ba0005401c0403225440800521070505020054507040000302c0d007245c104180c1103e2a620000051000202482000d0000c021 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 450357356 1250 450356106 450356113
    0x140903011a21120702010507201804020f1c0605040f020109060f0c02010c170a120513050a06180b01030c0609050402030105010c060504030e060705030301030c080609330f0603060702 80
    0x1d044000c583c0e035a0080c00114100900811100c04680c070500407030740032680007450000c2c1d1541c0c0c4003402c03190760003108040344110a010000340c03415280d8444144a80d400520340c00e2803200c0c050500800080f002c202d503c140e0310000414000542031720070a40201d001e49109504d8640502c000340070042290080c034107020030380c02c0c03001a00354000e441404065080c6032426101c80c20307142c4000d00d0720582800f080c01440215001e070034994891060a900002180b00740081d403552240540d540a03c0303100075240d41c00c0050710702c004c13400d190000c9580d2412900300b071070480c200c0c0e107404107074410a030812130301d045004108001c4582d000d910100178020840b41145194501070000e030007031040d4000280003a44520020f0103050181c41c0000710454003034005503480c40940344c0140c40364402d001c12103004041810119040d000018a0742c80b03510401d00420f01c100d4080020f01049030600c0709200001040e11007060602c050b0b000003400f92104a08001d81c074100700c0105420300340003c011108550 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 450358606 1250 450357356 450357409
    0xc0312020f0c150f040f062c070e011505250b0a0c0305010e040b04170f0d0e07030809120f100203090c030a02030d030b01090312090812040f06140903011a 68
    0x1141a528507003050340120805500036081c9405005800d0034182500d07c1d0200005000240c400001d40c0a4103910780d5080d2149c841e1103222002ca00c10b020700504008080040742003060703500400003061405a0004503810710303c03d4904420740d825880d0f80440341c1d2402d00040c060406218002c03440041d856081c180a42d40c1090b03043c0f00041c030020009400340b1012000b003024064002902c000052a0891180ea600b40001c2c42c12a5640300c80300c14901700380b62100000d2303840710224807602541d07030001ca090714108800c020081d140e402034680c20340c140200b0368021840b0704204045018162030300c074056102d28001846d00c1c1044540d80d4614040d400c0480380070010780e0040f031b408500c0c1c651800c00054580141c80103c03040017103a0801840718070520341103002103801001010445542008030381440d82c07070b051203140c507015078860b10500c44c03074011091040e50b000e07110342810503000c01d20041c103058032000040e0070349100900304000d458254010041c02c1c100510011121804500e4140600 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 450359712 1106 450358606 450358621
    0x501060809121801211401090b1002060403052a0318120c0103021e130305210d0b0a051207060f0e01050a0c0312020f0c15 54
    0x103200c1d4a111401c500c000204486072021400f00f4083d120110400548011030744480d0b10700b8420300c1200f0350703920030214442d003080090300340f900e0300644d49050f0020f0102c4030200c1e4050300032030403804c00c64917080d00010a541c0250389481d0466a070004818500c441d203008503011a2010001c0501e0181054000302401e20700034405240380c1107220074000c0010340380b8240c41004031500f02d001281040d40c025805041003a49008040300702e5003c40060f005036038070404810131070b5444408240140801013254483c20800c0c1c1000d1002c41c10031103482c69031030240d5002202c15945642c00104d060303e400003500010840548104000c0f070f10000540e441e19183d00604001483c0980c0000b42c1030700c1400070b10259903045e11664a0644c00c00c5049440c908500740c00d8040c802080d5411513441000d100811841d01c0d0808102d8441d520601c10508040c3c0090119820301d98079400e210304c9 = true := by decide +kernel

theorem cover : BRFrame.Cov 450179856 450359712 := by
  have h0 := BRFrame.cov_init 450179856
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450179856 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 450179856 ≤ n) (h2 : n < 450359712) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
