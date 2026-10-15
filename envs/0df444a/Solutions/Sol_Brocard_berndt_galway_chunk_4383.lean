-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4383
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:26:48.101387+00:00
-- url     : https://prove2.me/submissions/4adbd21e-8d75-4c2d-bd7a-058c07e5a23e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 788129496 ≤ n < 788309352 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 788130746 1250 788129496 788129533
    0x20f040503011514131404080c010b0f09010b070303021207030e1603050c0103020d0b0306071e110d030903050c030309101404230f060a060603060b0301080607140903160e1503 77
    0x801800c00c01140c2498049129511b114044604803200800400c2d8035007191001d10524007080c0083e82c81d1511140c10b180050b1581030140300390140b2000000e05d89003018402d40640f000884804011b00c0c041c100100e014003e0309407410000c01c40e10402103103100c041801509038007107a4000003e0700300440b10b030f001100698481a0b82101d890380b10b11100b850354900f0403009200b81100c0c0d64810b04405182a41e5010003c504088410081d00d400804030009010480c0f5900203454100041d24640920b0240c80e18042c4d60780b05042400b000c4200030740c0f400d001c50346e5031928640c2841007003609031b5400074014021090b540907103000d1103503094810030440e40300b2880c0c0b4040d1550480700f80b8902e07082c40500d0a44125040c1d080c0d1520340c4002c004646d01405802c020b4490104440e0030342d81441900c6030b0741d0790002e0900c0300700180302d1311006015044ca4200c0d41440000340543d80004440e803130000340a5140c2c0b050441860340800000c8411b4240c551003407034404000c0181c00c0d06031840000812 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 788131996 1250 788130746 788130769
    0x40c03061e1802190308030613241a040806150a0e13020103050a020f0703031e020a0c05010b060f07080904060b04031a0a0c02030403032a0b1e040b0622020f040503011514 75
    0x2050ac0e81c0e00c00201c001254842c1c0300c1a1301501854402c501c500740058280d00000ca00325443c01c01ca41070100b0302900300e0104406a0150740e080000545424520004402b01d010380d01042d14140d030141844600360040c403030004c1c40b038001c2e01c00f03010a0b110021264124410002039141c0c180051042e0700c0001d10940241100310000420b40e003202150f0b4140b04100d9001d00c1d422004550301300c5c41c8100f0040203000d03040e40c2100841d081c504100d10b0050b00180d80c403586500402aa00014660039242e49030b0740950003801907a2841500e40e620392070100d4001e0a20350411349460000000034556843e50b005040d82124141e010303504152a50b5002d55280518110034008030a44090140f09002e164806080079401804130183e0390400b00000c048605100030042d00d50f0400f40d04110114000303000030798110f00243ca90325559003000c41030b00c402c031454200d81030095000082c055144103e41028200b0350318200c0081002410701c1030004c48510180c452030000c400856070802981c90860381104 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 788133246 1250 788131996 788132029
    0x4110409060509010b1201050402060922050112060509010b061c270c060c02012c180601030e030301050a09051b0d0501090c08040c03061e18021903080306 68
    0x592100309075104001d5850449100445a540305000001c61600148110202041700c000300403504254011400c544a2901802c0c090510014041580d800c1d504043c152001c5401041180e1758684400302c00c601041401912050700b0480072584840d010320031030724031920003880140703007614004a000001c0019805603e1071550b944410241c94903220b4140d42d01055480400c0c9030510600e810340400035207410150030005409407210050341c00c00c8101c03c6149005090b6146003c000c00c0c0403e00e0701c01c19159640000200c8084807003496404581d6001e05802d0302c0c10300400c411000d14035640d006c01d2052036031100302100c08012039081c07036004079000702c007810000c00280d404d02407860b00c5d940300f6240c4045561b500c00040240010f2803090406035951840c180d015402c06843e140c10001c81800040c06040e80d6001701c880103012052032076124114076105006071104140c1e2040f01b2007020383d0981c060600c0c0c00700e03034080c0341c00d10b000c0605403640816210b08585400d028040e075200420070a4 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 788134496 1250 788133246 788133251
    0x16060b01030f0911030d02030301060503041509020d230f0a12110d0203040f1a122d0412050705100905070306020414041512030c060212190506030d08041104 69
    0xb80b804510b500540411034020780f1200c00c044100070500d8a030900754880581150400d00040c0a655072203400c81303400c01d42000065441692154401005000406009610804455007841040f6004a8160b820081000911a444460700c007050b210215510700803034581104d02c0c0d04000034404040c28088260034908502a010249000ca00d840703482600c4c14056400483d040180068400000c1c1c044c188410030b000904212400b00d0030f144c0030300440036400300c2e19200003418400000542140c1001103103600c8820038103008105007a00d8080e541a981d0118004100c00080c4c0103400703d13a28a60700c4002400e2400350340070240002c1c5880c0304111030501984070b00102140245c009880600300c0752860401c1031106204000890302e0800809800712410002040102104000f0001c120340504154207426610f2806d0030091056044c69481c1c406081309000a000a043e1181d55140b080c9408012070303110407082580c3c5003e83c01807031000519081c0054001210382495903084240a4000b = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 788135746 1250 788134496 788134511
    0x70e06091507050a020402120a0501050d030903080a11100f0e0307034a0f090601050d020d06030f2a050d1e051c0210061a0c0a1a0406050c16060b0103 66
    0x80903a84008c0a04081466100501c800c60b5034a100d10340c01802e040303c41100e022407130340d1302508040c094400500820408255068003d020301603200d610b13024101a0f58003140d03809071070b00c000c0c01c910001c0101c0c0d505c2c0900505800c1e0300001250041d54141e203459071003200280301d1031742e1800d440c81c1c42061382d904850940403054000c3c1251461112100311070f2841c80ba540244205040c402d14103a1140301d03041c080c00550b90308502241e041d1000e4a0003d80c1d9038040e1036056001d412150710007030050300c804014905010500c411030421045007417440c085071400080c2c1c02d48944003805002c0d8000e0500c030320303200007071144d40300d01115041044440390704900c0d540b107150a10304000040908007881c01ca900d022540d0510034114000d00c002c100b00b01c42814000402003195086031962070100300060714000a032000c0007001e038507503441061081044070040301200031001c1590308072480d50030103010070b40013603541007078608003004034000402281d000c0d21107001400541c48100d0516544844 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 788136996 1250 788135746 788135749
    0x2090310060909061107030c02040b0d0f05010e0601230904171306110111041203140304030905030c0d03022116210c170706061706070e06091507050a02 67
    0x1d1040100800c02c0000f03595055801c000d1300340c0d00c0c0f4885001c1040f00402c81e040c0000e411082549405030143e40c00506100c10502081c2986c8241c0800b1700001e0f03200e050202000070540086102c1c0703140350142e41c004e90340c0b00c6002040002c856800d12001c54a00300112450030100c1d07905512170b00455404c20f0740f10355013440d03450310303330020500003450070b000a0240600764100d1110000840c00358001c21181d9042d11041c00c250045004018400454030982d4040c107120b845407a104030009500c041d0384c0d003024600542484c502e8801c0f5802030046a00001a5292410720003850350b0b0141c0207403070300e0030f010808482116071202101505050a01200c00708019584140902d248103203420f10340c0701943c0340c05903400005814140100301d04510281c1c005180414842ca00c42890010a515581c41d49000c602070a41074001741d1940c0c0020446001325400000d001d03000e80500d44400030451f0402c014051648200d48195401c11031100c0c0d0f01d002119000c000303111050289080e900c05000769030 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 788138246 1250 788136996 788137001
    0x40b18011d0331050d05030c061e10030308041b0314030d0510080c0d03030b10081f2103090302120303061f1403060402070506010305031b070807030602090310 70
    0x800c032500c10303400441d94820284007403454901062004102c1040c10984a45202c82c070803444c000d6500030010741e226602000300401c00d5451101da0101902c1030340c504808040102040b43d030610042400040100d40700303141e4404580103480e0160364103004d9580741c0d1142030f040e0f40d250620720b2a1001c000c00c00000300d40c141c07000d4a9840b81c1032001e1691000480c0e024802d0320f01c041c01150840040070310800400b04000b17070340e810142d020781e00000e000c0c01c0c0341402e5006200b0440c001e6000480030840c210900e51001c02244141030840f6140c0a40d00a11420150300c1101c2c0a05000390f401c81102404075048424100c0780c0c070b4840c0c40c0c03824151f80c80e83d0219580364124085400594404814405c4503d41400c05150100c00c2c0e602250206200780001001e01d040c81d40004c00c10b000020100c0d085866030b40440355880c0d000801ca800302c0d656850455903980c02035100400c0c400c110717200e88845010118101c000c641b051001068140c0c00c40c0ca68500035800001303e40e030305104200c03000a0064890 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 788139496 1250 788138246 788138291
    0x70b1e0403050310050603090a020d05120c0102030a0e0d08040b06060d1b0f050a05070303150503010513050606010201020c0c13091203020a020c0d0b180709090b100905040b1801 78
    0x2d036207050326030500c0c2e100710403511203d4001c03a101d00d9050040025200c800a0601d101a404843d180640c07001ca09245003006024075000010b05400162002d80400540095001e0300d001401005082c802000e0b81d900d811303e01e00084009203c130b001080107c0c8400a220b0740200c0000c0c8141d00c2d064140c5000012a690303010602c3d900740c100318503810030541005d50341c070010050b81062880e00e009908024142c2c86402d00082c249a40c440c01040f0021090303001170043d100140003080181881e03012550b07405042c460032038a610510340051290352060080c0c0c0c4018040c00c004105680e00203041101c1880f80305201410640c0e200c10102c08118001e8140941c020b090303c0069580d810494000d003440101303590680640c441442c04400200041c129903403081900381d000402c3d0f0348240480d42460000d604c0200d4203030406140c17400784a15004a1030141c0c4024041400b503580c1c40301c0101c25500c2c2101c01500016803200040d9004954001c0f4600b54250744000240f400006c4e512000c400041 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 788140746 1250 788139496 788139503
    0x909090c0e150d1e060c020f0d0912020904050114100608070306180509070906060509041b080103120903020a0f09051f05040b030a0b04030c2006070b1e04 68
    0x108020041100801c101d603801c02403420b10441d51040003004541d0900604000401c070600c10034204001c107291a001d000d00642c420004d000d54151034000940c0e03036441c402c46400600400184c02e04040c06034954000b110b2030341c44404c0d00011181c08001040e20002c0040d21955247e440060040900c88012442480c401c0859400b45003040d2000303122a200904041c00d0610704a41405140701c9641606000e8001c220301090316600d105125003007124590001c50428106400450219000800703408403c005036001c00110311107030000010f081d84e40301e1a402249082c0700500214501020400c9200014142480055a00c1e404100e45c001c855001c41010340c4056014014546180511a0000b510014041001803980524040c4da910361292078030941c3d45901c2110a52800d01c0361016290700428503170740070b151130300300900401002c520407034200a174010441517030200b404142203004405402d4500b41440c0f640c6c0e810f4056800342040081e4109440b200310220b03014500035200c4d520 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 788141996 1250 788140746 788140763
    0xf2c03011512150b0105041208070f060501090b04110703030c0903080a03051e060f121204080303040203070b1e0d0f0e010f0b030c010212030a0204120507180902010c0b07090909 78
    0x201ca06104520419143c1c20040389403c044510020343ea0201c181c4017611003114600c030390030480c0d01c2c00504e2486003980042c1a0002a6041c50900c0301651049049030326126081c8000f04440080004403031501004070481c41c410301100c4003082c442c1e803204c0b1120000b0b05102d240e564a036182d09419402201c82800020386510420501c0c03c0407025041d42580c21109405031400d0100001e03000c03443d40c014082c064000b0b00340344030302400100107100000c550241d6140e03980c1d0302d945169850341e00888040e8001d2042000015489180e0011280744100350340800013114112410b809166012540100e51503480c0c9011020882c554407400a215000f4000060411080100501510806441c003480783c0c106d0b030070f00095a43c011a016035260700c8400410f60302c2d51844d00640c0280034a4100a061040c042800d43c201b00300010701c0400d031205000c400000c002003080c000c00741c503d0900001e00180f6540154000110300c4160940c2000007410071021146e02c0f0200641100d040000540b078400 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 788143246 1250 788141996 788142029
    0xa090b1c0803090d05190309020112150815011a0304030c1e0b060f0f060f0c0d05070506090118062f120f01050d0201050d0603080313030f2c030115 65
    0x88003001202c20713400180c1811800c00c0c1e81d8182c0c480510088016a4040c10f46840148045a10402802072450814101040300c4860b8048070366401c0c1c0c96005031030701449049000191041924189412520740c03941944a084070001c4405103a000a0001c50a100002e5103ca0025086003083c2103c02040c0c00f081c42c5008850911a00c0c8030009404a0f000d02d003102103c03049e5071100c1c0182a040031042d00c081342d8a00c84000d009483c1d03c01d50954003050302821244082c1c0c40d41c420000c05415004404840a54a80d80da1580c02c0f00c161034046140c6002c1c0168403000100035800c5030303c4a44880d4840c6086800c003200c030766140600e500d0b48601c140700000307507050400c40030300100340c110710100d411003000d40c1000c01181c0c04a20800c000f905000d4007103140604110b2640000c0041c6a0042c000340c0c41e81400e4107044c080c040502c104801041d034820b4003141d094805c1195050503102c81c03560181c4001484c13500c9119012915105406548a40c45003005101c21002c2030018a241000700300c041 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 788144496 1250 788143246 788143261
    0x81b030f06011719320c06090f040f050712050709050d03020307140d0207091503240905010b0a1202030d05131a090301050108160b031815040308060d020a090b1c0803 73
    0x103401408135a00801c42800e1303014030440d000507106488940654102e541c8c1e80154000400c05003810a806501c18103080079070301a500190405806841c15480304826140c40001000a4910403500c10740041c0d1107000410151030590f01003190300c3d009005492405040b0384034100074101a04260115501890455418550400c540e9008003a1254100000c1a0b000c1d001c06080c4103a1001818005909039074600d042142407a80d401e0401a04040244000c146400c9002e4216a4005807049200440014440351300444060304194010064004503000b05d900f0b941c250030481580c20180c940c000c011600410203041c030700860741646425626a91040209070a45405802c05000b50b0000c3d90380c0415540030b490207030103032064500143d40b00d0b520801d0040c01001c11060081191184500350054240c09981141c015402032340c0307099603555a2020701c42d640400000083d00107000ca88100600f0a00ba071050700100002810741d440300c5102011640080240482542c86000000500910 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 788145746 1250 788144496 788144543
    0x2907090807060c0b011a12100f1205030306090a020d0c0203070203120c030703050c0109060618060b0406050a05030907030c06120f0b0a0909020d0b01081b030f06011719 74
    0x1056280742032400242d0f1139560400e640c1040c41040390f801158000115000010400d07104000f4404d01920060310b032815000d084c034491446200001000b100002c1115086080d04c0c0740c03101e401100030f42c41c6440700740501400c19401880c00d04010f43c28004201d51180b98003640000c0040703035004544950490040500301588010510b290344030400c403100003144040300340d50140e13405042007615030110480c030074050842000001d20140c61f00b040031540700005035442d600c941d600d560400030035440d0704684140f80304600070040490014000312074150f10030030003103a02c11161015500d0055982c1e0307440080d00c100d50440004950034004c0903510407003900c200310151400f40b0040c82840705481c042481c107000e171700034001005c1c0c07101c03400001e5444801c42c820100d80c0c04418209690307500c006490b115681c0002200c000400e9036201c1e0703024a000a002c10414541e0380141038140d1808403a40b00c1c0001401403410240103031b064082d50800403c2880035002d0007845190404041c11403000381 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 788146996 1250 788145746 788145749
    0x90803190e01020901020d050309120f19090602031c020408060411010f0801030f080304050f070311190506090402070213092003061003060e1006080a1b030b042907090807 75
    0x100e83c818008100e09a03030028588405500a091260b41e13912848400e0b0300782222210701e121b01103000070720b40ba0820300c0c41000780300341c91501e0320f00c00c800c04948008845103e018400d10700103900c140310032811004940281d021200c480f9000520b030903030b030300d454606000045600b40d0f44004411400100c3d540c2001100c4400010751908404941c150354900e0b2000710103103405403603170f58044002000c0040c01c20002c80043c100b80101d80034940e41385002c1e00505488449140243d01c6440b0031100ca650614004042d01c1d03005100c1c0f810800c00743c090000942040905907806001d40401c07481d9024039104100304240105a01c1605114403030b2881c00340d141200c041c0d0b000358010810030034038148841a48050f00d40c4171601007900e5040102482c508050700d4840ea00c094a00f1030f00141f01100015803458081c860a409200318440002003c1c005074544030207855400083c00140006074000d824a0b406c060841110151078040140029448002c0324450049082e4080c1403080d04000c01c001310 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 788148246 1250 788146996 788147021
    0x80f06061b06040b370207151a030d030c200a0c09020d0c05090306130212100603150903020d0e0303040b0f030411090c0d1a0301022205010f0815010309080319 70
    0x5281142820030380f02c83d105e913803d6009400350f01050315020810729000740d00c20003c094070288625498540c0e60070310781c40b290300868801c5c805e0403100321a250182c081c0301059040341c0c607524110f4505148012292100103a20480b40c094059150000380d08100740341c000c0d2440d941c0042e21500c50005200c01c4842d1141e491040c04400d01154a00796000510503920858002645a4080b160301c04503d03040e0000079200c007680107145490200303840680c442c1046900034101511482120700c01700c3c0031a004500e001d001604921080c00140780034644c9010355120240803139190135030382c4680e0303103040d0041c80c0c801a02200020034071040c0241d15008400c2c00c08201c1c5c415400c0c0c182220404040d00c01c048100000d60785440010304031210702100c0d5524400044c00a40d55400b10840080420140b1880c030095014529008209948101120f0641c40c049032580d20b0306484000448605140714084030381016211501040001c001d40081c600988907401050701c0d010032880100c0c265480000c014 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 788149496 1250 788148246 788148301
    0xf0d170a1b02090711070308031504180308010302280308040314070501120b040e03030a09050d0e0108041104020702100207061b02210a0c06020d0e01080f06061b06040b 74
    0x7030141ea211041c1030f410480343e0030141029464070341c40b1403d044055001419030030000c0b040000403403071812014000d51341140d080000034030f00c554880020303078403000c007030300160302030006100500b00805149030f424400745608110442c0080c9980c0c000341d007a04100c802070f1000c181007003001381e04d0039400000c241c8507000d40b1000c2e0902000808076490711203200d1030213803035820105490310303140c0c000000443c4140a4a6580ca0145e000c071019286d40700c0c1c221101d10032054072681d100d125146401e02104165070300d074000d0f15140c0350707046d41c00124141940e01039400c101c80760042c1e039115041701d0081d519070060f188151400001910541d60305200c5c0386030604094000006030344103500e03448014082d1082030303a222000c0e4085458800f0303030f1344020100c001e9404d000c0360090700001d11225007404d9503034200d0f0304900c0c480119030940c02a10b1480e0404145008109036141410180a80301c2c0e500d008000f000e00b07130011603440c1c948241d0302900c0c048010301c1440215114205607400d0403ca00822 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 788150746 1250 788149496 788149547
    0x15090321082505130e151c080306131e2009030c0603150a03050a0203011b080609150a090f0605061c11090a15110f0c0f0d170a 56
    0x50b0850305800c1d0b0100c01c00c1000028aa00c00705880800c03650151030007516450103450241a0002d00c02401c0044921585146000c121125117404028001960201146040d07468103801d0010440400e04600026038407011034070001c403c2070425166008912101040e6a0465030414981400841c4803071005c4600300300307080c0940c90000ea8082940300070303a8a0b41da2951401848075041d1031110402e5403080034200d0010a1001c0044c00640e000e0007200204a9800c45c032907001c512811401d002004604500d000603c245001004241c2c81842c03010a50b4081101800060100c038060f00010301081d81c810070030881461030b1080c3d8015010981d6207610701128002c1822242a04020310921117031540c1302448460344c0d40064a12000b400f501260103242c035a00b090000d00e000c0380320038000506001c6072541e10b00c8000340003414081e426010b0240c52500c502070140310180741280582015962030384000088000030500040081800311b2515400c02e042c0061010a122a1a900c0b00160564 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 788151996 1250 788150746 788150791
    0x304031d061c060b07141501140607060e060c0c0613030c12091e0608100f05040e010e0303010807030c1e06080711010c030501090e060c03011509032108 67
    0x84800c003165a0140c104003410a0b41c0c004054081a00300c01600c48020074040700700082550600d4001e80c058040d10140c000c0000c0d0503030120740034440e40506a05a081c00c180c2828848000c0c50028042c10010802460360000c0034a0020192410070400100003035418220500b4000d0a41042103181d08400e10001c0c0d072401840604c03c1d4a01a10f06803108280c004901c2c001c0b103c480040203024140178054031039071450070781e0158911511002c20700400000314600c4040401d0b8080d50240c0c030f80034907410b08103400e000080c6124000145150350311008011000802c1000e18000d040740c40090908600b546805207410105070f010341100340b4030307500c00c0520002095500b002d6403860302d1315019581d58040c040f02c56141202c1b81d0440d07546400e01c80d00c0c505a0640042d41038a800d81070500c4413400c103084040e07845104071403c07055100f0030f20041c42aa42e4040d41c944404141e894050344c0c65807070b9141c290043d10b1075410140050f44010344000081d03041141d0035880644014024000b600324030303 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 788153246 1250 788151996 788152009
    0x521190c110918060109140c03070f05090609041805120a020d0f0504030f120801060e01050403020f060f0f030103023d0306090f020d11090102190c17030304031d 71
    0x4200c0761207a00500005491400342c1c00b81c3d10f4900660344111089541d550398041c00409104000c0c2c68104614000036000d12100001c60340115091b030756481d0091a0510201d81c5038100507186075000104020700d821594807806a0590580c1c0000200319000140c903150349055003005140c1c840030790501c403141e2840c1c2c003c21070285998090070a4420701c2c0761a007080b00c41c0e00c501c6c0c000500d81305601d040d14040c000c0100d900300d80141152074074151070b41c03120400c0d40c0e142e41e40d503030745070014808000500050a10640442c106203001d864a4140105009907009a40001c40060703140d080103c010000c0d803a010701381040c801030700010b02e00c3c55158036502c40c1418650300342d041130112014103035001061080d03208034020712404500704a020001410310b0040d5008803004c001c1d00341080000b04001c2d6a80b13045030301c0210705130024028140301d0026034000802c048030030b5400d00e020141c00688100c8070705034246058100d5014580d0303407400385005000d078010076484501c0032501910b070000540b40c51 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 788154496 1250 788153246 788153273
    0x1703090321030a02070519030e0f01080615090a05061b12070c050108250c0201122705070e07050405040e0a02100c05011b0503040c090c050304020d0521190c 69
    0x2150f000da030b609142d04103546440305509003103110400d16004001415030081961450003400c07101009050100c100454600303005480160740461b00c1594500c0d01d240c88001803000c1c0c1805042c80b0b0b406640c840001d4841c3c0c000120203a2001000300542d20100c00620105030304411414001d1304008542d1079502c104425802118184901a00420705a80b40884000040600ce1110085035007841000500c200c80c07039070b400ca002c034a5250a41b107a8880f940070f10090050010580d10381d007190b14101d108051960300781074a0b1030050300008a290b01d851049180720340c43c2616a00d980300e00e000203000455072042c10b4590960055000240140c1d18035078899968007051074020364500541c1801c6004011480d000ca440341d510a40c1c241c680c0d904407003d184964016106d03095050b41d500909001c2d035400514190014604000040040c94402c40c010b4603607018000f190800110f5400e07c0034030701e580c2c2c0341c041d101c60f00210b45082400c240740e441c0081c1c0026840c060705560304903a50300f051214007 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 788155746 1250 788154496 788154511
    0x180b0309010b0d061d01090503070605060118060f0905030109022821020405070f02060c0307050c01051504060f050a14060903070902030a0b1f080a06170309032103 72
    0x41030514009420a6441c5200100b00f061402081c1c601400246501110403082102c4002c11404051045c86000030040d00704025507d0100981d617050001c10b00205030b24103112079480709a00c4e10784080705510140056071034440508801d944050081b106d10b078040c0c1c0c0b00343c1c10305000000584400c3c00400d0b000b401880380c10041600340350841c0e8040c015030050000b50b1003d05040c0f02d005190902d802c2d203680282ca081203d034607642d100f1200008060856800b60b400341d004507038100084001107038000b0841c03516a08018444102c5801d6a1040d980001c04002c0010b526401e858284143c4008003422100b1300311162034100841d010f6490752042c4ea10ad16202440030b0184d07259401141c2d0110030003010349d08000d4882004000075001501c00e04038052030007500051314107090f004180c003a03180f0b0044040c3d05280341e100f100c1100005104c82d410310349804000130a0102a5801041007100c0809542c5550034041071600e8041e581c6204001c100d901e1215030b640c1d004820031203802940 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 788156996 1250 788155746 788155769
    0x60911030624041e030b0a092001051b0f0d08011401031e0c0c030905040b0d060e0f06181b0a1503200301080d080411060a1b06050702070618 62
    0x1100756101290f0300440d032141c48090300602e02c00d28214140704450080c5d0b481112540c03420b480d0164080f0031541000402803000380000c1c080780313142d64852a010005981490010314003210411081d0119140c4914003e951b44000d89028a0400502102148034410301d0001c01ca9031404022039110840386100c2410300d0741d00d801ca01507544006034048014004e420080c0304103044000001c0c82e000c41c4100a0740001d04041000c2840e00d042c0c05000500307040180130f05803241e040d072034034802054604003045983c460324607840b00600302442960f108001602d91005041c442010311428018042109166903200d010f18a25580d12145c0104c00c1d180280003080d4148140d404c2034008200e0709840800151661036421030952142e1b0045042e01c280c02c081d07400e03044002c03106641c1f0200c140c0b002040405a940e0003405030900002501c0e50740c0c1c0d1031030000c0c40194400b082d00303102c484444080d1503403603c0380100640c0c2c68040240f10018002442c04511001b2450700480107882503000d14070702c0c1c22 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 788158246 1250 788156996 788157049
    0x60904050d0e2107050a0b090907030b0409020406030c05011413030b0c12101a0c0a0b10050a090f0c0906050712050d022703280201020307050d030609110306 69
    0x864a000c3e1601241e0881d01c8408061112402c50b91303101441e11545100d200050f10104443c01210146c1e040d03484081e0119140703445103003040d400740400300300c2680c01503075404c0784002580e1140140e0300214042c0007480b802c00c0c101000108840e2a1002240c0310748020002040c00070481c07000031040b80c3d0059480f6904c2d80340ea1929401c00d104016034038089034040300c1400445041d40d490001162034000100121890014010a1601400c1c40c00861384c0c202c41c54640210b000d894003241e22000f501c4c0700e612000d442e040002c0898946810130980281ea40740440b02c222154403403417545201d1420061482490503100900c40d102d0b00400a2aa11110310381050701d40c094004d44440e0703020b1080940d00ca11151003011010503107c88080c6806505c11100740150901049050400e902c2c0000c1a0354080404400c401d0031280c4101241140b104000d0000807071428800c0b84085602c85d60007007a420314203207042041d200102d480c0c02c41100c00b0030901026130b0308c030310890080c000505180c42c4a03d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 788159496 1250 788158246 788158249
    0x611030403080315101119031d011101092607021c0804050a030f150c0516050f0303040b010806010518070f0c050f0312010909080403200a0f030308060904050d0e 71
    0x484c443e210a50410900101c95402903001a07101001e9602c2c0011280310701221110114005e8540c10701501090741c003000c2c1c0010312400160b42c4d41021040c10807040800d043c0c0405421140c610b001070301e0500c6842c1c07180c110368101c04090a8001c6190102c2800c00d0404e400145401c07080d0002e000c140035461000c42c0c1000040400d0300c004090003070401005603504d04100e0091140e03100200c800082040c0c0c140f215151910503182031441c666103050401c80d0081051100f02d01c4000d090301c403171042c00030030810b02000304001c41c8202d00c038024401e01940340c19042c51170140180c0044d407280b9151141405030004c824002030341702c445807400441d43e40458009a503503002d00c84024090780107201d201500c81200100030184040021400503c1340c0ea03840c03520081300d511510090404104220402c007040804802d4440000d0071900c40303100d4103000b00003c840a0407544030034210b03000408104249074105c0b810940c001d8040e11384510314907280d41d4240d12512131002d0b810070b00000c03140b00c0605 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 788160746 1250 788159496 788159521
    0x1e06030a09021801030516030b1902040308191107140402070f0b040b06100309050d050c030d290d02010909020d02040b0d0b0910080d030203130206121006110304030803 74
    0x41c40e402a14642030f8414000e96540c8800d800d00040d1154400d0030203140070018408081c03401c49802c00007030074242d11650030010045d2a80344656100640900010010941e604000d01c01d0100c003030301e18441d40c10b4404001d071000c408844011880e400c031020402c000b0314002e460b204800380485005a4070206440c2c4800751000200000e4140800038040104114583d190a0b01650b4100d0b204004640c2001045054405d50080144190040c2c06008122030042e0064100c40c0310b04c005480c00d00c8035100e40384040742e07a00c06041d00000d2170f1000701001181c0000d0b010322032000946403240303500e03240d030000703032070401c1e10711805042035030014404883d034040341e05440c05030165100340344da00d8040d100480d000e01109842c01c0d126200c440c01003034085805144210450f00000082d01c26030144040175002500002d004000c07502e600d003409801660345100a120a00d00d03007503003102c1c42c1003a09919400b001e4681181061003006281035681140c0082550f003203983c00680c0568954032003403c03810 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 788161996 1250 788160746 788160761
    0x709090f060c030f06050f060910050403120e0a06050f03130302120f0903060601090e07050702030a0c0909061b02070302090907270c021219181508061e06030a 70
    0x41180b8002d02d6100b11a81034009510b140702c402001e04c101a00c4104105101c0f00988107194840c00030000040582070050b014066010503040145c1042d541c1e4881c604000314074200080011100d1001240e14a403942d0740401812803484c0c06c50402c0681c0300300d81c40a00c409809460f280d00013202c228109031007003280d4000f0050704804a521104005800c2c11550020210544a0b01589000071155403080720307050200d40c0e000c1d40c042d21130f40707894105907155407000350217a80500840c141807001c0346c00f51138403000a18080400041004050600000300c42e115820b01410176001701c07800e264a6030014080d01920340448082400d0744801c00001d01c1e0a405034044201d40b0b814854805c14014003848140401043c03a07001d010415240790120386a045001c03602d04c122009000c0e004100301104842605a900d0f41011425460360340b0304002e40c4202503025410a4070200026000c19521105894001100342c40003c941902c04ca05240842945440607009041c04800240704460503081200c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 788163246 1250 788161996 788162003
    0x3050334030e1f021b100c080708040e160201051302032a03010504080a020d1404090b060705060a050912030408030a050709031b0302090612060f15091014010206090709090f 76
    0x70406583e0b200003035201c06240001540844104a00805a082131007000c8980c502c03a60710b400e0710300800e59030810950481c80d001e4a54610170f200c08515100c0e04c40a250280038040d40e030405c285181d42c0c0003420766900a001040c1c0d00081c2c032286005072030001e642c01100030501c502d1078140c0310050305c0082c002c81c5800495415801c00040c4000d112042008242858143d400d4506110903203406844902d02004040c8008401700420000c0c00d80f15442004510b074014030306460190303c4e4417900e00c0c098003903403104140780ea11014016203403000c2098400800400c00c1c1507085203030503112445180801084016143d8a6500245000d44122180e101440e0b20004001070001c844840d00088180c50208038024020500403904519100d1310340e4aa03c100c640040100d51340700c1401401029024140d11040203801c180103002e5520198034500c40c0301141ca860711800d203004010044140c10100b0681990000f41c00e0154043c4045501c01c2a80c20320000800c84200e81e1610020701500f81c2c01c0038 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 788164496 1250 788163246 788163289
    0x32f030c04020d0f1a01030c11060103021e13051f030305030408030402011103120406380102030d0f14181011070804061206050a12230703050334030e 66
    0x40d401214242030300c0e41905c0d0a80c0c04201003d00d400c03055549800089046220342c0c88500100014030f0900141400513440f01a80809044040040380b605c80e80507542010080d1524108140d032507080e0164030000003003100908030140303591405000b501c03000d000a0a810b000000080940e4020200c5007603850100040b65504c0d1710300c2ea044000c00360207480c1229090f0501d004854400402e044402c414507006102c2c25044000c00c10b1802144071a1a81c10b0542c0014060300700700d4101841001c3c2c0d414101c1d074011600160701c100301419620700400d01001e41c200074100e808401000500c41401c00007a03000001c0321840b00182005e60b009064004101510014000c03920990042c0340c080c000703004045c10300246803103004208916001e400f07040000840d16800102148410700242104140c02481d100003150000519082c00d02940081c3e807281d000049174060490000103070740b260b000c0c2240100e001da051404030351490f81c20144c003030104210103031680001c0e59459076102000740a003a00 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 788165746 1250 788164496 788164511
    0x1050f1c0b0424050c03010627170c0a0b070b070302040b0307030603050c0904050d1d030d020c0a060318330c021002030c0904020a18032f030c04020d0f 67
    0x52800c0d0304030300c040c0100c110b84450440e110b803d41802050f0080305000801c0e41176a007410821203856010211510041d4180c0381c41e03d002680e0301030301001a102420f001801c42031114003a40ca0441c05d80c1d4002d009614103a020003591000c0d5013039580e0300d6882441e0b10455200c464044000c0e000b107800084658000009004029815520a0302128441c2c8181e81c0622502c608001c44a017045030040c04d281c02406107407040512a910b840150b07a112640032015180360300201c0d14024403414040b0140c2c1c08260340440904d0243c4095005007d00d1030700344074102a1042e0300b030205034280d40c010400c0b614000070b8881e407000000d010381d284880801e242c00081e100385000c0d021389421036280c00035000740003460203241c40600850340b19100fa109402e1811500200340002948010070031010407600102020404d0070401c0e0708070041d4050301c80104100d610401d01961503d00301032003101142608004482c0d520041030510030341e04e00701c5005850318010009180a842c2480100c99074030300c0e0018 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 788166996 1250 788165746 788165753
    0xb0a03170712020c010f0302160f0c1e031101032d1401090b0105090f031203010303080610030c121a0a06020703060c0e0901120f0c08210301050f1c0b04 67
    0xa854190300800300e2002d01040410300381e850300341c0720304910b00040c450111140c20f1030194000300141400c103500b91700c00ca6055150f028582d080741c901154480041103041040807004072050442c00784100c003001c820303440d42d52616460500c000195050503214507154040c8100d040080214404101c0e06a00c0021382038403044c000c120401407802c91401500c0041519a15803045880251040c0c40302882d01143c1020401c42011200c0c03540d505d0b01c9a05000c85038010301e200618001e42c440c0d21803140e94201082000340c9140c242d4075040c10903103000e1180010a034040b00702034a40161200001d682528403500c2080310301014581c58110540441c0007503000d50000d140021a40920020046104180021aa008400e00702c880d0700c01ea0540040c091500071103604c260040c4101d440c918030307290668a041e03141c2c82c01d13032213901d681d00080070644803542070300810701c4d1000c542c0340d00c1440c1d9810540050130101c10205c0b464014400b1003080c4c03c4034010b0403d52080d1a0704100a40014036241c035 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 788168246 1250 788166996 788167043
    0x100506031609090b0a0315110703020304030b07080f0c031504020a050c060a2a02010f090b01170a05030a0c141519050f060d06020d090b0604111801030b0a03 69
    0x540700046568030005083c201c80d00c603003903601c0d0004008140b01840e50303d03600c685200c904d01c4108110f50300c84400102086540c01051118407940107180c0719440e5080c00b0003805401000f00c400d1001c01e00c00c200c0060645602c850b4081c0001e40115201d45400071884903020b0500d800582040c400281980840c0e002409001900068421241c05039580a484419945241801501485929103640015481b00a2184000094030000400d50813030750b159800c0d03400505082d50142d54440040c801844a01c421100009850300203000910207542c0b17982c2d0300c5c8940c00c3c0000c104410300340010100201c1c524481100d0400908484900300608650b01d070910003580c4c2d4040004420101e9108c201d440d0140e94810000141070003050790303402003808a80d00512004171049a402c201410103031003207129101c206030080001400600e8044148012950030400d46c2000200600008513062490030300b80030043c1080c42c000c100705075042d01064100000390001413607054201081140da22050 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 788169496 1250 788168246 788168281
    0x4080631051e010e0642060903101a1008040b1b090411030a050603161e08060a061505042907150e070f0501051b16180b1002031210050603 61
    0xd8005003a50606c0c002c0d20310460760011048040503940c40b075050018505803000c0c4c100c1000140c151811401c040c401c0700110341810840368025803481590b41c00340c0c00c041c100c10034040d840b818084142d0515440e000c0840800a020507c0a44101d02d0f0050b07000260003a40d2000501030428450380b8040600790030303c1e4000f15004001c1d00d1a140c0000c0c007d01c2c000483d0384420302d886d910809840d040406104034600d10300c00c0030514a41c05000003ca9110800010344240141500000c0481c1040032002c0a010240c1885e03041103000e000a01104030340103110a421040401c503c0604050101c0c3d00781240078404024207004103006820748240d909800c050f00d401d80180c2981c40a40e01c580c217000041134135001c1c07103000a0090000b1609449052030100f00b5925107401c0b100d0803031340520000d030b807001c907074021007428502402c1c0000706840303600035117448020031a000b03444051304030f20003980c2e4000c10100341c0e00c080d501d00110f14401c1410007004080c050181006580740741c245044500700028 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 788170746 1250 788169496 788169541
    0x706230a0c1502041710051e011505160303090201020d0e0a05090405010f02070b041a01031a0a090c0b0901110304060203070b070e030105132102030d1104080631051e010e06 76
    0x40000123003d080c17107120005803280a50900080c00e034200080203401080380840103040c070808000010710700109080d0241c0061003a07802149000a51000a0514138200801414006c1c8420640c07000d6171038030020000d1780c500f81e840303a48a940d1410300034050b114000411468905c0028070300180401250008d00ca0384c01044513a9945806840510350070f90244400780c220800764420020042030080480c4d0003c42e010404600060340c0e8031200c19100c0e203a40100740c60200010485000d507000980f8221540351100a5400c0c40e2030240302035200d1040800080a4050200c005180d4601441c0c0303150400e08040e000300043e1900c0c4010702c40c00308103070301d0640da2480d03020040312180700502011668114564080c0d401c0c0a80c0c45891070181c0203030840060030490511000c1030081d400c10085100d40e0090307502c01c00300c0d0000d81e50070380030301c138160312407202e240300b2a03001400300300006520940380802103824910000040b07242401844124040c8540b070044c1c00900115150325030003800480c44 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 788171996 1250 788170746 788170751
    0x3c02090a030c08070602120c3a08091209130b130203070503010303030e06040c0608070224100807151419020607020c03150105041d0706230a0c1502041710 68
    0x1d1007040002130b0181c1c2c4103244e223a50000440142202c2043c0800c031089201d842400200f410900745020001442c180e80c000140503002004014030b0100017052054200200c29440d049480000c510401c550b0108008443d072134040c80b0825031a002c0b400003009245030811501d0f810092070041c405d60080c44182d00181c00c19625611076074000c035940c0e0003964841e1446001601e0150242da038140d004080100750b0003001403c2d41520145c18806110200c0070040f500c45113400c4070741c4404500d00d40c011080e1544900000c1c4812884120012600000307030034051760b052003080c8001e45920a121282030906801c0300c0d0724141e290002940c5000341c1e0a0b4081d81c981c0f0442406165403030010106000d0000c00c04001081070b800c1c16840608903500c02c0400e0361240700008009444c01030141c3c41440000c840c0380c00020110780809000e80903401c000200d40c0703010032000d00202a10719624018209400304200319003030f1070050741140c000f0a0b101210401c4c8441084920340c950300c42d445600800b60 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 788173246 1250 788171996 788172013
    0x606050a05121c0e060703080f072f01021b0a0204050906071b0f05060f010603061d062707030207060608060c0313243c02090a030c08070602 62
    0x980b0080042041006070000d08031100a074201006085140c82800305001e5044d00c400134585410000f46206406510b859500d41450505030020031b00040c9032004120003044d80e229a26024080074000c1e9140d0005584c201500416542c0203100310810442d500310820340d00203c1d104040f4500160078002c45040140e55034440f03565480340070807120800092001000305908500c0400d81c100d026004504410160320541d640d00c2c6040c1c0142c41852031424100300410000e60705004a401919070f80810388480c6a070101d40400400d0050a11880b4140082291400b26410582204100c20301d41401c0340d40e06080e40301400950012805884150030160042002c0b80000348403401944500c1010745542c0c2c50143d8a62005c3d802282140d90000c1044040c01d14010100c001020344100400010381c4030441c044840110549160880c14400c800c5400404400c5428000703040c400d40030f40580d55070601400101d983e580f6070001000540c0e10680410222400a013000960f0300c90780844141c0c6 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 788174496 1250 788173246 788173249
    0xc07091a0a030803060d0f06111210030203060105060c030c010f02041502011b082502011415010c080a030e070b220e13030c0204021207090f050102370606050a05 71
    0x141c0140c000901007443c1040424664100b5440324807460740184c8059001c880c00d80c0d252400d4035a6519003124080020400f2504070422020458004000b440918220b614560100b81c0f110750501c5207911440f000b185041d02d51006100729910194868000c00c20211035141000094006020b03005151100a181a540500500c40c076100c4002c07011140131250346407403084504020062100c154401d03400c030417405110590380d0889400b840c60f000804c48004003842c10340b403504001c0001075131034010b0b036000c0c1150743c1058525001a8000e8165035440001c02802e4018200e000c902e181144030760107000a002e00b0100240c0f03508860190b405080000c0c40442d069004c0c0342c1d0044602d80e100110208540c044c030764000e210414880d0415003010040c9030001412a0440c4120b1401000c42c102085103d83d808003812028008152409003824107000000756511002e1103038045089040040c03040c40b592800303001c076a00c554204004402d0001d450a800545400d00c21203024135003003840450b2030b = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 788175746 1250 788174496 788174509
    0x70e06040c080a09021203070f110d1211030c0d050c1b03030d23010914160f032a02030a121833020a0221030f0403050c07091a 56
    0x1220307031075510203280380c650074441001000100d800b240d200c411b0f040c40070321028003403010b0301d6864080c540080000040d803c2c2555040254812584920f850003000c0c00001d00031101120000a1403800503080a1400c5071a860b511808071640118030075003500c0030303070164080001c0c040002c0038020b5415590500c2181d00002d000c100369250b154000f4480309080f18240c0e400124100c404c0030302070003031844803a541e41c2400001c0c2c002030009a150402da00101c045440182d8200d0183ca0100c0415428000014580c45416002808054480000d420000414a510464410786c41d0410000c3c4041c100041d5807a4448680c001c041568445500d00340c22151149002410704c0840000c608401d5599843c00d002c441d001c403284a0701c99a00c030143d5a0540100484202016280141d5801e00454080d142c900d015160340f80c41c91041c000c00505c09043e03410340ba000403840d142d04915896502d01911240a0650211400e00c82c0351300016141045400c076140d00300854100408d001b1920090161 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 788176996 1250 788175746 788175761
    0x80c1503040c0308031033020607021f020d02040b0a020d0804030203030f0403020f0a0804050f030303010b040312170a020706060509060a031e060905070801050705040e060f040b12070e0604 83
    0x2c0301104042040071510001c0219440340382c1c10164020305844207403013082c0d0001c0b41c48420341441001903101c0701c5001e40c4400a0f4400c4c2c503000034031091174004c00c001d640701d507142c039100744050b941e80c3c3e959505505a01030b1040100146815500c3c0d9860f0040d2203401e03013202c1d007058014842c4c03d00030b9607a24018003850f40241d400d54080c518594810110340380358500a04110210701c1340c0414084406410700613088007070b202e0300380150340f103262070108003009003008480c5d80710ba0030420041100d91401021101181e41c48044d40920380c544840c1a10b210440da03c0404a00d0f4000c82004030800142d801400352512a00003080032903210300622010040c11501c0790f801034040d01c020310205c0c402420030f0155845c61051310b22182031654905082e02c110f5001181d40d42e000440c1404450b0b42801001d41c8101c03a4030b0b1407803c0624020f0280041e81e00504414000d041624203100d141e26980c000c0920008007401c110080d024020301c0d242d8482c900d21036080310003410400b140346c0f4035141c01b8411 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 788178246 1250 788176996 788177003
    0x3050102030402281e0503011d010e0327030a1e0c0605160b09011803090f080115060f0302070b0f0405011407020a06150e010b030a05070311040e0a0b0604080c150304 73
    0x1c45401c003001c4461784c1c0340c079810030380384452403030707000521035800f40504441c00c0347c15010003920a0000042ea400d4031f10341d114805440d04140200c04800c4410001120341d02c08083c1c10128015000c80400e00f0b00b105010083c04004c000142c0000c1c3e042355103000c4519a100d02c0c10b204140d1b549180c100c1d4603000e6000404407245c10f1141e00d1020598420840d80c21901c048000258032044545410320600c040a040340442c0d01402c0412400c41e800707588000610f400002401210144c8a10484001140c010032060042102407880e100c1e11a03419941000c0d0b00458640c11818147c40303408084000310313421a001d44c209845c0211603802d03e04207a001e8416500103207400d00d038a0341d50304050301000d00d8541701031191a40008494810702003042c02030611114003556401c04401341d0058031030040202080c141001515069140740f5801c403800c90700301260350840b0f0780f50307010444050056030b50520707841030010802140001001c145002ca0650403290004d1070501c0d5121500700380030444024 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 788179496 1250 788178246 788178319
    0x9021b0d03180602071b0617010f08030a050c01060e0103030c02040c0c02150706020904150806010806071d24182b020613030f03091d06190b0403050102030402 70
    0x2c81c0003ca02d900940540b502c03c0c03000203051801010203401298860f48844e00003840700314000002469268454090b140035502d004210341080340c840d5480c4503001c103040c208000000c5aa4080c0020b50016010300203420904c615945d6a06004086000c0104240e115070314001401e0b00c0d041c000c0c500c2c0d0842c580d028107444100c06c804001100241c01800301611038503000c000003a0b403540c0f0307485098100488200c2c170846450401d404145082c07016001501240d02c41d509004045810400544040001c1c40743d000b09220540080390702c0803001c42e011500c0f503a00901644489092002602c1c481c81900595085540203c08121071640180500c441d80303030641c60490518000525030a1016001505c044c0c604880c10282c42009011580243c1e814184030591302c0401d540404580c1c018880c600094005100040e500c1281c0341001d050103108030740302c81440d136440c14103009442c01024440801c6032501c0e035a0170701c00e0107507200700c804038810040095561021851032200c901845009681f4 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 788180746 1250 788179496 788179541
    0x31a060111010c021209030c030303190b03070b09090a0b0d0308090f0705062508030c030907090c0f03053d0501030903020303160309020a09020c060c091c080409021b0d03 75
    0x80c0903170b688500c0c10a40c0601422151108541b4100003d6000341c65180c1e00f640c0803c0700c24590700c122101080400e2081d044003004224803000c240683e0001c0c041140d510603da1030b8011020010014010f10503048a4600048014590001d4802e0705c0340d0000710603100080c850103e19a1583d5150048550001052054140c043c98040760560a541d06041541010110340c841e00070320303001103a54007071840c000000c00613079103400d10810006105102050060800c001805844000c0d00e188010401d070f5a40000740d11481c91441c280c000031030341c4e00b11031107450b0440012284444044001d07007041da07203054001500e510034030602407a1a01940036604645904501200d400600e440c035004050322000c404e00540e80320303880c2c6002031044460050391034299000789400c1110003030801c0750b408814454a0925200c0314510701e41c00041f450400040d10b050319000005000d2134003c4107610744089000c040c40621044405209400041140c42c0b03116002070032401d03141040305000921486061 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 788181996 1250 788180746 788180773
    0x105041b030906021e042d090e1c02070e090703022107091404030e1f0e0118151803170a020307021027151404031a060111010c02 57
    0x21103226103100c3c100162500c910101281042900901c0700014103100041c1040890800d2400180300040040c02c222a1035607405c2824061025101d00800c090b01c0d84c41c1c01c484100f05200328419440c03c3e803414075850700401c0c4002d42c4d455084c000c1c003a1518903800441c00034100041d13203a0880c2e9000b4040002c51242c1c00390740e1407083e880b1400c0702e100d11922001080c024040d01030451500c0411014404c0707450f1604005000891212015000b2419282c41420420b03c1008103400900709003440c5e480701d091000100d5043c0d01100b10141d101d101d10002142c542240300314400712030241d44e109118049a5000040c4425051000072301031060700c90081048908000074003a00322840c0140c0b810075071035070040752030500c01340110f5002800c420442c080d841807143c0c01c042480b9814840402c60307800c140c140241004014541024810b48062076405e5960308070444000e99400041002c09141c92910352010040c00c1d5585c0340851006140c1001d90301052188401000442d8000c018080b1b110300c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 788183246 1250 788181996 788182001
    0x1080f190201110f060901020a091e0302040c14040f0807060f3e06010801060b1305040f0603020a030b090c0d02010f081914041109011a030a090b0c120105041b03 71
    0x126540f00c84c0200001402502c2d41070140c42e2142c440c00300050394501c00c44800900c0001c95401408143d03c824041d4066007403500d83c4c84003500d905890000d0b10031070400c4250303500102c1c20401c001c3c0c040b000401040c0140c0795170700ca0040707402441c1150001621400155400d142e94406013000a81e05107007503c900c82c41c00b1404a40c950742c0007129041c59440445094100009002d01810341e0003c0c2c010412601d0901c83d04000340111a409400c1c41881c18042c0c2141080703106943c86603845050b4201882c1051b40140011980288404401c0341e0324070300250310301d008450400d800e006058211165081c0300180000441e4141d490340300070003448000b52050074010380703046003c1c0c030b40c0301e4811a00b040f148a8801001c2d034000401c009840c061a180b504001e05c4d41e44180600c440360010841c604204104518540c40d8001164076943e0b1300c01000007c0c40714281c054440311000050001000b0340350b0060070071070000030402a0302e0381c031030043c002507039907034200790700200c04d034480d0f54040c503110380d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 788184496 1250 788183246 788183267
    0xe0f0406090206070b090d021606050c100c0c0302010c05070f081633020f0912030f040f0612290402070b0411090a2a02030c100501080f190201 63
    0xd120000c0c500c4456004103d094016802c01c8030071000ea4801e200700207408004c8421140c0051004100d054400c9106622866480c81040d041c413a000c11880c0000c01e0902002c8a1200540420002662700c050000d010345030300b81c003d41c0903501c1c00d60002c0c0824031410880e002e05401c00300040d03601c4065a41e8007280d601caa07040c445c14895032600c1c000014541d84103402704080050b05c542c240c500082540c107804600d0303150020450f00c100020030103aa40b20f400d5510583c81101c81700711441007000002d0651142d188a86401036002601154000c04103401100b0344015a68825070140e2100050080b2080209903005222401d114650007001d504140181d0460260000d81030a1413503492080c1d03c10f09580407200f2000c0d2002d0442a0304007140c0c5160b01a980e040244606002c0001c2c50050000d409241c440c601c58208070b010303510303008000f151840d0b200c010884080002e10076041000b84406c2c000e0b1041c500800b021482c04d901c000542c4281e41c8076a1543e10340c1800b10ba4010340300400b54 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 788185746 1250 788184496 788184503
    0x20c121c03090c0e13082214150310030f0201050d0e01020a0f02150609070504050a081c1b1b03150b0f010201290d0f050c1c05060406270305040806100e0f04 69
    0x2000070007e0700312041c0801e84000d0204201007010030b050fa008100b41c00c06908000d4030544c10500804c450032000c000044101c0703030014a507143c1b034001400120f480e13200b8110a9401c1c2810410306840d48041507000748104000c40d038900190241c6890103d89402101070304075886840000450742528000c00050380200940c200b20f4902a5141c021a0071103500e94003003100f40e0000105270501c03c41e142800744071850a031a2005010441e6a40034002c10b40c1b0740e02c05401c61801a06007000f003c3ca1000c00400b45800495161905004211440290003c040c0c0c3d00d0044009081d014087d50050162008185190101e00d139108580b102c0c0102c020140e80419a1001c912807101021a05200640fa03d150103440546680e1802a00340080d031600c1705030f001c0e081c141d07001c600710100d10042102500300f0351181011583c0d121902d0301501c0345100d010248d40e01e0160071070640030582c21100030400c842c90070003640c255544000b100110600303076100e100800321514000600401c070b15014694003521 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 788186996 1250 788185746 788185777
    0x607120f0306091518020301120f02040f1410090623210a03090803030c0703030c020c0306011401020601080d0801180207171c0b01020c121c03090c0e1308 68
    0xa43c0c40281d42601c1100c220407880c0d04c42c005041c03205860060b105070030030318007000551855144c107845001d0803210030300c003411035a006004032046590356000181c405864070703824000c510748007089107511030090307803000d0071b0648001001910b404503003d02001ca500302d180100907110908202d0a1903070a000240b43d01048100f0020544035892070400e190200c0d00b001044804030310300d0b002c5c3c0003003c0c0f5000002143e20071b000b00f1006038220b0044400b8240d2600d004615940040ea081e45040320742c0c3c2110b0341c98000c00c0008a0343d81d980628608425809a0071103072036980e1110302d0340e290541c5608a400184804005005032070382107410b00e6415496810040c94071510381c4400840300700156a880e01408000781440300702e0840910045010108001084003855250010303656018200d20103000395144000c0c8225501c0600030715400b0500c01c41031107100e0036044001002400000c40459641d0104040401d0b0300403a005114802c1090414209900345152104401d40d008070054884550 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 788188246 1250 788186996 788186999
    0x708060d020f030d020c100c0f02060f0706060b19050903120c0a06021c0c020d0207031e05060c0a2d05030c16050a05100b09180c090907140607120f0306 67
    0x12810411001c0240c9075a01810345030b11b00c0400c21000da101c141c1804100201d4084a40200e20100402241c4981c100c8841c0e580e41d1042421040500940f5030151540345404000102c0d252440300402c030400c0c11740418000c81c802000e0039a000d00a000d0ba8039007581c0039030084540001880c001700400402c1c403040b03c503281c0441e62080c00b07036030002482004c82e81c40c500b003030b0500030401e015140610742c10340080c140c079542142009503a0703140c0380b00140a02c0240a1059540a442c1651010160300942910124a0030000c4371901d5400403821070005600300d00407008a101e0401d1a002d022540c0e0b0200d00d011020442c00c40b01a000a03050b45801c407010815282d02c50f10150440908601c01c0c2c01800d640201810440d06140568001100303c80c02c0600884c81951000d019a0303000200d40d104504164043d0303011890b0159040c00e06400caa950402d0011081000407584201c554100f45c100e182c0e40390380c05000310fa0183d0840100041c070f200e4070080c0c00500400d120800206503250005066 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 788189496 1250 788188246 788188249
    0x4110901080106081e1c0e060a031406060307080f192a0915050c0f1603110102150a09020f0a0b070c0b0702150d180b15090708060d020f 60
    0x20280d000c54842d82d503a05042008000034003081190902e0b11020078081c00c1c480f25196284e082030070f03a030020410307000c0b070341000980a804034500482e40502055120490340d40003030000d05181c404a6212005840011014540b140c00c0f20310828640e030321000302d602c0f401d60010401c00081c1803504140c078001000003003031525100721142e0311040a0700003104c002c1c01c01c00c480c20440003441003042001d0700005200303052405420450040c1c5d07600d8550b07a2102121b0300c85041c184525080a414000c10f600480e03500d09108100054a00034a801d90b921501c24005981d2a02c800540a2038250307540005406244144e1100c0140703400034102a2943c4400310000c0c507440320750b0700a0030040704041144818000c0740c21450f4045c0007007101e42d52404005400142d0380c52059000c011f44040d0006000d0303100115500f00004101d01e110554460340070520700041d842c2021500700074810320307103e05405a46403800f42a40645e000f1b40311007410780c41c0e0f40b052161541c0100ea0030b0380c10140150044445 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 788190746 1250 788189496 788189509
    0x60b041203140f03330a140102100c021c020a020a031707020d050d09090b0f0d0c0e090c04050a0209010801090515220b0910090507090506070c0807050406031a0411 72
    0x1c500c00176004122a803070344020890080a4180201032000402058650303032640002c020580c0c600104041e219401d00004030700d00781045200040c00740c20f01c82100415600003400c0554008040c0206008035009641207030350342800748000e90b00989241c0204081000302e070040001e2039420300c0d4a803400f0070907008902d008071803036811603d43d40181e81030440958004000c0003d41034042d81400703145402e00004d1180b00e090308603e0322616101c0c00c02010081300c12898402032010013221192851703c0c100c60380d255440e808000c0d0145050200055164507280b08075210004161600d210903400d0140c01c03401004024201402d0750b0b20206002c2460340c44119118450320900d01e0301a0a501443d4040709942d0307907a0a4a01420780d2000384a9040c06000804c001e8842c040320006180e0b5509804030340e012001e60000b504100001484000d00440241240075100c0803001c8901140e507600134032084070803d10000e018010b02480409040d114811174540080c022000780c0d40d80484a40003c84 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 788191996 1250 788190746 788190751
    0x3021213020a090b0108040803101a09041a01021c050d021c0c020f0318031908030414030c1b0f04020309060106030c0309030801260d0e04060b041203140f03 69
    0x409845100e0100c218030b0040310110142c546080148500590080003070040d40004d000200171800100004c3c000042503900c040080c209411155a018606840502d01c1c0c3d000207101801141008030080c58001c030b07841410450314040e8010101e4140500b600103580540a80440401c4400c101030501034606d4000b4013183da9403484003000040341009003104a8079500d5001056404c0400c107044003400110954030450001d14a0310a803c04410009080111080300c03503400192110342d100900601034003452003640310300c00009140040c00781d030980d24021541c03020140e5000b01e4015180d0034800000300d407480c501401b4040041c1d08075000070260381003226608800d034490401000501e49c1070050b40041c0c1d2050400300802c3e0140e4900601c8402c050181103141c510002001002d400c0740b88114540d1410301013035510010785c00000030500b00e8141c0e00e1a108900b0110301082c0301103910225402c6a0000c0d01010000200d59020784011100710100c1e00c180030103009168141c0101c0000f1071 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 788193246 1250 788191996 788192011
    0x70e0a090515043c020405060d02091009142701060f080c09010801030210020a0213020a0311030c04090c1209050a060c210f0b040f05060306070f0e10030212 69
    0x580b9014001408100d91240c06030398003101511076030604c0380c41e00801a03a8894803800d040c015000348421020064407072580301d203400c9080001c80c580d02c100160301030201800c0448845060101c200c41c211030003407040c05008d00344640b200d0260303114602548054080e29a070010f20044001f400c28642d2561000d034005008905040c01d2280c3c4194400c10081d8890441b82071181401910350000b4074400e014000240180350700700300625814008c2007900e013075603401011000805821105100607412040c0c0920100703003440e154180c0c003000c00c1e00303032881a4800b9100c0ca060501c5c000e0b1030b90140603e50043c1051014041101c502d0005501416140501480c008c00e0242200d207003080440da45080c41c80200911140280795013400c16620002028201030f01080140d07001801c88018145032034000d5200e0700c0e26028030f0b071000141e0001441120200c0a4800c150396015050f0f5103100c54002401c00204000b40c228920315200038405070301c0006250041c24089004c40120300380c10b00351980e4 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 788194496 1250 788193246 788193271
    0x150a1e03091e0c0803120601030c0306050301020d091401060e241c0c210339020a0e0c121e010306020c0d020309060f0f070503122d070e0a0905 63
    0x407018060220581070080013403400840c9004000c5258200706ca6000d06800c0c10945c66101017041d2a1082d001074001e0840280219981c906080405005146d014002c0b02d01050400c0344402000703040c4202ca00702c50042200000d1665004802c400c0005000700130025488088288105901c42050003010704100d010005003e000c642040848640319034000d15003802c50605800041e156085607040f600d07414100242002001441500d9540d6103005000841111200c1c003442025560203141c400d03402902c1100700c1039100c00031080501c07411a05298520010803600100540b00c5440343e600c032038011414411030070210615007a601c402c0e407094503181d402250180040c2c01c00e102926104503140000c504e03101065000c0b40b018007031761040248036000410001200001e1004568170301e5030080a030303070b581c642d4200454060303182521800300a0800d4040700313240c91b03041c20401c01c100e0300040d03020007540d880030003c5031551b4108040c550040ba10349400190220f1310b005190103401d28003d01d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 788195746 1250 788194496 788194553
    0xc0f0a0210060906030f14100507050403020f03010b011e0903020d0f052e1a03121c15030f02012606011103130e06190306020306150a1e0309 62
    0x18405840943c0c0141500302d160041c00c000155500d0440000f00780c0c07102008101044031400641403001c80107a0400043c1070004029160360300400400560303200300e130040e201c02d551074241030880c1d516901c264017248105200e65100311803c04210480d856038a0080c6046849038042000d0503191202140c0340c0b0b6402540404003c400c2c040444050003040100c000c0d0007500b01c0c00380307034142078100c5080c099130341d07242c903034408265100b440e00c034024081c2c1181e0020f0789200691701c03070354080d544400c1400035155a40c004210140a00070991004d020300803001c6042d0b84640f5a00904084c0482c1440544135209038140d64807a1280902c60544a01d102180751420001d0300301c2c00e4180c003000c582e410412040030742c101804840010740300c13402e0800407140d45400c0400c4c1006408040d5808225040000000304811a002075219460a0b10401d2140d0100780d0402540c0c042e0303001c400c0104000d42c940301500040030740000c42005091401003850012070b1120186056140300060000c03411094 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 788196996 1250 788195746 788195773
    0x30a11241909050c0f0301060f0e070809070807050103051005190f06020f060417130902030105030c0a0501080f040c0504020708030109051008150c1213030e0f01050702090c0f0a02 79
    0x107660300325803010901800142e55559420340c44591104a0711300c68050b0700c5c0130207591384096105002030b1980c206040c58540d201da0170351080c101c0132600c6c1000030714204002980d07107101207a070000300c2e450440203199031030601c0010342c09004000c0c0003070001c2c02c80702000a1280d4036103142c102051590442c4403225400c0440708000319805410034001d643c803d0381c2c503501d002c0780003e8640d4401d41011580c1c0440030b851030804c40900c601c00c0c941d80406001000410710b0354103a40154102c0c2c204a0494201350604c1d014011410719900c602e1780880d01d03200c00140344950750b050303282c0d100d48503404000707105880c0c0300000c040360409803065542c041e020005004040c99407143c50b40201003580300f0010790f40b81c010350564650b5000788400740c6003680004240501240c009440e251007401880700745078a8040884000c0094909082d800141e0b030b11003520060820444d0180c0c8500c041e502d20345059055000d07c0310380c48010700307003050340c1200300011540f824a0074007412501809902400000d6245003 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 788198246 1250 788196996 788197021
    0x1b060c0e0301150902070503090603040c060e01020619051801240e040803012d0617071107060c031205090606090f09030a080601050d0903050d0c020609030a1124 71
    0x9080c41d00981c036240c1e00c82a40381048450000b242c0b6119405039076034820f89000c03401c1d40039281905401080c003000348000c01c1000c80a000a841203a503c580040c00494012a075994042e14400858001140c0d03502c9030141b56004540c0c000050000070320811550090b29003194144050140da65200c00c000350700c004c181f01d03008001060740613a12010b80c01c1c0394455014500c010b00c41c01d401c0e07403439410182d025805103808507450200501c4d82140210303030310a0045c0004000c08200304890300b40d41c0006200d035008040c0c0c0b114490f03002c0c0c01003c0042c01c001c0f054810010611056040c40140030001c3c580000c5801540d10030000303003001e01407a0929a040c0b1140300c8016007013040e00d1401e402004002c000c00801d8031003100f03071840c010035161600c0006968500c18200b03100d40031030906011506164005000b13250080e00148100181020550105e03110101a60005141d401c00c212162005215031021f15a500d40340b01541c2c0050100040c4004010701400c10880120300c50082294500803070 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 788199496 1250 788198246 788198267
    0x170408210405071205120d0f0506100804230f0106051c050a030e120f0616050c0604020609060f0c0c040c03091218080a110a0918080a1b060c 62
    0x3000a44181426601c180d1603210501a0795100859a4264000d008081207184610122002110765510a82d50814007030704040200d0304d403581c207000108030503042500180c002c080c4141e854400c25112903540000c0303500049200c0f030b11a001d61401140c0100c040c0100d02c034500d06040005601c0d40384c202880501e203d4540701d070441c04072052801010450100c1c200e900540d0602d044104030200000080302e15000741c00ca0049481812000480d0410001c0c445010340310101c41d43c907441640e080204d40740c0c800d25480c600160001302c089801420150701400b02e000c0e008148600b454105948068507402100600c0440c0d0f11140620742c0c2404c0900c2054480750b01c5281c14010100141c41c2c2600d680855442c24081081d0198608080082e5410402c00b801c0e0391410b8400d40384641c10400030502c40300e07a441303104214403040000c0c40880c0b071140010300580c001c0080384016440d20381040c240c0264000c103081c420400304102401030b200b5084082c42d03201d0030000030351803403040004010b00c502 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 788200746 1250 788199496 788199547
    0xf110c010f140c03013f0501060b0f07020105070807021c111e060d0e01020c0a0c050f0d03140d090f1401050f011e03020a06050903060c0a0f080601170408 68
    0x42c60144402e001000f81201c1c199074402d100d5040e1303c140c050300011a51072035413281d002c150480780c20350052143c0d01002e01540340590024015240c0b034000c9900d0501c01d031505a070100e80c04001e07490055000d00080c0c04514010907150b0308104a0781c001ca500b0f40c000700540c0120190000103502044410010301d240040282e601000710a54070b00c4482120440b8408188214004520a6102070154010b0002c2d115204001d5494440c030403801c596401e1000fa0441d50042da07090045041d00b0030100c48144444000d1034911820207680301a80c0e0942e140c00481b0042104000143d5080300318054841254490b0b02642c00501840c201700c8400d041c011450116a414a01840000c0c3c480c10003950564204c2c240501040d051f288485452240701c0e407000790001c92020000402c6134100c03010f090031440a0741641d05e5952107010824092084001500205801c480b45086540c440c60502ea80944103042400d4280585011000c0c540c01c1200c0c22240c5840c000f40b840c020350044080c1c1d9840001 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 788201996 1250 788200746 788200781
    0x4a01150617010509060f100f09080f03030c160f080d0b0108040209070806041e060f0806071b0804360c021504030201020910021b010504030807060f110c010f 69
    0x3a001c507221880061040600c107007503010100d8295039545810f140140c80041c6181002602c0e031001a0540555a44410108081e10f50009030b40d440032441d1660000700001440c03659941030314210b00750300004c405841d140803040e45c0d00001451200d80b080c640340601172550316600441c1411050f9402502c900781009100024000103031212805035810007803d090010050f0b4440001c100184038889086030100000102028820441d034480b0080d5410300d094411101d03120a58140d881d4010307038100c00003a20803403030120b403424034001c1000d01c140b05104062a2554444419400b803091800607003041900d031150b404030722550500f1071981100204c003440544c4071900c000e900c89a02c0044c0d44040120400042c081510030f6044690f1070b41d004143e10b11280e9001d0000350b6a80c48006e48107186607a02004840b19800344080d02c04507035000b0680d40c606042d550f201c4019002690b0035070031440c1ca4040c400c01d461617400240c00c8101030480000341410300301c46400141c65040d00c4a820005 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 788203246 1250 788201996 788202017
    0x61918060c3005040e2401030b03030c07060804153303141e12090105030a09050f07060815060904020a0e041107050105010e041e050a050a120f034a011506 68
    0x550318006d8a01d865007420001014503281d0042411031150201d00704440c028424042813050300315080900503406855401480d008040b0340100b1642103a420070050001d80c1a42e00800118012a44004807800481d00c00f0743d0b070740d5668a06001c0c107a813018601e504410401001150902c501c0b146c2066000010110344110001c4400b10b4490082d1543c1040800000140c41030a60b80020051550080c1141d000c000403220003034940415014900c00619180f0100309120260f6528803088400286440d1a0030980c000b044001d40c03190351500c050000c00000780a507035036127110b5903807a03003503a80304166521045d19200f800c6450581111120071200010700000c40d050646c001c48060400d1140e1002102c0d60a0981c64903107400341c000c0051040038081701c10001f1125811036950f096489158016400d14020303400c1e11245c80c00451400c118994003160341e2002748600c410015272035074040816a48808403404070345005810b542c16910b51214020302c511074020748008010340d180c8240d449 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 788204496 1250 788203246 788203291
    0x2100503090f070513020714030301141003021312020414090601050a0603141803040801060b07030305061c15020d0f02130f120b15061918060c3005040e 67
    0x3240b016a1152002e940802c0e05401c01c246420850323001e1034010110b03522503a41e02040d0140c000e0701065203005100780102d040056001e0b00945a8a038100a1981c00c0b4508113000010309010041c1c09907801380e01c801e0440f41c507200c01c4900038006c1107140050300c1c566040c10140081120554032003400c0500d001003100720720300d40300946074000101548101c0f9000c0b081060b50710b035002d030340c22050441d46011070000e00c1c0009100180203991080d10140800e94401040000e070003001804118080d007103000ea240002c07040e1203811700d55070140ca0014100083e8100f1142164041000b4649039a130004103940c1802480e050340001f84082d105080d46c0908003200085008580040100070751900404564103404000102d0200500500703140d403165074a0349644400b00a403a81c40d00404c0311404002d80d03000300405144244c54641e203400301d80484c1503591140c1c4a00f801018404c194215041d5140743c40e40e01e005440d404410780d5900d85460030520840303a101409000380214540f04802403905 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 788205746 1250 788204496 788204509
    0x5061002031e07031709030904150308030a090c1a130807080d1b020d030804110103020a020c010e031213090b030c1513050604080106090e0a0c1505040302100503090f0705 75
    0x14002ea10040d4072604149020744a00140c1c02d4039002541c6000108181c500c0e0010151103403843c21501840a48400121840c41021a00015245000c2000011550140c0360400c0801307a100d80d405409030b65607a80f2061510481002d11107240c000010001d803a801c8021204014101000140094600c1e040d56669620015a00c41003441051556048074170340d103030009518280c01602d003055402032071400500b00d6400300d50440d0345041c1207000000ba9482403003964503211081c6c0040244100e25001900e48200ca0800da941c18410940000c0c80e00c00040f010781652149160080405814034884006560f009900b0314000d1707004042421030303662a400801d85003000c13001102d907500c00800101204100c550002500001c000400092074001584040100c0d40c0c1400100113080f01341c428103031030341d0f003406001c1c000d0f4040200500c464039070b414541254804030b050940c034181d0b0741c0e40883c41004900a404003c00c1001c410441e0006040c020010420300d92005000401d04080c0058030 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 788206996 1250 788205746 788205787
    0x30e0c0f1908010c050403030f09061b02130f0b120c01021e03090a170129042a03090201110610090b03030f0c031305010809060106030c031e0506100203 67
    0x706101400724000c1910480c00c5440103840110300038000c41d5682074001c0d100d0f45c8544407c500264494103902e00c881d1007440304409a60f440c0d6203052905100110525081c01c0420301681c0c4003050410710901600cac46d2040000860011901013003419003503080090000041b0b1381920305030007201020300c85a80c08503406404d5070008250344804000541d1a610310f000741d01206070401c0d0400000305004c61040e01c02502071031000000d1010004208940c4c00c0204203ca01444141d00d4800381542441c040c1c2080d0302d500c1e450f9208405801145510f0041003241c0000100400e1303480803000190759001c4a442401c054040047c0f24900340071841001c0e6070028400c0c410711607030706e48941d107a03030ba4140300f22500051070103011515061540c031035a450740c2c04500f00c001c0d19105041c0004503940600e407001e10521481c005405581c5c0780650030f88c09010594484c05c2015515940d001c02031140354210f202011650000150074a401028040705465100480303055600902000031139618141480d103 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 788208246 1250 788206996 788206999
    0x60515030a09030c140a20030604021c122705130e010626010c02010504120f090b070f02011106101205150903031b25150f020406030e0c0f 61
    0x5203220035040071036800018003402003110180c0314080103450030006116464500800040380320303009500781404010b11045e1f4145e01500007400040c0540742850001d05d011184510500c010103240c1d0b00c1e8490009109038500c045260130090f5100e40803100c0900302400a12540d080d5100e0034200028501120303c040411400e07118494111112030070b400480041c5a40740024280404040c40c1290f0700980c141700444542ca0850050000c1d481400707010300868004c0e40149010b20452001c4680c8405072032103200b400200c0f44001000b1640c07400074000070f030040030340c800a828140300040c0003854a00c050000d550080041c0718850b014880b03610101c4d5400b4024601c4202c182c0b40507410608005180e902034034811003008440c0c0000b1005510551400d4041d60020070130204446040c0110f40e2035400c01c1c2e10307900c0903486401c00340e04001100f60040c000002901150f48041040e5140406042c0e030180d0003150030081c890b0036002d0315040701e0388540038000800010f008901010307800c46c2880d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 788209496 1250 788208246 788208251
    0x40f03020405040f05030d0b040e06040317100e07030f0e06010f12060e01110702100809100e0c030a03020c15030435040801050f1303080109020c0f011806060515030a 73
    0x3e0801c440c2c44100005103900030140e94a4144252144000b048041900c0c0c2c05103061040030401d5003004900c16110390b5240e101c00701c028024580300d021040006020010b800e644d00c40124150b68107107001442400e03196008201541d40c00d43c21030a844030922607215960280380144586010114148240e64031015011002231785420000041c0005401c044020751811018880e40c1a07204010071589000303032102c07061254950030485005800311406801500001c144400080311604805924080e08048820b03421203080028185039003241b040340541d010f46100c0340c2904003c0f114000c040486c3c125a030840c60191078203600705140194011101240b88100c44490742980c00c0c110580b001d07024101c0e240c91312600c1190080c00191000740715070b0221000103002820341c149441d003541d8155203180c1964600398041e0040c4d040000c550030302c0c0c0607440284001030341c240304070b404182009904d003002c403865040442c2294079540010f4007511448e04054561030f44030701103a8100d5620f0000 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 788210746 1250 788209496 788209501
    0x50a02100e090402010f0c0c170c03150f070c0210020a0b01060309211809090201020c0405090d08061c2102011503171201090b18060307061407080c0a060b06040f03020405 75
    0xb02d902d011b11120003040c2212041b00407582c9d62001d00c40ca5889981581101c8036444004101581c504070200350310242c040c0040090000059280d00c20b800c200309081c00c070070252083c0d001030740c0c0380d0504605a0050307008040d0202400309187c40c0c180180040c0c20208651100c41e00c0d200441220344041d01c016843c030f02203401001e48100e15500d455810340030300c1c03501c8507100d0312528040e11942d00241d00520440d4190f82c05450144282809942104001d01d81c01c1501101900e4841c4000d049a5012904034826441541d015a03800445803181811400429064500c0c281514031a00c1201c00c40e031404440c410400d002002050569812401c1030381c0040c010307a40c020316032203240448104629403500015084a80360450317040140212000e03029004007241441011904030759050381030348501e90400c00d41e4050401404481d100140c194035040880d1a10300071079004545036042540302201d10000e00903070b84200d0f0401d0301b0403030303005151920781080e00402501c28003002c2c0c0300d199107802 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 788211996 1250 788210746 788210777
    0x506090d150e0f10060e0604092a0e011d0414010605041508101e020a0e06031f08030309060109020901030b0301060609050a0911040b03070504090603050a02100e09040201 75
    0x80304100c1c80074040c1d0501200c1e841a04207600c584070484003000c03511854102941005443c0030780c400b55480c034812005a96510340800020b0b00d103a5006035480714008013a21082030b2a0b9203030b1410100c0c803508030400c0c070f442c1102520b040841644546281030000c1424144801010106d6420035000065900c050388802c10f024010041a070009501c140391200708880810201d00721006c441240c01941c0002e030001c40010300359210407644600d52071400042d4070b100030b10790340900f501084070b2800101030458000401e00c0b80d401501c48404005034a071845079955183d00581024103141e40155085080042d034180d036035003041c000c106d2800d0700400c0c0000141d119038080f0b6040c1d000213000b0f001403540e401003e4422480780c06580e0107100407442c0440c5240e001d000303006c1c0c1a0075995501c0d2400c0d02d0122203141640014208904204042000240003140360140038080c50080014020790300c10b80c4104059145580c80500130b205101c0c0702800283d035880205d6030722980a0038900084045120f = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 788213246 1250 788211996 788212013
    0x6020f060a150b0d15090504210309021e10020d0507030f12092a05030c0603060114070c080c09010608070c05070f0e01050a0801020301080307060b0f120d0e0108010506090d 76
    0xf00200c0300d191021480300000059074205124179001c0166110246440341e54903001e48004a801602c0819000580010448600844100c101242c9800103502400703174000b58242c0900c0e45000c029031500c11b8030003600d2401004010103440c550004101c800301992000d071250142100140502001d844215141030040c210940246100388080202e101e10b440c2030080062420541c00010011804c45001540105903001c03d80d50010001c00c0c02c201e5400c20011180d0000b082e05040000420040f20b07210039010251058900c103007903200300207042600b000d1414402c0203015102d481014010024250060446a00005a490300e4120b0400138285180340c0803081c2c1c0f051101d01178035200015000454a0500d068071005c50340c0c00900c80da5900340900343e010070702072420700b40c10400283d0000741d40e0b40e0040c402e103040502600c040b035043c030000074070286004624a045c2d03040400b8010301c0581c80082008030385004d0a25a031594105804188140030308182d007030203104c0c055031300b009001c0d050 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 788214496 1250 788213246 788213249
    0x40902130f06020a1a0606120c0d05060a061d03010e070303020d020c0609060327030408010e120406020d0f120c030609140702071a2205191a1b011a0a06020f060a15 72
    0x52a48c00003030800301ca1041480e0710100312040c040749801c011444074901050940c04507800e558841c02a10403014022940000107000142c0c550744e51000b04503118000e00504006501940241042424052001e800c242e09154201c3c03140c1d004020510a80d0f84440903640c11400d1b81c02484010440d1904580000c100f8802207035180c8000305000403a01415003100400140e440c3c00d560201c81203c480422034055401098013607004041d130400f080b48900220b8500302000d1400300c1e00300c4001600c95040b540421130500000b03486540c2404214114025901220501c08280d145842d012000a413030782843e0060000a90680d003440d81c0d8080460151403074544041144070440321a5192514554201d00c41c3e1406041003d020038421100e07010700104a41040301102d00d8505030b007400302c950780d004a8920661190451407070b81500401d10981d00c02003074811084d10591003480c1000b440c42d40c070340c2c0904115400301101c05c6d00300c0c80128010741c010b20600004070741000c416620011035440c5 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 788215746 1250 788214496 788214517
    0x60f0a02010b0a0e0a11090d0f150f0c1d0a142707080906010f03020613080f0a111504181e0516030c0f1202040902130f06020a1a0606 59
    0x104402103015494071301c409005144580f03007004400c519401900890003041ea080d07601c6400c2030641000314200840110406205211000d10f100c6211451800c81700f0850542019139512419004444e40141f0050100c0c5055840784103074041c41c10010782c100156000d1260380c0c2c00607028811098440d8540021900300c00880c41d010504402072410498100711403040019110300c000c0f5440b8031011803120705849060004099203811a003d004156028080b400616041c028000412000510091014805100140070207500034245903c41c41d2100003041d100344550310080066505090803503080340c0c2c1a5940e2410089019120b10040c5100001b14103070003004080c0101031002680014800d601010911500740419030701101110044c610403004034a10869180c44540900b106903000000d401c0c003d458180ca8500007426a004071880359a0060345040c1400181030f00c00007030340504200d20080000c240c1c280c4403c03541c00d6442d08912403511807a0080f40341c9888600441d00941702 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 788216996 1250 788215746 788215759
    0x6061531030b060306010909020a0b1c0906050411010302130608060310060b22050609210f030d140609040f0c03120c1e023007170d0201020405060f0a02010b 69
    0x1d59050002003144211510340c46801110000703d422130003031040307408582c0c000e4102ca00e4581094140800355100802c101d5054901ca80c5582c400d03183c2d8010301c0d020794032a00c40440e20781028070b005100492501c040038141030040c0720314524105400d040074110760b218640400191070354000309017800c00388060f041030340d0b0401d00d0120b80e07811a10000c2c200c410711107140030f0070282c00b400901980c50090040990045080241c1c4000c0d2406500a0000c5100d2003d000d40d500030754107420786082440054031985410101c0d103140e0203240e40c40b071140328030b40c142c1201c0c4080c9004c070000760480c00020f01c000d02800b143d0349898107001d14240785030b010755441800808000d102040107444045480da00315002c103240300d00c0da084c40020202c2c9243c0554080c4ca40c2244244100618a109440c64108588000c090040d0611501d04000040041800ca5001c81240c2102541c079030412403604045c105680c01084100419218481200c5840406010749500c0304902d00040b400340405000e510b40c40300 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 788218246 1250 788216996 788216999
    0x329061314100504030f030c02040b1207090c020a051504080c01050c0403060b030c01080f0903070c1509061404030f03090e07110c01020106210c0b071406061531 71
    0x40000182071581d0340101e03000040d00e10506001c0300e07140300e2404001c120401d20600400000e005032003c1c08801c0c4014804500000f03518041074a03680485081c0c6425804110200b00d0a440f92103a00081000361010b001c952105850f002c2c0d17280e00102e078000210090000103814080300500740d80902815038003e108904000c1080300701e41d002030009541c200d00c1c0ca07411a119107000203465020a1041c2c4810b00903581d8201c814074010b400402e048582d000c10894032000030b21558941d00500120803030219614060800104185c200c0d030040018840514070200d0720702c20180958040742e03070165900314280300c1403408941078801540030480da902840e080c4a01aa00200182008840803080312003040144004900380c4800e0b04c0381400403414240110140b1184124401403280100c094210b802e64503240100d81d68008581a264603007406280115564240501d54208100321010100200c0381c2e51a101e5038418001d404400303504000130003080c0f1414a0582c3c0c0c0303445178046000305c080d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 788219496 1250 788218246 788218259
    0x90204320d1a07030606021c050d0204030f11040903090b0c1e030a140307050904150308070c090515060307110f0f010608100c17070513090b01030c03290613 69
    0x949040c00119614032010b00088805209104d03000c104d8080c0d50041c0f40110041426001c04d48070101c10008110003049100060300e00350004000441c862100404906464186000a480214a5a441281000a103401080e4007115450076199004c1825640381110840107180c00089a2100c0030410b4039602d404108401202034903001c41d20361240c01e046201e0686900d007900c0111900c1d40802d40600490180c1d09103076100d4881c1104150300c003500300c1e8403600c4801081d001410704417903031084030707405001204007401000d411503924060380c2014280d900005400d400300078102e50401074000117960000404003d02e5080d80500000c1c2c0e180d044801741d80c94060301d8140100b100500c0b0300008030a01400a10400214014640d19965000d44034040454207800140010301003002c1849a61002d580ca5001c81700140408680011011201d0001400f0b44040e98090410b00d480c001c2940056201400d001218411403030360100101c41d84c40c0020b94a00030680c030000c039008100004030740c0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 788220746 1250 788219496 788219513
    0xd12060e01090c0806030c010f180b0c0d0f09030b06041e0e011a0906031e0f16060909090f02091801020c1e0d050403060518010c18090204320d 63
    0x110155684684d4199030340c1003071540d0751251080190000340d060f0700c0c444c00c107440f40a0f481c0b85040450040c0003003654408000c007182d0041e04122969410044550b0901604880c001e604120281000c0d9290f81c41c40c2c0303c0d107000d403000911040c0034644403d100c0f0710600008220000c00c0c0d010b00760400007801402d044a0080c1840f0304c641d491881e0703031400b02115241c008111440351500900411900c0107000c0c010381c124659845034103452084403000304020805001000009041c0d640346c4810915000c070040a801031544a00040b81c82d0026503800700d180018074618460701610100390036241e4810600e045a00c03007040b00c40552012817000e400c00004140008141e14102e00d00c0c5c82d00a80610b40c6464420441c108000300d101003004200040e095001a9840792110500c00c1d03401940301c122034207440c10b96804d040000c0c1b961300da80d007801d200d07010340704003805000004500b014280380100c40c07202d4200d0300f41200101e0754841c1400c020032207010041102c0b00076001541d01c0703d01d842c0102d403 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 788221996 1250 788220746 788220761
    0x72f01080a0e0309043612030605010c021207080a0b04050c01090e0403111609021c06060e06070c09020f070c08030f040e09101a0f0f030d12060e0109 66
    0x203040c480101d034840c0c0c040c0c003070b88000384460b4010714078140940b010080208000c1080b8113030101c4020729070001c400981000040c01c40c011003128040c81b0f03a8503192000501254512040c145005000d0140340d0784038031801055681a0f0300b0308880038412028518001e810f62200206104610031041045810400e5500a611410844034001c030128010340c0c022010340240056007100c2000140071030300c03840601034403803110b005884c0f015104d51445044102c02d904903411007900010046d20343d80c22280390811182021600700161424400300800c8004000b00030f41c410080407802409104459034840000c10b1840c40443d40c500300d003c440c60702c5800c005800e03109001e0040001551001c08801c45403100c040c02036a5141c1414002130800721040074050690501c220070b8000c040301040e200300c110300b0412030242e00031a5958010402c0308a0700141e200c0c003070300e11404c48240d1601c001680b020003403064140700341c0881c0c14266543c001c203101e41c0310410b01e50f501d400014070700300e9582c090351 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 788223246 1250 788221996 788221999
    0x1140412031e051e0d1b0807110303060d06020d0f140a060b0702151b0f0c190e090f01180b06010c0c1a09040207060b0a05030601060212072f 62
    0xc0b00003802a54030000701c40007060300c030301140381003202181e80b0519064030355500c4105549142007440d960406412203601d20401003800314200b8080070317065001041250300004614040da104100c07244c01d50340720302001d4042c90003107140c03007c200c0400a00b901030324002000000100030724446880900050010180c0318206032a03000045800b00c41103000721820f840b84800c003640350820560900c00050001003902000710001c0c401c601c2d00c0c103090084c403070408001c40d0080811800f54085541003900d011040c0f0310446908440c40018602582d007030049603008280e000644d61041d207103034184419034500b4000e55182030501c01f50743e03515800308190396000707e25409099650b00010b6424400410700034201081c40b50003007200078002102c01d20440f4804440600b8400341402040903600f24100071900d86403203d1030b81c282c80c240340141000618084004041c2c81d4505403020f07403601c1a24186544000c400903101c02440201621500c0e480d8001365046003240e40404c1840035100401e02d0705 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 788224496 1250 788223246 788223257
    0xa05010e03120c1204020d0206070605040606031103030c0a0206160f120207121109040602041a03011a070f0b070912080909090708070608040f0515150103290114041203 74
    0x35443c41e445015030342c42e003644040d4120701d9110303a002c00c04102117441f022a070002d000c0104200042260003401e0146100e43d40205e826030443c64000c00300999903802d28002c0d8001c0c08103c103501c0002984200190301940d100380d551420011f000d118454001c00981041728840c030b424104407811070422541c2c9001c0d0300340c495aa840c0c4440c2d00e1a80704030074018003507109118040c401c2c0e18221620541043c401d0400624141d9600c440000d2100821109262628088010403890070190708841300728610744c00313141c07421486985d00558600102405400b0902010000d01c4407409080c5002c0a0300c4040c2c0c4142c4c060290380f03800e504d1075102c3c01185014030280804a40c42e002d00280386001d4810740d1028200c10741c240407040300c4c1858018004d0342c86040c00c10030719010400c1844044101104030044034410328240c0d046c00d00d0300c042a03a41a04040c507000c0301c2904810008007a0103401412203090300010300300b5004841c2c0707041d2031440c95000100094006a00741e00840d000811500c42d4598 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 788225746 1250 788224496 788224501
    0x60b121c180b0a08070201141303120b091807051804030f111b0301020f070309030302151006202d0a080a080c04030c030b0f180d0e030a05010e0312 65
    0x62004818451041c80c2c1c1c4a00140441c40500b800b502409501101034400001d0400700e20000c0010402c0aa444982c901c0010144c2c00a0650144101d050808000c2c001c7c0100e800d00808031b980400c0c010b0000c2e070001e00e2011400c1c81460305004042c01001b009014100b1103489200541007000305a4003100814441000049214080c0c82c040a401c11404041d01654144901c1400d07401801c0c4034440d495503080100080e140fa409003e0440940203640701e810303050031494060314001040c0f900c0014410494104030700d100f14103842809603000c03458031841801e50094081115158a0b090740101e000351203414100d03020f00300420910b100c034261075107180040200110b40303131828945d014012072400c000d50320482d802852020b401c45080c3e0200c1e4581641c0e901c80440505858100f213450b141d6500034803203030304410b6202c1a049a015030180403803401b0703407503202d642d1101c0c014000103006000704400341540e401c0c072036201d220341c01000a1008020b000705268482c0d2080c81803505189000e0302 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 788226996 1250 788225746 788225777
    0x306040f0b010c110a030b1003030f0903151e1b03051617070e12010218010f050a030b010504050a06020a1a0f1801020f0c01021308061003060b121c 65
    0x240c91850300d0107031500c2c250040e040d210f80700c1e903402c02e1804d00d411000c0000008001030004000c2c500c241503450702204580d003103107001000c2d2003030185080c0801014007014004102c82602180f4029881c200000e06d00c050381c820a400c403080c1e02d20101c80c151901003090440d0901c0401e09a00070402e44d010803055603084040d03603012010602d0342000a915604945040c0315032507103640c00080c103080c02e860b40126080000c6a03203451550035005039401044c0c81901032403058079240c40c50b0090070100c0603180ac69400401341c2c000c0c00010000c25495040d1102d5076400b41d000c40e005000082c0c420034003a900c40c1c4001c0d5031458203000c1200d01003c00f2400e4441048030340005401811200d1070103006407182c8610504a0200f0038178120555820403003800388201700c00041c03000c68114400980c480c80c1000a20000380c4e02079005800980040040141641c05100c131401920f510110014100d0342c50000703d180d8000c982811480d602c5076106010000041c85080c0c002c2c040c4958802000403402d08 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 788228246 1250 788226996 788227001
    0x14040f0204060e092205030403030305060a1a0313080a050c060a020c0c10031b0801060f030e07050112020c070608011a070b0a0e150403120609020306360403050306040f 74
    0x100720300000d001c038982c005580c60f00c0300c0d100303421108107625070421022240d0486a014045c59007142c07281d200241c10010950940139080c0e101c5000c69814901500d098001c0c0b480381401c2c1d0703424982d02c07800000507001c0942da01881c4030840d002a0324a8036409100000b4105900020080c0c12a00c0707400c1c00a06119114021102078000280140840c00341140922641100d82c1c03020005040c0c407250403484600c9400d0304841401084d9a0300391440d4507012020302603010040042c0d08050911107414403000d4000752a5007164003e281040f0300e5031501c09481d00038000c1d90392450990060880015095605c152014180c810107001801d0150140602c80300c94450640b0041800c144800010000d06851307010115418805080d640c1c4030101244d41c03000a17a003190201e01180f20059650040700c07440c400d4501410103100214610705140c80015114001030701280c0004072158071910880318220034030001c00f08000360341c0c0600e05080c0b401034155082201d01a0080d8501403807880f640d0900d0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 788229496 1250 788228246 788228249
    0x170106050319151a0f03010b01020a110a0506030108010c03050105030a0b0c0d0e1504060c0f0c1203140114100507020f010809010b06040801020705070509010e01060f020705060414040f0204 83
    0x14010054021903080d00c0ea0341c1002c800054491441d030202c00c050075195400f8152031031141c0054140076211441c2041425111481c501e80660300d8880d0a00150760002441032503244c01c040003241280000e4001000d20003980c2142d43c1044010000180108054006075000107450702c044c003883c0c0e2074406040e40c80005820261801c810f9002007002d1032460002007015203500d00002c2100c100e528000c61406a20450107240a2100c00802c01030003468842c1118112440c40e1810898250301f80c01000e04129200140041c1d420140c0301d10000c2c001d42c0301600a89a121071440c40e980c2d0b41c1100450820f84900301c5010354a0300050b50b524034071401c00c03168030035401414100006905401103d1020000300151003e45d6524100981aa40c038000340000b021140000740c0e903a00c2e42d20b01641045040d174402802140104014044500c810041c43c2c19240305142c500013004903507404038076081c400d80c003840d0040000a00859001c11007a04084c2c40c0d9001c2d18140f001c0c10164200408a2045 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 788230746 1250 788229496 788229499
    0x150e18040c060f12020f0c010c21020f2a25060c060b09090a02011b050a020d0c1e05011e1b0524010f060806010c03110f060703050117010605 62
    0x80074010b111203405081e1110280c40d5501d400c1604400044080c002c036444480711121901d00403499041804003405610088000c6140001811030023480700e40400f5100c80d0f00a050b1900810000d00100c0402c0070348908080c400c3e800d05015a0340c10130f80c518642c0c03401801c225402a14011407800f0402c03469021000044200441d0403850000c1c110761600c2e0404007106c0c1103444404011665403106e100e0b901031903008010f403544421501c0003415170341c0e0000c190b050001c05500e000c00400c002203407205813282c040d1040040074285180c41c2a800c0100d0700b10410703600f00d240380da054000c81601694103842082c0c0b00c1d0094a81c03d2001207500040201c0e500e0300003240160351500e06c0c06c4103441510498400d108545d02e00c00303080d1000c4c2c802150b0002032036615002d40c004001145030118490f00400c001c0c100900c05003130000008000100a110240c00d120000b40c0c6851a0341d0108071010b4101c48240c02d60301c06080c10391009002d0f081c28815a4107860020110f03221820061081b802210b00 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 788231996 1250 788230746 788230763
    0x10020901210c02190c09180c06110f160504020a050c240a151403150a022508040303030203192d0605061909150504030215031905060a150e1804 63
    0x1130044810701030800356011b840030848a40c820400910701d54001da003e44105e464141e0301440380340b451807a002103000035210540c01801c0609003310404803000c20380300281d802607510114098140c0d101e1140e90103d021502c6030700d6401403180c0042d03207801d03007480e4000040c1000340c0311208603070103076286c242891204110100b401c000142e00981c0220a400c80541070300c4c0d9414540080d00d5140004a6918207a10340000320002034480703d800ca00184880404914185005500c80c06014015400010245035000010642c40c0007000c0341c2542e51400c07403600b031000c14141d00c840150031412024126a20304645005007030042c4500800301aa140904a18102a00b80746540600c144000c0b0788030a0002006020031440d41c140015601d2180740c0c0c948035621880c520510507075007403100da0b1880c0c6a10030300c10700564001008008020030b0100134081403684550000403010b010b59801a0720402c1c0362481c00c1a80c5400460320300200030226060b03440741e40c5480f82c050403070500300c600410030304 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 788233246 1250 788231996 788231999
    0x1030203150415020d090b090a1722060203070b1005010c06050604060e160210110f0703030b062205030304050d0803090f03030a09061b0210020901210c02190c 70
    0x140c0c41d811550040c0103440041d1160703001d03445481264407050011400b69103500105091000203002a0b400ca203c01d0020901c52940707880e1880500e0480c20003c01122001500080f5200011085503000c28406890110a07958003000382d581d030301126085946d080c5610000e1340802c11001c80504460040e150b5004000203a500d510003401d00900c0554015a250400301d041000c02d0b40e558411002d690b000c0b002d404040102900d00a40b085055a819051000b00111020248255210300c880001402d840b05480d140a802401e1b606c0d00c4290015408a03136501d441000c62607000101c8502004000c009841d2810325482c0e00c20380c0200358024541800140004404000030f581c044a1142551411480440220300715802510b10003409511000382c4000d03c1301d18458940c10103101d54005001c03012091001c0d40303030000380300d2000e031061703010070014216401100030b02c06520405040320060305d250700014001f441a4402d4038010b02c6848104500c2050500100364156003050280855a = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 788234496 1250 788233246 788233273
    0x1180b03060a0c0903061b080a0605012a062a090e040807080c0a060207020f01210e010e0a050304030c060207032a03051c030c02120301210c0b0307090e01030203 71
    0x1041204504010090713440000404610300b40b0031400c101c0c3c5c000400b06075012461030010401d050180c1030480c0c0b549011401c024a230b070460324080030042c200e0f0381c0c443c1109050646528082102c8405481942000d1040c0b040f0342500e040600c220483c2c42441d0101803244034200c41140f2680035030300914100d00d001c10301094045002e403c400f072040d00020314050131924423a0500d03058207003c455542d008650031085240c14010324110400c28038050807104801e03c075031512036a1641c0e00300182a51071b0403110f50040203400150401c1c10600441c0e1a1090070302d4055903981c001e100c01d440d05001c01d04085211440800c9030f81c100d0341c008007070030510106d003203901d590040410850001503a0400300000021400d108103061900015034140d041100c0303083c00b4059444100000d02150030014610070271000e03050a0b02d0540d40c2c1c0781d2510601a046030302c0307601e0781d89411001a0101000b4440019203151407001184140340594a00394569501c101c0301c44a0242808000c1d41904100c0100b20310 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 788235746 1250 788234496 788234501
    0x60a0905030c030705010b040f020304030e09060102010e1e0d02070e010605090d060603030815064803030403090b09010f0f03060e0a02091f08130f020a090501180b03060a 75
    0x114018419a80b4002c4030b0b004040c550b501180c42210265107826415216280c98828811020190101545140741569000300310006e1000d1681c89080ca090100d80300703034402d41c440c50300c0900c4001100c01c0101c549a40c049200d81c044100f0074030b48504103013040b40e0303880410711104a603001c00d121859a402d045003901c440e081500c5482d0048008901907012444a0092070001c40c060b4840d05290304101551b410300300c201100c20360185000b0440d10000d0303d000460b03500000c82c45030311a03003080d81181040c40744100c40c65540c00c000950303000810034240c0c040011401203109031106c0c1c624640d01c010320b25150040822840c08100d181c240724801d180511410000a00c444c136000643c242c6420701d050072110103035079080115034045103514840c201501803902915900700e0140f010b2131032500061040c900201101ca00d0030080c0801c004004030a0a80c1c11160340c028040c3c0d400940741c03a1301400134082407045a1a9a0400711506100100d1744600883c0034400b40c05011140c0d0f07400315840c007 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 788236996 1250 788235746 788235761
    0x313030f0510060b0d0c0311220302100807110f0d0c1b03080409060b09060f0901020f0604050c1023031504150801050c0f2a0109050c01080c070302060a 67
    0x1d207030042c403081e400c00c281c1500c641c002500e01100b15580341d10811101c0011140310f8440101031501d403007505c0c0c211201c00c005403004d80c00d1848101d00c802103070740c02e40c114440013a403009401c00c006410340407509822692440c4500500d0307803032030308032020303801590b0b641c40c4020142d410036007128011143c1c1601c1140511f0351207009401c00da090383c283c540054015119903000b40d921650100f014800100e250049500500a5041c0242002803140029000e84262590100610300000700241640d00074091510b8502480c010380e2428030745401c0094440c41e088000703610421003c000c8026241c010301150000240035500180301d04032138400c40d20968006800141c1000c0407107400b003030a950b9406108038aa681c01400d4200500d031001450035660301038208203052105000c84503144020005076112844288011010f40d29800390a2181c010081c1002415500705141b17841070110000f026403100340d00380d030f9204140d641c0b6003440e4a1400303001c100400507080700c000b0400448060b0480d00303 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 788238246 1250 788236996 788237003
    0xb07080a03290907050c100e0106050604090b1309081204111c1e021807031509020306010e01030510091a060a1d030c0f0d060b121b030313030f 63
    0x440b0580309003840c403940c4003865a002c2c44512007001801c941080140303103030446a6828020308010000c0082d603266030841c00703180d4440b640d41c01c021441501c00d400c011300601010341495a919242c0001030041c0107410086401401080ba041d42003080e1445029112500310058900700316000b0140b0300c1c9070101a1050b9001d61801c07640c2d4580d6500c01c0704082c44410004e0b41c00410440d00c0c0f030030364002e581c01014116440c2c0d6000c207074005602c800d022001c5651109841e44041e0381e841000794014903840f03441d40842d40b41528081081d9103140d000718000c1034240c82d180c1d000c914a40c0110142c650850310b0000f41e4419880c1003000702c10582200341c4800c10100d1206602440b00040340301d075017100c031403000007500301c0d56440710498001780301300340d1031000b80e0241c541c00d1303401004185005c0c02c00e031642e4000c180d1992030500340111544042c1407018000d08590748500c174041080e986010300c003c0480003405803c00803845140000c1210007003c0800450b000c55881d40e02c61103072121361601c00382c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 788239496 1250 788238246 788238251
    0x150207030c050f030c091306050115091203120501060903020103290607050709020d020403030908030c073c081509100e10020c01270b010509130506040b040b060a0b07080a03 76
    0x1103145a846d40d0b1141d10440c0d80700d01e42c4009240714108217013529010384c4000c014211745180545201d9000c000c207015100341758078010020350710349011540d040503003000d10ac0e03091829002152460340080d0700c0c4100e078003d0b070f001e1115146540d0244005034103604034030303013009105510000506185010380030090140007929001592030850030160780c450412514001c0d4002400e2003019041050752015002c0b0900a44c00c0031079005513103545d00c0d8280243c80000301c0348001a44080c807941d0317031a10410243d0040c030601c0c4281620122425296019100c8140108c0c1004602032042c00d00140c42110404014200041304a0401c00102188a40c0c0c0e50725000307011090303c40f0842c40c0010450039803d080005103140c0100c0988080c580d643e603540014280c80d4140c0700c04a8070b10600107054410441d122090354494980c5001d8010701804001d080740a081e040205010494103054440c45c05881000e000382d8070442044aa030007140101c4502c18004c7c405803000c26500805003140d03603140d0500 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 788240746 1250 788239496 788239513
    0x60f0b010210150306051009150b0906072d03020c030307030918021215030c011706101209031101052a03060a170c03010e0f070e0402030a1b150207030c050f03 70
    0x5c0d4415101c0c112010700c44450802003c0002c4001c1d4810004692035a0041c8803103107050074a496003034494021058400c03500807032000244030700d224401030510f00703001c0d80300e03298040402c0c5a002c0050140081d400350084801c1010541400720444000340c0e8540d5401c0c3c034007408d103120b050003089005181c25009600303001500000341c5240300180610301d540c01d07000d1204103040c101440c09007503011141c104488409000920352850525a8001d00221380200010340c5181007162242c501c012400308450400d00554145a001004a00f00302100c10003805180c0e11864404102194402d80d80741903240b01030380e140c5002244001e1600701c40018010100380c3c0e030340c24500010421451411000c1c2c2c1107011503035440d250034400c950100e1b100001406e0341d42d55104c000c035140d480510802c1e040c074401c400010210740d4180000d0300313140d600c640c0002181c02c038003080c1915080c45014030075405180310281c88800d40005040c0044960020021f41098100414041e0200e001c2082d00e070584070f030124 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 788241996 1250 788240746 788240753
    0x80d120204170f0606030c010c121215091802090106111f140a0902030d120b060c0a020909060415020a03090b07020d030f0905070e04030513060c060f0b0102101503 72
    0x4020280c02e80340702c010500d0f100c28004060402d075010b012144264000001c01002d0703608100200e4505820502070b502c481d4284509845600400e0601401c15103000d90b1300c014507010780c44c050151800814200325148100202c030302c8400203880040d42c000034150040190b03d108814541c16143e090081e69aa040300c58030b4064070440343e40c410b5405903119002c80268800d01056540d0200d0100000e10035404282c0100e51a03089000c800e0007040540700d685e03000c1007595084200c5418014001582e11209003414a8851580503000c078401c89402c400f181e00703041c0000d5a940603030b8200075020712040d00082c2c0e42c0c0080d4400703541c0e4800e0686400301c0c00041800e4a12803441800c2680140c142c0b00030202008040718043c84040a101d890000c4c00f0002c11000500b000030b5900c4c0004904164481c4d050603255030044001c0d60400c2608240301003549507002d105039040611944060100401000707100b02a101c8031014640160300c080b0200c1e040704074075040354407120182890070781120746984 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 788243246 1250 788241996 788242019
    0x406021608040e012d061409060705060a06080d0e010c14030d2f030402101808030903100903021902120d270f0605090a0e010306090b010906080d120204 67
    0x10302c03083c1c80c00c0328040100501c440039440c4000002c80300354003900080f14040303244c4214401e4004c040c00c0010741055150b882d0545000c03104403500080c092034031110503180499540408490003c8224202100000c07845070006079040c140b081c130744070050400c245c08011500c200c1c01e00400c0d1841c07068080e0394000d40000380010900c07901280d401150142c007001400e11003414404003e0900c00890285004202c40b40c0b09a94025a0440c1c80388243c007d500300803a4854034540010310011048240058000f800100802412200b81c040d40c2ca100641a018400c44221400240c0980c00c01091703a1100c40c1e0352224601a18802451f08003000300f00c0068600c2d0881013554480130602032281d11449001489600c407101c44840000041541030081820740c031022885400e003404008240486641d94950303048002c5d180c0107030380741415a543d0401101502176440203031100140480041b994032558000d030000d5802c804020a403443c4810400c54070a424142032a02050b406e0101052068940 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 788244496 1250 788243246 788243249
    0x180b0402030c0c060c190302030a060302031f20040303110f1903090e040309210b1512280c1511120901090902090418060501080c0405060603040602160804 68
    0x90b80300c5070303e642c2c1c0411403524204e03014294000b0707500144044a42601416401d00c03241d0b0b1540380240c0c813078803504014805002035410081d414041c040554107480c5106050502080e14000107200d00341d00f8080c006040c03601000c41e10108113040002f4400300e0f00503100640c12028034811516003504a803800d1b400c2a1307846844ca507041004c0c0c5080d401313050b070040e100c40142c000301010301d0190416580c060810141407040302c03030b203000408828020340000e81d034040300c4070780240921600740b030300c5940d001c00b41d1070b071030020b500c50380e90311410100305880001c0070090212000d0f010400a401d0150040d80c1c015200710450300140707103401c045000c502807080340403142000c1d11600c00e2500101011400c01000303002480e100340e000e0060f210f15a070300015131002c4540104005a40c0c402a201240c040c1c1641400b102c482c60410311140704100359980210f048503880015190a54441c4040205480301aa2120b0b804031081c03000c00d0102d8941e40c001c0c095120301d03002c0f00182c44a16034038070a603030700113 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 788245746 1250 788244496 788244511
    0x30c020a1103210a0e0114031b0c12122a0d0e031b15090a0213140709050a0909230c120610050f03100c050d09060f0b030102030c04180b040203 63
    0x21500b5141380380c018107510310445003400c1200080300031035002d40441c0402814101182458000c19034003090783e41c202c13001d088014054615940441e4a241010351015030a03424100104001a08401940d0048102121030030f4440c0c0003851904400f600d00d4100c100e10380c5046550743c1102500480400c0100f280d00302c2c0c003484420009840f1f80d80741c01c00343da01042c030b031100b07440380200080d4290201703111113401c1d03044580785007801d5040c42c18030013070100c42c2c929400c68003c0302c00d02582c1500405014111441210f52001c600d40f0317080b810302a00d00701d000003402c0f1908808540c1040c003140f02d4501c001075001d821100307941c10450021703425858002c01c55a2640003d01407140003d1008140005054151807060940c0010f60200e80ea401c0a4181c0d06010f0f55280d01035a501481002101e003103180d100300510600c102414a40003c0076450603213444613140c140425410304040c0241d070300c1029040c410504044c509051408800c4141c8104000c0c0c41d070f0350240310180c1d076880c400780d0b025560 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 788246996 1250 788245746 788245813
    0x9061501050f0714060705130b030a02190c151509021809010b070605150f0609040f06080c0a080601060f0f03020423030c0406151107030b07050c0d030c020a1103 71
    0xf03c01c0342c141c0c28540050070031170407c0810040781d070498440750000d50448800f0344a603952541c079200d050009000340c400d03840d10780c651842d5845207140d000031000701184c01100c204549140717000002c0c080710640c4440081006013010204015106c9134050980780c0101c201001c03a0a4000d0001404888240c001229991000c03a100e4107112440c841d25601c00409441c4041c802030540000e20a883d100c1d01492290b00b00144149054071150440101c441d2102c0d000d001098540d01d2464450303a451400c00d01070088080300051794040010340301d04031011a100c0c1e1440e41200e81d811517504104584a0742031540230031000585818010b0030b945c1003264000c1e0b0170568003030309017098101500c01c0f80580c8607509003001407100c400000c1c0c1c1c206002c451800c01c01c0030313400b400c0f10440c00c094650f400500b460725140c00b080622038101c00240000c10929080c1ca0034050504429421110000e103100010f900c40901800018542c3e03009a8240340300400b101c449030b580c46501e040e22003021074aa032006a = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 788248246 1250 788246996 788247023
    0x11b170c010e0f030901120f2004080c1806010c1403030f01060909051902090d061d06061c1209051903030801080703021f050f030a0614060309061501050f07 69
    0x84184941200080203001845c604803905000a000315241100d01500d03503a502c40e035180c030780043d41c490220703403e52181c40c1c42074980c203107490b4070290064070a181030f030f010b42003082a403842e1012800200107061205015991281d100450b503140c00300104403549426569551b903145030810155203d054280450401c56062100042500d40140c0c1301c0f000305800c240c1404405480540b80c28500d0340c5198005880c1c010301000648107401384070f00540158074100c20b04001a070404d240c00304040003241111041d0721104c0c10f012640100d55000321040301c101e8041070009a409003186c030303034480e28070344010707046d450b98001926005076440c0e4005810384110100105504811100d0040c50240040d2851a182d0380200f00c105480000c3c07801d8640d00703403000010041c0031304150303501807003545000c5440340343c0141d4207802886503004020500301c00322444095451301e00101e80c8100c1030200500711540710841c3c54042151412140c50501600317205d218007400809005c2c00c2c0d114001c2c0d640355880c1 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 788249496 1250 788248246 788248271
    0xc0a0f03120501320a06020307060b0d08070308100905090c0907081b07060e0d0c0c0f05210a0b07091d161d0a1205010506030a02011b170c01 62
    0x4003540070a0040d09030900740100034010000880301034034007180c0d00850607020b152040318512540c14408540c0614402c10200c0d450764000060002103224410400000c175001041240440350104000d10102c030812050300002e1180e80c0c883c0d009101240309038032880d120107800d419214221141103190b4401d140301ca4007454800503160b008180d6041000d99400c0422400388183c0300d5096281180c0400110340c8104403041e8815800d02c1080829241d1164440200400051109400340e694003055a00400c48448861030901264002002e450385081c240c2c0c801141c2411110f0f00c408a400340fa08100081000d0120003440307445036540d04c0390030904001c21a040c0d1a001d2120100103911041007100515245004e5120f0000c5402c081140b800b009440403200c000303031030300c0c140c000000503000503980680162151015124200034440b07a559001416611052080c3c007030b002605140e6001c00c016494030130b4020807406900c0601e0034040040056481e6441106c041d021031395140b8841030103 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 788250746 1250 788249496 788249507
    0x200901050f0f0f1903060f1a070c09050403110d0509011b0506010b1c15030611040807060207050109081906020318030c070e130f030e0103020c1b090a020408030d050c0c0a0f03 77
    0x707000c04c6040401c034076800c001038042a507003140143d5a58a140c404544990080481a03441a0380d00544107200141ca9032070000203403806650071404200c0b07281c00204007000104900088402c140e4589003440c0c140c030011165450000000c1018190b154100004a041888880c1c060103002d0441503442110f03403c8801d00c4412400c001034406c0c40e2200e01401074888500e0740044035004503011802240705c001c00c0d080b61081c0d52009249104076000012469004603140080320000d8070b031004038641d030f18405512112a0b841d5481c507900090340b05000070701c081c0c0c059904100c03585610040c10001200c3c10340741d9804035200300007550100c030701003012841c60301080e540840c0914611428110342d54407104c01800f03820004003171010640d24805d66910960544a07500e000d9000c0310714104a02111490f200406807201d8025215030000628809c8680211004c5071100c000075454502c058180000400b005032a64034000340800c4100307403100b030401150392454050040b18080c0d000a142c080c14 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 788251996 1250 788250746 788250787
    0xb0603090d0e0a0b0433091a0a021015090903200307050d0f020a020d080324060f1303080c06100e040309090903171603200901050f0f0f 60
    0x49103903843d6081c040b0303045840c00d940460f2045246e80f404180c62415a2500c00344203a100e0400505017000301440039480368021045075914607c038286a1081d05801ca45c074414621072a0140e8042c165000114511740e02c0903c000c800c003c8441d901503290034950041d6a8521020b800062a110fa4401d8088000d40f900082c1c0f0b04032802580741c000306595898598a1460000040c81084034400d03003c18000d07c000f040d000e82c0203028250342080c0317140c248225041039850404850003501c44000c906113880103090900b0008110710b0030059212101030315640000b1546840c0818842e001000a00110180c464115070402400a500c0c0403000c01110390150b40c04922000c141e401070101013a0441d0350314041d600001f90210f850946420140c4600110405004e20200820300300152096007804c0550018003540c3d05010038054030380140d0300118414440d070a0407008103c0c8054543c021801041d010024207501820300036444480021500060035480700d00342c00180341100032016524104 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 788253246 1250 788251996 788251999
    0x609020c011d06040f11040606030203070e1002120708120703021207020321180a03080601170103080d0b0307080102070b150909060f070c05031801020d1119060b0603090d0e 76
    0x8904101c0c1d402c01a0b035895020303201a0095900541620500580131182840140301520030302481c0c7e50703020010300075130045075010001440441c2c0c2107110314000d251781245400607030060a01c44825642a012a44529000c594030034003003289403268140d0300986d074843c110301e0700d0058580482c0900d080504400400c2c0008540041010b6401400040c503a004149070529014003c1d5480704160080b0000700760306130501c0d02c660fa119800709940f0240003031050400307a88005041d01c01c0d20351070290107028040108441001c0c4100088202c26034004417200a0050888140580d180c034040e00720703844031905551000109040040744080503448080000341900c00c065946021206181c4818014213003908002e1110089802d00b8401e4040112030780e00070050b29942e6110982114400d4506100a800740c002c003251081d0b0389000303041080e04600389001800040d10340600251101103418811682c0b1982d64040c41c5240d241d240c040c1d407081d080c2030000c2110300c800724406800c0c16032071142c0d075 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 788254496 1250 788253246 788253281
    0x14130314041a0a1704060f0b03071d071b140d111908040504150f050909031206011b0605071d030a0308150d080d0506030318060313060609020c01 64
    0x100300c88500c002542c80d04403180390240b9158058128121002c19089000f031000c4007404060005004042e40702010201d08070400704003840c4401c05061712030201c0d1188000d043d1900007030012441202c1000c03503000b0641c0c038024007a1101880348501ea4810404269541030030901027550700304080110909400007820301e0384128440d0091142d5440d401e0342e1302c60b40760101080c0300c401c0051403000e40d40a084010000e0001d11001d030014111034440384102c3c66441014600042c2608101d60460301030700c0c5c91000796103410589424412040710181104d130403c25251401100340d207107102110ba03007622451010540c1c0c24039001c000c140e055001c1e101510482c0c0140360000c20390340000c44074002541800c0000340780d0740d15600e01110b82c0c48065071942240d00604c0a030204000c020082601c81e00c21001000651a040c043c5940c0740282001030343c070603680c00d1150030140f07032201c040c5500502c0e401c0320b41c0f9601c0550342e80b81c043d1092940072044868002c144201014002e0007000700100c50000b00 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 788255746 1250 788254496 788254499
    0x71e030513021201150b0a080c0405010813031b030522081011070804080c0a170604031202090301060f150309121b1202160b0c06040201030e011413031404 68
    0x501d0003091003240024483d010030250b851902e4001c0d0840550541c40181880050703680340302c036090700e0f40f05096440001d500c0d840040c44422440c4c0503142540c1d0103950f200543da6a81e0001e100c01241031200f03030103000d040201c10080029000d040e20080c0d11a5071880c2e210000b4a18910b4141602c50180450a1104000f40078110303000070017110a150b081c0700807420b100d00442c40b14503880386010183c0350010010300418240c40004040ca4064030994509004079500c07203859188100f03072000e98070316801c40c80c007107008284a0f61030041e1503181c0c0040140303402c560348002400c580082c0d200300d400344c3c600e0400300003124005007811100ca000303080c284004a042d41c1d42c41c40c07920306a00001c05014040403200d00201500f0014284180c0c031004240d03001d000d1b081c010759100048034080d0315a080c41315000c81c904044600b611044c0300403200801c030381c2c3c480ea0f0055000d40039000c1044042d41d03a514200341c003901c2030040c19014041c0c02803803501030303100f5080080548103441c502405143c0304210 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 788256996 1250 788255746 788255761
    0xa050f16110d030e060901090f08240405101518050601030c020c010804020418080408060f1006020307030311130609183c0203190f1a040b0301020f03071e0305 70
    0x1206403010600f1a132080d500c141541c0141c03420714141e000001c4100c41c3d80f034041a2b000e400510319680c036803501241c49100ea501c0300d1000c01d80204990050460304062441210aa002c0d0003c15018180c5c0503503d01d40c54403003003069040445035240c41c2c10142c84500b0b00600d940c040c824811003c190f031010b88220322003040040c2c41d1034409000280030b0b507980c2403511501d00a003282c11986541c0041055655035450403903c2d65424141c40031412058940c01041300302000c0c000041c1201d100d034000d503007410400e0710107400a08800454507011881007201e207400020709051507000d40901d44806207101c1c10010714006691a0110010600345050307503481d681ea040402c500e1105001e5940700e000f014038158070b00200081000320307552043c008804c1c420301001142c041030600c2c041e003a081010400100c03507201910340321100c0c55081c2c1e2440407220910309154100404c6a42c1c041e00151400f015150314070250b41c0222110400904480c030051510704a412043e188075116280038020741c24180e8 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 788258246 1250 788256996 788257007
    0x603151701141b090d15020a020a200d060209040b060406030204180e0a23100c080906040305040504020f190309140609030a0e1809070603060f15050a050f16110d03 72
    0x241d060302c540640e241200800c000101c2030141c00e51b140c030003551200100680a950f840203601d04a51009006902c104041c14280f045085000c0c0100a030282c0d80c40b5031614402503228a040316002510342c0e0f201034868949800074001400d80ea503005960318508844044d02da9405c0320320b0b824403410032202844807040060100c2825801c00086072024034903541054840300300781c0701480c1900900e00c80303041c4800a40d0080364110480d480e409019994060b1107502c40710101d4004020a4040c0801c1c845030501c0e502501c20710214814040c45c20100042240713000300c0410181d00025102c2000f9001c1100e0200f1852910340c00d4001440c090400044058407401800507000c1000f00c600300e52241c540d501e5900f040000f24a201d841482d080551029480340b074240038010200b402c20714005403c0c0102000d0b0303000c039510311035903401c1000d004c4021122030340b02000c0030003045001d2044080c03125800c0001c0c03020b11040060300619034000e181000c2140c0640001e54030481031200c0d2100031a4005 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 788259496 1250 788258246 788258257
    0x210a2f150421020a06050c0901030e06040537061a0303040e13150207210c2111072702040503030d1508030d15050a06090603151701141b 60
    0x4410448071180c42c64000c03031905101c0940a0103032400d03c1c050000007408035005000382d082c2030f039040c411403d080889998034030060740c0c01401507022030560900c0407105074000c009410303465114540032407904980c03100315880d208243d5540e075072590920070803da44100381070016000e03000745003442d20304920720a09101c002c100f000e189250b50f03690020032020044900700303662030704802c54994585050203801c41101c03000044548210701004962240141d510b07202e21580640f807a100040d10700b025a035801c1d41e164081060054804401e00540d10501140e005081940ea20101d0f122100c190780007035548d0f14048a80380ea00c1004140425240441200d0070750034030b0b0001080d401102d00855420b4801640420218040030900c5100c901c4140c101c043e048104042c221000381e202d404005080d0554030a503408146190010040344c1c4c026000303842d001d090030000101c103039034500031104240841002c1001a035511922417912519118002c0e4102803130614030300420040041c0c003085840354 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 788260746 1250 788259496 788259533
    0x20d050708070f050d0b120d080c040b070f080706141005061e07030e0a230a0b0a08090c100f0f0906090924031112210a2f1504 56
    0x38001d4540742d40b81c6c000c2e04010001070222490032440610241d141c820741c0840710300140184c0049001040c0e281c0c142d5080d115003603079840c549035991351100020490400e003112103420030b203c03c0011401d01c1c800c1e11b00e03040c03441c5501c1e450381c039011094402260079030704202c2c4151014400b28020950710400c540b8001c0b40421016038401c400c2c1011340301d51920b510325a42c0901c4d102d0010428041c82ea402e120004840480061500e110300c040240c025160f005130f02a07014280f020691051107081541d8000200b0b00507102081380d0480402c181180401907540454160086210660b51040036001200120b1401ea801c1c4c0d41030141c010004131043c812403081c10346a001c03020450407005251484411901d008180107542c038605071038540c00001e9518030452010710036040042c3c0200e5000420003109c200d608182071030400d1001d0542001074200204140c4c58103620780000302600d038080c83c1c80d8207480341d80800f4600a41030310701800010b8007400003e1583c01d11000684d421103000807002e8 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 788261996 1250 788260746 788260757
    0x40e010801111b0c030d02030d0b040204150e1302070b01050f01030203090d051321050f030f040e0406020712030b0a050d08070f060b1e0102010524090a0b030a06020d050708070f 78
    0x28000740f8035203006045882194940628200168000c0d0004000d040c00d510841c0280321031a02e800801049005a105000c1403c42e00141d4182c143d04c2694689401e140c000e049024080901c1c500ca4204d030030100d001c640c20211000144a80d1070000040011144e091901390701d0740c40c20460b100c0d1241411185d6109202000c03415496403191128020094850740da02c0ea001142c070a0f60b8070f00210200303441078a1500030203210341c41451001c000c8410803000c4130603c516043c940f01e1b4481002400510550300580c0c2030092400003107462541c94150600f43e070700428a00740c4241004034402280c1d0140e40f191500b440c418000450205c02e0311192900500e041441611600703050000d40349079aa2913900c208840443c20a5081c80085903100c2c41c400e80c0200010307540d015868560300e80d803c86145458a08195410103450700d400e074075138084540f54000c039a50b150040801e21b001c501060031600381e600402c1d0b24100c0e05152164560202051504000b80d003171010000d0301c0b41c40d00728110070402a = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 788263246 1250 788261996 788262037
    0x21f02030d0e07031a01030302062e030305030a11090d0206031008060c030403030606030c2106050411090f0402180d0f020a0608041101080408090118030606080102040e01080111 78
    0x500038825140708484506080c407001031440661501c6951601085400e4400281c50224000003805801d05036541500144100c0e280d0300c1c2440e40002c107070300500b0307822100c0805810100210f140c01c800194402d0700c3d49900d03424a0204031040c1c8850380018001000c0901014000359a518103e80034a90161242952611007018000c041000c60300056000d216100900041800d403070001c40c880c9001c1d9030104001c549598044054441c040c59204c00a54040d4140c4035056074402c035003c2c801c403c440001480ca5840c008502643c031208840301000c4070114071183c0505101002c461045000c0703904615003641501030004654a100115005440c6018020108100d004004034072039002000c0440e00c41c5e450000030034040701260110b4100550400140c5d0b154080d903000c034043c651110001d4202103240c0c00440f2180c5018155843d403500840d1b0000c00326041c0e20818026162041c00580d48030b040214820f44d40e041a8888400c13170385031840d017110728009803040d1000703000c03032151546215 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 788264496 1250 788263246 788263309
    0x712060b1e012c1207031a01060c020f2d0415050d0b040c1703090f010f08040303020f13030f0605100e0c09150a090e0c16120302070f03050c070e0402 66
    0x40c95240c0440c0c001213000715000d801c220004034142141d2140e03010244008018000d205240028401d00010800740e001c8407005140c01b0344051034858010b48071001d0031003c3c808c207544a040351410308000a18040d100091070601d0b0041c83c9209101070015080e00346058080380072035032031100c00340c030080c10107000c20100a0a24a1200244107041041020102d041e845545a900401e0b945200d00d04500c40b0f1503841d40a170f2014030320750301251503591035070742c82d9101980658801d20807001d05404c00c0040025401041e0203000c040c500860f0244924221490048200d5201030310540191020b08800c000043c00d200710541d1102c0690001e030707182c0600340089001c2c04c0e40e110029074019070120b2034001003988201a1021a80182046112601c8036603001007248a40603c1d0700d6480c2c03810a4860124030b40800348100060585001480e06031182c4070101e0214045408400203200020760381c20700c1d50300300120f50103000640500c81d081d0030b26070300040454603500d078000c81507003080c61034640c0d8 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 788265746 1250 788264496 788264567
    0x1d0603010914030409150e0718080d0503010305160509220b0a0e0d090510051e0309030a020c0303041d150a170609010209060405120712060b1e01 64
    0x190302914400b0803544940d1007684a03000340c05184e40d243d213080c2e101510220100840c008503003403410000c829449140c402c030b030124a194592180e0070800c8500280d000001c00001d100c2c1c003465640d2580341c0d410740c54100e0410701c1030041d05151006481050207296129010290000300c500402c0c00c9409450b00d020740d507204160009002824420200810050305410118503010054103503a0201c608590940da045142d00485030045001700411b281980550014252444c804822031008015203c8901301c2e580201c40f0a201c6400205070851340d00e0f010094060b50190444c003441c20035040c02c040805c40c51040201034910301840340818800303918490300040140019142e0136809445052076144013603288600e05942c0720340070001c1c07030b42d107010f109855241d000204407610b000e28020070000c1901c00c0c000b0301020385c0100d500c005030b00d13804000c0c1184010311800000c41d01c20074540400803105448441210000c0d0b0001901c82c3d10780e40940072020a107002e84603505003801e00b1225a02 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 788266996 1250 788265746 788265761
    0xb01090b0d111917041e140109080c1603050606040f02130f06232a0604050105070305010518040b0a09020d06020717040b12040609021e030c03071d060301 68
    0x2d940d0000110380041c02800c0c000c1c1c48501015484010040303814a080b85410390084401a240a486044510136411a82c0010005a000e032a0304201c0d64201c03202182101c504070310440b01402c0001d02071078600d006200b443c0600003540c80300300d1814a0358480d1500e6600c0200039500c2503a0342c002c000040c9110340d05842c0c4604003600c00d807506648991101d00242901e0180341c0100f460003001410344041390f401c1040d4080c200b00000c0c1810354000311a0701005441d50080c01405140340c005482800422030580f00f01d010340004105824940030103421144107800103405000781480d100144104603e642d50482e40c05040e40c1115646d08020400800304584025880140d00640f501401459005455868002e44401401200701c0740e28410078804c511442410020510103e4014000002040d40c4940203030008582401c0710740c0000e0058032161001403100a640310000c01e2800d08020390500a60f06034002d20001c5c4c203100111352110441d41c00e044541c220b1100040d11303528203421816 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 788268246 1250 788266996 788267021
    0x40201032301030c1e0302040b03071206020d0c080115110f07031a0c04240207090e01020a030b03241302030d05031f03030f0c020f1002030703030b03010b01090b0d 72
    0x410140004641021071000e00c0f090f241400900804a01c03c15840300781c1d408115000c240c070004520315401d000181c1818900b680c0d0600074050000381c1000302d04c038030007040c0d0301c19030300140e0321480507084104a45000b1380c0e0f1001c00003c01c1c0107100700242211900d203854081d00b0008044964a011035140c07001d070b0000030310385018481000040000c20824ac40a01e845100001c0d91a036a50b21603113028080d602c00c00503243c55400d01000a84208400c41c0c1b1803c4540c41601ca030544c072403e0382416180c1c40da445c04038582d070010f00a03d48035418410107107540001c80151411140e0f0105e40b51400710700545c038424886032400420003645a05e4407482d04c1d981c0c00f80a0b00c02080c24244040c00342c0e0821559000a4030300c03c40d10f0350141d84812081425240e140d29020036500118204942c5007606100898028801440c2240785035510400e6104c09100c5600860307940e181d900d80141a02c0558403502d0103a814406022826a04030031024140ca8060381510b4079486c064071400702402d003004001 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 788269496 1250 788268246 788268281
    0x412060e0d0c050c091302060d060905100306051e0a1109040e0a03081303050426010905030c010c1d010e0310020304050d0f080f1801022107270501050304020103 71
    0x400710981c0050503618018022400e483c2e8002102013880100c00088503010014200503686000601d0030f440a40820b24400c040085c1441d12005a801168401e468511a00301a48010010041c00d03001d0164000b00d00d038a80f051140b2548520420308202a0030419a10740b9003c007902c3e5221b02c1d0084e51140c41000b4070502501809000300c0e5101c2b0700e441c1065000821150010b4000036442d074034424490703410350300c0341d141c90310f04480d910020300c030340f0310070240e40c40c01c2003400008030700c24001e200d100d070b0240026643d03d0000400a6086408282945003481554140b600d040d1849240202020f1420700305508880100c600103801d00c0d150401100707045102009000a00c0000980300d40d02c40140e4903001c03030745c446000703058540020444004a40200140000d140544800541e10b8098821000941400402c2d100c005025000e044504400c010840400400580c400c1d072000b45402414082c4810354110b01d41444007084602480307050010010220b401c69220764895a080c0ba82e0b1040d8 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 788270746 1250 788269496 788269513
    0x8090424051002030c0d0e0406121a160219020301090b04060905015718090b09041b0302040203070e030105060306071b0807060501150f080403050412060e 68
    0xa0180d500e03074099a40503038a2156400201c40c0000211100141a900100888280384030300310340c1107801012040c0c12075280c6c4400110342c011403048000c52441012000c0c5841180312404494913002451100314601e00550a501da030f070082907480a0062048081070007185500103e4050203100b031009199400c1e00041209019a5502001038075110307100030311800924103030031001080b80034407c095499000808011103c40d002606800b820805030405d000e40c5040907504104130405138590106d130074030502c4c025000b64a00c0d11070140660040422403400080d0106185000c020802840d5401c1040c900d44416080101e2100855000380150f5580c501441c00501c0840c0000705507000f076003071401080b4549004940d8030310541803139642c40c0d00d8a0001d0b8002c1200385595200b0b442c03aa80030040a00402c40c58010315000c1c01c4d520101550b20f1035410130050080e641c0300b48500400c80e4610600000070341c4002100c1c2100c0714030501181d004450304002c4021306400040078503920075000c1 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 788271996 1250 788270746 788270801
    0xb22051002070905010603050c040b030703060905160215040819090801060603020c010b010e0306060d080c0a0308190c081b0d0c0f1107120201032f040e150a03080904 73
    0x18250143e507141441071046980e510b2040d029a05c00390317410400f1500500042c480160301c00d01869000d0180c0c6008100301d59600c6a02080721410fa40405000d403001c45030b1410300e501040307174903010780204c0c21052040c60251110303055801006120303003088003600c0c0c2041d102da129981200150007004001c201d102da4480b4050001e5002c290401131550a101d81c3c0c81c0d107076018110210440070080c0141c0401e5681e041005203001c3d00d60303421079801c0c0047c44201000c000400240c04103505c25151400795042c0301604002540302d82e0258075500c2d0038900074124041e80503003071903003064001034082d025401e0303000a10898014810701d0b0014515081c81c141300294081e00c2140441881e031141f5446860040100f41c540041d40621101b04480540ea0341c0194820303030243c1d060384d84220303020f03c000901400400c0c0e8a8019000400000320101301031140000015205070002000146004e0f080070110200c0c00ea00c01c6448081c0c030020000c9507201c102e4590390008410002c10000207503442c10102c8 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 788273246 1250 788271996 788272003
    0x10e240402190906090f09020f040e0312040c0906050607030e09060d05150a0e030901090b0a05090a0627030f0b090f031b0705011b170708070602070201030f060b22051002 75
    0xc00d01480c170f410410040c2031203041d40f10380703202e903500502040c40c81015030f8284000713032007003610b0300e001440100300c0d224144140002c140c0c0a944941f42c2e000d8801c0c540704030003064400d20b4003d18410502000b10100203600003008004050b000d0b6080042940c0e0b01001500b147c44001300604940514140c02545c014109140c1d032280b05200410022186400e0000e903503030003103c09450200b510b801082c490f88000c200500a525040d14044d840c10444401040e603a0301e0b15800040842c4c1c1003054441842d8001c1070b2200b0400d000c01c91400d41a1450b1212400c01910702e40c00360080c183c200c04108021014407041c281000040c0490ba517400b90281c0030250b0380100240f500744c034014003401048540c45000b00740c19422406003200c1005004d1346074880815207030040314409410800080c4005011a03001d000c05601171840140c880d0101e0001405940580486501d00c91414400f80404030780320090f02d11103200018002000b03480d001c0c2100d41c8107010340080350b11507404002c00034a1030703000 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 788274496 1250 788273246 788273249
    0x1202100e011407020d120e010605121c0311030604050717150901090c14030a020712120506090105100f0e0a080601060f0905030703021c020a03080309010e240402190906 74
    0x21800704940b9602c03840b040741c0301e907002400d1790002510070f1815442111075030491050a8522000082c0155481c4000303410b020810061f40c1c41a040001c5503081c080103200c2e45c1e40c1ca001d0f0360170140803414000c80045102d100040c4183d110390f80c1c0d6804281d12038405c411080b07030f10381074070303000203140c200001c4905207814150b030070030300c04c05441001007440c00460180083c0120300d0386405540c8040c1444011a5800041c841c0e03c415909120382c00100c1c95000c2c00d00600034041e240c0c02d040c1ca031030071a00001d8440c018151400b58006c10010001500c80302e42c0d2503c3d00402c0c0c41d00d88581500c40c101200c8041c144200b069002d03210b4000400c0d0700c100411100e040300c41c191504204080c2200080e19802c5042c8919a80350300001410030150400c41d02861200302400440c40c003600c00e84c7d001070000e9540c0d4000351104400801004540b9000344190700c18110b14100510202845a80e1004d214051000042065a0110124046403502c17102140b0095180600c4a101034989070f030300d002003c90703 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 788275746 1250 788274496 788274521
    0x60c0f141605030111070f0314120601030e0f07031514040c0602010b0907021b0a0915060908070305070902220b07062304020d1e0311281202100e01 65
    0x7081c030002d0380780380510600c03642a0401e4401824203005880c2e48000d40c0c40c20405030184003c608110f04200f0304000100620341e81405a800e1030f05010000408a8142c40e041c51401c2d403110025044150380028000704490b80000251218403005041c3c0e0701a04031010a07281015280741488204508e88203800192b83c4580e00070056108604208241e410301603c1540142c0c102e0071148814038070410b00c84801c0540500160761040d40d078400002140c011501ca0b0340881c040b8502401215403240384403004290b0b0100400010342151039860300c501c3c20b07120301d400142e07002600b1208203915540100c568050300309600c01301e6586140f441c402d50702454007101e10360301e802185070400441d0300940070503001002240350190303110340c00d100fa0000002e20645084403005c81d00c0b100020214011351055110b903403940380840703d49004600d07011040b010501c0c01d8034602c2644680200c014104008181c00c04035032080d103c540c1c80182c2c104000e048000040c5401c20014030070400054200d00181e414 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 788276996 1250 788275746 788275783
    0x1e0c0402040608160302071709041803110c040203010b04061107030203012c0109110609011709100e12070f0807120504150206090d030e0f06090114010b0f04060c0f14 73
    0x14940c0205d04921031402d004000800c2060708681e4010b482d4003810a00c8405440001c0801d084001020315444984c8200c00090344102c82c07100140c401d1209113908001503070f003036045504000401d0a180501c0c09201e040107002140000340300360030003680c0300954000d0020800552401120000522444001c8049043c0c0031002603d001051240c42d0529420142c1200e04003821070400c44a1743c02810710034100108400110291520450050300074507e413401400046400d04855055a03038880d10382519420003151041c400410301e007240d18080d48581c044c10b0170411458042c045001d20b0001815081d100210817000b250001e0003001924000300c1ba000c09021208022691940e0840f40c076130003600b251080c01d00a501a401204070001110180c66100d000760340071902d1720100302c89905042e0346034084008803490034103046024000d80c00e101403a0003480081c90b8518843e61080d90308011500501c40103000501c1c14200001c0ea002d00f03100d9000c454041d500340d8170903400150100800 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 788278246 1250 788276996 788277031
    0xc020d0204110a140a05090f060d050a060528050f19061d030102070f06051e090d1106010b0a0503070912060f0f06030f080711060a02010e060f0601021e0c0402040608 73
    0x2041303c00c3d60501800c40d40c3e4030b854500c0060a102c1040700800020383c1049040c000900c004070235000b464440c038618500051101e20742410000c02000e55510308c0f560032a0361030384400f0354039894003803030640d80c09954964000980c0f001003440b10445015030300300748081c44008075501e58819170740c0c01c42288014080403845034043c02c0500b02e10813000300810480030aa80b00c000100203400c9a94440e80c540f00072451922042808604407000b15401d03446034004070a4880b200341c0100c0742040104600d001040d41d98103002141031544185144102482404000601d90610480460000d05207001d0201c00e6a01a40b6148015240d40010702e111281000020320142941d031095404481d00b00083c140407002640382c3c6212030340060307000c0e00d15050740840c90303501d600c0306070003001d5460590307000090300100e0309882428403102074009800c2d20071110134402141e80c0050103a030380340102c1e120704556450101449290041d45a0041c3d0800e00104002510b036420500080c03050030324820310003402 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 788279496 1250 788278246 788278277
    0x1c081201050f01110606090a2912030a0914030c0d15110307120e28060e03070f060c0905090c0a0207080706140c0a0b010b0d18030f0c020d0204110a 65
    0x71070701c0c40896455605c00400542c0034500540240c0d0004034501c1c00040404005640c80600001640030303a91010703031000084400d0500740b0034460900359200145040c0340402c03500400051951144902007101380c90b1501c899078041c003e141a2050080030011040c120345040507400843d4070f10b10b031000389040f0341c2140d0049400c0c00c50b4480c050035500c0c80003200e6000003110080414284203c07a62103003640154100b038400300a02080d00c034081c40600200c00610b400e00980d6541600d20685030410b010840020f101406030b08000c0d03900080c08a452a4216411940d50041c2d9106980c828800014000c01d001c0c1040100320b480069429144c40940b560a030556401c400e10601000a505031580c18216440c1c901034140326080109941e0416001c0d02c803400000c04c2a0441d0312482000a101141c1d0522403007240e020000c1c41c45c3d07842044440752406483c141d03826412109004a10a51604550380d002c1803030041d541c028000c11010f40b40141c0404150086a02c0c1000720f440c031030503507010 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 788280746 1250 788279496 788279507
    0x110609010501141002100f09120e090f063001061202031005040c0b031906060318060c030f02070f03030612050d0e0409210f090308091c081201050f01 66
    0x1a288030b0f0b2074000b48a035840c000e1004041289004108601402d1241e0304142550b0051800301440d1100114120560b41804500c5d4100008000305200c92804a1790294950860660b0300000e140d581e0340c120741e50302010800c40342074a9800700c01d22914076440103600001100e06604c01043c00000c12049032071790000d00c00c141080368040d51691018a00102e27080b4160805503200e44181c0c17551403150381e079446901e03540c3c0040d500700f0f8001442001c00c000340542441020011700d0340b40360900424140060110b10207192101c060012612100f10a9039075000c1d4000d00101800c41c90119034544417401c00254549104104400107030501c00b0000e66440b009810104244d00107014081681940300d090342e00840d08071419070425220344085011903000e0703401024481908a28007a0b201d00f07410010660000d55141405005525605002040c880300039203004a90503035440c0d4030040c0800004041e680c0d9a0801019030800040042801021f02c600710304868090302d0001e0400d0250b001503c0c0c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 788281996 1250 788280746 788280749
    0x1060e06061e03040609020d03020f12190e061c020d110306130513020d12090603060812090607061d0d0201050606121009020406050903100606020604020628110609010501 75
    0x2c40c6842d0801d01808800034000840d00640f18a000091080e869030102d05400d50351107041e030140c1c22401104643da4ae052207100300e40b84030502e000b441c1c00080b0300d8458444240c02c100e4030801c03080b9900c201c05611060708842d56107004401e40144d507032900d01003001070b512100241040c2818281e80342d168030280001d4a00445000700310b24079a1607000c070184001c01009100a00c500503510301500540c54085500d0400c9018800c61099411000c40290070450b45902c0902094908031040003c41c9010410046641d0240784440d500e042c00790000b00103002c2d40b02c02611661800039500403800c1c0000f00b1603204000c10041d03518101d0b490034240e007260011100950031100410003198008140d01c03880b58082200d100125203c1c2c2c41e4850981283c000b0341212001c144002039245c0c1e035280c10801904043c0f2820800e0048506218000b5103440010300f000303005060111307005401d41040e0100e104000b600045007020b4940d0705000600219200306c01c40180e0140b1400300d00c0c445418041d803070 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 788283246 1250 788281996 788282017
    0x3230f06100f0b090d140a08070303230603070b0a090902030c0406110c06070b040204241a190e0a12080d061202150a03021b0d090b03040c061407080c01060e0606 71
    0x2121740100d910380c01e1050501040641e11400b480d901400010781000c00741618078001d90b400a5480e01d50201d0601f6103080180000c0c0004c2070004006071564000b6541060fa00d00240c7d040d2a041101000e540f00c0707042d500460f1030f9500100c04c011504140c040940100c5030329556444081c24034548254861131b665081541204040018001244036401e0058120b0b1002e4000113108492020300c4420310107100f112241004000700c10040c07503454400c0030b00e02d125035110b01c502e030076549540c0f5000c6400c4501044240301030344140140c542c2c1c2e801400c40051011490400a030441c500d0982803a81c408030590b41c0386072400002080e41003c01840081d8158040c0807035030700010340d421120154001345004401c060b000c100000c114000e940710384044416080c0103001403042c000024024021740e800c900401c0c102801044013142444440303604031842e070304029550506000d000e5965109445011b407070440e000801014150054ac0800121800c000904009885800c10448a0301c82c3c6c43c0c820 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 788284496 1250 788283246 788283259
    0x9111512060f0105041508090f151807170d090906051c022d13141609240e03010b0310110409060b0a0305060a03230f06100f0b09 57
    0x241c10742800c50900c109200141822800d142e90f0300100c00d101184901c207480081c505074240f04000804020706140803410f500540301d0f460702c000781c460390312500401c810f6178462510b230340c00700410b4140150405001c01040d2880b0300b4160750070282d9960b08100702040047c7c0c0104000441c4078191140c0741c1910401011003015440b1034180c20003649020f2026070740214032080c0c030555400304034107101d0301c1e6201206502c4040c070203404104054290340d41c0c80e00a9030621811244003000110f41550000003040521848000041c040701e0340a9160458042445031f1911b0030241c1103140d9090100700099070b0f0311643e13424900285402e8950078914903405502c0061911800c5d00990010741d400413200001600341070303454004a06031107465120381151000020680a46035041c00740c540c0c030007002c1d500000460b187d0b51f1900040018651045400003082111400c4c2e541c0500008500d05116012900300f42890b03054143c5071000ea215189101007101d8002a0000400c0d098881d607000c020f010 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 788285746 1250 788284496 788284501
    0x601081510031e050f060901202b02090303180f010908030a030c0519090509071403040b1e01060306180e0601051009090603060203040c091806110c0109111512 70
    0x4400954010030041358180909941d02c0840c800810020744909880f0b0000710f03ca4a00398480260980c034200d82c10b015540030400c074507140c1449241c14445d103a081b0003203100012000c45260007802600b0b1103640c140400110410004084201148240c070201c60344080e102c4540b0065a04c1e4100b0300c42d0151541040c07207551512030080d840b140c42442c40d81060ba00d4282d09641d0310f502005801c400002080410a0600890801480c001d074808044d081a82995407201c6250a0131f000040c001813070b00c100c0c2d40015000030b00103481c2c40e01c80001e10b41c414041e544c407810301601610781c502407110b9a01144100300039041403030098411845104000e80410303420702043c0b0802040b800c08078002e110140030f0004000da02d0b4410741c0c00446c024480183c84e030406180581c0c042e003403544190340c000d007040701140704600d545071034031034860340224002520b4100003a40c46050088071910306035940b0b4002c1802c14400c80c1d82e020751070718030708a4510078050400c45d580c101c903005505e0040031201c0e10400 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 788286996 1250 788285746 788285783
    0xe150a020a0e19080c010513030219030b18100b09010e0903040e010b040e1602060a0504020f1003050411061612021011211308030a0608060108151003 66
    0x700810041ea01c0c0c82d100700c00706003000c6034100001000e82d070b0080d100a1402c000320070081c45160028402480c2031468103001a98080d1071000c50f0101034420143e41099103086881901f030700c80110360060780952145040724003c603813441c1c61081142d660103440030061905074a44900b001c90344c0000d02c0c401c0f890b400c1c0580c02451034002401036005100810000c03e42e4015070340103034000c2c804080720541e901d00b403166002028502400c1003041c254241098185550041071055000488800c00a0725645500001d01d0380c103000001182c1001c01c1d0148447c2036a0306820461090307018005c01040403003002d00b030001c0c500c01c01080380c2c00d8840c1c0b000c640c40010303255041c5000c10181841103409068801a11008440000711151204840041c2498000010541d480407138807610400071400e20f01511910400d084460004019500000020750030342c106a0000003d00000001c84809684401c50241c0e036000415043c0c4040b03d0f4240080e00403c0848072420980b9030054150480d48003844 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 788288246 1250 788286996 788287001
    0x702150c28051b0309040e0f0d051317070315022709010b07050f0d0c0b0f01060e130204150905180105010207050607290711031918120609060e150a 65
    0x1200f500500082140480f00c0d03a41c2e0051420110506024040c2205034400035403519105003a510140001481046109803c042c4160100d40703141c07503071190b01a01c40761802d013456103a40000b4584840c0f801183e490f851130b580600032014000c4031400004c024007149000340300c0150f0170544e00110080052100c04140360180c00888c1c801c030104c0c0d180092a03901542050700c00c541500028404212001c2403040c2c1c0300106400c01c41c0c004805882c1c1d4100b40e801020000072000742406980303501c1c01040e80c00c03101e904480040c4902115820100c4901d07000800e0340fa0140718440c840c1100c0f101c80c505a900e45c145140c1240e80580091002e0344c5400240007084e005403505a0785120116240c1600307003040f1441444e1846a000400800d19003560007800c483d103101c800c045141e10a10814622500c4042070007127100b69820200040103810740c000c1a620303010f411843d0b9090b1400341220811400d60410782c0018480c0400348002caa441e002d241d901d0300e071040381056040061021880c00030725913 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 788289496 1250 788288246 788288287
    0x50705010c0c0f03150606050309060402013f150e0a0507030204091a030f2a1f020309030c0d0203030703121503050a020310060609030303050702150c2805 68
    0x2501d0890405585a4044243e80714650090310740e111071041c078443e4030f503080c45200c0c058251802e14078154140b240a1a584e010300401c000e05003d2002e5440c10a100882d000900341c90300a6041c0c44101d204030380300084040c24182d000302150034040c02c8041801494200c509488000c862448c1e00d645e13030264040604000b07040e81c41496030030000450307105c02a005002809051000307031000544080e0a25284c400c644840740416006902000100c070707010b05017106610907851007e4104e0404d900062182c10001407910440424a0301141320245c011000e400140011016100400c80c10414080c0300e2644901c000d40c590010050000040d00998014454850360200000e03030000442c10f02100d0f481c2c0f900140c40b10fa009015110451608001001d03606c081c0820070311481c0d141540281c82d00d21507000007420f0685520024450b075208000b001403a041c10050980503081240440002c1d5010b468601c20410341c10b00e04a0307103510901607659604105960340c9280403401808079800980c0c6 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 788290746 1250 788289496 788289503
    0x200f09040b1807080a0b0604080309010f0306080a0f0203150f010810110313211206050612010e0a02120c0a230a051b03030a0e100b0603040b06030a0c032a03050705010c 74
    0x2102e601b4440da484410150018040c100c005654415205001511811100038000100b40c01d2900500c049107021a404e1046039005480c0440a02d07a840024204120b209440c445002c0d003004010201c805411918101c580c107905036000702c40404040c0041c1c1c1d551448145060408001140c0c0c0102442d462541d420300442010315512409194480e4114200f6001000604420611741e40c2c9100c40c86404000c00084826920b410f4010250680b290414070032307045000840c00001d440506280c04440340050758120f010000e1419000469481d00004101c01c0010080c42012140c1d1121071001440c100c00c8034409402c003039802030304442561000c00d424184a86000d9450041d40c0100051801071419400104404542840ca0b615201070b06848400c01c50070105c0703420054484030704607508503410803028000c82da10500070034079060b000c4c80000d1049202d102c000051014452005410a00565906401c440d10321942280d007212400040d1a0342c0221b0b070204400d40c091988541968132 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 788291996 1250 788290746 788290751
    0x1020f010f0204060905010e090c0702011701060c0605070305040f0b0612030c0102030109150f0b180603041410091e260c011103010b0d200f09040b1807080a 69
    0x41059500c0c01e44900109007901d03260041003e04c0035540002c80180a40030a01e401042400d4480000e441490084c0c030109580e00001489420769100d4010510941c0c4201c0a002040d40e69060092035504888400c0d24004c0c0380401045600e44207004060041c1e07003000c40805007240316266a401c80c400507003900e600c81030314100c07441c01800c10700140c100f0110174000161658541110b00c01610761441055011840b400d00500c41c0c2c01144d10500c0a441902c05403503100c00d00011809460107400648603400480030007003208214071681040218800102036801800c03106110b00141e55404000410307d4882c660560b01e070004420414034124062240f8460380b601c03641c60147c4c10f01141d004403812003000104840c0c029824003a25420b4110007480c0762556140000302d68850292070b904420300c0761100c484605e190714001c91284881103042c00d107961601003490320002c690144e80e02500841c10003c02c840f031843e1504903410400d803407880104560380d03441422205d0150023800015113a5 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 788293246 1250 788291996 788292013
    0x10c0f030e13060f05091b0f0703030f020c01052517040620032a04060513050604121e030507230d0807021603051b030709180212010b0102060103020f0102 68
    0x742e8015900144a220f1108074518204020f00c040c02400030305142070321011001100c2070021400c102c5070503495501c0c1c01b94644c1c05a01e01100a40940c24009078483d0021070060300e00001940024065889450f890409000c098041042c0e48013050318503012511502c000003101c0c106098480e842449581d00090200d90385c11a0985048052441291540e0110400020449000b004003020040c80340080e000f0001c1404c07264184514020003040180210b2038140c0d20407600b40400c05003070b00401403500d564880b4052030f2100ea0341e6030151801540d0f003903503201503050303401113040040e016a1158603011803a2560603811085402c00d8908160b03418000b04c80e04818806181401d01039a030b04542c0e1300344040c00030701d4114280c03030507402092900410000614000703020b201400c22004504090080d50700042d048c141c560780000b480701c4c2009080c03020010488400007401d8400c41d081d062074040c0f015641d00700d910301054140942d010600501c0545441902280807100520490f43c462 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 788294496 1250 788293246 788293279
    0x120412060207050f031e09030d1101090c080105190b0f01050c0f0d1d01080601080711030c0109060b010201140f0103150209040207050c04110c06010b16020a12050705010c0f030e 78
    0x80d04d940325001c85501301058440050021141c20300a01d0700080032a030508840e000080e42784c00e1090784e502c0501000c194242c04010080d08090701c80da0304aa5201407803a07a410810b806054200d0b0345054001280b0b18541810155118142c80500040c000104000024005541c2a0f0040300340300c1651003250f851200090007000002d00500aa0b5200c043c410886809000900d040282c1e040c14000d0f03c0d801c01006036402400c1c2a80861146002c402c044640c0d60310a085103e2109900040d50900c010403051001c1c54100d604242000e80c0200403040d2018440c016002017540c0740d45444080c800104007090300348254141e20700d4902001841d10070040c0008003280e0050000325025001200c041c20140780900c180c108201491081501c7c1084c0d00400685441c0705009243c0741580108a514441c07060071103074080594040d00c880303003290304c0d107120fa0744a540306103044030700340b07d040001f080c1c65101d1030140e13295652044d0403040d480c01990341507403003c52030303480d094006d4628500075640 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 788295746 1250 788294496 788294503
    0x1140c1b04020f190801050607032115080f150106092c0f04061406060d05090a08070302060a0e070501050f1c050a1d16050907050409022a12041206020705 68
    0x3405050403104e00d000d085006001c0490503804144503d209214040200b0b4005036040003030280d5500760000415000d88401c02884074100340303044d40400d02c8011904200c0018844400c0528508a8490000c100070300102e10300300340201c800041441104126441c032690032010050400001c03c1c0c01c0300003440c041c00d00510200d03100e144a080e1541070205102491041003202c0890b461030299070318100011034028807035983d0f6080301958030000600148014032400011651040303040c0d036540030711308000350369240644016414514060213100001d00008000003142c4068407801c3c205a01c080300f408050b00003a010744400c8600c1d1807800748400031485030a1082220000005401c0b00e18090240d40340c910084003072030356008c0004104601c0c0d45090360f1040b10011101c402c101d13510007404681c18040ca42c007031a480390021800e14440605001c140d01e040c82034560003000c11180c4245160b1b51107900002100755041007006100781004880c503641180e00441d405403a10b90103a440528 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 788296996 1250 788295746 788295757
    0xf0a060f08070903150605011707080112080c1b030f0105090705060a0e0301050a0e010e1f0b030a060c02070303080c0339070501060302101d06030411100e01140c1b04020f 75
    0x50640e600c40087c070003980c00898501d14021086503c0155151951002d0310356001030040042c200c00c00d00c182410440100100c4141101d564140c4001070220144d04480c1d5a07034001c4c05200c3e00a24201403000c02d8140700b414821f40548004080e01c502c0d000a01c002c41d4040260300c010408808030100300c640f4240695030083d1603ca0000461f00c004110503401c540b0025820703402c44d00501a41c48441c01c4120840c42040c4000500154a010303460000b841c000821400800b4a802c0240c0344046036008503218003280e007e91201401992026180340c002d200865280060004064405070000006102803405100310021520308030010900f001c113a0f04002000c40756030391522000e00c1141008180301c02d2000e900e0428090080c501c0c4011070001015007040360042002100090a10028955160340c9a0002e450b9600340301220000400c0d000740720b848640414240b208181c511490f25080350380d1000c2010141c06002104108100c6402c0048a01d0f64401d40901c0003813482c2d01d02c1c1c8000d20 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 788298246 1250 788296996 788297033
    0x40302041a030d020106060806061b19050601050a030b0f04050c0a0305160b0a0203071e02040e01150e090d030513140d1206051318140703020f0a060f08070903 70
    0x4410080000400d840c2640c82e00883d0210b90414404010840d0000e068a82005003120080c0e110f91803848881c60501031050618240d203d02800300680d2010b81941e030072014050026200c807603032140207101c8034160034480142005482400078246ca503142034940e0704180b05805840ea030b09054400103c4010701c540080d2070507002402904105031440301e07164010101c10103001d09004440704003035224012050090002c2e0f604440d2000048c05042c02e0402c1d407a40280108005401d0b02c2c082c0d8001d00c001c0e90890329520b040c00003c9020320206040603c248a00001840d001c6041c034021005403101074212049541040b45000001e50b10545880384002d0300001450343d1000c03548020300d031002c20800f01c2c254500d4414244540d40318400080f28900003a500131510380e0484496a620240708100500f4642141412881c958408500380e02124000c4402c0110101e0f0001080b002100754030488001c075024003041003095028040382a4406858241034540039942d0b15400742c00900e520155 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 788299496 1250 788298246 788298281
    0x706020f0105090d20030d02030403030906050a141b0408010203040b040203071502060a0c2718020315010e010c060e0d08010905041a18010204090c08060d0302060112020604030204 79
    0x2500d41035024440e042d8031608210080c4941c681881000e031480031701c040101c01c5920454142610300d18100110b94000001080031552880c250034010001c0c081840126081800c00010903210502030150017000a802da100c040c15495540c20014030700c0c0c0341c0c55041012001803100050542c07007803025520890040c410412107140500c1054140311403078111800769621400c8000207141c0c00290b0680c002d0b007009001440c004c07104415074000724015461007491214250619043c0000b0440c1e40403a22583d03400c8031034800e2459644260b000c00c44c1d650135071040c4021300d00580d40c800d0801d480c1140d0103043c9030b1190400c68136100705440c0100340c1c00700030b44d00680d82180070300d5202c168a0700404a5000070045424569070b031500d941c2d8219a10440e0071045030100301100052000030101d816100c000710750307595840390700070007602c0614200b03004141c0c0340b00040c2c03840c01c000d01030941d000e9155020f01030681c00c00c001031003407203041c030000d03a08040c0500003c00140c80d14400c1c41c101d0703030004042 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 788300746 1250 788299496 788299513
    0x60c1805010e011b060b1f05181f030c0f21180b04080301061d0102030a1818050105030c030d09030602180d0b0603161401050309030f0a050d110708030a02031008070602 74
    0x1413140700c11082540399401c0d010070311f2401c03050380e000c0c060310b5140541c0b06156030308240d02c03400140c81c48030507808100214001c4022540154050f0f00c0264004510380300c00c0c800340000e140a94442821a95084016030580009030380c1003060389c000360788810b660202d142620925155082c1e01c0c0c10031502200d100c1c10000040c0010350300480328480a003041c012182c920b6941c140000d460340640d804081c10f115848040c1e00c5c00c83d032a10514400340c0740c00301180c0158044e0280c044007a141c00c1c42454068060034448525038100401d5949501e040c585075820b0481c80c5580d004002d500440c1004088081c100411200c1d44c1c2c0d8800803034609001d104410160304100040505000c3c0c2d1010020344001d064404014405002c0c10313a00c016030003401c1c06602c0b0394900c0c4803e810b500c1881c48041c8448800901100d40b03036045400f46c0214910000c0410000062064441c0750388140b0401810f40070081c800507030041d00f9a0000e50b80a811803010b1409140d840d42c0561500101c0d40050300943c204040 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 788301996 1250 788300746 788300749
    0xa14010618090603020607020906040908160201110c0924040c0905040b0409170c0f10140711071401020a120f030e150402040903020a1e060c1805010e011b060b 70
    0x40321002c0e080c100b02c1000401d15550028400e4812224020b020345002c000241040e501c4da07000740400ba80003030481f42d45183c00f500a2008044078542240810000340359045001c4000407602400940a4960540b0391950110400c0750000d880e2501100c0c0b00ca60070003200354486010300c03103100c0210744a079448203081008000546070114851070045142c44040c00c040340c0b04c021184600c41001a005039508500001c9034241040d00d481c140c01407060304400c81c0e0024880d8400000c40310000c00002c2c031516102d5084800d1820403480038035540c0060014000c0040501c2c81c5881c00758140125110038200d40d40740401c0c112071b00880c2020070940444a92016018015070800903038003400f038070b418140340c05480e00c2c031034001e40041d0250340c0d1110803c0416008020b121022500311500d80c0c4c40d40f0901441195810008000715040ca081c0400104203d01413203104880b42c011a00c11002182080b00441e071400001400c641040b0081000e04c0c4c800d160f2101e01c400c424010103010400240210 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 788303246 1250 788301996 788302037
    0x8030106030513051c05090a080a020301110703051e160321090c0b0d1409010207021c020915031e0f070b070804120204020409060815100f0b030a140106 67
    0xc01125029a030242070304001031020a03255a0040d0701441000c021812a0040b511b034080c543c101070300a0f59401021900803000a90322a1785071080b00244580301c901a5407030081d004103080180030500910a54150b441c442c070603e0101c8040c0d4200d20b08041c2e14072801e000ca402106c20a9010864640c3e0402d049004140410b2091520400c1404000000e54a0720b01d025001c0c03007040170741680400c0803418203026422581410b078203810b03400300c20309005a83c94002d501c1340c503080380700d0054000c14441907018015401d401e2a0000c003d19296614a5440d40948250b180c8241c1d1500030008021524810b400483d41a0480d0780000c00100301403e00b2146020000d401c2000300031014004000000c4844007100d0940c3c0b2800768030381c2d1040e41032011901a002d25040b01604034100040401c907c2e8000400c0c030f90581520b01910030340c0c4c03103e910181111030715000300000081d0380e03403041c007280b41044000c680004401c0c0001801e085000e2911400d002c080e0401c00002e48001000c00ca4550b140 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 788304496 1250 788303246 788303251
    0xe010201050f01080d12060305010c11010b0901120b061504060306081e0601150c08030a02090f0a0605040b0c1501061e0206060d0f15090c0504060f05100309020a12080301060305 78
    0x1c142c94001d505100032107a494601103400400c0107090b00301c90300305007801e0b006071004542c000000c0c0312944c03649001800c03040000b0511100c561820751080c40d6490048040c604a5001d0303441080f24050b60b80303034284e40c01002004c85410040d1003140f5134008980c0030050000708005d66001540c241000103c1d07052200440304002106104c0c40e101c5000c0202040c00da0440e0040c21700b0040d98513640e1001d42c0c6100714a44085c1111001100304400100c00f6001040c21003030840751080810601000c001041c0720038002d010000c1c206000030700110f1030400090403404940021a088041c2d400b40500b403282090b00100d000501e0401380d20a02d6040c02d208013003c0ca03190020305080c0c40c003a80400d0b0f5500c4600360160034804901041d6051004d000c070304070010955040d007403040d1003071810031204c0c44006118aa0003107142a41c006212078066000e6020b0341d100410003140c1440500e0110f0142200607002e030ba11010300d13500022404802c1b0020008603229101e0b03161a50300d4210041d0494000 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 788305746 1250 788304496 788304511
    0x33060902072d0b04080307030501080f0c04020327010e01360c1d04031d06090d020a0b040e0402100f0f110705030f070807080c0607060b060f03070e01020105 69
    0x612862000032030300414082e248400c806081d580c01d8151a2040e2010072640c40640503090759004d001c24050a50000c6200d030074503840034403199070780d1030701540e481040300350317200d40c0f500420181282c070320345a0000c54101022092800103c4903034a0800c0c40240c0503902c14900b81e65031145040701c00d40a002c2e40c0c80ca41c502c0000450b249901c94070442c00481540031400d0200f031a400d0580400600c0e08001d406440381c0e40341510500002169040000c0c8103841c10b0300804c0d4207184507100888142c10021118001034421420800c1200a0144905424030b0881e8412056080400c1c01300c2400003130802050050300b0b01081c0e0401e0300500203e11190815441000903462a80c1401e03074003d81d888002c0701040c40c000c8641407101c0036243c01d005d00c0e034001903410b020306110b02c068840c0c0026503100b50b4002d08103441b082035483d00c1242c0d50b00c0460b0703911504860107100c27400208105501042242202803d07417031418201d413520100660045070b0702e03000700318246880d5141c2e590921680303600c0310a = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 788306996 1250 788305746 788305751
    0x180f050f0f04030f230c1908041202150711030c040c051608040e0c1c020306090f09010b0a08030406031527090c0b07111e0d0c0f060203030f0a020322330609 69
    0x1071545500600d44038032b004018610f06407150040031502d4841c00041411804840651642450701d8480c05504600c8440752180c0710b080e400e06140e141c00d00c41e02d00c1d01178aa848031031900000550842c00525074010a565810301807200160640100c04c400d84100720005440da5a0700d008905502d240d6050541e80000f6881842040784d142c989802040d0030503011650305041e035641c00c22090150064000701d03a000800301c4000641c401c000006031007643c8281e181803000020040e031a800c83c0c40309219508444071038200e0106a410701844812f00c0030300550010072060307043d0301c0c0d2081030b60f00c90340301c81501c070400501941403015184a04030b0100080301c03030f151303100e4510010314480b80c20141074500c90841a034a19040000510042c0001c00c007410610005a0740c07028080d45075002204d00c0da0078855820001851400d4910840e0303c01d40105420080c499001400507001c68604482142d0103944114820710a00c0c0480c6907552040d00a0380e01402e42d02666400750941e402c80d40700041d940e0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 788308246 1250 788306996 788307043
    0x1505040506030402010c1e051c180e093d0212010308090301020412050a0201080906070c080a0e190609050a06091205010204180f050f0f04030f230c 65
    0x341d40800300ca40142d02442d19078907015490078207101ca10303c07400c0b04102100301041d12030100400480c400e0f841151000c41e1301641003082506541c42046490000300e042086a0140115031810202542001400301180da04440040050b06441900d51040320380422440c007184920111408980c1f0100c2c0a0000b542480c81c07c0800041c801810b0000038403080b80441d4030451030b102541581c0042100101198038026641081a110307100f442c0c00b030b80029001b000150460100040b0341e40079610075034a81d007090080b501d400300244c118038000c0041150581070515a5aa1014030b50000c03140700364400003851604402508a00d078503803001e07010301c480200420000e81c00c2a006411907a0391410055114240e1621703c1c024490781c0c0224680b04000004411406c50326130082000ca10b060104105a48440010f050390328070860315a5404146040000e00191159200c51420a05402c0c4031030384c0503810503140c030f00242c502c032040d0a00d50080768a00d01c800c1e04000c0c00100e00c07195156100c115 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 788309352 1106 788308246 788308249
    0x10f03030f121803170c030408031f0509390f07060b0607140d020102030f0c0a020a0b0903070c0902181c06090606030b0a0c05030115050f1315050405 66
    0x440170320001d9400c404150450307004a03000407104e0b0440d5100d0410202000350b480303104c60944001e040019050311110842c90140c010b0115020401e200c030124076808600c840001108400784807190380404048000b242c0c00c030030007041180e43d40e80705410484050010480c001d500b0000000e81e07403080c00904000b49641c2d20210741510507821454808a090303010540712101907640100201c3c0402e00203800420055807540103079101c5216940b0b1300390b80820100e070441065000010340301c04010070141e00d0130207040f40c44000c5040100c42a80d0060701020f162095008030890008a00400c0050902c4e080080e4401c206014500d03092401c130003d080280f000300c1c1c050b04081c0c08070300c02030800d0040300715a000342d94510b03046a10700441b00b81d094402c1c100380e000380007017080003607100381e206001880c4d60301c0001ca160f400d1a1900f10b288940c50f10f110490400c121040c002031006 = true := by decide +kernel

theorem cover : BRFrame.Cov 788129496 788309352 := by
  have h0 := BRFrame.cov_init 788129496
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788129496 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 788129496 ≤ n) (h2 : n < 788309352) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
