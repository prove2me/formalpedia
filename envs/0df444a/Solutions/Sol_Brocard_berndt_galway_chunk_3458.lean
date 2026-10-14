-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3458
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:43:16.355515+00:00
-- url     : https://prove2.me/submissions/d35e90ba-b19c-4425-be7c-574d551a5dbf

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 621762589 ≤ n < 621942446 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 621763839 1250 621762589 621762601
    0x41505160809010c17060105070f05010b0f03060403140f0405030a03030b09060609061206040e060403020f160e0703050601030e0106030302031234030b0d05060f090106140d080909 79
    0x551088694045980c1e8000d1500d412a8003400c0f5400304c216000041c42030170140c1001c4440c0080ca81e08644103140c110700c7c107112912a01c800764201d030b804aa550351100851141c0340340c40480a08005411005070001d0700302070b680504802140807925070301a40100d505022525184d0a03500242006020f0710f543c40c1c2e007072800070006c14905204510030903001c0040361300b0b070038400169202d9810240215142c804d01d100210340c55034005005960094855551004603841031180c14020b51181c2c00414955080300c640c68203289000880a108a168030030130411784c04600c0402d44c10180368240000c2e241c4900d0700413070241545804040d099030a000740041010790000003803644801c16110b0402d1602d40c0c900c102e04014000485241d544651a482d68160700c14056250340c8034540c0c18001914401c15012900c41060141c09507400d030888070070055080d61440b01c0a5020b018000204281410000b02201403140c41c504540070706020744035102040607000031540391400003449085140f40103 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 621765089 1250 621763839 621763861
    0x81c090e0408070b09070b0d180602070c0f090c080601030e100218010e06040302090714090405040f03120b100c0302070f0b1b012306180a0b2e08041505 67
    0x400d0b085604c080b03001e0014607070200c0803c4170707402d0741d400455140c030f022a1202c2c041e0103403100b0310b28100305400392020540010a030b8070042210f18401d07041a04440e25003140c0500c925081da01c07c0d1001c0e400c100ca2820603036403000c601e40d4070074002d080004000c1d4408012034a0421404074610000c4e100040c4040000c09603800c48084800c240d131202c2c100d241a00510100b4001d40c0310080d00113200d40e002c2003410340111910b0405282540300c850230881c0410018041d100306850030349d03250101c40d410500749a800f5833001d8800c61126002c0c8006510003010035a0070705035400000800c0703a5200c080040510900010004040d843d103121991030711038000189a600000c107250b19410300c00740320004c04106002d115010400d1102c1c00304640d0148824080495004240d00d901554a2400e9402c02114038401806415480030001e242d149800910400104103c1c00c4036001290b074855106c9101e0b22005e00c0c004410901c1c080007117486600d00345d80004140035240b07240e40d00380401c100d050051 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 621766339 1250 621765089 621765097
    0x5100f0b030f031e1b0106091e020705150c0706020403111f30090b01060818030d02070501060302030f0604020a091b0e0a08100b031501081c090e0408 66
    0x2141501d0140305803001030740e82c9103e148110000c405400c800c0b8508040844e01038400a0314000e0b000a01d400c060032024211601600001e03a117507510070080d00380704d240e40c50031600c43d107200f85c013145400c000351030b055503540c0b100e2004a0f035140700c040000d03401c840c40d030141c13240654001029915182c49181110390002c0d0b8401c40fa002d80000751032185864140c0c2058104650035132101c5443c516503c041505602c0101501e41c500c3e000d40740c0b40d40000e00310740704240d480c80c050280480b83d075040820003400d40501070030000f0b01607601403454407103010100440f4010700c0b407040700580d210780e030780303085805000c09030310295040c0070342207101035041001300381d480c0708501c2108c100b02082c3d01c5951003400c9031b1102590500b01500b620f14200054042e101c501b41158000f00301412540c0d54a80051034410291084503040351595200d0301541002c1000303411026a00a50702013560404400503604c000314031340740c0c20f8440c02d9182d103200c030341c001e8031600090084900c0e048020b1409040c180680d80c0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 621767589 1250 621766339 621766361
    0x6050402030f010203160804211e090503100b0d0516090506010302070b0708090a0b07030c0e03060c090d0602120c1b071809150608150a09031202030405100f 69
    0x741e20b401d071072044062084900c00c18552803101d0600c07503041d008803041e1702c00400895005205821050003a196050b1402100f14140e541180711465608003c1605005000d140c0520041c50400d00150ba000305100e1035030401d120001601102540c0041d1402180c000094420301031200f00c0c0f9207480c1041c524806a4042c154144069122200110224442d804c0007400e585180300100340200e2186100c0c6070044d40700001c0f40c2e010145a21555100d481c01e450b2040070a13960940340c40d501ea0050322912600c10110007618075880d01c4000c0003c148505040640704074041c0080038208806507058800c008003040001c08146040040c61400e030781b241c0d00c90781c80400080d20780d0069600000380401600c07168000792441e800c4603011a006000c0a40044800c503003031032180d1620902e24840d040051a980c0000c2c01200b03105003801d2082500030b00500080c030700b48402e003004650803900364950030600f68030051340c3e540c1e6800d01a04200000c8880c1e90407c4c142542c0e1812480650401040c0304 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 621768839 1250 621767589 621767593
    0xa080a0807080c07020a0312020a050715090501031103010e041b0602060103110607020a0504020a0e120a0b07021b0607060b27070306050102060610030e060903041406040302061801030204120605040203 88
    0x244409000f00c03001c0c0183c1d0402507200707403401d006000094690164400804141c01100d0b11040c0d6503131500d04014880d000661549280c1d000179100b281d10001d1040181000e0034100f0499480000041c2240b02c140602515012403902003030030818003440008615807080c0150221070b4a5240c000d448400a100c1a100c4200382c4808219030b15025086503e9250700805983c50b00349008203001c041c0d00a858604280084485001c542e078440308185802e500f604405041410150f15181001080180c440004c5602100c41a12000038020602c551540c04440c81501c8440d00e1070680c0c042c04ce8144002d4100c2c00c028040b244080c0e80320005600428042907600303003a80c88050403811181300d0311505005a02040110380d640c201000c2481c40c4011030715010a0746885001c40c149429001d4030140307603903800060100300f0443c000c0340d08424007a085408925141c65a0001201d501030002c400703004403440d03a40301d407075a806a03041350300600321210301801a05240c01c02100905045030141e0080c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 621770089 1250 621768839 621768841
    0x21509120432010c110609030703030903060c0206010623071719180b0304170c1e010b06030105210d030204030302070f1a03090a0512180f06030c0c0a080a080708 71
    0x88800b0401d0900c0e0880181c0d02d9450300e112a0b1282c1c156020711900044d042542000f5031800c9490501c8100003445c02070726100f084501d14070304030003103c044030803034011900040c0051110940c0326448a880350781c2240004104000350041340f81901c00c050000b0076403101c2c1c182c000310800514010f0001ca5030314590302c10404045001c01ea94030070a00e00b0003d02000044070500041440750040c41d00715015415a194154809140c1b20840c0c0c400c4465000741c4e482481e00c41d40700c50001200c2c0c40d0080c40c240c006e0080d4220300c4c012070201d00060150328411908561b06145203400142d544402101e18000c0320114a07030030720060020b40c403d000c00d82c0140100840411059951040001103d00d2070480700c800d00d0748684500c019410103054210140100204071010410070088000b803c0303c03854116980b0700d00d0f4800360380c0380b0b429010b00038020200074500400350b07a0b9000a6943c0400040600c60303542051199040c184040c04400510401c808140fa054041d401115603100e80990b840e003030700c6 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 621771339 1250 621770089 621770159
    0x9050405150f07180306020a02072d050111011812230301061413061205180a0602090f0a0b030a150312050a09180506010306060f0215091204 62
    0x40c001044681d02c0740141c1c2c80003c22199482001c9050f5800811903400c500c81e80c0b0f03950b50a040e48c6c0881c444900603030118505011400e024040000f1b071555070001040d170000c0c509141c80c40c090031031180078107011415140d080c40010a40000c030960001a1805500c01240c1c0352207801e105000406c80e0014000402d20800800544008441d5202c051b401d43d0446c2c2c40d2040031a500d1010085849a100007030040050a820340105030014240300c1d101c450908554444050403501e0080045440b0050300c1450304c00c1010210f4002c2040740c010801590b03601e46007021417840b0390580c8a01c0d03008809017a0000d070b81d85c9410b01850184600c4001400781c00c02580b9641210300c0c203808082c10120b07010892821040c060130040c640600e4509059108542d03c103402d051f0011203425081d5443d44581c1002015a4584140c502400d21810700d13070485013002030001e6aa40c5d05020801c110b01d151400b094032040d0400c2100c002c040802e22880d0b4584e03c414041c0100012410b0240d0580300300240040 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 621772589 1250 621771339 621771373
    0x131505041a07020d05030301080c19050d0f0c1206090b070f05030a1a090405030c0106080d141605160602160608070e041d010b15030c0313050c040609050405 69
    0x8640050308036503072041c988400c0d01c109070b0240078202d034018100600c034800508148091b50081801801404c0d413003800c4010b1003807851855450001c0c41d00080014003040c1d464407002040e064000300c482c1c0c1020181d1400490034ac0c0c154000034200e8104070017403400c111490708007181d101d10502d6500e0507a1101441903510354035940c80800412020320000e500c0d4442c0d540701d18410054014581c1000a0203000b017074070594245e801b40e81a03003001601c0121741009000d454000c1a0a0300104002c48030110014110b20300d036040d00006920000d0078035012900c060741501c07019001000e176090150700c4541c80342210114420000540190011f501e0305403070701c0d640341d0200e90b102d468000e03255072f41079030803100300711a00b4110398407603581c0c5025030a5445408499600c0c1017a58000102c20001404120701524680d42000440100300100325810030203609613078014506903c080c00444252030214101140502c0b0290842d1801c00c0c0028548405e4200034001d0b8051001e4030400d4000d00c03204c1e9 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 621773839 1250 621772589 621772597
    0xa2403030804020105160b2e1401050c0c031204180608030304020d0525091401050a05091009050f100605120610091805220506070503070507020402131505 68
    0x40d0118540400240255000310000d000100c8034070300ca85222441596005444681620001d440c0c40e03000801095181c1c510882818203118480d800920505d40b807840300704600194039960400038040307100f5400300da0404c0710119420303006095903601c4145014541302904688201c1c2a4025820700c0d5201c646003501c0b0347c4003501c0024025600d940d44580a004404140341c004450310f100f040b82c0301607545006201043d141014943c500c1c4d64901c1c0080032001d13a9507240c0008000f05c3c0b002e0041005a8540140400311041911800c1079581c5105081c20368108039030060a0b030724100300400041e6024080030510644954124078106034079000704503034038080c001002c0101040f08010542500d003540c02d81c2c00002030f40c540705c0ba4031912084143c1030701c6034050250204545600c00e000c0004440c0000340c640c1e1061140c0c0c0442c03410283c9031135a942e0400741c00c64080c414000f000c100c40d1442402102c10706c41e000381c0203541e80c120815612502c40c43d01c0c81030b00640340740192100701d00c80c4280111 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 621775089 1250 621773839 621773843
    0x901031112060d020f060d090b1e0f07051b0309030613111201020d110c0c03061303030237030533181008061303090e060f03060a2403 59
    0xe10056640c80d024440c2a840101099078405e85040002816544000c0100451111800d011a0030200c1c2d14142e110f040d409400c004442d5108020b280c0c21603911000d595000170300180c1031000f40c45505040d1440c3c40b50740b407120103058003d0158500c2c410008018400c0c94001c6c1d00b110f0076690b410307849a580100c0d401c0c0080c00c1c50320018080a540c03401d00071188190303044000040c60032107404681d600f00d4243c1c007181c0b5290b14010403014110203050140940380394003500501824a01414000e5100d41e000300010300f859408240310008a08200f5500d00d01c103040810b07008814400040a4000094030108900090406000500303042c02000d0180d00450151403001c01c0443c00350907259400d400b142184c0e040114119500c018841d40f450071406000c49550700a0880d003040352490030140020003118001e400c5182c1440044da1221202e400c44082054540c92a00c40d100013a4601d03810082055042c8180e501780200300302c0980c031001c3d00a54582500c0822600d004074198286540c0c880 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 621776339 1250 621775089 621775117
    0xa1407061d061b0f070203100612020915030303070c06060e0408120901060303021905240f15061227010203060a060309080a2703050c0108090f1e01060b0c0309010311 73
    0x113a03c0400f03202005e005c13000d10090980300da13900d003404140d04552582e44140507030034801c0502415418669041500143c1c0c501070699201d0800b004a5a42c4c4009000001000310712440b040a1019076400383c0040c003480c06000a03a81010b0401000542000800208515002000c2411030405204620459515030040d141c44803003042940012424280305545038001c8126080c24038200703400d20b070700c12140d102c5030340c2c8507042110040002c00002011069079a40320020b20007a0707920726082d80c036081c1c42c402c0d00451a51700c0405413200020020b400040c50749110441c80c942d18010f4000e507100340d100756103c2501a40d148021002d40300c030b401028000040c20400b20343c8561240d03a000d40d0340386100802c030380a4880710312070344c1400c02c075684166580e401c0740c0b14101c0e0541e4050303140303500b0804220052081000500c2880d45849030020f044c14140304020041841c0386080d04444c0060100110302d0703848450416015480ea8000214a80040e10700091035015a5003070083d20305500c60703505 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 621777589 1250 621776339 621776347
    0x10804170a080a0c020f07270509010c03060e010e040224070f170f030a0f150303020601060e09041a15120c0f010306080d03050406020d110901030501080c01050a1407061d061b 77
    0xa012a9000403403442340100900841441c2c2025080b4011315018600b4400000340d201c150b614001c048130610f4000320740100b10100100326041c0301d07130300d4030b90440d03011a41200702080c01c0710124050411400d151314210747c0400c02c5020302658940b050302440c0521940c1c034004d00c0c0001130046034800c400150b180120248040340c6000215400b59101001c034171400140581d001140c0c0e644035541da4000c50059002000600c2210380c4061084000d000c150380e10007030b6040c155910000c901d0ba403509181008507600026400030b0000001024042002c0d1030760340c1c28451143c140761154107171804c103405184070003c000c80765403082c80740c0c0c01101c060401820b9680c07401c4104038058580a082543d4654003805110541c210603c0707455542015270050315139480d140300015017550300583c001c40c0e10750400e019070905a44c0007001c6401c014018540b2001c9181c155030024158050640c003c0d090510700041110b03c5045007064001003590401100d8485d40d03070f503900c1e200311a000c600c0001c60b490280 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 621778839 1250 621777589 621777599
    0x92312160c24030c08010b0f0703140d020408010e060c0714100f020904230601051e0a020a150248011d150105010804170a080a0c020f07 60
    0x900c0054038280714030072a00801e075072441d0034840c40e466030351607002200c0d52003005907540303405205007241420700e070a01581a6151404130106400346403070b159000800002c18004241c0705000800d8464119401036803a0501903403000002c2d0028024030702c4540c03802402490701000043c3c00c0c3d21a402461209150210b20341e20688924544000c03500140f04002c0902d510300c0d9580501403000d0a46480103071110032000401017500d5202100f8610b0788140c0003330035641c81c0d0318024194820000c2c20030790350b5680f00c401001000058004504014140810303880d2040f1f90204103060400d005841c66210205005802030480c41040740441c12030130700c030b00306140f681e03540d00503229414620012204a80c004140300e80e41289a40d041d2042c60355141400303158148049024101d080b4103030f009145a00581c0c0c42c4840c9008180a0281448160400a82004020300303034004150314800d003258071007001000c06030065009548480b009414012104452440040c10800c880341c554001c1000c18130700 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 621780089 1250 621778839 621778867
    0x80a0b060418061404031b0f030302032e0e07050c19080909070f0206010609060e0d0f0c03110108130312051005100905180115030e0a06092312 63
    0xa40311a8441840d0301c00b618001c034142d0720400140028100f09004645458036008105001c000c035004480c441480458004c69042444001c19641c1400d0050f981c2e20380c1d00703603c6281d004401242e00150f291084042144102c1019641284d50744007030314659032540e020980f4240a00c9920210b43da01c07096100c801124115419640725000c3d0414914060b001c0000c0344000c003084800c240030802b48182004410390420010340100f4091405080c3c03503041c80c40c0102080c005140091140f240240c03564103100c00703510000211a07001004d4405103031b40b4902051041404000a0301180c030074000136882007a000026549241d00d036440f140184031041d9650000c00001c1c0103c80082c01d08100400c0342d8a84100700001c000a50f1282030741c070fa28040400250454042d250611444041e004015040311412249042d507018200400e40b06038481d0020b00e0a005030074007910850070007070745d84144111402d004481c10440202203036202003c002c82c1c0e0b9101c030050250720700c0c1b1b4003c220101144d508 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 621781339 1250 621780089 621780101
    0x20901021009020d0812060f01030c0903020f030709140f220f06200c060c0702090105010c03141635130e0f190605090a1e1113080a0b0604 61
    0x4020704da80c18140c61a16091129008041c106100e4442031050000c0c85c03405512000c0144c5017482c05201020a07042d004104071000d110007130060345040311039040c558051012030042c0658107410015003503003640704141142c055421000c1300c5051800700305903000860003003e8101ca125a0b000240100e96502c424031041c104003a28101c0c0d0b2610404080d0204042c90301b40c03040080c0d01c55465000300d0b0b030024200900035000054a0314104411001070f15088150f0381140c4003400e02d40c0001050341015100c00d241f1007680c0d1403403240007513080c0f03802502c0c405224105024a9000d1540d0401c4000b070030000b6180d030041000010000902460032648400134800c44c8090420703003002581e01d002e18214030205489110302080314608100328007000200e40000c1c80c03600701c0240000e03441d05022807061b85000d484540200d440c1c1350450404c0c4202c2d200c40d46000d002d80000c000700c40300c4c00043c080c590000e42c3c022440000e800400070b0301e1500002c003006420b41282800e04940c84003000c1000a1407 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 621782589 1250 621781339 621781343
    0xb1507080a050a2304151b020904050a06020301092003072a020402031905130c052b0b0403020f0c030705130b090a14010e0702030706051f030609060f020901021009 72
    0x1c94503510050401c3e0700100c5241644010b8803d175202e50800c580b040e410940b45085200b00440d154900362600300c0d10801d11207040c2c042e1030340140c9856504202c0e040400d07804010701900d0000000040c100c8041d4418001e406080900c00e00880341a01011400d200c00d82c0d045000a00003901206140c02c0380360742041030520304400c0c10340c0351681c1e80442e0981c0c204a0328107200540c1010003a148010380d00803668840740700402c52039000c1079562810700a90342030203001d02801d9010007030103200e01e0703486032030046d090780c0f9100014602d070a180035100b4500440d004c500500803440020075442000417400c0000d54010040d0000e10b0514080c00420442c08003013044407a1280d402c42d0704e81c0c4400400301d008120302540803400b080d100141200c2028103911207407c001e040c4080100c03607a030100655203055070103c1c01065a86510110031016901e842d40c20b46501c41540300042041011350180da007040c401c0c00e09001c00d80f62015001c0403401041c2c600c6000d600500310103400c00019a201c804218 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 621783839 1250 621782589 621782597
    0x31a15091302031f08030f0913060806190c092c010602030c210919050a2c040201050405010f021516081006090b0a03060305100b1507080a050a 63
    0x6050034001001c01a8119403504007980c00800d00c44c500c0c0a030100704d452110303604009482d043c9001101a070b030b0f01c1965031810000c0d1003c104802d699840c1c0c1820304104c05c1003030f000d000540e1500a000e44414041e20369185800e941d0701142c00000440c02042412903413511050b1620f458482544010b00210010013405259554038204101c0151480c40c06812140e0003952201c9007405030502d031000000f1811480050581440400048081190500d010665010003200400d0f05200180801c981100340d0184548101180aa0300303401040a00c10141d28154560320b03c46e0302d1003071440816039001e40003a0013004244800c1d4001e101da15912080d510446880b080000305c49103212106607500440d081407810000c92443e070041c009a00000b8130700d08003802034a40000030341401418498411101d101045031402c190096006d14015034100c001c0e41c0648015a0f4228014200280000c0c8116905281c2c41403840c901c0c820788090300c0d403106c00740e0b1610990440c151590f40102588400700 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 621785089 1250 621783839 621783847
    0xc060f08190914030301060230031501030f141009020c0a0f0312060308040302090c030702060403030c0c02040513020a0e1302130b030d0c11030d0210021809041110031a15 75
    0x144404c100460081a15034050001d188098540414900c00e0701d4020444540c16420480c0284401013140c1d00010b00003980543c8a25031001a0041c00051860b43c683c00d180c81a900059151001101d21030b82214064606050311420000c0880c02958041d541543c004403d00000480d404d03a03260310325000741401101040c80e03690000c01d41e40c16400842d0603180119007002103003081d86070960040031301010b0350f04518102c0002541c600000700003404054445040c2c050950041003109440e940141c8240600e10300400b0308030b0b034588059002c900480110000160200c0d061070b926014850348109424031684e16002c0045412a8403c1081c8896440c01e8031040c0b9038040194904548060701d62151f101000d080900c2c1440f04403104500a030070100000d50455800701e00785401107407942c00141c41f40348000c80c85c10f1134050814442e400052020074041801090b11015891040c00c40d0044948095a00d040701170f600d4003003001d01002010605003074207140142c01441903c071815055420 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 621786339 1250 621785089 621785123
    0xa0302090d030c02041103010303080f0a0e19110607020112150f082407091205121605251403010b130b0301150e0103031b020d0c060f081909 62
    0x7101c015101c224041a18030501d0011424940100102c03c07001c1282e03182550300d145c81c083c0c14000d0050082c40004102400901001e00c0384d400041507514040844014824080750106282c606100c00c4d2104402d400c88103101d4070708101182c54443c1c1c107a6480d2180211244041c000e004207103254042d0040051020a800d18000d880f2002412000014910174040c0b141004410651445d01a0032511040410000da50003407107440480789900074001703030302d0710508041e424103404109a02201c100050400c4000d05e0f81c80d40340c0780050060065403c4002c0001c42c14100070300c0010001030f821800401027040d1070501a4000d0807a80240000c00c4007609040080e8004030f00220704da60895981c400580e0a0609104000134820314400440d242800d20010704c00c4800144030080c20442d20181e640d8422000849442015a020b40f90440540c058640b0007003180240c007a0100107145110401e100c1881055158050340f0542c407220390f05201d2481c05405800c441c4810744040d03d00c4c4000c00c4c1 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 621787589 1250 621786339 621786349
    0x240315030d031406030115170102210403090b190e0d120504170a0b131e0510050a0207020109030b07030603080d05090d08162006070807260402060a030209 68
    0xc042840e0b41da00050b091418200e010740402c0150a03e402685006511861445c000d0b800d082036400c40a4821070029200c5100390181c416420040c0b00b15402e1400300040600c0d1403000d41c02584a0744490140907200e0511440d00d004031a4807100c02aa0107803030101023800740449100c0008003400c01c4480030516141c408a60803110407003000a0000030b81000507641040140d81c00072003c801616207050541c0b142e91400c200582006c2d015078442e041401044010350356a054a090707410704000802a9040ca640c0302e5880d101c9101106041000154039104a80f08590f03000354141c507160707070403400c50301c84c00c400b400f0081c03410007419900c00001c4085a0f026005c2c00041201101c0444c1610317104a24604094500b013484003031103035240a01a003200310034150001c00a0918041c1126070050010300e84e44008412030b10035078007a0782d05100141d130740710020a01c038001980f550050004002801000300c110441c1002c0740c02a041c000c2070062900000a10b10640340c3c0c0380141c21f00c4800f500240b = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 621788839 1250 621787589 621787603
    0x180809010e310603120e010906051c02031503061302030106060c051507091a0408070803040f030807030504180c030c020607090b0f091c1a040f02040207031107090b090624031503 78
    0x1801113610041e0f2006c042d0303408450003010b030945103051130500d20f81c101301e2502e4601c01c4402821164004c000603030709040001107428807400c014119282801d280c00c000ba145e495100b004d030b0103542401d40200d001170250512040c6240c1c000c0080295002e1142e81e8680768002130002010414100300005a088045258990200071112400d96540c5050b1f00da0b0325281c6503600c01146500140010010700d40548034100c100c07034014040c10f6840c10103140454a40c4100d80000c40b41e4040c0b60709180484803550f100a0b0340d40900c0c0c0f0700b000306101c0c600d4182da40301e504452603800280d01400520480c800350028201e0b5112440c02c0c1402c2030f0440e40015070f400504c0d800102000b51001c3d20f0f6051044081d400c260720f131f40214040b030242c20151910340c0c42c607018602c064011500002d40c0d10070184621403420540301c0000130b44501a85a00c1d2039000f401c20000350303a121700703040804220985410300b54100d045c5800d03403c2c9000c40d07401c9021940160002810b52000d18a2001a4403481e18180424 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 621790089 1250 621788839 621788873
    0x2304030503041b170106090b010e15040806040c05212505101707111c021006140a06081501030c11030d020d230604050a180809010e310603 61
    0x852800030714154130600311806680005000c0c2e00303203c0b500032166049140c3c075410710001d0302d01e03100000e41102c1411040c8100d85c40481c040c41000d04000078030081000f040169001107403076461020561241e10800c0840300c3c405c071000d800004101400301194070113034222042c501541e9210568440019500f6014a501c0c175020804400700f617051012106407940d0300401c682400c0000d9100b56096580e500310600386441c0e0120b0000000b01d11074007c10105225080c9010180401034580c0075000d58145190801400381568160103d81e1034081d4040c0c07072007602480305071684415001e004402600780083d409003801b05c2c20514050f5a40b0a100801803407a0307400f000b594840185c142001110b0b940b2030602c007000c038003d4a00125001350742c41c4a80051007110007203055103504420354018008030950120108080740c110703003001201c002501d50120240c80d1b00b22802c00590a0100861203c01030074607401c3e640c20303035501d0715070b110b4250494101001c40000703c1e507840307580f407510f00848a2a0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 621791339 1250 621790089 621790109
    0x10305090a20030f120f072f12010c1b020607021005030412050a0206070f0201180515010e16030e010b130e0c12030f070611070c092304030503041b 65
    0x2c50490404000c00320001c03202c2c1d0000c02402016000e1146940130701e9030b00542c140c60002c0e8440c00d00490280d0101d5842102003401c0c4440a580e81c41090405040069405116841800d80140300c06110f1490000d4454843d28440e060800f800600f81d00d58007000c0b0b07408a401d05c061809a15010f140800d00c40071a2903d0f84c3e03e08150030401c1c1002103a020f400108141000700c034000f0780d804903402d6000852810110f081400200003079001d413050740d1403000c02804050443c0d0900900150307064001010700900007850744c83d007180c0c130941101140d00000c241d0800128000c428481c3c1c4c401c6030702e007001d0800012000030900c0020401c18640c801058010344804220b5800e08051220035184401121042c038803c420100498807030144200a0382d8007000481c0c031106202558000301c02e055000c00b00d503a0348d5100c0b454111144142402034411107440e180201c440c82c00f44008030b026560703800e03130f5424243e030706c81c3ea04413610fa000510481c0c100140780a45000058042808d50140005500b = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 621792589 1250 621791339 621791393
    0x11011407050c0c040513080a0c0212100b2e0512161d01120c051c0606020f010603080d0902190314010b18011202011809090201030b09070e010305090a 66
    0x2e0040c40c0c01646400180700302e00d880d0500c20b0381410b1a511514980d802441d0320b840f1203208406070340698801902940101c00c08141c00003030381c40403610081032541342a08004840e450000d00020381814a072120000b041018804403410740c02d40012101c02d520320b011032800d20303c410f403004010429520142c000d55040e95407403103c9e0f003184100c104c0101c1c0c0300788000424960750000709481c402c00d810356511960340740c0b20310005101ea8112803080e00003018041a6070b1013200b84000034120303032180c40010302072042e4524003d201800741204882e00152498201146d01c401d4900410a5060481c1c0c03200f074400904803c05035980c040360046018103203403401e00284071185070a50b60640b1240e4031640605500030000b0044070720040c1900c02c0c007440e902c9440c0c4903200507511605c604a01903100018010001280324980d0403081209100707982c02c0c05102d01c518184202c02d9002c0d038454010901c0f000c608112548203500c03a541c032481c04403c03a003081082d601e41441078000210204c409080183c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 621793839 1250 621792589 621792607
    0xa050705010305090a0b041e0203060903070311061902030709150305010503100b0916110f072c0609072601091503020901090e0703060c050d06150903031101140705 72
    0x1c4500f0741d111203030340302a01017080a030795403400260b0024002840010b00e440b400603801200d10000c4070156019003124901c1c180504101d80e00d4002030130440000348401207598a4040c0400e500c1c0c010300c0e914110344000c9041d5a030500203500002c2600741000304440f400600440018400707c1d201c0c2c8141c40001d0309506100a150400c0303000d03483c10000f03070700349039a01c1c2140c0c660600d902c0e48108900010507404955180071103100728080c0801c10240314190000c41940000b1035420111804c04410034000b0309804404100050310060800315003041000042d0141070291380340d0390000840ca403070841c2000308084800d080c24100b42d100c0d03404240e00c0c014400f6403114480c0b0320302c600d1590b503c248281e00d103500103aa030400c14010315103480e8480c008042c040b4010030000c4080c50f440602488110b041c010b000340a50890507000c416282807090014070b02626105103a510115503650351006030854800303803920400600482c0f040d40d40d6100da031282824100615020b40321959465580b1480d41c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 621795089 1250 621793839 621793841
    0x40909030806030d170604020d060b0d0c03110909131b0509060411070206073003230c0c0715030e100c0c020f030a0203100b040c03050405150c0c0a0507050103 70
    0x400260299100c4469400d0131508001052440300ca502e50b180000d5036600c000c01d0180c001c201c0b001c0551404c000d80401c440b00d40201070174403045c400380f08000602d0b24110071070030307290b9541503505c0c400c500700f105042c0c41c02d250710b51aa100d02e400e400f44a1b0041e480c1d590711003002c0b0300100d141c21101001414403a0386031032285076822650807107040c409448280400642c0d0f204018000f48a80b200099034800c20403002c0c034169800c00702081c4116903100f81070100340d030440c030410300900007458545130072840c40e5108010848410b04101095807540e804194100c03c2e4030152980b112882503080005003950401019000c0301d59a5501150424065a40314035120310b003c80040a10300f013084003002903500030968503005070122142d80b4600c011a02081c2001205100a500340c0100c404d50041c080107030704400000141038408101840c0d01000840032540b00381d1700107055800c40015504c059481c0480c90380c00c200c40703000701c80c074240003400a0f500c1d283e28a9811581341d088404200704075a09 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 621796339 1250 621795089 621795091
    0xc230f01020d1103040b15120307030201020d0f150b030a0e0f07150206070807030207020a08030c0604021203120c0f1312030f0806060910021009030503010806130312050a09080409090308 82
    0x907070f402e8504508140e91804902d40c40102030030507071580203c00780d90704d581e034070301d60300003040c9503401d0380e40c2c0f1703402401e00078041d500c0926510300305820201e62140c032036818421034030b40300c44940800d0480d40c00c20a4038402d40c1d0000d4442d049042d1201e408039880d8405110a82ea449900c000500b083d5140c2002d01d0344003420051418195080340c810003008981182c4c540b036100110349001a45d135112440007650012142d081000b051001203071380d103d85840060403602560080320301502050680102d40d9681c07003004c0031420700310403003000700c0d010f4a124000340c280c02a2a040300c034140701c05410100500070721036000f05407142d034090140b0b0078590850180d55040c4428070f0041020b183c2000424030314401d060500b4041c4181c44d023240e00140c400d0101d0001281503031018040c2044608004005420030300034070800703000f16008500346007005130000c9001d561641340c040540403800740d200c000b00401000b01030000c2e140c0ca40100011210b200800240c40d40e0900000c0815082c1401840900 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 621797589 1250 621796339 621796361
    0xa05010509060a140307180b19080312130212030316050403031d0a1502030c1603030923060f0d0b03150c0f0c07031101080a020304030c230f01020d 65
    0x10010900180e40c6034243c200c1c05481c030100010310400702040209240000325404041804007452503c0003a80ca41d402c1070548402c202d8080c1d071081d00c141100403c0400c24070070b44006500800201e105240740414580d840306408400691300e0425401181c0d0b94245682004000c1e0000003c000c10705801030503400911220b0b14040f0b0425003556030280c20300c890a00d01e00717400d00904420445035170741c0000010142c0701c80900e1114003544d00002a41e20f4010035680c010038060030f040701c58074010520340a81101d806640c0c0080c00e41ca040c0c14441c842506601d45180d1040108400d492500c55000814952800f041081d0b9209150080c00c1c0480d0005030781244260028000c282c0b4000307621141d07981050310f901d00f4550754032000c1200d880324451101c04003090700602500106105000c00d8030610010280c9500075150f4071550300c00202d11040b05c00901240c011002c031008180404110301d81d01c10700140b10000540c07401c00c080d20300195014009141d03900015100c40c05049030240ca9a220 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 621798839 1250 621797589 621797599
    0x10020408161d06120c0a06030605010e090408120405030c19030306150e01140d050f0405150c041202040609090c09110f0d05061516030810050102030706090305130b030a050105 77
    0x45600300d01400c01c07480180c1520311440045450710080c1030144017021702c0300f400a110700401e0703564a0019020303218078030400b030100e43c3c038009182c02420310f40500351040c0d501800c10b41c80c0c1602080844007684000e00291150720084c0284004908100440c00c2200542c007070b500300c2100d0030314004003a11519007000a80100020180c041c15800074440c0011a2007401e0000740b1040004030f0b60000e0080e00f80c9070300c01381d00f01000d00c019030411450181c0200e02440036a00c40c402204c07000f110381c44050b01c840c201105d080000b040002c3c030030700c030032b0b075003a40b0040000ca0401d54420603101070314000d00050342e004c0a030990801c0803000e180724001e401151081b099040c0041c00703601d80180e0150018818145480344005100c0342d854030a2030b0a01895054640e032946e80c403c2d141803020071a6502100400d01c030780701182c4c802007040d801404030f5005034001d500c0d1144070b941d40d10240c1401c2d40b040f030920a041c42241050107250229030050480da0100503100e24101011500742c4006a012070301131 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 621800089 1250 621798839 621798869
    0x50901150804060b0402190c0611070b010e060d06020d0e010c09050a06050d0603050708030a030506090c4302031b010c02063603010b0924031002040816 67
    0x181d41220304242c0c0140c000e80009443c000301004140a48100c07002404120341c45c168119103070303800120145040e401480e080010011000c0c1300071241c4608800a00b45000540040000f01c6460341403e0380075102900300036500e412655400181e030040c000031880f00b81c41303552060104400344115845405145000c400f00303843e000c0890780c404d6040c0522001c10000107445150507809130010001540d0003011181903030780e1007041a032690013101c0d02c203002070f00b403401103010392401c0e060541c021b01c003c0803201e01d1700c807600c01c0e8050b08980300515900d1007092200e030a20042c00a00c0001c01c40e411141c1202d401e0205441058100007020300060541c000214285003282da000d5903013005607505035030444d60b4102d984101000c0a5020792106040e49244001007076441030002040c0104100394000c0c1300c190714071010043c1440041761141080b400718444080c45c0f900f10f04104000c20340140c10780b50a9507003000c0d890141da0250300440c8859108c1c5889a80d4105402410002084940108100 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 621801339 1250 621800089 621800129
    0x712090c06020f06070e04150312051c0603020307060f0c0c17010f0e070506091201060303050904050c1c020901211506020607050a080c0d1404030e030a020607020d1b080106050901 79
    0x41b9160180b0480c091540c030400c542214081c500c0c964059900800424407481003020020803e51240409407102c1c80030350718400e400d40d0140140c0d41602e9000f0050032074981400412901d10307115424001c108088a08000301080b1907d040b03002610002c190124407104041301c00d0300f55050000b0301c9000e80d02d410646100e003c00400c2c0002a0340c030450701d042d521110319000940b0540300141002095213884c90010426812000400821106417800d000540d41c809490940740521000324403004000e80581403500265030040510b040f05061092a1f400300020703a008014044080507080c41d40c0d035031950703080200b400814000380110310050903030b8178081c070004100e809400003403030a220308400841c100041100c151a03c2103c0440d0400400800101010460798241ca040c3c2c042225282091000d00740824503600e1190054100d603d0000b680e82440102d10080d441075651030b805000903081a140040e07884001d121840002c18074a04110410050001c103a008903d92405e658203058 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 621802589 1250 621801339 621801347
    0xc350c0915070305040b040e01050307051012090519060209040f150b0f16050a060c0f0c021519120b0904020d1e140a110f0d0b0712090c06020f0607 65
    0x101505901500b5200d41d510719042d81e05018640040c0c10304c82e0045004281c0d440400d6550b070496504500b1102c43d6aa200c040c40940320014100a000601801741c85055100c56009440c1305031054040300c1421422440040000d5031041c001ca42070341e000200810949002d000e00010a10004402c010713400c00140300ca8401c7d40140b06040012501150f0074016412500c06d9035401c403500134061303151703c0c807529046480d90300e41d16080783e02c07501c0c0c405d440b9113183c400d113800c40340d0080d16140d0030100c4d00d4079002c010301c40c607440c540351078480410050b0500d08210908004207540d101d4541d20140c9040000c000240d03010144d1180c00b41c0409010400960b8600350030b221155001070054201c1400300440110030400001c003d080c0c0d003100080c80301d41c40400540c0f464014000d51110b469604120300700f00c041c4a002c140c5c594040d910b0890b040200c0c090703882e004d0700100b8034144641c800340b80420340401d81c0d200720300c00d50760000b000a0800c481d036018440144e041e071502d0050005850a10000781c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 621803839 1250 621802589 621802609
    0x30c01080405010f090b06041506020309010c141e0601060807080a0c172a0304080706020c0a0b16080c0c0601031101140d1a010c0804090c350c09 64
    0x541040020320105050040a5202640340048100140011006403e00d04103d40046d034440340254500585d10f400d880311402644252074059000d945802100c000448242c020f40074240d480c1c038410205840814010410326901d442407807040d00c041c0100e213110b0342c10b1100581c00841400040c5040042c02948040c5003a0300075050440060341c0301c0c0f03c80c0200c54440f1441074101c4000044400e10070740a2804e140070510001941481c50b0b01c070343d12461030841c0e01003514000c003003800601580d0006022034000c0e04040d02000c08a440108598590101034202034550900c0005010291030040341e000c0c503410b41c091075000410303250805101c0615a1008140701c060120304c00a581035500d03a12400d030224400e0350900c40540c80f007060049000c000c203003030108015800081001d000065000701200d403103d0390040d8030700d400c2c1031030b20800170041c002e100303800000c12403261010200d2503100c000500c0c1e0700301081d07000c0206550441d400ea50b1880e01804603403200e4070910071707020030740c0d82c100c808 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 621805089 1250 621803839 621803863
    0x103050d0f020706200138090115021603110306070f17061201020a081609081e070b0705010510140d060917040312140a0503160e0909071a030603 64
    0x30310840030405c0c62820b1144207160800340c0d401c0c00000c0c0820605400000f0041e0000d4002c0d02c91510aa140155007260309010203401810301001044011000c0002000008440c0183e80d9030649220b1032104603d000c2e00112402c0c0444014040241400c00101d580101d00b42400416840008000b0740301040c2e051803d069800c0075400101191501b40e480302c5c0c401048030003036440c1c020701d0601410315803080381d2071120f80784001031844110b48200c00040031171705224041c00b0b00300544650100151041c80c11040c1501c600e01c03000600c0085a0000d021080c054400003a036807c003640d01c0710413100b05a1200103008048a1300c3d10455560850112505511000002e036501c11803401c030303400021100d55000346580100e0000280807160340c02008a880560303030000d41d80030b8500401d155014001800001540c03d00004611050880790780f82d25105a0030b04400e000d003400005610b984088440b4500d030381080714104a0403400791801c152655082c0d448038291b20701400030981d10040c140d03c03 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 621806339 1250 621805089 621805097
    0x729070f0201031401060306080c0d030509060d1b05070b0906040c0501030f090b040c0e1e0105040507020c0a180e031611121005040213020306090105060d060b120103050d0f020706 79
    0x40d0003107a02035405000072103e03155140d01e1300e42e5030f000060001c4c051403050020a0090007004090352400c4d502c1e0041595050310b030142070207920014004590032181c11040516502c0c984082c40c242d1b0b048e9100401d0006594540d034401d05840c1a44402d04007904407515640a07030103102c000703560103ea41c01503d80c00e00e07000964a6004400d0405491021805000040300200b071005000c8035610308010380c0c2e1041e8209281e51103401c0741800402079213068200031490580148210315083e0001c81d0807200c644111202a440030000400714002a03000c0c4084100c801e0203024151280d014002d50070b60020099400c004400b5600b810002c0312400091009159004090842d46c5040d549216460320600f222081008884001c006000a55040e445150900071140c00d01d5803030f0080305e10980019040b0a400d03440c1c50140300558110b40e00312698240c84e0b100100c1d003075401201070718400740b152194003800d514504216040000d80c00d44070040000038010301040640009400382240c0d4a072070 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 621807589 1250 621806339 621806363
    0x70512030405040509160b0f0f070201031128090b04030618170c01060b0702060717160b040c060c0b1303051603020d0e03070819140f072907 62
    0x19910341035125680140b82d020f803611050104c00540005d98007560003006500342e86032600c5100040040c0a010180c09000404000141d0100c4000c006000300d1403060501180035080c9003612900b94200710341c681c0d901c440e1134010390041c04036014030301c4440c40385084c1400c001c1c0c1400700b609002d200d64040940056260601078034100b14451081240c10381109101200125100d29003070140d10054101d4241d40c06c1c41c101207152030b081c90132a462190b00400c111300c1d020441d82d8058488c4069030490410340d00502c8210b14003c1c005003202d82c0244a0712020401d840c21b817500c020048483e130002804c210104010400088c00c00801310b410071a86154904200c3d26482c04540c20312a103c0250401030061000d04200b607000136040c040020541c030340d0b0424500300710070b0556551942c456442158080031000c202104440c000c54442405001040c0d5440540c666051030140c861603014410b07070141c1c4003004008040f00c1d20080351800381c00e50403030341e00f0141c03141109802407600c0980359540940e = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 621808839 1250 621807589 621807619
    0x21002091906110d030c0e0f0a0e1006120e191e08180d03120f020d020309031b0c01020a03050d09060501140a0b03010503060f041a0109050a06060309050705 69
    0x280e032030154001207007095003540ea200e45006107030019200030b00c21035101d90150300500c4d500170700501492580350354a5032881c56100e010000483d14031441d03250002200b0101040903108184142d00c1400185407000829280042c0240711803045c09800600d1440e0594808105c6404038500c1741080b20110981026055810241070145801100050840e02051400100316008000c0c00d06050440c014450310142101030228002c031b56440180000d2010b0308800301c00c1400e0317100c540030a012480040c01c000c2160040e404a03031042c0c071052810307030005c282000e0032003c003042c04510000c0a40603159034190400082d656106680000302800300126184086400d142c2c0422001e0303401045c1400507580d00d428100c5d0102031388510038018960a000814030281c000c0440b07040f154003030000c01180c0d9408403516410780014004880d545081c0303103680203e060f00344002e4040d200c0c00c00c0000c0c2d2070800b0040101120a00d6000030f052508000028021a50114540048400039500810500780348 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 621810089 1250 621808839 621808849
    0x12010638070302030f070506060a120f0b0910020d06140105040803070305250b0405120a0e060d0209030f100f1b120e16180e100e0a0c060c060f020a02100209 69
    0x181705229a14a4042400d805226001030024000e40d42520350fa403800b512100180d858907c100340140180005142413030008221985040d440b0079103c0c10f42e45a51071040090f0141e91241a42c5d450703144c0c56042c1441034410309900010a4002400d01500d0b1501d4032154984034001e00a0107824404042409000800003445640402e8154108a08030f08400d1601e070f081c0107400e80c0e056880d48120003114000804c0c0c07070101c4200300005d48500d0030075602101007246035480075080311903442e000d0040e05940e450402014a41400c050054403605800300ba030b120031648081041101d9078284040400f840300c5601182050910314508908032941110180018142082c41001184180102d400310300c44840c00c024207039245503a42d00b80c1c07020301000240a95840028580c110b820142c05130b1015402540700703000320300f07046003030b5a08141603880300104508550b000901068065443c2002c0003600c0c400c50040c6419100110304000c0e1185000396900800e4004d04a015070010707400e0b40c96910 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 621811339 1250 621810089 621810097
    0x40c0902040f29070807150b030709111e0c0c0f09041514100513060e07110f0304060f18030b1302041d01020a02060f22111201063807030203 62
    0xc1d031000980c1e10301c40744c905802c4a41c441c00d0161524404c42002c002801fa043c014228188030080c010840c9a0400c40070324010400400c004071860b004002e110b0f034801601c5030300110402003007019900c0342071410030700d400d0a0703861040a2184411f00c810700781603a12440895005a0824103030021046c0c0c0440310001040e0390405006030b852242c003040000c862890260056541c15503100b0415035269086c081030303998034080c46d0581e0342c1c040009200c0381e20550340008010790713200c1111aa084800c0710b05040d13900680044d00016203548645800c5c03a00280340504032000120014000c074030b0f58682c28415640a8055244071103020b00a030b0540d51190401d2291a03400400c9160607030250120600139880030f040e110250146500081e4806400d04074184682c0300d072001d201480c2c0e00c20038000300c0900c0141e8111152030000648584540711040000c05105041e40005200d81c00c0c074404001031a600a038007080c619125038000b03a0380b8410045079103030ba028009526118512464241d0950007 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 621812589 1250 621811339 621811409
    0x8060607051c1404050d06090206070f03031a1023040e0a09020a0806040308010b0304080d090b06130b0604050f010c1a01180e0615030715020105040c0902040f 70
    0x46500c2110b0403044003100320802508464480c1980034499079400c010601440c411142d01842201e40c180200e0016045000845c0c4010b18240c500b184640c0c0e0b0280f5483c42c190142d002035a200a0040b20401000105400240c200c8101d19140b4034a01c0040c28064154445010a46988580c1c240c450310b84042d90050520407c8840207850000307601001450942000c0e84a007102400c0011104404030340d1394015905940c504101e0f0f030a200d2800ea031680054030844440000300043c0c85414014401c010405209480b00c66940c1041c50800c220304004100301c001d91460b0280344101d07555203400b140d003102c00983d04a5001d900031001a41d04001c5217030080c1452281041a10087c0e808600450507135101d907100b1018200400c0190003101d00300074120303903260300c040b0110f00d07203031400c20342c25242920003401c481c4a66114062010101c0641507118007513034541d414813041004030103a0304c0151100440031810070740303000c119049600f00d500c01d00712071301c1c895500300528070710704802503640341 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 621813839 1250 621812589 621812593
    0x10e01140a210e0d050a0c0c03030f08181914070b191b0f050f0f0a0b0f060102060609040812040309081902060301050f01030204120b0f0c04060f0806060705 69
    0xc02000025010100d0b0140000b5820303011001020300310050320540d030307040030001c00414040c2c2d0b410005443c5c60740034240c140f09124068200d00006400c0000501c0694400c0d600c0f16090b804104015110b0240036103904114130305403010b5040844001018540d68080005958906c0c0d044d00741034a039100e000c0c0103d0301c280502d42c400701d200c0c890f041c001c00b0210b06514081042c505180011a0032001e450803102c840441c404d061000f00c0e02c0e01440e040003d006606940f0056400300c1c03094541001c0c4860403180e5080046040c0a02150075209036128000d0b01044c40c0c02d20b84000001d450b03141c0100500e10400d40e40f408101801001819038154051081402c5501d08081c20301034040201442464243d104001c801e0203440c41026111840b00d601030300917402e5900b8001001080003440d1000c504140c1d00b408001001e41d00002d0040c007443c007400c00d81c8503074104141e0705482c51400620f01c18542008000c20000150302003000011030300549803118858176200300141452007501c0c0301803d14 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 621815089 1250 621813839 621813847
    0x10c110a0621050919020f030615010e0a080309010831020a0b0910050f0c0102040e010509010608091c03060e091006050427061d010b030114060f010e0114 68
    0x941c01c110212042101030a2002c5071440755542c003425204122480c20341c6410100c80e040300642003640d4a01024802000034850410f100c02081c034261080f50042114401110300a91558010b2a4041031484c203507101140f050924460b9640c0740b00d95510141000103640000314a0070120041240c00c070344d01c005407104009110720040550181c080181e06c40d8070344410005034055803504441c500c00001d803007943c4842c00c2d800c0550b410f8100940e00115000c0130090000380d0711082c40244043d00c3e420036499015410702d4103000384510140c00034414051440c0c28002c1c1d8180018040c0d1880703080c1120f0031110420b0020403000f5004661102d01c04200c0c4000b400701c40c510118640790f41050a40341002003030340d5607041009072009090380307074808a400da0009490180c00b22560b45407900400d004034400788110150760140030464070b10140742c6d40d5000764610620b03080c00390003030040380283c40c03180f40e041c40e100080c564140343c588136040c00f40c0c4c0f82c03030303c10355900038140d031661090103100e03094403 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 621816339 1250 621815089 621815099
    0x18120102090312160219090c0809010f09020a0e04020609060d0504150605180a141819080315010207151d0d080304120504080d0314070806030c010c110a 67
    0x2035081404064030038090511825583c0540000303461100b50940e1040080b5001602448000c804a82035000c2c4400400000715a095040c05021a0205140d8500b9800d24000240390b00b1a0003528a0074006030070f100c3c1c01c00241e981d50f845003007a01c142403081840341d2200e1002072254030030080080c0d003010000c140d0402c108016802070b81325502a00e803a40064105000d108102c450300d02403203610000030080c42210003038200303085502446480f00010041d0503005040704862089403039280107003034030f818203444410030303c8280d00c030550000d81d000c038503507140e51f640515010080c000b000c011044841c491150b0700c00c001d00c2c0c0c01840c8240d2800481b0030542402410314100800320b001c542c44104400056051030031000c5029500300039a142551202d43d51152680808155103003081020311000c204000180030050f4082c1858800060f455611000c40c00407110040a003401d00001c8420440c1c41d0f100410440214002441c1111021465203080308506140c1c250940e0041c80503003000c50 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 621817589 1250 621816339 621816341
    0xa0c052b0303091a0108060a1a0d080c07060302090a0605090d1b140f030d080603120a0503040c0e131b092c060907051e0d03090513090308010308181201 67
    0x40c0d81c40c05a0200b04d407004404004002c140c00c28411794000760300c8680014050342440c0d00c2180042c40e5411242040d0640c0710000b40d98040d248002e44000d0400160885002e200308041c4000b0805810150306029141e400904581d0302da00c02c58042c4000040c404503107507203034501c1200e01c981c000312042e4015211944418001241d000701114007803940084102440d09807a0842c503541c004004018003003100008a0324510041c00301034251081c030701c81501d036000c400e0161681c6140c036075481e500c929003810104001405503002c0c40d900c59101c0140844c5615200c01496000e0304000402d521040540781d41000100580c41002110720303240c03100007072448003030449080c02c3d40d881100c15489000c00007a515a203068802503495031001104005034100300990030042e0301d902004c82c4840c80841c000c6481004220011000224001010f01151820f1811480d0382e80407410200a06100c070b50f00034200d560103006c042d00c0e011000c54010b107036030f014884003110401f001d080c40800791205460b9034 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 621818839 1250 621817589 621817601
    0x50913080a030501051e061c092112050105060d05152e030b18040614091e030406051c060512031c0b0a06110a0606060c11030a0c052b0303 61
    0x601c01d071341b2045d8520f0300500c10318070b01e0320061004010070326000708414064183c100004c0c41c00360a548521240c1c02203582000d00711139041c1035104110104800c003600030300c40000c11f00c600503d0351a0000620840d00c4080a489005408140004180c1c4070740d59445510803900b804503031f0141400d1b6540740c003200b60b20220a00382c0505e40061422820340350098040d07499094041c4d4204d140084101c0d1048407020800e0381060241800055441107901c040e5a0004121100000f82c3c2c8891060316401c00c043d801c009003404601c024505107414004010040e2084d0702420030154030800f0400c120441036030001d8020400108800f80319040754a000703480f90010070070480040402c020248070a840c0d0f004440e050072005095590721810402b069440700c41903041808a4401e0105120000b002442403070080c4c100c50711205006a5281b91440041c0003e2502c1ca00981080700030300d002920080021041c3e40080303174100300141130b1560684403028008014120b0780d4038007400c5004c0c107806070300c01 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 621820089 1250 621818839 621818849
    0xb040510060206160c03050a050708040e0f070206010e130c0f12150e070501050c03071a1503122a01050709141002060c090f03030301180c0c0c050913080a030501 71
    0x350752180e44d81105a80c04090b2580c1180214540c007024600192007500104060002c500b0310071b080c41c4080c1c03902c4000380c001d030300149014442c1600f4060300311507502e41540d000d0480d1000741047d42c10f26404145401c405410f04403030032900200003003003019041e480c070013030804c1e40143c0044a035a013070384008079a196102a10401c0382150601d001500601039001d17403a4a120007001010300d8800111070741ea0040e03a80b208540024046c1d280050840708e0a07041c40c00010b80c2903403083c03d00b030000801d00001d00b44124440e0340402c00030041540100143c2700c0001400c82c3d95110a01402c1e054101e4071180f180b001d0321946040100720700c00380c02180034010b983c260401c0c90324800b0360a0078001c1d40e0030030700a1100543c3c410070004100c4ca807614000c3c58070040c09000303c1c2e854403480011034070b5a0800e0300b0294040c100000140d11840032881100b000d01124a4820b4074240c0c151038440d4004940e0190600500b04500000d011801e102c000958081d4000050355441c0c460b5030f8010010310080c012 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 621821339 1250 621820089 621820093
    0x50301020d0f0b090c070f060f090510110403020f091e0403090905010e010b0d0b011413140402270d0b0a0c0e010503010f09150801020c2104150c060b0405100602 71
    0x8040f510782481214503114413a501040703031801c26113454490892161080849001e13490b24102040e02d80d59001d0000c41c13038840d400034864070403040c80300800c8e118000210f02c0b0f150030502c000c00142e51017410042c00400107699180c0551a1f000d1903901d00d654150440303c92000803000d100405512020700b00480d405818200a07591700c680101e11400307420b02c80e41d0303864402408034000f040350a611503890a07005041c940003c60b120341081d40036402461032000915a419410004100e0b040354004450000302c404519241504100d000c01c01d200184d800c140301d81031501c0014039226404144032a03a008140d646851070882c800708054100d0102960010b0303040110340e0000d50080d01624180c481220f48480c1c618148943c0038014844c400c00300d266948080c0001070200020f2008120041400014080900160f400c0301d00c01e00c44c0510b00c00e440355003000b00308130079043c4a07001d10030a0514a0104440da42c0303401c2c02e0700900030100b949544149014203100b00420040342c0f030030841c0c01d5502 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 621822589 1250 621821339 621821351
    0xf0b092406041202060a11060a0f05160f050307030f110a0f0305040302061b040504240b0702010e09130b090708010b010203030411010c080403171b19140106050301020d0f 75
    0x284003807030142d07218800200b26055003500c0145408000303040c03200010b2030702001d00b804800b0010314080040e105020540c2d03a0b03078200007010b03502d030090365409030300d600b082d00c00051600402008a0b59900d446420090b001c00810307121f510075000b05081040d0410705100c2d100c02c0d009500e850754040a4a180030071a0441701100b00c81c040c0c002e8034481c40d00368014010965810702090b01c011078142040b12281c008001c04a41c0f50365600c610241c107020b8440100c08140c1041e40001c03946020380020002c1c401c00e01c840d0340140e80c80b035184400300005031030310311458840d030311002c080391a01d44004147d000f125080020800e00007802c107080340e9052000f401425403034001a42c4a200644010b4042034110a40f5059940a4408403500b20b2080100030700c3e003076480e203404010b0008159942c0d00504c1c00500a89202001c1c080000c806041d08013800c4404d00074a040302044c18040c50040203603018404080700f4070820760200c0010303d0090000d5541d6400651410010b010b010004504245004 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 621823839 1250 621822589 621822661
    0x3031808060f041e02030105040c060306050604180209060409230106170103080a0c050609150601080f0712240504150b1206060d061401081807090f0b09 67
    0x30707005001d10070ba600c0d9101e1035212915200781051040c07110740d1141100300d0398440180c90034032405105602031840c61644a0402c0e00003429101c6680c00148184002e01c02030003031042e903071079845000b076241d81c005a0360300100020450718003495004c00982ca2070030b8030442c4200c180d001e100c40c000b200944a42d05913038a9200503110343c419601300400101801e07005000282d602c6000700740502007400c0419403901903075030f42860004201c40102c07aa40010b10446c3d03c3c0c4519044041e0410001d00b4821824905800c2541019000500240030043ea448208144c81c5c2c09500059101100300307043d21003600e4403036401c2e00c000b005208803802140f42800c1d21036100351910780c41c0240c0b0302020080b0f10b041000441c400c100207015044c0340c0d000d0810007a49411031480e11555004101d64031620f03082009840014004040c01030000e40a40d0400c00c1b0105101404503003401500c80c250800500391704004a00d000404a00e150140c0040404003400740640c42117542c1740310551210310800c1e0b41c4c0f10135 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 621825089 1250 621823839 621823843
    0x72d05090106021f021201080d090603050f040f0f060e0106080f191205090603010f08010e010606200a0c09050414010902010905011202090d0308090c090405030d020a11060103031808 80
    0x9120b040016000318000c0c101480300500c0081c0310f008a0200541032442c10000180110020f90024480381e101c15a00c001d20745c0c02c41510380c0200349906040010389091458484c101c0c1d0000c01c002c0040001181ca08100b0100051240c1500e0300600101704500f504141c6900030907a030b02070500244035101c00d0703201003000020902580b10103011075500070120f5a90b802c4507850300c0c03490030307050080a000500403034030b0307140186000b00782c80d40d04890100d1030042d6450840e000b44907034000300d0f41401c10038014141c008038017004140180840c000c8803251500030b2070414080b10001002d040c450000002c9508840d00118012170140c0c111800111945880a00300c40c3c5051009001c9403404a08000560189030f044007414801a405890040c0c2800008c100140c0c50508401050410084c8421100e040210700b00528064440b0001821b01703464860ba039001e4004034115454001520b941080d2141d40c1084118002c0000c843e02543c480c80d020300707410ad005080603078110030300200103112480 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 621826339 1250 621825089 621825091
    0x81902030a08030705041203080f0606070b06060d02090a0e06100c110907030906020a02060a050a0e19030e0307060c1b0e13030302040b070c08120309120309072d0509 73
    0x200400034030900005680e048101c0c0c00082c801c0050180a200004202c461740140460303082c401e03030780c01038140ba05240a82c0c0003170015000310300503402840100b001449607440b80e40c20620890304951686a070700b4400000c0d12941d428150440c1c01608d0010700d0440f070071f002c01d00417081240d49240303a401c3c4040480320440c00719005860342a0250101c985400e1480403e82c03c40d030549000318201910f0384851050b41e0054400070010381c00b000402400038001c1c481c06400100c2c0d040144060f40801118a94449803002600441034688004404150090607425041c00015060315903170382e070761007001c0c146001c02e5606880000d0242021982110981c100d4401d445079201548851b0f15003015040c40c5040c420401c030306059003080085002e02d03501001d0b10f070351889000d030306804504254906023484107118000340d0446050003070002c103220214503ca60b01c14070400c2c03551241d54114903949084000d922030280f9000100c5d241e54060392641d01c01103480d00c0e00b8495500295200b040c03181a101c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 621827589 1250 621826339 621826343
    0xd11160e060f044d030601110c0a03080d0209030604030f0e1f11100e07050112020c0706140d06030f02041d031b01060b040602010b0a09020414040f140a05010819 71
    0x12038440d01e0059984d0301003100d441c100488055160080c0451004400d40341012135007200403008800c00c0502d40e400000340d140001002d01820350342e15030502050b840041c90000411010002c10480c0d5490140e0703042e1055400020203d800904182c1800fa24a064400e80213000414100d078008060a1181d040a158440079448207000c0312511000c803081d081001c0c41c0b100034061008002e00b4410135000e8900300c103403540c024103505803034040054080c8400c44000d019050060159180d00400070a24200b20780c0d29003004081000031444901d0b9600c81d4641105103285840408001c1c004d0884211030758601c260303401c202080d50071402c15226081d0922402a1b0fa104021840d4840d5000c1a10050090210000700b2940d072281e00501040d0019008000140e64030b0060494500d02040800300404400c1c01c00c514290428900c070301c214944d40310311070280d600c41141c901402880d92204c03040101448821150f424038003134990240800703210341003051040043c2150800c00310040c03010169 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 621828839 1250 621827589 621827621
    0x3020c0a0b0402030a05010e011a010c0c0b090a03061112090a0b180f0f0a1703010810020913020714010c260a11130603110307020d11160e060f04 64
    0x11419645406070448002e0089805010b50072150b00000d209000314000315104900101c0c1080c103a0340403102d10780380384180702d041201110b07908010980c901002419102c011441d2a9140420000701c0c103039500c0344c0c0c03000f0559803034000f0a1041d1749401c0e000e0004002049140b4480351115502923070303116499031001c1c09403d11800800d10481d08a40d26250401419003500c01c500d103c04486820601e0320801e80700280c01145e42e0b0801c10180d1050188450b05002d101e509650401c40e00a0303031740325056080c41000d603000032540700b29542e1150032600e84025a0043d940c031402807070079540c0241c0820705000345609050000c4030701c07401840c4d41c0710058000b081e84040100780c0f07115080c6140c4054098403105a07616161101030300147c00400780c4001504150340154030301900101115900030642401c1e0105000340240c450307011408001601541c46c0082c0c2c044401403525081841c44080d148074003001000c00110040c1070076010340705a2085403840c5c0e000380d8450601040d1030502140f0040a = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 621830089 1250 621828839 621828853
    0xb0a020606190b0a021c0201150611100608011a040216060b1201050c0c0d080705030402010c05070503061f05091302061e030a06080c0f0619050c03070308010f0603020c 74
    0x507082c5012802d80014101000c40c99440d524a00c0c003449502c124118401a000101c0f45000044200494400c40341c10348020041c01c0ca440d1462402010729004100400c50050122200c0c4142000001018440c1c9402004803999440b0b01e076000300f115041120b103020414400c06814a030502c01e55a604a0760b080c1419001c000d55280b0000b4003080c00c0c0b45a0020001e062280750041c248a00ca100da420100107583d6500c0c072604051908800390115403c000220341000300743ca51050990390031950a08011100c9025881c040c0c0c03d0200f0f41e00490781600c81c0908200c00b03820080c0010140b030182d1148220041e444001307104c40c890b030032035680041c0c0d0008086940107040010040c4002c0401100c991401d41c20018164a203a100b92402e404c441c2d166142441030800071300c02401065411500301da000d0700d010000ca00d1501541d40d5401c00418020a003031101070080307046401d400d4444041da640d40c900741c0b13400f8220a40c28010041100080d07100030502c10300a101b02c500d410f4500c0010b080c4 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 621831339 1250 621830089 621830101
    0xc06070c05150c0412030c050607050a08010b0301030312050402060c0105250206131101140f09090939061c0e1902040207020a0513320f0907030b0c0309070b0a0206 72
    0x101760381008049042110864001000c03c070240000ca005001a41d2420741d2083c0d4054000d00008040e044416504010001000029007010440346046906400490b041e51a80000381e80b60144520030060b6501b0401000035020640320400b124005400c2c41905416203ea400c070794602048421421005255404030046000d0070f80d124885041494455080c800c2c5c16103555032500440000501c0304804102c2c050285820300c01c80c0c2e4810201d038010040d200202601800b984c0200c070151108200d020280000c0c60103030005000c00c064090689603440c0000c00640e0007070358030780f6502d2104518240d4038a020480c0828500d269000713090195000709a140c00f000000d52010348203e038010f1a00c040020a078468100c81c10140f1200d25001034840201c14092140c01a503602d9160400255551070f0500400c070501c840d085821681140410341e14401220314100341d64001501800b11181003110305a9004000c0d48601d0482080e01c25030303584d40d2411015401100c0c071010250b0000000980 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 621832589 1250 621831339 621831359
    0x201021905030705161422110906070b0f0907081e0709050a0c09080619110906070c03050f0c0603400b0c040506030f040303020c06070c05150c04 64
    0x102140500d00342c0b03140c031849a071450b141c9103c1c1c00040b904000420410450126050242460158155545041d641100150300d5003521440240f4a05550f20504051414588400d0703d515000103008507039510781c0d608001e1304249003218a044060109400500340ea000450f00104444d1544001c010105640e140800080ca11251440b82032180c5100002d2000c09402014042c203590000010f0303101c10800000c0110030180c00c080304c15407100b414040e107403010030f038031010900c41a54001202c211b24075410605108800b4515804000481c1c1c06040c8003041100c40103e038402ca048070344ea60076030f41405849020301745555038849001c0c400070784800390490283c540c1444005103201113619804038000a0781c0c0851421107aa04881401420012140045600241e509003014109844c1000191103440010440400701c440c0c00e010034100b50103030b0190f40e404031558040d00d000d450002c00091050800d1b1600f600c492180d00810132240200002e498028010030b44041d242c0390034a400f840d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 621833839 1250 621832589 621832633
    0xb0c070203031c0209091512010c050d1e0c0314090a020306160c230124050f0a180c0909180210090b0315090903040b0706151502010501180603020102 66
    0x645110f40030811004075544058819115154000440151460072020708c00208029001c8000582c03403c6c0d50600e8164000301920b00300c0c4244580800d4000204800c0c02000b47e03131400384e044281c281070340c4040315601074008484618800364941c43c0ca5460150745a5200080c00f0060740503007150020030800118052041c1c0c44060504000714202c1a65460b03201109241503007004895003084000c8043c9801e0042d064142c80c0b002087c0d584015200c2400c00c1c0032198801c00d40329a25142005800d030312050310384001000c1d42c091003c1801490418040508181c044d258006903407010040f5406017030340305940c408903d0442c1e0341040e0000d41d09001c2082207898064051104030180040c10070b58160042d8414011050004101442d00042c42030082c0b01030402e0a940d00f0601050014801a005640c0101c1d0861b0000c13680300c8440380001d04148141e00f01c603095003107130b040c40c0c503d031a0150010f80c100e51481003d11a041d042900d40412141c1030300000340141c003c230060310031408000c0c03034103 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 621835089 1250 621833839 621833887
    0x70804060b042703020712020306010521030d02210106050d09030e210706050301051027060503150a1202010503220c0f08011104060f09030c060c0b0c07020303 70
    0x89429440b40d6409456140f0004541c0c0030a0b481458001c055060091400811644182d180c403214103500187c1c88110500401d07003c0c11021024a00ca00c070002d4003034079081c1e498410350755030315840c0311f400c00070b944480b4001c018168148031010300c2c604404103250485565903281400c000d00711504001900119a041e410402000c40505481c3c0d03074402070442c5500307507680c8510010280c4080d181882000e03804402800b006000402c1030b501d0720704400300d00400c82d20f8091070341d00c05420002d0071074071643d40c0c000d5400c0c580d41002c5504c0303800000650140f8101600c8940728080c86082042802d0103001e2241d40300391000300c0d540154056806550090380d00d0b02d0a841c480c14041140709002c4540100703881d628200340b001c02050260b01c102d04090230503440248070210400d5800c9225220700d2260408204603100312820703651083d001e1034081c580c0029041c10107551a0001805080200e106481c1100d03220003142000c40090103c80e001c550250180d410011804c1c0d582c209050344400c0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 621836339 1250 621835089 621835091
    0x80711030901301a030c0a0503120d140c030f0a0516030c03021b03030403110a0f110607060e030a030c0c110f0604030506040305032d04020603100b031006020d0206070804060b04 78
    0x40700611441406240f10822482d0130b404600c1c4100310416103000e0410941d80d0040c401c0343c806000b26100400c0307002031080d03240c010175940c45142e01200010310301e0803102d042980491003484074914044005500804d42a0b241c1e80140c1c580405441c116001a03840c401409004c1d2041c0001c02d029803c0351110840364103006062131140704809030160444011401950070000810040540101c84000ca08452100401e404260b59072151030071100c1904c0074111a1030491035900c25130f103c0d000c5640050303001800344002040c10800b107980e40c10071507080000c207041c50007520386688a07019a203241c41d00036242004d44110321080c4190107944210070754104031300708804404200c08000d9107008a1080d81d400e9503d1510240507a0500c1340065400008011141d9002417003078410b0040c1c0d0841e40403280e1a43c4c0780c488403000c1d6002041a0300208407024044200031061000c81600c50413103180c2d40070381d00c1080e211072040f07850b103800302c92260100741040041070101b030359076124544030080070f00 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 621837589 1250 621836339 621836417
    0x11070603050c0d06080102040608130c05091506070c14101d0102010603050a030503070f03140a110d1a13020f040b0702010504030602221e1e050a06080711030901 71
    0x10b0f10342d00b600d501c4d40101245a40014040100039480000c65500008024060308810b58a9882d61810001ea1003810321501c60040401c6451540b80c1041d000440f004104940e0380c10540b4200e81001038a210740c1d01d40d0410700300c0805880c1000481003240002039541c03210b02103103804e140c60301c211141405904540d40d40740040b0001314104114403200380aa11000c3e20f038540803400500d00c03d1040d0f07805c8201402d06844d607d40300e801140d0f242c0c00c2480c03880081120800102d8662160080340e9800c040d850402c0c50f0408010080102809090401d0303510340345003924245c042050b0b1041c14bc104000140c200010812208e0b090090140300b071052410328541a80d0303403140000d82e0054602e070b58411001000799400c01d5200c43e013800081014650071030401000c503115154407112440f42e4071a0b03031111002d260920f0240e000010146c04000c050b0f41c035103a20381030001e207061000c584041c04640d08003003000740910000166510010140c1d40d80401c42612102c044c1083c500c28443c40409403126 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 621838839 1250 621837589 621837607
    0x609080301030503190e0a0e1e2403060c040519030605010f06020c010c1e020609040614090c1801050a030e0d020309030723040509100609051611070603050c 69
    0x1800441c000c0d405080156200c3e411000b104003803c5010011505000c6071508000780380d159001180f088030030504502c040380d940c083c00000046030b642106070440c01404200b0500c00c9058801d442ca013017145514030603405d5201e007811342d12801030314140b000e034805002c10466442c1c4407405910300c0541d200c540103115925601c80042c2d50b020380000d0800300d000002400265410402414119024a80703040e00c1512a1101c0160440307145248410a01102c4040e00f591128400c403285010050b204100c82ca5a81004c0c503004850301f0200751080b201e41c0003181a50b881341e0181c84019807044406011500d80800544150340404090001e240d100c4540581c40b0000b401200750b446410340155941e058650b00305414400c1ca84c01200500c030442110302c1d141c18502c8030782c580104094a00140c030b0f45074584d0341803420340541c402d02040c0e414181d01140304586600010300420010800d1640e0042100080d0340d4000145605180340e4080317401000003c0c82a00402c0d0000110254140b43c0715540c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 621840089 1250 621838839 621838853
    0x1128140f03130309080307030e180f0103060b0a03050a060516090308030601030c110610050108010501050f250209011203031a1309140708030c060709050307091505041e15050303160609 81
    0x561f081d00807880c0100e040005050a4034004540d40420012410928008569031a4401c06000c094070301a86c420794000316844405c441d8018503000750848404072a185084005444110f4444c058803e80302c28005856020309035074016698040078442c110740c0c41c0d200450003022103503030304d800f0861520100040f5200501c1618000c011035141400b0311414400013405540044c2e115070304004c2c00b048020700d001003c0c030031754090207150605000c1d0304c4104148003814021030000658410440400090031100303000208510794460b40313007407204220028080018200a24010350400040c070004403c442ea564000108148203400b440e42081c85410301c0c615020842d0041102035100140104452a04110300c43d440301152909518050070b00010907152800c038403c5079403450300c45000d00380c1e121a600000001c3d103006003040104e5010111b1100300d4564021032141c14525228680340a400072030344520550b400580214541144c0140840944183d620181c818654400d070000c005048 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 621841339 1250 621840089 621840097
    0xc060e030102041208070c0503060903070b13020909030307030506060703080103020906190f05120d0c1502221d09120d0b06030705190c0f061128140f031303090803 72
    0x5d020f841c4d21882c86107800f059000e03a50f00014401d5110000304110f4000020403682600da20010040d00c9440e64480b512161442c0500254000309140030007289600001c0607502c1102155800d00003925038805022051194000c00350000b81d592006001604000026940183c80501140c00d9883c054404000140c05078200d03c1e68090320030001c02c500d00d449841d003500d0900850142070100060007016011789080d171070040a0344106900f144000d480399041e9005131000203070204088248a80a0100a40358014031a15000c0d0a22040c00021440007291203400200001c00c1907074100042d00101341c1040d052500420b032035018070380c43d9441d504055130180090340c803425120b050107a003038074040d81c101c2c00303210402c41c0700024400030601d800f155541658004500003001d8644070691000c600c00ea0040404828025403008050204030748040c002040c0c669600d0450b60032908500828414198404020380701400070038500d01c0744810401d00342d072080c1001c0103104c6e600d03d50070f811600 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 621842589 1250 621841339 621841343
    0xf20070501030c05040b03040609051609321b0403350f072904110301060906050a2619051516120b060403060603050111070c060e0301020412 62
    0x4805410803031540c040c0581800342c43c483c10034508284c1020340521590000400c040d140c9a1100c426509102060060f00319044010b0941c0c18915101c4601001030100d10014480100130320245085012011800701040300d00ca0010070b9154903921181d00940c4181c40c14400000d108200010014901180364400519662004039140d0401d02040d460038080310b01d1403400341c00030807800d40c54510103c2103e950a500101c038100214901c03a0402081c1e030031842c001349c440c101105101c10300008003107040d07902e08114002d0101da030300c038400d40050b2080d9104503038100c0116002407064040700b146445444245070f091525a503140d159480c0760000d01281e01010f440c5a003074010600006014201c1d1001c80000f8848450070f1907200088900e00002c8030000300042440032000c5002942c018041000b0010403154030b82e0f03101c0c01d05000404040c4011180340d86000c40300a002e80200046d20362103604100094089440e00d034040d20640046004a50b05541c20400850904005200302c96828 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 621843839 1250 621842589 621842593
    0x90d0804090f050f0a230403140403050309030d230702060c01061205010b031203060405040f0b24040501050907080405161203120908180d0b0901091a0708070f20 71
    0x1081400115000314005010040b095041907000842480c0c1d81010440c4d0079071ba000c400d43da0f6501c40c101162404000164242581c00000700041070220001c0549401181102942c0344001c9441098a02011010341080d41e0a0a000c40c0003001000f103018200f0140003401961410711241449804c49040e50809158400d08501e800c0034400e09220b54506034500b0b40007058013800f5000803901e42d0100404c80340c8107503100c800180070014010b144803501ea512002814050510f00c4001c00b02c0800c060981c0b8070b90782000d100302c005103002d0081c0c078101c3c0d0001d494030005841b183c508492028005005403094400e4401d400740c8042084201c00061044007000c0a590b0054600208040c4056646c0202c0701c1c01c104480c00032500d03e030200c03541e6002c407010b0408950007950101e09548609040038050409ca0000c00103101c106400000070581308050103401000f8211201f400c9038415142140010703403080c0050384503401410381d4074840300d45007440340c2d102d150555421400c0903101d807220103135 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 621845089 1250 621843839 621843841
    0x114070501050906100e150301020d290306040839030901110309030705061312140f0a120f140a0306080f011e0c03060506030a091e08090d0804090f05 66
    0xf06008843d0403044200c9903107442442c10000c8280c0c4800904030003001059010f404584d590254101d072240c803c41c1005012401c090141080a114203840384808208507240b0170031a8903000ca0703001c0c49954000c4e905824136031419802c10303c2049031039130a040c000e082605109419000310005851460602c010741e40d84c0f242600044c90946041c1c2580c2c1554014000f00047d5030b03010a542080c0d80f070580e1015100c80d1200800c0d6201c8002c0d5000281c181c1d0343c1120a400d00141c01d000d8a14100103c0460b80c1481681d24459a25081320902401d000007516103c42c1040c4201c5a101c00c04481f8030700342408403a410780002c816808041c000d0702081d661001003220741e406003e00308181c0ca10f81c1c020440c40345040c0850f0407809103000101041c69444014800103402540304802501010708426160718000480070020300810b102501c1e04003105101d100313400c1407203820119066202c07501f44e052a0f28842805484030140c80110380c2e081c81030101107904400c40c42202c003100c2c4114400300c1c0c0c03 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 621846339 1250 621845089 621845101
    0x10309230c0103050105010206060108071e02030c010b0303040b030417120c0702030601060809031e1b0f1510050f010c060f02071b03030504031502090a090e151014011407050105 78
    0x54580c80312150790605080c40c0040065a0700414001e50000d0f0a00300524183d5071a0070844115100500481d5400503465250b06410307400009400c9201d4800020400152030b4000c06942e4000c0340b241440c1c0342d1f02000054001068840d622000c410345008032420311b14008030728024680c0468071140c51076804549241585007c000306030050103541441103050505100f03441d01c1f441448003c1c884c550286145060110740041101c003c91186003d44040c0e0035083c040130780307402c0102c003410480e20601103500d07800d0b503205800703500515100d481420407034500404e228094004242c0d9a06010482d840140800e5003070040300740c40da6010600507502d406929209404910b140985a0b00d0025210140001703a000030849041d203030401c0c41d01c006510002c2c46175000e0300c03c90820a80141c2d4036100010300f900150880c8401c0c0314140b0070384240e020000c09043c440308044480d41001d1100c900304202194a1201d80341c028401850500c508941c4600c0404461380540822101e0780c0d07580b030400103 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 621847589 1250 621846339 621846343
    0xc03080711040c020705040c02070e07050306010f09060f0f020f010c05031f030807062c030a2c100507020604120201031d030d0507090e150f150301090b01030923 71
    0x4900300040b681000a02c0e4541c42c000d6a480440c0101800749070b94190042d0304a0003000f041d4001d0021f40302803640e41c40c04510040c0b540d00103a40d1356012034001e00d0008205401100044180c84103a517519003941c0c1d41f91811030711030f11450340e04420340c0520349541e10b518800317001d0340d40803001a071038103552810081c861426501b403103200c0e0440ca80d43c909040c00040c0000c0c0849980b00d400c02d00100d4004911403803000070303424148050844c1800840c0300300c505980800070701207800701516200b5110030701c6a1044c1990282c00144e0b40600d80304a4411b01c00c0c5480380010029154904c0c00758101042c65010030155442034004100c0b0f440d094141c2000c5681c14020b0700e00c1d0b06030840900020074007408195990340551650340d200340781c803a000038015500c50440d0f64010800411091755500700303c0e800d1300401025044403030190403034004045007400d10f482c1e54104144d50804d190326580c0b900c01c5090003800540a101d04150312107580402240c1c000c0d80c180459540360402c15000020245198 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 621848839 1250 621847589 621847613
    0x609050f04140f0703020402030a0b0d030e13180b0a060f060309020310091e0f020405041505060619050d24140103090b0105040c030f02130528051302070c030807 71
    0x2c28194068055404100701c0840c84004481d81500e0268403911981e506401900f20034245c3c07504140c070004280145a40b00d079002000b81416958842c8001c11245070005588100001c0214003005803604c000140313a2410350341e841200701000107110740e03c0f003814000402e020b600c904000b0f038603070141e601949410702500700700c1980c11100b04018407181e92240c071240902902114003403640d906400501007401d02200d0340c0c03640100200554645464088001410110241005803510000031400d0516000b1280078181c4080c031850380b411016030440320380e8401c500d01c0e40e405072683c82c0901d0950340ba44265140c01d0a10f80c0d002000c9060103481c180203015080405e0426050000301f8011840400007541910720555000c5030150744800203074041c0010340340d801c0f500d073f10003e0303100901104a80d540050b6501160091203590748049089440c1100001c80c0d802c000401c0420046454040012288070078810380140c103040c0c4039221a0702007043c1c0d40c415510382000080600070006698041 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 621850089 1250 621848839 621848873
    0x915090608281401020a0507050f0c130f09050303040501060e09010510030602030402190b0c07060203120f060d0f230d270302060f0403020103110a020a03080601030609050f04 77
    0x5040202c6400110318090011109501c04031410403003080c14801040003075810b10380e040c0000e43d600c82075900b00400681c0044400c2c1e0315405485002c1d0403041000c6070b110801340c00101848604c0020700b00c09401412040003120000fa9682c00714000100c0c144007640c8214010300001030311030303d0401818924240200002c40f180d14040400c002e40055215940549800480068030781c1e580f0710201d01e00d07d4180e0a1030018820018000590481c0c0d0401007204000b090192940a0b075144030507030751f0307000308104034102002c85000100202e44102d061980700100900d210105042e0343c4a01c05240b660a00a4070807a546080f50401d43d10a0041c010031003140a009100240c18524000e000b8240c0b11800f224090411910b051204101e80f40100510340007840140d40b00103100440d60380ea030051004030b000c40e04110740070196101400545101c1e0400380c02070401c40520355000c86610320000c0c43c803418940d6030344000c6150032061003002d00c2142e64050100035030070903003030540304034085800d0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 621851339 1250 621850089 621850093
    0x90510050a15050f04050405090109020f0d030c080304060b10050901080c070b15010e040212040c0603050408031914040311070906140d0503090907120e01090807030c0303060915090608 81
    0x800c1210141c50102d5a405014600191200844200c0d1400c034443c0d03134802e584c003900700018065034101c19844003285c03d03c01c0303c605007040c1d10801405400b80001c603024000c18610011140420541001150310522600000800c0145100018100300520780c42030002003010030700b6061940c21640058004c240017905a05109803941c541c0d0142c0c200401105401160368008001a4011031a41100540090055485000700085420f0801c070448056032402d01503100020060f0091040e18090754000b00c48902d99912245461584041c0a801500081d514088110084004501c40c0d00952080d036852101103541c4c200310f45080352907000b44900d14589002003110a00d8144001c031200320554003180302c061a42809400c5004a03d00d45030049440800c0003421603100380390350f00c10109000c0c00c2000100000d8028200c418007400141500020000000445d009400881c403c52181c50040f584685401c2c50b042610100e1090f050b1001d40410b05019040a40c01004060030f00a00 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 621852589 1250 621851339 621851359
    0x509030313030c170d020d0501050603040215220308030708150a060e0307120c0e13031b11040c05040602010c0e03060627090318062d0c0709051005 65
    0x48026454100160060a00110382d400300200f1910329801322960071404402a00c80b00d1402c1e403000a544110f900d008590b01d094004140d45c50480191303400342e03030050840740d0701c26415220f40140c0e5200c800607003207148440100050485070014044095031080142d16240d013003000010b03000c0c440151405a82200002002d1000c2c0c90f602125000c48084d0700c3c1117460303a01c10300b003c01e00f4000d1079000f081911220040d60ba0a014540d0858130403544480070f09400307969000028040390700700c1e8800500041807548044200c20b10215100a0303e80140903102c00b4801c4000090704480a000002002c2a00400e0030810301d6020b10603050b000c071007420190301c06845000025144c1d10b004040038450324400b804000920001007214401110030005004181800c04003165039030018850074014598005408000b070800c90159460005031000b10000101141c50815044241c0304262291038010710440c0c0019100308404002010140000a182c1c200205c8030b40a03e048e5400103801107071065 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 621853839 1250 621852589 621852601
    0x13090605010c110402030a0b04020c01140609012312011e051b160501020712020703020f0105180f010324031505010f060f0203070f0b0a200f0c210d05090303 69
    0x41c507400403c4012580141d80c0ea9803580d0460092040e80e0489030014070104844018140550050340301c031080000c0442140d451404014012009000300900020004a140c046540e0f88000c2100300d28024091070f00c182850042e2070841d0710081e245c000500c840c450a2800d840d151161030780144402400b80c0c1d44100c40080780825102d8015440d103d03601c010700308401d000c029410344028a41c42008610018061080299240344600050384103418a42010003558010b03012280e2040c80e102042139514903400411a000401d6421181455103e500a2001082485200b883d225004980705905801c41c1051901c3c1c02d582d4881c0034055140c0001403241c400e5011482003100d01d00e1429a1941c100b81034124210300844800400c0c20402940341c50401081800e407034860342c000c0783e08100c01c2c000061600c1c8584035842d004403d10380204141203269400c2001448400c244070101ca880385000340d4900002858451b241c0031000d40802c075120840c1c80e60103010303003004095000b1400c40c1000 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 621855089 1250 621853839 621853853
    0x8190b0a0b0918010305071404050403080f090a0203032b0b0121060509010303030b090f0105090c0a030e030d05090d11060613090b0f0603010c02340b13090605010c 72
    0x1409852286840801c180007203a650003186600f00f401d900d00514a540e681c03400980d260704600804503101e4507030701c5150050620348140c0744910703015aa0b10004da21241a074104d010000303060070a441c02107504400241c0c0301040108400030044d030b590314802d0f1a1032000d02c0105800e0208240d001d0500440f003415030b07030014414400c002c04c807101c030407000715207100301c0028809540f10780d4100111000000926406a014101031217007035400110b41e0317941c0940540e07081c40c24000e083c1d000c00d0b054086004115180082e01c034005460400142101030215880d283da0000311051100540303400801c1160501802540100101824881203618906108684030407008140300d000300c9551b00030f5036203000550464115030303400800b04406030418000854648100711200c0e40258203100d140c003061440001d0660100d0072481c800d001e044015014100d151807081030301070052401c000c005c160b9803440b030014482da64864180c0c024240c50451040140d55566015505004211010030b01007000303 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 621856339 1250 621855089 621855109
    0x303030106140c1b040605040b0a031101020c131b05120a02160f030c0c0b0405010804020f0303040503120306010f050a05090f031f02070b101d0a14040308190b 70
    0x78a040008403401800746401c800e0144694292a80c818a0b288818442111380c0d95801103006890601c8142d440b14140300a48031040d40003038002405100810200c1d500603e81459600e051058418980480000a450480c0701c280061426074510706880d1039807a076006548040303520b00303180c0e0402d0110440400c2005004054688450300000d0200a029160704202000ca5200b6115403412007141001000000d01d510111400d42050300041905481c010948080f03138016518444180c7d115424842d80c0041412120340510042c0804106a0303000e11040172404081003081c3e460f0724119000400f81c144152001c0c050040801058540d940c1c030108841c60088281d8822201d1444800401d180480d900340ea4241600440d0100c50014043c0d0020462107026140c6140c842d201d00d0070011404130184215004881644041d03a10301006181c441d5011121541c0020030300400d2034a040b200034100c0341107000520b443c2c02c008040000f00390481115640850411a405401001c82c100c092 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 621857589 1250 621856339 621856349
    0xc030c050a0c151409010501290f210717011211010c080a03061a21180a0305070203100902060301090e010b0301020409061a1e030702033f0603030301 66
    0x284601d8038050149600d01030061010f226420003a42d8400030701805184015605030042c6d509150000800d040040170150030049841030300d60304030101d003898541c00e50200340a810789407400c1c0241d400c06001e400d41c039204402009125145460f1521000300b46103c00c032981c4000784460401800b48035000c20100c2c0d80d6aa10040050840c2c22440040e41c400b00c2003e001002032900003089882140e040d0820400c883c442c1d42e201808562205036a00320f409203000d040a14408400028071104c1c443d62541d41107140030405030b100d8000035803082e003400005402070b0042280000d4034801c5007000c100d643d0b140321011804028030645a40060342e544010305c98075644644880c0b114400907020b502001c03641034020021543c0d04e07071320040303240613202da4450f404400c01400c0d00e416081030000103e90b210501c005000291040b90440c82c00c0caa000903054070110b1100740182124490f00180b0045462030f080c028090707401c48050140140803a26022440c054031607010b0101310b07100041500c3c1522 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 621858839 1250 621857589 621857597
    0x3010306050a0b0901081f0e210f0708040608060d0c1403160806060901060809060610050f0310080607020f03031504090506010905040c0b36041d010c030c050a 70
    0x51158402c18015004480310598000c00c881c0c0006011300c1c00155a8a000218a01c1c0c1603645030790000c510100e620b40d83c1d0862140e00b0010010b603031a0b0041d41039984000c81482c0641c10b2500b00e01c0c0d14412030704500f8085806000014041c08200d03000003400d54040c03002c8484001c903d809135100c41c81e2040030700c0b4a41100249580154071a03405206603006281a0007492161075542c050702a80c480303040d41c0b0f86006031003403030020410b10303c01c400c0e01e0b102e507810350002c000302d032545014456034080c260911000c0110910442c0454120100218014002c0181d0080e2213420044034a080c20000b408410079540041c45102c502c540c080242c1c0d5100c0c1402c069114000c1e800f001042c00b5220b58000200140101000450201c28030b84c07049000d14081c01c1c1d100788140e220050b0459a116102d0b40140b9846010280c13140782d4012400c01c003c10842c8100c2520300708405000c0f81c20f444030590702c89003031101480303941d50a5000b4450030500c0c00091405114840b4000d030040d10030f100d41e1a00c20100 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 621860089 1250 621858839 621858841
    0x120604020c0a1209080d0c1a130b0402011202040e0a0e03181201020c030301031a100614031f0b1c050402061209030c1e0613081b1905010903020d0908030301030605 72
    0xa43d00802201000700385c040d058034012194550014282c11085904980548004008650b01980f0901d124894104021a03880d20a030645444840d440d0040c0100c2c10021441401800b0000d04c0c006000189900410360b5002e080c10504141034850001244081341d0080c4000d0f80c07440902d425043d1003a905aa13420361b036510b01007a0314068840c01126507103a00c00040004100450500c041501a520000c5c0908545035903080361040760301e07485180d0000f070100c0d0701244004581c000564000d14054001100d1840c07020480c540543c440e40000e00d01400401d5428441c04c0303014420300c020300204410030103464140c0c0010b02c2c50103441c00c9104149840000201c030401d00708211004200d4000c04c451429a00484132010b20011541071030003401441c000c100180301015035880045da11001c3c02d41003039200610344010047c9101c802c082e038465800740034081d08007040b0101c5401d00590010034154000d08000c3d1401c0b051a02102c01c200081d9010003071407030040192410340c0c0c0d000c000400d403 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 621861339 1250 621860089 621860123
    0x2a0e2b03031407020a021206090c0126070e04140115030914060f0402040e0d0206041e1b0609050102070f120201050906030a0b01081b0d09030c12020102120604020c0a 73
    0x104a0001ca03088441040c0050003010754000942c174511504c2160200c00000c080312525854284c261760240c0568003a8000076600c2d80507500500c41d1340200754a424960202e2140e216030302a09894050119900c0100301700035042a0261808032014030407031f601c19500d050004503003078a100080c0c0b0101651460503000704544118000710172444542141d9150400304c5241e1042c090944080744990301e810300d01c03c0c2e840e0307020a00c1c8004c8042a0084c000940d1035803110803800d20506980c1911030092401031001a0421040d062660707540b084511a407410080003070b0a4441940010341550f03c81c0c0d10820070a5142074040003a5213249182c01d0f900034840c40140e4803402400c160940c0b02501204000c440310b03e035441440040000d980e8580e59443d52000b0503030000394440068041141004811044840ea80103082c0007403003864401140c1c6080d0b00c0308010039000000590050350005038070420191110341075500802d007190214030b0b00c02c12001c280c0e914104c0d540c005101c45120401280313 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 621862589 1250 621861339 621861341
    0x5180d091203050712020601051305060d030c110406081507031107080f0f070305120a2705071508010326040603150b130801050f01030503090d062a0e2b0303 69
    0x13043e5014080c02006202000f01039280e000902445014102c4020601039480316800b0f040e00481002e00101481d82c602c0e01c0840328800d03140015150b107410304030200c0e4143c495100380d0008119490242c4840c403c180000ca1b071071200582248109820020341108003800541141d404940c41006556101150b170540500b50040018035489500042001d4082c560031100030020042080b200001541c1c43c114180121840240b25850403000e400c1d0340400455043c8085180501541c1118202a07652001074080854a41d9460002d0800750041082003441e481400c0c44185004004124480100d41886140100c0c4600010141c9030301e81c000c05440041c0c1e004c4040e0003c4060180e40c1d010030701c42d0391091003640c0b107050360399803070031000640c000e03448042103060340da0140180d841d00c0001801c20845604440c0709130740c1d0540d03510445c1c401110040003002081032032101e04c1400740ea00782c00504010003401c000750040043e040381e88110518004050070410038028045c149200e20f0038110 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 621863839 1250 621862589 621862597
    0x41409190609050111040e1e0c070206120a1b0507031704031e0f020f010501030213091502070507060f0f0206061e060c010f0e0d170606090d0605180d09120305 70
    0x241c250b51805403e005c42d070040800400a0704c20030060b20900b074407049070002d40790340c0c03a0b0b141c0d00211010002044102407850010401c0030b0005103c10305124070320308050740c0090241e4120104650b101052213001403032345104112451241003480c00d101c280c1d100074010b60440c5024410060141002a041500604500302040080c00a40003032801000e0050048810490100054400c1d00700c51009c581e41401824141d980c05403144400c800008003070405000c03804c0c41100c62190303080d5248100401ca201510405010300700600c0307494501300000c0c1040301010701c0241084284a4500c490903000512903030404002d40f0300303000c00c4446210180450303074031000c010341c0814001440c4412850541100a00b0050b9507030402c003101d00748070b80e1542da006192056001c251010700000707055080504403a070102c0040e004070310304a81c2500007404500000005c5995a546000b848884401c9040103444d110102c401042003000e20f22010700f80a46510541100c044444110401c040c4030304151 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 621865089 1250 621863839 621863843
    0x5030106210e0f0610150e04022116030c0305040b1603061d010e0f010302100e0301200a03060f0513110c0f0703050609030415031a03060702010b041409190609 70
    0x10f104207404a803071180d10b544003a07038a40755504c00707040003003084907a100900d044051982c0764000c0c00031600c81844041c0d0425030340500e0b900c154442402109000b00c4840e48110220754420401e40702407003002d42282d03590110030007014078200410001501c0d40c1507082d080600d071000c0c3e10380c03c1c10201e803c03400303030003950410440901c00084c0341010b440c41a80d814143c0c0c00c0c0c2c0c0440e14180d9680a24107501c55024031020390b005030070300740381401c60b40500c0060252050250020515145048244c011950000c4122030150340c0021000703050b076494070941c4040c04101a1002d0000d141030002145820481c01450300c039681e840c0420020650407040b03810fa08010010344075102e070350005950721800345120554840c0180c1c070010f0001310000c0102c4058604070308024600c0d000000d0b046004205003a164022140c10147e02d040a6404100a511a009070380c000704100780f0303100502003960158891061114015420b21013415004590312204502c1c0c07540c041c049800c0c604011010384100d03040 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 621866339 1250 621865089 621865093
    0x1305190f06090335131d010311010c052a18160f0203041a1201090605012c0103050403091d040618020307061b0b090d090605030106210e 60
    0x409582052040d02143d00450000c0106619062000c6144c0405500521082455504c18249601000c003600540111042c2a06040d032200c081c2070b502401d984000004809010041080102c64048084005028602840316120719079403242e07100d21000e946003111900d00c0407124910816034151541040c018801091aa220302c5100f016140a1701d422020500910700d83d217601d8080c18120f62484043ea00551815180c0700070b110050b2045960396075269000c00c09003004035107074100300303010341460180000c03c24234010001d00001c0790a28110060070344030690915104000b64003460f03150302801c001c0b510340c0c0c0360f280441d07a8004a4000c09501d0303824130b0150f20040088503069101f07504c950b03410490315500e19101c0c1800320640c107009526502c22403090041610400a005401e03003200e255080c07a0001c2d80d02d0919101040ba042015640902594544598002d5a00008181a0906502d19412700ac0000c0201001039900c2e007030140181e4108500c80e9035588486c0c1c0501254007 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 621867589 1250 621866339 621866369
    0x8011502010e03030a0204050102010b01052b18051b0a05060712031b090315090807030309050f03040306091101030207031209150e100b060301060e1c02100503070201050c130519 78
    0x51700802074000c1e001d124010341c86c00401071115400369044a40741c0d40d03500003080364001450b021401c0704032030040400700b15464210f0803a40c014498681200070b4820340c007070040c12042140c034400d4405031111480c81400301007000c009984800c0125480290003961002c0400401101900589500103035a00e2005005107004455907120400c4425a4440c0852013440800c2203500010765540441c042c0031340400704160000a402540094a49442078060756105038041442c035003582c00c01d52090b11203d40710442442080f00400f00006000800d09045060034201c2d1402042030701d11051048126690341801d000b070014440003020b1080001d2070620000045100c0c050b00d400d088500c3c062081d040102d200910700e015802d07a810380f40f20390341300000c07a0008000c10452040103802d5030083e0144081442c0580c442c04000440f860f890384803503549041201b802821501c2c01002143c80400501c0485411100c0001c188206e4070103c03440401120002c05118240701a6400704c4801c0b514a0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 621868839 1250 621867589 621867601
    0xf04180318030506011706070f0915020c040e030c060108011505190e0c09040c09080622050a081c2c10060807050f090f010603090c09180b130308011502010e0303 71
    0x88a034200d40c030f0190240c0c5c07ea500e8001040e2030701000c00c419400402c106140078480300040ba010024601401d01c111a10400220013007422184003400342d500507000018403004059080001d42d00410890f0000c201644501d10070141d0310a450060901c40e003004405900c50720f4000e080c1c10068455002d03180c16500b065803400c2c00c41da1007003030302c0740c0514180900d160701e03103018486000c100e680d544043c020558400640c1d003030f0601400d681c0e02c075529030a410f2801081c02000f08400072846200c0042c0e035175002c0803410810b80e1110111080302070414a42d940040c030034040d041540d50002c0c1d24080d29800100150307041a80e1406688140f03031402c000002c280c0000103690080305c0d41510a41d0211840070300f0b2003180340c000c0301c1c1510255001c0d0010400c1074460750000c0c69003401110101d4400e900e2304d040c11f054880c4140003201e401d881c00000001d21a44200b8160491158900040e20420503030780984400e10510580c0190580020100780c0503000390886090440c0b90016070365203182c20 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 621870089 1250 621868839 621868859
    0x1e02010b010e0904030c03051c020f04092007060c0e040c03050106180b030f10031202030a08100602060a0b010315031b081501031410050a02090f0418031803050601 72
    0x306540e600082040c42041258202000001d0145415a960f1094010282c40a641d02c2c1d000b1003405450032100800c00c02440c00d40c2c40680181250000310035600ca01c1d001652041d81c8035581a810b003c1c840904000382908464202c44c841075016201007030308100030304280c40c684810390f0f041d80c000713041014034060a54564003250583d4a0340d02d501c10380c08203201e040110f08d9228020980800010404a00c4900080c400c1c0c0e50b203e0044200130b01c04035180d541d0803102c0003502441d0800350f40b02003034044101d600044040da10208440c030b000400c0340f81400003942e40c90702509064445980b091004004d91081c1c002d1090100c80c42d56031400e560741c80ca86a424461021a00018880c008401050000340072a91500000702003032000510390964564005039541a204c08131284103521522462800b9402071f18031a04200c0d82c01a10349000c4410300c00c000d03050405c00e038030032458050305d004080b100b840c00c000c040360940307806800001c9418400e03d80c0d1290b03401c00344c034501c01c1100000341c442c40 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 621871339 1250 621870089 621870101
    0x4050a0e040c06030203070e1903051615050f07230d0509030f0601082d0d03060303030f09171e0f070201112d0114070302040f05220506011e0201 64
    0x100d08500c1240c0b95444004074204d0005503155000035081180100240c40d04800102d0300c40e0b50f00b0b01000840c1d5503a50303024540000111180b60388002010b080101501c3c1e00030310f45c1d507507a0710300380780b03140c072103054000b8400d4400ea01c0010004a0582d0a1a031011401c05404484a4040c0226101c0700081c82c0003030010781100001030311a01c68a0311080340781c200411018103c89806e00149450101d404096110014419980784d03482c8550386500690b0000b0800c1403558003aa4400050703041c10340c280202680c8681100d0300040d400d0810100004115000e40135009501410072900c2c1c4529444c8003102003a44071501d2001803003c5545103d02c00038200420015200741c0750080e00c0004105104d44035401200c42514500311092503a294000c512005d02c010088500001184d108000202c20348107410341da00400290f001c2030a0041c2d0b00c01c1000000030300012601601c80541044030403007500c00c0501580c5080c1c1d00c500215040b40d0142c447d24504055006942e81c0086a4401c02402014 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 621872589 1250 621871339 621871343
    0x50a0b1306080c12060112031116060809150c130b042c070c06020a050904052502011a150c0303010b070c0605040e0a0504020f03121b0106080d110304050a0e04 70
    0x6110503d00c8140b5020000c940e00c00010f40162620361b02e000c40d003008102c040039065040c00324004150001e414140212a405071400c04600d19031340c18098004c010920081400c1842c0e400440e008141e100000d880d1540003081d4490036a403100082d40f03616404115500c00c0020450215000c00d80001400c8180c810800412201c0048940001000003481e420707181000410b0001140e82c0114003d5001420703808001e082c900d213000c1c411000700b0115041219504c1560f00c4034a00c0c80102ca10f440300c9030308207800501c0203000e55900e41150f002c0581584844a10900100080e81007100b42502035569a41e20380055030b44940e55146049215804150304684800820001107203143c0140b040e02c003560a1401e04000d2581c2e02050b6200030b203405001a030780050400041580d0343d604011820302c0808100f1290346500034405c0885071340608400c0d40d0016411300703000303004001000580413000111450403c0603601484021811480340340c03c241d401403035440e004100b43c3d020051090203a8 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 621873839 1250 621872589 621872593
    0x60a0e19180e1207150c0309211715010c0c030501181a040c0909050a021002011e060e0c180d06020919030c05131805060610020c010203030a050a0b130608 68
    0x30007011550341910690308002c0c80103025040c8001c2170031169010000103103043c180000c0540c40c1d43c032800e003075030110081c0e00e040034500401d004000b54800070030122003800807140741e21414207081c1141043c2c0e034419030701d04001ca440b4883d000e02000b0380303e2200540e004030080050400c0341c5130b1011a075031f0280c2c0c1a50b145219134181d0302500d5040584910480d0414074520348142403400074406800e220000351240e104609c0081c01603602c00c0c0a800000000c2e400001d448007414902049814400c011580410300c2c0070700c20003034021f41c071a486610028269110380e0720760b62810580c80038410003050300c1e044500c9030302200420101ea8020210388400f2641c544000e004c1e100c0f0300905030b0071408000c040314120390f010801c50518510044000303030b0048001c01c807951001044410382441d107106495031792048051041a041c0400c90014000062000c0c1072441d03000740000c4e40d07a2002610018245039a20002461a0340d1a8443e00d009040107011250840d0700d030300800302500c0180503a110724 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 621875089 1250 621873839 621873853
    0x60c09060801030308060609040f0c021b09010305030a0c02030307060903020a0201080a0b030a02060d09050307150b060301150f03320a0903170702030909010909030e060a0e19180e 79
    0x80c1e00609a5034101e039815038078200b2a0f030b42c0c10103006494000b01c00d003c0e0410b4035010250780b000c019009854a03980d56a00602c404128421504042d280b4281d840780030300c0c0e003600184041080401158400e420341e06100907240d006d031000c40d00d1845100e1014103001d1808803100109540810140d1815000740e031014410b03100d1091040071201c0440c501e039410750003018150300505016000d4201000e02d960002080307d040d88400b800c40d8000c2c2c40440303520320014114901c034600c03446441c3c6400401d0783d81c0e609541c100812400c1180482280c103023404052801c0483e01446900000522040401701c0c9814110151088410402c00c011018980d11401c0005003080000c0c800d07000480d4150f6104540126210a100c8401c20702501c0c400440c003040041500079103454104e0b50081c4044040015924424140185090001094240320b4035040001600183d03100c005a11040c0d0110f0302c6000104030440300d024000c4d0700341d005a00b034041303d0000c00701d581300d1540180c01d507000c14415a001 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 621876339 1250 621875089 621875099
    0x80108100501080d080c0409060b0403020414010302100c0204020d1a10030c0f05130509071701091509021303150204060e060a0203040b1b0109200a05090a020a021009060c09 76
    0xc1c0c80d002d0042800c1a4848007001072903030312034030303c0d01e030842d20001c8454606908d80c1400000c0d1103040d00300b143d418030009420000c45c1014429603440ca03601a080303510319415070740020349030303a082c240c000308000c8450000402d42d03546904039000d0040b80001084031814922103c45186010340d6079900c60011301001d0001d15010b4001c10740454855503800649250a00050300c90780c1281020340761804a4000c0414540c03a031080300c0307008540b10313100e400c0d001c18040010702070380c40140c02c000c40d03d41c24100d0040703814101040142c00d8910000c005a245c441301c40030b5400c1d007182903002900015001e102205605019070042060f513455985488141d007100d0306104451080061840060b401084108041c400e400058400b907000380840c003640c500301c0c40207a829030b10890025650401000b4062500012031400d00741400c50035070b40200700b04e180100048040c6030041c80d4000403500010b41c400322038402c3c042d03140c91101004017004031951900300301001b00503940304030012071309009000c68 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 621877589 1250 621876339 621876341
    0x20c010501320a090e16060804050601061d04021b01110306042003040210110f061608040507150504032f03030f0d091e1401050129160c0608010810 65
    0x9003010283c141c0c910145482e800d10018008104500e2160140e0341b040d481c1546d46204600c002d0491740d8a041141c10181082801c3c03205c1a40f01b038052103070074000280d06d183c00ca8100300d0030340c03c01c480060305e604046481400da0301d040202d004055188c0b080b5840c0d186000c1001d540654801c0d5000c002d9400940310030144d40841100441c0e8800d002c7c0002801441c04c00d80303941400d9524a0140c00034200f048586260120700f01c0710364900d401c01c20410060a10030714480c0b4880555280400c4282407680b10140c968072540503018102c000d0802c0c0300403140c0910101c500640d8080c0f0318414144008800e0400d40b491201c20800021170718441617800d26001040d601c5900d200e1010515080030900e1007402000c0800b01102e601d211000355040700c1c680e1110000880e406401c408443e00d2039400820708450f8142c004c007142031310381c500100c1c0304440c07411009000f21056054540c1c41e400e40f0a1038621010070740c401810301040c1180401c0141d400302c1c101b170403149410111402d00d280400440 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 621878839 1250 621877589 621877679
    0x7090e0106060e1e0d0803070e042d060f090e0105060904150b0a1505030619120b060d241116080904110414150717030901020c010501 59
    0x7410f905078201a40c40d0081245021441d8219041d0b150503045000c1039411300d0b0941d094400c984040100403d0340d801c050200031140d41240c00b0000d40d2076059054481850b1903140181007141000c11092809150b4440c2c0e000c3d00140706c0c000c1445545150707590113855080709444555080c07401041190520980503401968440240400d2101c400c00c510014050110129804088021f0004541c19012030603000000346544065403440c02d2401e01c4444140f5003549041020440c2e820040031810009402d016940480f07060003c0d191880010360751380b80c0e80b101074503070150749203030074907a14208a1102d040583d0359802d1122206442c2074891a000e00c7d03014103030824440210310000f030a110010320b0100002030000a980700d5860102c909a08640c010340041d1404c074243c418103103000b6010b00142d18941c80c000d4505a0542e556910700019200084a107540100102d210201c080d0195140010054002c0040b582d582c65000103041c0a00040c66006080d90300e00910f43d44136904071 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 621880089 1250 621878839 621878849
    0x1215020903062d1e090d12021e0a030504052a28090501090e0c0315190c022a090402090a020909161704030e06070f060c0207090e0106 59
    0x40e00c0143e58a85800200920000c3d00e028a00d8102d01034601c03016a010001e070040707662031503010120310f810194010f040703070140a26202da480b4213041405945d1060900454011618000d6241c0102580011503d80044107440704c090002c50411301090340340d0710540c4607900400840307200300a10600036a56103454201c403050036582880c10f040c1c1d0f00744400280308180c803400711251083c04070050001c0c0010310b81c11401c0d0044e114401044640303218003c00d000c101061010780343c035202010009a171030302d84007017092052041c080011142400ba03080044444112001800040c5030214025120b000392030302c2d25402a0900b0480405c203130903c03500c80d0000005410700b0010341f51138003085005035008120b02c072403e400b00044145500c076512881c0c00b07909510529030480300500301c0075201ca00b4a4103030342d0300f8168000c100004258001c4d141175240109a540f070f84e851a080c01c01c07904602600310064045400e0800c04c3e0b10f2154000398000c2101c4100c0020426090081d0295007a500320340300d1 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 621881339 1250 621880089 621880093
    0x2307020307020d08040b03100302010f052b0b09040b01050315040f0b1b0703021f0902060708030415020403051b04020a0e0f0604030b040b150d030c030e0d0c1215020903 74
    0x41c0010308015100311810790040c0d445508090b581c4003a01c449500460f083c47c01c0c1030440c20300300210758001c1c40c128040c0400d03080c038078104040843e02030714208043c2e9070f050301e18440226134116100954482400a030002d413800f00395181c1402d09458040003803103818000d01c10000c49008202a00740268007940d0b1100107a003013080b445d2a0340d1a8004003800c00d0740900d01801d4101030302e08900004014441c400d40203010f91644400a0404003100500108442420b091100e0016a500011100b1482d8005070440d03d03a1603c1c00c20341c200b1803154900901051000401000b03000000440e01045003030111040c100070400390078081030b80107601c50280403400f403a4440c0f0440c070300b0781028484088050001824280d8070740741ca000d1050f0503038003518a03005440505c55441d2034001c098400b140140c03056850703600390395002040d82c290910040d04022200304440c2150b604c40550b22415500701c58040d861a44404100e8924001c0c41d0086074801d41e03e00d4803003454400d90094031005040240 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 621882589 1250 621881339 621881347
    0x10b031e0402060f1e04080f01150812070f0c0902030103021c03050a030b060d02040b040e0a090515040201171008010e0c0f0f01050c101d030909190e1023070203 71
    0x207003041c50780d0052041c1d0f6a043c04860000e0117034060b5032003e040108039102c024a140c2d5041e00883c3d00f120441d141349409540d9051041c0600c010010302c800103201541c403216a43c013341d0602c902c90408081009005158050001904240c0c0703401a606817402220408010003620207500f00080401d000200420028028910018041e80c4900145007000d48030324503003a0303240c1818040b648142c02c4500c0c8180301240502c1201c207484112544071035002c0d4100a5081c60b510f6407079645c1d1030718103c00003944100c5c0018046920503402d900340c204540c2043c2c0d009003440d02078a80c1440b0b40b4000c0592075841c2030307128003e100307002580e0703015200050300c1c0d403032240e0b62a000e0040c89040c600c119418080c0c00c02242c00a00030801000315600004e00c1c00007160080c911404601d481003000c6a4015801446414103c2e500c08051036040314202c680d5003440c690b448003c2018080100a041060280e80d41c1401c928605420003070460902480e028144d40315100040f80d4100f00b40c8a010060744240 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 621883839 1250 621882589 621882607
    0x80a120f0e180a0204210506010b0a020322081c020d0c08030a1d0f061e070f0309021201020a0917072d0302120a03030c0e06090d020d0b010b031e040206 67
    0xd0b80d2034111401c010003600e001c6c1c8681307042c0c46800003010f04044091079260b1900c217020040c40010702410070b8640700ba00c0d1686d081c80c000c0d5240500300d03c03074030081107920240d000400a4508040201040002e80d00c1d44840344001d02d6403004512014000342c001c8070552210640700f41070314110b080c3e000514900b143c9440c10100700034071030401c505c0c201f003010b580c010103805820080700c040d007208200141240e140814154007140c81070020b0012a0350740302c06228166410403419041051079141c00034100d6098000074030b01a0f9403030491081e5510002c1c803410056802900741c0240d8041e05070305c62030004003d204650b18401c610802c0c40f00420291540801240c294040720750122401c0d10b40d00d501d869400069a150042c20381181c15800340307d0920401da05070062038103500309400d0090a507200c010101300544584545584510401d051910855949050303800140f900007141c0c02c031030744c1c481c4649840c6038403e50ba03400c0c81442c0c0000d42d22101c2010a502d620230703540a0b00207420142a4 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 621885089 1250 621883839 621883879
    0x70603091e0507030501060b030402010806010f0915110f0c0102071206020405060f0301090510030201140903010f0c0e0109120c06210c021f09050322080a120f0e 71
    0x11010403504081c0700c48078212007403440000794030560300400141080c246986049801c5450036401b10b41c15402c103200b0000540c0c0c101c40c180f41d0090080c00c0038541500c7e4440122110303900350700800844c1514010a0a0056200c80500010304002080310346400d18102100c0e5102010b18000d401079102403010f0003225250088082202e1090501500781500c0d040084c2540d001603108c05082034000c0010030401005000e41e64001c2d103d80000b018260039900000c00100d20b00300504510a00001c002c0c40585095220480c16076803a03e0410120a2001d001041030303184d000a00e00082d2007200202e460004990b1b18000386500524501030f032850708805031103d41c03042040e500030304949010411844018055410300c40700e9503003d00a10101c0b60154050210081020b90001d45080600000500c00000311000c1cbd2500309201d00c45511040411040c04d004c0750440303552401910f24040402c00c2c1c903800700c4643c5629843d0400e20010b1018200c7c0d80d8030750050f4050b032040c2100000e038668810 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 621886339 1250 621885089 621885101
    0x30d0908070b1608040e100518070302030705091c0201110d05030f041a130204200d0e030702030706020d031103130f051c110d141902011523010203030702070603 71
    0x103d80240c2e003841c8a51610103030b94000f41d100a1810395400c08000d120b100602410002d40400c45906d103814142c1e88446900040080108050650020104207054000c6058694440001b402200c810204008a68070321500000c100d01041803c03d04021b19400810452000c501a90700d05056988403076818007010b6001c2d005881c0780c011864803a040f00c6241e940140300b80e89440300412520b0461043c0400c55882c03480d144150440366040000790080030046400001801c1000f01c2d01a100c03903400c504501c56140c0003035062240000000b01d40c3d4020400c49850750580d241000b901c0e40c00310340c5045921040312000070728100405103100040c42d60300704540440c001c070308440302600e0b484c090200700c100d10324001b0081400c0e86180c0b00300e05004c11404408030310340d181c02d120890702081581c0075806420240381400000e1600da00000f4400d44c0200700c1d5108509500c60895580c200e0303003003201480b1522640141c103d400000b440e50000085134020398656000385856840e0050440c02050 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 621887589 1250 621886339 621886357
    0x121b03041b05040e0618010b0a0605130504381018030606121103010b090f130b04141b3105010b0406080703060e0105130b030a03030b030d0908070b 65
    0x369030207000c9000c0d111480741c0504404684001d000e5400c000820f04d0303035039000040d10601a07042c24002030042c3c036a0103080301114400d04049441d148a06410b101056040e00001c1d0828541140c01c41c5403038180e20ba82d117480748000c82441003034003a1409a000b584600590507001a41a0019594a8801d0508100100c0c001d907003003c40d90b0b12552141d00b84ca20780d501c00c0841c841280010000c0c412284034044c0c001070120000c02400010304041890040004d0078505410610f000080d0b03041c40c10500300340001da100c0d4103418a4a040c5c981a0342082441403181c1052265601c42040350000c9944001e042070018507185441c0c00d0240b514a20070310000c61080703000404d40414617410f160303000e000d0281000d40001601c8509041b002013560800030210030405090090801c108070000803028190303002540e04000c00041c0201a00c0070b444c60850558042c4260000a028545c0c560301c03980810300c084042d41d0ba8075091083c2200c858100740180d03030701d5421041c8100b101c10580d0000300280d00c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 621888839 1250 621887589 621887633
    0x20f07032006090d0215011a090a0314011d1506120a0204050c12100f06034a0307210318080a081b1204081e121b0304 52
    0x810740c0100641030a4080d2200c0b00030360300c11485041c8890b014421408201000c00b80340f8075540c5051595024006504d00780c1c0001040010a00d90580341c2d128070f100907640280440540d50705c990a0540200b04400c02104086010034007010001c001081501c1000d41d05802d444c2e00380c0784e00c0c04000030440c144072894802d1062400e40710050f15140240c070310401303000584544551140c41070000c0d171400141543d61641c04100d05105590141d14080d0941d26580750014501c6070a600c104401107080391401d5281e134416004042000c0604234071415010003076292024400140030003981c9004c0c0c101c008100340003507005401c4101840500826140c45440c0c0030441d81290040750f841315803481000d1300d051100140d0418650b0f0001c04003034100b01503200c402001c00711040c594a060081c4e40d0f5401028507440041818810f021091b40d00b0001c9a21114009600c12001d00d10a6130003a5007a0540011217030000d0340b520701c03e01040b464030f6180c2d0078140c9140d0320340e40c6800c4009452803a1503070309 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 621890089 1250 621888839 621888887
    0x7030e0f0a08010b180103031d010306090e060402030d02060115030f020405060a0215070804020d0807050c0622140a030206210703050106200d0e03010603171903020f0703 75
    0x1d030344107180a801403100b10000140702002c1c80c2448840c0344501c00b07184074403403030400420000b40c0c0401d01c0c5c3c844c044080040b110300c2e6895401200a008aa0b118610440c1060b021081003c40440c0b5036004078421011a1410040303014180c1c1c6400092040782e1070f5555520824001502a8110201c032006100c001850241c0340c4c2e0001d0040c1d000364a0300d90050344161082010314490110300354210580782072008091925078006215090b01110080049001003050810803100300b144c2c850300c250080c00191189060042d00817240c0070018001031070341c5016400a107544140b8040d03010743e00d02074a0941c0c090300b59020300c1078940c80382c01d4040105084c401c0041c0760340078070290385d03015072110782e80070425501d4441d0003448403540d115406000c0085049810a1060005000d0001c4416003000c1140810010000340100301651015000c04101c900342c241c80301000c4020960003402c045c0a01e2034031910b0004070200e0080c41c602c2d00c6645d10420441c00331074098006c0203285142c902c000404 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 621891339 1250 621890089 621890119
    0x80c100914011e0c020a0b1305120c090f07020d030b0303040b070c090f06030c080309010f0e030f0f01090327060503040f08132d05040518070f080601090b010507030e 73
    0xf042c4240511840041c9882d02c0413400c61600d03c500600074030036440030a007066002c5c2d5082100b00e9951080c3c0b44100c00c2110070422980d814000760383d920b680184006103c1c60034000d481491101258003000600806101c0440180030340300381501400007900039030915003050a940501d0303010400958048001103070005038074285000c1d20458110340c8902184003844c524105100c010035400c00e100f03030340040c4500e9541d81d900020716110001070b032501c00900c03c0030320082030518000c5030307100c1a58051203140340b00808054201c3c0078181d210f5941c1c1020303a14001e614007469420801c80c8000b402404008110320391141018581281c044d0110b450780e4945903845450725030001c0181100c0b00c40540b020041c2c01150107145001c0552407440500c4144403a910b0070f035851a40c042c10f840b982d914004110002c10100c3c030345044461050440b0000781e200c2d01e9440c50f80701c6034840e04289129500021a8050807800703943e0b442c40c81a19401c2c1409643c1d41c045d64442c8116a41039002141503c1c4801 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 621892589 1250 621891339 621891377
    0x143405030d02130b070203150604020c0703030c020901050f09010611070f2702090d061d010c110d020d0507150e160503010531031404030b01080c10091401 68
    0x100107103060000694910750000c0101c80106194003071000550240190809600c02040030030320007449440307148040d551600000c00a02a1031080c0700503200d060400b10402d90404207040c20a0300841e400840ca0f80c1c4e45080241c0d4080004809030451500301c0104001402000070742a02c2483e10181c4d0020743d201c61584003524019803107000441c44503209035400c14000500707281c0300c0b116004190f180c03d810074085112802541002441e090390744900b0401d801d81008580350444101009000c18079217444000d0a2003000412540c00b80590030400201900000307044a101d0707000d450341402c20a2030b49410b00c0711407803040c410074000e445804c014808082485400d420400c260f48140100341007205040c21a6001400025528120702e2400880c10a902989400004000c0420a00c1e10980f404858042d02141024403405011030302104000e00441300c18140c604000458800c8103201040142c900000d40551020580da1501803028803840030440c20301c1041070420b40005046004040 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 621893839 1250 621892589 621892597
    0x405010516290906061011011104091b051c051e0c0301080c060408030d0513080c0c100e010f1b0803090d080c0408070909060e060708010614340503 65
    0x110044180581c03000b6814858002a8203d4001c000904d2a0314065001c5240d078861900701100344459058426800c0c1c909400020400c040d000303c40307407140c0d90f85500e075019003580c0788007c0700c42d442d40d42d02e0040b40c0e205205848150b21000b0112541d5290361180500500025002412040070443c0b000702c4400307103c895a0203003030303000340250762980343c00580d03400c000704111010710514042200308000c1c50008155698441d01402c0081c0070b86a91488600c0600703000402840d0000201c1d03041350400c03000c41c620f005d90b1400d45000c8015540c4240032100041c7e040340781030118108030b02c0e0418035881882082244048070000d80d01c0c070b108a1b1100111508100c5034030300c140d8071000c06010515409459940c0011800c402c0605040c06e10608503169500f034081c041115a50721076802c140001034002c0450034241c2800d84690741440d800042c400300090007441c0c00300d0034140d8592100022441245d403510307a4518041200c2c00391460180741d01070980f5560252100310950b41000c43c1c000c5c4020 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 621895089 1250 621893839 621893873
    0xb030f1506070227010f05010801030204052701020a0f0c15111c0603170f0f0d1d03090301061a0406030b030a1b030506060904030f05210c040306050c0f0405010516 72
    0x841100c1d041c4c4224140049016002075a140302d481d40c0802159801240041c10343e607044401103100c2d60340101c07070005000147c0560020300001a8101c916002c10360080c0f0601c4041e90300c1107180b840650065401801c0d43c1001009244e00ea681031000280070782c48507000d507000041c0685040c1d50295456002c44007009100911660745600f001042006440c092101100c00340e1182401038034000280c4c907004031035198600510004860900c0c00440c2e00c01c0080310385c124922207400c040500116525040419018003e41c40e1035004030f1400513000701e05c400743e61000369691515003400e00c12000f91000f40f1003181c061041e4210500081c010402c20304c501d400008030f03201c8d0300307107142001c51031302c80003a0106000342803074800d000109911155800028000c0e00f059035848400560b582142d400301c8100c504980399100900405250550042080b07901484041c072198450145510072445400c0103c040c24000700800c1050394001e0700030f0301492500c0030584039500750075107445018148070509 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 621896339 1250 621895089 621895129
    0x30b0307030204020a2a05060f0709030b0f090c030106151d271b07060b0d0c090507091d070e06070803040803010510020f070e0910140703060b030f15060702 69
    0x9100d4009120f41d44500340a0207029401c07091800039140c2648a0230040d01d01100e064407c00000c01c1c0c44e0040b10070000565200701c025400b442c0540085008000948541103039000d503042000c16442d050040d28103441104403490b82510000d0005d4644503443c800b0710200f8003007000d200515a503030f602a000b22568040101c000100d940545400301c902c01810f04030403000f11000640c0f4880310106460300c56a00000001d0311810000024098108003c0000c010003d150004503800c0460303000700780207456948400382029114014a40c0d80c0054526499003800144006040d262040e000c1a07600e150140074146411080d0f103c0315080d40c401c580907206648004010030280c1007201d04065000103510203403040307030f090701c1810361110140c2c0303e030500101d12000411100e29040c031500e24440301080f010804c10161880d2558804801c8400c28007080c509400090f070060b0f000100c9101c0c003c4552100c1d6030356a000d020b41c0c1000d20584100da02710000384801030058071804040541c1000b00d2076 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 621897589 1250 621896339 621896357
    0x106080708101b08130204021603020d11072d0f03050a11010e0f130f021204020f1f03090507090509060604050108070501170c0904060e0a0f0219030b0307030204020a 73
    0x300034064562004010010385001c900c80720201da41300700b4043c0c000100c0e0846100d00421800090064040e0b04d581d40011210788811500f0141c0008a8060305580754841440700c1e00807802c03083d10f0b0700c154030820f00190209000185020382c00000d0241146081401a8420380c581d41e02401c41c401540007241c540c0c0c003044140301401402c041d4030020550902c0c040c541502111b0120300e014103030b0030303102d0f0082000811241300c05039250448009504210390454880d410450903580f40b0805071000d038017580941d50550968140082001420b004060601c02018400c5030110000c160000f400c1d106400340600100d00c02609010381402025084014912130a00c501008200c2c3c5041c1e11112456100c8042000180d07005551070032064a84401a5580c1d80c0f07141c80013a19105040c07100303038414507100020645423500c0f9100c41c000d20140c01c4c20883d0005401c1158203d10502d440c90341e4450604294034082440390700007545640c1d0240035604040ea072030307002c01c003a600002400320200711120 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 621898839 1250 621897589 621897613
    0x19020607050708070308131509090519020c0a0204051605030105010804240501050111210a090e34020a021c06060e060f0621060a0b030403021e0109170c0106080708 72
    0x141f0301a0150002c41400c1000d00d0f11190041c003055034600c06c20f20541d031144001072012840040c641c03c050404ca1701075584a100310421345e207038801120128880c520b0400450b044030070440034068030001c15190f0f9455070b421f0900550300004020400c50f9030030755a82104031062020907800e4420180c4d4140819103504190002d840481540602d1001d0360000030a5401c02000c3c0030b80b044600c030700102899071100300c9072044601c0c810070b40090001820b4281070013100c400c0c0c60011001202010b540000180d5448152000c2542d00c403048001a4050744070030000d407600c1b0000c203490320002100100c031011a0f40c2c41c42e05484003644011040202001000000e007406c1e0f841981c11a01224150f24041d100d0101c03001c207100003454004180d1000d400508592a00d1621401601c840741000d5203e107041d250007503503640d515098140c03144214503501a02c11050180c07603840c41e4040740c4451070a02d401c45c01d860b20341052080325115901c41000140c00103040c4158400340405502808500d855030b = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 621900089 1250 621898839 621898867
    0x1a0315060d150e13120f03020c0111040305120309060a0b0d060507021c0908031b0316110a050f0319320105011a07030f020703020901170601060219020607050708070308 74
    0x18420001034600200c5080040d1604c205e071040c80140d0b04094141054415084000340100300c0b81e00303010b40ca024400189039950b10302030401ca07171041d42118801d0020707407103014080c04142d6042c030071a4008804582d840c1019085100303001c0c40a000c05820744206c0e160b40341170b20000d03101c110240e048821141085100341c0c810b40d54107055810b214000e94980081140e030307842040d15440714541d43c08030200d90400180121082843d044001e0a41d441c4241450403401c2401001103210340f1200d08000390904045c2058500c05100034050407403d40c0301c8003405406801700400311102c2c242094005490007003180080e49040142c0302442c0d66904901c111821600180c01102032911303402440d6400e01c41a200b120642641840e014510440340d100592034410f10b50002544a8140e8bc00400c00c6602040307055011110714003110000d03640c89030140e0700c485248880c2e0341d10b01045c3d020540035080450050260b144142c003107405180c0d0702d08081342024600e801c02c880980000803060328140710 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 621901339 1250 621900089 621900091
    0xc0f0c010504050103110c0d0513091107030507141002090103050c161b03051b0418082d0f0c0f070f0e0403050c0d0e04061a0315060d150e 61
    0x1040208022924040041d206000b40d01c10141010b80f01d42041c00b0026880c402d44500340d900c0400c460640d00041d10280440d040b030003d180e1500d0208000081010240c00b81d6400050030b00c504a10f00003075602c003102c8585c44802d0030381d41d40c54420362001851000308007604200c40d41d0140181c842210b00001026580090442000010140a030400070040409082e000642c46040c0008050409507503a43c00d8049920162440c0210b080c19000d08070054403941030044200c1e0304020010381c00200d880c010081c2c00010b40b00000501101c2040d641c07500e41c444406101081c0b48044c2c418284410701a50b10402c000003020310040351441492401b04180b20503030000320003408141d828004c1052121a043c400d000c4032110700f9003c80d083c0f500840031a0b40c115400c506031100c902108102505500d071000c845805030707150100c00543c241482d115000c0f51060440002e14546680c84100d07d8100e0340b4800031340c400c7e010425044404014458455804010303403c0f00781c2c162130078110012684c0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 621902589 1250 621901339 621901363
    0xc1507090b030103120c17030703090311150f0c090909010b010306120b060d2307051f050405100504051c11040501050607141213170d0c0b060319080c 66
    0xc0030b00050001450b44003d807101101146400c450070303155420461140b841c038014050f28200004188001d01d41d15800c40b8522078000c4d2100008600c84800c2145d6070710b8a074000440e10f0f001c5030301240c42c2d8204004900e1b0440b1520215905281459001a40c000c2d010b8a0a4582d03030743d100c4c80d05e00d4658250080d100140401d1601048038459a01c0b15480002c000b0f040a12400310300c00c4441c100511219001210040c0030845003111804462490307458106000e503034464400c0c08503c00704e500303410540c8800480360359601c9040c14581000c1c800c404110116400034441d007400042000c0d02d81070f004034608112030307240040351581130410800b0700c0c803680b1107140694245001440561664412500602d078400d03c0065110450503d8500b0444204221095a100045e0128040c4482c4202070300762b490700160050003402c624851603541c20300d80311f140c01040043e80400c000c5034030601c0701688800d0240590340501c40700703035811050b015600022540e9040229981829001c20400044030352 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 621903839 1250 621902589 621902609
    0x62306030a0e10020a0509100e011205190f14180703021201022803110405100c020f1005070605151f0306080d0c112407060b0603100302010f020a0221030c150709 71
    0x527600c1c60008010400008031020340e29101c1000c1005c1b83e4844400d003600384184001001800481041c0001400c0f2541958000c1d684203404110311070030740c500c12000005104020400b80d0b203540c2c00d10541c03580c41c401940555509200946841404603034040500102e5080010000d2000303034040d0484054402034860740f84103210a01c001c0c0c0b0f80300d01500302e1003810b0800000280300da200088a0442c0c0311101501b08040f8034110030b0301a0840098092284680c0c03062026a503034000d0610700004441c0c41580c02031421326010441107082c8007200c403c0000b40f0b40402c8841d103659a0f41c0c41c2200c02d201d4100010740c2125500e05100d2015955442c49504441600d0001c4103d140c0c40145985203920802201c0005a00c0302000f403603500681c1d4080005e403080381c40e40745c02c0301c003040d02881601c0141d02040c804040d00901a1010400700d40440d401403038240d0302701c0c1d040c00340e480607200040d04841a00c410030420503030840c00c020500d0030305490401c07101e60307180615008100030070b0365011407510 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 621905089 1250 621903839 621903857
    0x904090606030c08160608180f060118090b010e040201020f0a0305092d040e010e24130f080714100c02070803040501090b07020d0c0306062306030a0e10020a050910 72
    0x70700040c17066541210024544a0300301d0b01c480b05101c461603a0610449051320174a80a41120100414414125007200405188020030300c020700003034400c1800000c0c10784e52130700010303c08019900c10041d00140188100d0781d248244212151a0402c10801a00850070101e000c0740e152500c1c000f40c0c400c42503101140c2c500007043ca1003c190b20b103921032005201d282c4584848062001c00d40c4018161000c00048440144100412940348003403000740d4000701300d00b0000030311040c40e03000d0034075511780d80000c0c1c1e48040c00320b544801d88560000d4504070744030750103100b0300d003009102044501c08030344072500700040000a40c00007030718050703035a80300800a410600041200340c0c0c01480744c0c011102907101060b9542001e1000030348000c1d02c5600244030b501181004002d0220340d500070001d55801d20741c10181c0f0700031a0811844e00c841c601d080c07940100c04000080480c5090303042107205102d080b084828841001300c51b9800d17a0009200d050010b4804a10518a0316049000c0c3c141010103052031700007 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 621906339 1250 621905089 621905113
    0x3120f0b0f0112200c0c010c0321020405060301060e03060f011208071109040311070506040b04090f2702150408030304080f0c0d030c0f0810060c06020904090606030c08 74
    0xc5041d400c0e001906109901d1004540305106401202c070441c2103400c01c500d0003d111111007144e4000800ca042c00384140e03254106154007449000b00c0043e090f840e04a1100603007892051103401030102040da07560203110001d0651107000195028180076109c540055900000f0b06d0f103062070007081024049050001004403680c3c05101071175058200c41032a560308a03030306110082030008822142c121007102d041005240d4084210645408402c064400c010707a42e104001c0c0e64000e5003d8410030316420030041249464a03071058000360964100825041e4000411035403610200c903040b03d41c078850707480040852a003d0340581d00d2101c1950182d05060501800c650b40703020052009084030400112030140010b00f006a52442c01c02a040b031341412020708005010f040d100c3e920001003003003400303031100c4140610310440c0310300541c5040034121071905104a030242154401558815420017105c51551114015215907038003c21000c0ba078035155140103842d401890f03000a0440e004044d801c20 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 621907589 1250 621906339 621906349
    0x2203111209130c3e030309060106021216110a0920030c03060118150c0309150c02151b01230f0a09030512070207060e03010b0108010b0708070f03120f0b 67
    0x702c4c2e100d4003500008418201e01d214400082031800f41c3c0c0d201e40500100341d4405000000f18030800307a20041d54403507603031110180c0e82e0b02c11111001c040c42409120b0032503029006014622210702400b03005101d2044c1801140f49244540c0012460580300d0400504810344120034801070701041131480e01d9071a00c00b1070000c2c14080a4078842c10401551030004c0b010300d8840c003903400707402d140c801119030482130040a8404000d0210072070108a076024002a0386620381d0b000d003201c8103551166003020500c2d50070042c4440750680074001c15582400820000c2d0710044801115002440c00045c005008908000ca241c80b480f03070281410000c3d40821480d4203464a48541044bc2d096010030440600d103002d032194000c0007451131240c0030740000c00060030b81c0003401d0821501d1984078400c007040c40c00c05050a80b401403460602040b095801046020800c500030986076010b20302c0340382008016030303a00045800d00da0303003a80058001c08141448803418812401e240c100c1d20340410078200044007080d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 621908839 1250 621907589 621907607
    0x1215050120060f09010908340f060c11010606022b0903060507030f0c0503060a0e06060f09130c0f091e050d050f01020408242203111209130c 62
    0x1515142c0f40d10042844041d094004c1890b140c0e0104032540c40d803603042e01603100040381303850100c4100c01201620070300c003030503c2a001c07403290040580442c0150540f11072001e4491015948200549114050343d13181080c82120060045035001d40f502d06212000744030300c48007000e0300e80c130350889a130b004110090300f00780c4403021039a2146010580d03580d013860a800425040b0010910f681c00c210480c8441a07002c401941700741003c68942213015150022a09082e00440303510f44c00010422005a030b48440304042d003000d690041840e03126628006140d030a0318040200e100100d10415858132500d86c010640d01c01030306244085054114407072003201175840462240b41d0081801d0040e02007402024028521175107172900c02955a559180305041d9900b41c01d8403100c0090100c0083c00507180660340ca07190141000c3c0300091b40000c8809179642c0c90383e990780700031002e204801e0280520400140300304904038282084032515a9060002d000301c0d2000741000c01c8075940b414000c0b01074290171040314 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 621910089 1250 621908839 621908851
    0x213090e03131a071b05101e1e05070f020a0609210f020f0102150124020303091e101b03050c07030f0e12150105030c2b03121505012006 60
    0x1c2d0070034060b00c02948042c02c15070401078206005035030200713541d6004002c50704804a48d0f079145e03100481c2031200701c0d0305180b5150200131740f0003111409504103214801403c0014060700440d400003e903940012000f0b4825802480411180d503000c100164940841500c2c200144214007444800341e60f56000700622440000c1c86882ca2003000342c2181d1080100d0b950b50f10440e20000502d5865903001c200c0c94401d200c0899041440391849840144040240c0b4050f00184000b0586038080700075107c0200c02d070060fa030340117108507200d040d80f1610500a0020210054500c40c506049411004041c0c2d08000d0100ca40040204034800001f0380c00010410a6220b0349440408108203071300180d40501c4d50015800e031445484420303210440e0b0341e084a8100c450486c00c5a5101400c0c009014451103851085402c001c9409203603480c440c01d00c8200d41c800ea10a14140b001c9002100c0d885044407160502c804648410003800d100b0380d41c01901e014080440d80030350b01c41403680a40c210350740300801084 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 621911339 1250 621910089 621910103
    0x412022706130f0f0e0c0301020702090a09260405030601060f020a03110f240601030b030714010201020d0c0c0c0803040b09040e0307240b0904020f040213090e03131a07 74
    0x50704400b0050391080c0e80100e54480c007401103607200140d034030142105110010680c090080c030812685014402c8906899010305010310598070045200005c4c402081c0644a084140e480070f00806020114460035410b20750a013600c4074245824140381101c140c1254090001810f10032000d00d4000810700f500d41d62520340003050010000a05c2c1c100020040300003200d220703a0a6000c1c0c1c1c4e41035021000c0703640950007080a500e94448004409582ca182c44c1a078168118010501445000ca034000601c4403040c00094038144948801008a032401180c12000440c06a85a0200544664880700074401e00006500f880d04011221025100b181001d0381300d03aa0700c6500d00160300f0f040c8140c41d20b454001140a05010a29607806158003a86107110350f07051502d94400c02928145001c140a61b8014103401100816001404002d51207003480c644142c040890014115941e4081c00482c9288200134603143e6a503540e156208030420341203961510843e02c00038107003031000030030317602130540060b5 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 621912589 1250 621911339 621911359
    0x60f04180e070e0631020d0b040c200123040302100903120c11160e1f0b0d0b0406270b100507021f0206010f0b030f0103020603060a09020412022706 65
    0x21750980303000702142c0c0d00f08403030780c00c50344065080995501400c42c0320040201404400754150800041711740303100e10800482c1358006510901183c080d02c0c0c1c4e00d40001d04000049600030b110b2400c03810740c0111031040c3e8030801d013810442055030500807100701d8800c0c55014000344006980182010540c01c080d24001039503103400e240a41d21414684400043d490709070350740d8407501448048038007203d00071084135030b0070880030400c140302010010290001c0c55000d182c59500300144000503030302c0b403624020300399202c802c165215904c500c617200080500b001d001042c2d43e0001032607030100709858800840c8900c1c2100750b40b519212440700851846071407412542d00c0c00c040c07000841c036001c04052507812610071010341072210740000300d25040c1c491400c400d270240ca80d05d045410a0780310032245c0d642c0240b80c44004100505000006d9a04000014a0444400d0b150300905003240c0040e40703c2c00c0041c0020b21500c2c02d50030410450040c1070814828500c02500501c0d0035412000084c1181c1c1c0a610500 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 621913839 1250 621912589 621912619
    0x1c0b060909030f03090102040816060903031808030c0a02090c1201090513050a03090f230d03020c1002101508120304061b081e01060905060702060f04180e070e06 71
    0x4030450f140140160420340c0c90703007000c2124a0003074200e40075102c0c0c98801c5841e007411000600c0c1316401180e040ea5586a50a401c40c0c3d000c0319a00c9440c1030056141c3e95080010482c0d03982400501548018138005020a5501d80100004503e01610240c0310000401207a901c0f880ca000c2c01c40e041d41c1440c200030815480703c40c07418000d205d922a018201e80942d40303031a410103a0000329102114480301c0018445a01c1e200f82105500d018400400c0107449401d40540754100010085d680502a00507074a240b601440803d9046d07200302012001a0402c42c03c10b64010104e2098444a0809440c0c3c03880d400e051000c4c1558a1100805604100134080005807c001894102c001940c0103a0b45d141e401201c00040646102e0084d175a0704010311310903020002c03c240680c2041d048032060b03a5030848252819003440303d04c0d482210140d030030104c200031040e40451141d0003480104003081116542e452942210401c0b00e070402040e141d5600910410404804076048840c0c11080c100c4880500c80407107 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 621915089 1250 621913839 621913843
    0x31a0d1e02060403051b030d120b13110a0201180201050406080a0207023f0d1101090503030c0310080c060307051b0d030203070906020105040203100507090902181c0b060909 76
    0x44030000d500941c001400b004018012881c1900e000032030524070800e0000c002050388480da544240d10000c1e00030340c0c61001a41c0d054004800940d4042c0403124090a10030102d81600c0c1c0500d664003d01c54000707103805105509110340605400f02c80c00000410030765600080961059100e20400c108420000c101040410341c1290900d0b9401030800381d0300702003001c0600c1a440020407909a5038000105a1034420001c1040901c2815800140410342154207083d1000005085590300e5907503504034000c000b6100704021400380c00ea24035025100e162044400202800940015045400c03403120068691507100130b490300007096041082e21060320410350b225030a07001010400d00d109440d40321101039099030086008000c2c0350b40781e10120b03407202c0302a402d0300c2099030025013640c400050f101c80f5078000e03403240390448090f2802420341076440700c03030341d00383d80094802c40700010034203903040018605564003242441111b4400010340c1c00070340b41c00c886d410004000300d010301201400100c00d5001 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 621916339 1250 621915089 621915143
    0x90b011a09131113060c02040f1b0807020307020d0f050c060f0a030b06091806010e030a050a062f041e050d020d020a1e08070f0509130c05090403050a031a0d 69
    0x41600c82d18113540d11031006056050220007603015600c0c0c411040c0c0c0810490040310514607a0000d41c0e841801c02c0b840440c0c8250000748250118002446800c005948514506400d6070040500302003004041c2006420111a080b01c9031054008003d8213a2042800050750500050742c100011aa0508400b250080c420140920b900508000c0100c0040351501c1c003907405810282e03100541010b4403800e1540d0703002c52000150050340105003040000340507400c00308418600802e10740120300b5441400214517440c014001e011040854140400445925030250062200c00d01c0c0103014038200126086045520b0017074050b903504070003a02907407109081007008001200108203540c18030300400b8040c101d1406168040d006826001440c0b20300c2d8024001943c80052180d491902c6240400c41d803220b100c0c0d001c86e440c00c483c1030009100d945522a840c410f9009448180d0390f514019801000c0b02c4a100615110f514a49a404500c2c0c07100f500b0300c0095a401526001d02c5100100840c5001078 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 621917589 1250 621916339 621916357
    0x121e0a0c061103041205100e011a06160f12020f031905031003080313020f060f040501080a09060903080f0703090822080a050703050f152206090b011a091311 69
    0x440351050b9040203c0000c401f007411099090030024005d126000700d003611408080c09072000c889000d1110145041d00080452604003050a0208140ca44c0e030404425141001560f41a141d02098003405405100001000460102940c505922250000185014400e46c08200700e0080009044030404c0144400030f150052400d030303128600345c0710490704540301030780c04ca02078a000d065102030350900700c007501c4c00c86400c5810a410103040070011035003910024050b9100c0c603100d108820218004d4030482500502aa0301c00895282120042d080001d000d0203c0042501d010340060100300080152030030920004502c0c07111008205040c04900011740044080e4000c1d280b0640801030300041c5901107911610070b960790006890001030711000100d1001d8101070040001a0b0502c1c404901c2c1c0d50030910200ca09110400b60707440c0c01c0d04417420504100d80407421036006110007001a8202c00b803a5502c00b100c645000c804034082020f420301488046d5440340c541c03555907a500035080640e0a040 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 621918839 1250 621917589 621917609
    0x807021905120f070e07020a0803092b0806090c04080f07090608070e0613022b060911070b06150c0106260c0d080405121e0a0c06110304 60
    0xd0114800e600340400144240c510589010090710301548000c94403c2000351502c0181202c540b40560043c50308000921220450003000000710000d07030480d020b14015080780c0c1c000c12000b42071448841e4209290310004690720518840790015640c03090216500140030b0301c0200c00303038541d40045190340c05a90004441c0e801307901160f41c00c14100048a1048400030b010034002e86a03941d00382921040c5a0150050320250400001c3c0035040104c02003590751061500149000325222560707106c801140c25100c0c1e10b86402d0002d49403580d2074001d10020b030288140403c04902e0302e03440c65410b40302d1750500900d034082036000a8819650202c1503a0499840c105040e80e4001c10b81c0043d000b00051301600c41501401000150145d820380030300c41c071140f01c0c0c030010a001c1d80007000b017140b000040401115030610801c40411151a007003010302503540542c00401d00c800140ca40e690040b1080c0b21824000d5100448950106002d100400111881810f081600403005003041c2d00714810f0f500458000 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 621920089 1250 621918839 621918859
    0x1112010204031a060a051c0320030d06080d02070909020f040e0d020d0f051b012705060c070803010b130e070503090d0f09090b0102010603020d060e1015030f080702 72
    0x100400c0b40c0c0d00c030400b05040b11810304030b40d601300412207140340c80e010301a00010302d4200d01d0900000c4009101040317010f0b04000010004100d0010b41e003c454103207282d807a0f04007240c500070f408828001c4902400c040e01c05090310200d4107200030354842040c45010319040e1902540b40c03e41d19003540300e161168001c0c1061107071420f84000903958030007002c0744000502c00c10f441c0e609040e106902411184000b503035000d240020300034415141c0e4220003113070034107175580d004c005081c507041c04076858101a1f509509540f248030b50a1131070a00200030300c0d18000c0c0c2001c0012900041c9410212815940740c1e9100f07076142c20141e054225106465041805920040418000119044005588203105400031207241c00006081182c0d091100032203c2c01286400005000507461038002018498040c030002620603960b0700018014100301d0002d5070603c0d560305654800b100244120384016841000901c0070f20001045064018450300c0060080030007804050108001c05045501854000389a1103071 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 621921339 1250 621920089 621920093
    0x4050301182607061e15080f030c1002070f0605070507021e0102060a0c0327050c06070503040e0a0605062101050d0f02041109060a050903060709030f111201020403 72
    0x31125015609441d0007241c02d114581220ba5032001d2503a0780e4607886000d0a01c81503503103130ba002c3c140b0b800c140068001c00b018401c04082ea903100c1c0c69642d00299540c51040362804400904009520300b560000d0740081041c00840c0800080301014612400c100594440d01d038100a500c2d0030070020000e000d00d04203410710509036030000c0903050090084a403042c014002c1481003886200c8000318902503042000020803480c941d43c41540c0c15403c41c00e0100303091065001e031244c48032400c2d550720698800060b400041c42001c204200312024242c51003440d26442e0f4031410385da405940700d043c2a00792840c0c0000c081c109503030060300043c54042c0c0f0b05138031400366412034200d8501b11400340c40902e480200000b00c900c1c1c40849110404e41103a05221a46500d400384800381c2441ca291075100300c010000d203901926008020260b00003181e41e406e88512040f810182403100203050703c070800003003000510100b8800390851000700d500411080c42254020085585041c09501d501c513594070115001003 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 621922589 1250 621921339 621921371
    0x1903050604060e070804150608030c100c02070803030f09010605040c0302180306010612021e031003032319020c03030a02030414040204030f03140f030a14060901141504050301 77
    0x20103188201c40500c0280d8481c082c0c1e0024410071121200003414030404907002c01d1500c85000440612554003260103070701d6045240c516440311603803186540c42107040c4241c122840c41103100c840c1403440989001d624021005940c1d0101900a00e48180803030049021b8850942c0304d20010000a88180700d022512040134009403c00149840c95072000c1040a001c2d10700031510780c0c10b8804a484021703444a030380c001c900081d041000d0318014140f8075402982d10b080d40101641c4203070f00b840ad01e61030a90462034020003501d00801800e07040ccc406c0f07041005611724420240d62424050300000c40d0a2078035003000b20300c9e05280d1034007550940000646c25098503804001001522400302d12400e8031901c0b04180b10803886503100c040c0241080e40e02c45000071b8421610320f9444010140118200b0200750034004160f1b10641708290080d0382d9441c00a55a081301c3e00f00d41d440142100c50170f07425850508940c40344044840b4162041401d44032034101515588282c502601001d002005060035048845d4 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 621923839 1250 621922589 621922591
    0x41505040302120f0d030c0e090a051b090105120603010b0d0804140a080c010807180e151f0305060a09091b120c050f0d0b040303060302013908190305 66
    0x40d0051120881d01c3c0318a00700000c80c0c8880524200003000d403070340d4840d006c400510020850070208090758900406c141c1d140710341e081c000c83e8241000126810302684034a554145e120311006e540740f0030f02c00081182e03004420344480400c1d00e040c3c1c0c0060342c3d90200103801442c040419079404083c1c8007421042c0010400a40117544c01240b02c03242d00103011003004064102440350b0100d0364000c244d1844903510444045420030b0703560400a8150ba03900313041b04000b50b50f9404c9080b03901003810403c44090f0275110740a50141080d174541610151015002d40d1040300401d003c81855100c20101c0c01a840d0b034241c030310082011034000c002004640c500a80341d544192140c0600d903040a030089444100c0700901d849807503100c604104801c0c58941800303020700c40c0c2020298071106181410001c030381c0c0001c1980c0304501c00d40d0000f0300c0600b544009801c0c00c0c0c40319051152800c0b20080304204401c0c40e841503030504c8517980100d40000b0103141c4520944600035001c1c0b400303007012040400e42c6030541c01c21 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 621925089 1250 621923839 621923843
    0x40905010b0a06211d0d031b030c05070f02030f010e07080607050424210c080f2406090607291e10051504090e07030201020c150415050403 61
    0x42c0b520b541d2030004031003030f0086600c844403082c4883c034481110a06a0302104071040c2d65580d0304500c0c2d10306440c040c181840c50f01c4420209449450302e41440840800e01002e11801d030808101c05107141000401c140640c040051149010401c4c2209542d82046481b20b9680c1010092107800f800030328951304d425007481112218031490300421491405401900c090b10444080320b41001c2c0c2d81414240e450320100a210706100451709041d1001040c40036003030b4107a080c0c4402244003900b04100a01c40c1c02c00130000d40c1c1d46046c000504c074025281c01005a0a0800c9500050101c42030500080c0c0d00d1080e0103903107070f0003170000405904000300c050031801c240b901107500ea0190381d00c1d00880810305808030b6a040c005500307294005021982c40c1200d42d0030480b92541d01181540762000700e00c88458040b0140191070b0081800c114006450081207911141e10f80a001c4807465640043e540b1449180e80034450040343da41030314507080320015640140b50881c0782da00b01c40c246040140482c0d0143c001 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 621926339 1250 621925089 621925099
    0x608030313020a09140609070c08030127060b09060f1c05060a0909030503070c1406091b06090a030b071806080105010f021b060a110724020d05180402040302040905010b 74
    0x40010b06035420300c509542c980c44e005c1040340c260b440c04100150710748024136072000c3c84400c0402030041030402c3c1c05940a0141d8400d002c2541c4824041d2455040010302d0040c203035030a20a06110a600380c0040d44e21240b000c0d116551280401c603c46001c9004041a075181c0c0c02c00c428501d0902c201701e8000c0b50040382c0603500700c40d0654179442e45006540c503807034014010500c20804544018400c08207283e031a402281c10004c810206008581400c00a45801303910740c3c0040c0c2042842c024813281c40d09a01d804076040c074600300f004008a00c02c80c03020301c005000010841d0001300c0c124040c0c080300c190082d00712a00042181c4489000c0d20060080c0102c42c001420b030a07881c1d5a903170002449051a84e00034151700c601205c0c0c00100105544903540c45800c1212040307001100450801191002d0f1000e1140c0c6070244c0100907400084001121101c2c0031540010207040f2501d4010040350410025507204500e4000d089000c01d0203407050b580000d400a00d089841c009105041d0b01c410813103002250 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 621927589 1250 621926339 621926359
    0x9191803110303012102010324141206010911090d0f031404050d060b04021605070e0f0f0a020705190503120f090d1101090c0303020a14011107080d060803031302 71
    0x6140741d501d000134001c1e0514425940803001c08507004011030004a48140f40100b1307001c0450081c605001c800c283d607121111000d0f0414131840070f2816070601401c41c241c9512495501040c9820303541c840610035414546d60781c1043c1c200e101d11303810807100120390242400d5090380d400e190080a04039003110903400554150f881c9541c00405008a8007144c0d00105054034824560f00e0b040020f00707861104543c82070b820000e00404a01d00325484041038040c0313000e4a601490242646244200141b030000741c071070174070100072265603002a80790b041072b071100d0300689400321440c00915081609100b5800d444445008104002c000002071a03050f40c1c040592050ba01c0e10900d41a1114099403903a015420008080041511076120140301525080010800e00070b940c86800c0c001c0007039001034005820a400d60028403010703210a40041100e070008102c00e08070849048514010760400034108980001c2d01c1e00c45100030380001e809040b48409030382c0c1d41d00340104140c110718006502240a11200c2e5 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 621928839 1250 621927589 621927617
    0xb01050103200306190f050109080303040b042310020c010c02010b012a0803070e0315130b18010e0d090f0f06270305010507090e040309030209191803 66
    0x80603500061880c01c011211040c641012040b054000410094202ca111504008078400c080c01e00c40050840d03080c0d031030030642040001024505107412650180d4010818000004d0480703503082e6006030407100c0110303070940780c9900c0c100d82c1201c0801c0c0000703031162440d0080000c4241d4020312440f106100200311400c0c3e8904103a00b81c941040101d40801e81c00e807115200d584030041c200d03002b1100c41b001000242d0040e541c000312504192141d0002915200c4100d2042c1000c10000c1740e440408040e40c1d4452915680c509207002c20720030300803d41c4683c0004680c501d003c0301c0c2c900030032102e00070003404040044050940c0d54011402c0c5000014209030000406441c061501da05442c507035080d00c01040d003020382c00d0380c903900081c45680441c0e0701d814480c0803400f1500c01c000b000c2e600c1040080341c242410315001b002c4041c01e030044007880020340e007804006608010003034122907040d1085016550340110b51449514240e41c840c040600f0080b030500c100c1310f80b0401ca00e09038429101c140548400c0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 621930089 1250 621928839 621928841
    0x1062102030a0605070504211a100b0d09060e06160908070509060a0e0109140c030105060313060b040e0609070e190f0912180510050d050a09021503040b01050103 71
    0x40000c0e40581014041c0804602e054101d141c0c001c40710300300705180c2981c0700841d090316040e170700105040b081c882185008021081d448801c811a444a4508403814518411200b00707000344245030503001e0009846100c1c1c8050340003003400c0c0703802c408201314400c91580c229446100480c0c44001c007202d05910705181d40c2c01803403140191480d01008000c02070030403041c0110a4005004185e02210f440030000700621060001c81c003070420140b02092a8031052801c3c0141400030b004106d0342d04050005014940f02c000580b58040381e00800c16440441500302031004000c7d04551580040c200306806010707080c000750040c014031001003112803203a80c07584c2100c40514141c61070411401201004007480c6000d401c8442a00038403440020080c04c4d60380c03003591902d420041d0202043d284074a040010091114000051006aa50000c80c0000b82e000030301038414a2038965105a1b500c02140e440c25482c2d01c00c442c420b0340039200a688080e6003406603917941048800310b8511403000000f2a0f00e52017 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 621931339 1250 621930089 621930149
    0x50105030f030d090203030408070617010501051e0a09090c0504030212190b0405030d0f0c110a03120f0e012310030b06090718030c080f190f0f0b07020106 68
    0x1100c019604108a40c100f55000c0c018210090346d1501c010703c4003040e026014041c100040c003064440903004410398100640d486016805641445428842024180d21103107036078825288802b0b201fa55018200c1e0161082e129035081a81c8403031a154681c46020707040070042094a00886420300d480384a0707652603036600d54100400240d105031142e500d0015049102458000e445402030302d08000244c0100c504a03a00b5418410311191140c40c8201d0b6190800c0000e440c0104035400b0b440105c81c162009030a240f0004050b84606541d0383d00e6850303040059000211054051000b44503000c403040d000d8a1003200355030141c0408424002040080c16485420b9003100e50001e600440c0e96a0f9500700040f028000300210144806151030300c071310b10f000d94402d802961141056402603801c01310034500c2c00200c0040b14502e94400564541e6100801e00340c112010341c0b20842180d4018507107841a80308054007002803210011702c080c800c40079010340150040d50710880d031100c0200080c42c442c13080c6600d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 621932589 1250 621931339 621931363
    0xd0501061701063312020705070509060405091b011206030b220c06030c0c2910080307060e120307080411010305160f09050303070507180605060d0f1d010f05010503 72
    0x13010341e908500284820340348002841802c024040907808050b1005a9001d002c0c02c8405800c0ba040611440c50b19060140e04850180c60401c01c0b494000012540c0d00e005003111082c000070180921000d0384a400b0034681d2162000040c004560340340341407074205c50300703039080000e001c01221110810a40c5040a00c0d0103500300301450070161800e88150001c28140082d2002c10140203c810085604403516599521440d40390044215071810004449071015140307104a440c0c24800700315100002090354a0540c0108000554481e100410743c0b034200c0594a01000e56030200401280780d40004c0603d218a01940b20000b000801800460803200e0444800c1200b00c038681d01d984405106148542c14501a8103204031455225130000745150081102102ca503846214240074400441244207540781c0c0510050040303605050000c4c5090142d4901c40c0200c941d42c1c1c07a00813072820b0301d8002d0084040c022203a030241555065820303020348900e0720008911801d100002551342000212544246 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 621933839 1250 621932589 621932639
    0x1e030302030109182402070f0f02040b04330f06020609100c08150d02031024050f19090204060905010f0e091f0503010c03020a170903180d050106170106 67
    0x480e809080c81c0c4119040e045c03c196070303a402c0c030a14000a4145d101421480c0c052070889900160030720404c4280c60000810a0040d800d00c02c1d58442010b0214411545034042815040408000c180350600b4114662010000f041381100000b61139401090040c020f0f8845419103a03038000081c042019980702c44812400500007a001030b003512910039042c0c0c1d01c5031005120741d842000c1500003915040d00c00419032003040c0e46000c009250144044100d0b038450038603c1e807a44251614000039465000340004034050044050100281c142544004000e040820000c544403078030b0701c800801c0071045000396404140440c5110509a0084c2d0841c102c5100c0282180b10582d1036414910414184001000c02d100c2d2020020482d990203015000c40c4012a51f00162141e0084000600446c1000300000b003852459041c80007070400070080b1000b00010a0404e82c0080d03940e130114402985a00300030b01130354030f0988003181c500740b0307030039030a4466000030024401942c0700d00c3e55000d42c4051148003aa90 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 621935089 1250 621933839 621933863
    0x12090618060e0105070b01080606010e0909060f060a0905010b0d0f021c0c03020d090602030a062405030403170f0108010b030102161202010920030d0f080a091e03030203010918 77
    0x140b48a8000341c070300d03200306140c110b041001d143c0c0c4d1810030000c00c0e04452800e8100904112030b0f0359218a17601013009045400400728245500d6140d140e62014180001c82c4080c000050b0a60f100d031940507005060040041181c1d42e034038680c405441e0002c9138403481d52401e00c4003600b420140c50003903411f98805a29100c540c800030905410003040d02010700000d02d07400340149580c1500601c80c29806d980070b048096502d00d800c1d0440780840d035543d040405880b2603113003c0d0900b00705c2c480e042c422103d070600741140d903629a414142c882008020032405030560040821280c02c0107500460f04071100302c0000d020203010001003500f40e00039643d44810f40c110224225011400c51b10108003895a1400000b6006c101034844508075400c02022242400d25140340d4500c80c28204501044c101d054900144001c0740c07400700800724038010300b0070051141c07500c1e0130740c00f0300154900031910341e000c24450f4000f9285500d00600a90001d00c5000303a035038a0f2501808990102c5020313004440d40c096581002c03 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 621936339 1250 621935089 621935099
    0xb04150503150703060810060f0902070b010b070c0e18070509010b2205040504120e04020708070f0c2103030e03032e03150f0c0e06030a020a030b0d12090618 69
    0x102d070300034904010543c480900003145181800911540c02407a80049521030030080e000c44001c2c815441007041074410440440801c405000060545034540b007425611810f9003420011404560031401c0c100c1d4201c0207000c03e000420b001c00b4460050b201c00d0312a2603580b0800c112010809111348045400304000c0021103442c07024032704e5184045c5440d450042a210b030701180c21243e0480d011a8240e40c000750011000e074004880107841e020485007540303860000d5540020a0003030302c4009014090041c0c0310800c12004002c0c2d43c001d014400c3e880c120f5071410031024415000051350580120b460311600c0d043c00f00300401141c0c0310b80d0380c07a808000550303192100c500162a0788410301c0144d02035840c021000402c0207480603006984402d0204807680e00d011700d44100c07141c08211100780b0981f181040710030380729042600ea002180c400b00603101c400c8090203802505042500c1030380308500180d000c003045031a00341c2031904801507403001310154640300d0035954545003829024000702e01c2c01042003 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 621937589 1250 621936339 621936373
    0x90302030906090d050f071e0f0501030e010b04091511070b0414340e060d0213090f0c0f050d0b04110a0806070f0809010903050415031b02010b04150503 67
    0xb6403a42c040c01140020300039442c1c182c10506400a81400781e0414007013040b424004020301002201d19841c0340301c090786841049c0c18098160302c41c40c0c0c141600c81d2003008503041d0079800001c09400c0500280961152480c1401508588484120300540f0b1704d00c2504e41040034006450303800c0d900000c405540d48943d201e09650076a440b1000c2c04521030054205942d007883e071044840c0c0511000c0e0a4945010115011445d04140d0026406c40010741c0810080766180b40e5205000da030192100c0822008003442030000c1c0444c500003070543e00307070a000c040c100141140c0d40c6040b107008541c030400c016100c00c01c110f0541c1a0207409000c1903401b03004070300441d06003a58415802c00c02032607011140da480015908203841200c4060105c0e402103956081181c11040c040e42c42603001008102c2c1e20003990700548103014a0040c85d15401d40454034459041c000c0e444003403803001c41c2017090001020a00002c0c0a0810546401d005030305020350001c0c1d4501030003601094520003406841d102901200b100 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 621938839 1250 621937589 621937597
    0x30f0d050a09050d0210050a0c0c030305151207050f0f1f1b0b040b010e060d03031e060b0a020d0e0f091510021b0603010e0f1008070e19090302030906 66
    0x54074664a034071040014008129086803414203030050304c1969046a00a411154000d02c0055900d00705032110460035400303802003030700c42d13418200020140c461044503030303404000d03440309500410080025441d00c0700c0003ca1800300d45046038004030001c030703010a1022003030b4000d04039504156030306041c858072000d03000902c2807840303989000c0c40080c003c440221710303101c0089000d44640f80c06400f4441070141e0400d5090140c48081c0e4052428245039000c180f40c0c1103940c602034101560b46842d0000710f5400d030a4441c8d4000418800c1c000c107a201c2801c1c505980c0040705850251207943d80c080c6603c0c1c003800b00a00c0406008258800c2c1c1070b0140c00303000f882c10000301413147c1e00b02e840c0440c56031a0780ea0403a0580e40d0426900505401050b03070360002986958510700ca10580050004000c40f4420710200c1e03902c907a8024909400f903c071850386221301c0f03e82c0d40140b0000e0003084400315030100070300724640c401d60007100b01030b600402d4030402408a800307000d40540142c2040010000d00e040c104002c0c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 621940089 1250 621938839 621938851
    0xe1f060f0f170c090a0518010e03030a0906061706012402151512060603010606020609100c0c0c29070507060f2604030201050f0709030201120905011517030f0d05 71
    0x41c80b5641402c000181494004442c220005030f0b9a40c18041d02c1f03403001202d034034000131400082003a080b10b50500d56881c04010046c104040c2c94032181800c209007504600001d0419000080303640f40c4400000e0748030b036400d009144c42e40034003403055401c07002540a04041e081305030300030380b540500c91103c10762024401044079495a040062000031030711003d81801541030b0030b6000c0c0c9501c0c10810300b01425200d0700d40c0a081154482c000748006408045000301a10b01e40c0035000a004a03401400c0d2203400c00310a0141070481c0c8514002107900e0f0303000200199051491200a00413040c0c1b030322011b14007544901a10035031140400303202907801480349008507400350400f00034101180c0401641080b10092640c03e40c074109080c03108042e024066540c11102140b6000780615100b88014003c40d039900c0040c0c100010401e228102a0b800e500091885811000034003420b0b800c400107a52a00c6070713100d00502203080810030300052102005a40300040d00740040352408003209914000340001401d0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 621941339 1250 621940089 621940093
    0x7060e0607140d120606141611180405010c1b0605151507050105060f031c0311220609140d11060a080a0506060a0c02010c0302010e1f060f0f17 63
    0x2000aa842e080020008040c9956071358050310f180681c52409841c40c40e8000000d00c80300620b0401d0000b0044250b4040f060180724600d2146141e0070407101c01102458543c0d00100c007140381c0b08480c00300240311403103070f40500000c0c81101c503800401c40f05c00740700c030790851902c5c40d0084101001a0f00c42e00315030341141d0041c98141c00c0b90001c0c00000c1c2d500c0c4002c081da034000413000400c001088400c0c0203960303114400f140c0c218940700052001ca0340340c03207013240c5a9200441504001186034020760221101900ea86400c5484001400d41c444641ca10754010b083d14140900000541c5071003100800161841c50360000d2000c00d00320f042c050a50090002280c404554401d404002c0c1c03100d00242030700003101d6545404038100307200b101040b2034014121a0085c042041150342240e0420310035070701d10b50b0a01e41400e0f03142c480e040481c010044509184d40c14000c1d003000c1d0743c2c050414505034070b809074034400400c02256202c11610b0759010a1060040006000c070b82040402040981000100c25402c1 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 621942446 1107 621941339 621941363
    0xf051e01140a0f080c2b060f030c142b03110f010b1c03021504020d020a0e0a0e0102130b03091216121b1716200307060e0607 55
    0x100624020b01b50700c044002901c00d80da12180c01046540d1080d0061502c034500681001954412907681025101c0b02801a14296119040c00400030803032070030341852039a000f940c104c0c80007800e90a0000c82d002d109242e08040c01040244079100c1d00014800700c00c0c00401842001a004008401481318001000079400090710119070030424106480e81d500d0f4400070754442002c01c0025001001d10200040b161500d418940c080d804c90b04c01401290b03103c01c0da2600700c3c0034070b408640c1e0100c5416030030000c0f140843c0007141c0146019050b00d03003400c45042004104d9100d4240e000a00e0441c00181c800d0181144403848200030500c0c0014071985211141070484130081005000c001511400d21440d02c640b20464802071b500d40c22850f465070307807420007a07004034011014004004000310550010b240c0824000c3c00e071001e585850146450fa00248846900184012281c84891070 = true := by decide +kernel

theorem cover : BRFrame.Cov 621762589 621942446 := by
  have h0 := BRFrame.cov_init 621762589
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621762589 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 621762589 ≤ n) (h2 : n < 621942446) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
