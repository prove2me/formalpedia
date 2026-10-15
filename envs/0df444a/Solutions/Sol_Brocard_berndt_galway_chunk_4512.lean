-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4512
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:51:35.596425+00:00
-- url     : https://prove2.me/submissions/65b54aab-c911-4551-a787-9e0fac275a57

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 811330935 ≤ n < 811510791 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 811332185 1250 811330935 811330969
    0x11060103020a170c09090c0a2c13021f230a0807110f210712081e010902030a06050d05100f09060e061009020a081305010204180203061c02 61
    0x80300c010881c41c031080c0113028028a0040c620540c038203014044070345030384075034a800380708601c01580001c08800340010115020190300c03407524440080b003c6840200b0340100b806002801c45e0682c0b50044e9110762440360606030600030703000342c9903201c40e01401741c0c4107204074011140d41c0c1d1142c0e50b002d0850380049800410f500d00d000302990312041001c0e40d64050943c04864140201a9482c2d883e20b00000c502d1100c400300c03224a21a982c440c0444520781c4541c5501902c0801a00c80182c0700500599a13a60041000d00102d441d41125034000c03070410100ba0044855540c001060040f10140d500514001c0e01c0102c0b860410f0306541c4d43c03800da90340c5020a080b015240c03a0740b070510800c88103a101410250f0084014008411046900c9031103140c11140d0001c245440e01c40803503c0655842602e0b4601d800c4d8a42010944621b1810203d48281c010100c400f90f400b04008540102500c103090a108241440941c50742000400c01082140c1d10700c0e14000d108042294002503030300c000b0040300c00144 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 811333435 1250 811332185 811332209
    0x81207060c0c02060d0b180405101515200c010504060e06190807110d0905060f0403140f0705011404050108131707020405061008010b0f0910030c11060103020a 70
    0x68010a41e4551594076000c0d40c4a44d000c984502026855003005140180440b0311458040d1044900f9044c007405482c0600158007200007803112403960740c00410b0402c3c24000c00840655503032031101c00c448445080c0c0780052140550505102074000700002d100410b840641001d45c2010002811030055114840400c41501d403161017580320402104c150103c540d1840c24001c13848000503041f980c2c245c0b400346c0001e110f843d181900440100742c1c0440890310f83d0720311250500d480100242904107144400044008210010000c0d040b040b50141d40c4220502410001444e004618200051948402d050002d15503030028010406c40032502a50024200014140ca82101f002c0007400100402441a10a1406034884034003000107804128400c4500340448d503194014400901c40c06008080843c034120014040f40000790054034081501042c42806c00b01044005440c003001c4032203050103c3e640300b5025085541c03111100c0702121303504000f402154910307404503030030b18207034030232203e100c11 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 811334685 1250 811333435 811333451
    0x7020303040b130812090c0d0c0504111207030b03070f080304060c11100e0f060f03060d052e050106050a09231e09060d21142208120706 60
    0x75198101d98842034002011076110201702e0403c084401c1d0039215845eaa1003180c1c00401d40746050822014815030060a4001d9145401c0502c0301a0441c1d0030455841a410b000714148030b80c40310368080c4180b4080d07802249103c1c543c0281410300c00300c0e030494190740c4104081482003000010482e4112203c0c0d1810019440d4103040480c41e40c4d400011a41c2c0c00b65044070343c0e0345007580c0b00c01c4046080e4011a01d40000c12046020450030b0f2141d03001402142c039040c00080c50364608004c0c0d4040044c055400d550003920f010a040625030300035800c1c1c044506180c503541143c1e404030311070030f4013410141c10001d262010b54400030340810864400e40045820503a041e005484400e4000d4000d4580a0406812220f64200b022902010ba0421900509107400040d40c24503028160a405940140c401c0400d90b00820318411800e804000010920040b20520b004800004000700400c800d00b540340040c0f48039601480a5041080d40204803590020310291020002c00f400c03142042d502031b00010740c1e10 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 811335935 1250 811334685 811334701
    0xa121101081b03070207150c0b041209080d11010c0e091504020f0a02010608010b0301050717092a090a05010602031614120d0b0301290102121b060c0307020303040b 72
    0x44594200e88102c0d40c8044107020308a90005410301c269800070703003100c050006018044070400d81081000e00120444c00c08680807901592410011240503d07203c1c2450303807510074881c900003499064000081d100000014654000e20917181411400d103440440302c07002100080003000041d0840c035011785d89502d1000f181e50b80e941250203003c44203108540314880c2c44d20180c000c1002e803280408550070511038403803518040c464544994403980301c0741041c0070441d607503c0c200741000307045205903c0b648031800c500c455154440e5080c80c040014100d01c60414209025a00d003000e041e42500320305050040c04119008400d40e10041c1031110079140c4c0d119142419800c82c0c04003e0b40130020f006421110000e20040001000040201c0c4418003a21803403500b4507080f100300c1440d111550701c20b184070314030742d01d1110085008050144102d035074031803a1810320815079101c9001810320343c0e1240141c068131030051114940c800304101000d070440c54100400783d00c0340b200800c014210300d01ca10011f404d41c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 811337185 1250 811335935 811335961
    0x2060105090f151206130302060a05040b010b131802040302180709121b0e0106180b030c072603181515010c0c03030507230d030e010609020f04050a12110108 69
    0x101c046001100d58500340b0000e582540241c06c94141c00500a010015819901502031f503405503078044440f00c4035038070f01000c50700650440c04080003a0251003400240c19030f1072414001507a10340038001640c0b18038510400100c1a0950450501081003d04112400d40c004648000702c905c0c6a0000664207ca40340c2065950002d0441e8454803983c520040b8070f0f68407240c1d0080c1a11704035100d0200120409551303044c8006c461180841841c4104009015184942c020307280044c4280108015183c1c06034071080d10f020101d01000f0344100101c204829140461520300d008070100020303024000d03004200c07007000c040c0100710121400100040d0a081c2c0d20600714401d0940e08078080390742803500c03450b00800c0d0b0760112506413140c91018045854120f03000004844054505d0000d000c038040300704069000d04141200303842c2039540c604000841003954001032105800300c0c0615541c0760306100c10440381003102c2e041441c02c1000c1c210500c0000d51030b144c13114284802424100c9680d07558100200346 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 811338435 1250 811337185 811337209
    0x6260415020c060901091101051918090e100b0402070b01091503080f0d0507081312030b0a0303030e010513031b0c05101205061002150c0408010c0f02060105090f15 72
    0x840c4503c0c410042440c606500c4002524810005020092403020044405d40524000c44041c0b01644200d04082d50080b03007c041d60a80701c0346030755040780d40c9052403803c80c1c141d910488915000700c90005440320543c454041070b2401250f00b182000d0381382c2c903000e00b45c4105018038607881da9103074a054003641406000c0c000540d840107000345c0e03607080040c1b02e01407504800d1400c0c4c0050b0038940866a13460041030041e206020301c00c0b6000a8050b035840700f092002d44660b010080c0b50362094194456281e0b600280301a5010340c5020031080c2c9841c0340c880c2103903002064041407038410a090744c00203034841100481d9040110204a4002c0e807410000c02c500c585600456000c2d041c1d01075626020340100780c401101182c0d01c400c0106940b21400d10000801c000720100040c1c022504105d00011640c0314a50810304401d1103904298881c40728a08650b42c1780300040100303010f01e180d070560507810020180503000c1500c42072024102582d40d14100f40b005400d5828001008501c05416110941c8500c0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 811339685 1250 811338435 811338457
    0x30c02181923070c0611090607080306040906063206160507050405010306051e0c091014040e100801090c0605031509010e0105030d08041e0f06150626041502 69
    0x14082c1030018002e001c1320013214040b40d0907070070041c803544501501400e603007141c14007425413071500303a403a03407900c81e90f07403008044a601070b0740c90713901c00c0204407203224a4000d09a61f04d0b100c2108110070190381c10400440202401d0300da0124511a601d48400007a600311040758804e200d80b10505203007190030b00203190045a00701d0b01c0d00740008140402600200d02030350f00f42c000d05017407402c0212060300080d0708079880e140c914810080200d06007880710241c641d00c3c00034900f40d00c01c01c1c43d00802ea0069845030342710307501030f20240c401e100303040c55002178017402048000000c20150055a40c0c180f1681240d20502c802d01c20301100041d02c918121035581d48601004245680030740c0c548004540200b0f007170182c0342c0a0f00c215454651140e000d1710045005a40040c1036107000340e03000346007541c0b41d850001c1c215100680b41041c03a00252017070003074030004c41c14014001c01450030802c006001c2540080e001c4000c111022985203d0400e001c43c0c1c6030000c2c1c10090030040d404581c0c40f014081c1c4140d0034204 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 811340935 1250 811339685 811339751
    0x12110102031f06020610060516020904080304060501080a11090a0627060f0b07060e1504050c1903020d14010204050a06112104151803030c021819 64
    0x1c4a80501c2c40c000c0702e03085441014541d0107544911080780d907890304407009444030b50803045c1440583c1c0100040d09440325039a00d410000c0506a000c500c8140040d201125401004403c4c4000c000b0b4600619001d090f5960060032005116200c2400b441903008210303000719203801c0462a170b101e460f00a4000f40c55054409044041c2415039480e081062031000040c2c50701c1c005020403103090405849046030300b441941800e0a68a495800007080106000010751240034001a04e01c1108905544620f00074000b400307648403100c040c0812070104840e46441c20301c144005100583d03daa600100f280c0e0419151016060584104c5009205a4124a6100c1000702c0b000414a0f4000a049491222b00081c0c9807440240d1520091402c00025045000310060001380f1800a00d00300006011255140c014860700130045840416005a001070340012882400d45c429410710ba00c03a015074400060b0740032498034041003c510610002001180780300d80341c140d8441c0b501c080003040030154410010300 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 811342185 1250 811340935 811340941
    0x30a020405090607090603060f05060c0f0118110103060308460905040b1c1502031806090f190305040e07021509010b0906010c061e02030a0b06161211010203 69
    0x1caa43c1c807011500080040c0900c1c4001c1100c5100340900b104407642c428800a0313050900d010421541c00510320121a40b0842c00c010084001c2405002a03030054200002280106410001031140030011004e0506060100070000140804201d6003240c1550a10002c407074050014454504c02e03841e0a042203240e81d100210029180c2c1018800300030554403a4101e4683d24420f0000b650346985186910400c1d1b4814800c02122048541d44039502c640b51080141c00000011022138206450b0b40807100b07201040742489100401005030496101301c01003070010b0f0380c901001c0c0c1daa018644514030000d0400200c1c420140107400380c170041c000b02e41d03000041d4684110b000396103002d08024428a80c5040d00400c20b080d0062240c200b100e6005802c016250742c03114019200082d1602d01103c030240e441888402c0301524042440d12071031100005a940d04003040c610f415588141c00341c40c172a803c2000b070013210301c545002c84107030b8943c0200c5849203a81da1180c1601c1d00030b415020303038049500003c10 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 811343435 1250 811342185 811342201
    0x81218070e010e191a030d0318060203070527152809050909011b110a1e06020c0d02100209030a1203091a01150503282004050a091404030509030a020405 67
    0x17244061309800e40c1180c590668400b401c50070f503129501801d114829520044010840301d400955100c41c01e42420b03071425150408180082c00120b24960101d41c00c0f40b04851507181070712002864910b040400c9040800301d440c03084400d901e1210040c1101c403005950b4403480d000390100c40061100420b001c0350f03480c2c11603459000c0e01044c0d032444442c0c9680040101c041c3d0081d54511409181c11004082104d80ea64030b020307007104443c042040c942901c03d00500022040c0c00240716109040c0068055040e41003006442e08610490000c1462300601811141e5107000031482c0c0a160001083c030102d0312411000d600400000d00083d0441c0c0d441c25100c1d0300410030900c05812900000041703880b50032140002c0710240019114030001e0b0780d01140d6400b010416041000c1600403100c2c0000301c1c4808175018000c2c50512800881c030381d07040407a080202e403500b505800e000709070408041c8108050300c2a07070138215400a10040501c000440c0c400900d440c20413035030f22180d070f0160041006007402c0c41 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 811344685 1250 811343435 811343471
    0x14190c0e0a1e0603091211070f0b0a2a030e0f281e050409050c0406060f1b0809280b0d0f0902011b050307081218070e010e19 55
    0x300507840107182e00029110b200344107214950b5003001c04c00d10400070301e4108a072542100100c800342c40c402e8030f0011400d90041e0b202e010042040702040c0d5542c0f008100090011460700340b41100d5068100c076003018a6440c40003040301d4540c189022201840000001000400195950380c0c0220011664070520302c0c3c050701e8651143e40100c03180d4119641ea45061141c00c0509412198860009c6010442400c181e00100c82440c800c009442c98240710700e000c6002c8581b158011400110740e10a0045010382081c0d0000383e4030740c480c40c0075041001d180c850001c00d01c182c5150602075242e80c0300c03000001a0880d910382420010052282c0d1103565681d01401e00d4210000e420002c5107010500250a079a900c204007009a060b101d00c401241410742d07800014010b10310076101800708020410009140b00300802c652a405050380c041d5003014198540e070b00b850390303100e0309032a440410180095414404c5450441e5081e1500096550720003d12865529906021036006803c20f82c0d40d8004080040d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 811345935 1250 811344685 811344719
    0x8160c0b1305130c050906030c1e0301150503060a1e08100501090f09020307140312070606060e03070e010504020d0b030a380c07020402090d0f0614190c0e0a 69
    0x225030190b2022a0703e19481110b07a60342c001d001280c2c0400000b5240c0c10400e0141d5446228880d1441c244480505c10001c3e000204a400100f46000801844400514000088690404d1034101d0542ca020404500c54603a00d009241c4103a03c6017540441160130211107c011b400900c0555020603001880340740a000b0a0148503020f90400c0c442d501014130502c00c0003901034005006103040c629208000d0b610829440c80d007034050288014500103503d2010040801511407134000841d6441c0010003021440a01c03119882504030100030808000d0564005042d036108440060342c500400f510f500061030311200064260180325035410901c150360b80a50380304940945811a04515407002d140944c20341035640c0a50408100803070010340508002d080d600e880078100514041d0f1030300006044103100785044030340406425110080240502603010207404c10402c2943c00d0400c02d40d5030381d20703c03e600301c00c244480ea02d00010522602c6000324000c55003001d0b102946050f114401d8102c07603446c2c1 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 811347185 1250 811345935 811345939
    0x60c100e1e370807111c022404030506090c03010504081b030d0c08061908150c040e01030c090c08150f0109030804090c0e120c06031003061a011b08160c0b1305 70
    0x8400800c030340e0800c840e05064034014100102d803001c46e40e43c00c12030140408480d4004020000320208148c000300401030001d076001364010611850141101071900240c0c10565000342d040800380000540c0d1602940c296104950400b6440a1804509451405250590800603003400e0b00c1c0a0b82942042d5550300031030301615018070301c50308404040c40c0b42e00107200c0d0034480c0d44254800d0a0304401851059000a0096030b082d2903d0b941e5070340c00c0800707042a0816910840342caa400c20500c115031090500300328003420180c4140c6000840064130510203000f172400741c05110310080d542d0303100c1c1c00c440c006941c1c000980d47e1200d80312003c8800130000d41500b100844c181c141c08800503d072180a4107517011450000b06842c1580a0a0112a40018281c810b05011101000c00014020b0040d403c4907000b9092034046255014001080d0000000200d400094590240c80200f03108000300e50143d41105d181101000782440c00e550303214a00c0c0c0c1f008145c0348010908840b81100450b0502c1250700c1 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 811348435 1250 811347185 811347203
    0xc25020f01020a031d030c0a1d10080307020904060e0607020f070b040f1502030c0a0501090c1e0603051512030904060b0f030411060c100e1e370807 65
    0x100e4005983d0707400186006004112919913201041031400440010301c00b016040d500d25810900120300180c50300d422804600c011140c0020540c08040551a80102c203201201740c403074900f0603032980f24860408084e0085910700b00107814422140c11200460400c002111482e2401d148001d41350b103005104071116006228000403070007040c00076034003954001507040b40707401c2c680b0034048100e004403000c0b101580428000910720395000d02c02d44440a000d44000304110301c507071800da544042c25400c00c090714070040e41070b20710511450343d0340f4080d40e1082c2000240c80c0c550400307030b18039004e011002640c031608421001031a05000b1001e80b101d150103860500c40207482e010310b0415800303000000c00440b20300744001000304d2a80c9590079030780b8901030030039464040b408200301d0a0100c50b104c240721403a203a0004d0000d4103070410101e111640c0e00860010040c29220b0350517202c41c000c4940035000c1105081c2c008030710310000d00700e90010b507442d44070b031480c0b001c545082800c80d0040320082d940307204 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 811349685 1250 811348435 811348459
    0xb01020307030e04090f02060f0c28060902060c01020d0f0e0a050a1502120109020304170a12050a0608010c0206090706020106031707050c2107080d05030f0c2502 71
    0x10001007640c914035070644640c0244071030482404010904030354142c40c2503521410f1070001da282e6400911202491004260383e070611400c049140642d814503401c08541c05007214480481ca0312071184503641d0058001c00c1401443c00091418003d103940510340e944002811803c0b00402c0c0e01c995a420164a0148107200307480c0312164480c0c030342e2040600290454101500007071035506070101a26040c48006080a40149641907240030903040725801990010900043c01103075440364681d24210001030f46010445540104401010240704c1103154486020800501781078024002414148000b0445c92181c2d44000303641e140241c40f07070401806244800f0810360320601540c0c0580340c004000740c05006441506420961203054113907040e02900459601594500045c00b640c640070280a85551008407031041c101a44d40e84403645540c003e107410284541c0000543c0e84c801c0c840e603000640c40e5103401809c015803040106244407030341a42d8200085104c0111981074030740c02541c500124134 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 811350935 1250 811349685 811349687
    0x501060627081f0213140f1f050c011b0f110d0905060906070b07020c1525020a080d1206120b04110315010b07030305100b0f03060604031b08010b01 65
    0x100701809589101c1d08944251071481c9041ca04001d0030501010005181185e45024450a101a0380151030920124480e41c142413070700b8a041500007000b104c2d204003500300c09007024a040c0901800380207000d0041380700d004601d001c0d2b12039810301095040045102c5d108440c000c0c018100c1c025030001080401d0380d00d040d00140042d203204074244689421251904060800900c0d820401c030702c0d0352203041004010000b0300c40051940c098281900186401400b4000b0081380141e200e921a00c1c90000b40200261214a07114840603554020060b400c0a000b0f40042003414000d46c00c0310b074035440b42c0c40f44400042d0703008041c039034440704000c400c0214644803ea004804000c903c0e0280600c8006400719002c0303083c2201807402094010300700e9401c10b44111000b201d0301c000b60b015110045021442d01d040c143c05009199004072941840007442e410000ca0070780c50300425080803101c0300c000c80001c02c5500c0f10800c0740c0c051900014000d5055035540a0245400c02d2805001020350078815080255 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 811352185 1250 811350935 811351007
    0x10c0906020d02030f070f050307061a010c02010206040b371104081f0209031b1e0a0306090318120302070828020f0d0507030b0708100b090a0305010606 67
    0x50380b05640070f075180000e10b048800040c6c000703c20039922440f14104150001c1e0f0300704010024544a03a5003c201c100461484801c10400c048a440c1801080c40c04000140c0c0e012580e20b40c0f01c5d9000d80d407040a0b4549440d40c9544814007212041c090081aa0703441d114684502c08030b890000c0d180b0705108440b01c1200b030380c0e206c0c001d6200b04c112607800b04000800c040380c03035618815000400d040c01418021880000b0349840050b448107120105401c2d00c400c0075082c13040140b10300f0030841440355038034200312000c251000704c60322002e0421030740d03036940f2802c040c030802d4550784200252208282d0035417180070b0001c1003040514114050303c551203001605100100344001c903c10072000394150f0b10080002092080a2070404991004078100902a90fa42d8121110360320340c004c0c00109001c5040d8a05607003103a40160460060002c1e40c003c00c100070000e1a85d40e001c0d030395921000380d11000520003084c02401c070380c0c0005280b5400c150001c505a50f1100c002c0200c4442c0001885990b01016007905003 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 811353435 1250 811352185 811352203
    0x303040e190c090e06010e060f090a0506030105060405060a05130e0604050a0b0108150402161a010f080607121d06070f11070e192a0314181509010c090602 68
    0xc0b0709038400800000e52a130b8446030313210b030060500400b021000d50003d0916171001c0d020315204200868018540c3c20102c040c54050031058401d40e155504140000d00180100e00c560386c8103410000712204201d2080c0c00b40d894501c4002c0c00703444903503280c000d086144041262001d000380d1403c0c0c00106d094005001d0036405240c1038440c00d409880301120007000703883e499441600700e0340821aa52040d08544200c8100d540111281c4010000f240400c42c2c5405069118260001e0440030501001d4000305016401005604001259001181c0c40c2c0014111104041e2440104200018851100850920701c51a21541c50f407402c030b800803d0581c3e030114540a2400c659100d980140810f03001041c611340c0103828017020000e50400d44044005503402000a10545a4a06048403d100b0400c0c01001190300506081c80101034904e440760207001c004010300214150000541c02e43c0c00c0c00c7c05192804034000c0b940d003006141c5a10018043c0180c524890000340c454072001035254404900c520f1 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 811354685 1250 811353435 811353437
    0x9020c070608130f021203120c0d0b0105041a18040216030e120606210a210c03120902120a050604050c0609010804170904140a060b040807170a020303040e190c 70
    0x84da0840c180c00740040000b0b5400c9600c8107200400c504c140003415103007454482c003007100143da03942442d521071006803403525001074180281404180302c10070607216094030556030909425200c004088100031090b0b1090320194116100058906800c9102002011402e000b503c400500d42d40ea2001e001c0000c0030f5002006094100700049200351034800712820140022003044c0300c20f0740c540318246040582e005d40c11106003002481101495403640d10312000b1140178140581c2559154902400b1501400194050746540c2e030480811562a44c071000000034094007128440c00d00c51401ca90b881c10305075010303104d40c4102650b900382d40c170f442c40c1100d2f000c1d9010fa40b1000c060300d5680e60b42201e103c030441c219410440600100401d91160300c1031158000500000390481d00308003102c00b0403100c1c6a041807051141c204424400180c001500d00120307010788202c0c90140d03083c880072504040d800d80d0700035418000010000b5003001310380e00c154012082600c01103c241c8209844404851a03180c3c0c01d4 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 811355935 1250 811354685 811354703
    0x10209090612100b04020706230f0105060d0f0915090506090a17131d01060314010b090105130902031017030307080f04210201061703070c050f0a09020c07060813 71
    0x3c1c101a86a4008005140001d0303c05030420b1403075510001558011812003e003203500c4101f103100740c0100001c15800000481c0710700269410040420441e1045170810a1001d4544442181c842d030075031700034020203410905840b1078030f01080102c0050800c0c401c01361024454000461001c610120700c0c4e00758a40c2c014004e0030100c08840e2002250303004026920241050074400280014082c0951000032000d552886003d40c10302c14041c0441b02d4880c141184540034400521909074074400b221002902400d20544070b421448070140110300c16003110300750324008001c2c480c0081d5000340c1e242c01d0318604607a48003e1440560b810750b5a000c01c445000000d484040803910303212001b035081780c00902808201c000c480c902e4074032041c1844074800c5800140c2d51184100542e205004404482c02d103a400994070344039854580c0101a011809141e10591012158041c90f80d51008a00300400b0b10704400d64031003901841e09500c4005a101350808501000002140448110b15200e20964003640074 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 811357185 1250 811355935 811355953
    0x314031309050a0e1204050d14060108060a050a050f1f0b0c0c0a06081021200f0d0201080f150d1203062709020f18091903020318030106030f05010209090612 69
    0x888080242015607043c510349c4164440144281702060207845181c004042c2c5003410764404044520017026003e035245820705010314a20103441e055004031448943c0c2918661110000c45840084d41c040314200e200014450015500420440010311003120464090381c0d030352805a4403403400300d42d1500200b03090f0005204031259001001d00c0f0a55440c1421840b4107140d4807140c15040359074a8008001c2c0007003c4c2c1d0450b2400d86104d0240e1301081d2510107040b0321345d60001c0c1010344040c1814100361151000107016425880c01d00c841400c0040c99212030280d075040c0541e0803000082e05400003401c091010070304681e60202c0f0300f1184c009030100303410103219841d0040282844441282c2c001800000080c443c0c1d903100501c20b000d4021400850641002100c59240c41104010450034421040c01303000803076000302c1131781c02c01c0140890072002e4070b1b0b000e40020700412141c2c0008180040c4580c01000b8400154003a00e000e180a5855807242c1d2a903008009820300910301824140c0d01004d50 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 811358435 1250 811357185 811357189
    0x5010f030e03160809030c030706020a06231810110f0705010f0e0d02010f0b010e12030c15010806180c010f090f06030e0d08100314031309050a0e120405 67
    0xc0418000d8206055a052141d050fa00380343c004000300b0182c0301544080b800e100c082ca81802a0b810b00d450840007000304500d0f200f001b0b9201e11800a000e00940c2d0395111094144801d54001541102421040d400f1171500103010500b01c2d10008038040184101d01d00c0540c0070700c9600c5025040c0e28000d443c0da0410040640904441e802401d0480e21035480c0c2150100c0440a03005541d440c1d6003601c05004210060003000782110401c9903100e65250902020541da07076042200d040380003100b501e034114102c0c41c200d111443c5108081c1c0910041c0726620007544d02c40d0340d0345000c070b0507603010905680c0e081c1c07101a443c0090040030750008032585c100100a80c03040d03000b0030440751441d1050902d003884030790b40e030354000404040e9880500400c0e03d50040c2134074548180481054400369083c19030b250b0600802c142c0c070450181c0002480109048180d0022540c20030617584421120103082482580b203507089806024181d42c8452840c0c2000d4401046040105011030704507801d02800e42040d01d0042 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 811359685 1250 811358435 811358441
    0x512011a1917100501030f02070c0b0c1e010207030e0306070f08101701060302032b0c03050f0d06080f010204080c060a11030d0605011803030c02040903020c040e150c0405010f03 78
    0x8654020302c40c1d0846110090141001e40a10400400c4481003115203048000f4041c2c8004a000441e898810000d980016045214030002e6030003075080c503a100c0302e640d64075070b24090801c2c3c0d9446807190710341d200e092007203015002060702070f10a40d15251030048605c14181e40300f1003a00d114000c9203081203076241e038503c14880564000400546649070035643d8200340d007410f041143d040001c1c1d45480040c03041d4241040250a414900d00254003a1f442c92009400400e816060080400040e0307410201414070840940e5090b02c65101c0c0325580e1465001410000e04280c40390411901519004c005881010f100b610111116040582030403441ea9041000c1d551100d1803c10901404001980100c0020400342c2070ba0340c0e12100002d0381c43d0425002502c461a4150ba411114815020500000c0e51140020f01065410390b4081040032003031a069040007016000103422510740034103100403010020322310912124480c2d4018140d12000d010f181144918017031280071039065100c80c00030b03900c0fa038 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 811360935 1250 811359685 811359727
    0x50f0a03200a02010e010608160e0415050a050a0b061309152d090b010e01051e1317010c0c02010c06060f090b0f010206101a0702040c0512011a 63
    0x180071a40501075280c410304a80c1052400d400140e5456401c402a8a002d02c200700c044c0902100500a04400400e130410005090148503160400728010404005001d00722110700502c0070810b0003203182c2805024000c2c8005c235000040700b4200320030b100035070605000b11286518800c00c002015400d040d41034003c3c081d4004400c64095101400151410040c2c801d0010701ca0481040301392809001ea01c8084940641c00110841b440e04c441d882451fa0050000100e1540038200a5128041c1c0c0c00312070503903108014203240d0a580041d98007200c011200810080c5c840400005a19180501150b4202e46205000c0400b0844103120b09000d036018014000d175031031044602080e4503855089003542103c0e00e500c2003e070582c8801c006203c3c1d19001c0405201244280700620b03a0b031420a0001c0e180da41503101c2d01501c009640035080c02024000c0807105031580190052000416601004065038020040307514841d41d0b010010400d04510346200181825580c03616003000345440000007003400032 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 811362185 1250 811360935 811360961
    0xf040b01020a1703040c0f12030e0301090f0803070f0503042319030905120d0905090a02130f0608100812090a08010504050c0a0920090a051302030103050706050f0a03 73
    0x41d1a000000303070042500c901e1801d41c82101d95100c0c281886c1c403440001650f00698101000d0181c24030802c1c25061b04a0f44658140c54800200a400c0740401d004150b059006040900d0387d504441c24001000c00542c01607040f41c3d980b08014007540801ca80310b0005490092419000d01c0703c100c07c00398005191100c11f0713420810344d0107840903480300390780c2c04080c0c4604801041034400c0c2000b89141200c40940580983d5014019450300c0c48001400c01800b8000c080c441e40d038002c0031a042009a0b8103a44c5941d13a083c1403440619101c40a128000e2528071030440002e240c00002129140c8076070b4003000711805070008011602c0c0103400206244c0005c0c0031f83c0d0b08401250000240020300340200c90096000d8800752000e07013038080c2842010501c542001c002d080c20040c2c804040039280c3c1c0e41c000084403800701251207041010003e0003210165124a51148036030849510400840e070055040b6071150046480003903a4500a580500079000300003001002401104006406901302c00104464 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 811363435 1250 811362185 811362193
    0x40306020f041710050a141807090c090905010518130305090a092a020a140f0607022404020f0d140106060c03031401080a020d0602040b161109060f040b0102 69
    0xa50801150a1440d01c5444440e41e0000f0b002c1005000c6602c10244c101046aa0030b1220800707031104641c030450080c0c4800c1501452381201a95041c0900a00c0c010340b6607000e0500c00c080030004010706082c040c1c0100020507141200000da50f191215202c401e00344603195215242d40c44680c82e001e8400c105405070103101080000001a945011a01008e44a0540d00180003201c00044030103204910454041e14201d42d8022104540c0004a861200e58041440004004050003030381c14080d5511150b03440b8460700b02030004c01900400c0d0102c2022070320704101145200003441c880512801c2c0d030080e400c1402d030b1820011034104000e41078102170003090090071400000c1070141c21a0b120350300c00c0b0000b8221108110070142e16004d109040585070001071940c1d4140030816031104155403000b1f10030840b160030041009031540680c1c000300080c07480d40d601c030072140144036900c605900342260001c2202c1a800b240349041c9048600402c00582558440a10030080c48018226941900e041d03200d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 811364685 1250 811363435 811363439
    0x140c0a08090d4127031903020102191e140306090645010b12190501060e0a0b030907180b09100e240603041a040f03080603070308040306020f04 63
    0x4100c15210030035500011031940d02c1034130f501c46403001c40c428100c030003104400c2d0111500690340024a0302060041020b40111602d00c0c1c507007a402840754101213600540c1510f078200155400800380c05a880c07200f15100e9400f04001421902e64490425001030b4200c10310114002e804d107400d0056108002401e2005041c44c94080c1194990803075044c1c6036910400c40d042d0312441e610200a00701c1c000e036400f01c400954102040d15200b030003051081e00d00075a65030005112841d40024040711044007003401c0201d96101c0300d004004c1d02032801003a0045007045c40004034007103035800b00c0303110750469405031401d24285490b0401e1103001406219410b9224040301503941d41e50301e0300134002c054415084031060b1510502c003010150080080f6500100c2c55040001028025110030900310308031011603072a503591070070741040c00302c1c2c2400ba00044000402c100810034000070a038003850190302c580303105549803410981d651200307000c0103100e400184401c00001c0c02c240c0181154449900c96075040607 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 811365935 1250 811364685 811364777
    0x7120902011103191b0507030b0408070c090b01021c0c0b0702030418020403060c0f02030304112d03060a0c050f0d021b0703110607111003140c0a08090d 67
    0x20b0002800c008249101307081035000e8540040403890180c841d198400101541c64440c01e80f100300920000c1e20603144040010204501c2d0000c0307400705036008040f1803016440305103080003010301482d0300b40540703e4402e51039140110b0700340400c6034002a50300d8101550782540c4100c20640040d040b030301036202c00d100100706880c001715815001407940d03d0060b151895410907805440501034110700b40140d4807520340da895400700c1100c4d80316421050b040108540c0d032000c03607130a0417000c1c100e60003214658100341422000f6001c8a142c2c550403000c0f5a150341320350a8903011900b8261541740411402c100000341b4001d00d00103040038211401d4014106000da010203100301440080c03550302c3c1d412401b018004c002c450380034141c4036101138454604100d20b40d503c0343c8400c0c02d42e942d1180f0480031040c602c00c0c10340c443d07045803416031080b402071003d03030414500d210000e402c400b00d00310210f004800094002070f400542c0e800c85114a982d00c0f64549031244280c9110a0142d10640c2d004c40402c42e20b000c91 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 811367185 1250 811365935 811365937
    0x1b06030402040f09140c011407030917070e0a0f050609190b040615170a050f012303010c120b0f0d0308061203040f03060b0102010b130b0d0f06050a060e07120902011103 74
    0x174818a40162051030484000182280c00c0251030a0081e10f00380046d07030200360300800110950312611781c210004181110183d05d0101e90358000034000741001c04105d08000c543d00207000c031840019040c05103407604000c025540c50210b4101c40700ca45002c843c100044061307003118541c074070060000a03a607a00c40011303201c0c000742401d00001048011010145161852840756031025994004112504001d5918949940c0603c10854001d1422403400c1d500d01c40403809880c0820010001c0010743c10720356014000000c000101a0000e1610440c10080d041410042c02d2201004085800d40c4070190307010b0703c036010040d04154004584079000002c8540420003403002c0d028036000350b0322151075407030520156000c4250190443e4140b40504071980c60b00325086144c61440000440d00901c01800f00d40415580140580075051442010f014003045a0060340030f503218405c188001c1d170307e901c0340026481003600c2400024032200c2048080c03200c5680420b425600c145042d1a007004554201491 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 811368435 1250 811367185 811367213
    0x2090a081516020723180a1a0f0306060d0503160303020d05010f060e0d05010e03180a090902010816050f1206210709020c2b021b06030402040f09 64
    0x785008051020703040840c51560780860182c4002c11509042040441c100100b01c1001520608070803020392640d900c800400d20003100010700f0002034070340502c00c40058200c0b5502040e00d5640451710f40c1c15800c003441440101700001c0c000f0456a1610018809200c00e03280d4140c0c0c0300c0c0010300c01c041d40300c400341c0d0000c4a07103406550050386038000f9031407150459406a11500003604210020013a1540109108841807003c8846550031006410000e000d0a01d209400389940000a040604a6064240004000c2090b00c2c11400140c9074503801d412286460b0029022840c2c0f00300040e0070700329907410203a000540749429070820307828803d40040c0390032224041d12480c1e405010004e07542444202e1a5482c00e500301304c2d1030714015810410b80c40340f0007809a04107943e000550702c02d8001041148683e44a5610003c15007645200c80303081c40c03030180d0240d40c00103010302071000702454010020f003044010010880e500d10345481c1e0030003004028010840650548408040012400f5584031101d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 811369685 1250 811368435 811368463
    0x20a05040e010e070c120207150c140705092d0106080a1407050306040911031e1c020712030e09101a070f020f060403080c0304050a090b030c010302090a08 68
    0x2448608049010401500c143c0240000d500d56008010400e0385c0070389401001604014400350000518404a080c134801c0c0d0000359844c14012050325010783d01001d4001c0480c042c8890600540d9030f0500c80341c0301c1d0403074400e103644a541600400c0b103000382c050686035011030104405050a221502130301c15440300364404800714908038200300080c4164082c000c517810340001c0590350f601e00342d00c0180241c00045d05442c05903568056540411240300c0741709074411070003803c5030b1035401c12a894a4000c840c428043d049070081c50300e00c07071401c1d101030f480885042054003c1c0003501e00740510920240d48ac450260204002d04c2c082d4084c549812252a004011301c800450b03040f402c0c0b1402d911050001d169201303900e4010460700380801d04920440403410b504550000c150210240041d030035000d81e4001034035040c1e0014440c2640100040104100c0d10269801d503e92561540108203c03802544141c2c0c241c0c010013a5200c19600c0396004041004000b01201d41141c0c40d06540303841c0440c0103145403 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 811370935 1250 811369685 811369687
    0xd050c0a120c021002060405100f09020904230f030702060d060b03190e03040e011203170c04031a0603061f0902070f05010f020906040b160803150f01050c120706020d020a05 76
    0x203030940c20704907602c004c684510b000803c03403030500383e44191b65014224150b0180326502c485144682d00142c0100740300035001001e08505007428100002e4500340b10012000008000890301030048010491051400d120030146040a034141c0900103160310100d20b40180f00d595480100c0d8144034440510701440d04c0010303402c5a08503100c01c41c005c841940541c500554000d0208021000f414820b1605558103072581c041c640600c0d00c1d090360b5054000c0700c440040044442045015001d042c060704c00c69001d0040e1410303004032182010111070b01524102e806800c104c00040e51100701403071501d115035802c46100c00d101d5580740039104a81142c40200c0764569103060039400e00a09004c1c00100800e0044214a03040c481c0d40019050320071481584200070000c10380105620700094251070194100c68429600d14107100c0c4107003008003000f040c902c218110000c0d19035551048080da0780323070b561140082c2070030340158003444800e802070301080b00c98a80800480c1340c0c201841c0050025503840d07403115 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 811372185 1250 811370935 811370957
    0x7020d02070b1c1805030f0c150112030309141212060909030418090213020318010b06090d1b08010b01121422060c0503070e01030207050d050c0a12 65
    0x20306081c03266000318030320341e4148140c00410301c2e400800d81000b007079508002039000500740c2003140240c44a001074403601010420380d0b01d94100d03400034000390b00842c1c25204641d80e8040001040c0600b0b0240041109070340e504840000e009600840c41c450090303880070230790404012040c1c5030a4124079400c07038030075010480c2482400d030407a203942c00c4a0f08941188141c50001d07c416524080d9200d86a1140046c103051022645564403107002660050301910783c2000c114a150043d60068408103c00345069070140348005040c03007411780501000345164909140481001161180054156003594070703a0000145034400c1c0300d04000600006001048210100c0009085083d43e081043c40d07190401d106403d00e012010080341c0d0080603030301c038480321603035940c20728801c01d8422200612061a082d654100c050f04940030f9445466569114494035030060011010380c003c011005140e07510100c1d2254250740118043e01004100c01e044540019083c3c60342c09440303104100341c00101d02e000f104 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 811373435 1250 811372185 811372187
    0xc011404060e101107030f050c011104050906030105060a0920030f06030105160c03050a0e0d060603021504120204020d150f0e0c0f180303091005120906010609140d060507020d 77
    0x242180d840d01ca40d41000700d422552131101c202e2240c80300040400c51200100003009001c3c1087c1e803040c3c600f81000708400100c1c008404a29801405140d06c00c20340e5000190051a050041d188604005041c41ea4464544220040034215031450f00b001c03800c000024440502c506405503100c4d104416070b40c03151f41011000d0500b12070f030151020300d100d08081d03030613440341d600400d01c001d1466140c5401e655500c0c0040701100c006112400040d071119080c9405010311105400c0141528002c8a5100c191094541c0f004c0c030611852003000d0003410096034407400352a051b8040c0034517058090010034034008940240c1541c0c60076420003c40c4550000d03080c07006d83d1103c105940d000d0b80c030000e0f8600c1d0a44201c2e80350707424011300c814540643d0486e00c00003410748045c0103849000c98060001007510904400281140e0401000d02c04144007a000190f0408400102203040700e0a80d120868071a042075144500c0259019450790013083e4241d116000031079610880744150b13580c0d405040a0200120 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 811374685 1250 811373435 811373443
    0xf01030e16091a1c1b080f0d0f020a02011202090603191a0108040f03350a020a05120709150914092203030e01061511070602120c011404060e 62
    0x1030b100d645000d40f400c0100d5251078510222082100d40003002c0646440c03460b049030b440c140c0f8203500c00e002c0800c2500003181800043c551081050318410385003c0040c1314001c481d90742c00f03010707101d0043e0f0010320240055405401c001600144180000d86084050804614994005c0d101e40d107110381c220080c01c4508500d8841c141030480c2c1050b101803811004e6000911f2080c010300040c1c00400c4010076481010b024540d0100b0388a00c01c3c1c4101810200081040e03060910442c4040003110410300042e003005803407007202c03080c48d200c0e1540c5040c4624500986154400244603105002003100c01281c901c40d0201d84001c0e8400790707034400d01c1c05410440048448001041c9450149003224184032808080340344010210543e80c05111404201e401d0442c060701052030308100952030078070b000c1480c08100350040d0070b04200b501d45043c0c000b610ba048555900341880382e00300503040f012604c0100c012850041101d0048900041100b109011810070f0841081d01c0440b90700759540c1d43e00024000501c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 811375935 1250 811374685 811374701
    0x1b03110909010b0a090f1805061006170a0c09030c0801023105060d150e06030c0a03030206060108060409080a0e090c0f031f15020303060301060b180f01030e1609 71
    0x81c0080c0800001d460200e82c1c00c01307403401420310044d120950018100950781c0030303092499400000c00320715041402c0460312100103030b55440d6000d050085c046115405060681c480103591041b9184586c2c5000096000300342c002944c1042044000e4004041030440c880c8201400e1010001a03a0300341c1d500ea05400d08030003249c000761240c2c1e181d8101d0560005c807441001161401e450f1144c0c0d5501105049004145010190740c000380c41c4400411300710f030035402081c4551420380c101c8118100d46810000303c420341d0311005006900076000030748035510503402305820080141010038001a180d0345d07041c45400070071340b1500140c80c158040080b468500b59160f00411034408031403500c1089000c0814503c4000d24429200304c4d03101361413181410b450220b200601081d098400c2c0500c030507100940302c0d407040c0d031841d01c01c0d0300b4020045030300ca10716003c441da520f0300d0808141c0082600f02c00c0c8a2407840e91101541456070300c01c90402d00e40400d0095080030100009160b6010342807007907140490b8441 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 811377185 1250 811375935 811375951
    0xc0b07020106142b060221040b06010c0506130c0905040605060406210b0414030412060509070e071b05100b03010e010507051210080318010e0907050f071b031109 71
    0x503541d101301c160280d01c0000c0484400740302040d00010b480c241613020f07108003481e825011103480c03851803003a2404060a4000d40c455109004191510001142c1f500b49002d0080e0507504943e0226071400100d103854502c0904c1804d1044980f030b690041c1604031081220251152502c0d00c041100501e003074459080608001c14240001d070f0000703403070a06020380214008017402400004a400c3c4600c501c04821070840310003c8070fa84030f03207a41200150328a48041122800d0901c1e012410328000450032070150344402205880c641d9070207008417000c0300900303d07203c504400310340440042203041c070211948038448880030130b0b82c0c030440d0141802c4400d84400e409170f0364980070a029000d40c2c010103c3c3d42c1160305503101c2c40240c4a07191200d441000a501c503250710702c400110303030419060352816141c103000c003602d0701e00d03400380d000050080710b24007145e09400085080000b12510448000036000e01c0780252441522025884007400910f40b2540084e580d000e480320042c0707818134002d03048039445160 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 811378435 1250 811377185 811377199
    0x2010902130c110f1c0302160c050a0e01080c060a0c020d0c081203041a09190c050112021c0e070518090129010c0609150e070b0421030c0b0702010614 66
    0xc1e09420303517119603a602c00240520065860441990700c2138040c0c50485890704a001600f42d210301e0b0280d4842d004e40324450184581400008601e450922070764100d42d50040a00740d549070342d0042182c5035004141072070920401e0000400540c07030303000800440a1007922603501107810003180700d00e850700140c0001441101001040f00054088244072890072016102d21450385603029400d081c00c00c1f0806040785c21560038902004d00244440c4a42194000e88074007411500c0700380c0c954140d1041801c43c0c081d41c1041c0104541140702c590000241c8400042921b0550742ca50000030250801d50480800c1906c1140c144082a1750a114045503050b0b5112000e40c440c242c40a2441080b4001c4030b41418007800017594814020542c2000b04c0b103e50004528081d1044035801034001c0603008056025485420000319030b0504400c211800d4503050406502c10a2011039106444104620120b08104800d5542030000e00d41002d4a4000c00042d0000f1843d181407003681e03401509400040c500c6807503 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 811379685 1250 811378435 811378453
    0xa0801020f040e0414241b12060f150702040509010e0a03050d140c0705070e070e09040203010b09040305031501080103120f03060e1006030e030306060906030702010902130c11 77
    0x1072072001c480481d0615502800c0507640c5040c507199200d0904c1c250340d000d020360140d8202d42d0001c0d000d00d191140b803524203140b464030740705010800241002d05038503201e4001c0105480e0242e00052150344000001d0000301e076148200d01281100901800c41d5008050128208045203031a0040549c0b05210360000c0000c40011100036940341c1a0f00070141c18880e0004070b504100070a600301c0284403e40d02a01050b81c00c207111601072591110f0016a0640202407020510071234200d49203025403010740d03c5042c01c0b80e5031410000b24580103001241d06658540d00d0445549410310594455802a01c8050b124130380148030100c102c145c0c414041c108203051005200082260034403a85e0102686048502d002c4000003c0c0c00400c04d07600301040d4044031204211206118243d001c1c1a03a00b40d940c188803422001c491180e07640800d40f080341c0d015200b030103400140d0824901841d0310403001d200105460056401051a51451000b842d50780703511907852001d2250440c00242c2d00581220050610403 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 811380935 1250 811379685 811379707
    0xb03040b0103020918070f05090a1407050c010b0307030b1b0c0d030b030114010b09010f14071202030f0301090204030c05010206060904030806031617070803070c060c0618110a080102 80
    0x2000c1408001c1c8509030380b902240c492076030b18240301c41a50070041291000c0d611900c00c4680728a0f81d2041c1d52082e01600300040390050a8002e508602c4022816800ca5803901b03075041d14243c11030100006150760324420b00c200e503682004928000e41c00b940582c5428280100c5c0c140c5414400e9418241c5841d04000d8000303604c0000411508003002c40c40c0000d4030341c0f440c00000c5d01510241103540e43c02d4040c031001240c04007040e0001c180702c85090320341800707800d12100d0550380c03c40300c41658070608000384111008640d01c4c1101f07056480c1603105482c501081320b0f02000c0103030420307000040031a6022800303004004541d409140900001d0004190b03d15003c0005040040c000388000c1c10040424040703000350301c040088d00c5a070301d4100c40000c030298449251719a200c1c1482c80d1040148124040020381c0400882211011030300024800702c0340e0f00f40321003540c070401c5182d8219520350340c44c100698041d219541d00050148906c41000100d840e01042240c00d0b4015041800c480e403040181122032 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 811382185 1250 811380935 811380953
    0x51303120f110a12091706160e0a0302090c190203131a0d0e12070b4c050a03120801090209130e07050907020a03081e07181a090301060b0304 62
    0x400d81c403948400540b0304030322080f280b226084e1b00170861140e02514000500c00d010900074803d8a6649109130b0881700c1c440200c030403030021441c003600000200030510160508500d41a4042c41c0030380b40303070700d080c00081c4212803101002c0880e400582022600f501020300c0408640e00800341102c01e17141c080900910f902e820302c2144080d5802c1d271361320154843c0900b024400d0400c05443d840501303860f11010f05000307489030320031140c01409151122020103a000d40f00008154035540c01d0140c0c1c0700c514607440400f40c802802000050460503024001541e1303489000100113075118428581e075181d1a4007001d080400184c0000e103d0f0b0b4012304c00607900780c40b0b419103001d00351881000403a510428880b03103401d085841e00441e8110351103070304210f0740c079400007a194000c42c425035928103555030b80b801a1101d01294058400094402c4010403032440c860f945a8074048100b9500413003490b514990310303070241c10040c0132150720140851151810716081c0706900051403400240c0c2c1c95071400755540156 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 811383435 1250 811382185 811382203
    0xa120c11062803060f06030b090f01030506071409040612050607090e060d080d05010b070b09010603031d1f02010606020c090103110909030f13090c0c03020a12051303120f11 76
    0x400080412903100b00c2d4840e411000c014149000c0c400241915200020003400750303041b19500540c41c4002040c524441801001c4c100d03500300000d4105c54403045070485145900c4107595281d102c0034409208103503207030b100d041c000303000075030540e6502070720f500d05141018002030100003407014414080203030404c101c00451388020101c440075a00307030031860101103500a0404107200325103403000120b8820040c0740101900350281494960569800d80740c2400d9030315502004002070b203000d0880d1050440c91400d0b12a0f0760b0024a02c1050420030403142001c4113003448464011303074413418100901501401800284607007a100350002d50304603104c52003a0f40040260303d003d44802e00014505030000e000b682c5040308428100c50350b54242000342c422107540e9029170314030710386403920508540b40030b540d15065050f03154001c1c1008010035210080c8919400c0d60042c1441403c002080c41c41041c2d150050295100d042c0d1855085811000200200024090710041c068a800c030f54016003030015070010 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 811384685 1250 811383435 811383487
    0x80a0f150e0703020c0102030c07050f030403050709050a0605030a030c0606080d270f1205070b12040f060605130212060102030f19051b0604110109050a030201110a120c1106 76
    0x300d02d4031030a208070001e210300c4036061030740e510202c00e103c2508903600007031070501e000c3c400302c071540304080c0c202c95128401c510000300f540d400700400b000080c03015004254405011400051a00d0b03680d40400c0c14004500b104500040c2d00718880b500b00501403051401500005009001400980601030500324075400d031f1000d080300d91380807202d8486132100c8850107010b40841002d400d5503a00c014002424490b5800c45050042c0742c0e0209480e41c051040c1c840b0200c800000c1e00107515651124421214142015907104c1d032a200041038680350040404411811400e006036101d02c00100d1300d80207003001c0d0002e81150800c01140402c08140401d69881e000c284400d00d4500c0c40c402c0e0305948030b1050754600001002c034080ca0505135400030074000d100307a009048270041a60000c004680801450242c250722403070012091009d540300e90350040c642e000b0f010131a110b070039654440085041c81ca81c0b039500011012400d0004120003842829100102920b500b802c0041219610302042803040d0408 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 811385935 1250 811384685 811384709
    0x20a1703061c02030f1c020d1704080a030b03071403160501170a09021906030e060105010f0c030c0602040f03032307021203160605180a0804060e130c080a0f15 70
    0x1c400d540d0300f171299440d178020030811100204c80480741d06c00c0598040c185900903001c1e89200600c641c1c040e40e15000244280e00e4404000e0b03035140e0311040d194001d080e0800c10540c0e40c180b2030070aa1010010071010b0300100d83c80c6402810307100100751810b500002d25001143c0c0c0e14400300b1980c1d80241502d030480340400f018007015030703c24003080014604414007070740c04080078404030010168000c40c1010f81c1c0e0075070f0707050048078100c4184d90340d0303014288202c03130014805003501c00c0c4552180d10503d81c0b075480380c03902104000040c0c8441080ea0416002070700c1c5500030400810803d500824480c542009116021a040000d0b04100245008202001e4020305480c0d81015800c0c0c002d00c00c40791251420071041c00116054101038004001c12960f0111a007200c110203505690300103100310317400b41c0c03050302146070504000301100c1c144058100a40c10840804c0182040701e658040c00103601c0180e521603440c1d107840b00c0e8a0341a00c1074620450940317850144082c001ca645c641c0d464007901c1340b83d4545 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 811387185 1250 811385935 811385989
    0x705030901061d071116030f0c05091003080c030d0213090605100e04150306090b09210409020f0403120215010f030b040b071b0b0402030f0d082d07020a170306 70
    0x285041901c403000609141405800100400052404064107203000391504a2702e40d80b96001e01202040a0b46c4240d803180001c081080000d610b400140038000c0d990090300d041c45400c80c028000d90700301c2080e000c01d500014805024802c650320074000200012114651030010b85900030340030320f144100c50790089845070001a041c1d002040100c004641c00f0360208080c141d641880840c01c24291014949401041c80b000740c2030800481c60110382c0c00140c3c206150501d0f00c1000c3c0001d40c0b00001140a2401c20300c0000049280d074015000441d01c40c0d0082c04600c3d503070407606c1d651b03418141c014500a1060400c10f101180b02d80f020390390300903401550342c010368543c91000d84006e5060f01c0c488404141c42d07900f20342041a0400d07041d015620035412900060940d448403500c82c2d40b814034400000c4c03070001c0060318081c005000690380540c265003040c41114460401486400704072404005030340680c00f00750401103040c000c0f00803900528082c50550a020f4005184114000d005801482d030342104 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 811388435 1250 811387185 811387217
    0x507021501170a170c01051005061803010b09090a0b0a0216030503040c030206030901090201020f0c01020a20060d0b010e040c0e270f060108090604110d080c060705030901061d07 78
    0x50407081350071610001030642029040c840a03404007400c00700d41e50906010451000800703400c43d0540f10b00a001609005244482c452051005201680d0641d224040312466803154040035000c9d12101c0041d01c0c20750707228108024100c1e03002d0181d0031868410000801c030107079038045402000c0d6040c41d289680f51214101002101c3d4940c1020394031030320000a002c031030081580f010445c10301c01e03020f842000c1c2d50003080c180c46642e441e20035400740c0c00c0804404005011107030503444030540c03c030003491741504071000b040703c6030071903007254045507a2088040810b40e00700ca040c42c3c1ea00012601072041612113000180f88038044034801d402004083c40c0060700140120600c044510001c1d685003052601e003a003c0c00300c2c0d00039038201d4041400c4502140050101046c2d0274071480d04140780000218070345042c44000d0407844010b0b9801c900a020354010a11706101042c007510403030340c40303c0e12406e001412031b08480055200706681c00074011303203c0f07000500c4031581c3d50010140c2081c0e82090002c1203 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 811389685 1250 811388435 811388443
    0x30a080c0c220609050f18070306020d020301050a0b03041a09070503010e030a03140114060a05090409060509070501032d1803092102180711070315050702150117 71
    0x450340d015680c1107407030b140085040020740b50100a400148007095031030885004807403065461604005015000507001038101042d9001c013842c0030202c40c1d002d5960f440b0b0504a0f0031446c60203c1c82c940000c0104510303e02410342c100074090800c68185541841da490080180c80ca33a50070b0309500e1136000041c0300300c030306001d0f41004202c0a0300170300083d1b041140640e101e074840c4008402091400c290003900452035143c2c107040c0c1e401c1d0b2100d04c2c0300c82e05420400840b6000000c0c03070360401904104441c0942c88030b00030020744a108850120707403030a00603441401c10401d600014101464015508481e410701208044030758000070741b40700f107440c1580d1844013405400300300e0300015401880800805a1008502d011115120602c10012080040981d0003c54030440a580301d6180351007440c8052a411103a134110045061800c401c4806410b80c504104050b401900e02c5030040d9504c000d045c000340112a03010b049403000c0c2c000103030039018030000601c0c10700130052000e02c0090548840e8000300 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 811390935 1250 811389685 811389703
    0x6010302031501230c01020421030c03050f0f1603080a1b0309020a080a0b07020f0a080a080720011e021207081308030a0501090b10050a03020c03120c09120705030a080c 74
    0x1e61640c17188003400303140c0030b0760080c8501d544110903002030b8208621072408400e881540b6a459059814583d10100c0d0103800c081c0c000d0203010420071a100d0100d050500610b1a0100c842c058450b0900c135081c041e1000000906004116092141071041c601301c1d02005e400c0c694560030000351084150000c18414440da1300480325a1003070480340f6052009410203540302d94059401c403031300b60210340b21168588001502c01001c115051001c1051940a5000998040d0040c60b00080414a0054504451118038001c00180c0d548560088041010401141103000c42c6603003075140c10a1641342da600110003c0c690710400c1982000301301d00082e4070b0460701115401406070f6072a41000a41000104028401c210b0224a4800c045900e400c3c4040d6142317079080d45440309410b0100c00a0150b0203540304100c0805640400c018805032510443c10260282450444064a4010520512041240490b2098500d9000c035000700f1090f0b400142101c0c1013644803401c079454080c4140340c07509e80180350f = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 811392185 1250 811390935 811390997
    0x30110c030c0c1f082202190914060306040f05030d0f0b0f1e1302041e052e0c1a1503280f030905190e06010302031501 52
    0x102107550300000200b190540e01c045800030b51100d8501c541a54101119142c84041409000003a154114480590341004030384e00d09170f624030301c1650001c0c82c4034419400914200114034030a200c410b1171841200380c043c4080b2041007440c108000000e60743c5000800040c550001c06118400b00f180078029508440c110700024440403a6400f03c00025081c101034050290700101d10004061130721015051400910030075405500400105000710702c0452880341d001c25408101c0099030314078010ba401ea40b032112500c0000b240d41801b0422440141c00300035020019030f240011040c0410043d9460303440540ba042c80740c4604860320b455003440c10022074000064007444100311480071041d000c0a00e40ca0101c0030f84550141150008084040d0510f00e000903c00350342c4140d0000702e01d21000030540c1c2c000d042c82010320341d0301c500003504400100c40600c1d20307100c4035208220f4a2200d4030902d80168003400c2c15403c501e440b8820034441d1002403003403410084408005600c604404612414545d54 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 811393435 1250 811392185 811392187
    0x20d1103012c061c1b080601090f0606021f11040305060f0c03070e09040f080f0a0207080d17100b030c070309080703170d020d05070c0330110c03 64
    0x14940481c040d482c0d444510011081c1d003014003540c0790b0311000c005481480c00401d10a0072500c550342d1055820b010801c201c40b4540340030442581030b21101203040042030301c28000c1c200b075810161300000781d556a04044002a0900341e051040980100c2c502c1703000c0c0c691441b800701c82d403e03101805014103002044044119400140030090003008510a88a50044c6c0602005503c9440380500d8902c402c90f04000040c91681440c0002e1815a4080390010b00440103070000b00040c3d20340e030900d40d00c54181c2c418400d00c001040103040d50140062070040a0365409042c004090900203450814007006240546013510300041c02c1c0500000214050034140c00c2030794803890f1402c0303c0c500961111310140c001c2071200c00001500d07400001e005d01540c0c0d005030003518021a1210045c6990480400312600039020b00c4200c103850f0151141c1440744019580e0071800c03020506000d03045005c01c504811400c0d85d8100d04680c0050014050034901a5140c00004c0242e4410401d1381d103805060380300601408 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 811394685 1250 811393435 811393439
    0x9010c03080705041805061e03030d020a03270c0b18040b010c05060702030405040e07050a050910080d0c030801090c09142404030611041a0d09020d030201060e100f09020d110301 78
    0x5d02580302510a10082d01d0385410703402d01c1446150560100059603915a00401c050b00c81c000403a005007050191070300b0701060100345030566141000f060488030f1803103a020307000c000c10300c00d02a4200c0d00426680208a20b03101d1003c0050402d290076007180c0e4010707030300d810321120300d640b054803900400d9801c101664994140054001c0d1244e000d48507107403203507040c89990360040d42c0c0450144211100100040344070740c940003c1c051040401400d6201d100039111002070049014042c08421071010f0b80c4108041c1050300d400341c08036030107802a800c00c41c501a40d81340242d410414035400c1c0c8242200070b40581080d4000aa0525a1100401440186900c1c203c00705000d46000d002924480d400078403800b59502e184844038010b621501c00e00c0c070490740c69199204100d10041241410307210000c6202803803500403840c0c03580b0300502100181c2d03541c1c10400001d010800f080780c00802501c20703981440d29186a00e1509400790095040d42540001c1d42192801c00d40c3c8505407281440b00501e440350307 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 811395935 1250 811394685 811394729
    0x180618030503031f050102190b070c0803040f0605070c0f0f17040909050c03010e030a14121305010614100810050d080a082d0a0608030d090203070b09010c0308070504 73
    0x134550b40001000c80d00b070701281a41c00410811505001c2d065101c458504903103450b601020041e00d48010b000e40c0141c80408246524000c41c45240540115812000d01e0b140600c02c0b1000100100104440c072021034000422656030704d42c00c01d400400200c0d202c2000d080980e0800300000041210b403400242c0021501001d030002400b841c015015604154580b074145426900a00c0c002039103900104012a14280550090001c405500c81441e00700602404000701c002010b441840010700ba501c4030404200c400d0142101a10040e1700c82020950801d001c1000d400d050b0150105120092000825840030101410b0041c40300500c40701c2551118100300486901a51a0400154410001441401e5020004240d0a16040c154165200f1440c6100c444003005030020980340d03280c82e8000340d0100108081c201c00303064650002910f00d810300c1010b18007002c2d98843e0440328801d1084400a80e00101d0150f80c2c1601810a1561a5103d0718200c510748103039009406101030b9a81242841 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 811397185 1250 811395935 811395961
    0x519052208010603020f060f0f0c101503200a09091103250f051302090f2e02070803030c2b05152d0607020604090c0f18061803050303 59
    0x13280292545041030451000303000c043c1c0700b0301ca03100340c600404011082e2003800c00300040c441c004041c0d003505d00303048010302003200b6502507080d110580a00c00c041441840042000080702d403203c444e01a00c0003103010081000e0109910a40f007040355288144401d005405041201420000b03040d140761f812043d444000315508070719145983c0d04268404102c0c0142195540140c500c000c143e0301a41c900d8800b07080180d8041c1302266040414000320b55000e403105052280440e80044041241d001030f91460b04a0f100152800d40440d8030034481000340040c040207da0b007108041e0350b055907071100314001c44c005e942c0030b007601c80d48114440c00e2082c0c2d91001c1d03840306014503040813501d50004292400c01002070381140c1a1042c0c0c002124007001105055800c00d9025003021306900d08254064001400756000b56000c81351031600d0740001e4920660204141309051040e04003075908a4040c0c0c01c00780203030729500502081c492101c1021504031580c260090003541d1240440c3e0381c07440c1c48141350440c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 811398435 1250 811397185 811397189
    0xa120e0a23030307031d0103060b2a01020a0c0b0a0b12030a2010090501110a09050307050405010b04150c061b020f06091005151504031205190522080106 67
    0x441c0440040410080c60084204d41e0074036090b903141600e07040a0001000e0041824407028140b6a40d4070001070f130700326144003034820714030300034041c03081ca4010f54141d800c44401c40d400d540e0503034410880c03005000d400c242c09030481c0350040c8030b80382d03070b2f540c0d981e981350050405a0415500082c0310703114141d034500010092644e40c400d581c0c0c0841e26209626802000b908051556001e0b406c07070311110644501581c0070b105140d000e400003280f9070903901741107007440e03009501400000710703003200501290404000041c02042e003507504104035850039803852414092070050648131550080881201d9101d40022140e460300710104200c43d00f17440304a00f03e41d481c42c108203000740c081c00f6120048000089001880384112401404400400000c04e500915005103c10803220020740c41d4010b544409039840d540c40100c082c0a0303503032030450034a00c20b42c10030320040104010080040044110308407010085c24ae4840c00c006031511110380c00c441c425030320030602c0001d00c9404100018186015042401 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 811399685 1250 811398435 811398479
    0x61207030608070e0609071e0e031b030604030c0c0506120a050a05010e060d0302071508071e0512130605091f151a070f0c0e07030e0a120e0a 62
    0x212481d030b00c2c2d404984541d2984680200c01401c00300080ca2800c4c6000d19903405003081c03816101d007962583e003588801c002c8140040000b0244105d10480382030405c003d040105100350007039020218280040d6582100810040400c9401a04c802c07c2100d010f86110103008000e1240384c50741c81140380500e4980d070840d001142d187c100f00109603a4480c501c103582c140c8001e201c44513500c0d6100010300c440352180782021411031145000018a120180d007040240e865603a031350140506110900601d032a001c2c0404040d4070a46c4105492140d400c101243e0a000c2080000000c3e41e45800408030402d4550002400c0c0c603040c40c0410a07080e0300421840d010302c9a01001004040242c100b49081b161001001c0c0c85007565000140300c844c40d07040c60740c0081800c403544a4503001060380d07501411140c5a00c00c49400e080781c0e0061201c000072400a540c0702207686000c010618901210581d2284150000340c41c004460040c40140c40c422060b2020811000d820001c1c121b564222000011000e602c11034 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 811400935 1250 811399685 811399691
    0x120c02030a03111303030e0a09050f060102010c09080c090c0d0f090203060108010c08060d020a031703090d140a0f05040b04060503160306030c06110118110f01020d120f0b06120703 79
    0x300c800c0210252200d840c1c8041c0c1301e403010740c11681c060b980700342c010046a900c1507182c03000160340c15850150368440c90005a09841c6410b244c1c00190075625116444070030301c00030700e205102801d030005d4a00800704040301c04802c1b50311106001d40c10b500c00c5e0301c001b921260074071000d180c0d500c90704d8111300307042442901200d2450703076103100481c201d50304072088000143c0058003180451074403160320105640000c1c04070140c29a69513852908460b00c0c0c00c5001008008002c00640301d000b403018280c00711890030002594440444400084d200d8541c00405101140c42c10341d60591043d0241c1d4054134012a50f00d50f5141c0b01e2001401680044520320000e50040d520745610030301c41d01410044960001c0074109150400c40141c0d903041c0080d00e006015985c0d03144100f0031101c01c1f400407841074002c2c2c04800b04c3c00706100030312030064101c0c1525410756008100241d440c40c0d0141d0a80e4400200700d81c00078002c6c480c40c1c803250150041c0951103501900102c0d6240a046c0030700e40760303030007a05540c07010 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 811402185 1250 811400935 811400951
    0x30203130f051f050c0d09021203030f100509060d120903080301121e050307140309060403080405040e0609060612030f03071710051c0201050702100806010e0402070507120201120c02030a03 83
    0x1d03002c0d00c000301ca10080e170ba182813100d1045500260481a50584018005510b100000a50741e14640007150300302503000d803c80c144181c1100500c4001c028040a0f1003116080c900500419408210703800d008203040c40c160210011188a100403c021315404044240d595075104041300c2042c0307048005880358180c540d0a0790880914400220040e41c1c8040514200403c03030302c0f00d0220426000301001c260000700401d04295503031078014009580706101c2c441c0c4560a20f414003003154004105441c1c0c0e0340c400428003a12800001e071080c0c0c0000300b03c0303003a506030659040c0c260850003aa8242c003844030703011042c08681908030016041012009840d011950303980440a54500c01390312a0b55000200409058041080800f008100e540181400e0f898070030742c0e50218901030440b248000004440e4001d02c9007544c2d12100c45090102d0458040d07041c03184940f5015281c081c140b107078141c01407404055408590103503000038001c1280c1c28082000302c90088000e034495001540140010f4501004 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 811403435 1250 811402185 811402243
    0x150e06030c03060421170106021c0815040f2c011103130b0c1c090b010b0702060f210717060d05031204060e010c0507260a030203130f05 60
    0x40240f0940e006401c440f01220f101507401e641c000901c0c5c40c9030421040005006e0415080f1562500030b180907801020080b01c0581084030301640d032241c01d400c22114a0a1007038482d42c141140b08110b0040320001100421a44548020304070151301403003140d1282c840c0ba00064103000510400c400c0140244032811035580d056a16100444110800e10945104130340455040e1030b0ba55070240c10102c1243c9410340d6400b19401540b800701d0030208140d200e4805504110302c0d401041d004041447d074041c1483c510f580042d205001c2c5402c2d406004c0000300341d07080f10707500117a20300704880410742040c012410080002403402c4900311056108448480102c2c880381032070440a55540c0e0401d0245003080e90320302054600410290098072415100c54107600d00703810a11801e842106280c64a5960b01828508090148a0055117180640e0b1000e54800307030289100c01c4811007205441c0060b81d136a41e585222040090200018110f150f003025100c0070807200003861506098450f464401030141110 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 811404685 1250 811403435 811403443
    0x8060306090102270a0512061510090e150901030b071b080301090c09030602030a14090a03050405091816030605060d021e04110c0705100512010e0406150e06030c03 72
    0x301c01301c50030b5076100100c84100d0350004902c281c0c401042d40316126030784c400144400e8607640141c0200d80050040c003d4103c40c04400b06a508070950f002d20b40052884005400c18076503201c0d040c00d040c1500001000142450042c00c1001002803174908207585908140800700e01c00c44e1440c0114109800e42100044443e29207202e8175480b160303003417847c1e003480541e4001d450944841010304c4003803540071000601e640041c40c0708209154001420169003001007582020103410f40f400b5401400040300480c0d0300c02c0880d01516403d1f14000617503103e50040a680345c04030920300c10140950404035202039100f02082c02140d0144500340400d03200c45080000c0003010010081d4007505100101c04002c9021400a8050728000c0000409502e03044d0031076602e9000318014103403030b04802e0045c46240303441000141c5032050742c5052410300700100c00c01c40c000b94060240000402080700090100320f42e5800442d544001c14202101c1269242000800c621003950020311038082ca81f043c00103420001 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 811405935 1250 811404685 811404697
    0x905031f0e0a1a0a0b130207060e010504050f070e061305060a080d031407030b030a060e01090507090506010810082a0616061109131a1f031a220b0a0608060306090102 73
    0x400283d031680c1d00740d0500c6e0007948a450125101a02c1d8010752040c00c20038414144940c3c080e4014044500c41003040d07509081c1c207a001580301c22400d1040c0b203102d03100c00386100b0010520020026664543c840010100c007025440b0000c03600c140992150726560540154519000c1000513030b001c0d46540d20244c05480206944941503881040c2000c0802c0940d040020b0b128640c0d4000115005070b40c0b86d2904001391a085406225152010301140b9684052502c0e4400e902c0b03408090103a040c1203499849150020b0225040e00318040761020b49205078519401d05a0010801583c0704404402020f10300440442540c00901d80ba603018002a20300c41120303002c480090070700c083c260100c8107440040020302c001c00c404481c4113401c036503241c90f1340c01902c410350207a100c40340302a102c01d64001c003070360301c41c801842d140822a00081403d0300d130046064070340810303030104442c43d944081c1070764018401c0c02e9601d43d00c0042040f001a080b6040240741d80164401e43c142d0f400d81c2ea43c10501c6080c0c1c03240c0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 811407185 1250 811405935 811405939
    0x20a090f030f020d020f0a03050307020306010504090503041e12261e0d1803080a05090106051c020d050102040b1b0307050a021507021305070e010905031f0e0a1a0a0b 73
    0xa54a031500600d080e03444070713610030b10040280000c2c1c011300c40070452142140c0c100315030540c0700140c2c000030352608104460041404440c01d0103c651039566131038907402181320b001e01900b8129144044110034690f000050700d10001c2c5080914081d0411540068605e1800440200c4040d00404205245021a0f080711222030740e10034450341d00000c4c00c0c1e181c0e1003a4110b810341682c50352b81041d02e104405034441250b010380d44060080c01c5c032001800489001401340b0613130b43c1c0b6041081165444803000e49030b401342e10401150b0005041d002040b40003002c1900200903500c0043c006c0f0f4000b40c2c89001e44072a10a40102e44c4031914010701c241e68a2242040140407035000c28982d00051070040c00410040c58603014690802866901182c82142c0318103581a0040d1281c040140169010304051084042480e00481951800c804282c581c403c0090112681e03243d80015100c80c000c640001d0703141c096a00c12a0a0f40c1c0c1c407400e0807042d0590041c100301031448140c02069410305580034440040c000 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 811408435 1250 811407185 811407203
    0x203150d0b070e06040302030106030302060615040e040f1110031d03040b0306040203041b032607020d0b060102010213080303070f080c1606110304030903110402120a0c11030a0201020a090f03 84
    0x58076426603500303c4000b581c136400401040040b005803428040d05005610a400401d00f500300342d0100080c6221401101052942c140001c0110600041405030070541000e00078140c1c4000d42040c200c00024030351001d800541000c20412926071692100441c04420708000600c6401e50401d1516031040703100d098825001800800c02d00d14140d07000b560094800c80c000200d40074420101c1076203000c2d65001f0b541c2c120b44090f481c6541d05c0c0c18144002d071b0b400c43d00c0d2027070702d45203440e40000c220302c8074608050103146070758000a0340c590003541190206140381000141141d134682400d60b49034000c880c0d10002940e107800120f861402403012501540a409199090030010010444200c41c0d1260a580d41900d8000368004042014010340c09240640c1e03480e14254194100702100c155481107944c02244100405041c0114001806410161200c004624204003075411034a020110303994003183d02001902034566038055000b09170508140c0c40e110111540c0710500b099150300d611002e404082 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 811409685 1250 811408435 811408441
    0x50f120702010b0d151d160602010c210504110a0b0417010e060106050903030708030f1803030907060e040b04110a02010b0d0206040902031e07030c080903070f0825060203150d0b 78
    0x200c80d03040002c444490411189a000d0018032082ca416051240d0a087e0001c00b0000e01001e1350a0081c002c0ca981c090400e0040c0102c51405160000510201c81c0f11040d070341c1c404101001002d9490440d5000001e00c42c40f0100c2d124891031625505c5445000882c0131500914520300d6018044e41c3c0300720120313a02601041c1e284c0744050311668024111541c0c03501040012000082d0100b010718003d410441d00400c41c1d150408520300030010182c0320180b10b5105104014429400060fa101510810702d48920901c1080000c0340c090102d01c1d80103a8040c1c14a0603005130140d40b44050708180625500900450b54242c040c0411180740b800040d410403800c01c030030700804002d82c0086402103049480740400d40d40700780c58508051802c9e283c10b40000e0300d403181116020b50000110341c00c00d0701d800295151241c91b41e40c171185c9482c2c0d030303000030100c5001180c1881804c01e0710044041c3c69440000300251645a464045d000b075008950101d0f100801c902c03155206d0a11141896499600403401a0551 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 811410935 1250 811409685 811409723
    0xe06150901080c0c010c17070809120a090806042a030f1106120723040e01050d0305041a0d0e010b0d0201080604320f190c050f120702010b0d 62
    0xb8000300040c030341101c00c0110881e803941c05d1050000c26441907a0380644c00380124010584200081c04c2c2c10200f101420070722420a40105400c064000c21180b0b00d0b50b282c1070310b4420745021095600000c00e5016074410001441b00a0150304220302c0d584100c07014200012040104c849181d000c05007281c564283c404000030701c4201c44042005008250710f080c0103403001c238814800c1c0d00b21014000106105d401d08504e4035411001c4400811301c1c90814100360600481301484081445040e20840c1290f1080051502403c00c071001ba1a43c4900d20032140052400c849069200380c240c0b03000c0600c0d04c201d40340303299818441c4c1c18241c2c00003081c04841407400d13001105c0c80b10000c0e040950240d5105c0401c0c000400741d510440003150a43c200740701d4030f040711813900d0450000414681403081d40c0400c0146044507009182269150540e000540001004c0102e9450050b0200105542000202d0b100e100b02d202690511071520307940240404c4080704148144030801520061007035400d03420301c442d51 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 811412185 1250 811410935 811410947
    0x510030b22021002011e020a0c0f02060c070605130f03110103110d2d090c1208160609020a050307050d170706180b061020070b0d02040e06150901 64
    0x5280d00d541c1140301d5070030980010340321080040618000d80e543d45d20048200300301c020501c501000260007103080c24000b08001d0210000c245004102c030060351810300440d6240c0064480c100b03100f00480e00041c1d181d42010300079600c010084c1691002043c00002e45d10848121403081d00da1000c2452224040e00b40154090304e0003001070284010107000113000c04500340305244089010310390845500d40311420110540300030304022110390b42804060300100b101c5004000490b0901c011021032032641d81010710300c038010308144041e290340c04081181802040d4011a28182c022200d251403680c0e2002010340d141e8041c0701d056000100d1102000c080340e035450a03041c4421202c00c0c114505100c40e40c50008881c05500780340e22600740034040c1401c1c80020382200d03500c41c805a030403541402513041c01603d05003425151a8021261b00c800c41c1120006206020040c00550655502c1c1c000714481c010107900940207242070040c401c17001a0303092a00a2008484817070300000a403900000000440b0350f = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 811413435 1250 811412185 811412221
    0x151f0f0603020c010e010c120b0f091303020a06091202010509010e060604020705030d0207030306030c080d120b0409050708010f0c03050c0702040908041809060f02210601090f08030903010510030b 86
    0x1507551728003034518542c0003070140100800055a07069201c03552904640112604003000c0341c01032141d01458420750301c4815182d9040550f0342045111004546022440c040c6e20303050040140b400c192070300040000c1d089084000c1c141a4009010b9661007070101e500300c2c1c01d0300b8082c156650044c3c0100742142019402040d025000e401600c2c41c26805980100507030b03105a00440000e9910700003001444400c80316040a4040e20b8013503c500194840d0003044000d00490170101c503070b0b46401680c0c2a6880c0d40c811188164440301362041c940d6905005402403c0304004449094204907454000380d102e8400c02d441010f01050650034011945c013804014280c1c0c80c1d04a0300300303004110200d80c0d40701d0305410b602031010b00800414506000d00d000002d5514038500700100c4c500600c8520041c0300b0310321601c24034140b4405050440d13035407080103c1e80001c05510030342c40c402c0401c80c0451540c001000400c01c245c000c0d80203200c10b44541c110184d18051a100c090043c0c0305100209079101d85c0180301c0d8003 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 811414685 1250 811413435 811413457
    0x50c210a02011808062a030702030301060305100302031c0810081e010b060d0902011806050d05060f1908011404170a020109231501080c0409080c151f0f060302 70
    0x10f000c585500741c1903d0304d0402d0b51650b5a6904a19100961860212580e615040200040b9080d400c048101070f681c1d00044c0640320906844400041403c100345800e4001140c000f400c45024819000040c1803905400141400207800000041d40700d0240b0707401681241c0300c1d0801403e050400180703c1034207000f00c209605803952109440c5945a407007034040c25005900c000c1c00182d040b40303440090410245a400408005a6400c04001c61604101a036402c00000b8001041a648100001d8040c02007100c10340d90225841040710740016581c907503107017a1703000c1d038000700901440a42e01400c40802241c008085458204000c1c1c40c00c00007074007038200d0410900010800c05503640e034036562445140c1140c0c0c2c0401c041a48d2001c920b4040082c035180030403503c0c091910b94140f080c20364665a2040b003207401503860300f14040c00c0003840c01c00c0f01c7c00c012040d403d07105c5540c09000a15101c0f1000e1316200801168042230150b040c1c40385541204851030f0101804845240c0341050f4007a411452081e0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 811415935 1250 811414685 811414727
    0xa032903070620070611060702071202010f120501120b0105030735190510090c12020105070b09030c0d03110a08060f0405070e010306060c0507030305160f050c210a0201 74
    0x85030502e0204804c00c060925910f8400506144d400344514080c40100100c04545c443da500700a8950085203078825660280303400d050020342c0440981d00042d400d03210040d85850030000084080c0c0110503880114820a00700c10144d0340c40302010350300c035a240600310700612080c2400c410004080303840f0184180c000992001004000e46003401c141c120f0b40b4048502044410500401100b48526442007c0e00d40c0104140c0c8000d40314000000e0903030040702d86e003580ca80e091006681c00f0382d0030340719001c0e8007154401d5503160482c8070903240e40021103014a184160ba5180400074028000c0c0710b818071503124900e0030180300d0841100c3c0e0200281c0150303080400c1e80b85004960b15035003e83c40c441e1105440b58007206100e07000040440715141d2000040210f90070245000031800304e0f01c8070032640c240c40d00c50707220910ba51401c840303040b0400c401070540e00c428220038104580070558006018080302c03c4011984d20300e00d219031081d6000050901c60b0044018000158001d6401030083d0b81050915 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 811417185 1250 811415935 811415987
    0xe100c0b0705031e04051b0306101a040e0a0c0e0607030806090703110d06030311030f041802040503070306090c0b1218011d01050906010603022b0209060a0329030706 73
    0x506a01c01040c1c03000d0350550040e84410a10f86002c10040000160940040402b403500d43c81c01c0100f100390340074118028041b940b03007159460742c200988019210700e143c2c50255060540c0710300c0081042d910030a001c200b84400340c154916000080d0b0308400e0f01601c07940c074150384801c200030720040000e2805081c9a03465090000441129001d0300d00000340102c00076000d0f0031400c0142c00900340070030002c80d540c000c01c01c0d003c0f516844015a01201e565811800c81a94038440c010b001e401543c0009070188600c1900205028081c2c0058607814014000e03007140e00d840d0f6098100b24494030b0a04c0320811039040104000080a04a0b8003000c043c18000244040c00410ba02d04030184101214159039107031020300a2b28502402001d00500f8181011441c140e07020000103065544c0742030141180c10000c104290688454044408000000380074541c3d4100701c034000f40007403440144c0c0d803242103862150482c100c070f6480201d0090040042c014000c0780c1c58244100c0b00302803915685103c50512030704e6 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 811418435 1250 811417185 811417231
    0x12090f092a0512060307050d0311010b061201090c0806010e060306040f020c0d031b0905221d0d020c03030d0216050106090e12070b0609040303090b070e100c0b070503 73
    0x100704815041039946a0ba29402182c00d4115a20040e220718820703000004100415545c5054000c200c0d036140c14500851040c0c50341c140c1c010034003072003699088140041d0031541e56050703a86080c103031a0340c214200300c1c04801200407118134108461280c0414014040e502061400001035980b252008101181c6500c11b501e044040c2c3e00070312503121a590181c14038420040d00340c0030380c0c0d480c3d0103806140e41d403034800710000403c009030a2051601030340c0f440480101d41079005400d6081ca0500f20400d02018001c6900c0c0c1d061703000a40c1c150b08146c050191011406807006c65010403000e00200114200300c0590078050080d4028022034851429091040300050001e024220042400080004081d01c83d21402c0b0b0404464940881c07210404000c5400052550b0709441c2c0c0090091324042090354451800b5001441e1b00440600094448800c0003a120b610a11740e100c1103400f590070b9650000021403c1e40e486400d404014036104507003001501031441503001d5640524a54201d25151500300d203 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 811419685 1250 811418435 811418501
    0x30f08090309400e01110403080705030c061303030c11100216021509010201060e010b0a08131a090c0a0b03010e040305130f03211d1f080412090f09 65
    0x1034041510b15481d4200c280b080341d14460360a461204030000d0000003540021b0303210f544181e01008012030804a141d40030f00c0300800550f90502602e03011511941011816031140c0f903188041100080c2c10000c4032070f000d508c40c500c88a1083c8480000f40804102c442148029400403020740d910a00c3d01e00d8410050382d00c1030260111079200b00e00065880ea10a8002800e4800795008040b1400c204401003141e4020715080f0340420006142521480e21902804100b507103441d9006030418941c80401c620446a4000c124010350100c401c44004841034028800300307103030310711a14140400130700c01002a0050200110307441440f80c5002d5141c0040c90804943d403240e150400e1038070b03000300181841040380c1e40c0c00000d22500340c42000b20f00d0507450900104280c03000003120341c0707020301c0c040d0012040c0c030ba02940030881c00c0d1403ca032410241e46c160004000c0c0204540580c0d0008607030144156150103000c0c003009031507000308141d40140c2001c1d022009000a103040b000c00c0c0400d40c44202c1c0002d1018 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 811420935 1250 811419685 811419769
    0x4140111010b0a18050a11120c0702090a021308010506010f0309020307030602032715130c0509090c0418020a0e33030f0f0601060e0f060a020a030f08090309 69
    0x1811800c0744c3c0000070015800c4601c010549105036190002c14119418501d061314000e00100a244846175030b55001c9070b030b25004150000b50046001e401788422012580c01401d0100c1c1e01c02d22942d04240d130b07000c1e200e0a03a0f83c161403183c04103803a00c5004030b001d0310070b03000128103030b0020b401c0b90b003810f6aaa031544201e1340202d6022030b0200200002c1c090381e031194240d4441ea05c10307c0000303104816410a0785079405101400b130030825111000000100001c1c264420700402c001400c800b00f61511554032070f214546c80240da4880c62a09141943d034060200c4280900c50700034000701e5403a4184a488940040c010300800550300c10b6034880c0ba006554100d00c0e108448015442003032040d461000d0603d4504404410402500300011788900e180000520750b046030322030300d40310007146542c2e0007044041c8601104260000d10000d0703d580c0040c0c0005404885601c00c0eaa0180310015800c01210040d0081d202d004c400e4004000b108901e1405510511443d0b140b101c1811000c86240c40d0805801d01030 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 811422185 1250 811420935 811420949
    0xc0114090a260706020705060a03020903010905010e06070e0109080304030f0314070302071a03150402030601180815090a0c0311012a060c02030a0822120903060b0604140111010b0a 79
    0x540c010000c1c1c40b030248280001407020b40002c04005081c8000504a40a211401e404040c0c1c08200030001c1e03507003500b0883d445600301c00208081d0748034074541d9444032412102640070500003104c0a15a51064203818100d48840014600b400e08581d1a1900c00c00707020020390400c1010380711500965907040007490380764400e0300100403c41c07401c141c100055018402c42000c3c03000c244204404080c0000c6c901d45042422500141c4e42d550720740061340c1d44012031b034414665a03624840410b24980005181081d88a0445d0250300d558078103400b981c2c2c50700018001400051203030300400000d0455241180c6081050500b002d2001000c440c3c6403940e441443c0403400c13980303451422018081e00d84140850144d8501c040d500d0148141070103030408001a0000030300e803003100c0d1250181c6203408034a5030b4480d4004440054840207000c021b02c40780d040e01059031041d190151100c80d600e0004212000c0742c1c41c46101800c040d84243c01907030fa400c200104104903540316449894544d440701d003280040c20031 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 811423435 1250 811422185 811422239
    0xf2c0907030c0b0c0a0210021002040b0309011d03070303150518061822020301020f0a020a060e0106150e0d151a03060f0612071208040312020c0114090a 67
    0x25500b032841d403440095200100b011010001d140d540b000214802900ca034064510040c0070036440d20413481d080c84036400400507403020401241c00c02d68600258041e07100d150007806015400d041c1c060504808003588120350b0720030040100080d000384c00218030a01040030800c01190303100040f40140c3c10468050084200c80e004200b80c601d841072001000c0200f4006400c070705d02d0054103030416074060340b150704801c4800c3c1c40300c1001c65a09404503400d51080444040c2c4400d492140655550384550048030a1802c00c06c11584c4000144100800c54001c0300c1108100c0200000079503c4502c0c1c059025085006442e100c0d0208444200403654044030100020b0804a255906000040d82d0041c80703201c0d410401c14409464120102c849d0440c01c21aa0300c2140410341c400c4e903107088625480080900b110a60704005e11207a0f002a0088034007450000640300c8405600f00d031103031401002c1c00d002c40d42c1c82c40400c01c0c20a6800c0a0310a8409c09050411444e40302c0c2d42902340b030b042e544841105c60407 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 811424685 1250 811423435 811423439
    0xe0a020f120a140424020903030414010f030c02030306010f051b16050d112206120327061b0203100e0706020a050604062309160f0f2c0907 61
    0x2118450f00d040482c24100b1541c0b981060b0f920307420311407140e140b40d8043c200041d040d00e80e5400c044d4101c401c54800142105d9a03269200c824141c551010b0f40114041000034807049000750180c00f0300d8080309070b9036018600d103694500054070701c0c0300610420f000f041418041e0503214865422a003030208140030051522114807900c0e2030002c0070a8000500445c404081c0e0000030b2145404402c1540f81203c8120303601c0c2d001410466880c0441142128503802c010000410f080040b981c0c0108502070385e40c01c00400e05e120b454a040d080c8801c0e400048045c40395040100c0c5120b285008081440d0051000902210380c00191500e4203481001080541e10000d81090a03010080f240081180e40040d00140c0208e80b940c03501c8100042c0054141501d0302101d021407401044444c401914202c000400b90400c80d908564444201889505120b0040b801248245110551004540480300841450340c18100d40d44e085c41d600a0301181c541ca0042204410142c2c010030b0300e44a600c1c508000c1072804c1c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 811425935 1250 811424685 811424701
    0x907020f010507030b0906130908070b06040b060403050a020909030d2405010c020a030605040611040b03040c0e1012110301021c1a011b0312020a0203090f090609010e0a020f12 77
    0x3070000707403000c004d041c0340032802200b589802c20001c0e40007000312402e2080240c05815000030300180c41c030040280c140000e00d035040000d5420302c14040c1c40f05641c10442000f5a0083c45401d00c03950001908651050800400501c3c10740d0700568020031210a407400c24954540c000305588020b020712064075019040d148011064429550040c642464804241d58081c1c01050a9841502015086c0c0d51500005400d000458110580e00d04000703414560b07a03569a02280e0f07417608280da08543d0340040c500001500b4507003038413640c000c0c1c1600c1104241146404000c04e082c14006108807514280c503510205030366001e1014100032081d40311800c0030711107107500e14801c440d03d20002003117003180308400b40c0d030360390f4800c0a84080d404880100513007000300c1c0c14142e5194100350000f0021038000a07503030006680c00300240002d104207032650036007540120100f005100c801c44459410441c094010040c11400c5030340140c010f11034003801841c044903802c9000322070b806030040801d52201d800a0120f04 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 811427185 1250 811425935 811425941
    0xe0406031e05010906151d0c0f030405150f010504051f060e0d021c05060c04080307060e030c06070e030f03040e06012003070503043201050919120201110d0206040b13020907020f01 79
    0x891003403d41f1550603d0101d13002d24550043c03000b0513a103007002000203010001d04000584551f11240206110343c5403144685803400380034003c0d103018508090100c1d414941c95050800c441412140501a90f8148407003105d206050722041340e809800f1040180150310b0300c03c04200d06074280c0c9048006250079040032480d000c0080c20b08802d03503000f08010005c501020003507031901907018a000c60b500301c850b40c41e28907502800540e00954050710b01444841030b000341c0003000202c0c090301510544007580d0803943c1c590041d40b28100e21100d165002801540c4144c244982030140383c03060a094171111001640741d0380003c4801c5071541d1002030140505c030902c0080400381000c9201012002ea8074100c90038107220b03030501c0309040c030201040390002a620302907000c18143c81c02c0d00034030142d031751200185190612108140e0100b640300c991030b40808070200d002d188946098004015a072100c2d5142c030980c1400408019902040420380c0005035180c580b09400340307007161300621044510f080c0c52421 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 811428435 1250 811427185 811427219
    0xb0603091c0f021209040204150e100306030c0b0304080403080a05030405070e010311191a1306320f1c14010609060809031908070e0406031e0501090615 67
    0x34800b854200c0c00402d0350001e01203210100c8104501d4854101d003012801034005c40e00301e00015860150b1380c00c0c0341070307118408060040c42100c8440010902500590446d119404040c1061b1052041030080c1c5898400a40e00300e0310454040c3d1403e0f07039076242c1480942085030400300050001085c001444410001e08018012405180e1255451070f038440e07030000f0241e10f000e40501c032410000000302c81200c1640c00108440070502071880c80307a201c0c00e412a40306003c068026207020501284107841a000307031140002d1520303407644501c140e03020524a000300d1040c5c400c80e160200310f588000f0144402400313068480440c0c6040101030010b00c0d80580b401c08508020700704101c40104529584480d00314100c8a850070030344081e44032445884e046218410b02d614204d11281c08844101e07a0001040c0d2040311a50303240114680c08004000594bc110310003d00f0008614a200401040240d92031100500c1180001021a460b0395054262103207d181c2102c0580003107001c014071043d107000244 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 811429685 1250 811428435 811428437
    0xc1014070e04060f120f02100e0102011505011b0c0909030c20031213030b040b070206180d03020d0b1905030c01050c06070e060403050615120a0b0115030b0603091c 72
    0x3e1a400c0014102c0c1c02c94582c442c0c2c5152001c41e00d0a0343c1404400030107a40d03001c0d005415403000d0610014090000b00d90a101c03580190710340002d00c0b0300c64402c01711402c280e590503946d080c0300d0040302010701e0316a48185415520215850000220700e0802d1240d110011321903154044400741a040c800d40a455061000200d48903e001522590b45d020a22250601c84070050642b20074450074040303905040c90700300400303090381d61007484103000c0a850841d01c94400e5508a074030554500c941d034000d01003010414081540540b1a6086080c006c0e005840700030031501c80021b024601c8000500b0910302550402280c0700c185101b4402c41c2424082c0c520841e03402e0900340d107821400c1252307903510407004000c03000708650f00e2032840003550748074100c80c0155005800c070340c41d5041108141002140070752490f8856943c4882c2c15186003000b00300105804e0704030300c10504582c030b406205c90080c692881180100f50380c88100c19055603811018501403201e807070081812031501d1110492094807180690 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 811430935 1250 811429685 811429691
    0x611061e100e13060f141f080609011b02120a03020d02090303070c0510031806090525091a010c2003100b030c0603060a0b090301090b041a01290c1014070e04 69
    0x800882c2030200587e00001c080542041c806500e2000311028407036034000318102e0090341c0a0002c00b10054002640038021800340184540e0766040c01d9940b60f60110055a40440031b00145078450301942c090244194146809450300802c00d0001b0700b1544800003c641064000409016506150319860842d0f040d40c10208004ca80b000c0f42c991200d01c1500c030040100b602c60560804115082c4603181c0031041c8a9801150b6003c00c1c0100d045949607802a031030641d1402d090420001c915001d6100ea120044c4c60fa400380d40d02a884404509401140d1004071311404410440d035510100300d603842ca204a004c1c000b90351480c0320201810806007100c820b1003040f00344140001c50380e98403180c0d412198071075070059442107008081380c090080030130040c003401502c00c20481808642584482c4c82d6600a502c094640e8852880084088100408102d0301d10182c1204680c141c40200a0000f0281c0804449da00303114040c810050f501006034aa04110303410040c0645103410101c40322900c00215014 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 811432185 1250 811430935 811430951
    0x9140301020d0608061801060b091c1718060304020d0b100317040305070b030402030309010c11041a0f041b031a030a050d1407080306040b1212040611061e100e13060f 73
    0x3000300780180302b00c0314866413984030a140c07503040d00c184088880b40d1100d600d00821700150700e441303559000155a100005040c1d0075a0a00b441d048085910840d8001c0c038030382030f460b5251280301d001c807801000103489008002010011540d40400e03d00c00d0010148076030b5a443c1149030850900f40942d00c04058213105005010050b0b5000c021394000343c00230300e17041e03410a80c0341c104040140480d942040d0020315091007112821844d01050640304c50641c0d55580b203821800600003216403105480381c0e40a04140701503559407190b0026201b0703240c200489a80c8a44140000b030500c072401204850540c40103000000d0503400c444805070f1072000c0d6034a1410200c064503045803900c030090009104a0356a20703204044d0341c3d0002c030340944865541c02c4448100030003c454a85602c28010704003c43c0c1740300340e0f900000314009070070b503ca41c420748080c2c0e041d0119158408000030016010191803001000c02041818800890b244900081c2c100c00d007621481d82405802c0320b00781002c0c0d5000b9400c040003 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 811433435 1250 811432185 811432199
    0xb040b280209031912360608060d1502030c040911030702012304080d1e090303050117151b0d1b091d1b0d0204180c09140301020d060806180106 63
    0x36801080c20b5418401c0000e68035500100c11302503101e924030000952951b410030b8003c00c0c128500c065807000d0b141e59a96407120000c000d0040000503004103022002144c483c1a5070041d000b43d070700450f180e419941015120440002500c3c13081c1480394a480700441040451982401154060140441d83d4007052280da41908100352005102622082c0c0c0040d9103032041c6c0c1581c0c04200b40c200355040603100851010303c414094a442a016400a4246800890780300341c541e2503015110303210320050114a0b0243e6900b1a144030040031619202c0b2001040605011910001c007004850000002401582640401309185410509000304100ba1a09100d03040c01c0301041401040c90002410896030b80021900c03811046400c0c10031090004034004a05070f8050700688180c400c8031049041c80c0c580c604009048a0b4600391400004404030410804c0902a400c0c61640e07074009030025240801d0020710034291042540704113110f5111408001c1c84100c0310340d800030764001e1140203002180c50156 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 811434685 1250 811433435 811433453
    0x1e05160c2a0512060a050708010b0403021909061205010c0503060d06183513030308040606080a080c150721060e100519030b040b2802090319 62
    0x215840c078140401d104612071504028040c0000e00d8018540c0400b082d00070303022500ea0005859060945080401141c0702500605c8072505903900b14140d182418919001c00c0144094841d42d650443d001c040c000c103442003980504009401000e003c81408021480c0140c21610034405420810805000b4081c680d40c81c10002c0f5010358000d580407500349114110922001c840010041a1b04201000c03a0802c0e0909804c803140b80350110f4100180650541000300315200c0e020125203101d01c640418070000c0d005d501c441da0410300a0b030300000d1881c2c4482203640340c006242c0d070980c2e00c1d0001103011135040c8010820940c401c0c8058464407000d041906014040e4245605242c4804880002c103241c10706c80c0d5070281c8018640140308401078100000b000614080a00800e4020110b840001c1508062011010100c0303500c405030b01040d54440d1078055035040094494451420b9046800c912320307078901c0340c0d49000380e840e03035006a86c0c0c469001010b10f0811071000c0e0080c81040e0110003c040781d402c80c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 811435935 1250 811434685 811434713
    0xf0a020a0215120c2b060801150f032604030807060506180103170c0709050103030906020a050606100c0506070f030b0301060b19020c1512013201031e05160c 69
    0x34480907119000340c0c200d003508011180748805c8121600b29080c06031119034122104407010038008014025044602030b4000c041401000038001243d0741c00c20000b071034a803043c0d61005000c894444c0c1c0b0311088031702c800154042d501c1602c0c5150041241f000740304141c03140300d0f00010708950301d80f0f1440840607481e131071440504c0060a00c03904105d40c82c6004141e031301120302c008151001d43e401d40303071101c280034000c0c8420f002c1a00040c4038520041452800040d81415942e000350092882d81d07620000c0050012016401404000c40300c04d42100080301000384a014290a0b110003d40d01c0b0755460050807900018507492190307050400c02c0200c003c071001207a80c584003900003241c4011100c48107038034010505408a811008200901815210480190607845215a100c0065903a900c5010f000040300043d019240540220561000c1c1d0344034045000e4140103040208049034920401090f400940f14003c01440c0c8030b808001c4c6941d1202c8007810020b040341841050181c10792512002c81142c5 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 811437185 1250 811435935 811435951
    0x1030302190201051608030a11030606030a0b0102030409020a030b0906060a0c020402070f23010f050105011431090b0d0330050109020a110c090604110f0a020a021512 73
    0x800071500035a48034404451801c0320706248410780400603d44502540e0013102c00300f000a181028000800408000b00c80c01800d000300520b040d40c88101c0e554008000e410050760551004120020303182038240090003401c6030948001840350340d000d040c88180703000201581d20910303007041482c21098110031710041d000d030141c1e8010b889240318070700140343c401182c0d0080c220311080c506091003800840120000c1c040309800a0116a003011000c60554000380070355404a110003c11102481d049800360100141d40c1300e03002100c80c0045601d00503444001c15240208198101c1444942c0c154003030a5507403481542c4411280b032503600c009010f03ca400d0500300700041c041140311958811350b0360740074110f002c2038030804c401d580d40e407482402984440c00240c04600104503071201104045081003401b600680440040e80da1042000000d14114074401c40d81d50040c426030907510403940150070100032a40007450708032064010008003802c0c0c4100d4620702a0100040004460001201e039000448 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 811438435 1250 811437185 811437223
    0x5010f031a1207150507020d0312090204050429090705010536090105040b010207030311070f080c010206220602070201030e01020d060e01080c0f0d020a0509040311060c0301030302 79
    0x960549000301e040750710511644019601d007031040044021940d1012100d40401015524003103c5041e64240241500694070107510035003040400d0217400c00058401c5584000618941c0503030001c2c0807101d0640c1d054401c104915040d10840382105940801c03c1c122000c2d40d032840c5400b218403036690800d4001e4030704002c000b007481440f04d8001c0c02542c9009280d00141c07045004010003030b075208440c0c5a950340c401c40c131000001545051903c1071614071030041c1d002d48807160840e01c080e64a03a4000c0b401ca1103510800400040181c80600f40001400500005c0c000364482080020310780320014090501c562200c102e07042140d641940510000c0e644110702681340c0c501800160004d015100030442c00354000560300720303420359591116064a0444070340c00f0150b62550700d050703a521840d81185400400003000c1c40d4807480c041002c082d809200500c98a22581c40382c7c04200c0c0407009a81c110f0108a1035618901c50309020722070540d200b609d8103107990641d8956107000355200400c40d40e00c00d400321 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 811439685 1250 811438435 811438451
    0x911101416110303030a0b090a0e0a0f081309020903060a0204050d030e041508010b1207060e09060406030212030c10140115020c090117120403110909011806050402180105010f03 78
    0x58000c00e99001c1c0b03a001801d076500c0340340480c1c14801400c0c1010029203c1c05418002440403a001d10400b8407901d0a480181140700c60765a68444001c4040d1045d50000418081d541038001d0070007200c0d0140004a40c0940c0b035503050010716103040f40c00f40c079448440d0300600045c8134585419030040141601450101d050707024040124000300031500d440c2501c200c07100c2e000f190070302054015450f0140240c510503c20054000e05907180c241d5801f03410001480c0f600c91102c24503200d00d505070000c0c4010000505503541c0d5002a42e507041c0000d8107500d90300042280440300d002807107590403901c0480d005001e4869002108141990705000321000019000343c0000d082c0d00c2000024880c010183c04178105503140c100e1070a014400d031002004902c1280e01c5101011581815241101d17485504081c3c1c24000c40204012418020100c0d505590b980340f16000311201c0b0101040d500d800790f000011a41440c1c010301100e21182c0b214004840c004000410059900c22241028002c6520700010303226 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 811440935 1250 811439685 811439693
    0x6150b0a121506080103020f032e0b030304090b011e0507021e1210060803180f011209030302071202010504020f0402090d23060907080304270911101416 67
    0x2c40c411910a030024401c0b50041072494000c1390040c1a00c0c0219050301001e000c241c200341e42c8140c0139a03400d100c26101d040d03540003542806c8401d50000070380280400c2900030280031030320f550040d074000300c582e5403240c00c44107865170003200101d9210095802d41b8040041d503080580240708a01d03000340155269044002040040340380c14070000002000d030180c1c44141c02e90303a55180d2040c0e07001d501040c41c1a20008400000000302c840040c40c00c9000d00340e10006c42c2c204126503c12211860500c5240c030140d50000c01340b0f20408512134440c0d10300588a604900305440c206c0350520701f00d4150fa1418040c0809669004c070328500884049601682d0307100301078041400ca003900d0701d0007003d07003464803007245240c40e010b81e500c04800410800c9039550f9031000291a5510142d21034006260007c100c107100070400c0000704260070705650080a800c2c2c0608500b0000c403000381c0000e4841018a1401410a24005d00c5c0d01c8480300039403030000c49112020021a1451050010641c1e6400c4001c1c07010f8100 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 811442185 1250 811440935 811440941
    0x5071e0c030b0f0103030e03030a0815030a0b07021c030e0a110a0911190305060d060504261c05010501090b092e0e15071209090f060306150b0a12 64
    0x1441e802040c00110f07040c0329082042c031034001e000440c00b00c0e0020015030307100d090010544c1e102c2c407441c0da2001003c0e00e458215002800c41c40700c801d40c05004141c80080031503411011540148816401002c00d60025131005451700143c3c01c600c420541411410b50244100103214040d054002c0d80c80a0a00a00300000e01d01400580c00000e030242086107858200382c45201071f085126812031054015840440110101c4030121441a44400c0111085011500741d5103c03907401445140c0c0141003a0b0b880c440d0840c02c80c00500115084040010780c800d501a00449030300c0c0100d00c00b00d00384800d505100c006040b4621a0181e41c18200000c00e45c14a01c1d61080c09144a5003500124100d00c5000841c1d008210500e1000282c0821011050300f201c5003040d4012682843c5030700c40c03d40c2481c0c90380d0303510140410010420401c1000048010a80d03810342c0c480c00001c5051140005416459031410006403164445c0120002c0280881009a0031b1450111800007556142582072030f0b0100c02c01c2c0f002 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 811443435 1250 811442185 811442189
    0x11502150a0e071a0901090e090604080f120117010f06080c011103040f060503061f0c030c020117012601060b0f03071b120e040e15090c040e06070f05071e0c 69
    0x40c40300450000b8880013034003d008040f400e99801c0d007503a440b043d8462040a094528221030760125000a02050154000d0803c1c80d00040850b40b8180c4c1502800c1641b000a03009900c0c1b20b100b404089403401000d1003440c0d410300f0246000e101481c5886462134503031701d080d1011410b12215041200d0030304401d000b101c0140c205a80c400e0081600c4180003003040d00104c80710f5020707684960b1409203002d0305014684040115580380314404480d5901200d288000003130881c14040c01c540d04406644441504901030700408200840110340ea8204000070a2525001c1c1410392400005005001009084645400c50030b00199075076120f0000443d424800c840c420030f81114980e03140d0302001400c441c492505015a44d989220941c00010007007100c803481c1c0f90304c0d556400854100c032581412440c80b9031040c400000d031005620760401050540780b00c280c8c3c100c0203410101c2004100c0d80c0011a001d200c0200d450301905113007403130b43c6082c034011b880756112521502000e0f40d0001c1082d10400300300 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 811444685 1250 811443435 811443449
    0x21030603050111070309061809020d11070b0403020d170f070e0a060c020423040b0702030c030c1c0504030302030a03022b0902040f0e0c040b0415030506011502150a0e07 74
    0x3c4900e0840c03403a0f08164101403021000225020800500584520545052515502d800c12486454100b039071000790311a8144010068070f030081540180302103005040768a0040c3c0202446182c140740c02401c0013100100203007480000d90200708400020414a40c3c0540d0281401000c1e89072501c1c155013010907481d002da071041070144040b813110381c0700c0750360252140b09480a0054407103100c2d50340701003c1c2000400c0015030303000700002d01248940e000c0c10380015040c010390f880d0010403010b260843d40526400c0c0442d074810034098600e007408031a00c010703160642c98160304060655070000d4903403280410010801d030b000300340d007800e0b5501140c0302508101400c4d21411140c5082c00d2032405080c12520981c4100d1620810501441090041c203503500250700c040c003004049072041000a0101d00e00e1190000e545050b2002c0d070b6030301480d120300507500640050104d58906041080142c44500c42d04c03045411210075040004411030301f031600402030100100d541c04401e44014645103041d0300c920 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 811445935 1250 811444685 811444691
    0x5030f190606050909031903060b0901051605190b011202030604140c060d06090c082a070204050f010e01080a0b040b060d150605151306030b0a0f03120e0d210306030501 74
    0xe1030351000402400000d200c7d07401121600b4200b00150222446c134030813580c483c181005001895885400108607000380190803520b0f03071400792a01840c09041e140c0e008195041c9c601c403481423211f4a0986801840548880074580540f940400e48880028100030102004021841101d01e001d0103002400400035215503100e4401245481c081c000fa8440d4159051510a80c03440e40c0c0d104110030351003229040c405100007a410000807150784889890103141c1c4009000c40c0c40140d4650045070700622a10900410a504140c43c140d450141a84044801d610102030140001d2000141d140c0c82600010304240702c1e03a403a0049501100c0000004060890301900d00c0350b12101c540c4a03105540c0103a801e007030104081c03840e40c0298400da520741c111001480c10200102031103a00100110240031b40340d5056180c0e80c50320103140e1011600f0072661302d81c900298014581e80104440740614003101c5810541d10f45440303400600703586405074070100031181d01d400c10090103604141c0065034060020 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 811447185 1250 811445935 811445941
    0x902030705030f090d171e01151106040b1506040e2e0f03060507180312020d0c021c021c0501150f0e190f09060203060a05030f1906060509 61
    0x103050380e01c01c5074400d00d03624007a400300b0000c41380054103400c009a03a03118014280500c002080c0e1400000340405403090ba0010244441e180e11a07001e4005d0013407240c2c000e44141c0c00744020b4140800b001114040303038058001c000200780c21902050b0040e000c8c0e0341403100d0039008004900b180c802d54000030040303444e2400b885112050300e520944218101d06981100c0844036100f0509900644104d0001c003481e010240003180407035008135040001070402007202a0034060100c1d100b41d140c4d0058030445107007040080c0309601480803285c0e11000d0700e4400c442580940c005100c2c0f082d80002c00042801003805041191201001558424a2446a40c007005580d10b0854040c02e0400c03001040c044015400051021f4146040c100b0394a0b03260201100d5030701e5408110000010404051900d51984c0d81e0a00e64031641c801c07540507500820000d079581c81d002c8103001a0080d103030721880c01b0b82d000d00710240e42c901000c641101070340c40c200041c101c5c0b1400e505182c40a0110381d00815449402c034014 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 811448435 1250 811447185 811447187
    0x9030615230916050d05090a020d030c140604020a1502071a040f14010c03210c17060d032c0604060207240206010e1f060207050414060616020a09020307 67
    0xc204032050444180c4040c0e50f42c03c60203040300c07400e040340b03002007101400b220740c08825a400c001ea000a5940c01c580901c8101e80004854000f0f070201900865008060321003070084d04d02d0001411080c01c402030910b400c0070350124034140d0b550312400c80c201d00c20700400c1000724030030300c1031000401440d540610b007004035589041d00c1c1d900501ca4000100054100002c1d285100320030f030341c0b103030710140c5030403d004a040c0c0b01995140800346c14062500e104102c01d600c072101a02c40c1070520091035546000d140b003128101207080d00d02410051003283c0301b0700c4620001754401c1a5819490524040c0007400c40c021403591300741c5030600c0d0306e694071102c04035000c1841503001031078800f26040e101503035420090a45140d6800702d201002c100040c5c002900510540343c0b00d8503e941c229503d5000600e000307203107668540270b00000360070020042e04128005c1109207410302403400b0641449a403048103082480005120f841107509507550028480d008805540d2041c03517420080c82d002106541c0c134541050 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 811449685 1250 811448435 811448489
    0x2070920071b03051006060309020a0b030c071a060f061e1606060b0711060f030106030c0c050303070914040c0207050d020102071208030106081b22231f09030615 71
    0x1400c462082c0b42030030007c0c071540303e030090f040e13240d4000d44540081814009640d215602c0240180c1e50000c00300641c60010f046d828110724003028451070a034450030300d4010010348400005846e44503090901010201c142034800300c1ca03c8076000c1c0f528035510000350030422460404090050a50380c98404002404600000101a0b1a2103402640824000320b0104500c13409015400304a42c81c083c4014071200b40a80e00011b8040c290b41004d00d60881f00d82d4849143d94401c541d40c40010750241020045d060328000d0025200034119070030320402d09080d400030358503100c0340b160714460000d100c00e86081da402803002e00044c1500040c01602c801007400c0c0170046070300c00e00c60400060300050000e544c4040c10408502c00000f1200b01c00d181174840a100e500345a6204041c10441003803210004c0e401c0480c2c04c89201504880348000c01807000c2d4000c0000062550701c2e290103a03001c44480007401a40224140244e0790320000c0060200c078600c0b00000440400c4e0017800714134408050031803070445861 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 811450935 1250 811449685 811449703
    0x507120e0c0d0501050906070804030212030907030f0501020702100e0d260307020615190b0901090b03100306150510050d020c0d080a0e0d090501110a061a0102070920071b0305 77
    0x2a0443d40d4a446400f021100c9c0751040f00c0240068009141c01e80e0100c555074011500100f424003103a51164503500c1e41d10990600d10780803079141e0350024042d821070400071141020710071581800c4c0e02440c01440032400100c00c09000a0200765050b82140b03030175810b0b6050781c80f00c00c180d003000c5880707190008005c1d50300c1100365134610300000c4402c103940e418540350030781140008500d0f0381034500518101d080c400d82d400903441c5034107106001c4400300704444d040f406103107c5c9251a0309980040e00c0c5040c50340455186c0c1c0e0904259601c0c801d07060040351104404289014507074a845130b0799018034011100240695a40c03034000303010308241c2d002610340c002400c0b401110794260400c0582c4c07808804556a0b40c500140c03c02040718448200207640c0250403500c050612981030728001c00e0303141d84034070440310841d2040542c1c3e0360380f40392000203580c108600009032601003801c00940b8075440c001c14030810b60b1900f140032100000341800812000c075070303c4e80b000064091091000ca0f00e03882d04a8440d00f0003 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 811452185 1250 811450935 811450951
    0x513020a080334020d1115070506010506030c0f130e090d0e0906060d0e031b1501120311160602161215021e070c090507120e0c0d050105 60
    0x159408210701c840030044841d6012481d6019080021032100507030f55488038110003100300004520040907840b080f050503160340c0300344030748030131059900f00308a0704c1d459940c0c03d5940d000040c0900b000003080007490505644c0f04840094032543c402800f0055031103030100c81512b07168007240192002c292106000b0a480c001c00d0080e02e00d0340c5084250340c0e80e0060101a0000544485501c0002c1c148080295081480608094601308800c90448169207500d40780c08807940c00000c0581c1c07180385901059001d1201c920203840c0c070070309d6014501e8003541c060141740551503400d1048002c15001d15224140c410f90380d010380b0b984020b015180b42590081e48540005405000b03240b4400429211404082e10360945555075001c216448818100e5107514641120b140d082003501e01e4841c00200d00880765103c110015900c0c80300c2e203400c4025440d10360150003042d0030401840109a0040810b902c001c40c0c1030000941245190443c03454113810f010b5145d00242d00b0f08550090103010340240744a192b207 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 811453435 1250 811452185 811452199
    0xb0a0e1905122b08060915061b0d0c02180717071d1c08070213110301061d012c060d0212130506040b0a0f0216110109051e030f01051302 60
    0x3140f16500200c2010100350000180003500086a91030300742c0140350801140b8052204166010740820180d0b4420f92580d400c41100c1c4588000700a0100141c0d03041e404136280c603081c50582540410a540100c10207140d00618660001d2480d134803400c50940c40072104000c1c10300c2810400800303424044040c0440880f81c14080c808841030426080001c05040c09210140300f8060f2500c842500390404042241d00c20040d00382000081c0050051510401e0721481c095641d501d0441c02411001100c149410541d003801d0181100ea078002701000c4200c5584081c0070368444d4001d640142901f0322000342c0e075000c640441d1002020745a80d020344070380d40034080304509940714501403102c1303066100d40003026136101c0b10000380012109003c0c5600f001d200003000c80c0505110040c042070b038010300951142840780380d86440c00d002c0c9596180c008402c0a00b003020195041c031003c0360280d400340211210350b10240d420603607282c404002ca03076440d408003c000c02c0b0b0303030030001005031011824030010391244103 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 811454685 1250 811453435 811453483
    0x9040507110304050f0d0b0a06150804052a04050901060609140f060f040305060103030c0c0905090a02041d011401151e1211120108070b0a0e190512 65
    0x4040d1038604500858074008608003071402c0c00f04400c0c0c41d0400403550b0003a80f03051984000810800016009440704000807a030b0030306042ea0b007610069081c02c03590801c5100301c140400f064011441c0760040c0c1410100c1005640040c205c2c003038039242c405049800c185024204544c0b06410760058055900d0350780c4143c0b50079500c3c07807102c07482c10341c8200c030a40c0401c4000400d03500740740c104000c00e104450085d419040983e40d48800b0b00b80030b400d0f40160b000c1407091021004024101c40c0000160420340000c100310b0401c0241c0c16600c17059014000d010300c1e50344402c510f030380307840340c078107007142410080280700e07900d5898403504000c0c40078840c0c0096042034443ca030720441c1c012440310300012400100c1c0c0c001082a07200480e0f00f4020101e0914400f41d5848044101d044648000c1c1070085034800d1018255143c0320a03070703107082026071120003412414032014503080d40c400034600c0044011101c111880d4410096410801c16940c80980d00482c4038160980817040452400c0301106030700398004090b0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 811455935 1250 811454685 811454687
    0x2031b030c1801140d0f030302071b0e0f0403050c030d0f060509040206030a090c0308030103030f08240108040809091801180f060e0a060c0504050306090a0b04140a020604060509040507 81
    0x11a41e911150700101c2c104005104d40c01410410000c5020020311030320303842816440c0c80302c516901410030b0f800680c0015244040c030082d288a40c842886080c60030050600e412941451500081c00a050841c100b2000c1402d06214200b9503e2111207882500d560380282d81920006009038405100706508044000901d4034015254505c103d402070842c1d8a15914040103500400d5020b0044504002d941b00200c0031409040246029503c01d884450510b4a01c00024081040080c1403c950740400d03070103070f8215000d8102000c0300749020709080180341c4462412407054040c032042d807600114400304024400000e40c40d03103410400381000801c45000780c82031040034480d240c44050710b17030200318040100040b00c42d40442d107200740070826100c40000740d90f13800e0b060f5440d10780c106000620103d0140014a014440350703400c1003190b0001c000c4000c1e16030307510a000744014030141100e40445c4040040c00c038203201c0200b4a940c0100ba183c4c0d15030310b803403014081d60440c0c80054001c0d0303c0c1c41c2c0055446 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 811457185 1250 811455935 811455949
    0x304151b0302060c16060603030e1305040804140402040e040507060f23070809041a040e060609220c09050f06010509130e01060302040f020705060705130303180302031b030c 76
    0x4260158003800103035a80781310300341065002d1042c072195000000e02c0c4070045a00c82c0700340d41c040c4d4400d9803042101404401040031141046824059a80c502000d210000d01220308403421603521504808501566a00042c000d0107168001488030101c075041108000c00891180300f62252600d40807280301c0f5803481240c01010010070300314400803010413441c0f024080c40140000c0da20441c015490552084007003810398001402c0c001c2c03003c40d000c081c0004c2d4a054068444103910250007061a8585580065103020014001109a8240210282001d032601c031030481040d812903d0141072075940e80a603002860200d038841d0283d4800340200b0455031050301102c1c1c030350030003d20440c048020841080010b110503071498100e90350302c40700000180c070745002e13448001504a40058458000c1e00704541080e200501942c2000380c1000420b4007845d41008440560340c040c98000424422204418201c1c03a0030b8101950522501c001c40d00000da410059042480043e025140c0240781a000d00a0f2 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 811458435 1250 811457185 811457237
    0x9031c17040f030c020d120f020d0507320706080402130606050304060f0f15050a0506090a030b0601032019081311190806091b10030b12030415 63
    0x50b0b0481c0001c40703000701c2e00c0380ca004006203000030600e03036161956542d0486005c0701081e01c04049861880c50a04240d014011100400990b00b04189010400c2e40c40c0800f082000c6400781c08030103260041054689401c0304154200100c00460340b003d0749407000038100300000c440880c440e003107512011504020740e009801c1110700300c0d140e80e8115129590340c0700251010341440412a542c3c0c026900051515019020400340d18400200845050a040c0a001010360700400d0042e0020041c00740c1a80302c0d080c1e00b5040305d4202514840d45c5e00c3d6000106c0187c0480e1005080981a09001c0700d0041d075050020a40076607044d01078017841c000c0e8141921400030403500716914010380a00700002c5281603560b02200f00d001001d0442421041c680c07501503012503044060107501c11810001d9074001080203502d0800d4018540c9a0250308170001500e000042200c0307404c040d1160700000540c9c5a00000040c02d10f0f550094907200d60301c41d03051010034104480c0c03c000250b00c1031218441c00c0705030412102 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 811459685 1250 811458435 811458443
    0xc080d05090405130204051504152103020c0d0c05030d09052815110708011a1302120406050907091107111c11041109010207030b070509031c1704 64
    0x108010303080c400c10004140007048031030000c00304800d480040e46c643c8a0301d4441e00a034260442c0001c03035107041c001280d1404940e2034451414010500501e001000b10191606100441c50448112458200d0404243c100074a800c60b05200745481084241c0c1100000e591040e0201d98102c0711a40041314144040c1c4074130b58201c911900040032551008584907003c1d584c40001811090f40c403100c550050b00d25028600020782c80d01400c00740e1080900c224401054804000d010594070a14824070940d11262094401c901e050b42c0b1104010454054440411406004152074502400c082c009000100d84986035401981c10110f0a1038140c842d10414180c0d080c0d040e82071100d83e0766040ca0085d0149009035010f00c00203106200403c0b228030800081d03201b000300428061a01c018081640c4100c04130980c05d0310244103403031491340d000a034801120f412000001042d15503090076242c0c4d00c01e54145a4060091000400d000ca101143c0032001079025520300c0d411000001c09040d0310b0b5402c0d14010 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 811460935 1250 811459685 811459687
    0xd06020a210903120e031611090f0f01120c0506031501030c0c081603110f010b15091003110d110304150212040f0302100513020108010902040f05190b03010b070c080d05 74
    0x54000703130240d00c0302000100b020110780c5405c5921000c006c00d0402c204040318103140300c14040c40c0e2801c09102050700300300b8208042c21281014660b04065000c1401140040300640d0120014050311001000040c08007401c03540c0c1e01c2c14400e9080352810000500640440d0900144400162080c0c207080d0318103400498103800e10181400e0b400d5488410a400d5040108030015090224028080400c080b007610000284400a4109001501040502c0c03031100d540107000ca01c0040d2140d0121130516007181c81e0000b80b483c04000403411500130b140604801c14a031140c01c0307814a030302c1802180558003415034141076541031540c2e4403d0784103900282c0146d42207003012800042c00c005004a000340709005850103030604414200440da800c444c640500616110308a0035560800c107000d001d4240b8107801d525060510300706054584e654456503000350f05d8404a0030391180d1844007240607042d0344005d66640e5950342604030311a04000010341f800a0402c4000603003035030024002c42e4811180d1502 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 811462185 1250 811460935 811460957
    0x105070918020f092101060b0a050d0509120a0215010504020412030c05150f07080601080709050f03190812010906080a020103050c210717011d04020d06020a210903 72
    0x41c101942200e0400280700c0003d00c071070302450f544e0a1362001d0b0480c0421290022400404000d030075101103a110483c245400c2192180541d8844101c411007040a64003052503100c0e6401280b0340b4507070005400c402c2d030000c6494501c4581c00700d182c1d008498047d0f4124210398840003003004a11a030311074100003c028444d2040042c0c01451000c8001e400b031000c0e20340e03104005054001c03080003118802d02655a500801c00c2582c1c0192006402c5003081c0f07000c000c186010280a0442e407500d018852143d030511075404e000e80e40030802141c2c00210300f0111110422035150040341034005442101e01c000c141000481c3e1114a0301c10542200c201c40000c00024100340c005500608015058641c045410441394103c40213850000f0110700001c290403440c1e03d09503000400b00d000d0081c4d9054003400500c010072580494400b07034038000c41c54440042041d104c510000c0e07618064948020a801d0001c40d030802d5072a000f15500f04a008600001c441c41d0b001796036a031045540041e40100814078041e28 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 811463435 1250 811462185 811462229
    0x6091b09060e0106030c0504080607200309090f090c030f0705010206071b1101031b23160b070203090307030c03021c080a08060418151503050a060c0315030302060901050709 76
    0x1071100d130b1028144a854240c584500342c2c04e042003145c0717200c0070039101d1910215111070400b01c01d0cc041c801c00702941c1029845000030b20400c001a000b11401d849120100d20318400900c18522250801000c80d032104807240741da6504c9801c40c0c0310340c0f8090b004032000500c50a002e41c2c000e2052030b01403001e42c802c0507440d690f03001075490b40c48002d0f4100b40da00d0040403290280140740e040b034904a500c480d241c00010340c000c89485195940740e8103041c0800e2114202c2986041c00c296440380d03002801c4141d50f030350600224510700915445075414070643c0000010f00041c080d0b043c082e070b8020380300310f1845c0c003250141045511001d08002c0c540300b01008942c0c101482141d2840d0400300042000c10104080c001c8045101115102503506a034810380c01030120700c6e00c2c4152025012075044452074036207540c650340d45401080b80003909481e107502440840d0742c403a0740082c1081a8950074510140d80341c0c01c0095840d4000c5440910300c0d86004081103100e8000c589207030031145d24041c040ba084c010110 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 811464685 1250 811463435 811463441
    0x10f051617040602060a0f02040f050f0d02190608160504060f02070e07120e0a080f07080c10062105120d0f2a0914150706091b09060e010603 62
    0x2034141c505840ca5078041841d8640c0c0c0004200400140c2e00928690510002d0741c4102c034001203440b4102841048200030254a00151030708940301150741081a40d000404036540d00040a402940a0391142c800100b10640c00540000d40e442940e950141d5550340d0101c0d1014041d2051140114000380401c0103503911a401340089034442d441a9840304d40c5e01d0018040c030070029564000401c0c041340d502050b45205100d020141c0e41031000401074100941c652080034404c200254107500320004554050020103011150b40750041c0c1e00300c43d00b14000b0392624005103680e00030080704445940520300c628243d540401c01d41500000a07000d80c90303106200402c2079000e010392034091078950000000c03d15040c49000f40e8081003400700240c1c1d0782d00007280409002c03013210440c04c0c00300d030300c0c010720510a01c1c21036102604015102001e803107611000c114164001c20304000e02450400c40c0e03140400c0b1455090b204050019203464410b96141d4096078152105401a2500b8800101c01000094400d070 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 811465935 1250 811464685 811464727
    0x1805060a031e0509010c0905130209060f04060203091c0b0a050a2405100801030c05100903120903030e030d050d02090a0f0b0702130e06060f0406090213080c010f05 72
    0x10600040265142d030216020111400c84019041d40d5442000740842d03080c01250700360b40c802c2c50400d403100d08280000d0300602c0c088001e03a1030980c1c007044075205c0b51103440c111080080325410f11030b2520350b2188001d41d00d6000000c0103002d03c03040410451040004003c6035485c941c401070b07807040f50703580d0307500c640c001c00b00103103030380c101540b110001108411a11341c003081c0e44039111100f0640c68141401d00051402109110041118040040020540c1c0b100710b141a14000c4a10f8100400b0b4040d088840c0ca500e0382024280e0428080e60f50100d43d0080402000c0303174800e0701c88042844c40c002c1090b440301c01462000c40858800c00c20310010201560003009051802052503400307035102c089505c00064940c10828081078009038003001d5103041802c1401000341141d00b448940c2044002a4a459000d04940d0085070901140c090594594003d00c0103803518210071501d6641c21007140400c050a44104032a40c007907890715850395480340302c1e00051604140c403a40d1820000340601c3d200003c180d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 811467185 1250 811465935 811465937
    0x40818030c120a120e090a090804150f093002040e0312040506060a140f0406081009170910230d0c081f06110f010513050d1805060a 58
    0x4850114078560ba050382034010460894028031001d80345240400342507103245400c005100f04450300031025a6188400d41d400010500003003441172003490b200b003143c0503a40162a01b0b00c8000c0c0018903190744030483d02408981d56a480400c5c81c0d55018100b031200d480784183c0c484450200c100c034040304200140050444c409400040d054500064040c2150080d00c00450300c1202700040c00b0521508000c56600322104540b005585450880401d0098905050345030061852003140d0394a603a46502082c001d090380c105444003001c4020782d0700020311524100f00c038030510340b10001c0d030741600100542c1d1203100003610542d110040b01f0381c166444001d031054000068920f00b1100440003070f4001504840419410204038199441d002411400000303250040c0c408032100c04110420b46400701c0c604031082403c1030104080c20501c0d060a02a031001000c00540c200010b004100030014138480915016600344c90b030804024004441d100203040d0081140b141e0b0300b4040c06107151040080640c1c0520f = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 811468435 1250 811467185 811467193
    0x20615030715140706020301060f0e03030a1407063e0a140c0d02070e0c0903070b18030106030f020a2310030f1e060602030c060c031f0b030118020304081803 69
    0x2141d0f0400c1c0580c441142100d459801100410280360421404104170a041c00d29900c0d1403e0031020980d240240c0481d042040300e0f104008401e6030320b00c400c0350101d540004040c4010000b140c1481c1c08039809111641d806503a21800481001c6501d000c1001c1e000040c0740755161461132a41210340540c04020300e06041802c0241800c1c07480c0802c2810821010f54001c2c000580c6045494607066000800302100342908000c441c11580c0e000c55500103a82c1048030894441241202a0403068424100f0a03059880c0c1000401070040c5565202c0312148200c40340c960700e07522090102607032401402619103203607465100203054034040a440e49441c10b00d14001500d40e4a5070445002e0754007260702000b100208484c4034140c5100b601030300025107035500085103011a04080b081d95010011b10031032280c0b40c0440415060303c0d8070310508618202d0081c09001c0340d5121521480158828484c2020900c201e203420720101d08240290f07031145030084005d6040c240c0c520030755800d40311680000d5900d409 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 811469685 1250 811468435 811468457
    0x507030f08220602120703052a0d1710151103280914210c0d030f02071509060f020709060f05152b0605090a0c020615030715 55
    0x30741c5000c848421054803645040140c60f00c1006401c009078203210320024001088130078080b130303080300c100c850b8060641da1201e0b501d0300070441c03140907000308208114103000300f48a1040301c1e50b2081c1d600300c8207402c40300f4107a010b803940000d081e040e0803103220b03064480502485540070740b80942e81c0d04c2c8440c891907003940d1a140a8540d14003204000e0510a400b0045000c5d207444695405801c0401922a040b01020a40c1030800014505003006000090107400399030103010001c028401d245081c00e02510000603d80389103005002d0141e4001031000600c02d04000064490118184240e650b03125101c2c0603a16040450446034006684101e005500c130f01c902c000f8a001e071500c103950080141000d007044441c20001000040d08207091507907500e64040c08541701041c42c034083c421308071071640c903c041008603082002c0060030031540311a81c0213810b0010007600400e00d81000c80418034a6003500d401e507642d010391f10b100c03801040c0e0158240d0b0110400748250003182100540c2034040b8105092080 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 811470935 1250 811469685 811469707
    0x412120f060608010e0a0c0e0f010903050a0503070b0a060b09040f0914060714040807090b12060c1e0304050a020f0307031b031407150c061404061a010302070507030f08 74
    0x80d206070b00c82000900b052004019000400c618550002030030001800300c3c070040b200042000d59141e1207140304082840840185a003c0e480f5880110760240654580d45114241103803681c00140c401c4e43d0780110080010400d507540d20410b0145d440e11100641001c0304c083c02d0000800c130fa12030010050b60340c2e080520104426160030281d2080203001080e40d8545688010300441412650b412002024000ac0c060802c0100300c2c1d4080e61000302c000241fa58440d80020040d1003407100300c40c0b10340076103024000b50106031801002456410319800c40c0b0546441e0a61649101c06c40c0c0103480c5422142c141e0b401498030703117400540e08c000142142c40160b200c0c1c451004601094000310001c01110204104010102d04404000ca0f280300140c415149000219040e04041045032420402e91018030400c004441e8441452000c81020301c2c9100c0ca401c0c604fd100409403900d4041d00d50007180c500c0c040a6100b8001c0782d446640c0302000d071044078a0359031356800c01031001c1401c03109900c1c00d1291645030707 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 811472185 1250 811470935 811470941
    0x8042a0e0c1216024603020c060406080c130f0b0a09050f060a11030405100507060b01030b010c031103120106020d080901020922060302060304120e0a030209010b0a090b1b01060e0412120f 82
    0x10400c00249005d01913003071402914203e001018140140802c1c0410440c80d41c00c00d04e900d80c802e04903000c140d074424001550034a4035016810008aa01040c4804507214160034045c244524194079510f02130340c0c4850401c22025800c6040b5988208100b0040070950320500061034844540d1007200e06254881d000a10042c0300444801c0008201048140c284031150245151081003801c0c2001101025030008000341c14405002c3e0178401074480c00c0742c610800300b04480568142e505050100e5031203040094590400f0010346c1e0000f01c444000c03442455043c03080716108600100103820054408030304c90510f00c103480c6c1d0700d4140303542d644000000d42ca80100031071089106614082c107034210310340086c000c010b500100030701400500700288010303201c0304c444606484058003503540703407485410200c4480310300d90015400000042030504400510300c111500d8907110000a003c505c0d224001e004c4094400c4070042c6c4002594503140410078010880c2002c80f0f41c010390045801000740c440c480903 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 811473435 1250 811472185 811472293
    0x501210f02030d1d041a010c030c0c0b040302090906010810090305090306010b040f0b0702010e0618130213052403060d060908030f0708042a0e0c121602 67
    0x1103184007454180303661803d204e503000c0041c2143d00300004100c00c0065042d8103020052a410f102c170000032041814042c01030000c2c4c803a8080784150115403079240380f6503c0e41152004034000c1010401240c014900855101e068031110340c000d0002c040007034150405454501410707420300c0310402c01c80303440307413414448140a040c4509080e0307907a0b45080a4640060f405520088407490b00740b050000517a888000240407140c01c076400e0b030315810042c0c21480060a644c203603a0348402e2021441d0130401c0c0e0350b00070b0101d1051914070030300b645a40b0300c00c0c4181040721403140c00503070102814108030100c0c1c0c00e000e540c004001804075405400c0544d1440111280d01e84142c8080e0800b008001c40700e66000201c1e5442640d07494a03681d20700302a95140040540681401e0022003480c1c80c11f000c011155508200500031400c020030b41d0306103800303166210340c426010b0000009000000a1000350090320f4680d660341954028007169100018110680c540e08055840500e04c1c00c00c25890300305803a0440f54 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 811474685 1250 811473435 811473437
    0x103150b190801080d031a030a030804060506030a0308061302090303070602070605070e010c0f0305090312190e09010e1b071101020d08010b04030b093c010501210f02030d 75
    0x203a00c60100100801e4041001c0115040100b042c0050014000100d03c55040e100c0a08000c902100d403002c428084001c1d00701e82a0301449a10849030901d03a02c425400d0140b0300130b900810060f1903034414951100e5003004050046003085011407e94202061114500841680010308040c907810000c0d040da07000d00b005030340c0c0b5500400c10342c0501c8854845d150300b10382c10741001341c4c2000000002a15540107a6000751010a05c1d5900e501454011403c032010080002c040d200d5513010345c1c0e000010b60b08400001c0c4c07800e000c00c60030013400a002d085501c0c40d074000280240c43c44d0303181c140e1080c420f070b00042900041000c2140d281e22400c84680103040450311468500b030406050800084c5099440c2058508002c0c01c2c0780108640754540c0210740036032f40c02c512100c0099481076100340c41c0004501061100002c1003000090124460350012200600c90141080440c04110b0746820f85200b0301030044014a18420301405070010a41d90815a100e40c1948148000d1034001070301b009180c4440c4c030 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 811475935 1250 811474685 811474687
    0x14041a0c0a3503060108010303030e01060509010b070c0b04060203120a0905071d090106051302070302160e062e0c02030a05012d060803090f180a09060e0604200103150b 74
    0xa101c0d080c01051900c0c0c0e0b980ca0400f411890030b68002401a04c0601c4042c0505989080c0405800d4007034000c10081d290241180001d541d6134845000d10342d21620040d610702d000701b28007150100d08a402c80b01100c00c9076008600f81015013681041403800903040d80402c2e560380740c5210002da001e0103410010040900c035946041c80151040f42001001007992815900d05070050003503a8500141100095100c3d01c0140c85164501c1c060b4904543c803841c0d21102e0010450000346161003001c00c5120762020342e403111603100100030b0741c08220f9150303181c0039500134a490342d03450305071003903200d40c881a0009046500180e101d4413010b00311140300d0b0381c4a46a54580300144c4800c504002009001e1050700e108001c0301d460803120a0701c90007104074440c071420302d050754408150b80d0035807101442d034032407000c03604142008aa01002041c030100103c443c41e0400e96012621701c03001c00c42d248240d8001148d50f1000b0104102007500c00b000308207150600d82e407002c5035a0050007080356280500b100d00c08503 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 811477185 1250 811475935 811475993
    0x40b011e091a18161103090916030e0a08032a12040308130c0e070917010605150301080d080702030c030408060f0903040b0a030203040602091f14041a0c0a 68
    0x7125030301030401000700122041c2010310007141c400c1e044000c2c442c013451800c507110b154032440107425403141914840c1d0060710310050249011404c841400d000720b203074900f08180480c2c448100d4807584801c602a00d801d10a1000030860709141388082044075055102c0b9012908500c403000c0c0301d4220070102d814405204080008250700602010303042005094080001d5032103a07642843d2190380e005150800c1d4074400420b0180d07028100440c05011019994a00c60100181c0d840c020552403148a1085003190b00801c09055803004890513543d0400180104500000b4180c0e11868064144000c41c8010024440c04003001e1000c0e0020b0403a50028200c6400c03c00c110100414001c0c0030f5900c103410402003000340f18210022900d000c00c45040140c0c50b640c3c0c41c20810001d02400003015001020751049000707000c0c0d15660b5284840d02d54440c01416544001000910701640c003c00540b84141c070100403d0048071409404074100e03500c11280601030b160b44176440c0f19001422001014045002 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 811478435 1250 811477185 811477189
    0x1404031113060329220c050a0605071b03150509100e0304030c05060c0a120212030a0c08070915051b010e03070b070810030b06010522050109050108040b011e091a 71
    0x4603119810813461840032034201098480b070300030061202d182504040304824410440e121200c0402400002c3c442c0402d283e440e034000d08141c1c841c01c002c80701c8000b8940c0d42034121015100c40740649070031003032040c0320070900c1643d54001d142c05000150f842c03081a402c117005807940d00485440311800e0713002c0c42d1264a14900301030011a00c0e005030b44900f00a0001059000d4009421560142c00c80c400b040300c0466210107034100026401c40d610200310002c108520011aa00324224a0065a407413686969480c001184d09000320b0146020600c00340e6046020703148030394098682d16180c0c08640354460a114849800c68000d200c2000c143e400c0442d1080074400c6a000c40c2e548280d040c24142c0e200e26228508120030b401da40802010500380c032020030201e0748110162040125103a507008900303c4081c030f458912003054440c6900080c8900d1003c9481d51081250600641d4052502c0e4242c3e4241264803a20ba0302c0c07490507040e0714402d9400041c40c11584e0181c5885000c0321407a4449800300c0c201 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 811479685 1250 811478435 811478483
    0xa1d0309040c0207140405061f03020307080c07021005030a021c0903020c0d050718230114040e03030c0702060f120114040203071b02061303030e0a0614040311130603 73
    0x48442e0940d00828010080480006000c140508048078005420f540f1480000e00942c0342061240c0c0f010946040310301c20741d17090f5005500900310b6844240899070350402643c21445100c00080d08008090102d04480340500069908603209400c0076041c5100111040d0b58884100c40c00f21034551203c0501c0103054051000500781c0b4411b80c3c20300711002d2542c8541b50766000c6482400751007802e41184541c3c20210341d00c108019010f00d0008942c40a41e00c007560070000c0217014403550544644000035040c6020310880d001c413949a0091411a510840c03021510f13041404180e81041c4104030075441383c1400c200410120b03100c0c241e81e401e2175041c07900540c80c003103a0041032070140e403040040c02003294020300d40084001080e03d515855000510116205000e2655041c1084c0f0503c50302004258010300d440c40c000074240c900c01c2425540300d10403901c6e120401012100d084080009001040e4100c69082c911080074100e008400c0d0700700740c00d204650565005844018200c281c0071380001441c0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 811480935 1250 811479685 811479701
    0xf030d120f0902030a0f020a0f080c100203030613090c080f0f06012c060f060d0f0e010b0a05090403090807090209030c0d02130207021306091d01050708040b0a1d030904 74
    0x40c0108402d601c030303a01181d80c4103042c4402a20181c20301448000310742d2102c00103006054407458284000d9643c0c40c07841c0e500c00e030001d039152080c02c0164800c3e00e0140300000342c0b886010000e00c00c018031484054886e000307100100d4152038083e8104000301c3c0605c0d082007101600d450240041c44050810300c1501d08200040e0441d0001d424000c0038020309441000b1503003082c11a50481c004581c99100006404e101e0b050303030316a00302901194200c038503031031079000034013900c40741d0018451825002060343c200e03810350250395448080450180314609148407079541c010320070b08041403a10307161030107249001d10580c442100c003900041e28402c02c0c20b080c407500c2d80d00601903d25800520041d400142c2d1000c030880d407a003e556001c41c0381c2003595611802c3c01030702680c90504100f05610350030600054030750a607102e07424255032404116149014421580b0604142c1d42e5443c6030b0321155543c842005026000941d40c5446141081e030040700720a40c215030036a104011aa1840010107200603282e080e = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 811482185 1250 811480935 811480961
    0xc0705151006021c020a11010219110406092a1b050106060e010c030909110714030904150303170c07330b03070315020c030d090c0e06030a110f030d12 66
    0xe807200c00044c0d0b000200d41076a21f502c01d240d03e0414282c40300407860704000d1804000d00c0e2107a04d00000501103803034101780c11000c0036941071041d261100101015160f4031041500712a146e1240603242d0f040014403a01464001d107026a000b01203400303501d6000b004a5400c0d50142d45d50f0800b0004180c2200c51030105100a0074980c0c2440900c2d00c02a0007100310f0711070052059220503d902c079200308541101c0b88640d00c4403260100c1d9540c18000c555a0b0002c0d1005030003646009080b50440d44d041c801c001c100d0f81c3c0340c2d40f45400700040b103000b01c229507009003508540c507600f0b0010800080001c4c802440c2c83c1621460800483c9441150070800079034a904101000d240c00c4050b003881e280030908909076900600c400c03500401ca41c2c17116000f0701c50300805916074000070400c40c80c2c0d03083c141c0000308040d00400080c5c6015441d02410f00d104481030342c80d03541c950b01404803140001c0c0e501d4070b222411031008026a0441e042d900100e42032007000d901c6000052150046d0b0010491640310b031142013805 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 811483435 1250 811482185 811482223
    0x1404090f110915280f0905010e0c0f2b0c0c030e040501060e0603040516060c1103120703080603011b200a05030403080d0b0406090b041b05030c070515100602 69
    0x24620100b120b401c4140860a074010f070000340301d10440c41002c151401001144000c5e145269200f488000034102802404034005804021032250b440c00c42c00c0da08021403050025240495141016804801c003500c00c51400b1080c40741c0041e901118410708541ca9490b880d902e4814180d0724000f01000540d51246105a26020041c011540c2c0042c030060405020344085680352910b041961074001962180310b4810400c136000318189a10844107100c03507100e281aa4104000b200400d51511584060007012100a011600102c2d115007040fa400c1032004e800000e1580d032511400d1103452200d5021008200c1003c60a441ea4130507400c00b0200c03038103100140c11040c0059448503103078480c52001400035140484c0b19110f1b80e40591044c24500e400400402a59a0f610040d002a107180c1a500d44501d00e031400904500301c0d100d6001c0c3c405001c40c1c0d01c280c44d541d2080315040d00ca4011800c242c0b000d04c41d0030b00061400029142d564002c182055410320f1440c600f076002440c00029a00324890180c07 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 811484685 1250 811483435 811483471
    0x91f1e08010b2e030b03010f0e060c07050c0105162021030d020702012006040c060201020a0e1c0206130e06010507030e0922060603110f03071404090f1109 68
    0x400079160b05982c0120300f440c0201002d280d90110082c0c13404014069042d4a864004c8904440507441040c105e0b000c1016601d03195503514540c0c4080c050500054503a40084130240e4266101d40004c1920b1060b617585101c02d103055403500c1d0001c5940c081340d81005d80f00380640da026803510041c58440aa4104080a4080740840c001500d034018a0f010282c0540c000c240d00c411603018040c0a110700d0001000c1c0f0036040390743c0d40d080399284400d0b035050300c00a01200300812014418002c036401c403141034031071003104810030307050240300360b24141c2110200703520500c2170005907a81002840a0041c11013400075081c00c0c00e105a82e49000a80154188401009180d000981160194040303550031603521f070030f44c4d4800d43d4188094060f4003500c510000c0030703a2107008120695216506590003070070001b03121a220410300c8016004543d2031681984803650801481d5426141124007040140c40400c0e07600c220750319007c6040000074121407212072550701c0801e40c103049040542c0302c5580401c00040b20 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 811485935 1250 811484685 811484719
    0x41a190e040f0c021203040606030f26030f130501061706060f06030603250b0c01150e19090501060e04120806010329030c1201020405190302091f1e08010b 68
    0x90072040c1c2003a0b1703113005c0001002c1c8400d03a0311040040d5007080b0001014001d51821a03aa1900e00317001c40428030088001d84480c2c5060003d5a108000000185550b6151040c505401a04d0a04111042d40d02c4d56030201d00000c01d2501c001400c6680c0c0b0003051a803d000d070801001e810f4146489015603828420020f643d600001d080503c4034040b0180c1c4800040b601920941c0c2e040754000001500d0005000e20b000703c815030111407515460302e042c400c0c050301c4010010400000351150007000341501c0601c90030402c40d5102000c8680318000000303944d41e0307a2024a80303114080b117090302c0e041d410a0040c9041c81d006005164020350918042117601c00192911503e18540c40031a025121104503039100c6407010040314819070001042e0a11a200042856020b540603004060045030002c101541580840f0400010f49600070078854990380e410201104000b0b0703007000202c99461510001840c800802c003441d40c1c1c4082c8461200c9050705040e0402d0950b411291682e00900201a00c21441c07 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 811487185 1250 811485935 811485943
    0x1e0b0307170c061605011a012615190602030403031101151a0d050a23090c01260a1a01020a03020a080c01110d090b0714041a190e040f0c02 61
    0x107002c1115500d4a8500c001c000700c618405941c1d004210f0741c80d100c3c40d504940001050040300e56401d994401c285032054803000000100742c405614002c5104011a10500e00c4110340b0f45084030141240310001d094401c000740f100c1e043d40c403460242c2c00004041c01459030000e2404403580c0410000d00a1940007500300d1068031711807140050740080d68180c0050f0915100444042840c5164240040d09291088000520340070781ca420b030244a88a01809840307500100c00c2c400c14070398019102c881140320054505188622400c6019040202d2400c5845c40f2021030318014500c01e0400030310b5103c07410000ca001a66495101e040d544103000300c02c000383c0e0004012040071b50003c59180c40358140c0032103e0142902001841c0b0f402c0c1c01280d0344d506144650300180b041c41c02815a6881500e030098255040305043d05140204081000240802c5441f000c41081e420b100c0303e00315107024900f0805003650090b03e00035400040040f50180c2d090b10307260250400080b15090300304034602c61040080d40d2 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 811488435 1250 811487185 811487203
    0x120a030207060f121b0207050328020301090506091f1b200106081609140a0b0612041103010e0f0703140a0501060f1a090d0609061e0b030717 62
    0x10030082200c407190b2184500c1000c45040c2c804d050501001c40f0311101001950500031240c00180320742c40c00021980b03400a682103024642541d043c0b1101d04400c248241e000c2d0958099826640791a50b08001031800c1240d24070400306003016003c0510f511282241034429000402002030800d01c8101d030003549030b2040b440404d00b17814218501105011040c0105103035038420601c035441c203a80000c00110104001e200301d00c3c0c03020000146600c1e000603004648004d1032904c0b08d4a1540c0009002030243e0380032420320300c0c1c000c0001d8241001c01402071001300c0121000c580419031f00c3d01c40080d6003424054103045641e003002400c4400f41880115680e03010710321018090100b004007600441c40c081c060b00c2c83c100c1d080070092144075101e01c2c603a4640c41c0300788584414a087d40c405e00c0f4103178502405031210f4207001410040303203030001d481c0c00303000c0c001c10399007650071603519400c16612000b2103801c05c00e0b1204030700c07001c6921910582010304214807984000e030b02e508501c0c0344910220010a440034 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 811489685 1250 811488435 811488437
    0x1d060124080604090219080a0c0e0112020d0503070c030c05090f060319060b030d030c02060c030405100207031b05060907080a080306010f02070e0108100501060e011403181209120a03020706 83
    0x148850304c60000a0201c800c110220302220800d9501154100002c200415a6401210680c200756542e18143c0000c1600b40700d03212090f602e00280d80014600303000310244042c0207804881c107004040c1c84003245000035620440b0305280c03c3d9010402400c0030100749600c80070705ca150001c2d61a00c2800b01e43c8507a2140c4500c00005840c0740ca40c800c102c150b92040007100c40203401c07280c540181c007402900810443c038420f00540308000001e42509407403400ca92080e0f034058050b09564040443d400041e411801044050000d0508002c85001c1c3d42140300e03800c83e02030f00090a0600b0405e0b18242444500d400c600d159401618020380444c08010480742c01c40000e10b4000c442c4110944224204110f68112020315404030000046141000402810f0410307282420011a6a80d0009403902000103c0d01c070b02003906444900d900c5c020b48805140c4c030508010351002450080c000f528107111001c2440c215100300428044864100544900702105000d4000e0403002040e1301c0207541d5101c1841614 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 811490935 1250 811489685 811489691
    0x140114031e0c0901020c0d03091a0f0a0c0b0a0b1806061b071d090a1103190302010204210203070b0913050f090d02070b0f0d1d060124080604 62
    0x1c15900704401000c00a5101000d5611207007050741d00d6030750395400820302600610400850150b00c0c607103994070064040d803680b5016074032442c001c60300000248030900101481810b00000d4101c0400c00024103410131240e669004910340b628202208090150450040514040c014681a00d40c05200762a40d85a10041551a6508000905a8071032061240540401031942c0d4000103000101002600c20410b03040c094075065005d06548500110341c000015401035040c00003280502900c0e40b006d00d809020b4541840b51000d034044600300039102280140c2d0300107420000c0e40c0207004a080525001308070081b40c00281d80000380c0d81d0185020301109103c00207141a255514030940030001c0c00e40c140d06002ca803429100040c110402110310803103901840718114503da2010032400282c40c032140c0349a040c2840c2c0c12450f400c80d00a041d0022003195100260b010400801d5050a40549c4140042440c1e604202c2510041c4281d20002c0000142603403100d07002c1e03504000400d5000d030060b1400 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 811492185 1250 811490935 811490941
    0x140714030c120c04060308030a0516080408070201020114070903031e0203040e0a0624020c01031116020f03010906150f08070303080406090b04060506120312040b1018060f14011403 79
    0x45401c24241c40b0034503074031605d81100081041550005148034203242d50080000740e903001c0864800d00c0514000000041e110400600091100809400e0301801032000150407456685040c040706003d4440030003141880b6400c104042d806041001061018003000055201c41c1034041d41da400b40d401404403560840c400100f61072403941c4282c0013024140164802101d03540d440d2841d18030302441e61001401081201c4510b035029001c1e2031a119455031205107032881e8640395403010300f04044100c0e4002e18462091100c3c0d80c09014058840b400391800080562014288041540d0307213a11000840c20125010000c02c2c10121300d8508407a014203203034040ba611460a03000401c0d81c07030070081041c00c900050005108095020601c1150207655428015a0341901d00703030350b0b026150040e100e104e08800001d00017110314190b07642054101302141100c94072642c42d40e03a03900501c1168a01203035a00300420070b030700c00c01509000800340051200020410383c2c0000301110309610100507048400804 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 811493435 1250 811492185 811492219
    0x819110f01140a051909110109050301090b0411061611041d06012907050c0a0b1602300a0c06210b13020f0304020a090c021e0109020409140714030c 65
    0x720085c141c80c44001040140340d20300d007641c1046103803084a4009030078004007150a0078148140c0345506d8000c20035510b80d03501c503030f9051803041c607a0314601e801250502c580c03000c0b0500050b44484440c42510742e040d180b1550710600c0100c03120814482256811032854200c0710030041001070544400c1e114118412820080c0451480350151300b001e2007040029180041c49001b03d071b8030007001c1e030840b001c1d105a03903101d6400a850040c00400900070f101c42001c40010b2412200f80c965045038a002910303810030500030761001503410310944405801c0f2581d12070030000d03000c0481000d03244505200011604948ca0003101340703501d190802c001070f81e86403401651b548810701e4035402c000c0c95605558400d09014800c1e201e400580d0100c2c05a404503101013100780142c050800d00000750b5004042c4108c0060500d2900341d844444448155039a40780c400141c0c6a5000b041821070180240003080c080385489985003481d103074040c00c5035008103154456250f802240c45110b400c2d084401304400404004 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 811494685 1250 811493435 811493461
    0xc090109030209010603050406051f09020c0c061204060507020303100905091c050a1805010c23070e04050d090e1f1d190e060103030c0819110f01140a05 67
    0x10280d0f0040c6100000500c2990507089988a288160002d0040e82c882152a8100c01c0c0107485003160002e000500b800040b959501824a4104400843d40003442d044081900c40d0700070b821039121005c1400821044c00350601605400001d180700861035440c01407402d207030540780c0b4040c13810f002d515440030684d64081040b584200441d540424a015000c814001e00940d100360100b02c00700e00c4942d0092245040c10000404440c070603107500c583e070f43d001d98406110034110070642500e00110845a540060708018440c00741140e41d203401c3c1a03050a003401460190084c40390303001c205081605200241c0c000d44100c4d04070712840304030070b0112150601810040c1300368004101e484150a0040040180030030b803c0d010f00c030700c045c0c590215141c030341301007064a07010440402a0b83c4104010800a0f1046075103102c0c0303601407409941800d808a4403003101241d411944000030391903002c0840020002d000b0000c00e0700b0064001c000410003180c680c0b111690092410b84056522030009034040e101c00 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 811495935 1250 811494685 811494689
    0x306090a140f091612060e0f0a050c09060f0a060f030e100c140f0412060618090b0907030b0a050406200403030206010e06031f060f12021212030c090109 67
    0x1101000706181c468000b1503101000c075008080c44c811246410207070310809540c00165508483e20400d01216520740e50051704050b1005030740c511560300c1c2c00044120030b01099580520070005030811144000410800e036002038156032280740610300700f200c0f43d0b5030520064111509030408000300107009e0f02c15001050401c0d4091594061503400030f0030307205190300004010304030b03480d1807008941c0303181b00c4011406880070603220013004100c00d02260900121001c5003034810280400c0341034449020050300314141b500044d599880c0c040c0c000400880c00c07042a0b0000d250001017003880d2840d199814400c10241450041c2560fa030049014407a598002c02c40716862841c0101040c850003114651540c007034071055005001d03134000400c07040c130b105070210b01480c40200140900b88411010400700d40000201030300c0c0c5591f400c800941603001d241a0307070040180c001c620f00c00c0c2d6101c2c0113104109500c0c41281d412508a1040040014100001d03660008803107a034080e200c0301200010f035080c02003a = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 811497185 1250 811495935 811495961
    0xd3f050604021e0d050109020a1205060a1208030f150102071e0503030703120c03050402100f03090b1501170105010503180f011b030c020a11040c201c050304080306090a 74
    0x300c2403c69004107900010b145003504d00c03808100b07030782c0d0b030326a64412800b0340c07600b01c000903a042000321171000300343e04042d81011006010001681e5140041011444044802c54508e0000300c00c002c00c1319640398a039680400d1100703082d20300b40807130b4000035150f01150144011003011803030031009000030180e60384081d110180480c0c0d07580c041d82c02c01504811824500950300d9060030000e01b9254405d004090280394080c10710b80b1a4101c05c0c2040c0c8240294000346410595120b1028000c1b480350340109026030000811505218500c0c0001000c904a13074003110001320f265401044640d134002d0883c0c1d030140c0c001102d180408070001e940c5041241c4120203aa50398200701a41220601170410f12441d180c2c6034608200c0790a1004040e0384405039100e0145c080c140b42d0f0681401404e094000070351284031881c042e203a4810500703080310421403451410209510107114414921084941a10070060718200581180b4007540d8185e16484000c080b240100412004030b50110203517040b1280030899 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 811498435 1250 811497185 811497217
    0x120b130603021c020906060307020f0105040b070f0206010f090504020a09020d02130e060a06053103030327110103020c25091119020a050d3f05060402 66
    0x9800004406018680000c0e031140700307046107291010703030000c011041d0360354081c0907806140d40703280411400341c1004015100750700030891800c256080c2881010303c41c5100c1c1d0000c8100707051040703004151600000b140790555008400501425640340380c10030403103410302c10200e00d5569034804220940104c0c0e1004d00c189002041c40b0094010036000f51007158001c080a845140c4d0380c40041000c010705a41e51500015184010300c0b045200300021301419440c0001e0301c46500350a43c1c0e0001e24440240014550491400b09008060f41801010071011a403100d10081120000b000c802d0050204d800900d4004c41040c0f2800c9640684c0503140180c500e1415203030002581c4043c0103810000c090388240801050002142000013403044900a801401e0303000d05258041c10141c401000e260000419407050300c40c002c1c0041c00820007003140700072950317440c2c4456420282d0a502010228a4a20080c0b51038151840040718110004000c6400203c081070300e03298400807030020310030b0820020f02070034 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 811499685 1250 811498435 811498459
    0x5070b040206070c090c26070807050f0f0316030209090708091e0c01090b0f040302130207020423010f05061c110c1b0a0f050d03090b0304141b10120b 66
    0x516980302001185c055150300c11041e07110b190780b100201c070a43d0040e47c604c07844004225040d128600d1981d12008a0405920346081b19542181d19000078000c00100a00042080651405803443d0400081d0a0a06508020002c400554540c000401c80c80400001c60001400c940040010a2002400c4d07020340c40e4220101c521241c45800c4640000c0c00314000f210001001100881200e824081846000d0300300303070556081002000062240031411502030042001682e12440303003080c05601ca0741052040c0075410070100d04103505038841c1c0e00d50706080004000c2900d4013403c460790501001001d00c04104002c00c42002402d1087c4214803144022814121850000a50a91503961155000010b0491208022440c805402400c401c0000c07280200110b05000e02d0305081d031846800c0c406200b5032109200000c0790012241507403164603100d01d102484d0020700248a0003010681c200b821001950040b5940040c00c00808040020240d0320306c041c66580e90000b001c1074801000f400c0601 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 811500935 1250 811499685 811499699
    0x915060f0e2106131205070804150c02151608091f020708071a04090903120f0207020405180c011107170d09080319050307090b0705010c020f010c05070b040206070c 72
    0x642515503050584182400718030444e162200800c212030384446a00600d000c450030440d0700d0740200d081150f440d00d0030b01011400d11100c0244072101156a51604016089401044007400b004920340041c0d0904002c44001c07005038080f4180709541000c2c845544110401c040b83d0b04c8807205050306c48040540c00f01e801800e0340807078810f04444c041c2c800c555420f42c685044800408141d900e0100001d810007040102c601c0a4111010300c138024181a03e83c0175002c241d90080d00d070302c0002003070f1460307000500d07008500d0640308040c0c200142c81001c1d02c0e501c0d9038032030701903461030042110307030500441e038220181c0c6036410040d0704082e154a0030f41240c030114540d40140d4600140150f0b6010031013034100852014000010f41d18102850302500380580480d080694050380040d0a0b0000c1100c940800318020072020f0003040614401c50000a00c4c8542010080c20450f42c0c00310303205542d040a03030b03c414003503112060324032494102406c41c0c050b40b0b0b180b0004941c0e00c5010300051514202c500005801 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 811502185 1250 811500935 811500979
    0x150703020d020d2c1206090601080d051812011806090c09110706020d140408221404022a03180d030807080702010b041e060915060f0e 59
    0x242416001c4945440185809640f10b50340a040c407101303039a0a9650010b15000450101c1580c4000b0340600144184030807241c0c101641222081e846030300007801002001d40400002d600c11040d031600b142480c580e100d004210b40304251803244182040100100b40020a46c8512018001d4101c03011440600345401400362012800c16641d40b1002c140c001a40c0d02c0030301803441c1c0c4040080b142c52501c0220f64901009400031a2075000c02c1e5030f1034100c00c20a1070304800c294001e0b07006661580d2608583c650174411035100c09420382c08100101030400c80202c406e0001d0003084c1c400c17900036132140d940f13100041c2c80310700b05c100a0341103040b0003800490701403004c00141341c2c101c844031280f02c080c0880010310100f500c103100c000b00000c1c2c0800002e00d486104050b4542c0091451002140002250002405490b1036182090600388101000c2032503141511451000b4283c40005200080c16020b4808511489226000900000f0800c041c5014070070411040d040000821055464250101400390 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 811503435 1250 811502185 811502203
    0x7031d0a030305060901050102071211191e08071a09030610031e02010206070e010318061b03050405070b0c03120124031503031103070b0a1a06070506010b0915070302 73
    0x460303d0080801d0b0301d42400606141030391411b80041001070b15101b0048001c0b83e100905990145a1003142000f594401440c080001401c0820325580d0342042241d0140e502c510420b1241100c044008001c1c00c00c01048980884021003c02c494600340c601180d0f030300f8490f61906983c940207043c10401d1041c51400840e00f40c1c1e02401c640c020f01001034029040300959080040c0c0540c0c0841d000419142c0309a00110a103c4185030110f699103440103c0104103600ea201107440c079844081c10401e5100400c03100c0703142500c91a00b8403990600352039040d01d0b400c0d64006d01c1100d00c400544000d0641c010800c07114188002d0010070b81c6503a481c0d0181a5481c400c81c00164000720346903000304418800e0003951080c0100d00d00e800322142c910355047e80c15102d4804201c07154003051004074042040c09402902c035006022001c111421800b0940c0022000701d1040c9100e8542071102d400070a00005a0506503581c044030340d42c1d03a001083c0002c4054000e4842c618415200103240400c2590210307000718 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 811504685 1250 811503435 811503437
    0x20a151101020409020a2003030c090f040528060308040e0c09060d0f0b01030c1d120d1706100c08030613060303030b09070305092806091b12030503060907031d0a03 72
    0x400c1c0091203001041c0000c1f60a200c4003960051002c00d162150000c02003000c94001000c06d201060a5000724082d10001c4035002e11080300c41e80c0c0d4401090b100700c061324000c40103107402c114481c110f6840e840c0394007407030240d5030151314814001403400c0c0008003151004000109001c5e02c0718804ca940b43c01510742c1008816550341400c003140c80310350207405105003088654650145c60381c00308090640a0013014801a4071010a05404440c10410300542c402c900c43c541c0c50303010b4560f491010301d031004800344c0390500480302d1041a41c141a84103440c40c0c8038503400803560790b407903c0310400108000340425018040d03900d030000001c100340c1c06610000030050145c0f841c1c2c4807581d8200d0260708491040300c004029070410340f20b5140310f140d10784040b032011186100e490074680103522803000f10740c032100048601d032610003d03100300303540d0013030007400101144001103880f6220390f60000c0ca203002c054005400346c0500703400b00d0fa03014000d070400f0345010441c0380314045548981d00c141c0d0f0390740c5030440158 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 811505935 1250 811504685 811504697
    0x20406090e06071206051f02070308220e0606120406091a01030501200f1e36011d131505040e0705090121051204061b020a151101020409020a 62
    0x90030080085c080d0600300c6030020501400c50300c03404552544580c0e082c5561045000f1184c022001690a9015011604542408a08400b040e458541e40c0308425003140080303013501c0040240c03d540e52421a03958410b922071040103901c5a1401714090110440000c2c41101c45031860030400064202e401e04a90103980284807401c054441c2c4504007201e4109182040d07000c0201c0003d44030310b04010f00e40c07291030701c041009903005503c281700325402c440c44d00800c003000c0710000301e500910007030b294500d41c400c088606007101c400340001c1c2840f600035246a8042c042d0708030b814110b991781d806400c0803200340c0a00784001a0200007074900150140039052146280900c0341d0180d1200184050565101424405160b401e00075410100201c507900c10707400f9046240400c00003801481402d50501030081d200e03844a0a1075400741040d0324040f00f107203030025038a1089026079110004001110840c0d03516400119a1507801c1700c200f000144900c03c6980001350001d5034090701e90040801c4459071340e80e8 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 811507185 1250 811505935 811505957
    0xa2a06020d1811062b1505090f04020d02010504050d05060615070302060118060b040f030606270e01020c0109050703020f010503010312030c050912061e0601021504020406090e0607 79
    0x140c0c10324a000400a082804129008111410454001c110700c01499400c4085889050140414282441d1005082d00c0c1c13186028941070301b4105190b03000d01000c0307502c0356040c80c000c3d46595095900400191082412250031019a4022001c6030040c15010303002844568650802683ea5501966441e0094490707000d41c02c0f420100318107031812180c3c1740d0302a0855900e82500c0e0b11141066058054101e0340d91000003902d8441c1300000d0004150045400c500c04cc61400d00d407044410903403100c0401c200144190b084250841940c0241c01a461400500a40c440d000306d8028080d050047c7e503503620309500b000c10b0000000364242102c0c4203c9250050024400045605020a01c0002c02c0d02c1d008a000b05190390081c0c0120421080a152441c00c0469a80c00224a10002d403091207085e002001885900821842e400845d1464100340c00d8080c20704000017503450000b160603c021a10f0707100860704564980e0040b2000b420f9001040c0b0441c4440005180c40e40030988800000c602d501d000 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 811508435 1250 811507185 811507211
    0x60b0f0a0905100e070c02211c03151406390f0102090a1712070b010816140f0406081023070801180e0706030516080402060a2a06020d 59
    0xb400e171080d00c0641d55010000b1303183e401d100403545210000c100640b580524191504410007030004c0380302c9000d031080c28050824401504507020030600c105040c941b2102030124188040101102000540d1000e950f241e2a40301c42c012046803011022650302c100c4c0c810304002402c008030f02b00c05030700c920a4500714441e21614508034400d035521590041900102000580f07a056501c000342011501980e10205403040194501e83c451039085401000303034401405a0314040010244800769082c01c001c2050401c100c02140100000d0300e070f03105641040805c8000d0700c4035000240203102400071240c0d103e85031904003010300314403140b002248680300364250040204104103402490140c6492035241d08245800000e003003135451001d001911a40c1d507400da0742c0100700c0c000040c6101c1e076000070b09041c001c41800c04484446040801c1000c10f00c141300240c0d8426044500c900f200d820154203035080c40002085003075029844100b0030240c1805d400a21615800401c01c0020723686042020f5042185 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 811509685 1250 811508435 811508459
    0x20d0201060906300b070f080705210a020f04030c061412010902030612030307091809080f07020a030c03030e0a05042c07050409030504050907050313060b0f0a090510 73
    0x444c14202c0a61310310784502c424240310502a0809a1014000c504040740c5c45441090714203441c0301001400e0a41034280741507201242c2e5800c0300c22807820034a003202800248140550f9a0410390411403000040b85040e0007541c1100c0c0444203c245c2c0603200c66880c18060f400500c18030403900426141000340800801d124121000314031048166115a400c0c028040d0007500000c2443d038101e1074542e1110000d24040015510901199948240716810a00460550920320301c00a0b0700d14201022580041e5010f030503910403004c00c11149854078072500004410052541c005008500162008000d06030301045100403030348142d03a11840181c1c0c4009020840b1101c09482c40c0c0e46c0c4c02c07050710035501d02c85031008081015400007254101d41d1100c0014040f01d00c002c004602089002400700860704041c0c0b0500d5101c003680c01e01c182140381002c41c1107005c008140c402442c05907101201c14072551941c0109003a0007024243c0a0b00a40b2800d1f060010141039800c2c0c3d84c0c01144c1c407000100008151 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 811510791 1106 811509685 811509689
    0x30115080621012d0c0f02030a08150a06051b0c0f041a0405010f03152a0201020c01020a1214010812070c0902070503091f0e10030b030607020d0201060906 68
    0x440c131141207070105501c44080c05188a02065515000710554114485500704515540e60322400d11207044085c0791000c1d805601d203407000c181d1039840005802110710318041c1d400002c0d051040c6036a100003c4403020303030214000c903288039a0f0078290004216540d80c807486043e414210b50014090700d8003600b00c00c0b1859910350080062004580b900172411407074a1040089003e8580c2a038051a05000450403034001a00301d40c000034400d60481c1d03850700244c4021920358084020040c230004400703c8110505007026000500c140516103110b0485110320003d1108000c8442c040c07026400c450010b5481203c0342c480041e072400c1e41e0000305203030340c881ca002e55a143c0e80301d820050980c04030604400b180b60045801e4008640086064100300760031101000366401100080b07019004400685802d802032006000041da00020303404d01c8490036070000d01079541c03501e4101044036018 = true := by decide +kernel

theorem cover : BRFrame.Cov 811330935 811510791 := by
  have h0 := BRFrame.cov_init 811330935
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811330935 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 811330935 ≤ n) (h2 : n < 811510791) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
