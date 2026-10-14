-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3435
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:39:21.012638+00:00
-- url     : https://prove2.me/submissions/4e0a4aaf-d678-4510-9a5c-b214122f9684

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 617625899 ≤ n < 617805755 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 617627149 1250 617625899 617625959
    0x20c0306041718040204030c0f09060308030f06060d1e23010614040e0a02130e0411010f090305150108150103050307020609040209041802041a0303040e0c04230a 71
    0x14404400d40c440000e01c0c00c202100c4a5680071a130302c6000810066025040080c0140d042c070095000d20318040e4843c0d00e80619000c020000914003c09996100426004280d0b0b00c2d981d21000c03c46500c10115038020f110300e070000c1b800807000c0c1886e04d03c08401340e841c010012810f0320300c10980c099482da20307020100da01c010300421040d0300c20810140d000290030522420180d4500d00b1282501040e100b4408075074000c00c001507107941141c0c03e0310080115500050190030a40c845549030b40a41b51002d040000300c101080400b030140c0c1d0756000440d0700008403007850303400707180200010f0420300a4a100b801407165090020b1341c20b02e01941170700c1c0c2200c051498803209a00300038482e44401e1103143c00c141c091002885030355451140d9000e03e014150340d0294192103104100c01c5940e480000e019120f440040d01d42d090b18000b040d2420b40705140264000340d1907032100740c0780b00e000701c2d4807000e20b4403810851403010703010120421100b4401694611030041c1c82c0c0d040500d88014084151881c2a9505 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 617628399 1250 617627149 617627183
    0xc0207060c1103070f080706120b0906091f08011b080606030a200d020711010315090b0f04020a1821080d0603051212060913260409050106020c030604 66
    0x80416100c044020204c54409980b501810040c400c2940440040d4110704020411103400449803500d1100b0722804000342071000c0c3c0044e48509014082d14020074400000520000600d00d440c00c13a1942e89080114140d501c40145019200481200310550300440f500b00b001405519001e005807070040005003142c3d10520b8410080100c007080c02100342c0411042c4c20320540c2c4000a110010900402507a903001e141400246045038100c9141014600b0708400100c00751561071009841c003c4c280411280040ca000a15500040c41c20a500900c0041c58070481504404192403215100524410165840c191035070f000101c0801d64040610050100001440c81001410012480700300010040c0c0c80b40c4584d0301c2e02c060381d0600003000b6800181e000003085001d001c41e07448030049481402c0791428001052124a0701c4100030601d40c485280150035070f9240303203d17011000c202d0030815240c0e682e40c1d0459000e00b07802c0c41910058001d804c041c0390f0a00380031400301d129a03000b041c01d4030884014 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 617629649 1250 617628399 617628413
    0xb09031804050c220f06110105180d0309021825030e1c110a0b070e03070819051f0c030f051509062d040c0203040f060f05070b07030608010c0207060c 66
    0x4079915400009069202180702d2100d0824100501b600d9910828031130300c0c8294484c21140d004e041c4501d2600000201003654200081001101902c3c2c5004910402d0740c2c408a440c2c1084109001c0100b54150100301d841002140c0035218582070002c1003010201140b000d80440e0394907803042042c0c1c1c00034071400c1e441010805460b0740c41c00c2c00b03107030600c150509144107506045400a040321044580d03428071040650201070a10700d5441140a86500361601084681c0c62842c2030510000003020b040302400c0c04800d01450b6601990b08840d06104500b00000200a241418040010030324282c3c08400201c1944245ca1051442206034061034a1500800000040003130034035a02140c5400c02d14100a00c80070303c0d06441036164075900601161204001c04c0c1c5400218410465100b404104000b440940e031110071207040d401c2041f54005401d070f0071609803155000140c0702c0d00c500780520002ea903050384010100c503540d070005c03c4024000f007022a20b5400e540306d81c800140441144130046451 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 617630899 1250 617629649 617629687
    0x10f0503130c030506090a2001051c0b0306070203090907050f0304020d1509080301031202060910020f04050a08100510050a0608150d0308040506060409080301090f090b09031804050c 80
    0x700c011a10b4150b41c1e589452420104481500c000e400041e191002c10003407040c400c80981c602d0300c035444a00c0e075440c0001d00301d000b54950840504000e607444110f0280b20b80c480c40301410081c082d61514988060043e64076804401c80368010b01d900c0d0005114070344110140c46a5000582a49140d03842c0c6800300314004810398029110040c020403580c4c13800850348181d10100b031060041c0c1703480c2c1d0300d14180f0b0810451520080000c3d500981c080104015002c222807050001180006803140e0400c82084c6c0c80f400f454005d140c03c1f44007054003280a0b81700090005036608410b605000d1581c900c800c020703030b103001d9126035900642c04043c00e20556004074001a40070307007448500b01c03e508024001503414407c110083c1d0116a8090902051010138042180e006a00b61401d11410394180c2d9500c03040c0c40305101c0d003400d045d5110030f0f01c114100a034010420903038108000201d5401c0640195460743d0000c2542495521848544100e50400d805041c0c0306401c42c052050600b401c42c2c1c14110300c514 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 617632149 1250 617630899 617630903
    0x6040b09120304062a09090b09010b030609090a0803010e09012414041103040c08070e040302060a050405150c090f0a0f0905280204170f0a110d170304030e010f050313 73
    0x921020b50341c1140186501c2c0c10480c441940c503800b41b00d1400c820b40c4122801e0300821070186207080018006ca00315601281d40010301a94914016510001c10500304142180d004011000000c0006446800c900e0198081c0640c3d034003c1101c40c220701190a9820f8003159001c0c41807614000410540d24a101c2011000402800c0869801c44107104001e06030b000b21021036045044080501c0241d208120a2003e0510950780c942c03942842d850280d80d820700103044001c01d07516440001c00300b000601c40d884030044040008443c906041e032002940f500094007042c0100c0ca032030780303c1340c103458005032540454403050b200102d102e00b0100b50601806000348010b5850398411040c1890102018204408000108005842d2414001c000314045112121106180c2c8181000d030300c01a030100b21a08803650050b484c01c203069421003c00c00d08902010085c000040b81c02d49100c0b100002e400030740c492846555024041400b09006560460650415500040c02480010740d40c202454550550034 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 617633399 1250 617632149 617632181
    0x20f0d0c034208010204030b010b040b0d020a030e0a120f020c21031c050105010305060a080d0e011e1d01050406140f0f070f02090c1602040f0e070806040b0912030406 73
    0x1080c0103030810040a826800404545c0d40042c080040c440c41ca40c0039409005040280c0345894a0a504102107020f04007240c90195030010f01c81c0d9015000381c0c4401c49400c1100107030742d454502410700c0340c00480040034a401054061600f2483c07a032010407074210600d4010001711a0b01c44480b0943c0c10075034814440a11031004015184682c0380c40a030352b1000c802c20010104540d810034000606582020342581d0055407481021b2000600114900426074541d03d801d0a0b02c40711000120740a18020006210b80f0301e007403804441d0300703038080000150841030a5140607141054401140c141c40f031845103038006035210020001c010182da000b0940f90500503592810315141c0860740c0703243d510068084800c001c100c0b81e038104504084556590080024044078140b00b520183c015017180482c10081c403496550850b0002c1010076485070300c3c40030440088480c1c440c1c5403102e076035a86400b0345055461480f5203000905404000440c451100508400f643c1582ca5540e034000c0034005d03001d6496204 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 617634649 1250 617633399 617633501
    0x405310218130515070c0b1b0418110703020705011b170406020606030c01020c0d0f050703080319090c05131b09060e0a0302030a031809020f0d0c03 65
    0x9070403040365050240e070100030002410000381c41c101d4500042c1074070000300d1907542010050a00e410061550403141c00c05102c180c60360318085003030701c480c2d0f042840b40b034480c40c0070038040350f001da0b6800c0580c010300140034108141480b2041c1d800300341c0920200100140c4c442c610520241d44202e02100c074841200c0030800082c0c6542e07607281900c245843c0c01c01413100c008901007009035410022160007041c01d078050501c01038031310b000075110040c224413103005200c8a001c5e0010088641807018070142c00c03a05940e811901d07454040d40c41e40c015108660780b51201c1c03c107500750030030a00c151030710241d000501c2d0f4211440e05c0144510101110810b02d10315582e101c1c04c41036510b40310b03040700040307055544500205040c0000500b40e0400c8024807030095101420910060320001000c0323052079010300b0005840600300b20800001215070b00054095400480c00760011486030000d0805003a0100040c49030111190040b01201e040003804080914a94402d41481c40c8802c1c054484c2c0f0349207290600300c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 617635899 1250 617634649 617634679
    0x31110020a12020615010513060e01120e0303040501050601090f21080a0c0308010602030406090e0c0f0403080306090f06010206190e12030103020a0b030c190207030b0106050904053102 81
    0x341e81c10320b00310700584c00c0300b030030882c105005a440c0360384410242001c0b400d0409000303403c000705100d80500818080f00b49a403414a030b0040c01a070070321815150007404641c407880322040d2650001c1c0c3d4126015030901e000310b181d660182444205545a10030046a241c0c030340500d00104174424084030091103c07890303c4d04003041e11800140841c8900c0e40b501e840c1440301e880d00030a50352050f40300034210740041c0f20034801d855004445408032602c9000c2140ca51b00c8000c003212036446101c0d802c0203020800140081005044005144a4041200e0012981d0b0b0346405810342d04a00b26103650050304003100189284a80400490308520526000501c004420f48034902c0c01e0515a1190a40e42c0084010401c6240c11100000074203240a101411400d000151404501890010100d0b1400c0301c1a81307410306200b04403001c010b60700a021102e207960354980c0648140e000145290241e0300b05000641c000104c9000d180c0c1000e8441510000c100303640d500080c0c9400c09100c00c9034000d21084203000 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 617637149 1250 617635899 617635913
    0x12020601060c0f060605120c01080703020c0c0f211f1b05070c1503060801110a02060105090c070602030a02040305011416051804020403060b0102060f0618071b060e0708030301031110020a 82
    0x1280d240d081f0b00821048a0110015001c010000c064401f0180104101d24000c080452203105d100301c25a51050a05001d00004100c810401e1030340c43c1e800340321249410104000521100140c206080d501081e041c5209a541a03c541c8042c0002c11041c1103040d100f00340c850700c0180341d40390041c5400038a407620ba11a1020403e00380600c0301c0001d40b5404c00303000b1b0364070a1044010b00303400c002e0180d26207040614040d40b100d105100306481440c3c00d41c0085c5050041d00300325440380380c0c401d0741159030740b610100100c02504140825a0990318040b400344032104500390490090400c000c40c8200380c6000072040740c150303102c0381c008200c0400c0c01c0c02007030458860380058400781d0310481001c1902e0a04000081c030701480242a0b500b103118880c1481074584808010a0300d208406101c03a47c590341e8039109070f03074020b480001a441e18514602c1d107821300c603041e4044640601c0110688804681d503000445c1da0f0300080c0000b401c0f10744040c028a41c689024444003130661481d005035a40b0f41c0d8191500d003 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 617638399 1250 617637149 617637169
    0x60c031e1803051606080f0601051608280c0b06040203060d020a03050a0201030e0318100947090d020d02191a180f030c120a12020601060c0f060605 65
    0x83d810783c0a0495540030186100d0800c1c00340c0098070700108a454422442015200040c01c402c3c107004000881521201074424440120b0390408001030743c42060080c01e071040c061001010ba103809040e104081b80c42d221b10485c1040d9030700f01c2029191512840d04000c02540040c01701a40306180101200040e03e0b902381c04002980150080d24407246c04d400090240c0b91050640090354100304a100ea80506000c1c40c481c075078005641301000c4070551001642e10017010380018042120300600381103010040384004c00c0b041c0750352000001c0450000d480007075086400085812080b0300703102107501030900301080014107000900e2110011400e4000c03031504040d40c20428104c2010721014024400b20700004e412120442c0b004924003040d000c039100000065480e200e2284940c861442940e03501048510580c0200401441e185000f0304c0e0025540c00154500321a0344001040e030400c014004a104d07412541c49032a174031150081c6585404484030100822140c40781c0c2c4410204031915260b41714 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 617639649 1250 617638399 617638403
    0x60a052517060609090a05060621041109090c090c070c0e01060f0504050d020105090a03021c020301051e18070b0f0a0206090105010b19020102090301050c040f060c031e1803 76
    0x11241c0800e54140c058500028401d074028681002054003d440b88002241e000d60078001c00501c42d150840014014400c040c8444500d40000d89101040509045464041d1b445090046998094403041c040326410480d0040d183d500071000341c05031803d101d400d141e800b01c58010301500e400340c030b03540b6040c0c0ca158035088600c007140c603040140034041c1c01c108440c90724952030034406d003841d25001c000f0b1245101c80304000c2c101301d80070071909000c0c2c8074a101e45009e15401010960f400c00040e0350240080c1032198168800c3d800c00f000320780c1804599103501c8070300e16407030800c03010b40d0b0b101d9420000781d89405441140358810310308000b48030000c0a02400300000c41154541c1d4030b03580000028034100010f01801416403606004200300d05140040300c0e5550b003591000200301030040710507802070040038841a055400c20781000b004c4050310009100b540d0001040b078400946414048070401c040e91070003000300340000700914600300c0c80860b0f0501d5003043c1c40c0c0f00b01204c1a000700455040025802 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 617640899 1250 617639649 617639657
    0xa110d02010608060f04080a030c1205151c08090603040c031410140907060e040b1801150c03080601030218060d0903020f0a111201140c07020a1502060a0525 69
    0x107000c039900134000741e504006401300c90505414030343c4032070318075100d0a4681d8050540c0c4084404605019500b0a450700f0401a400c2140e8900000728840b100c11075206544038031016850300c00c0f42d07480300080c10100c80d003000006041201d4141400465440075106540396504507100000060000b0030300c206985000c0060131111070328a0444080d903810108031070b190907001003041441c100000394002110280c1c5804622040d5031001300f0b00420b44080d685802440c002e4a01c2e03400035401190718100c9103620040e1003034101044044801c6c0360001c400400103141180820700541c460340107401c091800c2e0360804d01580c05100003503119800641070140494403040078606141e01808198030384c200705c2015010003055035075194014404146428031805004c00b9141281070254421020a40f0348403407219241480313180110541c01420040717105100040b40800e08050420b2480c80b0300c0c4640c0c00629844c1c44100c0a84040c00e0020043e80c18928120284050003403200342d031501009640e16 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 617642149 1250 617640899 617640911
    0x91503120e210d050421080d1410060201060501051c0f06060309020f04060b0418020c01090302070f0605070218070c020919050c07050303040b07020102040f0320120706050a110d0201 80
    0x1da0300c1c3c100703c040150f0380140304041c40100a21132681a100450fa034100071010400c901500d0000018015003402c6402e0706d14205543c01341800341d200c4a40100c3c40c1c41d40004045030b54240482c00e9507814020240000c00510581d02440400d01e880104000212400326004080d800780c9070031100b05034408800241ca440c502c5042d0704041e0034100300e0304420385061214908007615900c00d4800e511400c001d60201c114140030751225541038031010b0603040024890141a030034020f554607000d0141c2007090f84a0301c00010003e00520850301c9141d409815800700c0aa001c00c0a104546c0c0201900207104e000b0b080100143d4402d001c83d0300c94850f28501c0c00d805003030465220220745009000612015041103a8808201c2c00070540764402d0344920020000d50704d6031400c134068025a07200032030a030241c030070200400560505040451082c8405502c41c8114202000900d601c01854103542c0d4005e020248001031040380181a0304100d81848070380003600030310b0709242000d841312140051f5500c0b5 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 617643399 1250 617642149 617642209
    0xb0316080c28030b0307030302120c010e1b18101208090a0b13050301060e150a0e101701052e0b12090c19140109031218091503120e 58
    0x1c46001400c900170b800405035103045070740280d81c0c2c82d1800c100206413500454860200c5a00b50080e0803000658000d81d0b08001000341410340341d9145540c0d881c440d84141002c21031008031280c1c018410318032000c844200d14034064040d00c01180205007a1101c0200300001e102a44451031004001c1140701c680c3d80c1d6500320b081c60b80c080202103130043e905c20703414400200b0240d4188400da50300300c00c4074444040700d14003480000300b214249501c10402c2c4d00c01d00c0300b000300101d610101441220000c54041d103000407442019422140c0441c0c04003d0700c24189180d04900480002c21030030b040b10b18080b00329445c0c1340d2130082402c0d044521564065a103c40070000d6018040c00300c00d4801c0815604c0b004000340b412800d10a02c2c0c101d00404c0000103109003043c0e0240c0c4943c6184000b07540044207055000c446e00750041a03003502d8040c034814800c403210300081c4070701144100c0005c64803500e83c2020140c01c40d40c8401e1303c6207601e8058400c201e0385000d8409550f41300c0e01c11028800c500a84d0003880b185030 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 617644649 1250 617643399 617643401
    0xf0806060f041e0f08010603030509150c0708100f0528060504090c0911030c0403080703090312050711010206090a0605100b162f120f0102030a060f0b0316080c2803 72
    0x20350002c010f1707a41406d400b040000e4002d0250f50380030600700c1e0921300d4003049005e00e01c00740c024402183c0151240000005602602094190880f140820280090b141c201200e00c10754001343c4517907021600d604032405142021003a03484064041441c041011592000000d01756030700d040e400d07142e401000310100301007003081c401c441a25000e04541400c604d090f00300e03410320740210320002c1c0c58000001028400c051050b00c048000e15400010003131134000080c1c00034000e801802049a011020300c40860b030640c000240b0910510b03200700280f072100300d190b46030310180c1405040407151500b11f01003c240844c01e5800782002400009021000d05564280083c191140c0c400b8880121400c1003944038a02e050b81244012070b000b41c0f0003000280041d032910b4030300101c0540c803000651021040c450702c103074039030000300c101c5009040705d801c00b81d101d01d0380081c64401541c0c10164080d6500c0c5900706a40100700096000c0011104603003014602d544851076040e101d80d4070b180c1d410b005180c400803d609 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 617645899 1250 617644649 617644679
    0x40b120111091206060f0d05031201120b1317161211060c03060618030a02090c0a030c020102090d120c0b010311011101021819050301060e0f070f0806060f041e 70
    0x4500041031a81422404224894841b501990240da244201c50007801402c00445607540514900d210309507a640500a0404044aa04a0f16600074102048100c101e510320100600c0d01f114020170315003040f00100005030300c0f00040c204800d00c000c06820124980e65041da220515a4450b002010030458040e4100b10300102070407a500814824484203443e000181d88070440c11885a1403d2240b41d40040e240403003540000b54803c5001c00ac001588000390090120702a00d034a051102601c3c0d4142070b0300340d0207214203094025404600200109600498110550f0081d0800312481302c181d8a8944ea401e400360002e4641c150360450b00c4029580c8804000c1500009400071410b00c00e80200103441d0842d05403595218550343c03603101070141056404003000380301c0203000704003031951005d142c107040a0854455403804014400101d0540c0038005010603e1450b07910001555038020412203180c0000103c00d503110000c0c4030108400384000300c0120001c8521152600c0203181c40411452801 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 617647149 1250 617645899 617645929
    0x30a0608031c05060a06020706080a0e03070c06030507020703170304030e060c0f070e01030201120f2d0f110f03040f0c09091b0b04140d02040212070801080102090f040b12011109 78
    0x10080304204482d804248103090b40c0442c2b600030510340315200c0100291441c5141d40300a40000102c0d882003114142d02503045030300702c2d10107002175916400305a856004a201c040c1c1440905014890342c5030842000b0b40e8818820b060580c0d94802c824013140c02d41d00042c141102c15440000003501d655010020321000300814203803842030b50304503400200712100c290240c0e0100341d22460341d0450107003140c001c20400030150350020b10300042414580e00b04070f05100450405442c0c1102506240f24a00030005194100040d85141011014000078076901c02401920700504000b04c18000501c494a03100c02440c65480c0414000301600f8001c841c1d00907024260180403c1701010404919084103803030481c1c0c00000d90450b03000030707400840c100001941b0025482407000860030000c000c0010100e000c0c0400f035a070350009a0300c40b01498200d1040c610000c0d401043c0100c181c1c0145066000b41700d2140002c1c0000ac0b50017280c0c4241c40c25522000070090100c0c0d00032500c1c111504000c800c402a0003 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 617648399 1250 617647149 617647159
    0x30f11030a02061804090209090a110d170c0109080d09052401150512041b091806050613051914011a03090f030a0f0f020f060606030a0608031c0506 65
    0x118003680014038622a40d58a0041360780e071910513a01c1580c1e694040c01100fa0003400c0c50b0620f00d480e0300320603100c051a04040f5510624800c1000a42c102482c0105030158803881b842481c1e10b1243c1c08600541045510010343c1d920384047c6400103c1e607001600c0310124104d00401c0d50b043d180740c4181401d04405590314000300007050160b80401421a0f681119100172303201c0c00450101204480344d1041c24441d070051041d500a0008004010701400c0d0440c100c3e28403040119110110481030300e10900c40303901e052084030164000f00f10103a10a50300190000c01006a80c0d40500c580000d50b0021251a42c180342d10309a0440ca60040c3c1c001d0341445103002901244540c100a8181040010800f4281045c0800700002d0031901c3c0c2000200501c0c244001265211440d070003009040ca00494a04800690040d5440f0600303800002c0c020b4281400d07802a1030283d40c1d810900110b43c000510180c0415103686000810000600060161121ba00320345060440c0900c010020744102074000c034096 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 617649649 1250 617648399 617648413
    0x7091802091f050f060c0a050714010c03020d030f02160302010f060b070b0103060504030e0622120803161e020c18010b030a020d020d05070c060c0503070e0d06090b01030f1103 77
    0xc01c040905030b034207940084607450002c02000303000c600b550240103003000140c41200249005d101001800008035080c4500440303600f00a40c0044400d280c920320b0040140c2e02000400c0000b034042d4111001c3c1d502c0d01d050060030302400311101d1b07010064a48041d000360b59151307200b03c801c110358094a005052000300d0705280c0100c44c0e44041c8007080500c40584095511004a001c1600c0b40d40792100d440340007000151108201c5590a003004102201101400c0008600081e00c0c0c4040181c03607641c071f1300000c0b050705541c1c9102c1c52601c419400150801040503540c241c94070114604e60041c084e030502e034000d003840b1000c50184a05a401c6003a400341d800211001040006801c904aa6200c000c0040c0581c0302c15040c0b00b0700c0040d006021084000c0c0342010b041200e0b90758000c400c0100207000310000e20402000e0002a82c840c8000c5d241a4006440385640c00c80390304090401c120294415800011241c4250712403d03030014080e0030440f402814103450800740310380c0106854920380203d000d0104 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 617650899 1250 617649649 617649691
    0x1203150e060105040603020f0904090c0e130c03060c02070b0414031e0607050a1202040608040b10030309060f111c0f0f0504060809240a0e01200c0709180209 69
    0x50f41c0100c0c0b01780d008141e00001e204100810100c1582c2502170064014004c1130054940600c3c201c1440c0038440302c80c0c901030001032810181198071008103401c8500c3e0180d060840e20340f50068091100180c0540c850b021000800c0c19413580200010101501c040440c06482030030903052a03440202990003440742c1d000034a8400d400b2412a42001140c104680e8502c3c4050041c1c0702c00b41c24046182c0420700c0807900151450700035031100c9c403551240d0031440090369070380d107803940720403aa0102400048002405004690040c0000b06400d406410108a424040c2e182685001d51004072406030030042d00c1c0403200b2075003180383d8a00c56841401d01c4100c0c451019401042c3c1c2c0928843c1608000300d1801155010000344480c402c1049091483d003a4540c20110f201030301c1070207544c2070003020b141294280c0c403801c040c4601954081c060311900010b103c2803a1540781b03a04602c1c4d03081410f01036410005041e08039407181d075441c0440841d40c42c10034006401040901d400003011404955004207240b08 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 617652149 1250 617650899 617650907
    0x31810110615331605240708090c0f03011104120210210c030e03120709050402040303080105040506032b0206010e0c1902010b0a09150603020405030a0b060d1203150e0601 75
    0x95440f14035150962580c1c10030b000c030794004001c190081d00c98000c010301c07025803041c01d0441d511000052a10007100c0d0710740050464000c4012248258180c0044c40c8442040c03500b01c00e059403000c8024000b2403650501026200994840e0b8440034800080450600c1181086540303e01944e019090042e0007411110091a00d9503019500700075169541e00349010890103940107000460110301200c0e11400403481e8200344100a0710709030045041441c0001c1c17546028001c50b015694140e4811080382d00e0a1309120241001401c29507041c00741c18105858940b13104005400f13086000040d19065a0300d103c041e0130300d40180c0000c0720b035000400402004500e0b441c1180e4900b03050100c402d1000107015012401485450724182d4458a800b40c001403018094101801d0413103000000320729280d07505000e9080707102c1c900c9140c5c0c054001c1524040031403000800140c0c0242e003d0030001c0d801c89a41e4075410402458410400801c0d0f4440f142e105003035504618402401448404025500700b46001034 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 617653399 1250 617652149 617652229
    0xa0b040e150112090f0f03030c03110a02100203100e0f07080a09020f0d0303091509020301140106020d0c241e060806010b1806040909020909031810110615 68
    0x1e8813a12203981c1c6040084a1042c15049500034116020128051500070041c0554040071030029060801e040390400380300089600c0350045800401c004000305444901940008042d00c0704044841000605682a0320b4003521a81c81c00000c404585010003001c0c2110b40050452910107191520726401606d403049080a0001c084404001d0b120f410310f0118040c4c05180c01c01007540c000e0b041200130306e103001e412843c1d400d48224024800024858100358415000744244401170b0b1112080285103802040441100760190301150803141b40a5020840c0081920aa900d410344d1901030492544141d040e1103007950080c0c20911406103401000d40d0b50f041e06000da40c2d0050000500c1e5035403c9038004508040307100103410700e034071a542ca0401c80c004000300c43c0140c1c0100c140274005020581d0100c1111725030000e448081d190000c40d4401c2c07155031440c01d07140005001e50302e0f160818a10301007221502c20300011326007046143c1d80b64144114100140400007802080039030b0700208000a0b0720030 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 617654649 1250 617653399 617653427
    0x7030216050a0b090f13050115020a26040e040c031406060a03140102130806010602071d130f061a040f180b06011809060645050a0b040e1501 62
    0x240c0d03140c150040000c5c0340f180c0100129a03020001c5424155100107540146040711403884440180c9041068240e03104c103000000200841c0c0c440c2920820210403803803030a14000c0182c0c2107401c1c16200d900c0c41d11203480a6809a0340416000c03030801c01c00002c0d2800141010200c0068001360401b100403820000040c080103095510035042f034505100f003541070fa52420010034900b6400c503075a410a03911901c0c01c1c000c2400600503c24081256500e03115003510111000c03030300c01c3e140e503a000005d50200002c26812501307903887d1100880410564018400712800200c52891815881001c200c1180e104204c503204040c240b0403250081c10030100402089900b120342c265031070342c4850040340c0c1c1e10054410b40c2e942c424042c0c40800e0080c0954801c2069403600e072549608030649500511000011440000d49006040c803880b21968400b000720b00d041d0400103030802940c2d15000010752001a5400c00da140c0b140105080120000e08982d540e000305420188802c40c4540380c00003461780c03529030741da = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 617655899 1250 617654649 617654669
    0xb07081603210e01141b0307020a1202030903010c0f3608150702060408030406020d0e01020a23030f1f08030a0e010206060a05060414060702060d0207030216050a 71
    0x9240c061501800400c89800c41d540b40c6000c1412049050b03900034016001040300c1586007501c03080c1c1d180f03402e0800c240036030616010302c03400420b01e0350f40403020390000b480f600841c040c01079568000748280400e0a0030700000d4007d0354494418074281130840b26141400400c02444407414840c0c550403101d02541e0603600b13901c0054042014110900600203080750100400c440030002402003c0071410451813203d01d00100300503110300780202c0c0d0300c920558002d040800104003040c00110240d00030880710015140c040341c091122150340d800ca82204c410480494035000c00d5850101094005000d0400c0c6905102c1c29810240b07111036031240c0081001a0260103c2e0640100307a03030302c080c00b400030714001045035070340c4049a00041403134600e64082405881500c0111b40f40d403400001c00d0707040c2d0310060700c1207040629028041c0088080c8542c1c194100c4001c014120150300d464004103500c41041c0400b507130310700b035900d07000b1b21300b12302e9855421325950210b40500540d92041c44010444401c0d030700b = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 617657149 1250 617655899 617655937
    0xb190c091e03140102040617060f060705010f050f0612010e03031605041e210f030f110f07030506070801060e090a0f0914120a08160e1203130b0708 65
    0x604001c0d54140303600003401d111004400d421512005400a1082d10030968074489007100862495401e600281c6003541c0c0400b40702c1c41c84003103041000c050002c8030700a00010a0f0458150340c42021100c0a5600300081d040700710030850789042c80001c14005072081350080001486042d802a22400060000800c1c00c2000e0b0160782034038451400d40300a00212808045d21a40c480c6c104460b44a80e440307016410582c99450240018408042d007602c03a4000e0b1259584801e1558102c030040152145c2c50140708080c0040040098104080c000b19891100100706050440c2411807a204004000f8407c0080000060010039030010f01a030102500780c980040e15180d013503002000d4191216051005480c124299042c44903480d41c820070460502d040e500c4900d40588001c265101d41038441011403442030104041c04a003004140c803000403407400f44007050091000035211000140200e01c00d500102c1e085000352011101d4500408203030b03550615240890782c07820307280d024814100f807510316905 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 617658399 1250 617657149 617657189
    0x6090402060705071e06030b01080406090204060b0c0c0a14011b11100e09150105040b07020609060c1b0a06140d09080d0c02070e0f160201020c0a0b190c09 68
    0x2900ba1070003075601905980a20781c0b83d000d0038043e20400200074880d07820b9500001884c90183c401d402c0800c030180d480c040d0759030700d0b40c50f4800900404041242c03c180d4600d0300280310a01c4030013070000d0700c101102801e90041108100150240290071480c1e4100c83d89500d418183c0c0c04c0b800c084818191000c0038031f5042c056041807100008083c62141d008401070850f8503444e5400035100854800469068032181c484111032424801c0301c40200307020941c10001404501e5440000e010513070320080c4031300e10307180030000850030036041400340d94440c0e40301404111300e002e4100b102d0120388a0641d85e46013440c0c540303d4010860011048410311300a000908490040b007150001d8007125008920580e55800c19042d810081445241100041c0941c040100c0c400205100080c002c0d0081070b008090703070f1500c890412242c1c150804050940d9401c02c0a51420350081c44415045401000d04a13124981020b0004411070059a031203410b070300d01400f03c00d407160032202c0382003500d1400c100664144aa4 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 617659649 1250 617658399 617658409
    0xe01050319050c030607171503030301090f02190503091203070210090f0f08041401020303151512010e0604060e0601091406070203060108031b0a050d0c020a0510020c040506010e0906090402 83
    0x81c4981500400d410400d0720b5030030020790b01078a055034141f002180d65842d50401c600401c0c1c0c0104d80e06800810040105902d40d0b04601c800206181c001890001c150030450030343c3d1140710300e14020690120400c10070718000d102203c4010310401c1414618542100020349482001102c145181e660f50b44800600c1072403543c13001c1e80e035482110010621441c0c1414070f250340080c0711300500d00d56284c000141075440403003900d0088184091100078221a1030410030507504800c0c4903100031209000040801c3e503260b030031034000c00c490743d8610340c207051800c107100584170960414148002c212040c08120b9031721210400c219080021007141025002002500511505402a40c14030603180042142c610100c014440001c150b600e606142180c0100247c83e11a119009850780d048180e604410501481911505501c02070080c0b0b40340d911074000403154401c410825005a102c0c8085118504181c0f081c02c3e00320409091640d480c016038070010f0005140200350501401840c0041011502d80b = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 617660899 1250 617659649 617659663
    0xf02040302100c02040e0f03120c1314040f0507170405011b080108190c1503020f07060b090708060d02120c031e0c0a030c090b01180605040f0e0105031905 68
    0x1008008105942414800801c0c3c403032a00003d0380304520b440d8250a20205c0000d1040c00008003001950901042406040442c24010042420b403601045212311810860700848094800c0340196040103603158144401c4620040292000c1072603d02441406a0058030070b5002384904011511244d0b02c2e8580b8501500c1c4001100603c00f500d90200c0d800d5a8000c1046416207484d42c1c100c0780c002400350250900780401940240020541810601c81850301c0e040030152030a2034207025191076042c0701f5000d010ba20070b890a449855407440401c40c0c51404581440d007094103480c1110302410048000f031889954007000910511003900040b070000710038815040d2070b02e00181a10f0a00c511480326050216450000700200d000b01150441103140400481e03041e250400717802c501140c03c010810700144400300960b4184002d0b045103070003900d0f11000c3d000181c5160790351070380c41e245805550810b010154100c0804110b141e80103201c40d8500003110039130940c09004107056802c070307030400d02c0c01c0200b = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 617662149 1250 617660899 617660903
    0x1140102070305100212092b09210501050601140d18020d05160602030307080703050606090a060e0114071101080403050f03040b0601080f0403021c0302210105011710090f020403 78
    0xd0008013000648150703010344443d18410412444c583d580c200c0c031a4541d152020480e2825070741100c070449000841d00118101c545600f41407c0761a1602611042400e201c10011003245040c0010410400280a8550031200038249507110380d0344020440824080c0e4000307112038941d569100d07102140c0c0c00c002c41d91295005840d800c00791526041c215118850105900d0503294060780002d600e0784004107c9204581c507680e5032205032100042280640b001034103e44e8021410704c00324116540b2150803200034412629008114101200054800d0661551114048070103100d04d002003441e0301e42680070b44e84240b8003070341e10340c2c1c50f4035040d5051b0203408215500c224000c0104000c0200d94140940246000d80b40c481055a078880c0c0c00b400c0344000c41740200140c014501e1a805501d0791000c41c04900d445003009402c05011040002001c42000042e105a0207124010090780d40c000b1264400102c0040c4101130783c0ca00a01079042c0f880d642e105252a040d62078040c034101140c03130350689000d0b503 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 617663399 1250 617662149 617662153
    0x3005031009061e120804050d110301020c06061c0f08090415030f0c0b041805090f01020c06040b1e13020105041703030402011e0c03030b0d060e0d020105010806070801140102070305 79
    0x1600c0351407852002d140488079030410b11251102080400a44d810001e904c0e42c054a07a529090408082c8030742c820010a080b60740b8148180e28080587c3c0c207001618a0b03542100052800e450000b00708101211010b6101144407524000600801c280b98030f41511290804101035407600d43c1c0010034000c09910445c1e4a201140f41300100400c81841100312411b4003a000084141f034882c0401003091069100d4101ea0880003400b00b815101c00742c000030740c405a1401070b1a01d8041c030a004a0030b9074019001d26000c0d4203c1c10404c0100041c0c40c1c005500100131089000310007110410301940064040c00309910f480d52441c004085a101d001180e000c0c100441c1d100c0c801c5120701da0a184c2d41e03001914100c0c00319001180c281941018010388107484525941d8242c00066562002d500400e0641c49154020386035810b1040814010301880c0000569030004040060510100a084442c10b0f00102481d400100c140100541e002c1092415201c1e10200a1396078200400182d1a090807544005d0041c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 617664649 1250 617663399 617663411
    0x14160b040c030302060c0f0a0e0a0302060c0a0501050a09050c12030c0109140f01140613060308030f04051e1c12110c2808130b070503073005031009 65
    0x124800007507100b10ba10a400321151074a800c1030191490056402c0002c0c01c07081401341845e10348c400c50f646101d0183c0a40003803203240d01c036000f04103954014181d140c0307207900820ba02c4003001024894154441001d81c000c20601d40c0a9641c2030b03c0e0101c2000b901d116190324030540c3c3c1410804e00440b0b01e20058103008000380300072440c00d480075207071055420000d0301842d8840040000706015a1940034012250000075036034182c2006440c404841d100030300d040d5115030210000d00c141c402940103600d512417524091900d072a2283c0b50510360f484440c0740801c804d456588420000450450055501c01d241c0c0f800002c2c00c90844003202648907072060b45003480c00c000300380755181009007044482403069030300d080d9240140407001081d91100201d418012050035001c502c02a000e08020a941c5502c5410f1569801e2108081d80012005903215040080d082e02003050b80690314052a03012035034801140c0c6000e44075003c03020000c8080060000000010f8103001c00312080d000940320304d50b010414 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 617665899 1250 617664649 617664653
    0x112020109080d020604061b0906141606090c0605040e01030b060d060c09031b06080109050c0c060a06091805100504060b1e030706020c0d030509180a0f05150114160b04 74
    0x760302003c0c6c2c2c040d80d20614040c07803107008501c680b0740012600c080c0e86403000c1940c54400100e440003a81180c40510080522003001c00f0b0001d03044449400c2d01a50020460a080c0d05102440c004954045014000108800c218107500c481c51181126085904401c455940c80701041720000c1c02c2c01d0085c0002e01e0a10800009900032800000b80e038003a80418050302c4911a6404280c40c060040d9800b140550004000c62004c64020a600c100303100c011754140245040228030341501514080c101d07948907803081c00901035503c601001c8503000d01c003280c00e1034950f880303030350311344140307410541c01c1c140c036000010140000380c0c01840c104107001c0c01d11550301d40030b802503260f2a186179070068030134000d51000045032840003401c1503811800801c407070740118071944d040d19954014106a5000b240d00c1d01961805e8540c0e200c40c41c03068441103000b265066100b610081240c130000c0c05407040d6144034810f40300c40d0342d1240d10346044d01a082d440ca56a1664140801403004070202e00a107614811010442 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 617667149 1250 617665899 617665903
    0x240f0318012904110c1c030b010c060b0a050301090c1502010603020901150c0213200c0c060a03060e01120201022103010b070c0e07051b0633030609010b010e04020906030112020109080d02 82
    0x78680e04a1b1400314400c2441c664118180c031901c070f0010380020079440410300801c3e070551000d0300d0403000401c4991000d51700ca001c20300303403012410241c2d002150500c040004012407010071070b5100c1a0b10082000a0566000804144060040006032032640c1d0382c0000c024018102d50000c04c0c2c00402d001d03000c00002013444050318080f800d00307070103011380060045840194829581501040405807205003504814030440382c0100b214602015110b020001d076055501c1c404602070f058441520120100c1400068540b140300c50f40000d1820072003030a2100d40594400340c9064031410740d100c580d21905070030552080c0074039421460040310b0b0042030010a5410000418081650b8070000340d42880c80109191503a1084802344c400707146040381e071900d281c858000c901e40b212040b0303040c000d002e0004000c01c2c44e20300c3c00c40c6d8032000d580d513481a00020350380024040000c02d00440302940341002150124009010610440d10f003c00030107100b0f4110ba02a0001d10003405400089074411846188025 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 617668399 1250 617667149 617667163
    0xf090a032a0605060a06110c0f1c2d2003010914010903030e060403020a0602091305040c0812040b070809030715090302090a06060509240f0318012904110c 68
    0x148100c55400c0c001038402d005021f070300943c81e4500042e01d4500c0f20f01d801e000b00d201a980342a5440a0382c2112421007014890071520701d00c2c09201c03070455003d440751503071200c03101180c1ca11445608100c0408005003e02c007100541d003510200d80d6040c50b40310008a0b015109135003008182c074000e440c003824813010550126901c039021ba9002e00500201d0f05000e41ca90788242c90280050b0882c81200c0c021402d40d40090090403406000550300006001c40c60044a0b4217603402c44602d080d000007013280020400c20010f83c0855032902c40d117081e01d41784290202d8801c0c01402050b450012800d5101a582072082800500e03011351410050700300326800411944480c00100c0c8103002c0341001c03525914281c401d08051712210b0311030500d007101250801c078281002c07103040015208002d80c04401c00070088007a0145d178122000841c1c0307a04241047c2d84005c800d020302402160701d000101d01080384020880d03404484c003040805041201000400d028104404007650031010001b14105035101c00a0f0300703 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 617669649 1250 617668399 617668411
    0x1302040c1b21030204030203060403030b1f0f020c01030e0d08131a01180603020904030507050705060414130e120c070803160b0f070806060a09051011060f090a032a0605 74
    0x20b00c80e9000c00c01982207006500000e50950b000d4000180005d00983c0400300440008040003003050b06c1d40108072824807403120540019a642d054256029010420311110fa002400c00b48402da0259500741e6580c840c00d0030101c104200403000c58143c2d51103400307001056070030421881903202210384600750078200713100f000d001c1d2144034a0700503269641e111781c1007565402040380d181c50711648c500700c4003034101c800152100d0180c0c140c0040c20769140001030004001e00018022459400000c00444030141c5020b001c00905107000c1195104020840e03001c040749484c00603440c0e42000d200740380741a045e0707080817146220000d180011202d0340d91074900000d00c29010444541c3d110076045c0c0792401c0c1910804045401c00c5e000c1001c0f850903c01030241d005092420f00c0009603240700082031481c22281030b0340810480541030309086014403000e07500044038100d6401e0760901c6246182c0c1c400c1003043c040c08001d02111026007480494a00300c00d0442d402d02103015404135411700400a14041c1c40c4 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 617670899 1250 617669649 617669693
    0xe1c0b07090e010b04060507051c030501090f020702031e1507080f0c09010822020312070605240607030309080310140a141903020a08030d06050105031302040c1b 71
    0x1c00100ca10140301814140c401c4a01c465050520740203003030f80c0640141c50115a9070003405584114170b05241d000a402c00c3c001d580200315545010200e20455005107001c0c43c810780100305070005601c001441540c0a03840060506800f559100418105222504000381201c4030005000d4001e03806480d090260703110035484060b80d11203c1c1a04864400c4c003240314045980d42002450900c007000b2203010b841d501002402004030140d0000e400e183d01581c89109000d130124408040c02618031520740d0002c000c0c103003003004c152440003c0d004510f0303c2c4880c0740719010014411080510a0f0040702403141d0254948c0d03200e04005c0e4611045500d54000d8500c1d0311101c601e001c0e92850200002412030700c541001c920a44100030a001001036031042806d00424200c40010041e10758a40d01e4004041d040051074403000c0b0407040305c042c0c5001342d04c980d040103024004c1c40306a039400d0103241c10f8158100e40020742d201c0c800320709031109a007800b145c0302c0c1c0c0c9080050240900446030f840e202c1c14208855 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 617672149 1250 617670899 617670917
    0x28032102100b030c0f010908010f05100503070807091a040906020702040e01060b0f130b0a21022503200709110301030321020403060f02090906010c120e1c0b07 70
    0x294007411200450303400390341940814490521414161700e6004810010b1405041c4692540000f83c00d4480d11814110300c566501c0030410b82c90a10311080c40500b404401a02a451a10300440e0f0368098500842c0500c6607113880c40c5880941c3c000a48850040c0030700280840703906818810300a4008441c10303805907040c10203a030424903061144400f80d40c44c0c1581e103800c02040c6144088039030406041d040014800b020081029000300380a400d41509666481e01c940c1d0f1005d03400820003c0005095071103078014803800000202c0c02e40307148084e4440920f1029400e2260804840d180240520110740001e0000d860010003004151030f020b803944540c0902144003208500229171000340720250008003900d60440c48114140e003940701c05400350a025003419103e440c0c1401300c80d004ca040003039041e4002156541c5041c45032400f903021009080030b000101d22500c0c0d03072158580d02c003608070400c40020704581965031a911940034900d0f001d0000b00f0500b503070b0300d0300742c50912081d10b582c80480c081070 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 617673399 1250 617672149 617672173
    0x1a011d2d0301092103090c0f1a0a0203030402062d03180307050d03050405070819110102240a020706090f0b0105152a0a06060f0506070228032102 64
    0x406600d007120b600001c2080ca9821315420460703900115100320080548940c0c00c00003090744040b0400142c503a2a4422000d0791909000e00d00c1307801c50f50307614000910180110b08503140c010054030b42c0700f5010743d119941c800080c22240707290440c0400d00503c24038040a10804400d41d60041d520400c8900e000308050300602e1a203568034015450000e005900440b24228524826000b807500710b44544212600795440341d5809040200c000c02e180000c445a14880e000d001d480710078180406000e0002c1c02e91998580f104a818009001c00d00b003260114801140203084558100d9410310740094081058012515215130404855581079480d412039900120b038910781010f03900100e20700c00300614a041c40b1100c605690b01300040b9004131020b40042c841c02c0c1c910f003e000345807150f4496000002c1240c109544504541025085540140f8091151000613141c402061610184004103117800c01e04850a85010280c141c02c010050104004000309a0040c0c0700d0188180c403181c0c0076106496541 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 617674649 1250 617673399 617673401
    0xe0a03090b04050d14120313031b030e0d030e0d0f0c0b0a12110702060c010209030609030a02151f120308010501031401091d190203101a011d2d0301 65
    0x140a03c0d64021010a060000030781242c0c00500c6200702c2805840b0140343c4512205241d030022100b0303941410b44400c46000b059072007503540c501c0702c00341c0a000056810b00d84004202080582e50315001d1050080f01c2d4003410700030300585045407402859a840d8803180d240607100c050011204481c050300f0340350b011561007070354002d48165200300c0d40d03a564000580380d01600a000c0f80703260080407450070041800540c6030b00c80100300031030040d000940e94030148003e0519246000b031108410390028410405204d030b0100b02c086c4076012801003020a600c8800da50113140f00b5882c00001d44204082000641e0800e60410502c050300a4841280503070780e0303034015010f0f588009c03954855001d42d04018441d40340994800d440c07001008c0340040c0845d0302c0042c0d01e03152401040400382480c40545000003145801c00c004c0e03c01040014041c010000842c0000c0c10040c0d810350680d050080c140100c0e810b0441a0300344481f0304100801070b5044100e402e00d0300050580b00005a1007600034000003407014101 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 617675899 1250 617674649 617674657
    0x506030114010609080609060c0a140405040f02030105100f05191110201c050702031209211204061e060915080d090902130f1706071112030402060d0e0a03090b 70
    0x1e072080c09c07443e210140000300c4400342d6402c0045d400c1071040c40081002c1c2c4582c41a04500d1054501c0182d807941407200708000a180307505e5000170403460b1400b5001040d1700100b69030204103040000e079403e141002c4107075003078622021460f00310310942d80c4001c44510190003d5901c5000d2001101c00b1b11020102050644030301c2c0c0031052000c68129202c3c011809070b600180c1d0045091040d2424108508030002c44884103980d01d000682c001c00c2c0801c8a000003641804441c508288814548400324640340721031280204040c0016641d8181415007890f0410110764900d00c1c2c900402c2050303102e030407010050015114440d0324840f0034038041140320000641500004840c2c6820705428540500c5402a40c840c2e0007803282c0d8444188001440c400038808034015220150000d44c000ca00c0c48a510b00d03158004080c04108094140024084c02011441d08200440c0320075442d92692940045001889581405842030b46400f28405141c070b0040b904040d660720030798606103030558a1000e0720890003 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 617677149 1250 617675899 617675911
    0xe0901080c0d1713050901051c0b0a0209060c070603150602100c021204060309050c09040b13050109080a0309020f04020309280803071d0a0b0409050603011401060908060906 76
    0x2114150410103441c1603481e003803a140c894400030041c03040034900c224003904042c807501c9074032252071001c2c4054503046d58880d024090580d030300c640381420042040004011994054100d61441001c1251a00030381c0444051071000b81145aa0344c0700002e1603a0748950700d10608000902d041e14000749001010590000c4038100d030f0041805a840660050042c62079450160541c82210011a0745952140103000100340c19180000c200c1d07401d044c41c0b0b081011421416208007071550070000003a0b122850b0580010903580d000c42194401e10303085006081120002c0c2c44408080340d25400d00e40d058001b00516072003a110824000900b20900050303001c1a80d64061075003144001580c041075480b940c8144502c11800c0560400381515007159940c020f071507150000d0040705e0b0141607a402c1c0101c0500488060351081c2285181c0101441c0c0c0b40103d0088000194803080070031500c1e503094112a1089044410492042d41d6a04000e03104400c5845401136a0060720001400a080490210701c500 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 617678399 1250 617677149 617677153
    0x13061515120b0906101d0907030c02010510030305040614040f0e162a0521091c030813080c0708010c020d05040f06110f01020301080d031b0c020405130503030c0a0e090108 75
    0x10340300b00f4042e51b0500c072260b008509070180f2000440e90760b407143c29040c055111510001040801d0150090941300003c0000000000d1044100002a8400304540c12101103140c000d031440b004843c40d6259204a90000207044003100e00030954564443e01c441c02034006030b041100320900120705903540404c00e5010758104d9141d079002e400300400d441038001c00034810005e0796424140030021a084143c1442c034002000d102040d95001d40c123014a0341901216150384000f440b0141e40d500401c2c0520041c00e2074112a00480d0003000c003d443e47c141e50b650040c903025520182c0c0c9803881103008095401880005101e00591010100e001d076041b00c0654488030007801c5180d060200c2070380d1900240044041314482c3d448480341454082c80998040c12048000d400c0d0211032100040550316400c01d8041c1180e0903803605003509800034500200107a050720042820380c0c410441c050444400380300504203000001c100200c114050004200041641d00c80d0a1200c031054103204800100f4040d03a5025 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 617679649 1250 617678399 617678419
    0x11010507080103060507030b06160c1706190929010f120f1103030a0809070b0c100b221e060501051b0715210513061515120b0906 57
    0xc44e80c00d401066000003a420042803012001000c514241e0001c0d655030901c54021060303604003e25140b14000904680515958811704010403949480c0082c0c0351040008160340c42c21480511b03a0032004d04950401000ac00900d06800942171303a020900c400360b0400120800814084605c0381108180d840781d00d40c0f12145480b544d07811028424240c070544a04c087c01e038910316299010801018040303e959101c1005041190166240c00c14a401182540c1d070b040c0702d15040f6401c00240070761900c03a07600000c103140b20a0703000304500800c081d14013801030074401c0b03681ca0b041c10a80c1001003811b03200341204a10300c1c281401c503011180a402003a000074010001c2244032900c010054400000c500241c444240c0d0303418085059101a0800e000480c3e04410f040c10940528000c1c050300e400603e405118500d443c1030076a0a054075003100030321840e56152a045869840400c1c500680020310100491100036030010b000407546020740d140041c00d06210b280c41d03013400b150050051101804490034 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 617680899 1250 617679649 617679653
    0x1020d05060105031e0604111b15040305090415030221060c0a0507170d0204030c030209100f17030c0304091d0a02090609090109050d200a150c020f120a11010507080103 74
    0x40002410f4964408c0e190820540154000c8004190141c0c03032440003815401c0000050707040051015240090b80c1c0c5010401c00800d07041800c1300d181401c2240d00040303010780c1c1e8080b005169210340020b0340294010501b01205042e54a055490b200071000726a0b45a860050310b13211440b5482181002800c00d00c2300f4000140001444a40c000402191a0a1180c1903c17120101d801c140c0c4142c540c8580004c0400c1542803840969400c07207003007007040c5441400c003081c0c06141e410602c5864250803083c40d040307840804c203009842c000c02000041c0c2c0d5581e0754441410000d02804181d42e40c032030b140c0702d032518400c1c240000c0000706e1944c041e01107a601e9444408201c0c0f4010020211031301e5549922041c00041c40c203110765004801d060b294040b000240b06080c03144c070350080c8005c129a52018141c0404039541030166000003400903004592485100c10884c20560012004a0301e8800c4c00000301440c105070014246820540c0d4954000c002100480d500b038940980f94440859860310040c00 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 617682149 1250 617680899 617680951
    0x3207240e01110a0501271a0a020d0e0d0f0c11010e01050c010203240301090b0a0504050313060903050d0516060b04020c03040b030a2a110111070501020d0506010503 72
    0x480c032101414800d208860441c400c6040452a04044a59035034422043c04010403482480b08034884442a10305001a81d95601c4200d140010113901d907048a040010324259044c0c048030030505404005100074400c0c815007954500303220f07000c000410030080c3c0d044060341c0303d200a68105600039800c0403203140c5000055440d030041c840d81030f040210410078800d8108090000718080c1ca1340c055501d21a42254005844c0c510030102c942c0e2082c1d04110080c1c0109011800054000c4014a00000d051701d40303140562561181d00961085240c440d40001130032600403000500701c0703010710250b80d00c842c2c4404044800d4030030081c06003455446039020f000803030410360090140070b101410040c036048040c503406155401039800824050800000c0180400c2c3c00e0065044854031a41100c10820140c3d0f030100580c1041d20652041003541440c07007450307040940000551101205515540d03403241c0c140303a4040d621210255a1460038000410b0865102c0c00c1100d1003a00c92000b1004140031403481d0704 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 617683399 1250 617682149 617682167
    0x3011a09131509020316030605030f1b040219020622020d030e1302031611070f1e05150304050f0f07061116060207031a1909320724 58
    0x42e4050203001000b16500120384000d40c0201101d603034070164055450001401d84940c1d0304420301170f41142c05030044240300000c000080c0c446800d80c44041d6407040010034000d00a28618050000340200c464008580214a050051708001a8030000c1ca50b010f429448180d00140c00179084050181c05802103482240c1b2207034400070007000a014000140c0044050703030000ea8240d9081d154190700103440c036800001e00700e04640d00f80d000e0300c0b200b403411300e0200703012601c0d00c01e107041004409074000042c0c498130311000143c80000c0004a0100c21008500c0c62030b04122011100c9200b6100e10200c403000009641701e89400342d400411919003000e001310b507025014183c2200900c03649180100415174000711002400b62076004050151440c00c0c8045580c9480c802c040000c40c580d428025409250990341d1080b90b4008004140ea0390140b03403d03528240d40b891000c080d88030020300004518180d490300c14031206c4c0c21040780c00c3c0b951228010310307900d00c02c60301400788490020348801c08180604010 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 617684649 1250 617683399 617683421
    0x160f0f0905010b03060d15050f070e090408030c07080c030f1c2a051215310b0d05060a0510061d12070f06030213060f0c02010e03012003011a0913 64
    0x10882c400c0c804001068235420340310391002c40d600030100324166511640c03201222104a8036050783e801d142d1225011840054503a401c0110005556410f00051038100d892258410781141d9540078010103446864024001d1000344980e034a40c040032240741409840781c4104006211980004007045804000701111068810300c002405005c410715601607030640324035800b202052083c1103010403c2034024903100c81c1c00c4010f64998540c020080d51618141d000c4003000c2c40021100d50380800280300340c00e1083d0041c240c1c45000e0420030448819005540034030b400700702d04071906440b15030958019074416150482800d42d106115910315000182d03000042291054070b0f0b5040d160400d490850040c5d810840c0032940005414420007110050f6000a10552811003500803d111000b010181c00c0d03a0080c0c1004000c90446c08556802e62201000e514203417002c410082d0740041030307112740e0801d1041c4840c054081d203046581c440c082044a164200007016079a0009800038280024041f107400 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 617685899 1250 617684649 617684663
    0x501081509060f0f030d0c0501050901090c1215050705090310020406050703050d0b0d240614010f120507090303180f0e1e0a050f06181503160f0f0905010b03060d 71
    0x29002950300c0900036518507106c5a41c40c400103d5980c2803090a559020b4440001070785000d502074041854010440183d800c101e108042c510326500f000b0318030003403103002900c070340d031500c42030103201e9400a00428a640d801d90580303c1c840c0c0d1041840080780103501c501300208004000c2d000c0080c0c0b09800805101750510300004600b0600720100b841698841c0d4125101c1d508100c042402034521054428480c0f0b100c0301c140b0600b805c0c9105409074400c05206607041c0082529002c82c1d00380a9040065000c0307144e8010090b5140c030a00003481c156140c401900804c41445280c0c40c1421900690310903107038504248541c1c0342c80c295560140d480010a07030b500c540003c4025580410000100700e004041480300410141030803858a442c075000a404030b81f02e400c8510046a8200790000c00c01da10103a042c0c14060001004000309080005481c40083c0304000030304041101e90503000781405680d40b1510b4410301c1030f16111084100c41003030181ca5003010301031000598074034019031503502641c450b0341 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 617687149 1250 617685899 617685919
    0x1d040b0a0c1b03030b0112200313170405100311190c0804031506232b08041d040c050d060f0e1e03070b0f07050c03030c040501081509060f 61
    0x140940752107842c0c0404400194940c0a100b05642c1d02003403000440f0326608080250700c0c0d5902044168820700a00c500e848940440010000190b040c2c003281080d41144c0c070300035804406046000710354028000c0d0f07881a884225510a02c6110340b10b280c001d1b00c0b0303095920b80341c0b4102c0d0b010010704481ca2500c01e004c102140000c03100140484024000943c4600c01c0c5400c07202400c6148030503644540c0003884640003110400070280c00340f40d1111564901915424000b03c05c4500c8c620019132020301000d03030000d01118082c100240e68004008948102c0c004071140203c09010400001d41964082c00d202c0d0384d10b509121501d00740700d4401566214410019001500c206000c0607100c94051880158200820311540101114034011812512a025501d0020345507640748000c00c02030481c00001c0b2420000a441d10700840480e250460000c007140c4e180d1400c000401600c2c0c0c49405420700107084e000c00310300346400b42e205c059180b00c00107104000e9540c0340c000740646c2c0c1c0000c800555001007824 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 617688399 1250 617687149 617687177
    0x40e0c03040f120e150c031c0e01060e180f07090507050d0504061a01050322080405061b0706080f0412020c060d020717070809060d1103010f1d040b0a0c 67
    0x124480400100c1e40c41c1e98503810703440d0003080305001804503040196401008603141c6a4004400c56404200150350040c50680d803088c10002030050404280310b5618049000c1820100300010a1287c0e00354006250b02c41030096010340c42c1c8585445034062030740404824054045103030800c0d130303122445207052418000111805000d03204151000e070f40780d0381c1d1840303014151901c002125048000a0821502d54140a11101d111101d94060035214000d00d0404c4c1c0108491203089400400000b00301503101c5145480504481030210400179103803040c1070b4005540c900410382c0611607080d2842840d1255240e450f82210040d0718540d110460142081d031043d544d40300c5016068401e00c034400183c60386603919000c00315101040120307012003400c1c0013580c001480c1604407a200902640c2c0c2d035440d50200f805490182200034200301440c0341c04000420f10700c04441d155011202c40f000001940112100800c01040090f06c01410f506414000100c000e40c01c3d4001a4000c3d40514000750240100 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 617689649 1250 617688399 617688413
    0xf06050c01180b061807120b0411040b040807120816031b0b01060e030105060303090103111209060402040524040b120303010803090907110d0e21010902090a02040e0c03040f 76
    0x400012039544103043d007070201c54201905203900d050403860f4107103401e080c0329001500d612501414190042d4455181040c00c1d01c441c0c00102d0f44842a103801512142c42e0501011307550003501545003180301d80480012221607165240c0c40f01c0e5001903005140510304c0c0b01080c0c200410081c1641840041442d89030342c0c030109500c3d5150107024200e0380d585541041402011002c800e04198401e0f81042e00384486640c0c040121104013000b401d001a0000986111741050b0113400512a991240c031020464001c40109115105a00c2154200f000741c0d40d000080c031554029800310540c0b5440004440c90b035040561104101002c010407880011600c0140c5500c1c580c403d03000843c071f0f5003004c14010400d0514020141c0c00c003030941008040d00c1608105070340d1ba201151881020041e410102c418a5245d42a1201000d45810026400542c00c601c0c0e240c060210100100c1c09514101e000032100c14462087d1011758000d51145e500e0f680322003a05002c41d4002a03c01d540c002c1207071140e81d00003500 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 617690899 1250 617689649 617689691
    0x20607111305070201060603090515100806040609050601120b1807080d0513080c1008071e02010902010f0503060f010c29162d350603070f06050c01 65
    0xc180401c0b50f14000702c0013820b54007103900020134035040c010103200003000803401d0202484006e0940169075501a03105990300410381c02001280030f81c1060000303110320b42d004805c0d0079000b070003285e405036a9550715010908a4100c0500001070131000304015507a1030500714030003400001180c1400c0d842d600c0c80d03420021400c0c80d14020810001d04e008945541d0001d070701c024030500020701200940c81010820b0f00d80c3c00300c180c0003004611000503401c103000301034080102c01da08603101b001c199900c201078001c01d82458240d001c13038040482d07039100511030001c030ba204103400740055200c41c4800c401903d04912901007112002c4684404c04c42eaa0720004982c01c0d2402c02401c890130a08011024030000c1541110850130132901c500300820854a000b40300800701000040205140e0b41e482048811403410f04007248546c448250120900400b8540f01c0302040705140c5004276526213804144c0d840304c0070311a8460a6404507000c0000501400141201509103c008030721001620408160001 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 617692149 1250 617690899 617690929
    0x5040333020d09330b010c0b07090323011404030212070201030605040f23060315070c0515070e120d03050705070f0507061b170306030a081917070c02060711 69
    0x10b01282200c01100000c01c1c113a4801e03460079420804c250003031000174612141d841c6d003d4500c9580501081da00752051341c1ea180210707007048200001e20132020f101005091030314061840c035801e2070b00c540f207144984071000c0d000d10b5143d001044040002040c08400350861035041c0d061541e9440002241d0321030307005106041403004030014445110301e0707200c3c00d00d68050002c00c490202d80810000e080c0c5001071f18070000385160000049c00d686155007241c0580f04a0710040450082c00259100f01d032203080076034002c0000340c440004030302c000f40900c48041000c440c0c4294991210005901c1c250107030b4007040d00440a46040ca19144160702c80d0811180302c5601281c2c90751044104200c1c0301e40c00380602d48820403c2c507801c4061182074440c45080804050031035800030001001c02c0c6d50707680030426413001507440030718513407584444000300c0d12420707101c5400c8010403d106040c10002c01c64401940c800c100c81d0301c50310f02c3c514031502400090340000c4000c4540c0b0303d80049821040c3c1c0d81490394070b6451 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 617693399 1250 617692149 617692193
    0x204090203100512030a09180e100603061b09030b09070f060804020906060708070308270c09100e1b040902030a2406050a1101060e0705040333020d09 66
    0x3928280911091302d070340003401c41454005208400760a0b038846040c0d02120344080c1041d02066100700300500505000c031105c0000d10911607603040c0240560002000c980c082c03c0b081040c1c2d9604215104074002e102000c0c8001002c1f030300144000b0307c24070341441d04214001d04503402651584101805410140c00030408a845401088110b14050a0255101d40c1c19200c00e4242070030340c1c3e00e1120314050f0321402400d00041000086510800b00c0702142e4a40428090b45401c0c13044075851600c03200803014103801511a0000550710011182c80c2204840c0013841c4d24600383c2c0d42c03040224070b088080d06003820464040000240849540c005107000d0900c40900040f202d04503606122025600800b50006504202082005540000c00d44044001c10709218841c988041c400500600700c03074000540c0003145100b40b18075240c0c894050700030b6038455001d6010f052409010000c143c400c02c000e8990340c00c10329684100300030b8150040c00341103a0910010981c0040703030b52084042e05124010407101 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 617694649 1250 617693399 617693431
    0x506030906040b0a09030e040e010f110409050114060405010815150309010c09030c05010e040f05010b04050909011b0f02030c061911090a060809160605071202010513060f0204090203 80
    0x40403d14510680021140004016422817954040e14076004900b20030304c43c0780e030703443d04142c520740a4210103d4091441c00c104144201e00e254010380e50400d02440c0100c1e8504400801d0009008018400300750b4000e1005050501c1c00c001103590841c02800016081c1050005070741544609071800182a9000c8540d6120300d0701212050844120010650400050035000c002040007212200f007500c00a18000d1090900c507004036000d8a90800003a0820b480c280001401e694117401400c142c5104031610b01e243d407034400202c1e00703956001d1000102160100030302a6024025400c1400c61041c13070050f03e0810a00940c808c1c14900100c030080031140041b0800114442248039000c03c81c0d80e800d90381c6046c0300c039600118410720b01c02c3c01030340c060080d00b4002c110388a10411000c00d2240090444d00c01258071aa070043c426040b4003c1110f04600e0030115442650041c0105407085000c1400b55604540700c2d1140030140000d1204908420350030400859030f143c0d079000545c4125410740d03101040c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 617695899 1250 617694649 617694653
    0xc0f010c090e15150a020106081e01111806030a0e0607020c01021603080301050d02031903050a090b120613060f0608060a090203071e050904050411091825050603090604 74
    0x1a80b400140308810a40d250a41003000d5900d0201001385807000c02005a1580c040307010036401410350b600113140c288100d00c0710360f92200861004480358800e480081c0401a01f42c2d9040c0806c3c0120481c440000803c100a0150740c10104082c662000c02003001090040d0015040d905140b0151b0396207006030851031100e186560100414041c80080d86850b110712851901e500102c0c0c001070003078a110b880c0ca41404010341d5810080e050f84109080c0a4014030f08891401034401d40c0019802400302d10f44001c0090320400d1041500d85035501300700541c02c2ca0740d0344010040e071824800d0309641c91641d074071030101d185603111048502074106070301c41c205581403007801c1080425065010121141c0100100400d00d0760164401c007614403c10041a06c1c50000041950a4041e510b55030350028030301401c000034000d200c0d0808501032000d1703c48100381d4490b52140c00c0340903804070712071342568045030402620781e4110004541c40100440c2c0000b036a621b490004645a1060750405c0c0c880e0712410912003 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 617697149 1250 617695899 617695919
    0x20a080415080f130b0c120117160e01151817010b03010c0e091312080402041508030f0c1606110f0c030c0603090309130e0d09050904080c0f010c09 65
    0xd00f0103440004068146002c2c0c0c00007440b840c110b100180100302d000c003ca8210350b580030030740c0d2003000c5200440f8a03130340c0c482034880000c0b4002082c18680e803252808e810003492645d081003081c4c40e10255a00890313800c00c8820031250000921450811a0301020800380e4807480840c0001340c20b00f280b00b00c10301512841480d0030740b135412074614420f0740742002ca030310410b42064600100140a50380110540c2d141024840344201c103240140c4220440e001d1040c545a105500381d10640c400c540400001c001c002200b503045d0814010310490713038000c02650f010380884c00c000c2e00d0946d15801c1110500142c0400c840072031900703640000081001d070b60880a81000070301c804070704804540c00400364800307580c0009030b0f1000d1900205024240c000f010950043c0248100e1706020000740180080425800911004110079040c408490181c4000356007090b2140c070000741151001020a103c80c2c07220b407203030300e40d9074080006040140b00701451b1407450082805400d9824145407a11440203141c908194 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 617698399 1250 617697149 617697151
    0x2060703110918070e090906070e011101180314030f221b06030605030a0b070c0f020d12021b21013306090806070c111915030207050703060c020a08041508 68
    0x3d4458030481c0c2c108402d8403070008201d68009c10310b00d80b0210505c0100c00503641101c2480d44a5465402c001e072800c0e1880c01d1903015003005105ea0303640c0c16010421000c00305d5600040d6196011518008085002c05010302c540d1850701140b0944145849515034442240da000103640c2843d14000050420100390944101c0006250560181800219558500383c0a020091468040c85540000b40c3e00f0b11108000d0144030381d03801303031545d6041e000303a052401c5882c1e078881e5560014840d0342030142032400a00300f4100000300c09095800000001c11812640c00c540075816042d0399031318407945060082c2003d40203095020b490200c5000031060081c8038282103141c004100740550b14000700100d81c000607145511200c546003080b201252450020380300c400f5011201ea000d46061111031418490304a20030441c2d41c10006d00d0108044110700390180d018424001d00543c10200c0d082005c507500d90002d00f0b4046a62054a608080680d070b80855038005030003601401c0d0404e590034080c1ca030454035907 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 617699649 1250 617698399 617698427
    0x60f050301061d07030f0212061e03210c0d08091005070905130b040e010b01120c0804020d0c0b070f02192103050706020304141204060206070311091807 67
    0x20b002890602c4006041c01e240300c0324910190440c0000600440c1c407a9010310b1300070305c05d080e0a541e904841c0e8030030800c3d1082a11400c0c400c070503c81030013041300d01103420741807100301c007401815615168200903041c441c02e48644003d81c01040041074039070342c070900000301400069254110182045040903142041501c0b0b580d01c0a440c1c4820b000b64075030844501d0044070700480d04e1008844816444c000a0700e10000c0640e042428107102568000040d000384018201c284c1c1c8910280311540801402c3d280c1c8044a00c0101e4020400705025042c820070030050680110548400c1e25a80d0820a13841d5028030404d40300009001da0100461821158040408000702c04148000b410000e94001e800c5030340c4c0003219400b0081244a0805010b5002c1d24015a00540c0454907031030b084c01c10010102040107044401d004020425040030081002d4405481d01a03008014a9481d030728140c00402d280043c02c140180d041c05001456501d4404445c018819000605807904007400c01416002500181d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 617700899 1250 617699649 617699651
    0x70c03060912050f271005030a0e0712060b03190b060103110a0e012109080309070803161203090206161b080a0807022b1110050a18050406030303060f050301 69
    0x20350140c4c201e120303003039808030002d81580340080d2144d5a14201c8800000c1025034102e00313050350000a4075000000b41d84aa07403000d4007441070078400c1d40400c5c0c03551000c0c0110414907540c00d0400e004030700c03140c1c08002c0040c006004c94042c81e07002941c0c20050079145600300d403120901d0b030811205503454020b105114051100747c5040c180d844101518682c111041c0030304210061280d11158418114102c4544a0340d074006c00495800d420500c03a03039071044030148840d110340c06000508001c0001203c00700e881100012000143c0ca903600845910f24424110805854415070405640c41800914041c49080300409500c0002d1604107090204044074084090002c0400c00c010040071820301031065103c2c407469a21942c0380b0004c2c49150b003082603c21050f007011011310303c030f4500c0400c40011034010b501502215420204200d030a0301801d051b44005a4103001141440e4020281c5a550302e4000090307032001a15000031908030382c1e1a90054002039103600b405c02c440501c580c0c00d04d0240c503050700 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 617702149 1250 617700899 617700907
    0xe0d030b03060f090304270605030708120715060b071218180609060b120a090818041d03120c0906030414010b1507020103150503060c0708070c0306091205 68
    0xc0000e4032100010f04000a585040c0c0015200b9902841210080d0114048400c0c41082d40510725600d031303041c40007001071607251042c041491720f030000d424411201860010003101c40030042503007082c0c2090004480f0144004032042000720306000f0000a00300000805458000070b051030302206a1a006005c1403180d480c00142988104c02c3c0a00107581d00100744800c0c11444e0003100000b0201039204102e02844c18001040000c1e0394401440446140300760041181c0310081014215011007a00800b00781e01001034180c52443c40b8040380c418100208002820380c4601960307070140480000204654100184820185141000c202d0b04a2441d040d41d50a105115011070210303c00500302800324041d6412506000600350030141000d500645001c9074010880481141134100c11030880c04242840340b04800c004100304e52074201c0d00c00030014501611031403035604246d80210300556591008010850201c2c4801e02c00000551180d8000280c40102c4c0c20510b860803005030302a400c000f8108 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 617703399 1250 617702149 617702171
    0x504030504050402090a0e100f06020c2b060c050408070602010b130509190b0a05010e19050c0405090c130b07050307030f0e130b0a0b0702300307060e0d03 68
    0xa40d000c2e00e20a4400503503a501d010002001107003542e2061a400d61201c1c01c00204031401810a401c8991010440140726210441030ba142d2a8401c140ca400c005c001a84100390103203465030843d404109105039441c0c1c02d042d1113880958107508519000706100090401040707404000c90f0f001494944000c004884850300010802502d08480300c4000c2d03245c90104080320410f216144d40c0ca40100e00c0d4880b4004645032000c1d0b4101e00b2181c1e0501d962901d000050104081d08102c1c0c417846100c0102c101e490699410100200405020004114410702010420380c480c0d520440c0614404601c2c0c545501c1903448507502400b0a41202c0d00c9880103004180001b03200005481ca9a80c0c98100385070001e10700b1740100d0780c0c1800c0071413941d0700800700b88180403180441e80c00029001015501840ea517a01d51401206510403c03030000c0d000040180c010a5508440c11103000903030840080324080c00013045290715640250350f090b200d00790f689040442204003040240c0c3c0340c4415080c1406114504 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 617704649 1250 617703399 617703407
    0x70f0b07080304061b080603010615050a0c1103070605090907020109020109090519090f1205040f06270f080613020a0608070e03030a09061403270c030a060f0b04050403 74
    0xd1100824095010002c07a080007016000010048140ca4200300c026001140c01001d20704140c0d41d49020303500c0c0481c00700d00d500d00e943d02010810035603160750303240202c59402202c202c0c0d5803040c00d413144015522081229a000d1041c00010302050391003a8507100c1c1a410441c21800241c800e9055a1400c2c90940043c0d811400e2681220401580000d03d40d88a00d074210740d44580e00102e0359034920340210b0348200040d01002c08009800b4840301d080d60a0541815912441640540d00072980188810001d0782e104034150302481030041c296204d140002ca41c4c0025050a036080703081c259070300c00010301509030100115540903882006240348649140c000c40c2d50b411707807070149804000d800304c00943d807140150280c0003000070140840340e69001a91004280c045e05010b0003001482d50000300d2003060303144050f603000c0c8440d03d0b18040c1c43d0b2103141c1c0591010342c0302441b2610900400c00000f0071581c0600040b81094010003001c140000c0071000c0c80304031001c3d003825901c10352401c020320001c00c0e1300c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 617705899 1250 617704649 617704657
    0x3330605031c050403021008150306040201080606071406161103090d03030f02130312031d101d01020a03020a0305010602030a1215030206160b07080405060c03040201110f070305070f0b 81
    0x1d0100d0018242c5001ea08503030030f100b140c1000e90490703504040c03c600e1a44c055000c41c8140d030000150b007881101e9404050315920309660181c00070340c40c0310114000345498001010445d11030120420b810030210340142c28040122886e00800d540600e280e10703c180c12036002060094440081d602d00718400b0300042c40000080c00141c01c0590301c40c180000028641d049440c4d55403101c130b52005003596460540721480e0540c800c02c1c0000e0500b405a880d1030742c103507003a01120f10724001a114840e101c038290340040041c124a208540030860035252600b000b80b000f08a07201181c1d030096038490320000c0c040d003039070700c10b0f4440350441d4820040d810990f5030040b121038090007081c8011130700e9071000007090610720300c1d9007010b50320034800a1104454501c00020140d041e10441c280e640720381c0d4451060314079650464018090703410400000d54661440d20007154010710504111081d5114800414940b00d000c1e0b664442035840b80b407080c410311200700a800300070304650701780c00707001420f01031040b295000b = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 617707149 1250 617705899 617705923
    0x27040b0f07051204031b05010b011e0905040e0c060304030306090b060c15180111070c12150c020313090915020f04060302030a06030b1e01080a120809070333060503 72
    0x11800c0f0114042500c40c0c000440c56001140807011550080d0410500924240007000d000c40c2d14021181942042505803510741c2c1807903101c0500c894942004c0c00b02400c448000f015041c051407c4004180d81c895000e5401140aa600021501e0034100c2042c102d40781301c2ca416100e020107102c1ea031041140014488005080740740c90043c0341d207800b030300c449640d849034003800d01d95400d04481100018001020341115405001a15102c6aa4a80100d505112884042d06101e4401c0e1449861600d50300600e075042440d01c122442c00a8044140201c0400d40e00541c88a6464504036424442404040f041c001001d20045283c90704444510071544500e10807071003495000b100040c5250020360100700195000380c002d10481c90240e81360080d4861441034104104900380c000703e0200b8001075500105640460101c002000d0710006031500c03031004099008903c615540800010390504540304210064240c000c4c2d6600e5070350a000910301e103003101500342803601504200d1a640041c031258012 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 617708399 1250 617707149 617707177
    0x8060108031204031d22060f0b042903010e0402030f0d1b030513091d0f0d030f0209041a01170f0c2d07060b100f03020927040b0f0705 59
    0x200c600402c02030094580c04180360302080780c1400301d1020b000d810303450810a40750101040620784170700c02e48d100900d0030302400001c088180000d20003450a03244060b801451003051600c8824402c0003002550310076046240c8403085c8105020860030304100b0081d00790807440c0600b11024424400a00051038041c0c00c0e02010703030464002042c54002c40441c3c15401d480c078541e29070f142e16400240050aa10090f0101c0c244142041082d0a07801040340d80042e031801004d409150100303170040380545501d0b90030180c1d1907400c00044103140e889128807070285007035401000a051401c0d0001d05031105001e002090700113010100080302c0c0401c0d42d21a400029003a04548520007a02400d60260400d0014030b41a00101184280031a480003d40060b921034501403009901200074440720440326081c030350101b111080c013030601c1400ba0b0054401c00c4000341040c0340c51405a88030100ca60658400f44101540c05024442803207071154880e503126000045540c0a803d004200419900c82c03141c400c80a4 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 617709649 1250 617708399 617708417
    0xc0c03080c180d11030c1009300309030302100207390f1a0c19111504050a050402040b0715020409050906090d21150905100806010803120403 62
    0x4800344421401c0e94041c0901102503103a030b02d14020000704507103600c0302d10034811007070040c54510300b100402c0007052299880c10140c8e071806521407011064450305d41c6042084507601981e5110032401c98001900969400e1100d42c83e40c00d000c1d00385400900b103100c049004004c1030001c80c064000314514400c9000704074400c0f10b02450840010b4516000c446070309250f618000415403411300900041d14440164036146070a020480301451085c2850444c45400c8990300b10041c00050a0600c0040c0c060001000c03200121400148a01e00b0215540c800b603401040038400f0713041c101c41c04005820161000c615141c24150308a0040c00303500c1c0005e2000c00010100314945100c0d8040d90002c00c09850144000e0801c1d4030742d103403030740404c0b00c9581551142c0d1030041000c6204802ca0b82c04201d2a1070004420030140100001038003141d118101020030190340004c12100301d2140f18481d40c5020105418182040105428460103a101e080c0d198400d10011400403030140300c1980041d410b040031618 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 617710899 1250 617709649 617709667
    0x702040906090c0f0b0a170402120d051b030c030418020f0d020a02060a0c1409041401090204030302070603150605071104050901020d06050d08040b071b06030f0c0c03080c 75
    0x5414084030040c4002e00340207080c1c0400840310f0441c0207076845030810002c8140c403002504141e0241c180081d00180318086c004903100000340700b090b000303400900205803000d06030506505d401800710011000030300004036410aa4842036892210541c28005940b41c01d10458200380e480c042d0f8090a070600c00040c90054071400d0950484018544070340000380c40340d00580e107040094020007603140250141e03900107000006684100315204250391100c0074016043d40d00444d823604071180c1b4a4110307030f941030200c02081c040a0503600070480141c0140c0e8031829450000c7c2442050f5103e00d09042c02e216510040c0103003c142e00302699114584503860b4489810b01408a1240f04240394125242c0424000c0d0000f040d00104204040c3e00c1052002030364031401c2c0b11501c02c03051000f602041e01400b00f403102c0801da20051120500807104401c1c501104004540d8040c02c65201001095841408003100900c44c06600e9018440c0d040100350200136480c050f06001e00144001c001c40000240040 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 617712149 1250 617710899 617710901
    0x1208070912050109021302090d110409210f180e0c070f0b180c010206060607020f181006050a0e04090804080d1206080f120a020a02060a050a081515070204 68
    0x145048880718030500854140907000307101d00382d4280e002d07148088140d0310003034442c000c4a80d11100079042489001c0ea40d20b4519441d0148032810741d1050302d84d41802e01082c209810410300b504541100003101b49442c001510340080ca1001600340400303152a6401251000380c40b0b812604407031505101542e40681428440c854108020850784241d286041031116071091948910100110b40310780d40e4040e901c03150303901018042d0340e005030301c1000022002d08150020b803c030749201410b800c281d00c03010710010b58400d40c2c203400d01225442800412014815500c050001801682451403070601e10a100901034600807801e035000b01d45030f0080204200348641282c0c01445d03c41c06880124043e8030b001400309001d10b0803844518103060011074802400700303040030f4003c0318a0040992140010040b40c50f504400340340390950203941d45c07000141c0c983d5801401c07000014bd807002d80d2400d0800001d00040700c0980680c40860701c0c04650140c41e110880c200000440b0032060945580272480020 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 617713399 1250 617712149 617712167
    0x60e03030d0204031203060b27041103040534030f030c050616170618130c06170708060f150405120d0f320c0d1d010c120807 55
    0x90403902c00103002051102e0440309071070b00c00ca259014400390741d0341c0000f0072490150003c40003070820000c54031080c0f507048050f140f0050b07001800210b614078540600c071101da00210303404e49070f6400170b0303803078446260741c41c4c01008103c8060300000d00040748001140f941300b051400010411561a0b8445081c140180c3c0e00c42d410300e600108075825460b02e03d015000c80380e91074102d28041642110101484292a10340c2481603402401010220501442282c1d5044018118100707030076120404a0102d01c98a50800c0a010551540b40c025010b40708041181c0f000100000200914807003403114503030303601d01720b6164070300c0884c2c981030000030440005010b03118552250794450701c1c40d1110302c030030100490084c181d6106500c0d80c642c1c2c1300b031411050300c072403074400b0121509116001d4103008482450022a05007511803034040d092000c0088138600e805002030280300800c020812685014840c05259134110f207080c0b82c0380400c0300d150703582d4418510300c5072441d5040c4140c00d0005102e40348910030721 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 617714649 1250 617713399 617713417
    0x1120f0b0c1201030302010b1801032112060b0414031b0f0604080f0606010f0f0f120603060207060501090f0b060d0c03090506040b0f010501030b13091115090f09040804060e0303 78
    0x184080d6500d1170064001c2c228415801d01070b070000e40d00c00480248202245040b2034010f05942c00513485144884030505140c4184414003426800d4404110050301c00d24000d4000e03110600c0c0d0329820481404011002108040e2295115400c80d0b0b841c00811800704034081010740744010107600e00d40000d2110300464100e20524421002032541013907002440f24040d410a03295540b50408140b02212124503152010002c140b042e0842d2551505c0740340c1c000c03440280d030340703000821513126550365050b0703442180240c2d245034803600144400001d603c0fa104180030300c1e4804000b0155a0313400304545010310031091100658400850786040e001c0c1d00301c4103907140d01c4015107225282c01d14205080e22000e0f11a4420790105800119080d4002d02c124021741d2401400d00c41a098a0500308000c0c0804038000c86614000c290740d5000c9032a4908d00c0200f4441c294141038035424080c0a10100744819141588510b6443c4e060201041c503d00c102e07000c2d510180382c4000c01d440c41c600842c1c90343c444c134051 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 617715899 1250 617714649 617714677
    0x30c080c01020c06341b1202010504050c0406050a0b0c0f01020a0c05070e064920060423060d06050102150106020d05090f030102120f01120f0b0c 64
    0x44102d08180c04100305100e802c050600c0380b404503083c102010000608179240a01c03035440100740d40c0540c0a04030071180d00000b4003180c0517090301c41e55004010344040c0e0500b40941e44981c140704c01c001c00dd102441e051001032f17030100662031502d030001c0c100310390718821105040400110014003400c1440302c1d1403810303c03000c0295561024140c0040081c2c0888400b030314140141c04000ca04155108079035401388400920044030b40c1d00d0003040406000141c81c8542502c01204000340003c8070502c07100c4a400e40c100000c2030011030034103010015490300c04001c1c0ea141103022447d0025902d0100b544c0c16258070790702910050400c50034504085d4000409254040404100c0400765103582d0002c00a485081c0d00380c41e000410460302c3c0c0d2a4070001c0c003036400580c10071000740d102c00b48134602806141000501c1c5410521902c40800c0c00c81c0d00c481d150f5403400704408108140a05803002c0280109600130201c005400140c8803030b0790913100c003032006000d00030707500c081100f001420090b0b600c0d110307107100 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 617717149 1250 617715899 617715907
    0x10e0907020321040b0403052208070f1d0c0a11030f03040606050108060f0f010c0c09020a0306050316060f050d0510031104020c030706051f0312030f0605030a030c080c0102 76
    0x82c0d03481d04801c0e40d840d00c0180b007915000c0440c04542825004590040707440003281c8541c0e80550746900900e4042017040360481c20300f81841c05064290f4001c010031000b030f202141c18507140702d0001680f030b0000d0f18001c244d001761400350141c0c0078155503c818210891030715100b44241c100d400c400c1500303038030440b840003181c02e148000d424401180100e06c00ca00130010700d0303619401075a10b05001c8640c0c81d40400c4080100c003075810500b1300305c64000c02c14988810b40d401e00b6561010840702a40040100c2035000c101c2c0701c00f0980500c60840030b45821801860b4040c0d40d0f00c0d000a240100d13005d0481002401005464224020010364907500d25402d814421483d042d03820309002c80d8188000eaa0400c20b50300515210b0400b442150100304900004d189020340513250500981006000306c400ca0030609408419600c0d00300050024601c03440b00c0c00742c0300c000101c000b010785010034540030700d4034a0301804024564000540e8410640d144c18480c802611904059449001f524882e01c641c1d40002 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 617718399 1250 617717149 617717161
    0x8060901020903010c0e0f0922060e0118082b020c010e06070504140409021804050a052b08100906060302090319050c011116030f030f08160e010e09 65
    0x90090408682c05900030401c00100060845007561210b034542d0b00f00180c00c0c02c8004a00384a001c1c9907025000f094030081200c242080c0b000074114200050701d04135514403201d0740c034030b034280602c030b0038800c4640c1c1c102017490050300c80411502c10384440881c00c0052103400380803503006000001030404403010442d114207482d113456000e040500c030317038808074040e9400055106000d50300741c2d810348020044040420f429602804004c1c942404280da104034804074a100e1040050596413256201d9000741040e01e0071460310074540b40010000b906a240b88500c2e107100e03001000a00d08030641146022221038a0740301c0c010850b682c030764101404007410120702189598054004140500d01642114900300d9045800d04400804000c000e165070800d100024441d0300c11000c5056604144080e62100065001f502d0700d00801e0341d00885045000110351401d1541020110308001900c0c140740c0131a00e010303440c0441402d210781034201800814103c4100710307445064121071b0768030302600c50815401c00e5 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 617719649 1250 617718399 617718401
    0x90610082a030a0c11031602040f0c05070b0705070209132a060207050f130e100207060b1f0206070f11030414030c011b120507080304060f0b0a06020c1003020408060901 74
    0x100c420f048024200111803030b841c3d1164588a00055103213020b1030610b00c07603d104141139243e100c4240c4e03000d82c44584452140080d440743c200b1004140d219aa40c502882c81d203090450300040603d020b00609008080c05030f240d01c0c41e509d80c0450789000c8466088a103282500b000f0111001700405410f4050007840103c2c2d03004402001d031016502280c1b070f050740c0c541c100318003c2d0380d00040c1074000c2c0c03551a160140c120325030002100000b42c0e40c00e49072a00d01145c010300032a00410707010780c3c6054503652103c206d81400304800c2d00207050188000e040721071aa402a40d22200906500104801102004251880b0710b001801068800051343e17561035917100b041214080da25442407080c002c0410750b181541c00782c40d40c8a0403084400c02e50a0710110381c3c8458482112100c0007c0501c2001c004410001703003400000d61049203d45000180d07810354011003002c440c2c00016041c064a0004400d11480c0d0f00010422200d0b642100c1140400c0c607410411000390059a22103c1c081c850002800201c02e41 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 617720899 1250 617719649 617719651
    0xc0f0d0c0908010b0604030b18060a02090406050904020f0d02031011031b070309030b060a0909030c12181a07021206070f0201060b04090c0c170d0b090610082a03 71
    0x306030785444200d41c54000e0302e42202c2125854680c0164208820400584840c0380e0039031148260b00180030b900141443d841c203265089440c100d5140c0d00003003507602860070b4030071000a0301e000d03200c100703043ca0036a010561418411f50b00500c104036521405045680400402900c0c0c154803005001002641d400710855801c1030340e0704918151041d04208501119105036481e00d501130340c54040f010300e1525542034a40000c1c10303040e009000c4e80e1020030708072950b00921a40922940c0c0303004103160503013820629804c81c080250700b0000602449081c54400e20101015611b0066a0b50410070745119804001d108018000390032083ea6410006500404500540b20380700381d844580d0707190520031089081380d00b140900704442c1d4051205202001560303000e481c50b6107043c00c00b000301d80201d4a41200f4442031009400c0301d410000342c0c2c943d50354036034007070b000c0280000d50b10122281810000114201d581000807400c01c01c82400041501d42c004003050a5406142540e180d0a0440d0281c1851a44 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 617722149 1250 617720899 617720921
    0xa0b04060c173606030103080a032409020a050706050f040201091e090e0f070e06010908010212010605090a0312020a120e090712150b030412050c030703080c0f0d 71
    0x3850001c02d2040b008200222600403030f0b0240c03001c06102d1103200c605000b9243c1c001d02c442254004085414584641c001540614050700403251141803e09004007a52012080e411445d51422084120004070800e080196450300c40c0150310317248090301c1250355014a45014104a040c20240b0004105100102e4000c0303001f030780d89213140d54841c1c46141102130304a00c020784074010302c0402c100c028100c0d8486004402120191040d15800820381480e10b10603402002202c00c54109104117580c02c14030a40c01000544000c1d800d080501510010018052003503c003402400590f00196a0f61141101e0180d60b00450303240011302c003210005c0d61183c3c046400c980d10240c1030031111031540200e020b2444400010304484983d983c0000c106c4048a100505e00c81441c1c840c4020701205d2001c280101c090301801800381d031030b840d05e03081c003128001d5840c20745000e01c8001c200c160343c50780020040f1030304140c040c1404401c1ea254600203001c14424180e895000b0341c03011812071403c5219030040b1000c94 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 617723399 1250 617722149 617722163
    0x1a0411090102010c080408191b05150912030a0c020c0a1814010e0415020f121504020f0a0e0d08070609060608010204050a12110d0302060a050108060f060d020a0b04060c 74
    0x4c0e0b01c2c064242d4500c482a20050a40d84c0144808003210040c80f41544103a4001d2601c41c0c0503808501c1040d0b84c02c0090708045a540d0006161840c0b00c03000302c10040c1e40010740c40c0003021015140c0c1c0d0411100d2001a01210b02d50381c40f40003800340c16008000c05210300c4000347c140044155030302105000e661300b0001042e60281889418807060040c281610b060300c3c0e880001c00c0644e200c6641e0303c072a1041c42610011b0043d000e201e0030030550030b02d4029003041840c120b08040c06243c00844d035a2629182d0b070b409445607206000c605100001c0e0019244405280d0600300300302980d12001455841c15039070f004203d0341e00050300f44200540ea42000c2d41c0350388280800c0c0150b030344a0313814900340c3c003070340c0625034000d508008100800e0b200c04030444041c501072030b81c4a8030880c188000c555003100071801980940d0143c0305125100c42d035842490300400821001e028641018504d101b07148801801007480340c3c2c92404517000b50b50314610301d1802040c1103c03501c0d0350340d0f0355240c000c0c041c0c0100c20001c4d2100d0f = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 617724649 1250 617723399 617723411
    0x40219150201051303120b030703080c0c0f030d0f18030c032a270b030601060f02060906040b010302220e0d1106011d04080f1810020f070501031a041109010201 70
    0x6900c0219003641441e81c1740c3c031160015105441000018628102d04603494880c0b03203030000215a10703000800741442c01001801003404147c0510a900840f001c26900a40c44400000b0045520100c855140d20083c0742550540a5458940f090400b20707400c050b000ca00e00c29000020805014211001c00410080c4559812100340501d43c5907420f5220f175024807548074810340c2a1788038004100d8000c20702110000f9011000c04082032411000340c0040c0d000c1030f03080d01301c6503e56804100299000146800400803071070240e5801101c4407040c03000034081e0003142558214079640c81049090080040c004020359240d07056010b03a144141001c0e10081a0208203444511030b010980c0742c107840c5e4028445a16040101004d180250002c005070340744001403007102d21b217402c498010301e2400c40f032004c0000305141e14003c00c844482d1040380f18007954404201101d04030404a1704404541003400d00003a080300c000800c504207001c00c00d210340e106203010361a05c034910f00c440c082c002440080c1d00070800 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 617725899 1250 617724649 617724661
    0x40e070f0e0c0c030d15080c0918070810091a1e04020402090402120402013207020f03060106030b13020307210e150a05070306080601090e0309090112150204150804021915020105 78
    0x50788401b0340c1c0341d50044210030002b18005030400f80c00544003c0762084034102c5950340c0f00c0701d08049025510200d003c1d1121035200503c54100c1580c1c40a00f4402d91181950414a04681ca2000c01d41c466107860001c000028041d03698503030555107030318000380080d07542c0c0d03410344c1c24613054080c00c80e0300300d000c0303800343c3c00300400501c00045610315102e90103408505070a68417178405541d00100000c0384d0010700401d0b5100d0300c0e1000d100450007024561800b16442c01e2110400c1025517000c0c000c802c0044c41881003202d403035800311191289142400149024a40012812010b09a1203001c074609200b070000803141d00d0864642544a5507085204010640301c10200700e065070000c0c4101d2003940d11040c01480607008580c8906080c3d954441201e1419441e100440d800102c240e0201c0e4030340010315940c40034408901a61021610100b50451a16040c10720b04101e101c81150148100404000094119100c0072581e0030720b03468040700c03a01010354541c46080343e0380149580e08019400c020110740 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 617727149 1250 617725899 617725903
    0x3050309040608010b030709090503040f080303090c0f09040b0712020f09041a0a1e21050c0d05031602060c01020d05070f0e09040201080703021314040e070f0e0c0c030d1508 76
    0xe20351100a007c2e00d1058a0b000102c405007440c0402980c03030340130030400000c1d0400458080700007401560082c544a1030280702480c00c1c0b03e18902d050b40a0090801c1d0080180d0351804090751150780b114010b500303a11100c000300d0340c010303141d08001e50f69440012000d44000d1240050140d01d04225814051540e0100b07000701480b26803110707280c0211550030b00380510600c2c80800069514071291800c40c00341d640a810303081c10300c1320401d890f003400d603184c904003031180a001c2a244850103032120341140b1800c0da902036a07845501641008a118141d864046645000403a281c03400c1540080d5150090790702c0345030003081c064402d4800300d480c0300001c00317046005620141c07201d00010240d031070707070b42e1650010b54288000404c0041011341c204400c8180303114441d0003c000d0011405000c645c22005820320003180c1644200c950180e1041c18100150b1482c850b0700e50030340f040b000075030390b160f211820445968040c0d11320080d0075010215065110801d644d01503046d00c0d0390024600c41c010b41d10304282e5 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 617728399 1250 617727149 617727161
    0xb04020c031608071a060a050301022a1204150e0d080d02070c0504052a1213020103020c0601031412090f121c02010f110c0a06050a150305030904060801 67
    0x1000c0d9420a1011582460202841e020514002d4500c0d0349031500644d04c0704044540b0000b6200d1540c40c400510509040c5a09244064001a40214609489110032140e054000a4951001207504071100d12400060000d25044c0341c6120040751074503240e0741c9450824a016100c0d03000240502c040040c42e02d00300000c5410160052903c074640704400c99098060f50201c0300c25124585291000540ba4456100740303031103402d10318805071210030980c4e000003003800c20503c15800207106105032100c240c01c0000c1150000035080b0170070080c40851005a020380a200c0b1100d54038022a0000400d0003c90386241c210080307000300742e540f4240b410442c0071b0381d4081c0d401d590380c020000c84031081e0305052404c8102d91216141e07080722240580f0103900607603a01c04c101035400507510b421030b0018088031400340c85185414510745334100120743c40015550300782d414010f41020313201c0000c180035401039032081d02048070701b4000010054407820056038035481110481c2c026860072000040c0c10300107100d94 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 617729649 1250 617728399 617728417
    0x1303150e070f03030302030601090b0c0616020105101707081204080d080c090103050415020f07020a1d060d1a0711060907030c0902280306081c02030a08070e100306090b0402 76
    0x20b1a050704644003280290002000c081c140403a6201c0422684020b5000c0e22070324086a009011610b001c14140c1030400d084509001568140b41c240014a540010210b058408184840780318205217085245000e6841d8050a051b006c1d111048011b00081e50050040d283c2c090304442207a0f80d010401c4422400845100784100c600f40718554040d03109401c02d5401c0f501075000515000c0304108500102d03031181d4003085051703800181050850030206d01150040140104070244801d0385803090400c6c0030004c2c00390344202450702040f400c10044d018038495814944c070910940f450420000303080c2c0c0291320a0b0305034030b110b00d8000035007a400000703413081a240d01a5087c503a4500c3c211600000c0c0d0014906041400f0703c07580300400c2029101c50004980407641e4001c107119107003080803070400da00c0b0841c0d041c40010780c030f1a42d540c40e40c002040350424003544c6814511a41c41003021580124603408140d813195407100303080c40060b4142c10801c113581c0710030000c0083c1a81c1d20108000c0b03120301c4c0c0303031 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 617730899 1250 617729649 617729669
    0x1d06130c09020901031407030f0f06050303031803070f150e030913021b010906050f010e13030e0d02030f160f060c0204050c120a0207030f1106130302031303150e07 72
    0x2052084000640103403898180c11705003c51300f1305041e006400714103011580c041c0085e65610701c0850b11b003241e0140c1082062900342c00c0280ca402d04000c02e4a0388401012400c84000340303844032446c003004000300d138260383d0041c0101b204c2d120a40380020220f02c0d48452202c1c8a8100005184681404022940c0e81940104800d6850344881001e202035001a000404215034560010807420340178062103a0951061400050514000e510301c144000d06800559407000300307800308000200840e5aa04a0a4040c1801d981502071500003c4021a14035002074041c020320000c00210100001c80025000d040d8224403146a2a80010184031185118a034005003a0004202c054103181d48039075040341561082610701244030102c07824a002c20741e0804845a0b0006e044818183d02180881c500c490b41d2601010f0341880703025056540c00050f010310700341c0e4680c802003c1014000c204680070106d101c94002001656800d0141a05410740340540c5107509150388044038003000305200c03065801d1821 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 617732149 1250 617730899 617730923
    0x2d0b070302161b0801060906170105070c062406021e0d020d050c010e07081b010905060301140a051009030218040b040314041a09010f0e031e010b041d0613 68
    0x112064800c081c0b8058042502d80342c0f5010035110400e0045c440542110b500105000b8544a002007840c0780051a160240e490301c4180403450740d103e030b082c3c1d0110b40c01c4003002c0ba500c6540a14804d0848904140740e240c069146000502e4940101d002c408038842c00c841d003601500088055922414568420300058021146040000f4052400751071039a5030800000b41e050074010b0900c1ca002c203e41c201c24640d5109446030b6168200c91040c2c000d0303603a020b2078150a10b0740b034100810b80c00d02060107120b19025801034406166180c81d0302410040900030094050045000d0000d400c0100a00060340105c800c6102e40d5425031981c1007060107254408030241c0342d030341c8903181166004102e00ca12004400c0401c4001440100100d49092441d01203214076681c0d4071100001d8051040684088203000501100e198903550100d051503507002c000c00e10b88507d48541320401d0042c43e4034114250300900e0411510385d80341408079281d00c4042d10108403103441e140d1a40c20f251080040700c0041001000d40 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 617733399 1250 617732149 617732153
    0x31a0405061f0806070507050d020f1e0114010e10090e0a0f170a1805120d0e180a0605040501080f0a06180b040b1906140d2d0b07030216 60
    0x18219521042e40c4103507428180e600ca0031554104142528080009000030a0210500c4018040c010b0f00c90342c00d000078420420440c0c000e07a10303807801c80301c04800c0b20b06101c24502d0901c1d00390001e44c2e1121024071601020368541101200c6944187c612a40700f0581410110f421403091182c4200c0829160040c03d01c00495030b01c41c1100c0c00c511008aa440ca0003914404404440030090018008161192509a4088110307a0903500312a40a24840ea04050782c3e03100401002c195503a20000610f0181c89105040000c1903003811198450701883d86440d00304103028a0307030b0b032098040d5002202d082c003076640e0341d01013555101000410b00405402105402000401c680d10119009905401d100f40112040d180c2282683d011034040d200701800404200382d84081800c0d5064507600b8510400956081840c132004c540c64159150380280c0030551002d0500c20b0804164182501200d002c3e2000509a06030b19580d40b0b601e030003194140001c0740400c10b224064005c1e91b14204d6000e0b407602d881e20240d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 617734649 1250 617733399 617733421
    0x1022d0901080c092b03123308160f0e0c0f03070c06020705030c07080d020a17040902190e01030b100c020d060f09030206060603010b09190b03040309031a040506 71
    0x4a2131107a01100300d04124001310390311480c020390880029200503840030f140c240941544200c0c41c402e442145402040b520f0a4840b80c0281c11100c5851310f03103e0841c1182010300c0807035481e900b000c8007901c65201100082401100c403202615510380440001c1035035204500c4255038141c2e0308616407a01407144900c0040100c01031640003c07589000c00071502070b900c5440032a8082d820039502a00001481c040c2a9801c00c081801840c811000300f04580b0f2451000b5159070708407c0041c11468685209841d07e00e808069801402d030b0214110f5a90300100794414609440f00404808580038821a12096010384203001210002604410000c154854101c032080034255049034071000100c15000403c0103441a040031400b001c000059003403039410042e1408000520075841103804000510400203148151161000181c80f6200d2001141a0080e1503c0498100c060035401c0801040189a84411340000b01ca020340d1a02c10400d0500141d26014501260080d000e84e00c80c02c00710300c04200d5 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 617735899 1250 617734649 617734657
    0x70b04230d080301080f070311060702010903020a330e22051005041d0304171005040b0f010815010e0a0e07080c03060609221401022d0901080c 63
    0x840e094a4100c0c040c50400600c0701c0702480380030ba5003040040f0041c00440307801c20845032001d030000c1c000c000481c9036544500381e03120b8640c100e03800f40d400400c4520859010303e079908003955004203a130218a031541400c0603000c1d201c038070400024045c03040e414104a10180f094050301101e54841520710020300034000d43c0caa540301da070341d50ba42034985540c914142921586000d0141500d60a680618203003c00050b07030501119554911b88020342580217600c004220380c100c82215a024506011144550341024120344007046254181002c000820000c2c0c92104d02c41c408090042d42d03e030340c0303890100360398111242103940c6800e0540d0040c856803214020300c5510441c0d0503c04a00b04c91320100c01c82c20002c1030750207181d03031754042007c0741414641132082c1d0b41d100340c0580c0c0103582031821045000c41d0110344e130020351000004032600300520031200320268000791300900035544c402040c0d6a4448502000301c280c0c00e268080342001d03111102e03200c100d8803c2e40050307507541c40c01c0c0c8a21400b0b03006988 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 617737149 1250 617735899 617735939
    0xf18180f020f220f05010833040b0f06090d0309082b051215120f0604020f010e1c0302010b0a060f08070801060f081e07092d06030b01020f07080a14070b04 68
    0x240d00c141d400b207142c2c0c4040b0000f0b03a50408c4014421240071106100581c0c814000c000e1080300d800101744000c1d01e0358015944003074002c503a10001c444075804d0546640300160003480c0301d8090311031200b4401c80000701101d502e1700301d4401a840c0b00e8450104454a0048075804640c044440b00400d900808400901001d168002d141e00030f501440a1103518100d040c04a007081d0350000340400055180c1251103000c1d425003800c00d484101c029200144612224101250b02507048180860a241c800d510040c83c2800c0945002c0003d40c80e00009410a504210300500003034404000440880c807640c2c85904895058030758000035849401d0540b424207000348800c20744140340c00c5010408480080540c041d0b2020348030441c2440c14036034410122185d144840051400700301404071408c120401c07030001c8404c2444e00085030100480101d05050f001d48900c2c03094840c3e910301169800c80450410340c3e551160000301d00c1c100026100c1600e800b4648508881e580090104010324841c240b41001d00700 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 617738399 1250 617737149 617737171
    0xc02040b010212030106020d11011109061606020714010c0e06090d031b0803011a07020907030f0914100b042903030d050a0209010f18180f020f220f050108 68
    0x3095000c060341c0f42e0005d0b401080140d0000c2c2000c040c903a0400205e0f400700041000910130b03504010440d034a40c1c4110b09030a80258800542e03200d0102c1c400c08050710907179001c0019903407a502800c150402e0400c1f001e4a503455480c11030320139481c0e40951520414040c01414460401082c9020003d00c150b041e00103505204032101f1102a0422240e50915083e100c1c03d01c0e99225410603a0100e900c001142464100345801c1013103601503510740160f03a62001007882c0105070b001c1d902e16510050410100b0080012046c120707807004002000c5423015101c1c0c0c08400070401810b0303510401c0142d444e110402e03050b0484c0301c2c1c2260105110803d07000100d19010b03046078078040d01039001104030340c401c0b41e408004a40c0440c1c2101c440d070344000c5039800007906142c5010389943c0e030100c40038910b0303840c4a0b44e662020341500c4800d00302103d801051402c44100c4086445140414000c00150720010408034100740420103040000c6210352098140c540d02c5038001c1500c0c0c2464015510b4010141140d1510 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 617739649 1250 617738399 617738413
    0x50106050909062b080406020c15040324020a020705030105070504030f0605060111150f0705040303200118050714060a020a08130f1512270c0f03030503090c04020a0c02040b0102 78
    0xc04c07807a0480940281c400e10400d5525440d010340241000c6240d01010310a105003405000148541e41c10784d42a240c2020f2100d000b445000b010001070b05407034080407001400811602c2c0900d401045e01811034034264001d0003659141c46d000c4407240710310b000c01000350b65102c0d0311802081e825401140d104006060501e602c800a03192103141524001141000605c1c001c00c008003030a8420a40e60812071500385107040c0703411070354080d0501c80d81c0200c081c1c0d41c3c26908120a14958250490010250a900300c204000034a003442030f122901c90040360410244210a03a81505040301201d0004801d41d003d00042211680c40a0040e80303c2e811400544420400205040c501600244020300381700a51456117220403101401c21420350f16150030f40391828164000700d11096030700d242d1107182019007181c0031100745440b0014a14039080104506d40c1d200c404020035170428000c500501ca048111503204007003500f0030050b441201c40f500300003800c061b0030f0f10050a060308800e900d00e8050040d2111 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 617740899 1250 617739649 617739709
    0x60f17010b1906170c030103020d0f02190e062e17131401150b07050106030c06030b1203071a090307061e0c081015050d06120605010605090906 63
    0x504025402c80c80102c18141030100720550300545001e49441c0165190300e0146032000d51100310f804140300c06401840d509000f00c08002480b42d02c1180e60303a0043c914500e141c0c1c83c540300700e24504031b400b401c1c40c21a60315020a0844c40c1580c0a03030125203174881100c1031440f01134a1030b000140a4a241414005013032441c152125900071080e1003503600c41da80200f10440742c1032440c0170784420801810b0036450580b905403101c1304e0740001001d44850507612642c450461810740c1c018220303980007618807611450081006a415008003403044000c5511010070250514003e85030700c650318000f0803012042502c2c00c030205040a2550744445104191b070305107034850300e030707082500d813284040c0c1400d440c50034a0300c0d04610f0b0380c49500301040ea10715002159181c60040750a40c0110b5016000c1c01d00c000d15a8800641d22950403140140103c0d4800d0103980d03580d101c4000341c0840c06104a6146041500105217a441003080d1032103450000c204207139a40300c40052114500c1c0046a603e4800640c03505403030 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 617742149 1250 617740899 617740909
    0x21605010204030f020a090e06010501031d010207060e07080d0f0c0609020d05150c040b040902030a1d0606031506010206060d050f03070305041a07030203030a0c17010b0304030909060f17010b 84
    0x802140661080080b0384005c0c41040020083d80d004034214601e01410740d4104a00000e440d41912028200091210328524600f202210600302d000d00300c0d800050a0300c1040701640000303003040300d0007007140d031140d448841083d106ca000300064000102c00d0407031074500310312500541620714014580003800480a40118602c1003948209a03a01e81c0881e83c034070800044000c60952018a401082d41003600b0404100c0142c0318078030aa120064000c408120010740c02e42c07041c80d410b80021400c2011400554025480f04400c0324024428002c00c003406025001c540b620501c5008141e01514445e600d540030080d2007041d519041d074483c800e010120886001c200300030a8094000e44402d500d6503c1c0079000d10451101e05141d01c01c1e5a01405500002a0000b098036001188903101041002400800319400040090f417482c90340c01410000424405003001107019a0083e5178003030285440300d50b003800351869072007512010070380c100c01000403600310b8088168220b44040081500c0c24a100062 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 617743399 1250 617742149 617742157
    0x61e081c03092402090a051f03020d020c01140a0f06030b0606031b0c011e020703020d200d08040201020c1f03110409020d1d0c010804060c021009080c0705030c0d03030216050102 78
    0x31003598001480480c51401b03000c1b20001300400c0b0741280080d6126040342281020100c840c00c01d01d9000702d0034100056940e01501c1c104440d1500801400400661801c103200007075522f240c4103407800711088d02c85216030280500fa290841540310322921840f091042aa0004103440c141062315036401c030411400000800c1019524800071454040d643c01c1c40c400e40d40d030035019032171213481004013000094000c0342c40d01c03038501e407404d0104014002e40485620384002082e541c02c1409454080714080742c100140c14010b41c000c0c0c6c00c4460fa1100702050000303105614411600761000414102000351089c2c11099500904507440350030319aa5103104001c0ea044424074070303062601c4104042842011500014480c00c0600080c20411500c000190402002601c09481151a80b0080038400e008020708004242540020405800c0c1810010841d8120b64849043d6000f00311000826180004e400305020b07030024140d140c00d003501d940940c000d6210454481003441100a2800442d07400e10181c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 617744649 1250 617743399 617743463
    0x504030f0b090f0f0c0a2301030e030f0f04140d110f0103090203012c120a0513082407050c0613051501060305010905131101030c0909061e081c0309 65
    0x1e0402e140d05404000c021051038011081c414041c3c4400840701c0380ba40c1c7c0b246d00048007800c0000d0200080342e0041e0552099801050385441c1c00504038a4240c00c032401042103804e03880900038842480c80400a074403c2005014100e82ca81e108500e4440c50052403000011105040014028455901190035a4080070408014818110004660030ba91040705800069400c1c0a040705108006403482180500c950390401c002c40412000c21000c8880c00d6000a80340314411200e00c803070140b501c000c00c04e8907070b25000c00700900180840c00103406082500d0311106000c1c01303070106980300078140d13101804003182541c0a109017843c40f00d00e03140e00322943d4082c102c6540c000c14958140b8000b10309482e40608040e45010a0b4003414021420000000000c00001d02c4d02045480c4020703130480d0140120b401115549141020004600c13005e4114600c0c0f100f850842a040c460b0f84c1c090b1140c0702c0540f913203c1c030305a10000032101e00c1e661190780251040c03031013100c1a00c1c41c80080c6e246040e096400f02a0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 617745899 1250 617744649 617744653
    0x103020c0f010e0f0a051203070203310f1406030c041d10060c0201050403320c0901080a03050910030e030f040501170103050d051608070b160504030f0b090f0f 70
    0x2000020310f010f1140c80301c041040c80050020a200b03943c0c0d5940c4284900941e0300d44071000c80415012803003402226032a0540702c42c805460840c618541001c1c0101d100c5803171008640000c0040e111641e032100c482141c03040412040308a006405024050784014140e5070b40c130404100124201a02c1c00604400b03002d2107000f81c0003850451940340052426800c10014000c4211610b40144c0e4408100c0741075960140039444000355581d201c0d02e0080c024241c1144020059440170404540001c00f2401c03c1800c80d1016140d9a80e80c00311529031089145c0a8001102009417550324140203101c03095094503440d00107001c1c554400c00d20309503040a40c19010580c0001020040c960348802800700450701318520745100d500d1552180d9980746d14030059814000049180140c0c1032941040031500c0d900215403a41c0c940d100d143c0920803030001c40b002d0076026421043e080e80f440c17090040d80d05a903800018013003030300d035107403a44401000020005070413441903000351a80300405111001c020084480 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 617747149 1250 617745899 617745911
    0x705011b0614060111070812090f1026060a1403030d060306090b0c120f1b04030525030309030611040519090b10090509060a0b0304150c0f0c0605060103020c0f01 71
    0x2c00104541a040340c0d81d1750960003445d05002c10b0341d0204018540981d0003d03070943d0b50000001003240d000c0200805903000c0012500c1d515404d4001508422b0b9401c040c0d143d40806080521000603100d044e0703023864025132107080a00c5401c000c01211000d02c40d00504503801c1004090409096480070b8008444031a113502121040003010080c954000f41d1a4a10780d05141901080449000d0001e04c000e01803aa900b011500c05d8140d044d01448050070302502d1980c1d15124205160b90381602051a03d0742803211f8505c0640401c484810030a0365030543e00c4502d80e5203152036640c05403403050f060704072230325081000007040e5544503008030380044400c00c03030080c0038980260002152254060140039207201504240e99550107180001615821251107230b640d100c150103e4000840707908015242040001840240488448401da00e030b03d1040d41071141560b241c1c401c4034803c84050301040401c0417046131400245140d005142d00400614006040c0040c90444c3c07450650345658100a41e550741c5 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 617748399 1250 617747149 617747161
    0xa0504030201090b0a0c0f0c0909050109150506061909050a081507030506010507021504080f0304080c06040506040312030b13020705161a1806030f1501110705011b0614 74
    0x1000e100074581346030000e05041400300041c1c160901240000c2c00f80c52803501480c10011504400c5000e484507140401c00d18040346803060080400c0f0a0a45000120b405211101e0000e8007a4502c83c1602038215400d1188005400c00c0c4031404114003418490201c0010640d621141c500d1402042c81030000d1003034a1211031145034808003d0903840405081c47e04100b41d42e42c0000c100c0710702c1039043da41e040303507000d1100701860940a160440d202c140102e4548498101c4004040c00070740d1041029500e42100227070400000d4880ca115142e0022010b01c03003000800c5ea51110f0740c21b406014100803e29152810000300c01c4180841b01c011459400708148090240400200701000c04551030040c4440c1401c00c55034161214051000c80410000f607064184581c40b500b801040c3d50142c00740b40c40b8248110b03036140007242200c00107180c54030747c0159a050340c030510340c060b06050b00300060030038141084011100d03218001c6c0c0b20b0700051049550100051658070880462904444401c41242814 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 617749649 1250 617748399 617748407
    0x90209040f03271809050318030601090e0d05070501150609090b0402030c04051203070803090721020117180a0501020a090f030b0a05100e1005041514240a0504030201 73
    0x31800e05400301002d5000f941c40107080480d008251111500902d40c0c400c1c00d505800b02828800c10002d02c170303000119040c03c06c1801d8090700001000d0171400d540f410303a05c03900404112501220045410b0340841e0020740d1003030013800108203d502034030011407906103841c02200b86811a500180c0000c414640401408042d0311481304a05400c80d4103603e907007004002030700139009901800d4410b42d40013440425480040003200d8495501c61503640c1c907481c04a100c00d80742c000e86d20924040440ca20812a1035903255402c031040a54141c50700001500c01c013402c2c21840c900104043c2840c0120060740710306180170131410303201c240700e90005651166012401082808154483c034514140c3c0c2c8400e03c000303610301202640c0144a080002401d41e108403100c1c0042c81d45500003d05ca2a046050110b04d10070b421408042d6074041d40d05000f4090a1162040c800089109000c2450307503203262854545010101c480502128940224415035620a00f0151350310a0625801003000010308004550304 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 617750899 1250 617749649 617749667
    0x30307020a2d0b2512111201090903020d052a03041802090411030106120e031b030a02071e050d0206071a010630021317030a080c070804050d06090209040f03 69
    0x44070720004040d24241301c0a070110044460702840d903600c030510b440c0b85a8195041d100c4144584010312101d5035102c00d0800107050341303075042e00103000f8101d0500403580100f044a02070b0003111007a040c000050940000da1680c40300e8000c500d030204120000d450325000559000310a076440c0700507a0b0780c2890b0200421a2600321400b002800300307000400100d9084408009070007610a00071800000011540b802c51042100308038011158040c100d0510500201034480d08425400b12203003503444120b100d5041459003000703894000340840030f0140342000c1089195051010340b4407410441035548540d413010000c2c0d481f91814034240700420a0540c0100d501a50105114030700d542403801482190740b41d520203000c0d1101d1500006c0713005448400c9088003000303082c090400c2c2d80040d003001d90383d0340300d9019622684c00603c84402240c0c82007900342c22551003030380c407020071817405182405010007201c600c0408c0c0d944590b10075800c00561903c501a0f41f0451180d5840f5080034054075000c1d00d44a0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 617752149 1250 617750899 617750941
    0x40c090918110603150a030b16020703120c031205011d07050903070302100509100207060f090f1401140a050a0f0302070b072f0d11030307020a2d0b 65
    0x244041da00700210324a2441d0307110500c810345610340c0c2c0341d03140014628038101c55440250012000200017041c0950101c841d40545905a0f141d4588980c01e074080340d8403e094000941508609074600c01c00501819a01d42e41d2031103420b1103000110f07030b81c514401b1224240d015040c003900a01d6a69030b03120001c0d5a0603071003001820300031305041400c004207985880e10300009000f04804002406510700800035107241140c020100d090084200000030740780e10040c420390002c11061441c03003d200d40245900000d9810f081d110078135035840c0c84440340c003d10b80120b05034140040d291a1800f8011545d005150800303950300c0e41c17548c40d0b52550006208003450751100041601c14071004001600c81d0311115041105407800d0300c41014807002d4240444d80082c14244100e00c5541c006d0074400003c0340c6031170308560585031450342003118810f01e40c4900c800c580c50001a000300c030890380011503403c00e80c140314140d440d01900b4440751030028040b1508014080e9200100c000401c0118981d0341c60300b410a503 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 617753399 1250 617752149 617752181
    0xb0c0703080609060607021003090311030c0307112412070309052109100207030b0f0c0406030f02040512100f0b0d350309010e0607080c1602040c0909 66
    0x4466490050229402411092042105602241040c0d444005840803150004c04070ba001103000c2070090020030401d041240441c01c0890140c5e4030300004025102082014009180341c1141d81e41c410282d420103020b01584185170741300300d0603266201c0c2020360040c50042e40b407a644518400728003034a1500104003030101400c2c10120000504042410aa58908584928070b00c045010029013140109060b603a0014698861800e406600083ca001164011403100c14903480d000e121401048080362080300614080000f000100e110364450710403600035500044c101a150400100b40c1c45400440855a030300800d402c1c0a0b818552190128855010034100702c1100b145001c00d80e948200301c8050030f040740d2060054005003c40610000b003420200421402000305c518001030343c4c2040e9a204102d40c64107031b030900c080310001a404c4c041c10554035030b010300340c0d00c51700c1c00011039110a0342c3c0c5408003006004200183c60b40c0c000d4103115490f6803a1032108170706050f0b44400b25200b0040e596052 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 617754649 1250 617753399 617753407
    0x40b0f09130f0f1a06010507060c020a02120d1b08040302011d040f05010602010e300c03070f1b0608060d060e16091a0a0b130315020706050603060708010504051909050a0b0c 76
    0x681e000301c04c0b08d0b80e941d801040820307203c0c501d4009034100201c846011b034111244c464109a2903001081c51a020150b64452100e10707186450008203284078180028200e070410441440598050040da1710305c0f4158100030881440702030086410783d016424000040c9440b140144034150b028018418550a40350051003602a15a196410744c03651681240d00d0a504110510003140200100d8400c82015401c0f2641c1d507001c0c0c44c000c80103145480c42a110482880c00c2c0c0c04010a6007030b882c0045903169510661a900c944d802c0140c0d041c01920200c5156656101c903115102c02440040a948088075441c0061441c0000c1d280a60b501e1000010301d4680c810b00075002580c0f8000c1e00310941f40c1040c80d107600c0303402c00c64070140480e000f43c201a01441440d060703041039012940007480c9207445090b092145032211010700d5600c100a44411003c941c1c03040050045050590000740e10810049180d0008072240740082c1c21182180416039854004940130401d104021001c1c0d5004020f42d01d0140c68 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 617755899 1250 617754649 617754661
    0x506030307150203070302040308040b030103050d050f040b28020a1506081f090b04050c13020a0c030c08041715010609081c03060306020a0509040506040b0f09130f0f1a 74
    0x102501003000c2c81c2e1541c00300208030013170b00c00e034151030246502c14012030796a5141c0104c141c1c140c0003403000300e980c2c1c4103048040740d007030344aa01950038200070603c0c20360502d820500c8040b200d41202c014140c909222491006801410b400c42c0a803058960f00030700349495290404000500007818151401400c00d0070800c041d040029141000c1007095125080d502040000c0c4009005800c402800404881c0180001e1041c08186410960012203226251600386504402680031f2401642e020905801c0c0203404a0b0040710f407407900707500c501c0110b49801c6d00c031b12070b81000d03200c07601940c161581b06011107090956018a09030140c482400c00c050300314a0b20f001e4503920213443d140820076441003d40b0700341641c0a0303005080038562060f4299120160050003c007290020102903200b141002c000c0743c2c4905080c454050041c0014107408403100c0300d60701303000382008040d00c91517000010281c8680420b00c00c9844000081c8503002c0300c00703c126103040c51301da800000c04885460240a10030711003 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 617757149 1250 617755899 617755913
    0x91327060912020d0e01080402060c060f07080a0b010509240309030a02100b091b0408010606110d0c08090607020d1a0f070306080601170309030d26131b18050a0506030307 75
    0x1003030070801d11f0b007690b081c0c0e114808191180110381c0c568009100b1101400342000700d40302d0052040343d803a6110301031940c6001c605015030305200301050200d1020132102410341000921000903c180b441101004a0410300e0200140e00464116095420108420000710381c180700b030002d200103080c1e0074131145a80200141900c0340141c0303114603114203806200011181d01c0240c2d0020400300c002044001c0c2c0e5a40050309800214940305200d0140b504d04030030060040407510007454001e0085400c240c4d100060102d60b9019450584c0c1c401c4544c89900001506181c151501d01004203105010b400c1030b034100c80b24050042e005409050a00609010120001940c02e0440d030040700d40c2d440a50112420b5400d5120301400e407600350040c0400b50214030b0304018100721806c040c8884031041a1507035011941d0300707402e2311079100c2030300c0c2490500b0100309100f40800d400a5088015045650f44808010564895a0380b00c403210ba150400c00150170500d04c1150743c00401a0051441c02040d80e40e401 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 617758399 1250 617757149 617757167
    0x5090601050f031c020a1203150905180a0f06180b13020a121a0c0f0f1b330105130c1b0311060c091327060912020d 51
    0x5401503161003510300303503542c1c100000000d40e5692a8848544d82078418000e40710510214269500c484404888407454440d120b8400c20740c8100c0300c508521130501266001422000d000114642540d0100c01c034602c80a00078404030510a00e00190800c1d0540350034815558140c8032100c2c030004007001600400c0d0220340e0f041d0701c0310740351580c50882225840041c1e18107201790001c240f881d00f24102d41c010050505410130b0f19880c1c9240c8002d950343c800d000c0c06464890303050702c2e2410b082c0a114501a00354200c0c05020441008890034201090780c00e00c80d4644800b40c045010071342d04100e610869810b92103120340c240700c0007811140c282c3d8101404105c004a101c400c004001e66504240d1001078800d007018806080c941054100d800000d05000307001c80307012480941c0d14040d80c4081060503803140308450318500c0c0034200080300380300d0315014401030030091118030b2001000c00c1814100404009054031141c4030720400210034815085c190406c0c0307150044141076601011455103c641c0200604c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 617759649 1250 617758399 617758409
    0xc0507050604082a011d06090a02090604110a0903030306090606090501080405102405090402030a0b182413030e130908120f090703020916050c0d0801061205090601 72
    0x10039038900444800c60b030f40740100c0c031200000550300202e00a41d18010340003481d42c2c006d10701c0c1c80c041305402d010f00300e500e07a07000380c0f45981c40703074401c03210383c001400c0c1081c400e507100d203000f0f100003030054490403032030451361001d5040d06c001a05603005108168241c40b580c1e0207400011002c014490034044042c21003121401101d0501100100050420000304428034903d55995003e2003d02c030403500082c441d442a00c0d0414550300d0303420011071b035820a00d00640c86603170001d0007051122a5620b4035840c2031000391440c01a44030b42241c0f540344c40010803103101c442d207403d101001c02d02c203180c040ca1445d03a409000420328402c0300c2401c60103e6880441d4401101040700c18500110a9084010041c489100020300300354000c0b40700b0038502d48080074148104070b070070300c6448166182820140ca484013030100035070081c0848003081c5205011390940609a07401e04080b460403903120481468040c582ea0b0307420003c2e644500512005902010443c2c905800d580280400c5c24031402094403100b050207a = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 617760899 1250 617759649 617759663
    0x18010e010303110a260702030d020c0a08030c060103060b030f0f06072d18090f050108010c0c050a0b07090b0d0501080c030d091403010209120106050906010f020a060b010905060a0306090c0507050604 87
    0x11105c050301c0b001201c01060340201102c244910120001c3d4480080340b0243d40329910032040010804000300c00c41d201d0030100c002a052a038256a01c6c03400810b0191001c030f42501c01c0d613410082410f402c01400c4112015100113000074034001c40c0003000080c9406038500c1c0c02d500b030304e44103040c0100c072004501e0100300ca040c10084160400a045012016039014149190410760440740407411548094142e402020007030002354445203056a0b0031581c46001001c0e58080003460010486900c0c5164010a00e03107004c401c05c50341c54001c11120b0f001010350018499903040100105401000b403403600c1342d015006002d030484034100103001c500040c03080018044843c0c0c078161445d03030294102c0f510b00c0c03401080b07281c6d641403550703403140281024002c140c019030710070021070001c0d030142105042d0220940c0c020090b00c1d110b40d5841018003070301086103050025485010801d80d50f4200902018560b0b50f4000a0080c6400f04460945030f50001c0641444410042d0002188003c00d04551240c0c0040c0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 617762149 1250 617760899 617760953
    0x15060a030b0c07080f3f04300c0203010e010e060c07050109171305030c0102120705030412050a0c0803031308070309081902010816020307080f1c06060e12060601030b18010e010303110a 81
    0x800340c540926985840d141d040c0d040c03030b88d07542c1040c1c101006040c3c03240250020071900e00d4444165080b01c1c02e680c101581940b1a100088040032100e0080c000c0c1403042001052003000d69444800030350011125030400e41c0086030415407460440450001814201d000340707210a0301100107500d500b00541c088036800d03000101581440740410803140145070149000c0b501c41514204552103030b08007082110411640b070000034815100000340c0f8064040700984a400700c81c03941d01d000d129800170300110140061081c0000340c071003003030104256232036604c0c01e0b88600300c0c0c0920005001c001c3c01085c000a00d2440407803400019400004e80d44d280e58042850341c0c0d0781c04c0d5510741c0540c902a1407807940c140c12002d83e16110585590304820103d407000e40700c04280c5034051007004070344000b070064240c4640c41100010f1440d8030940100300303c0f402c0501134605030550104000c2c00c1d81c000741c000c4141c003196071004104165104a0803003418444502034a40c005069640d1405400c408055800e8078030300c20 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 617763399 1250 617762149 617762183
    0x1003020a0e030a050f06010f26160314010b0d08071e050703051006052e12020f0307020f06040f030311040b030915060a030b0c07080f3f04 61
    0x2028041c01c0c10070080c1141c0702d0b4000341ca44a60340c0d074032003040181136001d03840c00040c00c118903e1035082a14441c06410b0034a818010f891607a80d82942c41c158958451070301e20031041118151136402643c040c00b108407040400000060035120f500880ea03029104480c03030724012400d0a02543e106a50012031300040207a500445da50b400d607211340182c958003d40310300004000c8000742d040f03003428060b0418009075646000704041400c030050342c0000501c41d086500c05040306908104044007560500141c04084000c0000484c0c100f0112203152182c0041031080c1282c0411074861ba20080100400251400b036503040d19005000380c0040034151030f114001026090842610b0107030090170002522850a4580956100840381c0711404805082000c16980d040c00310f00c190540b030304502c000b541500c4540c00107090783e0000d10180c07890901400180045120000140310171111814030301c0b81e803503e045d2240e040c401c03d500c03410ad00e000150112039688403a1308241d40d100fa040498644003403284 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 617764649 1250 617763399 617763407
    0xa030306120b012d0803030702100605130c030f1d01060b041a2a0109060e070b12060d14071a0702150a1403090d0206060d0503030105090709081504061a1003020a 71
    0x1004d5010003e0640020114070a80008080e5200e40305580c200d40055050346400004c445890150719048100025061034007000307a04030280306003641c5400201c02100c111107000311500302c000e8204202481201124070403007400382d28003030801c000080d86094503003196070010401001e029000d285012030b80d11860f109000800c0e004800105049440c035540c544070600a180200b0200c4101d0714001c80441010000030301c1e0780c00e6030061007607189400595440300d2107064005017016440b41c0c1c03104062000a06a131401642401c0c0080146586420309072109a40c100320000c02e0f1040b1400d004010150743c07a00d499000c151603240b95195242e82c01030b01103070501c00d50341c400c26a022000080c0044030000181682002036030798240c8d2200d48481c2c04004c40b4010f40400a400c42d8004d200520403482c01f200426080302d124140425101d66071441141081954115402c000c01c05104010511403d80200803200c5142c950414015140c00005841019084040000c041d4003248801185001e = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 617765899 1250 617764649 617764709
    0x310081f20071e170c0d0905030c0409050f10140108060c1903021b0c01020d03051003112e09080a0510050c070209240d03090e270a030306120b01 64
    0x401c08110280c51140404e4180743d00540359030f952845540c501490b41c40c4a04005801da4800130007a015082c2e20401700030103030500328410386041c0982600c280c410041002904460305400801286008181d400300103582e44c140c0c8195600c2d000141088080e040c1841140c282e6244044902c01a0b4204502200240140780c445042c240c4e40b403840f8400314500260665100b10260b00303c502c0200c00001c100d099841c2541c113250000813511080c030000e000c885041c3d403403210140980d1129459000032403404401c60709080380b074410400c40342183c1940661f0840140c02401d004100c2e44995a0741c0c44d80d501516604420855070310000b098505043e402100e04680e001003100d0030034180584c0b0321940d80c00b8401d40d800c14030b55020000342c86040c40e1000c0684030381c054071848511898510f5100d5075440003012604485104500303154400d00c04002035020041400081540044d1403502800f1038485800040b81c01101e034010700b00040004a0faa41501d10709a00901030b886419000c0d260010 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 617767149 1250 617765899 617765903
    0x1b07050a03030f0f2a05120f030c03150d1401061202030d120b0a0b090315041a04170c0c2409010309060e0304060f080a051504020310081f20071e 64
    0x703000c03140c0c5c21141c118601808010f0082d400d5645d20b80340510a0016403060704c01c0042c21581c1880060041b0746000040c42e44504014441f542c103a061034001100c1d1444100700325940f03000da2314085c504403024440d51002c0d0181e1540507101401e140c000940d81e50403a0f00344001c00c50140803039600c0f122a83c00805c410701c0c3c003800410500d5119102c40600340c03c407030340710b90003442040640c20555079030b802c80901441d0003c3c502400000c90071152405444001c0050354a1800c0d240c6924404900340010000030f1503d40150030000f0703001080005c041c20345000da4051010300803015110481080454150321000d003400698200e842c0741c200041d10310a0b5180300c4600020170001582508440b81d41d9071862680d036240020b6a030000c035581151703400e581b100007507204035801d0303401418550b0081d90803078a0f00f0407000d1820f5888420307501c2c0100315119002d21421080031042d500c005030260b41500c40200001824a440100c464550340c040c040c1c019001c21580030b2840140300b860300d440c1201907 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 617768399 1250 617767149 617767187
    0x60f05180a0b0c0102040303031503030c02060c0a0b040b06130510050420040303031e090b06060708070f230a201f020606010915020a060e0f031b07050a03030f0f 71
    0x403c50500a000b508188000c2d0003090070814644500600010b40740141d0790325440e13032140b0b48120f40a004446c1c010204440040c40b03010742c2d0780c001c9401c004240f8426889401c1c880800d24003030051042c1039208010a03540b09080009012241400300010030940b03070b05540c00140707007400c408030360f60681205008158250f800074011081c554140c0000184808a1500c1e417144000b80c07208808a50040b200604980b1000e004074200f031401e02c0040c001280501388081c1080301d2511a665880450b0b5001ca64008240e00e50400038540400504212205c040107408a0740e040e440d0400b070b0000c0d00e030582d007000b03a001000d41003e0303503582d0500c1c1030300c0c41c68031030608944050400a940e9004c01d5800501007440040005203106040300100d0380700c03156a010f00b20002240c0c6ea031101030f1640c40f04512880c09404603286d401141040500600308401000403801c03080b205051742041001c1d0485805540e01000500109400c0030907071f40e418286180102c90a0000c0500f110342034031100010f0160 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 617769649 1250 617768399 617768407
    0x1f0b04021c0b0d2108090a0f0303020901050904150e10050f04050c0c0604060b0102160b190201021b21041217040f030308041505100b070804080d05040e01060f05180a0b 74
    0x80368102d01c1d55103030360300c180d15841a940c40b04890340782e45811f4010001c01019068070120f0002c3d00c079070040c141850060512a0a0111500004050319111110150201041d001c2000100300c0c50a03965000700c8090383c019885400c0102050314002009a0203001e56159000714543c843d405c0b080b207050840540c00c1d9492030810b031500101500412094a005224044250f00042c800b0039a410072503400800311807030305a00440004543d900d00d40710b04259542032206c070ac04074141002005641c1c9007003014105029043e40610360b00c2d03d4014100840d0390060000348170390300e40044544021500640184119401d411241c002489184c11907281080402000410180c222015038092441080d03a0310403280040d140703000f22042100d034100b07004c820389401c100c100390b40340003410614000c4805601d0701da1180c145500c0c00c10325a42c00800500300140410154200650300c40c050611454820b901051101005003237000d240480380c111203510790100c290359a1080058020030001c4c542da529 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 617770899 1250 617769649 617769683
    0x2040b07020630010608220b042613210b10030203120c010e01090506130201020106090c08060a08010c020304050603060f0909030324301f0b04021c0b0d 67
    0x1c41d0b81c04c1c421070010503e9240403a000b560070100d1f140d4600442018503050b458541c0f02c4e070f0680074020b4015a80d8400900f540c0c4c5080d100440018a4043e62100c00755540000907a968901030841d4002c0040200c4c066040d0451100b04d2600180b194105203c01744a40360750289d031260044036480254148900707502820107a11300405030807403a2440008000f9908812145030a913004284001c085402200004c0d0883d001c038146014054018400007c02503100c2400f41d04a0b09400b0382080410204e0341086000d1618007007032005000f0800080c020b501a01c00c02039560b01550103000d00c20708020000030100d4030f902c4800038010100038829055424110600354490340280c0d03240f40c000d02007202480c1d03007002d403070301c0e103421b00c1c2c070103400500c01d2031384458000c21180f81c600000513000030b0705a036101c038410100b0204000c400386141044030b82003400101030440b0480e051701d5005500510006500c203003007048070020400c00e100041451001900024410800c4980003055141d80c200c100070 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 617772149 1250 617770899 617770987
    0x61b0b19090b010e1f0302130f0e06161d01080a14100905010803070f06090201020106150503010936140d0306050411040b0307030e07150507050d0302040b070206 71
    0x204807001e6800c080c4d4151201891005091010902d988201c500010b081005003841c090a10003901030341400201c00c1c00c8045040251005981c144103140d20803000e00020000724500d202c0c00460b6814440030110307114219600c090201d40d080d0381070080803000210f82e840c1e1600007060500c1d1484142509190070001c0044409540c011040f03070301e15000010a12000c004211903519422484001403410581c0e16400030b4102180c0884c115503c40e04000f0381c4c40002c40c0d041c90000c0158036041e0b00d0f981081904c070100c60b107200601c203c0c000711100880703281c099124500701c01c031980030079901000950704003a48900c82d80d501c80201c501c90046405034447e0f150b4400d8054a038200c03402d01181690141c0804030380514090304811000802c0401d40c414000d50001034600041c20680d501e0580c2e980010002055064070140801c00001c3c5080c100641445142207400e41d5007411410035080c403241d450310b0300074004002e006802c00520803042005541c0b00703904180925807802d00c10380d82c41d80101 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 617773399 1250 617772149 617772151
    0x501060f0909020c0a15090203030403080a0e010219020d05160801091a2e0510170f010e0106050c01020f03280b06030c090402121f061b0b19090b 64
    0x8000503519041c00314140149000b115403203003940c002001c50760816102c441c101983d184884200903510307030300c0e01c0040c0c90030300203800158050004961030340050007020700940c402400030790454018400728803143c440c0d090051501070301512100c00400745842c144e45802c0010f071071884031f40409000002d071228150010400c0d00d00c60340e092460300700280201d11040c0010349a819070451041248409880d2440042c041148218100403881e503444000c6000e08600950050010b101c64401d15141043e5901041e0081c040d031884084540c90074010100551040c010b0b8000c10030001420030018200350196040c080502e04029580d041805608014980d41070112022240d400e00c0804194072511030207004100141c43c00d0324556410203d81d0840d032048081c143d0ac16400e1103c1c4480c052404202c504c1030801d0844c203a4402002c050610704d000f0306903c039008120302c10803001c2d0035001800c84c40070a140d00c130003084040d4860343c1080004424661811030902c3ca480b95000c14009491030507 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 617774649 1250 617773399 617773427
    0x501021215280e07051204031d120c041a040e0c09280c090305060f0f1b0708070c120614131a1f080a050c010c030f03050415050106 58
    0xc10441e24a50640910603240b1050002d95503034503504001502444811992210041c90410701e00141420a280c0d5010240e800303030b0002e1645002070f030550000300f8a160424904079203070410b40b01c4e40071000f55582c40f00d0704810b000d1616540f02042841c03e10960b40c43c2004000d00500600c210080032583c0e8401402d8640d22401c9450040b4069a0403411402c08928050841940110030f03415940c000d02039403a40c000c20489500000408a03805024850044000070702c00341080c1400d0454490300745018203441d09001c0c18151400800007801c04480e6000d5104216a4580c1b82500b44202a505540c0c803214034141e5811001c406c100040e440302c510f68040840c011303007646400c0e904079091030b800c030001004090040158107400e0901c07210360b07038000142c29a03c81d1200002031642e00e000925030000003035034405509441000814801140703643c000703182200c0480b01c261002010000c80e00120002d01d581c0300041000e00000d0880070f051034400308401c0c480c0b941c0d90000205034400c05640c0f = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 617775899 1250 617774649 617774659
    0x6210501050c0703080c03040804150503070e0303130509060f1005030406060608061507051c030b03060c12040807080d020a08090114010803030a1505031222050d030302070501021215 80
    0x3560745a8107000e0b5a10706406a80d6000d25686c0c0d03a2855000364000340090b10240424003002403400354103151040700e400c0d05e607901500c0741004038025100410101c141403186d0400e0207154070400c2c00c0240c8004840089070701e0f515a0303e4410115940000041d0f20f583c12014050817458000d801800442c00b40e4490070702000515030310401100c3c1c6d000282c5030154040081c0c1000060454918050585030340500306480c181c0400c0250184010038681c0e0354008240c6078407a0744104d1800380400f6602001d8640d01c2460441c4041d0754010106005000400040c40440c02e10300b23103d191000d54001d109041411996900300c410050300c0b40354102c13500c1d03a856003400040f0018100407041c0c0c1d8120307500d1100031411501d81c050428041c04000a0072002c0c3d00040d0800900c50703038100040040200540c20865030350100d06200310b000b07501081185822070075105c0c20002510390303103251606103070186001602c1d00024642540a4811000080e82c003805017820301c000e090080182080200007114 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 617777149 1250 617775899 617775901
    0xe1512060105010203030109271101142a2104050a06020118030f140f0c0705030a0305120a06030609050607020d0c0b01120c03080a050d0506310621050105 68
    0x185155940001d00500707006030001e00c010800300010760810381390030309904907070402e800045600c81c40050021905807403550700c50503003002e41e50b0090040642c3d4400989140e1805070340b00120800440c3c03000b201007001402d4446009040300500031074199000aa884042d8070381c0ca16401052034025000c0c0910900100d040000c901e4014420766510468022501d045985151416074940400d401e112050049a030904038090080794010407880c5038a00029413a000d00b40f40701440c0244542105002e82c1c041040c8102082e0031400360340c100c03074903d65071286079503480c100c41c000f901842e4402000c25040100b501c1c108440454514480c6185070f084030840c00860303100319100803a511000c0c0140d10508018445800488440e07800d950040003c03805c01607607940d98020030740c01003001c4000a000445d01d414400c1280c0106034010604483c00d5440c00c0042c0f4054000002c0703403a0141c04900c901ca07030381c82c0086040e04504010456412030850a080c2d01502020501044400f00c0d00b80d41307048 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 617778399 1250 617777149 617777179
    0x1203021615120614190f08031b01090f06021e160b100f050f1c0b15150f13030c1503051b0a0c05010b060720010f0212070c0e15 56
    0x2c410f90382104c2d582c801200070148141c0a0204001c000c04128074541c2d04480003144044085c3e113158000c003614401581d4400168003001c00d80c1302d211144402c1641404d1f4008040744d00c4a41101440307801c18070050361003850000c0091290000083c0c00d03036000780481c07036081403501016a0400a0301802c00d0300225a030b0100019040c00440c003800c000d2501241081c811030078180c0030740e4400b403070144c0003c4800c0c1c0d40c8050341e900301341c41540c102c41c40258030080020146211207900384d140800c0d2003030900480210901903a5001d105184106640082100f003410800b42c40c140009603044202001c640d6250144000310700c91484011000c42d040c880480d00100824004104150020320380c01d09042c80e0141c102d406e901a0f400548041d03480758054080c680d00d0200034030490740b24100850b10f05065a050b40004201000c1441c140181e0f811010021038000c608000d800c00d4040c0d042da40c034801d50be04041c80f000359421040707020b001c0d2820061801070007031003203081010486010b50103580003 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 617779649 1250 617778399 617778401
    0x60f02150108100c090b220905090606060d1821080412050a021203010b030f01080c0108011a22170304120201030c0905030102120a051f120302161512 66
    0xc2c81400d034203038040001a4100c030300d26400605542201c0c6042d601c51035440c0303055065504100141101040001850040500354500180040c14040001e219a00c0c1c0010819141c0000900325030190b03a000548107aa102640d00c09000c0f21071000c02c03044800c10a06044c2ca140106501c40030149805480f40800940280340f6140300c0e84d404001c1d0080403509080403a00b40c0c10803103009055100d03402d4902c4a9140040180d4040d08583d02080d80300c0c07a00c1d04005440c1081030f403009059812443c1c29010b41e0340e2000649064580c280c080807460104000c50000da03111b1000300c4800000403c2494007480200c4840300e04803070050703481240d004404c64045490f880385124040b0042400051080154006c3e0031405250300385003031505116a9980c046402c6ea4005c0e080c20003420004020861640d45501c0303819040179140200b5031000307000458200d020312143c045c855980c0b03c00c00c01710701014030800c42c0c0c000482c400c0144401d1142c1e1031040d04440044246c2d544040741c04044c04403144621 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 617780899 1250 617779649 617779651
    0x90b09070302031903090506160c0e061309050c03030a05031e070206180307060e0102030a05070302040b042304020a020f0606060316180801021602040f0608060106111501060f0215 79
    0x4001c2e180d64076001518101c02c180c191400c81c144501e81b1400940c13640c6e0400035054014884246842c080144c1c0f801c0316202c08540c2003a641030f4200c1092100d96129621142140c22800c3c1001904045500b0010702d461a905149a4144400280400f005520001a50007000c04940c3c1d44030584000301142c549060448604c0c1c0140c0c40000080d8401440c49920b200b4840d10b8820f8030f2820781c20340c9a01003940c00c0303103c0072801c9a40010500010044030321842d540504585411410107090000103043c42c0720714440c401a091030040c008041180c0700800850110703004204640e1500c040304041e440c3c030004c2d80b0104607401800001889420420100c4c1d03c0380301d80303d080407008202050107550301e43c0171030b44c0215810300c044000f0400e00000d02c020a070070400540d442403205081d10410055401070b24042c964103060035010481030b5800141c00d415289503082407000c0709240005030b4070b0801d4104c0291074155041c40009440e50301b00710002001040c56003503403c41c0010407980192000 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 617782149 1250 617780899 617780903
    0x915040b0d111e070f02101e110d03090206040906080c030d03020a0906030e0307050d1e09050607020103021e07320a0213060b04140102010e0d0f08040204110c01090b090703 76
    0x281049044500fa01e040010010148207404041c0903101c2600451340d419000c010741c2c404100c4007070104100043c18003c07140d01148920301a00d03000080071000d5100c41111105109054548410704219914401610041c04898004012680c1d0f40c540304c540e61003003080450f004c1e002e0103502424461081c021151544055111480050304c0c100c8124000d00498041d80b5440c0024080e440000c1c40c02d0103824810441ca0351600d00501d8403100642c0240401d0f0034140a00c03070807503030820450300d0300f8058540c2c581d02401c0041e1074506070076220b180c0b981c3c1c0c04403400c600030002601d07004203d15080d204035a05611041c0014010a0708000702502c0440340b01d1b07070f0340c80d8450202e42005141035042150707010081794010504a9599402700c1c0b4a4105801140980903120480c43c11075909110f03000c140b0b2071007030040111149044001c1e0195151594803410400200000307400d54440e0b801402080c0001803015582d48504856180244035020b02100c100c0f0003080403842d455400a600340a0325 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 617783399 1250 617782149 617782177
    0x1306090f0e0402100e040513051606120216050703050a05120f0d0902041806140709180902061c050a061517090a020918010e010507080103080915040b0d11 68
    0x280b1203408029241c3d442c0c1400750200b25580c2903007101c940f134601500780034203514030f8100441c61a82c034009083c00310440400c1800c42c030710302c000c004141d440100802070040c0485c0042c2d644443c03103814a2012030601d0068400d01c15018000204800016001192400f8405076003044020700b40e8000c080c404c3c0540c84510340018000c2604880346a8030640d445c510061000070144c1590050310089180c070303070050380c1e41075480003400809580002125030200f61480c05044043c108100481e40311001c042c50075115558001000440d1540c10440e03540c51403002d0310520909100b8020350250108941c007928407420704c0f0001496425211045031103000e0745d110307401c1c81501142c80b0050020000d01c5400c080c0705003642d41e40562a0103e00c107005440002e0300030468203180c1080d0707003074440c04041010260300d440c0411142d2640705040300d056950002149644280d10b00004e56030580e500340700c2d412003034000340004207444440000c05504420080900102c480c401800c821401480541c0040c8 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 617784649 1250 617783399 617783401
    0xa0c0503040c030b10090e0c130b0306130f0629030a03020705060d0612030207030210110d08130c0e0105040b0307030b0106050f120109020307030501050904020a170f031306090f0e 79
    0x1d13844840b882d50145a01500d01011a035031041c50381614034103403401d034081e007200665001d2810075030310b0b120780390314050018404601010b021a03943c02005001c0c2102405001c080b80c00c0003544100b2001c0160010810700c029000091503a02020b1454121907841c4507241e581405030801140c09900c154141d005084920320700f40c240b02ca90740c000d00300c80c01e40c282c0d00d0300c000c207031042e514041e0760f115802540148075050852060129815008100d541800101300400417890800544030b9262482480c1c45407140d00e50103000a8510400303100102841190400071441c0e0142c888424103e4404440c03c0c0004100c02c020715448549070700010b01801c441c00d00500420780190004d0034445580b021a51610802d40d9020b4245003003038018058460300001800800c176414040c950151a040350b00d0788860a1131ba0000d89099280c4c402c9030740080e02d440360184510000d020f000c13110020b5074107882c0d4440f00e4031045804410303d402440c0204080203c0803a0700710b41c280b09a01511500c000f00c82007 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 617785899 1250 617784649 617784653
    0xa1707080a02091201020f03010e010b04080601050d030c060c08040b0604090b0c09190305060103200102060f0c040801090302030403050708010b010c2a0e0f06010e010f03150302060f030a0c0503040c03 88
    0x303980b00c0200c081c0c105110491020700040241b0007010652043c10280e0749a504102c0d00186203141a440000c402c982844148040c0d003002c512181142e40c201c0351301d420240c2e01e00c2e044d0b40381200e0550140540b40351003098a001c50300320121500c0781d07100c2c0c9580003440d601c5030104421903c03200c0001d00240803203000144801c100030002d08001034010701550307028407800c0741d920180b0900d4004813020f4000f900100100850b10405c143c40d1102d01010844000c00a00005c0d500d110081c441004107142c1c0c400300b05d948110b08201c40282101d44000d0240c05100d04010b541c950082c4001c07141403141081c0052440303010300c036803440004143d50380c4200401d00c0e20349a0020a42e64510840e85800c0d080700480c800070f0650000040010b1402c000035860718800802045400601090610080c904811116070380103d007504d0701030361818000303a0010502040100110700d0b41000b900803900090b4540f0080303850300a940715240104040c0001c9038a003500311244e00003640c004140c40c10700107003440 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 617787149 1250 617785899 617785901
    0x91c09090914030c03041a0414190312030b011106060109060807140d0501090c020109050d1d1c020319031b110307141c0b010b1b030706020a1707080a 66
    0x40103002d000c0351070011480d2004541544c0c00081030b228542d100142c2048016148000c240d43d48200701e8515040c1481d042541c1c070340c0d003000f40401c1d11030340340030641d030691030004c9440202858001d846288400c4549801800031f0020350b00f13041c0840c80100341d071a07906c1000035a20b4031810041e941d03021101d14058041e0344181001c1c00107404e201d403401c282235220207110094044d90106000104143d454a400d80c0c0480300c50000000c00c59060007482c1010444c002901c0d281d142441c41c00c2c100e0140c84d4840000c0021711700c1e503078036407188807400075040050030704000d900c0c49802202603980d511224101e502000b0200c040c01008900707124100901c114000300447d0003a07001d80c2030b0103055810b000000c0d007014101d4000b0000310070744080241c0c3e542403103881046024840310341c401e2901d105441d40548100144200903140d0030005030100d00508031072580300c3c55984c2c0021a0b88138002403402c030010f0340260040c600003441419441d0005030020103801d00410603034540300902e031950042c8078 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 617788399 1250 617787149 617787161
    0x5066304050a080c0c180f0c13050307030f0204060e010602210702040e1c05090f04110403120504030506060a0b0304201c060e01330306050f091c0909 66
    0x500c907401098002008260001c004000c1c04c1c061300c0241640b8018034081202d43d110550300b81240e41c54080422805074440c038070031a08544230200c01922080f545140c0214280346030400d41c0c05000e000300c0002000310310804603da0520840d400c0c0541c03078942030080182c1c00244554001130b030250405081d0107906d55012100b00200ca620545050242c3d0041019280c040031070518a9000090106101e81180d03102036148a013882c1062514441d600040e42c43c0541140c814490f6075140310040e0103c1312101114000c51340484403240c426140070020f8500d0304944402e48890155500007030280c5070001016050369001d031071050a5440d241c84440c0d202400041070030320420607500300107050307407802e9041e18503031032036004080c04240f01d14051090b030b0501122301c042c9038140717202e581200d00c090f2060031400407000380d09410a070072202e01e55016107030390388060302407450202400a9010403640d0103200b9a400700441d80c4a00c03444044448422802207403500080c01100c0030301115085811030 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 617789649 1250 617788399 617788403
    0x1201120204090f1104050606040f0b03060409120203070c0909080a030203062409040b1c2a14040b0f1f0507080a0e120c0a060305066304 60
    0x440c001a0303969420540a103d0081d101e04d01d01c6200300c1030703d02e4280a115030101e803d80300c440c00d183c42c03d5007850000d4118080c5001c0000c0c040001416600d45600c0050000d4100345504001c0400c0c100294a90744144d81c04d41c2c02e0800d0031808290b06600340032b01c400299001025910b0203e214500320300039040034045070391203d400710302c0c0415941c4282c043c011425051b0403103559003804408101c21110306003400e5004a1078420345c00340000b1000d41203404190080f104401c20009950050600e8080d080154840040031030042881d2861020030b10840b0703002e031001c1000914003c10844100c50384551150320200040d40040381d04100000314005c0350040c20901e0504803a031382e13604801c0e00120854000a0751070704090790540b80450a91102d010442c024000d410400b0700800c210b42c4060160006254440010420f5a101d610050a455468080c000e1014412207144a40c1114620300c404804c411200246400d50292140f01e0707840c0740d80303014010071400d403500d0101070300e20041c0700b = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 617790899 1250 617789649 617789651
    0xf0d110c010f0f1d190201050c0109080901170603060a150305031c1b02100207290103050705061615060b0708090a0909120815060c010501050a05061201120204 70
    0x1a803903035524240150000102901c0e000b003110350141038000202c1d05103290110440108030800103500001003154071007100120140b041c40d015500042c0c50074800c145400001d0740c6810405400d1100c103501070100320b202603880c1000103c40d580c1c3d012821000303507011a032540015000c558800030700d071300015a060900c81d4006c50030b0740c1c075156036095411091031310422a181c02c110b4007a19204c1d01c10180ca150305009508442c1608450082d6034400b50a41c0e400c3d2181e000a8171000c0c03120241c90416180c110300c1c02c84414500b41e405411a000b400e01c812100340c850a40701043d2031806030b05840005004d03858202c00c003039a40c0c84001241e5640422801943d030787e8400490034207072001c010000180903c0b000b0f41c2d549445000c0c0308480c41c441c2e10801c4501e140c81511800a21140c00b0442807102918003000c65840740607001c000d05091219165100500140302c0480c0001904a10304982e4202e94084503c3c0da40c0d0140405442440000a1100107050040c00480c684610a02c06d0a0010704 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 617792149 1250 617790899 617790907
    0xc020c0d0201030e16050307060906020a0b1306020316020d1d13110301080a0308101202090a0f020a020c010306080607020303071808150a0c321201030b061002030f0d11 74
    0x81d070034590320220018901d4805c5006004a0908011060003805a0719050000600d0b2000080d2905055000244450700c10408a1034649800056609080d0482411943c03801c1c14440109840141e000700c00240c0649045041e0305806004600801d0700840f44000e10110401c0400444014118583d04420f039201c2d001e9603448030a030f01541c0031305480d100800441c442c0d41000303041c000d0010803100500769061400d010800b202c44808032696410b66440d091611503500460141400c039201c2c0007807134808070782c9000465002500352612202030700c040011075100d00050303883d05002c440001c05a4820000700e211548103880806030500c8120282d040251030b4420181002c0300424070380c0b81d960b500c8041c403941c0326503032045c5070718803045044c03100203007508071050840c01e801d0b8681c2c5103116010100e69840030030503074221400122001c1c107c61542d03031a8500010411010f0300c80c00d020726000d200b02440c0c94000021540b01c042d480c03c001d400c1c00c41c2c1c052500054132020702e03400890b0700240 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 617793399 1250 617792149 617792171
    0x4031d130f1d07050909160302010e060d0c09051305012124020d06120f031107051804121409091005061306030c020a02090c031b04030f030f030c020c0d020103 70
    0x1c02105070b90400102038840d5a03d02002c0140c00d201c041c020b0b625540000c0c071182c070010b0800f406d40c01180d5081c01c290814132070031400200140174080384106aa8201780d0f103591039a91001484054440071106510a030344c4162441085034000d002c1c4500a100910310519260010040684040d00c0f80710060080c401c130b01040c2c2560350128004000d4180c02040c1c3c08461003a40c017901c0040c01455403c1c0382d422805448002d440d5400b14405400e100c440b100c41c10084a0520854000c1c15001d880241806080d405514044400301c03001d4604004911090658511488040d0451058000b400b812303d007104041203c240c1e8084c00382c40c0b2000a002d0300040759251100900042000d43d03c40340f074009d1030100007406641c0e00c0c001da6001c42d005844071030700580d1080e0013541c0044002508907200c0e555001c44201c02c60000011764000c0e1800328000080050041d80004d119201e5501c0c55400441500258103484102ca20718001d0b8000c00316006881c240b00291100780b0f4014940070441001d10 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 617794649 1250 617793399 617793431
    0xa080309181815060a14030a1b1502030714010207020d1709040f09020f151c0204081e011a1e030c0a080f06090319110f01050f04031d130f 61
    0x904602d43d030300e041004000c03280c5005041030009045d024803050709050000000782e02c403030203883d00074000b0541c20841d114142c06d1488180241542c0d030000300682c1c0025a010b9030b681c201c5803045403a40103040c203001001e6030600a4898940d8090101102100c1603942c01e44039180321001d1840c0200c013401400103641d00c0740960b0320301c10741c14000010486640d00600800d03440400d000c03070251409092083d00700c203401d0101c2d80b003d2501200b542c075002003103441402a00c40c2e42e11040c1c041c41061b401107844021041e0088030901c07080b008000021100c603440304404090710010b23912a550942d9180d005510b00d026518100005043d00c03504001038000925200040e0410000340c1e11514401340756242c204a09500810800c0056003848503421006136424074031100d90040155151030712090708010070101442c017912200a214501e0040c1301d000b2a120116000e03030000c4d0660014001d0100c54075018041c1501c05454810f20606081c4100041d0a90040c017124840d0344100b00d00c180c040b4 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 617795899 1250 617794649 617794663
    0x20c0111010207050712050f06010e130609080703030608070e0601090303050c01020d09050303010807081c0c020a0305030a0e01081e0c0a05040905090319050307080f0a02270a0803091818 82
    0x1d1b0164201103e001404c00500c3c05448a4904e840d541c05040188201030300e818042c0d82c003400d031700c5071003060a0309490200054490180c005010640205400042540540140094580b10b0040380c0c056a90380f01c0c6400001415101035001ca01040320a00100c0d00c00c0c030051404698070000503180c40c208924003000c8813081501a129908007000502070b00d0300c02d01610004104580040100b90000344000484203581c0800ca010b100842d115002107441e903041800003035802c0b20540342c036010505000f0301070403c3d00400c50b0002c0d510800051814207441c610304584240c0603030102007650b07040c4048500b980f10403c80d00610101f4000041d010343c00b405001e01c81c606040165455140c0b90090940106a1075866002d01c50b0600c104512558000b409503070181905400c0d01d40c0c2d4035450a604020300c03c8011100e40100071400500304410344100c90782580f0400d0701c00608441e0b80320215910b81c003c02036084d0b80510354280103441d555110340100c0d006503081e80051225122980000e140c049 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 617797149 1250 617795899 617795909
    0x601031a030a1101021009020a091d0f0601050a0f0303020a1203020906210a110f03070302070c06031505030601080d030207051c02150912030c030a060e090a0b09010c020c01110102070507 82
    0x26842015003640d45d0501a88110301d03d010018400d0518550000d1401d50f2140034090107941d5540c0c405107a031489921445001c00e0b407406540d011001008650b403541424006d1030f0150000c01d200280040401c0da0001c11039416a000e40b19503119540c81e10641e20080804000f016001d1100103203e070764100080002c18404100e10485000004207445103142c02032140c10468a03007421082c0f046102000c680000d40401d04e001d036242c1d1800c005500078042c0ca107000c0c00440082d240421000e0b05503010840b030030741207411541119a076104055607201c1c24042c00c1115041120340d040070500070b4010b808480c0c447c1c1e061350b071400001940102c0750600340d080c1d107005a0100c500c0d0340304080103090140c0c001c040a800380c00daa684501d442c0005100143ca4480d96070000000075460710110780c8070740d010340801c1c07000e050306040907642107035242c1454500386e40c5c0c00d08040100748808014880c200141203250060403440034108015600c1000b4504101c0c0695001c002c1c19000420501c08007004d40 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 617798399 1250 617797149 617797163
    0xc0b0403120c141e060a05070507121809050403030e0a031d060c060c0310060f0c030e0103020702182403060f070210050106030219030c120f0e030301031103240601031a030a 76
    0x902c413911000e00c3c280b006881c0800f810f2070700c0140102641d20400700caa200380c0107d4201c01710780301c1ea001120103055959941c91390441ca00b60200c0c02c0c14490b00494011406658148070103030305942407944480d5550780041c0810a901c4c07100c40c4140c404c2c4001d086071640205054100204e2840c1542032034022148d004505c540003041082c10208012041d0181c030311850883d800d0ba407400b401800c21000d460b8050706020303020300740740300f180e10070740440c0c900581c040c18000a00d100c201c3d62210080d802d40e44048002c4110440c0c100d9a081080d140300c1c042001401841183c40e20010000c440ba405080c02045028043c002c003400080b81c024240207018a50300140c0d61250304990700c5900100040240c101420b24040e011002d510861a100c05600084002200204a419440200440000c1d403045020210000080c4071004407003000c0c040041d0305a0700304540001129090424201200c0c51f805142c82c04211603510071b900540462088485a503240640040000c1c030382406080100c3d400 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 617799649 1250 617798399 617798443
    0x100911091504031e03090902090a08030a0908070501030e03070803060d050604030c0203060a050106020c04051f0b1c1815090f0b06010f020309011202070609080310030c0b0403120c14 80
    0x302d10f10a80e11510361300710700380d00345405043d90002c210800c107118030000243c0201f008542c561b0396640351001048403c040303e680e18a403550182c00c50240384942c001c03a0089000000f1a54020b0003061070000e520340145240480c690340d100c2c000d0300043d09190b00104801030310000100304002a40c020380c006d40f109500c0e04482d1040501e0300c0d400070042c1700c1c0c003030a2500400403150001485100102d00711008542561022400e004078030b8803495041944402d42c00014170700709050000c0100ea607149403036070f250b0410020080281ca81804110f008956000c2c101000315688044401030001c80d658081001801a100c032100603200c0401550102c0e19042401170b1076070441750b46843c0b41ea0b00d0003e1414034002c600003821401c07803000380400094000030700c842001556801005003562107520143c80c1c0c185101030082e0008140400c5a0f01c2c40c00030700c0403849090120a650459500108072811198030420845d6103082c03800301140e01c08071511210000800070700044681401d548a1002c030 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 617800899 1250 617799649 617799653
    0x80c06011404110d050702120d0e010f1112041b150e030606090612152e0b031810060605092b0303270f020111010510091109150403 58
    0x3081c001000522441c505400c00d50140e45032002d441c1e48040324000002c09548151040e03040800c0f68003565640040001c003a0661100c036404411403000c0320008109010b141e54142e0301300da0704010f600f1402401888075080c09545424116406481254801440c2c242e044015100c5061a00b1001d008040d6140c008103a91340440840c0d05450203c004001504100d808141000c2c006800d503405122501034881132600c003088444c1da20407112046108030b1a08096a00c43c040400116080e50152440c03520030b080709600b1120b060701c0340e40c07a80301d285444454079035803004500c568085580c001c4000060024503988940d500078520381d1642a5504221800c0100120000300d44d85200c07403840758000301e00e40507100c03015591035042c10b0001c1d40c075000b1381d00180101d00300480352082c5000d00003810200070303c1244402c2080e02c01e89030306003d1440c0007a4503090300c9044034a200800549038007084002d03044d07000b4500d0340394160740c0356244c101d51001148403140800300e480708400e000182041 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 617802149 1250 617800899 617800919
    0x110d0c05040306140f011a09190303021c02100c030f0f0c030b030109080306130603051219030203070f0e0a05030d05070b0109090210050c16090e010e06071205090a080c0601 76
    0x40000c4202c0d59049540b5020600384c40030078041c05100807181490405500048080f002c9035083d4400a02c503c0c440d032100048034044140c070b800304400500403c006c4150f030390003241d04182a08140d3b00980034004500031680b000703040302072120003099203c4108101d0030425219080a004400c1c601060441c0b40010140544440c0b400d403900036850035096501041c41d480035250808411a9110003108a4407101070181200b1b4101402034010142054002c1c1d0b020b40003800c1e201210314032030055461141c0190100c1c00204d44003000305501944c0c01891030312641210010f0b800052030101d2958079000403e01d403201489111011480c00103901c02400001140c40e80100896801404048907541c081030400c0301c00e40385003003031210108501c03d00f02810700c0030804000c3c082c1880154540c0d0348000c3c0003e03190400d400e4a141d4609002d2026807040460113510074031513900d81c00c44059415010000400700208003d08500845140c1000521100e000384107800c040001000c0039410400700036 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 617803399 1250 617802149 617802161
    0x6140a0b01050f0930031806040e180106030c120203160f0513020c0318040c030603020f06070c050312040501020f0102130b03070e0907030e0705061606110d0c05040306 74
    0x80d06004051040c0300140040f401100c2260809448668074601215040201c1034a0701219500f520714040c8140c0141c000040640103480e80003050300b507029011424018288100c0c001c0124844140d400518200c400b14441680c022089000160311039681e02c41c0079051402e500031a120903804002c80e015860104200e00290381140030030908585040c014511512103482070034024100b403180410306041c540d060380e01500b045c5003070369030318121160840e0f500c05030318100c14459803918147c0991a4428892081540d0b03016094220381c10240781081240c0d0446a0102c030314800ca0000440c680d28184019045181c004400303944650800e0000390400324a420060a41e81c0306002200d01e16003070018031390840d190b06850307994a80707844c1d004031303174408900208603084820101400307045641940080d0b07491441c241038812043c1c1385e401f00200c602c00d0b01145c0c410220070b440100c0100702264800100e00412003801c5180c022a9403448040c0c4800d03075494404240041070800c00e00c02640245c0d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 617804649 1250 617803399 617803421
    0x706050319110f0a030903030501120201121104030f080a1709070b090a0e0709090b010f0c110f0a060f03050a02070201120c02011d060114090f041e06140a 68
    0x540d055152400215031114105045805031503154032815007240801d8049030b2407012070010382980e40300706500c06030107401081c41c00c8002a01d04000050400e20080d10481440d0b4165200310b5594075000f6a0b1020344180815080719601c1048000b002038200c0784462452842890110b44507062098050002030007006180076900e8154100070940b0008520002503c400c010703000d46a8004801007030b1800d8903600072501e1031280d5424000515080400481107414015040c072648502c000110b41d080044580e8002190302284440005290001800202c0340042d002c06080f44181002600c1c0034081e9100c003012031440d04020080c03e6050096552000c64034505502e802403c0d070000700245440d00c2e003181019a10705140c4c0f40c29100790088100011690a035000080000c66020f031070303103000e104103429410101e42d040d00a0501c403940601c079210900360303072440c1d680303a4031244041c0d0203030810f13180d10401c03100c3d40000003030315481683c0030382c132003a0300d1004030389080040751049500b05056 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 617805755 1106 617804649 617804657
    0xb03131a06041b090b030414011d060108011e1508101a0a12080c100c090305010b01020c0a060f0e031915060b0729090c030706 56
    0x30103409024121010455000040c00002c030003424064454041204198100f21800e11040915409401041060214480024071a0840e000031381146810140c03085041c10641c410081d0302d01401250340200000700301c0b250030300c54200e1103e0700410040d803101021210301040041000080c510380c000c03246036440919011029004281180481c0405800401010703e03102c0c0101048905180001c00e202205880f0130740305601c40e9550700914071400404d070404004910440d0641c0305250f40c0c0784a039500b90724000b420741e89900d040604550124030134001c40c3d038500841c402210709030704090317824030748440040e60701800f942c890f2a458050208910b00341c2d0000d1114552191188028480c1c00d40215580411125070340940e01408005100500009005603083c20b07090342c042c3c0b0403040440f01040d804c03000380e4007103602d42d06e40c6c2c01c40110401507040030800d11002e4140c40c10 = true := by decide +kernel

theorem cover : BRFrame.Cov 617625899 617805755 := by
  have h0 := BRFrame.cov_init 617625899
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617625899 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 617625899 ≤ n) (h2 : n < 617805755) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
