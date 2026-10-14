-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0408
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:39:40.443061+00:00
-- url     : https://prove2.me/submissions/381f4257-46cf-4030-8d03-8eae8dfa465d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 73201440 ≤ n < 73381297 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 73202690 1250 73201440 73201451
    0x71b09090501021e04030b07050309010b0a030506070230180402030403021b040603080a0305090f060106020a0201021b100f0516080d0b010e030303070f0320070b0f090c09040312 78
    0x14030005400030b01c074901180081c40f490b07100400c18040203000c5d5010003010b200c0442c2c00710310214400c4000d16003004944000044ac1c606800025104943e203030700803078894002404000005805101308004c010503070208403041098121041001940350080f094080740c0411580c04194a80c1200d403480c0c0c00280c01159242041d06010b551030b1402c0b000e0100b01c030845940c108903400c0c07d0044030101c0c0d13485110030703080c404491400c1c0c015010046c40030035148120008000e4071602002054020000c0d50068800800b06000081c1800c110301d040300324042211300c0780107641d1118601015031404514001354401e10040e8102e0303051003600c0125241813a50b052102c06d200041c4010000004410f80400c010002d030001590940072221250750b02d50003d00003d0a0140112040c900040c150f181c0051031207d926030081d40c0c4070030120011711510000c100f04007080903054815820440d140c1501784245005c42c036169403421a140c250b8040c24044001c42d00b018024000000b17441100e040a009 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 73203940 1250 73202690 73202693
    0x30c120f0a0804180c08010302060d150b0903010c1d12030c0714010e040903020607030506030709090501141e0105010f11030a030b011b021f1e0302040f1505071b0909 73
    0x10345400030301440c501344002d4650010103c0407071141e19108403c50300c820540380c0ca59020000b454000b00b03040e4140f1501c0310302c10582c00c0c6640300050040c04541d101e1940b036404907018542102d680c0c25980060120b407421203a2047c1340c0017189048400700301c81407004194541045800c2d030040f503801d10103920401c0e00201d0390301c01010709407021850030703a0f42c6582900c0310b03000c020558100741d02c00b801580142010a00c1035200350403541d03100c02d002d4219403001da9221401c008884060302c0940360760f59a03400380401d604400c81c0f81a0020500901d02260007800410341b20000b8040c81201e06109140c4e2155241c03c0c09451000d602c41c0300c0209498860141c0c060150241c40d54202c0107000a1080c10b202da450dc200da0b91017000c40c0d03005001000400e0684c100c403030070384039084c0b50482841a80064241421007081071500340b4852590302503280c6141c1209900070502d2030300f180b1245000c1411543d0700a60140558000ca030700180840400c0b5403216000f005c0f40c1540c1c00c80c144ca1030a200c3c0d42c50 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 73205190 1250 73203940 73203953
    0xd08270a060804050c0103111b01060519050a0506070213020903010f0912080906090d050c030f130806060102030a0503150a0302060a0c150c0c02010809070b070b01090b0f030c120f0a 80
    0x503c281d00a10075550700d0289040114104d40b403811744c500b500001071200b10108204a8880890000b004c40009400b94850000903640181c000c1819141c0400300740c02d00c06810008810401080140c41d10b90402c440343e80066444080b4155042c003159010030540c0c0c542c0d038250004898109003d00c1085201c8040c14100c02284001d01c010010030b0112000c20b0803520000340d42ca01c5850844003070040c0f2a103140085034943d00400b01c13611310380300611080881c4c1c0c131204000c062612400040000c0e103445c21345003d0030f14000030311850542d0401d00c000540a90000c3c100c13584051a20246548071f0910300024451003200e4001a41004022484200d8107030040e12241000b4012081c1000203a00c2c002c42c82d0503035210081f10000a000d0405400042d40989401504029003006440392941c840c00c21542a400000040d1481c05006004010518251049002c2007005940c1c010220101d80080f0744d4a450180b41701e809a552a010b80c0d039070320001d00042540302c036020299007164500c0e04011 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 73206440 1250 73205190 73205207
    0x60e01030803240a050112090605070f140903060601110f1b0307080c1f050c121e070201080105060a0302041a0705070501020a0f080313021207140d08270a06 69
    0xc02a190802800d40c0703e402039100d1003102041c00401501e22581404011503203061081a40301c0c2c16602d80f928000090b9045c081c3d1481682c542ea6418030144c0118802050b90200c180c03211000c1e002001128090740f804141d5a5010b4021300300303d80301d110701580040c505030000707000710060f0117544806054020351040710300d0900e00c1102104e055584840030f054a4141110f0b8080d0721104600c16640015003146520381e01d901c4070709049040c1400103140034100185585411103076280000c0a4040298119040c1d04107001a00e0039418041d20307a0020700004010702485100320008076144620f244a50100c2e40500007800d205081280202c6140350b09802c0410206e88502624901207600d51002030849015a04124a980d50003c10346403201c030b0740d0014290040301d00c280400b00c005600c0e003c10080036a000c203001001ca0030310785001c02e405811b0f00307800244241004002d0300c020410102c1601c29200b0305803240b56240035034141c407a80300404001010f03040004280001000c40d08031001 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 73207690 1250 73206440 73206451
    0x1813050604060b04080712081207050304020103050c0f0d110c01020708030402040b030613030e010905090702030d0507081003201903030f030902010807030b030f12040f051002030405060d060e01030803 88
    0xe0202903160200c81d203090003517028040140c0c0c0200c400b0070010680003640e040441c050170100385000c80c151b811040d00c080031140c00c0c0204000006010455034103120303a50744440c59008403401c2c91404400b88034103100d400020111540c484050655100b80c9001700d070a16034161008541da01ca2500d4071502980080301c050344124540b200c65000d5043c00704a80b03220306803425480c40c1038843d80c1c2d41a50a0352001baa403030304002c91203002142c56210000e080d409012076800a54a0b5040113003108281c550080c20041041550003d001228030605000d0041c5d90f07200044e01c407052070111030721035114110403159038051800c3e421004078041c606410300030f490083c1d4411906106e41442502506c044100090004031a440000d0005100340e115101400c2c00900703803901c409000c60780c14603000c60141600ca05810001d41008848500d6604000a00080e03e8042c02c0304041c0d071002e5240e01851040340d018490010761800000700a9110300c0140104020524255031241004505600f003104c0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 73208940 1250 73207690 73207699
    0x1110c010f0f0204060f050d09020303030f090c04060b19030b1c140624030c090a02040f1a0f031b0a0e012604140f0118030207060903110618130506 65
    0x314615007501e02d00813a401d032242ca031100c0744000c00f620030407101540201e4009140c2a650800c80700182e4041c0021801001090381e655002c0c02d00c80c20b03003030507c289050011721940c0f502104115034440c4000f945d013541ca091264010f41043c500003a0090055081015449103422414610900d112078641000324002c03404003881082c02c0325940c0e5a44c0c0d0070b031100c86c900d44c40107042e80016001c5192140510380081c0684e42c4070000303100801c181400584d40d0720507081c0c003c038091001e0740c0e03e0f1981c80024040c02e5607011200415018803491489440c0100c101c5060000c000b031002d44c0d01c0d036a101142c03c1105001981c48c02916002040080400c100d640000c00f29000b4856804641550400072845c19003030107203545070b030350b503052603401e4944101d00786d406560103a110204007840349520ac0c40c20000a00c10802e00c0d0300d0001d0074806150404800d007d4925010302c0454045d5220704004070b003d9034039036a140403550603400400f44490300181d010030500202e204401454024602484050740e = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 73210190 1250 73208940 73208951
    0x2070f031406090d121a0d2d0308060d02030a08040608070f05091012110412060c0c08040909150c031d010c0e0418080403080a02060604050103030f0804030201110c010f 74
    0x5030303001c3e11207444c0f0769604000b42c0c8410003809600f840f540300c0a1280365001e001c2e1020b51262010804425140906603085403130464030070080303181c40a0085804500c06401c0b00840c18695010340382c140c004d41303024001d80c140c0f800c05007103440c200002480c40c1d0f0040d2005442c0c0e82d80302d030010062407048640b00300048140d450341450502400581d1001000140404001c030030300301c011150f64031030070b006a8039640c4840c00301d050407150400800c05000c03480c0420001c00c50508107030040d1401c14490074104207002c40300c200810001c1c001e5406965500a01041400840c10581c0c0700580854140c064103141c00009090780703800d54010420362880e244c1900725185012029422903003d0030308803000c1412544c00809502d010390003503d40300c00400c88282001e419485100054010341c00072240b11100060040a00b03804200c2982d10107070413501413090350305503580109281410b8020030188248403006c503040600039088803111502081080d6292440d1400c018007a103003c03d946182d20385850b = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 73211440 1250 73210190 73210201
    0x3150b0102061303030c020c060d090c080a020904240c051b0a02090c0a030e16050312070507030f0203100905010515010306030507051507060608030304020909010b01080402090702070f031406 84
    0x3082e81032255020b007000f07500405071030301d00764050000c031344c6070700114041d003800c002c0565580307000f030a5803c2482c5c00000700042d0703a190214103404c4541200200b60702002c030540061b681e0f8452194010340c0120a00050481e49228458410210b203900c809581003c01c8004000e6204019114180c8681081c2001e001c566900c02d40702c0c4c0c58000e029410812030780000e039413044918010316801d00306180020301281203c0ea402e0034288002c0c1602c41004c2a1801000185030800022200b04013800e04a454052a591419502c1a40d48030050042801120b44015075805000809000003401c005001690301e03858080d00909040f100300d8040b100d882d111102c02d510a00c0b9007015258802d000b054100d04010030030400c40c00600c116040080c0400c1200005000350099074000d040707020085403241003510400c144810018064030440c0c0c5080e0712900c50760b030302003090b179001034060300c050084c1c0e100c401d4200e0801c1116000322080c080c0700e242c0001007101034904c0c0407400030050191241500d84 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 73212690 1250 73211440 73211443
    0xc020325021008091b030c0d0b0403030b01020303071b0213020c0706110309062703030706020408070501320408190209060109060206010e060105071410060524031003050703150b0102 80
    0x41e070b130508455002d222540d0a1000c40c5100c00d0240d440101103807494844500000c8400e0410301084507403040e55820b200400d901401107854211090000d581035241012004003400300a08184d80c490303030812030650079900d62800c030945082c04421f06540e51100703c8440b9590309210300c280c4001600b00800b00e4000300011040d40c401807002000c1c5460700740e00d10382403407086001c038030000c40000e803d0340c2c2d280861750100001d000851042c580561218035002c440350401c101176200074103221144070500003c204961a2121411140310880f140c101e20464002c0b850040f40c00a241c0341c884c480302402e5024201812204003407080701c054000b6500e403401152940c55902c10a005070380214014080c42111104130303644040185005818543c25440d6003202c400707150700f814295008046203c0c410440b601402000e05801d88200002015031322401d0800c003d95031844100200c00f00110b002c4015410b03100d0020764106040f070307108944a040c248601c034901482c1c0c401c06413030030040d0f581d00e500 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 73213940 1250 73212690 73212707
    0x30c090f06050711041d1e190803130c06050405040f060b04050907020a0507060f020f06010602060606070303091203021b0f0a020607060b0409140709050c0405040c0203250210 77
    0x250b0700c260802e034141d40c803840e06a101030240c40d88692901d64072014141a060b9101c644003d00b402040c9180f0b14000001d040c00106c5a540b0315600405840d07560145403010340f4175442c0c0d1003000303182e5950318051101c503050056680240413115071040000c105a0000140c41511821202040018503051000d4111001407003401051304051000f000380e440c1188001307a00040900541d20754034102e69805082c518a0341042c408514600da07143d403100d03810044070600041e080000d000550500c00040c1d5185c5000708400e101d131030005048001c151090300411380e8950300585500d50103c2c110310113030107500400c42d0010a8099005030082c00640024041c803404c0595015140006185d02840400d90100ca4250380342e41e21107030305401c6600c4501c40c500ca00f500aa800001038001010350506090841e44094401d6003404244034416500008440840b40115000103c40200c1038003a03056009211442c01e801111102c0c0300c090514110003c40480c0c4216035505840c440c03520b0035200c422 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 73215190 1250 73213940 73213949
    0x2090a0f060522110f030f0a0501050103090c051e030f070812040e0403050304060b0310050103020319021f0201061a0309010c0302070b040204110c07032409080d0207080910030c090f 80
    0x10246194603445070f0960010302407500380341d199032401c5058610381e28968421b0300c0c0c0580c0c41002008100722000c444c401c41c0e0251909207020300c001d9860b40c80d02c51030344025014240c13003040c040801941e010548481d848000c8000b8040d01e589140003003055464400c2d612920341280180c0040751034802003c011202994643c00420005444903142250b4a8000610450b03502d6600c001c40e0000e03070b40420400c50480b590800119240d070540c81814100001c0740240485061204650360050307403089011800769600b802c00c1d03869124401d0301203015142da80d00400341040300082c0501c603045444011845210440d00900c00705c3e1180d0030403012031080c0003001e800c030f1030182c0c0407400501d015089512a0307601501075900300000750100d1070030b0010360f90040b0f0b01041c510181c0d1004081c100b107541075540c07810741300b000070380031544507401d041c49000600341c1c52540c001280c404001060041e25507602002d40050f0b8003201e40d85018008000c003000b21800f04852441c0000c0400c0c1c07842c2560281e8 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 73216440 1250 73215190 73215229
    0x1a0d1b02070905070201060f080606040c090b0702011112121e010b040b071b060512010803030601051b0a20032a0103020a02030702090c0403020a0603020307080f060d02090a0f0605 79
    0x40380b910002c20014080035040780e045540b5907200080e0780c40d40c418001c000d048c00780040d11883c1014000c0004960302d03020803500340141e07104200555428141aa0b18054081c204a00302d201807114560034140002259210b03094049616034146110f424510712500f83e4003942038000b00501003504104c0c009110380c02e1180010441400b940728200c014000740c900c164044490b00c07045201e0492907800c0d6402030703000204013140180c004450350782d469004000c014041c6286040001c0002c100d840755000345100080110104048428200081905180c00940c10201724010b28112380d90410380c0c02c0d005201c0c1c8120350f0301704000124000b82e4030208007055a000a8480c000c0015000f9400092002c2c5c15400305200070409600c9420310988543e1961340c075695158110320410403c4d10701900a2420944180100b000380d640010700c40f60460701841d400b07040c0d036940400141c05d5150002009412041003030521441800e6a001801c8030fa40310762003800300c01c0d191020b011680f2103641c0c00540c0da = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 73217690 1250 73216440 73216453
    0x50303011a190206060a0b090303030f13140714090702060f060103060902040e010f0f061b080d47060c01060b0301120506070815040b0105041a0d1b02 66
    0x546095030268049a80e10610720740c201600e4840e0410401c5150442c8000358108a0030401186421102000a0521a82410b04000740301000c00d03540d000082200700514484000710310100d80b114500c682c040c1e0700803400b0704040d8190400c1620385400340308680c001c80c2070003001212031924040b0203106800a42c01800e03282d844281200e28044094035140c141681d448021601a0395400200040c0c00d01079000c0817036503d0b0459031030440342d0507448809244800c0364180441c50340001d10f404814100035a01c81112150306003110144500d003140c15001e0302e82240c46103600c2010f85030380d0305030100c14030054400014002018400016103c3c6000130b0f194030119601030725203074018220f800e00d2400005162030700c80311181c0a5038003c0e0441008500c61496007000c000c8104407040d030201c058a001d04490904400d50020160580280d600c1161030309107104050340b24900303440c0140213002e01c40d051040c0130b810814144d400a00700301d0420782480741c107040300000300c02026880780d00c65006204 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 73218940 1250 73217690 73217699
    0x10605130b0a2103200307050a02130e030a08091603060f05060402040602070e101505121501080105010e010c0803150a0807060c03080901060f03030f020c01031104150e1206011502010905030301 85
    0x19025007032415801c824584001045d040031003000545a403902c5035009100b015140e004100c070340c4a5044406031001e0801c42495540040403040c0c40000c0c0190400c2000c0c1c0e103030a40300c241028103920110740c00c0240c60b80000180035442e000703040b10295003401081680c842c18180300907481030780a0071015034480c2100704006540d040070140e00c00303031a102108005071030320500c0d900e14a65200c04000560080380500c0710300406e0110a8000b1071401c402501852503c0003c0d00402c0c0501c2424140001804049050390142c2a07202e441a0700c0300ca015503901d0020040081404940c41580c0641050003002c20000300c0041e400007691066101c940401c03540717135021980e501006113804455500c44100152001141250801441c441d4032008040c801120300280380c0b460615100e810103041140f4000f2a00181040380c0940304001200200b20211a0701520600f81154102d50015820701d44003844803408280c060595965000100b103c09006104901383c0340c1e03140e07000d8810b801c200300400 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 73220190 1250 73218940 73218947
    0x7030b010314160c05010507020a03180503060105010f120c020d021603050c0f0604030501021903050601080601080604023108010501081f09020a0b0c0109020909031e0c010605130b0a2103 82
    0x1080c1650f51030003440c803101c1907550500b918015501d039805a804581283d04040e00f22a04180343c41407042c1200c685403031701c00013940e100018400e55052080340b04052040e10301c108540c0d80001e01d016428000c03019105402540c07103020459400050141c9070024030303140d40c0701507030000310b0750050010201092100e080240003602490490307031008042000000140084c005801d5101ca21500c40403660010032019065a0b401803206041180a0041200c10307078100d0b25207500130701c1c00e03100141c4419100c4c0c9407504000203520710070b42e455009142070b0010084095101c0c1a40d40300e03c001e02c11641d0300c820311a0350389144509a80446a19902140c01807002d90103020658001400009a90780c1c03007031075804541c061142d81e070f5580d440700340b21410341c200041c1d2940c001044100031031030b080c400d03180318003400d401d83d490700303c2001c001403100716444094000702c003d06801003490301d10803240d291031001401108540d501450b45448001130500c050103110316520000c0703004810314801550b044 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 73221440 1250 73220190 73220221
    0x20708061605070506190b040603050d0309060f060f0f080708070303180918020a0501080601020a0b1503031b0d03090c030b0406060e1e1f060c15110307030b010314 72
    0x41c0c0070040144407601c0400d104106490080080c40380350302034480a100d646094402446405024034180041000022000900c51042540e2850002071112851503c0c6001d0719600707118605050505002181e040d001c0c2c0c3e60f2800701c45112203034007002036644080c0e6881e00f00318412581ca903008454100042400390340d100011061013542c02000503220400328080326002c0c03800d0890703440360144031021400c4ca028a00003070142424442500c0c6801c100003942e076514020000d10102c2c801c0d0114130070702220b4000c2c0d048034100506683c0c032104800c13081b0842d5805603500c4840ca12454188480d4203009104100c80640c00104582c421403c41c0c40342d6440d000041c0c0200ca1560b5100703030010300f01400d2004075014141407861780d4850080d0415102a040001c0e06010002c441d0031500301a09040c81c0c6004203c072503a04200d8011a8507080140c48034650700e0410b0700f86410304034600c0c44103092000561040490751400c200002a0000460880e401202c18031008141e00c400b103405480448840f = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 73222690 1250 73221440 73221481
    0x6041112010908041202040b030c0303180f030d08060307060c080304170c100b030d02030f04030b040c150504030b07020307030206240a090209010806150405011209020d030c1202070806 81
    0x104003280559211070f0250300035409913141e058007045600852415000d503088560b41100100044403000d0b00007502c0e403041c1348207030411a054850750b03c856207410f01e0710b98039400018260f40f01c043c00864080c0c0355070390031510300b440390195001c017103501400380660014031a0080c0919045950b00e0b5150002c103440c420400341003140501c216001c2c03040800c50203e00e040004408a54001894141031420403010342020640d001441541b544500a1081d80c00b20707500701000000544031424480307070310700041d00502c20040341401a036811640250044c000c49100d445024125900c958080342c4a0042c84001070046e0041400300c0e0b0f06080c21100e45880920311071019402c60b51070720001b00444800d5000c1e000d50346c4c001c1601001c968200110aa101000703462030038445420791103e031141e10450182506020066801110003031550303012100d025400350443d04c0140c2c0354180a4079400400c0800c8030700d00c08030185090300510115a801c11114040e0041c031542c1c07a080010040381051701d41 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 73223940 1250 73222690 73222693
    0xa030e01030612050d020d092304090203030d02090a0f1401030507030e03071a06030f031b0307020616150c0903021203211911030103150e011a011106041112 69
    0x90200f1581180031015000602c9240104102c0b000048040d0030681c80303800d22000c0c03141d20700040001d9956200e40402d4050607140d0030a2904016002600900f041c0c603010b50144408901072031543d034950300610f00070004603201528036550700c0304100082c00c540244046070442018170034840d40244c010503040341480c10045040c00816074940e155810203001501c80e80000f01a00c0b031803140d030341c89254202d00c0030ba01070030340101401e4510742d891140002e01d01203040c864518001c00c020610136030740034a078004c24039903884070003000f84030814ae0441415500c3c51507000c000700001d0750b68458034500801c25111010064a5a000c1043c00b440403000b052082c0410801ca40c0d0805c55500000070400045031440791034140005803600c0b8000c9400c40341101c0d072412400740c2e551400c00055a0440e40e00c503641e6000f034610301c1d084201410000000c56220746c204012048010300b003801040343d0002c00e98900f02002c02c140400d0750f4421081d540a4203003c80d4002d5040d2074180f4801d280003034040f020 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 73225190 1250 73223940 73223951
    0x1203020705100c02010c0305090105040308060613080a0c030605060a06231209061b12010902030705160302011b0e090402010507170d0501050f09100b0d090611040e0f04050a030e0103 80
    0xb070880558001908800050755035881072149584c241c45640c0d08006040001c120618003507401810702300300034105a2141e00b000c201e0741c06c98902d03a2441c8000e0030080042d601100c02500e0419000d2440d8003046a0302400c0c03000003195424201c40c408212030007550382504400c0001c9400d0700805c0132000c5824030300720400c91040001c15580c103070b40c05444100018040c515128840140d4801e804500c0d6080c00c01c2005419030005110702c0c01350648030035410069070790b00c0d001c000b0340c0d0b28450015180080322201511740e05054041d070005846003141200756010f0703019408200c400785d5900ba0642d44c401010800305015511417006409124170820f1804004180c10010340318030f0b003007824010201900d0344010300060500c100084100c0c2410f0321040171310b00b4507502c03402d03890f20039004001f4885404110081c1840300e60304030f0404660807507002c0102c40290640b05c0301580c054010400381d1000d030f01c08074104210820750140710b69000005009901c3c51503a0071110340040060060415843d003 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 73226440 1250 73225190 73225213
    0x90c09160c02150c010c0207030b06010806120607020a0c0510020a1104060b04090e070504020f0313110a1d01080c03071e0b120f0903031605090301020c011104140901031203020705 79
    0x10a90f40c0310b0740304202c625071181340305035000b4291024030007480e085400150041001030300d90881c10341c100c1d00c00d0809445694038000450322486564842003070340d02c1500103011045802292154140740142581203080e5200d509001c1e02000400e05080141e02079200c0d0300100f4070880100030305210090011030a030b95203241021690300940c01000c110380d9200000c036a02c803000c0250780014642501d0942c249418075844030b6560000070b01148c5141e03402019041040803984c1d2814078101c0041032440c500c1c0c0c42c0c042203115803114003481c00c03c6400b0301c80003054042000410300303a0036100034002c02c001800c040e9400d40b0302c460f080300801101124840407511038580b4018020700300154494424038503090f503201e003440a001d84020956041041407000c10100b8008584100445050031661030940d240864024130440e60304203000c0d407800c00718103141c2d45244020001c5401046142c80d903066030804207d0600003e100040c144070307048072040d850301d010b500034141046c02070301910003903c0c14 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 73227690 1250 73226440 73226449
    0x60504090c090614090c0a030b28120b011a07050a1101121104060c1a0f010501020f01020c06070c060207050601030c050a140d02060708041a070605090c09160c02 71
    0x10008844600544000344954020b82c46000002c1181c4101140c1800030301000c9110b038400980f1219071080c001a003141c10a020307400401c00200e024000c502c148003201d0700030040303071303481c03a841412005040700000703243c82d84843c1000515000034945910740d20303210b0411462502d0110a0007a0782c0c0a0000e5030100c1d00c01c1c410705135090b01805805021414450006010240002c11350303440760b1500919101d0aa00300d800c2d542600c116041c4034010300740504040c00d48006804050203018500010416100454400d181c101c035070a03002c6841407100741c91090301f070b4000c8140340001e80e444040000c0034170340301e001c0c41203c445c0501401403a0030794980340d050420000f40c10980c1c00000c040307010480c41c205600680010316211a5005589d800000001d1302c098440714040c0c852800400e100051000b41c41c1110000c00c251001c8040c00c0000040c02044d5402011040d0307010b40ca00000560514004076407203150305401865407859661b0400662104402000321100304003808a5083c0144c03035 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 73228940 1250 73227690 73227701
    0x1b01290312031528030b0114031c1101090609050a03020d020d05031f050d14060c070201020712060212040c05100306080d080a1d061005010314070302090607080403031e08010503030418060504 84
    0x3581c486c00c4540c14510581c03040d1044154050003584509401c3c00c41c802d107544000e080045610300350b502c002d94400c11300d014041c0404080c240174a04040341080042c0018000c41e114820f03001d0710180840e032402640c4644051014101103003007040001d80000c080c107c022004120868020341c52602c55010803800d900c5940d00301c985a41ea41c00c0311404000801c07506520901824a5529008079039000079103c1040f0b21a8101d609014100481041845d0f0140ca191490001d5030884e1403070641020b031104c81380c1d403180c5409421250841d0410350b100340914000d941e8803600501c0c85542000302201c2d040c2c001801403422550f0340e00108108031b510a052803028072000c00801c203500704015680c401d040c2c15407003181807601d0b0404298043c03141d01409548049a4140144c4511200e00460000c0c4030745400204034134800076000c020035402c46818415074036108082c40f074011020100b505c1c80c1c0340c280a030f00d90591050104200094101140369040c00b580600814800c0ea500085015a403 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 73230190 1250 73228940 73228943
    0x201060e0c0703090b030c070b0604020f13030c0905060904031215080a021305010602060c0a030204050603040b0a0509060402090a0b06040905010609150305010501051b0129031203152803 82
    0x400140340740c140350380110900080c164540e0391768a9400c21145e811024810b0780402446880224005005030f0340d00e41c103551180b18102445c1d84d54400c90303075900b444199a070008844002c0724040c0860101020b214403482400c014000f0070440d1a5a1030a4841a8a8042002ca200d4807244100c0419680720454001014079000600d029000791040200300740c8100058510316207041c0042181a900213040c07a00032920810325030384d501481c60114080d10481d0007d0390080800821300c810070418010480c428440b582d030070020340e03e4820441e519440c06441c0a9800420603000c81c0c2c009800d540b04240c1d40038018012840c042c1e0b80c0c140d400644100b6030004011405104080248c4d189805211482d10301918003040550304060010f4040d01411a40d85100711151090344d051010941c0b080e0759041d0b80190f00f41051510040303c080b80840003202368081d00494003c0100e030088401a03901404400e002c1303c181d0303041e80701803203100d00c29840403190000c10041c0c041c0007185009002c41c00b85 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 73231440 1250 73230190 73230211
    0xf060219050a1a0105100302160f03020a0605040506010906140102060106050a03061a070209061002060114060c01140103061a130203090111040e04060c0e03031e04230906040203250201060e 83
    0x4e6141c1020851000400031005c0c0070f15004204035543c1140071f01c0800004c0364005110380a00c040c9040032482c0c4000440300030400f038641000c0c807080c00700001c0d401c0c3c101e605216092044946410345035094000c3e041609015900c000c0050040f00e0040c1d02402e01c0c0c0c1143c1c50300007007041d0b440000032400e4a1140d081071a15000064030301c2541820801180c0c05281682c2210107052600002955071105110700d0148040e40d1181c030b0b0b4255508401c840c10108190700a12409645d01c507071011510003803000720f4a0901d4144160090200000a112120401411508804680c1e400c1e0300107540002c10001c00c9540e00c074039150b002800c00c80540082c000c1d0a080041c24503091800c0c030101c44540f044842440a088803410850703034000f044441e600c06078007200c0880049442d20741c115000e107400040811152041d400d01120110701c02d22000f5004550030300070746e140c000901081388001e4600035400300d41c5c1c032014a002d0900e402d034441c0307212140c400045d4155030b800d48124407440c10385246048 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 73232690 1250 73231440 73231493
    0xb0a02090d0309091d06040807060902090703050f090610060804060902060c1b030111070318030b0915152821110114031503010e0703050708070f060219050a 69
    0x500d8441c1c460078800c402c9174000240030003129609550386410007400180714560020f2200c0403c0002c2d000202c0c0203901800407400e609021902501403c0c0498084946d404038400042603030100003860750080c4440c00905821340d05140040f031307601d00300400a40e0210b456142100058442c54010000311a245026003400f141d03105014040411401400d4401d80c105a1305d400d040824404071070310640d05060040c000103140c400f41c840c0044680c409401400100308000444034082440700741c41101c0522080c06603078089220b090410080e42581e00115118003038140c0c01c005c0e404220b0444030420503019481e940302c016840c6c0e4040080e02e0700741d0b0b01d40016400c04200c6003441001001c203003421704034040c4d5100941c0381258000100411000801d410f07107800c09440a601040c9004440d00c1501c075415101c0c1401075075101680310749205813040d0b400000b002e580c960032035010340d40164043c1c20083c242d4815041060143c4034151024056041c0c0e0000041c40e01020808400503040c2c0c6d03420 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 73233940 1250 73232690 73232699
    0x1030e0a0b0c0418020403020102030a0c0201030b0a0806070f02030712080403050c03030a0f0608010b03060403030b0a08071d0601091208070305041520011a10090509040f050c010c020d0b0a02090d0309 88
    0x585402c0210b004c01c60040c441440142c2e000b0003990b500c21803d2400c0d000c449007500040f0080c10000c10565000f05001700040796445003c030f4100d104007041d031a02503c07a40040303000c03aa28841c1c400081c204a001d503141e46242c1c2c1c410794980b030b001802494801d0603e40100015811035109548003a0510354411803019020124010f581c0204008130080041e0480400440c0e10707080001c0c0010101661500140c50a03524240440007501d240340856030300345d4440c10400400c0c6021030382c40c0d50001c0d480c4001119580b265a40d0420386e84240e4050480000559508240750005002142032003000d000c00300d132007400004202984466a078071031071065014030b0004402008118100d803642d0404c0405075820084c1410800c11840c2940c107040340300c0c850b45040310700d8020703500f0069020304241c1c02d01c8203121502845010b4640034000391013040d84550010344d403440c0b00100094110720210b050f60003061600d20305030781c090143c1c0c00c05480c1a4500e00000c10000c1c096104030302281e1014400d01 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 73235190 1250 73233940 73233959
    0x80106050a0e04030e040e030c030d0921020a06180f151506021b03010603020603040812010b07020f0f190603020705010608030f0f0f0708033103050901030e0a0b0c04 73
    0x10002d010510010b08282402e0711300800d20125042c43da40660b85610702441c2030101001220030314159041030b81d49600428050748090150100705880032920446c0c118504c210f030004c000c110041e19001800002c01695508001e800840c5071410403603500780c0c681c00410542c001224026104001c00c1120781c50703034440e5008983d80c0c513481103a5000c401106100154002501d03045440c0314813001461550303180002405045680c10007500803031b012050008000d480d0019000310507201290301066a00e86030124a02d0281000280d84000c800d038406085050003402d42c10700d8200541855072101513140d404150707070b0307803540308800080d40084c0000901c0000e00c154405454048040c5180101c4242042658003800b0550080703040c002400c2c000ba00f50740000c6416595000c0600b0f41c891130940d848030302194a804841218003000d6550513a0f00c110303454104051681074903424105000341c00110010a040c2162442c140704540042c0040342d40398403001d12692031080741684d514204400c08 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 73236440 1250 73235190 73235209
    0x305060702060114010509190e0105032e0207020301090501091218050a05010f270e01050405040b0a0e0718020901170f0a05060f06190906050702150f0c030408010605 73
    0x1001150080310050101034100b00350003069560902e440c58950a5101c0048c056480c2400c0d03424068103104400192078101c5841107049540441c00c0c0c4560682c031840c451803a60b83e45007202c0d42c0d00203c500203920307800981d01600d519130001c0d00000d0b4442540d5281421102e41d0340c82943c00301440300140c04890303881000d200603402441d40700e0400503e030034045012a2100e004a506100e2000c0c0805c003002e210b5440d0120480982c0401c043d1450004000ea508190310b000c2c1c24003848d1160004546820540509405107500c448010116560031411390000d14508990503014056500006110392454a105500005e9500c2c0143e592140c10300140c229460203480c0c0404102e4502001040c00d059070b01643e10044002010910b56619130000d288036440c1d181455001c0381c0401c083d40d1002400040c06007451081d1100b400030b94485038117481c24055090005c3d8400345000d030700290313400300b94060300e00c2e001c040301d800d82070045c1c8031000c50a540168002d00c1c42a9501d01040041c0c1c542440503 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 73237690 1250 73236440 73236451
    0x6040b01140105030a020a0c020a1409181902010504180516020607021b04060308030910050702010513030c060914030c0c0402031603051312020709110a050412060219030204030506 79
    0x200c10040301d04000180150000401e00000c00d83e001c00e1212040c0e006140000140da80180390548031602d48510310084c80d04c2d4820540921808000140c0e5030300100104014130b109400100010b1700c4404140c0b003250f640c2001281041824080014901e61088889103001e1001d030300842c4034a80030b2a044192002c032203034031046500003000d2100c45074000c90b40448070300c520468030f5108110740f80800c0180c101c503480100140400400c10060103804101e204041950920070b00c025100d0110032401d8600070b079080700c4070103210904080001e000f10420a0010303c691008103103021251122020740040c250016600c1d01700042c0c014458005012085510b0030860741107081d81000070700002003a08100380c0c54185503545000c507a003100b009894061440d0710a02c0340d4064644804000d444171040d1040d1045903033000309844e40034030b081c41030310500e6125580d0642007904d09040c500100c00b01e5142600c138140c1c2004940c420340003020485401c544903483c00360f6660b14600c3e101e458210b00412 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 73238940 1250 73237690 73237709
    0x121c0905030c100801030201180f0303030209120c0a050103020c070512010b13060605040504020d0e0a050c01020d051608131d060109060302030907030b220f170a1b0305190206040b01 80
    0x2c001d0f042c1d90801c0d4510f064980a1a1520581c641c07108494650000c40e00a42100d40310b0520010806616400a196104094402c00e42620008030b504e80d4560130109159880300c4d80300070a02455200380c0c003400c8070300f83c41011501c040707603100003007001c1c1400d542030750242d6510340354400a40e0030410001c00d04019040c0c81000102e00c3c0c154000c3c0203000c0c0e070068510403078000403268041d0003150410700c1185081c0c000c0e10360a02041c90065580c4a00305000c0707015000703400000303032024012803e9030040c50301864129440c0d103050791034000707a92140c80400c080c0d01c1100000300704181b109481c2c00d034294040300c4001c86400c01c903002410641700d5510032003c040c01041086511840464900100e84d44600b1700c0794180c88a290030501c81c080551814a0301e61099070382070034000b010401700d500c24001c4012038500c506c000003078280d51151010030004596114407641e9003614128640352042c0c000d251071420201e6060409601024452140006034040001d1000784103904410034010108030030b = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 73240190 1250 73238940 73238959
    0x906020303070801030f030e040507031b031808030403020f0a0308010905160c06110d242408060a0b18130c1407020d020d0305040305160e06121c0905030c 68
    0x900411040050100600071b41003118140d04140c0614001002d00300d0041c4144111314000310000c008194243c894110044442000140e280c000e21641c1c600700c0561103003681c10840c80c1c0f40c101180d88048c00440851040411206264405002c0b91168911a544600704d40d45803000080c10383d10058440a11040c140039248042e64210000c144010350019001c110300220482072140c038001c030902400c00900f004290301076a04503d121482039030145010b04101c0b615a2030906051000840000b1001005031110408601982009600800c002c0040c00100c1d207902c45a507a907003080303502000300c0c020804490b980d031505a08414802c22121010481405013072001000300810081140187c140052401d0554842c640e002d00910b0700901081c841120781c1c41c000300540d1051000342c4850041000c010310401070b2240c09011110200062031180e190b00d1708110b040c00000103000124424100442a400d4a9071441c410040c40c5407a80600315203070500b0f241c100041c86911a01c20780051 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 73241440 1250 73240190 73240201
    0xc030534050a060f02010b060f07061b0c150b180a1410140102030c03040803030f070e0f0f0f040f230108060f04021306030507090e06100605130f080a030906020303 72
    0x92003102c00321070f154605100b441d41902002d84c01090781c0c0209070742281002501c2152416040d004000861050004100c00c0250310b201509181070080303190300040c0c2d1034400c0e001281d172004ca0b040c000008414002013095059002522400205c910141c28101c0c0d10204040300c0c03035606c1031000d900d41c81c040051551422091400ca40421800744074a13142102240464691081090747c2c3c04804030000c5a40d12038a400c0100d6403600111030000300040c420300000c2d95980300d491900b0803030700003504010403080081c0401c01080a02e00401c0c1d0081d02c5509400100d03501c9004540d8008103031007001a290110094100d18031041c900b40000c1a40d1540040010120004085138001e1603189c0c0c40c8000d80300c1c0c1c4005101818182201c0d0050341c00c12201005020000c00c1c0f010494088401c20030451070450f4056846080486408480d508040c0702001901d02407002031a0388074050b080112815100d02d070003101d00d0100d03000900c1a900c9020301c10101508000d110001c0e0002e40011350441c500b0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 73242690 1250 73241440 73241449
    0x601061e0309020906060c010605090a0203040c060c121202121302130b0d02090408090a0b190c05060402040f020405030a03021e0703050604140a080c0303060406050901060504050d0c03053405 84
    0x140c13a180c0900e01c0040c0b503100c7e00200f980400040c1c200107110001da4201841814040c0d0401c1c2d4040d06c80140c52540020b45e103004103118507000350722044407046081200816240413a80c1d070002188660204900c1440c40110b5022034810041c2d24041104c1c0710742c90050040404116507491102c500d4081e285425985400c20340c40d1150381118441800c0d55140b621f52964050740c101642c202581403400b04085580f10003604034001000e070304401c40d0050b41012603451401c070801804c1604100302090143c1040c1d00842400300c1c8031030000d03240940c0c0e603000c02d240901c61074042d80180c12002c1c0e8125034481e511903840000010b803005144c0642180c035201d07140e0170050b10050007411107a119559240381840411400f6801090350341d1038022828000e07840344c8c003c80d00c0030f104034541030000c1200d140c00780410b812380d10306588481c03c2909050034000c4d82810350f40142c1d00d0b143c0141c0d001001540401941c0c207200104011503e04031000c05509400141e808a42d000881d003252381442240c03074 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 73243940 1250 73242690 73242709
    0x3091515120501020f190f05090a0308030615040605040e060409050c01210219020c030d02100903021501080307020108090111090d08090a0b130902121f080601061e030902 75
    0x210107242100c0611640b5003a80203225003072554080c03000116010019004800c0c51000300307601600c6101d10225440002c4501d44101c0290319440f1001c65001d10110b507801000d1a480000644080e40c2007041c20117851580c0c00036030060001a4001600380315408042040640101c801c1e941440140c04550719203403503580ca061410b0402c8544d5085442d03000c6040541d100095940f01d0842d038507904441441c048c0043c100541c405485010000006402e0000766902541170f142c0c00b030041c0d6031080b4070301c07006070030030300815821481940b507201e546030607210a66000b401200f00440d0f8801c154400504a510010305005450745016403042c103504501084071804041221f51440c40303104c500c0c0244050151111040d006404d1f894007090140200004051415110380000d19161b510000072040e4440e20100c16003030304228010a1810b840d0584940d00040c030301440381c1c03079030b40c42e1100c03107142c180240c1c050340001c0c1c1e80e0701c0c80c09805010250380c0d114607941e0f4034051064440680224401c00d6 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 73245190 1250 73243940 73243949
    0x9090f10060b160201090b040801090606060203070302060601180e090f0106080307050c0105131205010f0b12120c0304270c09030302150a0605030307060f0c02150103080304031e03091515 82
    0x74440e00803c8116840b500c07440003c0c2560780005e0b83c03120380354a4880d00801260200301c0359503180030401304040740000107403001903905500a02159031410011901070300700300806520a05403900100c3c1a100f44034800c1c1c1b16040c01401000c01c0440341c0201800c0d43c6640e800041d00f90410000100030540214040314085400c0c20301603a240391800c030164080c100f0340d0040e01c1d24000c1c40200c504019040d0070000c1141040101070100803074001c100840080011180d40840c1d000410101058503480c005c3c00c182c1c250001600d04103943c8100080d0204007028050f500b94003130000911580c160392148601034941c529000003480c0c21a0307406075441041c00701c1107103520541400203a0070300164002501500d0090152a12806140303820b0016000d146260800241081c500030305580c8000b070000c2c881043c03050a0701050740b8689030019181d0010300203130b0801c0f940540c12142000c0440c1294214002c90303a00042e10306450400b02c0620761090b4150907554100030021484030340c8000410300380c4 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 73246440 1250 73245190 73245217
    0x1020306102d05070606080c180c0901030506060d0e0715020a1101050c0703050106260c011e0c06090f0204050f060907140705060a05010f090b061207030b09090f10060b 74
    0x41c0b940001521203019034900142a2400d1110106150344042008440b0b048180c1c2c041e9015081c2d6038040d08990800c89041482c40e0082c005d01b0070030341c8aa007003140c001c04090300c458500b8010754144800e0300e00858048401d0b5000260400c15640c141644410a4900c0d20203062030300280d1f52980540d414050215042050114107000d00180c00d11071a001550300c040200000d6550707d09545498003007401180c0c4820200407400040680892555805031050f564441880988031130000700400218000080003201d01c1d8590002d031541c441c00070110700404209800d4007041c8100000c2d5040240b2030840380c12040c0900c4140d442d1010740719002030803800e00301400c21000980d54036601031104080c005d03200d0101800402682c40c1d0050b410f1781c2c8003070f200d600c1071b41d10303594080c0030b0f10314012846c1d130449010080007240c00c4407030040d130b80c22109910700400e4a020403800545c1d11a4240d81c200d0b03468004200e0004031140402406102c0e914802d001c0c00680d1522020300d8140c05180e0000710031 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 73247690 1250 73246440 73246517
    0x1412040b07050d06060f0e0105120a050709030c0f0911070221030c030d0b0109050919021804090b07022e020307030b0607050a0b100e24040e0102030610 67
    0x14540a1810764000308030a8008015060b9500c81c010541c0000a00c0100419900c207032513a940d5205604440cad0143c00503410740756640310451081d004000c010f00c002e041121200380840090b02c00c0b002403008207220901e603a4480d040c404802c0480303440080c0c2008943c0200400001600c1e800d80c01151182c07080d1200c3c0081e004820714600f98071840b20611010700001440c081c00c203059038810f64020b40d0030b03038920007542c0c6c03100180402c15800727890990303100d07180165004041030315800030408940005500640218084003003030566505100031142d0181e984104052940d04020345483c403214607018602d01860b100e54107501221444407459071540010009d040b25000e900a007162040241c00d45556480d00e003410760316002020422240303480303a600407447d400703010107454050321100d030041c00d41c0392100342d40f00150460940d00041202400000c0c60a0b0f0307501c43c4555202990b0100016030380b4a0120204843c8d858241b080c101404043d20003d1226583c8100c1c910b01c070402c07403480200 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 73248940 1250 73247690 73247701
    0x403110108070216031a01060f140d1503060911030105060a0b032703040602060c09090c0a02070308042d060c12020a02091305060f060f040902060d0e0606011412040b 73
    0x300006400c810b5104c88030b2640c00410020302c8041a216000b841402c82c41503626a02c04a904020414403200011007074650580045000c0d8011720504d880b040002032131842980110440d0019035009a5005903207114070f5091046424841c00c3c4224214003c000a113040340c00550115060b000d0030000707c0c030110010704041c00c0001111442d40c1c3e03c5c41c400c01103455030700450360381e64010701503c001400ba80021580001285003582c580c1e500003409041c180c0d544110202a41e0460702d40841140b11399840000410f81c1000180080d03c94807503035004d080c02c5040031210312a4000d840710a0210b40f08010090564070010540e25a0383c800e0100b4005d000c060b004034582040182c02941c0524000103001145401c3c10102075454441d101b950307010b030f481880c000640c000807108103410003000a2030084c28501070340b040e81d440740300a12450610f03407205001e0045454140c501e5800e41d00035000e1001d65a040642e010803180b10315030041c030b8180d104515444808000d0001810072655401240 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 73250190 1250 73248940 73248943
    0x308041202060412080301051009031a0c1209100e06010509070c05120a02010903030c030b0307090c03110304050705010e0a18020d0905370201020307080c01020f04090b04050c04031101080702 84
    0x4004102c9420035038413644442c10401420b620a2140f18403032030516410004450003040030703001b1a41c20440040c00f0507140d403c03250940e82d004103502c0d5040c0040001c0c000308100000c20718041d102507001004000e02d036804550459280c1030242030703582e0000f001000160344031480b81d036120110385402c25025030940345c00c0c0c2c500076801c10340a52070280410017503200c960541c006100366000e41c3e4140a090754084050341291005070185416401844060000500b107030003103005a041490001a0214414514912600306035000c4800303812a1004100b01c0d0f91001507040c4143c01260428880c0345031800204035003c90b40b40030b04a803500840c2100503820180e1100468a410400740c910340c0400702c0c003110410031410400700e44180300701e8011102c2d8000003e0404e00700c0d81078005616240c00c0e61a134407290380284c5035a060300d640801050b203410340e4003005000102403003c00407480103902800c12090ba00001d0884004c1142440200003040c0d9041d0f030702e410706400b030070300040710f0b01e408004a = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 73251440 1250 73250190 73250197
    0x110f0a05030628090203030a03050601020c03010612051204080304181803030905010c030e0a020d140304030b01030308010e04030c06020a0e04061502010513020306180c030706080a050a06030804120206 88
    0x11a454002d2004210840540c2e42004a441032148038684250300b00d070400301c08858081502942540c0240000e81c405070080c1d2106400250500448a8203100040000e007900c505400c0b289030b001c01e4041480410200304070030084440c06118a60504d410514a565280110701c01c0e00c600d6203e82000d201e000915038441d19610f100d2512026501980342030140141085000c215265072900c058030b072040d8424800d4004034513150002d418a007003a07030204410304409040503500d01c08070110a194030f180420042000758443d0003411025031650501912890b0142c0c8010485131004c01000002540708501e0000f0a50040006803260110042100d042c96100c85c0160010b00e04503000c90503000c3c0710360500c4423000c264000e00950362003101d0940b8207000450025099801800400c280b40c042c40f0401040d5144401103480c8007400c2d80019281030050391018000c00d68400500c0000305a0f0b000d6142d00050b804000e002c16440c1d650f4030f251512070340c8079002400e059800c0000c2155509000c8 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 73252690 1250 73251440 73251449
    0x3050a050403150506180705031f080102030a0507090e0606090402070602090d03020106090f110301090507121e1b080f100b040e07090e0f010b09010e10030e0c0d110f0a 74
    0xb9440200b0b1618841c070004e040941c0d22610501800310319488170030343c0070305a62103800d040e80e0305815525201840700c07482620f6203001c40e058112110208000000744060f42c41006503a801040718141502c0141a50321301ea002030124000083c10044203407100d40446030081c000399001a510092400c2c044002e00a00b02040d522641c0050204107141c0d0541061701611404801004840344c11a40130301103600760504052034541c01c0c03004200030902648002d038005030a040584011280380303801012181d078001004211981c442c1803020038466131252000a40e001000c0340c3d55501c00314005810901d00800e10084140303610006408840015a45c42c0244131000780140c4a5482d046c24214021080310b9440024840c10000140290000d5036a8000e5100410180c800d909003d0ba503549940060394203030501488050f51402c6803034007107160320303510b0350b0b80e0380010b80058000307210b8200074075142890b2082c002040110085201c1c0a60000002e00032104c05020020380004a00d405c1020784c030 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 73253940 1250 73252690 73252703
    0x1403060d020d03021609060f03060e010209060a03021206060f072307030f060c02010b1008060a050a0b091201291f050a0e0103290a03080301060e030105060906010c03050a050403 78
    0xb941040507000103429009451132642c45103101e1300c0310840703422107075140306005900f0170090041012440603486170700020300140000d4584595200422141d038070015a100010f80d00140e400c06002d03480c01450f42281302211610725180c049214030303da5014428001d040c04008000b40b4859041c0d2528038512100d4a0058a8a83d9502d0500110f420ba2000d02075070b0060502e448640281d1041c4942405908001c002c04070880180c3d108441c821401481e480e007005400d50702083c55030710342c0c0500000380b0212403210f41e100d10b800c0901c403050403d140c49030042e03810310440c510b01c42000e00408424980001500c480c4862410005000d51035000a00200000e4243d681a07020740c0301d0300078141403038a40c840110303901d01240114221041200549400251000c0115412094050b0000342d134000800b101811a102c2e00d8103072555101b07074400c41c00701c2e0b00315458401504080c014107038000d00807600c0e5101d61070f1403400a4082e0101010080c108200000c0d880002809002940d01641d0000b2 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 73255190 1250 73253940 73253959
    0xa0216060e0102180301050106051605070503011505101403010b0d180c050a0f05010210020f130e0108011a0906120f010501030f0c0506070c060e060f03270303071403060d02 76
    0x100d00030740c0561003844c03c0210560301c24005080501946040b12425614246408504100c070100c0c80300c0f0030800c5482d801801d00010b060f9900340503c054148600441d0030f0102c1c501002c0120304000c0c0c010724002d001d00554500e110902c0e002c1928110b45403280305650320101102010014240300030f214242480d1010020140186034981a050311810b0780d031a008192550b04181c41c081e014480d0500503440032842c1c40010362181c010b8003681c0089101241000d1203400103001e41c0000f50088001b0791201d400400401c01c09004080722410460703040d1040110f480d01151454000900140c001c0c01c2c40c24007003c9000d1308122007002411044020070055031203151003c50b520818070b0030345091102400c082445e25000003100c400700d42c010b60645c0150f1070600d041d9802c2441955403544100144194142c1030021002144200c7d00c0416042d40c09030124a60310b528080f89140c030f07180354018004c011072160040b000b1060480799001d0a510f950b03660300041c1d4005100d01d00250454680c1 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 73256440 1250 73255190 73255211
    0x903050105040c030b0f04050604031803080a030e0d030b06090904020d1401090b1806040b060604080109030909110715150b12070e01020c030c09040503040b040f0906080c090a021606 80
    0xd10030794103480c4691784900103615017585007000c0450981d409000e6400c00004200068040c03000c24a11403400008540081c0c0d40380c64112485d00300c030742c00101080d15042c141030f4405051080203500704080c241000b080340c051010a80e140142003210f07000d9031064010a00795038030500c03000107403540b01056400d210801e03c0c5680c003800c04210211003089810012078030085610b040d01419036080c40040107940d80ba500e80c94840b1030040c006a402c50b108001c0440c0701c02080c081c04189600949500c0c582d145000208412220134207600c1020010900c4980b00062040c0b13020740b2901c140c80804550500034441865a88145910107403000c800007803140c1481c126038183c0e5100d60702c1600c1e000d00c26520075006a0b11199888806545038100000c40c90b034510707205429640090141046900701078403640301c0c1126921540140c0d0000c95112000c01141c907940c0102406040780703001800b2503004180106000036009032010342da60303801041140c50403010001d80c494490b04401c4c18031000c1ca06 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 73257690 1250 73256440 73256453
    0x100606231207021506062b1407030603020109050a0e04150b03030d0b090a06080309010c03050715060326041205010209040507031d0304031101050310090911130c080402010e01090305010504 83
    0x44130244035901000390000c0c01c1031901c0c50a580102c0c00032225043d820320708030344541d1f80350407499001390240d0382d07038188401e0415000c0041d4410a1641c400142c1e040c2140005004490b4662040780300311204281801000b50800b009a04130340c2c03002c41d203c01006d140c0324101c00340c42d0500100790144000b01d181525017074980c025445400090301d2a21468607035650340c105560680c02510b172168400c01c42d40300103501c03c00c05002041e000e40340032800d180f82503071013070800031440d01e070400c2c0303151034840502c10300105c0c05265a03100316840810740420851540f0600900403032203100b910307803400340011040c040e00b0340454494650040c800c2009103810b1001400a140703514080200c00b0442c546080c112400204950a81c1e8104155502c0c4040c44801110030340c1c4020440204040001c800141e40c400c1c81c002c2c0d02070030348150740341c041c0815010240003050340042c0324200b4190070700900c3d8a21036000f501107500140c080c03034444801c0c5c645c50016907221401d0351008126620309402c1000b071040 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 73258940 1250 73257690 73257703
    0x3020f100501060e012c0f040204090504060501080316030c02010c14151b1207170403020307030806010306061d0a0f06110d0f090b091302070f0510060623120702 71
    0xd858407184c032109104e0004440304540000448042e51024422508200041c0000300c012a0024900e502c2529104042000da8025600c100c800ca41c8030001e000800c009070007450301601c400c00080d0b061038104040003011200e101406400e2180c041120f07000d5902c50200c0e030f040c80382c11003846e80e48507044100c4142e460103420702c0d5480d2958a900407940295620780081c201c06841c0d2103160a00801009031468080d01500c92814000030303031040c5d003003c0c00a0102e58812402900035544902080c100640f0001c00209818100f62404400380710440c0c102004d505410440c0a100140034221008150b00c141c0941000030450103244002901550003070412003100e05070750650300322003025207050b1024082d000520780425140e48007070080e01c00740320103040301100040001c40341c0d02615107240105da0210f80c0591f86c8400d40104035044c40002c12552201729006070080100b9807424030020102e12218110041c20344949178002c3c00c4140700d1041d03800c054030b2041c4a01d83c034240304070080d6840c0c1 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 73260190 1250 73258940 73258949
    0x7020706140703030e0c030a08071208040c090e0a080c0c010219081b0a15020a03050f0f010b0702010908070b09010909060e010b1c0606051b010b13020703020f100501 73
    0x1244800114030284140e00310300e0a9118a1402424030780d40b40c0c1c0a4000d4400c00e02661400c1c0b092465031100c85d9420012401c02074000c94174560341d1604e80c100501c0903200412100b017032003260414400003648a411b50401c80c1c5000780005810101440b0040c28510741e680302524407900420440044500031610310f000f12401d80888100c0c1180800209800d26040f00140079001d0600c120310700c81502c01840d4801c200c00009482900d15560740f414650161840d4042140c0d50204800d2282601407140c44e8100554244404071485c003010201178002050080700b0300b009010a410085900810214001c1c00030402a55900c83d200e0b00c0c0103a254120080e95400104204030002e1500c60921584041e01e82202a6030016804c2c1a9500b116900c05a07080740740d4022882c80c1e50501210f4800c250291409a030b035030340d40d0103000c0b00e08800440c1550010350b04d03915015840d1402da88101340d0ba031044502c00805170320b9421a0605a060a045040360002030081280b80c0d082e8082c2030b80014180e5 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 73261440 1250 73260190 73260193
    0x30303020d15030b241011070e010e0a051e060f06270405060607120f1101020a110c0102010608070302190f06020606210c01031509150906080c060d050901020d020703080702 76
    0x20544132245c4445045410341550060110403e120196200e03640c9001d101c5201c104580c00b5690b2a000d12000709026441701c5188941f86050050b0081503000e000d8120400901e111898410340e400444480d80180030584a00c4440d0188103072901d602d0181c0741c00050300045014103519403c040500700300b29607503c4e44a5403070b040029680d40b411300705540011ba00040649410180718800b80c8603000c05a00e40c5061150104102c1e001d01c4003400206030710b07d082d41d07403244400300d050842ca2400c1e20118100b415a410503900380b082520024540080380e40444481c608241c003a030b2020320000003030300460f000b00001c02000c01c2c040e03000912103004010603610a01705828032809004914031041300100c1e90f41101c1d0003a03042d503209801058404440c5001c804a4a80d982d00c090101e0728401c2c2170340d24002100000700b140315014418100204080806007126003040b00000e01c9a01c2000d005058856a40000c03030070f45030007541602d04130381841034215503901280c01c000d08441022994200103 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 73262690 1250 73261440 73261471
    0x120307061d150408070f0f020108010602070b0a051308060106050a11060c090f01030f0c0207030209090f03072402030a0905010b040b060d0b0f060a03050711060601020304030303020d15030b 83
    0xe500e610490001d2030001c0c00041c180088100c046461086005441542c241000317000b01c401140c100140501068400c2691491011040c4009442000140e0001056401c0351100700600c0c0210400c440302c14440d442c00030f50304c00c050400003419036926084824244111030001c40d0321900b1600030007200305651a000000d402d19102a03540741c4007100d0200200754140f190025604151481191145050401240b02e1015444c5001100c0b0800114001644804010425801c03d8510107810400344406031014000c003d004d01c0d52480380702002442c03c504054801081c4401d481580e51007070940d242035541b4107056500e40e0107001140c00070b4542e5468419852101d02d4588105c282240b80a4034007824041c2e00184030008244015940d038100d0340442c03202219640c1c0740010104180e85480008041c102003600500a4420741e403914241d40c0008184070690b0303000015901160342c18a80940c1e90016041c410300600900c1c1510080c2080780c0740c020042190b100c1049210342004040c6021 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 73263940 1250 73262690 73262711
    0x7060b090a020906180607051b010e0307030b010b03190f0b10030b0102070501031508060103120314130b1e040609020301240506130b07260c03030a1a12030706 70
    0xb2445030b00740c020b078451410042440a07100c402c1070b400342020000d200c03d04000d103035120f450401e004188903403a039400d07030031040b800c540e00311189080e50032083c0c005040e25810742c1d8454a40341c1d07040c041e201c00c1903400710019000640078041d003143c1118084040c85140414040c00003d004d9400a0320700c40c00035002c001103912700c281708040a0303000580c01461551300e0303e8010760040407111286488840701c0c54010400450400006000314400c0b00c1c070150b402d0300c1e180010102c1d4550a058030b0490340d1003090241905c4d0f92000410000d410410707600f16034403400100c01c03004103010300141e2910a2441040203014556000c002c4513402900280f00055115071f80c0407140749110181c48280005447c02c1c00642004400b520385880308400209e460741e10703016080103a0300800030481300040c0401d980f4610700d03c101503081d1442c040002150501445215254490100602d01c1c01c0b000c1ea14040d9144860035805841000d61024043e030010700c0c00660061b44030341c002c90040d102142080c20100 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 73265190 1250 73263940 73263961
    0x203030c0706020105160807021005040204061a0301050909071a0a0314040b040b07020304360513140a02090604020c01091202070806010e0c04030201050a0203090a12140f0d1b0807060b09 82
    0x51017002c05601911070752b040144060700404000d032090ba000f0b542e4502c042075600300d914031108240c00d1819020340301d40c904000c200c0720440040c803014030307600024010015000c0420508502802001c0d5407912048214004c9004000e10403034a054010341d20280820f01840f81e07000c5009600075843c6040c5981c90b89000da0340d922540c4546d89100341704e80040614040b90500304645544540218031081826400400c1624800c0e140c00d180d601c07124121008210307004680000445403000500400400358000aa101c80c00810f1640240e40000300305140c00400c7d17020420180c4d11441c86408400c40080007940c2e01c200340216083d42c4100400455007030400c101c11480382e804410f04c0da280c6403e6600455180d00a42c0940095110600c0010003550301c1c0d45082014200707149484a4403400780c100710241c2c90f044142c4044503005401d08a00040c00440c3d0000380043c0360500340d600309404034030741d01109001c403405400c001303011941d002000701c3e542007000440c4044501d01c0c100e444c0c0c6150007 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 73266440 1250 73265190 73265207
    0x1603030504050607030338030706020c190305070e070210050106080601080a090507080c01090501021603260a0302070309060503040312050717040b07080906160f0306050618010201060605040503190203030c070602010516 96
    0x1c2b000b41c1d006180c0384406189c07810710080844584011490150f9403562214644102030f00000e0b8500007207400c0014181e4104000c880c000d181f02028022545400c00c0074000d91000b800e06410810880000354040d02a9085a03d1039640003040350384055a07020142c0d02d0300310403c00c1c01d0000300740f40c40008445d1320001c1c1060035007017001e05c050b480e10300d150f54601c01060b448803180d14110910b280c0d8603144034154003070f01041c111a1805a5601003520f4010b1107492107411840520500f801400b0202754042d69044040103021000119070311a9131050fa0019241800c107100c0811860401c41000b5002201900841740f503141c541407506e501000d0740d2500c108955041c2203400090b1002c400a00c5005040304200090800050150719400843e103d41c1c092200040d032540c14214003009942d0901c40c4038000c2c6040d02d003c03414a4106000651030300600e603441206200c40711004411366806000301c0e81c2c11600d0000700c03103081e41c0d100c9010b8040c050480c4d0320302e80709240d030741807031251402880f40 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 73267690 1250 73266440 73266449
    0x3050a09050304120203010603020d050d090f0e07111009030507050d0f02030f030709030c060216090e0d0c020301020417060f0a092d02060a0e0316030305040506070303380307 77
    0xe14203103420700d040c245000e68444c0c4244e03403540d21000d000025031100e02102c11203034041e001030000d83d40642000707420150107502070416100c40117803c00c42d40102403491030700040107151950110a0140b0355500d406410244030003420705d880e100d00101500312000b03100d441d00c21403e881801c89001c5d0309580b00905200740e070016800822101d0144606080110740c0035a0314180718054546036111902c150129422100250f402005001e25950000344a800240300e140c0f01072060f0240c5810b060b496410041c001c0c01403025080f0900b00710742c0c082d01580c0180120301c40611622495100c40d5907a4082900e00900c1103480d40c0108500011901983d01c000360055610b40c540465079103040013041180c070b50b854034410310a00400050b510000180ba0780d40c440c0e503c044900c6000400c15040880b95541e503588030b651900d00308006a0480c00b85c1e03080f50303012a9866150495400e00390040e2592480324801a281e0180c24034602c4820305078000c42ca004501c81100340c5c000907060560307a0006004 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 73268940 1250 73267690 73267693
    0x5030114010806010315020403050303010e060909011a1002030c010203040c061206030309030206070201052110050a180c020f0f031c05060f040507020a050a140c01050f0d02071406130303050a0905 86
    0x51000c01c2d40c1d140c541b56900c0440100511389992910386d0b82c00c5400030b810000036522a182804460303e040ca0702140c200355070400800a03c882c410b252981d044807040020f002e241010101184603000f40182c0354003031289402990383e441d1134980501c0b41915401100f001c52411601c61001580c0752080f08140c0b58141c8503040d41034256000c1100a030081c0208038100310301040300401444641164071043c22070a0100030381d50a0281c01c1e01400d01c501d0700300b5400741c03000b03c1c400c00c52460034100d803452444094034001343d0208a6101207052000040c00d6805a100d81901d034004404000028650051360003102c480c0001c00707142d694191442503400355402095500b803003070985003d0303105a4101900d070044031100e600a907540303800c10644440607070392003819018804000406002c1c4e248400001d10349141340c4128403000420601491400034001c541c00305845040140032148003206e40006000c95602d813a0088c2c0200d40c1801ea42800c40c0068141004035050540d036000d0402050740c00350 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 73270190 1250 73268940 73268953
    0x71403010506130915080708120d0e0f07080313090203010b0702010305070219050a02100203070308070f17161107050d02090406020405090c0a080609011208030a1d0106050301140108 80
    0x100819a00820f40544015216400004007480c00380b0620000c4076100c04e0311810707540b030903800c50700b0a1817681c0b0405194000d0001540c1040c0d411003100c41404503a82c0015121000040003850b20100000000c035512039114040340c00c00000020b003d4000100f00007208090321880103100303a0000f8401c141e05401c060001030015800794001d6603010300c1a10407a02c0040d00e803160035954416244094825400060458040d0305100712205e05c1828540011880c1c100740f41d40041100c40300610b030000b00051f0362704029220384106420740750b0b900c605180216504003051261f4840d104004201c0204840040702c2440100c00300d00e1800b1a50010404040000da03a000d10481d000b0080c4100c0f5120390800c40401c195480c040740d2802082078407040c580b2030a07540d1014002030000b83c8080d02c603504a000401181148591440e40a44c0c8110600e45a441d800d881c540039103007901e80b214100540d03404d80701e51408154031410071100114004d0000800d440300c61a21413000b07008150150700680d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 73271440 1250 73270190 73270199
    0x6030b07051c0c030605011803080324090f0106021c02030409020a031b0c0b130b01061d0901060315090e06060d02030f0303040606180218130b041103070807140301 72
    0x1040982030000c40c980721080d030408030b19030080480e82c0d020341010109964104c10700840d680800310300355800030b030705840170143d0a5480300341d406d00008004015030a246901c241282031403001154054202501ca1002c50a0040000f810f81900340220030042c854020f040d050030100c2d01345421031603600d0b0041c0d45424100120540654402011380080c1911128840741503800c4405140d5005500e56407102c5848440c80c1a446032074000d8044514006000350b02008503150000355030450300182000f034201016544c40003104002e103030025522804a000000b20250141c0200840001e2568040c07011515500442c2c102c507e0801c0c120016880003000a00509014501010940c001803c540300d042204109510b140e20403182101c031552a11000c11665110b40454400e42c449841305508086807105080f0783c1c040040c4107540700d07441c4001481031022865205602d2181c000d0301c1403244e04415901303104103034810b446020025410381c0001d91943d00c01c1c0196050309101108031443c4da40780 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 73272690 1250 73271440 73271447
    0x181303050919080d0201110a14030a110705061503190605090c09040606090f06050d0f030905040c05030402190509040308041a090a021201050615030a020f0c0f0105010906030b07 78
    0x540c1c452034004110441100211140001c0c42e00244901c070001c110110725401c0081c290b942d4000ca180b00b11405011410100b0741210541c21442e640074100341d01c907a259000d00d00039000c00403000c104920002200002d0110100b42c141c03268030808840e921581c0350300d00b81030340c0c0c1c080180400c800082c900c40036400100300d50007058100d01143d084420803603456001072480a402d035001c64100d1342d103074402c200443c0340340501000c0317110303460007001850f01c2e00000c5940102d030031900030065035038034142d40109405100d00308007500010f0000c105140004070042c2c030550050f6802d07031048800030f1003080e46a400108030002c3d240082d0a4001e5900d6a83c1c041e55281809801120110350204450040003900500c0c148526250b40c0104100c0d0628014041c0104016056040f245d042000700890341d118244030310305001c501c605080d560f5480992100082c0110b80941802c0b400014102c01d250000044429114051000030880f599980700c5d2030044410a04c001440d4031150300009094900 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 73273940 1250 73272690 73272697
    0xd05090127051005120618013302070303230f0c0c031618090512090102010609020409021213030c030f0309120206070210141305070806040308040218130305 69
    0x10245051401d0b0386850009404030800c4075a000028404540c0302c2041d074000040b180c0141c4180c9800c2c4000c0b0a1004002e45044140154010014508080514560002c203000314444c1c070410160394908481c0700c020345a40340c0b8401600042c01030307075410f43d103606d4000c40844c12055041d400c40c60b05086003550825608004c2c00503d250107940c5c00c0b002c82d80c07001c1c0801103c0400020010b039440d07040a000950746480c83c80200c403404c0c035099054000903000291421480d4004084a80b44c956140040340904076070303000010824000f01c0c0c0050ba00001d41c021b00f010090f01d44c082c4065a64450010000120414010703000840c0c09071194082401000d54015880c4c8905d0042040308180c0c68880e02c010040100c0401a486901007040242c1d042c031640e4541c1c0840c050a00203605c94400d40d10b07225034080c00d8a05030500040200081103400c1000344011310b0f101003542c44502e0f081c18082d1a04100711816070180d0782c1901c01804072094450140c1c8150b8803445102c0301b02000b40c038102c54980 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 73275190 1250 73273940 73273997
    0xe072106050903070606030c170d0207090e030d0615030e12030103080708042c090102120f0c071b0602070609051305280203041b06090e04030302040e01060f020d050901 74
    0x200144e42c089601d40c0a480c0245001d218602e401c585081d015040c1c580d10b084402c0c005800c030300140008030380c1c00b02d4040100c4110403008110030411601450440c400d1000400c0c00074a461400100c20b10f15a410b40b030b42c8250394800b0024030000204480d140d42c0400110100c0d00410001800041d0800d005807050314000c122081c142600c5202142c006c03650101d03016150b4041880c0c0d81305a03155248060350148414000f03508156640c41210a0544042c3c014518413111200080580304010292000260001e0145220044180c41065408502d000d080014001c040003c10000d00850005d811500d01925490940790203c054034010b1402409420302c0301003842c040351380000d2001011080c00b650700b0f401039882c05c1500d8040d003807590341701c00141e1401d03aa0108006050b0042c804000316100506c47c004156250710f0101c00074030494212103000c0a510b000400c116038031110690304007004d48c08903440301360204416074182c01001145030002c0c130107440d401070103a000780c002e50340749 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 73276440 1250 73275190 73275193
    0x60301090c050d0c050304060b060c0c010804020612040f11030105010b030c07031103030907090b040504030507030c15140720071a0910030e1c0804121b060e0721060509 74
    0x304000f1421070a485071025110005003006c010b000912082e88a001021030040703400a1400c4081361486455403800c90182e03050104c0074000501355241da00443d800d04003981c031200241e10f071500c0c0410484003080010380300c0d403c1824284c44181014801c2d90b059030540c000450540e56000c56680c481e41c0044002c5040200380380c80d007114a602000554040c98441c40500180341c00c108607002201d540d21505481203040909120129402604a8050a4261520826003d0a81449a216404030f0b03204500b181c0b6150070908101c9046603400d000e0422591941c4006045d20104020b03080395800e110720503009210108600a6101c0081d9101c2030388820083c00c0c544560002801101e902019101181e200d01c01c108002710140a90940b94a07075004900b0991035040e002800c07084000c000400380e01010b10070340c2170580107480d2044890035503070351642c410f03982d0f142000113070100707c118204920910501140e6150260f10301c1c42c044400d580c864004440540303801000c2c10f409400e01055 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 73277690 1250 73276440 73276447
    0xa05040e0c03010c0f0f0c0209011e15120c0203090f060306120102030a020a030b100203090603041e030e041b0212030403031104140f060405130b0f120708010b030a02060301090c05 79
    0x11510203001380229041039807910041500030b104042c03d81d2908040503c2040710010301030700117a48005a46055418040e0340500348408410b018842003059084099180303a40c459038070040d07500c025012080341590409012900c144081a40d99003d511000356201d51075407044070b03c0341490320103150b02c00303030080c10402003060a40742c03182268000c0d2040c1015a80008007140440c1d0180240214841d003504e48120030301c1022b000948074021040c11510880001000c6001d00481040500c0086401d001c0751008151a1801800d02ca0b10b0505083c007440c10300e290101c02001c02c0e16080380c5d000c5c1030b8000d0032402120311181805940010801c40034540c0c0e946440540080810280c03000d08078100e072a02c107000c00d4204002d0b020019021281c07240d2000c12003809552106400c41550341d212400204010711810002080035000d41e41070b50b000081455504020940041c2d45401c4034144402000180e001c0720906850715002200070f504001d040004020425096100762060280b500e031480c10b = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 73278940 1250 73277690 73277713
    0x501150305100b19120203060610050307140405040204080a03091a04060302220e04031d10180e0a1a030c060702120a05070306021b06042003030708040914070e0a05040e 74
    0x140341c030240d0017580844180220102c11824200f2083d0740000f0b00301d6030703880d001821004c001e01501c8001c00c0402040440e50300400115441400e0714040c0a0042040d0740300e42c0c50f101d2269866000303110550004003c4500002d2020880030f018000050198401d4600340c240502600070754132840000c5103070701590420071803240034066224040d00700030a0140aa00300b078100103114803c0308418141d21031200c200d0b43d00c5507446650041c52016282020644807101d03800c805d60000c0d40c3d07444442000082020800c82c90b24983c00f01e4001280051012a003018507802c1c0340d0703241160a1400d421140c01c01c0010301600d41b0800310355540d0042c0044a44002d5169562401d02406500444001303401003140b200e804080d8020306e00d60802e8200a14952a058451085803031090f030484001c1a00000b01503a1912b05000f2620240c0d00200c0403590399a943e403031003000317100b5200402d640310f1100011403400c52103135508a030110001096012100d00700320411000740542c0c0d5180009202c0d0050100 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 73280190 1250 73278940 73278979
    0xf270303010501030c1812120518010c03031407020105091020090a0b070f02121501170106050a030507090c0804030e09060103020405030a11040e0c130b0a05030304120501150305100b 80
    0x75080360322000104800e03901c8c000c0c054001d203a880005100050050705c551907180d542901700213900f460504c40e203154505081d0014006161005c090040a10400420540542126014551800464111043c000c8400c4100c1e1a401ca04001d0102800c45030201c0341d034080003500400b80020020300380c01e5503926004410b540016000c0341d0070b44071a08100c06601e0018441c028550400c0301030000c100401410318006d80050040b06c0354070321000c0d040b0048080035806030002c5d050140c10707070404613100d0034216907510003407041821450900a28502c101e00c106004d501690341500c5074801005054200012448018031040c10560b00380800070341032741c0030400200c619000382940300d4224070340e4082c0000d075101c0411104490f48540d14102054451501d1803a0355080c251000590142c2d01001070b4154145070b002660510000c640403480100c0a100e5403c000e03c9107008010190080e41000035002c490312001e800c81e00b0003811f28400180e1038100d4200c400006000301100c1c3c00044900f07 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 73281440 1250 73280190 73280237
    0x106050a09050a060b0408030706090302100e0715110607050a1809051501140f0d11040807090c030b060f030709030b10081203061c030c0501050f270303010501030c 72
    0x40030780700e8849061240b01c0c00c0900c01d0340d028095a040b0a49800d040021050341d03440342810040c0301c07036620075046040c58801d10440d001c410300f5910902040d10030007142e550303401c40c42c040e03100035000030202201c180b4015201c0e042e01401c5036024280c0b540c2c800230240d17002c4d000b10760382c1e000b8880f0103110050b00c821813044020203807500c900c000070039082c03103d01d00209511040d0f00da410700c88454013042c0c0d080d850320251040000909042a51028101e06c600c01820a458244104030004103020032605800310300c410568081480c06c100b503039030149003101551040409907400c4401081000d940141a0700290360109132810021403666590b80ea030050f0003c11680885003400c2c0c80c138184602070040c4030403600301080340c0059045080445c0003800d83d0003121041d4030380114201480c02003501840c2440ca801790818020001403a00d42100981da103003c442c000980a00300c00b0b5407a01c0c1030031904140d95421883c0c0250300b0340e8200001540140003103480001440f50394401d0280151142c2680c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 73282690 1250 73281440 73281449
    0x3020c0d0507050f07080601090b060c060c070506090a0201080105010309061d0c01020708061902030403020a0b1005090601020303040c0e1b19020717150c07050a0c031514180106050a 80
    0x24255a0019820002d007413010052041405400c00441040055000968a81528095280010000500c0001807842e21401d0940b01e19409120100701000a0031800f134160700740118203440c1c1c180e0310700c050261154082000240454984e00c01400954802d1b445205814403c50000482200d0054000078044d104030010001e40d11070840b034601568107210f0400140400030041083c0c0c02d01c00c1914080c07505082c4030700c805036808000241454402c00001401c0e07600b05c401410385050080e107a506a141ca4002d690007480a440880c569520000407a031181d81c201440c0c0100340e09011403a02810405040d1045c1c505500230084c3c2100d0300500100241103034001c0c1d940e0508441c03031002e414408164400218120f04144109140700041481c030402038a0301d010501a654417290344082e8010454064290311a003164801004025a100010f4900a24810049010300b05640d41950890000c5050601e86000414928001000300e500344002200c00440c4440d100d82c003107003100205521 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 73283940 1250 73282690 73282697
    0x1090b06011d0a0909020411040b120610080a1d101b0509100e130516030b060901050706090203070e310809130b0301060609030303050f07020705010c0303020c0d 71
    0x5100c5150780060b80c1060010a04104480219030b4400042d480b0880b44240803002e52580d808200315562a40540380d110900a1100d46941e00c0b0307a00303100c040e0844a44804800200e502040c0c3c030381391030510f00d10000c107687d0703074101d240d6202500300c405007000380050503018104101c540070628050102c10080034588900081502c1100205504401c3c8103604030103000003040380d00d5042c0c81d2425840400c04035130809030072313032002032000c100d05480d1200000a501e19100900114400da060f0749406e4000a550030311146d0030305002c00110b881100c2e642400b040041041400044454019060542c0014103503001d0a0785c9003458145141c0c11651f0552095a01c00c07a100d0318407062440c801c0030141c40554150020469540c0c41603407144150240c400c65140300c04000758a09904091680c2801800034010180d903601d010340380074824003040300806d0030540059584050f2041003846071500e507005100242c40c00c00150b0301d004100c0030580c101502000140741003402000380540e8000e490740c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 73285190 1250 73283940 73283963
    0xb01180603150806341407030203090607030507020f04062102030304090504050303010f06050a09030308060f13050a0b0409020303310e041703150112090209090307290411010c050109 80
    0x442c941e8016030320030300f0704422051041040e81035104000705048800c82c030005603500c04230b007003d038a14000c3c01c03509540100001901010560301502401c0d60500c241c540d9620321003800108401e60b4018098484641d03800b4081c00c11100c4070300740c808050380c00a0152403405441742c2c1d681302a4cc01c2243d003030740d581d44000010804401c1300c03031782d49008000d640707005414502d01085c01003c0550910000d010400c03220040385656403541500410303040700a10844013a011032104902504040710201081c9140c1400c00d562414a8011000c03080d07070003800b852910880f110074405c00303017035089000c0f50920780c00390f1081105000c502290140181c802c080049140901e480b9202299814022b003180c2c0080c41482910325080c06280c07180402400c24890300032001107540020950a60301039409084142802036084004c001031603100e00070a50401c4500c2810a0b02e0200040c151060074034a0b030640009010900e205401c10b13000348140350690034607a447d110a07080d0355501605440c01005403 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 73286440 1250 73285190 73285231
    0x810020408070b0c120310080642151303200409020603060d11060409021207020304120303050c0702040507050901030f1b12060b040b07060b01180603150806 69
    0x821080c8001c200070f40c0302900d403d420560769a141e00b8031071454540c42c807010000c184a0107200701568081c000d41c1c01100c1d002c0c58107402c0d1200880600c03042104e52031640c6100b540d941d544440a61b000324010280000380c010326000e000c0941000d01c810144070b40140003040c1281006065000110300501d01030311519010701c00c900c901c481b0002c846104a00e17040c610801a121401503d238803000c100d40207421000f2a041042c03041840400b8a0780c0001d0010b40451005400d9010302042c1a1700218000140e5402c4010303070b66885540070342c01d40d075046041d1080000c1e1103030f040350390710150751510181460420341c085402d940382950326002040d0081805031071940c5c10301c101650103400c0d41d0140401840692420514030001c02040100107030011195190130700b07600071100070300c03c1c201c216650390350b90800d00c20305070030816040b96290306040400c480c940c440d00601e910101a9001403095a240181c00d400070700742d0450350034031100020030000f07601c9000c0c003599209022031041c2d081c41e204e14 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 73287690 1250 73286440 73286443
    0x1b050a080405101b1404031a0405010603170a1103031018020d11040e0a060302100c05030c0f0a03020609030c0c01050c0c090403020304090e03131a0c0706091703090906100302040810020408 83
    0xb6070105c009114418042000821040000201743c2c5040901d08280b540b518106580542405c1d080501028802d90718000c03007440b46002000d0000055441002c048142580c4070703280d00c0262842880255100070501110010b05078440040d94950401441d00c19481c011200341c1c1d692050300005030a02080800849400c28002540480c401c132080101c83c4c1190300040e41180b503144040200300d0042c04401c20000b0800444546815031400c4039055081103100b669120070480040b00140110ba002c00c0040c540002030760f08904506000c0c180d00303150000110f8040e0000c0145070301034819501500e0b240d403507503420140034074000d40c0950f0b07440307051084c00782c00e4540f0301d803013111640e1040004541d46a844100c01d4183c44207140740010200e002c4d034044031140520000321940b8000e0890010701c3d941c11600302000c940001c0c07000641c80380760855840d103074044d802c9202d401100080c0014610b1400400349403204559040045c1455203407204185003000d41c0201c001500e45c0000e050002000 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 73288940 1250 73287690 73287707
    0x30b1906050a03060b131701110c0a0203071203020c040b0619270303020303060f0d021206070215090616021204080606040605040606050708031b0a03050a1b050a080405101b 76
    0x120b9001c51030003401d50f004120182031840f03445000c004500c181f50354898290401c204402144400a480d40005145541c4070504032204a100b4414150b00003031ba01c100b891903005080d0160007034581c8031024410b00c00501424005180d014500f0000d0802152058074003601040380e6955a10401074441410304015400c0344400e41003c4190b001040020303030000460368481310a85082c1c541041400101d01ea800d45071400039030169540040c0070302c56000068880c42070205070700702d238011248440443c6104001360b803060000d402c8100008c4541640e190303411402c50a43c4103c910b2160075460300407040d00150070104c5640c01c10b5050110750700d0540a6007000d0902180d082100510f8141c0250851262800042c040c0c2c4000c00007595900e0300a00038009206a0001c165480c10004401401044101c5601015170b00d04250b081503011866801000300e40207444162a215200e281910040801070044440748a0380c045030858100b00d0181400b1414000ea80107410250746002904818 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 73290190 1250 73288940 73288949
    0x30806011b03030f060f0b03042f010804020f0306090706090b03090c0108040609080409020702180f1306060807030b01030b0108030c0a06110d0507080a0b0301050c0307030b1906050a0306 82
    0x841c1c1402480741c841458480868180c0c14200003503841e100f180d081c009421309030702000d101948220001100c1c0800310003144a01d204d4254040b01c40c50b4050880e01a00c2501500301e4940c00201351030f0358a501420903560000c0c002004045130000100000c1d20740791003110a01c19980007090708100c030301d8000711f03403501508000c0c400d6400c6152980390340c0d43d20030314003070f03404c2c100561640401c0c1400050f034403a03404a070f04078140f01d51326521260740c0c1c0041d5200b600c2c224001c10a0719403100c102d18483c00f0300c0c2d008461040942400b43c03980310014451a10f150030590710389940740c9000421490030011400290300c550301c400042e601d07506100d100d210059108660135001005401d04800010400d003028030f903c11800141200030341c01d0b031a8107001355020040807501d4003003403114440d00410124805d00d40d4100c01e01007045600d0030b050a0326401d41d904410a0000e0010a000074000c1d00884903544025091000c000f1107a400501281d035240c3c8040046031000806200e06640f5000358800f61 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 73291440 1250 73290190 73290197
    0xb03060402032d0102030c090a08030a02060714040509010e34050d02040e07020601030507080309060306130912030207030207140f040c050405150d050105010212180301060509090a03080601 83
    0x2450103030003003600c5040030003d524003220540001502900d00c0fa41d0100c0c241d400d18005c42d182e203410b4548240d540e014501d0140f00f100c5200001449110000c100da1322a503540c0e000e070580e40c40324081a00c22048644010b80708840a000115694580b96081b40c0200141030a403138035402d03d0782000992a43e40da40700358070b580340c2c0d010512a000346a88103980245c0c5601d40f1948d100c1e0310015402c0240180d030086546190381006000c005640000d00307074141c2e800b44d8103961204c0d5440c05400e643e0321072880741940200e001d2000450034a0002510755030380380821400300b0070030303003d540f003000c999520300701c280110f9404681d000a05030f04010000c041e140e0020081030101028000130a01080b044c1c9192046032103807848000c03030348601706a8004120103000302e2040c10384244030000700e17001880d242941910300800000e040d0710000e10380010b4003140d60510325001c0070306c02c0300400d205d50480654242d900ca103000109600c034041e90794401c0d40404041d00c6096058600245981c201800c0300c2d040 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 73292690 1250 73291440 73291453
    0x50d0c05030f1b040e060303070c080f0d030204060210110415020a1a0106050403060b01020a0b09251203050d111c0c03050103080901050702180708040506130309090504060207020a030804090b03 85
    0x107050340d440403030f1305907107140e060360603695141070009245204019004140c0d10060000241c01c8100084070b061a60500003520100b440c1d03804100c0407805544210743c010b9001344900d00300c0b88815031044448008048a03e85010384940054465075000c02c3c1d03c60050384005852824454030003281c00f004043e5041d80c45040d45010342c014068000d5000103848250382d003590241310ba000700190a54564001c91843c1c00e8503001030074070b8841c0350014517a0079004601c0c990b8a400004400101d080c1c6000400c3c0941d220010b4408481613007119228000460340c030800c0c00e240781c00e40c1004c0e028001d4505222502d0600d0880c452041d20304105140080c541400d0042c400155904c06a13006403a017031900b55119075450000841c5a040c42d0681c9214100700024010f000307900101040c0310781e00542c11103119403035a20610f0403030014810b007e40001e4107801c003400f80c5016038200540140c0251030260504400742c0000780c03102d0300d0341d004486011001808021121a0340a4090701c000118060300d03d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 73293940 1250 73292690 73292731
    0xc080d0b030c1f0f050910081806040c090f0e0703260d0501090c0e0307030b1f0b07020f010c1101080a0f0c020a020906180f1314030301030c05150a080601050d0c05030f 74
    0x705442820a11f070603c00c605000600c50090998072440b400040003c0798030a08081c200110419018000c01d002d940c2812459200d00c07203140948408182c0d0440206421450768946c01002140362100303920046840440a6900404202601c10303110443c40005071545084103520407242415064424041c4031383c807a040950380070034132000300e82e08444c410046541e60700c1c00c1e203012030302c0358100504084039102c0881c001011101500100b842500d21505d040100e01c019105092070304002820600642003503102c6520803e03d450f0031200030b2802003400410081c80d0703426035041e40311050061b4081103042c019880c0800d60b840e00808140d410100c0310200300c000008855000b4094070000058a010031001a158200142c0341d03034201050f0b5a15000c1d100b840c640360b90085c03009599000030000c000c2a02c0c9401201500d09500c50070615240041810054130581002003159041c800c0502c50864613041c58081c6080903000c5540305a0360380b03411140040440005086003a602820415154 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 73295190 1250 73293940 73293949
    0x8030a0b0f0d1a0403120f1a04021e0a0e0a0303051e0a020a060b0d06090803181b010c0f1e05010e1204060c0602090d06020a030c0c080d0b030c1f0f0509 67
    0x486000342d8184401c555519805c0640383d903141e841e21491001d1600b43d41302264907203603010b020904854034000980103038087c10403099000e032604040100c1c03220001c1441881c2180d00900e18006035051030406811848006a10032640c2c1c0c3c401d070040780c40051403d82e01c490f804060b042030b2208402d418244110107900039640c903004500240441d546003840085c90340d0b21601ca0078a6030f8482c20a2003030400a15042072309804c1544c48047e0201d031060a04001c460205070120340b0f0325540502d0414101101c0115180c005100301640c0000c0868050004980c3c46180c01d0881000300080703800c0400c06143c1142180c01c42a1a00311030340000d80150105109081101d00b02d4070320340307050700c0c0346005c0c2c0c01d045000b8419140000e0b4880203803003440003002031680281108800c10b4078100202940c0282c2503c40d140780070b60003040711008202c0d0310000d000d41d5004803c44c0c0405030403600c0700514640821a0980b0f442014903080c10081861801300b50310a607181c144103841c0c03400070708001d40c3c4800708 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 73296440 1250 73295190 73295213
    0x1030b060103090b06190e070201020a11060c03071b170c0f010b0a03020631030209070f08040b13080c030d1506080103060506010309020301021809070c0b0105090403020a08030a0b0f0d 81
    0x1502ca1030942a00c1400c901c20100d490000d80b1f2003494150346401d1174070010707000b503000481c0b88001c07903081c1544151408000c00c5041c890700c8941c40e2a807555030750040480d0400300003100b040c04140310182c0c01c0d011034440c00710981072402214001d0b130341c3c02199003418901003050b1940580f581c1408407010080c2c480d44844011a68142c1d60292500d4888a1512812000c1440505891280342d000c4c10308129400d504003c0724029200d0101c1c0f625114422540c2101554948011412035400318000a607008a1035600c0f1461141301c1503006241d50305c1c2c1c90345621681d041c802c56440441c2a401d010314510840e00098694800703074880c1803070100c020384422014440680040e688030000b40c09a40281c00911405030300500842d920031a14000e1a026030390366503428040d03217824000580e55405020307035601c00d5030081e40c8003a1507032130700f0204220050f000748100c00b180602014000011071560245004000070f80f4040380ca84128428040000c00c0c0b104038a106002032407800d00854021081c0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 73297690 1250 73296440 73296451
    0x10204080312070e0d08070b010b090105030417090a031b050405090d0507020a05060a1205010f0602190804050405090703050d08040b010e180d020708010b042d0e01021201030b060103090b 82
    0x2041d90742d4000c8207035596144d00c0031081e0000c401850000800420900808050381302c0e213010b00d400e90300c1e020030549900a0120140c08144104046008038090100c100e64000b50200307164900041e00c80891142c9400ea8402c80b40c02020f9805850552440d80312000540300640d0100300510700184000c0d911458010f881043c058005841c10554640c1034444d0090040a0300c0141d8808850100405502400e40c5000d0001d160900208009807070894540844800743e0080ca10782140c1c0380086541e4100c1c070700807900c016042100003160388480c026180303d1002000034014407490b42c14140d01301881400c0382000c20091504010020b54200346c2d480c1501d0590711103050a030341d1091a0312682450442c1318015214a030062402c16500103400d00550343c4100c02402080500d00610040c6d07035010006c4034071040d0350113691900001640881c01040014a0049100c9030040d03082400ca034024080f640c1250000d200600610503140e126075013000080ca800c10072151145c44030240048050301 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 73298940 1250 73297690 73297717
    0x13050601050327150402010215060906040c050c100204030302120406050318010b190503010e032802030409110a08130b0a0c02010905100617070303080703050604090b04030c140102040803 82
    0x82e203000c1080500e02e41d07036501c0380c02d00b25004d02d54500c00c84005140110340490052040c8100b91240c4502140d00038002d04010f080c0003540d4861038100310140241d01c5455081040902c804442808100424503030340f02d01c640700503a0340c0d007136080c000d060000600390907801d10004c0004015882e444411030303074000030384210814550560001e403409020345480304c80c0c0c0010b09031144440155050181411101e08900800a010a100349191240900306203121500c48000e09190a03d4041c102a00305120a1042d07910709501c95105104903500c55030414400b0380c0c04038aa08180d03401140ca69000680c803980920361f02d5895a40850070301009080c03080340e540b24441c0d0f40c0118000d4009a0b80264007505890f03103002408403010042525110740400c41ca079402000e01d5144c0045510f9050b02e0f010fa40d45003003690b0300c01c0140c014100c00b81810389c209580380b0f6003402040c5403000e4076029900ca070351508031035070310303408d0805070070900c0c01880d000e90340b040108000c072400000072158034141005 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 73300190 1250 73298940 73298971
    0x30c09060702060a080603100c08040605070c1b06020118020607020d0206040906030803040203062d1f080303180705030c0d0f0218040501050c0702010f18090606030605130506010503 80
    0x1804501240580e00000f0b410901c041881c04440b03412603100d0380301d1502070b000c8550b00300400c901602940d024282c5180401d03055404500401c003035400c5940e000c0844e04010307031a40c180d691100b014010804120788540394000b0203018007542070041c00c80c6601809444d282c005c030107400050f05842001c500910615036104943c1c01c40d1101c0c019180202260142048816540d0903c002207905c2200c00700d110380140c00c002508480030101c40e0031911702080010f510baa050080105040c80090110300f101c0e507004c0e065180c00360902144c1801340021101564490410400c0e26200500400c800d01183d00100d0050205880005440f0325665080350f0034070b402041400c1c5412a9105182c1c040c0d0010442201c1d454004030041d03019015510a400802c190b94440c11080118060004000e0014030b030340c40d6441c400d43c811144807000c08250491311501a135150801d40c00c5502d6076100c503001c04c1c3c03500410000d0385010b0440c1808440c0f03801d410701c000d19243c80020254400249800050b05804 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 73301440 1250 73300190 73300207
    0x4090507030b030d030b0301060f030b04020d080408060a02040e06031f0b0d021207081009080a0809030d0c03050105030f01091a07140301030c090e03090a0303050a0c020312040801110a05030c 84
    0x940100c0e00b410390243c1030b9980802240001400b42c006641680d0007503007012400140c01d01d80340846e104507a0091800c22054841d5805c011100081ca0010381e1004005c1c00046009074040c00381c240908920a4010b80e5245003442011095030014000e0b4400d4000b00c021110004a5584022080c3c1c004400003848595420000703030400200c88020703420210502e002061030000294002c02e40703d1010880703111950384030240d019a07148001c010083c400a004100c0315900458004da040442c620136070307040c42c0c80699a00e0803070b6081140400000c0c5c42da0b00411240c181840b100284031160300c02488125034503210851001c10725001c000040b502e10002850b000e20510001009000700000d45649503928185150345041074014120074518100428110200010455910503005091819000d14648041e28590407a26401090060f40802c0b140142e8050095541444004203050786590a060f034040c212480114117185503c0f0400c48080b0b80740c1c1000c1581c0e4007a4078600c10300e0392520300 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 73302690 1250 73301440 73301447
    0x10f0306080a15110a0c030813060905060403120903050301150507051f0f021206040c090f0b1801030204030209040f0203100f0f0c0206010b16050c0612101a04090507 73
    0x903034010482405420495000c1141c0f0a481d140b5914204800b400b40e90007072144c041003445036010080c0401c00740301840c400a4002d0500c01d501410f608040c00c90f001ca1a1929025903540030b40072200c2d50440c030701300410150000d110900700da1942c1d40030040c0d2501d0355030241191106029107030311000e01c61040001603104a041f18607582e40002074030800030540e40b2400302f0031207104100764101d081c11340500c03030b108440c030030b031024400d4281829169844500c1448010501e6540c40d0040002c90303000400e06525000c0c1250042540318001c5075940c080d02107061072000405a00d504140c010041003026030344000086400580040501201c02e00c9031000901e02131040c00d243c0011400c08c40d014088a602c1c0d40500c6290301902c00a108455110308201c0c1c65500034003d80f48003403002d018910038645c1c1c000302100b800788540105e0b510668480d0010b00d4a41040340b8400c035940426081243d045201c01d9800010001d210380d2070010a2201c846104600071801413210300c0c0e41d10400603103240d11 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 73303940 1250 73302690 73302701
    0x904090204020a090e060f0a1401030e120705070e13080f16030e1206090709090c0506040f180e0303180a060e0303010618050d02010e0a090f020d0c0c11010f03 70
    0x24001c008540d251642040500250348030303c034201c030369161600050414185184149481c0c84010448114642010300c204900182c0380b02d024100756491400703155518040080c50b580c01c203005081500ca1100d03141941c0b910516401a101c80e086c00c03020300003408041e4000100c170903404022140c0b221040e01c10044140260285941520301c1e440c0b24200b0705400603c0c14840b883c080c0d440440c0c41c002180d050340c2e101d505860720b00c0706a01140c010018084980c1c407a1080600c18084400f00a507502c00103881604250816800200f000c84200024896014101080820b0040612403036002290480c3c49002c018020140007800682c40c0409140c14414848119440982040030b0002960078541e0303500240500804a0280b81c06164040c80c03150140027103d80c010003002500c00a0f80c01114030440c1081855001001043c010a00310664081c65215611826006841d4501c1d03400d10303001e64481256030340078090b1080c000008214006081900c041007070924901e8134180d40c0040b0003e00 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 73305190 1250 73303940 73303943
    0x30403030c15020d0606080105010804120305092a0109050102070b0313080c100b040e0726010e10090201030c030216030c0206040b0f0316020619090318080307031106010501090506090409 82
    0x144005044404104c00b07500a0054510a41c0c848015030703242c00c010360b13840c201a03602400c0c1508c00f002d09000c0c94481d8000e964008020300680741c2d00c10304820008544104040725844102030450384441c5940e20019900041c1424030040103018600404148903100103400c01c0342c10903d07e48100e0038400c20908031010740c20024111040c05014110241c0101220806e0b40c0c400e9040402081441034001408030540703034924041300213480390444005606a464010b1000d80d521603503250343ea4202805001d2030982490004258030035144001030840d2074041c4207505051044c403c1d221010300050f4042c0b08181d242c00c0422004034580006402d60185510540042c1070002d00300c1d51040c54200650b00030741c9080d80d610006248840705a0b1684801c60385401410b03044100c52050b5200354001c00b010500a0a000d1800840e00348010507841e4203401a02c83ca0340001100d20405600140304c104000300040070b007415505041c0001c200000c3d51246500c43c803800714265015560300d500c13150303159 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 73306440 1250 73305190 73305233
    0x1a070f1202211f180b030c09042105030403090b03061201060801140a020304050c090408070f080c0d020609030405010f02010b030106060c0b0702010e03030a051e01091a040905030403030c 82
    0x201d841c03801d1025510040740c480d0a00d0b044045020b500f10720700700c10441500d09150b148082c08a400241e50020000b950364241c0c18407031081c0d20f24050b1944c0030000e004a000e6002d02c03481880290748840700708544620070040080400410010a40c802a0304081d80e5002500380e581351141000109904480344913072001d9482e100c00010b10400550217500301c0301031050b054006644064480c812070108503005000c54101008582452500c4c176103041d4003034800c54545080544a4540040000b07485408848103040005c0016441c801040703d442a154075100074184c624020804580764000d40c4205418001c04071607020284d8000c1d00034050b9818040c3c000c0010680d10b400c02060340400080581e2280409070108403000c0c8180100c8129840c0c000c0110b240d601c0d0074a4420050034010a0b560900c02c02001100e21111140e00c164000c0410b000c000c0f400b03044080fa40b162181007420f41034803580c039200b844000102c020064604980e0142051003120320a0301b030901d172100d40c242440f00c89 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 73307690 1250 73306440 73306477
    0x102070527010806060f06091f050705010e0c0f03010203040c0519180b0f030601080303150d0204091119030302070306020c1f0903080604090305030a05070519030203041a070f1202 79
    0x400b80016030f262040201b100c00c00244d0000c4400d00c042407240300d815981040541c00810036110009820380528403092812510303202c0d064650508540500b10703214040e0700a814441c0940c0f0744080b1940d40031034100c008600d541080c0e610448261034500c00d540c00742008642c030001c4d2078001c1440320014465540300c6081001552000d000030680e640712240700343c048640b12403590500154180c161510103000310301d503842c4d0341881c1003095036500389180c2c00038a8881d9100140c5a81c01000701c40c92080c040740780c40180310b808026100e40c1c240014080200080d0302040801d50005100e0210703500500016034031509100c066003000c000c5030152030340c8908420741100300c524070b03030000c5100e500170f1f030310210291034000400058030a030120240000d0801e00115409448503402150030100b5420103600d0f001d6140310085580001e010134001099021081000b40046440b02c0390700b407056035a2060749450031001c040e140a8645001800300b1201e00300d04004a00b690341201c28105d100c0309002c0c0c0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 73308940 1250 73307690 73307699
    0x50c09060d060e010e010b03070e04090c06020120090307090515040e0601080d0203041401030b03010905071d0f011d1b0301180b010f09180b0d0809011d010207052701 73
    0x10b81001d100380d42001d04a4800021004400074005050b0740b010f480c02071540d25440c4c03080b207814880317212043d40305a07106201c0000078104e50046d0010070154002081c1071119a403921000407403640040000075040105107050380c2c1c0031400e10150340c00240001113946880c0c0300940604d4804a8860b0498500f0300c2c00601c210780090401c2c101c135440d004940380561100c9040340c8a0141c0c1c03041c000c8100c5840d12482d40c1e03601940044000c1000500009400070742601e8840c13901c07075564000c0180d2074071100c440381c04004028100c3d07884141c1d0a01c0002c1945003a800304840d12610042106600d03042003c40c1900745124044182c040700b076203110342c695848121440d00200c00a00c0141c01910342590780c2d0a65010780059103450040341c070368910300c5151070000e150005c095619440e80c183e8800f0700c3d60403691207c07011078144e401401c0150700c0b040060300140c052001050000c201d040d883c17502c14a5680e002404406032007080e21021500207841d44500300095810009002800e405000880c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 73310190 1250 73308940 73308967
    0x6050a0c050604050303061c0c0311030a0b070306080714030304090b0a1701020a03050a0903020c130b040204031a100e04120c0b090a021e0307090e0f0d052709060103050c0906 77
    0x180110703c219000307000583c607807081d41210781c48c50000800544d055141000841c0e20f50042c848030300006000d80e118140150785017890100202c8144c404030340d4640040c0100d0070f0401c43c010140454841c4280010b070b164000954074080c038030038282042c1d229280d904841d15036040d20402011710001e8064061003008810b4080e401c000b60a0703000034980000038040310740b10f02038052200d030190042c02100710540b080c0010005610100c0c46815129440d0250b60384480c0300a10045018104c0b50301c8900c2e000e04651913580001d4500500402790b4003040c010b0200c245019500305601a108000c50700030f2800554000044610182c241981740c0d08000b8115004101f60b40858802c5403429000c5014100041281c541b855030345c3e030181d21804041c8031440680d0320440c0c83c1c07440001107500f01c0421080b1a807a040d141c802100c0007074004140f00035465040d5050441d6030301d00d4004501001d00c0000442c00d658002842d8074105034641000c80c400e001c05e0821584211405444a55111106034045 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 73311440 1250 73310190 73310197
    0x30603020a090209091005130e0708070b090307080d080c0702030a0606060e030f07180b04061a0a020607140708031509010b040302011419080408090402040e0916030201050406050a0c0506040503 85
    0xd40211740010024007012410320441094031001403640540f00400d200f5607004003018150381d0390611515002103a032903801c2000a00810a03038600310358400c04a0141402c01c0206e5209002c950b0191050203e80e80e040000d603503005824246140c1c4800382c5000003071412020042c041d011600d071140100d80e43d42d0010600319000320950845c0c050300b0101d220244d03641080d105480030561072000382c00d00040c254104443c581401400443d8064654001000031400c1000c000010400003800204054052080c59400650740c00c0c000c429102c40c42401c6114401d42100500010b0300100040e0805502540031001d410003404c2c4c07000541e1030b00c11100c400e83c80380c017050340480c2100f011440600d101a00325405801240d0002510034484003043d0340c2548050300803240708605004000c0303691030b18070140c40209005480d040306400c0003940d150800c1c00c01d60100c038200e41d41550910150341c00034111343c2251400c0c40c005588040070f60044402a00708180206a40103030f90600051000c0003016 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 73312690 1250 73311440 73311457
    0x150a1401120203160b0a050912060a050712060b0d0905030c0d050a090806011202040b03070815040309140a14030127031808060a0203040f140d0206060102031c0b01030603020a0902 79
    0x1300ca22801c0c41000d03084070109544220101c000342000308011461281000d01918440a4807010420445944450500e6821207501080740c0c2c0d60700c00c012580380d00103000000e80200f80000c2041130f0400301c483e0900e100c0c1c4c05041070340701e0700c0e03010100401000700104c444c01c000b400c05440170740c0c1030000011f100c0d07070210450300b0025150311400714120101083c842e040307a264407039802206809500380000307440d00c40403155160080c8040065619001d10215480b56562288070b001c81c41c044c0f030040c00050040d0810307104075100c1b0029142d0b6844440861066a20f01540480080035407000240905503410700c00380b0703511201c502c5960220300352100d0300040344251924820300040c00301e241030401003403140104582c800e2000c5920303450f4503030086401038010705100c9821b03245602c1d05d440340010480100321607449002071140c1d099044c02107035004082440a1454808822600c41d9604c000248410303032a03903601d40c0c001890707020fa07128000035603000c2d0202811655400e80350000b074000088 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 73313940 1250 73312690 73312693
    0x10602060901020a08180f030703031413120c02030c06220e160302030406200d060806091e150108030a020106060c03080c0711120307150c02150a1401120203 69
    0x41981e614040c025280f80c400c8540c2c60782003030340d02c840401c24100c2c000030380e0344441c1c002d20700c8214584109200418040d402501d02042d4083c50042c070001003540104071001c0311304d0b80c2d864040095802030a041311080c107490035811007512400080e08194040140943c00500021230300716070307552198000c4444900b402000345143c0c0d55401305a01400c115643c00030741d45c07030b030350719900c1d040c005d41c0556000340c058400001c047c895800d84191440825900705d04c1040301290015030f51003a80541009080c0c0c4502900d00340c10210781c0c07150340d41c0c0c022074100740103080340c0001020510100600d61201d80c145503180d002d035079101038860b00ca501032160000194241540403039041e019214505001d68140c7c2c410742159078130b07160514140c008030021900100c0c061204c0a190ba00c0800c00d1000c1c2480801440da20790b450b18041c00d20200200c180e0700d110b801c00000c421025000724503a190344058501c902d034581d542c82c0c050300c000c044c40070300c00590700003400021405004010502c0c424503c01d40 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 73315190 1250 73313940 73313953
    0x30405070b1b0705030a03051e040504061214070b09040e0c130902030607020604030207091d0a060b0315040c1502030d06030606150215060f01090504060810051e040303090804031208010602 83
    0x80c1411b4a801c0241c3c005004030713004200c151041c51403101d40316965920710205034200f43d2107000080c10307155580c1c0555604010045c0c548140089034041c40403005415008104c02407810381419210300036621494400c0b0340e075015040409d882171200ea01d5030398004000020306c03504c14138040018415403800342d00030710504000402007400040d5035809070703406070028403420f4580710407800039050604500d800d0620340710840909030802c203c2680c1003403145d8000b06201c0500018149465a0191100401880641408003040c403c02c40942a540c51511441030b00441c2d0b030059185200d0b800904852900d4040000b042c042c03d903100005a4216009206011540800c00c80e070b9034800c111800300ba0b43c000030203d40c030781c070b1f000070806024981814910416951540080c0c00c0712010f03405070b02c444d04210054550114203208003580700e540d60308000240c503c2465004140c0030028401400d15a4614403d42400710b50000e40c0d000f1030380080b4401300c001092000a0010780d0030b2240700c01511410 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 73316440 1250 73315190 73315199
    0x603060c020a030512040c0506070b070f05070807020f031203040609020a06080606090d0c1707091b020a030c230f010b04181506090c0203040f050406150302030405070b1b07 76
    0x803074190030b1540c060740e525051000143c2c1e040a64132000e40101c2d00722000810001d010389560b4041e00189010b103030b21010601c0c254034060118480300ea145401c0000801100001807017043c1528409a0103842500d03640b808080828075201441d828081180320100030441000001d800c0711024603c00d0316030807103440e983c520644005a043e1021540518140050005410142445034400d130244c1c080b2102c107940c41e0750b014500900c8001a14158006a5003400507001a025a601c41890007401045100d084d103002515821121350050400c241c071704044017032040c920000380c0c100e6209402460355020703806013560345003600c0184884550030722060b19081c2c80c1c40c0c071500700346002a020b0b0f026114080d80d100500c803510380d402e4451903955242c0108905009220360949129503800850386d840c00c2629600050310350394040c61181e420300c1c0092101000c0700003116007100c0141405612912149000c40c03d100058000101b4828081030031400030941d200b191011224680030754482d103854 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 73317690 1250 73316440 73316443
    0x120215060618040f0f0902040b06040308070305030702030c1002090f01030605060316050d020d0603020310090809060a020a0f0501021b031e1b0d020c0907020607020a02060a050405040f0603060c02 86
    0xc9900315407051091115425188800c80c005403001c900034000660b81800c6008401198842000c0103140c036036803504070045041074492030b030700700b18111844c1c1e003840e1540e030311203426200c1c101e0018100003020004c10300d06d0740200103884c443c0c0a0f0700b041c0c9800d0500116004029040401e03014490043e0b0315200300c1d55402481110182e94015110529603070300c03800740000603819494100c0400608028030420342a040c80038001644c40c0042c08601d607859801010703c0d00c1e0b16452115122880c4c04040400074145800701e5085075021b560f455164500d55078180d0800c5401d203406080c0c0e00c0c00d10035010410506500610784100c054404850081c410301a15542e030003950555400800f2140050800e0503000d00a000f606c0d642880a8210010400c54a42000004d103104c20169021003402c14043c940141096800941c0d88010715040c40c0c040e80003543c61030000c0c0040d000320000142191041c3c8a80100e40c0a0003001c0d00512a045245036071034010402403209440c030500c1c3c049a514034510 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 73318940 1250 73317690 73317733
    0x90a060b04051b090a050916110f0304060309030504030506100807060e030a0602030c0f0705060601030b0f011e260a0e01060302010f0e0a03021201090b0703200c15041202 75
    0x3c02110805800d01d0f02140c1c03056000314086070703210411030b01c0050181c0d00d482405200380210300444030014658040a40010305041c81400c064006850004c0900c2c0000103407011902c180c6400308803180113050903600ea2040c3e4201074401c0c05510200180168000c61400440e03040c6412540ca0950b078200c121581c41035188a158150415803e0101007021500a15003205c42c0801441c0340400680170005c903075004041c03c903103940002c820050690b81501c02c140c1d1030130081c0c0e1036582c112a00c03070000300340012003011040440d814610007030142e84030b0442102136401c0d80281c0520a48102d000108106003152107d140600308103035186100010b01032031007280d034181c43d030710103540d00c00038140c98018422812a41280c114440000540d840d900030f010003d503444c2c00003c41e040c6905041d0403040004065105060903d04840400c0215403020b007005201500f078640c0320010480b2480c10643d03110010044a400c58080c0000c0c00380800d40850568029021602012403401400d1f885a0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 73320190 1250 73318940 73318951
    0x15030609150606040906030b150108010f0603050406331d0601080c0c03130509060a0f0504022a0f060108010e06070f050904050406020405120606030303071b0b090a060b0405 76
    0x801120300c01c00780c28103000c4099001000140100d0405803500354803002c481e09684180e4209a9032010f109841c21078002c4114000402c0c1ba1101c85581070115480c000102b078400d640c101681e94000401740140d9074003a04d60501e0105040345040e01580c21211418a050080780c40ba101c110302c005003214001c51001400c2c16000e02d1864141c1c2d800006580c8110014400c1c1100d4100f00320b4016842c0051009000391003021041d14046230400082c405200e0000300000e0054000082c14080000ca40c8181000c580c01150003581c2c9204059450352000300c0846454540c088611400032440c40203d02030000740142c004448460380d891045500342c0d903500c042e0780c8089d044031022540c440e01c0381e010036022044500303041d80b0703042841010904850003110140c038890b41c00b103002e10642c50706003100903800d4200401000d050801c02d00107604ca100c060310950a00c800c041c001d80201c1c4a075125040b013240c016a036900c4525100130700c1511414a50011a609450314081d00c0c2c0781c2c6410301c6080c0c0240d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 73321440 1250 73320190 73320193
    0x5160c0906091509090305130602030d29090c09060c0604020418121412070801060f020d081801090b0c030402090a110d0c020115090b09070201063f030201020315030609 74
    0x7549410380984c01003c110303100303404000c0208419121200005029402071081e5401555590488024202126076242c407650321120f03408102c1c21841c0018004210b0040219046030542d02d591906140300e00c01d00441d150083c1e4046041c02d0194004a41d66100f0b600070b640030b04c032a00c4401e000700c81e8a00d044000420300100c41038034400d40c0e07215011201103007003900c08030782c038151070040d58000d0303030008450714400642071900501101e980050080d043c0307222400107060101c0344030070192040e10300a15510b40c610752a8034151100ca0300350002d048980d00025510028186205140e04560044806034081d0080d000401e0039440c4a2042c2440000ba96441c242049000c510900c041c0030f503100c00c0c104640d2240420300c2c1c0c00b021400401d0060016060028282000400344450040c000740b03154156407400c0f2041100d0428412069800408086c503021542d0b14a82007400c1408040b400019184c50711100c10105034055004502405191610b460410108001c0554402c011244200035 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 73322690 1250 73321440 73321481
    0x20f04060e04090804081f051b0c1501030c030b060f090c090409060617060108010b0105090111030c01020409090b13030f030b03190305070c080102070309050d0305160c090609 77
    0x99072040d007410816641c0140089241c4440da215a551600950400c4846400000301e91920f1030104400a02070208036405104526000f0015542508507600c4940c0c65500010301210701d10040c89442e148007007401407041d080d6124100072200c030105000c2199145882c00100b850351a01d0950780004441c01015403045c0c1d51544800310480d00100c80b02d541054031031250390001a003e000f12009400081c0840700d0b0511542c100d10b2420006034072002041c3d14000200380706076441011030300d20800a0030b1420306291400003151079482150400000c5500c04140895910420f41001030240d0103611400c0103501c649086886503000e913140140803074480c465419681d800307030704001c03007440c80241a1868418088103806844800070350880c0015400141c1c2c00400483d52002c40180000d40001c40c140061603030040c1401e03000780540d0b8487c070502e0a0704010144a10304954a42041005683ca07901c041d103002e000140040c01404901404c06030003007003084503403140001100351081a61813 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 73323940 1250 73322690 73322699
    0x408070f150c0f0213020306010e0111070b030c0d02040e04110423090106120803060108010e19380109050105070309120201020a17030906010e010509071805030d080a050604020f04 79
    0x7400700c010032044451a07503c198420150ba24400b41c2c1c89100900c00c009070f82c0e89000c4000410031034628a00314180003505d55110000f02000070807000361501841075540d81d84520100303c40c1070180007041410140002004240303c000342079000e020b544074010312070b00305800c1d404000644400702d0703004020b1058181e10741001a072651b2041d0300001c8013800016541d0b101c019044c00b04020030b0058400500020600c159941d10040003401484e810351894145d0814840b202c0090390400d400d039801c640c9503580310a0042c854001d101c1041c2802d00341d01c200d01c501c1100440403e40312900320f03010540c52013001625500807000c480740141c6c951f4580c003066007800c00b1011174001d6084103a046100d030f54000c900240c1c90740c44201354051302a0841e42c4074945482068602201600030035140d00c141c4004108940350040902d030091240d050544441d010605d00c1c50140d4825400660b240c42600d003800c200ea40c219230000c4c000c4916190a119a988002c1071005902c00d00c01c2c20544024201700401 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 73325190 1250 73323940 73323947
    0xb0f0a03090602040812090f0409030f0302030c0412030e03011b02190c0e10090513201f030e0c0306070c02060c0a02090a0501080c1801060c030c060c03020408070f15 73
    0x71003503100d04001400c240d140c9511a03e0250031001c8005c0c950000036118082d417034403500080f0112000c40301484000499540100140c104040b420b003459004400700d140080e035802074402034400641c00a12041050a000b0400000d1442c124004c4d40780c840d115129009a50741d03003c481e841d940050040f403016460b180810345a6000030380b00101078079400708029020013005401000049800c040301230a104191044840c040c02045c5800980c0d011880003c5003026001070001410710048541c0400b03602127500189100e8036008d04e00211100c3c01009505940511106004103089a10130400d4809240e6030f10b100740c440c04041102c03441d0140040c50b040d80101041d101da882641c440b0300d81036010405842099402e0a12940c440f8014400710104024100710900220380107043c0302e5114280d01030015041c043c0d0000c20480c5034801c1b0500d40540d07101034040d6070217802081150814000140203400a0041013005d0040710400515030408801100c01e480c844489070844022001c03040c2c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 73326440 1250 73325190 73325201
    0x90a030207060f11031603020d02010209030705060f1306030e0f070f09020a021c02011d0c010806090a0b091f0506040f06120b0301231806010306021b0d0f090b0f0a03 73
    0x4204201350312410403d818820b0000c0c20408401507207603110b1046510700642805500c0000c001160320601071451190360024001007114420344442e5601d130014000220280300d0840507010100e501c1c0da001807030a501d5448034002d40c61240a07914161107000106450b05214440c4c440c00c5142105c3c14869100390354010034422003140100c034100300c00c503440c020201c8234803104e03840035035912148002c0c041011601e600302d6146a0010b080d0521801c6e00103804260b001c0c10007070056140c10001400c0c0c101c0c507031104070700f600000c02e050303140d1400d071000f00b0802c1804c1803001d07001d040ea03000010380c07030a2003c250350035100b5208174012405e082010445400880e400141e640b1074907007840c600c8a071028401c031483c0000790315010380c0c240040c800a42100401410044003803609140703030380d2038560100755981500d902000241e03403503a17800703d0321912402c0c1c02410005402a000c98440841d0010b60b825001041a00c0d0046800c7e030741c185820303140c003950b603584000c1001046404205440b0350b020 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 73327690 1250 73326440 73326467
    0x20102070302090a02120106050c010507030501080618010b151b030406021203070309080703030c0e0307061b0f08040f0e060f011b05071802091203192102030a02030a05090a03020706 80
    0x6040c0031b0f00c1c002626001d0020ba01c244c0c003040d400079030090030803028020203a101106040034481c5515084c0e410b40e4031100140005040000840000a048c50030740241c208071a004100b84201e4101c0b09403d495507205245034940c40611080083c5050307004030540c3c0c11104540c02030020410320300d0141c1a180d00c0146400b0405a0f14050040040c60243c061b01c2482e0299800103105c1400e004060000995020070070b1107644940010052181e01c181d00c03000d407007021400381f80c5401d020b24200818004502009140348004078012852000e0351640904481c000841291103860380010300c0f8030710840c0c00c00580090000106200340c04012040514614403803002c59509981c1c40c11400700d094107034801c2c6d00031a40c00051001070740c03614080c0000911083c030050340c80c006c80c44242d040150701281d500d00500050500c01890a40404419645034040080540d642d1502240040c0250700031210b9040181c5413a012515038100003491043da42d0b4990000e200041c00c00c0e4084e00c2c600150003d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 73328940 1250 73327690 73327711
    0x5090615070614040510050411120f190c1e1401020c030f010c030b010806090f0606130e040b01140a090b210a0309050108090303150a0b070f0b01050402040302010207030209 76
    0x41c0c000201e20b482021500910012501c28034105454006e0624660007880324000d4285802d20001c110300c6048040c00c01021102400300741c408011107820310100c10074100711070094018910b0f11445c100e5504040a1146070a4104551a94030311402d4171050325800301000c8000e0f600703200c903001c803405250140788140110f0386210381c0100000d04c0c04e0f001c22903c00440e5107031140b881c4815011301548040e10824244140d02d484c019012410360079004140302c40b400761500104405446410407500c4c1302100c41031010180c0c0d191074501400079001c0e01c0481d900c00c0e14000000d07800e081e8182410704c071b138402044020250300d02038004014058175102540e000304801103061004540001001c240407200002c0d24600115090252014940b81e211034140103201080200170f50000c030491350f10462295065020800c0200030518040554002002c158400580202846204100081018801c50016030107a807518240816030040b844028090780c48410207100529002054560004201c130 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 73330190 1250 73328940 73328947
    0xe010605070614130c0b04030b0f040f0b0c03090c06070809040504020406090e101d07030f11270711030d1a03060103150f02040f120501060b0301061d090105090615 72
    0x11040380783c101c02d0710020307a541010442e0804001480c03442e10024000580c0f164105465a00c0e080301c2013800515015100c80b0b03130030009003040725a070a0842102e40000c1700005624040006000340d50050303414986610030007800020515000381168001988441450f042a40322810721003e018083d200f01da006803134190102d4414001d201d04a0401541c100400030019610401401c4070401299411804011001e041c903d59000134503000320707075003c5040340c00c0041c01c1c11b040c082000310310032495000700728101c00a45c0200142c0c43d031002e20700380300101e6100d0b2180481034419500710041c0010340c1e0010b00151190342d00552120700380380340141140070049a2540080e00700002600700722003900e5015074901e80c0e40114410303c90745e4403840c00110f2805007003c40700c902043d5640b007903150055541d000e041c00c000d4290003074001810101d98041c1c403541c540c6d03070281c00c400c52101c60400c600f00c901400c1d0300740d1810103000c6048480c01307008000d10741c41c0d0a081c881090700e030320308015880b6401c2 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 73331440 1250 73330190 73330211
    0x405010b03030a0e0406050a0f030b09070905070e1c050601060f0c05030d051905040c090b010e0301050405071d1603020f071202030304020109141012060e0405070e0108070e0106050706 81
    0x740700400f040409039aa6089000c0240100422160319801590052007407820501240460f81d05100550341c02200000090391442107151605070a600850300e014103050520800c41e801ca00d1050300c1210031903010403042d0304014210600380c10000090010392103840100115400b66420003075000d51854034600071945a1a0b107480c56100d88000c0250030703a00c0080003143d0a21940400984003113080078001c90038161240c1c6031030300f4a4000ea10b410340e03450000c01050b03800b0355149e09000380e028000f404180b8090070400e803144418482c0f00d43c1c3c5003410314815a06110106060705c1100c0e2013480081c0c081c13415404034002d402064208404250401800c00401e0004600d02d2034080541d004550b246060720004001c2c4006500950000d4041d04200040c1c0e0b440c0e801000407040d507450011050400d90101c0400b40003180c1c015220b1100100c140700a2220108000080e20500003242070310f070341d03507800860381c0f0001351044070f80948035400140821803180b8014110030740244400308050f041d4 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 73332690 1250 73331440 73331443
    0x17030603151f0803040f0b2a0706110a0f170403050703050102030709050109081525050403050111120103080c150c0c0106051903080f0d110a11010605060906030405010b03 75
    0x2602e800b903140c1c6880300480d80e0201254410b9014100180203942002d00c2c268000001d11890701404410aa0100b81981a031401c2480040e44588000c3d801580c0d5201480e1252229030340d0041d2800101e0b540705800c0c02280020b0300d42c40483c0d210000c9802c07081d10743c88100b070445c01c0a10300c4220180030440040030442c104000340107540030300d00059483c01c004c007024101e040160f01030b90600202e04020000b002021a042400392115410700b00c0f16656020b0f5500300422094848081c10078024000c00c0d00c0384d1000107401036a108800800010190442c03841c40d600800c802c81003007542c400c006100240001d0301500d02124800101c60321f0f20325162014603044022038084c14810f802140c960b1000000340200c0d0024030301038038a6049200032a014824075107050101400c60000001e88c281d1031005001116910820102c00300844c4240d6258142290300c14907465002034035080000e031120f00184902021a0700c0205a140340101d400140500ca410081041e901c0e5581c0d5034080d01c203900c0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 73333940 1250 73332690 73332733
    0x6012003090405040507061704170d06080106060f0305010902070209071b0f03030504030e0103050f06060a0903020a0620030c1b03030c070608060a0602060906040201030e030717070b0604020717030603 88
    0x100c0c0000d8004a410310100401003503c82481100208c0343c0401c0c4004103007600b20400615007a01d13103041c1d0740d420116003c1e018014940c072818040d803800c00005a06a8012540701000301c503940c4c02c0c0900e9990b45003403001c0e4049c0001c041e6018001c080800c48250141a202c0b1030800e01d80d45d010154103040e21030702100b025000301500480e0b1940100010140c3c8440d81d40b00448003420200624200701d03100c0c0d0318078070004000301d00030321002130042c2e00d0740e002ea44448000d50b401050301030b49030b0320b885000b0842482c0c07405000b090504030000d00340b10507020041d28400741e031100c0145086558512040c1e00c500740041866010300081000d5043ca0b0b4091016501826072511554003a040080501074503801c6c90b0f0142045411500610501c01404030b00d0580250302460041045504445030354114481c008009085600380704149900c032003c60041c2c4103840c012500d040440e82c91800748000e071712560a00a0081d420703020000b14881c030390406075400c02405021a41850054041ca23518580d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 73335190 1250 73333940 73333943
    0x70c0813031a190e100e0c0f120c040b0105040801021201170f0c061e04140a06030501060503040204050411060408100b0102010e1e0118110a050402030601200309040504 74
    0x100c488000e206000ea0100c21a550850b4003250b001586080c3c2503031070040b6810803080724120744507030901c00340032020019084124154001080741d2104504095560102e013041103000300003041440d0300a00c2c01842c510300c0c642010f00600044141081040001c041250850f07050003400c0c400403512250910203040783c50301d5555a50207135410409000c1d603283e01101e82000540c418900106081404208529a410140c0e0301e5520340301031000d0031401541c544d040d150700c00000700d40000c81d2401070031501c01c00700c02036821000c1d441e281c20044060354000d0180c0d4000c01d4007040440d0050800d94859a4001e014954421064a80c0400199258030690100c54960300c40151031f0b58030f807064802c1c064a1807007400200044010b614800391503000200002d20231301100041c5c4807105200790854039511a40007829181d80c005403506030200c0e07401c1010300780115086800170907242031600c00c482c00f919050310b6803540342082401800d0500268180b00181b808203004c0700302d0b03649503401124081c6 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 73336440 1250 73335190 73335217
    0x17090307030f060506031204080a02060c0123011505070b070f020a050d02010c030b03150c07060b220510300b010b03011e03110625060e0c0301090515070c08 69
    0x41c20080d081521f8a0030844298800c1c034001c020405c44500c0004e40e5000a940c15181c40c1d4503403450f200d46034010030220a941c1c148204c00800c0a03104201c80744a80c0c103840c951040351210707148238003080303c2500411600070b04040c420000314810f580184846c03401d10781688111880c100036980d515040105a544c0800076079160341320b4800e41901802210340c1444294010142c01d0000f540903005041c0c06441c550340d002c00080d41505004c0c003034000d040b8898014001d00b88a0342c0710145014100384080da0358100070f2074a0042542000080c0c5503504562081191910f00f1014020032192004c2c0ca0800c4500000c020309144001403441e01014000c01442580c26100d61500b5050245145c1e07050041c1d00d5030200070f40900028410280c2d0501c41c94003074038216143d03e1460222040b401c200344042d202e140d5050000300400001c3d411800c4880710712000d03101e06060741400c3c5800d030355481500401c90380003968000302c01701c0a054515401002403030f042e02115140d07184c0b0b050b598000c0a10301000c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 73337690 1250 73336440 73336451
    0xa1407090b010e031009020105070b0108030a0807020a030c080a1107090903030b1203030a0504020604090513290f0a0b0a090606030b0a0608040f020f060a0c05120717090307030f06 79
    0x42080788500103441c0c0c82030a0070340c0000c030782c8000a80c403480407004c603196043d07842d050030066900c22402d0340d5040368054803188140d40c540021555036000001c14400055250300042e4079244007243d40c141c01f07a8103494103451070a1a548519454004028074020400456005201c0850420410300180400007000940d5515400d004040d2a4100041c5010381d5884480c18040f06000045030761240341a84001aa40c4540c8000342c040d1150750b1110948904000c103000350130003213942400c905d80c85080040ea011407524440c101d003819801c4007c109655031000250204081c1400316400b103800c210014002006200090411030300ea0040c00300a81d45a8041c8071150701489559070782c11342124000021443d00400030300d200c0c40100010074181d10985030381c0440d143c0d0721640302440d6000300b580e40c0f0f40c040c100e07005150704841d050954451255a408441052218040b182441d030806400e400d4007544071100d2250f0342c800800340b40c040c4691100080401d8181150184086c480d440100c1d1 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 73338940 1250 73337690 73337699
    0x5010807080304031212060b0f03061809030f03060a0e070203030103170f030402010f1202040902091e01080609040309030b0a091202070506040909060603080301080c1206270a1407 79
    0x5400a41d8119074801ea108010900104200301c000d1000b02640b85402003940d000354128002800455116560305c3c50007050b2403211801c0403001e54400c15058590705503204c40c0d01003102481100707940303d14654001b0000102000640c0b00116809071010b1b0082000310340d59085c1c00d0301da1008a07004401a00b001c401031007040029001c0c040180040d00f545800c00c6081c0c102e200f428400a00300a0602000590451205d4020586001c048030344500c110745030380c0e5a41c1290301952010310040e200c0d40c02903c4c802c00903400c10015814502069451240c240e9450040c040c11480181056081c03010000001002031b495189080c42400c48942c08a01a525803405d000c40d51203c01c0003a0075074101140502580c0c0341c03441610119251402c1c0460080483e007440f4001348a07640010304407240010011803040c2d000070342c15110b81405e80f0342011030700504164940314601681c00a403d050460b8054201407149013140d44d600c40a034043e03407451006980c4a075004400c109080199400040c000c00 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 73340190 1250 73338940 73338943
    0x30c0b0702060720010e0d080a0c090f052b0f0204050610080601050307050d020310060e030607080109020a110307050d03060b0a02100c0207080709020d11070f0b04080906040306050108 81
    0x203800c0811800109558107201401070004100c0301c40310910649558a0741d8070711007003508685158000403042c0d454440c00c10700010050340080b10051242750501240c0c02d0502d126040902c1101c00c0354520740440c81c02c00c400c0166451841c815100003414509902407040e5500b00c18151403841500300c41f4103d00c1d00e105110640c0c1c00208068414050031480140c082d800c00c4005030f002d1402d18106642c0c0d42d8043c03007514180907126881160030710100c00c20910100407058030b8182d80c4161a074299914400c000c25582d2881111088000b85903680100203025484c0c0103000301030399034140340d071030891980d061070310b1504850b0007621954800003800c18030315058880c480280c600003014130700d0a08013401c003a549407200c100441032940e6424006140d18803e0066101030080c45085da05001c0e910028000650804800c0c0c4211914044032010301601500071a44c403103a2000c4642005251a00c80d0400f0501c001c105980b040010000760915030390b00c070000d0010f50301c1800c00048a50400c036505 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 73341440 1250 73340190 73340213
    0x1a0604061a030a0905160303020604020a0b03090a0305090a05092503061202011d09090f0106050d03200a151508010203040503120c040801020703031b2a03030902090103030c 76
    0x440300100c4400301c44003401008012250302a03d4040d004c58503071060301d031013450540d5041d020310004010107804401c142d4041070300c0340602e0013181e81d66001c1d5215040c81040340310039a28001c240e804101d49000180c02440a080c00c0e1000400324107502d90744801041c3c403500115000c90000741380162500c1d95100d881401208407820f4941000141c0c1451250240519040d03406814041000440445071104c8180c010b08008c02034030143d06411f00c0a1800d90300c8043c4603210000394281031003c1210f0a1608101440f01d4042d516610841314588004016004042011080c1e000d400b99040218002080031040040828130010720414584204030781410150820549640100180030100b40c0010607200040c204400d00c40383e0303451b080d41d102c05500c5141d00c46511540081340b580181a055400003400b03082409040c00c40544541c1c04440c6490740c6042007501c1d0401d8460054480d80c800031840d0711602c24100007038030b560550000f40821400740e008800060b04422400c04001406414 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 73342690 1250 73341440 73341449
    0x3060510030506010509040b0402070609060506090912040303050a05120103080c0d03060308040905090a24050c3103080408010507091a03060d11100e01021207050c09040f1a060406 79
    0x2c0005080c03e10000b0900d00c14403c4a40c411031f110001f00415941d40d5044030000b65010004010303681e003510b0b15101504048034200d1240e11400f0014101000118404500c0302c06a15424a010b00b180e50035075154010b03ca840040250502041640c03010088005010f50302035035180d81c507080c2c0c00300010700d4030310441c198400700343c200716040002602040644040e600c0084002c901942c40c1c4a101c0d02d4405412000340412039016007002000600d0503540d00701c0c0d03040c682c042c00303a03564101c000411840380074004007000a0110071412900e01d09038112000c8400003412104050703807519a40400d41064200d040248d40d9030781409103880d00040e000000b80700c46040c031500b50206a58201c0140001080c0601a00c01d10b04000208400d00c11400c006080040181d25000480702c0020300071200550164050301c1103034100640028203900303442205600c540205034a8010030203001000c000a441100c0641d03000c400b03c8000f034a1003c003801d2a009104640d01c140ca8034000f00000d43c0c82e60380c0b1 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 73343940 1250 73342690 73342697
    0x30203120f16030c020603070905030c040905030703080402030f03040605181215060118090203090c01020c03071419030b07031a0d060b0a030c0f0e1e0105190801050703060510 77
    0xc07801c0044010025079240c0192040300c015840c2443c1001c0e2400d49003003500a6005c44004100800f00e42c0061040003030740c005030111084c420500003400115106544c0c050101d83c402d000180019100f18a03480e072162015054580d0122002c00603132643d0881d411460110740c011540c14518168811403540708802101d4508146008040c0039071107a0300d283c04411401020000600603074001d18028011188020040307407481d6442130054000e4106840200690048c1e0b0b080043e00c5d88000744491900354002d000c0c2010926001085900303001400543d03400610000002000d80609402c0b500254007449121907986801c013402000c54241360881c3d880c0541e40903920207a504c2d0350740d400d4941c40c0e10480004050880c01c0004104100c0e0381e0000300708000928001c80c03e40c079140a02e42c122000c0c5140d000840d101c1000380985e990803001c50701c0341d01c240ca00042083d850300166030750017200065040e100007501d8520071070948104407500d0700800c2d1150004c100c942440682c89130860740515 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 73345190 1250 73343940 73343947
    0x20f0703020a0e0406020405031006080c01080622060509100503070b030405030307080603010209040e031801050414040c0c05010c020a12020a0b150a05090901150b0c030f0a03020c0f0703020312 85
    0x20700040e107103907090088250341a43e0360001400c020207070303044030080c200040c21186103106480700000940300e10b010701e4000b801000d9002140394000c04404d401481d0007400794020b4080821404001040c80b50000b442c5074560300700042d991504010117004818540c5810b40003407d01003410300e0039105510a0080b00030400421010030008015a41c001140346484c01e050380b81c6900080c0a40210020298064900b001c3c40403502c0000001b000d01c10440c079803100444100c3c42c010740d014081c6d88500040e0f40d0b282c03441c0042910740b5a00c100840551400c12140707602a5880320360844600d80a11400350340804c04000900c40c0200e241100556035100a240c403050941e40e4011205001e4a10040c401c1c496260303258564070b00129030094040a050403046252011318179010f0080100e5074022042440d00c0402e52045510807101082c2c0004000c0d8503002c0e00700340005099112144000805a00388031200388464180041c02c2030681d02c4004190743d50035030040504080300b20070094580030041 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 73346440 1250 73345190 73345193
    0x60e0f10180203151206070f0507080d11041205030c010b06071208070203040909050718060302031906020f030c0c152701020c010510061b2d051c020f0703 68
    0x110110094014050050f0301e0b62220300d0b8141041c0c0303503414810b03405202002030041640d000281c207445040701d90780c1c004007002e110071305841c00e100b01e0602501c00b0b102004205015126900540c0001141e41500d0303242540d20380f020380003c13109443c110360b82d8100052160515500340103944d90352000b129094034000f003a039100c500c204400c05480b8207101c803501c0060440390092040c0c070014560340c43c0620500c1d00620b011500c0708050300030700e0100100c0ea0001d045c44070a40c841c03001500d078050b0083c01c00b14800350003140381c1c03040c0b500220b40041d02005107001455a1001a40c01034040000d495101c181421080b401e144580e8032034451503286004010005000220f40414846020014030740f0074081101c0c00e0181c4586100c806c059800c101c02d10a004804101e05000ca0303009942e42a500c0400d1400c82c5511440d441c0e003d040441c2d0050301d05000102560324400b020701040d20003000780c4007030342d40c1410300b80c181130310000050410300c5607035650342c06001c80f448442c0c840c406850b0080c211b = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 73347690 1250 73346440 73346459
    0x10806090a1e020a0c0b090d02070e130503070303050a0c1d040e030d14060102250b0c0309040e070501110604020a1a0c061003020414070e01180306060e0f10 69
    0x240584070301c03a200c90b18490340c400d542c08212481545900150b5555032200300291902012040c1190b40e150030100091341003001090300400c8207101e0340036150041c0390684004a02d01c5c047c040810030250a104030002680c00c10040803d14480d84020a40b45401c3d02c820040326a610b55000500c0340442c10b95015074440301d40710351040000c44001030200405140e0301d10b180543c0700c9070381d5803515000103100b0188844009511881c400d03800c235140b1041003144104003070444080600401b00a820510880a214010348a02d181c4902181d0a15454000180584a100c01000610b40001109020550340040c68290480c5c03224024005400c3c9940454400890740c403c51070701603821039600d2000e6081108859265020400b01c540ca8104401d440388401210702c001c0f441186040e02d400002116950b50303a11800c151b0300c881010903d840010340350011090041c06a800307824402100080062107801e0190032092a01003191400040900318000c0282c002d04a0350940d1070104040c604 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 73348940 1250 73347690 73347709
    0x120a0f080a181209051804020a060f02071a0c0a03121b02030f030703020f0301080c04050a06050f12030c010e100b0108060303030a020702040b060a020a03030609110a0c14010e07080c010806 83
    0x3d002502071448607240d00103d9a0f4800b0790030965101c0d00405018010340070341010180540e00881e0101c10b056911001030383e80604000c0044d01681228508000110720390b0356011406100c44000741c6010111040750741002c848500840c0460740f01040125001c40c50b218001004210b07500540814104240103036490181c2200000d0070180080055a2641f00f81c044d2450340540c802c00725101e58444520340c0d11020741d10b42d240e00a81c50140043c12f2a00c2501641c401c0703071000740a031711403001e80900307101030704075004d80003a06444100a132a001c90804d00c40c0030b6004500102030480d00720326144d008280c9800c03648603410003a0b03c105205055a0100031640c01801e80c00c00140e80e80c1040c8080b81c0074023100c213031a41e48000c02090000d8408d801040c00802d5510941d010018a40c40d401c000044800b404065040c1c500c0c284030640c07100e406801880c000034000c4100c9029000440c400e1800d4403c400d03142003d0350445003080040b25410440030400103c01d08040b55245031000120380d903501c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 73350190 1250 73348940 73348943
    0x71103070f090213031406090c011d060a02160807060215011d040f0f0303060e18030301051c1407061101060b0d240b03091603020303030403050a02120a0f080a18 71
    0x3c0c1e000400784084000343d000a001154002420188400030300d110b40c6d00c0352411126031580740581007040b000c56101d8080040c07808602c0b0280e02c900389401d400d00080740c000d00300340b00c2548076a000e1500941034411100e001407a5040c0104201070030500d001b810541d140b0f502001686140380180414414451854400180d1a0030202691b42c1c0f410102072401c10154090002104001101e00781545500f00b841510001540e025468540c00e08110b03011004030300002c0d2641051005004a16145111100401044066442c0440151207a16036014800e0381d02580750320130070b401c1042c00d0304101300190302c0702c540000700300c40c0d442d0070039070700d041e20880d80c00088040e40c415008442d80c40402100708106501c4045181c200d895907010340151740142d07000032075803048041d407a500005040000c0c042d280d02034003550135500ca5650569641d08104d0311003041d4060000784c140c040f01090090300110203550b95989446014080213030140d1303005002c2420f03c40c1080c010780710950300c00e1207144c20385 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 73351440 1250 73350190 73350209
    0x6080a150905100903030209040b06120106030c0302040801060b040501080f010e0408032805090f03090109030204230c0702040f0506030a03080a0f021b120301120807050c090c071103070f 82
    0x11040e0b4a041800c1c1805800101e4065180c040b0f403600f0703da4140c0c040c086280060f00c040003141483c0d420801e0ba4003484038031500c074000b0769005001c0144a600a6181030800f403d002d8101a03c4000150a458082d0030200000344081400c02c040d40c2c3c8041402d400205a0322079000c5541007903200701c20401c0081c0041c02045000001c10f220362002a080d641070340352a41d0f01515140d0303161001020300341c02d44140d44640324004044400031030100894425007016110490164a9907090001030201050410941e85000450a01c40328a940b410740c03140d81000701c1250340e55002e20400c400c0710682800c0400f1946000c00300162070710005640404590541800d160655440c00d502c00070304800880102814008900d07030303107000c10b0160101562580d00c400d032241c9821002005000707000900c0f542045240c642c2104c400314030610700030501c0c50f000d0070a80719201d4400000c90b1000c901511703410b043c0400080c00c6001d0144550164103426001c4024100461400d014010b481c45a0b004070042d0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 73352690 1250 73351440 73351451
    0x1a01110304060c1a0103060b09101523041203030e01021204060b04150f1a0a020c01050703050d05040b010519050114092206030c090203010605180310060f080106080a15 74
    0x82c03100c80c80001544410009139000c5560312441c10a002d400d00c5055580030300e424001080c02000c003d100142540c1a403480220400c2c1d00c142d080312128441071140d03540304207400c01a24208510740050001c1d2160b101c000a481e00180380007800c54045035582002648103115400888001c0c1e02c10380d401682060020415214201c0014024412204071484101c0a1540000e00c407032050a442c0484120002e0107101c520f05c01508102885500c802c032006800400d000d403000d60040000d040194004d1a10a040216128a100850300e080e28251070403082c4d00010859880c086040c0c0c40f1014400c1600a0700c03d2902c00080c00480c0c010070624903010001c42c041134252290300602180b004200d0317840501450140341d000007031450340801e4130344c80300241020031440c0160084904036803045d42c07214940145075401810000840720b01c5541806a010b440e86a032429005600140a507083c410518614001c143c03400c40f291030f03201907003503041000764030b000c50700e1040384403100f8a07290300210300b = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 73353940 1250 73352690 73352693
    0xc02040903030209090a0507121a0603190f021801050a020c120f06010308220b030402090a02040509040302010f180c030204020306030717060402030d080405100b04060b0d1a01110304060c 82
    0x3c0d014252460b07130070080c41010450412100d0300700381c2c00307050709445402040d25071100210980c0c07000c074003070740112001d1140c4c0c00ac0f50030008021741d4009907035920b0761499407410205d1001d0b1105400c8843c40c0030340200300d408581c660300711010803210003400c20603d011280d1002039141c107c02c1003000e100d21548690591446418001250f1100480342690700c40c0d0b07180d207005041a04105403c200722440800454603002c0032541d12406c0d40d03400c400d2142155215070820040785c100400701c00d409034092000040607200c9041c2d2502a40c0309400201c3c3c00656003111004a1300e054603c0da113502c08500310300b8003090b52441d17002c007070341d4058401580d665102000302c0e02d414029801315617075001c5d40110185580c0003056880c0164402c5050301d0707504211920440360f001045d500641260008051103101d481c0c10f6104440c0003070301500201d03111380c2d03c0140802581001d0640382040d40c40b201d06084841c0101c0c0280041314090810b4403440000b049060342d80d006c0c0e07004550a00c682c1000000 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 73355190 1250 73353940 73353947
    0x181023241203040e0a0605040204030201090e04030e040504080705010f020f0a050702280e060102011b0e041e14010b071e0c03080f0d050a0c0e01030902011206030506100602030a0c02040903 83
    0x210341c0d20801c0216941d841c1e8031008405030f0f1404650b000b451901c0c3c0480400c0340c0c9054022202100c0e01651000d17102410705135003030b0b81018042e2044061040070081a42d140e103840c001c0d140700d98040c0c0141e585904050910900307507a440c000c1400c55620401141a10704907803410b40b155042e0340d00d000c0703455210a10118041404041495404441e10004085110b52141d490000e0305c06140a4070600d0310b800005a003a9064840c46124004110211104241c803680f01440c03202c00040022880504541303803803880714140a00c980d652601c0c3d40c5410092010000b00600601c08a42d0036031401c441a20b03007224841d4161041d103070101c1c0001105050110390b0003140095034210341010758a02610280006651011500d840683d00f028000b4072944100d104907a079000081d01d948100092400044005103400381c012418040303548005e034541130141c81010040c41c400d40c001d20b400d00f4602c0b140e02a000c115800a0300310761003084001c0c1030b19446070900310320076070643c4c021170000d01c4c51400341c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 73356440 1250 73355190 73355209
    0x6030f210a09030501020c070519060815040207120201051f030f02010c1703070f1101020a0c080901030e060a060515040324020d09050c1e1818102324 66
    0x1031303c40d42c004544104030794808075454081b11011030720b12000041c0c0c445190200f42031449030201160140c1d0001d94004c4000800e40c115242c010300c01031410480d070341e0311a2070030320106410380141c1d903c0c402c10079003414503030441118550542c110030109145558105c4180c0601000a0400c8449840c0504010008a210151254840c5c5558503441c1c076000041c511542640010009400141d007110205410710071a2404442556000074420054480680c01c0e4403500c02941010395071548007000d0041407080350300400800313001044942c603100402560180030b4903010504407042100b000002d0f00c60524001c1c2c00b440b50308001a154011407000e0090050318600d0000d1814a00c3c2c003000c001000c200140c66040446400d1142c00b001e00c40c07810310404010f0a50f41042c06100a40d400c0100880384c1f0ba03025508454800c00c0c00c03000c407074090030060b04015207140030761039940a0201c8080030800b0b01ca40c5d44500b51a00e220702d401c3e1102a400210442109003141c40d0844d104c0043e290b03800c08 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 73357690 1250 73356440 73356443
    0x1060e0307030507051314090309011e120902030c030304030807140304051f03151215061802090f0a0f170111070308060a1a040f090905060c1b01090b06030f210a0903 73
    0x155008c0c81c00d40b516640f40e0340850409400101820404102055040c090709900c8001d03694041d440a6010450f80080c41003e9041e64503104070b04c070b101101d9404100400203903200d404030b640c41b10400d141a181112030303000c0c3c000c2c954109020178001d5031504c01c0c10041e02c0103007240440c4241801c0342d013a402084603405a441c100b8042c1c40104400d0240c3c40242c5200344036618640d080f032030309408681100c00c0c0e0700401c0800140d10441062034101e0390054070345404010001c41c00300764404005285040c4583c001c02c1000c84510003000303620407104a51a00840901c02408040040491100c4510880e04010144203040c004243c00d604d402c0c603848054031401c0d54000320520001c4200c403071070308a03100300700c54030400f0305001c501b0900078000c8550340c41e4483d0042103070f6182e51500380019002910a000b0f08242c40d100d20b40800801d001d0a8203c5001d0081003070b81c0d0812006050401c034102c0503900301d5602032410605003030718195004d4600e44076800d5454070b800200c40f080300e020f04c4d503500 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 73358940 1250 73357690 73357721
    0xf0411060d0203180a170c03130f06020d0302030f13030309050a0308100605070f060e0a060f0c0e0f030615010e180f06010c150c030207020405070801060e03070305070513 75
    0x20400028200c1d030340190700501c00f05840c1c3c401a44104880d9595080e484001000e90a190020303ca00000360405814003e4241050380c1c04c000301c00c0d1441c0c00c00c0c94591301010302407401c20300c10010303642c050004200343d441ea40780079841e41c600004074401110010340074410890043d40850181440b9901a000055204003520040d4225060051a0301401da0b030804402c10358420004da2580501c0841710015070101c2c100c2207500c0d05889200081c11080713070002c002e0141ea440c0a001441601c42d0940da001505d00002d40c0c4215010003d020340001c13589030f40100150303032a03010180e400051107a40076210400c0e00102d2244440100e80d6410284c0050341c01c044008e5030000c1d000b005040c0716218809040c0c6845a0f0350b1064011282e0510380c800150440c1d0100786005403c0d807184d0482d414034943c42c1409480c0c13000320f44c04502141c00c101d0b072100000700110010710040d40c0c48205049100400c400410301e950035903d07170380c0e280d100764420103100c0c144c10000002450a25000012484080003 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 73360190 1250 73358940 73358947
    0x509060d02030a1506020a050a06051e040803010f0902030603100b1c08090411030402060301030b100b0703020606030705040b06181306030803070f05211026010b030d080f041106 78
    0x100c40c3d400b405610000705944c504882001c80d02501c0025040601170f00680103204880154564000600000d040c468000c400081c4030b4480c1641c5503e56400340d840760000e03039503035807401c01500c406000640004986030300400a110380e564000070807910070300742441c00040d031080190015080840444004101034440350490060007102009001001030a031024400344c05000400078080c0320489000394030043c20b00040c4082105442c005a0141c40c034035400d0403482e1203186c28585071b000341c1801c40042c4d0081342000b11905052003280000c0505072424010f150b02e0200185440c0624102e50720410035a5008401da65600200c401c0c0c41211043c007000701075240d00380629141c0c01100c0c080c001c540c01310160f00b40d81d071080c800c07941c0e66010f12050a02c01c000ca81602d6030b1002014000c0c411000400c4000b2030520b43e01c0107241103030711240d182407004844c0603160fa401e540540071958441d130000e00c072255842e03400c06500e541c0072958188400c2c2c0ca960714a441440107640300001e45c3c0006011 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 73361440 1250 73360190 73360201
    0x8070f11120405090108030306010c0f0c0b19020118050706050a030f0e0325110904060f0c0e0a05060304080306090601090906060c02040b0910050108090c3304080d0509060d0203 78
    0x22006105444050711998051707a21040900d40d60300c801c1d02c8d081d0002d1202c60750140411019261000030a21691101c0800e90780e594a444d0681c000f4a210782e0b01c0000003902c2201d0540901c10440340e0402031058400a003055120b994a4000b14443d80082c13003c0001c5507840e15100f940440c54075204107904120800c621000c05075a42c01580c244c0150070340308002c020300c6550070b01012200c03950103140d01c407070b5107051024449541406070080301d41c00e03107405e04401703a21054014010b48080c19541d982c8820580020405c801c40389900c0300340502010000d07c400300712058101c80e0700800590304a10740d91a80390040341c0301c1450f030384030581c1d0f6881c0c800045011380d0300180307031044603000b1181440440041810444146829142e280b445141950100015402881c4155010381d1400680c4e2819514601190251407200481c9c0c00081d07281040b5000303035840c1f40580c08500c0d44083c0c010f00b000d0401511666074180340742c10f80c040c07041c08580d0010070313a106412a501001c4002080d034030790519 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 73362690 1250 73361440 73361473
    0xe070305070e010503190201050a0c0b0405010b0108070c02060313020a05060309010203011a0f03060d230303040203060a150e040203280c1502070b0f070b04031101050105090708070f11 81
    0x260142c2c484882d400000040d42d854002141c00105c00c5080e210843d080c1180d005450551210301400d05000c1c29010440104002c070210500c11401a40003055400341ea60005200481c020100428800300b0b500c0d000250f100e460650307a000801c800062001912800081c0c000607080c2c7c00181d00481c0042001000700043d0059812180c50340701d01d0601510b0b500700803240b80101076004138030407424000680300745006903101c0c00d0303240a002001d00241c4030300503070001c0c160404540d001661000051000314202001500d910106803201003080041002e104915869a807294a00304000b070300c003190956405100444504000541e500c0f001d0820706214044420009400e503a00040001300144500c2c4070b00601c1d1665003ea4080d200141c100100038000f42c00140c5041d00000040c01500300042d85c840700180554025203030081e01c540c1c0124a00d00b56041600414081c400c80c2c018070544540020360150051501d042600b1020104c6800710707002504403c9401880c400c1e2500000050304 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 73363940 1250 73362690 73362703
    0x4030b040807060b0f0d080a03110c0a11040b090414030d0501030b1603110301090c0207090207030504170706080105060a030e070312180e0a090c0f060527010806040f0e070305 77
    0x110f40300a20161200d9030412601340e025408943e085540058002c0000d074146000b08240089410001070010002d0340514598220390300c0441550b000c00d80310020320242d603a08101d0118200d400b800300d81c4d01320380840c00755400504001c000f80396101c4c407a40c9003081402900c22040450100300100e40e5a4141051401d00c152240303104e240c0304802e902a070302e00c24001d07060a081000d00982c40c59103090700350001840d14503510303821405a60008120070031980001c0910a00030b0356415155410b082e0040c000c056068007204071070780449020455039030002c0b4217504503030b81214002d03145c20524500b900982108503481c46107000c0c2050100c100304811040842190165489220500102061000150b424000d00032009007110008061441c076400c020070581c4205c540d05802603940d281ea904241c400e40003400403500102d80c04030b403540b207104110180720114100c16200550308001070540b09000e0f250310301894981403601c5c0103140582000207002030b04400c9403a815602d0030300c40c9d191034 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 73365190 1250 73363940 73363943
    0x90213031b0f0801050609070e0d0c0f050108091b0f04020d020a030c030b03150112020301090b010602030333130b030a1103010b010915210603030f020607300204030b040807 76
    0x5145802c0400e56031414841c07507108003001b600103441c0752038104081c1d03400036000e40d80310361007021030200d000022813036040310001f05001b481c4115002d01b0703c0300151182c80010702c80003041d801442403099213600201541222801902c0b0303071112a2894010502900c65942c810f00024000990780c2c003240d5055010708142c240c41e9804020f5000c01c20101a00d40b242030603120380c0715034100018085050158001c8401c0c0348000c00004031280507030f1308c1c0c1c00102407d0f403022026801c00700410400b940204070000f0003076150b81107144000c9001d02074044084003555001c1c0540550110710210f83c4207680018041c0c4001000c8031814020b610b030076100c0c480c409410300d002c2d500f400c0400b46c813540540e40400035217400440403110304904030f1048611107050200080d10305044609540307107000501c9040050b5000740d440c42032781600144003a15041340a0b016808228074000ca0290300d0300300d103060084810100e0000d4020903100c0c190f0b00085e002c0da41018004881c1c0c00140003c101c002da0091078000d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 73366440 1250 73365190 73365209
    0x60e01020d030203010503070b0f0702031c080109061a030402040b03010f09020103060806010303050703050705030403021801080d0206010806192c0607030203010b03070309240204061d0604090213031b 88
    0x4807501c0c4044050340400c0c4101c603050f6102d50001d0288444036406414014601004c490414409030002071404101d1340d00d007580d0707070043c2141c4090b0300da10030302240c007426408a01348001403524000451005080a803000d132044003002240031951141c124035214030b40200240000010103813010000d15005004a001c6494404001006a00482c00714101c0340c040c1c0303070b844c10621680c8080e5026449450f0484850108100c00300040c1d0760242a030040d2125110341d000c80b0341c1007011251a014000340030b00e05651107440100560400003400980c03082070225a44090104010b00c0009800e08003d003c20000403140644c0c035032142c0e03d090301080102101194401e0720b9281c01501284070030300401d52020404c1000070031890003900009032241c0321f0113049815081c143c0c040c0381041c5030f640011806d16000901080401d60203c14010140d5146480501c4134032400c001030958422031180d41c030019000305440d1810040985c41074020741c1c0203d18554103c8101040034680d83c4075004441c0704 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 73367690 1250 73366440 73366453
    0x2b030c03140105010c0c0f0305030307031a150a0302070602040905060a12050d0804021804210905011b11120c0102060f130f170d020706060608042604050406060e0102 73
    0x1051290080700e200c5446001e400301c85034200f600440d80540c00c010256201441420002504251454004010b6000e03001031074030b03414000001803c0e1160750f940e00c41e11888003100081c6030303514142060007010480141503501c0b05240c400368041d00500401420951005c40c0024448060b5080b0307911486c804c903000b021081d29450b03480d15800042c840500300d03170301861212003070714081c1070301981050000b405024520b801e202440d4912504a0f002c5511080503280c80340700d8010b044170784000b40800e091045403241080700007000b07600d07901921046520b005a0410034403c0d1070740e0710320f8082000740c00c602101000c3c4024a07038a0035220702d414014800c0e000000d0b50b84403c400b515000d4001a1008182030110f42c9071400c3c03600e0710030b0f4150313207007600580e546400610060042a076942c8120000d40c0761021820b1040440e40c050f4005014066100b08120002e035003420b0280249503030707000c400c1d43e41a1000c140708c004e0040350070098200d8548000441d2203500140745e119100000d0f400c031000f = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 73368940 1250 73367690 73367711
    0x30b0708090d050304050106240305013002040e0604030809060906060109031101020c0306010f08191106030a090804090905061b1902030f04030c080706031404020d02032b03 76
    0xc80000c101c8200103035400c000e4018a0040c4183c0c010742d0094000c04c0082212074036038000c00c1c154282c03000a215041e00c05206150580d40500840380104040000d880b0441c00303d1030140441d00740303a45005807255238503081800315035890307100c11003210380d00d400c440031854285406441c100c3d058502d82241d01c03070700c000a040c02d0390020345d540c440c031010b80d41c0320001031031903948100e04605802c81d141503016000e40d28100d038604000303090007480e9441a00400b00d03e418800380c01c3c02420031500446011050340300001c5181c40c2506441032074203884080d03aa5884d440000c0080000ea00c00070700c202d20000c4e000407400b1480d005a01c4940c00740065035040d032604000d02c2c920303051102c00404000410b11003081499010707286042d90103001e00560349000c4204001141a9006070400c6400d000720020a1010300700410100303000c1c2495007001c01a1b5020081c03030112244000b04001c0c424540c2d40d000d43d08544045c41500700581c01200e5150850b0349541312404284030000303240b000079280940500 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 73370190 1250 73368940 73368947
    0x60f0306170f100e19030519050310050d0206040620010c08041103011406040f02090306040c090c020d0c0f030c0b0a05150307050a1503090503160605010f03050d0c022107030b07 78
    0x40884c1e8000030f010700c549000b00884042d42414040d01400010300500001040303a801e61080813040d566402c0e90b82ca445d05c140c410100d01608081d0040313610118840040c0c640c4000c480a462039428071f04481d017030052404a507645000711001230742d402c3c4103442407626048850103000301c2c403641c590210321041d181414203c0e1107002c0309400c12500d50000c98030750f0905600401200c01050800342c41c015101c0f000c00d00d80101501c00701d50240074072404020180d80c80c41110704088161000d480d0902d00110014001c0c0c19a41c400380020803030110358030806000381040030196030300c115580070311310f080910b0300000d100c00c036070a000b41014820a2640c2c1d06d800f0610900395000109041c90300ba09000035170745000440c5250a041c103680f4840344010950410140100a107070f0301030180030307280a15000060b02c006a21400303803410161014000284049820325980f411450225600d03542400002da8004098412140b0300800000082420038003091001c140e03802400c4003012034480d000c04a = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 73371440 1250 73370190 73370201
    0x203180607050c0d0206040911042c0106030e0c0d031d040b0d060b030f120414030a0c05010c0318080c1f050712050c01050f0a0c03060302010207060f0306170f10 71
    0x404a41220f01501000c2c03414490322150b50f4006003542e0306207034075140c442048856140c00f10321803000105003000217030f0f0b01110003500b0b5142d502d02405400c9980c030700d490000a060181d40d042c5a100e00103a00241410045080046c00c0100411440656410082c01da9000084012012101e55006280700d04040c040c4030000c6001420161311120b068036840b000f050714132000c0d0340c18040c04026008411007000300d0610003070300e000001c1d61240340ca0300f01006414034115440c020703040701c5c000c030003c47d16006820085940a08008000441500d402c07a48000400304520b44080d66250128461400040000c0012420381e0078514203404c4c200d06007400807034050410f000032010840300002450615420350703540c0c1603040042c10118842d01c1c036070030b441046812190040c80001000005007545c010480c1c2c290450404000042c25500002c0d1551401e003d001d050205655500340d4407803096120380003d00d444500d0306260060018bc1907142c54035003003000d1161180c3d6011000c1c0c1c14052252 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 73372690 1250 73371440 73371443
    0x90a0b0705091008040b0612010209040e0f06150604030b0a0219020d0e0105120c0c0712120e100215071101020d0e07060503100306050601030e03070605060112020a0e0402030c0f07030203180607 85
    0x2c6e401a980e04410000340e41c6418404600c10354090000b00c7c266216070044907600c01c05440038248c0600c0110380d40385403000050185011070802c0003281d4094035890201d41c26640c0103001d100c2c0070b554a200520103407007900003a1840d07e441002c100f940c1640030440070640c210540d918001d840b4002e00450301ea00541e02c90b03840d030b001442c0102d0001c4e40b030300b0700824611300c000c1c06441c01e25a0300e41c105130700242443e40503030360748146020b20038102e54855121024184111f500071000c2818a00080d540c2d10004544034407010441c0109419078060810031a2825140f8000d41d03035024000d00d5913019010b0600c0340341301441409070200d111801141a00d209407080317007484950b1459601ca000c054038010705001e05042e030394440e4084841e0180020326090307008000120b082e0420000052018404071010918248140041b42556901c0b015a41c4450012640583c8035112000c0c1403019114030840c50442c80d500140700030404d60080090040710b0361f02c0c04402016441c450a00185110b030010 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 73373940 1250 73372690 73372703
    0x302100e01020901050f07140604030507050c06030103081c0e0f0f0f010203010302010f08041506080607080f07020a02093d0f0f050103022802010e280b090a0b070509100804 76
    0x924450b186c59405017414501480043c3c2d000c000d81c07001103003008829181500080c0300064a03100307200007005503801034607098400c1b40c0f842d031554481c4511402014210f540d181d000100e00000e582007a04032481c040d6101054420075001c118403a69645000700c1040c1460048050404a1050600c00e4030f048039010307180c4010f03002510ba03044840e5007008108a1b500e01ca240b59180c00484070340303e540040c0440400070a242c7c2000403002c2d1440500801c00c081c14028001001105680030541401495040e55134442907103580000040b8507000360b010300e1300c1e5054a842d00d2448005e500c1404003807e42901c85180c5c840d00c1d5181030200c0300b15400f900315980807070101008594803e030300030808083c40078000309240c3c6070221061700c0382d03039085400e000603919100308144110080c801100e5017001110920702a445180f840380c0122031202d0301400c14855000010304015080c45424040c0d64131000d8654140350440002d00a9045611524041ca00c83c14604103842e00421446014607003021 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 73375190 1250 73373940 73373947
    0x6030b0402120f0a0309030201030f06030804150e04110a08100806042a0902091507110114070b010806010315140a0209060408100609110f030606160209040302100e0102090105 77
    0x400307108002c80795401c0702082e80708924520709400014492015038074840c0d514013000916500004040e51402e0044a10140c905101000042c208200310707000c0b43d0b40010300440101040302c00383c0344041409038150b009030030002e40704203603912000102080713007650302c0e030f0354031a11a0944140d040b46a0701a0b0840c9070300240103c0c01003010a101c008048400f1ba800c0c8102e5030382042548201121548003110f501c0d000b04070b440a070310700342d00d0513100045107000d1281048229100e6620304a1076030082c41c1444440c4502c1801410400111800c80390006c0394181d06580d20800383c1d54900091109441c019a20400900300300414060351244000c03031a804021500c0e03034544c500083d8400c1100e45d40c800b0080000141d079505c1444001040c41400c10700290360742ca01100c030380c10b031101990324400000e01009002d80454500b01541d420003000e8940689504600d8801c0d01c54280b42d1801940c03011400302044201540040e82403401c901d80341d401e00080e017240c5030f0a400d030b0080d5038031700780400d1050 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 73376440 1250 73375190 73375193
    0x203030103110f1c0b0a0c0e030c130b060403080d06050f010c030807020c0a0807050a050402090306040303020d180b1b0a200304090606021606020a02151602030f030c01050a06030b04 80
    0xf24040d00320581d004010b03108146404580f09000440f00904039075900b040c10800c01080c0e0b003413140c0e01092599042c040050444100060340780c040c0c4440c0503110b1610702200030340002950340103091400c0041c0019550f01d03101c0c184003905030003428100d50200d0818102148500f06010011602641a181c808142a066500380c0301000e0090030b40045104684446441d42e5a44040758010b2080e040681482820401803080a4040d80c10842c0224010000c05010362400948540c0c0207400d40b60043e01c610220814201401c807004400504510f20b410450500c40800249c034001c1c0c4e20f8003d01501e034507802141c18000c0c042e450350030010614000780218107101862a00d110740441000380c03407816803649500001c0302c0340d80e009200180c1c0110390100000d00752502c800c0241c11640020411050690700041043d000040456514000400c1064030011015100c1401d990700034151400c51007092101070340c1e50031401c00d1000035130a14011800201e128421f22003540c1d0072003503110301035449 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 73377690 1250 73376440 73376449
    0xb010f051818010507051b1207120309020303040b0a030b010c051c0315030f0218090c060d0212010b09040b12030d110403061505041d0706110106030c0e0a050106020303010311 77
    0x2401c034030844031500510b044020080c85a00d100d100d40740c44881e151542d81d0800030003200e0500d0703c0ea04582c00f10b481c070f070302c0c2e1942d82c0c0680d5240e41e13020516402e00d014240c4102c010b0041448020740603c03003c2404a9102c82e04c20142c050100d4907503082204a03038a100441c1c4100704444086c0407030f0032801d07000d41c41d44001d1184c409619090709012442c082404004504bd90155006603114800c1890900461915810b00340560804e00341031705003414a00891a03da00020800900c00c4d5000500a8003021064054440c0081908002e14003580e50384550352082d400b10f96072501c51071400544201c0d6161142140801e0701d2120b0003542824142d011101c01030114001d40528407109100020001d9604d0045d14141441c154050001501c0c040503c81564a100c1c94200c210100b0f0f0f81e1b40ca0704040014a00046070128a400800380d43d1010400e4014070b441d07000644022890900420220711680d1458001c20f20081c081005a0362030100b203880b40002c0c0401000200f140101e8021884c0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 73378940 1250 73377690 73377739
    0xc03060a031101021e070314061504150b0721020f07050402030c04240212040608070c17040806041707030210110d0501091a03011e0e030c030708070b010f05 69
    0x411300490701845030008410111820380b10151050ba8040c04003072007044000d405014103800b21100800b00d0341000d10a03945003043d5840001d015681e9074003192800048003151a00030030745811081d98403002801e04e540281207000d40e0601480040013000a21440003171030392610800c1c480900309950404040002a50025040c1c1004001c10300c00071034480364188650040d107070844c06107164882002000382c00c08801c510f50000441c4240010402c0d65084414958014014a8100b40c5026980342030300032082182c80c0c500200c2c07004a004560300c00c000540e28015406071940c00e0a00034400001c0d8038a12421000a00607040443e0f4054101115007100c1400c2d1841c191050400124540c5101221401d91000812a0f102c031000e403d4810403000c010b142c0c1006400920028000054541d0614694000c0301440d568410b0303581c9020380c0c10700c2510b5100c06004c00390380d42e6a0443c10407441641040005495203018403000062550181e10094111400a03207071002c1480183c507900c22440 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 73380190 1250 73378940 73378973
    0x5100318050111131409040b0402030a3228110409110108060405160f03020c0a0b010509090309011409060903010f020d060602071a0a02070e0709030b0c03060a03 71
    0x124440d6886002807001e0003148503c407040c610094481a00302464244248154054590080c120b031126000341c0f240300c511039210b501301c02015003d03111880800d180c81c060b00e5001d4125189011203941c80003541c01c01200015800d080341c00c00c036182019040d100e90f290070152480f00c100e202441c81621080c3d0f9a59045400345008110305d01088000c1800d070f82001c0411603488120f210401c1896030044034003900704400791802c002d145045000317004041d200f14a54402c1c0701c030030070750000044e10031303011540c0c40110796003990080b101301e2038200c1000c0c1e400c2c040c0a1041c5248400101d010b02d0000944425007416912803050117a61018a038060b84000790b95500710303000b040002950b8409024480381503005050042e43c0310142055881100c1d849d800140442d00040030401041c560b9420100c0c02084424070f0503601c0c0340301070044e460b000240d40040210071402007045091604850380501301ca000c3c1c41e00d010300b5a135140840c01244411114154001440c41091000c5002001c825400c1c0c0d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 73381297 1107 73380190 73380221
    0x20d0507051903051b07060501060201111305061c020a02100606020109081c18050d020c0d1208070203130f03060c030c050d0f0204090f0b150301051003 67
    0x1061104501c410151aa00441c01c0602d000c03500440d03221700714040b45d40c1c4440503c2d000c40034102c2445500099464426001c400e14008403c40b0035203a80d1400c0c044da0b241c184020403c89812080b40400c60401800e10300305116118401000f0310102600103003002d181c4c520300103050341c0294002e50116410003039003600003140030040c6d03a941242181c1c040540b03602858184000e00c0300c68071803002c13140a80021010301c880030801c0c1403081c505034291903481220009220b5490600e0030010031810013002003a20184c4600c0c0040d030000b03060300c152840c1c481c1000300d2001d520341c65041580300501d108010010016248541c56404103039050a014180080201415900440003014041c070348880c2407001c0a0b4a90381141c02410814000b0461560183c540c203004001100b2080c2c0207010061181c4907000148003079030b0403610014280180c1c1e030350300401180900f202180f00d0846 = true := by decide +kernel

theorem cover : BRFrame.Cov 73201440 73381297 := by
  have h0 := BRFrame.cov_init 73201440
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73201440 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 73201440 ≤ n) (h2 : n < 73381297) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
