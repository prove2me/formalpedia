-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3069
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:34:03.316994+00:00
-- url     : https://prove2.me/submissions/6b1ad22b-aac2-440e-957a-551ff88dc357

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 551798561 ≤ n < 551978417 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 551799811 1250 551798561 551798567
    0x903090e090703060507020c030c0301051303050c030903030412060606021c030c1e0201090c120206030610090b2106030a02061c0608010906151a0406030507110a0b06030d034206 78
    0x220480c49c0240304038030074040503083c14401e80e481200c0c401d1003502c0300e4155a03422a0070781d2010070f0320350048c0300c11f1010500c00e81d0188001c20041c80d08140c4419040c590340341480a5606aa02071000c1d90400481b5280340d000c0d528808034120264680002d07045210744007501e5410900c2245c10156109000c0901032580540c007000105001d00170708159141e441c8081d548028010398025003242061000c1140b1741040c0a420b440800c050900c0b1061589905c6042241e411459068034010952204005201c0f0000c105075000701058001e48030002c210340100b02c0d18414080f00341c100046900b41182ea1030200e901c8000a020390030000e21583c05241801406442d05e6000d20383c0001415030001464410b1034014040380c0c100c0710b02c050605140c100305500401e8010145414024072407040c042d45201484052411403003080d03283ca15061810038549810000c00f84030040c1841c1260182100c000348042c0c01040180c014a9000c400d4404004120300a03034050034050000c0b40540443c0c0c4c1c80d0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 551801061 1250 551799811 551799823
    0x7050118150623060f0d0903030213170d1115090a060b100e0405040f0f0c15260603070f031428060c03020c03070b0610030903090e09070306050702 65
    0x7012000d001c280d07100c43c3d101d841d0030602d1161501c2d282102040010900b400c002400200c1c07015041941401703240c0c0c14420a540d13102d101100000d40c00507044a01e840c0c039015100240001c00700306010f80005014050383c904260310310b00140700c041c409403c021a02040b481501240c604c54111150401d00b101550b9050114400c54034981001113119950a00d80031100b0f40d48815600c00c2c0c203441210301404010040644260b44048500e07421002007105146600d001d28800c1945141c407600c2c00b084c03403601e0f81e440c0b46c000301008969503e100d181001850f04d0200d02010751246003642c0c895030002131410070701d40e10104c101484004008103001d40c210301d0707803800908101036803040322211481d04000000d1690300c1d00502c000b6030010000c0342c1e85500403008000e06090042c604119030905900e03640200b0011a40d4030041010003580d81409442841244040e05044c03119400c15035026150f003045005050051541100003464108104142801036810030000c200358140000300030740f949 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 551802311 1250 551801061 551801093
    0x20030a030504110d150c020d0210090534050f0d02060f04090e070602060f060121150b0a0e15091c121e08040305041715090c090a05010602060106030207050118 70
    0xa45000320740c086c800c1c00494075490221840d8054154038000c2d01d80000100211141603440d8803c01d40c112030220b242c0c007501101c1c3c155402040302c0801d10060400c080e036405810580c0141d00103809a500c50b2181c40300b10700b585504a0786107840b85000d805090143c060341c0c0c0580780309403d01040035949900030a90350240ea09507030944030541e665102d2081c3c60f030b000b561000e0000c0c4d00c0441a031008804401c60401c0c03021640400310303418641e1100c0c0c6149801640007202036040004e011181d0542004003441108000c1d65442168071451901c003a06000d0b48005d00d0050030809101454403050044103c00207900101e0b2580d81c80400c02c0040c0400d030110069224a903103520946403d9001c0c0701d015108a80c1580da01c1e150508194841d56000c40b5103000c2c03230042c800c0106440401c1d9004481600c240440030051103010104000c10140c81c00151590031601d103000014408180e02141c40c0b03065507124180980e807502e2070318101d401841d1030395855420880c003409642c10070440c5140d1103072103 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 551803561 1250 551802311 551802353
    0x1118040203100209100f0c02100f020709090f0b07120e012909012102120102191407021507081603022404020f0d051006050120030a030504110d 63
    0x21041c1c2d202600c228480e40f041d56034020310800c11041c80030b205545e600941c0d8142c1c903000440002d1580400c40540d01c030508503012030148544039554580c10001d4400408010100740402546a15030027550021001e0203040180850300181d0b00700c0c0584500b40e42c075040f07a0010403c001d5400402402414801c00200c0030050741c00c1f40421400ba0801080d080a00080245807241d01c0c2148081e0143d1528a6490340946061031a20140c5c2e22025541d8105030140000360703407080007044a2030000c0141d0404070078400f0a0f468406890303480f40540c2e5441d903040d584450108043d0505c02070703074000e0490051070443e00040d41c8410420740d000e4010300901c66022035030a044c0804040e101150f100c0482d01d80c1c4481000014054074080d10310405002000d0049208640340307071509400c1c13181200c400500039445003410882544c0c4001b4040124540c0184802c0c0c030001c2c2c00740a80c4903c00c240181080586450104050001d8a4007100c0f2001000703000002c4078509240c030b000c000d482146d801c010 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 551804811 1250 551803561 551803573
    0x905071a071203020a0e090a060510080609160906030c020307120f02062206020d021902070f09060e13020f06041806090209030303010b13030203010c05030a051006090504091118040203 81
    0x841e0f4064001d07144046401e45501d081003400e1824803103150001807100e1484c54484a0008458031020b10490504503603554200305454103a0500100d4080030340041c111103031092031204103907403005240041d5403492401044e01d01300e91104a14601a421025120200320340d100801c442c1c0100d6168189070310351302624403d94443c401d483c08440d40008081014100300015800500d00b0790040003401107040b4010b050070600742c200c01c04d50003031090010260b032040c80d00344560045c04d82640f0040072228001e2100c1400c2c084001c0580750003070441b0150b201008413020440d5269007128400460143c0304907110750390b480702115082721481c5000c2600340361450101d0b40c11800d008843c603604000d4002d516503481c0c140310f0007496100c03280300c0c20195103102001c40161740070f000f2100004096070b506a101e007031051080d01214009080c41c40040840310042101075001040d403421210121400a00b5180e681000d841040c0001c83c1c803540040d822400d0000040e144d00fa080c05203000744c08540c0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 551806061 1250 551804811 551804843
    0x1b040909051e100c200106050a080a230c04110409060f0311090402061303050604060c0c110111030d0f0e120f04030206090423070206070f0509040905071a07 69
    0x1c0c0140300302c40b00401c2908581804141d10340070343c110003600000c070314007100342100c0703122070b4484184500380c00f9195944030310080160786013150380740d0060408180501410f40c4240d47e25180b551f0b40e04a0700c40300301010041c1d802c08210522944a01040140091020450000da840d28030f61090040741041494031501044100c0691484ca05682c1d0040c004a0801d50b1007042080010005100701d0b84900304010000003e1280200c000041d80724000400f81e40c00c0074074140007035401040040080240c1c8070314403000300d9a03040d82034500500a00380116024247e1001e5811446040d01004c00e003818058000c0c0361428581c480b964119144040e2007268103410f04a87d1548103980f034041e09014248803d001618040c0c009000c8500014000180300944512003540e100c00d03005442d0031034850000b001452501804030642c880030310f180050402004000181190003034000250003555a10b0052081017000c119540107421007815101c41d659000310405282d911029040f55050a20700f071847d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 551807311 1250 551806061 551806093
    0xb2b0b060d051c1404081f020c0708010209041119111c0c02030705180726010b0909010e0108030703030207020409020918010f0203070507240203070c1109040f0201081b04090905 78
    0xe02910760300c078040d00903840e0036041c074211f800d07e02c44512101e0781d0030065400714882c2003040c03800a0400d0700025031145004403c0208035003002200d0044204104a900481141490007024104140c108aaa800240200c15207080d110001c0912416076110134020180d4125400319104c600c2202111440c5d500d540600c407201d046418081c0c44030380540702142c90b032401240c0c2d010000702c150a1443c5480c000c00c901d851044d2081e4002c0f010100001804501824008540f5000d8030340d450481a06500d04401c260740ca2295501c080d040544c00b06419046503100d0b00040e03240c5800504e031404e036003890006103450509000c91b4407640d600c0c0c4a202c9100300e2040c000c1c1c81c4a4803044c2c13107280c1048150b841e51401054001c00009a00000d42540c440140541c800366000b480b540d42e030102d20b4042ca2800000d00070060f900380344102c100c50200700010b0100b4112094103907080c0f0b000c0c1030544940c40003000e0f403144108481440240483d010032034a01e40d9100356100760103401101c0400415000030 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 551808561 1250 551807311 551807317
    0x10b0d0804060c0326010608090d09211202010c020d02010605010e060c030c0d030b100309020607030e13020d020310051207091508030c010b2b0b060d051c14 69
    0x209003000c24002080001d0143c1503c07140d0500078106030309403005030b00e44e00120038000e181c0046481150380c010b00c8540c0e0301003501e642c814590f50042c21078000525010b483e5050310f10a84142e00c0b44400f0075426034114003001c4001c680d1001043e150100c0f6410080d000c6c0c0f801c4170003800103100c0e900103c94900e105003d02022100181c480c481d0b0008090b050019640c8540400c078421b101c1040b040c10011020400d110001480b5540021860514410001c4000d40c00020804050a20310300c0405030361510100d41d6034a9060400590b18140340740400daa5403c6001094049840418042d111086580040d803140540740206450369482e4001c000c40d64809107010f882d158082c0d8414041400c01d54003954540c1941005c2d0704046076070b043e9881c030750303484500c0c00400d0341d448031204035250901c2c60401d0301c00030440982e00b03641514000e09800d4030742d0800000d4a05140000031800c1902c5404400161a030007a0545600c241002c1d0283d47c400507040d01580080d01c884041c521031303002c050607 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 551809811 1250 551808561 551808563
    0x90f10050f101802090d08030a06062006180f03030106020c0a090912110c041d100608121c02121008061504020711030a03080403030b0a060c021002070b0c0708010b0d 73
    0x4403d05102d90580002c00a400c19001913401c4075504120502003036004014600c41d0707940c0c03d004520385040490091915100000c455600c40305142c80784032405008c5601c0d5440105400c850032604040c6011070700d0103001d042d076a03005000001c000b0903000d5010603141c40c05d64090724a8a0820340e2402c02c00c045552090001d45213410031013141003082d100b40c040d000c0e100c1d5000c04440d80c0c0d400c1400000c0c205c8a03034100040081e02c0280031440405420f008400c800504100304101080c0340c01002603c452101c00e4164080c0000540f040070f0f0300d59020468001c21504030119110203d440800c901d4820560700a40d80c500112800900e0400c0000c800c2d100e54984902c0900c07411500302808041e4120380011a85540020f05849580c2c40c200106800507020741d071102d12900b0503040107404c44d40e04141300da0080c03091401c00d0044540210310702424a81c1600c8003802c031071419904078204070083d000411040b1001030091203010000030b088040e2501c55008210f2141110100f040794000e01d0f00c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 551811061 1250 551809811 551809829
    0x20607020313050d02122e200307050d020a0f020c090114011b0b09150f1302010c030e0409060c0315050a12031e020105040614060d0605090f10050f10 66
    0x14092003c0c0c10507128025850b81702074040750440100c05500c13400c2591071400c010700400d17500d101c1c000400d010b0519045004c6180400c101c40088800052450280074441913900c04000001c44d01c841d21030400c403031420140e55011521001100f02c002c2003100c00400031001480b40b040105c06502d01051002d04890034007402950042d08580195003c0b014100e21603e480206018500800c10100300c1d40d05c5a04941d001e0b00a07203206001001200c5c0018112078841c00040c0f00704041002c000741c5414405409013000c019040d078518007100e4a07060104001c0d0054100843d000401006400039014030440351414005440c680e6940344401c8100e00c2005d50048a2540c10002001c0300740d2100d040030300030714043c8001c03000998000d220711410390040300142c0d1340e90204003d00c0030510684500c060300da00070714114182a00000e5280342c00b41c1d005042c0300d94640101c3c5079080200283c00951a000040d01c03510200300c500071008000896044000a05000000b50601c0302c41c0c000c0d03816240420 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 551812311 1250 551811061 551811097
    0x5130b09070e0f1e060103020403060f0b090c030906040b1008010911030f01290604050a1403100b0f1207080f070807050102011b0f1b0813090b0f09041a090d0206070203 74
    0xa00d14104100005d068141495409c10000c00420b1403400b4050315041418008166081e0313030780510038400801000c080e20b5510034424007000c458007056040e046508140c0b1500c060300c0d5000144a8800107600c40e41007503180a0001007001000d46045103e4641181902c4a0341a0111010300307840382c622808110b01d01d540608841c80c54414901d9880600c050004d5007090380b6040880c8220081d6080400e0340070740200c0303684c0715141c10001d081c1002c0700f82c1380034801c1002240c04911a503c5008503d4426400c90700100504442001607000400c440b508542110304185481c580b501d01c02c0c02016242e0240040c0422594014002e648503c00143d03042e01074000e01c981700712200050184e50004024403221a0510440c51110b6541254040d480303e541c1d401001e0000240c03828980d00041090f424074482e0451345e85c03400090b01c0a04002d64600025958a241c03030052030381204c440c00e42d0701c044042400105000002d111500003c50b0b001c81380103465072641070f83d8030300884d008504400a83c2d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 551813561 1250 551812311 551812351
    0x90705010804050106090e030c0f210913020412210f1202040b0403030f080702060f011404060e100f17030d020a02011805101104080703030305130b09070e0f 69
    0x5121081d070700a0044000080c41d03511506c5880a44604d1174a00100d50301c0410f02882c1814140034040301003007444000c0072560f04584031a008101d02210018800e200840d41070740a4030703000011690600c1c000011076513140c46070070750740382442e4111050f500f410f2807580e41c44002c14400c0e1001c480b418907071104002c0b01e40301d00045410072804680340142039000e1200082ca201204064409140300703803545403200c5412a001000d2100041078842103600403001e100d2200d8504d0395990551b14545041d141a250382c90203d006000c2c10707407000c5400003a6800300010310905040a4066802c07003020b1038461560fa00309200810030b80c0f161414030760403c00c2a004202c40c1c40d40207000f1000d044c0004103400b200a6809a225950b030b05c4e054030107421086100e10b25003a079105010000351107041041c200760404650581d40c051300e00009050543e0381c40416480d00c01d1f01d00301c203440d40d400f2004003018500b502c00300b51203a84520560406003d028045911803e907002e50328800e891480e8058540012 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 551814811 1250 551813561 551813567
    0x20d0f08130f0e0c070201090e07080f090105060d080c0a080d090b0c0703080a0506011e030f0c02010e1906060f0803122d060f0423070c03080a0b0a0509090109140609070501 76
    0x1085c04c00300d05210f40e154001904c50342c00182d45208542ca5281c601840c9400c980803940070900424440c1264540020000300ea550300c0e1280c40004e0700305c80c0c06902c907800380b1500361500c071391240c01070024100402e0b542c0c10300c2d113944c0104070228440c2c13051017403d4030707580004020740c003c01074028082010390000605c1d800d0207501465000205140c020700d080104500742420712a524558400603441c0c070000da44014141c0180c1e81d00100c588000c01c545c8100114030f5480b1360305144a04040700f034001455081c00b80540041000d4600c030000c2414034cd95408445640b035120b1140d80c894607400c540001d549000343c6954040c00d008400781240c002c0e80c2c00544043d00d110082c0f4142d4426032003080e11a940d00c85206000b600300420340006416a2024041c10841000801001c200690003c004000951081402e43c204582100110300041c01c00005041c0c10748582100740c11914030341c1000200441500146c455602581c18440107901c0c00043c00d449140c210740213001703070340218030810203948 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 551816061 1250 551814811 551814817
    0x6150403150f0b041a0a050f0d23121b01094d01020f06070203071e080a050702040c090b1b0a0507080a05100915020304020d0f08130f0e0c 61
    0x604800060010210f42c0020100d40300c00c001d04408521041d6011a5401c0c00038541004c0c10007203502c6603441e1405000101c0300d8005003002058030a60032800340320000d0b40030390040114002d50956201d4414101100d0305034205000b540f03c0c901003000701c0c0c0c2200c075040c4109443c007500142c56108184141300801c0e0404400c0c440c00d0001100c1d0b55000c104030b1008080b480d986107005100c03d02905610f000246020381001030560320b90440024030031505d40000454100540c010a0419a130302d1030203035035201c0408000c1c0904050320004010300160342c004020000f8910031a8200410728500700e08aa40d50300782d020b641001c0324100a800e00307001941c2180114046140c0c21540d05801582c1c4940c20103510754010b213030300e82c0300b410302c00101b10060040b00b05c01590800200480c0c0e8143e03c4003100c07040c000b1121030b40d5a034000045400c2d52541c44c24103c4564020b03600241c802c030a49000c640344d03800800c10300611100c210f00410344140d05846e402c02c4410500c8000c0d800d0b103c101c1181041d40c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 551817311 1250 551816061 551816081
    0x1015090504020a0e040c1e02120a0804020a0b030c3c0f04180e0f0313060804031704350304110103021e030412030203042a1d0615040315 60
    0x4041213540500e659182e00603e012000c1d07960761400002c100c00c01d00421800e4195140b0155003209003152003040241c0c2c180c0d01d01003504d242400c0036440b20700200c1e4009001d03801503100802c000041114210241c00282150b402e44580114440724060501316400d04a82455045e802c140000101e40140c190241c0403070a109610146015075890207103013182c01a4864086c0e480d00c0380d8070155640c1081c84100780031590517000e103280440e05a10311044291900403041401807800204052501c65190720a400108010035000707070500d13080c03410b41070f14030700340074140c59013040f90702725040708c646031400c44100280d5129811a207859580607248603429519a040681c24482e201c4106c0b0101d003900c00300e60083c41c0441d5a81003038280100d02600849540d010b2500420a1000007804031502821000c0314803c10406000b50400e1086460901d80c081c2c01510005100c2c41848000c4001c10360281ea0111801e00c001003c000b9420f000b8011880701a10301c02c071103d11309540b203110740c201e61228 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 551818561 1250 551817311 551817317
    0x102190e010e120708031809130308040b04050118032c030703150b030703140c040902060306041d01050a0605031603030509010c110a06080f0a200c010b03070e1015090504020a 77
    0x707885e401840e00e1a080303600790016404089902e0070060402e80b80c0790307030000020002c0c58040007990700d018001040140c4020302c451407401c0040d042c00020341c44090307095101d00300248901854140180b08800050b07180e40c0e81d224103c106424820b840d402c00510910240c09000a6455502e94560507296180510300103500c5001c82c00c050782d414894417010f90b200d0350100c094900306c4404140380c100e419041c0c0703025502e003240600240c0e4a501c1500e80c0680212004034141a0b82c50440c114448021713030241d031365070a0070309108016816400c4281546e0b0240d044a001c0b6102481404002030f040c0700180103c0e80070004810700754440c3e04034001c0c243c01a07031034402011540c00414181c40c925880000066044010312440324002a0300c00e4120302420703000d02901e151090320300a00101801200540c4c0e030001224082d0003402c2d0400c07000b034003008096641030342c0d4803241d4180054040716501c100c04400b010108180d261a118013040895580c0e44114503411710040c040254410640e00041c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 551819811 1250 551818561 551818573
    0x607021207051c0503041a040512072a06030b150306010e010504030807080a1b0302071401170c0c0d090807180f1d1c05030609060a0b0406020102190e010e12 69
    0x2420400e8410599849007aa44c4a65034175240c100070300c00710008210150009980400d02010642c00620601c01c0500380d00c0c401d64449503440c14001c030740d21446042a0b1000c1d183d6104215240d004025404c4a046480c14070100d00c898040003104004585440e01000301400032400552051589482e14401810103500d0540c490700ca001c101d8112510403160302e00300048080b200340e488880304900320408120074a41381c149a4000c1e480344000d00440c0b035000f20100041d522a0303c158405280a4084415008070b82082003948880e50701a1011a07010f00c00c0244034889544940801e00488100300050850941003450304441840d25010556550392504001c0c00450711034840c050030400169a0205100034071501c16040c80207002d41aa082c040110583c020103401c0030844c0d500c0b40c003c5899108030b039548800100c1001f2035400481c0c0c10200440c0125855405500a205484d01080d8001300002804004c640c0200c2c6010400c2c00200c02801c2c868890500304494040340500e0404d0b200 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 551821061 1250 551819811 551819833
    0x30507060207080c0f0a0c0b07031e050f0406080a200a08060d0602160b0c210405120f0714010606090909050109050d0f080906090a0f0c08030304060b040b03060702120705 75
    0x450030074000c24040050700624a20340820001f0b14900e0010885a4400703030130001d240d10090052042e0342442002115000001c2901601ca03c0449039500c80d92201640c40b55101c8000400c40d2404617800058070b8600700c41c1c012403032103036040d01c0c1c00003c61400d100d01d030000d000341c02c1301d601002a00d03640c0c100d025845502c002408034000340400c00c401c1d9004d9013545160f4286108082000781141c80418420880c9884040306c240c00300c828103043c1c00402c0d00740e844618006290004844400064070317800b1500d070a820b244440100700d0140240c0030780d42d81e400e090480034202e5019203e8013000c1040a00108440c0007150400303207245000307000001d0300d0141600c07142d0070950040c0c25500040c0007400700682c8a904590f41c8c941180c80d4500034800c138604148a130344d464880c082d016040d4641c1d940541c00f04200801c5020107013240c0c1058a80b01c2c2800e00d0040c000e040101c880a10480c203000d028040b03400c00040c400c1c480c844640c010310030500036075a8411181d1000506845601030160000 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 551822311 1250 551821061 551821063
    0x24061b080d0c120c0f030c020a0203070303020c130209091303050702031507033b0a08041e0506030f04020f04090b0103050c03071e090c1b1a070201020403030507060207080c 76
    0x84503041da1820003085038001d41c2401040040c03003980e42d40400d0701e800e159100c0d003580043c00810854190900249030154550140e1078142c031040004d601d4490180040101940810b680e40e60351026a83d8448101c8480050000d900a01c03c1103508a440e20000883ca5480c503600c00100c40d00904115140111383c2c5c01081c200080e18991540b001c486606001c0f0055040c452041003550625007041650b01d2040403002c244c061030a038080e0b481803604c00a1494032f0500c10321001c1c641c00f2042540e01c507139038030800008243c402c40102c010020300b20000f856041c40300480c0c1c0b04d40c030b05c1b030f2003008981e076030364200080107a040005039003141d40c5180344000074000102c0c1314003030341c024002001c400184000f00f47c64882c040c4c10001c42440d40080c03140d0401425000fa609845c0d10020110b8610034070b5004070f07100700002903641c2c405400b02c20500240600d040c06806020b501c20b40094035680c4158080e030a0384280c1c8001400170b28208060404120181d01801c001d6114001403454010340200607 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 551823561 1250 551822311 551822317
    0x2011b02030a0e0a09020703080f130c121415010503071d19020c070b071104021207030f0f0624180b0f0c070b0c06060901060f0c3324061b08 62
    0xc40101c0c001105010090ad00f540c455a4442a001d40f4006a0390a6a44040c03000c002446a40300c0c54950121550800401d0001d181400903000110b07011280030041904030b064080c82014024001c0290120f6440780f080031082460260700040308440c1c88103c2e900040c40c089803880e029142c0d080c000301800d10010320100700202842d5030103e844003020305200323006048845199115610410006006d40b9100851b04d41c400c11508000605124240c80000940150180c0e01ca40c17524094000c58100384800c20491012000c016103401107400e158260303000032072141d02e803450003400d0b0f00c2080881065402004099a00d42900c2d0074003000442a46c5070108682081d17405510210300040c1c204810480c0310740c4014201c480d04495454042e028111034010300a0030100065198844140f15a40d1400342515080c81011800c1820b48440840881011114400400e042a1038001c1c01002e03e100e22028160403405205054036110082e40c4140280041c6c0e2101c044022202c00804c0300540a = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 551824811 1250 551823561 551823563
    0x10c0c0801060b0c1b0d0b0a0609110a030f0902220e030f0c0d0e220b0d0b06030705090417031009020d0204060909200a0215130302011b02030a0e0a090207 68
    0x40c0d19446003490035030911703001c5202810110054a03030800556100c241000c80207400c05240010b0f92603da0303610001d403005401c41440c003800c12501411035038819000300303419092070394204410030326422910181c42040c00060b51149401d000b0303118021140c40700d415055140c0800181d5600c14107186811034101082c500d541f040c1c0464030840c5075000b8400c120300c090311460400e4504940d0030005c0c030303070001c01c0300c50b5280342428501100c0c007041d150f40541b96017500148656110701941c50203000001c0c0c121780003070290080c800006038502340509020301503a4000503c201c00c215800ca21030080d00018488a00c00c601c2c00400101075050744010407145160090240c1c0d00d90400d0b00c054040d9010380c0c00b141b01d841c60503070358614151031a00307136040b0419183e404607512038255408914140d0b4000300300342100c2400050191003410100f404440070f100c0d0b0024045200817000d90000e41028503842c5000d84c000700305094800d44220f03410fa0603480000e10b0011104c0c1c50713980a008a030882c1c08 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 551826061 1250 551824811 551824829
    0x80a0221071b08190302041d0103020a050a0501020a11030114100e070f0206070e030705030d080a0608030c1b04061205010c030b190504110d141e06010806010c0c080106 74
    0x3051145050b4408651070405840312407414554000c1e03035804079248682c1402600880e030303014071901000e03c0790301150000c000c0c0910191060007907442842020f242840101d1086034808400036090902c0700c07450048410503005805c48405540300c0c4c421b40050140700c144c0c50755032031000e03a00d0401d00c4220140150102c601d01c0c0200c42c103201d002a031600016003154284101c00d02d841c4001940060110f034080b22a00c1c01d130700a07a0500002c20f01e0403035a40c01407035050051850b0b2120569100c50040d00c03d00d4008001d1000c10307540d04a240d124407508070741e80e0654100030803c801da481c2c0007041010707058024100044095950042061402e901c00301240e0320394407140740308001e1b035040c0a01c1c0c1035600100c400742a16505000e08030020485803080602558807050041018a10303881600c501e212896014406900d0030381d00e808102a08803a442c41d0608500741c1c8642e4140c884060368402c01c01a150045c26440300401514550f1400d17400702c51450b401c030000300d01c3c03110a002c0c00700100480b50f = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 551827311 1250 551826061 551826127
    0x30a1808060f040302060a1505010507050f031902010b04020a0504060c0507051f08070810060f11030406030606080912030f040212010e0706020106061e0305060d120c020f011d01080a02 81
    0x720b0001d05260010700250039640c02d10506420058017030640230103d5109091082e0f4586107454030b1414078a00310305180240c00007082030703041d2041c202d4508000c00903640c020010b0b50031100403c4206d000311140350000070403d100030301c1440d000d100c401c9001402501100c26203a521000203101d0380b20160080e80d8405240c5d20102c142d031b0081d120582021b03030b82c1880070351490b01130031910341004984514400c004070f0031840306540340120110461003242c001941e54960329034a016000c2e01c15842541e0000b07182200040f585180401d203000c4010304040250b05d0f580300d0615102d04610b02502c2030340d1040d404010740d40120024420b10301d88038149000703050594a091000307400c41e05654030001c01e10030b444048000d8000b0522036400b03885442d080010702c90f190309004c5005508441d800502803e6983c900300c2c0400e030050000e00c0c14602c2180c00d00d0401003910011200781d240070340c18001d90601c50314001e001e036000b40c20f4142c3c00305514138010f091511042d0b03a41c106c403099184603940c0220030 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 551828561 1250 551827311 551827313
    0x120201301b08061908011d151315061d0f010b0403050c0409211d0d0f0b09100f060906054009060f1d030a1808060f04 52
    0x2030144a0754184255184000d01110100c0941441001010390744101c2141070301820041059404001a0480c90001c0220b0340444001c041a207070f1138003810f07141e4030400d40d0505200943c945220310034a00c0e1012605011690344c0c80d4451003240303c031b490401c10b0711250b0100d41c0c100c0d801c4882400002000c0103002604002c40c3e00500b03102c041c2c00c0702c268500308110910200e81e0000304441030010903100060f20b40313003d04001c50007c02d0001d903410320554010445c808507510003019500182c0300c04015129248001c04c002204e00d203104000c0c070161034011448080b80407522039580c08142d00040e41ca0700d50303560364a40c00701c440904007110540c3e03603814148410f0f0b95920885000d0726042d01c0e10040382c001c101c0540605d03038504e000c40180344403542d1260500c540d00f100e801100c040449090100414a140c040e002c0e20064a80120861600c0014010440c03030200f1500e0350041d04025500d0a07280800407101c4500d0a00711499000c1d055800060380c11080020350311401244440710840c0c149 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 551829811 1250 551828561 551828657
    0xc0c020117090a081614060a05010f03120f17071701051c02062803141e15030c060d020316140412020112050103050c120f0601120201 59
    0x400e50707003000ca8504820040d03142c0000821410140c0c001c20b02540790000c59143d8070302140d86442c01401c610449000b51012000020501d0080801020521043c5e803504203504480d0072500c809007002001100d10700e10140070707880300340c00810b5074070300007044050f0050720400c41e20003600d149001406900440704044084a80580540400c0741c01682c6690b07002d184100200048030301078071031040000e00020801089070300028004581e0380b01004954560300c0600201520b407080c00c103400c00f00d80011347d04400041d180d058800e80b03c502000c070751034282007101003a40020705207030144240c091800322681e0365800340c40c154945480142e41c9140c82c08020b0b01d02c07030602c1103200600152010041d0f20f17100c1e010585096507050704881c8421111400101d4010a001461042291514001000780000455000c0e0b03224810b0b941c6081002c0a00b80c025519503501c480303040c0c0c0c1d030804801031042075032024003c18214014544840807160501c0100b080c103218843d0101c4441074484050082d1030 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 551831061 1250 551829811 551829827
    0x170903010e031c0b0a0918300503070c03053007020705101d0609060711010305130f060e030c070801051023042706090b0c040f140102100c0c0201 64
    0x43c1001400013040c004040b90856420b8050f11a445403284013103460303c1c888007402191160810301d12520601c2c900030002d0346034158034158145030351868107498003a01038012030740200625941c85000c038003192002c60322030700031403a50110120001c103c082a8400032844075080c0b074a00003000c026080c10140603207400c2c201c1d03014600031002803400401c8250009003825000707140480c1001c0d030000c0d01300041c0240c49441c40560f442040400d080c0309000380002c6d043c2d00340c2400c0c0c03400c01103519003222500741350340f102c00c00901d42501c15105600051064111460502040040307078100950a0b024070308045064008282d00d82d035a20070852000700202a9500509001420314a0070f4030314010200e13091548a10980181d450b1a210b00c0b001c48200080007100071030b00200c0a042d241071616a0183c0310981c001d881410300b000114502c030458408440c100c4503540c007107030045031529203949841240464800c0c1540105445a03c034034540703002d0102a2502c50343d4410401c81e040c400540500c03 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 551832311 1250 551831061 551831107
    0x11118040e0708070b0d110403050c011107141207030807033f150f0b040501080c0f090d050c0406060807020d02160504150506071101110a050a170903010e03 69
    0x2e44403000800000c01c2c007050100603506800002c540d01c1c605110700748007404481c80002609403001500105001c0080740401e12103601741e98180e6468078413110941d450a43e0300030482c214088502d03d401c00d1400d41000003890700e0040079191880c1d66070319651350340d80108a095011602128801f58048524019502c0705207100c0b1000e400540d6600540440d140c10018002c0d50a98900343c0111741c4141e4030003e03000707106900e80c21201c50b448204006090b0081e208171800b14100f07401084d0010311400030750f004c07408000700040c14034400c54200f000103d600b081c01d0340c00740284095180951501d003e5100501103580340c4107810308140400919001414110500315000301150901c902e280d01c5080b000c640003150040b500400201c420000e84249900080d44904001100c00410415882041203454241c03511100c1101003640305840f0409004001c1c481d0300f0336a408400101c50000941c4074001080c2428103000a50011908480006015041940c4045420200b802c03450b04116065 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 551833561 1250 551832311 551832313
    0xf0c051804090f0f05070f14010c050a140f0d02010203010b0a0e1c050d08240f010504090f060e06010c050a06020a0908010507270608040210110303070e0117070206040b09011118040e 80
    0x62604010401c0c4030000f401c00c504021a00c11000cac1030017803c010020005030422401e011a98209503001c0d0b444401c00c0181d40c0c00d00600c82415001401032003030740d04a81000110503d4561030b0700f0112410303255000703000d60000c0d014804100300a00d11400c445482e101d14000e089401e0b10038409004408024076403000c1a112036081c1858070301440f0381d06d802e00c0c010350301134070149443c5005030340c1030180760801d03540246014080341d0b40f014075030405011580406c0c1814165154803004681d1000c08400103040c0e60b000481020025585500401d440103040c03520141720ba4407800c543d401e685054690f41e00180700407140a815604051400401e03e100e00074212496150503409001c101340204042c2c480c194080c0380541ca540038603881294038082400b601c1c1d59241680d40079141d0741861000500280c104e0380021098030402090601076000f58006100d00d0340c0d80da45d500d072012070050500007295200d01c4204071003500400680360056021010b080d4007420709080c04100d44c04103080d61a9 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 551834811 1250 551833561 551833589
    0x120301050d14031e090a0503030901020a080f131202130b03070e040501091b060f03091e0302010b092d010e010308070602220602010f0c051804090f0f0507 68
    0x841d03074a0042429041d54429007000301080c00211250031070054001000041c500c141c01900d180ba41c0c01c0040030500c5044a5102650340c82d10b090541c0d82c0648151103001da40311890101c040340d05075015000400d00440818504040c0117278507140c1c800d0950100c048680f50b41c4a800c21407400c007060f540d89000b0801c0c1006900511000a683c03480644126461140300101140c1445003c0d00280f40c410b8000404100e400400b5403840b0035820785121385000910707481c1d10500744d02d2090160082c0c050b04500320081d07000c500ba240c2d080c92003041c501142503650740c0b080b101d843d03158400e135107200c0d00c100018502c0c403006600e00c103da210441f0340074120b9525030000500c64a10035503544d5054a0304030304120b4540400d4540007009104800502080c9540040005141c80c0601c21000603030321154000e0082d110422100400c1e604154078401c0880d074140000461800741050003090300500400109190b001d5449000c04088441410340b46401503036181014800104074010040c4210801c03411 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 551836061 1250 551834811 551834819
    0xa020a0905010914100623030c030403120b03032a010c08090c040908030a1d03030112120e1e180c19021906020708040503031207030b01090308120a0e0a030c0203120301 74
    0x81005c042d0b01421091010450380491a00150700109aa03101010380d0503549044c00340304003040380c00848086000503a96a11007200392058010b8001508001e8001d41c01c0404281d00407401c0301e03880c8454020b4060200c0e444078501c909008000c24410300fa11600700d28101440c02c60304000840c00d020b1302a60402d4041c10000741c0103070889500c81ea034004d00140340e011019510090142c20002c0507000e10010001080d91b0b01c0180d100c01410b0310605000c60b245460803000e64041c4901d0300c91360b81c081283c04501144140001440c0b0300710304000c002c40004c0c4c1103841100460350f415504400405400b245044610036089400e50304216240010070011003c0c224010300c0c50003822000745501c3d000700362001044112010f49018100c02002d03a600c03003448844000104000301c40e098002400e2442086980d40501025415660403000092601251007440100282c020784803410b040d170b4994501c64004414000761030310368400e540305900c125150040526105546682328110001000100 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 551837311 1250 551836061 551836081
    0xd06050a181709010504050d0b060102060a090f1101050d0c0c14070b0a0e0604050d30050d020928060206240409050a0804140316030201140c0a020a0905010914 70
    0x1809206080d0b00300b59070710403240c0102d40600503a8400d83d0401c94a40da18010032280d4408503200f0304080e800c9032610b40e1024110004e45140d884040c1c0f80d9601c9280c10f0b4041082e00c001001382c0034041c1040740c80c0000105c1100201c8446d110000c00007101d6195040412140442d2080141c40c2e1900070304250303041450400491090341340c4401400000803d034201e5840e040305a40c02402c0082130303a100c003034407414140b10740e54501601411181c2d441c0442114525024903011252006903030345410321803081c3c00b4100030b50113400b000d41c0c8011800d6404140707082d0f65441980703c03203244090501440ca05000030f868110047e041c1c1d004542080301492187c44001c0e00359040e414200c03400315200742641003590821490940c0501070100c001804600c41919040c00e8145200a40407a4098182e01c24011005802800000d00051210080291801d14500540200c05021060f1030350911f90b5400200f400703d1652022450703a4468004108180c1c1c14031440951000140b02c0e0300310b074030b0071100d40 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 551838561 1250 551837311 551837333
    0x30809060705030f090c030307030509100c110d1103030f0a08150d290703060f17062701140a0c080720031605010f0501060203120103080d0b0d06050a18 67
    0x5003003032084031340052451070007000100b030100c80141c01e4a43c1c4139020305000701640d100100c12802003468490440d109032203020010a40b80e000102d003290341e1000f108005c211211010280c82400c0d00c1d40c842042994103200800d100814050f50541d200e42111010f012441c0040035a046800301e1295114240c4401000c80ba500d58800d0000100d0f40071000814500c0b5400444c1e01c018082d00d0080005e001c2e095408030090395907000c03006503040d5a07102c0c00e240d01d41002c1071814283d0080c10209014460040c00fa8509288688980c1102500c00741c12500b102c0082c14544810349103803040c485090198401c4841440a9207001c40e014601400040e01681c0c125a80361030a012920849403e04d0042c81030718050041003035104040801410914007809121a0840707105142000000d00940000704484a88000c3c038003903076840c0e1035920344000e0361f04440480d80300700b42c503080043c0140d61801c914850340d41c454040054a8281040b84a049400010742c1040c1e00740c0c0706100301c01280c038071296 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 551839811 1250 551838561 551838571
    0x140d1a120d052109011d0f0319020f0607020303040605010b0304020609090606250c14100302070807020d0807050d03020405063f19020f30090a03080906070503 70
    0x20a0ba90780e035080f91070300c10b01d5100f9a2854030180002041c010002c02c19084080700840d049480b52604400040070384c1c441e1000c200c1451746500800558060100070441c0502e040c020f401564500c0007042000760810008171a0ba1005030030000400040000d5031040c06c0c0588804a01f07942145000d0740400e20358840c030b1030315078810b201e55400240700d9610305017140c136000401d4034590107801b008400054080c083c26002c540001310114082040040c0d42009070812070010a10700c2d40c0e0394904815402980246c0c011707503405e1020008840561101000c205500b071007545000c6e560402d9090040c104152a000c040c1050b0042004006c680c2d107060503103010103881c41070740c54070312200c8104811510304e01070381c403400040c1342070300d00410341560020903c0707a00c0200b0b103800e40b03500300d2410504034410b24060040501c42032080615080c10303801071001000c0d1452071012140e020f0320114690f000d045034000c00135444448198201640034009075005070094004240504000401404600005103 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 551841061 1250 551839811 551839817
    0xf0609160302040203060d1b0e0c120103021c05161d01060e06160203010507051c0b0312030901021303080c0106090216140709020f091e030616140d1a120d 68
    0x201d2029560740f0040041140c1c0600c1131a0326410030003102c0d2910181e427284500d0b070100b07003000841301414402158420b8600c0d1051108580c02d5a003004201e00b56151112418103070b0080c0100094010008a940c04100c41003683d10b5a24242c003181c05040ba05146070a0300300c20000401110781c0040c1e20880c3d2500840304140c48440c689000200110a500080d41c99030070402804200c603008401000000e100e008030b0883c01c0d0151b213001040e00e018802040d0190301407005411400c1d064005150800081000540741641e0b401025806004540043c0c3c0c001e000020440c9a1990074803801000300125217040d07007004126803048041210584000d02001000306041d5203200060004030080d00243c3d01c1152142054103d074221600405000c90144a0328025225092050070f5965103203180140208500e46ea90050014a09054000c41082c44203240601d404001044040c0c150440014800100c1e44c10464441488802e1034000318001d002449544000c0c00001c01c2d4100c40c403c07181 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 551842311 1250 551841061 551841067
    0x30e10020d27151a0301050a0203010f1d040b1005030d0f08070201060e2205070b130509090a063c0c080417090604030c090203090105010e1303030e0c0a080f06091603020402 76
    0x2130103800c840d60500d02519415482d003410040c00c0049540510b05941f400d1030300c0000ea64a601d05c02d40f500c2c003047c1e81201084009070001d03001a0103207000343d510a43d07490941c83c2140d03413400441e2910981d0481000450301208100c1058ae0341b10800c540c0c0408a44024000d0750301d081c942030000f01014240d41c000c41e808480b0229100c2400d801c0c1c0c0d0300554400708845d803061740d41c202c41010780c1040f44041c44400c0400000200e0b803804104d1036028040c880060040700c6180e0382c40310006d1050700c942e18010007110310061100c0080303000f104800d140b0511761000392103032040c1c003501725014a01c2c0c40d010b10994900303200104850720225828803040ca1805941c582c804400140d05018561006210081c02d0f0b501140560454010b1750003100a000240082c3e600d407643c2a0704000121007581d1002c0e05800702c030000c40c3c4240c000c2108d0038045070a4a28140408020501c007601c1a041411180d001107421000902c082150039407100011000d000000d0042480c10140340162001904c41c175008 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 551843561 1250 551842311 551842331
    0x2010207050f0d32130f06050a08060108040620090108010e0103031b030315090c02012306060a0309020d03050910080106080a020a05090409031119020303030403030e10020d2715 78
    0x488242c4c19505483c103049480d0148407001e4466110140200398880c0d04200c40011741501480a039540b070402500c0d0303840c2d644c1d510030044804001c001d10a6030b403a915201024904d080342c052542d80385d403117030014595035803403080050240360341a404601c82001010040000c03a6000720a4264003812040c48621188941000c80c0600542c0c880307140513105031040040d150031a5480300c1d0f50b0011640007071040f010111602c80307e5060b1f44c11100400944140041d005141c204001c200700345403030500203000c0681d0f801144079040810030031030201b1000101aa0755140c06032040c804c10304a0b15000c0b0096040c420f008102d9030010342103101058021401100c214000d00540762681d0016008020294003030800800001c070840b030030b420502035a282c0d4440300500b050070f00c41c2c42d038000d001140f0f5612655400c90040040401e44240741c001d80c4014481103241d40010202010042008107190055202c5040302c0040654034140a8071081e0102000944044100191103115000000e140e0302c0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 551844811 1250 551843561 551843627
    0x801060f0c020d0c17210304020a09051302180615160510051f0b0d0c0c0516030b1003030207151803060f0b01050c06040201140f040b0408100209130c0c0c0602010207050f0d 76
    0xc5cbc000e0395485041c08200b0403080980c00e042c1c40114000c44000220345180540d401a2440a50307809401900125289030141041d000030100010000000100f40d01503841e80c0382001d06010780a845c4036216010b0002c04005c40341104283d18468081001a41c60b112030000341e44240390180012070303100e1100d606130901500d89024600d4110040c8d40c4d248d1310200a075000107649001c01c0302e4441e510004140c11400d14a41a4143c07903250300108030180c149040421660030301000b0104100c8896181c0402c16107a518102c001c3d8030500021031400c83c0c0040410944007a10710403410808148250500d1800024002d81c0007502800c140141d075900d1522014544a40349440065000003e00003843d500360701c005200700d84c207040c290399180100034400f409a101d0101010f41c050400058001203035010750252811741c115060900e41e007600340d61004c007038410542c0b1200150354040756890070301c0004d0111009551598021742402902240301801c112120b0f4000301c0e480f82c500703900104880c5 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 551846061 1250 551844811 551844829
    0x3032203020a0801090c06090f030f1b06120606081e0a0609051501030506190312030f06180506150d0b011b0501091a070801060f0c020d0c1721030402 66
    0x107005042e000b410b80d01e0705450b40c00381106080031608551440304c000b4074244911a000160b46800b4000c06d0940d16685407109070b201141c0c0c0550301024244800c2980080e01c04c0180010109134031214030071300c510b001c084110703200c51b4003050a0200300f05c10041c0d030061803c01c100111240307100d2080ca648075404020b000300401d030040702c051450142400b50000c0c1c1c0003000e41204100366003d211694495003403117140721002a20801099526000b8800522840100c50240704070346000260360401e04c2e01c9a0544030540d1080100c0040010002c0b00542d843c018664803101c03d9a144480e100344186180c01446440c0f4640425a5158005895688100c01d43c0c00700040000b00304d0038112460620703d008081c0c02c0c404458000d4a0002d0804030a03000a030705200e544c0680f142c82da141c2c42d0803015200030b882e1300e84003400c100c4222814001661280046415680a08000003903242040c0d0300c034100400c0c10340054274640c41051401001a0081044c4200c0c002c11641951603454501c0403c001726 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 551847311 1250 551846061 551846063
    0xa020a02061618090e0706090513091a0408040e01060302130501030e07050d052404030f1d090f1f050913080408030f09010f0e030c013b0a08010b03032203 68
    0x400d8240009191321070394100b0030035408904c0c00c5c3c80e6100ea541000340c9240405204a0b6040708a06c01200c0c0e0b03844096201b90802ca001c0e140401e041603a40d500c40580b0901100d0071a14040301140901c9481d214021441c05072445003011860040c5000c241050103c9504c00c1904141d26916100000181404030700001d00d80549004089070b2075160580d161001c4aa010303a1031a006c22052812a00c9051014019505919014102c0c103440b01c0c200d03102e400c400c1d00f090b240410204c1e4104203407140c4038001d01c42c095144203601ea80c1451190203000e11a0000202031003c100d4000740050340e2140071858000102070303c1c85402510a2900541c1801554010045400003060b6040486007000007031140c01001d070b88106031107035030000c00e5401c1d030305044c2c059425500030038a1500950227000144404441001300360a1420701c8540f00180700103268125088202d142c01c6207042d400e04000c440c0161011000074001d015461010030307907c2c0600030241000d040c81d803044180d035188542c42c0b18095 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 551848561 1250 551847311 551847347
    0x90302101a03060a0207020109090905030f03040b0a14190b030f120d060b030f0a0903021606030e240c070f06060b0301140306070e0f0423010e0a020a020616 69
    0x54a400741a41003000c0c40241040c064010071001464000040c801c80e8640c5505856003a14142008240c0005200b100000c860034070040010b581030340c07078260285100e103100e05100c022900d4502c6400e01503070030321940150b10f9440c100034450004884d01d050b00880c1842c03100050700c0444200084e00e00700c9a00145e600c2e5000f0701d01c4401010540f10300070691000f01c1e98061013030990720380562800b844121180c03580031a11401198000071540c000d0f20401c1c1c040c2c41202d41c0b0090060800600304a1035000402107642c031020030000e00410300000301e81140b41c0079003000c02c03003007400a41c0081c2c40080ca00c800d00395000804804000c2900817286a580d08104204002903c484000718154028048c3e00c6a0041d16012203185150004840388100025030700c01c41f00a15030b0b82402107800040d40d06c3c0d60f20030345a00300f40e98031840820501c00d082a1490107404154585092181d11160290545818600412081c603a040d00018075903088001300340740c140d540000c1c010844000d0034010b549106 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 551849811 1250 551848561 551848571
    0x1030e120a0203040806090c030d051812011a0102010e06071107090c09091d07030204110403020423090601030f020f01050705030a0c050706020f0a060e120406030c0e0f1309030210 79
    0x2169000026205403050310080351203a882d010f507c65600c1c40403030140d0358941e00480c10340344507622860180150b01c0f071841d1404060500000003966105588060340150ba64940d106d0a40c04200343c082e00c1e224400780001c22024001800080d04c80400400c080706110840320007079546203042005900038021048100042442002d0051100d9030f070344075400d001130501440003900c0c1c2009070501003c1c64a600100702c0b051842e4240b0004d440700c1681c1114007031003404000050384803401140402080070200f182c840041c004100038002c030151031030300c07035074820401800020a00000c1140c00781d012540603114084a60040310340f4032901c40014807070b00002c103034040d03003e030045044040c0c1d62240c800d81d4400754682200300d960340090203200d0390a901403c24503010072540c4d40080024030219090f980284610182d0b0941caa100381d100c400060b035104c01c464500c503806030154100130000ca8070f101c285c2c0805800035004180404801c2120343e40c0e828030004041c0200104507082001c0901400 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 551851061 1250 551849811 551849827
    0x4080f12010302010e180f0601050409180b10121e021036060302030903070f0c06121109100c0b09030901030f02090d150902030604061b0c05060601030e12 68
    0x2040c140a10049000c2490210081c40e981317001d6440380368640511800000942d6034185422415a000d41300e50305109041101140c0201c180c00303202c40c0348046800703c0760180c09504d448104164000c0101544180400c800d1050368442180201d0003500100318030301c0e0301074404500540c60000303d0000e600c108041e5200c6c0d62039400124440d00162041a002c0d454480c0384a111000094100c0614102e11a284203001c014081d902842d002800c06044a0910225aa40c4103d04400c1032094a20a00c800d0301080450791001c41c480c071001075448184031200181010805600500c26042e110b03014101d42e00c03c1070780c45209242d1007a604002c00d00780600f0040c61642d2280e011036034242c0004d0030040d1007041d2070b0030350080b12940d800150290b1034554540d1500c00401000300e1182e811141c4400074040503a030700b0010359000c0c034021180040c6a54001582d14070200c98042908280721641c298000410000b103203080c0c0c000001e00b808140882d0604400b4103000300d41c3c80f144451000424850 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 551852311 1250 551851061 551851087
    0x5030d0f141c0b03010c050301230406060e090907030309060f03140a05010801150f0303080405150903041d04020f040b030111070b06030601120b06060f0405030604060c0305130b040b04080f 83
    0x4a05040000400c0040440c62004d040c01e03a500341c01188081001000104220605e0381840d402202490046402d1704c10aa0000383c103480803584800c0024010128803c82c46c40c18018807134101c01140000c010091450380c02030900e4880d4850003081c05401206807105a020750070084001800200500e0709180c820000c86c001c123000c0c01400700c17640ca81088500440c0702c0750510400d450002000342c0d880c07451075504451909004004031407902902950f505040840e400007401914030034051a00c85c0c5c1824061221035480c1124101c00000500502c0090b1b180d02c105041565001e55010074800d1084020a01401803400c0300160341e000011000c040c0b10448904600880017141910301990361602d00c822010091031001d419a1600f0000c9207651518030010000d46511079401401c1030364403800241000c45c11a4151042d989071100200410b40c180708440d1b001048500d5090001c10a4581e03600060707004100411082250000c5014401d550080d2030103a08950242f07030781c504215540e2 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 551853561 1250 551852311 551852347
    0x3082206150810150b0d020c0607080105030c0904120e0301180c030b0a090506010b0d090606060203070b0c03090a170f03040c03050106050609060703050313140d090b0405030d0f14 79
    0x5501e5015030411000f0754241401003402a98080480102032030409061944a034419421307441644c1d0308001c8101e590900f440038520660703668450348515072400c01810b0424a00b08081032103405107608010020348114851140107413549002d0035151b8144000c20700410300c005040e2079160f4550700100800410003088400e50744251100c0405854400e00b41003500c2900340014840c1d0008801400000306031400780000c4003d026000c201c03104107484400440702c4d95000100140c00025595041c4402440020f4010240b41010f610f1481d0400c9580e4840070380341c0c4028034185640f0580c0003d080c0100664903070098149007199642064500791041014a20040b55154281a00080d0030b141243c20780349189000380641d850b240303044c0c0c1c0486480d44010b080c1004407034400c4104000c94005450441d0015075000200001803c2500c00742403c10564440a018a4108414085510041200541c00b085070808480684002c44280c442000040c42c545c03401c00c0201e50700c46c02c01106580 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 551854811 1250 551853561 551853569
    0x1116090c110a030e270103030e1009150e0a09020408030406020f06090a0f1506090f0b0d08040501050f1b030915070c0311010e031005040b01050a030308220615 70
    0x14040c1d0440c202800720380320031035498090080340f41c04040c3d589908000c03001883c0252020860401c40324030100f1402c0c20720b800c1c0c00a500080003a4503084050800c01b844104001150810b109582c0c80c001c03c11139402c0540c0e4141c82001072445044140d238468071805405001c180d038080d9191515655440d640380c10a129450061041181c1c0764528040441c41074010004540501480320450f11000f0180d40030b05d0742220400c58002c41d03050b0b0100d061007407034090141c0350070224285404600034000c3c3da030307100042880381e14902050000156083d00315401c0750401c0c00c1168883e0008203d00f0b80d14040c1c258410505884a41140c01c00740c00403000b01000c040490314003103d15104580500d2a00032200b0080041d240d070741c804e001207001c00c2e600c0010340d107052419a08051515020a0a1180e55a00034071407585510902040010002209014110655000d14031926548000300124000350600d004c9140003000d150680001900d5040c0342d0707030001e0090104d40524840c1c0c066150712442 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 551856061 1250 551854811 551854817
    0x10603051b01230a0903051b010908030906030109110408060408030106180501120902030f0d05070b06090f0c0a0c021f02010501150f18030c0e2d071116090c 69
    0x196a54142d0b00909a10006103448020311642c2031a06a003900250711040100052042d5401c00100103601003020340d281c501c102192000074100c85d000034101c6100e0303400400090300140682d1000740c44110a0304d04507580c48901003644280d41050240c80e101d65000b5803480c0c007a01c41008207001503440114100c441c1270f81c8001840b500003ea812074138000d03008550010f42d200c01c100800500c0c2d900054051400101520110b03490542801d00c0c14040c12030000210b04085000b1b01070040e00138860740e0200d416240103510b0314001542820741e201c01441281c00750404030303001108070f00c10a0701d120141d40c060b0010040d40c00c8803141c10440c00100c40a05c00545c2070100210b441d51001c1a15503180a0340d03164001248070305281610034241e0f01d560040d0040f041c810000101e80e051203050000c0c400305940b2081800e19403450000401495022501d0a2031b0303130484030040240260981c0c1c050800d28220800007055010107003040070038003416070100c0c1d0315070001c00c52000c0b80d8400625401c5a40f = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 551857311 1250 551856061 551856103
    0x11130207080c0d0f091512020a0905040b03070302090606030406060b07350f0f09330306010c02060a02012c0d1e030510031406060f09060f130e01060305 67
    0x9101242c520000015000c001440b200007007100240da52a0207032010703450306000c4007047e0580f086400726081003105400041c1600010800c0d0b09041c4610b691020059001e0040709056801003404030801801881c01000000b0000e42445690340c00003001c0c101070305a160b80d40c0610304003550651050b80c13581075050030000d01c001c240310420030030090802c411010141414060704040c2c119070040c1000c40820340c0d0820003030501c1d0741c81d078440380101076155000c0070003d008200e20030100a0b0030106115004810014407007140c0c1c211001c3c0002c1c0350304480403039488000103001c0f03015006809000000020308905048811001240b4200070012075080b903801c168504811078007840103100070448401c824214403402131180c2c1126a1141d01c540c0300424466a036030300c044c05040c1d00190302c071458111005106092604025030f00d000306c0122415005800d110001903802460015020f11a00c02aa240c90031100f040c3c100e6404080601c000b0400c40756641049521a40d50000266200307003d8 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 551858561 1250 551857311 551857333
    0x7060e0306040c0504051003021c12020d1d060d020d0515010302043803100806280c0210020d0603060507030c020307140a02040515090c0a050711130207080c 69
    0x1c001e44103a0b0018626031800d460901444000d03c0c0240280001c0c4c0038000010000d84c44d14181096407040c1200220f101503118108154468940f8070701c8421034101c2c007803400306941e1190a0398802c81000000c801c6060780340e0005000ca00c1207403082c61440b1300201c0d2041500742554000f0784154240c1406104c03042c1c19400440c00c9104601a01ca0051182c403503650100900c418194009a000040d8517017a401c4292a0407858200315410305940321165400d1001000511007960441200050110801000019103411210b480100380c0352560324041c0d0180188200980c010609129a086580718403460b031807009440c40340802c1e03034454141404104000c0c440c3c455885d01c50f8040e405107041064594612040b141610440c038102d11a030110000036131b455100311400f41c0c1d02c01e80d01e03004002170582800420b5100070224040c100701488001259904030044401140d442402c214104440c070000070703015250403014080300c41c0302281305403c0100580c0102a2986080d013240c1c241041 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 551859811 1250 551858561 551858563
    0xe031c031a01051e030411030f0a0c0e070c030f031e090b15090c0d02190e01110a02030d051c0609050403021207050c060a0c05060708060f0a031208100f030507060e03 73
    0x180100011181c8010800441340f02101e401a50700240310ba080803d102c10a000000c1c0f9010100751141901e0b0826030038042080b0742090100024155110360480c076180c182030242c101d0340b0894020b0280810019840704591090348403641c001c0003500d9000c0300c035030342415440003003c840504840c040e40e1040030070031034042030711200b211a00041c41c0307282980d103218013444903401072140f0041041d02800405841d42c800c6072418a03000700782d03a40b84890702d08040014504c03005814242c40381d4000d07915050250720040b80300030491000341800b075035038521214010248405c0d45070750b5140d5841d0070004142280980c005a0296009900301e80d0000441c2e8908040c1c2c2c4075001000f08070354400e0035100d255003005005800142024184108035130402e844031400c003002284c40d540000d504a0400c190380c41c054074484146a0181d80c80c1d0b440701d0441e603558460b44d101c000d00c1d2003070009440c0007030200a4503640035409021805403901d401d035503a2030520303500c000c140503120218a20f0700c4020f1403030034 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 551861061 1250 551859811 551859817
    0x3030305060112062912071b0b0f040605060616060b0a0b0c0a0c050303040605190905091510050901020a02041d07030507090501090e060402100e12150702010c08070e031c031a0105 79
    0x440292884983c603120030030703035091010600310401c60ba405a5400c000c100d648490307521542601040380052f24242c5011411034800820541c07040c601485202040822034444d59501d41d40090001050f458440001c1c000410759030004120050010b10a0306640004c5008510640304d081c9901142c0d8a900c10503032a030055001d10000160180a601c818109040c4255210446030401b203070b180d034440000c034601500c200c0d1a409200e204044400140c00c083e400d00c40610020f2a01c0d41c1032a211400003034440c1c6032904080e01c00d81c2ca401d00410454282448900c4070840081160703140e175560b18180b9151031852094528a0345420000210100c907030007584418100741c0040c000c160b50360b9082143c2200254103110400c560404240c03020b0321282d0aa400340702c9010f005059962010400b170094040043c6000e046904262550002d2504081d036260003800504000c11035810003404280390908001403d1203010410b084032300b034260558030034100030030b40700702045074000c801c001960984 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 551862311 1250 551861061 551861077
    0x6040206070f060b151305010906090e040c170604111f051e040f050a1d1612020a110d030603120f091806240504030303050601120629 59
    0x19a080200d68005070065052522032032040710300280b584c032090080350150105401d07030380c0d10715070003c3d070040550b002c0c00200e00100024603041c00103504064005001a078184100884222588081002c000403e02903901520070b00010100441210200e40d5a4400543c4c0a07117076002c5070501c1804d1420400c1b00303510101c5615000100303032400e05804461a40c411590400455580703070005c40f030198500020f0000307024500c1d842540e00d04205c200b01880a2990004155600505801c031440203035403000740d409140624412560800d00406a07898441f0400c286e103421700c001044400d4035000309001d95000b40c41812280c031a50001c1050302282c41c0c0f400060014520907003031a2000d4881d0341c5039414483d40c2d10b8821041656281c2d815000e00c4900444440c0c542c84000c248a481100e030341c00c24840010059020f10320518520103842c901c030724040a4201034540d000100c0d26400340d450403e40300030f100c100300002035451410103e0459940c40741c2040381f134840310310044001c01c01c0a543c03040b = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 551863561 1250 551862311 551862319
    0x203040308030a240303021c02010b030a080309010c080405070b090a0b030a0906050106080609011505120a0b041b0509150412030309020f040c0e0607031e0203041d0103050c0f040209030a0f0c08060402 88
    0x250048041d03120f815102080b23045649524804650391800c0c05030250f0765204000603510703404e190602030300f0f55001800100c01c1100000800010403400100034013190400e50900d661461074001060700103403a50003041601c3c1c0000103000140c1503aa00c20300b03906010b10003c100756622114102e5146800781c4449500045050040c010b12a240c002c0c06201c0100381880e515145c1090b6a029984000300e440700110750b40c41058084505080c010071003100d48640c00c15100f004d50080180c0303d401b0f1400001e02504c00c454107004515442c60864003d0003042000010700c2c0302500e001005044009000c0b8044c0703001410210090803c2d026252403c101900c8064842c613820b0180155500f140206404102502281a20b944084042e041c100c81d060342c0070b10358036030030000c3c0c0c0800351100541d0128040b280304c0040001c28408190307594450000c482071003101f031003080040c01078054144015494010100c1a4040020318004210700f50310800503020910795400c2d82c1d80e01d0b80e0003164040d400c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 551864811 1250 551863561 551863573
    0x70818060f19030b0d050c2b14070b0c010209130203010b090d150501060f0e01050a08010b0a0e0a06090906080a110105030709030f0b041b061b02010203040308030a24030302 76
    0x5040c0c81800002d441071183e150000d00e40d600d000c00a8249405010156503039000442070044030f0800e0307140641d1401b4154180300c070f441000f510710302c1035a01c1030b640500541044c5451401601091000b41c0080c55807400782c41e190307901d00902340c1c000d41c007000700305100b08104400c2d401740e000c55000b541d049170340c803c15160811682600348400c08040c402c00300e5a003d98002c0000700c0c900765100d040e01800312950f502d104c40e4030792003000d0024036002d407043e81403140500c8064101680500200d042d1032041d500141c60748904801620b0700700022403459408441e00e18045052a0f0048200c0210398000d6414040a40e0710000c240d01c8808030036002d40340002c1e02c4518540d40d4012002180c01c81454030b00061103c0e966110f122100640507403c48420001109100c18801c10058041c10781588087c210b88103450080d001e4420b0509803805100303100c0304d150200039a13009000307480c0110740007101c0e2645d9103000152039009004d100c107041005440c2c6200844a045440c841c901525495001014 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 551866061 1250 551864811 551864827
    0x5041d04050d0c03020a0206030901090515040b0a0e0307170d0c1b0b19110405090a0c09030201082815081b01050d020c0a0506090c03151b040b070818060f 68
    0x862400543c01078056200d07035000c6a00680b61032000398841c040e18400002d0100a91403c01e04018242e000c001a1000002c1400085207032007611607045626a400024130344590031001d400c0d0700509001070544856085281a0115044010450090700710030400c40e00050003000e032206503009a440001044c8419184009400b503031200b50800d81c90041c0310038884010312000140d90700154403100c41100030504100c02e080445400f600b007882d900040c07100f25848400101014403074800a03041004120118508117500400d40c22804420120f80d840707840303c0c1e071060001d81094480a0351910800000081a800c01b10300da00061500d03c403c501c1c246103ca0045407903130040c1072190103859082000d01003804040001a231018452006800d007860055401424440d0901031b141c0240c2165a04e21515a0301c03000303032030380b000c0d4103081c5903149020b825403240d41e402141c001400c00d00e800104201806036040c06000c4d0b81c00c03c0300c00e840d01258004184a102d00030000042d1a03c002800030381 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 551867311 1250 551866061 551866067
    0x618050a1d0303241201020a1209020607020907030f09060e07050402040b04230a090b09010503030f071403070f0506040b010602160302061e0a03021b06011d090f070605041d04050d 79
    0x4840704503007440306601038404c4e0300180c0d00f99400501d0207016903000510140b4250447c048a44524503540204401031aa4021412510400a000388202642d4000801d2140654003807030a00c050214200102c0d22549020801444601c8034000c0603c1465070000303d0b0700e49402210251a0110000d5092503c0d01d641e15150104000001010055001c48880071741c45400c00d0b000100b00404004c200d120180051010f4200181c00031030203a0400c21596075581408000c0ba40843c0d4010704000c032440040c901a070642c02812f8009154034141071858050180020315140240e018042c0c207600d81c0d0f695001a60754125020414014001141c0d080000d454400083d26040401940080d038030709454044112581c0101c074007a002c258041040d140300f600304044000d10b0f4030090020a00c5504007941e0b0000d040000d4001c0205000010004019240030300134110194110340031030301e946446130170192036608180202d01c440070036111040ba0180d00d8803011405a904107029060340c0c01005021 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 551868561 1250 551867311 551867341
    0x9030c120c100c0206360a18060905011512140f090a050708031b06040b040f0c030507260604020120030c0f0f0c0a06050d09060618050a1d0303 63
    0x89090201403001603002d6100c8800506c41110695080205040d4802c00003a041444410141804120214004940d1036014046081e10054844940b01e0301020b01280054075140c0c002c540350500b00300002402c0c11107100c0441010003291206400e901d03c1041d41c1c42103882002400301880f01410224207800c981e50407964002004130265103844040c1d4407180c2c035254290340404407582c4000b5801034135004040200c0c0c1440e4a84001d40801e05080c0c9810490303a8018001510903000424860308100c0d161807000300440d8058144c1740a1941c42c0625602c500300304c2d50f0054040c83c03103d0a503400100c0803078032610443e816140c0c56540d50406803c0804606040c040c0381d55031204000302c1070044000c0203440251100b1030018903c0001440f48941020180d4128070300891030341b0f00c00d000980d04103042d60070f0100001c83c0003441c8426410150b0180c0040e0340810f0780c0c2c410100408085201079000305121301204441446222281c19405460045440701d00c8050381080c00401c1c5590400900 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 551869811 1250 551868561 551868589
    0xf090d08060609180421080a0507020c1005030106030605100518120114041b2402031201061205060603011a03100f0b04090b010f0c060e010f060b09030c120c 69
    0x2e82e504220440c00444c0705001041e2482c0e0b003200310f903400c020410181d1082914003009001c0f890600d160b1080c400703401c80d03101418446540c2e03240d0f800500300318400c1000c075032007034070041c80250320b10400d140291140d0f01c02c0c00f030350300000d0601601180c641404981c0010340010b680d20304d07280400d82844031496100c90252203512044031210503c000d682400b400c2443d015400c4411210f080514001004901002e03070302ca1880c00080003009032100c00074284200400c0d00107021080301410b40c0480c10740c404c08074007400802c501000450190750055040300841c90880c010842ca0f00d54008000f80c6000c24030820342103030600f5103185080d250781340103103070010800c191901c900da482e109038070880171164002d06200e2601140401c1129407038024030122090a007484085c4d8268014014071070000b0f514007428a503203507088480025403d51080d07102c040d00b85410052242c6544081c070580e4403035050700380f2a01c0780380315208581c07401c04200c84150400400800003101c030030003806429252605 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 551871061 1250 551869811 551869819
    0x503060a05031b090a1515030f0f0507030c0315060311040801050a090c0909020a0e090f0a140d0203130e0c1909090507050327070308120105090f090d0806 68
    0x800210364404001445850310049112014014400b007403088880004200c800890706100141c0c21b41d0812103030420030340c1c4440d18140040307214088141d02415500400d000183c1c0b400513544005245035006d203002d40e030555424030440b107071124121305442c036800c0032404810300104104540c41c040d5101503507162000003e00c1c00e05548802d00c90031500c0c1100c030842c100f900d039100c90040094a45568024119030101000311071b0180d00030402440d040c0c0203590341800c00c9008174100040400c404800b00f200304084888000c194540460b4400203421a900c151007520881c044050000c030a42d2010068501040c000502e00b0b41e914003000c0e0090101c8a961704101316904441154584000400c0c1d0540c031940803442c0713032600b210210b1b80c00400003c02c1040900038005001030401440a0058400c0c04501702c25000d1030311581071001c598030007084801e00081404454400c02d6203c2c2c104e5404503000050f0b0760701c650510450400440b1508140e4124006003400e05018079141030300001c002d0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 551872311 1250 551871061 551871079
    0x70b01050f0102010e0307080a0806090403021213151124061302130306051b0c0a0b252006060d12051c0e010b040c020304121109010b0a080903160201050306 69
    0x151721a82194007075001611401000501c203c1511780084a140d0000c0040d1482c01caa8546520000d4848218060200c8078150000b0780303004081046001034080d010f01800780c0350242507590080c2840401e603401d034003e800b80c9007000d16101058405400c041d900300c40e0141c0c03140d480c001000700c40c900c442424103d0399400c0c45048424140d000390a0080c2d031042d400001c050519950b07184829130400c850005012041024041e031107808076090401e194040129901e0751100303040100f1100b204521219845a05250480c03419813285c8055001e100120302c140c40b14900e5048561a0881101d0039908080c1084401d0b0010b140f100702686c0b0300d0114a07115080030f0390a80e0150700b280d0b1840303c50038040c1d00c520415030301d08807e1162400d10308040782e0030040210000720180d100c3c041c0f0305c6084000c00300c1c00c81141c20f014042003c2c40040340e000300940c0e01580c503202c00100c55000b50a25500040010000403200080001156180c41c540e080d01442ca0740790764011522039000070050b0b90008141 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 551873561 1250 551872311 551872331
    0x1022a01050d020d061217030103030905011d030303070512180d20010f0e011a09061005040503031605070e0106090e090316050102030702160b0a05071707030206040b0c070b01050f010201 82
    0x2445460090011b441c00c0480c9070301d080c2066001405c0d080c1d110302500d642000104000ba4000840004880c000c0c03c01048003003080702d541c050000c6601149416010010401c44010b501000a0248409030b1780007a031f20792034281e400c410302015013003a0022684000c01010071540555005078110f10601844c8104110b03010700d25081d540d0343d405a200e4140c0b0307904400041079080c00780d1501e201d00c1c19101c0c0180003e5000040e600000540b07000d004d0b410200300d1854940c0319104036406810043c048940e654640fa8200d40c80750001c00054440b8041c5071800f1550380146159281250400d9030380b110340c1070800b00101140c000c003810a29540c802080145094240c00300081c59680c010b0000507245c3c60070500282c01d040e44900c601c4ca80c2000001c0c14801441410103581d000c405904d0f080b502d42419103840240010007910700040d0000200368001011b0340020f84130300c030340d1244048078000c1c3c4990180c550203005a00d03004082101400060116060040060040117414400444c1994030 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 551874811 1250 551873561 551873587
    0xa0501030e0a0507140a060e0907110a0b041a0915060f210106030b1003020310050615030c0301030204060e0603060a1a1012060f0e0f06150307080601022a01050d02 72
    0x1d035000c40303054281c0400720b1a09140c1140440000e002c04d0800c00c0a83d00b2310000a55030240081070b18091007c2540c4108120b0030801c50700b08000d5000035000d05a041904000e4a9050050018411100c406c00050f008000c040b4032001900184550303030085d5103842080020481d0780c21410368220740304860b80c1c903800d0341c51000340043c00001000010354509500b001d030540034005000658141c111035007040140c50020385900b003010410b000044030f4664800154001003441800042a40c1c040140401e2411010003581281d1003180c04001c46903690300301000780d210482d0403540c107401070390000c0c80d800401c0d04034a2812092040050342c078032071840041c40100086150900154100355a2000d10f54180b003294007030030b921001050540d10b4180140300d60980144a02d983c6030030000443c105880e01400d8403003051000c8003154880ca040c0c1c200408411048420741e00500c5403108542800206580b0151081182d0002081c9410080700540d05a8400483d0801741f541c00c211502020325 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 551876061 1250 551874811 551874823
    0x12160c0603050f06040e0d110312040305220302090a0b0a05060a0c23060103030f02100207030509040c2307021809150f0f060f010516240b0a0501030e0a05 68
    0x4901c0e00e00050742d061045916442c4400140100c0c040c40c5050390781c01c64070000194030180488240ba110038040c8145810606500420b4000c08078018514140410541c0102c041d241140c1d1907007031400308121920114400d0343c013a1001035007051461700424008440c0b80c00c403565140c0c0c09010350305176035528000301d00309902c1100e0000020740400214410440b90941c640310648200720000b0401a00d10100d82c5c40c0d0b0010b10000302030007003040400e0080ca000344060f00e0302e003d19160464590080341009403190307000013420340c45181340c00700c00802c484c02115070003a281c0205200c40440c001c080000300d46688144010307a0f100d0408040d0140180541030418815800c3c0d1b809841c6580345c066648141034406054019540003503030400200e85000785503158801402c90b05c1000c0380d8555401a00c503807180c80310502520907000400420310000c00020f0340949488924084000001c80b042e5046500b03880e00c0681c0701ca550f04040080358480d8021604042070f22042c0c440c0e500ca16900d0358a001 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 551877311 1250 551876061 551876069
    0x103090f030e10050304110f010c0503071a06060313110301060f080714010c0506130f050307050607120c140703110f01060303080a14041b1a03010302040e07050312160c 74
    0x1501114150502e03081c0755110b00783c0e1000c1070074000d00f9418155194107414600c8000d2a00442241841e03040903803042a01002041e00304c010342e503a50f009070800744251011a40c03482140034200b0046031035810041d084174820401d544a05030b1119a44e91443c008900200880c0d03419901c511010949020210f400c400410112006090442ca0400302040b000351070b0003d203051008541a107000b08001182c003070f500100c0290543c2c0726040b40d2520007441c0a01e1840a4040e20022030703a10308000340054083c3c001c2c0400d40720108480e6102ca840d009031825400340f0070000e0342403540700ca46ea600c2c04001d44003540c400d060050800a908410900d403100c88041058547e4440100300149900851b600f5000050741c1d205000b0078510070b002101507200038000501511614a540210010340c0100300044c006a030700c54804004030101000040d002804264803030761500329042c801c1e0300700062500c00c540025001d4001c285076928800441d41120407030548041d4480e14240c001110a20a40060 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 551878561 1250 551877311 551877317
    0x82106010816030608030426070501080a0207051e0c04060503120a0e0d0206130608070e0604030f050109051006081203091908070204050a050a050f0c1912181203060b16020103090f03 80
    0x60b400003101311039020702380740f4070500c03d0b0450742d418010f6990010f1f4031303688603221580c0507998200b13030310b40300b490400702e08245100b5504940050248200104c0c40340c0c100201140c0501c4810340b00c004140c0c5545080150200991040008030845400703443c80301700c104802020340e041ca090300d40210708a5440340803d5422020070034424404542c001d410305800c00c0040c82c00c104181e00b454041205441140409041c0c1c00c04042c40d8401c00500b50000b58907254890140d40912480508840103811540200703c0c80d80206072071f9960b200f075440181c902c103c507000b00811502c12246049601c07000343c2c840a0fa60450301300034240140e2261700929006001e00d042c00101c1e03291955180713007110310142000c40e0383c1d109242444003010400c001c1c0d904040c01404d03010254150300000b910658210300c0351138041810100714544059003400c0c006e40c20f50080180c242c0b80100c00710110308840c030038003c41032448010f001e4401d4500b0400c141288151041c103000600392100d07151001c00b07001c0701c1011400 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 551879811 1250 551878561 551878589
    0x1c021b1c0308070f0503070207120222050a0e0c060a0e061605060711010c020a03031104080a0c1a03010608040f020a03050f01150b130512070e040821060108160306080304 75
    0x101075809802d4048013001403038590b08606107844029112407a43c81600c000714002013002d030a40d580c80909485c3c50144607011001c2c550b025249201402c000c5880700d0200d1b1911041440e4201c01082618038800018410780c900444520103498502c003e10000341c00070f03018800d000385e03200141e81c03c181c4d880c0107030002d101525200500424810703000b9030705140e030303410410302d2403c4070b0300000e610f44aa503060130007050b03410120303039460224080d40c0d00c905d145102d0034081905000b5120411003c1d076980c14506400122200f0040216100c04e220707004c000b481c3e0f8000500410740e0308411142e0381d0300c000c00000210b5a80d031102464000b03c51a00156a50742e401d03040c04400c01d081d82080103190151680b41451441e03510012018040d03c50725000720342c1103060401e00b0009000d42ea014100c104644095400c090820202640080d91704040c20044000d103a0210a00035034401d205040503501e00d640750f61a482c0c3e440ca0b0002c20030120080c1926844042030309182403024001800c13100d000402 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 551881061 1250 551879811 551879821
    0xd0c0816080d021615141b161d150607031d1801140103090206030a0c09061d060c01111207030531050a0c060203090103360f060c0504081c021b1c0308 66
    0xc140440c4e5a80c0d070501c010302303650030420401050703c5a00528480c0182d600c1c540c0c2d40300c11001e9406012405164840703800a4090100368100703d0f07200d00c00d180c003402c0940c09402001442040d08250606001c1c8110100041100504000ca41c00b502c072018034000c00c04a0781a408600d140d0000d0301c030351030643d40340c0c21f581d1101c95021a800006010a20380380310890207c0342488401c0f2104204180154400102d400c0e4410094101840d0747c140381260030794803c01c06046c807285513015035000300082d040c03d02060300501c200f0750599128000b25180b11140e200c02c00402c2d511b0329004001c4071140a00040c0901040030054070b080144040c2e0090765a4810a40006088032240045048082c844450340300400c4082c030b501101d61001d0741710394040b00d4654280044001c1540c50002c202504040c104518240e03c0400340003190403540c102c482810b111290701c07003000602d20400005034805e5846203d5282549e2410401c2e02e40508100b207000780110146145014105c816000310b4000302c1881 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 551882311 1250 551881061 551881063
    0x60706020a020c0d21051303060615020f06060d0615180e1b01080601020304181a030d0e190308030a050421020c0d0c0816080d021615141b 61
    0x484090740480d150030002d603139581c07540003a91203c030b0011510041e5500449038135000c4d000b1604920318160343d425040f6a03d1030007c02600c3d043c00740080c80d00c403400c0915400d900004241040c0d000c031760041d0505079200c40c2841038003a2001419260203880c0e00721501024090740b5018080c00031107800030032136010a21400d0646400d100480300ca0390141d071200c043e410308200701c501c00e003009103800304c603e407120700040341f40d406280c220f55844090011190701c01c2c1d04540c012102c130041440c80c141034002800c1003613124075070004100d0200705081000c041c10b10b80409807001d0f031400d500002011301d449443d000c86070b400481d958800c896a40c4280014880c00d05a40c1414184803c83c8280a00141d10300a49980f100c551841c011a00f11035070408000d0140a48001340c40e03144101d5442d500800070410a01d090362040b0207280c012b114420031414800305103042880e00d0782e00030340c401c2490981c0889a000e88002c1c24810050710702214001c01844400420300c0d81c505401c03c50540e00401c0070740d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 551883561 1250 551882311 551882323
    0x1512020325030905071205060c090f0307090615030203220c170102091201020406050a0f03330609060207050607020303090907110c0402041805090703020909010e1b010215040f02060706020a02 84
    0x20211b0a00480d52042c0090000255140e0040f072158400343c0722002c03100400e5403100400c00c0c89078140618280845c1601c039541c0114211800e01400e144d00e0803034010281d00300d1005803036000d8811640392901c91140a95818203e0140c413501848684559074201d015050030300314014110380e50001104506850310010310b02d21000018021031801c0d14008000d40103110f001a02810300c00103c5003114034a0290307100e8071024850071440b50010360b464014655048100f40c00c44100c01003a000464403910032142d040544041c1e4008154403401c00d0108003441d00407001c00c03030b4144000c01a0b000e5940701c0c680020b018000d16121410305240e80d40025003041c0d0400c43c031502440c81884100040c895030210584d240006e60740001309038851700461800d18802e60030294001c0000014000081c130150320050401020b08107882040c4401d840840840054441150050740084a201d101000c40114142c01602c514115445a40300b80e0109511742c20501c015a00c260740403611951080d018050 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 551884811 1250 551883561 551883569
    0x11120d050c0408070e0705040816091b0f0c1410060f0e0402030d050322080901020c0109080a02040c020f120d1803090b0306040e0316020109151202032503090507 71
    0x1007141000e0800354600d654041601c5144401c04082001c540704500030402c54015001d03280542d00d140c0300b00d50381480087e00b5803003200d0f112803401115044000010184100c4101142e48005500c01c0000085030307800c0f0920025191004110295002903c04000c8106290b41000c00030032603130b10f4203140d0048004260302901d11400400204070051b0f0300400e609440c000700d42802901d1303848103032251413056a8141181d038240e6a000c44c1d101482840301c0a0b1075020b009030b0845030b55460550044500b8061840b032910a50701035403443c4010b16080d0008613a00f41c1d5481180e515055041001d4544020030180d407207410000203511606040c1409610301c01200b107890385a0b07048441d0b5001b052581e442c800c01c0c0b030b840c00c003002013103060351141c221214500e44001169140d4044211b80d1060b9500854101d0100302e0341b0000240c040c56400c241c900f034010b1901e602c0c942e08211441300001c1d50000f8104110070742094121544800c250348100709100496500040712034076171919034a04032307041e04 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 551886061 1250 551884811 551884831
    0x60506090f1005100e0622050d0812040f020a0e01090c0806100f05040b0a081008010603120804020102070f090221150f0a0f151b0c09090311120d05 65
    0x2c018003900790070742907030880e4015907140c8040c00340c0e8541141c0040c44240042d60104001425035000700150490f00203003401c00d0107000d68550f0350800c20080751566140280042028450050054003061107550b10074010b0112901c0142c2a034002032002c0706a4003e0803070004618014403218005208040785003016040c0045103082400000d4200e44090000a040080c1890b541502c10300c030341d095800915140c8005610340e00c0400001c2e02d01d480c112030354107000b8080c0c00c0c001143e92050185c40c0440750080d0345011140b190340d8045a0503640108280d055200381d6100203080521254204010242d1003401a10b41d60f40305055850303d45802100c40c2c020341860240b00d000800a04030030b00c1404201c60302c0010780b9000c400320354965020350007141039035001e07000000d40e000284003031160012165100c00c5480c0802c0f401080310040060060701280c6940e000b03101000c0c0c15030100c4140b60180c28149030030320105640910300010b840d41c160307030b102c408150b0b10207000c4280581ca0300300c0c40c00310f = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 551887311 1250 551886061 551886091
    0x801050610080103080318070902090411030705161b0b0d1d07121b0b0702280b03130f06021803060c180a0801020a0c020f1f230706050609 61
    0x200009202c000c0602014110750000000720303c2e61100c80c00c40c044101588001c0c2e401595076550140c0007034201400c114011030401e2419048603e0000443c1d10484441c1c0310300b82460303500c00a1545070000040100d41c01004c0e40d00c0c040c05060940d0780807000f0121613070781e10340d15801d0b00a80c400340c40032400008007241001c04504604034020031020706550b802e2a9500402c7d0a6042c000f54900e82010a942f035015003d00c0400c0300d003c0704000b0180d440c029a074000380e0a14801e250510921410742c000faa4441c10142400244005001540c004001507046450311101d0703214000790907200c5004440705035001601c107034584007410b42c51581400c101c01a1003140b03424007070b42c0401e204500c0c2e0380d101c10102c64070746503090340c84000b240050642c0700007c640301d0f24045809007025020041c160302c1050801500b5801c0c1ca0706100c080c4101880d00c00112031462051030564100c02c0d00d000094401512040984568540c03001070104030340580c00124003810305006109502801601209103060300e9 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 551888561 1250 551887311 551887339
    0xd0e040209091801060e040b042a03060f020d051312090503030f090114040e10091a0904030302040b1303021302030402060a0806060d06060e010206060627061608030108010506 77
    0x824900f640f05210a0407001101180b4140c1d500403e902c2c2c0000250340061010b0200b0f01501240141c0301e103125196a0f00c0d91030b4010800c00001200e6500314002984055051002a64030340000c801c440407168054100341c0c1c03da8070a0152003003103403c11038110b51032200784240422600103c102c9046400c0c0088000e041202003a140e10603501020b0315602c0014104203141d00c41c003c1e54000b80b055000498440f625640c4040c001501a100b140000450680105628400d4850201642c1e0b0099080641c00950414041c507510020402c4d818181d00340700c0090500c0800c00103002400c094888010900c0c20742c4100414025194406440c13036106008010041e144d507411203206d180141819103055031076400143d2180702e0b5001d54035510341846000620b0726004204100c0d4a01d00f60207039103482d901c0c0000c0c42400e010b507449107100303560781c050f410800710006041c07820303001005020140340840c10046030604040c400c800315180200040100724405081c403411b904a0341c2114103034032042c11 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 551889811 1250 551888561 551888569
    0x17070b04120510271103030301150305070e010f180e0c120a050403141318061d061012060302030109050f0d050906120a02070b0901051602062401140c0d0e040209 71
    0x100358403103003460001d07883c1d80c050000f00001645540c000500707c80d620b40c0c4071003100c2c00110100300d6010101c0d04000c086400103000f80100b41d81c829060703680400c0c0c5105030408172503440382e86202c28040300b00e00340e0119000810700f503517034420030a108185651301101007251003080f030020941540c044c0f41100f0702c0002a404040350007034152554042d41c031141150389402c20501d280e8030400a8060080c0714000303007201d0350010411141c600302c1c00038261492030882c03c64158201e03907269000c0085095010190701581d00c03406454074010000540d241c0365400709013110300241c030590b12030303000a40301da0714154108a01c1841106501d050350801c50107a000c15a81c0c080c84050041030801400001c00c00b4001d60b042e03605081d040103071030701c8500b051b252030f40c000e0005603070916003019031210b00b280260000a02e01c0c0101d11403170f9840c0402c00f8104d07003145500c00541007203040004a000764410b40c10a02d0141c030840e02f007000541065046030602520103e201901c440c05640188010001691 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 551891061 1250 551889811 551889851
    0xf0106030b0612010e0109181104020c010e07030807060c020706090e280b151206040e070522050709060c06241d07020106030c17070b04120510 63
    0x9824007040301c1d403100c00054154007a400e03406080c0c41480c800001c16215545d030326412912006000c014645010724070301c000c2110041c000d400725688070048101800c29a00400c03210980c0400011407070001005281081860340c0b080d540c032a030120300d000622040c1d10074038061407030070300041100d2072919102030446034041c0f003100c1400041d0800116904599400386025022000d80060b1110f03182c0d40e64070040c203c3d4444640180002e0001200100340700302200c1041d00d584c01400190f58900b001c010140c800701d10000c803680240c400c00a0141c46401814100840102c156900000b40c10442d000319400144184100090080f0030804203800c0000c0001c040d4100801017080440d42a8100d110b103220795168448201ca00000501010150b1040c1c00c0420510716015050300d884c9003c9090320468080600520100e610821903c10344d6200800c1041c0f598064411166551030507a20310b8205d0341c04204070f03400503100b2508014040c0000c41d1a43d034130340e1042011540007490501c0c400 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 551892311 1250 551891061 551891069
    0x9091503120711180415060b030108031e090f15040305010e031e070b010905131506030b0606120c0a0c021905010e030d050904020c16060509120102030903070f06020c060c0301060f0203030f01 84
    0xa00034040821300304000e42018020300020000c09552b96903c0390115900d600114802e4444c074854040300a0384008003086805d6400020100b40d12000c442c3d0410aa0440741840c800e0055410840080040d01c2070140d00080360021014507160004140c500720301007165450f00c0c84d080310407c107440c0003904072400c0ca41503940502000915645408000c007000c0b04150014110030360449054080c03008a070816002e5034413032102901c0603100d15060010130300440c140d0708c003010b4000b00003076443c03900103000d03080d003100615082c0880b20094002c1543d49000e140c810b8034040c82254140000c0d43c0199545007806000d40081011810340f1030014000e006108620384284d400142c400b202140c100025580c482c00b400c4248080d13070380c1d904007624651150385118011000000e80241d82007040c4292407140454002851a05030349640e40d000c5602a0707003040361002c0d800d1060038107401041000910a1890106195a03541008400307000410005803210856008004201c1c85000010740d02d4111 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 551893561 1250 551892311 551892323
    0x6060706020d2d0b0a080706080c04030602130e0c180108070c200316030c03020603060a080307051e030a1b06020717030a0b0109060203090915031207111804 69
    0x3451450607075806040c0e102010242c200f4003081403100a0002d10b010359246525800c10003014503000c4c103000c2581034910402d6000d4124610400c5011b0040d50604c0e0f002000e03040143c90282c5070b96440c0101c1e00401d0704001c49500c030200c1401481d1000804d6a044100103003140d0600842034021109072a11416071410000001e01103107080d40240030803c481a80a240490101c8400004009840150243c0361191050017071101c10b400768070600303505503070b040451600114215000d0202c00d62000c0c143e16080018040001142c1c502070014000c62446180038000920602d408880700500020944c2210b4108100040301c40d0b0304821078041007084029584980111802d00100034011444080d105900220840941c1c804850055100700300d400402c00201d1031490044869031b01901405000da44104088070b001d1402c0782145501440801280040a400c100800c0c00c0090320b5010010701d400214841080250750011004201d10076520031141154083c8203041e12000544040c00c0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 551894811 1250 551893561 551893567
    0x1e060302010329131d01050916030b16020313030f02030601241407120f080907230f030f010227010509280e01030302060a060f140105070506010605031006080606070602 74
    0x190700068004082145481719070915444c012280716010f0242110000040d00a8040a401c1c00d640b94402c0c0d001d40760003c1c000c00c141d0751400c2c3d0a81e0300000e655207032402e5100034801c4072903640b55002d4a5024500c83c921034209044107105251500304184c2040001c41c085005c4c200c0600059143c0044000030707890149100e4540b103044030f581d8442e100300580715913041200c4c202c40c20340000440160301c00a556080ca1039660140342500d65016028000c0e05104240002e1407000e034401c840700c035051000380048501c50044000910b00042c0f420032101607500410461001c502c800c008034100c8901d14200b007012448140000c0c0944030700c00f90786105014060705070b45032001c82c03010072041c2c2c0110046804404c0e2551400741d5445001d21044006103d00b200091300c10f81c1d140500d03030455078026060010b0b20b0078510400301c1000c10154440c10418280000f001040042080c0360003003da64541c19907a0030140e030b402c96600d2564018805111211051010a807188000caa401c990007080c0161 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 551896061 1250 551894811 551894839
    0x3031e2a061d0705090a09020102060402010f1806090807050a030506010e0705070b0705030a0e030c0a030e1302040f061e1202070f0b04060e0d030b0f04050a1e060302010329 76
    0x1402480451142e210702c04103070080d06900010980280d03142240c0303c0e141036903000e804800b9a281031000a005130071400c0030030b005500900303046445004909007001b500c00c4100d1110340381070317455105600041d14102d00300142c89040c00a44080d2009803900e900080c116260943d903802c0c18819085c182c2c030420b000405c0c1c00d1003002035500d0190b000410107600d00b0310980080460704192603030609c20b40b425003000ca06003400011100c00303082490180c25401d41603101a00d100d5000315004d50810048030303e000b010b03203403440240040e1080c0300c07201480a040c900004c2c04044c54605101141904400c1b504529400c40140e882c1c9401d202800741c0d0b00d00c024901b00300c040e0710109000384410307a40001e00c401c00009400c2007100416078002c483c0c1900440034118250f424046a40303401148651035400307641043c0c0c002a07400b15581c00c0218821070100070062420710f40b42100d12425544940a00440d81d05001c6c24a4104040003604081503040c0500201d03408007800c034521840074500340e45 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 551897311 1250 551896061 551896073
    0x50627011404060207030b10260102090d050105010e0a060f0b090301110319050906010518130210110d020309010509040f0b1905041503030509190305030403031e2a 72
    0x200104001d50001c0e40c0b00c0c2d95511002c2d540300b5031400700700c903140901d40000740191812244c80088642240e082c09510072040324000b000340d0485907800495400b00070301c14241d01c80151800c0868400d10000403558500000b44801c0c45010300509903290400c001000b0f030a900030200402d4070490350344241d031521504000390041100545082d000300300401041049034039400f0040120080300014006580d400391324070f0b1219024022541c1c40030480d40041e42080f030100300903a10508034810003503031650540004115440320004a8005210441c44204801701440800c0d080f160500065080180c1540080d00b14068482c00f5802280d4401c5620407441e02c9401118000f03e0103800d904840400d058180d08903016400f4841c001ca0038880d103200541108004c600c21650103a0b20142403078000d40400110842c0d02001a0180031500b501101090007030000300010343c441e458001a44182c80100048000700560140c1403108000c1085203115407170440e41540b40303a001000340340c0072281c80d07c1 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 551898561 1250 551897311 551897327
    0x20a23040609060e070c0507120204060906080102190503090601060804080d1103060a141c0c0b040e10060206040507030303110d150501170411090604020d090c0f05062701 75
    0x6940141044070000710082e16510400960341c41c00c0039510659126181611200a0144000e203140e00a0404001d001d181074400001244000c00100c1c01540e603118500c01da51050304520080d950000d40311551402a031400f00513502c25050090841c586180c109440c5d00b0b0522506043c4030214002508021258003180c1e2817222444042203200f41381ca0541403260012200c0070300611455402003401402c40317084503480c0c1d40c010900502c0a0b000b24200c2041c030300c406070840f20307400c8986010861100c034070042d0000d001600010107840ca014100e4034101d20841d404141950410018000481c402043d0342d01926054100401d00c0320061a07400010312a4a202180e440d2420b0b4111102c0e400a42620088a03000da072a407100c0302c1360305010105800142c0b401018ad00c1100341000e907600f0079950440d44450028001410301201304229019140c5004089411015040341400000070a00f003500c050170341070720b4117420034100a141b0341c4903982c40e096900c0c0341d11725607890b180d03070340e1140b140 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 551899811 1250 551898561 551898629
    0x90108101802030d0809060901021213052406090c030708070c26030a0c050c031e07020d24060510080603010b030a050a11060a050d0b0301090b01080a020a0909020a 72
    0x1150311000c49000005d2030100199106115070180ca0049951072105009440c0c0d000c101800c3c0c5107640d211803c0c282101012007504403184d01440300c0c1e030050454030319100081d040c1e45020f440c211b40b03080320800c65000030092100200c03c1041c0300340902c142d88421600c2e400301c9141040b0302c0004550901004500494070301c0b02c0035100242e400d005144c3e10b038000c1e43c0a41008401072000c106400c005803800d01416207200c4265005009110003021070700142c0c4031401540e01c02034905480c0ea0089201103981e090259a40d160103e5481d048900b20307900326003070780c00081c1300b0007082e400d0200054440543c00c40700c1080010300400303c0c006580c01e5000050100004084811507038462030130f20b8980c55024025210314040030201e5003907041c034074102d90303080a039983c1701443c04805055582c01041d500d141c8640645d6031740380310300000300c070114110b010305450402401e030342400b8410484039801c15001007100344d01707144841d00140c03500c514840554586040b400030101c40040248107603012000 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 551901061 1250 551899811 551899813
    0x1b0a06120f0921031506210608010612031701030209010b1e07050a02031506090609040320010f060603060f050909100c08100501020c0d06050a1805060a0b09010810180203 75
    0xc24040d2040010381c9100c43c41407a00e041c082d080002900e510036a11620070b01c00407850200c100030b4007400003440e0b03049150301e0b99800506e00f5119480207003150541d03000306000e4100c40c15080107040c2c2000744400e502c2501c91120500703604581c0410030b20070042c864064200c0c008100d0340444034401c8c0420040c1201d483d00e2640b80c403860308060780c0d180388684040e0f000c1c1c0144146c0d40501ea84401c0703128401c1e4405000500c050300d03004240540580010030960800041d844615958800010b43d4600d1341c424100208001d083c0410132070842c1d03110303403065051502d032010400100b0301d60040e80007100d601301e403004402e580d4014175900f84400d1b0f0039a04105071802d0391980b02d658103c900c0d03a000301c450091407401c0e00d490f43c00680e501c0d005291030039031000d00106180300060b0346401007544030800c402c001c9403103c00d619a440304043c0507c1c0c211103a800c4041000503420061007038170490316040b50704a1079949400b42054403000030703a48000010307840301c002d0040030401500304100568090 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 551902311 1250 551901061 551901083
    0x2150c1218090a150b0c06160309060510060801061b06111204080c060c07020306060d24051e010b0703030b0f1e0111030331050a03021b0a06120f09 65
    0x4182100904d410180014030a01c0c210020030803081001c243d55040e48070750700500e6103844418041c1d05a001040d4104101a2210f503c2400140a801558020020018110301c29410060090308041050304000104082500521045117040305010702c0203400540009002d01080500310325403003112041a00440c400d414801080b4086000307020310864031050395000c1c2c80e0541d0300d17900351058000207985944110701207001c5203465070000d46014801c5200e0141200448400140d80c050a01c002d2600e44d03445c420132401c2005a1f01755645207e8032601c4240070b40c1020a400024040e00300c0c01390825903125070402140d1690035170100440307002888070310780e0141d000705210840c00284205001400142c10a4400c0d50000241c030300401c08003001c9000c0c0c1d205140b500d142c0c0c11380c5811881400002c0401500400c500303001c8203001034000d9001c0c0008510baa0a0f03512254080d07485c642c0500181442001580d5100700c072100c6440c061900400d40d4905500e01c0405030030101d6014000380091 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 551903561 1250 551902311 551902321
    0xc010c0503011703040302060306130f050c130909021503040606051903021305010506040b0a05250311070305030301060807030b030f1f02040506070204020304140f01060302150c121809 81
    0x200001d54125124019140c0550b0341c01100141c603802648002034001c841400843c2c3c85240041d803602c1010080311001907103119000a20f8191501950950342c0d6403000140110b02600080c0c41c4c1c000b0b02120201844266000d5010480c40351006062072440d02010002c9030405c451500454024400101602403032000c2c403000d5551004988412489903074040d110714a824145d0003294100d410003071440d81083d15003800a06590f20400f104410028204000e0141c4408000704540c0900950715030881c0301c0c007070700d0f0181c84180c1f140f180300010340c08202c081000850010403641543e0749440e00c02d44e1920b0345d00080e0050000b400e01c0592501905800390181d480014004840c030001860300010310400302440b00403803240d4040c0c142c204108203e10009402d0580046800510407501c4682126410041c01e0a0400b543d00e0070480340d4668004005500d05030001070000300d840754207a4604030601d454035a54805116145e86940d0000ca60701c2201c6a0602d800c0d03a1103a40a0040202440c1c1 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 551904811 1250 551903561 551903567
    0x1306050408190807090506090402070b1302030c150d02161515060903050a02060a0c080705100c08060f1203041a19020c0a2108040e0604050c0307020a11060c010c 71
    0x441c01005074102d541c221510041c40c4034440a034000c02c1c0030345842d00c0250512092240359071020526980242c1c00b001040002654444001d104d07900c0c0100014102c01c03644100b40c00d1030f000c155401d201d00002c840348800b02c09128211640e080d8030f4140160390b04002c0030740c1030b08182c47c2c11002c0c002c1e503901a00e8044055050b0460407400109408008400b078071900203a6610116010143c0030b944520303106001803c04070002c20038514036041a001806d1a6950304601b944041012640d640104e14580108403603030107480d21143c00b90910305020310309030340441d100300340c0749210301d1252030380408072100840e0901c1140c02030710014001d4015442c1501c8070800aa00202c1380030f03c0c030390f00112000d076018408644403004640040c0009442c601e411121619101003454a5908440303141640780041c04000040005094070810054140340c5401000101e0740000c210b4001c9080420070440038542c04038980102c6503002e007111001c0005200070036100e0148030201c000c81d6103401d9000035600c2d0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 551906061 1250 551904811 551904817
    0x606080a0c0501080106050a0503040c0b0301060908010501080c061c09060c030b0f090903370c03020c121911031005061906050f03060607021807030b0603090d081306050408 76
    0x40503180001c0102d41c0e0340300458a0702d02c2481402d002a07400c1c8500000d8500c1503006680090180900700f4143e034442200300400e07402070380080c0104889c001c040060100a001d064010500c030720103800041d000740e02052051144c069030001b2026141d480d0124807485030301000c03445800030310070441c0070b1000c1005401014a604414030800c0f2240700e07881c032032034142c241d9441000c0b0a0091400d00740301000825540800300c2c00d10001c1f036038080060088490507000803010304450350304c04001030355500780030f400c002018100b81d008030400440c10946c00030015209040f03021495141000100c1414900800660b4003401c5505020b4903001114218281d0802401204212203a4903111062400c0b8600104a0b02c0340c0408a00203101c18460903c0318009540d118034043c1c03003e0303c0c0481c80d50000766038610a00107031600007000d0043c0501d85505100b072540602d01079500c44d25505064441c16076641401d01014100a102d10015081d2061208100304030307613014105000d2030900e490800380c690 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 551907311 1250 551906061 551906063
    0x1060806040b0909030f0717120123010f0f05040519030302010b1e01140d050f15010c0b040219050a0b070b0a05070e151905070c080106030503041206090606080a 71
    0xc0d04002d4028500d143c01e24106001d00d8a5800851403c040d2140d01103603a00b042c1c0c0d0542d085581c0000998840702082c0040940d15000e1a1760324549d0304000e80180900c0304485090316840c400314034920940d8101c07440c1e10b007018003030500700215401100201c5580c41140c1007241c01c0134a440140003403500328a29101504d20075002400221000400c0c401400c510620081c001c48100500c02c1540d4040e0b041d40303408101903030f81d507840d00307418549582c2910003e803244001950348038108000d031100c110303000c0700420092800c83c446030580d480d0300484601c060030291048113080d2545985414240c011070082001510200060356103641ca441d0a410400b8107482c0c40400744001401552980300740d03489180d968a8480c00d40c20000103000308a000c0c401c0156001d00704010b40803240340c1c1c1915030900b907141a40c1e916610b42051400d081018800e40c40814680c0c1404424400200040156001e64003001c491701c0c00d061075400c0002c090444070300050030749840c25401040b15880451550051 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 551908561 1250 551907311 551907319
    0xb040801151a07110a0302090c0309120301270204090c05070302010b0607020901140d050304090b030f0604050c0108040302010f0906050105090f240a05040515011404050105160201030e010501060806 87
    0x1066584821411200d06801200b00c0b60310200b2002e00010b9003003c26040040b006084546080d489030f000c51160f06054400c1803800350088100200410100901144010b48001c1c2600355403422401e40109841e00c000018191181d444180d6140c001d541500c2c0185031540040c0811551400040e010b54061032741075005500b04411803580c1e08010f821103022903405003e00885a1801c0300400e270795001c054000b944220f401d5900c0c0013060f07042014102400c1322020001d100e407514005c141c03405091581c461400c0e00010100300101704003003a043c14103e001c1c2017840300d83e0b07510f150890041418000320070b0040d02e007200140600c2010f50026045c0d9400744c0d86040c0320380b116800742603405c500301c64000405903801ca141080180081010401e0300000e000000c40300e0711000010240d030804c80b180320f041030f6854030a031490740e0300980207001400800e1400d440d050411000915500c1900c1c01c01503c00144044801164401c2d4407100c11182820b008100c603584441008161101c160f5440d449 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 551909811 1250 551908561 551908601
    0x30525050a0b16020106151409090115020106050418030e010203040b0c0105150105192709022a0c2101020c061b09010210050901020903070308030f160c15060b040801 73
    0x100741d0052090501f80c8504c0400c0310329010741c8280444800d100da10042d145503034144001c90458580200d9903029200c8811f4840c10152000802401c4401d00d07030145204a06045c03900720442c1246504100c03a07501840c04010443d100c0005078071398401c551104240b080002070b0902a4041907100a000e000303010811403030010944011992400303125607403028044010000c4003410b018800f0080802e5640905805000304811054001c0d5802c2c1e02c403058454000540c940325008800611030908201030508075800c0c3e1130700038260780303032200800c250052003039845501500c02824001c04147c2d41c100000d40d59007548010385601c0c0c1205a6a1811928a104840710b0f602d0b80c05007516800c0f00180d00038485425440c0843c8040e003809041240b003958200587c45090301c0c1405081c2c080c6000704d4810b640c1c0c3c04d00e4441c00b104080001e01c404030152508109403502c44d4445104011250805140001203010011080050903903601074200c01f03000050000b0081419000304030035203c0706843c0c00c5 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 551911061 1250 551909811 551909851
    0x6040e03070501060f1a0327030408160b0c070e191a0a0503030a050d090f0206040b0403110301181103150108070306060f06050301150c02030105010b07150603030525050a0b 76
    0x12615003481c2c2c00e82a03014400035aa5400c0000311004490071070208020351230b4516105070a503849508950b616401007560302818440501c100300041080c0b22200380380035403100c20781d40c440da2035008200c40845500c004c1005c1d00750091340c0c1d440175070001c4010030044000e0b2504000c90006103400601641100d1800151403401206984500c0f42da40c80705498001d4480800340204004981161442c040d11041c03409a141c21001c0e1000d001d0449001e541c582c02c0d42001143c01c12841460751103a81050000001a0290580140e0a44d8000e5030003d590a5080009044c1114640d203c22070480c08000010807280c00115a41181d029180c00c208558840c88203000303000d041d00440340810f8082004022091440b83c03900a00d0001e480d204100c19505e03400642582c50aa0003131140c442c0101d100b2040c0502c107464400f40d00f20865080018038034591300642035000e01e03001c0d540008600144011840c00c80c1e07244024a5500106913000e4620ba4949100d048801362055406851000030805e = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 551912311 1250 551911061 551911079
    0x27020906040903050405040c0207080307050f07080f0a021e101d0109120b040f060606050405010905040209090106081003080301081b031609020d1b09051f0806040506040e03070501060f 81
    0x1040194040e81d0b0365160900740300c1030002030084c03850300c1c40841c0704400c40050100c1c414405071038641c0c07061000e000400e084402d00b80c900103180d0001c5045422044c0c1c608407088000a280c0400307071381554200329040c05040304030451a036001240381c201981c0039440c08060357c030061a003460000351001c5003d001c200c00c01181c46070304c0341c0103500100100303102100108145841141d8018400c0184c0500c119503580c8040c16905c090f400305d404240d01040c1401a036811082d060050842558110b0802ca01000001c88169042c45048207110401d004a50420f00d03e00040000e1600181c01300da0b656552500f5950f601502401e0002e250080700c20121140340c0802c40c0905940744050030b840c09030a1104d10002580050081280745a48039180d030710310300340003200c2c1004428030b032561590240341105000650000d000c855070420304d00c5d034044000d980c0046485030024420303140080e942d910b100208005104000c1e07000e400740700c0402c3c000c0400c441508211301781ca40b00200b055071541d8580ca40 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 551913561 1250 551912311 551912321
    0x4031206050603040b090a020d03030c1b08030f090304170a1b050312030a06150806010809280f020904140106081207030f1e02070f0f1203050d2702090604 68
    0x1440d4058403c001040100e0701070254070b60031101901c1030f155014203e6001030ba000d101e02101b2400319448401903180241c202000030361140c440b025990b599040d65440c164280b00040c01c12000c04c242202203080b002080040d10082c0c101c0b0041c10000c2207060b020039079030311091001150182d412032034400c0305d90103100ca00340460382c0c050000c1420580103c480b0410b9003000300029801075540c0000114040902030072804003d8580302c1000c0c500300800018090a40202406502d40c84400c40b101c1040404032a1000201e1001d00410a80320320f00e4501061101080e010354403014010500c0180000b03140040a41e8451038000c110340c90b51802269103038a001850700b590207000340001c00c0030a0140c0c40107411503102d4074001c3c0151045051a1080300b09041d00080140d10044050000390150a50b20026101d003221500d4054905aa4032001c103980d08402030070080041000b46103101c060b000765071100c400403180e85459603440c00c0f841e40701d60b003c0d900360300c11007590700481c0d054180f80c4a5 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 551914811 1250 551913561 551913569
    0xf0f1112012303070306020c150f060616062a08041a041505070e0f0904051009080f0c0a03090e04031e0903050f06070f08012904080d0804031206 64
    0xc0180c0c0e41e10b003241c4000160403009090030070001000602040d90741c28401000954810700c401611009010080c918002c181e08030f001e1441d011005200300e0304a42c0030381d0b90780880b08171000d80c0e0320050b1130b032820703000304000d00c0041080d82050300103060000410030140c1800c680000061035601c108500f115100020b440181131512810740441808440950040e400303406901620807003042d0020740800c95800b150902c001940b082482c40c200d10300329414603002002120301400707074145520f40c0c5071101c120108030f161140c2c0c0e03851202c08100c3c50300241c0390000c1051001540703c410522000da02c42d8840c28045000691100022842e030396200842070003030340c140c0e81d81c0d041c41c406210003061030a40b031a8100248024200700200140c41000b0303820140540b980170349501d0400e01d00182c440e408040c04203050003034040050211203507a1030303104480d1020780200c1d140300034a280c092006116540081c4000d003d4042c00c510304680040707503580642d04c207a580300c9840729400c034214200c4009000d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 551916061 1250 551914811 551914837
    0xd08010506090616120e030d1d01020c032509060602061b0c0a06020705190803070c0c180c080901020901021011161a1509010909050a060f0f11 63
    0x4014011820306002a00e40254040d0505250a40da0044e900c0b0074031080380c08a0f00030b0006144001010340c00505400910000d900401501c40e1070f50300a09600300b05801200114581a11101c07541e00c2044440c0c124070307001e41901c1410450701809888807031641c402100152600000095034921803192100710703101385c6c1c00303014180c032450032101640002c2c0350341c045403210a0044107000703001403003500d000510441006a4442d000c0c0307401e504040d29444900b0480d070240700010701250150301100d902c12401d10f00f4281c800c1c007a20b002d03240d81e040f980205006940c0a2020050103c80d5801135102c0b52440c2c80b0f50a80755038400d652800c0c1d2080002c0d40b80160090a41310002c0300711604840c4480f0075003080300e41002c150350440085801502400e407041c00e43c29101070107041c1c41203030080e0000c1404003502c2d45200701c10003080060704180702c0d18a580c0d039106400002d004050180c0307840345a0052041c00015800f10400c0c02600980495004c2a0b181604490805c855841180c11407000741c0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 551917311 1250 551916061 551916077
    0x1a010e01031b081f0b09040804031403210f1f180b041503031e05030c0a1710080d08270f1501030606140d02040b040e0a0f0b06030d 58
    0x5940c600244016601a019094210802154580f010f11003800c041e6441548600c609420307180c0341055074a21040b6038082d40d0201c0c10310012400c080129002e594108040c07421080105a2403451842070030b9002242068041c80000f036140c02d403012902600e170201082c18651a502d03030b20410780030745000c15501d09010703d404100542000310f42030803864845500245a215040114003a10000d80208417031144022043c010182c204808116541450644060786800d50310083d00030701c000341c40ea110056000c01d840c1c2100f845440d40c440b000700c0d0640e1102e940d051040441003032a03518010504540500040004030ba4811544a849607403c030030030240d101c1580c6280018502e66400d0070342c50b4001d1062504c1c91480820980b40c1ca100b4040d169a219803440c20720301d08968582d004100c0c542940c1032004903035914200703028001c0c1c3e0110f400185100341400041c006200031108280309006000b400001d1115086080c49428011510304042c3c0c0d50340b8040603210405000c0040100c2c13501d0b = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 551918561 1250 551917311 551917313
    0x180114040314010c1115070f050c0109050a022803020105070f051f0c0c1109131a0703060f030201120c03060f030501060302040e160e07090b0c0309041d0322090908071a010e0103 78
    0x12340072005000c46942485450000f0b0707040300d41d0035210208800e40e0b043d4000111707581142060500c0041410441c158002c41c044c12030714054220104e88000303810060042124410b10041903840040b40360b100084902048000b25000d1a40c2a0b0700e07644c1b090070b0315100c81e2540617402420300414444e4131240400700091403130100480e142000d0030702008220900c0703407200002c2101582201072100b0120840c003628101c0401810346400d07400100701204e40305030800051341c1007200000500304078000031071180201841103004210b1580310307054189004000006210040d84601d003031b01e00a903414801743c04000b500d02da5130400310041c7c404403407001508000b0b00b005008003e410808a02d800e001e2341c9c0d55100c1c4446a500400080c0c005900300049403074240c40c02d032281031007046000600d000f0b0032884401460f12170040c9000c0800c402180054003009101c1c012080001d04142e080820002c1158104030b0003035000414101e444402d40740c1c00340c800500011515040360144100005940c0c21 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 551919811 1250 551918561 551918567
    0xa0b0c10290f0112020d0e010203040b090c0a03020d03030507020c06131d0f280c0504050f030d0207060302090d120206010501180e0c07110d06150902180114040314010c111507 77
    0x20003060081c0c1c40c0d0381d41c900c9487d448002c3c002580214040c0b0004640c0e828a9451681001c02d001045441080c242c0010001a1900081f19076443d400d4100001c0c159100c01040c0d0900503080c42655000301d0000c0d80e10714100e1801d00300426551a0181c58400c00c045c03001d03503d407501c029501d031000c005015000441001036240d40d010070010b1041c003400704000d90700401050b504015540008640081402d1249080121940c260030b18102d0040100600b2a400a074a844550084404248d0001000d0b042138a500c442c80d0780385548043c0150002e94400402500e58100b800380c0c6002455441d40380c41002101072219042c7d6006914810403601c6200c64035103a5840460202e42607900f40703c0c01c1c5500e660f461546070380079000716804115072000216402d114000703500017156a51060000b0a250301c0004071941c0004400e003071104203404c00100c007c03420f0055034401445c00399415241040c0f10301c10341007100c400b019611844001009110403c0e01e078011800c2c0e007036070b2a60090000d200e1500c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 551921061 1250 551919811 551919817
    0x10f171b1201090605180303060f0f0f03061006020d080705040513090f05010e0f120712090302060a03060608010b0a080a1d0304030c05100507020a0b0c10290f011202 73
    0xc001c10360716400c4540851203096500703c00c0f082c2c81c196614401c000e44802d0100680e05001694000365185242405c002000207101000701405071803241c185d080241c81e070040300402d0010050458044e03142c0302c42180c203e005640101380040c000c104422207100c9c020b00c038841c00382900e030b1a40e50030a4104814400070b9107525208003469600c84252001156008078509542c600960002c03500e920313114080352601c43c100d10060402d030701681c581000c284c0c0240a40720116481841018103031980c44c4201c0d1008042e070400f80d80880d001644000454141d8000300448000c0c1d2502c43e1140e07039451600c4224090080c080d00401c9000000a40711409980001c01340307400166a401820520b4800d00c2c034640158000300d0720003036a003c0502452500c40527058104003036240c804d00e411a2a40400c02e51615842941c00d0040b020520035600d02d030600c004099250004d50401040c01e010703520041221444840c400c405c00d12959501c2c3c1e50600680301050fa803010785407401510f030301c6001140258 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 551922311 1250 551921061 551921113
    0x60406080a06092909060f1509060f03040614010302100302310801181e060b040c031a01090b09061606140117030703080f0411030106060206010f17 65
    0x70795a4000418000401e100c1c0d00c0c2c1c24003a500e41000c039240082c10720038000c0f91200c442c3d40706290741c0b41080501d584204040080321815500c0400038a070b500350140c07c07802011a22076200401190003115500e140e00075610032400307024144607182011211445455007800041d4100c5000c3d20401282e500135002064950351400d8004240c1c042001382c1220200b850602504041001c0004c00201c2002d000d01600d908801c000f90041c150140d9170307200007020f410201c441c1850990700681c140074195120280280000c2c0051103520006940100104020442035400060700c1d8801040f551140c5a610181c40401e54610301c0c1c250848100092078001e0082c003000405001a940700145203800350910b8a0000c0c50030442550508402001140310a0b1581440340e00038081072000c42d500ca0130180c0c014018421107541500c941c1001c84d000d2013a40c0116406608107100003604a40c0022464120b40880045070466502c41040c2c1c103050414503944d01c0b0981c8400201c095000750b21800392000 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 551923561 1250 551922311 551922331
    0xd1103121c1a0a0b1b0c1c030212030103230c0102060103031d0a0801050702070b1e03040c0b120403080601050a09051002150f06010e0d120810050d050c0f0109030206040608 76
    0x114202c0400034484042e40d4200482100c0003164040090125040451030070b807845c0c01038840d000e0b01c00c0c042940ea0403402c0342603100d218010402c0060600034004e4400042100d40d034030359290f03124280301da039006203020818001c2091444a501060011509001a0605901078200c0b0f0f4a11303141142c40c3c40350f1481032668030310b81c3c4c950156290ba0f0403400c9002802d4085c000f1806103002e141c0079082480641c00140d002c074082140038040544441c40d1a20b54041410151f180c1d25281005c50520f0a036030032410507071900042404100200f600c0c0d0500c1a40f03ea91100c003240c1c1c4400045900707004d854040c4010400841c0d091125141459501d210045588115070301c0c000d00081a4101e1002a5103230141a02c00e013041c040c19581c001200380581d00162421403000700b080d07581001e14000103011031b04000ba1034022030146010018104010400109071180041c040e003040ba840740f008660182c81001c0ca0241404070354003401c406412a50000c11650409203404015180800010006a00 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 551924811 1250 551923561 551923601
    0x2031909080c011e1107030c14010b040f021903020408030d0911190f0509270709110405040f050c030c03041b0314060f012706050d1103121c 62
    0x1201d0091007034440198111308814143c031900b8811204a07444100000c903801c008104c04d00101c0d4100080d0310344507a0150b0420804000d80c2901d900425403508407503031150400d0815010307007030340e500500204240c0682e4104110841c9000703404902c40d61142004030741041c0090050700b000755001c80079542c041c0e0311040b402c903411000036481d151000e42c2402ca07683c0c500018080d414580c501c0201a00d02510444420306101c0c0586102140401d030082d1000000c0c50203001054007803205000410944d03e0910800060f9014090310750080c0c020b07180a140717028032040f0a05000d009807030280200c0075256255846030480d9404a910040c01500c3c3c45d854a18038603c9540306d46a402d0007140513400d00d03c141748142403840c0c280100a040107443d101c1c0400103110720a0741501011380c00d680700300178041036400500c2c1d500140100f0303884142d2084181c1c904c4002d1000c040c0d015103820b0b000302c059503442c500b13454140019000d800440050544101d282014541240d8420a442c2e9000d8092a039 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 551926061 1250 551924811 551924827
    0xc09070e0d050c1f0807140702150c07060806011211030408030c12010902031e1b090102070e18070618230402031905070c11310902130203190908 64
    0x10004040c1c50410034201c0319255641200c4c1d61000c19990001c1c1e45d443c0030902005001c20801c02801444030107842006c2c9150040312240340802250100c200d00c20540c0d1205644030405458a90121022804240b0f0350384034182e1b02180748187c4441549020b000e60440d2285e440c4e60815820080c02e1200340c0c1d40402ca0b0017400c114001c0d201e0700a02c0d040001507921b15004030801c400304071030104000c110032003a041c4055884822229000888000703074807902c3d01c446000403882c160444d40604002481e54060152070024003035a0b44a049542088844403581c80c5411511100d00400d10180090420360900104020418130210000d004130b902482441c01400078080768010340c1c07402410844030b41c2c0d074a060901030090300d0f0f20840e2800c0851224080d40c441d0840c102030107242c0b91040280d02108180b80d008030301101c10300c00f0848050b145017403010030804000c0480280c00e074816410304e0f032480c2c50325007680210307403061b404080110890b00c86490b12101030203684c2c0c1c1c1240c45003420300c5026 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 551927311 1250 551926061 551926069
    0xe011505061903150f03020a0501050309060a0903050d0c08090f0d050a030e0c040218010e120d08090a0f03020a0b090105010b04090e0c0616140d08040308220c080c09070e0d050c 78
    0x5030145c0310740c400c00e0114628501c1040781c140d20641c400b6040c01014003c020007110b0124820740c3c842202d8001049000943c501100d05200703044035003007098a06000d810080c1d50140c0c01510413115030048a000207028482c0ea680d450058803210005501041030000942c801c1d00900082c01e0030104840a04000d4400242641c010740003c0f044803001c04181c00c0c1a40e80440c011103145815141c0e9991001c08000c3c050709c50039189288030074403032428040761200c1c004004131074840f504030700c2c511401501c03031170b0081d1151512441a07880d004414040f0302c2840040c031526048540303030313a200d514080c0782c2005040902042034640129005840100b0115104e0038020080340d4a10310700602103503a940740c13000c8001d00e281e40400039548260303d041c0300c554120221503040750300350410404035503403503a544101044401c0f072002400c610f02c022808010101c180101680d4040098940101c0c43c0010700106280c116403200c0020318002400d40c0324101120308031500c50043c41550581500b0350081 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 551928561 1250 551927311 551927351
    0xd020601050d05072601060e060118060203040618080604210806090f180f0c0a0611030d09020307080114070807030515010807030f0908070302120301120b060109050d060e011505061903 81
    0x18084c0c9443d04003c0111541c2d2010007105c540c070583d2f616403000360910600075564007440c0100c80034041003860030840300501040700c41c001c0128508035002446d041ca040c58100001e6900090840d2803000552196806101c82c548204000390103c200303a9203402c5136124100001d012110007200d00c450070031040d00b0501c1140e80215400d00104501c0d18220b05000c0c40c40c4050b8802410801c01d06203c600d0014003004603200b90300c00090101e01d2841600001e420051103610941d4030303602e090400600c2c1c10348c1d801c51f0780c803404980d126607000740d940a0098096940484492120b03e240e983c2c00380b9150b005500b01d6030840760520340028600708e944010b001b00c2c0e10fa25010f5484a00205604c010540d04001c0000e034807880720040f5007154503000100c0c03c1c0780d40e031400050001182070001203450f44100d084a004200090280900c0042d50404000604e4640c102c1c1015500300400340c4038142e0a100c8150441e9405400c00c2d24003500d04200101420030380a40f20f0030191204001c0e1405150030b000c1c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 551929811 1250 551928561 551928569
    0x50910020604110303040b0d020918010602070e011721130605040e011d0106230403062901021b03011b02100c020d09050105070507170d020601050d0507260106 70
    0xc14142c1828184103800210034070343c09100e03510810081c040001c0410580d0032100344842c015031034202100c0060b85a50700c0c2280160f14051010000540c10390004080d801ca400202c45040280d0b2911360f486022185400d4080759540302204036120300c003a03003406a2090003942c0c516410245000c1a2801c00b070039550003100050380110b42440130f807100c038500740d0041266102d421180b00c1c8408060941c080148542020f1010b001c1c4c0902c04903400e60496251400c401003001c0e583c0d502c0e480c0c00c2c401040004003400c0042c0c1c80c1801c4080c050140c003004a201d020580051903401c07200990540c1324401c50840c55059501c030030120b40300c10500e5540484c044040c1d0064850034a002011404480744100d0100440d440401125000c0d0b40000214007520300a190442c1d64064505044c6d00e41034141d0b000804a201d51200000814008118002e00015035800d1f918240d98410400000203604040038200341c00081041107252500c503c2c000000307a9102e01110700300c204000c0c160844d0003c2d40 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 551931061 1250 551929811 551929813
    0x18030c08010b04240b0d06180c020f0d0e06180a090c08070f050a081806040c1502061e060d0f11040b03150f0702030c03040305030403060c0504080a030f05091002 71
    0x5407558901070049500ca030584e6080c580102c0305038050765450301240e2181d00d00741c0c000011000aa031002d5040750303015241c91141c200346100d410300035000602152280c0d00042c01442c0d00d400207840041581198441d031950340d844910842c80420078954055891a441520311010f03411194541030b188000410802074001600c40c512000940311840040c5550104204016005c4856401c00c068512075810343c60158001c2d9218600310301e00c400507070350092051040c5810403040203c800346d200e056440c407426074401d0981c0000281e9032940251030180060014107180d183c8010304d00440b9500100040000001c8199500c6480d8034641810f01507a0804031407002c407a25003080c1c000c1c44551035007940140400441204001c003e41005080c0e41c242400c041c02041c0564420800d80f000400744800352a42e0b0b80d0f5034a041c2e5030305d6005210170bc800a0030b2481d1003814900550036102150350010281c1005a000d070740484902c80c40e0402038081c042c040c8907140460700c40c01c400c000b85c554250 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 551932311 1250 551931061 551931071
    0xc0b090c01180303020307060b0607140601030210140405100c0c06090905010f1211010905031516090305190c0b1611120309010c0203070905070801090c1d0118030c0801 74
    0x144141e40030307003150b409410582010800240c1c004100c814668102e40c000802016230000243c8500c02c40b08058412000201010481600451018101c92084502e44d040d00c40c8410305460941540c2008500b0520034070042045041210215901d60310510b4440d40e1404540d0760325901d281e0b203130000400110348103c1808130310715510443c0d0150104001c604c0100749010680c50b80301e0400a401400b1004001808445034084d910300030151000a090355210a40780c0326803a0940b1003160b0600400c1c180c0c0c407a0302151802014190140c0703402c01e01801d01540e15580004d111441110101d03000c0101240002d4030b09a0701c009003183e520310328410f42d08100c0905040d000b40064a82403803181c03815003541013403040008110b03009007100382040d0541780c02c503000080c2080b0156104401480c2890200300f1070f00c0c4e000d0070641c1a1024000100501815a04200d4402d4003544403612031121410a4407010340c015400640b4241c455207504a0301a226030f07803d2010b416035408035281da91030b4 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 551933561 1250 551932311 551932333
    0x405031e03160228020f09090c040f060b160809210c0102010c05220905040308180c060f0f0c0d080108071d070503090f0d0e01110105070f050a0c0b09 66
    0x448031400300c04000d1004003411030840308100c0913403012101e0f5420f4410012080400c54941c0f658020480304020000903a610344084510b88512000c01d00c2c078403540c81c21400907150080752080c941a607141031516030803e1600d0f02005403410001c402075540400034007a5480b569603000c411000c1d12401825060041190a4428030f0b082503442114156418445c42841d5183c0c03000695070200c1c25848c40b0007207035142c10411806a4121740180c0491420f0004100c00e25030844840381c041c0c41e89603611042100d02401d91501c600440303150039880001004017040e50051000580441084080140d2610140b0b004241c0380401c0607002202143d00c038801000402420300055000300b0ba91603020652000040f609107034a60020004400c2c00b20100c00300c6c0000706c0800c0641c04004401d4201e90f185000002e0203050f03007545900d070030300155000314903554040c01030294600807a21034841900c00140b600f0183c40369080101d507002005450000c14010441d1070401c40c0c098410000036150352144 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 551934811 1250 551933561 551933581
    0x110d0c1e150509031b04020c01090f020312160b1e04030f020f030703021221041b1a0d050402030f010c0815010216030b22080a0e0a050d0b0405031e03 66
    0x101c803140203100051206242c02d8401003402503500c03a4a0b40c21442035414580003030300a01460160050035864040507408200088442c070b0380042c02101218001c040310100986d01c3d1140b80c2003118044804003540001031001e20440f500b11081c800044040e00ea005c03102103604d082150b0a0300018074140009000e503405014030209548180040c2d850f10065490103955400d0642508811503000500e4580e412069041d03402c44101d00d0207a0469402d260030107a1100c05413559100390011001e03000220600c0f501e4914610001040c0f42c0303401e00b8903a0074820020302005000b0790f018042d0400e01c4070454802c0c45541080c1e04181c40d4105681484598070300c0700d45540303038038038155402044962010102c4a101404030707035200300c0100046d65180420005100100ca6810302c001101d0545410041e20b04060081c080d101e0340c13480300c07900001c0c2c100030392110380d84240c0c0d4116218034503880101c1c0e03d05403220ba1241c0100100d9240443e00c0c0c0c011400d52240701c04580c00b80d0008400c2c0500303118 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 551936061 1250 551934811 551934839
    0xc0304030b0f1f0f0b0d0f0c0f030b04021c0903030f0f0608071502030301300b040201031404200319060c0807050f0409180203010e010c090e04110d0c1e 67
    0x103c42a1526100e00b0400b41e14142e401500440d142c145001c00c9400c901400c6801030104010407400511000b010760201501d001052444040802d0400d024081c0c98202403080d203d00e00700c108400b1086180c00004840140610041070b001c240c1c84860003200b41e01c07203000b0001350208014000a400c2d03e0050a0b80c10044c2541101e00c480e400d140c6c0500c03005d070b4000207880c1500c9420b1041450301131004801100b8080c0c82000f170742c001910006140610410440302e40c450340c000c0c0c03028402d039030360207a030f01c248035000302e400030402580f041c03140c00800c4c9200101c04002001a048034080703004909030240307a0300a900f04980180d118034440302925402401c07903801000707500744107042c036200c1e02c0403050b00e0196008201020b0b5a4034881d0201480d4141d03101e480e140c01800802c80d039440440c510b400f030040e110f401c10120710864000528004441000d511880c0c020100415600c0d54a007080b074840c0c0032403410b0307680100640e400b00d850264404002000d402002616061503e001c0088181072 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 551937311 1250 551936061 551936101
    0x41a030106091812181206110319020a050d0e0714031204030f0c03080316020c0307030b040b1017010209010f080601021c121505040b0d02030a080c0304030b0f 70
    0x1401d21000d0f24030040a0214811a01d9000c480240b4400032100300702d8209282401003880280c4500c000500030041014640100d401000c0500c58080741042d2850103101c1a2203481590400c0030302061260a03690103400c0141c0185881c9140c05030750b115813020b40c0c641450789e100715081120101310341d0b6500c2d802070340750000580240c0350a0f511820000c171140a40c0c0b002802c2903590fa03090305d08012150b00780c4406103601c907c1144d10b900348883d180782603030078040703581002d489480c0000da038a29000400c0070032a603104140d5442e81d0354070f598801d10b00d04090700000c4003183c550404206403581e1012540a1100303030707000607203030201580010a045042901031003400442030034000141d07030100740400c10700c0c1850008480444901021610170341c5180b503200300189007031105010f841401111000701c0d00122018807041110608001c00544400d5000354150301ca900014001030034a001341c503070403000d01c0940b070415070743c0d44a07803e10b10b400b287c02c140d08601c1c1c00e0400c080300380e20441507880c103 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 551938561 1250 551937311 551937329
    0x212010608060a09090302012007020312042340050c040306091b09200c030301120602070209040305030a050f060a05060702130e0a050d2a020102010b041a030106 71
    0x503040000c0030070f0215805020300701d0b1103038030f400310340081c14000d4100d8282c0303010100005501000200c0e403000f403500440d0b4128802e00038000307504540c042c054269020380d00030010082c8010b050307c4c49070345042c0207030201907040810301d480c40c105541c4440c3e0b0700f02200401d07020780e0010940390040f00002c2e4507100c0c41c140381a00d49070070b001c142c649507029142901d501040c001030761040350500b0350381100c5c4002c140c04400102c1c1c0000c0f800b900942c0010300d0020102c01a03c64007140d9020021a60242d0701580d05a50b1052004204c50b6618540c10b010842c0500801482d095aa40100740e045208503000d802080000050150f2401240309540d400038510f140507400c0c1c20400c2c00212a80340c10300c1820b11442c00811460150356403154202d03041d035a211300c20010000c1d0703a03400548903408518180c849006d00d000c40d600c07007401214900300d01c149055440000f030070210441000902030b408180d04665840c1580452606c492160a030354002581e0640c0c88046020201400e43d0030035004540300c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 551939811 1250 551938561 551938577
    0x61e0206062d0316240c1205070c0b0c1b18040201110708061008010b0307030611090409060504060b0607030219030c050f07080706050901050702090603030708031905060a06020c0d061b0302120106 86
    0x641c040d591810847d40030250801240411030225941e0142090140600c5880303100055080c00d290000d000494580b41507410500b03980e8034800a07a8820f0300310941007840203458684d840b00700361750385520510504046a503903051016081c138208440c0c02c0b68000d41d0003003088c40b55000c81080000c0007842d146009021080b0b0b00ca0100b82c480c0300c10302c0f000748400d0701d4a080d10300c5003006105440040b14040e0040010f00c490341000005060309441c180d070450f1900324000d9030790414604942c607854041e00100402c15810544c1514691360032007da0400c03014207620070008070301b400891043c1144000500c005400c1c0080c443c180f0f4041d40c043d00621804102154580e42c0042c1030310f08803034040b10b80c09000c0e030303910f03010a045103c1ca810082101c0d0000041001804d4a01c4c50802c40f02002c0400300007554640c0184009119240a080b001d83c0c00644a006249040440c0d11303805442981702041409000140c1c41f1840740700050311005c25004a5107001d51015940f6040c0108818508040 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 551941061 1250 551939811 551939879
    0x114070c021c12110309060c01050f060a030c0b0a0c0614150108150105090303120103030c1b0e3d06080c041a0a18061e0206062d0316 59
    0x40161580070086062010903203520386211414816a900406d01074640f40d0f40d01c0707890050700d00800d000c40b804401c0c0241c88000c1181c504003c0c0803001070b01d034001030602c5803604183d01e200f0980c100e040072904000390b4001e0b0200203080e130f01610148008003145c12007182046a1480c80c8480f00205050422483c83c0800c10344002c4e1a80b905c000701d0003802d00a656695010209007144100b0000e0000141440000010158401c0d10344c4502030040c0d00400d0720112588030702c031b02d4000c06e01c1264203080703c041c0070450880a07024610207003208116402d0044103250f41104040b0f0305200704881008a002c42002029004040f00f507001c40d40c43e61403440c107410f00d00d008901c0c0b81c035200b0000c1074100100b40510043e0003140c000c409802012009000c4564a42c40100891102003042142c02651a10740a025000160580c0254002406001ca013001c0044004100c1c03403c41c52a078000d0725207060031130281c03810300001c400e94941c1076051450900300000c0003001e03042020b800c1ca4101c0006d00800c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 551942311 1250 551941061 551941073
    0x110a0201050912030403060e150c040506090103050a0f09030206180303091203180303010f0501030e06060d0602031509090109030906080403051225030c0f0f1b03020114070c021c 78
    0xa45844085440f00b108481010b009403071405079420050820b071828021000b61100042c4103190f00f64881415a00355a842c0c44040b000d002e00d104458000d0028003401c0403a60007600701075800200c00100040450006ca50b072820349002e5001500035800c0001402842080710410380301180c9070000461450030418071403030352211940741c1002240ea010002c100030490703c68591405010640480341c403540c43d0543c519008115100d2240803030700d880001048000003041c41c0344144c00c020030100b03d00c061521204060360000f400c40001d4581001607444955444000c4d6000700d2095000181c00300c1d4514002d0018040f0340c02500600030040c0402c00040d6111702194214003030911800f1250300d50322403030b1113400788215485c00d05846c00804150440c1d890780c040b00c051300440e42d400c138903114500d009032540c820181d80880000c803814100303164120840701d04407610344203100014403280d4498098290070320642d9420300140c02e03900340c4c005525100c0c0c10034a030301c41048490b444540703c82d9160 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 551943561 1250 551942311 551942317
    0xd150b0109060e130b01170f1f0305030a0f0909060608060405090309031f0605040c080604050708070210022d031006020102040e16020703020a1203110304030809090c0f070b01030201110a020105 85
    0x14030b00c40c41e105c0044a100380d100302d070300705407000f00c41b4500e038610308141440480b01103040703c02880000302840c90044500004440d1811079070040051850906c00320421a00d003d00b022281090018401c2c1c0040e289a40d441140b00030440c6545000160a050341044251103000c0d1a01c000e82c1c0c020b00a8140555010403504072034416005220300d83c402148500000c2c012550000e44d10919004402e0b01310368101340c1d0288038000440342004a0b031344420007590414030644050b00140d20140c440d40d1000a103034024010190300641e10040c02c45840314400b0090707011009141e60030804424061031348944003105000d014540020342c1420304200200001c40c0b0000c01d2200e000c48824500a0603600a0260b08007545e0054460700441d0b481d0243c09101084400c82240001e03896000480030b480007100752800d607544203003a035141c071160100f003050403103019040c0c103c4045e040095221a54112005003196481198010807035813650001400c210504107075400325030051860540180e03808422 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 551944811 1250 551943561 551943589
    0x2303060a0626120a030b031e0c0d050615030f070902092b0b04060b040c08070f090806270a0f1403120c13180b0a1508010e060d150b0109060e 62
    0x410f0b91298481ca83c00c4019192040500350540034130f0191038103001d0702c0d2441e891070f0b003c05422159801811001e10150600102e03002d0088d4208a0201e440e03001c00350704c9501c1c0540002c0440d842680303804206810690507a0055050030303400501810326080907003490200c2140042c41d0030928171216000000d821621200401c5082c1c2c55000908000c0c1c2a441586010400f603c100305080c101c100140c450b81c400e999100104000840f08666544034110510545404101a01840e1940401070144040c003102e0014544110b6807086502101001000e031154011010501980310a007060180145820410442508100011a243c0d421800c41039040700400150940c0c9201ca46480e0308202c01d40e4006050306103103498104070141da240c006c0c0000c0e901c1203c400319500c0d900c030520420121180c0c505404642001c00420070000d0500b44650b000402500345243c112446e6510034090411141c8880721556492042c0e0041d40d014180d500589074a080544641011500203041c445071044 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 551946061 1250 551944811 551944843
    0x501020d080601201b09010510210b190303031401120f060f0f090c2705070306051003090308010b030c0414030a0206031e06010503040c2303060a0626 66
    0x1c185400c100313040050964020300d130820340350403104503a0344803044441c52140d140308865010021489281c500d441d5800300700b0740c0e2210111812000142c410000d61080007019041ea148000700494031a0503040011606007014220042c0c103610b0050f0444680c845c46e0200304048200521a11300d860b80302c55202a0498182142d1400510b00f42c00900207901508212508245038401c41648c250011603c0c80d12844d5140c486640b40c0700c0e05129003052504141c0101c0b1384041800482c40b45601c0705c1c0c1c00103018039020403c145c440012420460603040e8120004e940d4a4901c000d15078010442809022034200c00c9203103090000321043c840c06079007d51000d6804914030840390b40d40400083c401c0c01e03406000f890712072800340303442020700c4810000d413140c25103a580062801c3d8421401c882c460b95000c3d01d860350039070400e04001000140d030561400d5200201c038000a40750741c01c001700c07486061460700200e1601d0600e1841005030784200782e443c6110001c40c9281d10703550404201b521014803400 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 551947311 1250 551946061 551946077
    0xa14010b0c160f0303090504180f150513051b13020c030c1b03070b09091303020a1403130609050a09020f0715060320150c01020d06120203070501020d080601 69
    0x145150601c02410310b205540c070140c00d03001030504200c00100040300c2c000e03107481152598072418002640c660b400d450390415800c6803400c0004a841001c0d00d0818020345001203e941c000344141c0881d04156601008003a0100b402402c0240420181c0580d0382c1c0305a600c030420310500003240c071020110b42c88081e039130340200f28a08004030810941342c0749045001221032240b8801e1246038000715124016000303001c1c41c50041b48032840308080b40d141c80000381901d0419500e0080308a010721202030114218040c80c138132a004500303003856000358050424040c1d542c42c082403900c41d9010174a0380c010401d025081e00100501e03a5014103480403202c00c8500940d4440300d00351074000364407400c50000c106510010444d82d40b82c0c03c0d0781c069000e49125a040e2061825002c00e000ca05081710848640d00061300007099001c0d0b10b524014200041103a4005410300131804514019100590484010481c0c45c0c9908025803404103c9031008000a00241040c07190018009108000080496051110f04 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 551948561 1250 551947311 551947327
    0x30605060d02041103011e180213080303041a0709061b05010e0a05061b1c20040b0d140f040b0c13030303020a080601020705060a0e060f0307050c060a14010b 69
    0x1520701c801c1d096500800c2044610030003194440150428010012003070100d54110041c3d1117006900300644590090460316040b4900a500c060f40c0043c6070882c14641c60741c4001000001040610300941c030400000c10312030025411030320050b400501307040c10040313000e03020480caa0b000010303408030310000e8481d8401c10a46003051405001d0b02a0210018400c41c1040d50620801180041c005d01000c3c0a450440b5148090b0907018044d004405c0d1440017444850160700d40c0310b500550040150800d800034404201083c00a90341190b80201c018400008219000d2403031072040d8032116081c81500c107014207020205006034140144020034418031400401c01d084422020f8400d8541030500c2ca058180d242c2c680100a074000300c602d0808a41c0d4880841d07400c4d0300225000055544c042c0050b401d0480c021070442d002e00542415a800c404100710b41e0758144c50000095200f0b00954542e15528418440c40390303d04403004150111281c0b600310001e00717885490300e600b8111440d800006442e1001 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 551949811 1250 551948561 551948569
    0x4050408040509160e0a1404050702010b0402031e0f01140d08071b031e120f050903030a180b0711060309032710051e0c0703080c01060f120302060103060506 69
    0x3140c1142c1d6120380020208040c0d81148031840000950541c0c5841c1c090b0030900501c4404007407402951034500c2110158a202d040a07404154007000c0d510000c200070ba07174400030038200d038402d03900f804440c2405030620702511800c40c00c094104c84076204a48840d850100d00175036012148510714810090426440c2c24010710301d090ba806550406800540925100904220508988412102e00300c1c10015505415202550442240e40103d4004280d10101c0821a0340c0c01d400c101f4002840001c4c404014151402c1016001a40494550345d40d092800d0280390444401640303c00c419601c10000580010002100801c8404095404945a0312103000c0b4500b9405074003800a900d83d2242004151060308031030344101d45c0c4064a414841e084e50103011201c81c0314401d2124400c007050300c6000200780d040703002444080c1921080d1108103440b9551481135a220000d011a940c0d110f5a09104401101102000800e100100d00c0b1940e040e55402035260b00c0f0500c4043c02da96500e20005070151a = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 551951061 1250 551949811 551949817
    0x8060a030602071505070804140d0e040b040608060903040f0f1d04033501050411071202070509040302010c0219020d030c11041e05131a070c0804080102030a2904050408 74
    0x10484005e1020745400d850042440c2800c5500b81c1d040040c0c0c24424048000110709584204c0042c0e446000e182c00c00c0c030500000d003200c0390560343c2150307489000069415051018900440b68140515680e5251620708652216581c00040111041100030084180100d0b1096422500300d0000f03582a41c450030240c80300c0c48080880c200d451184c00c200030380c840041c1c40c50b4031030015043e00c040550340c0341c3d4207000441d40d01011510620108108810124110240f54840118248101c036006070301e41012405e9010140c0d02100940c0d190b0341c0c403e2803030781c040c4a0108219200c039401c1c901101690001104018270140240c140880c000d401e20034820740040540086002400c00c0c02584061b06450038845d490145ca603c3e024604004036095200e4040000066034200103e25440c000d402c0040c603c180000d00002e05210710b00c0c41301e400249018000e0401081c0c1d00000586034500704a9050940d05941102c0b040120085114110200ba003041c03940700c41e2042d140013640355a0707443d001c2001d01c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 551952311 1250 551951061 551951093
    0x310020711150d0504061404140d0305151207031a0405070e0709090b040b03030f040602190f08030916090e15190b010e031603020111031206010509010e1908010c08060a03060207 78
    0xc00590412040c8103c2c032942c0c02701801c1020803a12801000b86d4202e0403a0000da84030300f41a600209860755030b00d0b040090761a0001500141ca910560366510000305010225003030181500b1142008140f002c00c0c400d804c004d00500074512142c5c90302c204010503c090a005010b0803d6641c0c8500149031901d1340904504240501101d60b200484d01034104150000e209800051242110b850740ba0203031250078100140d4404020700f4400d2403540c4182c404d42004080810707a10400500d0382054103401c00e078000420b0400d100185400f1420031050928841200150281b00030109011303451013407004002d08075030f0b000f10003c1c2034896480100d402800d4544226450f02c14003441c4a001c04031500034108036803007600d800ca07805c0d00c0107845d603840c0e00801078440740c4810500009065540038030003c14419005241459400e0f03148000100051030f50400c00141c820401c0060024000c244208580d403003080c100b0100310300e894000560b8140c00c42c0001090207402040c1c25013044804a2040450 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 551953561 1250 551952311 551952341
    0x9060e060a06080705030c0612070203070c15030b1f0e06070804140901080a110f130507090305010c0c020a170f03031303031808070605150310020711150d050406 71
    0x281049000c1c0700c06800b040c028203000d0b015410001480d8070300080c21001300003028100701c1c00c0c208007005d01d14400c84000d1483c000e501040003004001021540d8000140450894035103160041e10802401c583d6003080217400f030382645407111031020814000c9070700c24031184ad0141011004a001c24a14000c00d04000d0a148002c00c01041c03107003440c0040645281c0503261860180e03612042c0d550382c1c0c88103100281041382c401c02515010304001c0c0c00860350381c80c0900303142191007100c060311088450807903600c0e0029900350010b00400201380203c5540003914a03010010b0102900041c41c85050b9114001d020803109060801129041c0807000060002c841501d48a19211032501c0c400305848000310002450a4101440108071128460116812104690400c0010b40c1c0f210700515015000d551000109284850b280e5410000301c17030282c84d00727440542c6a8549103800d9850042d1048081d10484902810554042001d01a10802d00c41804007040d01c1c0c5450400c1e000414034040500d4039 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 551954811 1250 551953561 551953573
    0x1204030807060c261503030405060f180a030b06030607091409061c0c060e01082e0905010902040918080a0c1a010617070f050a0c0c0e070305040b0a140a09060e 70
    0x10211641d030690320881c0e0240c5c41d4000580c0100130140c80e8420b900800c1e600a1041c8400f002c50054172000d02050120412200a1b00b03000e500051250740860340120303034080304101000001c3c1800e0003010340055050410264441c1400d2800c0006207040c0740e06070041091000180c2e013a904d00e2017010544188994a441d440e41ea401c14503541d0740c1c18012140480e078000c02c41c410075442500e1540c8100d610403070200d0741d0400c0384201c41c12001998807c010a641c81080030580802d544100fa008158103100140c0c0d503881c14018009a551001d85001d400d45014400b0b80480c185000b01c1d60701925929080c03503030344218903141400081102010800681140011a50541122201d80e0001c00420108606d6852601c00c89810424260b03d000054050202c042e106002e0b014908501c0e100c2c0344000c8082d6200c1100c1c5201210490729000009e403900240000c1c00b90300c19045420400c03100b0700348901d51004a4036441248041c1c5402000d940e100e07289818000d00345c6c4000102c41c040400c2d00e42c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 551956061 1250 551954811 551954867
    0xb0a0f12020d0b250206190509030c150a1d0a03030b010c063902210f120414060919080c0d02010b2809020d0e030c0f1204030807060c 59
    0x1040b0a44043c0a0091801024044c00824000601d2501ca04152601400041e103044640c0003e0070780506982551b1000740100b1101e5401032280403c80c8602c2c24001129283c80040e030f50076502a07116103940b2100a042c94484603e020980c00621074150070080f462604076030040f10072200000c8094026841c00c003d0301640c1c190184041441c548110000688040d02200413080100031450301002d42d004c80c0403501e0343c0c0c0040041c5446240c075880c40c00e040014100c854a0b50340d00204000b4080700006007000100b240031241000c550b001040100441c0c5030041c4a039030741d42e4021000244a100c410250801c1100312030444480020300c034140d40003800203007804ad019100001040340310380243c0461010300711000080603024250f8600c1105140d14000c44200250f014001d500e0b000350b103400c0303410b080c11000c000a250040440d0000c00d6204104994030707080c01010b40c03800ca1040c0c0d00b0401000402c48031000d0b10460790300440000360308140d005059070a4081940685482d001c000000c039 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 551957311 1250 551956061 551956081
    0x6030703020d0f0303050709080319030b0d0c03020a0e0702030a03051f141f050906070822061701060903150e0105180c04060e1f080604080a030b0a0f12020d0b 70
    0x20f450b00c40d450511168460b444152803daa01e40507800080d88140802d850140320203d2001d0002524100040c4051440c0c1c003060100700341c102c0580c2c4502c8102800c2003141010340b485030090404c940310701118101030f40029228402d40c219401090348030341c082000341140203510344c4102c489206440030666240d072140c0c090441140c500d440703a0740c1802d0a101c0c1a2144803003515225040d42e40500d0071a4031420008070346c02108090300c0c0d264003070201100c40480d80c807841425400c0c40400c1005240341c0503000344290140d80d0102010350340300c0d00401110350001401c4080d00d51008503c0e4020300c4081c44040107001070f60f44003004d50300308000d100b61810035103406011016400150780310703d81c040d028441580c0750341c4508003114130207100040b1000c1c42e03143d00d066112039003241e10000c00e64518a041c41d201e42603406850103000002c43c05045a0184103181c520314041c0d4071045101d1400c8544034481c2c12a110715034401000110311001c40d5142d00c3c08515a41d4080344400e52820140311107 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 551958561 1250 551957311 551957333
    0x3240301060e061f0e010518040e0c150702030a02010806041b0f0f0935010204030b1021080a091a040e0606070c150e0301020d0f050106111506030703020d 68
    0x43c41c0161108400b000c000b0b00a907854842000d0a615941003550995004441580c48441c03d004032071b54018201c03103980d41c2d40c0119031014002000808030743c3c91620811018110031001d0301c03403d42040002000688000c24440107080e02420010100c1e42c441e40814044c00040c0440081c41c0312103040e030007000f50400c460382c0b000c2600340c0d02c0c1c951203a0210300c240e4136141140180c50860b6882d01c4458070b003001c0f0041401c5404038030450054810444035035182a82c106400c211058040b000c10040c5070540c1074112801001e00260303207481c1650f213a0340c40c800c85004103030142880600080d0291024024000500140310341c2d204100250380c0f104185440c0d03081790080016030714500f07020680f0391031300f1005c3d9041160004101800d407454800107a0100550045840512080385d40341d580a68007803016210340d4840d5500071424407a554a4901100e034140c001809014210301613804800000545810130244080008055240d100001f458078030241e01c0251b0250b060a4840204504a004 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 551959811 1250 551958561 551958571
    0x150b030d090e0907140409050c030d05070b06041407080c09120a141c0c0201090902030f060a08010c0c0206090f09180601060c0f08031302060d0603051002090603240301060e 76
    0x7900b9541d40b10400b03255140e2031940700d0304183d01040041c06446242c20b5000020140c8268110380c1000c0d04600441d08105000c000f89022450100e401e10921003c403e5456010004031070030800041008940c1d6402d210250244080100b80d50018282c10151011243c80b45001022265150305031a03030b1541da25040102100c201a005000140d074140008040750010304002c070340900c4019841d411070b0403020086003a4108502c00400144102451009500541c507880859015140080c01d20480da16181d1107180141c0c0740010300303003885502c0b030216100580c2c103c0e003181c2d0300d0303c0c0f2000254803000d8502d06140d03c106a40705109180c0340080d2003200c89001e00c402d8414603030b40c030042036900084490002e0080140940d894001036588801954002d100c001c520300001d0040d0003103603254201100d608880ca0f9901424014054100100100714590320002d51420100d040881d4942c000034268040d41c46020f20601c00f000d042250240c2400e030060001c2003480e0b0388044503601e411050394 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 551961061 1250 551959811 551959829
    0x4110c1009050d080901060f0611241f15030516090f0510030e0703050d030f0b0609040e10020705030a08130f17040b040b0301060201060e1003150b030d09 68
    0x40110810314500031501d2080c0c10038050a041d01c04103400340c50b450001040f0a210b5503a13a00d01090342c0041c1110380d0050b0071181c0c0c404400d5000e15803118071701444650a40005405616030b80c61203024400b002e5030003403c00381069545940c100344000c5020694004080d60b400201440710801c0e07042c1d010900c200781c040c04501c0300345000340d420f940c0150140100e00411010f03560620041c2411504480101c2c031500e0f0000348500064502402e240454100f141c0941001884001e05a8103014654011561302c030f00f001843c1c446400148144a0000790354000d9486004c2c0c5071721ba1206103d08000281c002d0f80644d600d52540c80d00319240d42c401511000456820004161115100d0036018078059200c03407104081c030400d80301c5006905201198000f1820f0400010031302c82c01c0c003800b601c0202100d41c005034803075041c00e4010342910700c640c0101110b01612820001400c000201c1da01c110780c0c2101e000502c0c40401181034001d02040c6141e543c05119800a81410359844100c07801201c00c250 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 551962311 1250 551961061 551961073
    0x210b010b090f060307081b0c011506020706090803090f030a0515013212070b0a120b0f1509010201091a150f03030909100317190507080703050a03060504110c 69
    0x8810803c4600055507200006a04d0800041e01003440340030340180244485206420807a60a070028290707070310301c10214504060210104a00754042082d81d026049500b02024424240300f811962402081d410f20311480e40300c034018801e41c80522840c5022038100d025541001300203400154190310038880d00c2c05056040080a0604007411040c0035841c1e50002d40e078078003500280070090711411001da40c011500403200001041c0d04000028401000c0580b40d40080d122208020011640a42c28035800386180b0031034501107559038410307007040000c072145298551010302d0040b4010075224000034841c81240c1d418803500303481c06900303a205058044800c00710341840344c2030080c610f00040801c1e0300759000340303c810480c8ca031407400244e1140081050100e816503030389600000184035102e4182a040009200f002c4c01e40d82911040c1c2041c59040a518014242c4d403000124801e0040c05030410002048005c0394604c030b030300064002c12005200307201d020349020000c222988402c6d54119940300e01 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 551963561 1250 551962311 551962339
    0xf060e0403180501050d0b0f130b0108011403030a12020c030a09030605090111030112081c0501030c080c06030a0b0111070314010b010315050411130305060403090618210b010b09 78
    0x50218030b0a036681a50b5284c203108244d07403410301405e4030b18015640000c024008401ca0345801d11000c0301060030000115144650300c0000d405002c0c180c000c9446803042c01d40c80364007610000101c910b00d084500d81080c0525001480030300038004c0c501401d03a0b9000c009004210150701842d00c801340ca00504007003041c0c0c0c07520303841c0741c1c202c66141c208140c03165018401040510610001c0150780c0340202e407914505200011903510007400d0159240301165a10014402d0181055110000e44000002003500720310303c0340003031898040101600c1e180358803481d200945900c580340c4d43c0c1c1c0c11034200c81210030058403840d010001014201c400012580307020f1603040203620038000c102c1c2d0095850099441d00e0304004c1072102030051440c1c009071100c0d04019010070100d0500c8440000c50007003001e000760382024600107100b17003916407042003044003255090b1801550403100318206d5000e8070701030300070340d0200c2110703410003200850181544540c180005150454030300200218901280e141c0713285002c0c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 551964811 1250 551963561 551963597
    0x13080105071725030f061823010b0304120e0303070302101a010e100e13060303020706031a0909100905030309060903040b03040f1e1a06012307060f060e0403 69
    0x206144140c01008003c0b520103145000358045003040380fa61300045111921044526100790001081c040344681d9008401076001409821700c0c003803043d500102ca45945042c402c40c2d00c0f0300016001610468030301500741545800b0f40d9072b00c840711a01405413a110107a5050181d2142c5ca80410300d083d6900f040390010071038584420448003640d058480303004c0d13510600c040c0901d42c0040c3d40c203101400741c0300341a00d8113951280c0c44041112084c06000c240e40381103140081c00c00c0c00d9540100e003414141740040e00c40011040f0036401105040e01d5101d200d945200541d881c1c500c404a8800f801d0346400c030640c0c02c0c810301100a504c1480352000310b42c05619490a60b95507845a0b1050588606c0d0900214001170510410700d54094010009400102158000007071003844004048030a031501b560004140210034040d154044000d09055a000202d2144c1e54039961101c0e000c1d04240d0400103510041101c1a8400e0318022500141000b0305a2200e2420b50804c0003a2802e80c0031074801c3c189904581d030 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 551966061 1250 551964811 551964841
    0x5070509010602100e150903041802030c030414011e0e0f06010308030c1303020312040e071409010e0d060f0504020a15020d051b0109080301050a140a0308130801050717 74
    0x46980140700c2190420040ca0081c081541512041d01440c80c8204880c040c03081074074047c1d24020b000e16581c0c0e01e8900e00c40000013000f80340300400c9006000f0004244071080980e58401d030020850003440014180d051300408022000c241905c405006c4500f031000941c1c4441a0640c3ca00110f0f509059142203c0b0703a0742501b40b0009010010030800101d04406a901510210888844030080fa607243d500090031321012404041d043c03500400c08111841c071000050b07800000b00c0c06d0003032920510803020809480307003d9090381840020180742c141920341442c1e00e000344c0d0b042071040000e00d00300b00c00103003c0c0074155016445506212404a030b2032880544542c2140142e400901d0a441c0645059800e40c1020302018100355281e040103032603100c00c0c051a00180c0c030804169940390b040900b080301c01d28003a044284c40145880c80d1101944801480100381c17074200c8482030300c5080326509031000340c4158006a10650a0400303100070726030416900c9491307080d0300c1004070099607000040c0076211 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 551967311 1250 551966061 551966069
    0x240209030a0f020114030a0f1107050a021504170c040608061504110904091203060801140c0d0603050a1523040b060a0801110405130c201603050a0507050901 69
    0x203001101d4080015a10584141c406031040c103007843c40b00031490020545030070440d80c0b41c0d40d05846c0c8805402d00c0e80c0030300ca0150403088401030a42824020b4403a250b80e8810448000e00403010490320506800380c80c020380340202411b41c501000034240308101b03516203556403089401142481e01c04035003083c0104204e445021070b03920494100030540100009844d114041c40380e0b070541000340031429101ca01920785802d014406000036429002002000c40e485980042c00992526042c0d08446e40c07078680950b000464540155180d52031014034000400d11503200410601c552141a010000c250542c0d64a042407080b0070440b410b03040c94180407804600c6094094094a84000340c00a40c40c01c0007250414030203003d00071101d86030300400e421940e28141180221101207400c01151401025800c01c1d403031007a0051002200000002e00703074410800c0000e00035408880c89194104040000707100407003034000d100081e141d580c2821f5803102d414a10580700750190910100e00c604212850350704075 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 551968561 1250 551967311 551967313
    0x607081b09130504030845120a0206070320041205100e1e0d050f0304080c01020a0f030b030114130305090a030b0f070e0d032a24020903 60
    0x600084221160580c841d2041e40d50090780c014401c420000c0611489208a00c80c4d20f42114500b482e030f10b4610444280d00b40400d021081c190300020442c90300540900d800c5001400068484090355414242040300d9003c082814020815500307143d8001a51405040e45450410001030402c16000002e600440c8680c007408080004100141d6841c030074a046a000b070041d903401303041200d00c400c25a2190303c0540c800e0ba0200b440c504190ba661011b00d91b03d8080c2070700038400002c0700400a003170390240780200a022680400000c00b80320300d0204039000d80d008130000b1960f034a141e800141c11012146031840c002441d1030520100c07801c0500c1000040413640c1640f2445a54038000801c580c100c07000d04404025040c0604009a10f07007030a039a0180d88103500700c1c40d07d8a0701007201b12200c000202039001300000002070300d4594540c2d4042180182e0145408860900d1050580403d4401048a01c0e4181c03105070300780003032100d412031550b22140304517400300c0901b00d410441e00c164001d10441c6981 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 551969811 1250 551968561 551968591
    0x70c18050411120c120102090a060203030906060108071202040e15031b0f010c020a030f051207030807080606190c1104060305070e090c100c05060a090b0414031b010905060708 77
    0x42c0346086881125800780d00c2c1e0841d0304034095400820380080824000e070070b0b00ea4010816075081c2c90040c3c0914050480f40c8011800c510784400d182c4e07515500500360905108103c00414280c0e40319065140e03429402000541d038403540c1d803c8880d400342046440308095078400000c2c0100b80780c085401c22008204c01400c0c3d651080c40800c1007444440100c5e541c0c14401801c0a040046e01c500710501c000310300600700c40003400650304109040034070075505456120010030442000940080c1410740044103823030b04040c640d03151004030b1054400e40c6071001c2d2010303807501403002c2c01c1c0c4e00c86501c914031403140d10219400c52100c0c040c0010395400340030041180d08510000d001001c102e410099001c1d20f40c00440d01030042540114041c0b860001010000850120314102841070411110341c100000c0041000051721f02c0d290380c124020301500092400542010070f05001800304103071406c10004041ca400402e1503c044580240000c2500300e40c0c50084070002201113001d0242540308580d00e14039880 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 551971061 1250 551969811 551969843
    0x30304060506010e030f0102070605070903020904060f02090603090a1203061d060a171b030604080a180f0b0903070e0c040b160c0f08100b01020c0f15070c180504 71
    0x1010309801440702d41004150390720702141d945d04204c4540c40f10222000103070f4600d110708110080c0c9000a004505100c0d02e100d0400041e2118141c0c44d6000742c101800103a03040c10b98003044040e100e003090702c80d444070020040c052803200208013010392030722804c501401509030301d00a8058500d5442024203607800c2100b2061509400c41c000d03980088000d015071031040c0c54a034007400740181c1c18010400c0b030b800b62251043c40b2949411200c080c20045004258a180c44c1c0e641d031200784a41d803400c0c02003012078890001012200e4801c440a070130b0340e075583c080c1d05840e10000704035074100886441c030900c00d1200000e0440b1b0b0140e2301d17038007a80c144102e4520b0700d400d0201c4444564450781c0302c000c4080543c2c40410124085c1d0349080044e24148014100f030b01d18102446180c8403004580e60881c0b460503c886050b40c1e0000360301ba1800b2000e9031a01c240c0004203001815041509100d1180700000280801c100401d0304038400c150354050103a60000001c2e605064101d60045400600484414124003 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 551972311 1250 551971061 551971073
    0x190501060e0f01060f02420f01060f0c020f0d1e050325050604020f030f0d02010605040f1b0e0f040515102a080c03070c051203181302040b0a11190203030304 69
    0x741403071f407491240007a01d507180180000b494400c0381c01c01c0b121800301d4014814175a000416400051040c0f81400d070b2195240c002624004004603900d21511100c0011010003174140e003400041004550400500446070900c0b94581c1d0003d01c01000b00f1854284034000c15240b0281c0d07002240c4c1203c0108210b503215805d01c10403030007048001d50315100d04031901141c64401c12002e00004000ea00100d0600d2600c0300380b00c1070741c440c1a40007401c80c0c10840d081000fa4180c1032545040703c200c0c50300262040102c0007084035414044917094016017040100318a11081c8600c04840b8a0305889071071806070080c1e0304a40281b003000c21038007001c4164003200320000c40d82800e04031090183c01e83e14584000000c100e0b141d41d0100c1002c07108a600201c0c00c0002d0714186c04021805448134002e5441c0c0103182c425403050b2800e07064a1442500002c10303800758640d4a0f419500907001c0c0d203100c1540c074601d980d000b400d800c0c4450100c4c1d2040c8182010040d16002c0c2c0311042c6813a03507010780150700f1a1110340e111 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 551973561 1250 551972311 551972383
    0x50c010513120609150b0108011512090804050d081305030703050a030e0301180b0912040f0314030c15010306050a110f072105070b0c0c190501060e0f01060f02 70
    0x689403e80c5a24040c1c0115511084105038403001348800514003218500240102c10141d10106400b0750b07062041803015046410500038100c00180021307401040e18105038140a1508461303040038185441404001c88100141280b80c0480e00103446d266a407000c041d6030f07a495010050580d006071402c0b01c002401425800b0704038a004001280a1913100c44000302034601080c281d800748108010700036040e4041c420b1807414084002c05520b403078100300303039904001c012b0300c00108018010400080e0244007802541e40360b800c42001d68601d80d440000f0680450028003041cbc440500c2c203804074031400503511400440c0d13001c105d003580c2821842040f2036215001000240d481d0503401d4440c0e051451015040c00a000190b03d50f80d4440580d4217041c5501c0c040201550403801d810001c4034038094001420704505030321102a00c41c1c41d0f6852625074090310040d40000c810f58104000d018060882651482c1a0790b01070350380342000e03201c441c003ca0360b5402c5100c1003c0fa840942880c6180080110340c0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 551974811 1250 551973561 551973563
    0x108040606030516061107080d0c060608101d0601060c03050d0209120610050405060d06150e09010f0b06090a0e07110604050a02180106021c03061205010504050c01051312 75
    0x644542d41d40f2500d080c100c4664802d464621449810300120341c0009080079100080c400901906081ca07981c65690030480c0c0e03111040c410f0001d80c1a0030400350380c01000142040f8404d42e41000666500303003018080700e80c007005800502c41605100c508000075440d0407a221303655100d20700d164544090720180d0040100a00c3c6503000c21401201346c03036031030b1300780700a01c0500014070140c5000d0640342c1500103d50080c1d40303c1d07403c21042c444559101c0560100160b04079600156003094031000241030040b6a01c07a09600c451141000324111301944603592020a003142486012008001c018007441034000d4650f103c003150b2001d08c000d40e0105511a4020480c1c1452010300c0c1014082c186050780c11141162030f64001d1a1810441c2404d00b400c105e00e040507400c0c0b1842c2d5040400103034880c100c5105065803c50280036001d1028883d0300010b006041d140a01c00c050759940c20a00d000e4003003158150f581d88201700c043c11240d4824400ca8004412102e82114101d0070002107144032829000 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 551976061 1250 551974811 551974823
    0x2011b03050a26070801240804151d0c01090f06021b0a08121e160803130c090e060903030112140c061c0501060804020a120201110706050a120603050309010804 70
    0x24001000b12014000c030b5004001c1a00d543d0003a47c034141c294414000c844100355082d240c0c0600608407540c001044a0300709034084908000140b11075401c80042c40501e00c801c41c104050580b10042000c0890009001a82030780c0301e581c416141c800c843d514041c3ca22070600107920003070080103011071a40b0b103400a4a40200580800c40c1c0d1103403464a80072818185580684001500282c42c94014504100d500d40d200841030401107075405056820b64418000740201d000040004d400d281118810b554490340310b84040c00c943e40340d00000004240301c02074107080380b05200100b059042c002054904035108000d15034038041c4d2035a21a02c10410411291a00d0300c0ba20b2818600d40d601c0384081d112140099240150001848441d642641c2c010f030f0288081c4100c0704240030141e20740d9021003094481e1001858180b10091004845034400062242c60602886501089803503100d0001e11400ca82d50b900c14014000d240034820455560780b1005002c2c0c0e1041180e08441d5008000d21a84580150 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 551977311 1250 551976061 551976107
    0x40807020109030b180712080318030c01090f110915060c07150c0302060c2d120406050108010b061303030810150e01090603200903190f02011b03050a 66
    0x9501c0600020301aa170409400b036500034907000a6008104840c0188a400e0710300000640380e44404c500c91201503c16550b0800c407a00c0000c014008104851030fa00e01c49001f0007407050203040021090000042c11070f0212240000030045241840656011300e4520604040c0b6950b090100410390b40520100a41c900070641d00180038074441100102944071070300d90103d880f10030b140c02410540024a0380d00b01c82e000340603c5038081c0c0c421110040c10446405900d88000c4064001038032402000e000f80b080c00f2a4a04100070480720b600440d040b10507001c001c0c090b4044110810080d0300507001c40940b00241c0724000c04c04a1721490800741c001224001440301c0d1078550742100d104c01107451320240810390505200110f0359100c44c004004003601c3c541040900b80e100d0b40704001c072108042c0310841c14000b2451650030399003485100c4000c00300b00c4540a8041c0a1700e04050600c41980c0d05a011800e402600d1004c182200c1c0000001549903650a00c0d0021200060396000083e01040c1603400c045 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 551978417 1106 551977311 551977313
    0x108060a1515050d02040302060703090f0f0e040605060406030c0803280203070204090203011d060a0b0405071709120a02060906070e0604060318060c090305010506040605010804080702010903 84
    0x80e03d4000c1d503c45412405030041e003d5508003a600c00400960402090f03000040c0c00100c41614070f204a41300e50b18415102c0800d06031080c1800140d120f0001800031786254007856001c04020000180c4980340e484241ba140700641140000744d00000700e0390800e01403e801420140b0f42c0741084a0350b4510b10900a44030b0003030b10b4000340101e84403100002196029000749140100700340d0701c1e05020441c0b5203003680d100b0b0269501201540340c011a12110705040c041d9910590031038a800c0e888070000005080e03d25001441d65072103000758103590062901d148014000500030b0b80c010b04e4281442000300c0d04003000030b82020140a103443c140740c80794a822003034404444050400181110302440d10702c07003605550600900c00c0385881100f100721904880e8000c142d9010748001c00555541e4024001100c0a038040d4502003407240c40003070b0004002d84000c0094a1061604641480d1b407 = true := by decide +kernel

theorem cover : BRFrame.Cov 551798561 551978417 := by
  have h0 := BRFrame.cov_init 551798561
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551798561 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 551798561 ≤ n) (h2 : n < 551978417) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
