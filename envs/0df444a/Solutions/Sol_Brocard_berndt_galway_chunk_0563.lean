-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0563
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:27:56.543322+00:00
-- url     : https://prove2.me/submissions/2c34e52f-bc5f-46b0-b341-c56b29578a7d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 101079136 ≤ n < 101258992 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 101080386 1250 101079136 101079151
    0xf0908070c030c0503030403030509011b08031504050901090201050904110f071506150c15021905040e0a141503010624090e011409090127030e01140708030405010e06 73
    0x540c1c0910401c84404004005030030300b100111304092540e940140a0300c00c0c1076602c0d0400c04514544107180c5405c060100c00103a018000c15185d203441c84101c080c242d5a00c2d1014170440c144004558070940c10b2107500303c41501070750b41500d4081e40c2c000340406003458800b40011800c080014013076042c54480503041003403113186d4005a050407500444145c1d4455001800742c800c140381c200c403105400a480704c003855407044403100e0025144d62500024020b8007421060b405582c9240a91254030078000c1003a11807800100b107864842092540c200c5400308003a2003107041e0080495001489880c0c4800b010000074008207030700d6115010504012401115202117a40342407040100700c1e0444442c0015044c0030100041d50361420b80c1c00c04030200f40001d014090788a0b40c0200d00084402e41080c00c0b00c0054607810b007001c2e040c19904011280d85c000c010340002310a8010a05e9941c82203c2044564511080960074002e05440308075403030b400a48109d50a650f00c90b40e51034090300900066100e60423 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 101081636 1250 101080386 101080403
    0x8090f090f010801050705030606041e0911040602060109140105061b030403030305070e0103141f050d0506191503120c0204110901120b0306010b0703020a1e060b0301020702090a0f090807 82
    0x50000e42c0c3e82926005000401400010320800140b07844940a683c1102c2030840c0c0e03010f40204c114822100c00ea8141c00c00c69050f070400300040c43c410300010082040703c1c842e900720740aa0380d840c0c45803011280d440d002c0d4024072203c640100801c1c0f41580140440b0010204025004419085480e01e5640079510440100340c80c0d070100040190403c50152074007000782000d109401001c1d15001200e8002452035900e1562440d21287c0803501c0821036026000107000c41102d00d151303003089640c805017180d201030041500c513440c02800c020740c011280900826040c1c0601203065584400c6044030300d1500201704a03001c00e2440141e5a01d02075a503641401c4083d00d0b69030200c8034001001c061809520908103030a0110481890320005140d0341100d0400d1070003910f5041c1490120305000e4048406441c1519140d08600b6003090340c0c44d03c0c6031591003503008000300b02c0c40c041454240d0294800280d403040c04407002480012003070f080100c2952248a00007000100765555002a80140700305661828 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 101082886 1250 101081636 101081639
    0x21504120e090f0708100b03090115051804080f0705060703050106030c02030a0212031e0f060a0e0f0601030e1914060604090206041701060b0a1707091208090f090f01 73
    0x16000700d031400010409440e00c01552030020103c42040101400ca0010050350800217680f0700341c400289006400f152242c2c0d40d0f00d0a01e10b1010b800303800c0d00d0010181c0003102203000556454000e041d04d80701104403040741c1c80b40d59a0b4403a0311158101a0064101e50002c00540d0300007001400740c0c030311031407481c0c80020311541410002004c4440c49070b0351409544c42044800200f03500041d00302c08021084c070340380c0c0d603d981343e24086201d840348001074a401c42100742441480040080064407414064030b142d02c1e81c0390f072004038100150b400c0d500701d0320f140d00d4440482d505506c2508010364000d0b508080703c03281c410180b000d500e540e201003000d5a11901141802601031003c0c0540c81c0c000c0c3d001c807001d00c031034541c0fa00011903034425072084007210418103000e00b0507800d003904498005c084101c1c0540e2207500d010b4024140b101e005241d050900d08480004200c50b005d000c0f080b003a030b00106490040e4800315a40c0e40090b5016081c5950b1090b81400510f110380d4461206511030030300c0140d41802035 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 101084136 1250 101082886 101082923
    0x603020d05070e0a03020d020d0807030924080708040309050307081e010203040b06102a0b0906090c01030e0304090c170106050403030815010e180117010203010f03080901021504 78
    0x95801400b00c404102401c0d03054890b80d5188184002a82c1e011a009600803110b03200040301a0350200c001844c070b103c0403071540b0074150040110710031210f40301c00c8505880207000c81c0c1105c0d506640d01e8080031403031040210700010f20510140e64030501c03030f040562540341ca0714000703443c204880d0300043e1958400100700d0102100c80d140500419541d42c001c2d4150304043c1e4812140c0c0340c2c0101107038001e01103043d101071041e21481206118140c941c0c855014114144803105024a103041d06a5501106801284107030200058152107100110080c0401c8109400110042c1015a0900c001e6204c180000300d803200080c800c608000381c0d107803250042604842000e01112105038841e0b4240321041c001080400c1c0c001c0240307644030750040c0c24200309403603001c01651040345d034852854116039a840d04074405a407412407035050b101c140185401008000300030782e00341e00c403d024403035020003c950304100046030300b800340010080c140107540071981600c0040104500c1250140e8004400310882a4078 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 101085386 1250 101084136 101084141
    0xf01060905180102070510020a12050106020d030b03030910080c0d0e0105040215130306020d021606051801090510020a17070201150504090f0209060a080d05040503160f1e050a0603020d 81
    0xba1003012000350700f081800d80b03503a61100300b00ba01e0011031980002e52002d800f8410391b4084040000600e0421403540c49210081d60b0b0f00310340c2400d03004603103414628a240d00d1b0020540c2c11050f001000744400c0540007c0480701540081c2401803040018080d21010b21348901503040460f0071440006014076003401048100d420015542d9076152003044070349a0b8600003042c80d03050b01d40090700940c0c1c072401403030070750020721804001c1c02240c228421240104003050b00200c1c02240320140c40d20421300c064520130701300c0d0103d4000400030380c851400c3c00c016542503000790000140b1410040003152144c408402200411202e02d00103175940e80d25469030940f942c88110107803a00f9903007004041e0305690790440104030303090043c0c8501c0008000a14a9484200000141400b5425141b4030352004a016142c0d0300140242071007405160044007610004807600c004881380b050824040742e15000b85940c1c0b9070a80c00c0e801401e03ca104e00f010400307884210b6a80d004010540d001aa03030220488503404 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 101086636 1250 101085386 101085421
    0x1030911180f06150d0b0616030302130512190f0b1303031406010905040b0429091501141308030f0301060e22020d02090405040c080709050402010c03030b01020f01060905 75
    0x4a2030b10046803031004c40601040e90400000f8920000d00c00308400000307211740c00f0f62909201044244500c602c10181d240e0042c1c031000c0103103640a51066110020803c003d2885251001d00b039000110450b03030102244005541d05000755100030b5141d207540c5511105080440f005012100555005010140d051003607941d50030002d00c08924504140c0c000805501080c491940f1a9881e040d0130909039585a1020a42d400705c201c5031442030500e03441242e22840c2500c111407050782c7c1e0000190340d0103221440070b004998140d40d0034010309001400545d150300545a04800d0943d407500c08640c000040000b4629032082400c2030703480750314114004151180002c100c43c000c00703000500b6031350707500842e030b1807407462440c508003507101c14078054204003d00603005801d5000b41480309105c140032000d001107080d0781e085401e680700c0303a1316083c16100382d0f503098400a002a0340d6047c0b007000309209922016000c50148150b405080304144100d094401e40d403c181c450700da9030300901422001c078450301c52 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 101087886 1250 101086636 101086639
    0x50102120c1204230609250e0103020d080c01020a0518010e011719050112060b06030c12040f05060411120712060c020715111605030c01030911180f06 66
    0x40c600801c45858150300400a4801044d018260b0702c1d0040440004540644c100b03019000c6032081d01d8034800d25513072081e8040d405e40d074102c0d40400c1d81c4040a1a0301064055030740c0300d43c40300035a920b0350f402c0c444104900c907429510100144200c2c203803801c00780001e004900d525a1119103402c04100300030b24085070600110b042c099491084002640c101340d1004184545175000402680c0d50343c6001301001290b0840701400f880d00303001040e0203006c80075200c401800b0744005c21006140d0020322040d40f100395591604000300340119a410341002400560080c402d5451036003200319a5503c42c60a42c0544089079a03461031780150500d070600700c18050160200c0c0004000c0e80b480c0141000d0064500351002d0800c58481945ca045140204103500040001022180c141c44140794003d00c1110281c0051541d4000c131181051003842c4414142c064520040103801d1920034040190300030011000121000c143e980b800c40f2103030390741c0380500314202d0b0014002a1710b85001000445a8440180001d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 101089136 1250 101087886 101087911
    0x103060e06012c031516020610030615030b0a0f0e010204050105271c0c06020c101206090609020c1504082506020d0b030105060a0501020d21020705010212 68
    0x44116a0b01810542c210b01c65901609504a20303c510540c48104400c1c2c40b640501c41c1003042c1040c42c0120a84622440d006102203034007100c60002240c89040c02e90340c000e980182d1480034004a0910b0380041090702c1c254010340d0046030f0701d580f0420352034011616041c60b0b41c6d64607070107015040c680c010910511400c40c000c40c58141000c0000c2d04501810303a0070b54082100481ca510501703803c2c1040f08448100134091001e04001105803800c80a012404a07004034100b131000800d00c0c0001505c40e00f807003005050b50038211080c90119500000c0b4120449840d4550000180d04900cce446a280505180600542d0313502c2c540c80303100c0c6050100541a60003480306810800030542d04410b44400841610b103042c40400036000300c105480624038003400300d0b4030000e18040b5803440c0d03a008480c40c01c02a00280401d60b101010002c001e40e041c8142405030308843c4186101c40d103c0d445041889080156483c2c07806180d142920890704007001c00c0b10300341c0d40019070304a2a01000201a44850034180b01d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 101090386 1250 101089136 101089141
    0x311010e09070c05011404050102070515010305030304020904061805030d060b1e1b030c06070f0507020901060305090a08040326031003080306010e13050709050d0b131106070b04020103060e 83
    0x724245140003072200041042ca5603078031003081801e40004003084980418002a400c0504006000b5802020103d820344a0780f00000c088007041100303517040782d070042c003d182190780302d400388191480010030032100e242d606e0520f204070801c500241820107004400840c0c861400c940000110790494002200c9a181844554914a40f8002e050401c1000900c5262140112050301e01010f4080003048800e000114450084a034005501c1d84110700590390190340e1454404c050300d591107200d10180d04180c4a038010700005020ba00642c3d001700d0840103c90305c0030310b25140d00c4407a411a070800c50300d101c1d01a00d4103804881c41e08a032003100000700400c07499030403e141110301214483c800207207545008000145030f41e0180303110020f20315010b085904c020740365080201c003c1500721036420210b6090b00d8049560b00b0320610582d40707240c1c4444000f4841c0c64112408a2802d122007003240c00d42550b041140075a20741e140681140c0d841078000b088103040070b10014064038465000111610f03800402c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 101091636 1250 101090386 101090389
    0x5032205033f07060c09030b010b0c07060c0b0f07021c0305041403040f0e04080f03010305340509130c0321030207080f130f0b0d0b0a050a0515071b0311010e 69
    0x86a440a40c0540001a0000841c0d03046d0340b556103991029042401d4000009108422035004210100124098400c83c1e5240c7d0001d440c40511030b0341c0500000807000024510b034403ca03521039045412401162403030b07448001d00c0c2719540e07500c0c854000042d40700d009103c2044080704600007072005c800c01075824142010102085040c4600c06e0405201211011034103114140046511020825940950f01d43e113034200103550314515045500f0315800405112566494020110720060f4440030100720149400100a0390304400303000c07540c4041908112034001240a090400110311801428024503942c4103800050050010988241401000624006000781084840003601c5191058440015400070020306885400c100550208038401044115001d0090b000c4124400c40c14030160084800b409901c448602c12150003c2020740b0500040c80c065080341660f511480c5414207248154076211003522041c45202240840c201d4284113001d0b108840d51441070b02800c020580c0c608210 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 101092886 1250 101091636 101091763
    0x605070201020f0d0f050f1204060212100b090402091c0b0f0c04060909020f0c01090803060f06071203020f0d060909020a050d050d14070503041518030503220503 71
    0x125180f04006c00040d50110400c00d4005984c0048814000c2001d145002d2504900a5202c0402c0e0152035030150300250130540003031000020f550030391b0704190820200d00180000394212400265022090b1081c0d0708180006200044815000d00f042c1c045a0400d05e24810f101c02000e00212040c0e8070170002484000e801905520482d40c0030303013005035121405240401c15004074288170f600340d400e080c10070040c841750780d010b50700400049507407030000c0c0da085007002003911440714000c09001c1000a003c140b01d020754060441c1c1d810340c0d08441e02d01808200103108070381590708480307034040e501e0340708405509050703c400e00a044103070390303c02001d8610780300c81741d451044504a104004010810720b000c2006101591482e47d848812203441d1500c1d40e850321160013080002ca00000c1c20f110348980d41a400c4003c000480b40c020018602d4185100110000c0b00b070072003a12155407482240008664030200700c4c072108500d110401b240c1e00364948001800d01e00d08440702082090001c0007003410f604201c0c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 101094136 1250 101092886 101092907
    0x4050307020d1a091e0c0d0b0a09080c0304080709090515091207150507030606080a09020a12030305090f0c010905010c29090c0d0816020a0f0605070201020f0d 70
    0x441d64809041c40c20300e4180c0c01c04049240e032050020081c800c0c4041020300141001c1400b85042c0e0f032104451701e01c1c482940c0c80c4020101141d100c1d078104081000f28450031801070b0003402d03140e008101c0d0010780e140e64190741e00502d4046142d510016041004e1340003400004064510868140030401040d03c0390340e554540e01d18039282d00d03400c80e00443c104290411015005443c0020700780e0300e0f24000d0910210001d8202c81800b180f40c00c0c40006043c481c0701c0d202d1103050315155290648182c8a1043c010010224400100d800c43c400010116a400d00e171240c650004c0e120340d60200380791420148039810203010303581c8102c255000542d580b50b260303084080c1c081a148203183c40400d038000d9040029500444040a41d000070f168001070700042110340c5018490300c1700328101c2d052809000e00b88040300b0061403028001c210240004a20080c0d120320240381039000a2030200d5640e260580c2104c0400160b01140120f94009452411540c042c4055003885030508054008061702c10740c050000b0716903 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 101095386 1250 101094136 101094139
    0x15090402090a03020909010f0b06030103080a080702030706060b0910141c0902040f090311031305060706020705010e1e0304050306060d051e030304030314130311010b040f050609010e0405030702 85
    0x841c400c070041c0c0350984244015500140003da2030b060810255000b0100c00084c9014107041c8602d20819003081c00440341240d0380500e04514100011404a8143c0800b5040000314041000404003256480c05010007411428815a0380c42010300100700e10700c24241e00c45e00c140040c10300c4c05041038890405031542c6450710f03885141e400c1c90b00b981d2b0400400c0300d628000d40c0149030140401036510f4507481010024880e0301c80c1880c1c01d0368505115907a00601211280c0c40c000b800c0103228a04050018100140c81600c02509007801c0d9038455003034500030180c000b460303408911001d685605c100304440d61040400e01551502c1d08000c0801d80b281d030020410350003541c80d100c0000401904012078001c808060324203406444162010540781d9009450a900103400c0545144003100d080b42c050713015194484071888c40349040c1c1d034151032002410782d0501065503244815451619607000d1140100c40da111700180c0392030040d0810407a1038068110088581c00c00e410031001810000444290680 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 101096636 1250 101095386 101095391
    0x9010e0c040f0f0e01020c0606031902100c08030906060a0b09010c06020f040f03050f010b04051302010804080d060b071509150908070215070c090b0f01080901021306020714150904 79
    0x101030300040905203420f07000c3c80091a2500d01e00820702d041d03014100428802e002d44455446010805a545c1003030015149079407081040b207401468808551402099141070411b0080717010b40341c07000c003600304940a90068100400700702c203d207001840d0601410f1030a9090b410300b500c000000301300105940009000300d600003603103901100c132481690000c041c0740c2d0351101900c3d00c0e85450fa48500600c41303406415801c01d12039410615080c041c140c4500400c8030100055080d6400440709a90054008d5542c12003c1004825008550003604050461b681815903180620715200c25100142c4000301d080714541440d02c0000380050103216410110401e01160a16050074400e4040c4120a0020b50161031100310042150100024101260180010303c0071543d540d9035440070f980d1020700060340708018160590f41503005040b41d580018912000508000000310342c2d41840c0c0e62600001c015a005080401005c0c0078001c003950380c10010781b00c440040c0386011009040f4026288603a100e17a4 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 101097886 1250 101096636 101096651
    0x18030d0f020c25050108040b060402180a15021009050607200303040c030b1b04180209030a030504080607020309100c020429040e060c031f0807030c0e09010e0c04 71
    0x20294058482410030315040d60303403621450000c01000382d204154a8039808403400002030707541c026103200d0b11490300150501e230a0364400b000c000007075100609414109070b000000f940103884034881c0e807002d00342184865041d0840041c02a180200070044000168148000400050000b04189402c40840d040c85907003072840140000c01008568040c101520020040006002c408250754003200d0065200f40b4907074a420230021803a02c060005802d10f05d0042008000c05100d61152514011002400604002c4500d0009003007041035001034000540c0480c06020440c1d05010094100d11540002c40c078201280300880c2510359080008824825a0803607001951100d4020462641c403030b091154421000c000e82e00102c60700078078124010340c500b07140c0e091140800600c040c05841001c42d070030700356558002100c210270746040c4060400d50511500250402041016030043c51144862103101070800600c4030080400400c2e0300c003641c0c14189100c914400100d030914401c2c000b0f86021a404 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 101099136 1250 101097886 101097911
    0x4150504080a0507150e030a11010e1201060509060a03120e04020403120810060215010e04050c030703060b10080601120903140708130b0702011215030803040503070201020618030d 79
    0x24000c650021509000d401c000b10108072020a424007a12007842000001c03195a030300c21610116220713030480e0035a0110440c3d50100d80030310748c1040009814980042d614030038101052404e07c2c2125040c40c00d039102d15042c48a898801621a0301160036a400040d651854807080240c0c98240c6901060202e0203a20301459100c0d50100d03009142c00c281b81606001043c080102081403c0b00c40c000320720074440001c12038038404600ba6440280506007007d00c2c0e4284200c80a1189015104989910a4543e031442a4a0900803d002103002d107800041180810b802d2040740d44a5100c0c101c2005040c01c10040142e1f00b02100c40c14440105070005482950fa00d8113454020341030440315104480410f15400700a40c1d100100f070840400304e0002202990740b0880b0100340905d0a000340440c10900800601c51003561000d403a80b0041c11080036080d6807034640205540c020b841c140c9403500005506815960100141d80c2c001204c10f0202500306452080c15459020f035429590900b41c8400c002d0740c88 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 101100386 1250 101099136 101099147
    0x60807050f0318070504020a0e01080606040e04050a0c0b090a091e05100f0911030c0a09050a0308030402040b0114250b0c0a0f020d0c0206030606220503010f0207080415 74
    0x34042044a002e0340e80c184241c181a0090100d44882c40a11a480c40031425080c02e000391680c203002601d5400314400381c50300544141d0b20003041290803450a0000041004040c1a0b5a010ba03000f50007070000d003130b900d050483c0850455045180c0318101046501e442e030b160302c0d03a89c1d000c60b40301140005140d0703100510030905001c3d050541c03c803241028140a0210001038004003194203500b034003000241c3e41e098060a0b2429109241c0481b04240300194000204000810140016213015103807282c032400014547c1200b40c1086d01c0f1340d00080108021400c01303128030a14150242041101410202102035035445420101c0d140d010703d101d0101d500f80312034041000344503407144040782c107450075400e00c240d030743c1104c848000014200316a000c5c10a001080c825141d00c416521110051010303000d205a40c0e00c040c001d02d8020a00f0040b41104008a800700e401c20035400d10980b4031285440c0070142924801e0042c40c0c0407510410a010014900408a070700312608000064001011610107482 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 101101636 1250 101100386 101100397
    0xf0c240703090317010e01051207050d1e1407090f05100b0c0309060d02030a05010e040803010501031a060a090503120f0304020d05070e10090617030a18050d05011a010c02090106080705 81
    0x40c41a030b1304002140c2d0609081d1540d050300d81c1a203680e1b003021030348203510755107094a1140c41e4210201180d900003045c418015881c040c2c9071105400c244a006503215a0034903040d20242e80540c009607000d03c5203a40b280124401d1841140c418803581c04c0804089a01c80d0492080100e90fa1002a2141d0f201c03d0510a07205070800040103281c0320301140e1403010280d8821600d41d0509481e045c00429440d000c3c41d03038030380180d80024109003143e08200055004010fa60f001c000c41c460882502182a5100c20041101d00010f0703036804942c0341361505042c544004c6a001d40c61a807810703c00f1032185e148443c1501e50182c0c0440300c40c3d4040200741403e50801103550448401c0e40c1c030000030080900310741c558bca022a0072400c4108407043c0d43c1c0e100002c00c0c803020401c050050304200000c050b66481502c009280343c4185001001290303603180003907111041e000d000c54142e51a03c64207040d50b44c002000d0103c0c46001e003810300141c074913580040c001401c140112018807441c0070106249600c0340f010f545 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 101102886 1250 101101636 101101667
    0x60210050603120a020c040f020a020307140102070f050d17151905030303040f051606050f07030201110309070807090c050f030703090c120203010e01110324060f0c2407030903 77
    0x1c0d6944110f141c025140c005c00009071f07000e9400c00c03200449000441c821600c0780c41e07081d40a1030425446540c0d02c040113403061002a030545d0207110318004624504001c4149500c140000c08801c00e9811000c1c001c4001c0003110010464080100056480f1302814000e82603412103a4120610340040c0c00d40d5941c0ca50b800403901031001000300801c2200c241824402680110104d4902140d07850010040390403074002c1d0400a04144082101071010390043d20b08113220780004500d8079906001201a500100d8240c03009034008501003102c80c406111184c043d0603030001c11b11410500c030f000030740395100d5104c001c03015000000009041c144240e01014042e54000781c0b4400e030942d10342d0f0400f01c01044c9081130f486940781a2242035080b01c144104a103410648412300c1c1540c3e40c1d00d07501c20281010805c80743c03035103d11945038051562248001d00300060140c02181d1281c00c10010545440c000c081e201100890305c83c00102001281c1d45c2d12a40100181f9020544810b140f50446004e1025034840c2d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 101104136 1250 101102886 101102923
    0x101b050d0e030c3009010c0f0204110d0b03010504020a0608070225030308061e060906120a020c06280b010e100306030b060402040b03130f0209090f060f01060210050603 74
    0x81d001000110b01105000b08803504803420380041c880d849130503d041c011007071031000100842070762540580001c0080c240030701d0403d92044000c1d000f103000e0b02d45050200c802c80c407000442072000000c920a1240302801500208401e01c2c00383c1c01301d05d038458207002d010240899000006e0019100b0801800f40109020f200c0786041c61015203c00340209500046000c204503000051044c01c2c00e455030f4140b20012841c0d640720311080c1040c482580d01100125410850802c00080c00c2e50031030340514040c1d8110000142d5600600307159508201014141584080c07070424004490018061b4503241451613410004d0303245420b47c0142d64110040200540003e08000c0e000b005640591003038040300c3c020300008130140e86803000c100481c40343c0d0180b034052100071f1000c5060102c1d150402406288103c1008510440d1030700021081d10044071500465800a20040c1c94143c041c018030750440c1b16101c542e8919414500061744542008000781e0559568800250195904000030280d0507000182c0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 101105386 1250 101104136 101104147
    0x408090a0303020c041109010e01110f0703030804050706020606090a0c091814070302031003060213050603010b03150409020105030123120c09150d0206160203030f0a02101b050d0e03 80
    0x1e07481342c181c3e8401c1841645080080110a592042110b40345401691902040c1c5001da0040d41c0342240010610514851a00d4221844108002040207076001e80c40b61042894149441072404d55141c02410854000b9418800c1d1900d40c000d110b074001011840100d003481c03a5640407504a000b0354009034803032141003400c40d050402e50340101d044000d480740c0010365549104003581a403006803810700c0c0d8408850402c0001c0b4185501a00d44507915020401c50280d4440c0060990380007a08840500040041408030204180000d01c0032254103603002d1112083c0e5400103803d9000510070040c10a004544510400c4c141030900e074001e90300140201110000140d580f543c909860740034a0062030780002044926900b0410000c0c0040300410f9440c080f0080d500303214554000c1c4190f1050008030141c0140140e074244081c0003601c00707800e0000e0312003808140c024901401411550001d914000c44001d0070749424500202e5402e03103042c250b5444550940c0360009000800c1c04264038040401c0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 101106636 1250 101105386 101105393
    0x6070f0c03030f03050f2a04090903020309100306050d0816062a111b0105070f0510050a02090a091d07090c09080d1719020a080609220b0408090a03 65
    0x1150600301c0d43c00da4003000f990391894240361600606072480c000600004040304030000c1d003840d50f00c903c402810b86079400c090b0b44d40610002d5509429048026030008250316141382000d6040f02d0140b40c0501d0300303212030ad2910f4041955550071200140c0190340c0010040c0c1c00318400700300080b4007540401c04100128a4034031900ca1580b401c0c181c01580c0503110f0003e9040c5200700d2901d00c1e01d200100250001d6a40c09006848030001d110a95040c40760a0006034003041503108481d40040c080d0019200602114407010103c40c0020200d0940c0d44c810311420b045910b0302103140003a1510070400085150300c0380c42c08c11801c01401520103a5101d6154003040c582050b412243d071188840d10341001c1d0303940366a041c1d51111020740924002440c0d00c0b8040c0b000e82c00c200e1100340c01400c500c0c003588164070410302d00c00c203a0707200b224104049104142840060f0401c02d81495021401034002c01689100a030348160f501580640039141c0381c0303480f0228043c000e14108513840c1d240c0061410441d15500d14 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 101107886 1250 101106636 101106647
    0x10b0a120e1911040e060c0c0a0f060911120a060902010e1504030b06030d1b020f040501030b090706050c0d2105090a110405012607030c0906180207050601030206070f0c0303 76
    0x1110040103074a450540f81c1403a00440e401c0301074000c0039000540d81c0020ba0807140d040b110f100040da1040144040c0822401e0800d02441230085e50003040814480c1001181c21110001c800d010752500c0c0c140c6603600001007131f060341c0141e005001182c0da80f01400100c56032060b09001030351011248000200140b03590008204891140d940800b00da900c0604168407854107424100c0441c00e0300340c1c248025644498030055950ac01044030340f20440000200d01140c9098000700d82641c0444213000541e01d04200d42e00082009180c0380c3d242c0103610f40c20a4868124000700d50501c1040684000760140c1c09a03050040904a207040103a880c00d820f41581d2100e101400780c034150303002d8031107410301c2c1060f00686060f500044135201422075110814160003801e0402c0070315a0103090400700000d210b10800388001d000b0040045401428041c8160f041003007100d03150501407041110100048020558904594044820350744818490402c00c0000d0841c060042400090a9000c010540c101 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 101109136 1250 101107886 101107933
    0x5040204120302010e0a0308010308130803030a05010302030f0604120f020a0203250914070509190e07090506040f140604080f0102070b09031804051915150206010b0a120e 75
    0xaa0003031000c40c094041c05a04e5070801b07400039001500040c01800800c4a840043c181c40b005580c0b0030341c8885c3e88007503060854005407000055180c84600400a5290802004014139013030400303803002c1d0038a50b0700c8030640e12405016606021b040800d40c0446802480500000783e0058141c4820340c1021104528000035001055142072241d003000c0b580c4652489180f003050b075002c101030190348440c031003620309803c83c5425560000c0d0219400108806080c0c3c1040101202038070860107041085001e000d04903141c011a01441041c0020000320160a880d842119240c2d0060021902400e0100d07480e407260b504015014030072031401d112816015401808003034040c0205080c10b80314a110310340c81c1d104081c034808544100c2c0c50140001d00d0244d0295402c8002c10858184007400181040c0a0720340190003110740c921058020040c0f00106a50185458907900c040c0401d90b0505240d21124016100388000300180d241d6000810403030343d4818a0458034800454002e00c9140c280c40d001415030 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 101110386 1250 101109136 101109143
    0x40f09140106090e0d020c09060f040e060106081311040902030a0f03051306090501170709081006080c0901030b0f13060f050402030d05030c120603100e0d1b020607030c0501060504020412 82
    0x44c41c0641590b144c1c00705206000e16055405070a01e01001030800100e400c010385525800401401c1c0b0307903031590b40d03440b58058501c4584098201580340210142c0007604c001c0c0760744a0013040001c244002410181c00034484103040320300144450f09400424509001840d000f40030194003845c0749c051540010140120100c42c0302c825004589804088801307500e144500e902103402041004080307021800707660382c0284e00b0703c2c1021a080ea11041585480d050f0202e82c0091580ca0f5002d1118000038000380748506800d480c920749035459580c84198040c2d00510445001d000d0b800810114146240030960403608020b05002d984854078651005060a0324101d1113485540b2810103083c0c010f6003541c0c448e0a0102256040c1540c0b030311040500782000740811744c1401119292411003a6074480e80401400500c010f2800703000c200030280a1000d46c05620a84515000b41c0d003005942d002d0490b00803039810b1510344154801e40c0742180c0940581c0e00441ea0107800498046000c426094007196584e00 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 101111636 1250 101110386 101110391
    0x220204032907020c09070f031b05040524070308070302090a060e01112803020114040f0b09030310062f0606040c05040e0601030207080c07091505030c010806040f0914010609 76
    0xc5200d000e90350340c04d8810f06a42c11815100c0041c030454080c101e80d200b40642810040b50310040b21900c201d0300001c60080d6008143c001c1400d010758100b00b104090701c6007400188581c440b131504000d060301c1c00380c1c000040801c280640000c5009100c0d4050300c42610010300b501c802035454490140c50386500500b07039030000c0d030f8102ea103200c1c500c400501100d00c0e5080d04190403025031032100c050042140680d050707042d2b640b1000d036801c41040320001944500c0c00760105a031040d070342d4940400096400750000b6a9075000744107104521121100010449070b40b4108044c842c81d01580e0300c054a00074040c440b9986858104030601c40070301150032441107808403010030014440c000b0a07115401faa010b4003029043c00d00c0000c0255019900600440303001d20400382c00c000c407a900443c9020a2034200080b000e071a21000381944040c4000c0701d02800049010384070400c03240c40002e2001a0041a541c4900d45603988492208030641c00b80c40c5041d00500801c00d800032011007076010b00000d202e144407251 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 101112886 1250 101111636 101111641
    0x61918050a020702010e010f090b030c130503030408190c05090405011e1a060a051201060c05070501050702060702130b03070803090a0f083019080c0301052202040329 73
    0xc20b4800c5900790b036030586501c0d503210300480c0115194800c070961401404502d14001c0b91015200028600c10400012640e507282c55565041403400301d1039005500a034024442485030100120303000c203141c84418000071107000d15050500d03298040d035000a410507504000c0c4000e03c44103410a100c044c80b01306030003c0c140301e00041d060450740f01554000c485814035542221628000005240401161805038141b2520031003042c9102c8081c0d10440210703441c6080742040090511a01c4000e010908002c1c0c100344250300491a40d10690500034443c00d040b031640303d00c0003c1c0345c0c000a1540400340c120b4508680b14100c16a40764056203d0520817000741c0000a00748035644d10342001c1e14801405005850701040c0303422800b501c10b002c050000d40c85050500e030b1680c4440c0150000c1840c800c01203604076102c040207080b580e00644a0a40c0e042c2c108018440f41d11303200181c0d081910010800510001300000341c6000380030300d400051244c9404070110351003001d220400803513854503074250509034 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 101114136 1250 101112886 101112901
    0x30b1e040522030e19060c0b061005031302030f0715030b04090302150a06120b0f090d0503070e0a08032101151b060b090403020303090d0e0604030b06191805 69
    0x6195108000070b120859000501c00030340704030b0519000b180003030040700c890300e0000510200451582c10480c009420080b0780d030140b041caa00c6050308900140c42d01240c1d44c010b48001040751000a0101801004015201003191400c00068500c6104101070301c00031707901d50303152000b40c00da01d000d220000b038100000d00d401d910349445a000c0060745070700100b040381d003125615003d0340c00c02040b00b003e0690b5202d0014090512405001c1042d1148a01400900d046485103140c0d0385c2c043c202078030710b030701044850201a81110482303400400305d040c818820b610110000f8005185500120510701000c2031a00c81603581d50880c90010003100b0811950742c1e00d5a511842c0040403902910002d0603086401c0617140c0744041100340a80a020042904100100400d00c40401517500310016400041000307400007003030101601d030104a2910008101080000807214000c600000c1c000e034840c10003060b950b503906445031105502c00000c2c860302560310700303001151103010498608817605040001c1d100 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 101115386 1250 101114136 101114161
    0xd0c050913020406020d03180204150902030405070501030c0c120e06040801110405040b060c0706081005060712020c0d1a071803081207050901211e050105040b0306010f0603020a030b1e0405 83
    0x905448e00158104295140c00f04000351603081e000303a400c3e400c46000480c40f5055070004610441c020f400070500a442c1030b0005040316101d5200c02c080045100400001448a81038980c44001524041e61241d2514000034540c0c0310b981d20908281d2300e80700c07103603044e611000050300407110229020840d20116806100316485040902001c54104407000c0c01403500035605c043e0803844040d0743c428080d0315540458841e03480110305a80c2d0300ca90016035011680d040128180d2200d0036039110010400c1950b940f60180d0b184241c241d116221000081d145921566440951540088440034800d5590402c081103034010f10954072054480d20008944500603000c8511141040e940c100322062080d2460115444064412000070780b101841e01041c884002c1c1c9640949d21240d0000312545803404100c200ca08840da0300740aa0000801001004040b0b400030049a80301d013405a503d40818400300e000300b0310a071085038841c03040c425402c0f11040e547c5002041d05410740782001a500c1d80380d1403140 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 101116636 1250 101115386 101115401
    0x70501090b01060512160306090606050d0516140306040b0406031a012709060905030307120f0525020f0303010e0f09070b0a0302070302070b030405010207020a09110d0c050913020406020d03 83
    0xc00010f180003160506c2c14004040c03c1c0f841c00c0d4074000407002c2c0c552121509403800350b03000c600040c3c4042441d0045041c68810550011007401d07001d02c1030030000c039004c4d00c01040c03030861250122000c070002d4204e403240c1d0030409200e031009100b00322441c3c403807034040a46100c4034503040b00c0a05240000c220810f00035500050307007904011290300802c80d007190402800100f58100e510036101c101c6400083d41c2080a580a000b144c1c645a4003500c8501300760088034141410546410304040500c68140d00300c054100c8800440b0000b040030b408032483c1640340030384a03c0081154840040009040f441040c500c0d0700074422000e803400c840e2142d641301c035540d07040ca00441d0208401000f440d80c0980c0070342c0c0100001e40c400c3c01981c080c1a81c500c00d54403150411038003514030ba50000341420851609a01e81000b0f0891220100150150000500418010070001c1c1c4402399a0304020410390f80560203484801e040208807104071010056040302a401c82d2041034054451034103c00c3c500c2e030103806a02c0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 101117886 1250 101116636 101116657
    0xb15120103140a0203070b0a020a050d02010605030f070f05062d07060c02060702120c070512070302090603150c0d110c0114070c05031e0c0f0102090a060e03100b040b06070501090b010605 82
    0x21b01c4c0342454480b0301e00b41e024032600000c1d0710403070110f00700081e401e00842d841d0015136000081c1291524091500704900c4211040580c3c1068005001b0b14400d04a03042c2a02c0f41614100c0d20f0b0020028aa4155201ca0724608201d08c04101100c03038044514004040c040e01c500001d10900050790003d0360303102d1041d51808090707006400f11442051072000039005030340041c4201d402250342c0d0300c0843c0345c400c280c080c0b003e02c0340c1042e1800c1c8194103150002980100c016001090400b102e00046218404050140440300f0000501c20402c02080e4008804c48441d1503406a0340340454481c0500901400d1021000b400e54200011400c5c0d002c1c80d40380c188150448061407500840c41002c10040d6041e402401d68440140700c0305031002810040840061590000141d039840203000700640100d42e548180e0030007031044a40e1000e0b4401003109002142045404509281000700240103800313071442891704084003250000c14040305411100a4600074421448142d0f2170b40000c8030503114009450 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 101119136 1250 101117886 101117893
    0x50d050604021201020d06080f0601240e0301110a110105090f0a0b130b0403050d060b091302030a09021c03030b12031902070306050f0106030c0c0c05040b15120103140a0203 76
    0x140942000243c2001c000710034000186009107100c6008215041c503000b4840c03650101007501c0c0451810406e45000d098403030745505050510f60b118000303007014001c0403800c0006130401c4190a403800d40201e03625501c03003501d05443e5050200c00500c180f5480185c04a0b940c2454089004440c010804046214805025000c54142602c2d01408400054401c4545032070313004c510404280407000040c00f540c4a03554059552280c0000e010990303c040e04034180c0c222003000301d0f083c507507541c640504030309440100158603aa14020b0040c0101948140030750402000092941c4103582980c103c0ba000744261020031588401800380040c4409074810b160303555004001103c002500e0300c0c256402411680304851003140c403a981c0005482c0252241100c01070108014032516806004081d80e00031180b900e0020807142e919000e9006400d803046030301482c0d9a803180c444544030f28403504030007031401c01401d070398918160080030101000d00c81030312100001100c5a200c00030100306480b80c0d64005008 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 101120386 1250 101119136 101119141
    0xb090103020f09060c0f060a05160c060e070303020709060906051c02131a0a0b0a1403070908070b0301061403010308030705210907080c030106030305030a0b012307030306050d0506 79
    0x560096022156900d4901e60500c0711064941d035000040c084242e002010384150741c01c10b1b801d1841c0c504082c1a0310007483c03d243c204a80790b9000054682d048689250140103032000d818208018a520394010549004101e404030506800244942c222807014004010700350b070b518004411914a4010a5030181c02d42e8868620361030202078440d03005000030402950b404c030a51f440c038102c819061660120b19074500700a01c0903d080c5c4240c20042a0030720110303250107400da03002000001e036640e01342c141e04408008500d206100b014044050008207044490450b1a103c1070159900244901c80c00101c4075103000386101480800e49040381c2d40100403a00f0350300e8802064403031350010800a50a6041c0b40a05256080c0d034450041c0100c0ea114081c003295800c0c04003c90030900c0000105000c0c0e81803103400c1000a5010086952048003c0d600060701c03071080c8012a4000e008850303620749500000c05926841c0c1d0064020a09548652030801030950340d84140100701501c0c3c3d50150554104000 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 101121636 1250 101120386 101120389
    0x306060c110a080a061a010f0c0b04170409050103060f06030305161506090b0109060201021c0b1311040e0907050109030f0606170c0103110403020f060a030e01050c070218010b09 78
    0x11400414000410004460f0344821026140000200c2e0075103030742d612514007481c0107219011010801c0420f1030100821410f4110140c0004002040100552101c10000b0203200c02c104210214680c07216800350342c0c03507445445802420b0203000c1030351903a11b0440e210306030200c6803050108699140d11a81c0c20403010108801000c611614159842c1020120903c0e010f4410310420010744007001c800241c1c0350301100010010700c0b1341c0d04104190380c810015020000a004204a83c0315000e400c04a081c0b00c0c01d40109a03a8421000101d4000703003008640d003061505c0700050b20a9600503146450309aa4030720301c0542d10781c128400c00b8007149805a0074400b051500d44211541da0081c600865501d41d80c00348503501c1d409041030b40c1c00316049600710030103a681c14062082c400c490a000c031400c06042d0303000103c404403c07050b500e125010001d180381c0300b50300030b412503842100400002c2005150080000320350b03038030842c003c07840b030f080703085544041c25a003c00090685102000ca941003450344030 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 101122886 1250 101121636 101121653
    0x51005070b01122402040905011d0601030506130b0303070506091c05040e01030308061f080709140a3302010911040212160504030506040c140904050606060702120a1209060306060c 79
    0x403002d2100c5138007001b001c900c2c0d2880d802528002e044101c0e801c40c1c041a8080c13080304030100605150304140c1008113000c180d60790114081103600c10002c00042080300c050009185100d41c81006085002d82c0003000310800c40800c0e200038603111000e21910002c0381920845091166004007400406042c0050000c80e10403006184d106001601c0c030b80018120404607a00c0504840e220400101041c04110889ea845440c03c0028000300e4844030302c2e030358007000003a0190030500a500100036404900d41c104030f000903504c000d601100202c4080c181440e0002400b0745188035085c1c0d07000c501c1064a0210b82071a2085905412440d131024400b0340300c2c02200c2c19101044030316807041010900011003c29801d201c4036014500c00c25030501207030b24109007010307240c0c0c00600052080751802c0402001c20000b080c0254046030803241155a6071091000070510503012020070302e40c0c03050940c60700400003607540100000001c0c0c0c542c45501c0d45e80f10000c4055030784a02a1a0029240a80b03002c0094200c2 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 101124136 1250 101122886 101122943
    0x41a09090343140c010c02030312040f0c090b0901061d04050720030d150f0605090a03060204060302030a0b0405220623010303030e06010b04061107051005070b0112 72
    0x540c000c02d00c41454400c0026054000005071003111800406840702107041010007607007402803d0415510070103800107512030050801d00601003206000103030400c0780e050701c2881d140381e10128502c0c10503200c8030160700070040440024001c505800010602d1400b1b0411034136040c1d0b035102140c911000030010300000d040003901e18401d0200001701443d6002c5071003040740c6403860342002151110104036010041d07a25910100b030003041d1014040c04142100e900807816110b41c1e0403c2a581d16030314011500351225a44040d0455101080115000340d144d00118040c0f00c1d400030500000d40c018003008121002030303400328590b41d60b00d40300100b0506201c0b24144614000e074800942001411003281080c01040380c0035a2800716100103008054052050044015068008101c3c66040c058501c4084c0f1480c042c6500340500400040300790f5004008034809000e000e88106043c242c82c00000c0c100b030300404011504181484000302b40080c00b45d200c8d09007150000240e1502d80320020682050709080c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 101125386 1250 101124136 101124217
    0xb040506060712140d0b0102070506030105061902101401030b0708060a05220509010b0a080304030804120f0c080127170c100606050306090a021303150209041a090903 73
    0x120500c184c2d4203590084e2240080e80f46001c030301405514002400c010080d041144500d00610051103151540b5003560580e5030580960403050270103140603440c10402c910901040740c1400e513050144c41409031144d040f2882100501c2083d21100415182948200c03811500108a1481048903107460600541d00f0100c0030341d801020110301d0852025108204c8840420340c0d1100c8072003c00d030500d0840c01c0c0041020102440c01c0c2400d503651804244100e00c03c2c0c1540e0280701c1e02180510503182010303900b5079400071320021070070307a108481406801e1080c4041248071140c0c29207005041e00740140c010321607100d0b004e040981405000344146070029008000140314014503821040b4007841060094a22030f1500c075140e251000030000c4449004040b510317018014030803600390300c0500301c0c11029a68010104210003644a62400080c040c1522071507109041c00d20b40340750b28000ea4020305840c0c00c140c41ca0a00c0d51303a06807103a80d50f44520080d20034038070010f1840660141d2200e8961000001 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 101126636 1250 101125386 101125397
    0x32104030804120b0106050c0c090c0906180111010c020a02100e03062401031b0804151d010c0504030203070b090a090905031c270501061212030b040506060712 70
    0x1201d4407800c4603504641c1140000480e107281c403005112501c0e108a00618103407070110714200c0400b80301030300c92055070301c0903009031102408501900600d0060718440f47c80500700c81e80315090a009a0b50803030302400c2c268045481c0ca5121400514103000f10341490055800522408400d42e090120000c032600e440410011200c0c00c5142c250740030b004450040f10981481c980718030890304005038003150718030114185851706850280011030304020054840da1810190303016070311408c00440f001ca026101202d598503140d14000c011501c00c0154066525100c002c2101050452054a16214501010b58180d11585080140002520080c000f01310054006000160b036400304006950250380c048a06400200d03c0d116070950153f8100d01c4c1c0258200203010703580c0b042e0801000000d9416100b85541401c4d0702090030300600f500810b00422101030005d081c42c0050400550512039800c074040020b0501c00e02810070310746405020b028240003032207545080031981d200480310200d030035100d0a105 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 101127886 1250 101126636 101126639
    0xc0b0903090d0803070905041404020103180c0f060210050c03010b030a110d05240907050d02040e0f060907030c0f05070201020f01090b06030f061b03100305070909110f032104 77
    0x2112000541c02c0644240500c03900c81c149a413000d05034207100d0300400c1c0038914003045042815940e00240d42c0194080c00d002994034902803030b0150f4454000700c0648585644275000494900c14844001281e900703500762505001c081d2442804e80314103030340501000c4010f000600803d8400401150804a400c01c0080c0c00324100c02070b0169500044400145290b88004001501106441064550042c0d103241d8040c1440c0b200020b1036940041c00000c10082c000c510100801e00c20f50440300a0010251000007074503200c0c0041c54011001c4580c2805050301c8008100002e000740110200c20005488ec25242c460f2948111031581101905032b0462180c0c0e1f040d1100d5001c20700c10f002c10180522640c51943c40d00c18281450907081c000c03207490551118042122030401d4102411140c29030040035980d03074a400d89818403d03002600090400d001e850030001e40d0310101e50048882c20302c01c0901c501c0801c140b104122991042a03482038258204088080840c401d02c1d8602000c00c05214409051a = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 101129136 1250 101127886 101127889
    0x102120711030415020c010306150f08060111120a4e0f051008030406200a02031506010306050901030308060d03051e180d170c0a0f060c0f0f0c0b090309 67
    0x102a0413401c09a000103104222a507418041e01020b810744913042c0c0b10900b00c11070001c01c1e541c0050380c008100800440801d600b03a20680382000b03015541c0707040f100302c04101008500c031a40701d42004e8001c641c22071880b0b072a9058a04a841c150260b0444001008044652038060082680200c00e41c490f511071504c4c0341103806d4480c00305410160b0400066900e005081c02642402903046025aa84148010442c25a00041610718100a002881c415551007070849181a5103504000e40c180110310082e6007044110701900c0c0728a0003641e0a00805035200b083c488159001e00001e400652600f0020b00142400403104401034840d290545c900078032000703064809007560045ea41c143d400020744a18a014195410070b40340000c480d03d8495444580d2858100740348070a08055590022400281e543e006201000409400860421492202e49000e0004116081080c004511030002c580c845500c02c0b0040d069810740c1c0d40b248214100207895059181d00300405500080c44100070f440489e = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 101130386 1250 101129136 101129159
    0x402090a030f0c0609080d1107030512070c091802060a090e190f050903090d0609150608010c03091e06060312050c1902030a080919080c010e0301021207110304 70
    0xa60042601c0c2c0c8081d241072902c41ca248a00d81d01c0001001301d00041484500c602050010401c400c5003040c0501044004100b410031a50360300c0641340d4018aa60240c1c3e154100c002085490300c100720700f00043d500d851240c1d00f01c903184810764032480c000c0c2020000501f00400241903041541c2410000740d5951114040b480d5011203800c288240048155100008a8000c07032500e000b01460034002480d1200c2110381d03c1c01168009441509a0501c0c0400d211159111100d19600414525050140181107001500040c851981e2079840d003480c1c500d09034840d101d00145542d10043c0c41c3c46c181012400b19402202007002070f5022551040300000280290140320585401c40c0c44250716007050080302420600c00b01002c002c00301c58620b034400181e4010a6410704175a0000d001521526084c000c01c401d51070206a0056500c0d402d540490740090000c1c2010170340c402680d0381183d03450040240340c240e016024520002d24050000302e80329a00800e00160040c0d1540c040360f00b1700da90703894003014 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 101131636 1250 101130386 101130389
    0x70305070e0d0303021905030609060607020a030b070507140c090601030b03070b1206030c031b100e0409050a050606011b06020c0114042105040302010507142103150f06040909020402090a 82
    0x4c070313130300041c0140e0703252441c584402c0314050350a0080c150314201c0049091141c00408551141c00006484021592200000ca000c0c50b00702d5076800807894051000b0b86680e000d500c003929403440302c1c039600c401c000300092028001c0c0710141c448141502c9240040d405010724440e05c1d035040c0a500c4000c5040b28a103c094900c4125101081440b070a02c40145070401c440040414001d40190391000c03080c10a440c1c604046080c1903451000c0b0590a0320225030b00941c061500f64446d0a14410800f03110b0006087d1038045d004800f901c0e02600e42c0e81c01945c000510b50b440100c220303568812030300490100e901819100c00140004100941040781590750706400300c400301d5014005821140315101480c0c20a0b206811f542803191909056400103030060161140040c04090407030308508400c90213002c6a222901c0908441251150542c11001c6540085030320412003015080d02001920700440c001d90181c00103081c0c03a251a042811003c0a00303060300050303030899000c0100650341d40341c0000050 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 101132886 1250 101131636 101131643
    0x720030a031508010e0102210601080103030c020d0c0e040501050901021e07020406080d0804050c060901050f0304140d0504060215010f0302011103120c0403140a02012c0a0605090909010207050303070305070e0d 92
    0x11395440c0c1108e403006900c1d11a94011403445007242c1004900d980142c01c003810340ea0581469410080c00d8400518119003030300004100482d2010000340007401c83c1e41182c010b911443c000d10099850980396801c074000c01c106114403000c69000c100d42c40544400400358107002810104003a5180c8001d80e140c0082900d4420028036511704100a0240c203104034081c042c001c0303e24510740011400000d03c1070207003004204c030003c000004142003240c9524460041d05c04070050f5000e142100801400e642c11030b04c0b1381005409441000b040300b040158205041c0d40d074050101043e02c1c00d64004441081d54020000014031081002032042ca4580c203155116014003a90300355164210315091b485010344002162544e446150b0b00c0c0d00503a000a609403802e01001d4850020269060b400c000c0d42e03440c5031429422600480b00801e0301d50707101c0024583d41c0d0301516941041e845d003a550500302c0c401e050000c0c015801c00e2001c202d98900c40e40040350030070510302d800100e00e9183c200144512540312000c4 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 101134136 1250 101132886 101132891
    0x30b07110115061b200a0608070206190e0607020c180405061314010e0c0f040903081503010b1302130608010303090306150801020d0903020610030203060610030e03120720030a031508010e01 83
    0x880c6010705106c6d0181c945490300300800d0a02010207541e5001c0075102810440300c440ba0194403030190303885010814514000c6451740d0030b201c2c00103915009110340845c012115900b0a0800070b04120b8000d004541c820000c0903c0d50b90401c24018000b034036841212540b51110705240f03114401d0041d40c540507100406046401440802c00041d003e9403c03041c2c3c0102d040c0412480882d800410165000c281c5040d41a180200103000900410112000f10f6021a0481c00b181420300d00b5030240001108659842401c40e840f11800d441b4058240300003000079910b11410b00004100c2d40004004420803040300741482d0300c1300c9085085e41c100d4030010491030b60321a0a107003410750400c0b00e40d4010250b0084000e440b42150042600d9581c0141f01c02d025003501c07060303c01c0d01403180e0310140405590390262501e400c20f280010400c80000d071144000a00400c00c41c000d509002074220480d1007c4400461030310303050100550107011b940a03c480000d047c04c40004c1d080c8828010b01d5000003030344000 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 101135386 1250 101134136 101134193
    0x20705120d0801060305070f0c08041208030118110a0c0c0510020604050c120c01050903030d020c0618010c270806090f0111040602120711030106030b07110115061b 72
    0x20b0100c04164069003c040c244006c0c00401500100c1d9804444028603013090310680b1810030059500c0740342e000203131001d085480380041c0000c4502070740c140c680380314a946e0309007906d2010b1000e441c800030a000d07060004200324100c0300d01560b0900045442020307900d00344d543c2c50001882c0d50703101398180d10258018100704410000140069050000304035070804042e03580c1c8444690740c00e000c4803818148000002d204900303582c01c00a1352034810407248251b60b1500d90b0300b0000c0d16040182c0e14130226000314043c5c7c204801042c0554802541545e40e03402c2081c0360b14921440e944e40111080d10030b84c8000d5004034400500b440100d00ca421414014043c10300c0c840705d00d07400c43c1c1d070702c482107000301c44148414000240c0c0403a0a0b103045034410401c03603c840c540d0510810b8035000e00021607041d803078000000104191980b1252140b602c540b6540e4004c80688012401c0e6154120110a000740a0909200300c50045190080c138100300b5007501d004041030383e103110007951000513a64015412051 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 101136636 1250 101135386 101135413
    0x102010b03070e01060c05100507031b030b060d02180d0605010807061803080f0c030d0603060b0f0307030201030e0f07030b041e120311090603041515030c0e040302070512 75
    0x4030395458105500518805150100319203c0100600a90003042801103d01c0c09000c41005a00d6400600180400c007500b000034002e4010030a810704289690b03410001e203c46540248181d070110310000c1c2030b4520f4201c1400b0300e08000e504c615548602c4100012001c40d00382c0707841c164250f015109402c0012036504004100b40350a1140d40001c082220003041c6014041c440000c013001c4982c080c01e210740781d070b1580c24140c061740079001c0070300364600c40400d04d071544050319080801128080d440800ca450405400d0100030300440785000d07016848040e00308010f5100c0e038400d041100508003500e110305002e01e0309601b07000180d44161054096001440180850080890719180e55240f44d0301c01c01000795074070716070151100790800a02d59100d0042c1d00d0f070740d003030011110349010003007503a69249800d14141641201c24500101c2c01481c01d0000c0c009404000c11007001d5175000034842103070030b107020280302400400130001c80c11030090001c001015101d140e51442c0c43d603d8007015212500c000702 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 101137886 1250 101136636 101136641
    0x6050415050901091e020102010b03150708010f03110f060904090b09010c0c03021c120507080906060406082505060f040306111206011b12020307030201060806040506012c040b06010201 81
    0x140b800c44540d14005800340000c031804480305a40d1321a54503414010810700041c0d00400100301c41c00d40601400440c03a2101c4d8424846c10710a40d2252291080350b42c85900d0441c1c6151540001882c0354542e04120601340740070a150200090001c0444d49815a01c0300420705940700c5c5070049030b1060310300c0140140e400082c082d2010703001c3c10f440d0020100100342c900941c0d13003012144d600c1c6e0040781400402c042074818a51082d0041d58201c0c103000c1414800f100900d4098202e440c11801c0c01000041400d52419000f11400c8482c1007006110700c00c140c11064002c4c180a40761b10b0159210040d0024950729a103000e00040d100030316260783c03a00d123142803000903a504092000c0010508001011201c9400991303d90060400e00c0c055041c0382330203a080d81400d0844d00040d10700300b00040c0c9001d00c03645c000300400b56903120381c0c0240b161541ea22020707640d500701650000c2103600003000600c081c030391304800f40c89000f851480541e031250055640d1176070700304141d800382c0f110880002001460b58090 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 101139136 1250 101137886 101137891
    0x50109051302060c100207030c020301050f070f0f05040f06020606090708090709050402060d050108010510050607080a0f02100513111804030e03010605030105090a02240f090406030605041505 84
    0x5000e004600d00405000d401d4061401c00910420740400e09030a81c80c030410242564002607002190b4030119418007800b088540c0d6400c0340700b5070a250020f59030880c0aa0b81071702a20241c0c5900d00c0c1012041c0301035490403030854004003001000e0000107584020440c3d400010115500644141d0406400380814604000c10f03803010b1101d0881442003110b40090005d044031400c00e40042c50344c41d6480000e01034425910000d0181c0e050034004110414103600850090321390b00c100c81030599442c0184100c03802842000703801000184800d51903140907214101100c10342c0d00c107a500400ea03e1030f000f011184240c500341d0308000404000000c220f41c5446110440c182250708840c280c83c0f041000c90044030041001b4108100f036554030945480c25008a0b000e440003e000f808507203412511166034034900c0f58241d05c6003c29000800f844d58018200d1601c007540000c0d440c0ca44007030400c41d80340580c40b40044070340250b683c000000c049803103841420f00642c41030701100e40000400310383d841900c901 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 101140386 1250 101139136 101139149
    0x1309030801120309050f010c0b09011b170f10081204050f0111031804020c0f0a021503310b1303020f010203010f05040f0605040501170708063304110403060501 70
    0x3542ca0715000b0981001c003207003c0700d60494880d2600d501141c01280c42558140d80100980c01603414000740180642222107003101d240351030340130740404640448601c551994002400010a40801c1c050043c66824540c8011050005908195116000e0380351047c0102203400504003c50140b00621704035490300090308091a14021819143c42d02c00e841c2c3c801d8941d100c900e603034803540c0c0c0f400a480b00d40560b14800845420345802d01c87c00706030584c80d1b20740040100d2013142840c2400070010005015a07000d040c0c490750b44000303108041680b9000c02e012480d01050b10240d03d030300e100002e040903400d910a0341d00e401c10b2046000240f401a20380008048c0360340e2142d00600050000d041660301500480b5411a0302040801407109400e0081000e90001d54000e400c01d000820943d5410384503646000741302e011070b08401c0c1d50760a203d465010a54001e12900d0000c04c3d01c85220401075042401020380d0760143c40405001e500107001ca0303814a10704d10013114045030400074440c6074411140140700 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 101141636 1250 101140386 101140409
    0x7030512160807030b15040605040920161406041101021011191701080d11010c0e060d0b180a06090605030c04180b012405070b180a021309030801 64
    0x41c400c202401007000208030740c00f0180d45444040c3c4030b07542c0c81000e201c15004c0b100000c0d40c451316107400600960140c000d0414003400d055100c0c109850b03a04081040c03c4a00080504008a800380141c05d12407030181918002d03260f110610300580f0920065008902c02e442c1900010a507100180c18a8110300404244519203210001700010000407212561a18403804074848048a0251082c40742820b0414070140d4900021a960500103001c50190623251a00c52400c442c006241d42a682c008501d0b8001070b010a29034803e6003011805880c552001210100c0c00000901c0498800751900041059603211700c024090042001d122380006040c0200c41441514100b4010aa607894540111307400b4683d52030f51f10341a840c3d900d89c7c0c02c045a62001c1c10341c80b55607540081752010180b01c001501891035081c002c8448a01032000c4403001c0d68048900c034015611002241c40c0759024250141e25406880324650060791034110401e025184480300240c50807503414010310406058201030344000 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 101142886 1250 101141636 101141671
    0x130b031e0106020c0a0611030708030108010e1603120c0309080d0c0615030f02150c100f1109030604060509100903020a05010506010e030304030803070909060b07120905010504030807080f07030512 86
    0x44170411005d0a1b5405030a0000a4907a291199407a40c454040c02a0101e1030101c0080b0f03c031841908454401c140d4007080362030352208031401034038144240c84020301201c4420f00408034240241d05646101e406400c1174000d459480d0115410508020b00c1d00c4001076110350203208010307407840380e901c922801036500b40c0b03054116524050080b40044019115102040c0300144490410003150b002d2080c01c01501c0079412140b0340007018001d1a102c0c8a4000d00701649003101e10001c4064600c03200e4010014429900c07151949801400f000d0940f4030640520117050354006020300440300c0d903611907030080121140f2803d0860840b0700103000030741003040c1214a840d8654000060390143c032f070030544107503aa4441101c00d80c2c40c0340c4241e01007001141440000102200098040c01d15940110701300038a4440d00b210072500a8410300845003c140c1c05d0109102040400000d070a009106400300307032901d107545c50a4a915001060102c002400002c0c24081c0d200704040f0750783e0828004040e074001038 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 101144136 1250 101142886 101142889
    0x906050c030706020f09030d020a050c19090506041b120e0606090402060d06120c080115050604060f0215010e010302030f010504020d0209040303090c1509051c0305130b031e0106020c 80
    0x38400e004010f40300c42c0e004104150303c1c404d1902240c2a20360000c2c2101c10385007000801a4482209610654550241408030105400c103082072207500d0340c04008080100e41040200001840050102030704103994950600440580420302121901140c5950760050403009141c002e0340d014040c41019500450188000d50b00c3d50104644c000e64122181611644028038000007051107a220300ca4403000300c3c081c50148800c1507030590540300024004d001c0117070300441c4509002c40b144503481d0007440402c41000114410746905031710f1805841655001418581c11001e04c01017a0805299008180300400840c82c013042030001503030141c0c0c02804649095000180251003250003e4014040340300050109407090b0b001d6481a540010740706d02c1c0a88406401c1d040c0e400103404035010901011011a45203005040542e900c2c1200004020b01c1c2503e0b50210750b01c0d088000102e507000000d0318085003a105102c0918441c0300e0075000880600684c20748030014041c1a440340b03055401101166446 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 101145386 1250 101144136 101144143
    0x30b010902030415021615020901080103020112150e0720030703081b0d090213060806010320130207060609061d091c020309090f06011707020118050d0906050c 70
    0x1180c00c102001a00c2c0d56650404d09a880d240c1203076100d41e1480020b1b41c2e6540f561000203541c5942c010320f403442c071103110070412408902c541916a8085403125004000540c4a41070200410b841d002020501c0880325a4848420b0721540103c0f0421840f0000c12420341da200c5099060118980c2c144100d03440e4050b100f41c0c50b445112009010011030a00003404615a4119801c0000000b040f00e030359941e08840d0140200b01001c000c0b446a0300d00041d150101500f4060201541c40032005008039901c0e60b07841150382e148005420f0800280904280e0146e0f64081d03884000c10300c103000250b83c40701c50b85021003c990140e00700c100c515181c1502031240d004040150403040213568000c203141d894441040e440c1003984401e2a08000150100201c969030100207850451020b60713042231140c07601c0d5586102c621b42103c040d03002445044d81c891044c1c0d1a4031083e0b800c82528000003469904480c1a171030343c0301c5041e505444a510290312058a13a9102d04403a005240d50318003d4144104408150345 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 101146636 1250 101145386 101145389
    0x304030f0e010203090a0e0a0506091e06031903090f0b04060f0c0f12030e010605040905190c0e071d010201050c0405040905030409021b0712020109090e03120f010503070f030b01 78
    0x1c00c92040056145a40200115030000c01c008050700c40d95582c80c011840702c1c10003190080b050743d080c4408504241003444056004a0324640507841d0000c101d05e6000104074020000c40d45489051f024103c010341407004083d542d8025500d44c10054142541100c00d030750300f6888860904c01c10081040751030b40c4009162021002460714800d804a28204511240100312001d0651062400030b220455055401180c00f0340d001d50003440810b0b038030010070003122070811000e0099002580801201c1e020541071461851059034540c40039502c92030032101c00c2d1000c40e0003101041140c1400300c0c80c205110308601c101c010034030080c0480c1c50400c2298807140035500c90301d0301a9441d403401c00c0801a0a0003514050440040115124000600d041102c014a012820114010f42101040082c400c8800307403004d0b03406031a0000c00c68034080003e0000d11581c070381c540c8640814861000c2201404210900550740e0f09810030455051508241c204000c991082d00c014218400420016041c98041d60 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 101147886 1250 101146636 101146667
    0x706021504020d151d0a0206070609080f030108010504110f0307090f0225030e0d170310030204050403030e070602030a140901020106030f0f0b010909050c1003020f210705030403 78
    0x1806440710302c04200e4110035040018580d800015401001070025400f120094041c024218000218100703840d807a10841080a034200d0b81c10885000408e165402048629114000492408000501f004826002a0000c46859440d4014001400443e031104110380c03e0032907106403c0c1d405100060341d910703000d100c0d056040e030b00ca0b4000c0d6080842036050ba01101400c030082892205940080d107940255624111301154030b64080300d0b214244140b5000605e544162005401009a550b5039115040200300e2030700c1c0002c00c01c0c00b01c0140c489008450055210791804039025101004175401c010280d046401154014008201120740c40176604c58940758001c882540c034058440102d024059076000981046a4004d6000c20041d50300706d10b403141740c050410483c040c0d072180e0401e02500c006050140c810ba211206410040c071b052420348800c1c840504005181021004112159801070107150306042485c0a00307080010000560f02d512585514005280d40f610382c1c0e002e059000544001c1 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 101149136 1250 101147886 101147923
    0x5030a201c050c07061e02060609010306090609021e04051b07020108100506031e0709140108070c0b130c051005030f0714030c040810060b0409021606020301080a0201020f070602 78
    0x324801c1c0200b04a507407081c090340950f10425241e100143c91403201450382c407500d24140381707040320710b07480841c000f030283c600100305449991858070f82c2c80c050b21007444103035881c5030740d101601c006948404407c15424504c2c1200070400b00b12008020494400030600200c42486002c102c07a0460800220b401c09642420312450341d456010405010a02a81180340c2000000082c000e80c030b03144030400c00c40c03010841510442e40c0d0341c03114100c4817406548100408882c040c2e074003901943c00380d00300681c003900301d20302000040c015072a075170904442a28044050603240c0401c100b0300c14550508006044140d03503008003e2411000102207200c01080b0b00301948500000c078540c24801e01c4070200c54024600082e4481c1844241e050740c2c1c0d40684500030b0244034154a0f404030407410300541007101d0003224580d08092405585802944c0b000032181121751504c80340400280e83d510207103010b407801d0b0008140c10200b920000e40b40c00c800506010003540b06a01c100a02540062442049024413400 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 101150386 1250 101149136 101149183
    0xf060a0906022125050a0507030e04090602090406120c030b040503070b04030206060405090d08040b060a08150619180b0d051005040b070504031707021c05030a20 71
    0x10714000d001e448503020068191510303803c141203901c03500c1c034010045034011440400481d13108040b65004009a5008500b0500c40e1903c0700780107101410f181380c000c1c10f020054070407103800141115002c2404941c1258040390706425070a0074400c00c0d02800c4810f0078500e0b5a01242c40d0a45181d004d4440140381d80c1a05000070200030042c41690280e40d0b0110819030b031070416140203512034104498a5008901e0140040c9030807070002028404d0008507243d50a182e20ba60b150600d55034801402540c00a406542c00100c00c4002c1011814182e119030075007020b81400c40170400030345070301c1c0a04200d1a81e018000d03c0b00b812150b41024034178121103030008070942c50402040c0030b0807824101800c17078040e4942034440a40383d03400c4144500d21600e488501c0d99a408415070b803e024502000d02040751008549054240c47c0000b00080c0b40014203070358544144816005000c5002c0a00716619007000c1401d017241e40d00400400740300207a04051144030211001d0043d40e400640280305140d01c07a6821 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 101151636 1250 101150386 101150393
    0x15020613050309060a050306030c011e030e010e07091401050102060403121802090901020703020105011a0714070503060408040e0601091203050a0c0209090c031002041a0307140d0c030c020f060a09 86
    0x200c80d48902c0180c04071740c403920b00c40d00240558000302d80e058001c1c007410380c00e944950f2241403c00e851200614010a078003802140450052083d4465058150340e11010002c011004220340002401e40c45008201460a0b00c1d11008608061780302e24155800b40040c4400241c02c9032400e10880080c000005a0343c07549a87c0941d401a264000ba401408420910220728010740040001038001d40007401240d0b40ca6511446085d05101c0501048509000c2000041e49510340408080402000c41e03981c40e4a440001c4d050180035202140c5000e0700003010001b1170404465240c1c464800d09040392403528004014450054010000f020800300041c0708241a004038008201550003503c900080c3c035200b19a80d54421084840500c00e1103032044c8454400050b0007150155090200003440c100f460480f200c88940002d0203c20520110004401070503040c40080e02235126481c1d0040b441040c8888044d084a0b5080f2142d411908074800428500f1800180c041d0030505015001a00300181d08 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 101152886 1250 101151636 101151643
    0x141501050d0c05060403110415050f1306090e01051012080a030e0a0609050309040b1c02090c0d090b06010f0807020c09060406170102180604061e0c2103061502061305 73
    0x104860f90040c00400c0106c00e00901c1000100041400ea0341000ba516908100c9034413054580b04040d8007021000e94861141413581041c06200c9400401107040c685651a110a4941484001010ba075440e0100427134401603518000c018045125103043c0540681c5645020f8445d08401c1f03818140c40e01e64000c0d007804100004040d05400100400c04445245041a00d07548400c07025880380d1b082c8200701100340f0b4403221400d03ea01d9242010111000654280410550024880c401c109818003030003802020900980386a90301c55004814949401c4001600d5041c1c40743e55078080010342c0c0100005140c000608a00f0b00d8000c650070f07002940c50707200280203000d1541041614500c1c0c0c10f00d101c01080b054015288601c00c554141030340d1500c00f0280401c4d8040d500c1140c1c00124140860540d518241d4404250701e030b034500e000d500c1e010350790b11100c43c03c0c000f22030008030b000e48254120036070b10360510030140641008615008608032226000790b07203501c054002c00b885121300c8034810400070100b = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 101154136 1250 101152886 101152889
    0x8120901090803070606080d110703060b0103060e010308040504050f1509091204030c050a17070902030406090c0308032509061b170d110a050a03021305120109141501050d0c 76
    0x40c0300300c13035a48045140140213802a881a44907038421000e19000c01170054440c1c40c0d1400b81c100c0105103040c41c1d03449242c00750000c03c11290506503038a001180076402d032005a400303980105125956145400c081c04100d440040081d0b8034204008144850b600b0b8203141000c50317200c00c0341d0812140c2c403490700041c202000000d010100000010b4000100303d03482880c1421a0340031a40c1e4084183d0700d188241c04190b40404100712504018001d200c01a0329a02450f00240a4075001500480c10b80c0c5040705018690001d0391504004010440203000b01c45400f48a50800840207060002180000e00b0300c070f0703ca005d240280300e60300096a903003e620041003c811900110042c00d40101040303443c101d035102190303103040241840240c3c08201c41400c125149582103903112840d195020208400940001020400782a5824000506591140c2403107824400346000055560800d103002e42e26000c00c1c4407a1202504400310f100c1c0e204984c1c590b10350443d0416500045c08048500d03000c8500d401302e = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 101155386 1250 101154136 101154149
    0xe0103020d020d1a0703090614161101060f0308092d010e010c06060909021309080a050f09092e0b0a080705041518060e03070b0c01150b180a0812090109 67
    0x102410020707161b6043e0000b071800ca000340801c11042e54911520550000c04a501c5c20040d1707044014002054820411900c000182138000901151529210041100150f001750b500c00404218004245400c6c101c401d00140741ca05003481d540c0f2203444a000d481c403103e020300e0511840c5070b500003c40e40126900c400c2e141c0d115104224403600d40441000405650a007039000c1e6a8910328440b8800e11403260142c030a4116000c5824540c1c0607a00319030b0340d030004079400700b0b01c04240000d1619480f80c080607805500c0d06112410058807003030507410800109080e031350707015000711420420405030104a400129440c9001c8181e41c0d5040f109541031302c100d50005601c1c04030740000003070345507005180c54000d003458030301c0c1d940c0c0341d0341c41c8001c5800001c0120099415008074108108540c00c500041840400000c0042001880354406249000d026404601100000070b050100d4146842c21200032a204550702c926050070f001034165070304501d80000c40f01040010300102a41c1c05110401c0080c041c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 101156636 1250 101155386 101155433
    0xc0204020f3006030a0803010e060607150515040b0d0602031803040602010605011803120c0203010f0608030903010b010305010609090515300f0a0f0606080616090e0103020d020d 78
    0xc2c0380100e1944120b4505048242c0d01c040109034140b4011502140b501c2c1c00c444160304590a02d00b08501e0184050310150744800200000c4000035510343c841c940b40845064009401c0c6001031041c1c508030750340f400341482540303005000f01003551180f800c0700751982c000718016140c1e40c5050303a040c803e050a4281210030711000c6000900c3e07550541000c010b0321420785e07a80b44500070b07a40311050b11100a0000600245a103219610240c0c41780701d440c101980010004030300c1c02400791110086584a400c040082d401c00a030261060500340101180d4503028601004150f161000040840702c40340940d52800d038031640400c040d03859101c1010920180200b022586160120381b410301d10003040e004c120303081d05061040ca0329040200e41c80070454495000b400c0c0104403035603011850340c0801000c96090340e882c1070121b80c0140070001244160302c0f441c0c45030360403542100007912480641e80000850702403000140010380f643e012440d41280c1c1a9a540c0304403500e45003200c100003556000c07040c15130 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 101157886 1250 101156636 101156677
    0x60209040f0615021002120c0a031d0d020f03030708010b032d0601030f0c09060e0102070906030507170c10030e030d09030801090f020f070209060a2d08010c0c0204020f 74
    0x2180309003840b2400030540880390804145d441c01d000740e0181c4402c080e43c6040749800181000403100040400340501c4c500001c4c1c0007112419044808003000d5071285907400800f04a2019404001c19200d41c04a40c00440c10f61802c0c840091040105004d07108803030402001013a07054030f28550754440e400e81e03c0d44400600007901c900c3c2c4c1d000b0100300c4815002034140411340e04240c4552043c110f042c0c0c2c043d92050440741c1800001d40c3c5402100d99241d0452080803c006000700151294502442c85600a2301d001c0d498050021a1361404004550250300501110b161603900e11803800290001414042242400c40b03807010306601401100c40c000a0170481c3d10b01c00c0590000daa01c2c1070350100b880c100907402104614100724010350400c1d902601c020810600546070200c4981d0740700300001c091641e81621a00908010006589406241e07900e501d5042004120441d0440242821300001c121200c95081c00900318410640b010380190760004214102e5038004044420026808480f21a03030f6 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 101159136 1250 101157886 101157899
    0x9050109020d05060612010b03070c060203091b010f09060f0306150207080f0c0108150a030c08030711100806100306050a081b010905060409050907050d0308041b050d060209040f06 79
    0x29400030340c0d4400c25a1806000404c2d41c035110003900c0c008001d805001440da0700f07008007031602c0c2c0d0001c1c0481c070600c00107880c1c420010700e450005500c55080f00002e000c4220fa118038200e1440304600481e41800b000e4510180c016511410100881c0d80a19160181d440d14140981c0140b422b0b8000d00000103010f00320a0046800080c208100c5060400302d8500202c1c0700c000c2912103100f400500e0000b07201001141e15001c0d4034070720341299500100b070508020790fa565003160b0307103031290f00018a40e08003140c500309001a0039166000e01806031141c4940680c420720080c07807118020541e40c443c0900d8502c004200c1e2199010901400307000d01600700b00c81c2c449140c1c1e60360700c0c0810382110b08840e0b01d880706c00075944200f100c1030403500040e040e80e04003410041580040e04000303017440b20034400d032000043c0c195174100419000314060348480340c4600300b80c20904910741d000e40b0b00281000380f04e4020442c5850b44207204090f2038101d20010f885580c09400903018040144040090303508000e40810394 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 101160386 1250 101159136 101159141
    0xb120f0a0929010f0b040b030910090309170703030f0302030a0603060501080c120106060c120302120a0203040b070f020d110106120605011e03050705040b03030702120d0210090f140709050109 84
    0x4141000b10307901507030782d0340d110b00e220442990180040303541c0240800c12078107014001a58000013800c0648141c403d840c14017904883e64180140c0c000346c589a0100f00d081b01d41010701c400e0882550103096030601b543c40c003400000d5120040d00c02c05600100082001e01c09510000140d03500070f40a110a50f03440700c1039962400d421681601c6100040000e2800e01c0301446108206c0f01d10b0b44403110030034182e40315050078a01002d1000c040c941c0030403c00c0f100c0c90718541078911598040a0041c0c6906080c102000006402050340c414040d40d2000c0007036054001802c0304e000105443c0c0178000da540e07683c905002d0107440d4000507191981c00821410041c20390041750580314005040040d201d9041e070112600c280a1002410b0350704194000d00440c10a0341003030004074009012285002c80036400303c0e00e6a0440114040641c00906940d901140e05004445e41808010b0307050254072500d0300d5500380221090780061a645c040c3c03404070107480d41448030304000c4c460080100415a907941c83ca801 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 101161636 1250 101160386 101160443
    0x705090409150b03010b030613030c1e060b06090a23121b030a0c0302010f05040b070318060c020a0e0604110c07060f0903030c11030f0313030204060b120f0a09 70
    0x2c0c007a0030501d1040c0941014420303105840e800600625954035055018191421650b600760100100c0c48441d1010414070382d034280c01060112458009030101d410840c04403100940360707610810003080341150690740d000200b0256484c082ea0020442c240080d20600c560498091641200e26601030302da01400201d151810038a410803c40e00060300b4038101500d03005981e80092200709000c03400c1c0b0165108a6100e07482c8a4981000c501c0c140d01e0350503200c07540c0c000b40c0c41100000c0450004c58040d40e0304040f50001414141408440c0d06429400504914020700440c407009440c040020318030340e903a411010920b100c0214180e42c540300d000c4441d880310001e00512010403100424200014465041031f03003240d40540d03406260b001a903484243e01c2e81707078821503913151080420f41c1a0740750090006040342d55800d04000071492031441400188c0301190311022800005000c06581c82d06000c0b9281c1c3d000e1001f1030b450b005951003500340801440710b8035000d000010418964030b0800e0000d1142d49 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 101162886 1250 101161636 101161673
    0x260c1204050901090b01090308091801080a02041109010207140604030c030803010312050901050d050a1103070908150c07121209060204061b0503091210050702070614040b070b0705090409 82
    0xa82030f80c881320050195843c00540b6800180c0302c0b80100302050f0f0420182039071202c02402c1d400012445c000e40500d8050a8120840b00e4100340c8060b411407900384619600500d107502103d00305101d002c0081d4aa400921480000c40e905a00602895440c10200d502860b0b2110040504030b40340d04200226030400d01040f20000ea2100c056000310740070720141e030440c0c80140c1d283c03850003131030f240d660014180240c164070303a4a4861002e030f42c0148a01002e1446224280d803004003951506072164980959480d007503460f120307a8000d0154569500003107070040c0b900706032602040d0011140c204c96100790110745c2d8545624150111003088496001442101c6080e41c500e2080d01401c0000d580003150700c840106654401c20510030306041c4268410700c18014201503034181590b10030704800341c0d541220520016041007000303100c0a0340116840c1400c0b00303201c14035800d05082c061141c2241c8114080a070401a10301d00060308141704030202d130b0300410b01510038080300810b49072507a03e00140250f0308 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 101164136 1250 101162886 101162899
    0x602030108010e0f070e040f0224090109230907021905010c0314100e0c1b0102040303030507020f06150a030524010522050a020918061c260c120405 65
    0x4d40c11800144d88019501c0c441c4145405031910741c0c8904001c121440100e0700003200118002844080302c60035141d0341c030418a001d6131581c0240004102e080a0b8003c0708501007114903014080c03a141c03103102c451000aa403681819203880b41c09074a041d1103503900048408054440c60304020381904110040754054030140701031024150082ca400d4811105403040c541c00800070483c1103003801c074581d000050039224524006c02d5950883e1040c90564030504c103a074000408104140e40362013036660141c0d4620141c0044c126228186458880181a82880b540b60350781c0c1d200942d0321900114001c5501c03400b1940d49404031341e40c2036501c103164901d078500700103403034000502c505185981400c1000e80082501d00032002210910080c01d018000d1110309609019940d40c0c0d4582c0200c052403258500100c100619228040250802641e0042520780d0301c080344050000742044201001e0002c140c0e80b03003c0080c0ca0758014060341c052807400391240e104054505510704010b000800540320103aa10 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 101165386 1250 101164136 101164153
    0xa080d0c03030501060e061611130203010e0c1e09013c030c0507080d110318070b0f0306100221090114090f0d03031b05030a1a0a060f03090602030108010e 68
    0xd80b461020300a1b00754200d041040710301260800f103450717400c074a40701c0c5c0380502d0410710400100e401103000035080c801180d4000b005004803400c1d898510b90226009840c5441c100340105900082101c003450380c0d08500b004142c002d280da00580d051485103028281300310003481484a114543c9980c00d1000615605043e400c0718418824000c01018130207640741c480c030380442c03562050902d61103004058001d40d0343e041194041a4084001d5000703403940e1184504480356001c40c24240b6105610030024031404210070148c40d420701c0141d030780c412001c507a9000e08401b4240180c1c2045190b104010001c2d0803400030700d9011000b10090603800c1c80a0b61542140008101ca0b002d03103100700c402c081e0340542e00200c22140d6140198a0000503880391602080940a11410301c2036a61540c003840b0108002000308014a60756208442c00c0180c070000c10782c2402130f0724001c580d202d440c074044d00041001a25a00780954002d1300300518803640040115502c1d170b9182c1c00c950080c0010320660055010340ca44 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 101166636 1250 101165386 101165399
    0x9090c040b07031706040608121c0f200a0c020607050109050d0201240506070803061f020304050f0d1104020d09051b1503090309210f011a0402040f0909020a080d0c03030501 76
    0x294405623900c4500410310182c0d200f4503002d0540142501e641e000101d070300a0445580c5c40d0041c100c0c0150000c84c04101040f15040b1104070200c02c140180180000f4045411180e41c00032911400603015281c10b550780d295420524003406902c0c401504c103200710041c1516550f4150300c0f882501c0461000071542c1c8440ca0f0b03403c3d8610415108044d03101005000c0000850741d580d0013140c220303034006c0c5125442064184040b0300748041070b40e0a00560130201d810800307403e040b003407908010f0048481040c0d94081c0d6070740204070507c4100e41c0303020329408070f210b81409209502c01100030390013000b255031000f51b0504203040048104500c40c001d8803c0302848156581138000c1c0d90080e800d4101035814080404140542010580b045880e4102c1e440a00301c2c09001c140710074140a00348000102e0501040d0300d0b5101c400d16030800880c05144104820040030030140c0300a07040d10000c03240425140498000500c4810454100400c2c6005400d48002d10316004184858428465181070003143e1746d403103 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 101167886 1250 101166636 101166641
    0xf1103070c050c062b1d0706030501050f010c14070b12010306060504050c04061115010b09031c020a0803040c0b0f18010f090302060d0608010204080703110a0b09090c040b0703170604 80
    0x45200002000c07040e54070104003000c1642084440a50001480e0000003246d442c890742c5031920104243c02c90f030f0b400c1c0421076141c0503282c003401040c4da2500307030400c0020000708403c40019016050009202c1004043c8400744240001000700e0041c0781d40391405402544851002880b0840304a4030781a0001003038100740c05418401c088502c2c1141c1001d16100d02910742d4244405010b1315402800403180d8510840d6401d2801307031080d00c240d262508008000e042c90103010001a0141d50001d0600b403599a5001542d44880303980030200640340c0d2100e103000100b03004107801c101c102000229082044002410242059103090038145003115038030401910075075450415440064243e4005001500b0a14010310381281502000500e40c0d640b4021503007241c00a401501407500000030800600c0408180c001100300200d843c1ca1314245411140740c6203110703c0e00014040d1580340c1c005000850791005440007400201842a5101928a4024842841000181401404a13000c01c0c228241403 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 101169136 1250 101167886 101167897
    0xf06120803131403030c07050609060606031b09150c06070503060a060804021309120f020313140109080607020604030816080403030509030705010603080307021c0e040f1103070c050c06 81
    0x180201d29684654104140414184a0507a0b45003008403100202c000200010361240200c0b400c82c0b41c440b080c902d402d80c203000d4040e007a009264002810300240f0782c2e8440440e40c0040960220800000448034100d54502510361400e60100d14030105090516041c4003c0001408074002d40c4da00340d07904503050722a030106030ba5840e003214490b4070a016036800340c01c40540050000b02031802070f00e10719003004213a58590000315a00d1188a8141000a41080c20344200e6480c0303001844c2081141c0081c08480401803140b00405210003501c1811079006402d420702a00b21042a101a460500e002a40c0d41c00203660440c0001d02e02e0300040c0e00c640c54000001201500c659410429440360345089028140c09081e0b0481c03030208200350b10000d00244076500007144280c55041c1c0305e01c1d10900190070b1441d010810540c07002244460074080da0310000380b44070703801c0c01c60307000540c801c842da07149000b00511007410401410010034400300540115034800d07924820b100315050103038903a00f80319090086 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 101170386 1250 101169136 101169143
    0x3091e0909030507060203040c1404140f1b0c010b190605030f180a030e030607030e070b0f040320190807120609020603070c0606150f0302030711010f0f0612 69
    0x4009200c40c0c03059400c01c45015000f45001c0781048426194101240e0040d02c04a80300d20800504000c0c0f201103040440111504490420562001c074510040001c001000444603002e2040003845036500007056030a40007003030242c540c031840c1d1844028024907010024922840340d615401c05c181402c445c0c2801512140c0d6103c81c256100c60108040340d22024001c140ba4081c407541448896108201040ca100d009540d800040c0764120145814900c020b0820803c05003042c00418481038001604c40031600105000c1303565054240c0c1c43d90300c901442e04024202031641c9900010f00341c95860618020b0012182c2c12804099150807800310300300da201d80305154001345020485d40741c0380c51403104c07400e010741c0b80071030406415030009142d58012603204003c03851100204081c0038891050b0070280a01014402103001c003064003604407810640c1a90416800000190005204548824034146280b00070b02c106146801d1540141c262074220110081c41e200d80080d001d01100b001103003d503007 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 101171636 1250 101170386 101170439
    0x708060603010510030e0f10022104050a020d14010606080601110a0b0703090302010204031a040c171b030a05060f1608150f15030f040b090d08060405060411040e040309 74
    0x80064065002c2d240c146400c0140c0e00440c40300c5c248107c4144161114040403100060740c4500c00d15039590030002111606040306150b00800c0001580055080e610f1030301200c1610359901c00345808040c20104600040c1c1c00c2d400d041000484541122200d07003c1c0e8401d0b02d503003281a2045040d036650b290180f0005d04000a00004a80500d00941c00685900c1c02440094a0262030391030742051200c08a040c9502a02070404010612414440740c0c03014020b05090034000e101241c440d9075407030042c02c503004815a58002c1d030f01c12991301040740302505d96104054540d90714092014401c2d1550445170f580411110a21220721203204004d81d922424001900d2242900e190080c00601e14056182c543c10050581c0100c003441c4144003d18072a20f2212081103661901d890502103207240682000f01603842403868000b250f800c546442d61204050ba0001000c1e81c0381b02c00a400b8103001b00201d8901c21000902083c81d102c0001101e100728000d03102d12034100d5850302c0c4211588013110205100d802c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 101172886 1250 101171636 101171659
    0x1e0302040b0108151005040306090c091d031c021b0105040312020a080f0604200a0f0905060901080603120a0c02090609090d11011d0a03030608010510170a1a07080606030105 76
    0x3d40341c8117007504d54103246003490910b504c07039481404035907007072100359401c1c0c01ca28005c12550103a4010014980c0b90459003a5a4044540189a6074016200cd191080e24400e400b807091400d29410f80d1540d054442081c01c0c09041402554001d09068406030009042c6200302c4810b20803a000700d42c1c00c00055640d0b1442e80d600d48468406078103001d850190300c140c60702c071000c20500da602e114904c0c400d1500006642c400001c03001401520070800d6500500960010401c040e40d601d05c10b54801d55001e0070700f0301440c3c0d03c0c003000905202026004c410b00580c045941444160b0066100032800e20031b072000c1c19251140070030805c0e02070044902c1d203000e40c007080b92198028400d002440d002d103240000818441d00710445001c1036090342c040c1e0390070380d8042d01680080c10390500030400288141d400030800760504108001805109028034110079505a0803c02292400c0042c50415038010002044445a1105141c51280f0a89004001850140100b001d0f13180c2481220704841c0d0040001e640c0c0d0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 101174136 1250 101172886 101172889
    0xd1a0a0c0e0a21060504030f0f080f0109020a0207090c21050912070c0f0605031e060f06160f030806090109020a020307060b010c020d060509070b04080d03020c071e0302040b010815 79
    0x1219558240350007103c80500b002c0000c0711801001e000c0d905c03a4036903075124212030400030040c91075021403108001054042c0902900807803003060546c4c0c1c0004004d680d911010a02b41c2ca0600990f005903402032070301c851090700562051030440c0c042003444081c94501c41d8403800d10140d9500740c03541d041f9a08400e1083d1030035221030008001541c800e000c400c05080d071703628407007445411503844100450300010400002002e02c1100d401611300c40f1408007682e09001c030101e91035201748006280680000120401100802c02030f9101c0075130302460300040080b091030300038800d010a1720850b000d841c01c98000300b1403c3c118005e66060303100c16401142040342c19120b070f50140500940c2c00781070200d030000710f0740982c4409a0f040b801c0c9010707601c00320312400c1c0b40110500d045074a0f48201d02c458400d1000348803924010440c16200c2035145009611400490a29070500e1702d982c3c020602c4030700e209414010203c80e200c0040489000301c40400a00318010010340e1039501c00c6034800da03098084130400d8490b = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 101175386 1250 101174136 101174159
    0x807051905060a1806050d0e1c0e03120d020a2a0b04080c0d11060907060504090213080a1a0709120f0309090e010225030504060305060d1a0a0c0e0a 65
    0x2c10390920f060540034002c180400744480ca507420040000d82c000600014006282c003d058010000c60002d04880c1c02d0b101c9d00c0102688650749480404c00c00c0918400140c2e010006030549034078004500359a0000c17042c20303600944c00b500a80000c02e01e40f004000c07000d0b01c8c000c404001541c2c024855143c00d03a45544044070030380000c00484041da0140002402400c0800103611148042e4481082070100c40b80107500e400002070021801e50300240b0240045035100f4160340848038402c2002d40c4801c06148542400449a00500041d101e840d581d40203220000c4040c0e400503a151900c140540c846050844180e007082c01628400442088000001013000009042c1c142c005c0c41c01d200215100c0e0f8901d415602c00c600c00c102aa900450690700140785403080e8000100c00010301d0000c122117030703405030042c003884c41507900303141d5594009251515044911000d1710342c00b04a0700c40505101800c445010b5080c1c0710426002e2a08410ba4015809083d61180b603550003400c0303091682c80c20b55600d1a = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 101176636 1250 101175386 101175397
    0x10260912191202040b040b1c0e0c0405060301090501050f07110102090906060703020106030605130b130b060108040c05130f360602070606121203150e04050a050703030306080705190506 81
    0x100c02e40d00b0040004e0205110b00648060901200306603603078400d0813186030f58010380790b900c90051440c0c110342150309a4009920300a026041d107010078a99210710020780101804007000d046035003084100290941c81010b09440f98055882d040c000142503600c2c64201e01400c00016008407501c8042200b80c0f0f03054000e0b11413184a88000b140054490b6546030644800303460386071400e213540e4180c00c00c003c243c0b03441540c02007200d0001802100251a03952049401502441c1030005082c0490140084105400040c14016101e00b8081003080044001031181040d2156214a4071008084a00d14a82c9071201c5011003141c07400503c41c2203a40107049040c0181c102d4600d03500700003960004030300c0d000721001440322011111000036181446116804e40b030402c0740c105860200c1000d405242c0300381d0304040d01c4070052044001e079514600b051030b11800100250091003541c0c1c00008065140e000807003521422015130f0b050039601c02c140000c21411001c4100f081070405010306c01d60074903801034075 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 101177886 1250 101176636 101176667
    0x1a04030c12021f0906020106060201020f031b0403050703050303060f190504020c0c0301050a0e0c0109031505060f061306031802150a0e10031a0603040807021026091219 74
    0x9160100030900700c000ca4243c0200c00c0032440700360041100b590207124160041080d80000d515000d815200024503100c024800d4925a201c030543c0b50100010f41c0541d0040e41d40300c0c3c00c5a40c0384c1d480b1b0030a40d540c0e81080310114417a81104480390307030070b0401d1201416016a00809448141c1c104810840603400c8690071100d81e1065102076500ea9509000e424040c04004c880002c0e00d0cd50202581d09000c1c1d001130031811712000c440100001403180500550f00c8041040000e49a01e8110006001c010340c0a04503600c098003080c0120034072075404140b01100c1050320200044490201d0300440d036443c1500c042c0d80700141040292455170300000401c0725050902d0038844040e641c400042504d04180c1071900000d588021124190606101503903045008458503415403401c0d580e420309511810000900403c0108801c071600d034003600061403a1076040180c0c1400b5400e58080c080303480412184e600c0c25114503001c0e81c1c14070a0040c100c0e48680003107008030b0200d000c3c0305420349180e0509030703241 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 101179136 1250 101177886 101177899
    0xc030c0303022205040c031103010b13050603041506090b030a0b0619080607030c08060f01110a062306090705040618090c030c030e0111030a15030b0a05011a04030c1202 74
    0x400210780642200f244003600030004243d49081c042400101d40b6200c03074440a140c0790100212001c100700007035030b04558042040320381d02d044041e020710b0b02c0070340c0e64003894015401006010070490030752074801c01024920b204018a40e43d9a942c2c6007592124141d098040d0414184070010480305130318a580306d000581810106407107800d4a500104480d441000250044000d000d1180d9250190b08807400c0f40780303031580c0381c1d08008000070b1200340581d0003641488061400d5040c60403040c03001c102110341258081140100c8000c2411132900e050b603400c200c01026200040701440d00e0109140a01c2c6143e4038141054140002501c0900c1d01112204102442c65000900403c09008201480206540120b00c600d078071200507007607a1012603100b1080e418205c440b1821200d41d015030f03510641e803401c0402c0e01141e01034011000d40003600090b05003840081002500c443e20b42000e8101c942402c0d402402e19500102c44203940510b000c000c3c000c00c64280200940c00ca08042c0c4031400e03000a000 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 101180386 1250 101179136 101179147
    0x213050306010303030203060a0602010b0f060705211309060b1602030f0a111219240e0102030714030408040302091b030708060a0504090803130503090303031e01150c030c030302 78
    0x1e207490400d80c001ca000940000030401c0c142044640c810043c181c41c002030190b500340320005501d045000440c035000e0714000c0b40f00802d02c80304100080039102e40d9120080d1081050014200a9004101204c000381d00390b02c0014000305503100d940225041e4906149c103242e103007140c40c554034075084070a81c1d0604c1246281340342d01c40e051224606240c8298041c200010b41078092100e810095100d911040d0081180200300f0a1140820800309030300007101a51112030740c1115603120b940504105d21945044442c128442c0d0560095010741800d49070841c90b40b4290008071040c0c4070855006148840a01080006040c0010750a40241c2e200e0703c54034050040350400301081c2c204483c1800060722502c14002c05040984945026190940c0c003800790b82e803c1d40702c404451101412500c150b030b24404002003880410310a584c0c0c01d0384018266a5070742400c0c0d03007508130300c85030307566030b41c100d20500c000040c15480510350482d1030070310380d2504a91802a51020340303074140046801da0605408104 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 101181636 1250 101180386 101180389
    0xf06040f0f12110105060105090112090219030c26030f0901052106090916060c05030c030a1205070e01080106050313150204060809070f030f03140d0c0e03010b0112021305 75
    0x40b41e441c41610b5a0308180c0d00b1940c00e9107801d44001410017410301c4401c00290700c0f030741d07444120000004485c14010851483d42e1001c10124030321082c0448444852038404001c202481c1e0a51080310710038038042c1c1e0050303081c002100c4c014001c10b407121420f41c400c1085020050924014001c1c9046c141800c42c204540f030110498411082017142500d80d0280c02040480e2600c100c2254100406a00411410b94900803a050b041d5042c024041400400c01c500c004101c010000c442100744400c0c1526164800c0746400740044403480d004110150602d0001030000b4030800c1c81c0d14001c1c105942d13603840c0b640f80090603030f1240d10107010001d9450701da40a11010490700880800808003114006075035a2400000500b50000504828034030341040d20104002c0805900754001e60341c1000c0000c218101e50725040e181c02420b07140c0381c084a1000b20b81c0403104c0540c2e501c4452103003850b44844581894800815082351401d52083d03010488910100c03046a416074090006841d80d040d40c00c030039548900 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 101182886 1250 101181636 101181653
    0xe03030a05040503010516140c01020c1014090c01050403060f2a1404050d0209180f0109030f050a17090c04050a050a060f030b070c020d2901080f06040f0f 68
    0x1000d02000c6480000c00704510b0400748520340d030003203824002c5c441d20f290b00c204c028545412074503514407079236000c00c40e640d0084003981100c15001c40746003181c20010402030b140000e040307490101e0142c4a90000040c440040110310300181203416520949030a04680d900c100600c420b0205843c010740c0c070090b032498103001c0c4400b0040a0015622101c40c20300e100c0c3d0040c0440d05504000782e1000090004102c0c54135169801c02c800340c0e0480d0414566a240a0201d40d03082c02c04400800300d00c201540c81c1554441980040c00c41402680d80e490803ca035903109491920501d41c1c801c00084071440322094281c0c00c040b440d40c00990310b400b5504420300010015083d100203680340d03035010b80c0e03c105114040446110300700c01044e00d8064145c030f0398a9900c940c3c1c44140000c2c80310342070010f510300150131551014144080705500c201c03012080950a2811074010b2003c02680c07030340c0c600d01c8002040601d00043c03000d072101507440060081f0741c5c40f555010447d00e800c4004444e00d840c0c0d030001100051030003 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 101184136 1250 101182886 101182897
    0x3060302120a1104110412110604270207020627180f0106030c0804380a05070206100b0702031203010806040302070617070c020310020a020307060f11190e0303 70
    0x1200140300107140c03410000d0240105a00300742c8542e2a00c4014030b442c50381030068500722040d81003050700221160070064801c400721090f41349e22500c00035010034a081660403943ca20520340030800c03090b81000903448104d1141d604041e41c448024000c40707001c880d9088004000a88090300201e113004003502203100c00c0c9142c201112030f40c07a00000c0110705203c9010440c01040145028400410080009401c500001c1e102808480c00d00781440c40c0b110384061101c3e4003080000b0254810b4022045a404000d801d498400c5120304000215131210310004407907001e008406a90081323a45000e00ba40c0640d401140100c3e0140101c450900303812103060051802800001c001e00320518003450001c7c1002515000306061004060307c1c21822010141d01a610503400c2c1000040d40e4410b00000740341251011410842e04e00009490b10403540c044050200d0b248620810b001088100c8904c00070349203840f480803c030b5a005c2c4075003500030158554101d100706c40c0e403c251110f4954000440d0459110 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 101185386 1250 101184136 101184169
    0x4050612011b0e0a0e01060f0c150603020906091603020903101b020d0f021011070b070f11060c0904050403090333022805090405040b061f051903060302 67
    0x110000341c2e1420b5000003902d000d204007168441c40a50500102200000f0180148810070102c2e40510320746038055940d414440707030061a032618907078042d01010003078025400100c2c01521340102092040c18580d24a031300681c4461075141000303081c55002c800070340180000560510440c113010010a83c28400c4018070510003c140300e00032725034500645005070300c0c0c3d2090708100750400415030f869400700e80102c1d400d910440104805400c008081110b004901010786200b0200302803042c9141c021a0080752030810780c403030b000b480c1c0003020303800c0c1c4a99048418000320a42000000700c10715041d0700c5181e01600c40d040c0b00a0103034483d1a045a404c04140ca0704220180d14440404112044108400115240c610a610f44020403c411210700c10104107140c0c080304035000c00c03030390741c0c00307501036808503235015008200034940390600044510003902d01d01e005141038007000e10715100108013183c1400c5551039861a00104800d490000103040d84003a0400d5503d590200046e0340e09030288040c0e511 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 101186636 1250 101185386 101185421
    0x905070f030b0f121b06030f070807050f03070f0306050609090408030417070c0501020c0402210402040608010f1e0501030503160503041512060501021902060d0e030c0d020708010603110405061201 86
    0x300c1003c280b0300c40b005d5603100e611a100510070030042c20304402c44a0342c06501da190000840d103d00c02d0546490040380d2b480d036001c95004c010025401d80c00040d250300900b00c0e503410301446030384409105952250307040f22500301d01e00d000010b010a4030a070045070064820310a141d083c05603000a80d0b1f0f250003c07001200c0a01c07160a04010b590b03810024020200c5c42114110b142c43c950030700100030220506d00120100840a0001c0c0656980c2d601000003400c051000744642800e00e403e800040c160704410405403840c0c4000c40c1c1011245101e424141d991180041d450320b00ca52001c050714119071402103803244410000410070081c904d0384210b140c2290303150208101c10746000c031070540d04150409411544280b94040106146001c0a00a5038065941a5582c50582c1c0c15002a103495508c450300c074440000c070010645000642041c018a0079401d0740c2006407612111030a8501c18030010b0f01d9500f007420f81c02802d28042e0701041e0440401800c0380b400040d1f0341062801d494040790700050610 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 101187886 1250 101186636 101186653
    0x2031204080d08060604050f0102010b0303030a0b010816080c0d0e0d030b042004150903230f06070509040216020405040c0f080a120f090e010806100905070f030b0f12 73
    0x5004100e2011400c1460403c8506440c0036000303d0340502032489400c3c8503c6d0000e40d440480e9000703500c114400d440c040d0603031356a49081c40c0c0250103058140c1d6076900085103140050310080c25011440e44003c929600c15001740c850441e8210903400c1801d200e1805960f40d1250a0349000c10842250005050349010514040d203104010480c0c000c41401d40f059414228084d10345141c000c00c460a55601c103002e000010342128040782e02041c0c1d034100031315030354080b0300c0710740311816022514041369441000c44031040145080b10361503540036a5810085542840415414034054024059243d0b00c0b1102c41100040d507000101540d03000e1300c05542040c800a020b002d919000e0100710081d1101038001c1c00d002c040d41e0b4401e40b1110b2000ca9040030440f0700c031851002c05209014400003014807000c0c1001650b1a1144141c907148281c40400710100350403030018051319140101031150741d4546811403400004101a00030307284110555a0240348507105503c59500c0081c00c0b403450890800030b04004 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 101189136 1250 101187886 101187899
    0x605070815150a0905030a08120601020318061b0d0905150405010203071104021b0607180303080a05100906030f140604080f0715050f04050c090c180d02031204 70
    0xd001070003500c0a503040c07000c00700381a152085515104480e40d00119900d102a09007180c0f46041d03900041c0c0d00d406030303005080a201d0701a01907c898101e903503404a03181c0b2590010790b9244103161142d000b0441c21314400046140c02d80c00340940325031418254000f0308014050134100224002504007280604605000e45c9c200704c041140800b0721010014603050400c40042d64034001c2d01d0b0010044200807007030407240d4a503501562983d0045803445c580c1e44401c00e05441c1ca030403049445000050105040c55501104803070a04100da4040e1a491925111118100d0151800505050300a024440d00042c02c031090310418004500032a001005005140b03003080f00b16514109407038040d8404424480422040801c07100168240072010360b075144070b45010802e01d406010b800d00c4e00c0f0710304402c0002c1039002070885441356100700c0640c0c0b00c0480550170400d003490191480c2d403540106101e140c0b00482d0015140340300c000021710740d00c1c005145030700280c0303000d401904c0c0740c507800030208041180c03 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 101190386 1250 101189136 101189147
    0x60c061503060108300f071406010b030c0d0605031b0a09020322050703080304031707020f060610020106050a06050a08070801060f030c05090405010b0301061d0a170316060507 77
    0x15000d0440c0a8811945404405681c0b0800d00c00541c910045c0c0f0300c2502a1075450052040b400c440691420340c892144003040d1032160800c00c3c0c250740341c5003182000300e110200881c0150580f640300c001942503403110451403045800c03513609002d0240e0b0320300e404201540c0821401501400d91810880850542005c2c0000c029055000380325445c014014003144e80c00800f100c80001c800c2407038022030103200c0d09000303103040034a038005080707040008280702c02d2690114080c250800c42206a80642c1c5401c00126500c4e8080e041c0d40d000342d0095004070704585008601441c0041c030610021031925101c5c2c0c0000d00c81c407444e034003160105900103501202207800000150b800015401e0510f40da615003c0080d000c07044200400d0101542d0701c0e00c80149030b0240058800c44035025004004a603144e0307030180319661081c00ba80000c5004c0c2a11800c841c40742d505088070000b0050309449286160624aa000c0301802588c000f807400240601040380c1458010000d00500485000c40d6038141a8409010b = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 101191636 1250 101190386 101190421
    0x3010603051b04022503051201140103060b0c0606061308030d050601020106050a12020d0c0b070f02040f09030e061e0307020313050906030d080703020c03040e04020915030703030e0d02060c06 84
    0x101c0c010f0141e0300302101c51032078800045c2148580e14110581500d401c961074801c4001840f03c44010200215405405400c130000003002078030108000340c1c07100052200da001d40c0d0050b12791b80e40801c0020300141170000140030020034400c2000c40494444024600790b8005140a40c40156503400700849517a09009410007028144d40c5943c441c5e0410010080d0036100c03080c041c1c0500f41800220082001c4154040d00401002c1d1106490700003500e048205403981003000d903c61030034460007a2043d855032103800511945034541681d100221000d0008a0b0000034052400001d10814040b00c0001a4029481554540c2c0a5030343c0c0c1030080d2040040d1181c641100780140c40e00800c004079902e0008806202c51070509000c4000d03915420704402900c00c825409000f40408540001c5400d5003c10050065108540c0030000b0750302c4010007002d601c81404042d515a000c810700f080800d005e0b000c0344030784017005091702d00528a9500840e6490340641d19002641d4806010442a520144100030 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 101192886 1250 101191636 101191639
    0xe0304080d05030402150a0c03030c0c0609080702090a020310060c060b040618050109140a1a03100c02100b0609090a0209061603080901090803072d0504050109120222020903010603051b 81
    0x2401c0c02c01070751000b0188d202c071040c001c0c00d0650f1100340010082c041c072408440b26501c59801d03c112422884d0001c4e09401c0041c049014880c2000401c074440d9203030003501c1c4501c035203240800b5140d00d484003c540d0001007440035500381d80e40300044d05032a02c440c080d090140c00ca0001e01c0c2080301e0b800c0f41000c210360050b804050000d00e02901118102002e42440c0d4220b0b50610000c107005159842d110790055104031b071680d01d8800d070001c01c08040c229820004100c4102e03001d03a10303410300b185c1d5000181c9031821416548182c08114a0003245400d0f200d0f02d805c400405030050074041d144010860039032014142c03000782d000c070002c4a01090f0f0b20034001544540c0c510001c0c41f5403802070795119224000a1305031000c2c8494180074894031030595018240c7c00644088803040000030140250071640326025641c00649140c0010034018030f42806100c0c441c1e8068070340024840d40000c030558610b40c00e055403076050380801c8420000c6d0b03003d00a2002842c017980c05803c400b400c8403881c200707141c1c100e203145 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 101194136 1250 101192886 101192929
    0x213080606010503070e040b120607020709090f0b07120504110f01020c150f0c0a0c050405010617070315032102011d1506030a02030703030c05060109020c0309040e0304080d05030402 80
    0x80712a0741e0120a580d000303551382c146400d11504882c0014090201a04003540058151178801d02c0e5042c00200c00740600d0080d001e6038030340342e00c6003014820365600d04c074090503004089109100141c0900209035000ca210f2514103841020041c400c01541d0050398156001c0900d41d0b10400d0520b000541442d81c904240014112440c0b0640803442107104800b03400d02998000c5007800001481f02c1c125040c000300c000a62707144140519080c109800316009483c0114a40300011440c07502030b004107151800c3d07405a40c03150f641c0e001006c4000d0640800d844c409044042c0000000030004410304100400954181c0a12074441c00024210f400c45406400e24000d0340c0c0d40281052404030308021300c8071001c000320989640b0580883d1a0200096000750184596079000061540c040c001c10b402c240b144050310201c1e40d992448800fa40950042d0215a400801c40c40d4260b1901d41d0040382081d8041082e02c1c201036580d50058100009900f0300000300d880042040110f01d80311402c5a640300005207003 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 101195386 1250 101194136 101194141
    0x16120918061410050d0c03151706150102070b030702010c021203161d12061509190b0d0501020307200703080301120602090a1206150311100302040b03010902130806 72
    0x2407141d00680340000c502940700c0d40b84500340c07288504100d45204031707110410300c00741e5114200140144030406c0b0380d008107612944041600c140b5000c3c1c54618003403c400908054950700003048492080720555415442440800100044100081c1d0710a00c900e40002a40d82c0da044000381c103010a00c1d0901541700401c008210300105126108210a051441c0045207284040030200740d0003800720031168018004617202d096294001452845011040c0e0340c442420300c0402401007004003902d0780310b012089440c0110244030207070710400342d500f001000a560003132243c0382c1340d0032a841503ca100004044c185401c02881400c10b43e00194042d04006001540c0b654072880300500041c00340d0900c46080d103e082003440f030142c050300c0c0c0a160080859042e151f8803100100342ea03940000403900282003510542000c0d03220789403001102e03040b103000c000e200e516200300800b00503c0c2d070101c001d040d030034400400ca8142c0d40340914043d2a502d5001a0b44070401c60200140b94410b601118195100504 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 101196636 1250 101195386 101195399
    0x70801030804091a0603010f0312020706080604090f140606010311130b0903070306020a030203010509061807080c130305010b01021c121107060513170412081612091806 74
    0xb11421155071400000d000200201416402c9080c1610740c0e902400100002c5449882e0000707032802c80e072007040d841841000d503400c01d80e210061031181c10b01040003071000982c00c0c24150070241da554842c07003150404542c1c41d60f482007003562030040c0d507511340e10050800c004e6517010700c201c0d40b0503180c0410071741c1401204195641d02400780d01421407215001f0585196949040043c00b000e182d12000c250740781d403a0150010300941092103420700c9000d907800403030704508112040790759110482c89042c940365100003055440c03400150a4840300b2030200030714180810700304040d801841c1b00d00000305a0190760000240342c03161006d44401c4981e482003080020300c4c0c000c9600440c40c2e06800001c2001a1641041003550142500c0600a1810503040010310342207140b140c0b001c2c91166007030b840c226038240380428a50050707001d104c0010f80c0b415108000b04185801030300c0c1ba890008030301400d610166440040520000c03421001051613040144900c0e142c180c044c140c2801c104000b0800e00f868002d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 101197886 1250 101196636 101196653
    0x70c050a0204020c0a080304080304060501171b1306080f010605030d0210050c09060f030f0a0b03031e16080c061f030f02280602010b03060903030402130e0601060c030807080103 78
    0x88000b4480c0b0f60000314006002c03c24400403a04c1d580109180c6e0b02c031306c8d0601300700c1c1e0389a208840c2120480d10313100c0003060f0850501b448984040c00c0310000c0401003140c505280400e5100140d40c0d60040b0481001d0a144031a030044030080e01450024203442c48442c070045080da4201d4004034071940007070307119565940c0e0002e0700d141844080000462130ba26101c0a8444600c1103201c00380d003010b0006281101450728000542c003484140b40400c0172940ca6184201c1192007101549030305400409c15885407040325807009100400d4160421328025940146090188011408a98401c0049030101e10b40300144a4281d003e40264aa00a803a00e0300902200401550100404c1b1210340d00f800000c3d901c60080428045130f14902800084c00e2000c00010710300103030301c6544015824903d10520a00b0b01041031409141c80c10015401d41e21039500b081240c6840c00c0e2a4a00665608a1100d200404224290003440c003611400440ca0050030000c3c80c4860007010041840700010042000807102c0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 101199136 1250 101197886 101197903
    0xc0a0509060925030506010807090602120904020412030305040506010f030f06020c010e060108010e0f031207200a0602032203020a0b060a080f0c0102010e1c0f0c020423070c05 77
    0x110b41d4414299601c1c00d4641d0203a1400b81910300224080c41001110341e01540114000d03c001d8840840310307038642200b122603854900a0b44010f1b000390f20380c10440451207010740b072054002400942000e88030041c1c120001e181d482c1c1640013a444200b440280b06040c0000c2e40501008412014264103540310038400c0c11000350014400b9600090ba5084c0842c01c0d44666a548a00c4007500c1c0e00356501e00241d4040c3c00c1c0f04408002305e00580c61140320b02a4004111031841d00107401c18401035072280c1044c2c501c01c0c00e01a00858444444040c0086d2a41c103201005095200b90340060f124101038021070109002c09618520a51802255201080d000101d81c0795081d0720a0313041d03c2c2551a1008038404a4490f44154058854941a00c0c4209008658030304015400e9000704100415082206d0b980e03000c4445e450006152001501c2d0720501c190325162401d101401c140040074003541c0882c085403070032044450440002000300c00c02c40c2040079095003041e01d0b8a01001c010b901e0ba1036258503a030743c1d13 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 101200386 1250 101199136 101199139
    0xb06031e011a040608060604121208090109020d020405100b0409020a08160e09041103030d0b15030601080f091216060c03060815040c05100f020c04050411091506030106050403050c0a050906 83
    0x105d00140179969440100d40c06001d00806001d0140850b260000c80220340e50251408500004c0000350f15800500c25116095001040c00301c0041c096001d01000306000f518103801641d4040740171034025114001040144584440141d5900d000c1380010729804002d440200e100b00c4070361912002a9010301c84000d203400440300508d0702d0321140350000c401100344046e56007501000c00c002d9140107080d481640706187c2510905038400d210a041c002603c02201c03900c2c042040b010215880e0b000084c2c21641c000b0a000407a0580300405211038415000400e010f1045050a482c100400000c1c2c003605480c07084504041c003086003805291034503400d1900501121406103c002428051805ca40d907000744000380541052525141c03009002e80c492071000d2000d48224030510300726040501c43c0344d01c5950001c0305900b0080c00c1004001d0850340180140000d040200c0d2008070607030380c1c8801140200003c1d1109642c4070301e103140490403c5a01051603100356420303e01000f281d211275a040d40d01107070 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 101201636 1250 101200386 101200397
    0x7030512090916111c0201050c03090d0f030b03070f2d0b0901050403061401031704030503031305010b09070504170f030405240403030e090c090d06020d0b06031e011a0406 75
    0x108030501321140760100b810080035106044c0b0f11036a10040d50011001110190b00034001395403590203600e107a1000782c641c00e1841e88108100c00b0f51505ca80d141c0140d425484c80c010800ea000c0b000000e2030014203410080c1c2111200e4010024a220f1002c0786515040c0c00032850030320300c4a02c0b00c00e4600902c0c1c0c480c85c00c08120006500d41c00b6032090085030042e40c3d0001041204001c40310b44007030401d109002c11581213200458014038906070600b51001c89504c0801586150740b086840e180e1041d044004507619900e03042c05900d19940c43c0350003481000503a03281607c4520f440748100c4030092084101e4126000b141c004c00d40f03460080b0448040d1407041e5407401064001e40bc80d0078a00002201142c10004085000300c02c0603407280c0201100c5108992880343d0361200311441040f84942c0303000c09c1c0d01c03802c4080001d0002d04590007901c80840781c2000080e80d61083c0d40458803551040700d082070142d428040155401a0240e4254094081e11040030018005100300501d1307407003a070042034203001 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 101202886 1250 101201636 101201671
    0x4051002190b220c090b0a0308190c14010c08070f0c0206090a0b0d0609060f0503030304140c0301020f030a0e0106060203040e04060b21071e03260c070305120909 71
    0x18441c03103c81c40c1001d20b100c140f55401e00142401210725100e401030305112424038010700d100e460300c0c07200002600d41140c0e1261401e64803184141880a014416000380b040c2100400003180280108560400e55480003281507031260350002d18241009005005200c040b0f800c6110300c40d4490100041258180c070341d0341d0783e141072200207030006015031b21014403c0e2000504050601d2290003a40c2243d85541003800126168000840411694090f003509030740148006004100344c00e40c0b04085403610f005640004001d0f00110382641e024050000c8482d00001c18080c85620b11300c038030750440341c501000300123544c18420b000303440e44030b584280d801c1c94401c000400e06001e403923840500001c00013826845031040c003003055800d9a01c5841e00300134500502d28009034010703101c0204040e61040e00324400410f400c640e98642520184251185003000860205100c885040010980c4c0c0c0720a1008111640c65458a0303881e0000b00040c03045059828404030b0280d803242e0707910681021011230f0f24007021 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 101204136 1250 101202886 101202901
    0x30507050a0803012405030f0f0a0e0607091703030c070327061e09051f0c051506090108030f0304080901020a05120c10092018040804051002190b 64
    0x880c007448050100c80340007000041c0702038039451074200c1300029212080003864941c0151618002200d00e00c4c0b4844805000403010040d840b03185910804115000034042c0c4030044071880d0000485d1140003240001c003003805044140c488403030140c041751004526518000703c028035540036030303d4001c0070b11610195031540c147c8813803104007a26458011503540d10750399200003444644010100322203c80e004220b591628401c20021f011f07928050038000400740140740d00c07004000344010311000c0044902d002e0b00010028080081d50303043c0444401c1035414810b04000d0441010b0740920441e40c0100034018030310381d815068130b80c0207411610103038944103a500181d04008c1c0c0b0344402003860068502202d0b40c090184c018100701c0c0c0092085404044c0503116060480d42d0f0440b01414042c2e842030755000701e01c82441c103846820b8026140410001116001005a080c192000c8480000114050040382021400307859000494130040020b59482007900301c1540340d485016184a0b00e00c0d0019207013 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 101205386 1250 101204136 101204143
    0xf0506070f0503070602090f01030207020a06050318060c070c050306090604030309080409050a0519140c1b070603020c010f050408090d0201020c06070807060b010c02060409020a120606110c04051303050705 90
    0x1c07a600007080da0303a01e12981c505040207506c2405154401c105a20740103460b54402d100382c0c0c00c0d541e070281049020906050040d582e0350402001c5591032027107040c0c02400303c0801d000340c81c011003420246607245d42035403402d1000070b50940c100f1070103684000104000785800007026030700142c140c2000103d0310600d007811081031207a50440b64219081506000c1107201a501a034851600d500c0805145444168080c040d0b41205030020440025400401d04039218100104403010b003642d0a04005502c01c0c3c0c1e464100702c0c56038004408207501041c2d03e51006028015003420401008041005140554904a0300d00501408a000c1d4101d2034444045900803c4104c08031180101f245071610030070325290314243d008110859280b801c0c502c5240c0254000d1038030103a0258001d20281c241410040d50750700a410580d42d16003000001d0242d041d0001c08c40c801d00000d030801d540c40288000f01041060b2806424100d80c1c0e004602c0d002c100075080101c0c03001710183e254189046a40c40100b030521914 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 101206636 1250 101205386 101205413
    0xf0f05090d020a0e07080f09100b0609090c040305070602071211030f1e0f010b030a02101b0303090614060105090d06021e031b03070c0b090a140303100503070f050607 73
    0x100f040c2c800002150718421111280d200b00015a02d6403800da664800c1d4881c051410f454070a2030f41d05c008045910304220790083e400800000e40428242891000085e0041005075601c0044110029040c4140030741442000041c1995000601c0f40c1454052012010752100d4000780c5007051443d00da607a165002e220691070480b100c002c80c3c41c0c000c4a0020b64010a8102c10b40d08124415014004004541805082e007009001006000c0c524103a40034442652002820b10041046034002c031050241b01c50940b071a00ca000741c0d0002105c031018605079084511003680244036040b001e04120244c1c0c2c1c440202c44a40000750b07a0f00c0c24100301403410728041c1c020540d10320202c4010355940c070041407184020714812107a00c1590b12140e4603043c180c441521040d644c2c500020346040c1c4603808190442803803900305112204603a007040258540050040701c003085000160400010b0000f081941001d50300603000490203020003e20b031100110480d240e612525008800108036203050001c006500030 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 101207886 1250 101206636 101206639
    0x304170912010606030c030b010306180e0f06040b0a06120506010501050d0e10020d05010b0f07080f0409020d0e011d060f060102010b0612060114071e080d0c1805010f0f05090d02 78
    0x101c181c880d200031780640b126503c24400240341451000c815886800b41d001169000621013a80161060072280034020030101d000c0140300742242640040342c200180c034401d60242d041450603040c41d424082c02d8454a520040c40c803100365007441d01240d00400e03d9811a0b00908100399141400300c5284040c028000b018205400b940340110f2411206800500084040c001d0030009aa2118100d0b0458007505035400ea08900a0003114002810540248481a8941c4006081c940c0c0c41d00108180d900403010001d07429101d11a580b075151003405000c219429115a602c03550b9003c4040c90b6882000510351182e0704400f502042c0140d00030341c0104000840584042c5d62001c1c80c07c510b08411509650030340c005129040c0081000700c442068400381d59002e040b885e0b0911030020070015540551100b540d0f8007000308085103904403284641540070840d44c460003901640c82504e50816140d41c0c0c001410702009012154040b075000c0100380040603a03040807501c41c9600c0010410409181900a = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 101209136 1250 101207886 101207891
    0x3120405070812070203160605030129040303030e01140c1215120a1202120702100e0a0f050108090f0c190503010f0e0105060427030c080703030204030b0c030417091201 74
    0x43c1039000f03400c0b000b0518103000350b0889900b41c911010700e0100e00003601c03540f000648140014018403d0200c20303c4010104130b54038075920415006903a072243c3c42a4811030100395503000d522555102802000340495440d4111000d42c070340300b00e54480c1445a141c20240d5070a034000000d600c1b042c04a0744203041d45019124082000d1034030600b580e1140b80080580748078000c0704450401901c0010605d40115042c3e000d942424101d0f801d010031540c11411075420310696046050680d01d40a4110b0000e141d84501c10184a01d4000050a040c0c800b4004086540018002d0b00002d00005014080b024007501e0080c1c595209006604007a2419041503506508001a020780000f842d04200803604101c0c000f00995107405041004a60021080c2500c00300c51902e8032084005252a1a101500904103808581c10551340c03011a43c0c420242100860703030200d07044c02402801031382c8030341c40400100c441d841c500309500d4003c03840e5a00e1084403615840000c03088500d4803075001790a5940d983c2c030000d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 101210386 1250 101209136 101209153
    0x9091b0303110609070305070302151209010209011103030c2b09030903020108070c050714030106080111030906070c08040b0d09060c0206061f08010b0702010e03030304060f05010e01030302031204050708 89
    0x4040d5107065502c100a4860040801d60001004c038400040b03940c000d0084c02110f01d150b080c0b281180d1840c4621030f5118043c4400455500e500c08801c0c41800d241000690f19400c14001500003218039447c10026400ad200300410055100700b210b1720340d400c1074541d01c01c85d4084583e0b2103021401540ca010150b08092a00081541150420301541c3c0300341c0380c603501a960032504882c00681e00001901076840090300300415408240340c4074183d0409030001c0786498543d0303415400d65210071100c00c1508400000c0011000301400001d82014107441d04d80c26030303a85510740d601c160289003d040c0d00207034000342450710914180c2c0440d900560050f030500c190030312000045d4590340200d54181c0140c4108641070041c8000390180c0301d04146945178580c403a420300d0400c0c00b9681140301c04030305012441066180d1a81c040001d54419480f03000c02041030f00c00a150314044c3c074810f0303010500b103209403001800083c2e00481601c2c8090242003906030075136600c1c1003451a00c0b941e54000d075200c3c0030742000e = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 101211636 1250 101210386 101210393
    0x60a030501180e0d030515100c0c06030b03120a05040e0a05040c09052e030605010b0a020c0301090f0318090606030b0f06040f0501050307020a0501020310050f0d080409091b03 77
    0x3150741252001c0c14185502041c00c50704a09540126403020140e8019030140308501e80660703c0590030450310820700c459280b0328008160f0301c4c441401080b012580f01500e400422800c031114101802091074140a0fa040f2031000c2035890705c4051344404504c1c0c010486514440c13084040d6002403e980710040310500300b0090710802040d05803010303220281c0090b400f01d850b00071401424024420300d03000c0c082049150303500c1101c060104a2031080f040c22030f400000031403818000c03240608a500800ea655801c0f01700c000e49068201c00202e8003a0741403850f000046040c1c0d01c0c2c0100c400350542490074a1001c00000c1a42c2a041c0341c008042003031500d08041080d50f030550061030700b08030640384a800d5501c4002008010b00030f92040c58582c0c0c500400502555104e2406190410303403500407200500300702d550740c50aa0704101c0b5403000081e005da50810440c07405500784441074105480d9921541456144d8007207500c910b0181c01078464950b800350040081066070342d032181800003402120980c0301e10703 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 101212886 1250 101211636 101211641
    0x1407030c06021504021e130e030c061b0f030a150f05031006080304050607030203160f020f0402210714070605070908120d0f060305010c0c0521030a0e010b060a03 71
    0x3981c80144141c080700c14012100003251805550010006164003015120801c10901c0e03030003046400101b0550400701c105902d000e154080041e06011310723114800007500c0d071700e04407006003000c440f0685018040310f0291060102c80910b00c80010740c81d0f90703649942c0c1c420007421481c0340b1801c14654a490004d03000da10129084251b0b10124103442a80b00d0a25448080d14200e01031407010f50401c12003000145403010090111134442c0c01981d00381508000d0082c44101031110a64001200588050452400c5c0c40707a6003044000b12021030507ca1110510201030902d018000700750803510001c9240c0c90b0050440203c00e01400403001c1d514881032400780050702c001d0300e061012039480d030404203e043c0003094405c0307841407a1180300e0800d0700043c60140035045044030080030319586c103008404103100f80200380380b1640a03210002d14202c03a14285160031203642600d02008500c400e10312000c0c00c0c03032048bc0d802c81c0300500e01103090900c40407800d0040803102c0b8201d038014030006503140c2050b050b8 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 101214136 1250 101212886 101212889
    0x7030504050705031f02070c12120806060307021507050d1a03010c0507030203031506070804080d0e0a050109030305031008060708100f0303050a030e160914060a0506070f1407030c 79
    0x1107040d074050a075180c05040d83e40c0d2146030b0041c00e50244c1c00d04903030220210350181c900140103503915241c09980d80790156500044240c19a000c1151050080c0419000743c1101c1c1c0021042e600c0301d2641c50020b40007512400c0c80c16450303080c0002200442d403514458029180002d42012041003040860b1583c6080c1040403040caa0295003004091840309004034155400c460b01500994a16038132207845100258241075443d41c468018400300d000f041400d80030b00050500f200040020907401603015000030340b040c460f1407146100c1d030b0040c00147d9004003000c0860f689804c0085c0c40c1d0302c0d42c50041c44414183c0d0002110f912910b4200000d00303603c141c40341d000324540000400305a40780c07104540760f011a4003003d40828010003443e00c01c0f078403a40c403e1658030603420a1b950107442d1102c201c0c540c0040c4d0348c028102542c03120382407840d51501028060700030340e0489100b03504038609000316a541c0030703103240505245002c520040c01d000e00c400314009090302c15025130301c00c9030322850410802d00301c6 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 101215386 1250 101214136 101214143
    0x3120a030b0306010b030f19020d0507080f060f0d03051b15070915050c1504060501051e030c120304030b040c061413090f0605090406090501050702031c05060111030307030504 77
    0x40281c100300604000c55468140d81074139441c1880d540d030303140c03008420101c094070103408424000c825944500192021308180e11361224003140703500f0481c40040075640083c01e00981e60480b4014050155510144000e0806094806141d401c0315400c09440a0040c8070842d075400500d804030359000c01010403000b9007036482c0008084a51240502100d4401190144c8003000d40c1000d100b1140c00d000710050b00c034900d2604100c90340c201c0c1c030084030504014241d40c11581281c030340c0010302c15440e03c9280300074002c00440100150051010001c3e9940b042c0c03035909800f540416021004900040c81118003650b01310070110520309091401c2c031042d900a106030320001b1041c4450000b100c7c40c40044030b0208600c81c101421440c03c0100f20b02c0286015034042504aa40c0c001c00111070320359003802d9100702c2c0181e0300058000182d040040c2510001031500c400c6410401051051030304803015006284100b07a4005050780c2c822005880c110b031440c50491080c0f2004c0100210247d0681009100b00d10 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 101216636 1250 101215386 101215391
    0x70605010305070e090705090c0904091506090b0102060c0a030603120c0318030f1b09141501020309030709090c09020c100b04110703030519090f1704050604170c03120a03 75
    0x1355102e41c1d010100e005d403200b900e10b40050700108010325003a400150045000c1000502d400400800682101c0d25050120345002045002c10003100540c800d00300180400c8006001d040e51110000b134039100020b0403050341e02c0012a44010f0540b1a50180f4040c2d540241082d0107030344510f0029003402502034084000a4606144582801c080c0c0d801c041101d5000200d2400000c01c0da40f688000100340307034800c010002059000540e0065030140c040030040c0304030400c400e4104148491000791700700980c135040d540104070301050b0741c40c00128082244d4000301e00040c10041031801c400001c040754040f000990004c91000401000803558098081c48008100522000002807106441e10440b0041a43c0c00500110005ca8000d8209940c025621002c054254490202c2202126504441524100140d428500400c54903110010311084500141414186013800140f442d11a50143e410702d0907027072000a60590003080041c1c6204401001c0c1d51100826000303040070790b0420710740940041d0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 101217886 1250 101216636 101216639
    0x5030c01050106090e180a060c090e010803030f06090a020913020d050609040c0504090507030501050c03010302010809150c1c110904060f080307060c1b08040e01060e010909110f07060501030507 85
    0x2c0c0030740316844c104c408855901c00540c0d20240e02c4050179111106000d2103010303068910000a8543c8202c030180840c584503000040d09018030300ca40007605070440b85d0680d00400600258010010304268000c0046680c4030056840020f040c001e40500f09035943c00181c2030f0f4070a02d009100349c000d4039071951008001c1119540e400102f0858480944024005400407036040c446420160005110700740140c080300d440302e070393b55101400c42e082140c0c55201c80c1c0010005000710b680c4844200e07040b01c103c400401a6030947c0c03440c00000d00c2d0150220765249000500f032944441c07450a800c100e104d841004014818030380d0000c1ca6290f1040b0a010303c228a081c001140100a441100040d240200002c60502c203ea0ba540d0004041001e00b110500203e88043e0400c03040c1400d4404442d44030381d40700c0d0b4407a803408038035880c9513906802c18010301003180103044860b41d010740c00c50210360701e2300000701e1f02000f100d6521000d88078420401c4110040001c0100038006160416812a0301c1a42100d41d0079 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 101219136 1250 101217886 101217899
    0x10c0b1510031a240409061e060801270509070510110a021e1c061406010f030c1b030216050306060618220504020103060e10030308150d05030c010501 66
    0x44411000d40c1d0341c690b0075002090690708059034560516528481c162002402d900300d202e600d41c02603402000040d41f916000d11a00c000e0701030f0356078411500e24110042c03a08007103002c1c1c52040140602000800304180d046c1072441c04594803030744032110010030005400c025090940342c0c1514010f540c020f80c000d081010226125400100040b0341c1c5070003826001c080365003007000385c0c0d074101e8506c414005507414181c01692100c05d40501c11115101e480c41048140c07400320240c8041680641c61004200d04005a41c1d0308110964020411031600040c5d0000810050304c03080c841031a5001c40d041000b90310320415400049500424181c8859481041d940b6003c05a0b12034046a500f600718405211845c00c0c1400c02c1c1080c41d8600e8018115808104040341c0c5000c4644024030380c01045440d40280400e550b09480349002400502900003518946a407105240100521000f0100104d007800104040a000c031085408600100b40010140081c01c1442e501d410a0790f03110842d501e00400080c40 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 101220386 1250 101219136 101219141
    0x60501080c030616050406050309031b0a20060a0c030c0c08030c060c0301050d0318150c020f101e23041502010e070501050315090c0406090602010905060f0402010c0b151003 76
    0x10070139aa41e4103482c082c1456000c444a40000e407240c00144814403c620a0303a4040c043d0842c134800550051514904900703000243c051501a1110503041c0c071294403401d03840300c0e011191030140301c1c102001c2d03c0341c1c030b0b240031550f001810388050078030040c140000c03070003000c040018903002c031041048555a845039841c005242c813082c8502036000300501e0b084400030740150f1210051902042d1041132542d90340c03120300060540b4807440c0000502820142086280c0006014503c0303c003a1560f10102010000c00f8200c40035400010f054410700d0300300b481809110704400b01c90100694025900058180030310402c0c0c1d0801d015003000380f41031070124090b040c03052084a00c140b420343e000302401c070300d00f8005540035407020781084010100030b00c181482c0c0c2c450b07c40460040300440c070708035036a03458070b00024007c2c0500d401903021a418000618003240c0002081600880c4d001c54a50645d151840141d803034a1000c2002808640b030782e130402c5090080403202c05004001036a0001e096030322a07a04504 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 101221636 1250 101220386 101220421
    0x80406200705090408042d0b0a0e22020403080903071d0703050c162402041802312102240f04030b061c050d0e040207060501080c0306 59
    0x980e90300c907040030042c520340f9115441e000390042c070780e0074075150711070300381c44500f9614559594075a50300d0030b40b103042c0c00c00c0550310304000c000d00c406141c00e00e82c0d4500010401814410460721440d43c129403c11f840c1c00a41c04029846140c6208640e960740e2441d164031590800050039229000380c1c000062502045e440ca248000c0c030001e0158049c2d510140c05600a03e00500f5519500c8414081c04124807c0281301c00781c0c40c0d014402c0d1490b03031205140300b0484400d041540f007402c1030040c0020070410340c842266014040c0d45000c0561a02191654190328021504012180000d0b5164030100441c0a540040540ea000b82c0d89000d00c0d0800a041071a10b6004000290400c0e4009140040c481d0b5000340c5a0041590715601e51406240344d26400464000741c00c00d4840c407070b000b414490b49240c00c0ca080c541c0700796200c142d0110001291a4151a100b0030f00030b4205102c1102d51010320b0f50b07629411103c03a158041000c0140c0d584030302c0f44560307640c2c1c42d80311306009105480114503052800d030b20010 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 101222886 1250 101221636 101221697
    0x60f0f0902040e041e141f200c031201121104060302060a08091203100f17030702010507060209060409020c0f010e060a15080d020c10050903070504020f1303080406 72
    0x6100c0c2c44039a0740040c01e007440e03541d0000c0c076050610300c100001c1403148031709a002d24800040002c1c0307e01840c0761020401c01d8200e8006c0520b01500d082c811018016400101802480d4140c1c03500420303540203045101d8083d2030302040c01c0c40350020a0881d205450403a040740189910015030fa01c036410700049400342e00000e0351011042c0b01603480c0e50f06c03800c071789503100061201f506c400b9651800f080c0c003035420517212000d6000900105000c00300000700404000c040c8056100c9918180c16400c0b81c50784170712503000c0d04211000481805220244e01180d100700070103020780b940c4aa03210043c4009412040048031280a0700c0485052690140120703285034021f4009000075448500e4410002d004e6110040908100c244002990b10b50500181c01d03004000c0d00a40344100032401084400c0621480c240d042c00018041d08606441c0000c085059410580707006a480844161304011409184000c1644001c015404003c210b42c000160003103d102e034a80c180e060301c01c2c1034000f0840540c01d8100 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 101224136 1250 101222886 101222909
    0x20c07060903020618060712050903430b0301120b01060302070201090e090f01050408040914090307030f090302030d020d02060109060503150402010c1202071d0412030509030904060f0f090204 84
    0x1c204a0b840c1741e4095910010209454500790340c6e00c1404901000c1c0260340403941c08914542c0904050010b020040b41f010401c00c01442144840382c058a0b810762141e007140c40c001c0594541d40762150000d2f002c0c00c10000d12940740d40e0741d06030014403503904040071504144800e000048450090080c1c402065050b15055062824100861000b541c01824809a8820045c520001002c28803030540507502071000980d03518102031f0880d056441642e11340030307586400020010803010200c00d0700e02840d0b2510f0409082c0c0c94004085484803050741020b5494040d030100d80407a103800081e083e5945000d502941ea550380e80f100d40070b08079145441140e4264000d041105220b20740c40404990092050426260000345511440302c007100c08103120002d80d02150381441030321901c4c00320b582e00c14107082a4480c68a0705698641c50f1000c003841c0441416250404649123003428010303100c082c400034100b04055555252a00303074031005882614401e018420300821810040d00841d070550f803400790030 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 101225386 1250 101224136 101224147
    0xb0313030c021306120c0501020c030a060e120c03070c0b04050d080d0f02070b19020a0c020f12030a0201060e01080102070305070318080106030c0305010b0103060302090c1606050109020c070609030206 88
    0x50781d402800100c100d0b80040440800c0b48070107403e22070780000e401c0e54914915003080f04c0c913200c1d045560303035000107055510143c3c007132480f42d0380000e420b50782c103a101001084c1859004030700f6140c02e01102d54115001400305070390100c01000406009207074080c1044c10a403c3e5145e0001c41a8456030080581150340c0c01c40710004110114004c1c68450f09000001441c1060a4001022078000d81401c42e51107080c00c0502110060300e019035125403003044011843d202e42d0020150500010b040001e014525031101d620442cfc0c0c40c001da12a03003506810076a9914504803500a00800d05409814102d001500021414003414400d80756500d516889092400e80162800d4802c0c001d15880700401103409040030803485801e0044500541c461380d9100340050451030600d0a41d440c2c018034604251038240204050f0760754500e082d030070855800c1c5131540c0d0030361f040c001c0c0b95180b0042070161810381407000024402280e680200008002103054445003915600c08070303820a501c3c071001e54800c800703106 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 101226636 1250 101225386 101225393
    0x150605060a0513050a060c051006180f020702031507030c08130809060f0a0206011503051e0910050f01030201020d0504080c04021b1f0b0f060d050702071706060a0b0313 74
    0xc101c402411544015480d0380c95000405405d1703035401190001e52164101c0c010840100a030440c00000541c06114160500406d550b03074054000c04060f009031111000c2000c83c1e1958100c0e00f0940d000307001e4588214510742d00c43c0302d030901582c4640000340b03460b448410882c8a05071460040340746150940040c00c181c0c65000c210b40100b90b03803036841102007100481e0030304603400601459100d5000380425615220811344200b580100f40000d050a15041000601d000301210740005071500c0c0c0d10102c4e032502280980ba016444108001e40c030b140405000040301d2140006040341d00c01d0303088401c0031009071000c81e024012803080030203c1e803020f401c01100345030039000703800604009a00c450402c0f0460746902e250015a00c40c1040245071580910b52291007405141c4e004001a103194019920640208200744681d05202d08003540e181e0210704030902c20300081c001828608a040a40844503880076200c11041c0c0d149403245c0700305000009d1981004060b640301d01d100b40103e01c009407042d02c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 101227886 1250 101226636 101226647
    0x314060409170c0c060703020f060703061d07120212040209180303130503070b01061107061d010804020d02030303011d0702060114060a02071502030c07050406120f141009150605060a 80
    0x900c043c02405071009008464030f41001404000c0c4c000e81c01000341c100101c18440c1040e10140803141007505003079040c08800c410105160078403280b19103038891035650000446841c0f0013a9400c840c3c0300d0002903101021700007041071030b000b54022151f0044030386031281c10348204444080c200d107507900107100280c2c0d03045001d80c0b03e0501e02d0003002074900d0b00407103640d9009074881c02d82000000c0b4504490043c5040004c1103114054880e60502120030300aa03034501c041c0345d03011003c45041008880c00181151103c05491550700d43c00703421640c1300d58407084840300c102e400910071000300101c480003d000c01d20000f145130403102060418a11040c00405002c1540d200716840c0007944151340000800740381140c12040440318560145446609501140e41045010350040b03100c1c034100070081c403a540388940c1c0701829582c0082c65004201c00f83c0303040c00c0111594000c4c03e01901030018009952107803a00300c0ca85243c426100b0000140900034140221480c6000e0143c00100c10b0165648030340c041c6 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 101229136 1250 101227886 101227897
    0x50112060825290f040509102301020303160e0d06050118020313020d031806020606100503041230051005030a0c170307060603080705010e030307050307050a1e031406040917 76
    0x1407070303900c5c050321031000c110380038010b440c64256641c0481c170030441403d84501892880c901c0e01c90f035250322200880000d47e203000140520483c50300c40240e0902c5036005101211004102601c03d00c1404098200300000300001d1152152001c10101101c162070350506c00c40c0e1044184c00144068240c2940900c200368013021021020700c10240042420820315a621100401c07490b801006186881d809000503103642110540a0100c20b105000c0082c0701c1d2170b0600ca11545500d4004e508181c010400117028401104180c4010900c29143c00150060b40043c1d200d4082d01140c1d400f11aa10800d241d0303a8000c610002d088560400400e22400356940c104591084070301003102d041c00c0d89922034804498569000311500c0b400003845404026003030150032900b81205018501b1868095400380c82e500c402001402004000161041001d00804001400680014084c0c1000b0300745030018004011081e480303100c00f040000010982d103814000d0944182c1e1140c140300ca0141c40030282455500b15 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 101230386 1250 101229136 101229157
    0xf0f1c062d02030402010909050906010603060501020d080105041112010308030109060501170a050604112d07031b170406021f0203131106090d032001051005011206082529 75
    0x510343c0015042c903803801827501986090024251780d51518201a08441041c1d11440c1507422400306102581d821000c540d0440d0010b48011942c86444282da403954400c51164148003984000040b080c00b00f640050350684181d00e0703040241030b807100c00546402e0690000301c1111000c035400917205400b140c002c65000b14000c0c20100d81030a900391244115005034200c800c641d001a401c203c8462440311440f801d080c5045200f40c0b41010070b4500a10000e0400c07014900910b0120500e41000900741242074401840800030340c40d43c1e03d800c0029102c203c60440032580d00c0c134000d560001e1008500c01c4a00a80190000040e600e2a131b03034a26086110908240b6401513060080480507140c00001d2000340b482680c5a44032020240b00031420b201102644203c1c03a8904800c0014141410706950141c031001d00302000400b0700b0361243c4002d0226504802d0960269000c1e006000d12010701c0005040c02d80e144500ba41c5031558a00b98074102d071000508020b0030380b020000c409070380400007014801d00c0c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 101231636 1250 101230386 101230397
    0x240103030e030a0c06030c0e061206011407080310080f010e030d0b06121e0a060b0a030506040b040905030405030d050c0601060c05070e07050301090c030e0c0f0f1c062d0203040201 79
    0x249031301c48008101c0c2c2a032207500840d868818203d50158444d4000002c0001222401c0c1001c05803080c00c0610030307008210321f061240b0444420303080e00c800020f0f41c19040e8040107442d540e141c8680383c8100801c0610888800d8460b03003294280118040c080c101411003028000c1d030908003003800304000340c8840301d0000c1d00b0560401130b01c01a0744c0001000e034800d030182018104107034000000c08601a1000301f0008101b840c0400910964034024101c40d5000d50318a400b1506894031400240288142d480c0703e41d005141410200801030080058402c503107080b8140c2c4c048480354241942c0a00c0b403662402c1150304400014488580240d588078070450040088480f595140d40c1081002e0000381c031100d010900c0440104094a424094160352008626041c0b0041c1d03544d229041d0355a80a0300440e00c01c1c001c0d0102060785845001036040401d00080103a480140000c124180c003640c00d84050f19507506008080c14a80401c01105100003040c1000911124446854000940028008a04101 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 101232886 1250 101231636 101231653
    0x90d091403100c090e010f1a0a08070804140a060b120c0a050607050703050313180905030901031d012309060601080403050309100c1106060a060e0402030c0d09050f240103030e03 78
    0x280d030010310328060403941030409405802c10845101248e01c1c94040d4480900030058580c0d016484008960022040e00701090a40ca491811695404c10030340d190081c0d11483c8510030500c04d0641102413190400d451503100d20b20744448031500d0701d01070540c140d0400c8090004110700d0030150000d1082a0081003918001902c0390385480c1154070141c0b0300880343c280c911061103480c0745c120141d00c900c14503d03000c02c103480c00ba684044d2203005140415041c50795420000011030200009031010259480c000c002803005103000701d984941409110b40c21750142c10001c1e11181d070029441e401103030140c560780410b50710741e54101c40030351004003e244503000b000c0c0c2c0000b9074800342c01103411036412611102c0049055103280d41c68400e004000e28030601a1401c10010305402044844504500340c0b000341c0d803035855030611a19842000030324a0084d00d024082d009001e0041000c22440c102102501c5480340c0c101c011070f4050b2005010015440000001040083c4c01140d4090016402030181c4040340e = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 101234136 1250 101232886 101232899
    0x2190305100503030909090a0b040f03090609140904020109030203010c0309061505061b0a170a030507080606091302040f0b0910030219030c0315170c0102010509070303111203090d091403100c09 85
    0x40c402a8ac0c22039504219103100d00c2015007040640014140518061104c90b00d00b500070403811190400035400356182c1e902081c15644109107001c090740e0081c000380102c0c80008001030080107012802d03a80d141c5844113180313404807036500580803100014802da081c8040c80c1c00b2000210150841c0f04450f00c5a4270002c00082e81c000e0445060496803101c0d183c4038100b20310058180c1c1d50040c0040100301c00c040800c8141e998000a072a190001542c01c00035440e8203500107130003845070307070845c440c03201d080134001403402d07000340041880c420309403032080c8958100d0740207905a009170b000c3c07503200701d860003490034485210f07901000801201c0d14000c01c00481d120310603120501c6030f801100c1d0f094140040700002e82c1c020442c070120004280f0080081d860006500c50b00d822040c080182007080c00c01c00b00150310402c2206005103440e4507400c6540303003019085699501c3c060140307580465480f800010f40e642c2042d07150118204054042c0c10060300e02c0304480024101c20100c0028400d0b540030100e4030 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 101235386 1250 101234136 101234153
    0x40b0f041d0706031406030f071703070c08100c0c0510090204060b030702061006090324020f04081f0605011e2001140c090d0611070602190305100503030909090a 71
    0x1400c454400181ca1704040305680e0103c01c00501e55030181e03000c0445c04619501c0081d0304001c4545d18010460308002070800107046124080015194819481c40482c0400c0d000c10541e001e006203035000c00003240d000d04142c43c045038001c1301800d03d40000004100404540c1c10884526100500c0060019120b2000100c981c0044d200c40d0010b07400881000a003021045d8140041d254500b0103041140c9035584a420710a00d01141d04580000c00c107504000200680680c1d00301480c84e45180d48550310351052030790320811803004144007e028180f65080408603c60101601e20682d5484602c9400c00e0303a0311004081442c11408006140c94521000030380301d1008a03507450040004108614900d40c03103481c114000d000c4551044003000318154030741d10800104551540180c0c00314280c0071070610240680a8144050091400043c028914001000c0241000d001c070351020007868803054140100d01d69640216a05603100304141840c41c40d02500240e44103500740300f101c00400165841e14070 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 101236636 1250 101235386 101235389
    0xd0906062304060801062d050406031b0b25020109030203100902032107031b12030507080f09030a1d0613050a0806090c10020f010606020c0f040b0f041d07 68
    0x104684281c0d00115946002d0040d84001c01070766000380034040c00c0030b40c82c0080b4107180c0400d46001050007070050801c0d600328034810040030001c0081000503524100310380380740042c002201b200c031680700b000b00d04402c0e1a0b05030380c0340701510819802209400c255160b800e0b840c50500341c2c14811550000401607804200040d41c1c840c04800c00716580312144180352800800c80301c040140c040100006080703c8281c2c0036900c149405141c1006082d2401c100820050f848500103440030301410030001e003054040d00a01c6c020081c540e02e00e82d0660b81e81054032a075003425103904c016a0401c002d500700080c828410351215642450704010303003460b00c1000501c0c030703800302d851242c950000c01d808103c40d180640c3c10340d00602204010340018642091610f0312603403031003080c0b44a02c0010810448c810f200b08120100741035020003c00609440d0344019645000000000d4440c00c1d251110100e00d0405018504440001900000400d800e485c10000644140c84002440d151240361035414110104540b90 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 101237886 1250 101236636 101236679
    0x207270e03040801150305030a080615030c1903050f04060f0209040f060603060f0627050607110a0b0412080307020c030a060b04110304020306071d06210a090302030d090606 76
    0x42ea1103240603902829911010310300c080120742d0090800c0441c00100450f003411080303203089680c9a84000001d06a06411000140c00700008410007800a001c000105000c4074043c0001c1440b1401d214202e040d107400b240e000c1e80c0c0036401c0300440c000500d03980051416200504d0054100404036020908580d400350007a0300321031b1508001c100c655054854000942501000c4440507402c0241c0640514080035040080b8200b01c1c021044505d182e211030700103010018121903445449040c1098a000310003121486200c400800084840a0200f150100c803400851000c001c140d603200c1100e650001491442076028120352407440b56428007000c04001d1049a000a805030000c052201321081d140c010040c1800c20004e00c0050b07030340007420951001c801d103401c13440301e08a509900c01030b9000d0045d55402040c00300305100c00245818902c5c0d0217810600f9030562507543c41c00c9003803c2d03c1480c54040d02603042000b52201c1056550451007000380500c1c0c0100d00703070b0b0f17540c11286044401d402d03110 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 101239136 1250 101237886 101237893
    0x601020c030f030405091012140703020a06030504170406140c07050306040b0103050d02060106050f0309010908040906080105130f1202190c150c031b0c080303070804051204060207270e 81
    0x81c85180b0b403203800a50450745440440840c2803d0070200d80c42d0074500c620103810645928040d027401d20003044020061580540b01107501507684c0d0000d006003006942c01c560311a03c0c0c0d02c100c24021882804e5804981280c1d480c80003607600c248610708164402c6101b0b2030f0602840001154688040007186d00842c42401100009e40c51410900d040c08086403200c4111341182d80100455139010b000d40b00d06203440c01c030003a9a138a4880d6424010010081e008010380030204001811002c0d580c0098100d50500c0c0c001e0205640d02d0714100703e0740860540040c0075500c032034080300c0482d40180b2403507607012540c01142e80046540308040700709045148121400d000c24078051001c0c10900705107074460b03a21410070421b111103a6034050700e0306104461300f0b0001c00b9540085c500748601c50300100c0c01001220296a5207040c40f40d00203007600001c0300e0940d00b81c0301d2102940068518030046500701d490b01d41c0584402810000301c0503900201e0140f042400c0c500b00480701c201642d91049111024009006 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 101240386 1250 101239136 101239139
    0x30f0a05070807080705090c09040c03020d0c021603111216050a0503060f0403080c040f150f050315040504060e1902090705131205030f040e0403031a0d02090601020c030f0304 77
    0x1601d03061864021902c0d0b41c001c00c0042148520010704a810707241c04076005a41a03544d40c2808005000710490703076030f020707080c0101e15410b143c0650003401140d00800041c071071100c2e00d810584e034900940070200c114071a090000c0000c40d01b0611a0801c010009010729018150620401d141a64200107405054010801002149401c9000f14028401a40179240a01d0144844020000010009000e0010110005800702182400c0328003500d05500302603146c54551708080c070364004210f01d85000c16080c13030000c60154000d034162840703600800f1300c4c80c3c60f087d07810041c07001a01000e04100c0380d181e126a40381181880500030078280c402c07003c8a104c420083d90041040a00000c0d22580a01504000c11544082c20112500c10384150b00101a441038440ca030291452081d1540ca0341101c5c070126000c64080b00c8041214003890103503a042c4213040844449e0010312284041c0b09500070103e190200c01820700414055100d5014010384424200610209003014912500a4496003000a0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 101241636 1250 101240386 101240393
    0x303031b0c0706171005090f1b0708031806010302030703030f02100207060b030607030203131709030d0807030b04020a080a0c0e0907020a05011a0117040804270c02120901030f0605030f0a 82
    0x1030645e442911a00070f24007251a05022812280700070b805190020f80d07001c00140c1180054041811412140700c40c1c0fa5522114100001c0710342080d00e140906903c21300d0512030382a000030701141070f07030b80080241c0103c41c03035a80c05440d6002c2c02c1c0090019801103c400903090f00c154030103003607824041c0c00040303030a100041c100350408400030003580506105005011421040000809160394840c480e40070300b80b41341201104030b004010419a00d031080c040160182a0300112450203a122600c080c000c440025003040242c1c02001c0186000400201c000382100340c482d0001205054141041109843c01d40f001c00e9050b202201c8440151303000b142e068040040910941c0340b0462801240d0013084c1c001c030300003401c103907100f803a1034080d02d036440101e0240308082040700c00414004c01c00301d60b40f03403140305142400382642031f07020100741c64180380155250020034000e05c004022046c0d2894080464015401080d58400900031141d5450000c02e0a490821a11000700020002084034050b1440c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 101242886 1250 101241636 101241677
    0x30c050102011404031b03030b030a0c2912070c12091a030108030304060209010203133b1f0902030c09191202040507032405030d030b0303031b0c0706 66
    0x6400fa40b00441d001c20040442d92228442e01030031202c0030703ca50388040740c0c1000c502500e81c20b04c409500d030080000d6482001291007150303040300d00d402100516100f03100c1e11801690065024480c2c0807004000c500d004036640020709505c0b03803c81c00c0500c00003160f51240031a0364400d880050220742d544c0070511400806100e5401074500a01d4918519070403c006503449000240009208903000300b0381c5440780c1e00900684603c03620701b0106111403075850007540361004440c1080a070341280d510030350350b601807496410047c50401e41c082c0c0506440f040c21102000641040e03000d200041040007040c0d401c8223000a47c0903504030801039895580707a00070003c41050b082d041c00381807010f5100400054803400805205581c0480d40000c0341e558898054010b40503545a40000400c0c59600700400d8180301515400d1321401e6044404c40080e096060f23045071101000e061381036000348002104c4010200184084034450409541419040502c50385802081d802c4400402e008451100e015031424 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 101244136 1250 101242886 101242901
    0x70c1d07030b060a050f090604030b0f15010804050c091b07060605040c03060e0a2703050d050a0b0d1407080d0903111e01120908041d09070605220e01030c05010201 72
    0x103c038000d2401a06800c05401803141c1000425088000700b40707100c00b5038407881520f008541200c00c0306102c0c44c0032400c2800c0b2078030031030b840421030b140c400301d9140c0c03544190140f41c4103980c404010010341030540e04024800c0e42c0182a400e1181c9001d07409a0490340c61400b5003031076403055201003002410042040142c6002e011510100340c5492000c000d441d0351590700a40004601c0b00004d200d0360458141c008403491012940700109440d058101010750210040070b4117071400d07004001d241c40d9660401d00383d40f0354041c030690200d40d058210000c40d00c0039609203a102c011800701c1c0c80c0c00f951181c20300c0c24808003a54007030108001d4071003003050080d940c00c01100e210003164405800040503003100c81484403064502e0400041c0300801c007288506501a001c8603820405054945035102c9490346090050035000030f4140d10034020071006d0b00b000034040c0540340076413651400c00d00102040c21000400d844103080c001128440003800420440c034250107180103454011041d401c0070006800d45112 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 101245386 1250 101244136 101244139
    0x305010c02013603050c03090303040f080d1103030114030c0904050706080c030403020303010b092d01090506031009020703090e090303010302010906020f0606060d060902030c1801090e06010302070c1d07030b 91
    0xc1081d015540060402c4003c1641030070700ba80c42c0c405541450f0302d94029070000b150148000903012401c5000151001c0444030420121540310304000c1c4201d45d000d00030085112254414070050151074904a840741c0c45150203400c84071115003000010f0043c0605442c20b586d150041041404002e50081032550300a40039102c07680341d42000e6030020341c1c0344014490b001c0c00903000314a450440c1c0c2c56448020100103412003007001039a0512081c00b5200031309500c540400c420a4000070a8140007081d00c0c496584001c9130080c0b20f181c00c03000ca0295001080440400031540c1c1c01007071581800108500950514005603203943c114070000d030501c1050340048003954001301001c020382c400001e465512883c1540c03c075888401c5000104003600c0c5a03000501207500100030080804040f8000d40b103441690001903414120100064401c414580512040341c0c98540c000385555009400900290703100d224602c0c2120f0391000483e03001c4040540f0102c0400441c0180901c140c1e15001e02a0300410 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 101246636 1250 101245386 101245451
    0x1e0501020a0f1211100c081609050906040b030f01090b0c12070e010201060801020409020c100204150302130306091515120215280224010302060c070305010c0201 71
    0x2680700c461403039001d4a4014a0780b800c001d43d0400340752040d000000035196000880381003000c9030f20018050000782d84800000740d06d000c001210400988a441100c41182e01c44c04e030164103010500208490050a03140c0041e21040c026104e07407020446400c642210400010790800145000785803000098405c1d00c24482c1444040d03840008883c0080c0c0140311420041074480c90080140e0140c01668400702441d44003280000d283c00c442c2d0014505d6540180541c2c3c0e00c010000711100072802a070156442c00c1e0f4005100e44c8016009500501115140d1040e15401507a00d070781d8081902d00b009402c90b040803944100c954003001500400e1f00a1140da840158800d052082d6a10106030241c0041d00c03681e407010901e80351a903464101c030a50380c003d5018003001c0740c288500d001e0300b07010041c07040018816440d13601d40351030030103c0c20710b01070910720420f00640c0d203160204134032500302001e0b07541a8041ca00c00040010000d200b1421154299000422100769500c0c9a403d400181052501d1030314 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 101247886 1250 101246636 101246653
    0xa0f1404020906090607140105011d06040204030c060c060b03060c0a0810180c050403120504050109081b0105070503090907110c03060c0a030c1704030c0c06020307050c0105031b041e050102 83
    0xe40f0b680645000728000d0343c10644a4586080c0000305496403054004c481d443d00340040b03481c3c03000c101004581c1c1c1a40e0012619919040107000c22441030703100250220607403c00502185110341043e0020501808021030507075070220000e414120700303441350800814006020718541e5080a02a9480480e240da940728403842c181d4842c95035200c1400c20100c45a461405c43d20150003882950045c2d50084422040c0114a0700083e240d54024040d29000c1000000006004140024000e0745882e42c102989101545400103403000e42011f030080743c3c54001401172907925281c044416203368820f41c0c642c0104480302c0389881c201244100d9050003608200c080091443d0351030200c820f84203c1d0302e4005075088030000100d070140490034014001d00c030030405010038036034041d50711004035004514030120309544000c160386c0c03489090b0f0010101d4105c0c0880380c00b190701410103168019958140d01c0d43d452240d42c0342c0c0d100d551003501300f21112160262101400d4400b0f030710800103064207000411234032 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 101249136 1250 101247886 101247889
    0x4050108011b0305061801030606030201110a050715050c0d03050103060c03020705060609181c09060f020a140106090603140f0718050402040209040f020304120504050105040b030a0207020a0f14040209 88
    0x342d0140da54002070607210f2000c900192140c00008600d5001c0d2900072000c0e5850785401800780c101c0f4031090b40081d100392450002c1711f2020603c1c1e5181c03980000204401c0745086648140c4040002d103103000e000c0244440d6100b20814041c51600c0034050390000380960551810804032102404010105841880ba42c00041c00010b05507810040880d0541210707612006003089450f207040b0311008500480800d001450b5480031008c0c0340e852292200301c906516982d0441e03001c00c00f8102500164401c2d05a8400306203002c199403042d0341654004103100c3d45841c002d03402c0d034665078011a00d0310020000d41d84401000c0c09182104031130000504078a514044c011103c5107040b00007007903905d80d82c0b40401c045580e03560403510100409481444a01c00209000d0000e40003100c2c02e0b5903640d174244803a50b8140c4154126002d0b0b41058684d0383c281800d203c000356490300000e24150702035900b04044800350355038103c0f1400a08034004c2c0940300d2814042c0403c03486030001c007094002e50051100e150070f03 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 101250386 1250 101249136 101249171
    0x30201050618070f050702040609020a050406300902040b03010e0304030501060b030f0c160f080705100902010503071206080f061806150d021c0506070e010206040b0f060d0c0905060405010801 84
    0x4e10503440c0090f121030842c00003600038426544651240ca20014001c0455a0054060011112a900c0d43c02c0740d0855000322484210f140d00c0300c40f442a507000601d003601c0300c2c1a4815610b0500140c00003030300c00700101c0487e085503080b1200e40b0840d8130100b81042004403d000c0c40f005000b01944850039070401000701c041c10940902030f860b40781000b00c2c162000c00d18005c03000040c542c200440c0146441e00741014481e60b40020010f644900a80c0703184504402540258074080381d06170b54240c555946c41400b1a21402142085c0b44115198440052441e50803c1014000010000a07012505040d4902d020028440d400032610390005130421009804034500104680000d0700c0c04246094948005500200c83c82d4007005102c41110b1a42d00f405000110907103c0e002c02c4c2c0340c80d00c801809000580c0d03a4071049900410300001e01001038050f18510b0107041c0c0014000d4413040e00303c545030f42c41c041c030204180c010201c5030b96228100700d5545414018140100190402000081c0e16248503106 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 101251636 1250 101250386 101250407
    0x21050c0c01090f0e0408190e120a02030c130204031406100509010f060c0c05030d02010606030b01020c1c080405180402040b120627030d090209060108091b03011803020105061807 78
    0x408003101c000409100b42d443c210b4487c1000e041c917492000c000d02c200944030700001038186000f4600300c0c03454094100300140e07940205400400801103c072401c020071490610300e5400300c81054003404000006020b02c40d40928500554024150a280040010400c1d41a42e40043d100b0f25043d0300400404580511900968000745880c1c0c10045180c100f40400c4007075684501e07050f10540280508081d41903105009982460b079040c4212115030004a968003a80c10981c0c0d4040e80c401c00411aa680081c0c4203842d8610544887e828103555800240710121944641307800041c1030020001103160602c00c0900a44040300c81c5002070310001c160554803034004010082e104200600d00c03030150041d410030b071103035098401120ba0b905c8a15a550003d0078150800b00c1c050355400d400702d2100d601680c2c4080c0300340141d00051a0650410108048840d0032903d16601550b031601891000111028844004c44c001d80009c10340b801e040050001c501413603400761140c44400018801000e0f881000b681 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 101252886 1250 101251636 101251649
    0xf0603012102040b0a03030f0207061d01051b011d06010906030b0a020d090510020c06010902090f0603040305070f21020a08090f010e0d030305061201020a05030a050421050c0c01090f 80
    0x40ca8040038804a40107121101030749034458020b00000003095484082c8c0450803e85a003601c0d026955100b0a4811a00e01001e80d140501c032451100781c95441240685030090004d00c00250f805904480c80f42120490304182c3d1462002955014541108100b0240140790340b441c00c005182c83c40d20b5046420002804000d503940c0c000890411801d80e5800a50b29150410f09845e02501095130f003500035800030000321160301400000282e249924402e031070a0000207042c08240c00550810021076900042040f03044c00014030a07100417940b08038a001150340306038403a80c404408040c1242c410007160102d4800c652144180d0f02c0003807007220030382d82a800c00b584e894100c3c1c265800141e8110b100002c00c1c1d03802c42001d0306a034090541c181c109500904099410000341244012200e0a074400d0060500101b80e0810100c1c0041c115a481103921038014007004031240c1c0300240082030381280c1c050080000f940854036905c3d009060100048107070303090034031243c01c5150280d503101d20304540c407818 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 101254136 1250 101252886 101252939
    0x80609060c03090327010f020c030d08040507080d030902040605040b130209012007050a0f0812030a11120108010b0402041d04050c0d03030501150c05060a0902031009110f060301 78
    0x12000d0f803080042d503d11180c0303e60440002011030040c0b412102c83c1e00d090900203680c08995424141c0041420014008040d025240426441e6070540703c0c0d04000e041245c180c0703d8648001507500084c8003001c60170b0345595001c21803118a004000c10380e06280c10640c0b089191003060179a660711540c482e5a0303c03504250160712526803000503200c070003005c6c2020701e001e000844100c1d1005000b1840d00c042e0342e000c48500d05059240c0344e810503114240d0091901c154000300d5003884043c8020060b41d0300595400021030b113107440000ea0030340c542040031f50801c01c0b2900f0005010800c0207029030300c1182029078007142800e180c0390b101d045015020007800340c1d24a1403400718040c010144484611001c018000d818510042d14009004200c01d100310040003e0842c03028003020b104100741015650084010722190321140c052000800160400300c1e07151040011000540380203001d0300c08a10f01402c280082c51040d0028041c3e02c0340311076822480f401007003005122180c03c11075103d00008128095 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 101255386 1250 101254136 101254141
    0x12030606081b0408070306020301050a0608040b0c030a1d03030403080906060d060f090618030f020102030c0301031b05040617120922060302061c0b18160909110a09080609060c03 78
    0x144a081c8100e411840790390069220100a011448d0000d40c100d0320b0980382e80801964545040318111026131b00145281100d0b03010035192084640a960051040080002d280c840c0c180d5030084912050003401158002004200c01d054002d1010350744503003d14041d181620b41180040c40024180600505680d520a0b094020300c1c16a40303c00500d95001c40c041100c6888400c0a400b220144c1c00100c1c00074202015596502d4030600a4a000e034189000e12411039085946588031103680c08800d0542000c0c0c20740c00222980c4d035010300c60040c04805009c0c4080c1070400d0619060002c0d102c400040d103601048542c01a03101c409199020b41d0302c150042070f04054010b0b0744000b400d46036001940c04200480e009d403000c8034505660502080002c003c02c1a2401743d001d00c543c068813421544c00c130940b884c000a1143c81e564203d411030000c0c52800d042c0d5151655019000c4a0003440c003500102e9011621000b019001140031002d0001d1200900705850070124141e43d4840003000c030020b05001201 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 101256636 1250 101255386 101255431
    0x6031505040501080705100302120105090c0915041a040b04060503090307050708060f0f0f07140702030106031a06010c0503030a0b13050405100516050910020a0b040b041203060608 79
    0x8450150000034030030701855940307a00055031481280075030392160445030280780d0054024400c5503581d00c10184d40216507171800c0c081100502e00200084031035141000501d0155446000104ca03090001401640300c5003422014082003100c0384e0b508102e11001c110500440794210180c404441c40e501e0410350f40d5488a9001c0d045000350f40000700b40d84030700c22010683c40d80200d0607603c10a02000161129a40d40d0302d24040d26609442141080c2003a401155000e0310a008000384240429882e40c94400030342e000c203084486583c802c1d035100301e21402401000d0f09004106420007024600b8502c080c28940300c2c0707602c1e48000f0340440c00b056501c210780d20a03900c0b071118503c070000221381c1c01c114074038007410b22a841d01e9036011103519862410300019441c0303030900702c000801c106940c0c030b0b5800d121142050003403903050035a0038401e620903424440002013155400d41d1286202d042d20300700a052034074003101d0414100320100c2c203050038030b0410702c003540e800310ba07181d480394101b044000120074800 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 101257886 1250 101256636 101256671
    0x6030b09010606080c0301152f07050913030504150c02061c0e0106060212030615030c040603050f1605090d0c060507020f060a14180402041202040c030c0503010603 72
    0x51004100410000410951400640c0110304440107600d0342d0b0701c207039941400c0682c0f9100902a10800b0400c41c1e0394152083c2c0f041a84002823a92030303854020b504014210000e205407629825491640036030024016030900c2c141203034204c41012120b0b081c00d00e142c0d0300130b40320f8002d034041c04089404007503100703040c0c4d0710811646020310340103070001d50784244001803102880f820801004000d0306081d0781808008051096200700c5406034040c0c800c41514107080f4086520103002ca60b40b207080141a001c0321b2021400540c020300030010318642e81ea1502801405640004011580c2c0c0c200d031000f0001c4504444000c140c81030305500d8101d640d100301100095046600041c05400040b030010003089490300040200b142500845501d624009030004000b9140300b00c1e43d0510008200c1c80942e03001c801640050040100031110700561403110101180490708141e204580d01c07191540700d141035041130710820302031a0140c84c040c480001c0d0b02c0f001410760310061007840d041540d151455101108400d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 101258992 1106 101257886 101257889
    0x40204050f07021b150d090201090603020708041203020307050703030905030709050c090907110a0609060e0109020d03050a0201060504050906270606010c0809031608010e07050603060906010306 85
    0x450310b8400c00c513a189a000401100990007100112010f0f14411659440c006103201083c0001013850303080b6404142813603c100141008100441c0480d82030b80e082e10440f480c28091847e0403403541c428501d02901da40a0603d02000f099400700c6048120340d4101c040b45c00304c6231610012402c540c0240c400c11020b11082003c81c0d080e0500a42d070a0b4040221f0a0080c41a045641d1301414006040030440750260b8a8082008000e50762003101003500c400002004170400395130115034202c0040801505001c404100303002028400d41012002c6c1502400034042803c0031a505652810160384104c40e40740d03040f440c488118003444108440c4003a0400070301c0191664001520702c2d1004039020350b100d040c20410401240c5080020500044c1c03440c0081040a00c0e1600490845441340707082c444d5500444810003075903a480050300d07003060080701d508183d0b45030140183d00a0695 = true := by decide +kernel

theorem cover : BRFrame.Cov 101079136 101258992 := by
  have h0 := BRFrame.cov_init 101079136
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101079136 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 101079136 ≤ n) (h2 : n < 101258992) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
