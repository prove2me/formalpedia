-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2498
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:53:25.185986+00:00
-- url     : https://prove2.me/submissions/cd722ce4-ebe7-4550-a82f-7f135f18a0e3

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 449100719 ≤ n < 449280575 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 449101969 1250 449100719 449100761
    0xa110c0904020919021b03030703060504050907050402031909200a030b070c03140315040b041104060c05070f1203300e0c0306070c0506070c05121b060405030d 70
    0x107070f41c0c1100d1540c0c440f02281c2d8034140482c449007040c00a0040545040e148a030b81c1204c0c80b01c2d000004003952254680d0380d002d01249443c0c07030034070003540d100f13940c14a00d50b44840000c1c0403d141ca50040d55008030300420a130411884040208103541c501e00082d1429013100040990078524480482c1000c0002d4136401880c51444d680c07062013810050940c001c1046030324491040501c01c00c12140404050141e1030b4890400f405111114005c1c00710792072003689814030419090400d03014003000ca003e0150744500301480d0450644130140c075413000301e0300d41c05504000310700c55040342ca000d03000c1d100d0364001c0c4040284611740640300314840801603440481031014041060500c20300d1110303606840e0740104191000c1c2e40b5451900b1410150240d050164a040207142a40400c500d98118010011184641c840300d1086e41d40760b000034809030168104604a1400d10341e40d50042503000e4001d4a401079071181035070240d0600e0800d603005c40d5541c00008050b100b80740140243d12200c0b4121040c40c00d5 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 449103219 1250 449101969 449101973
    0xd0c09080615090c0919140301060b1819090203060f03031812010207060608010c0e1c0b0c04090504050610050109060905190b2b02120f06030f030a110c0904 69
    0x40d80c2682c0da0152040902c100010a0001c0460a85c3c07528100a010314060382201c08a02d41b006609020310582000d58508400407446c050007560222a0070103851460103e00814290349042c0e208160b80d0403e0050301400d00020b4091688002040b05010050b101e080c544d0810500f5181e0913031280c8a540107021544214084e00500061172a08461280c0346184411403540a030140c0840036000901c0e2010000703070b4039010341000c8001c1c56035035610902c90702da40b003c00c0826100c550a11080c00051070082000403102102c80380c00105001d6002c2c10f166440e0040c50036034004580c100c596820410034072001c2e10a81c29800c02030203090030070051a906142e4010801c0e44c00e4402d81d84074180d120541018000c0407580000030f8444010140d13542c2c143c64a03e002c491428200c030681051100c1c460300e4007595503100b9908441e2907011001c0c0c80b511468841c00032000d018101c160b06000340d801040382d27944200020f190300c2c5881d407108081403100c031980314180881009041e0158510b1010000 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 449104469 1250 449103219 449103241
    0x20703021209220e0f0a0b0c041d0702010605090403030c12050712150504051e091b010e0f0901121106090f060318030f041e030c06030f110d0c090806 66
    0x2582101202c0c0707081c40243e0004040054800b216042d0001d001d0049200444c4001080703030050301d40903240490041c0c6503402c54248034400c078801d091924114402c0409101c0d03003552502c1d0008070368070020441c2519540045c0c91390b00161030483c0442e0b03403807001031540c1e600090b505405001c0302004221a103072015010380391004480003076030003d0b17a49009000307140403800e200c0058480600304200700d20f49800382220f100608019450400c80314400100d8440700020031101d100c0307524250401801001f00156003204180c15007650211002080b48010b88a10758500d00900820401c1d009034006410f061440c0f08402c40d14034014034040000e40c00765200c05551000d1040107442640eaa680c41404101d2825400032240140c2c0c080001c070400080300f190064802c0e243c482010055a082141d41c6007042d0505200083c501583d0082c00c114041c00396225600590821002103803540140100340c02a620400b203020f180e6075151880c4042c107500682d002c000d004410300414980c00c209442803 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 449105719 1250 449104469 449104489
    0x1412190f0e131509230702120706020c12040f05010e03061807090608030d0e0109050606061b0f0a0b1311040f0e1f1503022818020703021209 62
    0x140900107010300c460498006038003544100c55005200318001303807500300f090003030103001a0410348030b42e140641428488808441c80d0184041350000c0c965018081c1107105d494004541c103075a066406d01981d80500d805020304400d00383d03100d40d815036407400c25608903016002e035000702d81081070300c400892113034900003500c079003200b49201d08841180140e40c59501c0c0104540100b5a0181840317000601d01d0000409058040c0c041002070020010b0020321034200c0f03030a9400a0400c0e80101e000c01c10a00303280c0c0050510003000705009802c1c4a00415680c640b0440c6201c012042d03110300404000d000002ca01590054101c003c40902d10100744c441460b4644400d1040748234503650300e0b1000c51540c1e00d9100560301b100010540c0c042c420f41c14040e145409211402c1d100240c2030079000710540824440e0081600c0c0d000741428000d050228144801b41c002c981c800c2c03206a0401c60110314030100701e0082d900c02480200150b640c20103868020300f010784034201c0013405c80081c0100307070603035031400c0c1c441c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 449106969 1250 449105719 449105747
    0x90709061412030405030a0303050f0c07030509090907051c0209070504050a0306270b0f01080309010c0305130e0c03090c04060b0a05090f130609060509090a0209041412190f 76
    0x1034001240b12000d628250320030742d80301c2c0358580b003035007016020160550007443c819600c20a2002c0155503a806a5001d441400801000a0010041d00103186440d40c000ca8200000c82c04903102c4540301c401042a944070303540255002d0003065200030440c58404522a407000c00c51038410308151a01e0041400078656000080509407142500a02107042d48403801e00c1100008601c4d80c0c111050070100484031003681c06007070702160040041091304001042790085a0103a4403103842c0300c2e075074404030b07100e401428582e0300c45848040700150b11034010748003500550003100d00c07640c0c074203103a1404c52070030301221a128001d1b8103081c8100300c1c9074641000d44210b140c8034141695202e8207207001078a005078020b00c1d15440429585a60b40022055210100382c0704c84050400c4896128010024003e004480c41c21450780000c002d500141031288885400c2441580c00b0854100c960359014284031445030507005005021500c3c6000c8445c41c5500140e4810605121690310b0f00c000c4014100c035400580 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 449108219 1250 449106969 449106979
    0x50c0a0f0c0503120703051501030603110402090a180209010f0306060807080403170907090b0102030304020603221e02010e0111070603020f04090f06030c050109180506010e04020706050907090614 86
    0x1c09041c000107008035207185400280c05611840c101201400030f20381652569026812500c0510f050f501a21484043e00e41202d00d0407103045000003004041e601c0881e000ea040607a20100080761900c0d42d01004140140800c09a210b8144070001400e00c04a090840100b40c02c10500304207498200800e075411141515007000700381d84a04081e240290404178048050b02e181c4104051004003148110075518409011302c525840900120381d2800241c0e0007031b501030f100300082807250b48541000141d00382140310060707003420b0507202e41020f0500100011000e61040c05508110b40c3e00880c001c1412a090030300100c03000100030b4096590340640a04024541d0000b9407079807402c3c0034001e6034000c1016140a001c4c18181c181114050326544c4001c84940d0700e082000f10703096011b00d61040c203035009004034000501c651140d580181101500b51070620000990044468880f40020b046042c0596404500e9041400d000c610b404c1040d0320034180e86244c5201400204140c2c03e200c0c11030f50007110 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 449109469 1250 449108219 449108237
    0x6291c0f020103090b16020f032a0c060a080619031e02011103040611010b10140f0909040f05060c0f0714150f071e050307120b040e030d050c0a0f 64
    0x10041c1c005095021300035000d03c11001c108084440e160321002d030000659429101d14009074403105036640100c41a506c607400d2107944c85840f0052000708178072866242800c840c002e00309040891700e264800040600009c0e0a00c08110b41400c024032480220840c00c00d03c9000b007451601d901c0c5a582c0c00c00d51503410700c0080a506419684229540889002d1a01c140d0307135981e0352900040c0152112000140f000e50808100039074510b46209030300c0e40b40319151240d500c0040188110005644905500a040001480548240d45070070024510451081407020204030305410704070320308040100745980e03266007002a40c0e4824114426544065807156031a01404200c0f00124141011104641c44190a203002c0180e10f200c00018079000384410303203804a010303504882403011003c0001c81540030800420100e00d00506c40c5a0410203202510780c0002d14b007006100040c15038000243d03038481d0340d01c0071640801200c11845115000700760420344034642080c02c00080d01b440801441c100500c82c4c0c01c2 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 449110719 1250 449109469 449109473
    0x6020903011b02010b01020f01091a09030c070603240303050d0c02070302180103170301060504032409060209040f1b050306011103041d010905091c03020706291c0f 72
    0x140044408109a240c900d8042c0c101241c0280207040320f500c01801072007080d4003000aa10188141d4028070b403c441c0d00d207250411503101c8119800d0241c035904d000e1008002d280c0c0141c0d42031280802914880d9000301d15800317542000c101400a8803440118100c40410404c006504001211030082c14a640422500303c500c0040c2e007060100c0c0d2000e500442c20204100c41500b004034038a040e40c0c81024910f5000c0c0a412080700030380024041c610108504010600204134a02e80e14032104404a40946441030200b400c071040e036180c10811941b094012410560a1509020f425242c4201840c1044020049004802146900c0742b004051140000100348264801c5403100301024a460441c1d640316910340c841d9022541404035a0322203c0307030301e00101306840e50303000e0640120180c030014416207a0758629075100f0128040c100052550070032211002900b18000c504c240314001040282402c8480000102003002598080c4942c0d08450300703208107104504488500ca402051a5500000328 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 449111969 1250 449110719 449110721
    0x3061f0e1302070206030c1201061704030813021903060b01050f04090903020109080c1605040b030303070f0e0307140f010201090b13020409020d080702031203130201080a02130e10140a030602090301 87
    0x724000e900170b2000010011074a80310b00013826840002d0001402e0340c1e0b0f98450455000c01e4900d103010031049200301080200340300b60740c1e054002c02c840d01d10f081c0c502050340c009041d40e40544414011104100c90410030b0124601c69521755a03400c0c01d10f40e1600b041c2040094040c41070340a040c2c070450b515200e9100b41b510135440f945400e0b9116040c680d0380c118084406540741c80c1c084103240384400035000030440341010300a645102c0d10190055042d031300d8044080d0342540052200070b0030495409480143ca540400ca5000184900103800428403161400d00844038107440996056a040084140018840000e03207a8000071440c0d1b10b103144101840010060b1000c2000a5440f00180729500240029a8000e00819108070119558445d91140b8058140000c9a4400c2c000d0b403522113500155000380c064a80c0000240001850505004d0004402c080309801c903070300c404a00400c100d056007a41d61035201806085a220101e0020440001c941e5207090200416554000ca1088419103007 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 449113219 1250 449111969 449111977
    0x1120303091e080711040b060405040b030f01050703060e0c09010203040b0a0c0623070806030304090c1101090b071103041503020c0312010e1e040f02090c07061103061f0e1302 77
    0x3840900c0082d40490500c0c5155400c40101600c58948154001d50030780780031320680141000203444c090500d403030481044010b003041c098194140c0241010350001810070310665226444a403000110181403203d2003200c03240041503201044c0301000884842e80e00001520b0848542d011004c8d41c0b5165494200c802c4403205030002c00310bd041a0210002c0d44000e250702100c2110300f10010100c2c0e603850000c4820103c107880d069090b0b0002c010a124482e140d4020320325403686400c2600550700030522040c2150030721001612400203070003d002200b9032100d0a2046007418400540c1094104140e0400900e43e030034001c1d092503800950311010301c10900964010540d192400040782da907644100c2c0c6107840491b100360212641c000c840c000c00c50444480c6002e25006400c4001c0c0c05500d50034040b400c035019100303d043d18828040f01c0000f540c1070182c4181500080c0c0200e4680c1025018880700019090310b0108a048180410241c5030b07001003105550982141c1d0411000190100c640c020300c5 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 449114469 1250 449113219 449113253
    0x402061818090304170a0c09180c15090812040e060109180608010b0d0503030109180b0106020705010e09070e240a020606130e060f09070b0403030c0b09060112030309 73
    0x11805080101140c004000b13002125a101056840d0f01e03040c12240740c4030010848001d0103070060800c24000101181d0000c00c2d140116820180c10381c0342a1122100c240c0c1130b60010f00400c03a06401201c400f6405085880141900340003403d02d00e40144c40e0500501490148a8401401400103072040c2c0c40358080700010003510070b00c0d03006a00c18411980207400e0502800d02250300b408070406840c2800c1c03855580043d0040081d40c10740e400c4c4082013000e0b1990341d0642540c00d01e40c070b2000780460103000c50320713000301000d8004041c42490480050540c0c2d00482059214140540c00c1102458211146000700e03a0100c0754941027080054118a152030383d14501e8040c00340215900500d5900000c04d01e01891040310114044102d95040c4001d80d100c003050419240c1006001c501070407603c104030358000b0150f0050320085a1214520381481d0442d1b48150001051100d0170824460840c1c445600b00c0005001b0301025030420341c4000031034130800d00040815035030344103400a1181c0c08040c40c031141 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 449115719 1250 449114469 449114509
    0xb0d0b0c07080c0c010810060c060f24031707080406200f1605090114060d09061109010806030d0f0c03020c0d030207050a0608090c040b060c2d010504020618 69
    0x481e007081e800f079131401c40c001300324081010400410109114403880c201100c5140d5583d150710101030340e8043c0540f0f18500710042141e03d400c0031899000b020007004009040e0140801c050f20702c0d500b040070020060004005009008001c4000403409901c21101900c0940c02c2c0701700f030224512560004255022601422800f41038030180c0142c41c08542400003111181040700400d0301c5208100107408203104418a48107600d42e6a04282071820141110701701c214400603001d6042d840340c0e0b0540e8022400c8405e0420002844001d940c0c00c0355040c0d80150007940140302080ca0818060021041d0010040511148410010070140b0170029119007000c05050026142c00c60710b0003030f6807650107008580c410341c003d0f1800300c0e03111310446d1101d220b1140c003001480701c100d80d2030510004180b00d814082d08a8001c002e418a132240c20004000d000c41c580041c4840a03c58844105041d60104002c07103459041000344009130780d0b020309855090840e1002a003c0099440000d2903a040e4540005100 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 449116969 1250 449115719 449115727
    0x1e0c0312040503040611062a04081516030c17181501090c0f0206060108100801141504150b0f07211206030b0a1508030708180102010b0d0b0c0708 64
    0xb10000c8050070403a44c1d0f9031102010034005103441034981f041100e20000b1a000f02c0030480080b43c40f44000d1200440b60020280303010b490b100c45078102030300f504c0c020364480984000c1c070240a881d4051448000018036040080e1604050000c0c0180078007800a403140a16901240385041920304064240f1004030440310100d11040d0020130f1450240f0411004510b05141054981d0091102006041182e03018100b80d5030f8010054509c180041d10021204c43c0341c40300032407094070900c10812064986001c0d602c4918140c1c140e2054907a6071030040340554104a102c52001004408c4441074070010658644c07106101c11600a49001c0c410015044504041048d041c82c0d5039549a440390030003507940d9071940d45001400c40f0640c2d06602c0020103586480001407181c91944c2d22440d036864041c12030040180d0703100d90451450b00044000e6866078000125955440c4e600f907075000a96030700380000d00c001c0c000c0b100002d09030390440c4ca026020001540009100c1280c100c102c0d40034030342c884035060322 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 449118219 1250 449116969 449116973
    0x11d01110a0f1b0b16061806090c06090609141305010f03060509010903090513200405040f0e070b0703020307020405040f051603050d031503140604171e0c031204 71
    0x80b640110070103685400100c107005142061140c400815100c080840500d07004c0400e020314403588240c5402d403810355441e81c1146540080403052072034540211404201a8694103003105070318802d0380900180f101035001040f40d113800600100480e0424860307607034070300ca031800806c00142c00045140d0840e858000040303480045401150140ea0247c0000c02c02503903919209401c03140654006400310340004410485403902d9036504803034031070740c07900450104040251030703003e032420189102034500e011400b40110700306803042c949500381101c5c05008501c0c5402c449070302ea800b075000d0b4040390000083e001e03040c2741c020021100350b40e40c050010031041c42e085c10001a041c01ca12002c6943d030160103807858080c0070041011003520780241c0a40b408a520190580007840400c000d2880800c040030300201081409031004800a2031a02421942ca0a460888285051010300c41400e0800b405121070342100d40b648040e04c07117810710002d035640560304041490340c082e03c6040a1103451711410002 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 449119469 1250 449118219 449118233
    0x210503040e180102090d06110d1109040f1416142d03091b150d090209060a080726190b07030b0904080702010c150e1506011d01110a 58
    0x210032910740600004024490304070b41e00741d00c501910301b40c1c0071100440c100d000c661544d00c03c420140e60b6000b0903103003100caa0240030640f03400c603640c000c0c0300102099600e0b46080070300845e00c0403241c003001000400041c1040010180300a004070810384544102002e520b4054600d0360f0316500492495034460800c1c590559640c00700480856a03000e0f0103040702c1c42680d403d01035902803d00c16010340824803001103071800e2640c02204142c0d00c589006e10701e040f07c0d40000020030020072101404512601c50b401844050030025119900900b400d0741d0801c84070300042072a130f042c0e4580200743c0c0c45190208a032210400c0b01c0b01120007076409000101440594100e40000e0040d2084131001d01a45d142102039040b2400030049580003554640042c1c00100507200820b6814030504010818448a4031100d0b030480e003c0c26902040d0f565403400380007000701005518000203d540800700e56240a42c0003d003440510a03c0c3c0d403504102d00400300791a8001e40f101c6040f00d4211080b07585441c5d007420321320 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 449120719 1250 449119469 449119471
    0x20a0306090c06090312211103270706050c100c05030604062403090203030d09030503011703180607050c12010c12110403020d0305090a090504140610210503040e 71
    0x940308030b904140010494024003000342141d81114040c0c040641d1a90107803071200e650413484a02d142c185000211058140c071a80c1143c0c000d00461a071280f0300b0b42c01c2e000c0401001c078001c6030b0240080d188100400b10004070b09094071914509585c03503680740032000c0d14010a52404964441c109180700c00070341c0e8060f0145110740000c6a051203000d038ad40910400c00314a09454800c0000359103100300003240a600040d428504c040d04880c50b000009016800f2164060030440004000000420072407400d241c0116a185d00b85014500d04452400c2c804440205200c08500880d00441c0510500c20700b031100e082503000160242c844200854400c034001c01c0341403441d80c042944e0030b2a5440c200324034411100b04000c600405850300d42036408001c1c05014942040382000000c00400040d130b11038261810090140c420040784038102460000f56a6204002500060b80b12104216606c1c4620402108890314649101d401070640d0f411440300108507600a060b81c0f01c002400503078000052205 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 449121969 1250 449120719 449120723
    0x605130b19120903080c070203030d0c050307120501051305090c0a0e060307170628060b070c12150c0e1e040608060f07030b0609040c0c031d0a0b03060409020a030609 73
    0x90701001d5191981081207410f41c11014000441840015a0070220760b401802032900040031030303040081c940300d284240c500c22003010340014004000e2102c0c0e20f400042031115806114400e11007503040201084044600d40718948481d6254001f20381d0040c07044c1714107014210040d00c1e00e1202030f210800501c000c0c4054580c14024400d02000182c1002698150480f48604802401c81900c0d08004841c40c0f8440c00b05504441c6000d602078810418248a488020700180e4240750300c1d4552030130500d20b901e5007940036500a48100405a0000b003465100080120502a000604070a505002c0302c0c00f0710a1002142c00000643e2a503c4104600c04c0303a0384030b043d0450301031180c5a103901140c1e803100c1d825221640c0c981e40c80303000b20b110103010782c00c0701181200190000d41000c56800000c1c040c0da044407003030004035240b0350802d4282750344a071501644110840c00910318480500108401c1307030140c407170340546000c00300100318543d0b15500a4080743e0b070020082000c0d80e8507820102c004103458181 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 449123219 1250 449121969 449121977
    0x110d0c0213091e08210f071407140f0106090f0b01030b010f050a14040e0f100f05010c06140414060906040f0201032003160311040806010605130b19 65
    0x1400c6044140b0b008090715558001080d5402885400039403020f00c0002d541200c2c6200c083c0514503214550078a40000003181c100f000080341000c0e41c0507407203440f000d841c2d0000c0001c5410b0130700003030708040300301c072029035100e01d000760408502c0d004d5904000c200c1910032041d500f01400050301c54456048161444c84510040095061001c015401c690701c01030300e20301003101440c1548041d4042e90243c901c4050030700745142015030641b0000c641da8000e422840548070610700b03011011aa03103540703951212040d2003814030142800030b120840c4003548509810000d520840c0020060300c0d8020316101c2c2c11280e0a81e0325414a4a040000c0c6000d246007600c00d40b040704002212103500155140c091900041050b0340c01e005500110040c0ca040b2010791050650703c0440d83c00401408011485810182040716403500742643c01020380304501d0040d215000203002c02d0041c3c41c400b103102411140b850800356079819a0381c4240080e003000e9403201e811410007040c07a40d00c180d420600c0c0302c585406a61 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 449124469 1250 449123219 449123239
    0x909110604031214040e04080a08070f080a150812090112050403090b03090a050a0302010f0c080105030601151806020c0405070c0b04080c010b0a080c011b05060f07110d0c02 76
    0x500c4064003403480090f02050f4521034109101e805001d440d8840140001060300c0c1c00d48901010501001c2a0341c02c0f1142000020038024495004041d207400c245caa1134410158040c01c2c00c01024000080d1102d4001603882c1406050400090781550092001c02c0980781020300416002405400031301707100c0d01044801d180c440c0c08020034403c140c41a54540c6444405500b85042010103400040c80e03410584560314415020034010800450300510a5001050450b2554000402d40300c0802c1d411040c84220f9005101c40c1d0f4000c580c0b00d0544400312200000204041070483d0350310745078414a201070540400118119502141864078100c0c2501c040c44551100070b0304580081032050701900110705e0101080010b280107005001c07501b0400700100b170541001c800140400007903805030003954400e111101d0701d560017008040d21228140c440c650001e5140c5c94803a11060010051740d00d000e400000105583d025001450314041c1100489060b819040e00181445009150591180a28031 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 449125719 1250 449124469 449124503
    0xf0925170c040e0121261b07060201140402040f090206030123063109021605010605060304050d03090203100504080a140915030a1d0a14010501150503040201020a0506010909 76
    0x13402405c40c0c0c01070344001c2080060a44076200f400d2042905103594150f000003d1078221000c402410000320711040c5d110000f1102c007207562030700103103901450559042600c039564040c0c000100503440398041da008640b15401941c2180140aa10b60096210303e02000101d0035242c140e1003018150004820b54000b40202820840280a0034141002c841110304c1c0c0c8001c0803a601c91045500a42607004250b141d848050320b0302641c0081600c1002c2d0340c0b688002e24288002400780e50f0060405032000c40c9142416180d5030303110b10044840700c081c15110b181840c00c54408001c2c0d0a58030007226000c00460800e86400a1150b0080a0383c100156000700c0c10012500e10300104e138094000280302c0700c0480402c4c0c040d0422074000518511880355200c2c1c02c4207412048031840104090303035101826060f2000e250504448501c070444d8a00c6a140c60010700400002003401070f410b8100b810403644a07a201d10040707141c0508a40010035500030f003000090300c5c048c15003203603480504c0350603903450354500c078 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 449126969 1250 449125719 449125739
    0x12050705071a1603030b0306010605070204060b07031e140324121c090f1e0f050f040b03420f070c020117070e0f0925170c040e01 57
    0x703140310002da04204142e01c40fa50500030035603940c51090501180340741040001a00b8078409900a40120f100000c06c1000c500d80b0f07100f104090441d04103000e050540d15180140b107140080c100071200d0308681600ba0600707000e403a405136091169075605580f4685070025411004001d040c20322446c000c5030700d80d1620326000c0390705154186444000d024601d40e6000d02c14685d0041520b0700f040c411140d001203003d02041e100c14000c2c2c0810b41c0780384042c480751801412081055809101d01490b000818000c0e566a01e46410b560074085801040c02e142d40b10000b4103000c01200e51840018221403184840b04203d6a06410755030600e8dc1400c44d412030441d44020700804441d216401c980140000b91004c0c060114440a00e00600d03200a40a681440c0d00f001c10700305851312004100f00700e81d61035041ca08100051000801a03c8911030750816598100c9aa0782d4180d0307604840001920688001e0710072088061503034100300c0c0315005400d01101c201e0143e8003a004085d04101c0000002c1092108 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 449128219 1250 449126969 449126999
    0xc0702010c0c180606021c0828060608060d050307060207020a181b14030103060c0c08072f0102030d240902120c03040b1f0e0a0f150605180d1205070507 67
    0x10320b54031442c200000d1f803030480300e03968020083e45074200c4d03000c101c41d0680080c00325452000c1c809500000c84a0030048041e2007000010324440c4144107014a24001903008030584140703581c000c90141e1203168510008071002081d4000f102d288055801d100c50b4004181c11100086e1205d042140c00390f614050708503508040700ba08191602401c000410002e82d040d400b4400d501700d54580040e0455542d51100c20b15481000c098682e02c111580d2051007840701071041c044500c00015410100c810140040e40701c2c0600026a508503568000103003070300c6111f100006821200c480c0540206443e080d1501c0250018072007a240304141c200000d011610400449014540200c2c411044c3d9a580314210795240c010b4071646d211310403607100020203106d074625181c000e800100002c0341e90200c41c010351044903506803036410120603140d070800805811408a904200529802446002201d0b002c1a0340e01d180c0c0800418480310200482041030340013000c1d0408a201d54142d502c00e507515100d503500604 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 449129469 1250 449128219 449128243
    0xd0f1d01060f0e04050109020405250f1205270d031d1c03020c100606110615130b090c09150403051009050a1b0515040e0c0702010c0c18060602 63
    0x1041100c240714200f801c09115034800e204d00e00104508000307901040a07941c00b65401c22941903400068060b2030390307000c81c0f440c407a101890a03a11055000b040204000c418014070b4205030740e078002080c03901d81c80b1210110703c10346402c04c00b4034915041c07150341d070b440000c2c403071000000389084032100304440d000901000c0141000014601403055100760040303d1110000d403800d166003084514100340042c0300c03000e0502c2901d000011031516000c805000690300724031099490b0020405c0220800581c80c900011000c140c1d01000002851080c21004242c5036207029845880c500400481a05201c02040307054000c0c3c0d40005c00000c4d06c00360b00030a00071400020b01c80d4014070440740c8102020ba010542140c065022a0b0914074540c50307070306c02501811401d903265600b040090105040400850030325010740c0f1009480e2610b000c0d0180d2004002030010340c0c0c41c0c140081ca65066a100b25030440d0750310340040f190018290740d0700308030320020450100c0b42030240c181500085c20b40d0010483c2c2041030 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 449130719 1250 449129469 449129489
    0x9050610090f150e090a060e010b040c02191e17030106180b0405010f0c0f0c1a160b0402030a0b0a0b1e090a09051c0c0b1308041502030d0f1d0106 64
    0x25041c079130241449030300100303800c09038442e40007003001080960090f0b03a41c0c101c41100002c0c6417450f40d030510041d00d0308101460b056500070105c2c0004103100f00f9407030b02466001403e95100d807200030100340c0e84ac200000043d00f210340e5041c0103101d4980310741c0214100c844030b854103020703036545c0e00d000c0400b1000c52050139116602448108040c1d4012503e644200c2038501e0b001203601d4031585c0715000190b07016416a0400907100c010320080c803222890803040348504159904156042c484102264080007008000200400100c0c0854404200c4803001690002050803241341c617800d02c50090400c062620311801c1411006100160240070042a03104007402c1c00659650f1200e0100103414076810448052080c8030810f000420402e180c03088001040c4c1e1480e00c406050708044120783c074007074202003034015103c0c01d2030006104d010458040703510070b0700322110210b9003000607810744c01029403101c2418101014400c00e0401507010300c4405aa03482c9a20325041c564503080e00301c8900340110a008 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 449131969 1250 449130719 449130761
    0x12030106050c0102040302040606020309010e0603090c011b050f0a15021317120c030d050a0209060a12061a0702120622020a09020f0c060703090b0c07020409050610090f 74
    0x40c61180e001400c01d800c5400000d450325907658086401c40c1c10030380c41000140c00c00300b249403003580e2005d134088500c04e040721180e056042210380d4540720b04607006040d050180a0302d0050586441800710307010141c00c0000d45881c0d03100c101580741c4507152220304a400e200c10521005202c180b03413080d143e800f201c0d00720140842e81000c813800d4030a20414800c1d6041d2140c12011401808048014507c0030a03042c0659104e80510b9204801e50320060302a801e81401881404901d8072110151444e1020501d01200d049030301e014600014100c582094411003000c802550648140400410b100e52007a6099900c60b89807500c035586440b0309440103011f29100c45035544034140f00c0040c0740c40c0f00c0d0005014100003076541001900300e90140e840903196030004103049007201001d003c0b080e401041070400340b041b417074503076119000400700410171803640c10b0114100c0c040d07407200d0b0300400686600c00d086480b942009030340301da0294028030078502250306004c0b0900400c2e00b10b00030115244020000e100d50 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 449133219 1250 449131969 449131979
    0x8010207081602061c0b0a050303040e041704091503112d04021201120507271802031b09160219080c060408070201030b100804060b0112090311070503120301 69
    0x250b1030700031030580c0e10040511a100000c0185c2081c6140805000300c001094034070700b03080c030550b00c1ea03039403107980b0a42052104000b200c2101d00d0b460f900a6210004420b450246940c0328200d005503001000d0035407a040452040e4061482c0f02c006480c09401c0100f42c0c005c022080000b0318118043ca0669000855481c80d1702190029200900c030070001c1c00941890800105e03860100000d81c03112080e0100d1824040c280300081c000103000d0100f8004655000c600c542d041e4502c264107040100741143e0b00e9100d0343c0600300c4890a00c1c2810350007001d4039446007414990402c5843c00d034545520920b11b00020800c3d001708601481403102054010700a20440c50031041d0140400c05815241c8642c02c00503001e200c00240031081c4107503c81d042680c0c680381c0318000103003250340481c00035000350941001e1140d540e03000220664400c2e400140440c0400c040401207408101005000145506104504e0200b68001d26000203884261003100d040d240e46104041c3d0746c12800c3c2c80c20803546010401801 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 449134469 1250 449133219 449133247
    0xb0604080d081b041809030509030a0b0f1317030403030b04060603020d0f020301080703022e02100606140d020c07150504090e0303010e04021903020607150c020601060e1c0602040f08070801020708 86
    0x1d2250023070a00c02d0038102d2501c0031900340b00c03504104031a1180704600700071703444802015007a0058030b503904040402155954a00f50492420801c4481c0080030002404042c0700c7c1d000044440c001400034411107584150150207500800381228020341000b1a00c28445414800d60703040b20080c900920445181d43c0078894210b0070400d0b03a640114800310b0013046890818005421050164006d210b500b120044a6003141d00340d80141c02000405403c241c0c40c00c0600702a200705180140c00160380707880c0001081d1814800d9805001d11030103030031604e0b80385030b04180640102e40507840c0c140000d0206e01e45840c4c80340300074040c42d52030600d60b20116000d82051301e1103504100803820011415a220380005800e03402c844000c40e802007900310a008181040c1c040d02c0080e812500050426504055000d050042ca50388058003605808180806040d4544144413215410400440d82c5a84074016140016428022010b81d440780490001c0c01180c148201c032280d81d04a1a414201000d51038a92 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 449135719 1250 449134469 449134481
    0xb0610050d0204031109090c010804030503090109121101060f030c1a0d051311040c020d08090309060c03070318030b0f2502060907050319060b0604080d081b0418 71
    0x8200041408031225a4409200400240d03014608280c035012044c0c0401c04d08503c01030800c0b1840d0041001810b4a9030080000d5030000d905041c8103450b6500c5005281c0105140800900519601000110300c00c0d0016400d114086c050002813000c5a10381c2d0b010040c00160f80700c010840520440104030102111917064441d80001c07900c02d150041600c1c0440c161032064640e000006441d4242c00c04201004000810198064400b07001c0d070450280069290001600c080050103280400103040070018022544e00c03400051641b51103030b00c107410640d0303039170002c1d241180452260700b5880074030522004601d040702d5000c1104810340d074550034803803d1010040c1a04c44140f044003142c0b103141050401d850a50183c5500404d000c0c80c0c000c030b06500c1d00310154031240c001e80203000310b502000d030000481e124940d0001404078484081002040d2640705075845981d99004041031905015440050180075180e4007240050b4004901018841840f0305c2c0b04541d0307602451510810313461502e8000c8 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 449136969 1250 449135719 449135749
    0xa02010e030408060a0b0f06030406050a0b040c020705040f020f1c0605220f0c021e07050a032108150f0d020415180e030912120d020904180b06 63
    0x11034900162140c20707195410a0304103034410b030803007010481d41088902c143d600c80c00044a01c0c0504540141c0070071614400036001030401601c89001440000e01500003c81074040a002084128100103002b07455054901500b4882c0781080d61131101402d860003558400080b00141c039262107000c2d030310441261180844080007035125000040c1d5031751100700702220707000c030554002c6220a103a11528129080508111203451508040c0020780d6800a49000d031170b10449010b00582103040410f601d050708d0f0b0b0748610390040403078001000300401042121110040c3d1903000446031103998054421070344c100d035010820245074030a1060342c1380c40140e46000b00e0000e04841034811003500810262102c04c00b40d0011500e0340c1d501008407518a154850444c0c0203d00308100140b202e210480e100c2c40766405007407241003082c0c0f01441c082024800341c001c2030135103022580c0e112540c01d0194069003169500e127210791302d42048540c203001040580c0b41043c1e84441d501205646040400011309881218 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 449138219 1250 449136969 449136971
    0x71e0602062805070801090f060605031909021e03060109111c1b0e0117011827200f01020d030c09030203070e090105010f0e0412050f1201061808030f0a0201 69
    0x42c0c1c060781c142d51080314010111070b07403145125030600301c8660980d41d6003403816202030f1a050302040300740d40c01025650030041541040b0345004904000318040c05000c1c1d0007079803118074101520030400185c294040100c006030180c5400341e13a1919818100c81c00703942001800b200410420380110152080003c0d400390700200000c20f080f084004d000308540a081f81c002090048003140740d19a00040c03020980d84c0d03210300c41a44c4e90b0410004840e20280f0541100c0116100d406070000000c0d00c1440384209590751b40b003c1510901d078103101d509840385030003401d01c884081c0359185003401c00441c1c140010030180c00a1001d8884c15000714002c10148031400100b000650012005076000c2c04410f00500c41c072505000b0500f4000401800c64006901840c1c4000000404000341281d90002561040e0019000c2c0510030142500761414420810741ea820740d0b42c0003c19144a102c01d8081c18160390141d994202c00c81498182c96410304c0130350080310b169510074480c50b81d6075280e40000785824042440 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 449139469 1250 449138219 449138281
    0x70507020402211003051209150a020c061602090a1b0806030106050d080304060f0204030f030c030c061d1203070203220e090601060206070f0e090a0617071e060206 72
    0x260056083c10940700e0402e0030001038420818001c08010010342c9070540c4800500d0104020009030f40303100142010b082440003c00c0c0b0b17041082c0280220a404c40c80600080d40d00d4400c640f15a00c61502c040c0128030546c01e05011440e43e00341c03807041410480ca02d6a12141240b80d03d00242c41c0b4000041101e9130640d210079020610b038946034240358a10b0702c2240080c1d10390800d403900c0419224410b07181c8054510610003000400c1c0b130300045101c055054100041c042d40c00e400d08544418403000c000e0401800c04800a40e517501080398040303104884400e865040c107134000002104c0c0700660f01e24006034414080070a480c81c007001080b502221450413002140c0d87d031000b01c0108501210300740e80d543c00040040241e44d80600040764404c41d64903100030721003000c08010740700e0280d200d006c500a4200c0d10000d040d405481d030010000c1c2081106800300420491300303559594641c1e00685400f0042d0342407041a4000820503c0103881aa401915031651031122401c9100d03402c201e44500640c07404 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 449140719 1250 449139469 449139517
    0x4030c02040b15070b01090c2001140c12070c03050301140111010f050702070b12010312020c1e0f011e050c0a150606260604110903010f150e070507020402 68
    0x10071030507900c0c2450030b10300c1d190900e5040c105c4d0107090517409071000500f002038110391a0380c840e484400c0030180c0c84041c0307040300c01221042c0c01000c10401c0c030b040340100d0000740603c24400d0380103018035444a41c01c010f03030f039540c0080c1140c103040140070080101e6024401444203840b84000704100e854185025050b07401d01002071400c3d10000c0003140c00643d0f0702d60610a04c0c0c2e606020717200c09000400e030a02d00d40060b80644101e541d81c1480060510340f081208040403a1081c8800d00c00008018004141c0118042100441d01650800b280c0314003142009030845502510a00312050000d2490702c06c3c8800d0300c50166219800038400b100140120741d050000161780c1c820480301800717900000604181800e101404004480100c001901c421001030186424452007480e8048000d980100c0c045045030380000c5913000300007019625500b032403003400780c440040c0c0c820410301000c2c44aa6a01603540c22409002d94002d40301c0c080003c808201e818050300f4070740c0090201c8a00120044a402d80301 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 449141969 1250 449140719 449140729
    0x60e060402121605040e280b0f07080a180b0f09061f03020603150d050c01170906281d0c060f0d0203100f06030e0f0c030d1404081c030606031404030c02040b 69
    0x2c0c80310b005000000d1b09030806110101c0a400e5019427404807200150810500280078120020900b00700c480e202d50071815800310342842a80419400b400341800e90070003140790714800380c003201c1d2100144035440006014501d02c87d003007005003c130107504440312400e580a000c2190320052013032103009082c0c81648940c0e00d940d9491102c0500903005002d110328030600050102c0320403070350a01c41c005902c06000340e450011800c1904690b000111100301340110041c03042001c44a20301d01441ea240002d50180208540c12180ca250340d1001642c1c01c7c5a4407404001035801002a42034010009002c48000d20a1a40c020b41d001900700c140300801d281e6a05214001041c0c03030b00103100113900d1b43c9121610090400900c81001804400b030640a811000426501c811000051040041c10001c02402c03c071142e0884003d4101c000030b41c6da00704d0102d07840c4820035114401500c0080e00e0f084000134110b101c0d10130034444449400076a19180c945840450b1565001c03032091f648a0741d00d260095840d510 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 449143219 1250 449141969 449142013
    0x602031f0b0706060e04080d0207150e030405040b030d090b222706150e04020c0f0a0b090a03051603021501030507170c0d0f0f060e060402121605040e 66
    0x403103000d00e594242c9840c0c44000d95401d540300d5600c404001081c800001d6842041d103192400300d00f001a2030f01c12070700b069450648000041d0b5502403602c56402c05108011000f0001d0b0307202a01d050002059074400c0c940c3d600f0303982d22110009036000300e0900c103040c4944000d00b110307180c0111800c08000c84980d080c4c5220b100d580210380d0302d03103a55000103041c07200d40102da031020200042081701a280420058000d100822841c2c100101844c849445656a44c15503c0391f688100854590207044403140c1d50721508103009450107842600022140ba100049080340c00794140d40b102d050945040e9044110303501300340120198002c10078514030a000c2d058031075000b180036900900c601d81c13070060400700400c40c400141901c3e410011400032251900d02c504600e0715805402e0b1143d924203030808450030a80003000400391810604c0c054290a8001140c5000f00e0080f5100e074403001c032600380507540d0f5030440940041030947c00350070046440e21b6400500c01844150580d007a2051021501095503c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 449144469 1250 449143219 449143229
    0x160b1909030b1f080318010f020313090b01030b03030a1d460b070215090603100501081e040b07052b0b2202070503070803011d06010206060d0602031f 66
    0xb05540d80354225100f8651910041455038055850b101040311340c140d6003010301840606000500d80c2d21030032144208100c415001d02c2816000c2102c3c0c46040d041c000d443c0000f8413500003400c1501c07111640c075011040356807035200d030b8030380d16031400060210b03103034546001840a60040381028040344a40f080400038a50501d0105111610314072010555243c0300c441d180c9039000c10846000348900100d800854a05c19011142c0e01030192440c006103230148150fa15881d0060000300034800d00280d07070342c0f014040d254242c0340c0c0c4009984010158050b081101d0660b81c2000c0c22801250120380c1391000190407106500e445071070150b038071074488003090205941c540b0070920342d183e041c80341544d441000001007040350014044503088141c441003410000310085a643e0028014003044010412500039640c8142442c0e2250780d1072403c00d0648203002140000c00f0300c01d5001418030f61000c981240308039002044503404202d80d49038136009410003800014030310b100d039018a002ca100000f20324000c003 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 449145719 1250 449144469 449144491
    0x4090b07081b04060504140a17030a080601031b0c031101020a0c1b06050406050a09091103010513050103080a05210f0603120306150d0b09011403160b1909030b 70
    0x410520700c8540703280e0032200c80c110b0310b107000e00c03050003e40d6108049904844440c1d84c0f00619030319460000351458140d03400980c49420302648241080400b001030f11100301140c031078403540c2c0d43c1c6400640c15030b5039100160040542a802e45402280102c089410b4140245000c201d543d00c0800c007582240d05c4001000041050b800c021020002c0d500c0b031910710400030400004086e8035111028040e40034602031a02800004111402d0841c810705c52040108040002400f8241c6040c485050301e82c0207014a0340924090032071171500030144d02645040703d40c8181180c1c82c2c02010382080b241e03504481c03048408450085142010f0100e090501805580405089096402c081c0c0c205498920f00c140e04600f03001c002d0007040010764800c0c1e43c8056044198580310381e42c00d00510800700914031385140560180d00d00d0000300f442a00b501d50b00721901c0f070036402c403118550070402a480c030880350310034911a104100818140c40b4000c000c0c0c10702000c03107401c00800881d10f0742d807240c04d030301003c4035286601 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 449146969 1250 449145719 449145721
    0x21201180617030301030b04170a08010e06010c1502031806040c06031401060e061e0d05041b050d080d0e190201030b010915030c020c03010911030120030109050604090b0708 76
    0x90320354030a4000400307a9010303507844035100307502568490205210151440401000040034801010341d00d04402c2000c0700000d41d10100c8990103007840c0700038040d00401d00886800280a54000e03100440d985400401200ca01c041d000600c40c06540300402281c00c01d51203491410301e510082242e2400760344030b81400c0c8034107401d040005085548000d80c0d00203040e18440104581a0082e80c42c030a100b45c2941e0340381c1c2c0c0f850381807403004440031a011040101c0000141c40c01d01030246034811070203507208440d079180e24000e024040e0403511441c040d81e5409aa240e00140025030034400914601c001114007280003140644000d040808030030b017800c0c1783c04122800200f190b078588940000c0079024207048602a003030a03041448800010205418542e4981484003800d000f080845c5820030001d000b40458140c0e031910700010a0f1140b0120300a45c240044403401904441003180441d0f15001d500d429030307107003090002c054400540400e401582c2d0300c9069021400305441c081c410007142d00c4000c92 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 449148219 1250 449146969 449147009
    0x207051207020604170321060102070e280906050c070308100e01091d1609051e070c0c0503100203090c010908031b070803030a1410050d0b0406021201 66
    0x51181419604500080801c19000141e0f540070649050300d45280503010101e011074002451807251071288800c94081076100021005001440ca200c0c2100381c2c26220380d2a91041c00c0c01c4080c1d02610030050007030070001840c1011204603050012408100c0e0f0200c1c401995856403130031500141d0f10240c03030010003d0490300303168001c140300f03411400e03d110140e012443e0200000c203220040c00f800700e0040d2201413a900c84480317001035a8145a000040d246000040018104981128411261101d080400243c04270000004041e441025031a460b01280d94014003201c030140c0c1c8210494803241032440200712a2400c11040700c50454801005a4030306081038550700c1c008803565030504001000e04288a00e47c0c02005486503100400b62044100310107010071414444603400003074803880003108115901c405904225010365500c00291000c0e04c1d1000016074a1034140541500a23203083c00410009240060345988035000f8003006041010000b00c40004030800e07449444404401d84d42c0c1e0700 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 449149469 1250 449148219 449148223
    0x30a060f2408070506032d0718032d080c0d1d0120070e15040518030f130b0711030106060201060e06060901021f020a0810030b0f060406120501020705 66
    0x2404211210a8150103140c141c030b40e55545228042c10340030707220200103d003110003291403c01120820100c0c0441210132003103507204203103003107a1160000d40322200c18048241c00d444881c05807a080f031108442e0300c2c030002c14020f050001000c4504222070318004da0010482000c0607001c68019603001d0040d0040102c1c00070010807540c2d52504820800300d18022882ea00940c8101d5502d0495040520403c0d0704040c2e03070b080c0781042d409400071204010800650030310790180703607140f81030440e0100070645500382d4059091101c800d80038003d510400038055010400b00241000d501003001a001003a00e801940543c0d40000c11b0898910f0701307102400c5124502800b032207002e04014402000b10500c0c000d01d10000100140400740a100c2c001350f00085039209110100900d811500403980c101100c2200c2c7c00250300c80f01f141000541843c0128010060440713071081101c0d04a40d50404680741d9036085984080050516540b01d43c0c2c4844c005041030301d0a500c90803050060300016140c40160810303034 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 449150719 1250 449149469 449149511
    0x2030a0501150506030106170a110c0604150203040c1206020712170106020309031902060f130305070503071206050a0902030609030d060509070906050f0d0204141c050714030a060f 79
    0x504c40c103c188018048168441c000095203110030782c1a8084e52101e010340b13001420422441a0400e0001400d008901d000248260186228940d0401540410301855080380801e590080980480c10000c00148034094254002240291001841d0140d5680c0d00c00c0050a00e0b03903400089880141410412180790002030300400160025601d0f0410041c0000d89543c1040112240303000c4402da44002d5450f5031003a11110f00c6901c0d240c0f42da600c1d540c8190080d2440d80d00c000c40351407043d0100440c05040114142080761155001044104920740e01c580c0a000d004204030416035503013081d80c02581d4204040da014007051009995244051503055040d01e1081d00618040d550110a2241c810791104074901101c05c20700d0040d071a024000c184c0340403403046602042c3c3d540d0000c1030110b012650006010340c810740440300b00170002c2000d4116680704100e00c001800d943c2010504100131003001d20f905080e02c000500b0780305d20401c2c80d0380c0c260444400e520709141c415034030312115a100321908440 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 449151969 1250 449150719 449150729
    0x819120207060206061909050903090307060504180f020910050d0b09090303040b0c120405011401060305100311030c130606020606031516051605011e1104030807050a02030a050115 79
    0x941000790a0850207507440501401c0315001d442c0c049400403180c0300208500c0302420000d04180b21718148400c01c07a950780c20030759001c0d201e40925400051000d00031001c84048803041200d981c07906074950723440d2009000e0000200c0078107400300405081d903a00c02c40c1a4040c104c01c3d48032036840e500d900030080100c0b00e0140c801401401181c080c40010480001503c0c1e01540c81072048405a070742c201002160301401d20309020461183d0700744020841e06400c64150a2440b60558000380e0b40c1d82001c03400d032a0140e4504541d078003041c1082c004644d5006035501c0200001d0200c0b0001c02070070002c201183c00907800c01e0320341603580c4018021607034144012900700c00214010126075488150204004030003034816900307046640a8034045030302400c15600b084007444203131403e1518a08009020b4800000c4480740c00b0a6a021006086058880c0a1408810044d25070401d4250381c0c0d003070003a41c0500c00544983c0300e0300040c44010b9504002c03d1500314490030000c950604400240e0b60301080716004 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 449153219 1250 449151969 449151973
    0xc06050a06030314160203070612050f161103130303030b0f1014130e13030807030e03040501030f0b0607080d0b060f1215041a01180e0f04030908191202 67
    0x1c10008240d1150141c5910b44500d070215558802084030900e0042c1c04010080d014055050001292500502140380009202505016558801418090213501102c041e0400c0f00320a1103d13100602c102c0308030340072414070702c212454000c2c0038a0320400d85060340e1085000a40f103003040d403010305001c44248208581551503c10b5107203811005080c040c80e149086003003072008903d6500ea2680c0c1c0845800404030f40c20310000608051620703543e4042220000e80110b0f0000010841c0c4074801d01c6402081400e11010303600707107414280110f0103040070f1210700c02c0c440d8803403181004540d60800101289841105440c1e40c80e081841641c0a58400c1c3c03201510440d010320590603c0140041260082343c041c160891460303a8420517031344924803c8007041d401610b0f0002c5d0010301900e1440711340c81071000b602c60102400103980c0d4415a0b90b424052244c0030084000441c07403806114450235002031081c01d00c52902901da41900f468202d500d007401403609086207202c0700303010890341450102911440 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 449154469 1250 449153219 449153231
    0x100e010509030901050c03040e07031d0601050901171218010f020d08131401111e090a060e03070b07030e010f0c0209060906010509280b13090f090609030c06050a 71
    0x10049441e8041c00c3c1029040c8500041c2d00000d0b00014021103000d885201d410700701a00701a0760050092481300031030000046103440070000344400180d039a040b030b240140030b110542c1c01d01c3c4245c03400c001e042d94016030512410840f9100b500f51304000d0900c1d61184400317030115500001c001041c4071b998260241c00d54001d010013008c15507212441c554400c11080c141240c04460f85421884140502507040c195440c1061084200c03600c0001441c14007036129190f580e4000b205a00c045c18400c4003806644a84040303000c2100d036014203c2c008410070300a0584071820754030380e100c040320b0340606d100302e000030f031140345202e0290317008000440501564030346424007520550100c0c03007540d0046c00c00c91241918030001800d90b0320031001c8841042d009440c031316001c040b1130180501d0403032220107c4090210014041069144070003a5000107004104e00448a0b150114000082043c40b407404500f0342c484404ca4041007890080702c000324070035a10540464014104031307045490240248507400d05001c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 449155719 1250 449154469 449154481
    0x90711060402100c05150f0a060e0a0c140d05092e0f02130f0305100c0c1421030a0b010513050105090406080d02060f070e0a060f20100e0105 62
    0x140c0300c1d80c003941c10707650b400c65803c1511080d070b000180844001c19030303c44c55540c6c01901e0440c445450089003040a051019100d884124040d50220302680c3d0150f03407038000140119815070020303084131303c003828140e0101429070042c1d2140d9200f82071560f11243c8400500000300c80400c0070f81d911203002d54a20380a800a030030711101344c000c2c84003015200c0f40ca072483c0106c06501c903411600b0225548100d201156940c0c002c0401c0c14030b9611055481d402001d00c00544a0306074050310115803110350728886035201c503a485c2450f2140f600d03e200700c42e2107180781d410aa60f20359a0a40e03420318244095580343d141000d400e2041d1900840850304003d010705c00ca403030407002640c070078058410908107181c5407042c000c0494010302c07640d0b001006520954144481c2c0c01e802203686c0d80201c004880405156903900b5042d10082c070003511240d00030000c0003040005900c01c0340340200032041460902e00d416160b143c41c11002c0c46001d1100c0441d04680244100e164991040e440b00c0350030180240003510b0300e0707 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 449156969 1250 449155719 449155723
    0x604020603130c081b01020f0a0f0f1103060f0108010e0c0a061b020402040f030203100908030105121f05071205220302070306050a0b090a0510050105091c11090711 72
    0x141000d0901242070848800f080b803a101c034003002c2c1131004201d4000c165800c220200790100c4d0401103015029181128514010218511240355000081c1d00e6002c019030395086052242200705440c0a6442c26148a036980c0900c41c85001d0152850748a01ca54140640c0f903084400c0c00c60080d02c0c66000503206484c0d070700d8031403028046640508108100020402c40403140103e45140294810f2000402040780210402454280c1e8002e0303048581ca82003101d940c004a60b450000034048840603c010085841d00d656110b103601c039103100f0b844141c1c041d8031342c020340343c0361480c0c01c01c0c0516101d01c2005012507000c011810142403030f510030312142c00c192448021445852110f00c2141c074004002c4410300d40204106001558040810881c03480c1c03482030b4600404500c4100d034414200074000c180e995010b80583d60249a611120b40b5025142800540700750f030004400a801080174800580c550b8428245490718a0141c0540c00355400140c0030032a001e04028010801c2c000600b00141c6c4c81800 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 449158219 1250 449156969 449156971
    0x507030c02090726010303090e01080a06180209090c090a230403110f06100501050f190e03030a050405040c0c030914040f0507120b0109060210020322030c050606030604020603 77
    0x19540504262a100022900f07260840301d944001e510148000d07150001c1807021314100c9001e55038500141d51100341000c0b821900b845801d045034406c0083c04003045c8580d000e10000f05000742d0351b0100c4d407110350115880c00801c0b034901d021034110200e1840f1900b801c5c808142d0000c0038400030000051044510f55108695540c00040401050002410140074641d07405c8194401000c4a085407101c41e4569583c6608480300c550030004000005219400b07202503400c50342043c500c07181402850031480010030192046001084086c12400c1e1103a01c00380010055003c095880c0f9070f441742002e0510050721140360851040101000c02c0b8004281d01282400a4982c0740c1003000c45480020000b40203011141a56036208bc40c210038052140c1e04401040b6041c0b0342c94106000c0301c00c80c0c0005544ca01c01d00d200b4200940c010b0070b40d030b0b076000340b0320381c01103030300400c038030040482c5400f01c1004130341c6091100812008107584000c84000e2000400806900c0941240181765034030345a80481c5041c04 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 449159469 1250 449158219 449158223
    0x11130306151a340b090d08010e07050c120c03090108010f0e040b04080f031501020c0307270f020403052505100e040b03010e060618010506040b0c07031b030605070507030c 75
    0xda0201c0e0300c003c0032000c280081c060300b560007001502a480d0410b458003800036992462184903080016070b0345e07405008042e040340d5042c1d01807000ea03a616002542c3ca9801401c81e16402e00601021450420801d0007070700d481e500ca0802140c80c0c0350381d04005426000180c20039521000c0303183e0100000c1c0c42c0c40040d06d601581c800300d180c00c60344861411f0000c0e130140510385940d21001208108948001d201c0301250804240e0803964090484014103446050900482c5000c54221f003202482e82c40c0303400328100044002c50006000c0fa0044415000ca80254004030358641160313203c24030680700640a0031401040303104150805181400066100c0c1082ea0800203010072021100613903641c0d07500c03107030680c1809070080c070100d0031503048151682406c41e2081e11804c5082c49407510700204002d15070580304080d03c401c2c5030030b0400140240795001214101c80074402c03150040000f5040040000103080314000c0681c4050441c81c214068880040c0302c8810000240f000703c000c20760214010042503 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 449160719 1250 449159469 449159497
    0x10605032107030c08071104061d0708090703060609050601020115060f0f050c150603010e2e113601080a0e030c0703030c020f01030903080a11130306151a 68
    0x1000b03e1500361901646500058210600456a1400d014070794080e4944500100c50401900d501c48024900c080c646e050104440e03c262000139001ca402a12213542000409040340c44459070b070740d100c10644a0035000340320001d0b03c5400740445541c09020b0090401d40d0240395039403850600354020003d01000b820700341004078001d121300c1d02078012011602024004000c1d1080407c107000315542c070300ca0039202503000b50710f41060008203180210fa605600b2fa40103c00010360451028070024050404560125440d07454210f404046101c0c0010420381540d02d601c1444010b0240400c014400400e00551054000d180a0b0002c0d1b1391120540c0d61040b288200092051420400e4510f140600c00b0801420b00c591000403091641040080310114400c6035203c08841c14140118140d440c40040100441d0340344001c506644841d4001e40d8044228004442c1010740104603c294101176610945115030b9418001420700800c0010748040e10315804220120451114521014480c1d03403410700d065 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 449161969 1250 449160719 449160727
    0x190e01050d0c210509250303030e0f030c0a030207050a03080405040c0c20190e0c0d2705060a1104060302160b0f0f090105070203090f01020f0f010e0106050321 70
    0x24019040312020401c1400031100344004403496000502d0b054503200102c2c800c500d003c41c8110210200106c04001807140c0c1056903280d80e4040c1c01619062603004014014002078922110080020300304070f40350000100345101c014200a13040c43e2051304500e004180f24071040c00414035074012103080318002d840000d420380300304a045030881d6200d40010800741c90080030703072484502d07202c43c0e1000c024103c03071014260b5805122041c540b00107105107410784070f9000020f00c48880c0f80c009880450728001e8080303001c0c0c0720030140c0c068980100c0300f4180d01c107c8030b10f0450140141005000d9200c14021410080004d0184098010340590b105000425400061a2250303500806245c49030650000c80d290883c103010359000c00341c140071905506921103500001d03807480014051540203983c00e0300507518101b015010b00c000b08525464140c15031081407001c81e1410000c20151400d02642e0340001155403912031a42d013507800c0d9a02940c0300781d1010a104a0090b4019481d00d4850b041406481d99 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 449163219 1250 449161969 449161991
    0x1b030f0507020a0e1909050a0b04080d05160f0302030f01051207180207060c180306020f04051e01030e010b010e0d030207051011010b0d0f0204050709170102190e01050d 74
    0x20748581c2000075089412050000341c000e11000d5218010300c103080d0161030b041031152001007150700300d41b0043c180c1c0c0d20040d050004a840000081d810a0203005031a20b03051041a0407001d4500640d2a00101e12840c8500c1041f43e038413003010402c0000030301c0c042d0328504103440c40d41203414041c0903881c0b00c3c1c10007640148004408228034001401a242c1c01d0312a2040740304544000e4005aa081d03039030604061140403514400c50079450b906c4818040410000c1c00c0da1205c0c0d0094018860154144e0010400400c099403031303a000036011001050b41040000070000018103944444401d00490380c1008022130040e030300802d02c802810400d03100a03484c04a682001c80c50242142e0007560004426125039808682c8140074110900c0d140000344600b002c074005101c10508900c40140079012614182801403406800c610780200451804180c0d4070f0b200e0b54403841030400c070300c100c45450390300140d107410200c07200c0e6800c88414094100b108c0f220074403000103011442400054140143d0b0b950030260 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 449164469 1250 449163219 449163227
    0x30c09010e22060f06181715090307020f031c0c080d09140708030a0c02010302180307060302070b0a02030108030307110a0b0a1406030109050c102d09061b030f 70
    0x40503207400c02c1d407002000096019030000300103a00403203050140b9440040f4099005005400040020340421808540303400070b000304060107014940040c1c0503601070020300010251600c0c1c0250b1699025542d1080b1607c10082e074103c104c100d00d800783e00301c40000c0700d08e410309010103074124200d0705084180071030b0b80c5480714152043d00942c81d0054640100c0b0340520005000c45200035030640110b51209441e01000380e500c0c001d11802d10006444882e0250055120b50050044280341c08284102c0c4006017000a040c41d465410003030000358041508814402244030050f004040030b0b40031480d40d41080403d90300ca1000134054001d0007003640d0b0244058004120805001e500714050070110708161040102503c40380c403a024000202201140051906108192101d07900000174180b88000205001480030094040d100b840543c064a40a40001d160514911315002c0340f0011440c1444502502111203904402c0402120301030b040c05a505140641c407020360142042040c124080608603 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 449165719 1250 449164469 449164489
    0x908120a090b0c060f0702061018020c0106060201150f031119030f0303050402130b09070f11010204120506010b03010609090b120f0601151704200303070309060201060b030c09010e 79
    0x18120700046081e01030303c011501c00d0241c1c82c6a44102d800340c85104003242d0310341065648600e10760314408104900300b5080c403810580c1104d40c0d07000d8100200f225546084601c5c80d0b10940140c0d45070100800034644520102002d81200d50420180302c0c1961510901801c10b80103040c05001080703002044480540e03d0b150042d0b9000c0c030700f03200104280c13500070054803007654100e005010504c1605280f01031406121b010100181c4401120303520b06500b100c0851040e00c40170b06000301000d50001c1600280010009080080d042d41e0119135545000352400301c059115020b0a201400103010b5198480c1e9220200c039400e90022410080070000641400100a400d903480c0c400c1c40100720b00800d000c00c00a04135415181c10050a0007080c001396101d007501c5900ba02c860051000007000203501034402c4401450754580b4803058a443e01c0483c2c91907000c00d50a42c08501d80d88010072800c1d5090003400098464042e08034258101040607100c60301410420505205090041c191103481c0c0d65244 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 449166969 1250 449165719 449165729
    0x60406030f03090e011706040b0705040825060509130e030f04060e12030f160c05030f1b03120412150f02090a090c2a0b0f160908120a09 60
    0xc000d6900c2c0b50141c507900503441100202e0480400018146a007441c2d400040c003451400f40413941c0e0303241d48078000480020842c2e01880014040070514800800c0b01c0000c030039607258004041c0f1034268800a400b4500e900920400500308a03420094840b00d4080d880c2c0700408001044403003075907881e6402c0d80200880c034038103080e01040c001110350f48184920a51102030310034040c41d49805040740d8491003004040151404c1c100a044180742001d00d5101c00f86009200a00103241c0320000a410014245502e20051340700340390400307040c03c0041103819a1542100200301203c007020b1044018069441030024048814000c401480300421240610ba80038810401541454900420094020401740c601441000340041440300452143d1080c0c4002c0f516007164241200c161016850020390300c10004410110306080025868000c0900440038a022041945000c9100e661903202c0c907464841042480341c020004200003180b18008401c511201d1a920411005c00b40c401250907404 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 449168219 1250 449166969 449166983
    0x52a0a11011404060c0e010e010e030708030d0c18080d050f09030a0507290d0504080f0a03052d0a18050a050105013b04060902090f010e090a0302030d0506040603 71
    0x648840e2107074480340c081c4102e02c154020042c1d41c10203201202c502c6d0140300018041818804141c0a66008240700616003030001d0131220200d80325040281190410226034920680300e1b100074a07503503040080c050501820008a038502858440d542e66200426082a024050700094407049013a81030304035012210080c040f00d900a40500d03169903200a60f200d50700d01441181c03c0c4140400d110700007041d030900048002400c0030b0206e9181001440301a108940310b080070414004a01144d502030f008020b15a03c1c0024203180103440000301d40c800d00504403121006842c00085d80d00e00050f4150070000d0640002444603200310184c2100c0ca100c2d002405c103118840c0c9160030480150002410303131304039206940900300050031304040225081260780100c11705040251006546150041d40706018030004110048240c02081140300d09440800402c8112401844140921406c80d5040503203040140000c02250b1002903d0b40104500400281d8031100480c001d551650081c0c0065900044 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 449169469 1250 449168219 449168231
    0xc150f040515071a0118020414040f0b130203011d040302060a0905070b0c0105180a150e030d140402100e030d0813060c02070e0a0c1d0d0b01150201052a0a1101 70
    0x320005003450901c500502200742d07110f2200d00000500030344040324840030200780d40c1c81d00c010030407009d08100034050404bd0b54815460f88241d1b600f0f0105000c07900b00110050ba0b039410450507501c01c0080c04081c005014044c030a00000a600003682a401075060328001041c200c113240c5a400c1080550181940781c40120b0074031446001940034600402c101004050f101664180d120749803103450f0f00c09040c0c911080d001c0d44103100503400c8002c05040311230550b8648841c41000070110b42c00501c071001c070381d0340b00400c00c021401d000306c0c002c60210450411540702c01e0704a000130750307505041c0354040401414402103240510400e0141401a074849001e000c850640900256292468031500c00903809450111303074454807621400303e906400c0d54455400740710a0100c1d004004003d00340039080720030142c1d1140801c40d002c060a0203800312103a03100d6400200780000b429500003400003444040e508a8000340040240900407c104d84400b005440324400e06055592a9114101124039402d080c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 449170719 1250 449169469 449169503
    0xc090702010e0c03070f0506131203090e13200a0509250801030503030411030a050d0302030a0c03020c030a08040f081207080703020315131107050c150f04051507 71
    0x7400940ba1810001c04035450111160101540e40d4a00d204160501086190600c6079040180c001c000c0b01c426a111000c0700d0b581e47c4c42d03031300100e2098002600010004070301445001440c043c900d81005c0303034000d038982c002d805840b4240d90802c0d54041304010400420609800d0711410260b02c002c04005010012a00d0300c060101054900e031100fa28034035409015004c040c030b0160181c64181d0750010011400d55581d55248031420034a000c4490f410700c69100000c000a00c01c000d005580c018558015860341041d41e40c85040d10740300340b0030200385070060128203030941d0b0010945005140502e8242c14030744035030411080a0703440010140442400145015502e6130820502d8040c0c0610b544958480e0b0b19401c00314101c1c00159209542c1400c4140d46940520340044109414014502d0024110005442c4005140c2c0050821611504004003075a000d103810b1460034116148141c02525095485200c05214801e5003c0e0612400e11915000300114085007502c611a81c4040b80b00c103450122 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 449171969 1250 449170719 449170721
    0x70519030b010b03090607050904110a0906020c1c02240706020a1e020d0c05031b16050a0302310c0302070209070318291602010f1404030e030c09070201 67
    0x500040c0c07180d0040d500002032981815040780d11075010b66010705400d40314842d04490941c0030500c1181e1041c2c40d80f0f40c44400d400715600800d01c1000030380b55034415510f0558041e080040300300070180b0840e006001461030300e058050f60a4002d504650300801ca210a1526000048207400e0043d403000c800f2032741000b009516070050000b140d140e00c400c3707110039030840700340802ea4600d00c3c014016082058403241090103203400b81005031048040e2410014070107100116000c1e08a800c10842c0e01a40401103403454000012000d0041a078442610760306580218074503103480c5450301d580c41d4220184d2015070bc1445000c500203260460180181c0707503403580c014003940116100340d1040004401045610f4064860a080c50a01c2001b14100f181691622038605a2110510a458000c80f001c4150300204013403803441201c1340c442d80f105080c19040c000b801c45000b0029250110b15000765103c03881c0f2403103040383d0b01035030600c0c1601076640c81c0800b01782060840c481d01600b081300c607000d0206050701 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 449173219 1250 449171969 449172019
    0x60513110d0603150b040507090b070302100c0207030c051c120311120f0f1504091401050106080f0a0c0e041a09162c01050702010c0b010b0901031407120209030705 72
    0xc040d810701800c0841e05c1000700700c0700c00351010004100c58080400c440100b0300d0240501e14000e0040c3c0d170040390480040381c1550380850b80c28006800240d000d00400120790200300241c10151240040c5807545400746000000040003c3c2c9025013003900082000e100750041448842481402a2684103402c0310801c0c9480598141815400348000205010700889409218103001c0402142c0c1c0080d010602004024900c8159a0a20039800040c06031a0034000c50b4002c02c2c1c2079450700b9503850045107040d580340000e4013240c04642043c0004d135100e036000d00c048401007400c44000503014022440d21415804286205030440c1c0708a040100946072000c49000c1200b1940320502c90140e03003020040380108442458a010503201003604495125101411080b0300c1810540080b4010391920140390b0026032000e04a1080007483d1b01455a041c010010700c1c0c20030001c4820182042c400103010f421150710a50081a80030401000700d81d03041000174001d000140500e400304044e5800c1071040c00c1 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 449174469 1250 449173219 449173253
    0xa05032d040314071211100618050105030307050322170616020706120b0114070501020301030614010e131b0e0115020304030c030807020406150806030d03060513110d0603 75
    0x9090103c0781c100c000a0441c1c00460344114003081a61004034207491840c41880354031624410144103144181c1c040c800c0c0d47c0500001820301e40070410440840c410741c1d0050300128080e81051181c1c40015000006407405003184091409c0300c07403d155104240402998008080b50b45080b2010040f03010101d9964018a00f405984038243c03048103060742d0365005c82c8113030800100001c0d003041341c039003140c1c2c401c03a207618051405040b40c05000c2a07004d2103801040050b138440e50b0020041041100920561464000c054642c0e20701c1c1d0b05d800000c00c00520020178100500802c200c2200401c14542c013444050500d459842c141d4546a02c02032803182824000c2460b6000d0264100d010980004155400c032070740301d40803200f0f0310b0a5580f902050f80194004a800503162980861105480c10030082c13a080c0640e10200c40b46414002c01d89000ca449010301c1c14940340c404107009a07220040e040100d00100007001c2101075030041d8085880c82008001000c185c80c090010041050708610814081 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 449175719 1250 449174469 449174477
    0xd030f030c051323120d081e04020405150307060f1b052d011109010314070807030902010c17300402130b180a0e01020f0a05032d0403 59
    0xe244a10180c4803480380d02e0f00090020b5100e0401c02264030012010860a00c1d56224020111012408162180e05582100410350000442c2d6a0080d13400250203038440c2c5400a901c07259040d030140702c0180900a003004e8011503e60000070042200c60401c4401c1c000c0c0034003240d03541507880b03100814422450f444100041c85c0901d140624030348c500c200c109003581010103002c1c0b20f04150301e2104100005005480030401141d9080002d00d82032080740c034448480d070300f440d030340d041c14500040c129020814a104d030744100342e0511150390341c0700c003c00b9480b00140c10000b031208110f00040e904500f2065000b00441050010000d6188608020700303e8140c1619548081c0000e05111802901601181508080c0d69200150242c07410a242c0c02c64110045000100d0300b00301c0c000300c5e040340707500c481c2040344072000420301c038018000d481400c80c2030604c04021414107010306812441449040080d01c204040400442d00008050310004010900c3e03404600e00700710140342004c4c04182c00c1790242d01003 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 449176969 1250 449175719 449175731
    0x703020a023006040206090d020112020f0a090b121b040b041701050f07020a0b040c030615050a0807050a0909140f01150905010b070b0a2913140f06030102090d030f03 73
    0xb0005002c4c1c041c079030083c13030382e82003c1d101401e0081c02280104140d040007441e80e0300b03c84007440c500c001c0500c0c21829141994400001c4400340400d085540020100002080000704441610071115000758042c0940e0958100d003842d06002c1d4003581e0804900c002000030001039100590782101d407084a00d200a00103940e0300e40c0241885442154600003603000780c0d01c071038000344e04c500a80358042c1c41141088042602c0e901c5030012200005005001c2c980015000d20031490882444801401c100008200013800c10021600340002407255068207a00c6020800400821075003082d400d00d0404115400e1141c1d10741103a0107015030720001c08100440d8000824600070500505050302d5914408926000403643c8101c0c815400400000c40550b6503281181403502910684030007000411044404410101c10800c502642c04a9190703100e00e0070320b00d0100c202c0c1003800c640d84403d42106d900f0044e51f41c04007003030191148601c1d495000002d050007008250300084c6030018240255420049 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 449178219 1250 449176969 449177059
    0x81612020d090c0e0f040807030216060c0213112d0c03070c090603030903120201141005120706021e01090c0f1401030b010206060d05011407050c06070e10050703020a02 74
    0x80c04c04107445051904003028006030110f2901c40c01000214480d204580c00603245000718080d04150750003070310000304011100400c0d403402458160030030f010988200721584030b08010000c18400c0e81882504825480b8075402d030b40314403110340002d040450201c586c2e00c002d641f440300e07166807001808403220410440c0c0491900341034451141030307990689904080c01c2c03c6494031a0741c90030301242402199244c003001d50000c40340420306400b448117510030941c510700304001c1201828160142429030303886014104072550f800507282c400303103804914510865045007000c0d8050b02403000c029002d8407103190006a01034640301c2d038200722040001c0182e080002000114151490600200e00690100300411910300d0700c0011603504c2d500c500700009190f40030300c0c00c442d000c0008540c0f001c042800401c3c0c00d8542003050042d19442059071500c04039005140e40002e6800d03000008442c10007001060900c01c02d4001c000444000b5001480c1e00ca001880000c04810a12082c2c0244000d911003501a21 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 449179469 1250 449178219 449178239
    0x705031609050303072003070b0a02010e011b140403050706020d0306080a020306060603060a050d0f02041d0a0326090a020307060e240f030f01081c081612020d090c 72
    0x650b000100518031307000450701c90300b016003a409500c001c16041d1808410083d601084a00c0040a603400100c0d200ca05c030032000303421a80100103822403a41043e0059020000c1c41000b60688001c90400f0710b280400041c050a0600644d00010300e5441b61210202c3e603950001004804100e403981c09000341c90302c420350369468a030b180710300940650040c404143c40340752079000b0b581d10070006403140c0c0d6025641d1001403000b0200d07030400e90b00117003100d4109081d41000d016140c410a0b0408110054141f40c01e041583c40d00410030260400040c4500444411002c18109413052055090f03094141803807140981c44125055049100344a108400501c00707000d21a020603205c0001c155000302c503038940010003400041415284000c03400c0044244840100020f54000d01e94003a58108543c10f02c21020714100005201011003075110030306200042e84801d21640c000401080d00d90f5911621909440850201c0c003500309160000c210003140700000d40c0168210340c0212040742815544503a402 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 449180719 1250 449179469 449179487
    0x90a02070b070e0103150e0415020304051c051b060a0f0605150705150106050310080c09130f1502070c1205120c0a02040204230301050c030a09050f0607050316 70
    0x2003884a0071000115400e004100c0071080207818100416144d0341c401e00b40480d80615001480110300c0d160030f000c00d001c00d60801c007182d075940e0741d02180b45050030b4031200c0e500c80b080700c20380440c41c03441d0602242041c840d105035101c1c0d42c50b50b12444481c8400e5599161544800c41c1c2901240c2d00d00014400346480ba8002e1008441340502068040c549800100d030841e40f160606072514440c072001038901d1280740e1016802048555259a181e00307100c6d45a5815901a6210001942c007040b500b058135601c21207040d41040703602034042031010f450700d030000b0b220004500140603481c1903500404201055002058400c0c030900c000111243ca814a150310307550340440c090300a9005050f4450f02d0000040102681c102030000c42e201d034041d40d80020141d911a07004109522102e84100100048552b190302004200314000d00a074a802003032032445000013400c440415498034060020f002e024082d482c2c00341e46003000d540d8149081c0c6009000da07402952a8a023180c0b14901383c044951081130ba071 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 449181969 1250 449180719 449180723
    0x60b03040615060e010c0201110f0a02031005010b03010e18010606050d0e16030b19020c0c0a0504020909040b0c0403051e0606010801060206070807050918040c050d02030a06020f0f0d0b090a0207 85
    0x280013210340111101e01e03000d50128107102c6001c0760030240032010858000700b0120000107046640146c4145420700103da04d620191314203180c0107100488800068a055440c1110942003587c0c42800d42e800050070741c002c6225951034a800030510380c2c1c0c0b000003003410000d0042d06200d414240264227580361030b62112000c41c844202c8052002413020304145421811840201110180c0400d944040b6404009600c1c42980304881c550000e0400d0700401d00201030407030f000c5042018440100b801d0041c0104001c2c48640c4190000f07540c2035600f402e5901440d00981147d12034921200107482000800d40e1078070b120320825001511940c420714a03103059401d01d9000e041e03103440300e450a4641d0503020b8844d805120045c000b00361035889a5810300343c0c2440b013034246116400c09042c00c0c2e0200030701d030300100d020b1003044041c1e102503180001d42c10703076007030340030f01d005a071600064032a00c003d024490000080c08400581d1110111081d0800d4003030040440d81c01002e615009034070f070200c2c410a040 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 449183219 1250 449181969 449181977
    0xa0b01050d0213050a09050f06010305101103130c0b16140622171c0e0c010c03050d11281b060b0a0504050702101b0e06030a090501060b0304061506 65
    0x4003140d030b81c0f6a403c1150072580c44000800c80d41c401e543ca4500740038400101a1080d03204800400034400b0800c9241c0000b1082e100400910402010b101c00c0c5110040c100705807107100701c08003000c10064100c948000c040a1661039201c291038101c41201c00c126013400d45012001031444044100c011030040c0c054800c4560845500362030100c004c1000b42c1c0309100f40d81444c180c1801c040d003001203000901440031201241c8a228005517104e8007215040c4003d819250f01803503011089980003030010b40310680605100344c540c164032002d0b00c00341110f211200c00c154000301311a50859908101c079440001410880109001c03a4001200c900307a01c40030034100201e2910307024020800700d40c0540d00d0008040c155034816620383c0c01150035240182c401c2801030b40701502501080c0d0851194140c12a80e02c000281927a40401e4001c064941d003d245503c510000030104107900c100c3d0340440c42166201000348400ea988411310006a00100d170190381e041d05100410313032508200788e8140282c1d41291a = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 449184469 1250 449183219 449183239
    0x2091314040f050102120c1909142b030c02010801090203040b0a180203010531020303040e091e0a0303060509310203010216020109380405060a020a0b01050d02 70
    0x3108207070b01400b20803e0703501d550708104010308101e200351660b00c51101c00980780e5807030b0b80490303411031002c08070291041042003c00082c4404244103900e0406100116041c11114140400914000540840000b0104d1441511400301900104658000d40c000d8840d86201d0b030303888415605900c0103d80c0201141c04010010311513641541c0301002058030200c107207081d08607a40c0072070f08441c070507183e440300c0c40c00c8030404800e550055000346050000604140700703104582d03404203540e03000300c0c0a2210181780c44400550a52810008070080000d07500004c034000c03e940545a889507030144041e4006070a052003c00c00d03052041c451800b611840c5540c43c3d07003800c440003c5c585620411040d03040000041003c0c0003580e02400981245551807211060f000014070000d868107003158026544c40c04400c040151804601141d22020045042c4007611460782854903050703842281c02841e4041d030086020603030303150300103004102c0520481c85584d09988800c10442060300c1c55000030340c8021205 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 449185719 1250 449184469 449184473
    0x10c080f04022421060f090a050612030d020c010c050a0c02040c0e0d08090906030c101b080705010203100f1203030f0f050403020d020c01030c0905060307120f0209131404 75
    0x50004900c41c2989002940c80040001810f1455800aa5902c0d550018640d0388169907164210294200c5c50441e021483c0010940100b0380c03d034801428040d07410b50713500020f42280c80c0c6840c12411050000150381da5030300c81c00042c1d0025003004200d030300c0c0c075071a01c04200000d501450459545508a4075480b43c0f0803615400c10000d4481d0b0744c00d0340200501c204144519440d00c24130010500e115100283e102c610000030f101610b4401452103100ea84112414950350310394502c101071071a643d03c2d08148484100d2550810000754440091440c2400070303824080c0007040d40954020080607040345021590f8841070b1007030344100c0c0034108003c05040082d10000780a684019900c004e020b901141c12078905081108031103007183d003940540c109154000b0103d5052121005909090a081144030301c00f030300062012800740030320b80c0100c0380000854042d0b4041c0d85030341543d070410a8244810241502c0700b00203900203110035409548003501c0403c01c1d170054052400c402400138030302c400503039840d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 449186969 1250 449185719 449185729
    0x501020c150d14010609090e01090b241e091003020604150e0d0c030203120f07030c050a0b040303150503030f0306091003051006141c081c1b02010c080f0402 69
    0x2660b0300058440d554000b500211100c1d110840c0200440c2c0c40ea001c54510301408142034440c03d21002910b6450001c9250004165140098000a00501001c80700b2034440d20807000707110b40e0385600e602c142d5034850341d041c01706021180e03c0d101101340c65070007042c0c0f00c1c0c91010308a03401a0000a40c010303424001804070040e2282011440300281c070704008460302035000308884500c09901a0b6403860080030620070340c14200301e00300000d42d0410b0414549030700d070f42d141d445a020328a401010003030b141840000b44442082031130045074100c5c2600300c050500745005401080c1c09851100c1c103081c00d882c0041c11b480c0100c01d491088101600c00703403840c0e03140c80400000c440300078001031102c07690000100210342c04100d040d81c1102103d400054044c148142d401c00c4000d110401e5100306070004060036074494800c0d0316505158030072801c42d10390f40000ca1103024008100042010b6501e41036540c1403440c2c0e20905034007907410035002000b0144440b001120610000c480c5281040403d5000c10014200 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 449188219 1250 449186969 449186977
    0x906360b01020109021305091c0507020105030c370c0c0509041a0a020a0305060d050a020d03030b03030a0207180209221d03030709050319030c020406031e06060501020c15 75
    0x30501c0002403640c15035000601910182c403000315940d988000708849400204041c6071a0f07031983c1c0820017040e601c0e4200910328450424001c0c10007102102003007140070071000f41d4000c9108082c0c04a4103103000003440d42c51445101ca4100502d00f0900c008441501841c01c0d241040c0c0c10444000e00300c0d04140520110303900243c403c44031071102c01080e08503141c08800c4c55003d0b448140c40035a807030090100080c15680c010300201c0c81500110704101c00100c001a8421003154140e61804103411b95080907001440000e00c0f60390580800504800d60f80c3d070101d030300800d40d07000a00c07280603c2c0340c00a100342203005010140d0703000382c5400030340300032a00c0b8052011148003112001041c09024840c50b240a554010f413400c0701d661000c402e0201144d0010220406000144c0080a00441040d41080c0d88212008058148030520190718259142c0f900a03001440c0c01c0b004004032150f4030300c0c20004c0b000030240c00359845481e00c0c01c041003079807010403030080303441e002003030224030321040072083c1d00e0b90384 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 449189469 1250 449188219 449188241
    0x10f0b0a0e0c09180f0606030f07120e1b19050d0f05030d09321213050a06050901080906060f062101030b01150e09070f0216090636 58
    0x24080c0800d011660300d026101c100d52050058200c00342c01e048100104101001e05034507c109018000c100f40400d450219a0f403061551410b0301900101180c944024019958000328600811075a41c500903194000300b0882681510410394460903c10300ea07030503100d180500c50f84000d902c0c0c0d43c440442c00c3c0b0040a80081d0003402600d02d041307003510000c82166107160003141e69011403d254031312407818805c040310210f00240210200c0001c60f078034641343e00c46180d101c51022400700304031700d080d041d0650385d1002d481d01401c000240c1c4c1e201c1c030016120741c1148906a000070801c10000e50300b07504c0400c00301d000b9034002d8041e0004105220800c80c840c3c20603245d0b50014040d811510340c00b0004403802900035070003140c0840195041190742c0301d40c2d500c9201880180040b9560043c1e803921450010303039000c3c0c01490003110010014000b2810b0034825105000031545035403000c40c030300c03c541e40a00e045031101e492195401c1d0b080c03842e541c46044d01c1840c403009090b100310b0441300b045c07041e045004071b40 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 449190719 1250 449189469 449189491
    0x504170307080f090105160b06090702011a1207050a0e091c170c07020405100603151d0907270c0f0507061a0d03120b010305191e06060c0203010f0b0a0e 67
    0xe00d40050004241f044440d003030f20305011620620105040c50190326801c44500d20081c4a410340c0c400010010705030486455018034124040d00d0354104040c05148003403c4c0081c5100340590344d038024410f841001340c48400d998000e040d034840c0c2401205002c502c1c4000c1c0b94860140070007945c0861400c0b00c0300142020400c1d00100b0200c0c0040e503862141030701c01c10603034407440f08041c103040b401401c94004409404808010100500281c04013000807654041112090740301580ca40341201d003812400d9010410980441b00c0b5004540303100c1c2e08120090b0340035070041042200115080341c4104014420300003207034040100f040070600540106c00c05030300c0704050134070001c10346010030445080348509400091702802c5008101009004240c05003509103003e0115042c2070b052030b07050280e8003075070780d40ca5a0790b21801c0f0344501c1146c10381580c02040280c00c1103410b0356040090080312801d0340403032280d481c042d00110340c00268032862205901c0907203840850307420412600800360740548005842c1c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 449191969 1250 449190719 449190727
    0xe01150203040f0b030928020f130504200109061b06090804080705090a020f09060c070e010b03060907140d021e03010b1b070e0a0225030504170307080f090105 70
    0x244640200711001382107000900d0b40d2490617030495424080898039012552440e09203407070000e00c880300e82e52900d03070701240c0650300d420107540010b018008014510b802141090304001c04e0140e46c42a80803102000030580946e00080c0b40119106c40d02c50041c5004076580805003171403046043c600404981c8207100020302c03180261111509504264094100d0340d0001d181131000f420003603030340758005070b00c49011b50804100313001450440c0180d80300c660141c03502180100301030804105440050000c0d0201d04115610380241c400c01c0c1c1e00480c0c4590003030381001e0118251500c600440120b000e031801c1d1060400d01145400c0000e13500441c0000c900516040b034112041070300c9001180200004600e0035aa808011003041300c0301100d000f01041a04400702c20040d84105ca141d207031b84569440e200503658200480640880801c00ea81c3c075015200c00c0301030341c04054001000b48150b03000c40d11034051181007043d07426900c2c402c409006001e10300900400d241000c00c040a02000c1505040040c10 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 449193219 1250 449191969 449191979
    0x120f0501050a0518030910031112010e0103060e0a030206062205090318061c05190e0d03050901090804090c170c0702010e0406030305090d0c05040e03071103070e0115020304 76
    0x7966010744002e0341056480082c050b81d0418102d9848410700c0c20809141002d54000005e400c4401102e01c0e0820300da00c6035025407160b14604225a4600c400e5000c4040382d50311078050080c1c280007400111501d80c50024003064a0500190102d0440da143c0d009003031076a030354000d00090b00d142c040c1480307005440c0c244000900146020300751144280c900155103c0c4503698403907845500200c05c07180640f070208181c103100150030400d040341c0c058900010039542c0703c0c106c04a16000c00c14078814046407814100304031155003c907501220380543e0380c051280340c617202e290030708031409400c008212540812081048854940080d143d81e440c07800e01940c42042000c1d03020b0844000c640001da040c0000a14508568100c01400b05a04c410303901080340c1811035030060000d1145800d910b11a0310007200320300c1000380c041502006003c0103481848255102448141d40c4d030000e440032508600b4480c0c0e140c00d01c1c10b0000d110400c4410401c1c810740b90341d180012007039606401c0c2c048402180010400410 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 449194469 1250 449193219 449193221
    0x1101020910080f060405090d0f0c0204050901050f06060910031a0a06020d0306060215070e0d02031609230403050a090803070c0e0906060a170309270a1401120f0501 72
    0x4001c1042c1c0ca5082007460912070040d1140d02c0140024812480d0070140034000c0400103825070004a2802c08030304580039040c1c140c5a416082c0b81c000d62150518040112603001900130038090518921310070340d40d4a6600c1046840c1c09080748171038100d045040d40000541c0702e5042034a02184c00d041c82002e00c52610040f4801c41102c1c0c0002d00946d00c0501101d91099161181100501c001d2001c0d000c098001c0b4031402c20502c1c0030b895581000380d201d601020990711041c984001590090440c2d50282924149843d50409441810f6445181c20100b001c5050a80720760042c4c0c181001095485a0f11030390184c5081d00500c2c81e078010403086c143c020800c0b500800080c542c81d0300507006855031b2880c2035005440607200601200ba2900300c0340910100351100c84040b01035a545424151414032400055482c2d4011031150130741c400320060003090540d80b100c0140710030403007880b9401300c40c0e41c6482205003644c8110700c0e003926090f850001000609401255404024802d0708450307011035461300c07554 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 449195719 1250 449194469 449194489
    0xb07090501180f1412010c0e0a06020a080703140c190b15090a051503102301060c080a031b020c04180b24030709021801080402060a11010209 62
    0x40046514044148059a0070041e440010008801e01805082c2004032601c035400883c4110405a10140c146400f03503902c00c40b64a000102a8008000051401c4801484a14000d91030f501030068180003003940c0d440402c07024502c680101c503075480c04586640c00c9418140280d0400304081040c04440d03481d84003400048220070401c07440c400381c5804d0b810700040c50304014102d8044080382001c251544d03195a03404546c480c441ca00c00003100ea94864035603001941d04c64031150b050182d00e50400000081c0d6001c10a800944481c410098585180e100c0d034410080c001c910215609400c1500040c6543c0000d0032042118900400c0000d082c401c4501f4000e03040b0078100240c0c122040e440781714101840742522040e40d42da1104061411500d400144a9001e05a080c0c01844502102a41082c411500c054510041c084034003883d902c80e004002034000901c080c3c00a5083e0084108962017080d1060060f60010010752074501c035400140d906c3c02d010341d01028655000c0c045210244c2e1200c84074 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 449196969 1250 449195719 449195731
    0x30a030506040b120606010f02010209220e0610091a060703050903280b040611071b09020703050409050a0609060b12011203050301301109100503031e070b 68
    0x1050506042041006680540c103881e400f40138414003205200c14000340e0590042000c5c20038005002c1500c4040b400792184210f9281c01a007246000041c0381c0350495412000107440c1000c03c01c20b00001011a00d864003514032038042011100117106001840e489503041d9804403a01e1469015500d012881395082154260007040000c504100503082c103221034018940000d00025800310b800c0c0022402111a10001c0c24510840c40058200916a480411400401100c60340c8948440c600400e500d41c0324459040c410001e9000083d10441c5402035441195164440b24105130400e9800d200514004118040c0581c07104000204075045215040140c001880701315500c1640b2894015200c20692040d60041d44110f048004254404242d90554405d20031841841c10b158800c40e404040e4200220800c0c2111402d80c0200314020303d060724140c1003035603400710565034441542404034241c030501d0342540042218025018005d00d081318100d11980406060640350345403010301202c11149 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 449198219 1250 449196969 449196971
    0x3020c01110d0b010e010807050f040815040201111504080309100509030910081306021b190b06060c07090b0607050a0602040816150f0302190e010806060406021504020d05030a03 78
    0x2800c4290060340a40e012402c3c0a0a040000d0903440f03000a000c1000100a6020480c0200d83c0810340c2c03515804540c000d003000003c8440f00b6122158a000324801510308a0101301d110030b07a0814000c0108001103040e004140c581510b0b035035601c0303070701c004d9000410300121806407940040301c80800f4440d99015628a40046403544e10080520002810360310b12201404500010445861060840000340d0781d48101c0241c0c60f809a0544100908c5907a4840210b074010b0005100103403201c0ac0da414546401090404140d844100500000348101510720100b5007022030306114650664100f10034480d00900090b00d4402a51100c0e400c2c4030610358203c0300545c00084c00c00c6405001c1000340d02c01c4292100000450340b800180040701003203920319900b4400c0324500140f45500a6041c4c80305041c9203c945014444120001845080f6030312005003c0380386040840c041d03090540964064450719001049440034644c1111441c00c40100101d83c008070b11a840386c0022410f1001c1c06114643d030310 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 449199469 1250 449198219 449198227
    0xa090f050f0705100311090613031a090c01090b07030e0a15020f0c0a2402010f0608100c080c1209070f0305070906090b010504260304080f100603020102060f0703020c0111 75
    0x1080198250030304d09100301400c2031081d90f80c020721001190282403049a110b42d580c400d4081c01c60443d00f00d40d1014212003c40340c0c140c01d0500e201041d0301e102d2081d2206940b01905000e00640d41c0102d02c5c040d0400c0c0230002d001c01c3c400a030003008542c100b51001000034242c9551009084070b10503000e240c010058104051700c5078003c004000140740c01c0001c841d0144501d042c51410f18030282c500e0107400380e000d0f8900b9845030442c000c0d0b024508001e240d110601c60113407500c8213a41d81d42d40b07445021040c0c0d483e1404140d5400d01c030382c507854041d000c13401c1080e01c0c0040001410202450141986003640140040010810000d0070f0b260001c2d841040980400303880c1c00d808100722491507000003802c1303003046000c8440c0e07a842000c95050f03c1c0c498502c078207030a008100141880070603400300d02d00c0d480300040c08298001c0020f0000c0d040140802245c005540c02c840c0c40d019151141700c004d000d0303400280800d50020380182c01d2540170700c6601d80103040550600d42c003030070750f0700301404418000c1c0001 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 449200719 1250 449199469 449199479
    0x20c070902030901090501141b0a090b0d0e0d081b130503031308070b0408030d020c0c030a050325120507020d06060306061404050f010e0c04050a03151b080a090f050f07 74
    0x7004a407898000064000076509d02192890814800112000d060700000207402a03900c0c06006103002404002e1341198451440301c85440040403080b880100c2449890350f080300c0749200704980c612030402c66902e0018074010055510590300300031002c940c0300d03000120200351501c0410107000715a5900d16070b0702c5a0343c03030558003905108480e003204150382410081071080d5040001110f035400000d020040e50784202104041c00c00341101506a4540036501c12007080c070134000060711003e0003802981031560a9000038101004a4003002012012820400400c050140024101c0c00d40082c0401080140c140c0d20001191296002110359030743d6200244200480043e00090900c1d00361402c03c00c0d803c1c05032000180700700501c41d030a80f80603814005500e000702d4000390390041c0b0000c1c050640030f07622490494100708070040040b21a07450a104400149415070200d40f28200c56160010303507858440c40c078406000c1c034000a4485600010062002a00811280c0007440840c0c01030801c80b4101 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 449201969 1250 449200719 449200721
    0x9060902120312190e0a030207090c0f0e09070203040f030b1005010e0117060a09020705010b100309120507240c02012a0e0d080c1e16030204020c070902030901090501 73
    0x600e030101c1d50750003071102c0714145840d01420b03504000282c0d02410030f00350401c6050302600b60b0407206103030303402840300010800d600001c03442c094541007402401242c3c545503045a806266082c0e0400190400c115001e89040400756240c1254107032050300d01d05070b100c0610484055040e03004440303801c022000c01400c80311602c518006402d003403800d8003810311b52100003008410709000440c0b10100c0c0c000411007035a503c680100c0141900c40056440c1c80d00f81c20901d0003801a01005030180441881d4107605911910a07904815404400c15100d10140d40044510303410240d802c40d46449100c82646c0c00f40301000884000306c02c7c040c80070071541441c0700300a00b5201c8500c040300503558002010001076a011007002c6428013140ba203180c01084600020302c42c0204224068100d1038002801001c1c1800401c0c610481c04030300651032808400c401b85241e070b0704070300041c3c01c888000390f01381400107103402d80040042c8108201180c1e07a00740c50f03c44820803a0b1054600c03054030703903480300c0d14803c000c42 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 449203219 1250 449201969 449201989
    0x804060809060408030103060203100510050d050f0c032208070c03150e0606150d0510051206160503070507050609061b1306081e070512010e060d03111009060902 71
    0x742602400540c10b00c3e90340c1d000700b40010701009040c150003000042c4540045245031b0020038006103030070000e41d86600d019046901040340140c4103414000040c000500c10501c0c00d0140307210607a5103245039607034a4200c408596a4803a06982d000103000000400c1000d00905503046c000e140000c8503510350b103409800808504004400c1d58105180104010001314aa9138000c10650341c142c0c80c03004095000c207003442501190040d25290105000705803412841c0c01b020342d0415503400c8010815403511903601c1204a59a00207807882d506440e192074480c1e0059074110242c1d0a100381011000d80c0e5407800c100c401c40d260300450b0b11180401c42801c2e011840001d5140440744c0e2145814543d0f415912611620300400d02400945004030303000c802818102c070828404c4c00d562a51078203100c20014815409000320410f0b48541d5030012074400341d0107083c0c031301400c1c004203031004441c91990143c8401c900c610100180b4040c84d82d92600d42d0420740030708801d1500ca004c00042c20015481000f00d1542 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 449204469 1250 449203219 449203231
    0xf0312060819080319050c09211b0d050d12060501050901050403020f150f09031b0f090a06090e030c0d08040f110d080d0c270e04061808040608 63
    0x4030005030b07040d000540c161842146030300024055940e90324203104103014610040040c100610b02010000e02c4c80c0000041c0c5010070341141c1c1040c0e1500c1803900e0101070040002c0e03403003294224880702c0621545075500b41801000c05840b11048110b607448c0c484c00c10110740074110100d510801032000c10200c1e48a400003910ac2400e1840c1800d461500007410b40c06640002030081c0c1c0d8030544481da66581d25000c100c0c101d580108941d9542181031141166049044918000c0c4a000c403070810bc0e42c0080c0d2815141c0f030002d4081c180b040061f8007081580c1d44003512078a01d107651440302088150b400e000c0c007104440244002d5a0701d00041001d103150800161042c42041070b81c0c1e0600000840b24116074081d0b40e00803038494240e8003044c001907500006600c00514140001407012100300682e0007140b09024103485185400500c2e510800750054000c41e407150110340d0358800d10201c880c0c02c0ca09500140210f00002c0c5120200c030714036030241c1c503540060350307540c0003c82d040006550040919a001c1 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 449205719 1250 449204469 449204473
    0xf2e0e06070308070818030403080309070906180506090103020603040809130f0617070321050d050f07031401062312090303061207050603070c0303140106050309010e030909060415030f03120608 85
    0xe00c02c24411f6200d01850100030701188002001c106000002c00010028088200c420041c4070b0b40c038512203d01c905102d5039503010500707010001d0594500b1109450480350082c00305451582c03030f03540d02c5c0d04035484014011752000032008840b4105506105220391004020f20007d038484c00c3c5640e075003000c00004031038904c0b5031017a1402d00001b85500184d25040031141490b403044c28503c001640c580c0240f5141e8400305207440100900800002a103074001d04040d1000c210500c40c000001d40008001d0007044d02041d41c4c0b0240901010712a501075441444040d00035042801d0b403e011001c6860545142c6000d500c08814050540ba0250001a5040188008100191508010405500005140a0500004541c1c3c8002c0c14080d030004002c40100003030242c4651307103d4030040c0c5141c0055034800c1ca25861f01003480c0039294000111440044001c0001d000d568581c420840680034841445002020054001002036140926001080e100740c941100e001440c0105a040302c0c00b40c1d001c01499 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 449206969 1250 449205719 449205751
    0x60a06080606100c020d14010203340e120106080303180304061413090213080c030106080a290c070317041112010b03100b0f2e0e060703080708 63
    0x2964030702d004525080403901306007504204030700010741c610029260180520400440400c4001010350003188a4000b2816a01c8031100726048141102814040604001650b8041e890072a004421041ea00d00700105200644a810f0120600b52002c0cac2d030001e1807541c130120500c41400c4c209542e011000007100006c2d810149030840c01487e004800b4001c4030004400a03024500040040400b005032030482c9080d50790341000b0103403c1c80c1d12010b00c6042c0300c40c00790426800852034180a10400c80380a14010904071443c3d403a008204038403031810000510fa6107a80041c40700301304140910800904810b0380d101c9102d4140904040051108800944842e0301004001051601607029217241628140100c41070000080d00600e4070a010ba80e0603ca6900443d904101131f8105100c0c50070f0170383d0b01040c1c0350b02c45030030310003c400428601c14a030b10514040748100781c0210b0300343c0b900802e603207011260501400003040542d4040c020580004880004102d804c5401c071500c1a00003090f20700c40e03260 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 449208219 1250 449206969 449206981
    0x50304140f2e020f0d0509010b09040b1602120d0b0307030b090706081b070b06042403151a010c080706090b0a150302060f1e0c06040c0608090d0f02031b060a060806 72
    0x180d201780e0b40400f59031550f600c04620b0001d402d5001507210100504580c4042c00e00f400c1047c07241504031600c010320713604240c50012051020a0b8442c081d040c540f411410240c559450601424020f151a03805206001001002c03401d0110198040c200f200c0207042d006080020042908400800003150740251010b0b043d100004002100c000c0c41d040604445680c5400c00002d000e00400715030a40b50581000038142450040c0c2612012a48116401c1689541da000d204082c5d41500f0351102283c4851040302d0b4465004a480c21002c9115100aa1038288540c5e10754085030240c42007607034003000c01c03410000c0b803030301d64401d20b1040c3c1d852203600003502d890341d03000600c0c51180404640710001c0c0412403400b4410071402609a280840e04175940b1550200c02d07642d034411040f9030954200c41c41c04000110140500492030041610700080d03d007069101c030041e10310340c00e800c0500045110401035080c46500c0080406c082c9540709001c0d01503820408170740400d84000e034014040c5604006e0030702c0350b = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 449209469 1250 449208219 449208247
    0x1005130e0703061d07030305030a15080726030307120c020606152203052803080115110307030f08010801180609060b03030f0a180501050304140f2e02 66
    0x10071650b0200010860003182444d0002d20200c2807040d210900c1070950100816800401962103414040b1080200d810b02417a07412020741c19110704401600404814007030300705440c42040b24900ca241414500014500d682c03451a0700c21103030f0200242e80d2403400c81c060401406941141d1100f440100501d0402c440001da01d0101042c2e810800c1c04006404107141260012000751400000240c0480541d2030030200c2e161605086980003c0d501c058040312031402e018111034081d40c069651040c2d5a0910b89006840403103544610140140d06041c846a42010001010901e2003941d500080300781030301d00540904d04c10b070044034481c1d044c1203140300c40c03001d103505000c01d40c0d401900116001080e03040603001400441e004e16018000014014070005241e802041040c0d401d6131680810307092110800c0a9441c40e01850b03000903001c00109000c40d0500c0b008400b000d025505071030b0501a003100c05d41c070303003002d60072045810001202c801d078480c4d4180006400300c058240e002d52418551081c008 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 449210719 1250 449209469 449209483
    0x30103051917040303030906060f0f060e0109051f02060f010b0d09020a0f03080403050d08130803061f020106091508070611101401140d050705010c14061005130e 71
    0x120101d031058000303000b071180040c81c00380100000c6051035a52a12070a004010b002480004d072111402c04c40006000100700e152074080340c490720860244541030100c12180e9460b14180c1c0d40c100503044001281035541c410f8000382032260140c540d540020b0056000e401c0a4005181d4200000d1070401089215844c3c4100e40400e523860000190b10707009803000445521103500110320f0404586000320400040c10300401c217032802402200d030240d1011204542e80300c400c4411102c240d402c80100d4001450315005150000002030000d02071403c00440c405034042682d440c1d0300144e4450030104107482c142e202da1390018a81015580459007010802c40da52000344c0329000810020349800c40300e401c1d0502031090884c929141c01e014100c01360380a668089400e0040780c492489400a1002500d01404030b022043c1d1300001410300355181600664000c0c05d400400d607110f06102c40d03640400c036800c0c040584903071514a202008682004240449410072501034081c6a1400c8080140104002815 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 449211969 1250 449210719 449210743
    0x7031d0a1a0403080a0305100807050a0909020d06050403030b0f040506060a110f0d031a031504120504081516050c0615060715060608060d020f060a030b0901091a0603010305 76
    0x500c202402603081d0700d01c148240d078006007070980c0200e00e810079264590041802042e580c908188003607118110b103526040d241c810564002000d210400c00d040603600800c0e0018002400c8615018007502d80c00140e4408590440009999400a40316464204000409c50301e0642d403c01043c6003010210701c0c40d00c507101414007404015600c4201ca22001c01c590090424407a060743c0c001200140050060070310750110681c225030070010000a4200000d03a407030100c810048078007694966071070304012190130042d858100181000040350036542004070121140f400a90300b8200d24100c00048501400e6105140c00c110003000000c811010009982e034008456007002c0c11b5010301107000462a1003030400c014032201c034081810303c489107154012022200a82c49104540d6500d40c104640c080c4012402503024020045030221740c00d014015100b480c400741000a0a04140c0e80060b02943d401da10075007000ba1182e001c00b43c12802c600042c2c42500060b5a02410740d419583d07034544030403034a01c0c0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 449213219 1250 449211969 449211989
    0x109080d091a0d020c06060a091a040f1b0504050a06050901050a18080706050d05010b030412050c01140406141b041802071b080106230904051509030c060c07050303070c030903051207031d0a 83
    0x1203007818cc0001c0d800f540a20080300070b03680714503d4550000e01260010f2090320b00c145041440040d2003400f510817034240e09016903500c1e140c4081250b00360345000005100c0364007034442c03960104040404100b05000341c0441d0b20b070141c4901e071721038504043d01c02c140c0001922520a10038000061032010b15102c030758440c0d003029504c4240f12103c182c010007260503822071034140501404203021081c1d01620540c0072410340012156038081040c1c818450200c841400e183d802c100801044080a550014164803800d000d46890701a0700d0707a004c0000408078242211240c0c441c1080050f50903c1004000c00c0702100100400100318501c0d280c1202d00396011f40941c04110004003000001d2012a18030788035080380340712904040c104182d8070b41020101442610a00d0041601421488207460721564042d0056195130b460240c2103a0040410604400307010340d019001c070001d101441102e00b287d103900b402a07140e074003a050050100034030100180c00390b00a030100454035183d14903140107803910600 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 449214469 1250 449213219 449213231
    0x50901050f1303030c060b010807120e0c040c031d190206070809030a050c03070f080703032a050d0f0e0f121612020109080d091a0d020c06060a091a04 66
    0x41d4880381c490030524520300070b80c00002104254004c41c1c0300d10b5642c0103110401000e4804d00c010b6400120030780e00c4901058500d110b52401030f070f0715000f01050031100301c02d845505c00c80074042000d0340d20703418140340406c1c0c9841d902c40081094000d0081c1c1202200d00403c0c5141031400480304906401c0d2010340206c40000310f680600c60100102c0740340c00740107000c07030313400364010f0030800d807500b40210006109005103000040e030403c48841c0c1d1800d40303d40c0340107010003900d555002c1c1d4810303041420f5040c58251a90114015600b6032101c034200e00d000e038000d05021307011503034003d104641008020302072007018030303c454035901d60401200840b00241c03607080c180380c5031020813031801c04003a0071103444114080010600034840c0301c0d8045094400e0301c62824041e11013808a032200007025501d800103400710000c00820081d543d0b008a070b00b040c3d101c06440d001c00406041c060f030b0305c141c01c85482540210203122503418191030060041c000000204a00c00e156801c0c071100b1a0301c250010b00c2952182 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 449215719 1250 449214469 449214487
    0x90d1b02060f0c06040f0c0f03050606100309020a0b0a030b010804050a031d0d060902030601090203090d08040201121d0705040c0c060f06051206010801050c120f041b0605180a030305090105 83
    0x404582c0b000f010705040310302d0340c134143c907000d1030801900b0000c6581e40c04c07800002a040c401c2c0341c58035007520723400030242071250389040601c6000791050540c1420191503000c8840540c80d9004103202a06030b00c009035030340d013100700d5019080c0e034000c41c001410015003004010103c2c0340803030540d0b81f00b68149480381c03100140f00c41c109406905548019803100201c840e40c801c0140c070307038410145c86209034259601680d9483c1100301300e0008581485403600000d100501451184180715405441410065501c0c1507500003034044480c5610704264613490394024882403201000160300500c001c41d0f0a100982c0e039084010415201d0690050900b030300c0b482c0320187d5a405402032005844060010325900705606906540c1e140203100300301e03e035440c240100e0600014101103500000500da85008280ca03104181c4030804c000400640c1c2d040e40d010381c0b0b01d02401d0032414402c014155030340c4072a11940b9020400e0785c0b200404004511809415804100194120303007600e100500900741503842d48401 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 449216969 1250 449215719 449215747
    0xb07050a021507030902030709180f06230f0615040b0f0c150106140c060621010921111216050d030c030e0c01080a050703150b03090d1b0206 62
    0x50490b24880c05010108407400368540d01200f0701c80c1c0201e04075403d942d500c0144504032050311294140140600500c0c030046415016800811403003084c002455002c200120b1104820f201c1c4090821082e402c02e00c4000030170135003480d07040703c0111818001c550b00c4550400c42480380f8804c01c13140c1c50700441e480e1203e80480c01030794103c1884805071083c008a007411a50702e080e0034010940403610550040c1000143d0a0503100d920781c2e07850040085841d03034030802c11154100c0e411030b094024200e8070302085510a000f40c0086a2050b81141d1141c0c81030031400c44d4100b4034004050412409083c6102a84400264180404c01c1c24074034607030b111025040503096090302100502284240f288907a241981035000400682c003641e0108403924420307100b83c1c1c842080c02e45050004d070900c40400c1c5180d01c141d00803034211300c00d42000180032240d03481d030707180305041a032000c204400080200842482e040c0b005000b000e0242c508080320102caa00d0240f80281d6004010740201000b0400d040c500900b = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 449218219 1250 449216969 449216983
    0xe0102070f030c0e0106080106020d030b0f0613030501060b0a02060f042609010914010e04050601120c080402040b040204031a10091a0111031611040b09040803040c080a0b07050a02 79
    0x140c20078290700301d41c0740d05001418040500c610480b81070400d00004034644600b103041d06845659014001004040c03c04030041d01c22100f146600506681b080030150741c0b038200500000d0382c90320000b00e850740786050460031101240e00c02078030a0420046002c941d035010402a40c000030800d2a04c1880e1a030b030800c3d40c4107100d0090324681c6015480f862034175282c0180082d0092650903640c45840700d031101c00303800c0007055040c955130102e1262002a480781c5001c1c0c011a61140c01850000c88102240a80c0f60540e0740035009040070584400900c0b0a600301401000201076055900750720706895984c540020283c8942882c80d0300d405000405d1040c000c0030315560003091300c01030522002c405002d1500c0700400b01c500315804600d5140d02140038000c040140c409440c1c0714154038a42d0b41c0ca41d110f20340610315055440d94048da0355070b400c04080c3d4a03502440d0080f0f015094182d200c3c902392402c03010710701c116002100c0c1c0e6800390102d2000a283e600903554005102d113880380d01d0784622032083e032070724007 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 449219469 1250 449218219 449218229
    0x10b01080118060f17010f111b010e06100f08070308030703020c0c0307091a060c030702130e0106090608061e0612010f0c0c0c0b0c0604080a050d111c051006110f0307030c060507030b010f0e010207 86
    0xb40c200b0b211088460426100983d40301540386500c169072038496035690000c07480700401952d000d100290001380030b5400780c00c004161200785da2442c0c607002c00090400c8a0f980000c80c00d582d42e000442c0e02d000381c29482c1c079402c10040e0b41e0701d1314100451403801e80e68014a00c009200c1c10812048015002d541e0304142c46007424600203019a5032212034010207010a40030703030240d034030815002480c3e040c1e600d2801204080e503850000003640b1240c0603c031445030203c10400107507403161803450340680e80380f140d201e60103100c0d6540d009140741352815a01c100341070350001002c00d0342807000c044c980102140b0190042c1c0d00188140d612284040f098549000e1500309074034180c508080d60168610b00c1000b007080b4a0409050081c0040092500c000c81e082506c1e120712450302007000b802500d00404e0400c201c40102e1040302c0b5402411882e061469110f44002c50024494100550402c40f050146640110040c00e0a04ca4060b50500080c80401c1c2121841e0410805541007420743c0d00900000e00509 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 449220719 1250 449219469 449219473
    0x90c0804110f031e010e01050613090221060402090c13060f1103070501020a08010807150315261002071707020103060f080c150412030c14070b1308010b01080118060f17010f111b010e 80
    0x437065104540b905400c0390140d024442c1c090000f407420740003804484044012140d5610001c0c181030341100d125840201c1c860038814004140c2c16400f40c100f021b0b0412600c1080051383d0307200240710061200b40c040c0d000510710343c001c40090103102d0010300030507001c2e4000c2c5000245084071103280c0359140f40ca9841080d41200d9012504443d451125204c4d010140020032540e00e40980c081080480c0706110001d80000c80200200c88081c02c0c0600401000d0300514000c10000c0c0c0b6080c80301c8000503079501030f6480d85e021100002c11341c01c110100f480c20b003290b85d2003e0b0900e45405803807540c00c0c4201d60700400300084108020200716020311b280c0c800c44458000c645d030142d11040d500d130056100d40b0380151a0041c101001500420501410680f9003061752480e05503481c2000c100184d4403403081400d40d59444400c0410045000b0102d800100340e5004da900405020402d03c80c00c46481e00344100e425400d01402d9800011030208031103102074001c80c030034205019085008d0041400c1c0c2044035440c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 449221969 1250 449220719 449220769
    0x402041502060405011a0604120f39030c06050c0111130302040b0904020a030212010b0d080a1707081807080313050a090c0804110f031e010e010506130902 68
    0x200d40d000594603c01c51103203008010000c1003619008500040e41441a03000074104418040030711110307402400e0305e1054015420090743c96030340c0624002e06000b1003264540d00201c0000c00001524916207a01803403541207580c0d410340c3c50b1640e2a603c940030b001c051110000750f480994000f540820141c2c0300301c204582d10f507440d20001c08000191403000303a1156080505000c5c06181003c0300307902455004000309009803450b402d20044c02e50a81c00c1600555031032601d0300168490442c01035405210740c02060351030780c4648010300f081408501c0440c602a020040041d010741100c845034108001014019440b000e5800241c0342c81d003513407c9101d09020201d825042d030b8080b01d50100c2074407800c99104258507114000c40c0c0455060200090000706920b010a0214401c1060f0000000020307000034001c0511401083c0b8042002d142103890400041d60700c42e403000300788120202948800028406410003900040104204810000800d0f541d40320b00801c40d40e800da120101000000c1042400e = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 449223219 1250 449221969 449222009
    0x3040c1211131a0103020f030f040c080106181406010c030806061e030601030e0f0a150e061e0612070e090304081b01080703060315050702071a0d060b0307020a030e040204 75
    0x90079043d40f00300d07000311919082c3c1c4800e60013802604c0d81c02482101160651b645c040308944c01050290054510745212000881c2084080c02034401034001701c003080541c1c001c0c1e0034002c0c040310f206900541050403020305001240c3c2c0d0010103180e074503030589000c0e58142c42c3e550005007203118190003194006015031015981008100103144909001d807030820124680303001c0b40c0e8442c4060790020a2581010540303000003001113030b0440030038403140b800280d12442190100e28107607003610000d030b40009905903030043c1160603114036031083c0142c40207041580f49406503a80c1c0c2d81c03103000b08901d10501c075000403aa010100b050390020300c1500c00302c444003020054900004008100994002000c520000d5125030090141d58100c81e8844010780d203018503a15180d008120141c001021409011000211004061640302e40594101841603440103524001000c55105901000d0b10800900030401040c0d00400d480c40c020740c16040c0344c0c860008900000b00207100e150801500707a4841400055 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 449224469 1250 449223219 449223221
    0xf0307030f0215040b1b07090f0207150b030d030b0d06110703170f180705060a0509190509042904080a03140103110d061d1f0203040c121113 62
    0x9014000c1ea200603501d45a419440c3d200e04c910700420420f2207041028098486a88091140d6440080c06031800941c48040c1402518403180d0480c0c01340341c0114168050020070300b80d0f407000c03c5041c10f08110325405840800d0303c501e00d026042d402e059544100f1203091300c5441d8042c1703401394804002c0025030b907500b80291598100c00d801b43c0005100114410410102d0b0380003034014500e00301e01541e00c0c2e4880b80e9a01d104410801c1c0e81c1130700d00500500140c1500c4110103054510483d031105500c07042e026042c02900c030703007202c8480d41e8000030840801072902c8845c040c03078206420a00422111088500500b03018071002c2006103001400000c1006004410000d440944120758050000411a221003805a4030a00000d00801310142d030203010740c0781560594802ca8410b05000c16a1542ca0b54440080700b4103420243c503c2c0c2007900000310f401203d140700382ca0320b031400e0307411411414282c80f0814595480c1c01400125140045040c2c280803d4070b841d07103a090001031072603500380700c1804c541d8 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 449225719 1250 449224469 449224493
    0xf140a090308100609030b0711061009230f04080c150a050106030b0a0b0c10150501020607020601030f0b060f060d150803041212050f0d0203040b010e040515060f030703 74
    0x81c001800140201c0c0000300551415000c0f18002e0392460541030860f01c41d50719101000d00640c0901491401c400d0010f4000c1c009548104c824080324803074180382c80c0c07541003502c43c6030210908046841d9003d0814114120906800104081008005565500c0c1601840c030440f040d5903810710420420760810000200194840d9034a00801d00240e40d0307401094080c9c0320400e810704e41c880c6c2e556009010342c01c4808040c14801d603c0b402210300140984504404039416201c1035141002d11200038005540c0404c1040e821034143e1004007095803460701d4004088071140001411440d40c1d03004500503070781e908181c500035480200619510180c68254200810084060041e910400c4100054406010094030b0451380d1200105041a10691b1040d0300e01822020034400d0000601c000088110084054001c80e2104940142e8904203424010a41c00050b8000801044880c0c100400580003040521800b0000d0040410b95210000010200d01104044642501c91108000107102c2d0640d810 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 449226969 1250 449225719 449225723
    0x706090b15040b040504030813110406030f051c050f0a02031e0310050319030509030f06160305060303070816030e091f0815060d08041a0a020d0e0901090f140a09 71
    0x402c030b4444041c3c18031003620421100030f40400c010340e001030003403808100d52218062190622800144001c0009000c4594a800c20340f442500d003c0c80300f041000411982e41809441c1c04850707101c10061b80d005219100c3c9014000f84446c0115281040030700030004d03509612550001214008000d040301c80298204660441650b45240c50008007402d02003401d00711601c074140410000b140c251400c0e030f80369000d92070403074149c0b15200c00400c031041d080c80101d00416280640b10006030140c14001e041c1c1d0400b6000e00d21070b410802c64800011290340880c1d8149000341d00c2c850012030746090968450b0b10090190381c020888004112032034101030712400c40d90001074040c8062680796404142e80b410343c1c0e4500354009a0750000b256440c03030070107008034826208500a518041d2030b80e42e07041c10603a9028400c6016540841e942c080c29030140520184d40e1000d20384103103d9482840014061001840b9802e1005d569071410040020303503402400300c40c0c201c10704031047d504100b0100700040c03a0511003 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 449228219 1250 449226969 449226971
    0xd0f0302101e0f1e0b06070b0c0c250303080910050106020c0307060309080f0f041502010212070e010f11010e0703051c0804112b05340b0706090b1504 66
    0x808000d44607244130741140c0ca01000700c3c007001d40b031029442000400c001d440055020303c0500544000031000f5421601c5000607082480e105c45270312800074940000055410415803000382d81541e600c400906403001c0302d0b0503103040e401c0c41d102c2003065820f0219907500400280c0c140f40001c6400398000604d4196500300350101c07540e1a5984c0360841c1111002100209016070030000301c23100042c088040c0020040134840549043d03511000a001c003681c585045c03000d40d40109907584582d5481407901d902c02503500340fa0700c2009901000812602402d804102030010b0300f1881c58001c034095000e1040b81c18502c007110b489075141d0400351b47d00c10b5403001203c280d2000c0091114000c0c4135040543c01a07610480115176a8905c600b00044511a10064042e01c03d00f640502a00d4041201510b48240180042c1c000c0207184a190300561a40c0c0d088070752040e005031b401d5454900b444c03c042044841c180b044070f40301e000528180d0702074840301c8006000002550180312140c1d104002c101c40000341210 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 449229469 1250 449228219 449228231
    0xc0109031110020c030702060a020309100324050918011506030e0705011b03030b06130b070501050114010e040b13020301081e0c01140318120a02010f0603020d0f0302101e 75
    0x8801010384c4540800d10076a50000c0c400300340142403243c090248011203005903403d0140250109071824000d540100009460301c5082c0350303012400399499030080307114000c100780394208404900514000780042d2190b10501801c216078030000e6100d000c0c41511868403604003540d402c0001e0181c0007110055a10b40104000010308d0743c00303000c20150500c56442c0000228000380c60913002000101310141d0440c20401095442d0105500864080c1c41102c40c2d9030b80f140903a0401508440301604070700b41d0f030103a44003002a183e80100342c1540c060008c850100310b0f0380c00741c030100300082100001c1412550000c0008104140302003817000c0d08204420810440c5000038a8465031030388940c5415000c02d101030001c4a041010b00c00030f59020490400100200302c4064405113010519540503202d1000030a41e80c44031035080c00380c4180012340f031000b40459821500098011480d1400040c61414841e40e03803001c060080c0843c403849a03d0b0f40d802c0115030b48004011418107005a10040041d150070 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 449230719 1250 449229469 449229493
    0x512010e060117060403120b09130b1003020a050f01030603060c0801030203120f0d050a090f080a140c1b150c0705100201020307020d050901090512030d060b0a0c06110c01090311 78
    0x360800d92440c0c443c0000e10190b16651010b030b800c208048561100355844823088926501d8081340d1901403062031800d240c214040741000100400302410002e5501808581000540d0f0ba03550b0500070b4460444080b0280c1485000580082403640d0004005c41d06110060700026044035405040340c2c000e8090b0790074080c441d08070125501c10460041100482070081450144955010961211034810000b92407103103034030341c01c80a1a1071038049a4900c0c000910146d000d0780110b204441164011000382880244d80c1c89a2b11482c03045882a0640200d5298030b4031903807171040b800081e0010400581d510048003090039107400e550301586014802e0400e000c5446441482117a01c03a80d1203602402c01940300c000103d5041d80b142100340d040203120792004ca0700795078400340144002c86000003540c0e285c07440068203050300d075a0fa02c021a80e00040c40542d0a42d0307085031042c400381350b04c01070020785102a6283c0b20100c0c003911003c0c1841d50b01e8114400101038116036100c448941d40b00846608004075 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 449231969 1250 449230719 449230739
    0x2b0b0606070f03030c030905150405070603020c15100e091506010c021309051204060909051308070813030b04030f020f16120507030b10090b010801230a0512010e0601 73
    0x54030004003086030084000b03010074031a0b0310400c0340c000145004943c5008130344400e4a001082101c502040d6066000c0c0400c00204001c0c10000f0a0542015828450703901182c9407a44991409047c88415140010701c044440b05840030242030040200709541c01d0580c80203580310003502411644a003c900811220743c05031945c8580c00354020104818441c0b070081d110050139240030308941d0b070300c02c500801211018160143c000b0700442d40d00c4580d95464042606c3c00d9a07405031006010114006222022400700c2003115801070b08019440d0356480c244011044504581e440a0180807204080c4030406a00c86a0040c1d001c0c8180e0881d8040c40c13440f035000b6250503100480b8000411040400c000900c107030403031428400c1c0113000746e61002c0e94940b9000454035040360795009504440c803041c003d581262141180c212020302e426041503060402c050340c2964032400715040f440c200c41031076441e0798505280c58050304014212808e070b10550040c0602918049803030120502035800085419021 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 449233219 1250 449231969 449231977
    0x902040b040e0a0218100309021309061104050904080309121603081b030106200d0f0f05031005040b0f0a09021b1b04110c07030b01030303060816050f2b0b0606 70
    0x384401210a10000401300446c528040700c880d4249901c1d2202d034009a540e60701c4d07000c0e1740300308000c01040d018058034106040711410841c0c042c90308c0d8148014171003900c4070084603034819030022042d552620f50404107840d2200f4105404601100010141c800180544055001600c41c0c1c603041120341307074280b030040341c10110481c0440c0d005041c801003000d07510400138006080c1e07031a0741801d400001443c4250911107510001c1c404200d8038070105100c107510440403640003010785442421810042100309040c03845218081c8184c0c0c5404102500342d03a0b034260015010401054040100d949151160194124500685003107400c200110029100462a010b040345002030710340401883c2c000300401401440c0164040300003e0001240c50141086450b02650003114400313201c1d0314515000701075405030b4112440e40c0c6c000c0301a1540114011030b06006882040751403411000c840700100741041c0c00f5180d458500400e010f0740101ca800320b008030342240d502410b04078140da40c620044c807000d40300b = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 449234469 1250 449233219 449233237
    0x121303170306030c04050a060306021b0607020d08010e0601170723090604030b04080c0d020a060f14130627020f01050702130f0f0228090503190c0902040b040e0a02 72
    0x4025581349140c603500941e4402e00c0c11400164550712604c84200701c0e08150340d601070b4072861000c2c04030400c1080001c6980f0001a00c01000405101c3c00c0090900d001131003061000d2000c1804501160f00070440b00c5a910b4803030030b2071103152070046001001811804018008c403daa819505812005001101d0124401030030f041d03d0140703559207001d2010342c024801e503841c5500744002e2408542c00d0203c3c520b1109140e0040610707200c1c43c24003000b00c4040484100ca441d00c1c01c400a0424030703000301202e41c8800b81d4800b1610603915410f1800c0030304082c3c0d110118050005d02c41e04040103540e1000b180d018026a01e02c110342240c00c1c01995184100d000c00b951007404441100e9208003690802450a0244d01010554a8690f00c03942c080e6000a05004480740d0031410002025048558514201c009450500c003000c2c0f0f03000c00310346c4a41011344140c50b407070304024a4070240240304110000401e10880b04654a40e5200100109508580a00c0c4600001d20010591190f458003c9e640200 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 449235719 1250 449234469 449234473
    0xf09060a030308060d050f0a0302060a151809060e0a0308010503010608121b0a030302030604050603070509060112020415020d0207080d0807211104050307050405011d040512130317030603 82
    0xc0e0541c0c5003900c560303400401d0603900c11800d292080c0068001c0c08482c0c4414014001440d03a0141490b000c0d041600c014415402e2900c1c15000c0d85080e03480413000001c0702c04108a12500606031400070f006482112030241c200380c21b2500b00001141c00040d80b07003502d8041e66070340990b662500105400c3c0d40c00d510131004640d005030340000400242000400038403403003108202030551f80b83c800c00d007842c10300302d13043d0040781e808410003c40e420b1501070356502c4081140a000c240742000d000524040010b000b06e4100b002d03142861005000940c11200542500740b500c11300c0b030341e0200c4001e58610030a1014801400b440da00014074640c000350b4403000f01100e865142103076031640d0080382c1c1d01603580714042c00008080e442803200d00c074612030000c1010204014503511818070091514101141d448103000f18039040042101c02610510790148068100740740303c06441c3d80c03d05502e4081c800c1040c181030200015050b4141080b465010200e9200f1a01d50240c100074124600c5a07002c200c0b035064060b = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 449236969 1250 449235719 449235739
    0x209090f0a200406111006080105150d0c300804061b120e04021209070f1502030f0d1d06270646051621020909070302090f0906 56
    0x75805480c4031241003070311030708441400c4018074211087c1d8006600410301c50355030703d0601000c8000520b00c82c60050051b104103000003d69901d00d624541c0d14400c104940c08944240813584516855403c241c0001c060300c00c5c0c0c4143c041c1842c402a500c14031070100451b814035000a6005204007001a0b02600300b100341200c141682c0d025118044840400703588103a007003050781702ca80d404104450160402c1802415483d0070101e21b4018044a0340001c1e5400068058004d041c55001048848a051842d0b40036201c10700760412401800050b20030300403083c00301e400c5191407100059041e12640c00d0101c012a6001d903c400c4c40a25040c40303401551507088000056100c034003550360000c0c600031003240300640e02041e8404030307103561a891001c8091100d183c100761803041e0900603240c11120380c144e00d1500c6003039020064034016010114650b4110200d107000e43c4103030030303905451411801901d201d00d5441c0968004009507c03890900c1e119818008505120f81082003101d07200d104090110500303 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 449238219 1250 449236969 449236979
    0x20307060f021e0604120801180e07050402040b2d16032003092b0f0c0312050304050f010501030816050c0d0c150f0e04090203010209090f0a2004 64
    0x280312900d00501c154410006a514214400c0e10110781282684010b442c00f810f143c64501c02580d4141300e003404004091006100d40450102004186440071030000b52060074003004500f400519480194064404140095200e80d43c0009019400803c4080d98216111202411500140c0700c840e0410010a105084215405014145280707010781810711030120722542e9400c0c004034502441d03080d50008640b20029040c40314650409980e6601c00101c110710b402030501c41c56900c2c0e00064550080210550203102035850b0380c0e0041c503000b0100151764214050007502a42c8142c0e0304903140c0c4118034400c04c10710380603c5068180c83e40841c0642c030303004840011038034000c104a019540c5000300c50303044800355642d86221003424861411803505910707180d41581580000d011750024810100f034030707459859005120040050080710700182502c15800404c0c02030044c02e4816401601070001c3c880ca05080b1640c941c841c0ca0880020304c54000d014020001b444100042250040000d20003400 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 449239469 1250 449238219 449238227
    0x10c09121401111b0307020d02010c1a0a05011706190e0f07080f0c010c0b04020d0812070314090a03050906161a010e06060403030c120201020c030a1707030902030706 73
    0x1405001d1000d00700105014160840d42c0040540c80080400105801080c051000742c0b007001100601440c2000c407103402207000707040030302002810021840f4021007000902e001c0c1d8040345803404840806450401c8008000303042c20301480390310445208028981003000540d403032040d800040442580c3c02071445d1700c0c02400285110449078000c0c043c1c1e4003425042042000b008022000c0204001e4800d00e04160821a50501d804e0400c9500982100450032909540d90042d50665040358050401d042490140c01003240060306400f005041c4070121364941c00000c1c000700d042c3c480614645455290540d180007081d00140864014403210800e4035206025000300c125410105801102e01e43d10305091095903208803441c103c110f070040c0032144020032015800181590060328060644c0c40142003c0c1000400820070f42c203015466070228400e40544101c1c0c1c402c00101c84d1544c84042003e8410b03501c40220540300c4800e400051703041442070107031411454002c0c004d44001824018121 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 449240719 1250 449239469 449239499
    0x2180f030708150109050f09071401120507020a060e01020a0c030c02040608011d0d03091106090a17030d050f0c040b0c03092d1009050d14030d02040e09010c09 70
    0x40d40c0350080810010342c00e103043c08402a010040c082018240d030610924104a0320040c00303019402c40c960040294200d400a640c0c8182c4da9821583c42101110030012200311100c0c4030f000300c04a003080e040c86429034000600008551046405000e2240030040c05400c074004e1034003a000061200c250080460b003c4c4046241b1980068008901c59444080740f90a50700b88400382c0c0d80c0c2c44d8403100e12891405040c07110402440c11803900340030008041d202d9080c0c8a0b00410010700c0307594005900745650f541c00352035100500070340200c072000400750400d20b9180d401041c0c8040b01e180c100700c0001c101400c40c00c0f0040c455038040400070708003803c01651666a0704085240303122407004200310f580c683c0da8220b510403ca450041c541066013000c002c0c1030081126035404a0050b0319000d103109030141c1010150080d07030416106011200d443d824000b550b0b02180700c403900907020010313107110008250780007002903800710406401603880c0c9034200c80c03c80d54401885000505115014019030981220300 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 449241969 1250 449240719 449240749
    0x10f021b0a0b030702030c10140103061806090516090902030706080c0d0608100608062509030f0503090103062c07050c0d03050402040b040e060a110f03070806010801090218 76
    0x1000c80d482e9010480190300c00c0e60b00c0c0b07000d6407000c202c00c0c0c0c04420402c1500d1030044001030a00a01c28514150b220403441804010a050707201c0000d5040c920413003052000c2c0c030790021020b0103010910b04000347ca4400c0c140c000c42d0a58072048012890030362034007402c24065800381c0240326140c50104100d44000018140131000c8804110f000c0c4035070f61074000e84004c3e00c1c1180c0500880b40d0300f042e41004540855100741c040d03801100030030501c2e5074101660b62007840b10340b8481c0c0a003140c3c150f00b00d03801103140e00b00806414410f6900d03410301200001600742c0300400c0c1c908100703503500d41004022f003120021810b080d11100030741042107030044090507600141c4030f04009007030400600099007040404000c060010f41d40e803041209501c0c044c000c18840c00c00589040202c80c110415098031500001d00c2d0700c070b03940e0310780342400740c503800200c106c0b5100d0300d40d051503903100e05000000034490f000954109000400031400841d6584280c42100c1182949540000e24100d50b030050081194450b0f4032 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 449243219 1250 449241969 449241979
    0x902070309050a1d0a060b18030102043c03120302070512030103030203070615140603060a030c1d010603050c0405280815100f12080f070c14010f021b 66
    0x9440d21140c89031405011441d180c100c00a544c280d036020b880000030000c0181c2411321008100c4070360760303508481d860000001010724000f03000c1d0200e0701a1146074481d4005c1001d546141110007810703000c052040c00302d0000d040101441810115054115010142075510085a151000c80c0240e0050080e14420000e58180b0300d140303115102d090700309a00c20307400348c0c000040640401855104103a48072500ca281d0611384c07800d203203200380482820300115016040020108119542d1061200015940032201106240c0c81d4108044144107000c7c1c520841c2c501c850010918074003d020f080c6c402d01c9203d450900305803030542048040c09600d00780c6496000050052594410030031307103900180c011407000b010301100320301040456610040c100030301500d040e01d06000c0018840c026204a0b1080b0b02442132101444c00c20303801510030f9440f41c4600c50b00002c0ca95040004440040701254549050501e05030300c0358006461020205c418000160000c1401101c46002c11840e55800034000d80 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 449244469 1250 449243219 449243237
    0x7050319060611010f050f2d0a020a181a071109090f120f0733090b06061305040e030705031b0601150503240910050f0d020a09020703 59
    0xc104401c4841d0398000c41c0004501c0c005094000009010310520200c0310341c400c1202d8030b04551403112540c400b41510f4400901c0c0c20b02c0006081c18032045941d1a034002840c0c034003d0405504c0700000354000d1182c1000b19145107090504c3e030752641d482c1c0086440403800140314803a042042445a841250200c921341c038078218001040d103c928000b48520351b075500804d007804442084c2494501805441d00911104001c1c80f2072001915081e80c1110303510403240c2258003880d5003680e90360b8101c2c92403081050400c15403c2c401c1c0100d031308043d010034041d0036494115150b890512185100d285455000008104c20800c585d040039030140080f500b023a4240ea0902003607a842d075041d680b012001c0305402d421201c201942800c10310010380140a80074034a000c51455080242c442d0000070304040c541c21142250385500d0b035500500c7c0110644c004d01c0e40740310346400e90111441c1c214034014140900040d000c1d040c03690030f003d40c4000350a40c0052000804a03e801010406584800401c40810807044 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 449245719 1250 449244469 449244511
    0x40f03080702181003211d1507050304032303160305090a03080301150813060519060e1f0515091201020a020f060a09030e060a1110020703020106080a0803070503 71
    0x30f001540030312541803410001d40d10354104001000008168000b4013080740901c1003c01d5048100d85001c0101507051f140c0c0040c5540005841a642001c141c0202c680040c0300405c120001c801842500d201b40c0580039042864804250304d0041941803030102d41c420403a0a082600221141c021548a40f5080346010030410101e0f0150405d40d1080751009000720040c4001081400b000c11003400a151101d064a000305000b44003011b0b285010388401c0c0d484d00450541d01c2c0841081088810401d4284202c40c1c0d914140c50244c41c00300d8001c10035901d2010542e4100b20100400421503100401c022410040c2d03000305a0301e80d1094200d24bd021161400c801c10b011000e0000c0c000c00540e0380c0252031701000d0804454284140180320800306031600340d400300003d405c4400030100c0c00040d50741e15203030103030000140d92041c84089042d06078030130030701e64410140703860700140b0565200e0384c0213104e40c6a851200a96a520050004000d07020510004084a10500145a20440710042e241d90030400d6 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 449246969 1250 449245719 449245759
    0x82809050705030d0908060912091002120a1d0321220306050f0c03010f030308070c020d0606060e03010501031104020304050304180606080f0f0402010305092401150203040f03080702 80
    0x4113424049602000200520081841076039440308a5001034128480145885071180c03090b402d12901c1070225091004a0350710821036a4032000050000907070341c109140c00a4840071280f00529060a4403000b82c000b41e0034045080c88040e150008052107a410300c8403050f07859003181c15200e022a04501c002d600c0f22403850400402036015420004080c2460304400c00303170072001003041c1c0ba14042080100203644100d45d025080f03a0f00f42c074201c4a84c2c0c40f07210044400d55410f04000c1e5000d8042c049400c20720185500000496000b81c80c1c1e55030001c0d0800c03d0509a40c000d2002420340c1c5011111a840382c08c040c0c004552040c400d0040e0383c681a2a030300600400d000d01d1600f105141d075200c40a01c8440d800c080f0a680040345003c45964503e406070b04011444001803000b41050344410202c0c0c1805000c0028805545d0504412a04d9200c509100d0148030f00034441d81c4003041e46242301c2c0d040c490012044405645181115200071415a10380030350301d17840480101e03044010141c0030007c8442d1 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 449248219 1250 449246969 449246983
    0x120b0a05130c090f0b010f0f03050408090d0b07030f0c1e050702190f0906030f030e300d0504030b070f05072012030c030d0504050102160503070308280905070503 71
    0x1c0f544009802d9800036a400129801d21044505004682c0501c000305500f14103c1409a100c0d45008215542c480c900340d40c0d9801540140d075001360f407840066041000c0790f2800340c49407a580d0340070000d1302442c4171400282c5091a07951404150480c0ec0e60450141500b00942824110700700545048040d6001c00d400420564010200e80341040c424080000030480c01d20090844800c2440340600f540c58208900a8a0400400b448052108192591549081d450408807101310701e1016128480317a24a81c075022035440e20303c900858049014241c014415102540e070060503c0a150380c502d02c1c00d072061904107042a0911505000300c074000f88ca42c500d01041c80794444c0740080f522442c2000e108807030380021003c2c15142c00511203102c2a99000058408100d8642000328064445e401e00b00c3c02885031400c1511415103802c1540e0074004000b00510340144a5551840700d80e90310384258183c0302c210160b0f034001c1030756208a000c841c20b03140c011000d2240940140d80a140d0345800007440c0500e = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 449249469 1250 449248219 449248229
    0x609051c02150702030717130506040603020405030106051801051c050607030b10031b050f070506010816090603050601030f020301020d0c1e05090306040f1e0615120b0a05130c 77
    0xb000240d103000101c241c00740c4980000d03160006505258403a551701c0c00500000e000c1064500010440d0038007140c0d0014180020071018000756a6943c4450004019522902a40d0b0082d0f08100b0000f070a0b013006046007801c039100070350341d110990034042008000f0801c800c0201c80d125030b09a000700411002d04c0800e005c0c0301152030000d12200c0d04004c1c4440c44010a90100a041c50950803a6912101c03500b61144070150386020391340c0381c09150380e0302c5150043c80c2000d4214880c4c0c1d4008203540d10002003010904000340b06c002d0f441d96071866540190b410314000100b0f40d412038001000014400d055407034a05100030000360410004041f41e10448030091900e000080c1c09207500702d2440640340f240307080e105030392401034070b410800d2001ca65036890141004040c084030352070b030100340900c110804bc04400d112a81c46400c0b443d60400c000508045d070003d070240700d82d04e18002003c001c60080035010b541e0182a001065031410f403003000030a00204000550822503004100203007040030f51070b010702 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 449250719 1250 449249469 449249473
    0xe060901110703080c1506010206070f08060d0813091803020a02091302040c030516020d0c0f05160f0801060b03060904030309060b040204030305132c09010617100c0504120609051c02 80
    0x4100c0924956607910140120781950013881c00cbc46581039002c02d001c5442e08182c10650915210f090106408420211018012000225211881c4502b0403052000c480c0200d40901c0300e45030140d02c041c40107540c8800240035078030141c05070006081c007080540d84010034203090080328020b500480d095074501d891000c0040c1c0d549040000c0c4844100100e4112081e0b0301c000d01035462a40009402d20500d0403000d4000030411060404005040003103000001100c40041d0b0303400d945455400b12100c490145414550030848045500b20081060340e10480c00204440d20139203550314254014005500c05441442d00d0303115406d841d494a0000340019403103640c629903101c04507803c0c1102643c00350081c8a01d8141244005080302c81401040c04842c030304030b42c0389250b0320303400780003801032116600c80c107a031081e0b00c10446202800402c6041c000140f9078001e04c0a154482d100301d03a640314901401807010030400ea844046a800c0d0f000c01400b510440441e9513000d07030f401040e08001c0d00f4140c800c00503 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 449251969 1250 449250719 449250733
    0x622150f0f0c140303190203191d0d080717040803010902031302041503060612020603061e030714040518120f121003120503010312260c0c0d0e060901110703080c 71
    0x5000c0f6044001c04002d00001b0442c114200015080480340c882d200d0517802c0340d02d601001c5103031542070b03580d840410403d100f102e0f02e00b110243c0240c24a0300403940030b0085280443c00c454113580d4401540e10a5601289007480c41c2c1c28401148001d40025004020f04249440311100580303841c814503400381e5982001e403011606c1c603d8808256481900240741a8401410200041e1140300980340c200c0403c969840b4000a5610209449074000500356071500c104072001a11504010b030892041005031030506c0717550355000001c0d40d0f403d140e00034070200e07501c000c4c000030305050200083c21074002103040d000c4c9010310221581e40c1a4070191007a0314040380c00300307007001000140060303506100c0c01030428500710740c075646030f2502c0c509900c4039140a120b07c0500c071b00c80d43c509044449440042188043d200c6041c411800d1259070080024444588120280a220796019070907805610600070304051078611044011a0005510117030050180b00389a03002c0001080c41d17001c1c100b07104041c03004000c0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 449253219 1250 449251969 449251981
    0x30a0303021c09050d03020901050c0714040b04020a02150915012d030f080d0204080d080403080702010e06041209080d020c030610030f0605070203090622150f0f0c140303 75
    0x5001c1190078220703895440d003c0302800080c80803c8030301702030b4801e040050321041d01d6001a00c061180d20307410381d003902940750003003411403050821120904003a2030400800a0803001d0104070f200c4c0001c0c0c2405680900e40100c0241113541c1013503031201d031440a50301401d0440a00d503020703c2d021b07000158030040880580464590043d03003007aa0388409070850515614544031040c3c070804004010f8800140001c0002d880707030b401e80482d4020b0904104035101c0b01c88941c07000b84898416101200003e001e140402c215910500802c0b004442800107041345445581d584560300c101e010b40c0e2828802c000c1400a01c002c82440040715035a80c40d0040c05000051204160500a0003080c80740800c00968040c0045030248040e0044140e10000004039500c070350310268071714000d80d00c40701e612510008910b5010000c020701d1403062101c07845040241c68803600102e480084079100301001075803c0240c0b010061261655000040083c10510605200c0744c41d104005001a59080800da1000081c011 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 449254469 1250 449253219 449253247
    0x20c06040b090115060806180405010b041a1531090e0d09030204150801051003053310051801030b071e2a0b0105011b0b0a050411030a030302 62
    0x82e020032004002c0015035103058003411010344500400040060401c00111070b9120705407a000e080c07101000c581c1c818681403070801d0107424015145800f850412000b040040322a2401444211000f419000c000d9840c0c60b140642d80c200c5e4900e92080d6241600340c0c4980300443d50155440045001446d0449007041096025113905164003459644403800c44c40149500c107034040c003541d034112808107a91102ca800042c004496070008041540381005100c5540f03d810300407170403280300e039058601800c00148490341c0107452002e140305610250703501c4407840d0040d0025651060100303424480e01b64030f68000c01d045923200311290894000e02401403082c8400d1610305039202c1401e14240c59541090750b810024801004010030038880380c242c101c0c2c0080440c0c041384541e401d1105122084405c2800e044600c03800a1040300e000c03801d403403101103020b940240944000f03501320304d205000781c071901c141200822008200b502c007101314541074851541c00380404094140241e50250712101a00701100b = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 449255719 1250 449254469 449254471
    0x20301050907051303020904061407030b0307050a0b04141c0b04020a0503010905070501050a03020c1902090c0708120a0207061b1b0b0c090301091401051b04030f0b0c0c01020c06040b 80
    0x140c244041846080590344e41d404602080c0c9134103468507485612545849405000c1072504802d805069008006100e03901d0761041c0d4025008604a4100a46e01c2e8207000c3c103a07000d4007580b824603404110512185400c00c060105200c0c001d41100c400084140c01c851150524a00c01c03202e62401d401400709500d041008040503140c11002000820100d40e40c4076a500748620649050000214180c800c29002e82e05860304200b041080e070b5201c582c1445240416520003401301e10403940c1c0030220f0101c020281c2030320b000d2640819403526050f021480c803020113000401414072950204500000a502c5000341d5940803c2c0b050400c01182a241c1c6c081c1540018003403c00d00030413824541d902240440c0902a041034070401c440e69141d03081c2c00480d0151204080181c8a46215000c00700b0742c0d041580218850030609900408022011001e1505032140f03100c0039125540202d41000828003a060341c0d0b42107400702185602e042e8440728420b09a81141e2050602900044104414481d01c034500c9 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 449256969 1250 449255719 449255731
    0x30b040506090a0b06090d05071706011505070804050d06050405061b0a03051f0b0310080a030c0327090e1903020303180709110d0b0a0501080105040b061605010203010509 75
    0x203202074586240800c5000b20700414141ca0103448500311011900c8240444042580152002d10701041038104582c0e04c007134034480d00400c841c03469020306040ba00820250b041c0d8000c1c0300441e0140040d00c808840c0d6401110054a030744404200004243d61800c80302c2d03c0151041e403001ca03c41c41c7c141443d50414500425050464040c802164017000c107807000c541c08c218090031300089580b5004405081c0031503018001000251501e0042085a4030201452003051020103120300d641d03e880701c4603107807412128010003107041c0851480c00640103c404160254000c010344004851205d0440c00c0c0c5900c99000e40c5480f9680c21400a00d070070180301400d41032030382d0b0407100d140003000d9900a50307901c0002d014192481013080701c0d9040340414032002000700015a07041c4818801441c3d4108254010315208154174500040384041e804d143e10283e00f251416141d07031001d40e1902d07080c040901180d4001d10b40c4080c0070402542ea80403039280d10700c505c50141c000141c5075810541803189070503000e411 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 449258219 1250 449256969 449256971
    0x102070303090513021b060f010f030507030f080c01052502070e18070b03070f0f0f02070311040f0216030206010e0411154f050d0f02030607030606030b04 68
    0x424008642c0140340340048503c02c0c0d84180c201490f05803194020300034030b070b1490f28545101107080c081c510f0000e900c43c0646828450340301307141d988a100440c40d4075a8407006006810802e01040891a2035224000440c0900c0b030f850f1a00e030000907080c3c215001143c030002c1101c403001c0c09031508103c0c3c0d100c180e0305220f05d0004281040c28052400082c40300280522454205074001e4a003084050195200500e00100a140c880c10a204040e241500c10f0760b00134000f80e8140c5494005500c2400c41e2501034140750060100d050075610707146034840011000035001900c1b184035065005051006258400f00c4491031a8900c15038603000313003444011780c0720081084054040c0004245509a511080350f011904400c2540381c4035042d1400f8050824112a1040c41c4414809610004d000d09907980004203c000c500c40400c1c82d01111000d013100e041503001c01841c0c0305114900f8040300c2c03011140e008039510390450312a0b034002460a04100c43c506e00003a00c9901c00c2202c550075004621219000b00d074 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 449259469 1250 449258219 449258233
    0x121819231c141b101505060712030b090103060b190b16060b06120411010504081203041b270c050d110706060b0d050c040e06010c03110102030109060e06060405030705010f020f2a0102 80
    0x4002039072030040500141854049411270443d260281c0e211003907288000e441441c841d030b0b480c100000180341e802c070064001c114000c1c060390411100700840c016aa03505c6c0f81d15040c032104000d4402d01c1840c481c02190000c2c1d81d00e40c0d51a05a40b103a026014090480141c4140f42c5040c2c40d12800c44295003940c80d041c01014001841596408903242021007500743c2269100d546900340001c0502a400740411034106a1030f0200d5800c01940341240401c65142c80307010708503000c1982d44101c1d110a4012400150184083c90750200c050f0071012958845075100303407d01840e0b85601c002c40b5295401000740020002d0004580045802078503804860105d0540c02e0501d0402c40c0d41107100003e01c1c60381001110107050301003602030107080344400c404500031500e943c1c58058020003040e0398043c0402c600350701d0340018031b5441d20008803000e40303d0290141441914000041d100c8002c1c04c010142940030315070003065190402c00c107404803242c0110309048101c0e01103107180440710740348190390b045401c500 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 449260719 1250 449259469 449259479
    0x708010b041439030106030905150f0121080f090306010e010b0414030316200d110402092707080a02121819231c141b1015 54
    0x1510f407041c5040b8098032291207141010310115484021110805141c40100012850035410390200f031100c0e00c202708890688950340390950386207004030703006035900c3c0c0e00c00d0062004008441d080c0500c0480d09422105c070300c049603103074006a0051080452070310008904480e592404200050050081d203040c0016541880c0300f80c4079078451401460710408403503803a01e0b540c0e1801c01c101c40d070182c0310800b00c4288903072602d44415101713500c0c103800702d8050b08003544000c64582805400d107066400701400601614481c14040a50030840c6099440f8403c8600066600c481d803000d0749941a03c007240f0401c920307101001404940c0094081c882a61061060a5203550100750345030b001090200050782c07845000e9009460440d400190102d007500c40c1c41200104502c20700250840c156182040704041c16102e00155207d910218106004280280c182525400307882e50312280c04407080914948070410750600c12141175008440140d5009000d0003807104030710b101d8000c0804103031044000584c681 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 449261969 1250 449260719 449260741
    0x230c07050303060d03090518040615050d1103010612080403032a0308100902071b0512070b071b06120506190e0a021207120612031b0c080708010b0414 66
    0x100f80d20b000b1014007400d1001d060107030040600401d801000e25400e500300d101c602c1c182c3d20054a00704c854908003405035150030144a10319040c1d4a01034059008e400c240d0b1a152003044000095980555941d040440c1c6004110b040910050040c041c607a5540e1841c83d00401e4001c52034414150501a081c90941e0035034105002039901d6058035002c14141c88020b05610100915482200101e100044480c10411b840c8185114400c00040030706170b40e40e46074180003544100c40c20500c40760b04003402c1480980102400703851510b001da680140900381100b29116280304c01c0d00084082142c03644401c840c1003060250320b40c0400151941d207458142750f00424800780a030301810b94885003100002d030b07440c0740b280e043d60306c80300ca007071140f48507400e05030300c082e01464481040d4000030341040d502083e04108507030064a1a581070b40c0d5401c19512130281c40000c50500302040310b8501c00c40390001400d01d4100419030280c01604c00028445640000300402c45080c0400d01c0d030004000010030803119a8 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 449263219 1250 449261969 449261971
    0x203040f05091302041d1009110d0b01150e0a0b27030613030e0402030a0b09090601060503060d02010e1026011d0c040806130201300f020904230c07050303 68
    0x8140d45c0030803405420b0300d20204249141024195a01c101140640c003603000e42c0200400302c0c01100743c01d00030950b040c00e0101102c2c40b00c00180021610a00400036505a8100004c40031294645202d50b0b003003c40c00540b030280258403003403819902081030700003030310403104500c2d948900640380000700008a01003078855a000b030601031442e800b08011130602d4040d082041c0d0002c0010406c40d07581c507143c2c500a00400e2190b05841c0201030903c00120b8203100060700c941640d104d600c8907401c0d56034520421100c0122110100d0410041a500390100d49441e61001c00102e0251520512100001c2c0740d1602070f5050340708003500a0015004020030303020031061000c0c403035086131080111350303031111602e07014807030b0354086006441032404009034034060b1014040b0051003686c50071402c0861515000c4000d51145d075006517010740341d0f820100903d07207a000c00d4580661240150070b007420200024112040300807088131003030840cac40b1b108101c07002e8016580e000c1c40000d203c900b450410780b60a566408 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 449264469 1250 449263219 449263223
    0x6030115061202090603040602030a05010e040308040b0612150a0509010b01050f090f10030e0d080114010f12060906170d121a04050106050a020c0a152d0203040f050913 74
    0x8028110103042c800780c040303c499007805000c083c2c0d203040a180c600c000394002c07076034040718501c1d1200100f0091f881c000030314016509aa80c4254070f0b20f071600d50290184001c1c10071030788a019910a240c00a02c20310504012542c400c2a444161801d00b03107c0050b5a801002090141d15080d8400096070b000310549040710301e001840b54031248480c0106a80070000e10344290701080003240c401190768540c00c604010990002628044a103005040d142103400780a81e00f10080070070240d11407540b003003270001c1e40c1c8282458031403c0310f02c1c0c002c0d21000b103035241c0d0842070302c6c0c0b81c0310007040c40b0035409c090102c0d0022070304000601010a0100c0000d00c0e40c0c9048080c080301c661581245050000d02015503009224000c004025950b9200c07001381040d13101c1e982d4140540603100400354186441030000b01103980000660640ca6490002118100c1140072040603503041004035100741160f203c001038a0340c046800a5568034144201d44401100742e0784150700c2544580e0030000e00010821760414041e03 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 449265719 1250 449264469 449264477
    0x306060706020309011d0a06060f05090402040c1701060f020f0f0c09040f12030b09130b06010e0d0b01030311060901020c1216050a061514360f010603050603011506 72
    0x43c44d0b8400c81c50150402c2210316403105e040407202d00d502500460541c0c0064841c4800b0000203903910458141c443e40d030301c541d40c0c1c000015400075000d410030343c010820081c56807800001b81400303010340c500d4074003080e0000000210724041c80990300380c040141000b030444000060210050700d5a91503607990081502600488a11000c1420010234a080b405000e40c1725803041449602101c1c01401003e940c240325108002d00740100f820800c0c4201541809600300c0007020165a8220041d01c005c0c0c80411002d0700316000b4514100820a54180c081c003942c03103551000c400c0d0305070480c040d1404801402e40b07185648104160001d26030002a40074480c001e01c1c3d00507841c1c52503491410000043c4440c040c20b1070147d82e80c981c1c20442984c2c00080001c01c03c15a02d041c4a40340c0e00c1e10020407580b4201c10360402c2248a0844010600102d056040d03c00e4140304e1011030b4505030258001c140a0781c19002111240005006d100c0c0c00d40110303030340041d05034001c02107406904610480c0451502c2104280 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 449266969 1250 449265719 449265721
    0x3030e13060801140106030b0102120a0c0212030403021801210314032e050a0e06120a050105060f010f1b080f13140a062307020d05030702010e010503060607060203 72
    0xa44405801440248100c030080020640e100e960714081c166140d6410400105140042842d6010307204442c80a0010380c000c202420920b00600c46d182d02c07618038134050201c421006801695480c100740c0c8103070742d9000696150352851050144141c034503d84180b03242c69000c0148000245002010060480700d103031281c0039011410166a0000b0100305003856040c000104210401c0d91341040a00d41c00911004094640340c9100d8860721465015050b48149090302c2040007511a0600c960426401000c0368801601500c0c2186040c0e4100e004444594542c4104001ca1070501313044038000d80f0a013803000954440400082141070201a008207040c03100007900148002c02042d100e051511001c0a07070780d03521036420a04d0a00080c814070006520220300d05d401d6003010141c01c0704650f205d482c0c8040d5500c1007056000c40341e00714524074007070720380610640c405665084400504a8041c402956641c40b490000411a1098000076814810208280040b035201c1108441c441350b0881c00068503 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 449268219 1250 449266969 449266997
    0x1060311030a0f381009060e130c02060f060603010e062709070302090c040b0f28091404061404090f05060705040e151309061d0106180b0603010303 65
    0xc140702c0f0200d0040d6a1403c001c03a03280c41885413201c295518002c0060641d80d41c4008202840c1080701a403c00102c4803407081010500540d0f2450629800400d101e60284c42406d0450842e82000c0121006038000014032110280c05051140c0000341600c90314950360410307261344042c09002c2c0c40c107030107102e01141142d04202d03640640c0000900c5580300d09660f04080e112166140c0c007500060703114409088c0415880ea0307a660890b0221400f41c1e00d81e40c105408410103030155041b40c00b0b50185040d003880002c84450560072000190026074990b4011a401d003007040c0c508900044225024504c0c144d400d00039002d178800000e5a0480c21171b00820419614509401015080c1200414a10449041c400c0540e00301000d001518455000b46040307a841d650300f0300e80c01409495007504001c120f8011880341726181c00654800d40200c03000709000346000c80c1c069100d15042e800d03607401d075036880b400d010b052030b0a9a1642006600030045c0109000403000850f280b006103c0101030144000d800b0070 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 449269469 1250 449268219 449268221
    0x6030a0207060501060e010e01030902090606070302071e15210b040605060f0318072d050d1101030b030106030803181e0d231c0209030a0c0e01060311030a0f 69
    0x794680e84203070180882c0d65a0700c00548419901829140030130b900d0b141c0e6444e2548a8490012074a8008006411302e0320760320107100442d0b1042905400318001c6c46000b05d82c94513000c61a402e00400c0000300304215290045100d0707a41c500d1007010041200b80112030001e0b542d01d800c5410403004807003001900351503050024000f070030f147e032189400030302c0070038034140c0f010070070380036500c140c01c185000b1040801d9003031829120141c5004103901411590421420f914503460070020310012801c4180354691a1030010f11028104103080f201c0c64001420098070b0b50303044c0107402c2d1407501a0000d00c056805e6544040b46804000c00d190000041100390f070300800c100700020302146403401d2080240303402c0414400c0c0c44100203c44103000c903408a040c00055500c103213882030760402860090b42400aa25501ca034030548103c03400c0543d40d0240b01c40d01036980d060043c0164144500da04505181c50922104500740701680090241494640c803491040c203084100d81c6e1000e04d0050004902c079410181c40 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 449270719 1250 449269469 449269477
    0x507022a0a081b040e0a03050a021e0606190f06110a08030106090e1b0f0c010902130c1b02060a180f03150b090c0d090c091506181406030a02 62
    0x180d01c030a18020008030301d03901042120301c0c0852414002c04514124080c041914080b02100075294021802c120200f8442d00140034031003040e02c15241d0151401c4c0040d03002a078950007070030260300544240710451425403244482000e0000600e942c503860605440c05500040c072506050000403405500d80220600000403080d92000f440c07034587d611131750001c1c4102e01c0390003074a0000c1000404603072042c5c1d4001e004020041c0400b00d4134500080362420144a4026440070700030707076483c0c3ea00c801c0117958050514203980c0040000061401b180c1600501040380f03522500c0301c4003082c04081004d619820103c802c0c02000313080081e6000b018054820340e07292503900030002c400d44100040300300401c00d00500e50038680d00c2820302000d074415041142c880d8080e00c500c612008100501c2e0080c0565030000c0002c2c82c003c4243c090042e0303844ca890341c15030f1200302021a260610f0281401110b811040354007003c0d0340003504901d0305007004040d1035000802240b43c2d03c03401021000980c41c28482e0129 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 449271969 1250 449270719 449270803
    0x1209010306031202010504150207020d021302070501050414070e1614040803030916081506040b031207080901090f0308070320190c0b0c030301030b090307140f0c04050702 75
    0x241e40e010b0190350f4024000c2000355422207407200034000d1190150703158000e88900e2a0024000011240f055003004491458104520290343d001c1c8030300b001040d020b1081c540b1941c007038030003103812000d5100b806d03042800942020032901c0404040c00814001e0301d511021a058a062109040914070801203190081c1d0740b08110f503102c008100461002d0124041c01031181c00c2d03c3c4882d066480b482107507220b40c0c40004841c0d448100a0000d20940ba0a40124081ca00b000d0291340740400e1401c8a03029541c041d540230340c0d8031040041d95044c6541d0040248000304244101600e007a82980d032003104610915802408001c1400a407140b552442e02c0ca60b00c4668565049401c0052414440c60030410742100554120f1004c0c42e0000e4000d61a10469066410303603006549140c2c00d558543d0207802d000382900c12a880140403440000d10340c100c2401c24200c011004103007010703001c01402e26000496000354056030602c0c2c1400b0020b0340000e117154034085446401920411184050544c1e144c0100075 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 449273219 1250 449271969 449271983
    0x9020a0609061d010f211d070503010908120601140408150c09030d03020c101112010618150c05011109030f03070b070c030504030c14040b01030b03120901030603 71
    0x26615080030307030395088803038a441e10980ca4840b009903039400c40100b10480d0100c2d02091240a000c0e01c6101d584a102c0d080404104078050102410812112210b0500c41d000d02d039803081c009501002c00c101801081c0480090194541c150f58110f2030740a018204804554841c0c04940300340e0148030f0700e81094030011800781d1039030342e82c1d08101e540d04c4440c0414900c0301204000703e0340043c80081161036140029005141c2904600c204074005d40c85681c8543c11b41c002d89040b158102d4042c081c40c0c0704a608140c0c1076890b901c1e81c02080001d440180d000c8000e0011202e440d9194101103036036070040700c6c00152100c40362000d051003940c040006001c002c156510b0404655245044d94001d010704040c280c08490013010f0800390715a59101e002c2c0080c1c41c1e007003010005852140b240c40e09460b800e129140c59818142c0d00e036215801e141c500e80003182c440c04000c1843c80141024406c0d510382d80024a014041c05450b8000b2984850040040d40d00d605800100681540d002e030700040d00075640102 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 449274469 1250 449273219 449273239
    0x141e0f040306091505070305010503030405060f0d090609020319020a030803070c050a0b011409240112020d09022e050307031d0c090c0c07060810031a060405010f06080604020307030902 81
    0x544051442a01013a1100041c50075011074400c61081c0702d02c606a48003d0000e40c47e05080c001040040d03044400e0a030a40c0f0800c00c040007070703020036004011f0f03201e102c0c01002c1900300d581c1c410141040c1c440f1201d02c080358410340d03650f00981c2ea08951141203d41007072000740da0b9150394200b00c2e0b0010030382c1e0000d0920f1080c1c25041080098010420f0304032078080d0140125441c0c403804005041c0020b4845d003605082408841c03080708000c0301641003801050505c0b4100e0500921110282e03001050743c04c84d2656101c1c581800d500b060340020940384911420042d6001480d51007000c40240301e00010100000800003944450099100f4444540060b150481e44102c800d081642e074026020b006004031501404169010110025601502d5000002c1c150041c20485e0442d00a00014065600c45405d44000404648900301c10b81e4079171301080d00c1070030f145404410b0100b40c4406030b000300d61204004d0300402401d0350040d125030f04048221000350f62620366000403005000d50a80196102407d00 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 449275719 1250 449274469 449274473
    0x3080f0c1c241a1c1a03060723160b060f04060306060f0501110304090e07050d0303020a03060609120b06040b03061003050f07061e020a060e01020703141e0f04030609 73
    0x2c2000c01103030314405006211001c4805000f055020302401180302c0d00040f011490f4103082034000041000a1030001c0030000104c00001c0e142c400280c41000124641481c0c000e003454180d65040c40b00216001c1c0c65140140104065100344070040c0041c104a2118020a0381c65a600d9064411060010002c0c84050b0703c0703040c080d0050146100b4041d4002c3c0760000011075500805640f1740180903d400395003814a0800214080d1040800414150141c3e08020038140c0d54810040d06150007644e0050b20340789034880142c100e4142d0b4005006001c10803000300b006991084400040a40c0306a51912036200c4c0c40200d8040c02e40320424580c54000c3c401049802c1000400c400b085900800c00c80c1c0d816110814419115101401801d00084642901080096548541e00351442ca10b2040360100c009075100d050490b007092042000da6500010b84070145a1301051600c038011036001c03203e280101608241030f44120809000e24501000308140d440071190f0016103000b5504418203005d850b10754 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 449276969 1250 449275719 449275781
    0x201111b01050105150403120908010c0804020f0904080406110304090603240b0f06070f0b040524100909080c03130603060b0901020c01110c0d08030403080f0c1c 71
    0x5403600c0c2140d03203003070700001e614a40802c10640010794040f82500c1c0c5821510b590400c201541007010600c904140000f5040318244101440b1101a549007211420144100b012611451400510500c00d801c14040401c034083d08031403c880e81410a205602c1c498144a810f60003075a1103410740d1454038000206100070808042030a01c104e610082220b00400e034002c0c100d07100105a1034200b03010040070100b03420000024140180104486064861141d5a040c180b420440c0c0c02c0358075800c031428008020744142c1d0701030b030319405000c5c1420f407501c0c10f20314a0464020303600c1140005501c540d681030034006800115004188190240e980d9410300c2101801c2100c003a2181c0b60000f490100b00052024011007603801d004016400350000c1143e11004590302c04546a8228060203440e6126202c0d9680d10114500c981c0b0400710980c0344e00d003508002d015004000c00c4e0740c000c64031400c104010329240b80b007200d0900107050741c0f01401031081c0880f08014442200e61000d40d8141e000030390080c500c4 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 449278219 1250 449276969 449277007
    0x90804081506060a090b07020d0b1e090c0d0209150d0b010503070b09030607080a182a03020108011701110a36030204110f21010f1a0307020111 63
    0x1c040359407555500ca00c070500030144264041200010b001e41030900c001d00d80c2800801c00340e80000d040503a5030000307441e40b00429501391180e00c083d83c80c04404404d03100d41c21180550140e50720001c1e00400300d0000200c0d034000c0030f02d08000d00c601c1072100040da07464403240c2c00504041001d0481c4401c0155071404452180d028010907200344201c0a0000d40989020100c03002894094080c01007503c6100003503400101c09031910052940b01c0e003004008813504506940c8607402505a590000c0c3c00489204545e018500b58085881c0d42c07a5003400540d811070b0000d070454410ec05c2020032401c142c0061030041c41184a807130a4180700164400300942c0c0b061250804c03081d50620341c1c107403d4000d07290300740e40c2c4c0c0c8590321142d4041c4d400310100050b01e042c0e44004281d00700b1109251a01c1c4d0050461000c1e42c4c048500c401050f5011805a1510b03480b41c0307045800b41c90f41e4800c0d007403c07504002c0082e13540c01e840d80c0c1400d00701d00300000090029100390003d002c1c00f08101442a00c40000400c1c52a21140c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 449279469 1250 449278219 449278243
    0xf0201150b07060513020613052106040b150306071e0201090b0106050a050705030d0204170105010803070807031e0801080d170103021203070803131106071101080a09080408 76
    0x82001000c204040c11040032400325070340d51106601d0940c150380c8280150400528400c0c5100b000c992040168a07034800034804130a4840007130000c20b08200c10082103c804064015140108a41504000d00005185a08a50800d100c409a56079007402d10504409800c000c030b405000d40700911240c29041103607240c01700301049000c01001c08001b0100c0c2242c038642c1000d003906e6089001008014000c03002410301d10060300d000f501c5e0032100d4440d03620f5039022190004000b90300080410000d100500070840301e41c01c840080c442c5500d001d0a407aa00c1c00b8080d0003401e803150024042c8100340c010b41044815440700d4500e079800001d00c002c041d000d820240f0500381c440c0a95042c5004551140c200402d00201e10100044642d00319000c0c00034000510720440e2080c801000600c020880c103001941c032406011040b881164960f18100c1024803099017010700885041c0b00c82e02c00511810310442c074030700007032915440c65138034509058054010820041c1c0f030100c0002c0e000c1442c5202056015900e9 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 449280575 1106 449279469 449279471
    0x5102304050c0a0807050a2f0616020d0201060503122a0322050303090909010605180406050112031b03020102040b030c180406210c03080a0f0201 64
    0x1d002981c0702d2111510200e018002d0f0fa92000c03045921a90b44c0c034049042400510380a460032510340000c40d11360b50284034000103c400800c40401b40f0003010f044034101c0c20502000e014507000f03900b012005015071511801c4450050140508070b44000e002400f0140e611000c0d0ac0281e0010403c0c0144c4490700318400f00001c040e280e0a80e036002c1c4060140d40d40c0e402401d00001d20464511600c0381d04060310b801004030355808001d8911104040e10b0b03200441c0d480001031801000541c03c45603018035a803000a11500740581e840d80718074400c2e8800c00260340c841010709010014440d008000442c07c6022040480e07080842042c4184240005810161076803055a4942c000301d403402007614002c03490701848521368070420b8800b20140c2d001c2251a003402400c0042242019003203441d682c148900718100101009100011500044265222207002d2002041c0780380e0290400015 = true := by decide +kernel

theorem cover : BRFrame.Cov 449100719 449280575 := by
  have h0 := BRFrame.cov_init 449100719
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449100719 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 449100719 ≤ n) (h2 : n < 449280575) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
