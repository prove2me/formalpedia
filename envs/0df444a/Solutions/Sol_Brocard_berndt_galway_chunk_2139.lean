-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2139
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:45:45.35215+00:00
-- url     : https://prove2.me/submissions/0d989e3e-7e66-4a9a-854f-18f700ab4471

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 384532374 ≤ n < 384712230 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 384533624 1250 384532374 384532387
    0xc080609100c0e060d0603030e01110307021504180c0306090213050904021810060306301112010e0f070312051c020c031c05070c17091804030f0e0901030305 69
    0x142c54100c20303c00c00e44e62000b0301042c890f02216803036001d4001c0368040d65405c6d040e813034400c00543d155800000361401c42c0d00100169005402d081d06101e041c6c030390201d070072444c040d030740d40c100b1441141e19a182c01c0c001e0303140c1e08234a401c1a07040c06064090300c0c1c0c0131401c5180c19803081b540e00706180b644c030455005449810014043d0b41d12808207000900080000c081b00b440e208641105070750742030080f03070003081c40d1410200d00d001d84410714100030fa12241d10242d40007010240503120f40441d98088480c1c1d080500c10b8411500c55240d03010480c110305c030002c201d102d800c44207542008098011b5002d168049403040000c01c01e9040580d14541e10b5007001d640da554150304880300c04008400800c2103d00004418040040000080070104800402c03034000464a8201030103540c03040c0c50040c00102540c1242000c6441e0345085418bc40394024820b01c0c040c070b503001007400f842084d258a0040c030000406c0005164008104808699a5141030404041a50b002072407201c4d046c0009410018003080781d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 384534874 1250 384533624 384533627
    0x212131a0d0504080703111507080a1b050c070e04020d03050c0a02031603150e070b0c1c210b060a0c02040239120703030b03070905040c030c080609100c 67
    0x84444501e1421000e00c003518160901130441c0e402088100c002808080d0360b00b201100109100302c1041c005400e400c03041e01c800d84129840c45010f0143c1e820542d40300f42d920131143c0402c031400400725070764907090707240d40c02010b54505081107540b02802000100c020040140e44001c14940020384c9414481c1d00c604005c1f88051038002e50000c02500340c45411000c024556000b109002100c5c4940b00207400c2d81a0140d03801c0c2518500e00070080d0b00d61000300300348121030f0748002400000148408031090000d045542044e808440c01003080807621100c0c0d486c1078002050039484509000e07120900030001d800001c6032452240e02d25034410465000d004108568894045444000711242e8a105440c0b05030288a140a820110500440c0c0421840c0d0040140850107100319140e40d0001c0381840a192026800342040c0080d9036814069018007292808081c440e0f94080c1e8043caa8100c009421171a0203d03c554054014920780c0e4095810000b1880d000680d510b440c3d003484501144449280c0780 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 384536124 1250 384534874 384534877
    0x30a14070b090a1727030a0b04060b0405060d080f030613050403021f1a060703050708040806060a06050403051b040b27010f150c0309090f020702010212131a 69
    0x40081c03a8564503818481c5001e400103110402e240112a61001212492085101c1d072043d22005c0c0e00a42001c03190102c0304501c10304c0091000303006416502010140e589101290204450840f0321a030342ea444019036041074440c040e80300038191ba419980014035140c107240f83c09003800070440300400100040c1c0391780b41c840a011803100307042414001f5041074500a034a954008e001051280d108000659a958990291030741d00ca80e00002100040800300902a0613401540140c2c00c0c401300b00f111500245241000b44000c104100141005003440070800128020700c2d444202040014030007400401c00106a0102650054038000c1103c004400843c02400c02c084040782d00030080c00c009441046030382d40c0d581200079140c00c4012035a0700c80135420744005103402900700034262800902c905c41d00030030038851481d022342080d908a81d952a40358080d900205541c1c4002500454404119601000310b440c4d1014005802030400c800c3d4112040128030754400e82c00c10000070b2010541b0135801a0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 384537374 1250 384536124 384536137
    0x13080a020c0a08100f0b0604030b0405010e0d08012408061009090203130605010504050403140c0f06010609080f06060310020a03140a0e1002040b0703050703030e0a03031a030708030a14 81
    0x400042c00159500d0344070740c9402d01c500d103410425041103000e81c0c240c2101d200d0142c5004004200d14101415915282c0354128000d104581540d6542210321801c1410030802129101c2559403200b83d43c11300d01d01c224207211a0a514450b0745840026460440d040041a030b40440d05486840495100f1841110b506000d68040195a440081031295a4a01e0706880c24008c0c080c00c400d0000b642d03200240401c58800310780140000e00403c01d0f8000c680782d800010102c50f4104003c07075840000301f80c4484d0030300d042a401800410454002002001002e20084540e80546405042c50b0b04c3c100380800d403600d400702c11003007269074005a940d1a0b039000307130b00444000c00389490790480362901c8200000100000c05903101c03584151016180c08201900031a420358101000e11402d14006950944060700420000c50a050701c400c050488840108002d0103420301943d4085804020a21000c01c90040030020a01a40100500344080c01d4000221001c1c0d00c043d00c0d141c400f44260f14416141400b508 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 384538624 1250 384537374 384537379
    0x402011d0909030316021501030204150305070b090f01031a01211404052e05130602191e052719031b180b0102100e0106030606080613080a020c 63
    0x180a00141500010281d4411703000d4145000c80b01103000000c1c1c3c1e50b0800c5150075182407040d100103200504040d0401c3c408041c0b490203030880d42d0b40f00d9482c64284103464214091326400460306585030300c3c05011980948400f03080420000740b651441d5400706803e80300803810700040ca00040c0540010000007520070229102c104200c180c00c0341022288042600c043e1a1481614601c1075113010b403001035101c1c6041001c080058100780300100002d880b0040c000d80700e044100d49200c012941c039000810b6003080031104120800801c02d00070384075082d00800c00d00101121140f00b115503421104861040066070300b4048514124501003441e4103007600d14940110351910f03019600345001c440c1d2410703a8440c40d1107004400292140c1c036000545442030302d07452440040e032080780802603400b060b803003030741807040e42d801c10f20040740e9200340c441e01c005206460795070340010018003e40d031040308058250309002e41884d00b0914203000f4070768000d11014120850005100724404e008001c40c401c0760001 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 384539874 1250 384538624 384538639
    0xb090d110612010e01091e050408040e0f1b0c12090316060203040612140c091206070c02030709050601023a0c05010b0a05150706060b03040b25080402011d 68
    0x104200400b0203104005140c15034000224110300715005018640d2803200b07402c414401c40c0c1c11002c000d401c010f4804e40d0801000c000c0480c08980303101800c0d09c21058144003003040c4c10901c41c4020412091502e06401607024481419502808180120480444207010361140440400641050700c22019a0b0700300000b02d00003c4c01d0360700030001c4c0c01118007988820002268031910701040c2e42c4500008020809090000303004580c3c84400f515441102400700029460381403802c5180000c00e55900001c101040c102d0000c6140410504000d448481e40c01d11103400c000001175034800880d8510494640743d440010200b0046560f0703016654094000848004070401c00900807030303099a000d5495500b000400071690410080c14011200e02914800d0012220b070310121180d000020100d45454880f0400201003a41c0c0c400355000310f02a502125050400024180c0b0000803840c2000c86405500c4030106440c0d000321060350702c641c081c00c00340c02c00d6aa400e800347c001c004e210310381ca90140d030 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 384541124 1250 384539874 384539887
    0x50d03030b031605030d020105160c0503130b191b032706081005030105161119140607090b0f090a150c0c06050c0601090b0303071505060f06040b090d1106 68
    0x10f42c22541030855030203800f03885d000c0c107102c2c008a0070f9070b80844e0030f950b490003070030745da81b1b090361060340e0004c0c5940c080e40a8900340380340e83c014004501d44c15800300e20308400201e0800041d1048038005c5600c2c0c0c1c02c0342000a04003040d1000e52103401e850000103018030001e0440741450380c0380740c0f140c40c01516080380c4101c02c06454a44c0600301d55016264402207480480d40407515082c148529401141d21ba41050f03080b0b0400c01c01202d00030100140e5000c5030150b500000081440e4000000ba500d120742400010f14035914415031401c04024102c42c00c002d208901000040c800c48120345883e00a9415517030380d8800880460110300c000e80c40008100244a117109100d6404050810124401d03a0752189180c1c0d9044100d070305008a1089101c5034100f100100321502c51580504014100502030381e040000c01d4980e080c034804a1142401c5864032502085000d00d42548450304042003110020300f1b0500308036050145004101c3c08034001c1145c0c801e0101406540c1d0f00003142000000c040310313074406 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 384542374 1250 384541124 384541153
    0x5090a0308030703060b0708090d151805060901020301050109140402070b010303050c070f080c010c050727061203120c02100e0705010e0319020d030e090a0c2601050d03030b03 77
    0x900440f07881001038900340010448117014405c55a0540e08940305030b05100410741001884281040f00310385110225520040e1015203001d10340803240140451005c03d842c5081c9142008001055800e031a4410401130080c2da800c20000030668210540300710004031040089402481036000c050501e03203902c40000308165000c0010110100104166100d599403001600c0b010f00490050f00d10f1a002410386079120f52140c8030b10310b0303040c0c0079504442c2800e9903400142c007412910005030303000b54110160344400a885001d00c00040c000c02d131110110a0846e2402045240780343c4030408242d855200b82c0e03075040d10800400c034100814600405c1134040030070f00507603964102d200b10b81c0401d05e03540c5030b401280b030080b071030040f0030f41c01010b0342c401c1600760345c20000280a05c80b011014010481d0054155454881c00e040c032900d9100c000141e48180c0403406041203007400c507009070048150700540c50030900c104010b07044403016681c55001203518502074014000307030201c8603018401c0641500000 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 384543624 1250 384542374 384542377
    0x3010b0318010504020906060c160306140709031220061501030c020303011d06030a0b0901060f050d0309170f010e030415170705030a0905031b0610031e0305090a0308 73
    0x1d00070403048070301c140514490705003612811603002c0e6000840340000b030620305040004000c07007440c00c0280c840c0404002e400740403124494000780d032680e40e600707174081c0d00a040d07040c10b40c3c100c04141800141149590303140c401c40004000680c04001440000c59905103540610742074014083d000e60f0400d03c3c08503483c0e00070340b400c5016540020306040200e81800d0000c02241d0607076860099440140182a10001c0c0046024089a805214034500c042c0400d10103660103000702c4881d0004140ca03131612007011180895070300214801e009605010000035009080e807401c461410b44181507204480e40c0407070900c0c00341d158a103515401c0400400003038030080010002c0d200c90041c10100c00c01c2440303003296564404100030242d44440c00126070264004e1001c1c1d0760003d851040811400360a9030b0303a90854018084080b4031044016030502d40070030501c2030f2a4000c240c009051442461130f1035254122521101c84100222031a42c1d580a162040045405042d4050b1846074150b83c1c074a8140141d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 384544874 1250 384543624 384543631
    0x1210507081009020f1b03120c03010f360b03030c010f320a020412051509280c031b0807090b0604090203060f120d03050c030403020601030308190203010b03 69
    0x340b41007010100304a851442a600f001d0f1014034010b04160880d40760349000d142c8042d1100e00751100f80070300b50b81d850040d842c8500c5a80440400c5849526040b180c154849203a007068541001c0503d814074803100c2c08002132110484112014402401301c1101c40c02401440c210580500000907030348088101504606003c11010000700141300c40701c4a00c2e11a2585c126031038045103211500d41c0c886114117031413540c11000751000180380550b200720b190b981e03002d201c0046640b0340151112180c021f4211203d40d03480620315000d046031440031224500c00740d65881804080248910404040c40406e02000c0090342d0b0002d65031502920140b4840004421885030b20041d201d01d9a000c61039900b5805182e4070300d40c0180441d8100f50034815640301031b400003890035030450f620405801c07140e96481c0705502c0c0e40710000c010f0010300340808001411382d03000a00d900c1002108106010003c0c1d07001600341e0441e501880c1210003511b405e000e45089003069121041200c0c008000450102074002c0218007 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 384546124 1250 384544874 384544891
    0x50901140f090601050a05181314130816050a020d1a130c03060b0d0f152406050307020f0601030b190519020d02070602031009060f140121050708 64
    0x101c1c20703070034410015114800c50711140094401d00041841c18042e10240011100d000c04010301c09843c02c021580414107049010038282e00c840381c0481501d00c4001950708140e074080000706801950f100d941c0ba610801495646c4000c11002c007405000040c00844a0719900500e4281610550304081c1c000c002a200140d6485e4180b1010803029850844d1000031180d0103582d100744c451564555100800040f020075800010f2040c01000050017840003201e03045c800e6500383c044404500c6d01d00101c44000755208044a00c2014206001075960040c4003204c995180140c0c0e43d6440c44c2049041240b61a9070048611590001000300a010b0080d01c2c82181c1c0c1140d09410108440340c40f009540081e1095165080f4640e80c0c41c580c081c00d40c000f0901c41a40f9000035103455516901c4408a0380200c0d214900140818021b210840050090500818070a00da160b00303030342080f00300100381c080b64800030b05000780d980011040304458003007050405d1601408010a24003402c024054540840c0c490700b = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 384547374 1250 384546124 384546139
    0x50a030b060406360e060f07110a031409060403020607060c020c0d03121d0a06200702011209240b011e0212030c0c031603120c080f1005090114 63
    0x8410480c003044601d0048404c0e03100300390a40d4402c002007052100c0200b118a1600c8218480342c8036030400400d4020382041854040515140d00014406c1407401ca2100e440d07041511190003090340000040c1500d043c42250999819000e8002070131840f039035000a41200c000714045050040030b03402120f052855800395405c03d035086080010203454400c1c01404910078030240204076815501104402410300000261945405180c500e0074944c81c03411141241c40d00728084a40da56200310388485403101c2020760503c165603001030450341415030001403c035542d01e01c4e07000b400381c0d0b010a580e400118100c1d141c0c2c861a10740100c0040c0c13160030300e00c1e0b020480304e9004070b0030103165800d8650b80002c0d0307901404001405042c507200f10345c809400203203000750611205020040c140010241c02d04c3c072150340c5240c1d00c02d51030b0180400340c401c0485000b040ca0301d036940049980000c102903000901b121031030900c3da1240040e20300c1a45640002e0781000d6154000b285140e007100f01d82d42c1401040360080c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 384548624 1250 384547374 384547379
    0xd080d050105030604200f092d01030302030415030f0c03090302150f1611030301080c03070e0c2a06040303052e0b28090303030f020a020a02060c07050a030b060406 72
    0x580d1310842542d009001100080c44040c0c408070100d020210342000611041900088a000903140c00d4156103400c04007801a0218801c030020200150440166144401c01c56145840294903800340c1e201e505200103401e100000014030942c49540401055142000036210301d403801802003200000172000f5100d0810512a50700c4842c1c4030700c0c440e00005000d0030007580c80268681400d44002c510106220b0310035000e200412003440510f0281803460010041d0140c02c1c4200b500d000c10a0b0b2048415490300000c1c00210061242140e0402460303112414a01c03036100300a400c04c115a8140d03030010300402091104060781034000078014030004206074200b010108000301207540e10405e404c90510003510800c5140c000c0405000c03182c4d0034141c08151203000c940c11040002074441c40d68009640c44006004054051143d0700c0380110501c0700b1810000c01032401303503807440b0800c00a481440c01060f400d10100701001410040c040240142221660707038980316040400540c1d41900c110b040c903001 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 384549874 1250 384548624 384548629
    0x31801090c05010e031515090c0703080403030504020d0f120906020316020d0609020604080a031d03210d0c080415090b07031802060a05071a090d050d02090d080d050105 74
    0x32082060781103014045098507000040d900c11044100680e0180949003003503032202803021040c1d114500b0902010210b41007101080726102004141c40c100c640f050202e240407c2e0b02c0000240d00030b45c541400101c98a50740000340c00c3c0c6034136000c02010002ca020100042201074800c036131000c4c4490311014410340c0ca0300d50981e00c1e40200c40001d1902910102c0325005031a140302110440d5004103c00194403207181c0214025500030340100360580d00201200c4101507010620300c50000070701001c040407030001c00000342c481d041d8480003007520041025503018000418100e8945108406040010b01c0c00ca000c0135281c0384003207a096941840780e01d11700b0110725260090220381940300010508035a01d0900c103500429800070010403420740e0183c0040140c891400520441c0707000d4482e41c0c1c40764014a04480f084644d401060000c5100301f0501114a00000d1901c135060903a09041d0345030741010242400901900d4552b6500c80140200f000c144100840200200208198184120383e220000e = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 384551124 1250 384549874 384549881
    0x618020405090d0210051b04030c0f0f032102010f020c01150515031605220302042315060c1c11070e060d08120a2403021807111002031801 61
    0x5450340980c00400840b000d05c030681d4000756000b10100c12210194060849002c5035070001e1300115a816600f4005010749400420442c0080c082d031919107541a08603078a01c4108000200740301d4041c0d0355a0320406281c2c1c000c3d0071040c00c09601c488210745600450b101c25028240400188000c032800c1400803c16003820260110303000301c0d0104c3c4510703545603800003062041045070b031a0104031060049803042c1580c0700000e1120482581c03d06142d6095004020854840e5207203010b51150750706008a13100c842242e1581d1000c4913550030740540c90b0130008201c40d88240c0348a07080c02e000b0343d9030f074400c04070300d60842d541c0324070140ea1801c0c880c10003890016552003a40c000c6501441310702000520601e4000000550f4600c41d0641e0350802041e005403000c9244103450300740440c1d0b12101443d9203110010000422094083c0103001c000e07295801056080e00d9170000b001c00401000c0002d03007114014040c4c02c2100450030f048910602880e1040360080d002681c5007007002c1e032060382d140c544100501 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 384552374 1250 384551124 384551143
    0x70e0f060315030a1b061b020a15050d020d0f1b0903020d020111030a030603060c03060b030411060f03011508010e0f0a05070e03070f0f0602011e09050109061802040509 74
    0xa211901e95150004480111a2032600c040e5142c4141c00800b40041c5035244000c0036000300d04010b52901c0e0401402401251031001102034001c091107425003d60b960940c003c040350024540c40700715184006048419102e0003110020650000404001c80d0819500c01e0f10041d04200040043c40280743d0450449040e5489520002c1c0d40080e027400035180c460341003a003903403050400c1543c40801c00c2005042d0341061800b0780220380d49210030801d0068a029421454145107001c00072141050701154440c00080c01c040d2080c0200400042587c4500c3d04803611503401261158580da0b40345050540e0030790f140c000e2000650a8800001e40381100c15172a409035062060381d00d0369036148800600148402060f1038200f005003e81c0d24204d440034403500010f0300c8218800e108060800849030300c1e0000560044045a24280301000c2410400200500c00003c240000c03400d003840e4180503014041c0640301401e60f40c503280701000000b51b4200c0580100d072094600744072903035072250041d4640c4e040c030 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 384553624 1250 384552374 384552379
    0x1b07031b030209150409060f0b1002010608070b0c0c0d0506011404020315010c151b080912030426030a1d060705160c0f09020408070b070201020c10170f070e0f 70
    0x1c03c0420403624140c07030103408510000c0c000090701300c01d90b1948001e481d201d80d4100c04803a51401015114103003084881c002c0201e6000901c6160310b4080c04a942c0c0440c0c1c40381c000c4166000c14480d1076240c041c006080e0403900241135210014142c20301356124842840744984009480302c058003642450b0094a116041c2d5880b60300034804c4035001507941009440d400c49840107010341e542981c0c021031050030804d040101d400d0341c0c03240c85450301405030b00b00903211960b294401d40b004118507507003100716640194481c810485c0d10143c01c0880199078040c008408016101000b04038100c05d841d80724580b1955141c0e81003520041005850391250010355902d000a101006004080204450b00c4040325100741103204005e59501442a80450540c004402030b0383c00080c00c1224001c10070201000c0d09140c3c82c02464602154000303540c502c0b03001da80d540034110020594501900480c0c0760700d580c41100105220034176120300445484041100c0706400305101c40002d46045c00c001078140c440b00000b = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 384554874 1250 384553624 384553639
    0xf2a04051519050910181509080f0610120c03021c0b04050102070501230a05070302092206081f0203090c120601062a0303111b07031b0302 61
    0x1000240070124090300104595a5002c000420090801884440c246001035580940300c40c0b4110030000f00c1810990004200280760701c1c074a14081883c0607890480f041c0340d601000100350f0013801e490701d04d040c2d404010746001d0340080040020012510500c14040c542003078100c951280c0008040850441c00079110b0b1b800001e042c001801d0000005080c000c0b1070500354605495580e1f850001c0400320b0b4112a01d940205030402000340034014007a94101030b02001c203204090030302134112044010402604280c4400c0071a4800b80070390304440e003818014101d587d240800b052280101242d071842c004c141031a18900280104001c180c61862103000c4286405d1182c0450075a0b01942026081e07031118040c01507044155038440045500203000b1a010300070540c07400e4000340807030042c0560b038081003001418101a0f0301c440780012050380e9050900045c00000d060b10b2048900a1000c010150b034451703021545400000038230003003224440c4103441e00c404c50100110170f20a401d4130009400219 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 384556124 1250 384554874 384554879
    0x315030302010507170121110418060e010b06030c03040204201317030d020c10060e09060618040618150e0111180d030315031a0603011506030c020708060f2a04 70
    0x187c00301c0442095014042020f013201000000800f11800c0307025811502a4807200841040024041c0001c80140103000700514034550010030550710000380181050100040080c0c1150b5850307104000c008015501c00e03031001c03c2c0300c0241816070301052880241210f02c001c00a00342c1130b030580307018910b503012018501f45a4001d034a103020b07401c031100c8412280985100c40e2100e80c2a840355030010010015001450b0030034113003203400d045014043c94019000c03881401f481c3d0140903806500282e0006000511403480e448400a80c4807980c80140030501d002c9194821400d250012000e506103100200900080302e10030418511034210305130204009031414112600e07010807240c140c28040e090210340c404444060040c21122900704603400d01c001101c00c850b003070107654280d030b2120041d0700820040110303458881d009012031140c40d0030103444070301d5005e24030720a10038400244640e4044460a090900b4590040340040329020518141495081d1050386051001402e1004e00c1c1e0409281c00d0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 384557374 1250 384556124 384556169
    0xa060608131721090703030908150103230106080606101d09071209030c0b0a051b090406090504050c09090a08190c08070b09010b04060b030f040303150303020105071701 74
    0x1c0000d4400d2020943d44207040910701c08001c2098499100c0c50050300809013540f43c0941601c07003d4000b91400c0d800000500c40071041410b103541980d030000200d1082c2c24030180701c2d2010340070402c500a02c40d402e001000070261000640030f8024101103a07414106a01d510301180d56070f100001c0d88160f03114560106071281000403a0704d4001a0521706460716401d05a502415184017040483c00070354050182420300221036401500610300801c2885941410302c040c51000c150f5210301c0550320b100086100c1c0325550b80c1e11a6004007203000b000d01040c640350400640341c101d032412540c0200c111800007a2500804140c1c413101c2e5500015807410244098801c0300d101c200550501c0c2032100070319054020035a1031015050841c07241c8070f009102d00c2d00b0354009003524155a00360340600d043c40000d100020703044c0203682e0b10401ca64001d01c5c142d0745e1402d044014007000d100403c010784243d0800b006042e41034102922600c40d40d00d92a80a40d0001680c42070741030300340300d10160340c0040202044541c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 384558624 1250 384557374 384557377
    0xe030c01021c0507051b0103060b03090a02011103270f12100b0a050d050303090115051c020402090d0503030403080f070e04050402280807050d030503060120060a0606081317 76
    0x202c02c0c6080303402c115490303490514003218a40720070034042a60345400000c0d0b03418081e0001520990b0a090f01307604242001c0d03a038403602144024107203e0b0b407140710b400c4600d0800556012208000c0c40d03000341d51042017001a20a401e01c055401508005825441400c0c6071a082c91500c3c22030f8010440c0d05515404080100320341099a81e101d40a0180003c2540c0e54502e610440c9010300302559490034245075440c2107a04141c0402e50a4030380000400c030f0360b950007110308082040c03645006801841440003600a10400d6425540030b105a0003510a0003000400b45101f244252120911a2071b000c0f0500c4915a04507441000900a00c5003090b2504060304100d0308184080d0080c0440c40f89200c00701800845450110003000c1e044c50100118241008148020142030b0350070b4980d11000d4900801c6d6101c01080d00c0d06002032101c14103030f5000c081400c90000e5290406a4805003024072042015010502c6640c001907440000326001c0c0c00c80740c119070f0340c056100c800c13481c18452400410302d05 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 384559874 1250 384558624 384558673
    0x210c0f0f0c19030b0a0b030d0804081e0d150302181302150c011a0109050117041713090c032417190b07080c04140f0f1e010e030c0102 59
    0x40c0c8240700300020004940304500360103941704c480c000c14000e42040c18580303012107a400351810050500203200120714910110380400ca94008400c2080449440c0c0c890240b00368a810005c881c90030f510070030510703441e00305101528421550307504001255a020410440191075440f1040303214589400146801c4070a800c90940300c5181d5428900300c01070709821102804403000c00c0000041e100b0702035680c0310445a001d81400d00b041220341004501080607001c00610080948009400d1595000000d0f4141c0e8081c00b980c0c80c180f00e090b03031620b5041d4040c02c4070400780d6002ca41444082c1d0005003000b07003007260142ca40e1101443d101c0c5042c5030700034031103020103200321b0034040c5000a414405201d080c0202c02e80c016003811b8841d082c5032a0082101000401a0303080900c02d02003402680001c2c103c41c001c4117021503207203d5010305003001640c0800384445265003c460320100d1101108050004105841e00342c803103445044440092644642605480e5401a04460020340700c0d5000d450340d607800d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 384561124 1250 384559874 384559909
    0x2c150c03010819032a1b030305030402060306031207050307060f0903020d0e01030f0f050105030c031c0e19030b0a050a180308150301090308010929010f02210c0f0f0c 73
    0x116460b171131032007002079601d6600084c80191501142402c0c0701020403032080f144464040401031702c0ca5610024010300000d08000d2054400002203805590200080d109900440c1c0700d5a98803100c514101e5a0395000b03142c100c0d80181485654245561035101e01a90290160050110500744520440e022805a00760707134103241c0c0d21010302da40040700f40304140c00c1c450080f40004040d410401014904000c880010f8400c0d40a070f400d00d000f00c0343e41c0c010000350a82c10306080031302c582000700040d1800044200070721880c149030000018000c9a10038240280b120031420811600c1e640b6821080e100d001401c414110341304a2100b00191085843c1e65106500700003603400304488800107400d449910400741e000842510040c45a403025215100e9411800001302a180d20f1400040c10240c0e0951140c6050208800c054040b01d03000f03004030b42c15040380e00c0c134032200400801d8021f50700e030300310616000d050b2080d110301040601000030000e1400c0d060f0001030141c854160300300050030305000b19400 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 384562374 1250 384561124 384561137
    0x15120210020f1e1b0a150903051c030507020a02061b120d020306090c04050d0818040e07060e01210903021c171302010903062c150c0301081903 63
    0x5204040901c8030049070100240083c40106416000b1403620746045241140340c4c05001c4910625502d540e03002e01100c4030b00d240c040318090100c20541d0800c0d8240d001030294090118840c480c400101003105150045480070001d070346858600326600c000c024070094205108000008040c0e00b00c07074196003071603c40001c5585082404440b21110780017000d07150071241e00803003440314a117003244038a82d101800c8014241040e00e004002450310706421005800700ca4006482d0000c03286840c0550100f8402034000c1c4060036154841c0da0b0b890341d281c40703a0300c0056800000505558840c003e80c0046a02c2010514034096249555200600e01c003e011015440340d00341c03a03480500302c540301130503050b16038a418a60110f004030060544000602c55400b59035045400301c0141c1c1c10a8001d01600d402100c0042e950603490411402204c60850350200c442614686400b506c0d00010103012112142d46810032586600382c07040c0183c0028050443ca940100c15140425807041c810030b40240c4c000d14085 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 384563624 1250 384562374 384562393
    0xe130c180230070509031216050c01050f16060204050613210201022a150409050604111614120403060f0b010f0e04020f03010b070c06021b011805100c03031512021002 73
    0x42a88d110001d6081105c581c03240c0700c82403140038002a840000282440c03031a28442c6015015644550013040d1010030340014124248940741d81a00d0207000050600303a51002443c840b2004403440307100312042c000c40452000ca031100090b01c1414442e6042c2c00400c1444100030440c60060454107070504501c055107124441ca9880c10301002100860311040d55840c0d00306000d00d025100300901e280e00031402c00300d50300340b0411540211503001158082d11101017045107854880c0f0140c80d00808a0340c41100310250030302000400510440f071003032004025440803000b5880c281c0303000a0b01c203030102c0d041d644071012450140511001c00540248018035181c40d0004411803504203030400c90420502056010800c03405104400103498203000518104031244030f00300c2c0140d54820054100505403071061030040c00071010300c015100041c900e0103030350301284000f03100302d01411007a00000e00707050920840d901009204c90035105103014000d81e000198090060110810324030204510402244 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 384564874 1250 384563624 384563653
    0xc11010627052a030103050c060f03150d051209090a0509070302120a0b0a0903110a11040f02130603090317040218060f030706020705190e130c18023007050903 70
    0xf0341da15940040591516541103040c032502d0020314410b15405520104080e002c0c00700050180c0c0e5016140c0650100164810408101c14583ca404014000c0c42407000381041003400c800540700055054440317a480d031341e44a81135010340d01c00b6500c602c40c07604010380610140c1808214508219007410455014141c50759070401d07146011203100c1005584c404209042507401141201400c8c0d04400510040038141c841c01c8500d00c00d040168890742e5a40c8200185803090340541e5100280f1500e42e003803203a80c035034010f0040c0c101860200c00088000c3c0302180800752801e150b601484c0c020700002e02c1c175001d101c15004915406807529920241015513810581c0d03081005a02801d0a58060070260b440c081c03d002000c072620481c03c13000002c0300741c24401442d120101650110b15030504030066840e03420408a4405550003007015804210310030640d910040d001880c00c00410603d02d42c03040f03050305950162140d8441d160761248516008602124420006055640b0000781030302d9881c0d400040 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 384566124 1250 384564874 384564931
    0x80f0111040f090b010504171b09060f0405060307120c0608012c130b1302040518061303051213021009080c01030f0612050a050c12060703020d0b040c1101062705 71
    0x1408da158840c9810000d816444aa0021061002e480c0403100e4107159000824900d2200c003014003884c1e561002407442d540c1045558000c0021403030103101d0020b1410100005001c42c0030f8000498140030000030703188011584000d58841424450003002580280c0e0840c0707840180c1404416486005080049011308040500441004000003c0608a4814802500c00c000c0600c0820314030170108002d420b03004160203070b22901100840030b81003568581682c16010b075041d607035410a040d0040200040a0700c2000f4681802111034005c10b5803442000c80713440010780580e00c0d0a80055260055070f50080c1c10181119a6003103002c660107846002c942017001c904603040c0d4041e80901c00b820207201c0103010001800400352040d034820460036280d03d580d054041c01d600101a40018402408680c95101d040008030042041c000c55200042c001e00d070348484035030303980d030340d480e081c0300140310f0800070042e15007030a0400320800c40502080c0c44500801c8018848451f490704026440d402032205e54 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 384567374 1250 384566124 384566159
    0x9020a030b0406060912080d0f0623040203011d18010c1814090711100c0801090e010b010f0507020d0b0a05190b01020a0f0609020307080f0111040f090b010504 70
    0xd60000307092056004000a50303000364801e00c28460000c1082c060308841c101d02d011210780280e25141e179144220107030340051015407074080486103400c0011440901a180a441d8502e0041c1003d503840c014000700030481c070082c85003d24200c001000344810204c0c1070100d0303030f2101a04854008220090f2181741c21340d0032416004002840041d0040d04a040240c000e5010384611b01c2d019101b845242c022841c0d000018012500b488025400648441c404000f0700310b110702d1700c03501800000141d22000c0e01c005400e000d0301001a0801c00e00002000052040070b4440c20f05948056080842107015a0b03154044141a6089a2142c0d01c401c00702d00c00c0d0a0309401071002140005c3c942c581300d0240c00c408010310404d198070034180141c0d802c85a900085e8140c0c0aa008000d011091340203250a4008160492000b901800340200004140d0400b08140340a0400a4024417003880103039194602d0f44528000c0c201c00c2829446c042c000301d14140d001c842c9110301070608030325080c2c592802004441240 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 384568624 1250 384567374 384567377
    0xc02100207090f02040b180a1503091101020321131403030a0c0906080604020d0209040905010506010e040c021e1e03070218010302010c060b01032301030512130b0306010909020a 78
    0x704200d90159032152030340d800c2001904608150400284682a01c41d0002c03080304603075040071100c40c503580e00c01c5000c001c040306031140e1881c07400174002402605010200f5582d040003006207a14035400403013100e0584482daa1607070b800002c612100050f01c1d40c00b42c0071030851020b1100200002d05101554038800da1f10400a40c0c80346007404480094071054030210040140c081e03030810a09421021058201804986c003503100d4074500e090034000c0c02000940c0d5401810032003007005008d0103500807401000203a803090990405642440281d65000701d03400b0060703000785520036407040e142c0403082044a00b8020303208140a07410b00c0342052104507601118580000079010110310704040c600d09030a5100054544540c59600040e040313005c0f540d8081c00a6444a44402480e0700c00d40c0244000e680010149082c2c04c0c100081c01c030600f000340000c072180e100e82c0b4069100702d0600001e0342e40d1080d0041c42c0074100c0c5c0c10140c0c40b40070f5800282c40f850600c00382c5600030415500600180186100c00d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 384569874 1250 384568624 384568633
    0x303090501021b070e090a081b0102070209070e011409060703031a0a03051614100c0303090c0f0e0a0506091303180b030f0a060b0904021804060801020a0207150206060d030c021002 79
    0xc08220680d408405031040c4180d80c82650740c00b00190b43e03003083da004800880849080260550103060290cc00d00000a51000c0c0550800041c0382d00504a0320252000382c1e5603041e101020f8048c40f61904c14100682e502040601c44500002e02c00d800407582c400700c10292261407201e42000c21480b007410381040702e0036004103108403a5a0704518441000385401440341b04c40782050004510b0340d205200c2180100700310b10f50503005143c040c1d006900002c1e0302004042807141d4421401c0d10100c0740d03000f40440007050102161042e04940511800f90788003c25107104d40d10341c800ba503040d191101c00210188944001841d61205000b50104014204841515501d14144016200c4d064006052402c03a42c0340c040180110408041592002e171029038005a9178501c0c582d5a604400b126000c8a030b001d0304002c4e021469280640240100c0c103a903800b1661201d48071451031402d1003c0ba80014016031000c000a0038030300d130002d0042e040c02c0c040d05020f450050140c02103100c00d250011a600542e20 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 384571124 1250 384569874 384569879
    0x4030c03050d030207020a210c09060602011415120f030406050901030b100e0603070905040603060204031e2105160c14010903150c030605130b09130b040303090501021b07 75
    0x18240b02c90700070315060f45401c51420950794002110414140240d01e80203040300301e15201540700c0c0304405503003070300644817001195450a06a025003114040c200040d420010307803820001342c04218a00464507982e044c592a0008800e1202c258880c0100c1141e511944403080410368050005102410341d0f83c2e40e031a501e03e03002002405a030760a03c680c1d40110803111541080030791066100d00c52000469034207690352103000003110021441d03006158818940900002004016402401220b1142041910143c1c1280484e14940c800daa8080c1c80c0d617071014007903c040b00b5907180180c01e1400e2800d20600300341030603260302c10030000d1071421140c219401c0001c4c0301400d0028211202c8100910786000f0306800c517075490710030100e00084440c8a81c0c603080c0980b880c1d8007a4001c1800307000c3c058120000c03600b01030155009458508416030154070a503000c21480c1e06c00d1101007110b03582003513140f800f44d120396408070010075807440150b440c1d550070300450b0a4040d40010710480c445c0c01e0401080050f0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 384572374 1250 384571124 384571133
    0x170a0207091104150e0f120c01030b0f1c0c0e10030f03020304030609060e010608031e0903070e0709061706060901080a240501030617071502100f050f060103152904030c03 75
    0x1ca46c0d0707a24460409241085407041c00061500d440360801e1802007086000200450300c643c441c0a801030740300c084030780c10b0403034945001002000c2e43c3c050810303c00b000d41e9603501c00d49280d00036540d13a43c03044805501440454100680c650b0442d00c280304a0380390542e079855810440d407855100700d0b5601e40715201c0c2e00c2117541c01d00418003e010074202852900100421a0783ca5207242120320803106004140100190b4081c0600740003044c146208a0040c504254000c0c03100e00716009100100b0a0940c010403940bd11564840c070855000d0200c070300d0404910015079014070001c06072a4074070b03192080c0c010041d148105402c40a030304086409034240c2002c001409891064000102c11424480308480f89c50001a03004111030081c4c5001e10b801100c10812410090945103849e00345042540c0b08841600c0c07640202e200f00c0c00f030700030070600c0d0311004011400e0b45c8c5030b480c85460b0006038210600284179480c542d410040002d0522500719109103807400d802d40c015500988060200d482c0c10070520 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 384573624 1250 384572374 384572389
    0xa0c0c0f0512040b1b060601081512010609020714010606020705090901020c0f1b03010209060409020306032a1807120230060103060b030c1e0705010f09170a0207091104150e 76
    0x16417000c01512040c80c0c2000000c00c00b010041c100403140c100e226400c10241c030750950400c030310100c460091290940b6845c100001e503004100c211021300c40c51294140d8001c043c89101d0544040b40d0242406502d00401c000d040340014100080c1950300300b1050007200c0b010860407802c0c1210380050302c10390107405100c040b551500141c8502076401000941010781d1032400701c03010f640100a00580b01d840b104c010900e8082e00c18030030500044030114075402c40ea6240b50400d032000045900c0100440124100350000300140c4008010451803182188c0c00001a005044c000d06c08036140066842503021341c1c007502102c1444d000728205070340180042c40d60f1600420015021860383d003865818040090141403090b00161035804a61690740342c80c04080388100c0f1020360300400203100c00800c2d411054004d010b004400c544481581850721030f000c584000343d580c281090340150074001d207044940000b9142020040c1d05a0600b00404101032412810000d03c2071ba02d50b80f41c020503e0308d0402d12600c07 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 384574874 1250 384573624 384573667
    0x4081c0510030308160c0212030c1006090615080f151003140109110f0304060b120c040501081f0b0f04090b0a0b041a040c1101060b0a080a0c0c0f0512040b 68
    0x803075a0910110321580c1003034611081c0d0f54141c88ca003104640c2c0d007505605602800a88903081d014840c1c2e040600300003904800d0940b489454100701d4a503480d0000383c00901c0b144429400f240a00300000c6107005c506186650004110b107180171210020000140b15042100d400b0000c2552400014074130a0312090040c05844410000c006541200c2c48102032409034a107a481a000008001020003c440d00909900d420141039140410b035040e0400c1d8843c0c0c1140000c1c0d008520f844000038560b0300008106507800100d10a1100015903008440060180c1c920308540140e9091105103883d112803141955550103003d4014850070008500000da070341c901c88031031180d4145402540e000d040445619190b0344100e0740003821207001e24040d41c8248502642200301c0d440c0240020741c1d4802c08006040145665685441980e01c00300c400e001c44115801131000540c2a200d131900140d52000410145800b910880e851141038006035041a0700a42007210103000200707440c0031002503802c4d0f0806 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 384576124 1250 384574874 384574891
    0x10120506100509090c1c020c0c190b0c120c070e0f071e02100c080105192301020f0a0515071e1b02090c030103110a030b04081c0510030308 61
    0x303540c6880700000d20070300807140420301c65221903011540d44c0c1e810004036611031651314003040350300d403080110304000e4100540c9501b06002e651200c1c07040345004010903034003408150030013a006007040712419842e0000083d90403144104001d01c0b54403240b80001c1c20040c406100100a564102810b58980c4079002c0d050f403c030803035410305100f03925401c2019444070300007121800003e684d031820124030b800d0b04001100004cc5c50300c0807060307000da400300b0114103884040e9050210380100442100b40704144c1d2240940c0106a00c8504040c81c00d510f2400c1e00a08051048881020003018680c0c104403e11400311401da02c01a20348155011045180b5404034183c1424402c280c641542c00f0001814034105d07104000d95824159078001811000c08003145c0c0107020024540780c0b80d0502c960550084c0815140c84076184905442e501e010198081601d5010041c20701d00d480390741d20900d0581050700c84039440070203c1d180318040030141c0324003489145040e40b0842034900c2c2d800c01038440031300a0320001 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 384577374 1250 384576124 384576139
    0x1060e041b1d0a090206030a050106030605011b080f09060f03010f1403030702040c09120302250b07030528020a060509030c0706050309012a020d0813030302070203010b10120506 78
    0x4141801001c000e40442015102c030421640c2c0da640c01d000800013880002c1d484100070041c09984030240d4852816500d1545080204589803001550f0024101e20460403612245500c0c01c00031f40d441d005080c20b0407299030680c5c1002c0948002440079045004154000d25011004118110080341030304001c00c99201d69002d1041c0d1040800e80304c0c402c03140c01078056621410709140841c49081000000c1042c2c1d103400110080524009450b15240c40344000704c40c2440c41c0614140115030610300031580f15001c12860036905540540d40c9400ca48060340c2c032840f04003a0203070f036450203105150981c5459405000e0421652070030318100c4e40040c19880c82d80d03109020140500000051307550644509040031038607a40d03110400ba01610501c09111010410846400f46a202030f138461f101984d002d4003502d0641100380c2044405800c00c03954540094040c0d0f05d02e00104e806540200b40160000d00003181c401c500c070000c100810400c041c40000030318900880040f035503a0b40f1480d90441d00845946 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 384578624 1250 384577374 384577379
    0x2010b15030411120105270601061e03060810020403061d07060309020303190e030f01110f0d180302031b03070b041b03050106120201090905060306011a0c01060e041b 73
    0x1451a01004000403c0e403041104000c0302c0da600c002d1000f40ba03214404c001c1c0308903d030820404000403e091104130f0017003400d1003d418881d02c0420124107176902c60b1340b0050600011400030640a60114540003455618607010800f000180400d9030b0300c002c20800540e4552a40ca41902150000b000007003000700e074520305454140b008110714040300d80c2840c1c0455950490300010303045200d28501c0d4180d8000714403100761107640040b150041e020048040c0c920040302510328600b69540031070b11a6100c001000049024080c24024282c02041c0942c00580d15040b000380f0440c0c807016520940143c0d10101c1d03803103112074800d02ca642c0c0b0742c0d041002840c01c0c426250307600918010013800007450b13046142d50038414202214403000003940c0203c0248440740d52101b440030f6070740c2060310584c0044ca00c844046450308042c0222801804064000c0c801a0320b009850134480a20310140507600c5030070807005814407030900a440141c800a00e0040e0241000e2820883c00700742410250715080214008 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 384579874 1250 384578624 384578659
    0x109150203090c0103270b0a110c0a1b0e070e10020a051c0c02060f030106020111032202040f020a050418090512030402060d11030a1d0d0c11060a0f02010b 68
    0x200240c043c0c1c20300f0041400c5140f510720355250566140340112001c1a81980418010741d800068001d40c0c1c9000c0810000a44020007a5030b0300c07070030f10f4101c9940d01903440000003d03500d1134903c1a5156040d132840301541c88507030007a12140c0070f6030714800061000030400040d00c4d01010501c6521a00c0c002000b0a55583eaa06500d80320b20f00c40940c4001001c40d20700d80000e000713010701141c095000344015512124170301444c0681e00207025140040d072a000241e65101d50040c110b9019000250480055600501710a9510814500200d03042074680b6060743c603a070120b001401c2c1603040c60b26441e445506040b554258450202c4003041020304008440c00401c4011030130b00ca046c0001c0c6a801e40c1c0365540e0010522034400e107800100c07800c0c0380c894144440031200d4041d500a1030100c0043c4200c0280c0543d15441018a410001d4541c01200215400314091004815070511030307a20368a2038098400042d400383c201d501840086014071400f807801541c28420900c0501c402c5135181712160780d100c1e0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 384581124 1250 384579874 384579883
    0xc0503091005090f010612050c01170a020c0a14070501110102040609170a021008011e0308090121140f0708010f06030b040e07090f060614181f02010915020309 70
    0x34001d0700903034860118600300010311100c0c085000c2d09001380a410b540703d0301c1c0441241000c006540c54002c1017544c10080d0b101e42540f6810030b44c0905039021a84032a100c2400139030101e480003840d849010b40110001e105c003900c2e202000003400c0a8098203203400c00240022104e0761040074103902c100002d00000d900007540d0000d4400740d4600004004e120342403a890042e000402035409076950380d6142800b94080d001074140c90b541c03009407040700491510b01c0091045400001c002030703030038000580740b940b0601c11a42242d500810011400c5074906110003240c50803100020140c081c6010010307000301c9152500e41003082c0e4580b0503515894480d0641454540c1d000b07a00401d81c0b25802102c40b03940e2034120003580350590b8195861540daa103802c01c01010070990b6400e6a41c1840c03800140307640200803054140b980280303034500c2d00c3c054070143c0d007001044096460340140d07800c8007805050b4000c01c07410a59503603500000750702200c50800403000c8401c100e11886850042013002100032021a = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 384582374 1250 384581124 384581143
    0x60a0c03090c030b0915010e060f0d020f0105161406160c0b01120206041509050a06050c1e070e010603150e04020d0f1106071b060c0803010308031521010c050309 71
    0x13440e502194032000c116030b05000b0441d082e28500d1301104004501c440041704550f00940e030031510070404005200c10302c108850004800395201e43e020b649a0560f50060008040008111401c00c040e4800e07641c99010f081031290007a081c540c4454204100c1c41d154055200d01620316003803030700c194001c994445122080501625081100c40200c040464a8180589018140941100702c1000f50382034000c251582a2103441e100701103c0c880003915a001e20129103e03150900050062558841c0242c060010715803014090b40c410b166000030500c150a1105010f02516600032810b5404440a8003604072560441c0c03030320601000600005a849800807410345502c801c4000119890307060010304440c542e800103801c18800943d1404000ca0240461003195550045031b10160321030304e044402c0307004240014002a0100010320229244101a55000c903030781c070b26814072034080004690160445501c1504c00d0070250302e10184d1002c00e0143c006200d999181460951410009542d030300e10381d10 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 384583624 1250 384582374 384582383
    0xc0d0c1b1401060b0408100f18050c131a0405100915060306050603070e09040c0e0712050c09090c0f0c0102040f05030f120d2a0807020f01051006080c0d0608060a0c03090c03 76
    0x507241d540c0fa1000d2904204040b504040040e00c1e10115824002c2e21440c9100105100c1d003803642d03415149800030711a146921400b44c4507801c1b044e00d0170003403b00815002e0140c00c86140017100002e80746c1c10703d00178100e81c8280307c0d01904155140c4840030f4140c502640003607200341c41c10700420085690000411160080c221542d00503502d40b400e041d030b6599616049680c090300210104031485402c042c185003090708100301040540d495881107000f5014903020154010191800b040341215141c000d03084056540b03140341c1c68000d4205410742240c0c05a40030b643c50f6060484108084d14080c010185001c01c0d0002500c150551081e8218081c8030fa2030214100d6965072112000071300711a840c00d203910311210700e45e00800014003070190503124210b802400500c40d40030440d520360010301845000d5000000c201011606000098490800c01007500b0030528051102000ca005503010b203c00812030341000e03043c1c0c1d041c072240e144291821201c0c44170a05080490f1200000c0004080d0021030307401 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 384584874 1250 384583624 384583631
    0xe0d0e0105070807110907110f010e060c070302070b040e01051f0f1b0609060527070501120f02030709030302070f03021e0102010b060304060e070e0c0d0c1b1401060b040810 76
    0x11842c00070544104100c2d6185c0200008040140023030b0014505840141e0890032506109003208500d800d80f042e09031004c025400240c0401c040d140e600010b44410341c4603006440100e87c4482c0508016002075209c07610041e00c1c41c2c010005810040000307003240c8460000c40d4900180b81030050700c65070b44080394800700117100c84603e101202d181c1003500a241d000c4000e00c42583c85c0d0403d500600010348640d007075200101d08032a511243c20b031000c503100ca25107000c1c04001c0e02e00300c01560101c003401d000c4040c00b03444d101c40303041c9000325100461165449441e038501003401c504000345844010b4000d0305440100301004d00c05a03036031186804044030042042c5912882900040f8003400c4049030701900f188000c0300340010400b02d50810400d6000c080c00700c40710165203007424032040320b00356445481c0d0703e0100200c142c5504030750000d07480c80e8003e04000414400302071390f510101d9a00d00040e0741d03901c4400e042c501a84028001c42c0e00030300044c044a0306050a050901e40c440481c11076090388c4555 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 384586124 1250 384584874 384584887
    0x6081503100c020a0218060d06090204090b0108031b0c01020703060b0d050109081b010606050702040c0201150828050d080901091b260327040501090e0d0e01050708 72
    0x1000c0210354814200c04000780401d00b00200d0295451500f400101d226a01c04040d29401580b51083c4620560700180440c4034401203440d08001403004c647d0a070380140d110728010380820f0b043c2054500a205a8008543c1c0711180c0d001d5a00000843c20b184105030854008449983c1c0e00086c1c2c001941d402640c0000c1c03d000d8031001030142c0300381c5980204594205480b03041480301d40c0700580703010b4034240603411007204100d12140c2240c40c58050080420001e01801c4e0140c03e040e40140911b0000c3d000000360542a00c0c42100c2c000e5069025040d180c2c0040504a20600b4100e0300b41c040700c0142005802c66801940c07000e07100c1c41d01c0292241001130724400190b1204094104000090f04042410404000401c0d0b00c2084521400350160210000705250030b60307080e0394010f09100118001540c101885201102c9001d41c40900c00414207824900141156030f441c42184d000b01042000081c0280c003854002d41002003500070081803060402035455643d801c40704590040303501000341c42c0e1303983c0c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 384587374 1250 384586124 384586129
    0x61201020c120c070815010b090303090a031203060801090f0803101212032d0c0201020c03130305070b190503060411211b0405040903110a06090309050406060815 71
    0x445411141ea40304181d0300340000c0d440000246214401003040e00c0406480300d5400307598482032a5191203e0040c0340040040e40128005404085001805d0fa85084130b20b0b0000392205000d0381090310f5490480b5030030881070703030144901c0c0000c00c5000001c0c08003d80e2030320f4176000f1000007207016005243c0000001c0340341046030f6078503010748109080c0743d41c20031090a100840121081072003000c00c1c5044103a403007000762451003401c42151800316980c1c8905860360007002c0c040c4004482c0c107564092028100e101000d002900501000e0781c02214200c2c0785050071890010203510042c0320078810000c0c2074110001466104000c4e0180c10701031384d01d881d4031b00070800500688081e00c5401d00c01007041246072031841c0310040c842d2440801e84074a501c1d64040164015502100724000403002c000400c910300f02a080885864068100803183c0342e00c40407600d082901c1581c1c102c0d0222740e144200b404040d00800300c40003400054800f003204a00300980a8441d0300003800902c0c0b280040c00f44d409640d07 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 384588624 1250 384587374 384587377
    0x91602150601090f12050601060e0d11060903070303080a0c030903050f16080f18121e0106030803010b070309061407030c02122406060c0c01080c160b040303050f01050906120102 78
    0xa00080d030710141407999545d0008154803036124210303540d008000000502034801e00d190f912203140200402c00000050340c0340c40c8a8422030000680014040c40500306598042c441040114000e0f222a095858070b0003005c1d085a210101c808181860103420801013076004060b01c40c0c44d61100d0703085030b68a441020f80c01c803503044c90740000c088060018030074006001e11805040204c0800304808119103081c820850001c600ca009a0426802400c2c3c09402e00c900c071111403040e180100c00042d400740c0302d441e080c1c0198801d80160b9101100001d1500405038040440740091040b1b1800f10032500050100d0b081c103214980d0050100a4204140d00c05e5599071900e0052101c401000c3b903080d04915841345048107003070384600413400c01800c002102800c0500413900c40d800000003820f0040400c4d40103650f030560241903954420310601030b8450180950300c00700e05403409600d04101502c0c00d0302e40102034a000500000303880c0c080c28010095074454580c002d8020320110b8010030f4244500496a009 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 384589874 1250 384588624 384588629
    0x1a06160c03062a0f0c0c0905010303021e15280c02010b010e01051329040303170604140a1808040e040b0105120606010302030402011b03090509160215060109 69
    0x404880d080000100030341035201049050500915800e0a5a4410b008035440c40040c20307600402c4440400e070001038481c840c0e9940700d034403c0440b004241d44921412049030001d81003100507a001951b43e0300901c40030813800c401c05120300000d210a0050000001034944050000c1e0803283c100b4080500052806480c40c4000c08007000130030002c0506034000f400b0702108034406011600005400d0515485941282d41c0c0c140044800c0041c980381c6141051402c5100c00701802d458020349203000401854401000198003980c4c2d1070400485415131104149000f0342403500c110720740f02030501806041c451060740200c04900000b001c0080090b0445005c0340c0e0000140114030014011521081540c0c0c07050245008043c0100c00ea80ca41d802d10035a1208003000c50501e41c42000000c003130350f04c02d4004551092040c0340c10f00714415000c122011075a1094411004a030b10751405110a080c00440305a1181c1902101301c80e1f0740702c0c5103010b0340f01e1014044552084004a0008490741d0251045200 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 384591124 1250 384589874 384589883
    0x4030209040303050a060501050717070201090e07091a0307120c0e0d15060e10030b2a03070216050d0305091203160b0903090907050309011401060201021c1a0616 71
    0x103051400b0719004008000880303c3c11065403030000e0104446d44508150340409611035080c021111314030b00b030261203420040781281009065480031032424546100c40c1e01840485e203c10725058184451480300008a5610b9014084d0500800011640c030440100b5020500400000c0f400c1e103440c821207810103502202a08040fa1092200c208400c24451541c0708a401c2c40c00c005c2180c85540c409407040c0c065590120050b1039401c1031001c540b200707541c550842c900450a8940d2001020003015508948001941c4100040304002c2095014003d40300150005200c1070340107070800000550180000030060204400411100300645a00b0081e140b0701908904981e1030718903a030b100044412040008841c40c04502002c1114000b00000340e4412140050210481d80c0e210303c0119800d030401400c2c1c903c0d5640f034022a8014000d408805806003409a00150342c4500640f01c807000c0200300045006810700e00490480003031060103240c10003c1003100c15a07071760301c01e101d60a40445841c0c1c00190 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 384592374 1250 384591124 384591139
    0xc03210815010f091e24140a0c0501090305030a05100506042601110a230a080a090615050a0e0108060708060307030b091f09030801090c050705011b031b020c040b06040302 75
    0x4080c0c5e4039600c201c0700b11001d0800e00204c0c0c41c001c84070410070030040e4080101180078200407008204c1c40e000a0321381c100c01440c160101c6641c0c2d80700c1c1d81c00c2d103c10f010290302140c00001401a0184c0718010154410241c0b820f00701000d15110104102d07201c3c0e0b10032840c00b40c8041451600d2441c26880c00c2222440300c0c0700034040b82c0c00001c0c505146500c051307101d2000c03600c134004076581c0040c01d90f0404580030f003d4001c1e50900450240c1500c1d80382e0003c0003840c0301650b401d0f0350000100f4610034820010300ea034902e12506030500e001e020051850760456050400c002c001040304000c000b1b074103544401d8920703184209071100c1000c0391500d0580d800051651400d00304000d030501001034910400100005c1c1d403e54440d170010050119801004040d00250710b0380f00522000c0318503004680c007016249000d03071800ea80c50b1505c0d0300312807103441000c800c1a074601204c3c0400f03605024190980c042030303602e02c00c0390b844243d019550b1110b9510060050f61280c1940c40c5903030360313481500d00942e006081e01 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 384593624 1250 384592374 384592409
    0x100e040b0901080322030c03030806010c020d0f0b011a0d0c050903060a052a0307031a04020d020702041505010f0f0c06050a05090f06070c0b04050a0c03210815010f09 73
    0x3c41e01c0f0740200313042d10002a0350540e00c0c00b8840b801c5101c0c3d03040300c0d0444403480699040d910102c502800042003141400108002500182c4800d824020310502a0507007001071201032400d185125810303800941420543d1144400607403540302110418840740000007000060300c0020340e401d0140c4940030750b244c054842042100312032500607500c110b04600c0201c1c61182c2c141c00031000d120b140130441c1c110000500c00950300c00d00941c411080e00141c071420408190208001405030f034414080080c0da10303004103d036411400e150280488109041e02c803071283d01c1c02d0400080c60741d640d500d211410091982c0d11198038a008200c81582d29401483c141712915200c022203000d48415102c5601c82d00c111000b40c4080100803c044e40540300650750551040616180c4014902c400b401c180c4643c01100303d0840020030211840d00194801c0800c2400ca003200300c500e41410380181048030900c8098410805d9100c100d2840880f0b401003421b094004120249044481100315088440303440c280d40241d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 384594874 1250 384593624 384593639
    0x301021306030b060403030504290a050c010f0e030304080d0e1b1002070f12050106050d060506091608060d050a020301050414010c05193207120e100e040b0901 70
    0x39001640e01c039403414400c0021140074014684214800500012414030080c007000500d070103005840740d60300e1204c812001c015040e4031169441b5441c6034012030340005849628075000e000d61000340140c4041081040c5c010501207490744000ad0006003000c8002402540c00051a4480b582a00342541150464a00c81e1505000c43c00d100d00014418061060310042c210301c0000c4901c26200201c2c08070f40d495203010300580350001400c0040ba04d039502d41c0c401080d280c0703e0407071040701c260103284042980d0500ca024004800320241403083c000c8241304030b61120035088a5029001601600c1c0c002c034800305420502d04040d025200254154205000d1000303011a200d214400d03014200c000b00203030700448000707a4640c03196800e8403d0031401000c10b04e0301107028130070043c0c01040e10b03900034880c034510242000c05110205038840c0660800701e802d20511402d941100040340150919141d4240640d00041c072810688904004008803984409038588481d0840400400080e2035041c4a5854082 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 384596124 1250 384594874 384594907
    0xc071206091707020a060809032106011e020304060c0c05060703030b010815152101120611040e06041508070b120609011206090614011e05060a05160c05030102 70
    0x6640b00030318041444481c42d4100125420315038002c040c10003051401c0350540344030368000c00306078003400309002c18074041c014000003212108549110a1140c58082c0000d4285c038140d21503c03007031608140b0802c40d0f05800200701c50039100320f400c1140a00d4044c0c43d194070a0541904426045040441c5003820541c041c0c1156081d91030903213a601c0c0070317034400d560740c50000700c0510016800001480b1000c041c0b10814000d01c02011405600080c0112803001e44980900c00c2c0d01804003c1c90384d0001406011513481b50006072014071016900d014a00780c200d0428800180c40b41d48075959031660a64001814003210b0000c2030706006a42e06c0c0c0355100c0d07003141141c00801814074410303030180c000783d41d905d01b06540d9410b071501581180744544440d10703104024003000074111fa030309540700c5d8080140030122403414020880d51080c00043d9410000c031581d194180c0c4d00840c0107807410300c90305034001d4000c000d645940180300c0100d09020907030b00300009103202940c400e07500b43d440000c03402c601e032041d5203 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 384597374 1250 384596124 384596141
    0x5031e15070210111b011b08060a09050a090b0106080907050306010f060305150406080a0309050d050d2604111201050115050c01090609110312041208031f090c0e010c0210050c071206 80
    0x82d07800307e050007a5415540c100086410960100c1440c6041c0032049060344a2500040280750002d046c1b94140e540c081c0180d03080e080701000c40c120030104210072034204000e4015020a0f0040c0c0525458141c0aa080c4011401003c040c16250307800a5401c000240d901d40d80854002c1051009540e03400405844e08000035041d00013608103203020485040c0220300e185810740c404018108402e40c0c28041301c583e010540350380c244600010354003511000e40002c0e9801640203a0500f40c0a480500c200700148400307014845160b41014010043d503008031200c041d030224a41001582c0b201c80342d02e120300400039404002e00440c1b62021540901c81102c90b001310300e030010750407a0305004203049404014000ca104605103081c1104801c0c0010322402d000d1074010458003003680c5003400c0e4189032040c503400381c1c01200078903a403034954141e459440840b44103440300c01e007090700f03e20b0150380118810907542100e14080c0140020380603c1000100301800080407000b0380700c3e0030b138000c40c5000310281039000e = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 384598624 1250 384597374 384597401
    0x210090804290a0e060c0303010602030a080703090f110604081e0106172503021f090f050d0b0405030c1608070e070507110a05031e15070210111b01 65
    0x35101c1c04801c40c40407440c41c08601e4007a40359424003900c0c0300f00303c603480f45101106422904c2444410408003082010358045d00c0950044c50700c030100b0400080c00010700504a03030030941407680050205249070362000200c1d0708444078856014148010600d244038551200d030b418030031512036902040c640201d41810001100007400080d5980c9000340c100009200e400c0c4150b00182c40b018005c451103400110030800280c2240800b65590300020300104400348001a0201180c2c0104081c96000c08000d010700005021040800d00386800304d04048407042c0020041011240401d0a1217001c005039410f811a600817604081c0e054152001d030b40000780f0984c00c10f8800c9000100d100070080384101c3c8031703843c10745d2900d0800d080e9440d1111164200c11405410032a003980200303ea4805005540454544001441002c4000910945413500b0543d005504505080600542c150301084075031004007420350226014584440c3c0c445644581c61103c040c1400340702003508d86900c190051000105c02 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 384599874 1250 384598624 384598649
    0x3110c070f181b050d1803021b1e01030b030708010905070602060703020901050906130906060e0307080c01020604020d0c0f030605070e0102010b1c0f020d111e0915010210090804 78
    0x604440d1001c3d034a000000c03912414039940803c080c0c612420181214803105400422030f0440c142200400b40d100d0741c4160010303080505034101e000c41303001c0010303554041940d6140c0b40002607880100710241641303029040584a104051300e0b40c2d001c0040c10058602a8002c01c40d40745189801a66101244900b01c0940518000540702600901c241c58000206031141031501900000300000c550081d44810702084c1c00b140046071444c46032044101500b00e0341c54408900440c40d0806181c1003c551020b000d43d0320006003410b840e40d0100c0c109400130323419520b624510034070303145c4003081103400d402c05400c403e070709000042030261035006140540141d45405d034042d540c4000482c242e91410b2400d070b40002050864000c00e2100d8882d040445024100c03090407001c01c0c1d0b0009600b200d45000a540700344c083c1110303020f503241a001007160301104003180001c0002a5004c1810342c0401401240e41e06500385c03030281c90785d000f0701c0565801401018100010380c2c541c034003000c1c50327003023401020442140c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 384601124 1250 384599874 384599909
    0x3050d08090705010c0212070e01060e0a12030311070b130b130c060807020f0f160602030a090905190e010507020c0a030302061504110703080a23040303110c070f 71
    0xe100100d024226040c06088000d04200040da542400302404980040e10341d0a00816440c041c052324000d040380a00064855151107001001c407030f040140c051207892210000c000c60740310b4003e41d01c2c1c400e40c0b6040104030880b2281035003020380950400601800f0b249001c20100b5030800554143c00d40c0300d54901072594440008640303540390740e03103c0100040c038002c0c030510010f4000c5120651102e120b104032030a000e020010700d400e10f0150044440140d0080c3d001c00100200201c03e607028100f6440110b08140444900a002044920408000030f56a1020a5403100b81094880e6040c0d9148010301401e040098880e008100440e066070050203010008204d91410075815001c49030140e0007421613032119020440300072220101f81d0362140c0e8403c1c0045600010f40081c05081e03001b80c440013480c4c605108140203440d85580d69000300b20000050b280c011900d501d08642017500745c41d0001d058042d034007090840d0710030100124014814900c0015a000d900c0000c20160390180c48410071914 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 384602374 1250 384601124 384601127
    0x30a121e02030304030c0503210105040e0f0d03090807062405030723040b0d0807110402090a180b130e0f012c03071a0f34051c020403050d 61
    0x80200d940180c000700041350100b40708503a540074145c0104103072031410350411a21000b00015181ca00e402800e04030040256150511030031613000da02c403000e8154281e00d507520316142c5403641c04184c10b040e0f54000030780134450f4410566245543c003c3e010080d40c00d0002c000718401038150010a00344175007200119942c01c2c041030072400c0300c421000403030703c182c14245482e51103c0204845500581d94452500b036940c1c1c2e0644c0555400e000b1040c00d0342d20301082c01c01c0009440e442039943d004a00400440d806510b8880e405d0085418480d040307080e0550202c802d101030301101030b4130756000c1c0410361100f40c1c11740a540310400407205c40d0201c0d140d45000030002c500f40c91a0700703650141e40f1181111111461000d421442c003410745001502d03d0030b1000d40d546100724120750740032101c16103804200b00d089001c4184a0360403440501946007031030041d01e099501081d0210069031048050395600c03000d103000350f003960700303d0b00e41400c11380b40d00000b518150002d4010f071206843c54400d042c7c1406645 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 384603624 1250 384602374 384602417
    0x313080a0c110f010504063b03070e04170309030c010e070f1d010317040312050301090e031e0c0c1e04140405030306100e030102070c0303020c1002030412080702030a12 74
    0x2003068450301e051528199041c0c0341c810221503861102c04181c00c54442d41d0b02840c8080041c02010495829025004009e05181400a4125184840f10b1005000c041b9400e03080c0c1c10300c0d407101e4010440d81c035a503450f0350034190b014841c0c40d4005507007081c1800200b09000b24a0358165144000010020f40d582e2502d002c074981100d407280e480d03003070010041c000708074080061182d050f0448a05803400383c0e01d60310703180010710090250000680110052150603028001c0da540300c81c00380021814040384e88200403005489400130104144000f6124610403020302036080c8401e4000c100e0404100f07080d54000d040751043c480c15204034038111103001d41c011140226405a50800011400c3d44e40300001d00c00b402444240f1501030021804694070256424001482003c1c0300e00ca13040d240c2c610318900a8a0481d2a20002e0b1180300d000d0694000329030b0000c1580d0071250ba41c040403400405032300707001c0242e1040b040e001c1e40600500b82d03880203001d00d40c41e4000701e64929540d9620400c1d0002404142d1 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 384604874 1250 384603624 384603649
    0x80f0f1c080408070609020a030807060f02040311101b0f0b010806090703120315230405071b021302040e0f060a0b0a03151e1701020a080c0313080a0c11 67
    0x41000c94002c5004111808050b25016108002c00a80c03141e568001504001d031950003129800700c0000d00c8400c1107250b0142d612040d03881e42040d406d180c216541c0c40110b5212003c058000ca06850805000c64071074280903100e21800040e5158100751420090191100104161600d0064400001d007542d000281c26205142003000b900c40f1508541e106490081001c030610f0030140c84080d030302d03810000c0710000401070000b4580c29010a00c189000100070901c803410612035458041000449074224100f910446001a01e1200c00c0801d44002401d00d08140c14440e0640d102090205d904040740c400c240c01600b030401c441900381c1da0001008008510783c000d442401206001035100b1502a0300328401c251000ca1090584030344500c0b440002c1c14484030860612501640304002807201203207400c5948103240001e52034000c0e01107000c0c04252010f8001003111100000003180380400055448825030b208001c142c0c2d40c00070940081c001120154103075119092004002c0b003914100c0f159120 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 384606124 1250 384604874 384604877
    0x11040f270201051c060e1302010206060108010614090a09050f10120f060b240a0e090405030405012010090c27020c07050303031611032503030204080f0f1c 68
    0x9022254180640e00700138440184010b1a22100089081c10000c54550310601201400070300072050f50000a03d05180502002d041c020664010b2214562007250240004480300f11250740b00f51540c04a40001816440b41c1c0d526490711051100e100e03a01c40466000351084a0f0010030161079180e01c1d55200d41c000c50080c00d100c040b082840c0012125005040d41030310003003512a0700b006038440c007443c401e006034200500c2a8002845000183c10280b00b44051400751508249403406581c3c0507070360310035400740303a0511039030b5400c61002d5803c0c12412181083c0d04819280c05aa02c1003100029080d6050200d070340c14030044e40410340c80782c8000729400d8104072203000d02ca84000002020700960008203c0059400307002008130301c0742c608000941c0100c0048182042c0160074402c002d0084c2c900201c81c1310146c00c100250910250107601010030501d100c00c9040c404100351a05030024400d0350311082f1540100da0030300b00307081c101040c0c141511002d2810b81e800f45c00b0303031080c81944500002c0500d0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 384607374 1250 384606124 384606127
    0x30106020a1104061203090602010c05090d020405061c080c19050a060b011101020406120b0a08060a02090f0a03050c1008131e05030309061602240411040f27020105 72
    0xb00e192104010b510a8001d00009038040e11003607001604051844240d0115841c04c1c000c00000c0d60900c6580c0142980c1e2510a08100324000003540400700000c000c0d11540d01c401c042026541c40411000c0c030440c091107401d214045502c6c00441d03507000280704040c14040c7d010580102120801c140d0329065200c0094407100c8259601e100043c0308028038141000751180e00321071996400d200820152030a901c41800a104140c40c4e50b0070b64904042c001d025068040040102e8000007405542003094110090389074940180400c405554100c0c1065001c0c1181c0f4000061180200f00e914003103405480d000900c185004090710748800c1a03e15080b100141d05c00000802c2c19010301c8084034504244c00c561402041e20b0f00d600d103400507900c0002e03580003182440b20403a0740d021004a122170b140060445124081110700c141c515140303c0170318032100200050100b00c402050740c030318240010000c002d4a50880340f0b0b200109480f40c410340300011007082d0070004103210200281c03016816903801303 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 384608624 1250 384607374 384607393
    0x5100f05010302030745032d08031302060d0605040c08040c150e040e07061b0b0a0203091603200402090f061614060403030522110102071e0e0c03010602 67
    0x400e483d030746d0146482d201181d4541e207024100490542c000700d400240c0481c43d210750460a00c40e4510008501c42003805813211410624242c0b1309408d98401b581001c0b0207a1a6500c00c40d04000c12880941d000b540580d0000e07aa40714880e032a848907045e10070a0301c04211040350306500351115a016200605800c007811410050074078000811940130b5032918000101a1400c00400e00707850b0040907140154010345020320100e6400f034400304c4080c443c030400150444081d05d03000901e002c060007048400703400100107015540e08000c4000207203480251441003503aa420426003100b0f102c1200001400325810603820351400d402958000b0200802d41906031000004100c000c1c4d1007003001c0114050145aa5008201700a8211000c00c15110240c00da80c50189030050440d400142a90f4014090b0034907905014081400303880c0640d1710100d040d00c04021000141d251079466031101c00802c40b41c100d45507090071065000d40c119103c004105055403290380c0105010f001c2405850010781c48004031 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 384609874 1250 384608624 384608657
    0x30b090303310b0c070b010e0103140a03080a18020619080106020a110f010315080105040303150e04031215060c050c0a030812060d021305072c01031e05100f050103020307 75
    0x40c40d800040700c042c0c04d460701c101692402d90900003640135080150524004100b48140381c203200510b80030510281580503a82d5502901451024013541207140d80d511204004807081380c0078074181900185081d07103d41d040b0603c00e00c03950f080448080080c4da00700c000980980005034113080e003a071010080312070030b2a4200b0b008480b42c00b40705607410983c030384905a10390b60100c841c142c0a00708a0001041520f894200501a20100008200031041d000410407107c240c4080a81c1c00c0780e414a042e402c415110354030b02e0003410804141c000030a0040d5400203505810006849203144501c099850203d42c400803c851041d1500c0050400030042000045548594084960145000707004500c07000d0144c0108003504007141002c2d80c41560740090290342900302c418409240864130120a881003003040703250b0101d07d04600c582c140354a490403100600d14101000c1021902000700308002d281c02320001c000d4585c1d500c00c00c80744070f074040400300751540310f8005c592040d086d94603070b20201c5c1c54102c1c5 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 384611124 1250 384609874 384609893
    0x12100509091e070f1212051c0e0c04050907080709020a05040b0a0203040b160201080603061b070305190203130b0f1c0902030a0b0a060b07020306060f0109030b09030331 74
    0x1103140c25016602d0082601100b03c405040a00294281d61510788203526054041c0203403600e1b07800911105201c00d200640b0454807801800384800350200e002c510340c0e0019450b146003140141c0d44070341040c080041c1400001a010704950303c030811114a01e80d103280d0075049115150113600021800c00c07051110500d60030041a00d26502e01c126494181e40744010012038100c4400a14801f4200b4204400d56a005420542041c001c501402042c10a410240840020303501082d9074400e02144150505006900303849058105da2110150850313500390094496000122050001d00240c101142c074010075401d4030703038699580c1c505c10310f08005006072510030f10b40c61103242405511100142e0060300c00307000140c9640d2185800002904040400c041510903940040c2150081401901c0150790005001508404107a407440c90044440300100c41400103600301500c400f14000620041050003c0110301c100c82c4a04110180460003141960464100301a03003d0300c00091050000b00f8003298 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 384612374 1250 384611124 384611173
    0x309030a080c0d0c03140c0c0a2603040c0317030f040b1305030a080106030c050a0203040302130e0d0c05060114010804022b1104060e130803060a0302061210050909 72
    0x710b0505001e981c440e40c0090b51110715810001035114810142040d90086c56150030030341074014181410100304031107684a10780c42c400381211034101c9403c0d020f17842054040c43c100d5003d40c13001340e03a0304d05414a8418101148403ca9242c1901c5a100703120050700e0b02924080c4050380d400340303621b4032140c0b4cc06410420240041d407140190740074400c00600e0400003441d80c50300584030b6200a626020018003100d4a00303440c001031020400094012590100c200c4080d03d50480d91500c4150001d80d500c0006d050341c0301d1400d024862003107403048282e0003407400503510780720704211202a07880c1d1445126801cbd0001060340030801d69001301e001450240003031003415101d0302a11949607819600700c1d20360710400700140c80352411107819002500740750241101500e1465800041405d081c0c1c608281020328140251030400003002040050ba20039640c44001d40e0004c100c40e848002c04520003686900669441c982140100300004003820000034803803040c590b0070003402c08100c001840089080514 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 384613624 1250 384612374 384612391
    0x70903120525060c170705121e090a060b0303091503070201091e031227050f03040f050f0301090203100e0a0c06080106140304081e09090c09030709020309030a08 71
    0xb0340940b10125000c00700b141669010794800300304182c201c040941440604c6102801070b03c11708080044590f0004100c8a41304851090307201c2d42c0d982d2046078900c003140101c0c0c201c8410f1502d400e00c888590300090070540c080c0078510402c403291f281801c0658130310504440541100380000b05d0795415034107401440d444440c034000407481c4034841d40d503000609106400c04100018903038800c01815030098640c08d001c421030004000a45070422840e505605410b13800c1d04002c054155403003004800c2c44071409400d865002c40e5107943e1986030080d040d41090240600800101000541d581340500070707020225000b60150441c0400d00d010781024118029990405204505403c00010032110f0700030700514066407004001c1d41040001041d5600c0c9002c1503072045814010700c8041085007048440c4881c101c10480c10103492584070030071a00410321840e40c8a0740880c00c21060110010040003c1d400450039680c3d0303c0c0e03c981e140422404141d502c02140e07403092081c0c031206400303503180e50741200c0032 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 384614874 1250 384613624 384613657
    0x30803042103233c0a0501090f020a0c02011206050604081006060207080715090b0705010606020709060f090e0f0a06020c190807030f050405030d03020309060709031205 74
    0x205105116480c0d0300216040000d6642411100c0200a0010f90040d0349003040e86404a0a160300d68892510344004901d80c18140002040c25100c1c0c2c003141e10100519007010b4210610f051100840100713024030a10401508003000452030010720b200b00c1d10b0308071090301ca000812040f42c00445040380d10766022903400382c0e216000b14065581070007070402029500c0c02451441c069090943c10f84185a00c000e055520903070080c03110b1080031460000391050a1440740c102210040304403000051a0700c4600600c400090020074820190072003010f4603661380880385242d64031005581202c10500c110401c4904620050102d40100d401c443c2034280f0810458220710282e581403414200d007218200c0e0a07a5001580354a142c42c02d01c02c90140d0920617008221059185c1c84144141c480d0006c002c0c10400442810004a0300a0b025100500b0004c0c04855858209600160084d482a585694948290ba0008034498400c07010041500c0d4010500b00d0403418131801991650841c86031401d01500 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 384616124 1250 384614874 384614903
    0x702150f01060f11011d0120120114030703060e161a070f0f0206032410080604240605120901022b1e020a110606031903020c031c080108030a080103080304 68
    0x100c082c120540301b0004c1000041c803c4554040c2c03140320049444089600d501408035074294800c559880b8110398851102002c24a041c10010303080c410746d5040200070b00d1400c3e04441d142500001d5100390ba581c0c0303001026610b0b44070100c1014120481c01d002a01d00010040b0701c4c001400c04083e06401071148208030001c2d8080d5001079015082110039080e07040500b100079031101030b41d21858030f00001c15943d4242908210f20010000d1034000c0110740506d840781514202000100380c40906074001c400d2107950304d52140c00080c05a48030300d5050044c0c0d243c44001c9605804188204c03140c0c0c02203005e240110000300c0040c0c0d0150718489031080100e41e030355100c101440170310b4403205021003c51380d00160b942072440701c0506407524040111903246d10000c04c008540c1c500003030004e04100d603a446481000e0051400320316103400c0b04a4941c142c000c0cac0d104013034082c10400d41540c2c20b100d00d40341d11005eaa280c81015541713010340c261110010711180010404185c4002c020740c1c005000300b882c0c250282 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 384617374 1250 384616124 384616151
    0x303020d06060221030919210216090b0a1a04081207020406090b090c1c09080403110114270612060f0402071113140702150f01060f1101 60
    0x1007080d4007950260300100030b9800074203050070780102241c450302022411401c2c200482683c4120079001c17070b0414042c62169000307202244000b007580c1c84e0562850041d01e0b085900083d111000003666507003410800c40d001c520301006000750070103408003411000d00ca51074403450645420030219a503001c1d200030400807403d088140841d43c0c10b40150700e8410780d501034901c14081154040da101e50465454059007042c9030b6140c1e0003c94010444c0960261100114041e1462010000c40c000d50814170b00105402000500307400782007100c1c0207590203400440180010340785044042c58914030403004000300c04062800700e241007030340d000c100500049070071041c0c04610150310500c01e4140500c0d11400700683d41c0b400c82c440703541c1000c007038500b9402c1c24070591720307180c036190800c400c2403241d0101025030401c0c0c41940e00c10340380100390089141d0b40c2e0404c00f801940f621490401c6200121074100010489080b485c8080d0491302c4999440400c100c076000101c94030a1459141c01d42d5540383e103500d4583c3c9 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 384618624 1250 384617374 384617381
    0x20909010e0f0a02030601120f060803070c031205030403050a05250506040605060307060e060903010f11030901061a12060307080601060f0801120c0b0313050d09030204050f0103120c0303020d 84
    0xd0008600a9610b07060405900407440380c0103000c8407599004000f00100360364000c031815820943c0000108880005501910140c0720f40d4011008610022a0f20010b0020307190014046901420009003000715444044600380300454001d030204004202201015100742c00424120a895402d4205107400211071024100190801e0300c895100e04203000500103148211074000e04103d00030a075483c50004081c0c03040070481d081070321800e804078024117a520203401001c00c3c501c5041c0308000480c40850541c0290300706641401d101e628000340890f856200c402c28116140400603903c0c10241240c940c200306483c000c041a8042c003403290001904241048514040c5c0b40303a86816408600ca83c00040040c80305900c034407201400621100b0104081c40290401d4071844a050381e034070b0b42c507010410315503850030400400c00d21880010058a0380e10190741c0c07065034400c0350240b2464440d10f03040c601001081c08090118400034200461103800b40d43e10418840c0319007005814849803114400c1107 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 384619874 1250 384618624 384618629
    0x9050105181c0219030215071806090f05040905030d1109040b0a05151e0a03061a0c0c01030b0f0d0c14030d0512070e0306041b050f030a0602070602090901 68
    0x4550800368440e080c075800784020410101d04820b031540e12415400020f41d0b520114840d440100c08881407101411b03c244030301d044610b480482d05500d414500401000c0d50f00040d8580c00342d20b00b0b8903000c40c2e407520610741171080350302480381d0500d094107200070071000b002c404c5012146032008010702e110312002d500402100309e6a22030810340301d041403001d001c19036030380d0034080b44207244032402441180d03258981d00300d0b4181c00c0440305ea1030700c144155609a82013401c000404104002c40c1010005503d5044002550352800380d4520581050152040c80c2c083c08028485680000411030307400c0d40300360301c42652420b00500c0241c0b11041c15000c10000c00100c10182e0320300d02c0349007060016450f00b840141080d102640100007240da2000c0007001c500070680700c1c289030a44900401c1c2d00038880d1100710503000300203058800a051a00d450340e00980009034011b0701e0880d81e440003c03c0c1c54104000c4e280c0e01c1d406030241028041d0756403910000d501060741151040d500303000c10546a26500c144601 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 384621124 1250 384619874 384619891
    0x910030608060c0f0d0902040e12030109060905061c03090f170c12070e06010507080a0518150406180f0602060912070f030c03031d0109060b030304030f0201050c0109050105 76
    0x3a198100790480c0d05245000b400350501c0e02c0c040080c0360080c60040304507880c8401c41100054054400d01c00034014017110070990703c5030f00c01c504150144c0d44007030f80154121501c0f07030070421490341e80344100802d8841c103e8401d0383c8240b184001d4030301e510321001c90b1004075210740762079036a9a03180c20b5500c4284240e078010751003088100742d103c0d0a44204105a41107c40d0880e5400d0389092032181c0e055880ba003a01424200c048510013045103039018605131103a059201400f60349400c0c2c450001003454000001c102c1642034403616041c294280b030074200496440e80365285141074100b54080c3c441122400191141ca03241c040c0003d1007003c03498002018160590141419050040009190000b540340605078000100102c00000e1100d400300006950315041c16400082c0d5410140c0c000c104480d400c40f0fa00d410755003c000558030652100f2045440762008010001000c0f05240e541e01950000038107107164451900055801400981042c42070900080f4072100e140d81c07814203403030701070703a000c1c8 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 384622374 1250 384621124 384621131
    0x906050103060e060f060703050c03030f040525150203071a040201121107140a060f060501022e020319060305010f0509011a0103270b0429071202091003 67
    0x4100d69240c003907400280790301c10240026090810006103854600b00c041c921a80d0001020001c250050068480102e006801e980e128a06554820304103003088604845a0003000003a80c1c0e40511780e9030304005c549403404030801c0641400e1000c080c0301d9101089805500c030910a0308000b50810600740700462407414603000d10304080c030015003c1d4504500c002c1c035080c180021462410850820f541417150450204541c160700301c912607040010800c4007620450030000b51821460807030b003007403003101c4c020303801c40b0080500030351310324040041040740d00b00004044890030594074094014540140d090b44602c0040700c4040d0b01c40c000c441c4540d01c219081e9441c0c0c0300580c00c080b5148140d50740410700a000380031209445261481048080e41c0c01c80c1410340d1105070100303000c080c40403840721221f40b40d00030900030f0307660a08251140049a04984030007001c28410b501c4001c1215914488031680028440d50315000026208600c2491442104642c240440c034040e41e0340000040c074103070244e10b002 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 384623624 1250 384622374 384622379
    0xc0304030b0609190b01200a110102010b0a0e061c030207050a09020405090a05150d080d050702030a1706060f0d09051c0203040611030c03070812072a06060f0906 71
    0x441008000a054500c0fa0200c0420071550284c0e0344144012111441000642c03145843d006031b0320a000c0d1030030401640700805001411150020b004e0304400d0203241c3c4110442c10307110049091740c01c480c40158001805000402c03403851f10120594022400421112030441548141c0e490b0000c2140b0590043e031150501300050700745170383c900303025001c10700c003d51500742000d000c21004a8058442000e143e0f81c0c1002400791b9488460081190100808120004500b820410500e0b04003400d0002441e1401010648480c000800c4580b100665169091803403081c804044035010700814964000b0810814055240900c1e0000c1c00907407100100011062080c0c1045417419691404400d00d071403041c850040403a80001c181e034101d520a14026004100e00e074411030a500a0102e07211485c80045207420800c8452009000401030740e0500071425034440a04840300c00b030000c0d500c4403100c0300042d1014441079811504410742e00405000c80c82c5907580d412008c080d41c0d41d503c403d14050303886105 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 384624874 1250 384623624 384623633
    0xe0a060e0c04030b06090408032a0f071a0f060904050f010510150311040b0d0e010204081f02070b041e140f01110405100f11061f0803030f060405060d02060c030403 72
    0x100b1740043d03007580c9842d003a2506540d241801d2001401003440401191494203058100d8051840035038003160841d9110a500358042c080e5410040382154100d4444100036582a44426400e2148074502010342007a2280d4041c00894080604180d8440c05001c009010140003405035078050200e507680b00702c2e40c40c94640144601d42694903d2410141400505003e8909410542d415610300e11020340e40d800d200c680385802402c542d41e010b0000e5001160002d140007000c00c10590703004103000814800210911184200d03c20803000900b00451240401d0108110342e19182422020344112078040c034042c4c1b2808040d1113010340c090081e600000640c10090000e003e8050702001c080207031790420382440c0004944a00041c9540d0400c6851130842e002c25201384250054059020240d895034149084c04005404000444030407901129400060310000001201e102d030404414000031500c80400f04400780c01c010b00f01507403018100a000016907603940042890010b9400250307a1a45075260 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 384626124 1250 384624874 384624893
    0x70801080307020a171905100e070f0b090f090f01060e100e0909030415090504061d0403031a0307080105060f2205040c0b070302030912070f0e0a060e0c0403 69
    0x104403650824400400107850b080c1c1140c0c29240e002682e07501001e009140d551070003a03092181c0703413428810100c680030701801050ba00c102c1c1058034000e102c3c5200d5035014655440b010303c81c0f6245110f415000704003645d40a4043c04040c48020809050040303c3c40000e65080c04c29601040009851401044500d40261703011b10054404d858040340007207407040142039120000c014074058011480040c560307500034070032603024111180300c20545200071071000308450780c9806154000c2d45001c0b40031401641000448a14003c01320402e905592070703030740480241c409000040307039045913114000084d540c1441050084d000b500e00010f818645142040903901610041d940141050380c0310b1100044040c00850124210a60120303641e152450401c8007805580d06c074500074580032411004055000c00203000c0548111802c0104044e607400458846a2178416503070a500c3c0b200c0c00300044005104250351110b031103140042d1084c0c1e513151101a5040c11241d0305c8407154002424010481d103011b = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 384627374 1250 384626124 384626129
    0x301050f0105030312060d140d0f05130605090406030501020a030c0311090102030415050702090403080108100b030c120106230a0605090306070305131212110913150306060e070801 79
    0x103458030403540761001098580c0b00713a803201040c061045000807142d0b21906102c051642c0c0c80b1454220143d40304001903210b1003000c2a51002072900003480003101d100d0019520740400c1c8100b81246039280010607555548000c00d80e0703800545030600000801c2080c07000e0444851544c8000c10403416110008084404401d25000301c0e090510668040b86d078004140c03002c0d50f03003044d40300ca0380d016420429101800b80c50402544404035400300000c15510036003990484140d0360840d4074054070b01104905503070031001e003540c02d43c2c40003c104a09140c0303020407007118000c1c2c8000150752034448102c03000801c910403030100c00013514110904217042810b411802400e0601c5c0480c1001c031000002601c8200203001c4204158a520108400f01007080a02a020385d110700b071090400e58004018001c440c40445202d551844c10781603440582c3c1800460705400401003a101098810b10080f07001490141e0120341030303441808010000550611580010307201020b64480d40c1d14050038003c00141d4140c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 384628624 1250 384627374 384627391
    0x1c02060603190b04240c02011b0806010e1908030c0f1c0e090a0f0509060a061406030606180a0603090c050402120609060f031b190506030109050a021b0309030105 71
    0x12140e001c6101c6960041d001941702030029001485c200b144030700c0f01e92a0b03240c14030f05131070010a2100c440e015449040c2146280756a14203403100b8040c01e0341c44020480783d407801f00c0c0b01035005c0c0d6018501101c030821483d220080c0a102ca50320340200528580008146c001d05610184280030300040c2040707074034041030005450401c00b41d0000001007000e0000c4150a0007404c2070b40c0450862140303900005c44480020301c04101c2840c081c00b04580e56601691900302e111b00e070010100d0950140d103244845007201030089451901c4020502902ea4040321035414203071400052420303a07981e2039400200078105560045150140c0f800d10b000c41e021903074000c510a03441082182403141c0e00848069200104560514855441401044103146c0c3c4600c5035516005425039000480f440c060440388840c1c064030043c5100c00b55000c0c59218042601400390302600900040000d02c0858000f07e600502014026040148000119899201000303030181e4030740000c1418040ca0809104250303000041 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 384629874 1250 384628624 384628663
    0xc0f0f1c051207030f05042301020c1504140703080408060106020705010c031b0215041d04030507080c190803040b07020105040809060a021e060601120903020d030902031c02060603 79
    0x31006421031145008003040048400009042c0074020b41c856025640c90440502462810f494503800450400b81c044a164402c0303140c000d94010140700b40c500740c1211600500301c114002a40541415000700b003100c0c140c104411341100008203000c0f103c01903108502046e121821700984605100e4140c01001c21503203c503900704201ea074800100140c594140c10454407560303500e0034100c84510301d0407000e500018100006510f0b00702c110001c1c4225905501e141918071407844900c09004030565002d00000d030188880c80106034203100800701003030200708640c281d0512103030b40112604c2c08202601c034444e01000300000e10042d0003500398011303a01d2000300401e18095451030303030714021096014022400800c101820f140200002401c40c0e070072a010203084120070204540d00d54040312301c9400181c02c140d29556044c064000c0d0545681e058010f000b0302008003038110024030070b011060380d0610514415842c2c2e101c20b0581964041d805a0142009150070001c1c5807510881ca1301c20b050b141d11 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 384631124 1250 384629874 384629923
    0x20409030f022a013203060f0d0b070e0a0807080102030a1a150f0903030301090c0e0612040f08040902031501091205070b13030c0b0d050a1b080402060c0f0f 69
    0x3c400c2040d003000e401d00702031100c2a000410304109014440f800024141000034080d00d0091560255100d00c0702100c15104009405040c0b2002e04407502300207111010580115000c14000c038030203d2440c0c005488880304c5552806554030b0500c05078070114059500000380312030310f00c4602591100300d110b80e82010103010f028001c10f0f07550151882010042c0004101d1a01c502c200780c04440070300354001d048944a5844240100003800c03000030803402f142651a11510900300f040c203071000d00300105da144a555440740c0f0341002840285500301c800e05e80402020802203928805503009120442c40e028800010200243c2001540e81203140d650f0a1310300780e10700213500061400181d556940c04640c44181404a24000444035000140410380340c1e900490101e2a600c00781c68080c25031302c02400745403200500c1c04100c3e0403880d0000c20400e0b2002500e0291401500d105801c81c3c40a0951381c42c1072424000302c2d050020150324103401e42c1141110010301030080107003481e1181c448582034890703103 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 384632374 1250 384631124 384631183
    0x21070e040513150e0705120f010c230f0d110310080601050f04021308030406050c011410030609050a06050c121e0f04050a08040308090909010603020a0918020409030f02 74
    0x5140f4804a09860302d60640c00c0e01510700348100401040060801e460a1081005658440005c5c00400d081c640c070700355a0003252445203501c107944039492003101c1c00014070200c00c0c4019a02482458804c80c408205150260080d0321840700c43c2e20300d120a40782ca84c00c007000302c0801c1b4222030b840490194440e07401407142e070f0f83700b03441e500b00b58104440c01607036001304466401d5240013640c080060f81c0004200000d095030400010400d01c024079008000c00c41d81c101244c42010015591820281c0c00400c3c144002000365110003074160250048410000803a03036064107561003102c0000450300045001140200306400031600154240c0c078441c4172603204540140031400082454001140319030103c0d041c0702041c000c100e401500b044285580c1c2c0d48908240e4400da00252a240c001c80346000003031903149041c0f003900e080e203600900e50b05407985040c5122014001002c0b00f5410340e00c2c503c2c2c100300107a61381d100785900c46204c3d0721039143c0d042e41e600300070341080808242e046100088400c064600f1 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 384633624 1250 384632374 384632393
    0x11030121080a03090c1520161e06030902060708031b0a02030318150412030b060d0b090f1608070509040c0306030506010501050f0f21070e040513 64
    0x450210440031405030651080031040394005001801d812800500020039951540044010500940c0b00240095a44101c2d10074200d15202040010742c40ea0034541c4900c1445104a0540380301c03204445004010309440811283da0754041442c1c0a00640f0010314800054010401403805060420642010b41c000c14507500c9401801440180000001006a03c24980b0160686022a2a0342e281da080103000707580c07680203580d056614064018001c50544000603203611030071542501845c961101e0317850302c840440d44c921980c1030640380c00b52145030b81c84140140ca0100a222008aa00383c2c3e0710091154464002d041c10039102c0218040000002c00b000c1c030481c010035a89480c822a0f950361400711035030b000c1d80140c3c0f50700505055812032419450742060040d03034003903800d48030966654801518640300d1005003c1d6001800d0110060030030503000901412000006480c00441440f0414914142c044410714040707031001c12503011a040921070180c6c07082038403001c164a0215510b85035403c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 384634874 1250 384633624 384633629
    0x9150e15040b160311030f0903190302030a110c031609060501081b0d090b01030f020a092f041d07030e120d0f0b12010e010b061e030a020c1204031401110301 69
    0x1e043d82541c190341094841e046035132031104d00700103503900c0d24017502c1e031441e41d0752042c508148244038544005441c2c000c841c00c400c0752203a26400031860b2200541c4161200408201c020700e09020364086141952070a00c03a140c041400500700d52400740c14415661308032000c540081d41000407010030840f00000a0407011030b4124003603103640d16400d0452015010f40683c4c4002030441c00d018000008000360000b031194401d2003102c070200c00584440e034640488001700d8141500c40c43d08903980113035005c44010340b00c15000340d443d16481d158403900301d0600ca050105255540c0090881081241c0b50b0620400451000c48405003203510400d000e400c905000d0011500b410a56541e54130880450300c1d840020b54400160030006403843d88807240d4001d02891003074100d59402c10803501128030b03049085400203c1c0f40b0380400b41200162180031060380008050351003240d401c01903145400f02c00c0002111b080d0407505110360352825483d00fa5000c0c0181034000342d0b42d0381407140300c0e5105403100b42174906 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 384636124 1250 384634874 384634897
    0x803010515130f080609060c04140d0b0907080d0519200a0819110a0b061201050103050a0c0b0304031e0306120b0601030e030310030803060109150e15040b 68
    0x4504980c400400464401c2982110076002c0b660000981c85070300c94103031030480b980311095441603039400d50381ea6100c420071140c404070a0403c00050020742c120800c1c0b08811304018000144100c034070740c4c0d07260b10054103076580b2201e94041d050400000c10304001102c2c00321114600182014501682071303843c244142120410f0044d181e1804100520410090011710005d00464201410364200341581d580000000c69a00712440e015038040c50080e580d140c00c02d26013800400c00c065264941104440d8064030003540310a2710140c09210b8107007401042c1c080d6000b0009406140803d160400c01c0640307507441141151014000c01000c29040000c800d911584c0c048000d81d00244c00344c00718010070032504401d401c1903c0c0704854050251030100d480c4116007e807010841c0f52101c5010a54074003085541c04029240b03490288009a1104080e41d04001d041c18540a0035864603029501200b2150030100020800008030089103882030080200801345414a841d00e41003244114052248075000300 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 384637374 1250 384636124 384636139
    0x5190e0a0f0201081b03100e0106030c050f030709031a0f06010c02030c121c050c010606020a02150706020f0711030d0813080c0a080a0206090c101d0f030708101808030105 75
    0x110720004800841c0043c0e40c1c03034151030742d0700e151081c10034000c041c06008080614103c14002b04290380a841500400541610f50f14140f5003181007850081d4801842c440c200701103d00000001601407110000c550340300c0300004058603003190070b8025400e005040c61304010035551183e002d40c0340400c80507281d51b4140c50000c80c401d8901403561400c000c1750807641580d0015803590040302e9004018208901070070009124256984100300c2c2d07070b4410344001035449507901e10100b0200d440c850003000418411200942042c2031500c4001480d001203005a8049802408484035480c0500c40c0805420440c20140d545050101078150b2805204d807009220b0840024130241d8100104050140c6543c440c050034ad441600305002900c44d81e0039140380e03080b0300c41d07507041c25098a41042980c41c402103940d00d0002c02034800b0340b040c10854100e2006504044240c03d401401d0b01e0601090000d40011070040003107142125202c01103036100400c1041c221903000141e000240000f0450341115030486810 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 384638624 1250 384637374 384637381
    0x140403021f030e03030916080f0303190b0a0e06040f140a0f0f151806030803060904140105040602090a0803040b030406112104140c01080619080105190e0a0f020108 72
    0x242c005000c5074200110030301c008000c0058107640041c0300114006a00307200c82c10301d951603008950300e10a4070a01c1419801c00d1001490705a11642c105440c610b0030030700803c50512402c0400c054444580214103040840e00c1000540e0610b07028807018000d40d20b03410015031410020b5160340e600701400b0400c40a480d0066800020030a400189040e00074950030400c01d45c80d600c0001c2852210722403050005140c500c020000c1160707100d801d08603030b0004e00b01c500d140e41d25410421550b00041040b5040e2000c1c0760f4440c0f02e04002d11a1906c102c0c428507005956840780c008006600f041c55100b6040369004101c00d000000020080d69040740c0d01c40c80124050120000d004e1541c0669500c6001c401400c01d04518002544000c6ea40514003804050a0100c4400c40b110b41316200240d00b1030204000b60040f400c0c509228104070101c10b00e0308a20b0412030344074988542521020382d4594854400400900480c1c2441c5c0318502420021000920742880342c0c0d80d48040007001d00801a06100105002 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 384639874 1250 384638624 384638627
    0x509010c06060f05030705010203030c12071718120c070b072102030d110403020d14030f0a020c0a0609230a050907030e0114060117100b040303020d140403021f 70
    0x440032459100320107010007900c51800d03180e00c0500c0e20a0700d12a202e200d40014040d40080210f0f4007a1202c0e0000d01d14141d51115400d000d02c40260850080201c40c50040070012214a029070080c01d952201c4094240d0b007107246450941d9004901400d8002001f0014a000000032404122100007130f0300c0d40c1711100f60901e441450050f220403000515000c00b03000060317034007000401814010220030810802c00f100300c184a400707640002500640099a03280100310085034031020b00d9100d4007100e00c0c1a46816001440d0341222000401503413091407620310524010107220050042e0b0300c1c01c4a0070518088600098000e00c84000902405864181d0499141c0c4022440a0440a01070030903a05000340f0050007048070900f1481d1a500e0114008451481e540b0200d008442c140c2d01c0c18189244001c001d0803842c0003400e201d000407001c0d40001502c65824024000540c0290042e0159010700c0341c026003034285e014550030801b070f42048103000507a2000960751070007000d05800907601d80500f50 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 384641124 1250 384639874 384639887
    0x10b040803072312040e13020f040917040f060210050906130f02090412030b0315060f03070f030804050a0e0c04090e010e2a010206010302100c211d1e01050901 70
    0x402c3c81405862445040b041c0d00000504c12680d0803141180f007035440301c2d1294020f95100000175440100c8000c035061500c1e264001003180d90240000b0742807003050f1b148074149c590107a40418141c1242450030050103405210002d00304491107000d00203850424490b0b0384890000306a980e0f000c8580e03c285052028205507000003545c080c10307507405410641483c802c071071540c0e110080000d051007040c0126007000f1079030200010400400c1d8139181c0f9034204000f511942202c80b1500b603c20604001a801d010301035000081d401045119a140d00301000e0001d000d803150001c0003285025030134415894204030445003198104100002c8504c85151183e000d0058041c05055512610707403007582c80b00501c050107100401a18030003404550b451b0040e600e030142444003175130041310103040581c41401009040d403003030310840f05e01c0c0e0a0b10040c00703000c1019880300211000900507401c1124018400c1800c5411186c00311030303c58107009030040254002c040e003c4030314104603006c900e05a059003ea076 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 384642374 1250 384641124 384641183
    0x9050a180510051305120d1107024009030f0c2d120f0906021f02030a02071e0c05330d0207050309100e090103171e12010b04080307 58
    0x7065450511b46154802d82c16003045908020540c54890044518201c13501141c070116409407050040c401400580107422607916141c5030041c2c1c8208005c1d448803003058445405004440002500d801d5504008220284001d400018401e101003a080821000c0700200c2040d040c4040c10010800017481c403401c10001050010414031010301c0d40716009401189060014869603102e61003282d03914000c13603651440c4440071205124014400013010000d0300195406466880054908025aa10080300200050a0600b014042100342c01004030140c0200010141250355840750002c441348092005200c00d144810b21344001100020200c0210681d4240300031960119110551030400300e4484d80a60103251098407000140c40d4960f02640c460f8000d40030103131003154944e0071991100c0b41d20030010411201100107205040c124543c0c0500d01d0050b03a08108903130346400b01501020030304401a0084e900b520000c0c8405d100032a000002d441c8104d130017924051a071500d120702607580d0440d04 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 384643624 1250 384642374 384642383
    0xe0f0c03071403160210020307050a050708040b0a050a0908061902130302150409051e0c13030b04080c10060e22050f060709080c0a050f010e0a09050a1805100513 71
    0x1004120600d411001c0c8101c40d0725050b006c1d0f8060030704e909002000c80c40216100382c0401c106006902c010351044000c0d080541c1304030916071400e07448042303011720381d080019000001540041c560b6a4a6400904400100350f010020a010309149000050040d5070030a80110a0347c00f095220003034081c3c011500041d9006031014008150050400d80d0b194418020300200e1130511010400b1050940d4a00e018a9542c641400d1540c580a01c1d24003160b12a05c0e84418081c1840c2d1f000c4081a6080b01c02ca00841c414800c0780d0350f90300c019100d98103003590700200c038580b5031401ca402c11058003841104c69001184011050340c8840d801a24076426040860280103486402000c0c3c140040024049004903501c1d11029001640c42e82047c0e91060005042e64214607003100030446420020010212020141000c0303415184d1007000c28042a0542e205040c036585850a1000400581c880c0640c24000e2600d0036150000e9030f1140c1d0f03622040e41c50320403045940c8d02c0000710382e86070003e114042541d10 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 384644874 1250 384643624 384643627
    0xe151306090204060e030a020d0210120203090105010f050301090b070e0d050124050a0605040b130509070309020f0d0b0103080a0e06030406020c12071a09100e07030501060e0f0c030714 81
    0xd41c12503200075001400b50740e0100c1c8070105403090514000940c00791859004100d0b03161030f0b15540c240b000c10301621803203105205512401800c07020b5180080c0d881020b0341400040e1942c500081d800c01c540007030340900e0090345801040c001161082061591001540c140300180b43d800038040345100c014400054031035440e259241294403103000000d05034070b4500c40341e0420709886030104094410f462046101041003004104050303164a8060007440741505403008140350744001289081900b25040000a580d4620a404510340303024014002941624039085d01d4200b940c420640300018000a0280080410304200181c420300d481c101402c0083c2c9525103038206864080040d4019012580b054060341110b01100080241503605054008001c02c030340394034404031243c100802402c0781e4841c0c01500000b000e01c041a000d2641c08940c11001840d8013859410070500310344160300f1502c010483c1d0020f00c00e00982030585250000b0001c113510b1307a41c2d00c5400c2c041c1c4500b400c581c101990740c0d80 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 384646124 1250 384644874 384644879
    0x90c04020c160b040b03010e09030d060602151506180f04090b0f011202011403150316180c17071205040b22030519090b04031b0f0e151306 61
    0x20301007104001a107980c012048500d0f150360018800340528020741d0358661060004000c1005d20707100460704178004105503407408d42e00603041000e9444a4003c80c026038008044c0020303800030807010b20744c8060107031000192180c4c0b540c0060124440c00340080d0020003811800c015a640d084010342aa080c01801000781800303d240640b460401100c80c203000720010300000840c400c004809190b1282d059407412015400000000b03c203800c081d042d4820b0134000501c60b08507031010080c41101800340e1900c000c640e071600c005809000c403540300d600300c02400d140b20800c1e826002035143e09007898840c000340c15680c5000f022103403041004400c0100508120610045c44010410503004038000d004900c03e2801c43c04d100c140c0001c220304000c001450400000c6000c0c4001d0b001d180036803c2d0380c940102e4840d60b590b0340700c0c2150402d0b0010340744a12400e0070208061310301e5126000804131501c03500421490b2010b0303028070740d40081500c2d102200c01c20000e1090b9607042a01d03a00c0b43c1e8072100c204030168 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 384647374 1250 384646124 384646147
    0x1020c0f0c03071e090e0f07030b0916050d060c111002120c03040c09021c05090618060408220519082e0f090c0608040506070c0317090c0402 62
    0x1154041e500c1d0003406041e0000c0b03445a110000000d0751409014082e000a10380029080280b0283c82c0103d01c0317004685403100d0044050002e00001c500a440701140780c200341004506102c5210400803100c03150b15820000d40d2519254500721035009680001d000b68a001c0a80e0790340010090310001d0701030781510f07a882401030b6000d0000380c80b4000280c0c07601e82c0c901c501e8075a24407040c0c501510040c900c80c0f00f04051240c2ea001080f42c03040c00d40d051040b0000c18415403094550a480c040d440790000b02c20803040f84d2150740801a0040c80e04010320043c1410744400074144142c0300304e440c2c02c02d07151100d10781520490460070011f19003c0c181082c07451072001a04c4a40c0c0d801c1c010540e081c055a140d4942440c0c000c4020b0071060b401c1d6442c8025103805104a10040480d184000746080d281d0907950085485484958000c12a544841c552880d0903d005410001c0003424502880512403c0b080402da00510780c032200700407450ba81109403201d000c00342c40c0ca541110f1140d0f00c41e000182150704039 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 384648624 1250 384647374 384647383
    0x40f02090d1a0c0a0c1106040554100e040f03020105090616080604060314030403060c080c030f07020a021207050f03010b010203032205030d0504020f01080709061101020c0f 76
    0x50303410355899210748404200400a04c55403003030a00152401080f080824242e03403000c035858200401d128035142d91080850304004d0078400264a4207107483c0480c1d0b18132055010354844e6000e04081024a028030030008904035440c0c14000c510102110004001c843c1281c010b0000c0c1c02003a5580784189043c1c500040713008070f210402c030015400c201c003141d5454400201140900310100382c0ca1031040818608680809009014a038800d4542e58000081504006d030160050401c401542e651400d60070a142a2404c861004082140503820003840b00600000d0780c0e0022a00d03c202d601b00c0d02d07000d20403490440c1c1c50b0406544010035295540c01c18500155130012a00162050703a01080d010742050300300c030030862040d800f68100300005540894079540203042c1c0d60150400d040705c40c280d03859840c6160080c100583c2820360314414001035140015605858070003d18242010345030030030005000644a2258034140090300e005180081002e40540b441c803400d030030454101c000102d010603503c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 384649874 1250 384648624 384648653
    0x206030f1021020f0f10051804060801140708070c0b04080c060703020903010606090305060f13080c0a0b0c181509031605190807060f1418041d0c040f02090d 69
    0x14420700c0708461540c10405500c94170007000810f20041c444007101d0990341c075807141c01d000e00241b40044100712156605d100318005040d1440002590780c94040d412800c4040150031042030100311303001c01004542c0003811041d80350b4460100f201d80d8580d403a1a5001d4040d1809032601402400304018990f0341c564003810780710388110001c0c44201d58501084e0f40401c001d02000d007a41e002840000c0943d881c0a11340394001c030711811031000400c6162505000b90704060306003807003034009510513001c0c0700107100703115004074401c0c1005241c0114002110340d805150b03d072060085003c0d90742910591006c00075651040c9020f800e44030710240441803140e416840d40501441040986580405a8440e24409041d6a03003000140180c40c1001410f82c1d100c00115400f03000c001502c002c080c20081c0d4134025090043c07140614400b000040020071042e20702c0c0c422881500003011106125800001641d44a900c006a84c00500d01426186201c040d200b104129500800c44410441c00c101c2c1d0382c03030b20b1301c103 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 384651124 1250 384649874 384649879
    0xf06090309060a0c022d060a0e0f010207050d0308090d05041511100f0509010e060c03040f0503090a0308090a06020f070504020304020604080d080a0507080423101a040e0a0206030f102102 82
    0x17103242401d000c106083c048c50400c20001101051500e10328204982640d0482c3d60500466203040e58a07400200c5150612a00b1400501502c0500c502c2540400810b440a001c0e030030081d0804e030030408049055004070f030417402001902003004880c0f84041c805100f81041d829400d000902410b1400f102520041e00c64000e03640c6001c40345c1c00c6020000c41c94902450f0740030030309899500c0d10340b2600103603010700c5400c0c1d4660208101030b42d0300342d0f9070502d004000e500c40c1119541321aa000200140c0324601d52100c1e01f55003080701007031000403003c1005010b80f40c0c212401038a035181d41c004521540503d800c510b407184243e91100c0e1019070020300d0140300e90410f90081c0029620f052049580e99130541780204507001205141020508a00c0701c0c9078686040c504940351062401c403283c05907541d02c075a4844610085106052500f0540951794a000800000b84a004403a501290035403000601081ea11111440840c010089540c01003000340207281c3c8046031a00517045540d40714501c2e090407407 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 384652374 1250 384651124 384651199
    0x160e0a081e030412150f0203040f03170c0d0e0c0310140114182211180903030a1d0f0c041a1003050c12100302030f06090309060a0c02 59
    0x1841c0340c0001085070180c0b01c410009056800b880d90391550600500490206041d40b0b07007015440091407440694451401000142ca0702d40c954100900580e410001000c0c7d201110003c120301072036100c04855000208110002e14031800144560034084a48000c590501883c01d52038202d001c1908104510141d01c100744040ba45c1c3c03964850381c0300000c908880c0d0010f4081d002d58507010303003041555904c0140c0031840c02d918424a0290249200101403c544c0300d10003100c0285542003010b000a00000489044052414030000c101d9690100503c40024283c032071684603030064000070210352204032081120602031030300c1420b03901d890302403042601440c81d10a1032070704076070b01c074000924164010b0003440f0084486c0ca4114003a1800070840f00800c4c0301000034184407820741510a10408104034814800c40c1144105818800480145e0289030311980901c40f0640700402180c02440c1c0454005580d83c426101c1501c20342800318000c0c0d4440740e6042c480404080c154400790300340d20301d811840c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 384653624 1250 384652374 384652423
    0x131103011d0105011e1404110f1323060306100e03030f19140702190807090203090d0207030b011e0e010608060315130204020f040b07030c11011403160e0a08 69
    0x7044c1700d40c5140f140289a100c40c1c07000d032640303081507445007070b412403400340585ca42000b44d4015022a40841c60b201100303c48003d08100c5503000c554000a509441500904111049000150580005424988562075031551b03039086500413003810101c0003000d0180d81d00c540c0c030b04d08080b0054001502c8032617031680c84107068441c1c82c41040d00f4501f0540c40e01c4401d0a103800ca80070b101c640740b050b4400ba0001d49690001140c001003c00200b00200014031015a5a2420031180c9040414110710a003e6600081041c400200b0003900c0b02c0c152549000c00d441413001d0b040510981544a03403241d1080c046000006c5192503104111600c101e10a8080f103802c13101040003c21180c80856141080c030408440c80401441c05800520f0b441e0071604580d03003003a898210150966103e603d049012440c407241041c10020104203283c030300340d001d0030301d95101d0b202e1120038400c0f03100c020030341c1c00c00c600c0484c40c1c126614000e0014412458000e042c0020254070307036001031350300c80b01a42c0b030a01000081200303 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 384654874 1250 384653624 384653669
    0xb01060809030a1e02070b040f08190c03030f02030904060609080c12100f020c070603140906130b071206030503040603060906081209030312040308040b06030303131103011d010501 79
    0x100c0320112031998640440d0000441084c0364640100404821801000000a080d10069000e480034041d40c02ea941106841c16a00d54a07060742942a9030f0802000007500b0040744010b18001c00b02c0781c05042c0440001c107010320403800c62081c00512076225142040c0400c25a0344542d241055901c0c4000700d03081358090804005000101d400e0300882c0798401407803182130200b00d401c041c5106060100c00350400c07440c950042d050074900c3c0c00040001c0c1c1d4400e440381c42c03240040e41c1d00d0703000a80310340a402d90f41031103403202c000d500300c2210140030451118049880d00380f049001c5001e448261004101898607850030984982c070910078240002c1c00d01030049060307071030391050a00b220864402002d801038212040c00c12600030040041c0c0c9400184070301d03030b052a03001d070166205274803d07a14407500340b0301071070015096075000c0d185600a80c030620400c220b00e502e090b0350f060400e07001001014913480100020b4050b0038880613101a03507820300a869240c80054120174140c8000100c200400c2024881 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 384656124 1250 384654874 384654877
    0x40606032906041d0304081b1c0b040305160b040201110d0918060312020703051501080c040b03011805031803120319020405150a0233061c0b0106080903 67
    0xd00700380e46410003000c51558078265100e80a412400c0d800355041d4050038007410305503000703903000c031400c0d402c200c2607a0300040394603c010902e44070031580c81da815003442d07240d80d22036a40c2134002041c1d4407446011030207060040d0266540300c040d12107250001c2d003661070085000c2000f900c2c12400700781c0801c440d001071400861404040c614681c0e404800c54904600c400005480300c00303448850381c2d1954040003107107104c54030410502990300140909403071807030326515240210792240c503081038003001802180004505140d0070342d81201e001c1128007c0c2c40000340100b4000324105034030b010114555081101c0400a40004000140061040e07507188081c0b64840c604c540e0060035001c2c041000608001c10350004803e50b940d580401400d06071a00701041c41c0340e440d8020180c140c100411035041c00c590403c1007075295101041310a004001d982ca04400c8191305044280ca41c080c814005402a00e405203600c2c491250f4124240362048903090844c0d030700c3c1c2e080c01841c4c00201c3c00e50014509140010 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 384657374 1250 384656124 384656183
    0x120109050c04023f0403020703031107030b0129030703060f0509040c0b070507080d0509032a01050c0c040507030209130c020606060706150915081b04022104060603 72
    0x3420888091002460b2a180100d441101c1081c0005101c1300c800307501440d098035106074400d40040071403c1c114180034008520229032000789a1020000f480040c003181423460443c0c0210071100c00c0c441c2c82c10851030184030b181d05010a0b0280c0070080022032649034000308100c03040b640c1c0c50256a511a0305100009a0031a009010314050840401203402d8240050080034081d80a8807400c5032244450350900d601c050000d80019804500e0912a00d800d02500350000005010358509070507440b203090a0b0400c0107000d40c103105007c02c2031500d21400740700d890045036005000300075601c0c040030013400071340000e00d000340200c02244100014075050711619058052680003800305658a07010412258001c000403992581c650ba005180c414556010001070000b0000c0400c11104903038410307103005100d9004074601c2d801180445080451140c841501d00d40c01c3c1c4002d84d0f0f44d00c2c0c034a140250803841182107100d2507500ca0030041400407070f621a80940b842210703810540d01842e00038282024815 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 384658624 1250 384657374 384657397
    0x120f060e030d0c0905042007290a061410020a0b06010c0c09020408120715050402040b0d2001090e06061b060c0a080c070b15040609020c0c091008030301170705120109050c0402 77
    0x10172109010404013132040803900001c070340c900f08007140d0080c41442038004ad1410780c00c450700d601d02071100c082d4502c00f40d00c4100003075420b00041e5200742e0000395980c0701380d400901070044640200350b450f4428420721f903206400040c1451066940d8829000a40c41481008040c4c082c444000c0d030070405600884071304503040440c088010b13401e540420000c00000d00100d0784a0369a1400e200c094441d0980b5a10850180b41b00c1000300a01d2151b031410501b4105138581000716003034050207003103d500096500400300381c8a0a44441d80c08001c100300d410202080d04252007000104a9003c0d0309070000c2c040c0c1038955680239126150903a0750001030090010003007010f020a0f0006404029080c1920103804000300b01083e40ca81e030301611400ca0744001607140c0e003604101070500329814048100c40d0040f611014a01a040c9410b00c01c41d101c1c0010b00800041407a8624602405c440420440015110007405013064a0b101c0c08900d0003440042d5048806000d1140000c6141c03426100395000040e01 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 384659874 1250 384658624 384658627
    0x405030d0c0306050a0b03070e0303090604061b05010912020d09050f0d0203160b0706060f05150c07270c0207050a09090213021204020109120f060e030d0c09050420 72
    0x1880c500001501c0303154060300801d43c1d1008005410769500078920014203010410740c2e40c078202800018104150840d0040c00395000300220400c0361590b2040360304480035442c7c440024001c0c0095440d1600304241e0207003131503081075102007c0c0110300c0403003a00c5000701e07000c6500e1451164425a1144107501c65264812200c0030400301d1070826050b0030451074030003420340c1c1c00030030200e4482004071211382003114554008104801003295920407a000352040c26441024075140000180741d4800c03100d51307400701d01400b06030030302400c908004032009081c1c90400b280002000d4520314036010105000300c1901810b00410311042400407035103000340e450203440d800c160350511902c01e001d003a01c0d01040340c10600d0310050302e1601a4034030141100508082d15995181468000180301550700c0d089400c8203000710700c0e020b000803d0308203015081940b0003804500a20010301240c118021180c4009040742000455026036074008040c60580e0022641000340000c0e80e04009400c400100c1c43ea841c0420 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 384661124 1250 384659874 384659887
    0xd110d0e010507260306040b0105120604110d0204140901061b02092e030c06181406070b0f0103050d09030309090b0604120605061512311a01050306040503 68
    0x2c5100144151802910800506181c09800306483c0001000302e0140344008000d0142500c0d003400703550191642442d1140c207111100300e0b0110029406007003d071155075158030251200c0420815190310400348001103440b80d580e60052a11144000030091080035281e00100340b090107410780c0c0c1c1040041400c3e03401e4a803265420300a519001400d040302d02040c030a0008040c0310000c1c114081310041041090b0703814a5440c0c00501c00c1c4181c1c001c00e09004410442140c41c505542c0607104444400001c5032a103500540410f40c80e10455102401c83c3d410344081190708960183ca01e03041f680728108440c0110032400c41100c96182a0100400044080354200484817490700920701940300203202c1031a0a81d960400d10b034003144010120340303254844041040920300318510049540ea91003405250207262041c00340c0302403008125882c0e18240c094079511140c1c203c107108010080b00c0c00401c1c803040550400b02ca13115014401000302481c0300001241c0ca050100c2c03814052580400207604018 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 384662374 1250 384661124 384661127
    0x50102090f1e040915091a0a0507080a09020411040311240f030915190b010201111902010b0405130507080d08040f0f0f120806030109020108072307050d110d0e01 71
    0x5113404e000c0d1100200341c0500c0e2a00c3c40140305040c001071041f003442c0c907040c0522291078000b5400070705126030507142404021805030414141076100e0142100050321280900c0054000c00c1c48480b10841184086008030800c00d408070300304100d00040b507030518501060b030400303481d10402e00b040540e40a014000c140722551410007541c1c0299078102543c5096400c034110254482d0b0840701040c0c5c1c0002501400884d546501c20765541078001e20082c000b002806c0e8903c20b10380f04501800080c140d403100d028400c01e100313501500e000840200144101e0801c80102c04088490134002d0300d65002e1300b0000150a1400214080c8480300c52f19410400c1c0c0d5552200321051144800660b150380c0b080d0348910002d05507a0101484501c9240202030500308800b00804807000209500c0c040d81c9809844c1002d0303a00b21590542c44602e030700c2c01842c07484090030050300016110110050100001c80c8105c10000c1c0404d80c65115541d42c5d8035000c2d454100b00d075040e030306e482541002011980701803980b400b65 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 384663624 1250 384662374 384662381
    0xf010509030f09030c0603040f030f091a1c051f06050414060a020a17252a05030a0f0303051f03060218031509060901020a1b030318050102090f1e04 65
    0x440080c2a40c01c0c0401c100d0110b080c560003118100d90f0010001c242740c04140e00620100120182c0c0c0c68a030510320305041050151200b441c00d500004030001c14600c40004070b4080740c2151445000701444107007811400b04819010701f4080e0b03015002003100114041d44504180c8044502c201004c4200030030283c1404000d0740130300c1d0f4017400c5009142d55103002c0b80003181c0c208810703280001019920910300300082100303240251701c6418002c048404d00c010507501e01070355500d000811060848480681c200301c035031b81081d43c0f100e501030241d2002d400501840b1200c1c1c8000a0207a10240000e40d203201020010000030300032140b02c40c000300828400715100740d01800d4050400301c608041c26203001d00207450601d005a10425001001c01042070b0140107001d000d4001202d0310003582003500315400500301c00300b8034812000c0000340404c01c41c01e1511a0300700084100c001d40c0c1d81d6640407282e081040c0070394080b01c440780c01341d1103428107282e640c1441101414500c2e0100c507070342005142c1c80c0400010303 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 384664874 1250 384663624 384663637
    0x1a01063207210806040b0a12030809071502150c0a05120c07080301090906060b0a0e040b061210061b110103050402040f060603140609090715090b030c0901020f010509030f 75
    0x2c8144004460044203a0088404015689900e4208151a01c030040100b82d402810119029030a04601049a8046071540e11001030f17141c10108d40355541d0000180ca4211103600010301411402001d25415401064128180080886842c0655134a401000301c510031480001d000440030410b00f5a24102040034641110200400916000c01615560a0354200382c11440005950702e20b9002048107a00c6100000c00f40d031a2601d081080c900c41c09410790040c01902c0e4080c2e9103404604125a0700d020845135010001c507260f140d01e0800b07540c2c15403010494010034000c40d11012164030b2503442007152220982c0c0c41404400f01e010036000440140c01d01400072a081a141e070100d0360180300d01c0c000d030b00240c20b80d035400180c243d504240c0400203840150034280515001030074800500c1700403840400b518800083e40303018211030207080710407103503541c0a4cc46122000c0700340448104880020817400740242d0864401c503c010010314201c620a07552050f03c0e60003046995003021840014141 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 384666124 1250 384664874 384664883
    0x30a0c0305150306180106180e011a09011509080607030e06070e150f0c250608090d1103130f030c0503010509071502030c030c011d150103031b1a01063207 68
    0x281c4582c0c038008c4404900c00900044281e94542245405c090000d204a07540070035045442d141c01c40502c1d0100d10103140c1030180624181002e800b03c181e1130702450f200300080008030222800303440d102c0030040c000c060741c084a030070602840b004140301038810303003802000c3d81c03000701341745807000d000c0c9a003142c10b90288250b90110b40013400f580d0600c000038040c442c100c4040d0300c4040c1c10f4084603d000c0b12140c03400d8220b8010310031628180318035000c000500b40001c0351a81404440038401d4000c2c1880c42c06503c40955080d681d078500803078803500814424013220b00c03c2941d400143c0c0c5500403d4240c42d0212b820383c0c0e2951015030300b0014126559103043e180c45d06401502d14080c01503a00c1070960340010026800c42c0c3d15801c0c0a154504440444181c055040010f411781001c000c44480c0580010300c005004c01024144400c0c0814422420725021076200745119200c2c10780418404014800348a0080440da0072070307452071018601c8240486528182c0064a0600b60040503400c0507040340d00d0645 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 384667374 1250 384666124 384666131
    0x6030f1a07050403081c140412080901091a0405070f1401080a2901111b1c0510091e030c03020c0406080a26040b030a0b0409030504050616050102030a0c03051503061801 74
    0x6020314840c0784d07d68040d80c062100804400307801400640b00150283c01941c0c0f582c54071440e1404104a03084044410106035605003560b00c40341045494150f66030030924440c0b82030b801c009945014500a4402100280ca461601d540d402d4142011202044003550795492079111400c4503061001d4006012001414249101a80c0f089220310700342c4003910140c414018030302d1144503031a007560009880030f81c030401c859060040382d0b6110740b2000000f150003050f6440c0c2c0f00140402c60032240b803480f00120380320707030340d50203640d03170500030121000307000c0036800340c041d0050b21b80480c02c1c54007402c03050b50b24070802080d80c4c1d08141c1e12981130b03502161044044c01402816586806218030041c0010201141c0942c0c5a041a4402004440c18a00c40c40d108034580120103001a402406031400c1f00c0f002c58003d41c60b03255806100c910580000001031041d4030000c100056502c0356407202a006c1701a5a00b040f8940e55048020b06a0300c210310440c1e41a0301c14400201246040841224941552000030 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 384668624 1250 384667374 384667391
    0x1c0f031e020a020405130c03031d180402180130060c020618010e1203060d02040905070611160302090c0c0a030207061e120b01020106030f1a07050403081c 68
    0x209030a0002100080058201d02c01d0340095240501480f900031241107210240f21020307a03140c5010b191a488010284910707661b081c001d0b022411114007841801030030a04000380440d41d00054500c08540032446210380c000b6a83d04103003040980c505a40f4084111481542080c1c01809400002942d103220181d0882d0140000781c4580914616510701c2d030010300030ac1c10680601003040b01c58070402c623000e078903040420074403081c0021009031101201e02d10303507030329111400030800426a09001075046400d003598041007090000d0305008843d4207a072a02d1220761001002e94581da0009806c0d0641c58604230b06001514000d0b901c150404550303c0102e00d4110b224800508011038118282c01580149004108442d005262700048042850701d5908103428050b01812108440b2507801d450b035603a514241d4079034008d5109901a680110140922462602d8030300960410300754204038002506000c2034040d80200103440990783e01502241c03c0c601d181ea04000446008011001242d4449074807 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 384669874 1250 384668624 384668657
    0x1021c020f04052101060e040b06010e060403020d051e011509050c07050d030608010b060307081303031d0601090f050c03040303020708130e18070b0906030c0c0706020d0306051c0f03 80
    0x4144c40d290110810300b4180c02c01180c82c2103440a40c01032141c1c10803071702000000741c4107045856010a090900001c05404100420018051504001d4210074160300c5c4405005c40010b03042510008040702d2412008a6540380707003615445050328164818a1070103000b084800d400090341f2081411200c4d040954541390709180c021100624404607984001c20300400c6000e000c1c51160020980728580b46080018004000450052404200c694000803030740416109810642c1c5426001c000f00c01e925566454081e01c0390400c0c0304007005541340003503403010360006000c1c0902c078002d82000542140c0d40d940f0254080e501c9088100d95400041000303000d103040341c4000b41c01500a40a00f614945400e10344034100d032500b16000301c16a0720103d0100f0900305d400f4101d03240c0d44000e90310740c1d80b2500c64031045c80c428042c0c0e00724042c1c58040c510010400b01d80c0066410010303112580c040c82041e80c0d603020300070000d054103000000d401c81e0948040c007040a8240c07114030207100749002502c1980b01e600 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 384671124 1250 384669874 384669889
    0x6020c0a020d0b0f010f0e070e04090821010909030f0807172805060603010909150603081c02030601020304062a08130902161b18060e0901021c020f0405 67
    0xb42110510400410302440200d2022694007501d1410103000e50b50b41808204507400200070010010051b140c000d0740580c1e140da821840210b6403140003151a110900303040704400c011035002240202000000090700d002500511800d40d0701034490b048400300c8014103e27460b0f50000e0101080c0500d00440304c20194072a00d040740704036001c1c190507904800724580d084204458280102080d07040c01d041c442e417036039101d00b103a044a0380c3c0d020001d5400560b282400344440c01245603010f2916041c00007043c403003800001c1440c030105609011034880c2d20015081240002c1d1102d0340164001e10040c4000e5001d07001031111100c0b18208010403a1380c014400f00e0043c26100e08035100c80c000302d81000900102460840030703001e203000540c103140c001c0000c036024250080e00035007160080390b580310381d5400100308200030700b03041c03101c102490f4000c4a1810284c18244550520121010001604124103101303603209a180c5200d01d040500c600524007001c0c1d0440c40c5091840d403400c0000080c2561184c2 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 384672374 1250 384671124 384671149
    0x12031501141908011a07201203041701050c040e040b060402040305030a091505070f0609020d05060103050c03150105010e01030515060d0e010b0f06030a050a020f07080306030d020c03030706020c0a02 87
    0x241c84010540c10051801003158003000402012017061000000050740750300c00d080401c8460154500e540294000907514255844103c00381d4000010042440540c40240c015001c008500910240d1603010b244090740c413840c85003503c0d58011030080340000d0680038201d5006000204003504207030b140c0d201c40f400d541c046904c40b00400c1c0045d400b000300410051158030001040c1c24402d0070b06801c2c0e10b40c02d08221419500502240d61120000219075850703580011458124044481035a1245403165441d0040c0c603a0134800d108000041d08289003403c40103050705c8042c2e4584201c0007010005501a004c041c100c400d80759031001c50789040383c070344001134001e44032790810100304050010240c508550829411500590800c1c10392041a2a00021207810400b600360000e055912484400024001d008207804144000200881404441c41c003850241c401101500c42e144003071981603a07107504d100701082d00341e0028003446010940d03075809803207203c1e03c02056401c2e82c4010f900180385000280c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 384673624 1250 384672374 384672377
    0xc0703170108060609011a160507031e11030a030e0d0201030902120309150c07120f0203030a110c0f1e0a030212070303020d030509190812010e0702120315011419 71
    0x10043d00d0b140c100b070030701e00400003d40c1040e0601f20684065016100d02c8040c41c2104080e07162040030402c040010400558100003411201c203034800f600d81903281c0c41340c0c1c25199071020b03a0800c3c6440c078000c03030364181300c50303150311014080202035051207686000213005a0500d03a403074000300050f8840b68500700440d0f801401030350755000400304125040030700f14540c8e00707068424020108504c0d00052070b1000d039201c43d4088101501546483c0410102c2440300940500000c62249401070f04810802c007809030b41d400740ca02c00d03510182032203e400c1e07049003200d50142080c215400b08081400c4c1e00105280060b00d107491284d182e4020540318441c11101100941c0302d84001c10906905101c811040c00341443c050100e4107040160316a21a6080540d0f414110942c9181c81007016220807100c0040e01e42a1060403580e50f2085202e0703050046440d980540240714500b40c4035035042003180d10880f0410709a28100c018680110340300383d069155036869450400030900701e1000d4803002c2072500321a = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 384674874 1250 384673624 384673633
    0x10c0b07120c030b27012702040b090a0b0a020c19080106240f090510030e0105070c0501050109020f070b070912080903120c031b011b0e0306010f05090c0703170108 72
    0x30024442c0841071422460503100703505103c0340007640d070315001604491a1052078010b05c0210038000c07111511020187c80e003d8400540080ca500c85280580080175048582a060f15561175020300b46d4030413440a480160406a19003140c0e01d440c12124600c101340c2d0740b400d0500c58030f812500342100c0030343d004064040900d812003101e0019101c46100c1c940c0c11843c01001484a07490041d102134500d0003a07603c1032a8810746a46a90f2080e408100780701c2070b140080c031450502a03005050044800c505480b00d50a1100101c0da135a414002c542401c46151422403400c28284c494410a40300030b402c1c3c50400119500000e000250340030469091806604003a548034801c81c00c241c0b42000b00078540c15502e5090103809280c2c54040241d8070b803850a060042d800010355507042e0700609840e0f618014402c0394240740c480055000c6e81004002c90300341c04032226641c9402020590300a148285684108032000203070a816644d030143c00050700c0b0307043c00982443d40304846c03060101d090f00f020150398007 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 384676124 1250 384674874 384674891
    0xc0102070b0f1f090f151502011b0e1c02060327071d09010e030a020106080105060a0308250b040f020405060f0a091a060f0307090f05010c0b07120c03 66
    0x70307521001074000b4141d40380304048050310f2602c600000c50b0351080380741099541103031841c1c10186422405102060b011404000d584414505800030b805a99160066103000030341c641504181c1e042c48115101c644030a03040c041c0b00c3c0704010b002d1284130100d40103252541000c0c0010313200e41c07000c4e42c01400c507980400c4103480130000407000c0b4010340303101414940c4000406c00c042501c01c50109078540c00d0304555041d56903401181130240c0385d240c4940000d407200241154503581d0643c410305c00c3e510b03500000d04c80d9407540e03010445c1101c454000136100c401c00308400094404440c283d2044501d001d07004e0030140110343c44c0d5044040c0100d900303039081b1008802d14021403400b071003019031151007295803982d01c040710310114020105034016048503d54071541e2402c4400d007407a480c1e5911800920303003035a0394245400e10625800907210400840e102d200042341100001950500b900c4044c4d540c402441625100d01c034078048060100001d000b002c00c914141918180190300c4104800c4c1c901181180 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 384677374 1250 384676124 384676141
    0x2001020c0d090314030a0c0204090623100608090304090c02070b0a0504090506010203030f01090b041116020a0e090a081813061802040e04081b0a0b0103020307150e10050c0102070b 79
    0x2095444c0b100076a00100b001e45440da0b00704a650501c2501580c00241d000a1303450110003c00c06100c2e0600d1034034442541c000940d014186041c45501707214807102e049070381d03240155141081502c2040b1a600180002c2c032490003940d12030021a041441100c400315034031040c200042c1e2002c03c410300040d034001401c2c40842000d01450360008420b100642c61440c166246602c202c0040c010b80c2105600c40070911070b10b41c0c81d82c0000c4260403140711039076070b02c2c034401a2028100c0300c4204100c1c0640c03a88000050f244449199140c032030800f00340034200245865844102d540d220b4650f0100c00207239101d0b070050300d449e07140304001d50000a0304006200341c240f4845203600c4070740c2c09151040e54010407041c400d03c0c41100d440f41e00140e122424540b80c1a4201d0704205003005402419024403600404c1313828005500a0203040700c0c001e0702074401c141c1d107507103482120800341581a00860301c1c140d800055400c0c461080c1004503070750303d000350610581c01c0c2600e00366400030380141c4d0f01e001001d05005004 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 384678624 1250 384677374 384677393
    0x7031e030801211b08010f0902030601090c05030403030b0118090212010e010f09051003022701140916120509030913140402130b060f0a020c102001020c0d0903 70
    0x429580d101149403002c940380b00d0603c080c45a1008184506561001000256525a280180c100d0320001e001140b4901d5800c40100500001a88030f8421100000380140a030f10131940e2a41a50f0784080c07031a9260788003903001d0001904a103040080d0700c002c000804100400c044040c203008003002d40d5031203128010101450341a0040c44903400040f00400c600240402c100b403c460312a880130071140c4d00d0381d0b110f006120240d44003035005407010307016818201101164200c43c48100ea2041c002ea40c946010301c080604040d40c05420664001c081064080300143c002c004981a10b880191034100801b0b48041e120f0640c0c100c4030a50000c42c10070164a88178032040704c07140e4007440801040455052104450300090f0020b8002e484801c10300b420b40500f50000c0700e200902510099407801c503484001440d074032959901e401401014101515403802c1c109a0071540c0403075030340710009807a440d030400c0c4040e03810700750701c0d5503650810141044420901140002a40c9500d52141c1c4c40e2960500701ca40 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 384679874 1250 384678624 384678629
    0x30b130b01060f08061818010b06030c0403021f0903110f030114070212210702030f04060c0309090b0a05040e0f150609010605070b0708070e0306040c061d0307030f020307031e030801 80
    0x20b0002c0e10085c4000c111b034402d450340c08116070203405e100401c010300d0a4010708450b50010f4002c0c40000c2044503141c4680018021280b081d0b8940c3d500b00070b0b0302c1d81c20510036622034248000a900000420101d181c0403003082082500601e8070700404240c00c000383c01c4031403101c40094551446400c10483d15014460401201007030b44910386005400c010518108400880c4005003c25400c089070a09100b0411f441e83d0100e02e401c0d680da43c64655402900c08400c902045001900d02c40021407441114042c41322081c4014008691345418001000098101c00c220301200e88075035442c02da846d01c020001003032140d9441d51510924107040007170140e4218160004001d1180401c0b0950000d04030452066220301d181c0740c560ba05845e032000c1101c0200003e03910a51610411081c8810302500111102c1180d0061322401d4009000420070510300c64412a0158950800b0034100041400b030016000f4551004064503c03658482d500d40c50203402c4035480c801042c01d8881e04108140d00500101c3c003 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 384681124 1250 384679874 384679879
    0xc020307020906100212041e060306080c01111f0f0f0b06070609020d230d111f0906020a11100213030201050c120d0902040b09010609030b130b01060f0806 68
    0x58000c80790082030002101400350b40c0281d804402c1541c40314400e1140e07000c00050040d44a41d504d60b14420920360521040c403030b039a404040040014141d0081c880c120440d40800081c1842041c0e8100560f000d158a15920100c0d000b1304480703000c01d0040003800380044103c0400018140c00f1a11088104d800b44170b09155041d140c1144c14005a035101300762000d0b9a4001c6002c946c68245e440030424945403000000c0c09409800524040c400507031620303103c03490054088441000000000300c880801110380e80510340c02560310080c2c0043c10822900c00305c61400d8000c24881440c1e40c80c0402c0b64421203a03040054215859101075420500c0090a00c001007281542000031310010301000d01c66501c4001c0c1440b2001030044800b0b1000c1c0310102421003550100380c0c4580420140401a1148010481c4280d14050020103549002040503060b10050355030500400d0942d52410f500381c1000c1c0201010318101e208440c0040c0c4e100700d03014082c021a9a441501002170103014090307505c0a442c031403 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 384682374 1250 384681124 384681127
    0x507020a060b04051b0711040c030507081b0301090209030f12040e0106030608061909060504200d12030902030f0109050114090606030c0108150406150801080f0c04110c01020d0504060c0203 83
    0x2075440d030f0701017045044030a10a180390f4508292500c036030071600081140d0b400c5030400d5800140c10340c056000501c41d000d66181c0314400c0c0d58040310301030100307103007616a0403b0b002880188486299a4081c00e20464050110b070340c1c401c58100f58602d4120101010801a8800601400a501d03820714040c010300d0305090a010550070250a00e850f0640180809000d042c1c034100d40410900c1500802d0956420075020480d900301420402c038149213215a400352a014082c3c15900d41c203126150702d450039007102d004003c450a0103006c030090068048180d9241c8503901b0a8a1030400c284038514282d0700c128000102c1115810700c1c0c20410b040141b200020390040d1081041c070b51000704103010381820134603019030309a80fa41018040c0c8a001400f00c1c0c0c120f85000004610425410b1240d6010781c225162181aa030317881c51959540c070050f044016081d040b20300810b80a04258002d01404c0300c8100c46c05040003004003c50742280c20a0040c00e06a41d2128140b0040c4400c911414440d10403034406103 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 384683624 1250 384682374 384682381
    0x7050c010813030e0a050d0b010317090108061c05030f090a0b0a1d061606020405040b0603161101020d0c03020304031205060a0311060c120a08060a0e010302010c150507020a060b0405 80
    0x1c604603022400090140454880c401c52156220017010028000061031000461801d09081101804c00d000c100c4021030061202c2a41c0e17105503095600000e016503401c070090362050140414880c0c1981c440904590407108140090f00a00c058845881007051040e20f6091440411044c2540d0342e1081c4058141003005d0032060ba03110701e1044409146a80984116901d031011030b24510844c40c00441c0c410310b111442d010001e03aa0024011100b04440c04c4c800038402c0710800c46640b00640b1080808000c0200c48030344540211450f203484100180014204405415248140c6001c0d01c031800010341d00004120815030051000513603031810441c100958a007100c08195a20386900016044181d040c2540c82660399803021200c04e2100c80045c3ca803072000030400c950302a004030301100046030f90000000c2c03032400c03c040108110303045001c0c4145240d02e0740d001034070552030ba8403003610300e410200e480081346100c901900f4085e01c80c5500606c500307011420043c00312408804694491800c03c02403 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 384684874 1250 384683624 384683641
    0x60106050f0d02031302120106030309090501052b0f0f0201080709060206180c040e010204030c08010e1e0f0607020f0f07120219033c020904060209010212030c07050c0108 75
    0x240c80031142c0c18480182d5035190841030060000d04210020340c400700406800c0c020000c1908404101e0f031003611680b07440c0c1c1d1540d01c00c90540d1824001d090700304402c03141d991000001442c80d800601c0c90a601c0560054036900c0341d0000100c10882075174101d1806070090215607015208990040355407800e41001801d103580291501c0010346424020860410781c280b01640c00e01100202c460b0040007049141c8072030000078041d40040c4000d40b00348080d1480012f0040b810701452100038400e2000c0d00c41c05802c1404a90503180c401c1101009201f03c45002400010070001580101150780003031003046210200f0a140051103066407040c1e03000400c04104141440520600d0998121000c210910300700100c90b9440199600240144010095100a800448014109030f401a0b143d0040c01c1d0781e41c02c1e0180301c9140c1d00c0c20080d0010b0f495400200460300560180420301c81c140b069880e801c3c2c2c0c0141c120802d403c2511029040e074800035802c030410104101c0300c0085c14007820301c0310701c52614008 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 384686124 1250 384684874 384684877
    0x6060111010903200c04140a05090d020d03050c120702011d1b06210115020c120c21070803130504050906072619060605091c0c170a0302060106050f 65
    0x3441d20100021002c1644c410501c0525150305010b0802c0111544d4411005c41320513060712080911031410011884a280210b013681e081003007600113101080006500f1802450000c08140408205104240c01480c4c1105020301034005580040740400303000100c51249c1000400c0751052740d100d81078500d82d000040c42c020207490400c8070883d13140c4080c090756480510390340b14403141520002c3d00220301e10b095501d400c90200b03550381c21191a20152018002101103076494100150b124841030035180c80c00e80e058280200301c030f8080152000c6021030062811800e500b01d0921500081480014513900b04c42040017400c0440c0c0510040c10702e02c041d9903c510300580700b00c04001c1e458885901410101194441010000c0c00070b01d12490400150402d003001c02800e240d42c41d05040e00003c02601c110196401550010030402c902541018212b007400c0707100c0000c035100311f200c4900142c2043c9490301f2a010a00c0c1c3c03400380500307140d240303002410800c3c142c0000703007800014040100108520350 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 384687374 1250 384686124 384686147
    0xa0509070303050309031603020a1505190f060b0d0f050c180d03030e16060f02070605040915120602040e100e0c0903010e070305030a0e09131b1706060111010903 71
    0x5042d0303542d0720f0b4034110131b00f58410181030090a100111241080640c0000c1c10f4040c00e0040c02d00a840780a0f0a00030b8040d900d050b6994194032881c00d00e83c03180340344950701503000c00d0390b180c000051066803400720b10195044820303100265503031150070000009840c01883e81c040c0100c80c2c001d1601008102e1000f9800d0103a1a06004940e1501e41804050007980321406241c0d0310380c1210404007174103000d0004016107024000001c1c64085c01c40c04002e00000b42d040980390700c3d45070141014100100d80d0700400c00d80072210b1940e5143d003000504191006420314415000e0440075a84500382503202c815141e0203401842180c40c5520100010b00b0355008854024540b64075003590340c221040000d000d46401041a12140110200081044000802092503041d03944411048038120f0040200440c02200c4001ea540041c0798070707500041e680c50b040c4d4030340340c014140d040c04161104080d411010f82c40071b10101700e41c021010b201503584c01818512204a900c0001c1c0020b40310f9075001803034285404d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 384688624 1250 384687374 384687377
    0x909010b09100e1c0f06060305010218010c0c0510090b03090c0301060b0a0f1d12060f06010c03020a02090903120c2106011e2001090c0f0e150301060902210a0509070303 74
    0x811310a04004108081250756030f0001411b01c07070703e5281c4c01e110b8004d5004010003104580720420041055005118001c49190400340c5084c02901d80b000780070202600150704001c0040441000c82c1c10805a8040d500940f4024010155502504c0905003140e50703d03040000d54003010700c01e83c4809075000d48020006038035484c06080b030442850340051640800707202241d003c094801201c4003280001170b094821025110040000c1d21141c0040d558040c44140181c0143c0000d01c1c040c02505081203501d03000f00c143c138116840c0c510310220740007510000352100080e00400140c410b107004041c207141154176a0220300d50351103080210020308400221450a120081080016114180203030030380740500000010149801404142182c004c0c4a00b18003210142c0c0b07543d8020454188414010042d00c4403220f12210340d071a400c1200e809240706102080d415901da80c0081012105800a41a01e10000c42040c9034011606042c001c000f034001c0040701264035060400650980009a91046a406 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 384689874 1250 384688624 384688669
    0x80a03021c0e03030f1b04030b04080408070303051b06010f170c090106121b0f1b0512070b180309060c030f040b04050a06050c0703020907050909010b09100e 69
    0x1030940e044400d28019410076079500e07150080460700750100085200d010014045412681d408440d40b009000e40c0380005003183e0240f0060002446002005400902400109007050365403c035030703403610004d03803c12000210042807050500864240401010312490b010f001150306003c00c030a404c0c0d00d1072040f6904400c4004043e400004c06008070500000068105a1a0341c1c4488010300515040a040c64140c0d28060070816101e1a80540e0482c400450f40c1d00c2030483e1011104507443c0c6070309014400340c4d0380200d4000c00001c42c2004010b065042c0300d00881d07120034a5060480070450020302c0c03c1d03251414460740d90b034440004000c0b20101c0c00d08445260f10b944486078202d01d50b0041a000b2106224000b9010a05041c0800544101c1c1c0b4100c3c2d416108580300c050485d458042c1c13065000c10366204600c02c0c8014503000603010f5006503146000760512040c0000511512002c0e80700088030480099031030410b0600d0a5140c4280006040c02310340d039990400410f4a4050040d450041c8450 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 384691124 1250 384689874 384689887
    0x504120b04020d06140114010810030807051227090712051e04110301051b09040c03020c0610050405012106050601030b06120601082805060111011d0712080a0302 71
    0x260007105245107a00130500304100c0c50384031520b03200e050080c0100250914003049007210341d072080b01c0c1c852080192039400c0b100c081c510340e80e503132031604903840880d0140109480c81001100c60005441045071440c110522501000d961a100009060b400c07401100d091003000012a00498500045c480040e070004055852031074180341103500e88411001410048140f00a00000c007184060f0507504800030821a201d041c40f042e0b8946420256540d2040144411000303860b1940c0440800949401c02500d00407075120b040d81401c1c03040754054800342c0d0003c814407960510348546030161101d40b4555010207094903039016135810450000300070a45030000142d0f141d202e90030112100d43c0141c43c4039101c11681e641054030210458a590000309050000b51b5900d82c641116050660740d10828801804850004405000024849814040116190502d00400b4400c074111440f240b00c501c9081841400b00c1800c001941e4006602007840340858404583e0349411541d0440c4a8100180e5480 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 384692374 1250 384691124 384691129
    0xf010212071b0906150c1401060f15020606150a17040b0405010b010e0d0605040606080a0f030311030613180c08030702010e030c0105191116061b050d050f0f04080a050d0504120b0402 80
    0x4500c55075147e0b5080040000d03044101105240c00d480190b0741980403d000400b04aa071028112010382e4071500e64000c04010b414500014461004c0ca480e043c2140c0120f1207988400d08070554007240c0e07000802003088140102032041d50b200000920b000c40b00c40c0ca0f418001040070102907401343c400740e0390702c000c5400c016444d40040010040e1600b84e0343c0403082070404014804107031074203a0100b41800b07100011040c0340d0044034890940200717040f0303144c10701c80c51490080481081c806409880000c00c0d1020910124102e0b000b011014002c40d513482c0c1901c00141060700c0f0301084d9000750702440400c1e800e6a04001980d0001440c003030032901c0c15000b40e5007102c0203040492403464a01415100d060741d07580c07c040c90402d544107611105500c4000c070600c000148c0c51018040c10755086401501d460b284108020284400e18100050a219001c0d60301400d590184c0d1007070705a0741c0601ca1000411034103006201140c4d641d4104542460f00c0c0041040400012034030050075005c44900140031503 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 384693624 1250 384692374 384692393
    0x10e011209020d08090310110409020c190c06030e0106030f0212101406120309010804140106050a0801020403050c060c0a0602030601120213030b06041a0f010212071b0906150c 77
    0x280c2e00200100701e070702c41e1828900c105602c0035804030700074003c000145402c80440c0c058074500558103000c5903e0245820701c1c5000a400210305803900f4000c03020340c42c0e24403407111005556280255107680c4034525080e00034040380c9183c1c1460303140fa41001c2082005c268404045200c56805692014010071404102410300d41c00c48ca909811624107510b507800c88028048041c0319020507141031304002072584445640e8003d025486000030012400900015800e425a00101c5c20020000c82c51585417000100b20388403540001290342e5001c907040003441400c00501c41303501d405445540c03a042c04194000e4071759a2600d0040e0440781c000011513a2039109090320751811100450442d07ca0419803403440c030240144c401907409085c0392021400b680307410320641d001ca009600b00039078841c000030240407900c5203900c403681c158013400c1c040500d0056140018a1424400d90b004044006d840240d102c22043c03d4200c001c805141943c1400840ca207000c0841e00302c605400d00307120751503240c03502e46000d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 384694874 1250 384693624 384693641
    0xf0305090303160c05010306080307060902030f101514062d071a01090e030703030b19150f0309022209051c030e1b01120608010c0f031505010e0112 65
    0x40c440003c1c0060b400342000400800c1034402e200c0444c880380d8410044040c2d0f0035a0248103110f8008000e480d00190301039206940180c40075094607204405803a08504208030280c855642540b542080c078202100d0a401e08040c00c248201146482c1c0d01c2c2e00803031028011301000019455440d001503001070b110b2003070391003105525022955144650310300820080d0107005034407140c154007800480c1c00b144030b00660103810361100045050440c0307524100e015149041910381c20a2680c400d02100b280c00d000c1e040c001d0400e5001d054100d0844e414000d0054001d0381600c410103240140c1d000050303442c03440b0040074821400f0100902007650001d10000c066001c80140340c4d01c154a68018081da80c00d007030400c040c036284c170100181003030030003040d85170400c000d540741181199600c802c8180d0300402d0715640b01ca0503610b00040040e1030360602c6086031001800c0303101042402c04440c146580c03601401e14a00c1c14403424001d0140f801c2c0001e404a12410900381c113100c105da0003046906180d46c03180c0603 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 384696124 1250 384694874 384694879
    0x80901050a021218090f010b180a090c03060e01060e01020303071d040905010b0316051305041a0a200a020d03020d111c050c0307051213061a1017040f030509 69
    0x42e60108200c801d6039941d075800c01c083c0205c4e803990000c0c158158090b5414100e90201741c0c810329018603504850521905012915400381c0407200c08600013480c0d02c81c20440c012503031400a0201d081a10743d801a06050344440308203e100c0104030b039a640d000c0f050340c1d084100b0741406d9221407581190104039201d074503a02600a0b16200c00c4106200b415001041d0a0005400784c80240100c5240d059506425020300d139008040002c000040d0b80040e4452644a801464081e0501da45010220b09540c01a11454a540e4450398000383d00c000390200000d40c00305000089142c5288004040e444e64050000001450fa000c605502442000d40054000c20084030115a44064403400200384543d850b0042207020320b8a0001943d007904a012640900160f80b6110304140c0400e400003040fa20040901c3d5000040d514a1000582d860054421824103a10300300e00ca50100d2060164031072052048404000380508401546410031400640141d08605ca4403000701040c10190348920a1030881134 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 384697374 1250 384696124 384696127
    0x40c0e07050a0c021810091802030a0f0f0f0506041505070c06090804120303020c061e0a0b0d060f0504020102150622110c03071118220803130b060409080901050a0212 73
    0x4000c0907031b4450750a0b1480500708120f03001403000b0a211010469000940581c003460650b404140100c1d2a1040180f182030b80b0700e0f401c401070f0740e031302d01071071081d2422203071035001406010802c502d822500f501c0350750240b0f0801017403406210007021000000030140003070340d0303030003001c014007030f03a00201c070050040201c2c83380c0c1c3d610441c030b0014020b40c4500c1c0560054010100420509201101e24818081e004400e140703442e11440940b1006100c15110242e0003001840180002001c90107006815112840000f41902c3c0038000641014a16007050458038494070030402c00380e580d00c0c810f140343c3e080035115152078036021004c1001840030388a407194005001c42c88545480740000202140ca119120b042c21010030001404140d442c40b0721785881b101290000513616410310701c00b60701503400e40c00040c201a00c1c5c60700c0c0d25205038004d40c2c001c200b15036003550603000e100c2c51403041c980200080c1d80c00c0191140c2c42d26100a980150201c4038100900092940b1030984200075941c030001c0c00c0c1110fa03 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 384698624 1250 384697374 384697381
    0x2070f051b12060f1801150b030901051f091a03030d0b12010516050904021b07060e0312030a110c061303030509010b01120c050d0204030b040c0e07050a0c0218 70
    0x1101406400c00303403184200c0038412064a09000803910901401441030701d013882d034581001100140c0b11341809454030350b40e01d544507540042c41004c00402000419442035985c101450b000d404e45000034200200c1590f00c4481c6150800c50140032030031110b400500050501a07003040e811500044e40c61507500d840701003501303240482c0d1a03002c0da034002d03011207080070060808003505098a90441d5620284690b034105052254007400040502c050003d000502c0c000302c404050307407510b89000c072510140e4801c9c241802002c1e006111031a03030040c100c1c020142400202c2c983c07106488014011012141c41d48042c06107204800d090f2084480080c00380d03500ca180036840e80c2c5805520140c1500041d05081c01b04905007018480d42070f10f000103a41d00064003d000c080c0002030914002907900704003040040c040000840c1c406000954400c00c41c00d0010700b801e0a00429500440d08580d80c0d0a070b801c41030064180d0044101ca900c2c40144c1400d0701000814000034002102039101c1e100810000c1c000c1 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 384699874 1250 384698624 384698653
    0x1090804030c06091205030415050403060f0f0c1403010b070c0314061f060804021915020604060c030b010c1106090d0803060103140105010e04050916030c09060b03040206070602070f05 81
    0x290001c2d10160350782c1c850313500d80d90b615903d800d01034140050240d800400052040424980001c070315a181c90420514007580c3ea950b04c811640c0510b04099000d581d4a102c4409031490300422031080070b01e2402c821840c112004c02092440184101e003d1708000190b0101009000b81902c00115005407101d00110201301d0001d440391341c00c0703420080c080801002e810740114009000c4065844580d41c0c424641c0d00c507400d01030702e03c1c08060310061899040d900021096400c1c6140c4a00080550145c1585d00307140c641b07030040d80d01255125041c581030010300038182e46d110a402001e40d8200c840c130380f694821000410101d1294001080e042840300b20480300f405a5400118040c0000b82d03001c11050b2904944811141c000307000321030014120b40a015030320714150304071503000024442618041403040c11101a22104c96108640100268204001c0c0940702e1180348000c01c8945289461480c080c0d0010b2031612485900400d5103034003103802410320074040060f071406c0d64044201e903465514041e0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 384701124 1250 384699874 384699893
    0x606050301090c03050c1207110304060c0b0105030f0d050a11010507032f03161209050d1806080115020c0d030306050f030c0609310f0e19020609030109080403 70
    0x4203002941031080c80c1e21014803071700c1460b10845146400d2801c1150702d504010781d03400003820040030851000180000110144005c100802c0d15803a180c40d03205807807520205e80e0005030b00480c4260014170b4166221040814944000320303030740c40c100d66039010f10101030b02c2d0101c1c2c2040710150b561030101000081c44c0c04d94130052007400c07110032010400440030204002201510b00100c03280c0300070300101d60ba40950229815a1410f18281b04205030100041c5004655075010b051300c89610182c007441e0942d420003c032100340c0c690903145800032030804c080a1320801042c4117044102c2104000c00c002d01d8424050307029181002000c0c174802c0c40a030706004000d8444c81c05001c0c400d903091401902c0500d40080c0402416074040d03c520308003806981005034140c002980402c446007110300070008114160301320b41d2404a003000003c1e0582070760390703244215002c10515042d982d02070440844a441e4410706048407a0741240c0c6159940380a50210340500b10641006022031000304021081026904 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 384702374 1250 384701124 384701129
    0x8030118020702010c08090109051203030604051807120303061809032c09040c03050d020604260d0504050f01020a030218030303011208090f060304030c140313091e0606050301 77
    0x54004018549440c000102e10403040024042a4029210400200921301a040f5400c2c141007407081c295540c8007107901d41590030f012140e80c3e0800410801140fa2074400d498001c0c20703e0403039100c000c0c400c4864556984040c05103c90f24006905007608040c86904488007900d02c41100e80700341c40e00445a40040e1224440803404100d244003949015100c1b400740301c0c10854903490119903e15601d09118240f8005001903802d254000f1020020030010041c0400c81030f0303991700400c11481c10307040060104405980908041198440c2d0041c0d0700080c105031881e8801090f0000765503110f41c94014545404080540460f500110306011400c1d00356010f0300c858482c262300301c07003850810f508060322480240101c00104c0710780c46944000c50390010280c0030081d805840501c0178907000c0d00084640c0c004580450000c0c0a00c1a0b9100304403000b4810800c1c980c4040045041882007050101c0040242c000e00a4040d034070b0fa5200c030600328001a85850102c40403041015a0f12244004c00c103174003d0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 384703624 1250 384702374 384702389
    0x4150e0a0f0f12050a090513090f0b0708100608012d0621020405010503180a150f1803140a020106051003020a08090708122a010501081002032e0e0103080301 69
    0x31070030f40e50075405903007100d205655a07907403d140c5508120400000124200c0c40310445643d40300c811002a03011150b4803c814001ca140c5019031a0445009142e144024000d80c000754035050104611904220a1415a001050110700c080001710410b0310020f0002040314840344980c038000b0340c10b50032050080300024100c2140c0d41039500d4005450030380c401e81c45618001074003040000c1c55005404001c000c0c2007000010398005c02101c0c2c4501d1504001d41c0d08640036160303140c901c114001c401e44548a6100502011401000b42d242c03005003028a00462043c0c00820004404400600c01c0d4027000180c0030082c214040c000080d00000c00a4104030265400314480c100400c1d0f034003038001303a008201d2300ca606c024064030400c562404c0b00c54000001c3d1003203030645051446084005089505a500020130002030329614201480d8a400e05980105c410940704000b40002104502941031f0303c4628140401e40c03016801c000301038014102d82c0310030790310300c202d00c004001c01004800460494100c1c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 384704874 1250 384703624 384703643
    0x30a060e010b010c05070b03060d08030a0b1f020d030209042d0b0d0f030c080f0a020114061e040c05040503101a010809061503030408070801200304150e0a0f0f 70
    0xb0702e070064402c034494000244c204d50040000f00070046107400210b03840303100a0400e02216030240d072503500d0307a0011784200c8016912001d411099040c107001000040040d0452030b2a40d8408510194941c1c030051034400c02c0540002e050084d0f074a17590400082e00490f50403a0b0441001c01d10001c092060b16025042c0c03182c01d00c0d4a40e4401c0c03400703258040c0d10640192500011000c04c3e41c066552844c1d60300c4c100c03800802031008130304100d40980902aa0000c0e1b03000030a00e84d500301d030705101501c1c2c000d000034402c5026003001141460380724241c1540c0e07602580c0000d0301c0e07225203d00365120b00496014a50501c5118480820404650040c5000010810129265601c5070006440e40c0c44212107107507203a80640c2c00504003c0101064460740d00024042d24501a200c080e80780c10501550421380581e0344525208600808418801002d12907100403103007941000d5031080008010103407540403182d151120741644c05018014001555031000001c41d1055240c6000d081c2e4262203103003034038000d20 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 384706124 1250 384704874 384704891
    0xe0d050109020411090102060f07020a140c01031506140c030706050103080d06080106030b1306090b0720030f09150904050406140711030904230a0204170c03061b09030a060e01 77
    0x8001991251241600580802c1d684c09e041c402090344001e007480c04520955805201040c41703400303103c1c602c0034040003605800c3d03100400074007526041d02888044040c060703820441c255000a0703003500441d45d0011141d903070111010141c6140070b05d0310050102450b000c000020405e41000604854000d104c00b440340707581d10007c9500701c2c1c00500c00606514035010000c0d042031203201c03460141a104400028040f0fa40e0b03140c8a40001007169100d003c10b0200d44051b5428004681540a241d9044025860480b02e0440303240305000e41c01c0041d000b0b05040c809144070f20141001e941440002620800643c901402c0c0040500703240a0505c600700300c008046107900388101840c860610301c03400110f01d0700380800180802070400e1030329240340100028151100c4904e40260034007032102040056215401c0c100500029640400d140d891a44071001d840340c80c0e01d012403070590040d00c14200802a100001041000e44100c42c03007107a250203019140c40c00c20036117601501c546c1d98040000c200120 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 384707374 1250 384706124 384706151
    0x215070903170a020601031509240f0e0705121c050a080703050423030408100603020a06050418110c150a050a1107080703140a030c0813081204030e0d0501090204 71
    0x10403c0716020041e0050320050000c04e0844040d01610600c0250002d861055038070780c25112043c040b246030205015810a02d0b091441c0c0c05400c25008024100304446640d504016035076054921688e8042c452010040039989002e0250b0072903184486050702c1da541c022000141036501510380503000c25500d03004504201d00c04c1c03203518801c6512159400411800d00c0190100900c014503207031181c8400c00000c81e08000a000d0324070041503200000ca4005d007507104200305214150002400c02ca000d2004001802c3c000d00d0180d8807241c1042d000400120340f0043c081d1318444d03400aa1064404c000c004146441c07450304141c85401107450400071915080106c2041ea080711110521341e81080c0003110101e50340d41b00511000c2d120b41032110284a180c1150f00864020341541004039a94217824110640c12500c045d500c404a0f4150700b2a1170300f1541d5141e0940602d031810002d0700b1240d0b000030101401001c1d0103a900c41c000700801d40308486841c0450282050800881c065030401c80c06101c104c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 384708624 1250 384707374 384707377
    0x80705042a0e040204180603020a0e04030c0803090109081209060108010203010b0901120216150e03190807112505031c080a06090c0302030603010b010801081903021507090317 77
    0xc0200c840e249810940d40011980002c0751014182d100d41c1c2000005241004c2c4c01c0701018412091002013840d500d1401009490201c0360b1151441030a1001080f00083d40908410308960303211001030346039100c0d000c0702401040750500003490043c002031000e0001882d800380c40c0c45042800121001aa2650661400e0303010038810421b40040038040d1785031560150304d1219103600c0140300181010903040100c0d0f030509089000b075600144911150704200e600d07000e140c0c000c4100c040210729102c82c550603c009180550602c00030816240c0c00301c0c0710584500c0e4181300b0026800c00b06c0700659022006d42441040340b60300c0407940300c14002e0000d0b40781004610360000d07060f80800070145000d8514190343c810b200808911400f652082e01181d0799080d4403509200c0203040c2e4006840c3d2030483c00703150031a00c844bc02c80e4184101d86004100f00b1000003020301d03500210030010f403200d501916083c7d1810381d001c0e4000b5090070089007042069603128900713408a1b800390300b54001001d82000c004505 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 384709874 1250 384708624 384708671
    0x914060405090f060613021201090209011106040803060409030c0506040c0f0806190e0a050115090b0d11210f0105040c0b1306080c091c0b0c0c0c101808070504 70
    0x2250003031000030b4141e00e0003540c0101c04031b02503100076180640182103521603030f200740c00c0224902d0340071541503500d580c404810600031365604000c4c1414240b0b9250040603000c02460140b09070345424110040500c9100714a90f941d40c03203001c40c2c045042c14a844c0460440ad03000741410500d00c000300040d082c400240103030260000b81d40100b00e0801a110750b1000d815003180540f0700c0e00c6580c0103071000400074810010315188080302c41d001e4070f0601c04040184c852500e034582c4210312510003400494803810181c2522101102c0e00c040030300b00004051540341c2402c2d1680e4490069441e522336552042d000f046c419403241d0000140181c0740d452000180c041e10744807100102c44d186d0140507443c00b4609560f08411280103903070508842e10300107540340d0042c64040c0072650003141c6410420000d0071b00c642c0c02a241c109010700300183c41107907603134038007100d0030f110300c41e18005581102c1203001d00180d003030108000d5a001e841c552602c0006070303150354074451140510714001c101d042c0032249102c40600b = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 384711124 1250 384709874 384709903
    0x70f0605060a030f02040222090507140406021b1909020301050909011103040308100f06110f0106150507060605100804050d0305060906100311031603061403030405010810091406040509 81
    0x2083c04c0c41c0c084c80001d40000041e0545142d0701c199020300010045c80840060903006004a11850030040003000003076512414208240148000d000c1c90f50041100c08004c02c0000300414201500c0303000500580100f00c0c004800001100c001c140f0390040d40085040e2401610101041d80744e040c81c441c03c0b03500401d0300c070001070340900100340085c0c4a003c5641c2c0082c00f0b5500c1400079925610036003a0b80200d6403000300418224501110012814025090082074010080100624002481b21006c000712856410007400003007801c01c00800d90b20407409044041c0800e2400b9502c1c01d000b81c10070509450684052003094200c0f041c0b9880703409510310680010700b0200040e210b00c010f00003e8203029241602382741d12404404910054500035505c1000400c0c144001c0001105020301110069004660700c0f071820f98460203a51000000c45046079402e1920320007540c0c03001c80501032001135030089145c0504004052842100c10b00025000324011213041107543c40d140c0000341d0391400c0e647c4404 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 384712230 1106 384711124 384711143
    0x10050c0c01110d0516080403050708061f0501050f0d0903090f1205190311060406050103060614031e0c0301050c030417042103090308070f0605060a03 66
    0xc0380c0d6a401e003000a4034058041c82261a2240d040a0b00c060000015510031340100907454000c41c1a0024540d0361160303260314049031250b9031031042160b0751044501084484d10702e00c041050900e08107500140c11384c9020010740302c54124030b08038213505d5014080542810814010900380512035500c603407065013050f00b81580ca02d19504103c0300c08018043d0b0000151001600b401490440344440c40d07405218034044034100380140050342d0a000c0d600600040201e103401c941d06a07442908144100c540319409000c02e90b0142c082c061b4190f110358036070800a4511601e180c140c2e2104001d1ba240c2c44050350100e401e4410641304d603a400c410010403c0305001c1107421004a00e0903141d542c600d407074034104e92549452503152104101a100c0320300a01010300569642c1c006550000075142c0300c00780f40c10441600074103004243c1d1700508220005040d4900384002c2c2d81500d5002154a = true := by decide +kernel

theorem cover : BRFrame.Cov 384532374 384712230 := by
  have h0 := BRFrame.cov_init 384532374
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384532374 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 384532374 ≤ n) (h2 : n < 384712230) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
