-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4668
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:21:15.951981+00:00
-- url     : https://prove2.me/submissions/bcf7e400-244d-4807-8f5b-6b4d583633fa

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 839388489 ≤ n < 839568345 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 839389739 1250 839388489 839388491
    0x306050609060303251509120c0b01090e07150e0901081c030c031b03020c15091c02030409050910180f030e0d0602030408030402100801032111011e 65
    0xc0c80c6003041010a8020000074004524213041c1c4800c2580794965140481e11000300ea25464010446800614001c12100c0600050024262a160045030801c6416405101143c1d2000000c0340308003049504442500f00c2c04140340f036102c200c9905107081908881076600c04010040c40f52a1f103c0b0200c40d01d18402d5900001a0f43c8503d15142c0d0340c080c3d004104410004071162100c45d03032080e0880302007c16541008a0004001e00b10703841030603061804400040d60210f80c001c407048042121f80c0e200e41a04404070280d041039107495881c0c0c901e1902681035039603910648261503108104650007410007101c10442c0c1d042c651609500c0c1d02d07000e01d100c46207604042070f03a41c055500d000742c80816544030f000d00a0004080d501a80c212a80f003038115440751720741039104c02181081c0021480307240b080060380e07920303c0d281c070400081001c0211480200940640107000007002500115004082c4c107510b65001e141d441c0c41200c11440026500c00107500b807112458521001501c89c0401c600c103030740 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 839390989 1250 839389739 839389741
    0x705030c060301081b04021b060603010507031808030718030f0203150121020105090d060f1104062102130308030f150a1404090503040b07050c0105030106052a1204030605 75
    0x41044a240401e00800809030007810302800c0c0f408248044e42440540031b4009404c094180710b07400c01101010385108040d4009004004007480c0a07c611644600d80741810400184404030902c2c019140302c60007014900000045010783e4000d0510804030044001e52076041c031388a28041c841c0445111080b4001c0c803d0801c1c481c1d8080440d0580c505855200300c41d003001c5140181540b03d80010303864140d051080401404089454680b00c29441d240141000b00340410840e00c1032080303484030701d00415806010302081c02400d52103030301401440076440c107840d4412400c604200081c841c0d800e000710450700d0030000008102c3c807403002d140709151654003407911343c1d101c0d038000f41006c00c030a81d6994001e030002018002c0038081c519044408601602c0043c41e50141e0362450b145034801d0300a040d0802c0301140d00c3c400c001040000c982c4d810300a2800c6815541345c04000f034154050004111034040303d860421003d400c25088400c2c2900038803080702c0301c541500c1007410460b031041c001660070b941000 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 839392239 1250 839390989 839391013
    0x110703020706020c0f090601110304151d0102070608150316050102010b040c0e011b1e0c080a0803010311030109050106060f0306050307080705091e0709050108070e1f0e040e070503 79
    0x46848040820050601d007117801c101c00c104052200000e00d09814000030620320350094000b00003400c094117443d9881c44800b026402d0142071003040c4c1028060300079941c0100002c59902140b0036007140d1035030905810be519400200d10f540c8c90045181a0548036400425088510528240044900030f8008020070b50424041c0b1003a111800041c3d008240f1104001159500c9440c82e0722001008070035003441604981d40b010843c0c4104040c40c98504103080342442403048244c0c400c0c0003415014000c04a134a07031685c2e00409030005101c0030308205d02001c008400c03500e003900700e000386942c0840204640c0e03803260320142140d03802d904000c001034608078012035642000a0200142c401031030051114918140402448020080c244040e070b14102c0402e060045004002c40c0c01902c01e510341c922210708000004100d040001c10b05030801c500f2600814582d2110020740380c482e2221215901d4005001c0c10a80d812819040c4a40e0041c2c500072803210785000118400d0140c501c200e050740c144a01386 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 839393489 1250 839392239 839392243
    0x12010608010504094704031b1a040c05120601060801080f030702040203070318030c150c05160204021c0204090506090402061206010201111b1005010b0909100911070302070602 77
    0x12010040082d20040b400d03403103448003a070f50610100d8400140880d000940003070484801110700007040e1505c580014081010b421407141010b0070380f402e102d412111441c0d1641700307160304080c444001d401050000305040c07181b0034810a01901000c1c080010652100450b00d540301404d2207100300080246001045800b070100d00d048060040c1001181010180c1d001c1000075070008d000101415503c00781a076801190202c86c10196009444d900011802810315030081c201c40b158201c03e00c0d00d4402c04418064008090381c9410050000c10901740c2c600c2d1020030000d01c100740d24021044e072140354080c584102d540003001941c00b00c0380b09000a84410041c404000f50940300250b00020034800070300c29800b0441e00e164800b50510022600701c2a54500d80010b03840070240310400c00481084550801c1e0402201944500c219400c20266140403110b042c1c50043d0740340f95105049840110344884d800500e800064400408208000e8050001c0d00c00382d039000b540110091b0091580001d501800 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 839394739 1250 839393489 839393501
    0x50c01030b060c03180d0506090f010c05030709150908030c010608011a060313060b130b010f0e0f0d0507090e01060303020601081b0d0203010f05100618050d0b0601020f010212010608010504 83
    0x28000641c181079052044407a00b01845c018140c1003507044c000316010402c104800c6025494040160113502c2003440300909480107072403908148003003002440201c6e41c2c040451022980700b104403100c4080d126000300e4542c0d0440d403148005100206080c0030404042d0700c8130044650060080101c04d400300d00c001050000c026000d540300e1000e10000d481c05001400e050340040c810240002c818040310300251a072424003210380d08481d51401c8062145d6005416068810202d05107012262600c3d000a03d83c80b50320360104e4001c100b901502010004200080d0000d01444441445a101e031042c41c1e42c000c203918071041d8014801c1100010305000e0210b0300001505854100329895590711091104100800b202285c16640c0d030340d404030054003607109060040304903d0307003d86402e03d07200c4000c016840d140440c40140310b0081d020007190756034604041419600c07184485030b5580d8200140e0511512917000d4887d035000003050070403003901290031416203516803500c0c40c960340c9900030b2000310f5503 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 839395989 1250 839394739 839394757
    0x120c0a03140d050a4a0712030201092003061f0305060103121707020309041503230c032a150d14070e1c081b011a1903060903090b0304050c01030b06 65
    0xd05ca005c0310640b001e1590308620001d0030300220740d005559484a2091000903020950060b55200b07010010820b44515401d0300b03500600503983d01c00c0f01007000036100d440290040aa09500301c206050044a030b034205802190007400b528010b40e52810841e840d89510312a05000401001c103182a22102c0030216001d82c07141d074011414a02c45405120080840c551821104c00845000100281400b80900940c1c82c00c5070310011548a190319081c68400b41c40c40c0c039440303034001000001c0507280d8244120610107200111071014540c3d900810a9801c9021000c1020b410000c0c00c0c0701d0581c0541c0100442d850301ca880c844035a82c4201c81250040880306007994420559005000018081a020300400b401410003171700d02601078dc031000d52000403400c103d13030994603440340c0c10604110014199410100340c9580c00490060402c0c2051f10030f40d40001026a55101e10200074180700341102006080098440c1303590341070600380160f85400303c90120b40040e0504100f81000d0400d0016120424 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 839397239 1250 839395989 839396081
    0xb2106130f03050a0201020717070303060501020d0212071a13050c180105090a2d0b03070b0f1309050a050f13020901211a09120c0a03140d050a 63
    0x4101e079500303c8040c3e1100b401d40d8110b41d000d112090116160b5040000511140b00c00650781d4845813602070282c03041a80003a05641081400c101c10540105103580c012880e201100d40d42c1003286000d215510400e280d032200c1840c030384108000c80644d00703100d05480d40120308844148080c0700c00c000c54682983c00340805980c00100400c064107006100b1600400c60000100d80741841c04c103192411180b40c01c0c50102c2c1541d00b024100020818400ca44030000d0950240036001d050107d244c25504c0b820008108510300081d002c414407003609a80b1014040181c400c0c00107041041454018100c25a42006071600c0400454208004c103a02021616400340091800d6840d1604600301004019406449001180f2701c620024117000741d868020145c010071140c0d01d00340241440e103841a1a090306211102c10000e00b802403a0014000d407515a040c1344c110f800341111001c40c4514040d081481d0303c40d038100700070302c0040115a0840e80c003110150740550640f60315034481d20036004c03071400b84002d00 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 839398489 1250 839397239 839397263
    0x108070506091e09090313090b30010c0e122b0318210f050405060d09060f0f0b0102010908120705090a141915080a0b210613 55
    0x641070221000c0446202c00e264050095034600114046000442c0c1c0460646c0000800580003081c034001c0c2c0c4054440150100a031480800200d078944403030014107400d83d009000c1002c02d0381340c0c00c4d500c800051b10400091007145005d0350090048414a816540318280d0081c50400c09040040c21140d0203c8520381d992031910b4443da00048a2203225031402016260311f2688000c075070242c0000742070340c420b00e80300008905849900490b4485043c0344030070008100201441150703c1015682951002c88465503a400c1482c0400e00801590000414141c2042d9007040460300980c0509421841e4010034428044854012422540c4003200100f201e003050100705440007024103440d60013801420440e00e428052400509031200603880540c40d40d80c200c0c016151400c0c040d2850000750503c0d91800401e41c04c0102c604024030884054000b00068600002c1d107a100350f40102c901550058420b0742e024950708441e01c01280072515041007807180074040f03090900c003208220300d5190060100400 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 839399739 1250 839398489 839398507
    0xb043f1103030403270e100e0925120302010b0f01030b010909051b070804060201060f03020a1710151d010806070f030222030b07080c03070c060905010c170108070506 73
    0x110340c2046000c18044805c1c1615401d121124049000140c41c41d03130030000d03440c90038402101090400760030070310700840c210007442180e0000207005404040540c40d40012240000400003060740c40d6844034000702d882d541440181501135104403401c51095510b464040540c07030054047d14901c04001340001c05044041140c2c4005a0200d0b4001ea41521303034511480f50000c0c2c5d0032503608000d9041e03c403c3c80010302009120707024800d0000901140d440900210714680000b1001c070200e1203030b090342800c08081c0f002003403401c1c0900c04408008500070440c0304150303201041c030400a8050700d442c1e040004044100d05403180d8940307040742d000600405070b940d40d07801300b1909003000c6101401490340038806c621003104950f000401920801e010881090310794240200295005008041402202c01c06d00196403104000c4980c037017414203184801c3d40d101c0c6061070040c403000c54042c00e254a004140344401e0340c0081d6000b140c2c00350429102441e62540c000d19203072410791143c0c69001c44200000d0310 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 839400989 1250 839399739 839399747
    0x1080d080f061203070614060310110f0c010b130e0708010603050706050a090e010e060907030207031211040e0a051005031603121209060b120d08040b043f1103030403 73
    0x860043c02205581c28028a030f69410240c41c000244081c0c1c05030200c0030800541820082c800210700180c13002d00c034840c000b2144041d94400c00414117280c0d24000303050200c0400940100d100d20354054544206120005c00c0b62004040110045005024071200000c001405000d4441030782c5d0050b002d0108289003440980b0540c2c0281d0702c07107040c04050760300081c007480080505402811070041951461504000f04903814900500c0380c4145841800030342c001c40d03400b11000b003c00201c02c400003003100c51035110007502c0c000e40d40000c014010381410402c0c80e0070140c020b580110300c64440d0403101c81c1c079602056103515180e141d42c400400b2084081003c04c030550381040c600642810710714840710030399a050303050380e40b10f8a043e10255140c14500b050f0f41040030b19620008010005040d03101144c100c01800740501600c09082480b429001c5000e014042c0100d445d030b604203180c600d42da0890030302001c444da02d4490305102407000180d031100001d0300440603000d0008410703010350302d10f40d11035500f95 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 839402239 1250 839400989 839401009
    0x90b011b03020c090a02070303050f07050909180d090e010e01030803070516020a03080901080f1012020f0a08060708280f0605130b13090f082107050301080d080f06 72
    0x78086100f80e0700880359a4403072003810381c0030b03181100001d6500d41180c10301130244d82c4041c014002c0c4071826030403c42040c0d0301c28281d5000490840d28081c1c0d03074842000c82140381401c02102400c80c0a21604902815040042c1004940800347c41628682c0c2c0c03014003e8031240c0074070000d45400c03020000100098420001895043d907042010b12080c0707071070b80115181c40120781003140c0c2000001548852507030821680ca6010301300f10b0740004507190510020420f030385036205460305888011030b44421550390451013014410040d16503017400d5943e03600340b43d403020f0a95107940806c1851011401c80c018811074622101050408501c0c2c6078105440c2c40000c2612854200c15103569190208240c0e0318120320407034200c0350f00400f10b609d407000000c000d00409581c06092685151032540c06c0019041ca00944c1d0107900400c4036503d500b845000842a40d440d803280340d54070a880420400c4c0103800c040614107030b45410085500da24099070095441c28030644034008a40150000183c0030700c0c2c804914 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 839403489 1250 839402239 839402243
    0x30310171504080d151815180c03021e090109061b030c030210110d060902271507051e03030f0c0f120c042c0c0906071e020a090b011b 59
    0x501c0141900c0c480040d06040e0304071025490343c101b8601c01050480c012400301001900c190340640713207002180403041188000e80c00070b0b03a8484030b240c440c040c02541502c001e0440700401840ea00c0b41c40c05948481c0e0301040205003c600000030220300b162040c6141e6800181720001b80048201356107080d201400344850807421481085404200e030313401e40c05501e82a443d5014400d4840740e101c4141410f0300c1040e005403000c00e2060020100350841172182003031150300c40303112050b006014404501c808640d903a20324103417180003a0440811400158000343d182e0b460304540d0080c0c00c10326410b42c6910050b0703600362010350396801080700d50b4410001004a2102c2140c228501240c40030580c0b0200001c031400b003007610010a0400801460040400d400c2090301c188910000440202d07880d44040600100c40100010a040049807034580c2110134840d00b00703849050300c010704e10f41c040441c95414002c0703000e52176060000840000c039000b113242c80313030b0161580100c900140c6c0422150b40142001 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 839404739 1250 839403489 839403491
    0x30604020c0109060b0301050903070f200a0815060a0509040201030f23010f0e01080d0e01050405040e011d01050c090607050a0611040801061d0105061605030310171504080d 76
    0x3040a108200b4403c1c01c000911614020600445803800c260840340d004005039429001082000300141841c042040041c1d4440408000000d00080002d610410844003580200d440000402c4400d4005402203006a02010004580d0b40314401e00081901c14412140c1100c01c010201b401580650041c0e0a950180b540014107048440c0600c210b00f03101e080580c0649010384010f01c411160b011210001c0e0403410380b014020b52502050a654600da040b5030b1007044007420102045030320803012140100710091050002030604000c50740280308900811181000c0b0089844540106010301c901c5607400002180c10f00000ca010f200d11580b00c407c0850b05409402e04500001c1c8091081068007400c014502c0d80ba41d062070b8540b82142c0454002c854172051109551241031501018181969816502651103007420704081400760320b13144006050f400044208801c030072442a01e1800c482043c0201e0403415a401c0384d05032916075202010042c018500000f60108a03c140205a0400c00104c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 839405989 1250 839404739 839404747
    0x50f180402180109120b0403140c030a050d051501020c0f0111010e010501030b10030c060f0c240c080f01140d05030c01090209220201030509010b09101a130b03060402 73
    0x1422a8091816182d2041903035400307000c00e503131150500020707040742008503030b048210751941d1300b400c54010401020072401e500441d51a154090175a0901301d8080100c1c2d4841054181c00f4159400c510b1402e42d200d49445d000441c04219000c0011185d001a000b030302601d4100740c14400d101c200701c5600d6041c0f0420310f0348001246001d1080e0034410200c0300c000034013541507140c0ba1185810203814480a0303482d2102c00c0c008542b155a09908807083c0782442c08220f510b48400741c2c0d50b90021039000d820b004031440400642d4400c2c0c82d145104810b0003d040080e440e01c400c0640304c07808141d8442c02002c400000500c82c10240c0c03002c4041c81400200061a42030040e5034891031039008004c2c80250341d4490b0490011414a4a20760f50400040c50000c0c0d00d81c50310071401a0341c200032a501904158550011607414002076008084260024052240b1807800c510305200481141c0b003044c41c2e080020320b900740910700c82000e0b00d80002e48080c1c440b00c101e06d40800e155403604041c1030194080d41c204 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 839407239 1250 839405989 839406037
    0x60c0c0f08040618030b0c07030c3c0809100e030a030f0801092d0f0908070b102904051309051b031e010902100825050f 53
    0x2100d038240c14812880315549a04100000300400036165500c00980c100c0132081c400105205038140d031001a907601292112010304045903810450100584030907100103110010444c0240401e881001b1801090805800300101006500001a0107001c00c40107001012580c40e0020503043d0b6a80185006010b5408810000b402c0010521003140812052400642350b607030408803090041002030402c12031515450141c00500341c4e1007581004c080d401c030540e0300300c0d2491a40700d4004241d5600741003180201d9460a0400d50384000016074098030084001804104c0025400302074412000f0460800c0003681d0707440b04404c0c008080d21007041e078180004141c6072507075581c15505101c02c06011541b18a6030a01c582041d04065068480c500070404199003030301d000440c8240000402c0f1340500340b121800b0343d039005000c850350003580900042c02402806911600340f5001e034000300300d84013940354845860000b00c42c0060b0f01030041002400448105041640a008011070650000340084502 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 839408489 1250 839407239 839407253
    0x5010c080c0d1d0d0908010e010b060a050a120f0603110604060f08041401022a010501053d020102070219061b1a09070612060f1a07080a0e0922060c0c 66
    0x4600a10015175250401c00080109008040c92410000c000304002c00c003000105280703100b0203481e002032010018005482c0c512a86034003076000c408030001c1200303121000c4a1806081030b07202c290348940883c3c05280c507502c1d040c402c41c0c045400a8030f510407030340d826890035604003e0090054a8048070400c04189844e8280018641d4880060414210401c008030101c215408000e41e030280d60300d401c00602c056207481a4021003c081d842c4414000e04402c5000c61038a40074440c640b2017076585040c1500c0031501500680000c41c8211000341d1b260901c2c1080100c140074501c6540c4c0002c8426020b02500c440b10340740124081e00070f585c00c2e50103044041c04030b03901220a41d480301803940070403010480540c0c0483c980300d00302c04142c0140995031403c8024107c10100e801005140b0701e60182c1104044c624004603200c440d444600c04d9245d0300071b00c001804160030060224021510700b400203200054a400300d441c11451800300e800303919000d440f000002c1c0090500501840700f11480310f00400c2c00 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 839409739 1250 839408489 839408503
    0x219080114040504230c10020a0308060f06070f0804030308010515090607030c211101110301050f032404020a0f030203030d0c02011d0a050d09060c030e0109120b0405010c080c0d1d 79
    0x200c840100846e017810b8091004d07034003410304044215001201188000381e44601c01903040081260404900305407500000e40320f02c40c850b0000c2440c080c2000f55010400c4410203081101c1c0280c0302d0720456a0b03520144100ea185400c0c010040c04003c009000031413070120050500907019140030411008203546070702200d1181c1c19a41444084800c0200c039180e8402000e0b03c0204030305c40248900b4100901c491000c0c0010300410384138549040800c06242c40400c009441000554010b1107036609642150303201e0b40042c1e90503030107650f0170b00c0c0128581c40c0014000c81240da020307000318a0f0080000f80c42c03000b4440c1c2c6c08a0411952030340d11040015008030060404040940050049510607103042480d14524882403c18041d5005041181640000c00801c400d909400c01c20320682c0d0740e0300100c61290460b00700f40c0828840700c01080a01c0f0708a07900f41d10841c403550082041590146003035810103030481c0c2c001d00320302c820003080243e41c2c40d81d00b0120750304046000314030f403402c582202c50b410150 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 839410989 1250 839409739 839409803
    0xb07080904050c0304020906041a12030f0301260604020904030503040c0503120c1e0a0f03141c051021050a020909010c0206010b0403020a030b070c1202010219080114040504 76
    0x40140411b41c0b030314414042e000781c01103c2c00c0244040c50354541001911320503100f441001e5100d0b240c2c0320204203000f2030b0740c204a240b049507540d684550ba0440008000311982c0010480c417481800342d0000090b03c2d5008540003086043da030741d26540c0c100c5071a0b00c001e000301d4000788008800a03950300c0410a6401c0344801c140d405445038181640d403844e21030b40c54a0020b80210000b400744102e20042241101650400701d5150000b078a070070155526512500b10806543d0300041c4400b654501010511690a14141c140070903200c000380c24010100501803070907526500f0903e408203171075456020340b200c0c0c460000e454800d0040d400141c0c3d040d03000c580a500741e94594610710f08043d41441030030702500d406075989040a0464004c13800310001800001c00c42c1c0050f01c003280603203002d000c1101140b42d04c43c41200030000c074004028083d41080e124018031024030021803000c50b00900e085416554440600100c0b207030000100006000081e00c02d584011700a8501462145001e0341150401 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 839412239 1250 839410989 839411011
    0xa090317010602072904030201030c17040b0103020a0e06030c010e12031c050c0403030e0d02120a030c0c0504060308070609170c03031501170f25031b03020708040b0708090405 77
    0x80c5020009214150000210010005c030784401103000e40490040c1d40503a502031800040480d5102c00a4034800000050150842100020403081001000071507050b00c0c13081e00d40460f1180d4071100850901c1c010f90b040741e815084821048030a508c102d240d42e04040380104a00728060614248074159805800c50400c80c00e08501081c5030140e160041e1604000c042000b10f02d45881d68130000d00c01c034026001c1d41e2040d08c03400c01ca0000d6541d11540142801403010a88203040c440d40b40c05425101e60703840440d00100c203c0310005e0035103010300c0346608803904000e89500c2c0003000c0d600e9500800c500c42d03084074151807400d0705003180b060311009024040001d20007036170b40b030804140b01d0320788a030710741c816034100180307840d40380400c440c05044203411040040214100b03468501503068104185216980d0b101440c02081205075403640025100710103803d500030101c00fa920707046041c0c2c49580009020500c041100300000350002008004403401101118107086c3d02d00c00040c2a980c050b20082000 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 839413489 1250 839412239 839412253
    0x1e031b020105011a070b0106050f0712050c060601030b0d1407170703110d030c060902032509060509091e0102040b0d09331e02041d0c0c060a090317010602 68
    0x2481c440c5003803004a04c3e80794076800c0ca4100d0341c1e24150900c05005038130802201250300710301e115030369098400413940310780351320500c078007009c002042a0001c1780011020320650001c030704a540684146000c2c22000f80c280300320a015602c0c1c180ea1440042103074101886045c00009001d20a44460b0010107900070140010380e196090110b00031200002d06449080c0b8800c6150010b80c0040208090070f0380110080341c0d1481d03d0001034200f00416501c500c01003007085150014030304410002c6c0942d41c10910820404c0c3e00c1d4010300ca00141c007100c4204940e8400800e1f102c640011102c2240414585c0c2c0002d450161103403015001c03600315001c214002500c0d62481010481d0f80300038905180b102580c400b001c1c2c801c880c2c00c0761404200307100f090545a0b4a48210302c410f0410000310849000c80e4801359901d50342c4a00243c40218903401011a000081020078110550300b8201c400501e01200200301035101c0e003031110b00421030600c00f2018000c103048054007680b01010044d000b441a90090074807 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 839414739 1250 839413489 839413499
    0x140d051501080f07050409090f0f080301082404110a03050307050304170a030e0913020915030606100f08070c0203150f010801060b030c16140307020f0f011e031b02010501 75
    0x229070b5014100d0a464080e4404000c0c00d15482000d660890b188480081848240360821581e5000043d00c044c0c5010130100f0080c0c140003c10300118103d4030f82d01c2c1202c0700c11441c007040040e04184a41710b0180703200f0b454042404640c0100c48800d0f075040c01044602d50550307a585492a41c1c1c843c06c01221036400124003040200c03142e510007956201c106001e44a108105d0764024095603841c0c6842c0e10507000742011464001010358501c0c2600c1d4050584012030800844007441c2c8506400981e01c030344501c00c0041c6c018149085809141101c0761614011680c40c0601910034081c010f141408002084070b00b400940d07400c001020942040710300000c0c160402908420003c10b0503046404940e040450400c0303d617003c141120350102002e510240c550070320001d44030b000d9a0782880a0311001c2c120002c0b0070090b01c04001041c23102e2085442e01c0c0f001001805004003030380c00d4240207000c0389040c403000e030b00c0c840b50700b185110582d001c0c80c00050079541d11286000302c0549400c83c20060b9951001400 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 839415989 1250 839414739 839414747
    0x90c0c190201090927030201061809060c0302070b010b0322030e0307080c13020d0e0a0506150d0c06050a030e07060c0302060603390a0b0a12090c06140d051501 70
    0x4058580c5844c280600014018650407190304c100c403000c481ca0b20300c848181858400c0d4032440103442064214110304556520030f0002d400c4107601500c2c3e0918161804000074002e00c00c5038030f0140c0c86511082c0c0c0d80e103810320f000c55075000200b90b40189803070410044015484003004441d001d00c40e403166800c040000c420305180c8481c6820510030b940c05480d0a03011036494400000311105040c402680e6100314001d240f0107403400e81c1e1154640d1040b001711000f00100815500e204030360702c03101504946d00d25400c106c0c211050b120090161000090309201c500e10500003840342034818200428070400c461001450165203501910000360050801c2c02010b5041c040c182e0840000c6005201c0d14281104490f020a400b1072084a80d400308418420f000f2042c1c020008180e000615054842d941e80620140d00da0100d00d250380025000e6484145070300c054405c84200030341200030012114100502602c0d08503a0446540009400b440055a1100d180c01490300c1380c40c07808810030388a880c200000d8 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 839417239 1250 839415989 839416007
    0x9040b042306061905131b08010b0a032c0f0f010207051903111510051c08090402040f0801060911040602060f0a0204081e0c0d0809090c0c190201 64
    0x110704a07034030044680c140c00c00600c2642059045680001c030000c0c0300300342211460540d210f1a000885600403d02c040d943c5d50005111128800c2aa81c048078a050112001d0074240187e914003442445907000341413081c0d00c04082c50710150003803141c500603000881c10031200b1500c07a5038154050940f400742d001c0d003408900d0401031110700030341c1469426610b9039100c40000b091a0352041345030800400349440b0310710400d4503400100c01d5078070080400030222440241250201c0c041c10140c500040d40c1c2c00c0c00d19100c022070310001842940d01c4041d6884654540c4500400ca61250f000e0002113610381205060400a10b0941c000040091031b00321804192061445000d054040501080001c40d802140071a4070014901426282d40e483e0715040b0000c1c015904441141c0c07003020301003c0c41c005506c24020b402007a840803200c0c081c207a1020801d501600e10401441010180891b0070141032400005030012044140103060141d6812085d1906640040000d40080f05800401c25560080504 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 839418489 1250 839417239 839417273
    0x8010e011506020a08070f0305040314070311100f030b0f18040b0c0720010212040e06090108010608120c010e0d090e0c07081602011707020c180601020705120a0209040b04 75
    0x10302031044454685c0d0000707015140b40a80408120440c0008041c0f0501c22280515440040e030014840042e00c42d682e140e000740405c0741d8550048d6180e08161600d0100108a4200c6030b80b9201c2000c100340e822406000e520b1151600300c404411010510f9a40914405d005030600d0821901031900713007403401200401900300e81070101d04200e5040030400d442c0008080e04030410b40401d141c003a940040b0700d0901c078407030241d101c0d00c404600032910807070032803e682c0038410444846c0780c030340d880d151328a003220301c140f241c40d00c0399000d0500c2000b1002e000c001351803091102000001e603003c91503441403c140b18683c0d8080041c0e48030310207004079900f40e00442d400003840c0703d2003410600b19548442c914801d041190b01e100588007211400c41e032190305c02c013010000b0031720180607500348030a001e552040399215142c0304240d1607452101c941003585c04030b031007420141d004007007540c0f80c0414040c514048088081160241012130405621580c0380303180035074412010b000b45441c0900f0b120056a07040120 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 839419739 1250 839418489 839418493
    0x71106060d1a0c1213060b090c031812120105011e0206010b03060609100806010f03150b03090312092b020d03020f0903100e0613030f03090c08010e01150602 69
    0x407000418180002181084029698400c03036803202c50900825000d600003000441c039090041001d0108031024854050303210b070400380000e062042c20004070550440e030b2064050024800542c04800042da012820180401a0307044d0800f444aa48010360241080b50413032152103004006c10350340040a04003d50f07081003901124920502c0082d207614040c4601800c4020110120b0015500c0804942c0d04480050059440013100413003e80503107c221107290102e2092040081a180a8001c8204a0900c00c042c48500d90420000342080d41000d1b12450f45884240049481048010041c0d406801000014580394900321203c90b002d070a00071703000c4081500343c52890a85030300020504482c40007420056142c01a4807203161450007941c02e1a40d143c8150381100d03401c0301d196030044840016010a4503806e0707803032800d02440c41d2fa40038001000548007030324a40c8014801ea11841da00d1744101c0c1da00030702d56a0b43d21801e007540c00480113031819035541c9458052211030440c146006081c2800 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 839420989 1250 839419739 839419759
    0x106080f0f0604080a1b030c15111c090507090504110a080c041d01060303080f0a090f030e03070530071a07050c093c06040f0b030607110606 62
    0x312880d11400c010f40024005480070840003a01e902070b011082046104e403041c03044801c95400c005201c7c84d074028096506004a1030010610021401486903030301035040e02d1440e003d076002d03002180c211120380614840c1e40d1190b64000080e4284010001891000c00c042030609007401e11540605003002d07190f129645000e0b04011a207000b046a1164107800c54002a025040052145400c1c03200040c1440e41e51905070080100b54000b0f0f40a40074801c900c203041040d50340c1010110031506000800f8101030072840c074081c00280315168042c0344560280c10b44a00381e6440000c251511018075110980d0138442024249644804130342c41240300501c402408000e10781031090317202c6503400d0441d81c07a01d040041c0401c24040c041041c100d44010103080b412042c0f8040b0340c01c2d60202154540c81b01580d001555900820171a00318100b25011140c82d01d8030242c6815041100a005248040344500c0d103a8000154641d000c1c000b241c8100a692140c5a01d41484185141440401481d41e48030300c4c8444 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 839422239 1250 839420989 839421013
    0xf0706020c1e03120f092e240e040c091404030e0109050114130f080f10060312031d010609051e0c03040648050909061507140106080f 59
    0x1101c1985c00c000c0e10700100e822925204000303401d04203050058100050410303080084041080071359403100e0307011001044103084107046048404881ca90301140344500d1402840348103440c215032504107104003141000d041e6150f4500c401d80e511103004c0304845031070004210a143c4c00100c2094a05400d10380040c200d410080061322803151b4a03403841f21300c01c0105d4161034110071150503001410324030b000d84008070b80d299903507652021080102d00b0140070754241209031401c10300524007940c0d84070610031003200d6100012002070409101724800380c2403205840c1c540b4102846a8000b4004101c0c001c9610302d0281003600c600407011038802c2c54180c001b01000746000c074080c162904a0745c00240818604140e0300c03180038100d0780409000c0c050084120860300e040c40c4900606240100c16500d51003004811800d071014041c0c034007210780060f120b9001503154a0021411608021b651441c01d0030060903440716150300400308500307d41c6a6440a06000c035032030030001914480021801482c02d85600 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 839423489 1250 839422239 839422267
    0x10c170304060b1c14010b030102181005120a050c04030b16030608120d05090f06090d0305011401121d0a03030b130c120903030b06190809030306150f0706020c1e03 72
    0x480780078250f040b100801200204087d08480005100140250340b20300900c54800c04410f410850584240c41409241702658003036000d0703410381c1a0340c030111411560b6101100001e0b000c01001070108207010400403000801c11b5106c1400f55004000d01816813800413406022159607070007003000c40d0b10030380b05150b511030b58030200c07107100c4d0103c4c8000c00c8035214204184e1426024207007126882c060403041100591001400c1840e0143c540e50520213640d81c1c00110440a01081481d400121102503a0511008c6a00243d040c140348182c906180494007205070304050300301038100c00080c0c0714081d02c83c80d032a000c0128114045130400400060419640180018140040a0203034540f507140c29018035000354840c00e03003024044c20155443e003c0203003c020b00510118010081818040800d00c814000070503648100c0014281150014104c59407141c0b03a00042540c031803a60041103468005030607400a041644000002003803003007190400700480e0017100083d040d080d8000c0c00840b2440d502 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 839424739 1250 839423489 839423539
    0x60803160602132d0609061b050d0c110a05012111040909050d02070501020c220905070f08030901052502040e0c19030807060b010c170304060b 63
    0xe4800000e12601901c0c000700640510300b0035403048955610009910241240d01080c01c4842814050134185050b6403a04000f0711800792100054403007000348581d600494001031b201035451000414240f907540e800b880c268000700d040d0001080c2144d0802000090036001400b544212051401c8a0520300002c00d001103404c22210f00e0305103d08882a40c010990003285210721800010b035655880f481e10030050846031004a4181c8201c000d5021440c0c0301080e00700035610142c1c050000c1c0d00006040054042000307491907100448441c51112044c40351203000c14a600c560068482246070240790385141030070f68045002500200f00000050380d00004861030608000181c0d2005240303001048107016034100002d400628001c00c1d0400107a0014801f4008641241c081242c42e43c4048039410f003500d9444002c107150400d20148000440c030707030012008281e06140100122006448640484d04072090070400c0c5100041840203002d854000c9036554841a5800084254030556031030b100c002e = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 839425989 1250 839424739 839424757
    0xf01080f0c1b030304050303010617070801180f0e0705031e030306010c030c02041515030e060a02031e1807090204050f1909060e0910140703200711090a060803 70
    0x9000100c003010300480b00301c10705001210000f143d4692410340740c1070307649500038000c40010a018080340060074500440301c91052160350303180601a4a0212110a029a025084509103032103110500c4c800300303c1d01c41c0400b003d10f0300005000d254a450305040c1005603607040980c200c18140000c00f6071150020840e50020405c0c030303009da0456000e00701110039101e403120096000c2c0c10b180700d050b01e80004500c50000d03103001902e0000c098010002c10780c110f598001e900396443d00103100007001803829901540d4404803101080607010411451240d001004498a2650507001700548490202c10402200502944501145040d00307040001341d041000d540c070544074507403104034013183d000300d1003503070005110426050100c41c1e2244c1850001400441e9030030101c0c80340c0c8a20400142503401440c8101c10204855809516941002c4016261710f5910410304601440d840c940d0a8042c0c00903c001030083c44590b18251030301c0f040100f50100540801145070030007000340f0185001004403a0155 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 839427239 1250 839425989 839426011
    0x6130b011409011403160306050f010c060b0a030605070c0b060f0a0506210109020a022401150e060d0f1d0d0e030c04020d05070801061809050603010209090106030b0f01080f 76
    0x4140b03500100c611030072048a140a03824040148886002c140c0c01d8020402069101480115140e10034801b440072514883c80c00074513038965a1020816070b6109960080c0003070b03d0307400060b440e521410700f07841c000c0c0e802c0d40005508019080602031100806c0340c00050413150300c00b0008e800d00000d4480c01440c000c0a200710300000307204941405400c3d800281203c0010b411240b0360307603508804003d4010203050740160150603240410071284034001c0d03448100d5810314622a900b052100c1030f8592103400780005100581c14a60260b40da014054a280e9404800c003258200d00d040069040d5a5150040f10305d020324880c07420012000810b030110420054a4141d9280c1416000a0310781a0640320a079085440000c0d00c00580149070020b40c8a9481600c1e00708440c4d0b078488081301c500b0030f41000f0702c100041c070700000d00c80900390350005500480020005810082c2e52000908403150aa100030007107903540f03012807801d0a001d580001c2d0720701d09007081482490310300d4000c0d031003c0000389150004 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 839428489 1250 839427239 839427247
    0x6061206060706050103320d0c0512030a0203100b0c0a031112030108101104081209130e0a03030f11041e0e01060509041a01021005070318060506130b0114 68
    0x151141c80642e0109a04481c0a102ea56501d05000c601c3c100035421f203584c070038501d950034407800900c189106840c0b040070008111409080b01c0442c1e44e200701810032100d90003083e040b12000320703c4401541c000c0c0c00321900143d076400c0c803003003c2d4cc2d100215031089902e141c050000f400040c3c0081424040c80d0340504091007141040c02066090003000d40e02038040c03000210000c50b40ba000010f4039540c11781c20740c8003000096601c0300302000501961007010b1982c6c0c84164807540c0410f100000d8104003001802c8110204520105a0140e030301040080c68158017986c0b49a0516615014440ba101c4090004100b40301e80c0038a1101036225a002d0107a07264044080d4801c00e2030301c5214440180000801c6090070350b140e01c801401688906c40d180d11490801501c9404010401c081c0082124140c008009000e00140e1030800740400502b06030034543d9441e0700d5100305140c0c1a11210040c402e8100140519002c03040040701c034141ca0341284403c0c41d03e10040c080340d80061520740101c9605540d90f8036 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 839429739 1250 839428489 839428501
    0x100b0f0409150204090f1404020901030f03140a1d241b12070c0617010918060e0309031e0607080a1b030507082520010603030503011d060612 62
    0x2503a818060b407071400d030310000c1d0004500030340758012180395102100c01c1c02403008900840030342d2202540d011b544000c00000420005900c0922012030910134140841104007801d5a030315140c002d80d4200000ca540c0c40b1607201c1800d885101c070381d0311440844158002d06100000d0038404200030b032100c440e168000034800c09407007020138501ea009003554101c0c5c413910307000440f013507640d08008030884d003180791284003141050148403a407005401c245041002a880d00082802509080c2144a052600c4d00518000b140b1b0300d0090010340e41e07140c4000c40d0346950b81c10501d468044040e942ca00c0f5030315888500720761418080b03040c5410034050b140840003525a401c0c5030004044c5401900c0e144202d05404451298054021a12440c810740314500d140d03071007000c41d85500700041400c2112091010700b40c1703001400b644000d140380c0320001e00c1d810210380d44ca200d80d00312611078005a0100b40c01100401840000414078040c000384443d83c1400307420b146021030154002c48200f154820820400030310 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 839430989 1250 839429739 839429753
    0xf03020c030702060403230a110105181002070f0e13061509050a0b01110c0904020418020406090608011b050409050a0216030c03030506030c090c07140d0809100b0f0409 74
    0x5000c90f001422543d036941d6a01d04a030100075041c0343d0070800d90200500d14070000c408610018900c0d0032000c0041207103120801150b1951114080c00010450742820320010748504013144141d44050300101011428000c0c10141c0310002e0380802a078074001c0302008a044090445410090344c80040450342d0510700d000e10150a4007038106180c031914220400441c0c01e0a0380042c4c5059100b038941c40010040155041c0d141d00c0070110a40c1c0003410741021400508141e40f01c581e09a12500301c004049071513038001b405407650341e400402c0302a01d903541400303009828401c070440300e02d240b0f00c80148800206030140180c01340d03210301140c0a40d1800000c640413016011a20004c1358080d030350a5910141c40c0142007590040001c0e0002807421002440c0c608000840d802c02800c001e210314a0f9a560154241655128105c04c580740381c0845004400300d001006004102d41154403483c005d0301d403401c22a40382840704e00035111103a0030320b2007050742c54582e07054030001900c0035180801c00400c00e042c444 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 839432239 1250 839430989 839430997
    0x3140102120a060f0e0c070b0a0e0a050a050d08091b01020c0619030c032c010906020705151311040c18140a140a050d0f290a05070f03020c03 62
    0xd12a004140c10003000d00d0380390b80700205481c003086001a0b5071740c072054440710842044031b44001d500c104110141c00b04a41c00c0c0365070f9000514020109210b088483e00394280803240a0440d500e070301c100001342c00c001c2d0521080900d6811880c18003c203190600c1c08a560b111041d210502c49005070f80281766a074403e100e848441e600151080d0f9552500b04070521303001c4010b8111000283c0b03850405512035200b8010125280c40d85a00302400c01c858880c1d00c80e82480c05160203159669814030380e00041d4003400134110b840e025001611500e9401202035200841c02030201d60b00200d07903d170500c0058040300c51005031010640340024480c010362819114494840503168041d288010f00084500c0380d603050300a010000e48000c00ca49a492110b00c40a030b404024865010118000c01c3c40715003883c0000034000350003114502c49405054a802c161074424810ba945100350000780c1c0400f00300c4a0460300c0c1c00151100c010080f614081c400141005031804025041540009210303103511001c005903 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 839433489 1250 839432239 839432257
    0x10503061c0b0c0a080603070b0406030213172113090c0e1503090115120f0201050f0a0804030f0813020f0105040e101a070c0e0606070f11030c0a060903140102 70
    0x54002802c01100c040f403a43c12030b001c86000030700448002040d608010841d0310884400c400428286420403500b54003039005400c448400408101c00010840380c4daa6a01c4030100c880e1000d410102144420000620b00030301030500310010401600750303108071180c031203412100043c1b00020391424641e01111844c0c8031400307032944501101d03000d200015840c4004d500074500b40001b0403002d40c8400c40600c20080520640018080d05c8180c10003080c105140110740c01c2c8140b404c14606941e0b0313010000250070116055002940711001c2204154000d403000c184402da03410018918603000384d003200700c9281544024068809014103078466400740b0191000751580c00b4009510345000d032000c800000042c402c01740d011040607043c1d04010701c2c26080ba421241c000c0c3c11098598280046802034400c0941302d2034100c070301003080c1c40109111220600d0070300d00c58140c2e02e1242015504040c41c2a102c2e515041c03040200c014200285504a0a40d10849500c00b400002c1d5032180f034a514020b02560740030f = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 839434739 1250 839433489 839433503
    0x3030e0307030e1c030503040602220e01050a0e0c07140f1005100501090e01120317040302100614060405010e030712120908210c0705220b0906010503061c 68
    0x1c01050b400c400382c035000b0441510f06500006070041c603c07030400360110002d008035104002050106005400500c10081e19424800b042c140c26240d540d4103408640c00507400c420944014085032070410004801400c00c280001154100140d41072000d00c51040c0c0140040580f0502c800303901c0040c019402c0c15984042035071000c0c0e82d840d503480054182103600f1040201000310106042d03018003151010f4603001e09074030040741c0c00c15120b060a90403c100030350521822016225074650790007800c5110710320a0380078080c80440007034160300741c40441c0c03c21552601c1c506c1c00d0262036107c1409031011143e0901c0c004460010140100342418860b80003002000c10360104c440502c40100002c0342411550307aa039466035992844540d0b1514085503e030000208070b0014841c40b1450100a4610364960310103842d121030b80c8a0000e1a004185e050b110411009101113000784200d600ca1140c005500340c900708001d151000000b040c91100500c00c0d4403a103807110444141d144200d00040310701d907018103 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 839435989 1250 839434739 839434747
    0xc0c1a06032e06090c0806011b06050703020c06130b0c07060603060203040c180203040b0f0703020c2b0306080c0909100f1401211211100b01030b0d110d03030e03 71
    0xc00c03001c03484010400b228141d06104002444401d588104124030440340e4403540151107420045134603100c024890055503504415000106500b03100b00c500030101903c006035601610f050301d90038108024180c40c103d040d8001c240020900c940d0645600021104055036250380b14602800280711640002d80410301c08402c010420028070350102c1600c2400c074259446456440c1314034268070086400501010343c000109140070107480d9459040a2a428003500303080d01560f0345868501d0410b14100211510005002c442e4030003402e4400100c150b24081c0850b9040000950303441340c2c2916000c2c0035220400004103030392018480c2301101500d21105000d0071903400901001742c5650301021507a001c4e040300019103480908408042c1d1000f2884d0010303c0d0010351554184941e070013110300d080c4185504050101c28045c0412520048510340004854a00400040c1262055850740b07000702d096400c1c03800821380d12440c010384514112092020001540fa049007d8580d94804059610001c9 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 839437239 1250 839435989 839436043
    0x90601140a0504030516091805331f05030d0212030601030204120605010e13051506120a03021515010504140303090d0b0603010510150518030601030b01090c0c1a0603 73
    0x1c004040387c6055405000803a01c0e43c102c0700803400034040040840d4080941c02442c1074070220b1308034015082d041e817811080010300014005a000326100c40c0070a0800d412444440524078624001d80400d50060518820000c03010b5a15035100c8056a600c1501200195150b80309404131806090fa00c2420a050807291030701c000039003000c0c000d010100a0036800612a540d6189921084a8101d801440000987c21444031698005003201d0781014005202c2c00d4000070803c09020014400d0b402044070039000501c4070307020720703001c6e007601e03006132805003000b56681c0c0c400c2c151401d840100b032001c0f20116040d00041e146100380e43e15030f500700c0c101055079024800b450114501c1101c0680c020b1000360384450380040f100c44d5a0141c0b42e85540e0800812036031600c5603002c1c00041c0c0c44041003401d0b401c0790400080c540382007640100e5103c0d20705801400401018004c001041c1ca060425114941595494100c21034092600421621400001400c16035040100c80c0403819054407c00d8038060074 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 839438489 1250 839437239 839437273
    0xa0906031b060c0206030a0903091703070201110a03141b1009060b04050403050f390d0c050304090908090d080903010c02030304020a030f080c030307020309040b090601140a05040305 80
    0xc4101c0300300a85114000034540d40906010b100855004001a00c0c0d545c0c0d000d004c4d001040f22020a0f41008230001010404e01c0180c100c251071801294000d6869009500c00184821400c000d21003154014154480003e50000d90244880c181c0303030b17607407034545246040044020801c0707004800d06104050312074406541543c8000c400500410003400344c6403200b018442039840641d801000206c0402c2041401c0c00d0b00c001521445e00718200c81910304003602d40d1898501002e261400988040310008601100e04102d4094581031078180400312440c2c17900c810751039004511a08a096441d0031101c001c0120700021036180f450010901e00c180c11550800813180d400a1441601035860081a01d009900001c103480c800c55005100005c0d90381150b4a8942180400c88101c441c000240244150950140059403180c0302c0d03030b802540c640c2241c204010507104020b208074010703030107217091200a0340c1c0907203a0064148101210381e600c80d040b4500711124843d680c0050000d0180c1c0c9842c0d0b52014003 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 839439739 1250 839438489 839438513
    0xe1909030c030e0613090e011107050606010e0a08060406020f07050a051507021906020f0f040308030603070f2d0b040602010f140705190306050a080102030a05071409040b0a090603 79
    0x20b0f5681c410f05030704882400b8080c4165201740905d240e00e090100700303049568001c82400610040041800704110f4001c400030341040b40c0454654100c9020010507580c000d0721107071181001c42c0d521203191316000e2030780c3d00c507030303002e04043c0c05c2940000396450301000100868030b01c968480300303d651400701760425a8030350800035105840f0760101004102c2c69840050f1a40c20310301c1c02001104401225a5218000c1d4841603d05807816014400c040300e0030301d40809000210300400f003c0d5940c1c90301c841010f08107000c58100003040312110006201030342c23001460311050300d6004041c450100c0540c9901801402c01d1f070080001401c00100881c40d03541c19009960301000740c6400740302d80001c090310074904800440c0e2807000102d0a006040002c0d00d006100e51320242c550800107115500ca9001c103406e0b100c980c0020806a40001c00e00055802c107101700b80e440341d11460503610040b4001580d206038452855060f21030b0740c0720084080550354603c480300040401c0c420401259076680b410007401c1003 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 839440989 1250 839439739 839439743
    0x71718060f060312090a031b0807080a0816152d091101050a0e09040f111e0f040b0402070c061403060931050303010503010b0411040e1909030c 63
    0x2400c0082842607980e0200c5501840000f400350080c1010418503988075001000c0391907202049050000108030200920110b4078081e540008540303082001d0580b03843d0056206044a40c40444501e02060030381d016030b41d04407180e0401d070252211078140031030040019180c00da5401d10b0905d480600e030700458901c88042c030b034101600400041c20b02c10001121128100034081e10b170111054080e5600c03410090241c4030960030200414101800450712039070307007124222080c140c45502d007003c0c880c000300307403000d01c25040b94252000314a0542c110540090342d500710b0f0140f0100350408400f40d4a6801013102c440000e0070854070f400e1942801081445107104101c040b039900402c2d040000302c40e02c103ca102d010094899026929501c40d000c81c414050a4140d2081c280403040d10804c04004103821400c1c1d0160f801103450b9414071041608407031404507030f0b40c0325a2620f4544c0c5a02074140f000e40b801c0b1201300b0902001ca0780d440c07002021051041402d4800b040c64001d4a0040503000804051054 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 839442239 1250 839440989 839440993
    0x10c060e2e090507050f060d1103061f090501030f0e0a0c17071508040f0203100f0501050a0602070306090f0b0f04030f0c02061603020c0d111002070518071718 70
    0x424040e0a00702140c060702c502400942084500b400282011103400c2c3c900c5030094545442d00351940c0000080f108464620012002c1c0001440040d180070f6900169000140004124840c020440584030f107416101c0d46051540b1075010072100380360340d4400c00d038540407002580c0281e10355140a50b042c11681c003400801c0000c07140020044103001480005407040598502141e908010058455a4005100f116400d242e002d21100503107040c8405000758a1746003011601101c02e071480d505842050300b0030350241c0900d920030040a03600258040803260030440004440fa01810700d44510100b19401400c8005107034280300c0b00c0c401c80386840c1c0c0301d14081e6403039140079200c2034030898801058100207544090140000040065410600c64080d03110380103c0d0305c2030450f6004204207505400082e2080d8011012500352401d0403002e0f40f0500c6101d10207041031608003000528450f90408241e03c80744408800140c140cad000c3c81021803c5d44044485031a64600150709034001d20351101c01c42c900d4 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 839443489 1250 839442239 839442313
    0x80a020a0617042d0303050915130303020c01060f120b090c01050d021303060c031a030a02311a0f2407030302120103060605010801060518010c060e 65
    0x524070802c451076406035080c40942e40d5450326118240100c40b150031181c0b1501a805941c010b22001000348800148652004a0b2074540201c455040c40341b14503215004c1c3e16081c00300440c004825001c81c52055041c1001a1112080c0c4011801021607070000300004400900208014100081403804c240c8190031407201380e691a08565101c0a06200d45c9011a0302072100800c04441ca401178807141c41c02841c0340745030300d40d070303031071304001c0d505c0c010310040c0070a941e0325039861204500d810107810000e041d001401010041d50210b000b4034101c0d07060b249403d42d0604086040548100c001c40b428002040520503036005074481a445c60300380e0080742c4110315400500115083c032039442266144000c1440c08000703d40e40c240c0e0843e5100c1a400c4003090b9082100c280c105964130760340c038060340c000d02002520606000c0094600035040c2c0114050050500c04050a440e001601040c500b10a02c1d203001e031402641b4015001c0c000c50284024603015010f82c070281d00c510600084030740200741d2070781c1e180 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 839444739 1250 839443489 839443499
    0x912051f020c07050607020105120703020d06090506030a06021605060726071d06120f091203090304050d1712070201230103060b0d021009061421040201090b04080a020a 74
    0x32881002d49820858100d031000b08000e2524001400c1c40a0060400d58645030030002030140102e0125545404a030b0301203110344200c40c0510654001c2c00c21000d041103d42441c038002507540041c0c0800405058000400d40d58907100d0303612004007aa804012503480742802880501ba0880000305040c400c3c0c071600020030007440e00381150380a09030303581301c20488011850303100c1c10a401d00130b68160481810020645406546000b20b13100742c1c0000b40148003810241c40203400c09c0116a028103d103901407060044480c0080201d03070840d1002c80d0717000032940c21450164411707411070071708044c04100440c03108810340c20101d003203200f180542d00801007201c94280000000c2c6815000100c03d0f000c6600610001c0d031030b0750051003107101c001d050b80000001c5a00141480c111005804002070001000300210740d00040c240744000d013607001c681e0070460054200c07034034003484d0345038407411501a201243c00c2d07900820764100a041b2210819507160380302d088291751100c0030b11049004400003040020 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 839445989 1250 839444739 839444741
    0xa02010f0605060307120b03030f071104061a03040c090207030c06110a20010213080a1505010b030f071110060302090c040b0427231b030a0c0912051f 66
    0x42030b510000c1c00c042c156203c0700822180318010b820000801540d41c14400300942c0d00b0409020180030f21840c059a900341c9281580e11807802440c0035010b50305000e801c1c48001c0e80084071a60f541d490601d0aa200d90780d80c1404601e056099002a19140c800900301060550011602d171442c3c0c00340405014001c903041158141e4810700070140009100500c02d0040381d00b05400c0055080c0d9064000f50600910b2110203d4943c490351150784c0c290f1150401b00108003044550b8141d11100c0c16040016615000854030a440b00621858880751a0f0300050005070041d11a4104101c0c07610450f446120316030100320081c4018007003a07100e41980c030001074440c0000001c4070192410844514102440e0084c4407020b030720700c00d2141350707256610101300d10164418030545c80000300352110401403207940c4d480c2d40318080011300301c10440741070000307400107040c01242143d8124a05540004900d401c401e01291111059080302c40c1c1101410070280c140440007031030030410b688441314135000c091903800c10342c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 839447239 1250 839445989 839446001
    0xe1e030c030615040e07031515080d020a0f0305070b010b03010602010f18060e070b030901060603051501140a0504030f0503030403021c08011806180911040225050a0b0109020a02010f 80
    0x1031030f41c2007150815120382040e41141d50b00c229541304881c0d0268480e6159005d42c20307400c46140760305a5a100c0c0142008a0000b40001810718402034026505941802074441000b0f00001d0011045110fa00703080611581c00c030342c0000c2e0810114519940c4a860b50400d551080c0f01d220010741c01c0c800c1d900c040d2030f020720481e000340002800100a8460303da5501c005454039103a02d299500600700c0008224120500540c807401c81c20000140c032500301480541140c0014103080038024860030b00d8601d50b600660401008400c4241481c3c581c0c0240d0022105440303188c00090298117480c00503000c0010000196004030321030f400ba503854420034550aa100e8042c80c0d006400200c105004103c2c0340d038a1000100c080c90b40d590040380a58a8404c60546540b00b40d1105c0785599960500c0014030503407a8604a00344000c4500b540303001c1840f0440c0c44044100e69101d0310004000c1d1034682044000c100075961030741d021040c84915a5204000300094100750301c0b0304050750074808501881c60b894428a = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 839448489 1250 839447239 839447251
    0x10602010209060910030b1003140705040e0a0b13060902120f1b0306040b0a0303080403020f1222121b0e100b030907081b030111090a12030e1e030c0306 67
    0x30344d090012041c104034406031024003000503d075858004107456150017501c4480c0702c42a4401148940328400d001c416100c00401003000c10900340f0090100c4010ba4555940002c002400400c04c02c081c0000520100300100c1002d403030b6850001e000410b0a1b4030f4011308055480d41040c069959500340c0131954603c41142c90869440407a50407450042240c0095500160040c00c001034100601e80441c5840c2999041940880c4411080208042d4100f1035a503401c02003501814480301528031800c080c0c00b41c8011140c0a084800c00b01e021041070740a55001000001c0c40c0b100c17031300d541d4207000768951600f400050300e415200401064116660000d50300440d00d0180500300b080c82c000e10603000d50001f41148989020358000090045400c012000440c110b844641b00c08001c0c400030182100c031816401c0d14040402c2c030050b41c00e50340305100042158080004100d1043c01c1c3d2038200d8001ca0421079030740d88480d4145c0354980c00408651342206a550a9003129494003011003050340c3c0300300032a59 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 839449739 1250 839448489 839448499
    0x40203040f02012a2f01091211100315060f020a0206030a0b120705030c041a1009030c0b0d0b01080f0613021b0a1214190e130f05010602010209 63
    0x40c4801544260040c030755803140d8070040840c00620240103000c4a0210702c09440300d28030580341720f022004610705991a40f8264480003150320000e400a00765050a10486520104003080e500c10f11001342a040c084c014020200c00348054000405402450350300084031003602040c60101e0742c0c0740141085807603444d07540c00401102c001c9078200816580002e150070a01911140074004c0c5032201540d1310030103000f0380302615070642094241441c052900421074030a40c14030001c0f44c0481540040b0061007442511842c00c114807070b84050307501c011960b01c0245160f1140e28000b0f640c80700700c0c025264000000e40d0a02240c1903500044a03d9407090326041c060f8200c0d580483c1c1d29180078085030705c56945485000d8140300d140340301d43e214448401c10b021070503082000c400040245c04a80390241c2051410310050141c0b24109000050003150714402066040e01004850f2034010b100344c0222200007030008144109102d50300026100c0414550f40840c2440300100e42a4018000c0d58009500901 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 839450989 1250 839449739 839449763
    0xa09050f0f09150c18120604020102011a1c02040227013515120102121605040303030e0c040501080a020102010f060b0f130807031a0112080703110c03060702011a04020304 75
    0x20503200c540d11164036094541d0380b02421070754549404110781c42e4041b1440240000c1e140c5400060f0945070701e03d6480091354508941c07040b06a9603a0710441680f0780c09202c0148c0c4c21114400302d4024483c0c070a210885150350303500040d200003070200100e4484000c1e038a9441042c101005042000c80740c4412210b84000d520560000c020070748009a0302c0709d007030f41503000030100c1c6034041500710851040e4058540d400081d07031041a80c01013150390300a10400c850ba050404510310040c114040ca01004003056143c50482044181c01c10010781440c0004208018075607640c813006d6607826003684124095401c0c032514013181c0101e0703c11902150900c443e00c40c62700751503000b005016131142c50076990050303141ea0702040d80c40003000300343d01851080c0681203038107000401c455085101680300340e40d2024051078690004012000790f8255a40c90304050031485e070a01c00050074840d4940c903040e058800c540c104401154150003014181d550110403907800c107840000d0209a10048030090300c0320540e81 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 839452239 1250 839450989 839451001
    0x4081801090f06050d05130f030810030203010507080610030b030c0d0c0b0f0703090b040b0403030507050109200406170604080f0424031a0a050f0a09050f0f0915 71
    0x554200044001403501040864a441103004003003416080900002c8012444001d00c9170944540d83c1c2100c5802d4010385611499606c07450803d1000ca4000d080050303480200c0c5040c400e080b2082d000e10f900034007d000d43c0c0790680004040c20812101e207403003000082c081e289800d00904c20491801030181c05032400000c45001d0100d580241c1104541001e03c5a0000411040c0341002e072284501d0214600e0b03840c3c526040c0200882146d4003c2001000700304010041c10841c60101c0702160340c1410f00503141e0740340f414a580100005040504121419044280002c416030f021500b4a2411241080340315240d055101f0307080d019a02d556090303403041e0045004a036500000d040c800360002c1d0102d20b01500d8204c4401d51000c000740341c207071124008410104046d09400340340303c001e03031400588230200345000015500a88500c81c0a004103104003105e980303521018180760140034260070900c403a0074240c0200c130428100700d42d0444500c2d003c001203994510003041c000d0ba01c001c0061102d405403511 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 839453489 1250 839452239 839452267
    0xc160608090c0f01050906032406030106050a030f0e060a0507030e0321060d12020606032103041b090230040302150a060e180c030303070c03110a0609050619050408 72
    0x120040f541409024445900103664a10007540f04658083c903010b210b418040308030210425940c1814410030060005104041d1302006881050560b40707404540702d28000526030080003404440701440c041c00e03080101d090760a4000c140522615541003000018a007086a201d01a00c09002d070344064000d284440c4920f5403448a4100f40020080c10819015945000b070084803110241c0c01360b000a010010303a4038091060f0445d40c0328001a03000c8060b19108014110311004100130400744c0b104040b40b0503003260b1b8001c02d003d02410b036000c41d1b40c4c010707804199003440f0805e203c1410800c1148040c4410001044440d80500d0341900200348204041c90f40084d89a070041c00036049a40c0d80300005800c0746050303401030042c0d00300043c0d02d000c044042c90a6042c041c000303c030a40650300800610a58640c090040070100381c051900c1d070019a03040c220181080305121001c1e19550174241c83c0700c188800403540901455644e9901000e01003107030803d40c151641103d0240c007555048c46009110020 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 839454739 1250 839453489 839453509
    0x506090f0d06061d010317030609010506071401050703091b15120207300201090506180f010606110f060709030803040519050610060903170c030f0c160608090c 70
    0x4901c0c4049103490310307181c441d44080607124404c2511807134000100b05020300584038a0400c004104010301c0c520b80b003404180d075082c041c440c04d4000c500c0001d4500500c140281c2a60390310b81440300a2109052145005002d07014100f000ea0f20f8241c1600801d05000408421008072050340c07c5410701c00c1c0d184001035031800c1c43d8814000e8030b580c080003080d0014540b00700381c005124040c0741030082004802014040c030710341501d0301e200350780c90403124038081240080c11942c046a154500c401c150710580425007083c0c00640078810541c2005404100b294100c582d0020030412181202c06614003410000d03034800098135041c1c04a01c52000500124800100441d40103006108030f82c21520340c56802e0614140700300c0c00f0385854021105000c0c241c1410804607004100c5850b0225160781075403070380315504d41035000c44002000d00013078900900c4c1c0d081c41a1072880070405992030325034003500c1c503098403602c0381041411070308003000c0040f0340c141c080c114080c002c4c10740c4c8008184900c415424004c100c95 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 839455989 1250 839454739 839454743
    0x60e070e1f030c02031303082703100e0f1f140705030415020f1b06070306030b060f011407061b0306061704030207050d060b03010b01111005070509150a090506090f0d 73
    0x420050884000d206c450188004e500c43c80303803a82d4402c0c6090300c0042e0b4640f8280b40030000111100003010664000901081c0c1c40071004d00082e441003841080751802e0b0b00003c09070201d000b14031108145000c003001000f81d070f0038840c0d4140080d682c000029010400c0480e405e10202c3c01c28000325020880d40307030600000a40803d401454000c42d070b194400e0f6900016100d8104034091b4a68901c1d03074005002c0035411159508081c0003c5085564020090800808940c0218612035610220787c0c840c00391065580c03500761071513503100307010b0500d5005450043d60042d801e01c0580d200104051003440b807042220201d039182590b0040030004101010000b800a03411031050070b1004c00d075951402c1c0390802091040310001100c03142c0c5014907081d1070300100d542c2c0c1400042f09d1080c0300c5007004030300d041c8207074181e00c00000c042e900c0c3da0302918035005800103282c01089c02002e010502c110080245000e0005860f444902540c45081008500c14400720b5a0052402e0610b030b042c0342080c01d8001d0700a4 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 839457239 1250 839455989 839455993
    0x30b0a050c3c0c0f0c041a01030905120f0331151103010b0a0305130f02091003080315180405072303010f0b190b030118090501060e070e1f030c02 64
    0x80105140b00155800c80c509801036a040b000c03200040d10b104203c1800100c0303060350240600011415010a5a1141c04000741071688a9451004004007800204140403140c44415160811081c074600150021141441c03201c0c00121001205c10400c1c1c80f6011509410403500c0c800a030b5580c400c20020035103e80410b107149c86070030312100100300f00c02550284c81c130401403503140c0e03160340e600074160790024003a1000200401c254a0211b12000c0c540a42607805850605507030f110201550b8442e0030703513071003c0c103140030210500c81c40210056641003041401c48054500304180203040500f00070a90f4014000c0d0701c5100c0400400c400c3e000c07006540402c44144602c441700d4000440e013912604e110b190186913454000c0b076113900d0004102d0107000750200c1c4400c106400c11546140c18030060003594001485481025000081d0741c0041281581c414000c2c4401c3e0754540e166014944140c0c0e00a01041380782e82000c1c0c060500d0708200598144e840f02d0310300b25040014050700105060840c1034214 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 839458489 1250 839457239 839457337
    0x70516081c051b010606080a0c08010812090303041206150b12160c02091303020601080a030f1202040504020711090c0a0e0d081306020c1e0d170d06030b0a050c 70
    0x4018217109440c020070490315a19524a044080401150100a41c81d424041541d005114000000a549022101c441f14040c1d64000800c0028514040d40c0c0c828900c0004640f0340c0001c0100030742210031401c0da038100c4800d400f500d40c261403000c1c2c02560f5540055003680750000f10010310755403d2041c5804141026200060340e5000300f20b0655046492011001d40000800101641040290300600d40c24015201c0141c040d40c004205e2021480000100002d2082c50b404401c1c0d0366041b90010140144115685d0b0b103140b400041c0040440310552158081c180051002d040c4481160880e40c0c5964a854510118008010180c0c58030041a61001000e01c5a03101000c80d02c00340394050401a0000d00e8031807158420480b00e00000050582c010440c0c0122030301301e8642c040e81100c000d50001c034100b15003c501c441d4240f5400b800c03140802550030700030b0000500c04400403031070180c0300c044001d110700d07036a0140283c0789100b107010b01d04000f4545800f2681c0400540424110240c0c507031401142 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 839459739 1250 839458489 839458537
    0x915081801181a060d170d1a040b09060a050d0501020904290303070c0306050612010f02121005030a03050a0c0206070c0602061803180105040803070516081c05 70
    0x84680680b41411142000c2c03000300d040c09526450f0990203000810a290145080400325100030f0140b00c005140c08030704913101d51118102c00c103480c0b0380040500200004102d202544d40250210000c85000d0340c641000b004a80c01c040000500c0f170031300540ba28042c18a02030070f020100c0003609080cbd403a0355007403001005650755401468207002070300c5011424440d511807005191058a41100e00ca9402040b01d000094207401c64181225044203001400e95a400081100260640c0d002100c070351800000e004c8426556000d4150100c010003a090650784040441c48000310300d000e4694554080300c1586d00113840b44004180e41482d62615040b0810aa40071498641200404503402903040f07109100c138540c100036003a402880c030100d015541c0e08024109071284a00319a10501c503541c1c88820440741d02500c1214020702036002120b64030101c60401c15240c5c1c000c42420b02416000f500c0000c0c020000040e2030080c04c20700c00d0b0100903010f46072410781e800e81c030081250b800c2c2c140792044160 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 839460989 1250 839459739 839459741
    0xc150e31050f040c090c0e01033b0708010911060705030d0608030d05070c26090a08010e010e0321040c15111e06010b09010c0803071e0915081801 64
    0x40241410b044070021400d00e4a01440000403079001007984510f000b0101000079400011400074020030300f40000c0300d0340c4080800c080e070040c0007411070031240050b40842108146a20041204008100b81c0f50b02c0c1c0d031a000c1590071b9401c0040c0241041410340700c0d80c1040c1c50b0440c0100280362041003103c1c80c00c000309481001355015548030340026000450f2800b11101c003401441e41c46245450494000b0307885984000c1d40e08100c02a801c4070710900a0403221a00c00b141c115521058024000503c1603541c46141e8003170400710345050055401c000e62060b00800c0042500c5008071155240040c03039440560324100d80200801c2030310107a1800034000340b80b0311400c6940d1810f20240e51111800b00038680410f103400700415403034645180c450b80031200306001080e02030540b03280b8100c090790f0300c00600c0100c4248803107079030207001010000b046c00a196041542d00c2c0240c200d150b680c962a101c612419654680b00e1b114911002400b040c20441251080ca2683e601c0006030803c1480310103110180e40c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 839462239 1250 839460989 839460991
    0x30a140a06080714090a090c120b090c030601030210120f020403032c030703030c1502030106020a1718040f0f061e05030304080a1b120c150e3105 64
    0x1180598501c81800300200900c42c95029010490b402088089a44042540c800380140003114036507030b41070b0b060204401c20340d1420091000381d401c554a101c031801c04007240402610b00081c0340c800c0c09808d580034200402c5084c100c0360010318881c00d0780d00b4058242c034040c2049000107000e80d5034a0702100d000320f035803028001440c02983d813050f4401d0744040e202c4016510790301403500f000c1400b190409035900000d004090b05d0340b5140040c85e60919240402003604100010401140003100214055a00155a0b424103025a00306458a9038a001160140c801c030318041d500d4070040d00c4801000d08041d001824074003c2c2800004072455600402c0c1c0488510388c01c00c0030b40700c0b6145a400050003e1815060242a00300e0141d8600f40c60082c0c2155180700604008100603141e51145000003c900d030184020013a01c0c2081041920600e02402040c52600600c034100482d604010003403840390f0032613051050003801414842c0840c22408404008106490040c1c6201c191259004046c0380106 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 839463489 1250 839462239 839462251
    0x5071e0c03080c010f0e070b0d1d060609070305071d030309030601030b06010e010203040f03170408060f0703050f06030717010e030c100c050c15040c0305030307120c09050102070902030a14 83
    0x81c0c0c943c9858881c0d0343c00d40b0324a085103240f450826031241c1c0302c0349010401c482210001d074515551811002c411700c2c00380c401401c00e120410400410380b05100c502181e080d10456040b1400092035541c003e0a504449003070380c8050000300e54100b4004426081a5041c0e0080c4004080b241040c80207000640352203000d800c2203c2800d40e02d424820156008680080c15a800340061070620f4182082d50030b50025510000c0c1511220082024204000404907009420843c0989001c1d01e80304d618242e4050080e5030a00000c0d2034140004d91100030003000d02c0c0100030040141083c0c0c0d14103118415401c0842240a589558401d8445000b40b030030002480240341803c060f246e42c80c4003156440442e22014400300901400b001404d24000020402c4040da11403103600c4040f6403254207094445040c16000181540310000c10320420701d400c40d000c007904040550003070100e5062010101c0740074045115a50250740401c200707008015040d005158001102200014400707103008031207185c02c10996217 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 839464739 1250 839463489 839463503
    0x10504090c02010c200619020403020a0f050a052e1b050a15060305031204050a0602040801020d110a1205151f090803090904030c02181915050105071e0c03 68
    0x10764100354010801c0302000b20f12480703d500000250405640b103000013000451f038628484000b000d942007940c180c50195030081c01c402001c0340c50785a94110f41042d07004141c4a0034411800007083d2814401c0701802d810000d1100e4a5510001e0000340c3d00760b8040d680783e06005541008985404490a68001c000c3c003c0d00103281318017890030036034902c03030705080f009040908240052000c03c90000c2190854000e91402881c0d60b940c0341800307030400d00036100091846000080004200d01c05402410118075844001c1014050080d440380e158400c2200c04808105d0035a0841d21600444d4009684140c0380140d80004a4651000850030030501c100066110460516541c105034090011800f602000000354030304584040064500e245c028401003c101c040ca4000e000c41d12002c111b96641d064507602d04000b41080c40004904000461006448629144200a15407401142c0204840c07040c1c40351842c042854503111103410200c401031000060b40c1ca90000002e403d104500011401909 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 839465989 1250 839464739 839464751
    0x40b03070e0423060913260d051801090c051c05010603030f020d0503010323150705090f0d020a1a0c0303130c0e04150509121305180c03060f010504090c0201 69
    0x4402a43c0d00c0140210307000c0c901500410038800b0700a0b400c01507503034000e070092106054250340524030048207062070f04400700200e04c600d00e5504a0708101e00401082c120500c02040b6606074901320f480c141405031840704080000c01143c101541d903480d0890f400c5210180072000e5488507400c1d2941c0354412400601a4910300120503414466040a03401501d80b6030f156524645450010000f05014030012001d0081c05440400c2d0401c0406820303088030b0050b2850389407081c00a0801e07000001c2c080c0c000c000118004031a880c01c00c0000c4100d40e4000c0044605900341280300540d1080c0100708441154104803040c40d000003007003c5c1d8401c0130300c81121003500c1c0c0b10b89040d0380810029072003d061492440d082c000040c200f940c04005800f0a035030001510359801590303030b1030305da0040c50800340c003480001c3c0b503841c0340074107030004054540075148500c15800070109041d41d100300b102c4c2103401e2075086c404a070840c0b4225441c01c401c000149001d83c02c003a1034240000446240c00b80000160b0755501d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 839467239 1250 839465989 839466041
    0x603080306091e1b0904050f09070603021e0c07030f080a12020313140c0a030b0a1d070312050403060c0c14010204081510030b090d03061a040b03070e04 67
    0x40306541d40f01d143c042c40010342e0704000d20680b82d8007501901c03c40c00308014614040c55041c008040d2100d9600c010030a01c06801c00381001110b2141c00c2c1c880313403064024020701041e803d00900031070314105203103c0ba0700c0c6900c03c0340940e041103400c032103c43c0d181401051000400304413a0044079982d1402460041d5503001481000341600080786444800e41c0c0c014020400f03d502c500b140c07407066507041020710200060700e0003c2030401c0c481d0480950300c80b40542020040c00040c88650b0310030fa1f840e0004205041026a282a000d640000000c03050340c00284c00b48001074101035803088000003410b103241099100c1c1e880c08290b5150b1028000001e42c070120900c180011041c00600d5601103500031498142404c001d103480d00405207121408401000111341c01414480e482c000454002c0d032072080034100106c40303a849040f0503505d00000b030708000000c1498440d2403100219625212003079440c0501e80150030003d6040100341d4800d1000e00e02e280049501c072801541c1d01e118681d008210000000 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 839468489 1250 839467239 839467249
    0x51009170321190920010905090108070303030e0a0b040312060b03071116030221030f0c03071a1e250302131428150909060608040302060c0d0605040603080306 70
    0x10300c0f050704581c106904600410549001d83c4d81356106030340451400c00700c100050f140e043d40c80d8015a0419808400040c42c464080307801826a4030030364003404000c00c1c100696580390001c14015118612082c04640028010015015140c05448000c0b404544d1071034609001c0c1c0080310312002180301ea0741d00748070482e0180080f1030b051000665016501d07043d070300460040c0398130b407006052208006003042002901042501d40c02c1c403801c091240d55561120005440740c029200c100c4110420030302650560202101d080d00c20021182e5403140c0282040762040e0000001c0c0200d65505c1c1240030240054514004890b290100d580300581d86e02c04031082c08906040f6684210f4a0b81104507440d140d1b42d0301c9680454002060340142846042c6806156403000390a51100c840c01d01c0c0514900c0d8035a800892a008a4840c0325042181c19528042690962b00441e8001e0040c2c1005000a694a400c100503003041026a0400901070b03881e13030013080490b06035801c00d88000c00301000300709491400d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 839469739 1250 839468489 839468521
    0x120114060112140a0203090a05010f060e010506391c09061d10020309030d0309150e0c010309030207050a061e020f0d140f030f06010801051009170321 66
    0x80034003c0141107844400100400c4018044606403500007001c15030003241008144e080542000007045074540c21521400140490b1240c552600542000000c2c4c41c581034050b224429152030600c2e010118030489a4021403c441c1e00d41d4484809080c4006040d000308027402908072141840a5000440c06002d082c10000e58841400c0190800003280403081260344818402e00c01d881925080c64419000d03803c4d1300440c121b058040c4114080141c1181e8140c001148060048100c9124800c030071031424165542c0140c1246030b50b2040310103040551099000c0595940a0310594010340c0d100d2000450b8082940d000030001400d4081584204a2004a00b030316100c0a0000f001d440c2e11201c1e009490f00001407215003484194002c020210b1070402c12030b214081034501d083d95070300d0708580a0710a1181520041c1c000b42640d000414603040035504078915034025150980160b180040c5045d00004075150282c1c24013091004941d039406005071140001001c0b40c1810745407400764154107440e41 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 839470989 1250 839469739 839469767
    0xc0b2a03070212070510020313031115062e030b0a09050702070e070905040204030c170105151e06070b04170f0409020f1306020f010c050f0a0e1201140601 68
    0x20400a00c0036158000540c08840310024510645803056418998181080d042c1c030070b01141d00000c200810050100140c42c9800d12984a44d100107125030b015030394840d002140085c540140001042451501d1108007a440800d40718100380300011480f9410141b034180c1c24000800e44603540003400e80390112300030001d044045010400341c42c0c030040003540c42c03009200300041c0c02031034801710300300c1441520030001038500603205654071696440e0980048035580b04d1680910780c041e9500b8403420303042c007405000d05403d4000040d509021000c0000c24101c40a8140100042413982107058a0341006445001d00812504185203000d040184094451051221510b02c0401c0064920203c04060f60152011103000503110306a08c60313111080c0c030400b2202054240c1d02c01001582e954001117010107440c0450003808501c80910095500d80100403050380e0900050060102c039a03c2503185c3e00441400902c18590091503201d040c2c03c5942072050004841d210104014480d42c0003131f49034041c41 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 839472239 1250 839470989 839471071
    0x4060e0f0f0d0c210b0f04260d061509030602090112050a0209040b09070c0807170705070f0501110307080d150b030906060108041115040914010e06040e0604030309030c0b 75
    0x20190b5420b014518001c25015100c104080421f083c082038045240308900c03052065200905001645215a00034032221705c507990800c1d03004200740044284c00055030300305441e8000c03d1400c6954040c065008810524100084840d04402d1030111340100b500845204c0c2c401699444020b0510080c2e56001c0c905c4c5010b0030b24031003400707440c561059010300010f070030040d03080d242d6446113009460440c01020449029001081c943c042c0000416000d04684c840070390702440079560401514581090040c80a06410a110101c007140940c0020b2420b240d2000e00060010200c2036000100c013103942050299150100410a03281d00811070b954000000342001031040c68aa5903c84912140d80210b602a010b02c0041c12112842c210641d8054403d0340e0701071101c100421724011b4240001d200c0c4401c1d80c0824404210207040520a00301b0301d80034400038107559540c5031001c1d8042c00b41440c01b101040406400400400c900c0220b940c01401d03400307100070401801c0307003118210328401043c02c0c180c0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 839473489 1250 839472239 839472299
    0x12010f020a050712091508041e06021b06010f030201034109010605090c0d0b06181e01020604080307270e071103092b0302150c04060e0f0f0d0c 63
    0x103400c1601e10521308207900c2e111503c0da8880c64410240036140d0b032003003001d65030502791000b000500d40252030180d64003003c08240310809003120783d0700c10080c032444075041d40305041071015510940010780c20025902040c48440f40708000c008400d0a1303410352111a0f00c0007441e110300c4030610f00300d80f034221a000d0020704c4898202000603d65600c064807c8480d40c1c40040d0070340c0c031000181c0207021214001400942c036042c501c0007401064844200d250300c1101500c0040d800d40c01d886401e03800102d01030303000707040075070f01c13030780e4800940d4805490901442881004000a660310b100b02040d0b866451030001112854a0071342608002c028207140d042c446015402003002c2000010344810450071038224242000d1042e61130f00084525a184810501c064404001d0640008070014071102080503001103039140c8141c0007041c02a0300842c1d0005503a807041292515081040d12034400004020035001c40280c2c0004020010f00d4504490394649042e0070441d0000302d01e0000c42d035007240000d401c80 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 839474739 1250 839473489 839473499
    0x15040828020d030221010906090e060c1210080d02030a030e0604111005040506041203110a0b072d080f0a06030b040b04030c05060903121501020a0212010f020a05071209 74
    0x342e20500100034101940802d1003030543c905c45820040c10200c0e0007030070344156125402807000e01658022076200504000910b1a61440056070b24480e065207034109003403020100203441c2c103010241201c0c800c040491030105181000344000002c00500f82c00031540c546070100c000d410b4030341140480031140c0085040201241814004401c0100c00f2603000600c2c4c400403005035500d01881d0001900004080340c00b113054450084821540350190b16201c0700307040851642c50303840c000100001d2400c030b09030703011800d09405000040300804030710703004000040f0b0001c4d0617490b140d071010300c000c00180340400340304c041900c000700a83c001c2c5019400340103050540e1540c00c1d4070b9001600c020f000852090001e014107201e5419140d000f540072045c0da5541c02c0010409503a9000b40c02ca06901140d1000800d0212160340e094040e13040041c1c000d001780202a8003080001c810541001860f07540302d0007140c610207914401441d070000b003500c0d910b813034841500300300b130141d40150750b80d20a2018151040c09 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 839475989 1250 839474739 839474743
    0x9080616030213140f0a060507110f0d030509090601052d0d0608070e1f090e10061d0604090c0b0f07050d0e010e030601150c02031504082802 62
    0x140c019808401204400101a0110001d214211001074002d09545000c104003943e1406564103500403960f10386442c02d0701081000c3d418407445003c0201e074082000f940040d8aa4110140710103000b401c12038407058000c0400e443c62249502100010340002c0c0c0000645440c4c5007054120380e0071701c0c0640c00d1003140640c5c4040340183e90007180d075000c017042d106032140c0c06840480300c0142d440e010a00c0350f40e9444803407658030409401207662600d5140e0020340e400d1f241c0f42511400c81980f0b05004442407629802ca0f005200407000c014082c0203c40341c0e8503c124141c01780400034108214041e849101c001d001030810385018102511541c00c121540780415440303a1101c1c240c41c075048125a0f543e0a40400043c20b00c56008c001b4a40d01036041d11500d0316800c2404000503190a0722860090740c84a0201238503940b0074058805000180b001015130107101e0071850f0080d500c003404036055410b0001c102240c5810441c1d080300c04000c006022440c003441e049151203001607110b100007022450342e001075 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 839477239 1250 839475989 839475991
    0x604090b21062e0f15020318010f0c060e0c0a09050c09010e031510150f02070b031b0309010501090b031618061d0603120a050f030406020f04081606090806 68
    0x2198a510041940d22804440d1212100b6900b880f01000d01903a81c40c0d01202040d4031900c1a00d100c02c100c031042d00c00c0300c0e001104039440c400c111409061900055001550044a0722a02d032042194401c117910002d0014800c06400e041040000d0041f07159500400084540c550001c1000c1e504000c2808860802c039429905403000900380f400c10814031401081c90101c030b042c4004a04042e000900c003180d4590005e0380183d0780410642004404101015154840b03c0614030006a0200e10b00b00012008440036680001e0400c540c0e42100c201c903402200e094100703036141d5002c0d03507584004011031102e91103201c406410a0300940180041e00854aa030420644a6141051804c00488825907c0e030340c0300780041c09005c8000c000044611400c1c00c00b2000071104140030b8801c9441c9807200f002d00700140d9a0b9040300e9600c0b541741c0611042c448900744c1024200311041c80e02803145806062103000584050101c2ca001020b51700c841d501c0c0c00c48078170f1540e030005080c001010400c0c049040046441 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 839478489 1250 839477239 839477251
    0x91a09091908071e0b0f010e09100506040b030106030501020909010909051921030c090501050f090f040231090902090703020304050a0606060e0301140f0417090604090b2106 76
    0x426110f90240c00c1000d400c0300c03081c1098226612040c2140100714101d8056800343c203680c00c50031030981e2101185400c41400f80ea84005580c8403100281e6880c41a800c4039511107000790000c2039440b50440880c0c252801c1e0b410455080e5004030301e05615041c001041801000303140d0013404501d010b41c5035140c48400342041000e81c20522040901400079134040508044c1e410300303659881800c0003000400808601c2040c100041c604a0005401c0d84510300f0303208200c48801c00d4030315058102c000c1050a03558400042d03001502840400d00c0903412903080c0152202c40030f0341d200c010a00c00500e040034500d9820800c40103181041c42c40c05a110400003d92101c41410b005a8036200c5081880c60880d64460042c5490f06218010458952010301c4030785184041e0001d002280070305c00090703c0b003001224079118100400000501091410350041c0403c00044041480c208820001c84c807035034413036001003c0715a11034030001843d040080290785041181040b0700c90001c0e00d060020b131a864041d000d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 839479739 1250 839478489 839478503
    0x1701110702010f02120f0306040b01080702101805010903050405010207080712020904060902150a0f081e0612120403020112020702090417091201050402190e0109020a09091a090919 79
    0xf041d1907500801c2020f551074100c20040340c6500d01030600385401e6000300c48950142d82400101d04465002c0c00c8114040d0800e500501200d144a41d1210020801e104041d10b40090752031100011407000e06c1000285170081e070b03d460b900c0c3e0034240068600405680f0240c0258032454040105103510303810f02a800b0350484a41c41c454840f4100a4050200380d10043e5100c82e044170800c0c2c40080c1071004100807242900c0c1d0800c107140c0d0300025215450115002034512824244c2c000c8a01d0040d43c090354450380042040b4200041d1003001841e10200c0121400c5148000600344150b40e0070046003420b00b07555072003c1d46030032950b601284907000040c00040246c2d40070141000e2140c0903a0903181e031031001401010111491300382840c064813042d02c0a07401100c45640303415411400c0c0044800351500095140700342c0c5d182000d01c0000b917000020400070408200f00201c1c03003d0107400380030981c01584049040300081d0104024a0600160010030903502402160b0b10b04014008081155600116 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 839480989 1250 839479739 839479757
    0x24020c180f07030e0f060a0b0418172808060604060e09040501020c1b0414061e0a090513021801181112100806010506070201081303090503030d06170111070201 70
    0x10300fa00a0900c10302d02c1e04c06030081d07110104582c0e40c00641c0c1d0f8482e1070710324001d00c0b0100c0100284401c4900301c211300b28884c600c0a4010001c242001c1d03c60200c00855a05103180500220b40741545c50380001e8803030300081c01e920f031107401103510622090f0803030001ca642900e010700c4c0070760190078640c076403991501480f8050006418404290305070340c01101000141d440101c041c42e0040f410105141c0914829403400d42c08410b42044c21210034441d1070b020306444400340c9610500585042101c01807580403030610301c040781c41071090148034003808101100c0c8612420318410442c1e01101140c5040500e030f07058004200e00c0030116490780308202201c1000481c5c04c0c191034160810f20074080c010084100308401d11440700321550313010080310480b00941c1c030f807641c0360010030580d0f104243c0060300250305c0300c004c42c480300c450300c40310f01280d486420000300c0155501d000c00d080d600806a920320990b035a92040080030046032522032035161240c000c010f690384e822800e83c030324060118042d0402040361 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 839482239 1250 839480989 839481001
    0x90a0c020a05072d030c0b0304080910050306090708220c1a040501090b0301050d02060c0a05100b040c090f091e050405010b040c0201020711040e0724020c180f 70
    0x400010350a50308032059842c8a81c80e12000280b801d2000f80c411401190340e00c000d5613031498003414906890703000b00c4800300f461034902c0e1140c0c43c0d0400703442903504035000c0000c0e8a042c0d58503002d55074043d8654840b82e0f00ca141003000c0240f4100024114030501002000b0003900c00101d0b29003020703a0ba4180340061032001c1500300903c0100c226004140842c603c1354200303100e11030b240e01074001c440c1c00341c0c0d41000d00340d00c1d40c1c0e01107941e000a01c10141c01c4802e00c00c85600500d459406040741d006088200c2c2e10901c0603890b6131385810300d07581020610617aa401c2d0303a41a41840d0081501d4031140d8100350743c100f07140204019005455200b1401a81d5442500804500511202e000840721038007080c8001e040078240607000340703100040c3c544181d281c2405803100600600a4400c450381200c001c584800800c0180000740c0020070380b0386030900600c10082113a0690000030000e41c026201540d500710801c1c04068504040380200c40e00c00e0100010810f81c4c050141d821503449003030010066581c0d01c40d1 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 839483489 1250 839482239 839482243
    0x4050d030221130c0f0305030d050403050c01090308060405060607020307170f06041209090b0603070e010504050307030b0907120f080c070510084c05090103050d0908010b090a0c02 79
    0x9041e2400d441c24120074808081c1070701200c0c4101a0013030300c1c413180c074a0781d4803c2014292003510004145401c01e1000b81c1484030980c0c40079a00078080c9c1491840c0c101070b4544142101c0b11441c00300e01140c0700105101907030600d8420140d0194003940d50618200098000951300d913124800d0321310400501030b011024802c00d1000003041040c0074200d41060600b032400703074080b80320101903400041e80c0300070000f5845001d008504c4042006032440380746031543d96044690300700c00c1d1880d078148002040001802c3e10104076142c02140182c0c601549802c200b4441d0f8140700c425400084c8038074007041e01d44003003416149019031156201c22161340d42d00002c0900c50030003042c0d0780020b07440300000480414094100414503c2004850500e04a00b440c054401c183e6050700349003c0c0d8580b41046d410b008440c8451100340240c11390300f504041541d80e402c00243d240409802c01c0301d10f030308007100702c0800c6508200c10401070031520000744204d90300c2d0004108405c0c801001c50304040e4440c030003031546e00c0c02 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 839484739 1250 839483489 839483527
    0x9010c1e171b130602060a1808070c0e1f0e0103030f051318230403021c0e091008060c070b2202150a022401030830160804050d0302 58
    0x1001c841961104010f003440708980500e4400c02016000304000207040200d980300c1c03109100d15001c0703980034066854880603440d4008500455128031402008924074410b071765484e01c01c244010308041040c0350b6901c2c50714400380030b600c07217225500722000500009402580c0f2030446484c2d854031a4850f1007a40c4040401d000300e40c03040b0808002c1c0c0c0c0c805200852a90403502c994484010480c03110b2940fa19008525034080314040c00581180c1c01074542c550030f41c0070441041d101071811240b60500300300003442d02102a03072015070494103c08204241c44090000c41c2e0300084401c0b03c40c0c10600035448250862500400007146c101e624254460703010340803101c633032100c0d030046c000800e942e03544812800c00741c1c0f02e001660094443c0801e95645c2413a01100041d8005080b43e1001d1581d18550ba181c2041d00304010701e885020300c0c11000b51200c4500e80c000451581c60f01c0c1200101d0420075401c50a0326561900700c0b08018001e010031002c2580060060b40c0070031a031500607503a06c8400d00c082c0007402 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 839485989 1250 839484739 839484781
    0xe0c12040303021305030a030e1c0c0b042903130204090503070c031e02011e021504030801062a120207050a09020d0c0503060d0f0201140309010c1e17 66
    0x21401003400140765160380541313604440e04039100c400585840030560348904110000340040ca07603514040c01804c0981005041500f8100c5144170112a5a203070b800140c1903420903806040c004c102041800311070400105649440200c003050981c890451003510f1200800804440000b046005c0443d292580075144164209058907259045480c0007000e4a03001c0c402038403089170428401c00b04001840880f03900380e505854003130f86c156080304101e1241c0c40015a0405600400c00044410500324211901c01c134802d64896045604009020303041c11070240d81099400300c4241082c5810344031524014245801c5800120988902c0c80101c0c60f026080c0c110a0704051107004c00aa40c2d01150050044171a06031418003084112100840d098001101c51135404481040440302086603003494039195801890b100c070b004040d01e00d0b070550300d910950f40c000b2241c4d911052040600e0703000030400500c0500c030500c89903c10f80b880004140640c1c8410103185400d00300041225131a5402004015038 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 839487239 1250 839485989 839486017
    0x105091c0f080d0b012a03110712230712330c02060c030f011a0904110306030c030c06030106120204050d060504050d091508070c0c0305070521070e0c 66
    0x16480302c0061000c4c0070003054840c01301d642d080012400e800d00003841d926101701c0c24003100c14003440e501d08889031502400e1a00483c01135a03000705460382148502c070f03007030f5006180200c040001c000101100740c01c116088030283d0400312050001c4600c170024a81640c0c5c00144011f03828441e6580726100f101a00492248001d44c0c1c90005041900d5801a200609141d000d89006654030504610144021512000c606242e50300500590f903a000c802c0d070400003003504003401e00c86000c000c24110342e03c410742440b40d10004030801c80240341c10009070114102c20707030180041c0e403514400b00c1c0030b07400103014403001e000700c24450b000c030b0400f40d506480050000500014211501d41442002400140d4040d2200d010350b42980c01e40c107008959100c122054a2009103900c406c0c4003085810010152240c1c08003e580c0c0c442074081025030035030401440c024000b0f410143c0c505010030050702c0c190b00b1b00c0310b801c0c00000f0580290800110740381c03007213503558019903040d44d4650420404510030306080c12034031 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 839488489 1250 839487239 839487247
    0x6010f0b0d1d0715020309060409110c07141309020904030806040e100203040b0907180b13050a05160e06040e040320030306031b100c020406090603150b0105091c0f08 73
    0x110005582000c8413511032151411151400e0200d072603204070700440d07410050401081004007580c2d4407032030281c42d4400b922404c0c107280e02221804c095113a8000c022010403103410240310714150b21103000020015908000004607503012600340d40c0b00500140c02e0000600008005480f96001084840d5070001680c1200004d61000701c02500700b96000c0c1d942d0b241c0b020000310052030001c0c480d4160f03140e54011020200400104502902e0822881e40d00030102107514040c10441d400340710b00035000a20045101d20348610421049110000550700b0002c01c2070b1143c2380c40d140c0c00b0448040c1e41d64800d00303020300c2d540c0d41030585004c0c0b00d5a0b06000d96103060b1030b219040260220180d805003504905a403403205415400c000703c40403048001c3d9020705000b210b0001e180c0200d0902c00103030b10240c0040b03001ca5030b5402007403c940c01ba51094494845402c000c41446070036100c0c45d903000000342400e908049011000c1070301180d8000700181c1c600d40d9003d801c814020641710314104103031300a000d6590b0b = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 839489739 1250 839488489 839488541
    0x7110c04090f11090118053304053303031917010e0601120510150207090b0d08031305010902030102031806090703080901050715020a03021b06010f0b0d 67
    0x1508807202060380c0a44444560000a01e0134800d954103c404000e5074615003600b80304070500500c806021485841544610740700000e191080340440200c0f640401005001c1d120103200540c5c40003840072641c10299400c01460181303842c881750903c5440038802d044642c011001c00e24511445220300040c5290007282c540c9650701c900c441002c0b0410b03445446090741d0706c4150010081c001c1c0d61150200d8014400c12042e0035075035005079404908000d50692050391004611031000c024880c103801600480030030700031400c681c0928411041c05540c80e101205082e00c500b046400042d102045655074030121030300380242501f000c590a600240210350724180101c00500321031421000005038040c0313034000344002c2404600b0000303c030b4200d4000e40c40c1c058030750f00441703455020000445d2350003204844103088490030310207081541c0442e18010380da0f41c50b100c03c6070002c9054084181042e44520018000d2144400390401203603803140d206074480000e00720310000f0b44501c1c001c0c0d0748580005030072004 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 839490989 1250 839489739 839489753
    0x20c07030f020a0905010e072a050105070327080a020709180b06030309030a290a020d0525080403141303021e09010b07020103090c0605070c0605040e07110c0409 71
    0x71880e10880340783c0805a03651a544007034441c2441900641720001d400540c102d030151a1a0b80614001761030851344e440d05040b4003c0301d07400c6200940e0940c0d510001c104400381c162040c82c915141141d000f8500607018260800c0d840e01402d4000c207824000304810300e541c3d00801142000d0b01c0071083c144100041a00d00680c030103103400d415a550012040440d4041c2008001c5803110700e00035018040740b50365900c9035913081c0f0030794101c04081200c44803100d031a20891a0140c1c094030118801507611070b041c589000a5171000b40181301e0188141103030204520302545d42c1e03101003556091540c50f076a141d050980329012001080c01c44c1c403c0010742c407103814010501c0c84064038422904c503a0090b031100300c1e514142d0300403007855800082c95001408035550090290160510500d400310b46007a03c0d03681c1a94000495101c1404640045284d030204850014184040c1025241807824146010100714020382d002e1300f844240b10700068000c103002c070240015031a0000c090310a105010003407030009 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 839492239 1250 839490989 839491013
    0x14011805100c210504020a0503190606080606210a080f0307120506060703030e100212040308060409110d020a080f030a0905030c24090d0c0806070908100f020c0703 72
    0x1c40051820b110b4644070b9010f10708201c821407000480030400a045004a0000c110140069a00c47c150307140000d1075560800c60301e003408800341000007940c0c40921384002510002d8008403415004081000310907102d503092400503100c0e0f040555140c245c0e000d6154100140510007800d6250b000922064801c038140c0114010020b0f5a9005401e60199401d00101d07a020368144d41e10100800c000f50200c0d20030b410103441e1607c44415030300000b8034000420120f902c503805440342a0070320700801c8141604241c007180c0c4404140c50038000d41c229035603006101c2e1035070200d50f84141c00c2c140444007552074011648001d001e102d82103078254065032010640e2031f0000e01d0460000380404030702050034207003c0351000e00d14501402c0c514060104070328680c0d620101d40a40c0303403469000c1c02241700310354510f44c0701064980a280c28201080c203026583e07060110040105c41405055201004404000039956030007002d0708000103030b46010301d581c0030701074490030b04150818401d410001c002e0000d099010 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 839493489 1250 839492239 839492263
    0xa0b18070831032d05180f0901080c120c030703030c1a0901050a0606021504080318010f0504030f02010c080708070c0c1e15320a270302030a14011805 66
    0xc030358403000e844d40d43c1400310888500b41307000440500c060b0140002c04441402003001c000d0640780e03e50f0088022400d0840b090340302c248150711500c402000350400d0381403401c1001d50300000d03000800b605c2c0c012907502c203074901c0001c0400c21080c0e0310707205005101c20403075100801001c1e0708016040ca104d80714042c1030240c61140d0304520b00000010854000604542c600c1a2030085194036507035138940d650390350002000d803040c00f5400c1c90900c264100030721580110046800002a4504240c10000c100d5180141c1c41801c1d0b80c91b10184c81049904403400315880b02d09440c008503145c0e21604121403ca980e8000103204410794000420b8a810388200a41038404e0380041036401680c1d01001c0c1401c0e69400042004151424030100f0102c400075a111141c40c00070a664620301c0c9035002001096011810000004894205806d81148144400c1c6070284044005041c0f050840c0c000a441e403440c80c1e4014980380c140c52140103454829007010200584042032a821f0107207500300183c442043c9004 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 839494739 1250 839493489 839493527
    0x204020d0f0e3c030a030204093e09130905060a0c050f030c1c09030e03070f270606050c0d020318060a020111030a0b1807083103 57
    0x320010a40025402280003e000c00304441542c034082c038040b80b05003070800905040440c1091200380c00f4200010000396102e1b9400690704d43c6050001c404440b142c40d502c0c1500d2040743c140c0f00441c010b51102c0e5424146d41c51101d082c034008030b070f1544824820684c2c0150045082c0701e8885004086a01c40c0c10740c14050000c0d0748103980c40701001000c58a2203c20345000c00c4080c4156840c40d44104080c60740301d405480700c1454003200d00700703401a00500409000c1d01d142ca8a184808041d88500c0560b40c00c08181c005026030f6081100e40c0400b403074103016182180800c41030002c1200040c4a02d174440c6242e1308000c1150355243c036802030251748400240f0f0041e10541760307100b102510000031561141140c0c844200340310098800c100450303110100004c115901d41c42c3d201c1030f20454000544c05040e41003000104480c0c1300d014000c04280d030103d080340001802040010f01508094841e50141090301031500364410303842160710102d000404044140140c0000c1000c040c0c220901f11804568902 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 839495989 1250 839494739 839494751
    0x151d1e0c0c06090a0507063219020708060a0c0309021504051903050d05160501060828110f031f0209011b05070302060a11030d150b160b040c030204020d0f 68
    0x1080d0f03a80d00356504004d04a038007007281004102e11540394045c41171a894448d00d42243c0c00800352030a004040302040c660f500006580e09a030501f001d14800e404003500140140c4c1c1e160482c032603101c0394002c0006c0740240d1034802c10024035110340c1c007602c41954010309142c01c88502088428a54110f402294014a019100c080c20310003902c0324003080780c1e03100e00109250805800219425000b807506450849900e10194000440c20700404000e010640c004001c104900007036541003803040601c0b044014a0500400c000c11081c1c1c0304031042c0c2400341e90f400c82c2c91102101182c0343c005090014505003d0503103107030058400d144c00030070390030909980b244a240002c3c00080c1d103211088000a20b5a805400708200505022000d005943c41d281044a410f11503c2c058508540c40300080120702640d421019024005c0e8810420241441c43c5249040920b641212800c01e601d000e009424940341100050811046000c01005140d0140c025926020842441d40160041c03842211b801800d040c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 839497239 1250 839495989 839496001
    0xc0102040e011d040f1103030a02010e0d171f05100302030a1a0f0d230a02120f0d0e0a1d10090c02150a0e07060206040501151d1e0c0c06 60
    0x1d2040c9aa18030040ea10300f00700d40311a5211750640801100c216000403065043d00181d5800b4005400099840e40002c184050155006402c11001c202c8180034082c0014440c0c03a4000350102c503642c000d000422031005c110500a1000e410200e580c0807543c08220400707418031250341038021394060441c1840900a01c40084060313002e801503104019040146407050b10710758502015501d078220f010b0f05029412440c80050707031110a0004100050a07404036154208504103110301c4684102481c001d0288124170b80051030311044061281d004100801d0791111182c0e4604064074004d1a100030364022444e10a85940d2203064200d9241001d029460f0b40098402803070b000781e030a00d03a80c603800360a0560f02c0d08040900c0b001301030f240c001050b50b0303043c07901c2400d4410007508001d06000d4004000c245001d01e0880e0030344003285045c0c1c00b1056140c800308484c200711004503420698000c86c094240d030700d080c00301400c4914802c1843c0640603030780500c4074909800006200301d10400043e12040c0e03440b2 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 839498489 1250 839497239 839497259
    0x8031201091b18030803161d03060c0a020106090219020c01031104091505030a0302010902090106032a02010e0d03020c0c030102031521030304061b0e240702060c0102040e01 76
    0x1001c06070202c44000c910001c090341c4039180714201ca88901c600d028180f41c036034407943c1503a002142d001c0d00c14810241a81225500071031404000c02004060524981404000c25141e00b40135083c113210100100e2001140c0d4001c0d00400007500ca07500c4115100d12180240d02080804880d1090240c0503102c1803200c5548207008140201000b4180285801e280c0000c900007000402c1003035401100711500403d0683d41400144a85406039001080303003011401000814036069022030f040c5480c0c10448645007648100000b24070116038030301804075540c1001a809042e034520401d1503170041c00c841c2d4080d0fa17050b6014051100e13400781260404c4400d442410300302c3c40180c0310313420b40e03407048040800d643c506078105a46080c2c1c6042800103070a10321405030310f5508251400c80310180ca07500c25014000d1b1b4181c1c0d14603a400d540c07600d20406a4480041190a40301c042e40c03101414200f0343e04035546251038200c401040e409401241e540e24003400c904d000303400038000c030014000d003a000001d0190302 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 839499739 1250 839498489 839498501
    0x61606200a090e0601030905100b18090703030e01032309071505031b040503030f030a0b0907080a150f03080c0f061b03041506090b040501150c0f020a08070803120109 73
    0x110340b100d0030704500b410b032810241140206028101926040d9000010f00d09018412800040c0c0d03501051108040f01003048100801f50400200c001600030030144050004e581011250141004203100e180c80e80102d01400c84584500580180358000b426291038a199644c030400f0a141510081c6882e18080001c1c903442c4545203001480500100d508003401c0c140c031207084140c955070f461410350303904046070031600701c1c1c01000d040c8400401000a040041d00070141c00241c00c8030103800c06e140c030304000b404510001c1c2440ea40b1503603541c079100d050300d124140000904030046a40c030403a681c80c50720f11007591113400300102a00a4910308074030820001203090040c40180d1810500e058610201d00701c54000400607174400c40c4200c20041803615500c00c1ca00a00a41000861003454000c28003080c0d617410b0344010100c00150060180d1a0381c0b1052a5035810fa00c808000d0071649a40000f031801c000c150060142c5000704000010101e1001000b441110417031074030120140c0c1e80708034400c00c80384 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 839500989 1250 839499739 839499757
    0x5030705010e031606180801180303051003150c11010501030b07182105060718180f02030a0c1805060a140c0d180f05030709020906160620 61
    0x121048050100e9030140040c001400009411121480c150301c041c03505500e100d40c401004280007040c20800e0400d01c1c07500d940903004000003409044c500c04100925144084070180815566171301003600c0c00c0b12456400300443c0c10110560454070301c10700c0c1500800c88410320101251002c150a0788400c410301805048075004245281c4940d1009020b96000c905402d5064008001c07203000300705c0420b0001903c0c070006024403480a617955920b400c46c41c0079006040b0009001d0026840607001d07136115580340a503120900380d0000050b0682e040c03009040741e040c1c4200d1590012041010300840c40c4d20010322081c265903404103005191031100c282c030486015082d08480b08100090443e40140300703c0ca1139070000c48209160000f03030b0b40301d603050502e8803c00030005514600341c440c811100d084000702900c842c000c401d118509e045c0000760390f141e20340701d414002500071400000355a41d20041d40c000b00e06400b01521042640e203451801070662501c00303041d54440b084540100028001501e100c04 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 839502239 1250 839500989 839500993
    0x3030105060a050c0715120e1b030709090b06090601080112030503060d02030a12020f0c06250c18110903062415130605070804120c0e0114030105100503 67
    0x6400e14040c041a80c0c800c0c8041428050100084401e03818100082c00c0180f44140c0c42ca00141001c0e10300074000200340c2644d45400d401c14001141c0040003044d0085400030040340c240b403401300746001c41d081520360350201d295145001c03200000c0c030940402103440748000302ca03040300c1541c807880155041c400c01e001c0c054a0142e08080b50340000e010304000c54103c2c600501540741c6403219800689040218a400c44540382280d03032500d411901001b0010b840103260001c3c0c80b000840c9404640d00b802490460594900e4401c030a5030941c07683c000c50b20529802540c00c0008039140c3c40c0424490003403060580700d05140a154006c80c43c0c10b0011ba8002c0c01009000e032045854140b90a403041407440c800034107003141071540190715610340d400c07050b8061480d003600e6240c0c41c41c2000a41128100d503c01000d0000070440580040c02c100221400c0d9400c5c00b801000c040500d08066110b003980340c2048001c07111400001c15015025144010510001c03402403205641d41d0000c60320340503483c42016055 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 839503489 1250 839502239 839502241
    0x1b0307050d0c0306020715090515010608060d020d060609090812090102040e0c0306010e210105010b040f0e1b120628060507050c09010f05100206070819021b06070908010b030303 78
    0xc003130341c0080000e00d001e08041514083e2010005044034441c0d1003ca901d03174480501000641440002c02d801041c441c1089441031400b030740402c0c4901c41c0d20304000c2c0f0034200000c0c80c1007040100d80c894805050f81500400082c495840e040d02282e104424200800c0c00c0080012030400c4140221011340c0c0010301c8008082e1202034845401760401b80c07916040c00300304034121040b503c6200c0c40441880b00406030507040b541240b092401c403501a003007414045008c00c030510000c1c1c032101041081702c0c1801c3c010700e495a241595460020700301503000d1200d100008480700c400714031560141c007400c2e0481350f240034000030a4242c41003690910b084442140210000c008483c000c0b00030303001581c014010703158241750b0708000132a0940240c2001081c4509202c060003a41010881454009958001014281009000a803440c6002005400c40d401c00e030228039100c86607501a901c04540020b0a408003950300407506868140864000f80003e24594000840c240c0500038140d9901e03024014603d5 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 839504739 1250 839503489 839503493
    0x10e0606090628030f0c05120c16050d090306061203170606130312030516090302040518010504030801060f0903240207080c03041503061410111b0307050d0c03 70
    0x282d900f00d041e44a0150400c4540d4011601d100902c501244459513000941910441103805c1110480c00000042010a128809580000243d0305070000701e80d0002030348680038001d044040d8002c141005010b806141c00c441011500004861b0690b481104140308031601d030002506081340107030000e0002095100c464581e2000400c21540110014010510304030001b070400c008403007981e0085400a00a0415004807545440342541202c41e045066122200b0500010411246804040d1140d542d640129041c0c1c03c09038003162100003a54006d020a01e803e060240101000b40b04800204c1c1d080000c82005602c01c1001ea0152640424454520111001c0c29810804041405180281c1c02c00c41a0049100200500140700c4084d00039076580381040643e400c206042051501403604110b03003809092101001c010f20040145c880001c096420a011226614001650b5145000c1d00e242c0200d40c9840c420a030708143c0d026022510a9a44d40003489038002045034054013011100b041840 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 839505989 1250 839504739 839504749
    0x60a060c1509060204120f0b0601020c0603010b090f0907020d081807030b060a082b0903080909040f080c070f080706202415030109021c0804030b130b010e060609 71
    0x3a440e0b010364070040c05c2940315518030340190884030050702d080f00e1402c1450208285c0180d615441075080c400340840d800c0785804142140818001c04510041c08074a00c0c10320745903554002059a40100b484019040291000e900c5101042240307000680140c0000c40c156142a44c0c0c5c14800c0c0184000d084a600c3c43d00c0d03401c1d0f4103801400555218212007070008088030100081c0b40b4040c0c096240f42d8486011201291230011070010803c144001800c08001040310a4169800f106040d00c0c0c2011660b914a080c8510b440c070400d004100d040082440c400a0000003070752010b691540100442064480401580e681110f219000008404030074211960040c07e15800c00c101c0c0c12002c0310480b8802c1030300c0f9244414030719800c18070b4030711b42d000300407030751034075010b410383e081002e500170880460303540c010601407491003007803524044c20015050108485042220300440e00890100078a0034407141e40c0041c0b51010105035812a100000441c6440944103913900501c1d00400403854202042d003802 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 839507239 1250 839505989 839506001
    0xb0102060604020d1805070e0702010b0f0d031b210503090307030f020a0b0c030609011502070528030b040201020c0105210c0706140702071d0a09110a0e060a060c15 72
    0x6100b981c0c58441c9542030b9000354911040b0300d807080307000e4080d031f0741031000b0b000190344020309203000c5a0400c00d142e1601c1e2200001002d18800544c0c1060360107903582406d40302004448500482c00804440c02001e00000a101050301e0800048520801d98a10070880d840e02080c8c404101e15081040448002805440441103c01c01030058440e08001521803203d010411104409000310000030044149000000c00303001d001e00307152402e0030824054001355280030900802e070160f00c5150001c14081d5500444801c030394080110908421f03220704d4003001e07903881554201e0161056100340341c2d4660051050380e060403c010f01000034824004043c9079078035005001e000400d82e0810107400411030790700400c241641c07416421030103410001002454040c40f64803945403610907442c2d0140c20466407202c1500700341040d0000c04e00c103405003407541d8030802c0301074055405000c034007001602c04986d0810320300c16201210300c1c0712516522081a154404c1c2117000803c1e45d01c080d000700d004666650310074 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 839508489 1250 839507239 839507257
    0x141b040e15060a0801050f101d19080703051209090705030705070f0b070e0306010b04090f1107301709210408060a15063f0b040b010206060402 63
    0x41d9a80d4208540810b00da035114800300c0c0c00142e400c80051007542007590018840b960240c40402ea1414104c100818500c079071450a80501003a880e010940ea50f02071a1071114060b0150b06007010b50b442405940e21006407200700d81501130000c04200100c4e0841c03d40700c44d1030740a0200900759552500441d055880100003c0a1080920040020403414130587c40851b00c640c01d245d0081c10312281c060401010745191500c03a0341300c0001448140500f070180d50494401d00004030b0740851991302d050260050411001094101051600c1403000c0b2a00748049032840854086188403511210b0550400c01c00d600c40100316070030f2105c2c00303810303804041070351028012094500e0b000e13601d0803104248003000d041c0660b01c400407405102c80502030100e96041044800108040483c504003560201c00b14815401488510001c4000840c4200c0803a203003010f51081d14035182142c40c40e0030b03520300600f20200c00001e2400e0928022802c00b0701ca858100c610580080c4200c1c1c3e680010000a5400400a = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 839509739 1250 839508489 839508511
    0x50f100504030b0f01050f0405160e0d02031204051c080316030e2b03050115081305031306030e01140109020309010914010b12150f15100201141b040e 66
    0x40801c8800f40d009000e018001c951992a52503c0300b0400710709000c412a0f482a07252030b080c044c4282e60400083d12458850030291048000403001404070a020300000c0e400d40200701521340410721103c002e0091b610304803420f0760124041501c0c154015000c81c402040d001c0104003040001e00054000c001e00c58061a01040700d0074603100c0181000d54480541c20804000c5445414481c00065040200b040742d00d400c1000e51715040100c1340464150581409020441000c0703a10201c1d40c0300b1001e00e00d504070302200c4c2e03608003c155a21026840c0c0c8242c03400240b82124150304c030541030080b52100c0b00d4101c0141c1e200e0342003d02d084002c2d440500102d03507540da03a4078420009000c200755242180307544800000c01036803200a0010304400345004102a42118a580700504840c0c0580381e00100e501c1c8031315809070ba404071741040d900407840e1420f9100d00b10f0540408020b50541048060761640c09203860203440303400c0d100580c500c3d0074a00035800c000500042c0300420300b2500903035110f00c2d6103c1c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 839510989 1250 839509739 839509747
    0x607140702061c05010611030f09120d0e01020606040c0815040608120405090a02090105040e100e0405100c0e010e01050c010f241a0d0c09031401020c0106050604050f1005 75
    0x8000b50099210310340f060390510b4203a10805018100380728203401001581018150b05190969a43e100d1248203090b41c0085004541e800c06c3c5e448a0b41d010321101149821611082140c0c14081c00240c0c4501d400b900500c00c090000d03209017014007803944804aa51034078941610351003044201441d240010540107950365200091400e030030031141030550290504140d5950401b0140404540c008084641090041010300e107141d900c58110f41c11503e00b001010307140d807503007584040109142d61100c21044c500740c040c1b1040c0035020461410355420f2000c20400c000d5003000544038809243c0380b007804984e150f409a05694010070080500c0c540c02000044d4109250324071200301d42000c92211141f26100c0140a072001c940c0401000ad0a0801300b042d01500719240307070320400e205d401e00b000400f075102c5000140c0306006820400c051980000c00a10b1580c013107440d54001e402141917540e4540c00d00e880003482d03061a8045900361070703000e842420408260801e0159541480300e8a404001c4200 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 839512239 1250 839510989 839510993
    0x6060602011521020936150a0e0304090606030b0a14060a02150f010512030301150309111003271e08190207060801150806040b0f12030d0c0f0206071407 67
    0x22440a02c54000c0c40384103401c88020900d070468180c0320500c61400303000403181c0c240c801800002d0a45840f44412250140b41d235480904601070401042c107001d02e44000b280101e5080307a160404015100281e60800c104105d10b01000302003010f07840b03078100981c12409000b0f05403c000700207043c40221401210000780340e6049009540c40116241f4100d901c28400602540c81c00c80f80300c11041001100940c15541440103421040c0ca0015840080c1640c5211400c1000206242c0c0482034400405114a4110303124028014007502e030030303100d0240700c0f0031140f00144000c8410f03000b03a50b03000008a14040c0303000c5140e0000200d100801e86125805000ca0391a00981c4e644209100303010f540603040c1c0e14a0450003800c86001138014002c01500c4120f000620b5a01c010000e5000034100d90100d00d0180c200c008c01c05008071704521641103800751010516000d00000141103803012200200195907031414115440c4401c1400100140c101c8404144151310915400c90000050344035140b4000ba29 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 839513489 1250 839512239 839512249
    0x20a260616180312030c0c02060a080a050108030a05190c0f120f090510030f020c011107050c04060501321b07050105040f030f0f02060f070606060201152102 69
    0x1180c0c507107001c0e80c6a140c48148141e000241d00c002000350240d0908407819070b965003514603032a0405900305503441c02c00014041c400c1400450440d00079041e0b03030303a44a2003200100400b00440d07030180e2450404000041c08070340003048400f40099980c034035082404002c5280c4003808180d121004101c007120501c80820704088110343c00c2031242d1400b580d01c03690050f014001c00d00440c1c000092210180c020802e41c1c0320003802c112050490703d07000400b50840c0101c0802802030a01021584d803810f160074402584007001419400d014208440d00c2c84c15040802c4181e03440d60060350300052505200603010107058000500300300c00030080c4200140425000c040350f401842d02540501c81d54010910007520621040c0043e140030310b03103546050304200c60035003e4000c034800181303480710000503207043c422070221070040c00358020501c0340c0d100400304a103107480d000ba01080e10260703d403040008090b4014840c0071081c03150749411000303051402c800b000c01804e60280078564402e0203000c02e001a030715 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 839514739 1250 839513489 839513491
    0x6020d0302070c090c0c061112060f130e01060f09090503040b0f070623090a030806010c0303020c0a08120c07030806040b062109010e15041b0b04090212070c020a2606 73
    0x45d03a580100d1842142400803d46400c0700020742030001c200000a611078640c2d40040d4800004d42c3c64480d00340102003c00d040543c1030100451151a017201b4040d81001900400d003100d0401c610030782c90580300c00303c1c00100c0b00000b1005000d81c0c002c00080141d092108040c28504400228460900000703455090540f1700000220045d5984c11880d2006080007800c102d030864000001062540c0750303960094842c42e40500118140003104084004261203501140c0700960303590f09a4034070603920314002c02c998020100d01c0170920b1040d030004800040042c01d442c40780742c05a44a4001e902c803d0b05104c02400f60307510241c7c105d01d0821400ca404464418607001c2a0020f038031400300d6103000d28451f8212a00c2541c40c07590781e08002c8070118017040801c10943c2040c3c10486051880808908040c002546c40c2d0000b0703004480401c0c005140441c5502522540c890851400c055640d480c8044442860a81000358849280003040c440490f100c0094000354079101c1c19169034441d012500c901d0814 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 839515989 1250 839514739 839514761
    0x32c0319170412080f2406070212070317160f1a10031502040b0f03100f0f03031409010c060902030115180605030102160f020109050406060f080601020706020d0302070c09 75
    0x1541841c0903c40e5449140780b94030130f61a80c4100e2050410340505d0304224024510000340301721b10304400a641d6951001c441901e50300800c17880400346020155611030325240300a568004400e004903031580700c0d6500310f07504d4440c6500900700000103030351121000c0421540503100d07181c0404c034802021103034501c81401801060394102103c1e146250540e041d170407003820030107000e0050100704141c1c1954070a41d10702104451b00a52240d5488a6040481d40c1d503520410b90005088000522011041d1004050300c2c000d6981c4107002c4c1811a808041d442072481c414005071082c0c0a02c004500264891041c2e144014004111b0100d0b0381001628040c44c1e401014249101c41d052a0410320f032442448000c0c4420340095081144550400d0800125580c02a101d0007904030103400f16886903a18030050640140700f0401551036050062900b40801c47d0344010803100c2011440030345c00000d50300100d0700541d0042c018002c0c4100214042d40000b542210044182900840c200d405070259283c941 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 839517239 1250 839515989 839516003
    0x906210e1011040828050d0804030f30110f040602070e01050f060d06091107062a12061502030c060a09080a030b010519032c03191704 59
    0x104841c1a00007120003034101c01050b024100010411444040703040702882000056440414560f02d165850640750708100400f180101141584d03c07540160025000c1d5010340c0d901c055a41d0090b2007a600f0008008010070003030052040e001d41c0200082d0309032001a005400494030030401c0280340419008200d14550322100805c00b802a1030741086500300034035020304480c207103516050110760108048640d0340d00441002032404007000725a003140008201d080340070014121a0300180d0100e0b040303828212880c03420300107034410170806980b440c401940301c0d003c0d4500c030041c5800306844180782c00075400f8405484910005130500c034042c483c1107021081c2c015540e01c2c4043c100c417604001e001812102c0b498074004500c80440d440c0019140400ca10303050020703006408400503640c5020780c0070b801d0502c011982070f905e0300950540280c10703131100c044440c04141659201d400e00900104001c025a94000d22000c107040c44291609000602a400c0c20001817110100703030b040e060401c8805803480 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 839518489 1250 839517239 839517253
    0xb040501020127030c0f050607080f07020303070e0906042004080f0d050405010509040915090b0a09030c0b041b060e0306150105180f03030a030605130506010906210e 73
    0x265030203014429000000f444012210000c59800d40b800400303100014040001c414840010081541c210340500f0350040d086038414603151000400914045070820100c000c07640c04070780260300004c142c1c0c4c042e282588801003201000020701c4100c0304018203036079000c2d440b244a0400c03408059040c40c80d000a03074900a0355103041842031403600700c10041d5205580e10500c40121a15808019503081d1a1f00746400c99591501c01c0c0014041c181c0740b4005807240c080440b54120001c855404a0011440f41205d00610f503564590b400407140c01d268003501047c0c19026460004c0c01c65400c659119201d0390041500c105504054480c100054000c600860802200c20300c040c07808002099002950f07000d024800c3c0e1805000a00a01031400c008810384a803140b07150003a590001c0c0b40c030a080c8040d0880792659001c15000f40902014450381d805086604800c1000c51494080c00d40300f1801130b114485001d01d03003181298000c40324000040b404403410044a141c085a006400c044580d80d0010409 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 839519739 1250 839518489 839518499
    0xc11041a03010b090f010b07060605040e0a122105060301060b03040320160b091f0e0f09040c151106041a06010206160c030e0306092505010917160b04 66
    0x1c64905000d00d07031285035044100503525207003001240c1034407c1c0310784841e04d400484c40e0004c05803500350002940181821525802e150002503051900381c021040300344202d0701d8110641d0440c2a10701880c43d200301e440c264000e82d032081d40041d81c0010340a800000d485654a080b29000d81040d903040b80019400901c02c3d50004420300349148141a5002620380d41400701e0f8425502c818620030007080b80c10115113098565120300e00d107021130406d014030550085c01020000d099101c50140d4031310912414200d03603542d01b400840c03184a01d6115403540410f50403d0008120314001c0500141005a2100d5440401d4000d10546010341d1240504c1c000407000310802c0c1d841054020000c03411980100c013081701252446050001050107420044042d400b00e0408948141c060080c2503054403135842800041400041c0c104194089003d000821000781c074865000c0e14001d1281d503000601103201805180d240072441c04100750070b8003c0314003103040803002044030161580320641501d404141085 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 839520989 1250 839519739 839519741
    0x23040b0318070e0403260c0d060f0315200412030e010807090e0702100203090c03061303140307210b01080c0403021e0a0b04090903091205030a0c11041a0301 69
    0x140c880c0110090621a0b0038040314402c14000103201400300f10310716900c100329486c141003080000d017040c0e561307101505e006c80a01c0c000340d20006a1503441e914102000510000303410034003040c0d9521800440349401d00c1800c100140401d20f00440c0d80c1c0081034071805280800c94000d000900340385480c01110769041c10041c0030825003010040c103004001c01045201540b00c0c8921080d1204641440b54a032074448040303107071200c0141c1d100b80b0640700100340b0a480c040042c0f03d00c1d080c0703400c0741201e04c0356032249070041000b0403503034005021500480c2014404101c11000d16442403143c502050070900c0a0200d0390002e41d4110748418290380c0d230800d5080303964401540c07a4004404002c0e00c0c81c03c0d28550110308061441014001100c0d80400344100d076680310342c41403000300151811503071100c0e12450300030700906008108501156503240c0000d484a01031b06003040320f070740040140d810041a100301340c42c581c01407003080b20308103d0564003075519955032141410781c44000450110020040d01854 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 839522239 1250 839520989 839521021
    0x1b0406031e0504150507020f0a06050a051308040e090309040c030915020306060d110d02070b2e050f15030109060302010e0904020a030f030c050111121b040623040b03 73
    0x1c90841d090508210125002c07408140d1000310030f0300700003259510300134220304007800014041107900864400d6406d004241d00100e000b940a40410401c0340c8a075040201050921000200360960502c02000755004820480b1350003150340068134070301450100040c04036441802d04901280c1c3c5d40304940700b0b00c1511b000c0b1801c81e68070741d0b60851560034041700041c114000c051140641945455002528000c0303982500c20078401401c0554a820140c6402a4041801c50700682d03112a2610103019070b035907140070000c8110940d00700c03042c414200001d000c04c1c5c02c881c501090301322100c04c40d02d000404043d0011402050141c00008a290030340c800148003c0030b411465211714044c40501c800742e81d0b0070fa5541d01300c0e6442105000308140610341aa00c3c403c00c1a009040d03946020070690003441280000c00c1108030030410f004150b62140c01400907213000800a4914482c188020b200d844d0060340000458452868a0f900f11003141845000f1507020b034101007a00c9001200788510008040149 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 839523489 1250 839522239 839522291
    0x24090506010804231213050112110d09110a090b01030b0f0901120215040905010302040b06030403020714060705072306040b090d061820010c030909051b040603 70
    0x14803181019115030f148074080e1846012410348180071204415410800b070940060080117140c0c03074080c01514101c0240291041328045005406054407246851280302043d9503800380071804c10340700700e00040c0209581320084407040041e4007401c0c0f00e645d0b840304c114020042804081683c5040f54001400d982c0d04500c0607024205207030324209240d0303e07403110130b0645400031182150700d2200e0000490540365502c1e1000c8456000a02107006010b40c4c1245040e00e00030b903400d201d44940d03036003070002c5c40c07004590190068200745414015480d0000e100001010000c4c0545e05007005500c4071400c1151642c8158141c00c5800e4540e0b25102031140031440d220300855071a0b0415140c0300c0442c032640700700c0300141d1080c021001140208400b56100903640180c0d5007095920110034648260494400b00101400042800740c4015540c0b00d09401031a081e8595101c225003850943c60302c010b802c001d8482d04107026000c00304074444803442c0150009005039a80442c0c42040f0304040300a4650411034 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 839524739 1250 839523489 839523497
    0x302031009060c0f08041716030207050a0b0708120402030c130b030d141813020c062e05040f1b0f031a1c02010e04180c08061b0d2409050601 62
    0x130615115081070440368803a4001c0142c1c980620400c003482070360310801d0110b0000e0000c40046100b03045c4d0008941c81130311410342d16030381072948414442030301c0c0c000e10500800541c01004a84203402501d0f0720300d070f0494400707011140340c60188000140d010910620081040c4d5480e9088040c074601002007800e082100e06007001c2c00e440d00381c100440341c410000070400028111a0503c055214444410203900080d102192101c030704040702515448241c0e00402c11020011980e058051042420408141e070310900b03c030540d15001c244000303800000c402e4062035950300410300301410f0041c14040d407800d0607070303400c41c0e00c010060003d01240c00e00344d2103048105150a0098040d2100503000d140c004e19481c071211030011510040340c4041c14810f1080e00310381010b00400f81c410701006403101d01441541d0054100e03480340348480c0d070b0780c6d070859960140d205030826680c2ca41680ca002028404240440400c00042002816031401c02036a080c03010341c00c001c0170070407011400b0701c13071135420076001d1230 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 839525989 1250 839524739 839524757
    0xa0f080c090105122a1302090301051509071206030213051b0c0a0809061c06051005070804140d0f032015040318080613120903081c060302031009060c 66
    0x41c41315030b038201c3d401c070003100301003030001050714440100910800b01e88000c21140e00c081b01400e40c40e0180d08201e221900a40c00c10000c1144a6514081c0b41c3d131030310f4090700000003a43c0300142140d004a11200c10b48402d566048080050307210040c0c0c04104104041c0c01003624240301e486800d01d00c110f00401100c00c03070180700c040d928207404038980c0e1070642c0000ea1103844203955070000b1128460408000c00082c031842c0122040b1210381c015400f00c550807110092220801c82064400d442001e4000b0720a00c0104802e204041c0ca075081e031480c0e40000303082c4144100c0190742e2018015602a0260003141403d00c181e520b9816081c10f102c0000c211402605148640c0003007900d044401900040501482500b00d1015492802c01c070001000a881101c8507810102a00103001c014644182c4020780e2070441422601d0103014840206c940c40202d881c5003114807019040a928040c55104401e5100c40002015136420400c248580d1004140020018007620f0990116101c0c0da00e05401e0040e201c03 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 839527239 1250 839525989 839526019
    0x210209070f05041e0e100308033d06110a03200106030f080403020f0414041205131d18071206140717010602010e030a030f0b0307240c0804050d020a0f080c090105 71
    0x41503d8100a0f42280c0b036841103142d080c09003000e22404030114ac2d00da0b0f01501000d103843c8146100d01150081c0d10b8003140342181600c92504d4042052001e4003054041e44414a040d840e281c80c0c41d40ca030f02c58800056410b07100d6a034841c29445480c000c0d83d8140000c01e040c000c1d03286c103100791140c4030000c0398200280044c1054020081d50000c10181010660340d40403410f1a005c0e90455444010440c021425141c0b24240300380081008044400c070001410700080000321400300d50690605c054004181c034900c0d01041081264802c40b088804c65101c0801c81c4080034108519401800161520b02e0a00034039a445400703404141d000d0021a810282d105034030b8000031084980c100c0d410302d0702082c1c84400a0707003440906078a1030001d41501c103c8800169103a000c4800015a40e100e4000c600084100c0e50200e4045810706000707084400208020020762804200300b0300701501c0601075894003070b515030004a40621031b90000c0c80540001c00d528660340b801c3c0d10714a01500044900181d481160 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 839528489 1250 839527239 839527253
    0x70309030e0120010204330e060d020705031201150305060907120e06040b040311150a1a04060305030901020f1f020a09080a0c210209070f05041e0e1003 67
    0x1c103201410300010451059502250801c90703c0c0c280c08040c02913550310760350b4140c140e40034140c1e40c580c1c800c1d0003448a0100b00c2d4030250401035415240350399041302d05c80c4440c00c02141d9800030000e080c1d00c0b0f60811820b000034006001800c02c101095003180e403503614141c06902a014030b040d60404142c60f080070010650f03940701205810549520303002207200e1402c0c025000508200000d4110b034420902040100a407a0f05e4403442544a5504c4000e51100d007808c11b642c4400340c0d810380803901e0214001440c5240194444c80040d9000350880907080c4044000c02c0880e42c039131b0400d8480da040003820318840d580410030400610800d00c010320303a020b4408540c2c0c03892601e149400c000c0c59000241340e08660310640d000406401e0010079550740315440d18200340b0100705480b9503440d40c165809180380b0b501400b03807074400d0103801a1041089503103003001111016103d0845c501400020f000129140b58a40b042c115402404050402098200403803044881ea000349050b0600d82015410310002c1c0364 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 839529739 1250 839528489 839528507
    0x109050102061b090604050307080313050619030902041803020f070b040b0301090902030a0c0b090406060c03020c190f060504080c0d0f0b060d060e0a030806010e03031818010806090607030903 84
    0xf0803202903251401e00f00080c1e1a4803591f0b1150f94548103044001c1789940c0c02100408000c1c0705100c0042c0029990780510803d0300034065480c64514282a002592174080d8200c1e0340c0c210b1000704009098220b140758049030b025500b8068006901031403002c100c110080003440003a24441007040e083c2031600c4c0c1d40301c03624401402a0032615403101110000c5450810070540f0aaa00404608c071142e160141161b41e5041002c005116605000c2e00003102400390f400c4001003a010b5029145920440051040c0d5492003080840c030b1002c01c81c0300145041d6810350280c040d00b065079031103540740d2900d03503070501d8180d854080703920507400c070200c500000754003090381c084d02c6038000440d020300d0f81e07004002282c05c8241000504080c1c01d01940b81000200455903081481c130a032100001626007100454102c6140280c031a01980104502030b06d1a04101c01c2285144005100018001c50300507240484507083e403022440b5485481440311808050040039489520348c80d0410040c850f945000301039000b = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 839530989 1250 839529739 839529781
    0x703110c1f0e031236010912110301050a0212060301050603030a1d03060705040510021501090207170705010209120f03070b0c0c0a0b061c05070b0a020312040b06010905010206 77
    0x114107103150b019031810300258220b071540303260ba103407a0803a1320340f0861509000111443d100d0b403540303d6881c0c0e40915140716040c00d04180d68203628507007000400c83c40c5040e000c5081e20044004441446d055409010b010700c2054950310240e15140e81044907a06074902810306840781e41440100183c2d528000103542d581607482c501000d140c0711000451124054000303000b90075000d40801c208101760070100178001ca60b0251031107200c0d82da0082c0200d8466010300c080030801221a0010130600c007846d00940320090190450149000c00d400000c150740d4058542110700707035008500342504d490441c001449a00072200a000d110041c0b6108986a00c0341e50402001c1c10799110205c1c0500703003540c080d61401105141207803103070842c3d800d01c100000c00440302680b183d4008a050300e0211620310180c40c42c0c6511000074050203042c039030800301a80000d04040b0440c8000c0c0000401d1201c11038206014502480c0e003d0b070b080c2018000104200c2c4240c00c1541554824030910140d10000d0801303041e504 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 839532239 1250 839530989 839530997
    0x10180f02040209010504090c0c0b0a0b03070b0c1002120a140c1210050613090c0237020603040b041727060d020403030e120f120313080703110c1f 64
    0x64450070045e1054041c40d0050900f06291401d91956181c0080b00012250300a101158060340c4501c9040140d4001814007034154000320710400c0582105405044d600c00c8500035624419110040c0a0403a080040b042c140b0305407110902864034400d01c102003100c1c118042c100000c0c50403106143c80e510440c100d01107800b6145000034011310300031101c8005042c3c003e010a95418150701510312829450141c1f1107130b603140090840c48140001140014190a501c142901e4102c2c10303001240040021000380900d14030250090042e0754110085200310301c50720f1115028181400e1108040f8410020300d000c0342c20070404402c0030706110070003082080038021141c3c20015418007041190081c1c40300803403511b001080100800d0b810a00611000200b03407940d81c4004184044039075074010605000307126805c002070441d4a030f0444402980c0c40602113030005542426a40ca808099102e00030960028140d661655007900c403d1108030101003080715420001c1000f04030923044420850303441410300c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 839533489 1250 839532239 839532247
    0x70c0b06060405060d020903010608070621380901061b030201110d091403031608091f050106030b0a0b0a0e0f0a080109150203011d062110180f020402 66
    0x507948403821103010f0300000d8100e548400e02d40e090b045c0a9000042010700c603509103140807610200c0095140c0c21a00141c0c0c846c3c0e003440d018580745a40542e60540707030701c902d501c910810109103400301d1045000980380601c400c0590103800c4180020a180001d940728140d641d00402c9541e921000c0f901449008410110b05841607140c01d900620308448a14038580001c6a51088a0556882510101d0081c9000b6020304209406d282e1248011160322030b40c1410700380100a85441001020382c400420003c85052140c449072200080002200119202c6e40301c0c401400b140d40c2c0360181c20b485000607100041c07002d0503c0b1800d0454004c0c003c0c3c1d05d0401003503900348800d0b5941c3c0d000c49019000090700101043c1c5c0ca0b000d02601a2411000c140d504503144402d43c0e8000d0102d10841e4101c400030005140d003a00c9070007182c03040700c0c6c1c05010320398482d41d20340c0d03480c003a146140c1012000811000c0108180d04429000d00191041801681c1050030b00e5003107a130110f10500310051720303c1c3d8101e90059503 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 839534739 1250 839533489 839533501
    0xa140a090c1b031d04090503030c0c0f030705010504060c0302031530070305010516080105010305041103032101060201020f0d0903030e06011203080a05071e090b0c011a0405070c0b 79
    0x211458080d14061140800710440d0185a0040e030705091140218104c0d00e0740444142c144020b4400c540001407643d40b0801c0064400b0012001400403034051005507554030f01d10004462a54018001c181c1da241d40d2507041c0400c2020394480c40700560b0240c2030a44c114980074011031011541d6884040c02880300841c085910b071820b00c000f810300503400d07210070750301c00c100100107943d0b002c2d80c08110303019071a00e000308100d10041460852500c100d552884034682c2000011000b410018100b252501d00701d2407040b0b4240e5050001d415020786001220708410446200e400760808181e00c101d055920411850203a844250308480c4201c82001002c2040100c920b4118000c00310400e010115000e9000040340c07010281c10203e00c0035000382e0364052a622810310540403101d055403008040b84045000445150340c074160071146007020b040c0a02455661603d04155511007000d4101c2c59564440031200700510707007035006c6030581c00e5500300620f190131213001d003490902940103810b0350002000290 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 839535989 1250 839534739 839534747
    0xc0501020d060915051804080a170c270307031e0212030315010302130e040f0606080f060112030905121f0506041b1202090d0b0112020a140a090c 64
    0x10310300440720380410616988039a07003c004d004251a034245012800d03000039480c40c1981d04800076041c41d50040509031220340c0c1d0b40340d99600002000c0c0038003040030100a00da0002000041c400c01d044400d1642c1c914448406004c03404400300040304500000e1483d66051318000781c10720581c0e60200500304001041d50100b4100340c85003000960082c142c242d043c940b5140440914040c07000b102d41c04c08840b00742c80055050703004242641c000da047c282000c120601801c000907070000e00882c561508010720740c85840c142c3d2100d8101101c0f50744050565940303a5010440d8070700401f10803032001d40b0035000303581c001c00e13142d41031094911903401e1034441040804140301081903014801c134904107039800d2030900006040215a00c5104034600310070301c2030240580ca03242e1003810b000e82e40c0f40e049143c807009100094001d02c821940100b0007044000001c0c802c1ca02c0140a89402003144a81200a02c1001410717500754003c2c030085202c00c07008403129190f104030300e003e40c0c03440c17040483c2c4411000d20890b = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 839537239 1250 839535989 839535997
    0xd0207270b09010303030606090806040f171c020901021207050a0b040201111c0306060c050a031409060d05010e06060a080126010c09150315260706030b09071d010c050102 75
    0x5600102d8403000004240e05607004004580c6141c4440480c41e60381c1c4c40c0c1a4407458216800380840782030054401c0010380100038641c0c0b0220751b005540c10406c9640d500c0b900c1e1803400920342c0c081d030390000d010308842d03804128020318034541511140c501036103596016259010004024141e03071048010408581c0180030400c0c160a07107104407441d00c424420143c10942010072183d0200703103840e0b00850001e205005d07003500c03290094010f25041285a40850310760356140c69107240703e8424044d00342550780d09401003c2903c0c006801046a5040c8422703c25201d0025181c1c43c85040100400170380c2c640c1051341d0504503100d00309180120380040e40490341c608000c60340c00d40305500e07003c248504207410041038002d4890144414600fa51084400d804441100d9880c2d010070b6150341c4204880d03448240d0b40481e0350b9407450710059007180303924818982103e0360001d4010a0301d4801d10007003410b026120a50064191030005507105800c422000609410a0214100a000d090180c00d00000750126 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 839538489 1250 839537239 839537261
    0x3120c05090909030a0311211503070611011d0d050304060b06030405011a011112070c05090c1b030a05070b250c0b0114030705131404080403050d020727 67
    0x2c582d01c1d0024889803079030f21819040380801c0c541588004034024800903510a00c040c10880407082100071680314002000915141c5050380003014018a52820300c40c1000801241d211480010215071806080d694502480400c420141404440c00342c00010078a003074003489d090440c1d9984550038074802601e81940030130b0700514000113100410805500c1800e1080f440310050480c1401c0c00c1c01110201a510b2000c80c4542c0320711030001da25203411004000c018821080011450740e1031002c10858403044a24180903800410f10075002560240c5036a1041d402c5005903103842c100e0a4007a10500075040c3c00f9040060150014043c800303541c42c2c003582018107010101d010310180e400201034034195101104c03107110003400000e00b00c2441440130301200d801005058864100814802700000049018405941b03905141601101c2028000e0041e400ba0184c280e50b14198180149040100741d299401c41d44046010880e258007080341d944007184242c441014801c07502000300c0030741603035412 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 839539739 1250 839538489 839538499
    0xa141e0304050c04050c0a0e0f1201050f251b0b01260729190e0427241b0306080a0302030403081c020a0c0605060402040303120c0509 59
    0x20128000a61002940c815840389088940c110034803030038041541c105864200c0840b10501206030020f008440349404002c0182c42800c0180340c140014052850150400225943d40c03030502203140d032485901070307114000b121980740420350401d96103034100400c0c1c00481003111005240d00380881d5072100c1d601e419000a0441c41c0b5585a899103030019070030600c64501150010744600741a000441d43d0000c541d00d00090128420080800807502445144003041450007001000d60000a156084149823415030b201c00000103020180001c90301105100c8000e1127a0b00300d000c3d18403c03010720b0380c00070341d601800c0212055400410036401000803c1030480d036a042c000030b091032082e40301000c0c03c1820190340a1000c1d0b07540b0702d9810703260582d1540142c0143c000300001e002050070031009042e441c9100c0750344168296001c01c01d0003240c001000074400102401c0c6444184201805401c0d00300000b00d4045141a1442d600908a02100d4840c0070115032591580c0c0b07101c0303000e0703001d854a07480003600b = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 839540989 1250 839539739 839539777
    0xf0106050a0c0206310e04060203040204090210030c0f030e100b01020c0604090b15040305030f0309030412050604020405240f06070b0414100603020d060902150c150c07080a14 77
    0x181405c901e0307400c0d0b02c80b82d00c031203400e80c00c9820340c0781204d1010884a070030b011002203441d1500d03010040d5000030401c0e600652100d240c10010380310038000c5044642141e40010b58040807210060951010a049204050800d070003890f60040100c5d4a90304400b145100180320950040180c1c10b0182c042802c650141d40400c0000c0c0000064111b0b84240c40c084a02c0c00994002a0349150399009600001d04998400e11400b880055590b004503005468401100d04141d610302030400d0390a41e0240455164008005001c00c508050040e036420844081e01c45d608040400f04130100c10304883c255038842c210303141c040d03000303034540504441c601030b0014042455403409041820b4070800e01b40c0170b201c0c14422485101c0b016400c42c4654420b4981c020800308402c0c91541340c401c0036112100c41a80d2002132111110030221404004213081c05900c00034000d00c00c0426480e02c82c0290041400c440448104030072000180d484084500400517030400c08481c000d0090f2114650107080b07044a40300788414 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 839542239 1250 839540989 839541007
    0x70b103c0810020c0f0703110d060e0a0807031d090601200f03030615070f080c0309040504050607230406111501060c15020702010804060b0d020301090b0106080c030f0106050a0c0206 80
    0xe0024113003500c030082140e05155600340d00c503036180d0061002514002000e5800e0540e85050390b640c5c40194041c00c40840e05242e000100d40c20640000c0f41210b00c00030004910040540000498a1300e07045c21100c60088118213004c12240240140002e04112140d942c3c1802621800c24282c4404960f800b02c450010707040f03d0003540c1c2d6009540b054440c45116025003d03c40f4040115200e07551b000030400d0003001690303a045401d411541a48500e80028084000e07251076610403544101d010304020308587c200380300044c4c8408c90706007200c80b10180000700c81c08000300450448084175145d01d042d0303c00b41802c254003800c02000340e00d05241c40040c580002000750303109404400d264010301c4200040701180c00310004911030b6800007404213022000280105403d43d004802e10600a0f00e101e0386c0c00030350350021342101c5c20450112065810a0010702c0043d900c44211944201481541c1e440d605000110f0304903460148900d0381000000181482403a124148240c1c00a601a0480f9101c440c54 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 839543489 1250 839542239 839542241
    0x1052b0606030b18030d15080d0e120f07120c05100807020735031c0212010f0506120601021204030602071a070e060903070b070b103c0810 61
    0x7500c4295218920400401c42418483c03e0070885402038600462038a103540c00028003070309148500010500f03d9032800103080c2c6060048500c044196581d20b200040360b1820000b03202c80a184919156001c4006a01003810015802c1e0a0311840f04900718100c400307142040241000750445134100c407922511403c480e810080301d5000e40c00325000d071101544c540101110f00b054156104175180f210a92007620003545020b1000c3c03d807800740c02d0f83e1502d480d00e030000070a03d100d011451004d0741c0c00920030309051401c03200c2601426100c0100341a4a141c07200045441c02182c042032120000305c0c0c040b03405c0d60f0003044040b1000c800300c0411920785a81c0d0410700f00075009984182c8042c01101d002c49070410845010a205040e1034444680c07003c00c038000d01c5032035000f0000064040c42246c9011a40100c540041e0030540c1c481d511a14103440c0c8044080110682c1b2340c0003038103d4a5011a405910020408503102070b8440e103070130494100c041100c00110361141d8404101400b845255903a09061 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 839544739 1250 839543489 839543501
    0xc033204020f210d030b09160c0c060c0201030b030105090a1e050a0f0b0609060a06140c060a0b0112020304021305090c09090304140108010e010303200f0d0905090f01052b06 76
    0x10380f90959200c04ca801900303400707a412100c03a00341d000c40c6801c00104500e942c0c600c0285941c0b21031400d00c00880007a5251103082649820480202c1c12000300e00c011507034180548418840c0036002400b5038200071992a503134001080f4021300e0040114074105940f0140144170655a400504071140268107040c204820ba03034181050794410b030400300090060404e01d101c00d00459001e4541c01416280a8040310081a5100c000289a5042250003030685080041c28000e000c0304000080390072140d0300150840c40d11400000803c0d005100304005641d80172040c01b075440e0444030103c2e8541e5a0749030341d81004111003040d0f40c0240c042c020f01002c6a4004040d10a4810a0b441300c40488800d20040d12034100c02d1040181c5600b0b00701c01403000a00c90b08001c800b10018a0008001c0205030501505205d451588100341b0352004100305201c03035201c1c03810030052109451400035805c3c02001c5600340e8405000b25401442001c1c00d50700007000318032180107000c02e500c50342c658100e114940b10010f014 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 839545989 1250 839544739 839544799
    0x8160201050d090b071d0906090a0b040615030c080112021e0d030c1103010605061606060807170c0108010303020a240e0303060f0303030f04061a0604090c033204020f 73
    0x6d16000c03550a00080d65040c207407420303001b03100c01203a60b180e10400c511200001d20300d06d10076803110001550383d1180e00440000c0c20300303403001d00c4c505121071800408072207420080d0b40801601000421503142c0600341c00b856650182c0d00008904801d0020050442030101d00035005030803005610300740340e442862054198454080d5207441e8040c00100350a8903854010b1a5201d202040f141c01c3c41c00700340c609120118444c0e0001703d200781c2c1d10700c205800d1007101c1d4800d40040c18000e2140d403082c40207009101d9500400d00b0542001c2d415624020740c0ca4511780320003020780c8000769480c500c1100c001010340d2100600b01d401d0025060500f046600ca03042500c919026203a14042c2a0052501000303891066811420107140d43e41c8545070b007400392030310b4000c40c840421181d0300030b0f10507111807000b0005480b000c040840e4030203450030018102e40c62100d0803012241e0210005110034011510460160b90555281d18581c0f13850000550320103000203103d50000000441d041c6c0344500b0864041030b00 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 839547239 1250 839545989 839545997
    0x92a0f0304150b010e0f030c0414160f09030b04030e04050a1e0b24071a0906090d020607050f0c01020c060f24040c030e0115080d03060308160201050d090b07 69
    0x38200c90b414206503052040c3c203a0129002c0d1262000030709041d100e120603020024121062030030300001140450303c07291400c0b00820688810440c241103418035290700941c651410190302c031400c80c4005c0c00c551705808000c080440c40c0002c601410b20440c0c1e100701c0c3c107200401c200007609103581e0303038002400c0c60764005134940800ba15001d5858924070407036403a05c102610448091031003106648294104c10120241e40900340710322801302e40105001031403e25028911a002e0805205c0b640c54550028041490b6034094907a00c5000c650100d03400e42c10004904145032100451828090700d4042d01e154078030b607980701051200000400051729405081c0740f04100031640c4400141444040741d51500d17034030703d11444020b444603040c0345c1d0206003050902e10f0002004403211b4802400d40301120ba02c142d02c0b5042100900440c80240480031540301c0500b0104181440c1d503a841080c3d0040324200c0400030b603022403100541e40140100d551849000c8003c0105d6080e80c60525107140040e0380c0c0c41d00107 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 839548489 1250 839547239 839547263
    0x81006080c031f08060c0d0e1b09090f0604290115050306011413030c080c0307091d0307060c030606030b0105090904021f021b0906092a0f0304 63
    0x11401404464007400481c5074562840c0e0380d103101c1020014416407080c071010100340300020700b24000c0c490384e4050780c1c9490003641d8940300e0040c00c0d82030341ca1504102256400004521031034001c1c40d072a00310b0f55a0103580300100750b03032021210380c184141340c1c0a245841c000d031410001007180d190b08080448a00307004d40900300c0310322400501101003d0040c4031100242c030500d10321a42c0148003440d40654149001501c400f68460304403041c0d00401150300201180103001d108202008088001401d071a00003808081204000039540e15118070825590390782d54034110034190503050344c40c85100743c0e1000f16559902d44d45442e030020620001c90000081c58500089181071227401502e02240050795030742e0410341c201042018400024004992246900620380b4034010005507080c4d611409401403c505203640c56001040503d0010552007203469208103c031507a82c4218064100f8800c40100000c118001c040c0c1c01c1e004420107440c0d41000012903403c001c452110010341c8140d10a016003014 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 839549739 1250 839548489 839548499
    0x613140f0a02031006030c0b0d32070e0a030212010605061603080702060f04060c0c02130b011b05070e090109020a0f0512071410050d061d010806010506030a02090103021201060810 79
    0x44480d0380c04000e003800e01487c010010121800050f01d0403080301c2000080e284001040c03201041e030f02c0440000409504000300450454030346a01d54042800c0c14010500c0c1c3c03a0344009005039113030340002482060f5240400207125025070140c0054000074000c541d48070003440c2500710285580c0c004400003803001c0009402c82c0c0c40406e04500481d0501c04103c000c3d01c85a481c00c01902e40c0020314410050200950405030381c039803640b8401d0740d524580016a0380c07080f9000524003008110062450b1480c88041d00003e00006040c80407920210a5428141c03600450140034008000c4040e45c081402c2e0004100015224060021183c081f55500c1780304c1d0645990540314503444c440c09414040b848401d803454141002404802c000d00c0c5040c51510f4a2040b0a1040f40c40a0700140303109a4440702d149648500302484501501e49000100182e62401000512511000f0900e403a2650081040b01c2940d01076015110030942c07040716642290703124400186401c20456440080c07540030310000034 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 839550989 1250 839549739 839549741
    0x812091f08040f240c030b0604120605060604090f060f1d060f0f0909030414190b0d180302150a1a060c03040308030a020c07060306080613140f0a020310 67
    0x104000d900c82011541c0c035034542030341e04600d1440a550300c1c9109000701400c034010045074802240c0010303000400078114613000b41260710700143e49000d0a400c01081c005000c03070740841301840d58012070206965a402c80440c0c2c450003298403007103078981411a00d86107100c0c0d54101c24240c42003200d202c40a6541c03000c00c423003c08145885411113810b004089445402d0203000290b4900e000340240d00400c20038004111081400c071444089030308081004e00004018843c500c80e0b41c641140c004480700c0d402100300004000501c1465101ca40016068411110540100280040905201e2481e8030a810b001e520f07018600405030707560b10383c2000540315050a03c03850499000b01aa42c8805048203400c0c0302c16513000611441c03c921051100000140ca0040154030503441000d001d030720754208441c194901801c83e0002c0d0241030a00ca42400480400500c1c17540c009401d0300b6510001d0390600340300039401c2411201360042d0160030550412803200003a004c0807d8400c0c0d04546800f00b0742210a4 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 839552239 1250 839550989 839551039
    0x6020c12190e3f0105041403070b0f060f042307080903090603090111130807080102040e0f101e1a0304020f0d030215130b090f12070804081209 63
    0x81e03441000d000c110101500da652150320820400c540280e6100c0f0026042420f07800304648400540e9100e02c1008100301d0821000104803000500540c108080c030340da9104003180060100040d00c02c0701000030191368a003000080000c0d000341c0204988201c1d071020790b018681040c5022080d40c1400046003c551040030b070385108004180103142070003145420040d07240e00280c0404000e42d01d0b0300180c008c6030a040018020040d0300d010f0441e0701032a01c155141060361303a62109900d030344103010070048100c1116804c2d0784a0440945030b00c5554841c0303000c2c0c1c0a098650040c0080800c1400345d0456425065051700075a191052134110209012072411140c1c44100d0b8000d4205806103c11505404d0810b900b1f10404d200c1e0040c3e4100d0b1088500c4078000386c104869000d4040c041d08009418004420189600850600f000c5c054801034150301c50369845580400340f12160b00040d1a07418462103034242e5000d001c80713205543c150b01c0c0f0481da140098110300a1180b12341d403c2c16000c0c00d00c00b616403041c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 839553489 1250 839552239 839552267
    0x110a17061225050405090f0607110604020f03150405160b13030b070c122001090f020f0402070b0903030103030f1110091505070f200c0d06020c1219 65
    0x20b00600e240c907841c8601e02c1c14542420701500c42d00c080046000c1da558001c0314454603900004002150360b1003911440c025020300b410084c0001313014030002c00180414050380c4180c0544102103000241001b0902d403462a500703004520b18202c041c0410000c011602401500042c120748201980b110007040e5240b19101082c4031084141c082000001e40c01c15034035500c00f8031401c0a4000b8282c4e41c0300d9a805626102112000032f0b452141c0036094400d44028403040382e2654020454401c85c0d94034543c00d0b85018802a1240e02800d07103460103940d030350301119800d0340d00c21020009800c00003502ea581b07801c00e0200718003081c5941901c00c0c406108403184038910982600414070f1040e0f40c00c0000040c008103105959111340404141c41107401401020300807501c955420070808601100146806e00c0280c011f44400c402d0100c034030b803c3d000010310310311480e0112030004004065140c484000d2140c48401266030041c510a10b000f00b41c18005801c0252001050309c07881308080d170040354445400191 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 839554739 1250 839553489 839553493
    0xd030b0a0501020313090b01022103010303021e0a02041a03010e0c0310052505040f03030f2a02190e09061b040b040b07020301091e05100606081603110a170612 70
    0x401c001b609015006152142d0060060750060402480c0381001d803040c00010850b48500000100304255042003044004007281240b46040028240b11035203c1d0501c44010b880f403921003212288103034180c140a40e071020006c00801c43c00420a180580303a0109222140c481d006401c12088004914041c1a00c0303111281441e48090a058030b40c06100400182210104642480081034900614004002841c000d8880c42e901070a1503500405141c0800201041c103d40d202c64a6611916901d58022175541254500c00710720042c0300000780f102e02170380a00c0c1d00004520038402d2000b8013003400b5000e500182c013644004008011450003a01c030b148545c507000b1008020410174500c446020b000304034402000480c40e011103449003105911502092510a48840043c10400400300102d044400d450282442080d01d021809800c500d00107010a041031081c1c1c00304481248250b0006a490381c05000c600e441d0400140014a409a400a0000480480c60201e101480c041240a90311008100 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 839555989 1250 839554739 839554777
    0x2160218061c050307020604031a100501140d0207060f020c0f0c0a03020d032f07061b0b090f0615041d0601090f0b0a080f060105010f09050904080c0d030b0a05010203 73
    0x1c03940b41c0885040007503507180021311807030740144e42c1d9034010070045001d60505054405501804580000c000d03001e50704152031000304021070b90300812a41e080c1102900590703200d90200030040040d206040c0024902440c2c400d076040b0648055010b40100e501e550210f030034452a804d200c81e0781c1c04045200c6640003d0f081c034200014070740840d00346001403007841c0c80340d01443d4988042d41448104c3e90034240030f60994003100602d000400143d4000c01803842c3c0b001c00b08007481c008105110044101030b05807803003080000d100030010000140280b1a40e8102e1b1250314003062101c20088000d4501445039007080c0c242d9aa42600e003404040501000c07000d002103919058030b01d07009002c103000301c61a40740c0740d107040b42c415a142d840d54130041c00d00700301030860001464035070f6007403100503040349040c07100c503102d072035002c0394065000b5040d108140c070310504c40d0f195400c00342c41a0050030003c042c94031499442001381030780364100340303440c2506540e0040d0b040d032034600690b00c9001c1c40082c080b120580903 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 839557239 1250 839555989 839556019
    0x16240b06041d07030e011a0108090a170d0225020913021e030c0406060e0a09060803180103060b0706090510111206370e0c0a03021c0216021806 63
    0x20005803c1001420300061010071070845034299968040712007600e42803121018400d50300301015650020614014081290569403807090000400ba40e65843c0325000c40d00c000d240c441a4110f81c1d0140000c0c901403a905888029540d0046200c01c00700e00540180303021400380301407280c1c0c1c3d05c4840d9009280c10300d00950501910b990500380000c0f1a4140309418032803d0903200d42c0308441c00b620103940e44291403440403003880f42c4150154426440c451034200100281100401075400c202810400f05280c40f040d1001200070344481d4101108114001031000200b20956000e102401d00c102c06464001f8100e0903000102d0b01c0b08495042c4443c8204290b01c580004841e005510940042401c0d9030308000c05000c140c44c001c00aa2203055411004c0484080c60210000c64010480d034110000355240100e10015a801001815000d05030081440030391031182ea500d034124103451110840d181d02d08401d4000490701107880a80c000d05048403808040c6c41881101445a035020780126451660340c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 839558489 1250 839557239 839557289
    0xa0516050f33030106030207051203130b07050c07140111060106140c12191e050904020a0e13021b12030f280b0f06031b16240b0604 58
    0x1050051114001c040d08602e912640d04001e14081c1c40190742c01070302c4400074603101e483d102847d42c01c10300d185400c0c002c11041d0802e203150249565031007410003e407031716605010f49841c020310781c818000d4014058041082c1c44c1c0800050141c1009982c4e1445620b40c6204141c3c4821080c003c0d2000a40c111460320300640000300180b51001e00c0100f118a01000000e1540440c1c000c2e0b400c0415240d24101a814103645c4174480e07640344c884da0000100356802d1404050640c5c131408500900540d00072602c0121180070344424028401c000d445542000c0d1540c51080081d44110f6410304541540082000070300400981e041d840c0342181d4200c0e04d55252203161001d00719004041101840c1544c6190100d501080740742c02d40c83c030a042002c50400007003402c2090101c1025480c0c1c0c0501418401c000001d990703090010315001c5094101955207c21400a042400320100c001e06000d07101c0e12204140400c8074111002901400c404019044001042040c60f200d541f08111220482c410301260382c89039 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 839559739 1250 839558489 839558539
    0xa0909020c0c0a030506151e0409030306240807030204121b031a01090b01030b0310150b1b0115030c0b0c0a02090a0c02011407050706090c0302030a0516050f 69
    0x210900300c2d881d250000e00000da10302141e40007220710750448010f1020030000b4000780d000401c0b046034400c1205940c6103020450031410b02c4018130440d2110f1080050500a5000f10082d2002d001d41c01d101c01165207409410710000000040003854090028103c070307100c0c2c802d035410388039a5948842c02424544604039041000e601c0700f030100044083c00400101824078104500c071240c840f01c1e072558500f400c0d1008039141e0083c07041c1450304007900c6440740da6010400902e40103290800048030407a00c1250b81c1900f03210b1308007035014980010300c28001c2c80304402405038180b84100030301881c1403a040c40b5007400c0c0c25200081201196010921010340c00402804002c1042c00881c0d05400f002d40004040704000d40355801c15980d14100c5401c442e82c20f0080e082d516030808418002410104d000903c248103494014180e03c2e9900e04040070070400050020086800400319031001c01907040c205e0310350072a440c204000c42d00c0c203900003515040c000000030714000000c01190400f5000d5040347c0d07076560 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 839560989 1250 839559739 839559757
    0x41202060309070e2a090a03020613170a0c050f0f011d06130306050f070e060901020307060c030e060702060705070b0603160305010c12020c030708071b090912050a090902 75
    0x140030008075444c40c102c1ca01d0b40c4a50180d0751603e0320400140d0684801203030b103c140f002500d004005002c0c0c65180c00071244e0440341d042d6090f42e940d44001a2032081030a0365004003513015180205083e0005c40050721100c0039004095000302d195642c0104404c40030602c3d0b4079500710545140143d01340d8094448a001c00058007440010030540300c000034041d502c8280113501141c600311080c8248000f03807080340d500502c0a0303041203040c1400240945110038214105214620002d00407200340d1003441a500d80951000e4144924107030301c400500505045156490144a1400051b5181c1c5c80065200e0084c815a1101458400c071503d0312848400c00512943e054820340f40c156544080901d00c5100450007036000290582c50264020400b100410050040c139005000c240b02d00e40c4e012040b2110f07968081c0c4003e07910715071403621454092620400701c1401e800703901c0010703c0750103d410400445200e24901c140c410f03130074001980c1d28020b80f10390000282216900b030024218a600910441c0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 839562239 1250 839560989 839560993
    0x303090206041e1a0306031b010c020910050301051b0a08042409050d0504030c09020d09080403080a02060c0a0e150408010207050f0f0d020312190509061902041202060309 75
    0x240c5483c000c52910680c101400325580404008024000380e09a000841c4e642054a543c514201000040d95410065802c84846500e144000768668000e0750442101d80c0c2c06481d000040c5071000c589210441644901402942000000f0300c0d03018148283c03102c1a0440e64070241480084032045840201c010422545002100350800501c071100b00382d0103100d400c2840114200c40149441401c2034895401441440810310041c0009640803025906641027803c0050311034121400c0c1001500f031041028000c05c800041c00300500192030001e082c0000e40e6000c45400d03440d40d000d1007040e44140a01c40002440d815030105151500950401e0021030070100035043c1500e5001283c22a07210350302c120b4003544440034842c60a5418881a884403078090301034841082c217102c000c2d45034410140c500102110840c00a50446950000b6209075403000104100b01d18141072042e9440209564040216011800c8143c148400e0b0003194181c0d424450300d2044034400d03034244401a00060002d145034 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 839563489 1250 839562239 839562247
    0x1b0c09190b150c16060909200c030a0f0f050702040207050a0602360d240c050a0e0a0b1e09030f0c01090b07080a0c1a04030f0905040e07030303090206 66
    0x1d9520280b00c0c10b59900c618082640e00c1e642c03030300c241c3e00c0e140c10903004d003006188145007001400d801c200000b040711100c81c0d021407003032150000b1003240e21101d8203460f07003c2d401003070801d4a41c0001004d407452000540302c44509240c04481035401009800403400001d42c200800b00042c141078019101c003500c03850407198403031090340e1950140e03004160650416100d40070b02901c11402c2c0b00e054151780c00284000c0821361003a4002c03a05683ca417000c00b400703280c1031640c2600c0d5100c0c1208000070a8118590400c1080e111703880080980c4e01c040100d40000c1d0381c01c8580e41c03407442d00301c40318011282c0c251100340c070b00400340c10700054440ca1003103183c05d2804144941802e585080c807043c5d034505808805401c10030320300b50014000c03288030740020090880c14401e10300014007442c00c070399948201d400c10a4454005144c80f5480080e00865914000c00600c1407004142e0040c460404201c807070b4840084c646d0710364050000721480e14101003190f0740702c1d013020000309001c0e503c0b600c0c3e03c1e40040c00440ca0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 839564739 1250 839563489 839563511
    0x70605010b09030c011b0308100b040e1b13050907170c131e0620010f1a0105090d0b060f1233040311011d031b0c0919 52
    0x21640260300c410559800042c400409103020f00072404440403d0801c030910054a2142d01503442e2803030030040c1800010070118803039041c040441002421210300a5540d540c9618030602c054400342e55601d50034070a501180c4101642005443c05610380c03410301d4003402d00d81030403c40c82c0480504040c0500a80b082c5105a015101032054070608008030001d40c2d8040c400d00005038503559502070f00640049105035501c0401c01140c80003240c4da00d01c3c0a10080014046502c2c60410172507e13002158641401c0c1903007014207400c10222140c005520403002c41c18800152028441d00f508140d1008040403028005840c0107401c581148000e000406542402000b08990510400c0c00c45110741c045484600340080c0da100881480885504072181c0740650080401a060003800c01402e00c180c0c00c8420510003000d52040f502001032030074000070072410340442502e81c2e00c00c1c0c6009091907101302007403015442c00504503160b000094001206035990b040c009810340c80d00116402d90b95161241c04203 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 839565989 1250 839564739 839564741
    0x3120a05090a0b310213111806090907030507090b1c0f020403020d080c06130c03080c1c11060609010324090605010605040611010603030503060427050604051501080a080f0706 77
    0x44c840480609072840350010700401c0364504e407000d0789600c1c0d24144040381d019102500c083e2658440300403628007800851400044050065041160308180700404000300030341e2640040703000303500a4071407886240e19024502c0c154401d48880000070344070b041446a4a40982d0720640d40200c3c0307408014201500c80e80003502401e8482000e0b0342103c0007164411032240c0c1407281036049107071100c400400041c80d560791240c81006110140041c4404507504520003002d00601e604426101540003d0040640d0050103101440034241c60a1044400090316030805110150680e03801441e006254009882c54140480217035a04030002620303010f03102c000850a00a9a002e086075031525a2030318201039000303040382444100041243c1c144072040001c20f401001b101d0304800b0698000c0384000c0250400c04000d04000e0004d0f441d181e1155080d07050203000304551b40618451800c1d038078407038805c4280c00304070603082c000da00c400c0e0000e40201001072440f0303004141d00c0040203100ca040000380d40700c0d10 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 839567239 1250 839565989 839566051
    0x603051c1e08180c01020703330c17060f190911031501022406120303040503040501080f07020c0607061e05010303030e0a0b0f041703040503120a05090a0b 68
    0x40403403590400e014942c1c1040800f07108040c0b0b100010300c81d680c01c010000b542c40f0b25078400030f06002d41d01e01d540c40407121014600032031860a81c1c50902640e8403080c0c0d00c0c2c003c12641e43c203c40054140000400c3d01814450194003800c0c0040c07403004145200340802c003d0640d541800c000b01c040d00f00000880484030300480758803003000102130341c5a107807080480322035616405110f41190401200c010020b080b2900c42200070610035600c4042c0c0d507500d000f01e100907400340c0ea00c2c6010712010040104000d000002003060702c80a81e01d11000340c444500001c241101035031803030702503000a9031707054417400c0a1014040d50b500404010a00e600201c20b00700840c00070203262606240c6801c0107006158040c02a0001a0302c181c00130304410000f0b4980300c125000150880c40504268000315092210010514059024407011103941b41030520b0940c0c0e0ba540501c048c4038208414800013082d001091094510484050010b000780490982d141c00200301e006045d01c9a0b940c0c41059241110401520341c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 839568345 1106 839567239 839567297
    0x71208060604090f0204140a03080406080a1812140c0c220c0f1106060a0501030207051606210c0e1207030602070602120a0603051c 58
    0x81803440b07a0781c00541000d0134282c08804440b001d60082044425184055540302280418059202220310001d803483e0b00a06c02000541d0060040c50b80c42050380ca00051151000310001c5001501d40e1006da032460802d420b0103c1713141d0800c0320300801342a402c1c503060800448500c1c0c1d82c1c0e80c058035007026024490075814a50401c9941070400c01d008031924040c4509103050800038604050300e5440e00c00940d9500d40750b21a58008140b090140714060445501d4a04000055020354043c040031102da11616004550b0050651099006001c4a940da4011150341c1d200c8542e88901c80e6049154180c640b1010100240d000841e02d900b68038151080703107494003841002030070403150f503001030540c500000e011800c0280a900403d8800e054680700151070b02d8004000d4110380143c00f00802030b070700106d00a410120001e05a035401e44482c58070001e0068081001c40c0c00040c12491 = true := by decide +kernel

theorem cover : BRFrame.Cov 839388489 839568345 := by
  have h0 := BRFrame.cov_init 839388489
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839388489 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 839388489 ≤ n) (h2 : n < 839568345) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
