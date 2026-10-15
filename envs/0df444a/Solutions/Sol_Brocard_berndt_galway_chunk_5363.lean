-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5363
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:37:39.811213+00:00
-- url     : https://prove2.me/submissions/2c46945b-7e3b-4b8f-a1aa-9c1ff0de4e75

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 964388489 ≤ n < 964568345 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 964389739 1250 964388489 964388543
    0x607051c05040f1e031d040f0c030c020c0f0105040b09010c050f07050108150d060f020f0711150406081803070f050c0a0f0f051e0306090616020d0e0d020a03 69
    0x420380344132800c00351590030015003124100000b80010344520700c82510b600d482c0f40c8a641d0b0440580046443e06040381c0c0b035019903407c0207480c00000d0f60b440c01c101c0410b9040044440c103a0055510065103404200000c00303a00c668044c4201003040010600b060ba4030032403a0f00e65441d007040035600c450540030b044a40310841ea100313560021ba8038001050001900c2d4001800c6031380001c0804103c000e00da0f80c1c080140c01c03150303907014041c0d50a0152840f640500402000114841c440302000a5440c40130000044060350b4140a800c8042c0014000310307402082241e0000d041c054a5006a0118088a0715520854900510800100d07110708100724000440c440401c80440d810240186c460b505200d95126600c41c034040307032410030700401290614011405400303090070059200311001c90080b13450300d40c060342c84403042d5002c0350400c0103074070800e4002160307200a440a449180341c807010042001a40c2c07214540b080801800403011036480d44018401940c0c007060300303d003220411001000e0012 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 964390989 1250 964389739 964389743
    0xf09050906010b040306050615160212030a09120c05030a0606140d020a12031101051e0c0a02071412011103010503070f030f06090f080d0207020a0501110607051c05040f 74
    0x1040a010440d580c1021403200d050300d02d9040143c0c24580303036407035920281ca070140c00030b50070031250340c007a4180a0b007610081842500b6000b80d0a104512881403211070b41000183d10403a400034400c0c646056804000302003142d14000360500d50040c2414020502040c5601c441c0e070600c40c42c801c0740200801030700901c04030355000c50360025540a003020b111501034184030003035224020350024002c0c07c3d4280e10000b1100e0082c58001c2040c0703044940f403400c542d02924410b0b030350003842d20b458040c1012003407000c0d48066000d0005003000c141010180d6100b212f8056400c04a0b40708141e2601621001c079041080c62201c0c0003403001c6808059640d040368805c0c0140c9010703004075040424050101c503194400c403680009241d82c4c1c00d40d00d403144402001549e1044910518141c0171300045410000607044c0c4130340e0040d0040c3e9a90040c4100940058150f0180b8140407000c01c4281071300001181c4035920540354107015955240e641c14403803005010300b0044070901d140409003c1440640b001d01c20281e4 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 964392239 1250 964390989 964390991
    0x1718010314040201080f0a2019090f05091902031f05040c140c03070b01180b0901150c0521070c06020609210f07060509060f0112060b0a030c0f09 64
    0x70080300300100c809400c0350b001e8041034134007010030030074414a1607182c3d10042c000e10028104a40c40f5004000030f064482030845030b080850010801c1040b09140101c09145090400445c2c0c5003828405201d210fa200d0350344140c0c44500080c00c0c02c1c6480c2815803007201c6111003195039180540059001841e028500310f00a4140380c0086060300700761203036404040490f210702e00003840e1800607881c160300c69244240c1d00c0c082801000c00040007015454042c003800b441d028004541b100d451022100c1c0c2819992140440d40010860a210002c04426000047c900400040c0d41c170b080c040e10306170443c991244170007801c244910503460440090240035200344507990403203948030422607071a2402d6600304030701d03005510407418841800d074a65500307290003c501428240e50b0030390350805411003002601c5c103a84580420000300800e10529510041c1d41913800e10a50420f040080401e080440007032041d17a40390142c584940e24000584011907004010001c22611042112054003451080f0f400b12 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 964393489 1250 964392239 964392251
    0x310501020105070504090b0607050a050706030c0c110108130c17010509010c0e0603070306080d030933090501062d0608040308070305180d05090a092717180103 70
    0x55881801014010300b0740f6034030a814681017980f040000c01401d04003c0e0300032410400000014801d0120034149400746000e0310140e8981a006030554009a40740410000500780090010301908003582d40d43c0403e1a00c008190340700103441c08183c1403580c000c0c0c07a0020030f00000403010b09644020b01c11900c100b000303000648607401150b00380c0e00d924561501140482c2001021400c024018503808140c920300030511581d11481750b428814840301640c0001d85648908090003c40e41d0f12414049642c210080e00c003031010042c0d2404440d098035203041d02e0b1102c0c00b2505201d400d4002d04c01502c400010403000c00c48500320380c500c0c0202c004044a00300321030000024a1406078030303013611840e050344403120280da40801c00c4000308801021981c561440d00c2030348003082c0c0100884100b401094840d50380e00c0041c5003c012116246603c00c1034224140b011018042c0b003218206e8503050012828079201d91301074500f080750041d12a1150421203004244c007803c040046040422840e401c0c1c03010000 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 964394739 1250 964393489 964393499
    0x902131a1207060e0102150a090c0b03100e1e100617040302190c0815070305090c031b060c10060e0711060f060102210403061103060a030602070831 65
    0x1840000d100c1c900650000c03001003021900a004968088505105840d0303040e200064000300c0c0b22007500d030002070703035603c0b08003c040100c00c0040e64060520300c02d0840c1546071030b040040042c002030003800306401824002c60a080fa100311281401d00300241c00c10721030b2a14440520034130403e03100b4a0006581c404100f00ea140d06d00c0c186070f010740e4060b4043c2141d0681841c410180d00c4800c02e088494048e04040045e9440c000c1c4180300f40400c1d280f185151034140000018155031000d084554160030111811189076400125518018054050a0740180c81100040c0d4540103076100340d01036006034010f050308070b034040d070241c0151141000d0b45517290311500b40845007180c1c059200030361548000003040b50a41842c411702c0d4807800504c1103440400c60f1018081e43d41300c2c17900c00281c0464020900f442042681e00a00610050400400742107141482c002001c005803403002405295000402d8414051030030126080010206002001c0b000c01d80d0061002262590551090005191011071 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 964395989 1250 964394739 964394749
    0x402042d0509060a0207120518060309030a08060901060221040905090d030c0504060f0503040c170a0203010e0c1f0314042004110d02160b0708040311070e010e0a0902131a 75
    0x460700e81c01910714030031f5000890b42600c00d6130000a10080310341854140c03560560f00d000096108030141c2001d1030725000d502c0c0001c3c18a01014080f0b5229003030f1000103000459000810822140141c06815001d85040c120340d1030b81d00c5a41c1140300f9290070103081000f00080080c4504040540b0b0b035040184048540702140e49001d03a000d5940081c4d9a94005d0303151912640146410601404000900380d5440800342d00702c06031001d1092803500010102020740c5000e10408102d101c0e004040c00b03000100c8800100b0114001c202c0381c1601000c032480f0394426110368401c0741c00030740902d1001c005042c83e0500100304e54031010344110854900c02c5a02c00c0d03003001d01554903c0003289410310700b03192a40481e10069004081084c44d180d10613202d60700840c1c240c611079401180300345c0b2495401d00301801c0080420000711480c1c6200d6001850403c0f0000140c1c0c1c8141c1144c5030011480402d8580f112b010713024114042002e54404c0b442d043c03030040307144182d00020940c86000645c2d6040751501e01840 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 964397239 1250 964395989 964395997
    0x10807120804060e061605100612050c09090f0703030206250e130209040603060905060912030406180b100e090a0f2901030506010302270402042d0509060a02 69
    0x41095070184400c00449010b0a6001001e40f0018145800d000249a2100000a0414007516198051201200c0401c0c0324072a0b20090044a034102406140e1510342c26a13445081d4100c81c017a14a9000241110b00240405103a001d80d00c07080c0d80310103649040080d40c910080d078070900707504001c544156421039002e0801074952540d45030107500c40562000c04c40d0354110103543c0386076680c00b0801d240840d9101d02c0741c60051886118005038404590030a11302d030080c0180203081540c1701c00c04c5d0100984100003036a83c020360001020034400900001d56a8810090f80003c0089503110284511a6000c00300f000c1503461012428a403580c074400910754a1460302805003d4201c140e690801140002c81c904c00d02d0240701a0342c0414615408050b031050350300b68800c0e030303058000c10014000c6140c8009001606801b43c1002140d2042e20709a004080c04060700080c4211303500c16665100468694140360309401c108200c0e002d185000560b800940011503044030130380039090008040b00e20510a071 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 964398489 1250 964397239 964397243
    0x70b0d0b2d120613141e01110301030b0f04050a020d1203150f03030809120319110a0504140109030602031008060603340b0a0c0209180606011b0206070b01080712 71
    0x18000f1303440d00d010750703c151510102d0513941076440d42d1001316003007401c119000c004c43c030b81583d0700445045621643d0840f81078403000354202d0800c200400214005551541d042080c1c400085900d440b5850300914010394038000a410107c00800030040c42440c0d072403c401d0782210307102400b9039000d49001c024044400d00440c2c030303420407018061021030707c00c44a4560000202c8100c408408858a0a0100c0e800440c0c000150002c0e00040f0042c0c440c5134000d0120740c00d5944402ca041c070f0310494000d04240124094901e4002511541d0095a8401c0e80103000864001608540c0d90034400c0d10162a03403014011824244101c5001c80d640f4280081c03030600d9906903072030702074042d1812000740b420030300c500440100c40c510101010444581031001044050803586549160155900c1440f49a40000b000a90080d010000b04080f050011a60380c2c0d1040e002d10b044159807201040300444195003000107900f104022031160100303e624070149050341c05100455401c0e5949041151800180c0440 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 964399739 1250 964398489 964398493
    0x60b0904051b030304030b040b010f0b0a02030403150b04050414152e0b04080105071e12020a140304050703110306070203090103090228050112020c070b0d0b2d12 71
    0x14500c0509404010404002c0000c06a07031509940c2d40358045101d6064401392690943e034801001420503a01d0040c004247e410445410644c2040d0080d407680564840500005900c1d001042c400100d980a0b02400c140240704004605003424064034078000e01d040080b4520070340300323020b581c800716a02c185d1103140c44640007020500c50803e502e418200c042e045e0b07145600303401d43c081001c03141e05020348007400c2d24030000507280c64105001080340305040d90351021684c0110011040300d40c0301c072912000140303074100580d440041e10f400701c1300c03078803014001082024084144400c1020210748001101d008400404581500c00304058a0782826940074000d64010000428154040e41260144131700091501d20014117401014401a00c403007000c2e0813500868a05000940c0c01c806100c0a9003e25042181804d207410141c07a03460510b4020905001c0d004a11100c03000810740102048890280070600e0000300381c800350040800e10920040d44544041001c1082c2c14104089007100b4a4140 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 964400989 1250 964399739 964399753
    0x30b0f0a050607020d020d1a0a0b06092b05150c0f03011a070204050a0f1a010c031b0606031505010603021c051e091e24090c1c060b090405 61
    0x70801255a0001c2802c913002843d1402e02c0003d60f4400852200c0107020b40100c1c41541c0c2c0c9440f1030f121403540140300050740c0d403405032510310903200c0303000fa9241110103607003104804014642410a0305a12018218100d0704000d0801c00c014010401c03e64010b0901c209025a4035002e140140d01e0145c400418600c0c0d5061004101d132082603c4403078101b09040203014685901500802c05907541201d03141501510761090740e0a5240a110f880c89000e0031050b85030f400700134800020801d904042d4040e040052050a1404080c620311808058550020701001001d0782c030310f00451220125000309221a01d0a400000c0450007802201c2c1c1c2c840726006040c09440d07614100c00b00030803001d031040b0b180404207111241b40002440504e401502d0ba078000302021600c00e00e0203201050324161054207500241d94480702c0115058648501c003114a001e804150740f001242490100703802d25859203c062407501c002440350000c40d508030140a01001c4c00400d210f00d003407011440f811b40d070050941e23000708 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 964402239 1250 964400989 964400999
    0xe0d050306130605030115151d01030c2109030207090501150c150f0605030708160323060103031701050d020108070311070204050103060c080907080c0f0103020c0319030b0f0a 77
    0x581060b0a4408150001820b03138072400400e084071106101003d82001d9168280541350010340c0003143c000711032500d20048000d401c900c0c0000400c104442c1e0506032074041c0c040225002d0200342095a00b4910550103802d50400e108014142031002500540910030001c01c1000d981d0040d139058030041d245100c0c107402001d5048a0400104406880b000504003900d180410140a030340071180403000007041982c206020141010380541c4190410b922080318104000404036901c0704407900b0040c29016540348450841c11918118000f00c151b0050f0340001c0308060300405031802040d25882100394507a01e44040c82940fa01070140039021600b03500c00130740060721a4000540d001c5041c0c0c10b5500f881e007142d02003800d4a10a8004445103034450400581d4103520141c000da00000001c0142800c1e484e00456640340c1c48400c0ca0f690094007480307842030311a40250101d8840011a004481c1e65220b03c0c500c2c048030680c61074001d00001c0c14600d690480b440c0031085a13002e034000828400c803062410b = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 964403489 1250 964402239 964402249
    0x1203070b0a09031e020c21100608071e05060c03070503070b070305450304090504060c08010f0306020a03020912060415020408120705100e060403180b0306010e0111070f090e0d050306 80
    0x10049040c000c01810010841c821810700050900c5041c0c040301003089d605040300c1e1030400829070021904c04401c038050071103104003842c0040441d070044c2d4071a50b540d42d0b0410460708501c24002c019105100000c2c40404001110800d6489545660307810003075074071041841c01040101c21627807110503e0315040030301c4d01c0f0303114a0b103408041d14502d01c0282c040141c0c10342504603080b5900c800a0f90344c1e10b42c2044140031550099036804209840c2c0501191b041031050071a048281c04080d003400d6001c146001038034000e504983d540000100719400c110f0305500040d6550f0021102100d03481c408001d40c000c0044140280c0702a41c6032113000d00036031414207100000c250051001500e4600c10140490301100062044042d4100c001002c0d0a192401d401d003e00a42144585030003429a408403c000303040842041d00d801050901e040c200c582c3da0540121910040c02c09404114040e0000000300c600c800200f140446501c00c00600426080051041c0c58910381640e40d0040382042000441e54501 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 964404739 1250 964403489 964403509
    0x306050f091e07030e25031403070b010b07050c03010524030a0602040b0901080c160303020a17190b0603100515040306050906010303110a02010e1203070b0a09031e020c 74
    0x2012100030301040a25001201c1842c06940c14000f09540b8402e00030340c100188118401c82158804104440030284041c0300342c00024403014110f0000031541200d80101402291083c58000c84100c0003941c4485e88203507035a00c0404211403130b214145400e074182c181030113844d00c034040400004000314000e10811510142038400c55600d40030315621403001512a10103440541110b003d00c0381c503020500000751803480c026001040a035002d11004a840380080e002d02012035140c500561542600c40042d41c242044580d002e8101c030195007080110001c07441011806c1c05451b100348104140c000c240282484181c8421002e07480002080c4158109600340d0403554600c00c4010b841c25942c2e0302c0d08411180140c0e030609494225100400903d580440f800202c1c0c9130440140c04224400d500107011408540b14041c011800c0c2c8003101290541401541c4403150080008003407441c0080ca800014000303c2c1044000c600d05004d104907000a1040c0c1c40c03000e041e1a0000c3c003409000700108508062 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 964405989 1250 964404739 964404751
    0x90103050604141f0e0f01050f0a08030d021c020a020607120e060a0b03120a030b0f011409010c08041e051207060912020328170c030a05070c0f03031e0306050f09 71
    0x18603000020308240203117001e911503242901c010544c2e50400c01004241000340788060b00c0f5414400081c054608040200e032003a034240030005a45881c0d40300c61004113280c1080c00b8031035901c04125541019000308405105541c143e990104024203500543e044039240070500c0c10036406000000c6900440b5441264000c4009040355030801100341c820090713074000c0101c400000d03110342c422841c83c1800740ca0340044d11424240000c101e03000d15074a40c0f0740d00504c40901e0400100d51000b500f803100c00812640507001c2140f510402002041038111140c1e194401c0c5030288402424240b817420010407018103403003990340c80e070451924001000001c401e9801003070782d01d80520501d0b4a9003035040408034401c080c06030001265450300d420300c00101e050288440304010402c112142c002c00f0080110352001515040054407000c1c41d08000c0c5100200e604648206520328a01200389608000800101d07581d0904d018042070031008102e0035110940b080d1030704034922182d200c80328642550394a52082c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 964407239 1250 964405989 964406041
    0x7050102031c0b130207050f0d0c030804120903080c210405010c0803040602090901030b1e010e0106050a091703131a03010504021605011e0e0a02030303060402070c1a09010305060414 80
    0x140211501800c1b81d002d24802c07a007681c000c41800b14001c0042c851015089501d040080400800c0d46014003c0c0300300400040c41455031120910b1220b024034050300145070800d0405440d8503c100f00c480e9655215140702c0c1001d0369506141342d0b495443e00466098138410780da9009162520755a44c55103030000b610072100c1c25002d028009068a40600050095000f50402c00707560421a07980303040740004400c504000b9500000511200000100040c1182c00b00e24160340e50b000d9031441101d407900140c105400c5082502d80c5000012000009440001c48045e00300800b207944036041048001503110081008100f44010812440d103980030f8000245842103a610111540d52414215070b0000700c0c610080c0b400c0901241048854450b605084120390020b0004844580000c0c0e47c4c2e0200616042c401c503000160f0504006405240200400c601c1405214181010040c01425006041840c3c0040c1c503000c002442c0345464013412149404030800d000c000e84403a182d203103005000042600c050 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 964408489 1250 964407239 964407259
    0x304061b081c0b0607120f27030c0f03050d08070c08070c060e0303072a05120604060f05011202010e0105360d080a0806030a020a090e07050102031c0b 66
    0x11030600401011074001112401c00c00810b011a0001180c4114903050b010f018144548400221a82d202001800244c28064510140f2070000c03160503900700181c169080c1c04141130355a80715006a03400a90380f288103440d50081c3c55040300c00d520800c600c006807069100c2d124401302940100c85117500b04480f0324004140740034985a2070755070f5000020840d00300e400350300304007c4a680a0342612182d04100d0285241c0986c0c1c0d2101c5640c07070348454102d00c1c08120074002038441c1115582c0395000307100240080301e9050703220038820f480e0f00003200c0a8880d18104005143c4008040c410681130790005c4211012030b03880d035001140c000c0c0802402c00e0500000b08110b0001403900804010740a000100040030700307030440902950350990402d00d40c00307502101c03012000100e1107800d644c03840e50300d49401c0320240e540c00c4c0083e04d40700300c0c4031000c0e412001111000c1a2015140c0105814526803070403128106e5943c03004980d81d12407084d040c520780c83d54070000104220700350040980c0004c000c00612034 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 964409739 1250 964408489 964408493
    0x1608100b03042609010c15020c0118120305060a060f0c0b10060909141803040911030420060307050f090a06020f21030c07031125080f0304061b 63
    0xa54410b840c1962581c02e02c07000f900c1c00301800300c20202c120540d101110f051044071800a0700142450600801c200c6004905400c22601ca030305a410070500c1310024000d0400901d021220801c80001c01da4040141c0c2100300310003400703406480d0044001401c2c540d401407510004031014143c2c88090020000b1505c11000419034108509000c1c1114618000c00d1b14a8444064a001200e62101d04028108545140700304650f4009580c02412180000442290189418294851908010040e618152407901e80042d45405903110f14807440c41d9100044007122000c00c54000350122a500c410200009010303140b0a40140085000d513104540c1810b0381040056844042c44d000440183d003c0b002c8030340760410402c050100301502d5565a410105100d04190441c40010b1204035440c20005000c400c0622640e802c07a1380c651110151001c0c00e22000743e0203455883e40454000ca0340c0d400c0c0021544290200e280512180d03a44000c0d8a40391505000f07513444001404080c209101c24905040 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 964410989 1250 964409739 964409759
    0x30509060714070f080a0b070819020a0509120609070918051f060e220c0312080a0c050f09240c1609060315053d0608160810 55
    0x90501c0c464000f8218080c1010381201030300800b98400e801c907a20071001e010100b00c0000c0d0b400d8120300280b80840c0642c1c2e424541401900500450700c140d1407000070040344155100000d8505002c04a4480401808418515aa42c2016a40383c907454000f45400c10000c003440e4006803032a0034107045005d00c510345403125801d10300c00000700c5081c000c8cac61880c071050440303a124034406000b10382c21000d060300308111040c000311680c00d2244488016066071034140b00e021141d4000556015401e00c0079101c0e182c000925242d002c0d507004400c40d00b0a011085014080c0c0103551050580031060b505046800c8100940b0044111800d0b0f83c0c0220100b8442c442c5442c9001840c45452200040035980302c40c288040d08075986500c95110640b9000080c0000380007140a0394041c119540040380b640c8401c01000d5003643ca5048907115001e801d96003032100d0b0602404480050000c16071154a00d9489109482c0030038103c0700c2514004e061841d040311280601e6180360444804401030380e815854400e980 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 964412239 1250 964410989 964411013
    0x1504031b051506010503040f0b040c180209041a1309020a0801020c061509011212030b04061202041b0903150b03030a0905040b010c050d1d18012606040305090607 71
    0x1441035000300381203140c2c59030035106a50300b201080ca41141b641c40c00c0d032a030301407660968400500d041e040001140500400c4e481410280c602d401080c0700c6510b030b40c8c0f6160020f5001c099a24040e90400f603220074100c09a03000d003034410134040c06400741006d840c0000001815001402c82e8010081000402c03207100034405042801801401000c0e135003000b240d0204080c081401580c801c2c1220001803101086103a140b240e040c4c0e02941c0c0c03e4074903050070002d401401d40c1402c211381180c0303400e0b800108a000300c4c8400300458002d80e0200031580040c580e070418200100aa81d010a180041c100f000403d01d8400c0d44407034841441c0010384008400c0080d0a69020440240006880010610161429214004a03200c0034200182070207840d5540315100d0800001d030b14180241c800c007402c0241700c5812200308454005048142e10100c54188620500003809240680f103a00c0c480390040790300b001000891580d07031000a04003a030702d690301160183d04c0169000d4004c1802d004410010300804a91 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 964413489 1250 964412239 964412243
    0x11031b01170103051b04140106050a11030703090909060e010c1e08150f0d0c030c0e060301090506060111010b130906060e13020907030f020d05010509220b0c09101d0a06021504031b 79
    0xa140d64044829000b04084000140f000e4cc6400400a80700041e4102c640c507804c807840c04c0c1f00821201010700700800140b00b0f4030b01d0300c005035007483c203079405403580aa05281700400703410203070030170b01010842210000c0701154110000c03020660b120701580707002c3c0e212030170640c002050400d6590321075907a0480c12181c0d03801100e21914020b41801120905024a60b200c1001d0b8001c001d01c0520340c030303100d9031014003070011030620440c01018030045a0a4004450b0000302803d10580070b90041038580003490017140a036074103441c150010405c500d90000e11070040c0306101101c40500e80c03039004c100f06410050424824155141a03034041c0d1901400500505903440200286642c0351100b4401c0003403000740f007250078500610000140346000f001070041c05070400315a20312075a4561038541c0c548208060b243e0320001204141502c258802000342c04551004824501c225419003403000000f80c5024040158000d1085a94420800c03451554480c0c002d142c404c002c00030000e03081302031040071002 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 964414739 1250 964413489 964413497
    0x504080c210d112a0d02030c040c05090a060c03140a021501060f110c0616050c04110c070e0402130b0406050a09020a020115031e11031b01170103051b04140106 70
    0x58507060305004c1c800b6614212100300400c070103410040041d0003110741800f240d8410214440c048080d506e003040203140702c0c1d0015004214a0060100180c07242c7c103c84130283c81a2030f580703808580d0318441d401c440c84895140c1c654014100c1000b03c11541c0b80c10012015046100703103004d0504101c0b012203001c1c020b16080c2c86280c0020101d8100802e28000b07054800c80c164010b11400f03600341c40307410407251841241200c00180102c1e81c81c0041c24022010711056125041c0842c0e4202c00018034001c04440c00b0304402c56402c255111110000307400201d4000e5031112004000f10321000098021480521008100044507a201e0300080c0c02510741ea04070446090303000c01c00c2510280c0920032505940e42050010492074a035996044014014032590058801d0038003880040045201102d000c0003030083c26150890b5170101c0b850b40c45004c04041030b000035070384105900c4d24011500600c4c11b0b00d40005c00340c68903150000c006a00e44010580b000c0d0841d65a000c400202c03084882c99038041c2582e591 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 964415989 1250 964414739 964414757
    0xa0e090a02100c1401060503100b03070f14130e100c0315061d010201060b160302100614040501060810050918011d0105060a0b041806080a03030e06070504080c210d 72
    0xa0148a106944c840d00150340c2c9040d00034801c681c0d00103240849a58a41008030f410420040400c1c148a4030b944030700f0050100c408046003c0c0c100e04040700f030b020380a96503660141750a01075002522a00a078007000c40d00001428208110325800c40d0980f2501c609020408000c41004214485000c0e4030403800594401600c104c85114041100c02c290000d00c000e11250381440c0883c0d03d18480c170f4083d201d0746417416081404240c020b000c01c81601884110400c150b41d518820038400101c403c0466224900e400f00105000740242e485c140a500e13403c4400c4446130415041c071201243c060b140d01030010740940e00d00b2946d0004d0040c0d41c180b1007800007204070070041002e4a429600054455446840c58840510001445a0949044611001142d814103000003100f8005000c16080803685025504d0184240b50305070700810308810311074040351601d80c0c40c0c0000315100d009900480003d40c100014111140c034003541c2c0b289a01454800343c0200708200714910b8a00010ac8850a0100c0c620325 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 964417239 1250 964415989 964415993
    0x609050a05010b12070f1e0b0301080f0706050a052b0e0f060115122004030f11060313060207050c063c091c051603200a0e090a02100c 59
    0x9005000e131060810003069150308001041e5081c1000c2c0c0941041020421801d0540c41e10300d48610005024680900b5580d503102c5603040d4650440d410b444d50306103c5c4d0a000208a40b00e8011102e00d1300d510380d84c0c6410300c14130071600c620820071003040e162000200038004044100b01e208641e5651080340040846510823a0020308114059001480f140241c0f0800c0d4130310f80c1c00840c80d102104011000040140001d64002207552000c0317101e032200440490003008200d00710845803134040c000d90403002005110410015035220403540340300b01e10380c050300390710000700250054250f8900c14020394071a00d40300b00104070f00e03070044140c141c2440c80081c450b06000d1b2000c400100721400b610442402500011001c0d00c50380710300000e280c0144491940f098440f1440d03100404441d034010305440307068181c40d40b00c0c1010100382c001982c90701078080040c3c913a03580b203403142c140c002d0024181c801c2641c07078444042e6454000400c0e02e00580150b9868400607a1b0f000301002002010b51690b004005680c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 964418489 1250 964417239 964417249
    0x30e0d111006060c02270c120a150b0702032b0906050c06011403101407181203050304031e02030d05060f010e060d020f040b0d1803090605070609050a05010b 69
    0x5500a080c81442d00c4030034042c80ba0322501042d88640c041c3d070030350403400d20030380212240c44040d00065084040c00c3c0610081d518840010655000d0070740c00c2500340c0d250402c0300003c03215080125110b0b1480c0304400c1090b68450009001100d00050a840c0c102c1d2a0001c0c04141340309003000c801e814055085a072906a42105e06d01004d4a1070b0702e40300303050030149201c16555000600074144114000c20b50311099075405c004003070000c9940039083c4507a2070300458109510400b13441080c082003031801840d03100c5050345000c90494a400012900e20702191300d094075550301c0038100b502004000014407509004070350480480092507402550317100b183c03018030401c6503405000e40e44103030340814040041e07030780c0700140942218044a54030b0f0740d01036207100b2a0003481004001c200001c0080350029400c180c11000d01030070607210b1805e00c43c2200c2c07107a0280740c1e1103145070f000b00490381141d002d0102c2ea02c0341002c0e02545100d0400003848000b00e032201ca1400000460480d0a13a460720400c0d0868181 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 964419739 1250 964418489 964418503
    0x150315110f1b06010e0c16061b0306062609030405031519020304050c0f12010c0305060f0103050c0a11011104030803100b090d062a081008060106050306010c03030e0d11 74
    0x6a803020300b8484d41003245528000d000503044500404002c03400541030480102c0000840703034040800c00981402108044000090416202c08203140110014886005044402d08001426441404551640c690f01c8414801030203400042c4410310002c10291420801d840b5803500301c9114009600d018252500f0800c10100240c40460042c0148000204000360040381100e048030000c502034048001710304907240c075141140066082403c1d440029815034411401014256200c0b00720b6600300d40150103491050300c0f10344c41680104422542544515031012202d0142000443e140321400c2401800390450340081e1043c0b04004144000c244003007c0c1d020041c030a0059850400e441a00000c1d00c900c00280b0141c003c9865084061540188118100100400390420510052050300c014000e160440e9020f40607981c491011404000000c0c07414100c2e0320990b66546103555003801140c020003010012020b154503218070b03c010705d50600070307003607440e07010780d61901d207070380c903d1007031860800 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 964420989 1250 964419739 964419787
    0x30d020d090c080331051e15070b090a0f0209070c0501060611240705180301180201020f010501030b1302030a061a040f02040803070204090c081c03050604150315110f 73
    0xc00c003001030074171404072804840085450340324403441c0c54800382503140240b01459000c100c16040c90107168028003e00400c50041c07600040c5d542d40d00103041d64500028002400c983e01020000005250400c041a4800c40030301e022603820034541d50b51400d403035198200c0d13004601d040d00c4840126400b0055120248454500c002c1c024480c0c50303262000d00000307000d050070000c0000c0c095031204070885d100e815030b40001d4000c000440c2c1c000400944000e510100701d0040c091644520b586c810705000e042d05980d0001002c0b001030301c44103000e40b0900365055040380c150140d80b000c10085400b07032003590700504c1c40310f0440c040b080e0700034104021103600e5503070340500364410701090240070300000903250403540c1601c0009600915003082244000e40e0f9010001603c148200d42c000343c810b0710020301003a0380c1c82e00c0520542e241c0b0810401510301001103a0b0441042c10003c2001c107501c82da01103080d8070182c40c0054074494110340ca111a5210550900815000040714107029580b400350b000c0000c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 964422239 1250 964420989 964421047
    0xb0142140307120c020f030706050108060705040e0601030216020405101e03031b050c120a0201120603030804020411040807080304030210020105070906050d06090906150611030d020d090c0803 84
    0x4030b0402d1020300242600c001e66007907555100c96011826008001c5c083c0c00c840b00200301c135190701c410720f01703180038207400d00030fa80041c042c00c8085031800740510191411790380660203e10441d520400110003e410550422002d224040200c0025844030b1140a015926000310080968109400d080c4440340f440649140d6500c900801c1012903032200ca220006103116030b501c2d91542843c10002d04d00981c4401280c3d0100030707588240c40207500000d4020925200b80c8503801148020350103441105d0b80c42c030015010644000c001401484c0a50000da00c3c007035261503d41c10306407108002c078a480305981140c0303602d1744001018010b514180b01220b01c85400b47c40280107602c2d00d01002071861240d44108014050007003403000c2c24110b00c1d086200a81004101048400228140700c005000e0052041c2105441003030049020740c030803038103505220b4000d0001d515210310090b00000941c07041e610b802c01c05070781c0c40304240007440383d00380d8000802880c8000e588400c07140307054888400340c0710000c4100b5 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 964423489 1250 964422239 964422241
    0x50d080c0412020d080c03040e060402040b0723030a1d040203091c021c0c1e02030706050c0a02031e07060801082e0c090617040b01421403 61
    0xc00d501004580a540790300e00a4949841284081219060f440000a141c01c8001c601494a40ca0002c054400c4440e0700351410780e1603e4120a000480c403070707400342d61100c40d81086000081203201c0c0481c10480080c1c0d50202140e601006c1103411174100a000c94001000318007501906200c1601c00f401140c01140c0c1146141002e8184035901e41e13142d009141503640f03c0d010215454001d011060001c80c1105142e5501c0100c000001d050440100049079840484c038034600741901906260320515a020700100805400c084058855411521148955206401e01d03240141c5060000c004040c15030245039000c0100e400416040c480160004020803c14000400040c0b07000103646c0d00380d50f2081c0c00415540c1000381c01d007400709182100c2416090802c03401c010002e138040f074403070201c0700540d1781d40300c40082e00b04090311078400603603018042801820050080300300800c4094002420107962a60398801d003102945035414008070030b200182400211401590000c4900068401c104006899 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 964424739 1250 964423489 964423501
    0x3c020a052710030513030e01120501260a170c010f060308180d0309050d0212150a0606030e0616090e071107050105030f180106170106150201110a0e010203130909050d08 74
    0x8821005c00b005010850b4040d130120b035030f90054a420040008055081c055581c695051965441d4090007080b40d140415003032280360a0040741c1c0640c2544d1154001c06101242c4d05a108185c10018000c2c400c0c0d541d440340b02c903100030030b403013010f00039417240518981b10240008104010807082540c0f600503800300481c100040d03840081c840580c0c408850111030380542d8000b06c0c09200718001c00308824410100c13201c01514106468510990801006100e840d4a902d0100c05650300135882c25900d9001034041400d440ba1194040d4026082d032034110681507644142c1c0100740820b542d4036000c40c5070a03075000055807040c01600051300c1c085c28064a1814080415103040100070b003c140142014400da0070f4881d800e4000b01c0040101030076402c1c50202c1425510700a2140380718400200c151020014101e42c01800b0703c80b0350250400c1081d06085201c2804d0710740395498117905045000c00c10840c060042200c10107400381208130340c0010400940d280842c42d26200c3c001c04c48c148074910003000310b = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 964425989 1250 964424739 964424761
    0x3070501080a0203040602070804090207110a060c03080408071a0702011104060c060209180924130b042d0308150604363c020a0527100305 61
    0x1d002140b080d07005030b0b03076601e60400000a0048503001001c08900140003d900e56031034002d02001802040840420b4009c1c004028031100c03175100e007031302007080a011000828050004242d10501422200d442c0104903a10140214401056802d0700c403444802e015225909210310b442c40101c00d1041490a418100c02070101244040004c2110b5000100d140c7c243c0c540c905000c0000090700c0d0300c8145418500085c0d51554203149a041600159456207000143d41d1003806000e1114100da10f0b00b480d0741034444c50000308008100761034988a82490058001d818501c080c5600040101c21100c40168a8001c100c0e0902500090051980d51801c0b501540c4010444084039800c039544c00c25490130b00e441e80117462552056103c0024030341c0614440d8022034000d1070b50201c190401d82e005819a42054011030309041c02d000d051135140c4c0800d40c0c1c4036141d9009110f400081d0901909112840c4c3c40c41404900050050700300d1800b00722049034505207260000074210712030605000618042e00c501c0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 964427239 1250 964425989 964425991
    0x6250f1a0c0405100302071b091103010308090d0201020a05190b011d010506130302030618010c0203040806070f0c050f100506010521040f170a0206012c0c0405030a03030b0a050307050108 82
    0x10312a0041c0e42c0c1c82c030701360b070700a5045174581ca07407050840e8200c03105a4210100c00711944034040c131150401d046410084180301c21a416aa844881182001070b0541408800032040c00b0407419840740ca041000421810401e9010000107030300c0e85000940c1c1450500f01e03104040c0d0040498195075030040d6042c03000880818191407040d81c0301900c400282580e031454001d0b591020b9054065282845400c0908000044419100c5002880345008495040f0f0380c82c4103620650700560420004202094801c0503035405050980c6000b0a00f20300540b01c850070041c200d00081340b90b0b4001007c200d0410014042c1d0b680c040001d08000e400c1c074a81d10b61103815038410052015001c0b00314000030381000108040b07405c01c2c0d03821411000b030703459903040a021580d01c610700120240c440c6000004146082c2c0001e207070f84c1c851b158030321a07001f140c80e615580c0d1614040c121414944003404003062940b410814084101d010740c0d00450104141010e1001c41c203060303044180241c00040e02440705036080001a = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 964428489 1250 964427239 964427249
    0x6041e020315042604080106170303010315022701030518031c1401060c030e06091c111c0c0f1511010902060f030618090c06250f1a0c04 60
    0xc03001680c3ca40c5800e2070f02c9020710081c005002075007110003000018002c00362003610003072002080116103d0710f0036200010050800030b181e91040005000140c01090703c0e101880301d0b904050705140000c00ca6400010038403410b2007610800540070034403036905004850300058800301c510f2039500c0c10000c0303e48900c103828100203001d4001d420032440d61896401482e40202c00c0061b0340003540c4804001700b652034500025400144c4010405201c1d10345017080758075440000304000031a22642191040904d0011020f8070248171880600550b903c0e0044940b81c000d0560300e103c00e80c2403a41c586401e2100e4075400490084485040c10310514101b00c50483c2508403a0520280c2041d030004404d015114500000b0b42050b0042816110460880080e5009140480340000b480f000d1213009413040d04c1c11603400180b58015821140142040300041400c1e4489505016008000181048450780102003c40360107804451000034444881415005103c1c04044280c083c142006d00b00c461f8040e45c018 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 964429739 1250 964428489 964428523
    0xc21050d0e0c030a0302070303080f06010906031a090a0510143d080f2a2a100507020d0f0e060405040905010b0901080a0c0902090114040806041e0203 66
    0x211007400001002500500c010003801c80b20040098500291504100c1c07104402140c1c40d000030518545041e0349092003010180d6440c0c00c03151601d6400c40180140e0101c0b2880c040956080700340c2c58036822942441a03404003001714035030402602d00011003034158000041c1010064001e00b855840c043c00111461406d00398203081d0b0265000100c207000500d1080d1546466240c0d54920b00350807042282c49900a614040c0306556020048462040141c003404844810031403c2c412208413000500100040b4118001c14021065200b02d10602c400b2440c103000c1e40100c1a07a08001418014a40d0214581c806000e540c03242c0000686488080c08054062052020fa80c1701c03039407200401d4500800000b0003e200d102c480d4103000f40201000c01429001d820100c0c00845ca0100c0080d0300b44403141c0c07001200325030a01d0044407000070b41000890504209400c000f07000a021004080c201070500315001d004282030620301208262809020000001e10742240100940c0c0d01207200c4d140c0c4451086 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 964430989 1250 964429739 964429751
    0x302030d11210c06130614070813110a1221120504020301110d0c030b0105031006030519110a121e05040501151403060108011b1416030c21050d 63
    0x7000a1a003e0700c03425034010701ca01c1007005051126070780a903000a0281108000e2000000d0a000c1126003c80c0c00d0740105503403601040025600306103d1035503a000710410750114040c0b01c0001d014042d240e02135800e0030f890010007070500c6028142034003600440200340760101c40320724000d411007100410345c0d00060b80c0d410014055403020f420600b808200001640c0e81e8100c112545401044c018440c0c0c80020701d010300035800c43d4021012203009200c3c41c0c100c9200c072850208110064a0024203101080704030f0014a810310566001d07454400503140440342d210700078038400606d1500c21146495401d420454412101c5a5109410304040030260700400d41c4c1c3c0d1907040440c0540800740b40044c0d0401e1b07112000600e28101e4007589289c09048080d00c4040e41d17283c006909942078001c0410790f501c1200640f01c9842d0103201c3c40c40c04a20304410315070400803511100c890500d1615016004584040d44d05000c1022600f41c2020680300140d1560050752030180003001401035001c00c820b100c3d83d41c0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 964432239 1250 964430989 964431043
    0x21020d110a0b040c030b0906070806100c0b040807052e090318090b0307120b070f09150302130501050a02060114040e100b12060412050a050d150302030d11 68
    0x4408150450b41040d5103403000e0034030b45014134180d61588820b5518220a401040310200b02240e00c5016003000d0741c03165800d031208000c00c441c0c241d20740503003000c1c0540c1c55000400911049101441140142076032600c40000b401e00301c2c204112102c50442000014103009c04a9807003802021025030310b8200001c0700c42c06850180c4a820880c90004c42ca030803840e600203565005a046405005c1b000d4044e2094980e4680e0600b400070f90340440109054480c4000581071071040805000305e20301c51800440039599a005429514a005000e0001a4000440d5109089042d800380300510080c40c00615103003560708020b44507101030151184408a80c56001c92650790343d045203211039581c03015207100000c0784908070003c10003050246e000d901d8410402c0403200001c82c0503489260803103510110340400020464180e0301a03000e05040c080c080c001a81107014610548810b20044c070030084202c0e0941c01014a0f2071018101202000050711180002c01c10108080352441c4084880c0c40301c0a02030 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 964433489 1250 964432239 964432243
    0x130605033d0e0708010306110c19050c01020102090d0204050705090d08031e070c031d030708061506040b04150516060b030c0405151c050d0f08090a03140309100e070321020d11 77
    0x50404204500c14103066080fa8855102d07a1040b80780b062f0304944150980f000168280d000d850507084c0d202c071900140001505180c0c10182d404552450181d2034020401c000484aa000355030036114280044100041d024183d106600390320700718030780c000c40341c640208001c10403004000003c00700500c903c080140c502095810030303c0307108020240d400242d100c08a20380d5404040385c01c001450003a5114008505044c5c0846050720540b0b414145814101606903201403003550310a0700f0020108188141c15484807060740d0401c0c459540400d04210030400c05181001800c02075125919003414480c4040005000340b0340d00078295560542c0b400c0c28403007103c800b020307110b0191840c05044540c01c04664011000103511045403102d180b15192001350581d41c5107004801070100d18241c070401c002e80704000c081c551007103001c0125502c42d800c18000740b05540076141488459070105400744104192040e5400e100304600c0760031150a08a20002540c071420b02000368180452988501009501 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 964434739 1250 964433489 964433497
    0xf1e1a1b0316051018080c0a210e0f0a15050d020a02030a02060709050f04110d0c0207060e0102030903071e03050105250302130605033d0e070801030611 67
    0x582a29140c56000c07070b414205031144101220503005201c0021807141040c402c58600000c4510744030310145060391021850340c0031481240c040d00c85c8480304c000080302ca0303401941e0f04021070040d03000124120b03005400680301e0f01101c4c3c46820381c04100c10060722103144e03020403980021140ea02e14030050005407441d204d01410341c1d064500015101480c03d4000004042410240e805c0720740d40e54484800f100c1e42d265900400b0b5002d498802036001c1c920342500a6104849610044c80c0b402c101d1030140e6003100c0d030705c204000c09030700404000c12400d03800c810140321540d000e00240d464002e007000025244d80c1103010350440d10048850318000301d10700714981c00c051648100200f040b0708181003000701c5032204000e48021140c02681c880c4026120b8004e6440b00e011001d0543c0441c3c1c1803c90a8509800003403426425044020f5640c2080c138201410031000d4400306080300d0078860352240501e0f611010f8101c00174201c1040c00b40400c4a5016070231504490300503000080c01140c2c061203101600c5 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 964435989 1250 964434739 964434787
    0x203070c0b0a09020909030a1407051209040f0f0527030702060309190515010902040320030f01090303051008010204083703020d02011a03100b060708040f1e1a 70
    0x1045c1040348450001008228405598556419000c0d130200907044a200301700005105070030854192800d4000603015000001d001440414882c64026003001280c003c1c000002005441d00d040c070048032080b12a50480d103414102c16091b120401050913500d21035a48001d0080c0d100000061200101f40a2550140c20103d500c52814105043c89903489402800b44900a5581400014001150320859084942c85000300b0500c1d01d0152201c1c00410840160179018051180082c2e007500080c40380c4c403600b034840e41300001c036030801c007441403050405504184000d030710401060150f1340d030014200394198019407600351141e400c07200918403048400080f45030215401802c1d401c054020a509070468400da008101d0604020b1740e07441c501d03241c108043d4060b040072800801c00c0410b03400c0002002405000c2c6c52074440e9994030309000c2c0e03100343d0000125641c580b0092000d66455138000c60500c0b021140d16404506284503006501610004070303000c09400100c1070b080100300903140c05c0503c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 964437239 1250 964435989 964435999
    0x90123040b0c060103150b1f0207030b1e010506090319060b2e0e0a18020c030f0403140105010b03150d06110a030b0901030f2310060501030f0203070c0b0a0902 70
    0x38624110b43d142800c2c002121042d0368030070741c00110002c9100c3c0e0940d90400030420320001180310540c010b403005035074810f002c5000d4a040440410040c10043d07025420b0492030403005403110429001ca8241030704981c9c8584000c0281001c103a4001401c40d024680c0c0e00e0200f40c00a8240c503003000100604043e682e0018001066401084100b0920b1800c441c41701030003000031038606608458900c03061140a50081554109100c1c50144048028251003001001441c1c0500610b00340c3c916049000401c1418200203414001c100e040745c4200d98010420000f840070b0b50400d160740c991404000d0400c01e69601c000000101076484603030301c03060540c00c0f1a0400004002c08100308007644158007040100c1d041020307010290902d01c0106040f25003202c410070780c072001951901011148a410b4413400b114860581c65a0f00c800e00c03041102400c032000000b18285410005825152079038a002103443c818002c01c00d0740f83e00806d8034002c02da4000ca80343c055680f00a040300c014000481d010703400c1 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 964438489 1250 964437239 964437247
    0xe22020307111209010e041e0e031308241519091506080c070308041101170718140d0f02011b080d0f0513140c12011e02090123040b 58
    0xf103001000f00b00c828020380e260600d00a401050000f41c2d10130810f5200d424007448500e03034003045540d104901e4060b05e1401e40e86084260500b4505204c0e80e03400044241c2c000c07071803075560a00e00402c4a000545007808002c164a82822048464a512100b01703010700b6411040e25400c00c5418046d2002d00301c001e01c01c118055104144107038105c0789000c1c0c00f0102d819080450b0907201c048043e84ca02c6a41540c407000980c0c1e0303607612615242c040007240c4e410301c4400144000d010300c0120f689442402240d6035908a9031422544147e0f12500740d02215850a901c90080d040b42c5465030a1001c2c2d03a08021180503124240c8012070716502944c900b00d040410002c07a900400c0403800050400c2148210140034124030a103955044031001d440c50440d92818001540000740c09880c0c0200c1041e4000c29142070300d800c0e101140303a0b5007410481103081d0755240c180d0000620185601c8803980400b0b40114108009c503c00640750758003240012030030410760f00a00c0f16480b1010100c1b0040d0a040e4102500c1d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 964439739 1250 964438489 964438513
    0x81c0c080d1e0c110a02010c020415061205070512070f021c180801060b07020118030204090605091504110402181003021e0a0503041104091406070e2202030711 70
    0x5190442c100c0110b40d4100104000624822400c4050f19160316014041c01c003071550040d01d105840d0340c0201e801645071003150800a840c1c145040040000340c807030005851441080c1030840394000e005105114051008441315001c045010b0380c400310360b0510001d407030b540680a901c0c1c0000a281090070090541d2140c03816030b4806a030030b150380c0c41403100d440301c00c0c0c80f00100c509a801c0c1d80240452440140b1000016600c550000c0c90341c0b1030910741c2ca4040d5a2281c01150a40b0304401c4103803034064580c2e050041c0340704200200e50f02900034101e414050f0901d650b4011040200c001d480e44a1034000c6843d10500c5000f03900758440110060110144c0031910390058065008a90051441c2000488500e41c00e1012000c43e02840040d540e00303883d6990710360b03c1c04502d4810300d800c10340050380c4807030403400140c44036000001107507000014280f900c1d0802001740340308514640c260064844918800300d010707804101201c01003107038401503140da41d03004007100c0c08100c00c00000340b184264625081 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 964440989 1250 964439739 964439771
    0x10e030c0a03113c01090e0f040308060409151109091312180501120204080a0606140a0806040f02041401030b0a06050607080702090405070f0f0e01081c0c080d 70
    0x150380201500c43c0841c1d04140785048040c030043c03030140b00028081c131210b2080c094070b1034803522840d10141070600540e03031609018242c440c0f01f164007000c070f41d4180c01840140740d00050b10701c0d03001300102c4e410b0281050316035981103984000490301d21030980313400c81d0020080c400c43c00d80380e080c1005010300c2580e04e032901c580f03400d02e20f074080c0640d0400440c034908071280d48201c4011910340c0d001610b07000e900740b400004407400d50501e10000c0c81168240004240d0380c1e02480b80040340c034018400403d055042440001e0300d89105100e0038861244104200103203040421019806900007540c00303503c448034000304d800b5115010f0800c600c464008004000c10890580c02c0780500e034005000c12540c2e840781e003440410710071398402800c1200144900401481c2c81100d81783c2c0700380b10314152821544c0d01c480c050341c451300c69000398958005400701071207107414070100c0e540141220802440ca264070b00c1044103034070b4641d10441e0100b100043d210f400740074084040361345504410000b00304403c10542a13034 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 964442239 1250 964440989 964441013
    0x612050a1b12031e0f08010e040c03060e1f02030106090509150904030f0206010602060c19020c03070f180c09032006030f151f1b02120a020109060302120402010e030c0a03 75
    0x400f25290040d0528081c174030600c006000148581c9825070240d0800341104a5681c000b00203c50000c02d124001c00040c2190103501209044500200003130326400080d81c076100c51020781c0d076410302d1040c00100303c40b0f540045080c0032a074050301d098141d40c0f036001c5441c00042c3e56950890b0000c078000c040c0010190b11a4044803035002a60945420341d03214403040341c0350359081e2070110341198144044003d0020103c10708103850401d00458103e000b42c540440e0404020360b11110800c408200100304400c56076010000c0d041c0c035064200700c408050080a4058100b60001800c41c0c0a02e244c00d02050780684a80342021317400400385610307440c0c007080010b0b12600c210358500c140104103586070324605081401c120300e105000c90102114034082011200e40c0e0b901d42c0144181d40030b250000c40982c495840d074486881804015000b149070600004d00310001c4c69221f2810141304000341c420040721071092942103542480c0c07803a422284100000d00c0c12030003451480d804400600300108200c0e50801e03607 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 964443489 1250 964442239 964442267
    0x60207030309150c02100e0a0e0915010b0f0c162603071a0a06030b0f091c0207031b030828030e0c040921030e010612050a1b1203 57
    0x6810907a29099400740507418183c201d000701e0742c0340c40e020005142605980d118102c891800059803080000000c02a18003a40400c403000c07402824230103480d10a00041880d083e0341c12030204294500100411507110300e0300b0542070050082010600d0103818171040780440c0343e0702007002c545034941c1d16241c14a001c00707200385801511007400c641c1b010790200903500300035044a07500701c5100c1004800344d041400200f0140906070f46100200c0002d0b8440036081c0504000300c6002c060b442e0426080e4a0192002120040d14500c0c5c0070000340550300080304003d403540105a40700c1e1800846052001084540000302200300c041210041e04101c1240c1c02903410356818141c2400031501401e904840c40d40300d54130780d25003090308003100d1400e10b60050b2214900c91085c164161507094070f03035134481c04a1010440001e84030401510700280c2401840702402c90000e108003a859980e58250b03441c20a2500203001c4005010301c070080488540340100240b00385420580760042902e401403500c2c42c55500703 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 964444739 1250 964443489 964443497
    0x14010e09031c1a2704060f0603060e070e0609010902070602040e04050d0e01031e11121e10060507031808100c1b0b07080a0e100501060e03012009030a08040602070303 73
    0x501d1081c5402d909024020418007030f50340c4e044443ca040c42035101001801076409544501d030703000312519180f164000460050b030000910810301d100d090b0520101e40c4c0a00c446125481c14000c1c1c40d03880764800b504441c503003180140d889241e484c02c14042d0145501c0840c0e0110044108820700802242141c00420155180300200d0001c0707005404480f050420b09030110707000c11304a030a036206680100b100082d61504641001d1002c00c0440c0d1800c8110b4820b002680000503c030060030200b2486500b00d054819641865402d102004029000300d10000c0c3c20400a07103d81e0700301d86049a44800075055140c2540ca9600d40840c24101422440084100080e000c047d035100c1006549460b0001c10b9002e0044601758951190440340d40da4041c0c00500c60680ea0710005007241000c010815602d1341011001c03803a90315000018000d0446911018000c1c1d0600e50744809019440c0c00600c0342c841007044458030b541411010034174006800500800109000902041180d000179298003224032030b5803 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 964445989 1250 964444739 964444781
    0x1a0117092a0102100c0f0509030a06110705060708010e040b150a0b130e09120a02161203030c0203071104051801022d0c12090105210405060a14010e09031c 68
    0x1180340803a0490243c17140002d980800b03078021140f04400030105481d004007112050310740b0380c480c48101da0344014401c640420000e554004c0140510107103034000054200303080f9540c034001c0b09040c00c1c1001403000f0081aa64030000340410303004130170104401c0001c0d248400180d111119409568049014440e0941501500042c440003511000d40b090703a8100c09444140c0ca0002e258060340c20416160040d401000e464030008001e59551000800c41810603d20082903810050110360300b4100e08000c40d00104440d9012900620404400e108103560004003a41c078042480302034072914000185135400010405080c0301c0c1c001101d08000301307070414035100c9500301900252a1061442c80003454000501915807000c01c1005401c0e050301c1810028030302000f81144007194904441d20342c40100b0380c441400240401003004540c0480101020008514000c2c90110900d50512424070b0800c0010700081c1038001c10300948039403e42c03141d03012105201c03000921010304215504006002e400c01 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 964447239 1250 964445989 964446013
    0x1703150901140d060e07120507061b2f040914010506010e0a0b090a090207140d1817190c06020c010f05030a020703020a0818041a0117092a0102 63
    0x5401540700b41001000728030500c0d803554640001e00001c1500420030300a4003070020b0011507544401c0d240c18800c0c2c024050841c207100c0040c02c0c00200d290000c1e075440040e0701400000e1248040208100320208844200105a01c038044280c810b402940d5006404c2854520402c08480700341503032407080100030320807955030100440b171804030141d146170b006207212810043c800300b65004081030000507092185180e180d107500c100366071150900311002e000f00301306803d44540c03d1110080342648e03460200744025900843e80c1107211039004491100d00c4035007402c446036004001d1000040d0328428190b20500403400c04005803141885014050301444502d845103610680200d19036944c1502d41600750307200e50f0000340003900148011015840b07110702d0100490000340c00ba1080300b6901c10f550a280c055501848240e45040180440429944030a280385070b801c041441e006a00080090046544d5580154a03002131000200c000010301c00c444100d41c0304050040004003800e800315104c03080a5 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 964448489 1250 964447239 964447259
    0xa022b0911150306210a0311061b0a030b03010f060f0e090105060102030406030e030c10050a2409090305071a010e060102190b06220506150c0c09041703150901 70
    0x2141e0b0394242c00e481040061060315041c107031016010b1420003040b0282003400341d818909a0460400da0209400301c44852150204010540d40038490ac26125010003501d0005a160b0054409440505440b8069100c003503c00754446095034092100620080c4d58580130380700384441900031611100d16160010701020341c140030b034034003600041e0300031441c0a160035000c9004042140f2020000e000421034200c0215007002119007000601c100011b46040c18010b0030221804145d04080408031003984411b50048480703428110746015801042c00c0b429407078210354510806400600240e02c40054000402c18902c1c1181a604103503404581c0e51154801aa5161914050b0110001d5020110720020302080101c6811a1018100a0341031303400303c107545060100303100c84580466807801000a18644200e00c0c2d40c0000311012223510703101101c8055a240e075121110203010b0800a00070408010038840360000303407481055082d0303d904045980c00e9000b07017140ca05034440e05000002040400b80 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 964449739 1250 964448489 964448509
    0x2180901060804060203130516091506090b180a060507110609031c03020d1a0a1707060c030c0c0e0a05181f090212160801140a022b0911 60
    0x1003502d800040d03a549903911000b951005001e03060045107040c02c03500080003000f4040f802300b502c5003002c40e8a8144003080080f19282600e50103540b41b409400c000032504000444141c50841004940d24440346180d0700e4403c000d1080650070408010000a0303440d8498054103803548601054034820b40c852303003080024007804441d07030781c0358112400c02c1d42d0005400103181c211080b10306016061004601c6c800d8102d40200041c220f140c0307500254851146020190f02003d0001004501c00781c9508500c0d465441c201070240ba406e002045540d2002d0501886400b101d6550080c10108210344404101c0b580300c0d001d907000200c1c5403c0801051401528001c100e103051019070003800030000c98190265113070300768403041500035038400c000000340c3c0300c0010300560701c0458001002e840805121030440b1007107a41c88807900d030340b52403000610b2207004c8090b56003004506001580f1218a034008864462242c003c1004a0348079403007017400c0584680019041c0703030180c40075184001a100500840f141d03 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 964450989 1250 964449739 964449749
    0x1090e07031e03020c120706094e0c080f07140402160b04030302030415060f06270f05030c0d081e070f05031206010c0f080a0509090a02180901 63
    0x2140300020842e0b06515000b201c0321802441200c8515000c4030200f41c2441c500155a0040c0c2c0110744148000c5810038412030042040744804690101c02a00c1800004541060034110720f03960008449002060b03185054400d040c0303120340044012a20f001084086180310315100c40c080e01140c180e5014012840504580c00d44100c15201d215400410009600c4402c0e020400d80442400c440480e00c000204c0380320b070b880b0f5140181e070790605040070001444c3c0d0180c13100c051828100184175411291041d40300f03c44050401c030308140d15154040341a510b00814481c44882e03080000140404111a04c604641007a01a244120702610174030180449104010b4003000c003c00c000c18079901614058040c54400c5424182412560fa072200d8207261404425141d0340d20100b0a0300641d40301c41400c030382005007400c00b41400702055407072100140102e000074220381004102d4003041400b9408a130508100201007644500d050744446000b50081d8060300780c2d0500800a041890811316000360682d9 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 964452239 1250 964450989 964451003
    0x11103090a03030f02032101030c0f0b07060908091905191d060f150d0b18070c03020102040510200607080c090103060302040218030c010509010c080c070e010e01090e0703 75
    0x20300b5510103940707550111034a902148810401101300d80403400c07044032001e01021b10440d0303c1d4074609000c101409150400d4080908808080000f094108120358130260720140214040a040c1800a80381c06114903141c0c20018030300000d12501c40c1d4481d5241502d0045460600c0c0311801d44088903800c03918041c07440c2103020004850350200381d520001d6804040203102010300450748001ca0142c00091103851b06003040031824009070301c81800b0700201d0410641c0d00064804441c070001c40300d0311025059005021420159a09042c800c0d0111005031201900107aa50841c02c01d009241580c01030181d2881d000e00d0052644500b004101d00d070181069558460a540300c00402c1940c60344868030960516540e21400401030302e072400034010f0100880601c01e103441200c41810305102090001e14100802001003011581e00824500030396a0410303609070b1100401d200085c90300c8816004080e56108440000581c91054075030380e8140c440a14051000160280f00c88e0b90342c0a040c04010800 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 964453489 1250 964452239 964452259
    0x1020a120b130e030405121005130c09020a03060e011412071508090a0b0f06040b010903030518060403061805100b0a0501050307031b1d0102030906032701021801110309 74
    0x80a0b01e800415480d0101c400741c034038060b6102c5c00944808096910380200c2d400807000300752180c05c188a960340c00b5001040e2100c1c0c1d07054950b00c454001c036450207062130640d40802c00c501024406c2c0d20500207401c608841c0a40741d611000c4124186042154032480360101c00030400101d800410140d0844040300804250300c081d0344010341e41080010200340203840b800c441da1020481401c110745c02002880303041d0010f4200002448290748045100c10b06001c4810340410000707600000303c5d05203500c010b078021207030b42c07034407001900511172230340080e00c1d403424803040c82c2080c2044050304001610030400c9651140d6043e88000540c0c0545070310304c0e48450080310410055000c3e40080d6800740c01c1d45000280c0903035522000c1030314920f401400c000900072159a0b900402c42000c02c3da140c40b801d0000314104a68140082c0302c2d4440240f04000c2c050304502c1c018188042c0d010030101c0b81c00108000e5442d0b2012007005041c004903402d44030700103140c0f010402170b044408405c5604046001d02000d00f0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 964454739 1250 964453489 964453519
    0x1b1b06020306011107060903020f010503070905040e0a05030304050d03140f0c0f0c0a050607030c05040b1801210f0c030b010c140c1804140f030a140409020c01020a120b 74
    0x81d00002c20740c6040c40242c4200f9090340b0014000000a0001038403000c1c0c41c2c034154010322000748111414a41486030410038000070540001c0004107c031000c0703e0125041c642c6400b401d050141c20040100341d44004030900c002c224003c11511811049a0340810014072210301410345076a05a403050071440b010300204135014000001030a000e003040078801e03e00030364444210f1078040d1004003a60b040c0c1060081c05180c40d4035000d084003100300351a0060801d810922903802c41d01c90302854102d5903441d00d09600e941d900941001d41030030015501e800404111041c100007520344118007543d80da00e01103950404a01a104016480070180d40303070007804005941c3c00941001011043c02144034502c440072003599213025001c6540c17900040c603503031410240740200ac1460004210506508030745900d00361120004141c451051852801c4d80703200c400704800007028403841d004060f101c2d0000610945102d0b0540041c03801d0502641e9405002690211007802c803404002c01d036a0000480d040690303 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 964455989 1250 964454739 964454741
    0x102040621090b2401031a0d0204060f06110706091d1e070f0e0d0503090603070e0904081b010b0a0b0903011b03092d0803281b1b06 58
    0x200e42000346000540d08503680398088003190445040c40440c800704000088110484603103044c4c01c0742802c090110150781504914102000b0030801d0291810600308401e656991b00101c0083c04007800184102ea10f4040c020214030212b4540c040070300c142100040d0b028400c0c06d002c42115041c92500e4500345042d0140c10348210701a140008000d00311011540c001c200038034a0340100100d0721400c030041141c4c42c002c0c01030007070380c0310180c416003103080f420b00420303000b000300d42e000c01084420940d02d80d1002c406403203100d0ba0400590704203100404000404c40c220004010051000a141240300710000c1a9400da4150012250b00a03614038010015008501d02415410200600101b40b602440c00043c442052030b40303128000940f504a80028002503928415501d001140c1012a1100100b5520b00c44618080014280070300000000c0b508540f03550050b100c1181540358801c8070a030341d107030340303025144845055110845844814030803500030a1840040145c0d04030b490b00c282d000e41c80d118 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 964457239 1250 964455989 964456037
    0x50405090718080304051816050306030307050115180b0a17010b15190215070503040f0209130510150311040204362c160e0a0b0301020406 61
    0xa0600c0000c4400800b02c0001030100300c003400205000703645552030202000b030806106008800c1060345c040c2848a01510701c100b10500c2130040c14000c0d600d866003004240b951251170400340503540b800301c582108100c0085074604aa0140c1e8006c44c045850300480400c603262291403e5102240325000c00000d0030081100800b50400000000c0741c0910b1804112018812158030340064000200318411030a4a1104640480c95100502c1d9982e851142d0240c5484050000014020080300280c10414045400007005501422464080c148082900b0b00c51300103a00843d814055412071082d28400fa203d10f0b8005103401004a0300075146489094542016403c1c1e5034105808000c003107905001c0c04041c500422202c2c06100303d12240be4030003000c0c5e085c824203404003a41409122102d1a00421220107001200402840c000909070240b070b2400200c0480c454000c0c2501310002200c14860a01500c100c1000005100300380720041014200d1045c1e015000c08108803141e0b0002d40f070580b01d030b18 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 964458489 1250 964457239 964457251
    0x9150102071d060a0905040206180415060e0108150f04020d0b1f020f01090b0406050601030b1906020c030303090a12020f0a080702041a0616060f0504120f0c0305040509 74
    0xd140d0490301c40070150a02d1041c2a01c1c030300c1602200c01030001c2800d001841030700801e51504108202d00b41a400500c0d1446070f0402c2c0c41c00f0401c4002a00c08941d50703940704800c2400340320b04815030a540c0c0e04001d001042d1000c40240418640030005e607800c4c810b0040034180b04801088140101406410400250050700030909600d955103044050b60b12a542d56402240d80603003040d6404084441c000e20301450206410540d9052000400003e1300501245420951054001c600ca40c0c603800101c0041460341d0700c02c0d17400080130180c1d180307040081c440e610641f00507078280c0340c0c940c00590034540e99100598507607403107038800300c682400302e1903104122003500d1051041e264480c2c60407805516100120342c0a43c0c20642c0091003004501d058400e00d5885d42d1000031091038280b413440050b406000b00a99038000ca00c1c81c051520401441d94000c0c15410090b00081209090a04010540c07484810b0140302095040d0b40c465091805070300f07005900303540350380d81031b103007504020a100e01c805016040c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 964459739 1250 964458489 964458493
    0x60e0d020a05060708040e0f330d081c0605130e0303060d03020f030c0619090f120203070218090c1c03140c0f0d0216061d01050f030a050a1a09150102 66
    0x4034514150301901400786403c02d0520321682040c00309d004840b4103038584600c00320f241d103590030404105108200c044107411100400544c0c420b0a04586500c92170003411a8040e04040d12003000181d60302003400da03941510101c0c400110014510708880c20300b0106880d40e4014800125a40380c1406050021440fa105840010500410b01491500b1102c400902c50b04102c0030001e582284070101d085442d42050203011340c95954a69400642101d40042d000d0245070104c480d029008100b260300c03a0351b000c0d0080c0c150b0800f402245c80d81c210192440b220a002d89540d42e0624a000e80041c1030f42c408070ba950010602d495941a0b848001d00c4000300302c1c0302c6052051906559061040c1c404a21100c0d0142000c820011002402c080500491082020046009100c0d85500a180c41c0001804400701603039100b0380c0d4010381d558000c403c85c89010140000030008480c4543d0003090241c0f60032082442140321440d2240041c403034510165401208881c0016404c42801c81814040901801 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 964460989 1250 964459739 964459747
    0x309011401150e01090506030a110c101505012307050118080702030d05130306020d0e030f04060f140901120b040507020c1311092803030306060e0d020a05060708 71
    0x1829801002da200144a640000c110038042c1d80181204240850034a01042924104400606140009024007109a985100130443c01445604460002d540e40080f510350110b88030540d8080c00e14542121000c0015107400516540952144442c40400c0a03c00d008481c000d6682c036019000041f00307440c07540d2520500c0b580e2649401c1000702071402a1001ca030344050300d0050502d42401804e48a00f002003c101c0c40c00846a0100c2030016030b94401340140c0c3d182c2c0380503504000780c44d800300c01ea40f440c0000141d03540c45c002101c00910485c1c8a9071249040c400345500c094860f614451540490300804200402c0203600c505180050710702002c900080d0441101c01103804c581c000c860000144e4403803041d4600518004070342c1003500711840010720040902c400201e4490103201d030614060303031030f01c02d00d200701c440003240381e04421403050740244110390f40c1d09008026010b58401c04003c60101c10310301040d81003009100c0b8107260040d0103090007510304000c0c0706060b400b1071820b40398010280 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 964462239 1250 964460989 964461011
    0x180c0b190c08370206040201021207032708070e0103020a0501030203071701030b06031905070e09030708030403030605040f02070b0c0f25020103050c070b010b0906280f0c08070602030901 82
    0xc410074004401a81003050f460b80062640031076030301050031000656010404010050703a00081403401e108818000c2620b901544c501599018440090a8a180040c3da0540400ba4072415031000300d4143e2011101003c2c0c0c1c900120958800c20301019401c12100d83c000d01055019030011604401d042c80c04000c540c50070188000c111400383c2003199240c1041c8148903d03440c08110003032001d0440e000b400181102581d48039030315803440c4034200f000202440003c074901014026200550b41106426580c0c0c0b0705850010b0051559000c5d082c0700d1480d0060400048200e4400d80e402c1036400348920070142c5400070304450580102c2644601d2102c10000901e02944c0c524004082e0404c070681c2011a0801e0320000d4151440280f40603041d88060110307001107401080d40c0380c1110043d2902540d00c6801c103010480f94492085501c4440c0c01102c20301c9000300300720444880c0219550744012174044c3c84401151031500120024001a2041c0001404501c95a000316001b15255000050300d984038 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 964463489 1250 964462239 964462267
    0x504110d05014b020f0f0d110703020307150608010609091205030603190f021c050610150e0a1502030403110609060a080402010c0501180c0b190c08 65
    0x508411101e50b5140e40d5032900030450b00c2520548128203441c9490340001416001204050072203031040c1015502c00301c48a00b40d5158111503102250f50031040e5140224052946182c0c01384038541340c03692070441076200000182058946d42035069002d1860320f201070b214940709180e03c0c00070401c40390b03560b500040e441c1400d20580000f0b0041c0c00c07000c500c0074814204448118000b030b4003042484010003c000d560303500401c4480c0f40c5010010ba00c0c0c00c100d40340c2042504c803101c5407402504507a01d0720754041c40d15a580b075000b881600c104c04a4401d44d0369152020308440041c4151542014080c0085500601a00403204400806041206400c1d641d00c05003000403d01508500941c00c001020300a21510700c44095907002d003510300364a401c11a20118210344075010f0880c081080f20f20105086a01c11680302c07260715042070007485003042e0a08252129200c0040c110780300c800e1602c00041a01081c001c0d5889014140310f41801c15040560503940900103203011104171b4000c101c20b181c40900 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 964464739 1250 964463489 964463509
    0x70b0f1b0d02100b1509010c050309060f030910141b070f12180e0a09140f030913090203060105062b020418020313021207080124050a030b0406050411 66
    0x4154010244881e041590b00211410a050306000304d00038442490705c0c122060031030b1002d036020300e02508012039030304081d03055014202c2e5003980400c3c00505120b400c441070001c2c40c0514064025100090b0b0103c92180071900c10380c245c4110002e038400050281c460011034401c1e04050041c1c5645401d480303940c1d60303c1000d600c3c80d04442c0240465501006558041c908200001002400304140e9080a860907640103009050b0310595854071004002c2044100402440d080403504075194a0014449c440e241d4000e000c44502075908004603441800f814040c106161360050042c101d00d0f4240307000d001443c0e0100c6c0c0390943e118080c80c41c0c805185004141340300c0546400700300503260303401c08401c01d444ca00c0f102c100d02c82050040c41400400849200340c3c11f5141d9040743d040241483d0041124102481039115010365440e003a407654001d0100b000b0f9a0f416800d490302031059548960401c09012420b020203040c0e4000c6500140002c1e0040c3e00880e006402044000c18468040c00094100c80c2 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 964465989 1250 964464739 964464763
    0x3070912121103270f100806032e0203070c1e02010e041b18050a1e08032701180303050d1401050f011d0d0c17070b0f1b 53
    0x1e44416034041c07140d010703104611502040002d107140050740081c001c03a04404802e402c1e0807649641e2410340e85d90318030240740c152050141c0070303201c1c240c0740d842e010307204003400c44000c0d010380034502e50107000b5007010f00740c001520000c0d0454060100710001c2140290401040c100510004131803803000f0815040841c4d40c84120724940c960b456041d4030004041d2400c0326000c030b010f00c2c10711201b000c031036001107003104401e0450301c0c104501c10619542819580c03029401142c02c19203041e00806d110914a00d0907003410004030441c200303260385d00c0b401a034070710a13408243c8140f40c154881c4684000700c0c84020081d440e0504d441252400e403507107481d0500c0381c107610072404a6070008116000b000d8502442205003420382012856615001c041204201d600f4415410801e0203640c00795420f54501d403892280b50701a26014428200340303480194001c080c041c1a0b01c0150000a01900c5c441c002400810713210f5a890150800d12201c224240c513400088000000301c003100c11508a042d030820140300845 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 964467239 1250 964465989 964466003
    0x150308031504090f02090601170106020c041505010f0f17010f03050d090e0c0f07140105040309090b060d0207060e06070827030a1110020f042c04020603070912 70
    0x81005507030603104050750102140594245800c0c1408265131100c00380445406980c4aa581c1e0368650040703a03c0381e903e5103c150382111080001c508113034000b4500d240e418056408024801c0403100350806d008145c4101ca0018104100028a00b071040d104d404e060001c030309003071011a41d2105c0c01d03000c4483c02d3704072180d0110f00c041c0c00c20a00c082003241002c0e001d202e00b040e010050078081c0e4143c1c040001807000c000d50308005149100c0c3c40d040400c95003401d401c5100804000d80b01101c2078041c0c2020b650550001d405004c0c045210542841003130040d00f8000c1c0b140749402c0103d050383c0080c1d0440981a110a0740e1600940709140c0c0500c40b4911420041d9910845c1d0b2034803107845008585040c81c10f2100c070016084000611000000315104001c86003000c0302d103c10032001d01490300383d0354030011054030f001003464001660f040d0041d009441d003d003000703240e00252021080300820b2030300c03030481e01780f01c2d0101080c05030074030300d00071a040760032440e2085240d030703e400c00d0032000e59651800320340354 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 964468489 1250 964467239 964467241
    0x9030305190509070303030e0a050f010b18091009170d090309080f030702062a0d0f1b0f030e040c050918280b10030f0e06010803070f0615030803 64
    0x8107000e420050400c941030000b00580e0500280300c50342c03204103000040525940d848020000b6104102c0300d04402d034460211040090070460403806400c1d0346400383e00030314080c1010304508604058a0f40700d040c121004224240f09000c00c03001400007030034103035000e17042440490710800c141401458610307188040482c41c030545240080c01242540e000310500d0304940c014101c0504d010044030466a0110746030b685030070705840c43e12909034030b0380700c8240c44520000400c0182140411800b0708155103459070540c01e11425001d803107481080d50743e180c1101100c0300c0c1d000010010074094216a0091070014900722a280120301146d8486050f4004504003286004651402c12014003000d4022034840210b41010005d41042e91807103440078a4040d0707402c4d4802c00e0003803240d020203e01e0340010004043c07c80e0440f0094002c00d100c0c81c1040c4150b04011301d002070b503400050928101c0c0d198100452500f1095190403a030162541411070386161925911a030f82042d001c5103001440c001d124240c2d403 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 964469739 1250 964468489 964468501
    0x11713021302071406070513092003042f1507060e0610050f10020a02150c0102030705090301051008120a030b0406080d08010f030308190912021b03060103021e1309030305 75
    0xc0c2510083c40b946c1000820005541504461902e846c1218000680410200c44a03071a0100ba00029001d6481180c008810030052041e04103403001c003902116000c003003000c0ba0042d1260160310136005941c01160444c080c030303900030403d001402018083e50b40042d00c0e2440e01701041c100700f0265540340c4c201001010911152400d1045468916421a041d4071183c4c040d0034044d45982520401a01c00c100dd40001c010301881a402c17603070403600d082d008650301d01d000e0700d0180c02904a000e24500039880c040000746600021031240b020356082000800742c820049554443da50f001188050070141c40b58031071103141e01c96008100c041e002c20800741c40d407502c032648000e00000c0140e006400c00104c2d05400c2002c00d8100c1681c036000183c0380744950030400c5d148100406804a000014040e103c4066140c1c2081d501107004800c414810b207040c0f85d2400c202081541e075100c00e0001a5209460001820826002d440070340004070010306a0f4100e013403003e400004072003214005030040394840e004c00003 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 964470989 1250 964469739 964469743
    0x9030f010606140705250b03130308060f0904081303060e0d022109100c02090403080f1b120a1409030d1407120b13021c0b0117130213020714 62
    0xa0001d2118500d14205084e544401e035030341034000300c80c10503861880c0241740070108200410010309002c00c5140d5a9003801c00d04003162491941c802c1e00050382e90b0000c907005141a1041403c0780780d000f4500e45860700c0d03544400c403a41d0300c002e9030304248681c10200000080d05a00031080c04003802d070003800c205c5c0040c4a000e8201411f807402060303031040701030010444440b10000c3d07641c5803400b9505034241d082d40e51000d4a084c125654040c1d80004c04004200415600480c807031320402c840c564800464549500084459845104410b68801c0921026115001c0c8176411548a20310b00d4020912190250b0000003140044e200fa8900e83c20009001100c501c080c0030b400c2281034681030684503490440c40040c4081e0748005001e80994036100101d000d13035900140e118a0110010045550700c1500b2090a00319015841403039119080c4900089158082c2103a07602c101011040d1110b65694140351800c0c150b12007408030f03400a8070b04001ca0107080b1074405080c00902c1001079107a04000954614 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 964472239 1250 964470989 964471007
    0x60d0608151f060804020102160b0a0306050103020310030803040c120305030a050f010506030a0e0c090c1b012a02100207060e0f1c0e0310180c060302130608090309030f010606 77
    0x4100240c030a15002c0e084103100074011164a4603080c41d95071260720040782003901c02c68034003403500803444001c52412030310f000070440402107442c1000071640d240d00540590000304ca1000817869104030030804078080100441d03201c0d1142146000305503d030400c64803014900384082e030009001208005801c10030384640d0350072901a202c855860340c905400999288002410394101070340b02c0c4e07900311072650100302e103241010005003098142e02e81015007040940040d40700f0007890005031401581d650301841084145561030120329003584510a0300c0c1c0b100f0411885150440c4529101d12030390303420380d202601d82c4c40d12030b1a0214402001c0400d5518016a01c80c00c0d0745d0300d821054440904903c0c00c0342c0500002d4550514041180301d010000f82440d010201340e154590900128002e824408070611a00d18803903500b4842582c2c54190460490003510100400030000340070034052140100302c02ea504c00140d40c1141d281296080119041c044503200d21170190f911240c09001e8503410039081 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 964473489 1250 964472239 964472251
    0x307080a0504031506050a0612020c0105072c060703200703060902090702030306011e0216030605010608091b0904020d0f0b09010e1204030b04030207050d031733060d060815 76
    0x6000c05c40c05d1500082000806101d0541408100d1090320441030054041c0c4103031244840007008546841c02c0050464083d99280d00c8030080c034603d80c1d10840c003034218036104d002005400c4a0070028569000e0360b0244dc1d0440424429180c10741c0c426154804000c048081e600c074000c041802041441030049000300600b0510554005004000700380e603003c3c0c280b01c85d004880d05520390a5440d0b1000742d041c0000c1741d61040340c601039014040280240c0e600018102c8020345d075084441c3c3c1e902100513848481e0301120902070f40c082c1030714091901d03000416a810500082608080515681e140900c06020040844002281c42e04021401c0001e2040d10702081060001c2d00560b068160a500c941c4a9404000c1130f520080000c142071510810540303014100103002c101c0d58028600303001d491a00380501c0742d00c1d1813101400003204602a1401082001d200440d140401443c11280d115410858003c0d43e0300180280189003260a45c0d008003001804111f01500016074502e6100c14090401004 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 964474739 1250 964473489 964473491
    0x31203290303090d14030c0610080c01020601030f0302070909150b0604060909021e0f0304060c0e09191b091d0618130c030b0609070c12110307080a05040315 69
    0x12a1549440220448000c2101160404003d00309403034240a51518200c000d01725100210b08110083e900050260281031070341102c00540d84d48071103e0f0b54503500c1410060058002400400c0055200341003c0900c034880d005503082251a61b082c042158010442a80d51054110200b807582c0c000f403042c1d02c40744900340c40b050b18150802002500078002d500c41c240e4910390005614008102000f07052104031550314440d942c81203121450b101a070400c0c0c2d0f090ba810740c905404003810500910481c0c0400801414008082d5100c0f02c40502402d000440e0040b21511250f220300e15242d154107050200c0340d00e84510a2032410440c04804800405018000040ca1581481150794410b0500d000b270003060548021642c0e10350110709400300a490340140850841c0d00c0200802812030000703485088142c6001c4540c2c0d0b40d4100c100c0700109440000703044c0301100d0080c820383e50712840c000d4850382c80c4001164a012a40c0d82c5180c113a600174500040000d40109060042080401680c8015001004 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 964475989 1250 964474739 964474811
    0x1005100e090f0601120809030304060c150b09060108070201230a0c02061b0a0c14030414010c030f080606040b040906091808040506030a0e0a0c030b06030115030209090106031203 78
    0xc5039035510f4060080605a2910180d5801045684421034001c08005815640c072039545110103000c10701e07007400c11120b036080940b000c0e0301454107100d0081d9444005100b190380e6111440192140c2c440540744108554903501580c0c05c203008200310400c1e003800001b11100c18548402480221201445404219040b080c1402408281c06040001141a0420380d41d07450140020640e035000f0300d048000c003d410314050b54141c04901001420484075084070b8102d00b9000c94004407041080c00c2c4009011954080721806914070480845602a0026040a146c59240c90000c1c83c1a00254419083e99484a03402e1082c05000e004000703580c04142840074030150183d980f414280a640070b0383d0300404002c00003883c0010399802078401e400380350065a0343c1c94058180800f1507040c501045c0c0308510b4800c00316030542014846c05011544141000303514a0a540c00c01c21000c0e070103000d21003150f403103610100124291040c2d041d01074981303850005040c1c0d071660b41035850200c0e05504020b40041e02d5 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 964477239 1250 964475989 964476013
    0x9060d08030a2d02120a092621040507080a0209070e01031d0c0f060f07031b0c150206010509100e040212101d01020702211005100e09 59
    0x4019660040c1801c2c20102d850441c140e0007500c502a40c068030a00c9600401e551007140030141d00804540b10300d00440541c0d80c1d511103481003900e00990b4014070f00100101c1e01c46240c03203402c3e04c084089240840c4030340303040702045c0300c070003061003004d01500d01003103000601003001010401c1c40e0007171042c4405044003289039000a11760100041801062112a8540c2400c983c0b0aa000042c0921002018441e507010b45411596420500744098020140f800b41e400f03103460300c2d10555100c01c04400c002480c2001e2590129090b000c43e010086407500d0782e149020009121081d10700c041c2c03074562469807606040b218001e180031030603401a80070f02200170038000036041d83d01d40041502e030100007c450503100ca20200710100341c2403169400d00c0c001d4520900d070b0f9800941207035082c4400c040c4403034510100b41c1d60190803841442002175018640d982901001e4080f9540c1c20b444411b18030945145e00c607007034426825180d048600d545241c50600e824001c21400a400c150000040d00050030882602 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 964478489 1250 964477239 964477253
    0x4142d0c0715060b0307121503020a1202030307290a05040309052e020105090d030e1009020109080a030504091406090c130911091c030804020607060b040e06040209060d 74
    0x1420301900c20000e001042c078040d00c0940000f401400e041c4501c6580f450007140061981d010040e82c07040c00d0b070608088050a200d41320034842900d070020005200c80313103047c140c51083c1c416a242240c05000c140200004a51100c01f25200021065034a5038803580c07194100a00f440010074600840703140030140030209502c620210140c03031069030342c41c46d0141403440b44001d462080304107482ca106000c854130391055040d04000e0092044004884003a000c451040d41518401d100a80069003c185144040c010b81c0d00a00030040c018101108215152004142052000001036001c214006402c0100c544a4450b00d40e007145814503940d040c0c00c0c03080008030803100c080c0c20750194010102c0c0d51500a00d40a0307007440100f0381c804080090645510525880760481c00360284a04c80c0b0071000460a42038a034024010395155854900c207542c4e5508010194004090030399019985003032070505511640f01702618047c441c0001e00c2d061819204101a01d80000c0503207004011092116000800d1 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 964479739 1250 964478489 964478497
    0xc0c060c0f040b0711130b01030606020c0916030207080708031906030f1112070303080906010501090b0f030c04030f06140a0204051804060f060b07140304050a03030e04142d0c 77
    0x141c0c0703da06135036488600703010124196a050041d4040510154070500c442c00d90300644e0600820307202440000d0782ea000513a11030240326940b07504940b000000034003c0e04400a80c04040d40207042c01401d01c0e1136521035007040d07004040e0481d25801d0002c140070b07892161f019202045409107d0034002142559500c0181d41c1c0d005d00d0003400e1111050180c0030964607215007083c8000340700129a072840d0340342401001c6110644d502070039030051000110b820f5100301a020141d41e01d01c0d150328901083c103a484031742035000501c030200d503060920001c00041c00401144800360f010300c0001c070b4010300400010382e00382c80180101840c1e07807042004020580b100e140d4030094641c140c420708031940d62410900081c04441c80202c1000b8508900407444804880c0581071644c02104a401941d46c030300700ca25500e1050b0302550794404030034202040083c1c8039881c071704e101c0c0d94042c01c04145046020090807035001d094422170b140c04401c04020725986185840c0b1101c0304d86449107d20142004100b10880d840b03 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 964480989 1250 964479739 964479749
    0xb0405160b09010c030804032a0b060607030807320318070f120201050d0212010e0a140c2b0e0c0303030f0a050414060910061409070503100b030c0c060c0f04 69
    0x84210010b1f0500d40240002e07802a4043c20b940828601d0800d460219629407101c00c42d003404801d00450740342d050403020b440702c403a4036450b1013000392540705055401c40f005041c010320f8400100382c2041c6000303180d5054041045480d030707625200e061002240440229401e8085100d034001103041040c2e000c884683c1c0d088645404408541c10504c0c001202c1700d2141d203040703a0310540001190741c1d010400c2402e4a04960307407200e000311103858200502c010341d69011400d00c1d14112400c04510343d80105401010720629400c9020801c040c0001c0004001c2c0c081d004100c64240e880b1200c070080c2405001e40d013030510b02180a50310b10302d045554504048806403004500d142e8a0b40010104905501c814104181100480c1ca40b0310700000110b96491514501c070040078100304002900c89800135140000c0318000f09428040d50320074200310303030542008181d10103107003515600280000081006501820946050540d54000000b5491510380c01502b0040456001c2100701404410030095a041d11 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 964482239 1250 964480989 964480997
    0xf0c0e102106030b0f011a090f010c05161530060e0f01061823030c15030618070c1203060f0e1e0714160b0405160b09010c03 55
    0x2540d840344000c02003298507200c00e070140c6031207004000d1214411102d482441c0c254846001c0760b8031003241c010106c100c00c0310001264802e0004081a00d03003500c80032032505040c5400180f0b0041034031518500094a00d02485210031000103001d00094a61146000344103030900d0103042e00100524106108078250150514044100d040c0050030907030001c40043c502e44200d015141801c41d650103201c0400e124200c041081920080084002c0c800058112581e01075a078062240c0064988540780c00b02c07030382683c0760007841400e595554454103407505408014908503244c0c076040c418411420500700307072604000d402c1400c00c504103500000000e2040c0c6d2000650140c0030041e54290058402ca03049844000c00068000c965003c1c0241c90600c21548800311086c02d5040940802022030150b400d0b01c0000c01c280080f24821803044002c041200105030802841c01064541d030900101c203881c00c803a2a00f02c0c5a40810a40e200c0401002400f2540720081c0740064004c0007820054483d03000070144 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 964483489 1250 964482239 964482257
    0x8060102010e2a100503010f060306060518150c07080f0604051e011104090b1e010516080903070306022218051f0f1502031c09051e010f0c0e10 63
    0x9409000e00f02c000080581840850190054003a01e2500240108c3c0b031070180e5210001241c520070f024080480b14941c413210f00c2c2980d011440101001410402604021884000c01c4040300300c2c402004010081c5005d03101c91401c0100c440c1c1040240c600580c620760010051001107a00802c1201c8008012440d1080101d03201104a0140c45140d0301001007440200c0c0c00501e812503034121140341032007118841105a100215045411984074001340020340030310521100c1d0700300c0c00e09903000300c1c014403206007040c6c82400060715020464104458180c4c0200385a04007450118480581c0070803c05001503050030700f84540040300158542030b400340c0c0c0701c0c00880c045080c201c3c0307140702123808400d4542e5001d803150200c0c09001030a2281c2c03020104d440b40c1030620b1620100c00d070780d4545001060048894001441400500241070301036036a40144050081c2c010a002140c4180c030503260b0020231403002d040d46443c2140c0e01c0084910500500008112403176994064000c07c805881c00c1804c08 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 964484739 1250 964483489 964483543
    0x2030115180b03180601080a1505070e040f020c0709060626070302090d05190b0a0c0e0f031f0b0a050f0f040917070501021e0c0307150b0a1508060102010e 68
    0x881901d500e40d0485c0643e00001c105540040340f0503503c00d0054a41c0040115103034200750846400b2155100040c1030300105440520b0603401400d04242e03142005410403410040c168101740e1715510001616560b92001c201d42130b006001d40d040c1a0400304030340b07051046102442c0030540b00401c80c070704043d4000b407504051744d034216000d405580c1120031144031b00c2c507140917103159140030803040d200c0ea144d0400080340700a05008400c5020810303600c1110762806030003444004501c0c0d221003541030042c903400020600d01042c8025542e24240000b040e06010708090100707901081c0c020710301954010404a030a92503910503601641029140000e0311242403c0c844c241c10051105a420000d0000749081031100c150060000403a02c9000344c4401220340d040024039204040d0024031541052040c0008280c000d4450a010000140042115824540000c5800d10b05070815107880307000300c450019855004000b180e00400a0008000528541080030390750343c42c0465030900301c4004800d03212 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 964485989 1250 964484739 964484761
    0x80303010b03131a0702010e011506080903040b0f07031106061e03100c020a021e0d02010f090b0f0c0118170715110a140a05071e1502030115180b03 65
    0x141c41e000180455a0429040d10139101d08068410100660030a00703a00c2c80400d046c4a1030b5000d910b80c068200307801c1e103072076400c2d200750000030546401d60006000010f00c0c21345107170091000400020200f41c0d5440c15180c007a1116050b04480c00c910380c022001c20806444400c440711082010100800302040d104001a1504070300c492070141c803600704500300c90059000201c0007182842144c6d0100e24000c0e0400c0e0b2064501c03941d44046e0300101010808002d9406168032950486a0b4605200d01ca921956009000e910000300070790460000960f21160000a2043c4542116044101220b420040d1a10200003d07038203102c10811100003851010031002c0c0105160040750b40301c0c1446070051502e02c207907468000c03003501004941c46480e00c2c0c0318074280c20126000d4806030b454842c1464115104c0000759000405174282c94400d402008022507240500d480701c01e44100c0c4090303a65230504803582a8140c0c0a0b1030001441a1280342c00c4603c0c0c41d04031b048059801034002c290b166551408602 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 964487239 1250 964485989 964486021
    0x4060c08160309091d0c01030509070906060f031d120d021606050a050903030108120d1e15050a0f090213180911010f0804060b12011e0e07080303010b03 67
    0x4031115031070520480806401924120443c2c00340c01e01048460005d15440010300d400402401494220f5031103442c456000f90300464000c4081c904403000c080d20f40f51f0784c50880d800758101e04080342c01d070320501c425143c6c18020319114410003045e81401c9041d101c00c1da0742c0c031113050b81f01e0030203c600481c0c14142c2051650545020701070402503103915a081d41020300051000392249204c143c14040050f029000000490f4101d0b05032600508074079503100d160140741d411103034081880719224583e030282c140d0301d2000210084200d1200061040051104829060155000c14002d040804080000441d602d050000f12440881c0160f50364030764041d42c0681082030b8010408a480118404440100a902c41400144100f400783c001e9521132006540486000700c000001900e0b650000c0c0000f031a6130000c10030366401130000050102410461400d64050980400b00303050481e0605030207d18038081c40941814403c0078009190500130445d45a105c14080c6010060002000c0790703121140b09550 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 964488489 1250 964487239 964487257
    0x30e0d030311040f150509060406111218010e030601060c0b040501020c0307050304030b100e010519030b07050c3a090911040302040b0909030a0c02010e060a030c1101020406020304060c08 82
    0x207503541d030b9110144046901424040c4007120000e034044013812900500807108654402000300781000c2c40c203001107400945120005149014040b1940115242e203405040c037100e0460646c203480510700300042030a240c54032a00e209600c1900100076294012000701d5035240c00900240080d9101c0c1004e40c0a8802d032005030704e80b8030000420b5020301c280807001c1c0040ea4419000d070802034407004044104030400340a24a0300e2110342c0d00402213071401150a404030342e040e4001c0303030702c4550b00e803140034060300c0403185500490000100004411000c2c0105008105c030341e1950503883c410105a40d00070300c4064074400e01010007041100205010300207201c002c202d04c180c2400301d4045811488569002440100d000300c0c2040c2c181009440d103001054800c1c1c204c81c00560404171a15001ca4810181207003da0501040ea8040b030307030944662005010000c9070351000f1644050441c402014070303040440d031007510b92040c00f05203c0c0320385c00b0084500f20303101850290b06e6910b0504000110b84211075030 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 964489739 1250 964488489 964488521
    0x6040b0a0902241207050c06070507050a0f0c2603071103070f06180603090f02090717010909230c040c110604050d030e15160903120e0f010309030e0d0303 68
    0x442c0701051500c1c802404880003281c0da510403605c8030b80003680c041c01014542c0348280c0081c400510700c180300b90f0140120500450480d0f031741d5001d544070b800341c680400205a82e40d0302d20310000e0001c00000d030800c070003105091140f100000c0e00d16801a440b4041c40c1401461514009c03002810350307500b000000f0140054480000000b03642d0040a07212969190700d0513942051002d0008609000b481041036058210380030a040c001c0541c00c22083c64001458071042c0700032a00d1045d0101041a540c50103080e0900c000554030405003487d000030041107914004000d030503039040902000c04242a048448144c40c00702d942e950104086e540004188a41e03102d82c801c0c0302c10030060110005007801d102c0c286071400c0148030b07130340b03c0404e454000d808255020141084081200c5400d60f502c4100d50340c80d20b14120482a449079200b001840810444c0340c0018031000000400d840c2030340502c141035000b42000c0206064590780a0940141000100c0c42100038554410038103009030801e03007031450f030600 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 964490989 1250 964489739 964489789
    0x90109080301060c23030d110f0403050a060b060f040902090409060903030207060b0a0510120b0607052505150705010e010203070c030908030f040512030405270906040b0a0902 77
    0x2c40101300c80c60940080e00d0b01c584000c0e00340002404003280141000d007060286181c050f4100c00e15003d0a42107101071914241048403c01580b503030360142c00030314821806443c400c1611f09080058500c008440c40c401da20400a0306041800c0504407000c4907103191025850340c0c801c0001a000303084010000d003030340b401e0210700001c2582c9503006284181c4035040820081407a0700c14460135131424043c00d60840380d00c21080d100350b030280c0e091250382c0309103810204446031580f01140300b5801440c4103c1d456030285000d511001c12103005244502c0c4800c8141d40035611389000102d402c000388850f0f84d40501c000400c3c00c1170010a40100341b0318491040259920704015030300414150041c9010b500103441080081845c110100880c4d1006481e00340190409090400700800109141030020482c84104800515070315078030ba860004417030740c03803c1c07500640e42110080800e20001301007082c180c201c9010400010685c540540c0c100c00e44403000185c14295102245100e801280171400c0400011 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 964492239 1250 964490989 964490999
    0x1704120501150605090f0d140a2a09111e030601020d0516140f0601090203060a08010903020d12061a19050a0c020d0f08030f060307060207050d060203090109080301 72
    0x422842001841100208074014034074145690380390300d078020200000c4c8104500b00c400c2c07038105400940407000030143d0070b4895003981d0354030500c042e00f450b10915821544c00c040a008010501c40b407480c078044580029080c28169040c0e141e01c0074014900441d03543c0c6030a8115103091020313101d081098400482d84c8551340d20000c4103540007269010700502c00c84e284080003511900c10303500d01a01100c0250103600b600e617521a804018401024924420317510309000204003001440c2c003c2c103e401c00160f59050000600c12024070640144003039a051005080019a000820f040d81581c0c51410401018104402001628441d44503001c81c0140e140c0c61410f003081040100f080311a0000c150604002c00c100980b61030281401030b0380845c149101d010050305108801504061285203451a4004950340302801ca410a540e003c00141e411400c201c0ca90400700720101c0540000d0008051543c6400700148000001d201e0061645401201285602c00250091081641e200e083c0a489603112 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 964493489 1250 964492239 964492259
    0x3210909020a0917031e073e180f101a04090513170a0c061a010809160b1b010504081c020a050a031e1d070e010e06010c1704 55
    0x64016403004c0000030031504290a0004102c648482081603a803118040f40015880b0a401000080c5d0303524990a009030701400c030035004030843c000b800500e80380c0c0f000036078545054058000c60a500400019000713011412055843d5030388090b003022640405d50701c6003041d00e00059203a001c0c090359466081000094207003e009841540c406080c01c0213155110403104041d424060340140901d041c0403034003000c0581c814000c20703100b1403c0c00c01003480c80607030340c1d2242203c280c0c4403840c078108100d0403125140d45e445078070386400c01102c03c02400300c00003104074165500c980b4820002a01c1c8000354054036500600042c0714401c0080d0000c101c10300d007d0400e1812070384099011003c48180c80119000d980803403003a1014208107a8a43d0f05080150405030b0041540348070900000251a45240c07449245001707050b5110400310690355000c858108403407424005801210707810402c880148080c100005405a000000340390020b07002805040009980c8004d1074000e1300420700081c04070303035a194 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 964494739 1250 964493489 964493507
    0xf0d0504060206090309060f0307020a0f2102010e100c02151005031207050a12050d0c0e01030b0405130f030908012c0a020d0305030903130905041b03210909020a 71
    0x41e001d558141e84d0341406240c0344e20a03140300642c070420510002801080c4c92016551041e80d07130045030440202925031811150050108441ea42605074803403851a2030306210780d01601e91030000b0320400b0b001c881002e8641c8882c0300f100514560b904e80d1039504500c01c1040c41c0200249400204031030400fa440d51925100d43c5c0100c2c0e00903c1a15490000c07090018200e42d6240c0c3c000c0090150b207601e9684005501c2c1360390030a44208941030214000c454658802c811752038510352950b80c0c900784054001b6040d00c4003060210311440c50041001541803214002c250a580e015181a81c01c0c1e0031403a050b03442c00d040380c010700140c4d0310b0240205144400c0f01400c00260115030240223400201a04841da10030b00c0a8000f900302c6107442002e0002030140020755000b80c1128150380c200010b52401c1a01c00095512142c0b0782c0e07840d28148030901a83c1d040c040740300402001e02203d09130960f1a01c0800a03200101c0da40c2d000440d46692103098862000ea002400703c6482c150f5980481e02002044129 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 964495989 1250 964494739 964494749
    0x91415070c09200403030f09080f10060603140103020d03050f1b0c0d05150712110304290c03060105210402040e0d0f05090f03010513060c0201060e04140f0d0504 71
    0x114100014004040c07150842c118100303d55892450b050a40e50304903606201440c514041c001200e90100384039105001140c038480440d00100401d85402521805031942580a40141403812034005d9407860741d9040141500e405407107206031b210300d9181c112800d00c42c6000c0b081c00c010340030900c0007a4142c103d40b074a4080e0300841c00c41d15207491010420000e01402e1800501c903600c4010314051810a45824580c0608107090146051144100c6901039603250501341604560000c03c100400000070200707150120008008034094603c00d0003000c500101800e0300d91b030080c010001903a82c1e84241e00f1113402030b290311051144540302c0c8130000e0859400359400c070320803401c0c0a5045a443c400150228144209643d0900c10100e40704040d241e40e0300007110702d500300c100810301e14040d840034041c440c000c120544050244044500b04142240d01b41400c0f42c0441e41085e40400c082d000c421800c50300b01c2d8228445082d90b0190211507460710040c06005112406000800c12049410401400441d0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 964497239 1250 964495989 964495991
    0x3030e2415060307051204020109030c09021317151306061d1323070e070507021c02090a0b18090d0905010201050c04030b0c0c0f011505040903091415070c09 69
    0x12501c0400519010403100600054401c1c4084140c42140440c001d410900604203080d5a580301d0700c500c54050017a8001c2084180c0009914010134803880e0200001c01145002d1061440030210441c1c588900aaa440384104c4400200341c04102941460201c190706c01410014155184c0c180c02c0c9002c900700104010b60340000008280704000c4480740d25180c0d0112200c04101d401c208503010103410140fa01c0d0540c81040400705034240c15116640c01446144c80309a00c0b900b1038410007048550b6071941d80c1c806038038a4080401a2030381e440e402d40204813400e020500141c0700c00810389208540801d003035518a400c0502c01c0801021440607015606552503035034040d110001a4260b400603565a8910142000100003103684401c1c165000161110f09600c2d000400e0f20151401c1005100f1030781c580d651b9500c0d100f05c1003c203000040101070640707051200d4a050b0701c0280034806a44a8100201c55071014191280d42d910243c40040340442d083c551102914201102c03000390900030400d0403 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 964498489 1250 964497239 964497271
    0xb0c071d070f030e2d0f0f06011a030105090a2403020f0406050303030f0406090f050c0315161808010f050a050702012a020c09130303060f1203030e24 66
    0x810f109026540040c01008010042a9220280c661700824182480d5040102d0000790745004402130242d00a018426001450710100800015040007410b81c0000522000802040445c10641c0103490445404481514030f42d42c5007030307500d800b5050380c40044901c3c41810304c07211300e0740d107214044400f0b81e4029501180d41030080030502044800c40c0c0100b96040d0300c00d00001c2c004440300882203034031504c188008155881c0329550201e643c0300e100804c03640c0b03401c0700f801703008a81400c100c8030003454424035150b911814420310280c9502000205c840c20048800741c00d4070742c1c441e10300401d4018203051000700000d06411010b0401004161201c102480c14900440c01d194814080c101035040c003082c1c4040900c6035a40c0c0e0740d02c00502050301da015402101d03002159a90f841030307980d00c65030b0390403070a10700a06c6500c0c0080407200c041c0c110800005407a0000c0c41700c201c5900d6484a1036070703d4140002c13804001040d240c50980c925421902006032440507042c104090310360f460040007034000c0c82d000f03 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 964499739 1250 964498489 964498517
    0x51e0406051005011404030f02040b09070807030f05070e0f01020a080309010f0b0301141f0503060f1e090c01030f0e0d0906020615150906091302130605030108070b0c071d07 76
    0x402c17001d43d0301c0201500038041030021031081e40160035031501c01880000d9842c1043d010880e29541243d10401090141c0c040040c040d405004651a60b80d40040c200551325202c800a04003c1540c0d0074503000d100309450134050359000f00f000106203608600b0581e00da01d0001c0031a0f000c0c014035814220454141116a455807c0c1405044031445017060207a17415660342d1404a203c40420360100702c0780c008090000f900762010702c01d0f40c5c01203444502850300c5141c9110161070351041518151044c00d050307010004031580c0403541450603202440e001c02d51480d2301c41d0043c050072074840c0c150a80d010720858200b4594100003200f040725200c0d02520035a40c2d41044800034001c000c083c00c3d0700203031084052134200f4158001410f100800820440c00c2915207401b05107103403481200b03284c1596000511031200070502940000a240030314200b0300c1d541c10114000d86400040c85007268200b00840e40b101c9203130051140c84003400302c144043c0e09424031a4151a14401d0540ba0600070a500540e2500 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 964500989 1250 964499739 964499747
    0x1e16020706020a1110140301030f03081f05120a1a06012307080f22140312090d0f020d030201140601031a01270b040e01060f12051e040605100501 64
    0x100c07581003d4070308070104c40c48090204072003142036080204003015034200d48a13980391010b140070f14029961030751000786034a409442c00c800908040420b0021010ba0f40b0200105080324090b21816075000b880142a000780314a8660425402459031491110401c01103803c141007c1c80342d0801d0740c411514001010005100000241d6040f402140800118003c148060010846100310034141d624086c04413003621006180c06055005016100d82c04000000c0750541240c013601c0100d015152954040000c19441e00c0307104640d40c0600ca0301c204010a10403507030025011550050264070140d11240b40c000d000340700c18040d503e030680d00f14000c505154401d03c11001c0102c5030604c000100883e01c030042d03546207031004850040182180100d400c00000c940c1c085c0041145103106910b4500f09a00c40b40d003110305800c1441001541c04414107016886a21030030120a10070300002c240e200c1035070b0b806074a80c00310400c0d07584070305031401d100810900390f001c0d502c2034101d5000480c1003a01d07100111 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 964502239 1250 964500989 964501003
    0xd0f0204030b01121505070527061b07050301090311100b09040206071704181a0603240d0b04031d06181207090204030c1208121e1602070602 62
    0x1500c14420390780113100c01d043c1c02034049002ca0041c0000a404040c80e00c4000540d20112207000010300d010440b204407203642d01149280c00c441d12005261404903c0209444c0e006070207800c00d001c5100b540348081e001301808108050329001d0001e0015030864140a01b40354040315543c003582c41014140c072100b080030300c074800011a00902c011995100c0d5006c020f001e802c560000c0d039072609403000c80c81e1105490342c02040202040c51141000c04c48000c03e0704210b5901c034400d0400b071a8803104020079640c072a0304583c0d01c00d8266102c40034903520701ca000f42c281e244900130a0341142c000b00c0300005201c20541c46c0e40c440c521a555160800c002e01d03161712101c0d034080d00706581000007404286503040c1034800c200107058001e00ba184003041e100c010fa500d8200a41e1091100c1c07a80060180184031802c1d4030300340503080000300e6942078003031991401c14510035068400000e510400c0803921000002608200d10418903c0102e10350410140d102044403480d8010800f40c0b040840003c0d4050000c5042 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 964503489 1250 964502239 964502243
    0x4030c080115080601050904020442061103030c1c020703050d060803190e010c0b040605090c090712150519090b011403180f06040c0504060603021204021e04110d0f020403 75
    0x30301e800d238845600348400b501e042c2c038000703011086590903411090b204201500960280343ca402440081c8581c8940c2e2a5036241c1085080140400030304541000000c100c03a00001c01d0511541e0750100228200c44d9410468a9801b03110300001c1c01d0400d155218015200b00710b5110401c0040701d6903201c40c15501c1c81001189103a6004200d0708625041c01601c40582c0228103050500c10141ca55884c0c041004045a00302d903500c1c1e8500610034100750822402a1050782541c00043c0c2e428659000340c1058410b001c091a000c2c0c88100320324043c5098000180102005031074160312080c0409001e00940c0c0301d006981405260403044003007036103e0041300b400d84214502091031078030f0b00fa540d40c2e412070542481d00c005124042031580c5005c0308104451040f801070780030209450501d810401500d046032301034030806005000ca8005c00c20032030310640c2c003c0e41c101c5404004449116103c4502662803408a0b0f03c980b03010b140802011140e07000309900ba105080810509031040303d0300040740902e001c0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 964504739 1250 964503489 964503499
    0x703020d030b041b030e0f0601030221100612110a05060f03090a17070b01060206040b0a0e0c03010c0c020f0619050304060b060d240e1b04030c08011508060105 70
    0x81401400782d0b100315601480640040b94448080c0100d2030102a204040800a552001c80c84040304c002d0000c12010207602014040c5549590006004004000c1d114a0085c14543c04001182010003070780c1c01c840101e9a080c40110340e20902803030a401d52000070b568000680c1089089840c200c9845015920004c1940c1d092551245101410790001400c50007107200c0c070000c0e90003117081031036041c8040710390003c070650b101d000f0716241003901c0703044c0d00c00400d562010f410300000074401d10408d58400c0003980c000034000000002589805286542d1603059442d050b9505425540001d8080c00c09000f6030369140040b4034001800320607c1541900941c0108281d08560340911030340055800c03a000300008905081420000340565008044910400783d86130400101e409500c900544001040c07505070019600d04076104070080b00017045d941c14050f21042c0d49003046508016980550b81280491411549421503940207103050880b606a0071800100010b15000000307140c0c2c1640c1010b44 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 964505989 1250 964504739 964504753
    0x51203070818061605090406141c030806060a022b02070e19090203151927112809061a070602090f030d031e09022229011202070302 58
    0x3010304d02800c140b03414070b03007001410400c0f5921542c80d402000c000c0c00c0c20b50206c0301048003000c20400045002e843e0a9600c0c8940c0c24030801203a00003030601c1e440310b0141d503495502e22000c04101c1c10701114544c1d151403051000c51905071164038090401040486030200c03040b85841c0d004403070801c03400711103d42c01d000503407075140c500240325003041091600c05011148103402e805800c0c00c604030101c40001e01041c1500e998481410103006d0303440a5081e8807500c0c074503461820000b40081042e013a02418400310b0000d100714985a10340003407403c215101c044c860300e00513211144a048a02c1c810303042d047d800d004000c00c030202c09030560b0004c0b030409054a8500344c1d180c1d640d18080c2d08806000c60303010414406a01e00340d10305002695411815680002d240b0200c1c002c07121202c65452a62a005494142c00100607220640000c1c1807103203000040c0403a1800c2130b01d10700a0250180628960105555142d00282c070310b0300d01c40c02811090301e40420f022400f090050032270042100181c01684100 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 964507239 1250 964505989 964506001
    0x803030402060f04170312010f1409090c060c1c0f080f06130f0509011410180b06040314070806071205100b0f0702040b060310170a05120307081806 65
    0x180102003003150040c2ca01c2c103255a9003a00c6070003d503217010443c1c040c0c00000e80030003d0040c0e2041103006d4400c141000d501c180c00e0411540303055094043e118000da001d80082000305c442004818002c3e20028100b540c0e4403481171401f5210070600003414206105641d03c800b00720300828001a40b20a659502034080e0b0741c0c1e0350b1604e0b1949000e0101070300300e000311841c424924418029007182034902200814175042c130141031800c442078861025907000c00c407010700441314076a800d10b404503402d810300d10041d065003200c1100100010340441e58170541c002000410840c5400251030f40804400c00e03103100030703a26014a40c07100000c5460000140e82d0384200400c103100381e840950171000d00d030108000b0a4441c15082d400d5070043d64181c40700c0764046490811440d0a00682081903070550728a0b0031030a14a1103810210400d010306e07a00061144601c1c641d00c10100f00b0348000c3d41d0003130210703103407a0f480c4c1d600b00c40d15510035a000c8000903680400202103c00a209e542c4503a00c40400400440d40c0782 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 964508489 1250 964507239 964507249
    0x7030e011209080a08010e07110d0c0614250807300e2a0a12032304060e121b0105070c09050a0b030f06060402030a09080706090210090803030402 64
    0x110070700c82a9242d441d180030864801c0074019080290301e0320400c550503c0984801e11900a200380e007085184503028000080c0495010042c120a091001e03403c015882d02d1b20141c0184110843e070b942c00c0108004001c011300d41200c1d88000250501200c2c03c01c0408112940e20003100c1c40ca01141c886001e040d489807411002004050724032008140070383c400401e840549001c190406000e9214485046c1c0d503000030221201e500320001021400c0313201550219103612101c1c0b081161701903601e2000b109050052031032307210066012264000350381845044c3c2002e03030400e014581c00102c0c01c0c1292002420040107e40009102000500c44040300800084a40112254060400405001807800145440c1102d0040c2c105540c000c582854050b501004403401c2076102c500c0703a4415044051181c0340411303c5500300700c0541c0c01582e80c0c1d40d0348081c00090a840c1070010858800003d00c10309200c000e030700080303c05108950302102189403500441c0e13039075018010348049403c00c1001c40c00500e01 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 964509739 1250 964508489 964508507
    0xb0f010c2a030f11010306050117160c0503070807060b15090d0219080708101103012c0a050712050603030909060f040501080708250605070201020721021507030e01 72
    0x740052540c0040d03269075400002090600b400c80e00804038504a164a40c0c06000e0076010709030a00e0205800d54914090010026003d8440d9402c4807586480040251190143c00c1259420004490b910041c51825094540c44900c040e51094903008440049207018480c103124010078102182c2008504c600700418003c0b480380c101ea000900c40c04280202441c0b0301c1e000b0050055002800c0c41c03601c0d2070700c0581009808803002090601d81008002600c1002d4181e905580080c6401c0a803001a1884005111444902c2c0c40060084800300320405070780e50030440c4140c12a41d41c01909405402e0503005481059075280d07856002130240000e01c0c20700c5040e03564014801032605007035030200c001140880704280c11a064030f8000450900031004c0030480001100014101c0d0040000c0c0b440c42c41c04800640d019450800600140302000d5a101300038050140c40302425800b803400c11165042401800481700300d001d000c4025451084c0c1102c85c00303540c0000e4141d01d4010781051000c00445601d40 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 964510989 1250 964509739 964509803
    0x30903060b030106090e0705044d0316020d020705010f030c03020403020414240d030c020d1a060a06030b0303031f03050a080901110a03090e22060b0f010c 68
    0x260344c20703000034148903a0044400c514600c0c4041d0000c2424603007880282c4100485260315104410f00030b0442c41050341d00e83c117101060243e0365580e25013600011280040a02e90303020088804801c0c040039489548024441c0002074007120004940c1803c1603071202d42c107100305c50114841002903204180680c0041045042c0c1d4600140b600e5125070000d03040f00d000c042d036003404003590400c21a05002e06031000049140d01c0c3d0706990f2151141000600300c1010803c010108418262000115104e0300c005014081d40400e009014032040c0e00d14401101c400c1750b03820300c90550201d0018016020748034024000d04007130b014514503030368400501030162140310940005455650300202241050020307901d6503226540440e62014501d0004004140d10101c494190300011664000203802810303070422922040701d02e840c5940c51030400e0800b00b0307285030124503640781000e001c002c10103940d000024140c000c64014101c4030007036004580d40c41c850400145411070704081d481c0100004450140f60034 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 964512239 1250 964510989 964510991
    0x1d0106110109050f0c0301060506070506060f0d05060a15291e040e0601080f090a02041e06060504051306180e01061206050f01080607020c091f0609031509030903060b0301 75
    0x400c00707030380f11407a10301e141c0408030294008a0344a0071030f1030207000308001800308869440c2041c525071108c5803030b480041d1416104000003801d080043d00c4812035140c8050700314058890a19252200d0340c0589103440002000300001400821100b82d50403d6561052481103092928245a403415059510140000d640c958040240010802a960052018108420303081005052a000142405802034210103844224508010108000041c010540390b01100d01040803101000301c148180c0041440300c0000b82008404107529420000400c100c0b41d06440c602d40303925100c81740d00119180c9002c0c4100c8001409014800304505410864041d4800c000000d603080e0f070b1300c0914007080307400381c2c04a43c10340d01d5500f04105a8042030b1040e00400140000e48824548601c0c02502c80000d2001107204024210205044c404503407119141c40002600320030740d42c0d440b101d01800703081161000b00c0d0b220a08011840811000e400307004280d81d4591070b98020340341166a031001a04002c020f6507019 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 964513489 1250 964512239 964512251
    0x31e04030204090c06091d060415090216050f01090b1303090f090606120c050d0906020705060a0510080c1f110d11010e031305060a0507050d17011d01061101 69
    0x503a40b41c2c400c0c498050311030152840224901070010b04600f449520032501030581c40791303003c0780b41e00c0400d6043c0c2c0100c0444001400404c929213950101c0caa6401c0807501034030128000e900b161400480401480c0120f003150184038041075614207070b131803a0b58010704d44003110000c9100b012003013012008103442070424241c480d0300d51001030b4641c0d8446c0d100064494480d20b080040030b4200d545010300b0311281c1000d01c020709e4894806402c0b4800d01d03800180e041d0b500c000c1c800901079282c2c15192020341c004107603401802d000b25031401411068035a200030b60510400002e500c100058075107076414002d8405456400780d000b04501d440a015004018010021040c0381e44110912854400303c0c2d054444001e2000d0984a0500f11128003500310300a40c802c10081005090180c040d40448200301c1d14190f41d085043c2c03081310280280d410051082c0320381905043c2164001c0c88603800b191807210961840d80e032344d074213000003038680b030000b11217140c2c804d4014448144075211550341c040c0590001309403 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 964514739 1250 964513489 964513493
    0x30f08071203060e1e060105090d02060f0306120d02280605090a03020d03180f06020f120402040b0a05010c060c02240a0f060305121602040203011503050901050702031e0403 76
    0x107140420407a40003955610041c07048560040c000c03600103045801110041d0803000010b0300712400903000606002d80403d1091082c1c0e0b07241d80741422640d0190109440d0800099442c03410b40043c9c80c01e0b44541403058840102c16000920000c0080113a401460b11551451451a2403110401c04114000b8501101c0d03001c15480d0050500800c60980203003000d140300d05009050104207502d00080604060846000300c203140c4001e4401e580152518a60401d940340c284001e10904041d0b01002c0801304500da80c200410000382e1140b4002d072002d1003046114010045000340a00409010400f80d03010b001c0860920f5005120070350300f0303004940c582102045040d050840048144082500503c104180c07410700303004c0d1684844000009200c090708603a90140c1350f06c8100b000802001c1c0c040b4409804c441030a600d80b4010703401800440d52540c5840008444500380341001c1c01080c2000003041081c403051040e45d01c01d100d540e000c0c2d03042c140241310701080055001030811860f8024080440 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 964515989 1250 964514739 964514753
    0x140a0311070f110f01020d140c1c0801080d0203031b09030f1207150504030c02060f0f0f07020f0922050f030d090b13170901050d0e010e160f030f0807 66
    0x41d050181c1800181c41c2801c3c4100712500c0c00b004c0410b0b046402c5040e0302403103150019a0314600201045d0103644440b924160070b841d12101400c510b412800110740c5510960300180c00318140d0f5080c0d01601d643c10060401039039030384401d682e40e07c880c40c02202840441185500900816070005050715840320303005610354a400f050303800074940340c3d00000b00d00f41007054451048400801c240000d1040e40b0349500c01414035400080003900954000680b2014449002c2c200c590540046580070b0f200c460702a07240185400c5214224010310801d11000694074080350194810504028495500c814103040c1c0407400000200071211481280380c940d0b012601031028103c1041c401c840082c0910309030a100c002848040e24140b0307440401c8002c140415012052206a0312010050903555401c040040b62244511a2488121031a00130314075103980c019040040e0039025041124440b1010035045004094030f0f104480c072449503000300b080000c4810842ea900280502e40007030400d484e94036015 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 964517239 1250 964515989 964516013
    0x30813150e0102090a08010b0303030a0209060705060916060827070509132105030f04030c0b09150a06060e0f19080105010e070305060d03030e2a0907140a031107 71
    0x90b03500070844591609040c50114000d00d512802404440e400c54042a00c900c40507000b0500d080d000034081078603489038421251a290701008542507072500380300b02c5855442c814441c3c2800034000f840001c1040c03181c49480d000704540c202100c44900d104c151030780c0e04c90007407441072180c1c0164040000e4a80d209601c5a1060f20109480c1c0922005498008200241e8803100950305072408141180715a0101c2074035401900850304049540b200d00f810341b042e294080340141640c60440401500c040c021a8500908441c85980c100720307180d181140d03040e1140d0303005180001d403034626001058608201d00001440024200c1c400d1030090b601c0c080001c200c41d8000041507911500100414003840c828a0b5000a851804000398101600040c842e0740c1070310005801c15440300c83d150101207051000c8030b40340281003d50b002d5a091003625100ba6882c1031a212301c50600c01000942180c01035030703914161710000d101c017441c000414506800070640b00a107010039100c14410b440000361411211 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 964518489 1250 964517239 964517261
    0xe0f0a0c050901080a030503151003020711010807021908040909050f070f0605071103010e010f0c090509090715180906031e0c090209120a030e0310050403081315 71
    0x600201002800c14588000c501ea00c03a5020b9100c042c0104808800461000c0c512949860000d5881d200c2d0480715078035042c0c03a4502c9a1000b01000140421901503005200b560f1080001d540b01038100c40040da000c040032185400542c10201c0440d0081030241e13240045a4800c200b9035040a481e15084402c0758129081180c0b983d20840c04401182030030002d8400801120000c006c04508040c0014011f010b0030780001c00400300d11010301c2e81a6400c0d0004030301c10605134001c01004d1400e0405030f020701080e54680c00803683c840d0021400d8180304114521074496480101407a0349032520f4421101e64559091041085409041c032045584c003290714000d004a440c003041203402c0d0b0916201807400e00100c0740200c3d00da14800c8000075000c102042c2101c0000710300684856292002c1042c12043c48020742044c0200c2e0040d60400d9081a05090031101c1074045401e41c00b2244440d201f180c4081d20b005e070205410200180c00314900d40403414100b445840244912400c400c0c0c4081a60301a081e4 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 964519739 1250 964518489 964518493
    0x1a01111c050c0f0102040b091002010905060c0405100e101107120b0403080703020307020714030115030c080d0815040c1431050108041502090a0303020304080115150f030e0f 76
    0xe403100c14641004140c4550f86004001c501e07261400700450312600c03030044940e029400e41950030349014003c0d4171201da43e60304a0191030007440c0a50400203268002d00415101b2201fa070740c1c0a00e0b1621521400460300c0740a050005448414501610b5801d4040b00d41e1220707110f02000850440a0120324036084ca22812241d50141414078018009220052008081500c140700700701265600142800486041401300070b5810150800709000d0269070f881305420b4440d80d00000208602a0492000c4880403c2901d100f00310030001200c004030706070342c0500000c0d280742030214685090743c03124003038041030704161901c408650000c48507504181030350522503040018080440d941c0c0710034005445028415239083d64140710001c1c0003c1c0c000f1300007034a082c800c00e207005041c0325158122000301c100248158442580c9180c0203640741d1141c082d9101035428940e0f0030520303910442c1e0010540e0502506107000c0380300c1c48011124541c617110504201901c5482c1010216010720222070103401c5500 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 964520989 1250 964519739 964519747
    0x3030a0f0801090902010806091f0308190e13052503051503060c040b0d020d090c080d030b06030c09030c0603010914090a1121150403121a01111c05 65
    0xd04104016031041a00500b400c810130010703a4020700090f44604100c0302e03140c46440708050709081c08031000064800504091000c01030100000c050305031400c941d02900f00780c1d595005c00300d410451081c0782c03c0d003004510f010280c541711750347c100d44d5106039083c48400d03504071041d070403500e0311190500c180c020030307030752010311a202803079500303e0001080540040010b801c100c1c040c44c85512861086806500001c105c40c1c45104850301110001d55001c882401160614200f110412400e80308182c4e00744114002c040406010303020340c0f40d8440d8020700d001d055940b400214001030b4004045c0039414000e00b00041e06956412001d1070203040ba161001804514848000002400240040105901c2001c4800c0080e600e003044040086d8180c03194000517182c419000011091b00b1107205441c0280084540c0c6d601c0c035104100c1c81203001c2e0343d0300808001d40140d0001120701510700c0040c194035000ba02e02140d4020206202500c0803802102c001300699500c500000c10340413124030020314002 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 964522239 1250 964520989 964521017
    0x15050906060a030e0a0b0108061014010c02272509140d170301050f0105030402090414070315020a0305060d0213020f0c030f1819060f03020d0212310213060503030a 72
    0x3040f01c3c0d1165010380100d514600304062f00c8100b04519030450b0421650008120031900c1d1822140c00b840e1000c824460b02e2111319100c0314251078110340f15550502900001d070807034640c0c0303002e0003070070445900c81050550901d4145501c00d4407a182c0541c01924104407500054405038400543e2407203444095103e5050600b0845107440944590341080014814040965528201c4036002503200a00311403295884520314109603103a80040c00303401a4030504074540003150000c2c5800c0301540d80802555851000f0041c4000098030065008100c2044440b2001155802001a2690740c65041c1c207000002500c180386520802603e0014080407410700301010300340d00c01c090705000032242c52040d02e417040d8843c019403a241c41828100b0000880300302c0b00c0c60003a0304a4440780211a419541d81c030400c5030141c0303000e0003511030584800c03c0c04601d08ac3ca52188000040300c11382ca400b840d8810941d902002880c81300d0255680341c056490381d0002e065602013004150036141c2c0d03150480e03001150 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 964523489 1250 964522239 964522243
    0x25172a0d02071401080610090b0706050603010b09130308060303040512071404110f0a0519030b01110102250204180b0a05060303162010020a050115050906060a030e0a0b0108 76
    0xd0342c0581d9245107415501403d07aa0080d01d0f1a900117000d031030074a054810ba200888210a02c2e5001013140d45000172103000740121900003602c945000d400038000741c50080188400800b00303d440c5112201c3c05000700b07000038443c0c03c0450704148000d0489041540b60400207040608100410105521001c400c2004c2c03e1102c248440700344080b00c0170840014a0290000f99128002d600d0341c0300d102c000b031001c102c0c0b0300400c169501c41c107030020320001003189044013034001c048a00c02180030820500100c0039001d414000c450102e580720003440c3d200c00c42d80e030281e41c030541c908d24202c4c1c2c0300d5250880d0b04410b844035807a04068034059071030499a41000031a8804807580548175074008d410030885001070b4801c50380c2c074401c40c591000d4106c240a9591004074140c424240000b94400d40b14419850b42c15800605200360f540518020051044210300d0300402e02d1151003480e4102d0750460001e400f41c90310b000545402940f50401240c2484442500d6041483c061012a121590300300107000032042 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 964524739 1250 964523489 964523503
    0xa030b190f08011113270603080306011724030c0607060c09060207030314030c0d060f08100608210d06060203070c050d150e0307050a05010225172a0d02 67
    0x189486249000f100b940e0407103c5c40d4140c0101010328051002420b0400101d03440c2c10311003a030b624020001507840e85003500311a070084d250b160000b814410300300103030805403400c54014030300f140170020045414828518494000003c540d454042c40603580220f80780e49004046880c492003001400c032403e5200035110400c190440011944030034030620000e6080101590342404c40f03940c540d100d41c0d40c02d4001c440342c0b14201c1026000f50030b15100080515800344514190703400202600c500f200c00c903104408580482c400c1c902694000708840d44c808240808040507015209031480c6003000e581c103a50190f6a15a00200060f0302c0041c0900c18440c150030403101800c0101c030030b42206501500ca0070003442c0311680c07404403207607508180441c45504000f150140fa80c8981626125030060508034001d401003900601000c207044039105280403c42107100350f266000b41c400c182c5c004031402c071160300c0d004200f0300d1080340d0903581c841c80c401c071020360f00032040f4800600a10410029078402410080 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 964525989 1250 964524739 964524761
    0x40503070f060918020c0f06092401090e0a020d1a060103060303020d0e2107031407060903060908040e0c0316021609150f1d09060402060a030b190f0801 67
    0x4668000b4848540c2c001e10308822038030705a2542c03840c01042e0390010300030320540c02c219007540704001c000c0180030008103805209141c0708080d40c0c0000243c00c0740a454195117800d54004006000060025807440ea12903208413004904880940549a001c03401d101281d4a09031010801c140c80244034107024070748540d01c14000e184c14045240b0710b070360180d80c4080f03120841050040c01103e44071203840d074503c0020328000c07002d81d0f2090b03007140107841a2100050700003a02e5901d220441c12401150004005c02202c1465440450503031031a00d0340402014100000c40c0c01303600030440024080308400031030b40102d0028041036600d0900458030503011003445000001d40d0841c0d0010114400c10b0340030001156042c010209511400024038000e83c81e094220034421041e0140c0816216100307000c050303021017880041446500c1d070b0042e03165601d01c100e50083d0300640070084000f100d0301c039810680502c0005001c0381210640c00041c20400352094002c2140004011001c00c07103024240202c041c07800d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 964527239 1250 964525989 964526009
    0x1a150712030c05250204020a0504090509010606170a0219030f1521230a030f080c0f09040b10120c0333181a01030b1f03061a04050307 59
    0x4658080050228041c141c3e0100e602d50004038a61301107001e10b0420000e4a40c014000c55441003007541c0980244c04c07a0244166041c90000051245401446010203440c1141c0320703a81550000142c1000c0080c0c02402a00032903001c1c0158941e9688451649248e5100354401280e124804200881210341d100c680358003c2c035946a007049a82040c60305030011190004240440310300030706042100c0d54415a40d1140e0041690000d0601503000c41c484411038402e6541e5410345d5803000301203603005819205010305c4201040b28007070103860b007001050340d940f0141c000f15036101c0510010f049652030118000108030075501011040750644207204025000313080070444036041100021544002015650407031007810a071911456103205804014503200c4000d59044440109000c05091112580b540c4a071a0b419031100c0c0d90b00030b0288090071900a8541824914801c03440c0e0001c0308009411824555640004140703000a905c407850055031140b11140d03078501d01401c0c10320307228190344940154 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 964528489 1250 964527239 964527251
    0x70606080c2718010e031305101409090a06030203100b120a0503160203011404050a02090f07050304170c0a030905030706030509030f0307090e070f020f06060609041a15071203 77
    0x745107007070b0003a4020848941c44080c0342114400280104500380c426a03072440045110070280d0311003140c0005a81041d00c02201e000c0b9001800e80d0000c02d280748000c5011014001b285d0079080001d40154805001480030405c04c0e500d070042800d00380705400d14994981c5a03280413105041191428840c1500c4c030008100c0307101d1507180c10746c5a02075107114441c44400f84003950203540d0300f50020303860b1121802c58810103080501d881903071414001001c80c068400b4000107280c1443c59410240b0441c00c0340c540d05d14540c0d8030b0303844100d041407601c404200014140b0040c004035100b08201051280300c2c1c0c039154042c40c00c200c03c05141042d9a40000101810042000001e68010040d03802418080c00311a40303d485d45074040c0c074030001d1508804000d5541d0070030003407413503844402e11041c11501e40a0382d4001d01d45680d0691207420403100d5940011080100b400203041c9944001c64440341702e1202c801c004024000140d80c0020807070342000a000c00701e000f00502c4841d0b43c58003001d002c141010420 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 964529739 1250 964528489 964528549
    0x509010e130f05010605040911070309032a080a1a010b040323010903050901110d02060c0f04080109030905100f1209050c0d0c080c12071a070606080c 66
    0x300d40101a2098012208040640d00d1480320382c01022007200d8101d41404290784138200100103802500c101410203090000e00c0f1401400305080350003a5400d5602c1000140c00c40d12000ea034615501540900190070000ca640c01031014103001c006044180040c00d0b8845c0b413400c1150503a41498507111701c2500c0390004005074030212003241c0c00c0340c2e4412240d1304150400c80480e0221948188031b9a140c0d420071120308201540704005112a400036225100354140c401400c0344e0701d0903801e807141d0241e48148c1c003040464a802c40604841c240d100e03e81881d060700ca81800b402d60701300f480d0031000325200500c244480d00d03000c82032100c840d40916180b900a00107450052445005140c5240f0740c1d5601c030303207802c144041400764003130f6a03202610602d80a0803d02d408600301c5814410120306014101061b0340c4d900d424040c4400740d68802008002081c1024074111860010700d4000120800070090365002918a025002c01031179400040d0880c40d841e0400c0c00201214800520700320032120b074817480 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 964530989 1250 964529739 964529747
    0x317090c12011b0809120309062509061b05150406050903030c071e0209040f02030c0f0f09220602071a0c0a181d0105040b0607051e03090a090b0907050901 68
    0xd10704405241c8401913483d1522620f00300340080072014034006d13000042000300b0200040b05401215486008246002e80107208140007280c520194001030390890208281807052280c0a0641104075603c4000a403d036103003440d007170060b00402d42c00e07440d1100b0842400214490306034098030301c1016510703629016030b50b050700b8807039442c00400c030f0080450344c25001c208d00741480202c0b40d030141118203035042c1810300480e8503085480807482482a101c030111a030410368a128040c08000e094802509070100c10015041002030400b40840240c032240084200c41ea070070a0103490250000590fa5070550412581eaa0308051148062120440c140712070141e500701140c000000c103203031807505400f00700000107800856902c242c1d958450b1410b4080f180c2030211645040310001c0b14100b10100c120000d20500e4020a040582681c0042c2d0701e84210798484020071a10b00003c0060b00d29201100000680b50290f5806c03a00e4501c0d0744070b1001c17041d820100f24a98100e00182049400c010309180020 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 964532239 1250 964530989 964531031
    0x604050c24130e090c0a0f06020a0f0206070b04031205012c1f09020418110f13260c010206010305060a1503020402040306051609031205070317090c1201 67
    0x1511000d00090400b0082e10300303840c0030040e00c886407090406003010649699220a5006914400c821307a03a000250085088224000ca8240d5005004050015101d072000d12454840603600700408020a000245554058512581c4603486000c0c90001c10150601110816008035258510560007c134040500030000d54403a0a060078010b02e40d42d403803020a56400418641c20f4900b030085002141170361198025100b602c41070001107050303040c4041010142e80300d90b001d00050030410850b600384101140700600c104680303c0344903010b042d03451541d58007100400401c0c544c10304080940964214003030281d108002024401800c540d419a1034491316003c0190168140558403003000003c240030b00b6170380000750f0b0002c004544903503403070800a0242204407599082c055070744601c1760200b4000c5841c41c042c0ca40180040c0c1d6100301f102c03030076034a90b804010140c00f40060442000411048080040c1c03041e10f44401500284040d4818040030a101512040480c1d051012042c546003c2c3d034880 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 964533489 1250 964532239 964532299
    0x61d010503041712010329430e0a1415160c030c030611030709230415090e01091a180a050319050a05070f08040b07050604050c 56
    0x400c3e0b42c8507410051071511540308102c00c03c011304000007061060843c4500601c1140740008500005c10a0b03159001c10b8088a9036001c0d5420312503040c14007544410390610b40d4070208a44002441883e03e5240c043e544034508800141403070f070a207500350429840e480020b20040425085400c81c800025400304640b0384071515203640401c42003041d1076158041050507400401c2d20901c50313103a040042d414805c500040d01c4150821000054079024441101e1040903d541c07074200301402d10049030900d034041c1250401c88006203821079910342c0d80d441160142c84100200308140c0d40b91070510ba090b108041e024180d0f9900d030000746004116200c8040015042c01a040c10190b500d041071403d2901c600c2c0060340661203409540000c11400000a281c29400c1c990071041d8041d16a104031440e20486842e500000e1050003480f0000c0d007100f40d0515400e10440005045c940c4507500b15100c3d4002880581d519801202071006211041c890300460590a49080010010480041686c0c210340303541 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 964534739 1250 964533489 964533503
    0x80d02010c050304241b0c05010c0c051e01020f0c0a0606060302030c0412020307091103040c0b04061d01140a0509130209060712181d0f10142206061d01050304 70
    0x82080c0000351b40e1080c2c44840c00910001050034080c40014154100a44110799561031f00d16200409070080d65155501340d4800c00a044491804180c140034001610400030159000c2c0701d004004000440948a852180c000a2803900d945083c1b500a4071081e500013001c0c14810018484103603840070481e0281e510948d00f0303807079409080c40400d04d407000503444400308038980030060700c400c1c612034000d50055015410840c80503840b20442c650500c0b03188650800725401e0b0020310681d005000510302a180141007a6902030701e03820b040c20041c2e0040008000103a0000340365219440c0600503042c1c01116001d085040c07180c0c08000ca10244510000600492042c020041005114034910302d600c0b80398858001d021903441c0a05804401c001d0300d00d00c1320841d890001a840000a20340354803a10340050082d00e1649002c10a8007c03505003d0810f03042028441c0440d03000388030300c0f00700c001203003100000155289848002402400120f50b401c50581080d04004030a0303a1200c140ca4209030072180d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 964535989 1250 964534739 964534793
    0x210c0524060d05150a09150204120308090a0b090f0d0c02060a05130308130e010e0f0f0601020330010f06090b031509042d0f08091504080d02010c050304 67
    0x340f00e4908100c1c03801c0d14113500c02c0b107020400308a00c04c0d00040031103440713441c0207003001611400311030036400399010314408402c1000e0b4050100340319455541d0099589800d48600d41c11541790000c0c40c83d401c40f0381d40035035880041c03101000d01081202da200c0c440a0b03d4641d81004299001581a101d02200d0900b04440410450314214115a8400086a000c0045c6039a03510045643c01f1220345d91040310344c03013198040001891907860000798820304d410301c00c100305035582c904c00381301004c00980707120704510090000300c80d4100ca1420380e007040c0407080c54506e10800742d840300e0107054405070008000b0300d400c1c180c2080b0040d0410526025103440242054803a03a03862400780d000321100082650146d466030030f2005200780600d04510000035032226072a5183e5106101c01c3c4521a080c5c014400200d80e00300380045803070107014244d51000246458030b9000181200c1015401c103400140685d046242d070200040c0c0c09104030405040c00b420802d0031403070151681031000400155a00301c04000c90 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 964537239 1250 964535989 964535993
    0xd0807060b120703030206010b0306010c060f0e0d09050312090a14031014060306011e0605030a18030809151b090102010902031204051207080c0d210c0524060d 70
    0x900070300103030000981411850950349031900ea035080d0622094001d0700446c0004a0320480550450780305440607100c050300071207140d6a07800102030000304854100e940d4004008901010300440188801580e100713904203050408041c2840c804100c506844c01c01008507401e10303265885000203d40c9581403440300d055048000c603082c00f82e100c1000c0d1300f00b403070851003d0449441d200c3c1c40d0301401040d41125896a00c0d524032021502c5120307110800280c6109041005510850045038002d20701072000c540e81c801c0000241031030301d0001044010419181c01c002c280750003080102d2500c0c031f918403c1c041608062905880c0100c610204480c41a0b001650b001540d000350840c55515034090122080b07561004450902ca030400c0c012a4890313084141d10000300e100000b40c4a040c1c900782400b501d1154918070420084990500b021180e1100454040010404241107190701c9035898070342d044061003e1401b0b5040030440d410500111501d420702c100b0a642004046610100641d103124110782c8078 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 964538489 1250 964537239 964537241
    0x131a1813061e09060c02010605010e060a020106030602030c123105191b05060c06010b0a1e08070f0215190204091802030c0105120a110706180b06030c0d080706 70
    0x70303440801c06108001280003001c2c2c60b070702001150340039410402900070b03ca10700700d0981e10603114490008502c502c501106241c80c200600082441e03000001d020b0f60b8035590081030b80c00c116104052900041405410300c5041e070f0605510000f203000200074541c0000d4100251105600d500721089400000341301000b0081025080d1800e1985512600301c0461400c090030100501810880f42c2e0841d40000d03482c101034083e55442e0190300302500140c0c0c24011510b480d5004900440200164118242c10300e0803507081084104080b41e0b110305032481d10b10009030058803d02e822004661182682e070b220180340102c0242c01c00110900322120154100a55003e4040c0b6003110003410301d4083c1c50b001e6200e01301503007150341c2d1094065130103000400c0b00544460150800304540c6002400c0003c0860304280e024517000c2c4080c42480c0d040030100d442e00c00880f90451140306500c0b05e280c2d104000e004602411710703402074088000f401c10700c10b18008102c207402c0b03a42c0e0082003c18042000710801102d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 964539739 1250 964538489 964538501
    0xa03080412091805041101091a13030818010206131101030f021903090b1b04060c0602041208120604020a0909052e090c0302031506070c05131a181306 66
    0x240c10070b543c2038245492400900c02914202d403e101c2c01a041107032035002c3c5420200b1194080410a011000704542810507841903032000e14140d0b80203030100000e10744201419840b00c0c0890111024500b080c00a850320314050091820100071000010004e002540900240c0d03070203113404034482213840c0100000e80100c100460b9905448041000559416488101d00c640142c21403c49038031200d005680ca095044824400d08404020603c0740d64010078000021502c03480c401460305903030b83c1c142150b82901640c21a2400400070380808030304414042c00380c01410841d0b046251076000e12010700500014411325030856112000030f00a107036940130100c07170a4222404e038140710032080314000701403003180280f200303403803400405c008264401c0c801c2d60b1207803040d0012000b00001600801c181904100400c0300c0441d9252800303c0d85440e00072032820f40d83c0c00088042044031036900b151080011803484035000d1005d2142204000d4041540a9045a071070070f2000151206410040003901c4 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 964540989 1250 964539739 964539749
    0x409020702041413062a0c1a0f01230306060114040806011508102105010219031a0d120509060c031602010e1f0f111c030c020a0308041209 61
    0x2035040104151000015203007a43c0f80e20540d410045444181c0900800014809402103881e405c1d00d104031b070050007003100310200c501842ca00b444043d00722800c0f50b10013408981601c0c09001c0f8900420800703184080700c2890741d1085400d642008520004640d580b1001444c00c1d0410811454034000000d91800b1500603022000070380d0340541c1c564201600a0100d8000080061010300004850f032510b0071840b000d42c0c0060a074101075420464010030f44880c440801d541955080103000c00540c5c0f901c4590106199a85000c6803514180140c070004030f4458400d030f4040c003041000140010101d101204020640f810070503110204d06000c1100750250145180c2c4522001901510941c07446800c00740b0300c0d100f6a500c001d82e4403c4820b000180c2c4060070510110b0f041025140d40003801140c404841d40140d140100d045011840307614984285149e03003e06503852485002e11282d858040d030307005070030a0300040403070014503a40204101002000505078200041d034012070140300e0f20360750000300 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 964542239 1250 964540989 964541021
    0xb060409021f0206070921021305040f0c0b040b030a0504140a050309090c070b060f1207180f050f010b130b121e07020a020103092d0303060902030408040902070204 72
    0x50410580d403030b5207445480c0001610400d80000c00c401e12803407488050340d580000320110f04081a203d904020308601040b6031003070350440c00320400380319441010311940c010790303025038411124202228100c40903000340d04100010002885003031000800c40360086482c04000800cad9441c2d081c059008004590708000c58011203031a401800302c0080035048084d81216500b04c280c0300e207180200d262003000c200130000f00c40c40c000035000345000301c08407644007006042d603040ba42504114504045103500101d40f8025014001d0100718210301c61842d10f141192020003407414840c01004040c0720522a80c0c80300180003540c11000000f80f03000700000c10350710f81c0a64603032803207002110f2401011500d0301141320610040c100c2c40c090800266029000b903801078040f440702500118058940e90f4029a41242030743c4511080d0300748107580b60091030341064000f8901303a4500c0c005040d55003e9128005450041c0309100110304030000b1107007140d00802e00180d5451091000c50003622160f0b54140c084 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 964543489 1250 964542239 964542259
    0x1d041a0c1b16140316080f0d17061c02040f020a03050a2c03040f0b090f030a023706080f09011b050706150b13120b0c090105070602280f0c0b06040902 66
    0x1b15400048085490072080240c2c1d80b000c007150012518203881070407070508107280310089985810311894000d4100f0900409a40c015410b4010405032841c2c5000704040d40e500244c402100e079850b102c0e4541000030000c090055404012107424844c92907003019401c034400c0001840c2c0454204101c0d0014a285000e0004403581c2e0048100140c01504000e130046071628080300a81c03074049803100a075a4024403121154403007410700d980d14102c00e00c850034800814006040f0111513142000b008103d1366a0300392442c681019074005d0f0f208050f040b407100fa8100024141c0100310307190701c901c0341c0d1000d18105403200903504044010300340760400c08020800301107011420401400c014451021502d0a000d0010b946400c0d0450302c4c104240050304400a00c8081014248060010a94160140350442c14040f02c1c0c0c458904aa00440c210354000a0b4030707010540c036068070b0f01e08400e250120b090070800e1004921000c2c0c421440404000c000c1801b590010761181e8071944000d0307030137030054903043c00 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 964544739 1250 964543489 964543499
    0x20330151215040b010504021c020c010209120d030b03150c090a052701060e030c0d05010905070f0306060f05031b011416060b0a1d041a0c1b16140316 66
    0x90702d00640d0207495402400d030010555062a00850744990b83c4000d005070312041e8101408025080b11241d45800d5400700120030040e43e0f1f0085c812540307521000501070941d01c1c000042c080f0790000c1c070503500a030480d1214000b110740410082d07034803141125503103550718a400d002130000c1e4000c0d04800d070701121010569401d214500380b441c00041625070801c800b40d884850658010801480c4140e1590090b2000500c03403d1510318604200d115000128000b0fa140da05c990505a094124800d203d00c6100b08005015030707800341200414040402c2030b0405d08110110b1340752500a410a460200d5009048005c1c1e4450442441d041d0ba60070317070380ba4407510a852000360010b810641943c046041410307030306003450142c03103520465580c0c2907214880c1e58203144191901c00014020340300c0c0f00701100780c000ca03400c041c0030309031140c02a52070507940c804070b0b244590b94614590301d05480310390000c1b01081200c4450220001640c02c58910180190070000c00646407203183e481b2284803035008040010 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 964545989 1250 964544739 964544773
    0x1090905040b091e0705060c010f06080d1206120b06121e1608150907050303040b0703110c150f1605070e07020607230c0106060203301512 61
    0x1001d030691605440a29082040521280c0140655010310717410a9800300020324002c001060244500c0001142d02188584108100c4600c0d50103181d1a0b00400100c0407032070340c00200ca00002d020800108400340c100704054005104141c801018281700d035000c291700d9503601050301d0f641c49008048424100560340c21420003403c40c0c40412451140c110184030203d60b42c2182010f0b10300403001002552030004002904203806081c4680728041e0301404101c5480510052025001c01c455596482d0356500e001049038070040c00c8016213130400160f9030b8490b07032400d01044106602508494842d0b40c0c0225400c024458080b1a03061b070144405010200301001c07400408803040c1c45900b2019642e0705406907101c07041100c04400182491150002c00102d40201000c0e41c00101d0f580b03803c0c0313240c03a00c1081c00c54810343c00080c00740c0c1c40401c0032807024240951405044a03030303d414804c2580c148090200a100c00707881e180c40d0003418086c4008030303110070308200095010b00c011105c4209145075648 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 964547239 1250 964545989 964545991
    0xa0608090c0409020303391207020f06190c170a230d0614032a011d0603090f01110a09050402030c07080301090e070617060405100504111315090b0901090905040b 71
    0x7da1000e0b20a4000c4541c800205d06a1029070102c1c146070b147c50040d0f420400314040d0714600d41c0e0320113400e01518010161804100c00103c165440310100304280b4206400c1e21807041c120840b05078020880f03403241c0c95100c84038481d40c4074030101e658598002510071440354020405a51340203454070f0030000388862920700c1e84111017030030350940e070044140c4061122030b000c04801ca01c0c204400541e298296500c00c1c1c100c000d0807450880010a010203290014006e0740c000e407404a244da0101c0d0988910f60030a101e28403104900c01a80d514055001c0405014111140715175446541d0110004000d1000401150010340d0300c984515500e45c1c446040b50001c1c01c0d11007100c44144a40c13000031810600505240c2100011042104415a90a803c0002420000744507108000e4104000a100c0d1218001c07540d41005840e806d83d290b07000180d001203508500e40c04000800200310b521049241c220f0f10000649401d801615a5005420f006070303168511a4001e040d010719040410040c0014081d4403 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 964548489 1250 964547239 964547317
    0x615081006020a080a080603210702130608102003010b12010902031e040609240b0d02060307050d0608030a030e100b0a410a0608090c0409020303 64
    0x1a003000c0c0e1501422a80c901c100b0100500d44c40c0308200d46041035000e54016540b00d60002d00711030301d09684600742082c031003680c8031004c00b480f0302040071030440c0b80542240180301c000c4441013001504e040c03001c0da42c40300548100c10820f69540c0e0000b442400030008900b04540281e051503903540c0d640f01004181e40101c011840d07111481c1c6c00881d0048040c02282d025102070241c00c50f415814101000407844050001c42c1c400e42d44624240016058560003248040c4c401098024280000d880700107946003c1045486a0084908a00165aa8410303a600700020380750a58803030345180d512400901c12600100700f144004103107005540e0741600a103039100c8041041d100658841e600d00e03400e44002e101920f901ca21011002d0002e8010250604c515198445071414420700204900440520f840d040140c040c00788407210086050000e425401003010345003035203551519004060300c90115142c80c600c80e031b03180c0e80b50300d0940d0740404c142c03101601803245502e564452685480e07487c441c4e000365 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 964549739 1250 964548489 964548511
    0x503240d08030f100f05040c0e0a03060225021005091c05030318010e10111c02040303091a0409050c04090c0905120309030307021009080a0506040201030b06181201061508 75
    0x214441c081108844c1103c0c00c401d90a80401d06000400c000b401b029042c960410000540c1c0341003556610007e00011809210010703900d821001c038011803100031244000b8403a92624100005072120ba400020151841c40c3c003503150002140084d44008108456128403d10500d8007000c1c410007100440c060881491003421a00d40001341c1400e0350b510480900c426045600481903400c41074200102d00c25003c00f0b090300c1c104d400e4105800d03449042c881036943c0f81d4040740900405421010280142c1800c0e004420a04107520707004103907101750700075460802d8480700032406051982d001e40d0081c1101407410300001c01c0e9500002c00419072841b455100e40b16044100c0c0c500080031044904d00b8002070055440c2c00d11940a02c5940224000e0140805ca04030340c1c005040081401403c0c5540d00c47c07800f03009181031900004050b620814403162042038100601000410b00b00103040301c0310781c103942c0003a404541310481e90040c540c1e82d1101d1000659101c03007000e410707400449144183c902150b = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 964550989 1250 964549739 964549741
    0xd1106010f0302100f050d020a12050c070b011401030906090303020c0c011b0b06030a020a030f050c01050f033403060e1b0a11250617070503240d08030f 67
    0x240e8034045410320001c2e4000445002001c2d40c00c5c8114440c1e0b05401ca6400c11a2410015a5544040368492000e120000e40044000c2d00518628083e4035040181d0400080c2020341c1a115103000350018455042c85c0b25200c0802011a4001c0d008036450540021041040d14a00d040c041c010390f001d1019603400b409000201003681d030007501c0e81040d40c40c40f2003200c1e01e03000b01595800882070300680001d40c540301d100e91002c0181c1d10400380d40003452060720700e90801803040c6084c502d401c00910005061000c01c2c070070f500c0d8030b1412034182d07944a401d000e80365428110a0300803441c1d40515803000341382040c048040341c0566030950000030403a01600085901903451152080c41180120140b25035490100b00022015219039012010100407134152546021003010080c0288440300c18901804141d03201080b026400842006c0c5000700c20f161250945040c000003410703031200501c100703d010002c40d9086881c0d800e40386078031507440300642031141c0e904090509105941044a1000d400a5198 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 964552239 1250 964550989 964550999
    0xe0f0907060503070309050a0503040906080d030203130b2e06090e1603050403050f0406031d16090f0605060309010501030209180d08060414190f150b0904020405030d110601 76
    0x9810342100e2441d40c8042c00c54544072003c9020b0b0100c3c15080d65540701c1e1041d41030100d182807004000810131920005005850017848600304011110680107140c4144200407040c45440e0b142d110706644044441c98598459429541c12071803001c482d08542d8079641030b01000d0000d07200a10542d0071603224081d155a84151050402408a5110340c2c56039001d034190180c603002c4c1d000070b81c025200381022410912900a400b165070441e80c021000651a0f0310010f0205013800800300701a0750210203802003da0b14a09142c66606030700c10800341590b654070391101280b1550003e0044c2500501c0955a403d243c254180038140078003082c1c1c890444580030900d00c1900c03142183c284e050403009009581981c20703003a6100b1800504094002e038031951450411145004154820284a4841000403903100c400c42c04a504518801d4105450100c645020030340800586d011150410ba0b031917510881a00400e01a00650388800e81510580421070030030b5801c520160349031121101220116a696 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 964553489 1250 964552239 964552243
    0x2160c0513060501120b0a080303070302030604060e090307200d031707050903070303080a09060c02010905100501081002070c09110a030f020f0904020c070e070e0a1d070c06090503040e0f09 83
    0x30f03101d028007280d4095500040c030010768100ca20290801840320307140710355a030310050450b44112056400650300000308007035031429101d505d000e021490f151000c40c1c6820010f080c1c1c3c900c04c645010b03040e024211444c00e040f4106404581b12028040d100398100400d03860050400e54011941d140300407891800240820310070742c10b640090200500a01e0941e1a40d01e0551310590054031001009840315595804100d85000c3c10003200c1da00e5000203080740481c1405170804c0700960a80a105081c5001080810000205800c0362200c0000050790743d105440d05294032200d070342c0200700490400c104400320300707084005032464071034585061003010f0480070704200320300c124840b02c220840c05014050243c03d040c2d010749104c1540c01d088030011a20b8904002107400c1c102c41200000d040070030054610304003200c40200411030151012181480300707129880e0250000c0241d010089983c0e00b010900c01c842e048108141c1d007082c20741e6551620b400b035490302c45108480100c03800d1142c20211b03010b80d0700 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 964554739 1250 964553489 964553501
    0x150611060c07110108090106053f0615120708010c1d0a060804060e0f031c050912160b1312180b0924031f0e07030c0302160c0513 57
    0x3c0007118000d046148001035414120140014403a590390b880d0200d81925240258014003104500001d41d540844603440301410455501210114401110382008403000a41d5030b042041c62005c4002d07500702d000403480448642040c01c00e14440c141001a0402e41035200361403208451b510301c1c00c2a544080c810740c4d0035101400c5113801000201c42000303824400d860242c1c000d48a10401b041c48001c0000349454184090440040c0d900b00245840e80020740c041d2900203011185000d1195281c1011110b4903809c02c0f00030b000300f03540009504400625024520044a64000c54000590801911009002c0070fa40011680309401c40609441240203034103100704040c105180c84d800c541000c1000300d031604042d1409402510041e41c0480c0f5000c00201e06009042d00b84089491303152603d07200840d048495103003104a0900202030118600070008594090b180741004241001c0090086009100308011996130065a00c101005c01ca00c05c40104101c40c82151400b81414124600a0032212 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 964555989 1250 964554739 964554743
    0x61e0605030a260c01090c06090501030608060103120203070503040f060215010311330306090a0902060a0c05070f12020a0f2904120c0905011a0a05030901150611060c07 74
    0xf120802510004401116088009164407035282000c200c81c100b1801c4d45c0c40e175501124070819004c418003200742d201d090003008003001d10301131003d1854018010303154201804003602c4144001680e06602d4001c104a6900543c86400c582d6540d50710825614003440038000c24005004035451200c040c3e14034403260b4141c1760401000c0100d442020200711114180c8800c6600507103ea101a074040d5400c0002e0000b40101c0200304c564038500481084041c600003041011414509440c58015883d02e1060f00c965403501d04140a0100c0c0c5c5040c1686000c0f1143d11446440b506c0a8000c11012401d81d07070721b55094420386150440760741701c80c004a10040140105856500d04001044004900c0365144103076403048203480e450703c0e4840b001c1465131102e4007021340e40f004001804100d00c92080c030402d40104240324801c800140c002c000481248030350094641044804008030700b00c06400c0d801034203100305c008a0001081d503207d0028001c070b80364012a0f0514040c07200001c621005020440e64059 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 964557239 1250 964555989 964556003
    0xf090a030504091e06060512011502120a030e0a060e011803080712090b010801020a09060527032b03060e0c0702061e0d0921080105040e0109061e0605030a 68
    0x34200203d040c0203103c80b415000c16400c00001d0642040c01604c13400380600017a988155540030541c90140c18000180c1c001a455014a141141ca40e81d000c1400204d220f01c00210a40c2c07907130148401c41c060709140811311140c0c080c041c203080030444184d01403a000d40d55100240007141c900290303242c0000d00c000018010444d4100000d144031301c07494000341d00c4401c0d1040000c8001c2c40b03440e9551100c1090b0000003441e0f60019211407504c2d000b1003c072004007003628080380341920f01c24181003400200c1940304100000344030350381c9450342c042c00000300c045607013001c0400c04803408440b00d641c0c501480701c4402003480d0107070100e202c21010020502c04c4c14078001d801c0c54038407283c1c00d21810790310821000c0b22000d40920490b954480000c001c0801462411010070101e000d800c02100007280b45c24403000482189008182c104c1d0402c922604540d400c590000380400807075982405080080c0005100e64075040c002c851448a002d240c140c05011420100500d5444005241d42c542d203911000d0412 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 964558489 1250 964557239 964557247
    0xb0a081f150f1d0402030901020d060e0108071703090922030e0901051903080c1e060106030f0b0d1b08070b0414010320070201020c0901170610120b06180408030f090a0305 75
    0x3d401c0c20b070000d580000d0032070700061415948842210884070140c2240d00c081c00040d0041211400401c40c00002e041110700118001d80b110103116a6442980c000c180101c8901c3d00203103079603001590198550707010441100264a841c0f40090041c0098080e141c880c1e601600041514140800c2c5c01c1c80461341410750900729070841d00c0358802c44c4c020320000e680da4820110844030420300030310407034003074000040200100e5040c0000901640d00044041811516200e060010f0b035840c100f050700c400343c009003020303048807600341d1000340148a50041102c600c0342c0040020110900ca006204030303282903500c58124040103004400303079080750442c04610191603500345a00440003008015881c4140101c4d0002810080410300c114000d0748043c00c81000d103400342080040c1404006d5028024031040740c8102d0a1a0260a5003400b842020b4150700c0054000740107030301c80a04404074404c000102050602d0f0519201c1c045078811146800707110340210114190b0140010783c902041d07410344a60f810 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 964559739 1250 964558489 964558547
    0x607030f3216020a0b030a0509010212041203200703030e0a0b0615040906090903030f0e06070f0516060902100c021518040903030b18010b0a081f150f 66
    0x40e41200744003802c0c2104000c500700069a0b902001402040d00103249500d078940a2a200b0803508000c100d40c0e5540d004100c018001c03a00e0141c01640507070703c555890444602c1208c00c500510248840c1c204220780d00c00300078140c4d290940503100046c46a503060040c584440101a15440c0e8004018404000c981c04101c00c1d1500c110b04416061013040500d041941d502419426145551300c82c0002030b643d14081800d041c1c1c18014811541a540018800d44620380e5400b1b545440c0204070008210054240c60301c0c1307500c13910860350314070021f005000c03104103079003011800ad20310850124401c51280862200b09402203005451481d00240b4404003550504d50080b115444100d10ba440000200540c40303c60760350303202c2c00d48607502036500003a4074080902408403411400d5072044468840030010015040450110750212000e031400304480e032901c5281102d0044032070b000c0c1c94500da11940c049000001da26207450610600d07502c03a0b0a500c40103e0030b90759000d81e0016131003036501360721018007 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 964560989 1250 964559739 964559837
    0x90803010b07021f03050609010b0a020a030e01051201030804080607020d0807030218210c060f160f080d022106030a0b06130612020f121b06090607030f 67
    0x25540d80068884041e0048113400e884891000c2002c00300826504d0b0305201c8541070164030036003d400721461407480d16801c1c0c071010b56140304402005040003079000c0b110465912960540d0b501040c0401801ca141d40c40e481c04281c150014019000c3e175214a82c001106d6910002d6941030310390003074440b1265616644070480c0a5408031803401c18a501840c03c481d9192200f9441e040c01601d40c04000c00c0d43d04100344a80e0805052158845c03181e242030107500c8100100204035158108880401000e840aa140401c82080c105902500024000c102009449003940042c40143c1d00d941c0400020110210103a1a4580540e101505580300754841000140d080508a070002002807a45040d04003090711001a84c00780d40194500040b117120080031400c209030884420601215052021049041880c0d51204500c1c1030049068208044060903146c60044660720f880281409030b44941904000d004044d0707064400c0300041203001509044100110440030b40130384461400746224490620f00 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 964562239 1250 964560989 964560997
    0x10912091a03060a1d070306052403060d0c060c050f01050c090d14160816050d12050702030604060603021f0f050a02030d1409060c0408060103030c0519140d03090803010b 75
    0xa500002ca40c50045400b1964406503501c0d502011005c081a00c0d001000406a50495005c2405440603080da01c00308144180400700c01e42049060b20384940e00c01001a02c0e080f2000307000340812113911000b02e905a8029a014425400340b0b040b510403003081c5a8490880703000300d61203031001c2030901448860340740a4403c80d18090203044011407aa03a01e5420504140013281460200380d90000204580041809151100689200c0490b0820329110204046450307628000341424040d02c135034100c3c0c600031815550000c0c1c010781110001c0c500351400b44010492070109a2142034401c08a200c462f075460b42d50b1070140715603611100b01d90800f03001902d241c1c2001d5084c0782980024041030890b100540308186c0007003c801c403842c0c694200303100c00909150b009480c076028002c0401080c800300d0740020b01d00d81101c1e031500c2c1602984000b41845c030704010004000c030204020140c00c0d80c007071180b2000780c40c03482050f180981d5505130101400360201c901c1c8980081120701c082c0010401085518060 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 964563489 1250 964562239 964562251
    0x906040605040303090b010605090a08061618031209030204050f070212030703110c060a1107080a0f0909050f09010e16031115070c0f051c0f0305090307030302010912091a03 76
    0x200d801c10199a1b50007809000340c0000c3c1c0003c001260460b0340349020000d08005015540180180781030002100008040780412081072001c0d410210860000d01154800155007226070b815003207031080001496503038988403da1080d420500030400c0100038444441c06420280c000b011041e200415014107030300001c0812081c99500c0300509608038044004103411007510300903003594a0424002d02c2141c0e03607140d0007820f24800384000070000d02e049046403040701441c1460f034001ca0b178080c006c0303130521303c00e803c1004410f0810b414040605010f41c003250150790f03400300034400302d0f0310350100d41c1d500e00c10106420308038500c59008001141820312a003c2c0404003400c20030000494240740030040d8082c1c08112111180302c02c00b0420701d1a00f1a000018202c2101d24440500b01c4103819034041c40c203040701908440a1420910405004200311900e0580280607120f90381e599040107130007010820415150003443c1100041440e00ca05010400e80352130740b1100d500003028038403194441d0001080 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 964564739 1250 964563489 964563491
    0x307060b0a1a030f0a090512031f030303020901030c0311040311061603050a020c10050301140d060f0603061d0307031b020a0323490f170906040605040303 68
    0x11605003030540c80c00c81001507191085039203042101104c1841280144040200c52501c030b0000000703a4081544441c0050000490b80c1760b49407000034401c010302d460320a030303290385840c40000708154240c1c000e000119002d8034204011031440105400ba07400b00740588869290070802840010351103816050241c0020b0b14490510141c43e00040f9424040f8009601292001c101200419030400c42680c461714241c81d00c121103003940304090300c030340010b000ea4032002400486c03c1445856503105040c2a54000c2c0c41848a064040030000042546010070750b600c03420078080c0740100158440072401d0b90070100080d40703450000e4400f00c4040c0c9802d00721003001102240c1290161740e440c40a0000303180124401d081c810351804600c0a0f482020140c00c505800002c1c2101d0340c0d00c4442d0421240402d6100385121648447e103003510f00c0038900400180c0c80c00b01c4110300101540c0003d03c8000c1c250180c5a41408401c000802844950101c0780c50b00c1542c1300f4400280020541d400868016200b424 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 964565989 1250 964564739 964564759
    0xe1014011209051e060c0412080313050709150603090c05040b030a0615051219110a080312070305090304030c1512050703140c133c1a03090307060b 65
    0x10f0f90504010500788a01d003044079000c800402c80c6000c1c0003a94201503100c420a06e460700d03040c2140185201004064113444000c4001950700300c600030200305c100ea00105607104584c541620304010201c440d00c295a5841080000c21410300a01c131352134040750407400d2030030740529207010800580a030300b46c4030703406000310050000090298015106550701189400d50021304103070901c2060741e020a0000c105500122099060511290585008030b8200c099200e41c0039038500800c1e00b001140c1c0c014080b5100025200100c52458034146005540b170b95424072060f120320308068bd5901850002078001036050700100509208699180c6d07a400d107600f000784446010924030001c4800444010300820703115041c0300c1102e4074000c90f55511803801d0380c50f5402c01c030442c030814212184901480244042d0047c0908200102c5541028041e4140380030507011500b0740d901407642072a900c14011502685c8910f400c9000700d500c00c0d24410121140198100849a00c0c1c031009410f8111003c1e402401d095 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 964567239 1250 964565989 964565993
    0xc020703022d100201020d0c03052e08030d0203010515030702152502101d0c04050a020702060301120c0501090b0a031a03070b0a0e030318010f0e040507090e1014011209 74
    0x3030400050700007142c0006132601d0187c00100103641600d5101da003007524180412071440b84082d92103114082002004110001c000c03910709034000c85030082a001d1102103081c950070b6089400544c169007003030364840340f11000507400da1f540d070105850010141e005042d854000c2c03400d00f0394150f4404403034464203105d144501046031000301c09440560051300102a1011103144c1402000b801d540741c41304444115120408480d2504d4803541c0b41489643c0700e4011640100e16501500c0d52142c008000766500d5a4421040500c00700034601110016038481001442d98010b16200d0221003485408500c0c151041c141200200ba18010281e07218038002d031a45200c1e2420032460b0080d10441c034100e561540300342005400403c04241d000e00c69802000030715840c801c51040c40340010801c0c2000b180c4140700303030360a41c3c14900e040181600145844100198107901600440c100c03104071410380705e25100d01c0c5440580c07203028011810780007442e007441803955200e0080341d00081543c410001320a04c0da5 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 964568345 1106 964567239 964567249
    0x1e05071710092f0301030203060a0506010804170d05070e030c03030c0307032a03030b0f09130212010603150203010302030114010e0f0612100507030c020703022d 71
    0x50800600307101600c02664441c42401c241c030048076843e2208151a900300748826442440707000040781c0200d0840c8582405004181d540760302c039603035030344030080e41040f000c0050311011020414001c00c3d1106200f254003400103079440c600100da040003090710301101480003a01c00d8008110311000b02c02e00000721a030050f41401d1103010400a101c1758a0403403051006140c0f28001c5821510815515038840b40c40e205040f600b1381d030070010490612006180450395400c008840c11207000251810346140282e1900b400c001250442d00d076034804201c0c41d403d44030002d000e82c001c80103204600c1c0a004481c3c84004080300c0b0149503141c02c0301e85409090291041032260074030400701d0503540720070340b0034440201c1000450310822401d24080380200b9044401c0c100082ca85080385640301d1000c41c59100712600103104001140c5804244a00c0c0c4000d6903014001003214560240030741c0b60 = true := by decide +kernel

theorem cover : BRFrame.Cov 964388489 964568345 := by
  have h0 := BRFrame.cov_init 964388489
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964388489 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 964388489 ≤ n) (h2 : n < 964568345) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
