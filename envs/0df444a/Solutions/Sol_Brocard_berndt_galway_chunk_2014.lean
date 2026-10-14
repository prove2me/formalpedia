-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2014
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:27:17.962427+00:00
-- url     : https://prove2.me/submissions/45465c69-9edf-4a32-bbc9-ba879590adbc

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 362050359 ≤ n < 362230215 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 362051609 1250 362050359 362050363
    0xf19110603010b120601050906070803040311010e07091b1e110d030506031009030806061806070f0c1406190e0a080708070b040e0c0307110a1214120c0a02030c 70
    0x740e000d50984540010244d11010858000f03d034401d02c2400c1080c2409550008140b0311b01440b0401000008008003040605020300b11090f240d0160000901c00904800c030078948900c0a841400e41e007500308144a125003003122907603c908051582e03aa1000e50160080784411600b50344080c043c0106c0820403083d0940c244622580321b440d0707450118503418540d052528001c420058000c1062a103084400000d5100351403640001003150ba4a0700da062603541c010802c501d4046083c1e11074400120302d070400c030350080d01c07001041c040d03800030440a980d5240c52410004064403150300000c10040d611905400e00d080000e00c801c11b15003000704646810201d5042442600250200c0d48070100810042108000c280058003808454900302442c1c01d400307801c19180981003220502c00440000c081c2c038820700c4403045082c1e8902c2214042c40d00da04100c0c1151452040500004000502900b5a5400c00c0100e9500090b28070030407080d036544d9050b60b00c00e900410603010450004006042c11807c0c2 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 362052859 1250 362051609 362051611
    0xb0a03200304051e0d02150a021c050a140f0106031e1524080a020703020f1b1906020c0d02210f0f0d020304140103180812090f19110603 60
    0x11039001000d203076030842e0710140303c056000000c4a035680504003403010030344c1c0424003c28420311f440f6008186d4490b25032403400390140100c54a264244030900c50b8030341401e50412802903030303507210810044010b6013400d44006000c1320010b0350f69059000401c2490310981c0010841e44a40000204203414030000d84c09864141c108200d5041e01090140b0544018040c1401c01da01c0100422011140c0060302401f01c100040030401c41907400301c0e01c48281402800b0300c3c0c03a04884902030324103d8007041401d0081102007a035103801552070740b003841b8881e4410b100c0482690a141c0042c403441c03690700c0420080501000c0f049801030b05001c6401007014a10f400c180d06010100054aa040c10364480c492520b0112039100340075500424030b1804464000c03040310262950742c01c444100d10340c15070050b00503149400700c1c2d03400445030110410070700c20210f0141c40c4014103103032194410b403074460a9030759030280c0d4820610503030460440980c25034200da080c405500d01c0740040c18003c002c010005511500 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 362054109 1250 362052859 362052863
    0xd03080f060d06090624060e0d05030c01020a1e0c03080a0f09050f030909060418021201020421020102160e0c090a1805010e0711060f220309050f01090b0a03200304 72
    0x42c82c6ca22801044030a00c0780d090002c2d415440003001d0601d007000041854069010003402401100d68031300501c0814400c40c0d055210ba00001d6541d40a1101d0042509014907070545011301c07001c4c0c018001d10f01c90000c010080e81c055841c144d0980710038041d8001001100000c1043c255608035000001e5014400d941c104184000a07646071a1800c1c14803150050003010117100c2ca02d031000441086280301d0300c0e48030168041e40d00380410008610941d0080c4039a4100070000b03d1058080c11040b0140103000da5118030170703400da404d200350018035044007100794041c98071103040110009031100ea414002c1c0c50921402072039030366a1661402e170300210305104602911644d483e100140600c00e08040095000682d44ca04403d085e80103244403a2600d0340a056051064a060701041d00b5540041c942c0c1c240c1002448040c000f04c4e042d203800b0303000640a00c03d1602a40060314408603940c018006801100c100d40d20b1603144c0319500c201200180328042400989540303820560002d5050324010314880c42c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 362055359 1250 362054109 362054111
    0x312090105011409010e07030b06040806040c0515030601020709020901030906091103060106110d0c02010e0603090114070e0a1a25150b1018080a08180d03080f060d060906 75
    0x25050003480c04510f40d5508409028160840041000d540c1c54400961b0140e110314002a01d40340c404005030b491f20030365015083c0c52041105001c14000c888006600301c0700119900c90410101c00700c680c50500040301d0035805a0401c039020051765060303800600034050305150001c2c400340d96654420071070b02c0542068070024031224035070f8061b0030100441d13070240c000c0f41080d128200942070300b10f036035100014900c020803003104182821640a8048940920b100528164581c1742500140c0c1c0200031a0a1854036180380c080030904a81c050601a0b071040c01c0505030b0a074150415503c0002407407080c0407142109010020000c0001c28040074661034105070025184040090805a02d0001d038090201c0c1054a00511101d09a23511008820301d0000740c00c014034104c081075421607112010741e00c084007500902148034200714960009241c0c2840d4880d0308450310190400340402c0c10700465008000c6034024002c6020110f509460561090006180051504040d0790b107400b40c2d41281e401f21409 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 362056609 1250 362055359 362055361
    0x7020a0b07122405030c0a03060905011b020d020d1b020103021b03031e010504060e0112020109080f1608121b030c0a03080109050a0506100c0812070e0307090c050a050c0312090105 79
    0x83c203c1c801d400001084201e00034032a051010300082c1c400c0034140b1000b015150382e0f2000204002080d0003140b42e1000182100e002000c401c5c001a4580c000c1d107030f40c40c0060082c0c0314034504060049480320b0380444408000284207400e0b0f03005400030f40c050b41e20164581058162451644010001184211a400b81d40c0e480360100101d0f0a20505060b04803074843c82c2810002d200b00c90b060f01503141190520340d0f8001190300f5600041c0c581d040306400c5400030f805620b03000341000d000000c40d11000501c114020849980c1c4481c1c1c1503d0758160f440100e03000c0c0c0100b00c10050520443e551b20f02140406040e41e02d4624080040e40c80c120301240c04402141200d03004010030545446000d0f0b104206500901607860403900081084400000031310500022031174000902c03900f0700503203031050540d101a03681805c0406c030151009100180003403180c030801e00013103000645401388136240001c42e20350a041286c124800d4400b40c125804412292000303010b403100e01f0480c1741c0da460003403580400004803 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 362057859 1250 362056609 362056661
    0xc06010f0f0b0f03070f17010b13080c090403110715120e0f0c01030c0203120901060302032505010c0807060507170a0e030403170f070606150807020a0b0712 69
    0x20101ea441181096002c0c0981880200c8190880ea0b21130b02c3da2804c441449804071090b20601c000a056040401205001003a01d803541401404561105004014411394403104180d561492152030790700012010f01143c0000e001e000b200c0c00c01e2002c0800d840c6155200d000e000100303081c107480788c0d00141207400440381ea4182c0b44240e8620070b03503d00c040e0034149180c1c01e52990300c01c1400003440c1007680d1541d814a00c644240186d807a190407031801c03543e083c00c4c0303145d80038007804417070000b42d129019144031101d061200c442e21442000c2303a000c1d410340c0181b612005407451540b050050b140c07840100700c903400103101449031034441c03917081c0c441d00f90700b40c0460028001d010300107040b625020314024130b198400c1000015903003241d600550f5001d409407403490b080e025010386102050003000c045484420805c3c143c0001e0260f0700e2950310244041403892040310315203810307160200076030005005540442c400d804003d501441c0350421500d140b0311054400f048584884001010902d50754034041 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 362059109 1250 362057859 362057879
    0x80d200306010e04090302030a0f120204060201020903060106020c010c0b0903160501090b06121e0c04061d100e070804050a080c0a1e030e1905040c0e0418081c020c06010f 75
    0x9083d16059600b081407504d01d07540a5500d1242e1b040d80014040c0f110300d800d000c035100304ae000c60401400da805544803030b5500e0703001c1e011f90081700b12580320380070781030010403060703c00071f170240340f11030140e6560b44506026210300011000c0508180b8a80c0820445021803e00d10102c1d90f0b0500d00c0340d000020010040d040c1801d0304c01e80908401c0c440c6c1c11440d00c403071913408009440c15880c40070600d0414a03400001c1030500d0200e2807018160401e003401c900184150052880d110311881400f040c0c80389907a200402001300c4007034014801542007110100b004c15100b544150f5010303118104aa00c4a40d2944070040c440c1c002c0034100456a000e420010100640c1c034208401c4036540d20110040c0075003940d0054406000707080030501030402e55040302030007138000d461f45e4000d00001c0d00070000011840402841c0c95420000305004508158504245241000c1881c14070f42d082002c40e0f04120840b45842d1000c40180c500840250302840000740c091024045036008000c1803c480c0601032071701c01810 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 362060359 1250 362059109 362059127
    0x6050706020c0d26240301090f08071e17071505010b04141813021f03020301170a030c03030b0103200406110a0f2418030e030c030307080d20030601 65
    0x28410004543c14054041700d12040c0e01c1d90707100c051040250700a101c2020900400042d034024048001e0048140180480c2c0c0005110503800f4180017452020a05000d00c68020200401010b840e0300c1d03465a1402094000900a054420080c001000c1c0d0382c41c40c0c020a8503002e8000740b05e01000000c080145401554a51a0380342c81a0780040d5001480410351184c014000c0c03014203260b160911900465551111000140c00c1e0381131a07081c0c0c0180b01c240240250024001e40c04c00884425142c055028006204e0910b660701d550707940d000d07680c0c0d50390031800303441c59641444c10325440c0e016241c0c00d1104a450141c60004403110701c2c4d103941c9420001000d146504600350313a240c0148100c2000302d18608902400640c01140d0740714803240c1244408080d10b17103100d550000c00d1038810b42d018010408171416004901954800092005510070152a50800840c103645070b4401c001601c00140c400c000341c03032407180c0ea80d400120110f0704030103110742d900d1071400c07c23850090000c10014030750b030404150 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 362061609 1250 362060359 362060417
    0xf070c12050c04060515040e04030509090c030609060d05100e1204081b0d21050d020c011b08091b04020910081905041101030b0d140708011a0102030406050706020c0d 73
    0x10101c6006d44020101c0a44154090038501c2c80041c0002070505004a08a8107030f1500030340302a145103880c1e282c4500e030382c000351603140c41a006c40b000b1800c907180c00061142030130b8100014003040c440c00c5a950700184ad8980500813540a118040400862103001920050030700c00060556030034084400c7c100c403040c80c95258418580c0c690080c012550307940c00f403508054165107030301d0010b600103001c3c3d800380030b11803818007420300001d1300b001c507010107400009050900f00703a00103410140000c1034400810864501c241d5910120a1070045100e10327007140c02080b8003410040c13800600d03101040014210941c01e2011070428001e0110410341c0007150026400c01c038004008a040a55400300c800004124450416807a09003102895442c2a5600c005a600000441420a40d0311600303849084512a00049518180074803003100300790982c0810b0420140d01844c5858105041540d80d50407094040e64041c0e401c7c40384025a80c01040507a8140d0440d445415100c000c0d1012000380d0081c0c4510 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 362062859 1250 362061609 362061619
    0x1b0601030c1701021e0a0305060f01080a1e1a090106020c0f09041a040c080d08060a05150f0f04052d0f030c03070306020909060a08030f070c12050c040605 68
    0x40021030350202018003600c0300e00030104003800303040c042c00780640140040c400601c0709541c44540817004500051441100584060020b0f584030701c01c028058051b8007410b03020401d004005140348943d54003d07900c0003451800361210112074080e0701e080740c642c1407180b0300100380540da054907417800c81182801819680300034100032001c6404103524987d4151414042c1007100d010070304001c01c4000c0460050010300419080b46001e050035044403c00d48121010b9010f21004000300d5840b90340031030320844014114501207458402072100100c3c0115048030000000d20800301020404001009010700d4041001d0302d550038101000401052901034440c1c030704482c01d5a0f915010030a10506101404072001c0121031500d20100382040c10002b101d5905008901d004810001c44e5801341005d2a4207032403241c0c0036900e240520004042d03601600020b40d00c180000c0b8240300415000f896000c0c401c800f6929429039440c0e2002045071021030840d9590031043c042c0449003018400e0380010401210 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 362064109 1250 362062859 362062861
    0xe01060c08090a0b120609060f06030c090409020607032a051504020f190f0806010f030b070c0606030b060415050a05010509030102090d030809010506090c03060d0c031203021b06 78
    0x1400100140c14010901100451081429a01c4000030300c020704c0300742c0240e0342c2ca2802c9080212048011a081481040c050300400d461f42001d1180011045018020500d552501034811610350000c112481c3c1c00f0b901c60703c1c0d24005072264405000c02c1c501ca40c030303241e04901c07407801c01101840711101005480b04085030f0075000700d100083e1400d0905030142181d00030343c84d80c0c0007085001140144098000021b46852401141440407480444a107600f48111481d1540342c80c42e2180800c3c41400313000c240c2910203001150500f40020307002805030408040b0103190b84c0d40d1070705481b0300d540190b400201d0b0304100080d5040900130003601c0500650100c902c9820b140000380c6030207960258a04001020034000400e4409504450005100514101c448204c1c0e00d00185443d208a5201c00311354244808034880e130600007050782c0203650101c1803505603568402070051250321000300752a0244000000800f04600b800c80840f0340c10700e42c5e40035039540150b28501d080d03094402903604c400e1344020 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 362065359 1250 362064109 362064119
    0xe151f120c050d0513021002031b0d0206070f12050f0105041505210115121a01140d0204021b0d03060609050310110c0610050f060310030209060420090405010e01 71
    0xa0442d803400d003000400250030f4640c5d114166080f080054001c0d00702c9002000504500c0c0c00002504001c06141034143d1240050a0340e00d4842e00d6a141e003e015034082408601c865014144e945c02a101c14541b01a0540d000c440c1079081c0c410a0311044540404030006122a06040c0216600d459981401000e142d1518020440c45c0c00e8460890380c0140d40c04030441c0543d42c0070b41010500066003034540384d5081c1c4404406c1c00e0304005950460300700070360481501e8200048401c030341c12116400e00303d400300c142180512501d03050030001207a00580c20001c1e036100c3cae10301801124100e1300c614000d0841605401000d0304940403074002509200040f4010007941e5000201082c19a03040703107021400d03c3d0aa2035284080c0580d121804081c0600b00401030244403e44100c1d00702d407011919160000610b80a02605110588403941c4100402c841403001d403c04407140303030b009100500b0028480700d5009010f03075242c800d80550b00c20b1450001f0091418a001e00525025000132062020700f9498030f = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 362066609 1250 362065359 362065367
    0x1090b0c070b0f070f0b1e01180b0a21020a080c0607080f070f0809180106020316170708040f05010503070507060c14280305010503070e151f120c 64
    0x503115154000c1c0000030300c1241003c241d019502c45035440302031071101c044075192010003141d0454030350b901103500440b448048144004454103c031a1800c0c00c400b410200c5514901501c13542302ca080c0c014042c5040041c1007240980c05440c80e4020b0130400d94a081e50344100210b0000c60b500550a42d8010009107142e5542d20003141c0006522080141d5515020005900c41d8015440c000e4480c0000c091100c0511011100402180c902250003510f000070005159181b0413007800360a005a109000c0980222000031450550314001c0446000081c02d5640440d01d961240f94201c0d850600414100320403c00643c116001c1d00c1c5c242842c50940c60a00801000c0380a00392001e08001d450f032582d030311504d004500c0710059207203c8500d075507540100740001028015003078002c00d0700512060004180d41c401d2242074181c81000b0040c042262401c00b840ca4008809409103500031101d540c21b2110b541c400340190515102000010492148494060b242c0c2c01da8004207842242071584030319440c0c0d40 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 362067859 1250 362066609 362066623
    0x605030c040504060906090309061101060608130203070305031c0608010209030a081803061e0609090c061c0c030902101d060d0b1503100f0e040611161101090b0c 71
    0x6072030004099071207052003400b40021100107002d0514012881c414168000d80c0042954100d4542042040e4449011400c2314074511070b1030001041e610100d07035100d01c05009004260b00003000c072080307181c8130f841d01170440c0e0041d02404e41f0f4100d90119030b0007090250081100808021000b181020421070100fa1170f004031102c01800003000040031444480c948040040d1668040c00b125001c0c40c1c031803507180107600800c0101040705040c0b40002c05504d040c0d0481da00c240341110141c5820003440041c0082900300c40d4143c240c0300c040062050800840e1701c0b80ea03040740c085680c04929500907005114042c000151604108018030f84104624080c008200e840d4000c1522082d0346e0302151802c0a005001c000e1029501c1580000415100b1041001031401100da0415400040703544202c4c00d41c492299206504880034a4400280410f025034095125502c1080005240241c0090f614030b00c184c207480203c80c0c59000350744804865a12000d0314021b811040031252422050118140d95030074 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 362069109 1250 362067859 362067883
    0xa080312181002070605100509070c0b06120f0c120f071a0d020a08040c0f030b0a0902010c050703060614010305011202042c030403050c150d0e03041a090112060503 72
    0x2010301c0c492000300d000c201651020401140c01c54a032001440e02c03002402060f1040803540343d00110101d690303d0030017411406507555440e12140b41e807060b40d800000c5040203284c590720183c000100054500d043c04844074418840c0082e25500d00700e0002c01c1000c10b00030000e90f12642c4106103903200e000001a420081e6040f140b58441d101d14022400030300b61084080c041005400400d006500c150407040c442d0045d07126800700e0034210389601c0c041e00315a1552101070400c2041e400030402080081e03006450480c010b1400620b254a0394944615101c540d0380100d4200e0790f5210100000d200c00c0d4000b42e0702e09004d00c3c0c180071b02c0d458000c100340c042c039481102a01c61540c41540c5c0b1b80c0304100c0e01c015000311503254a001e4410101c1d1a20035169045844140c405008041c09000c0341c3c43e00000901c0001c40490045082800a2686500506aa11003980c061008000125120755800c0a1071f400702400803085541d16000400104600780c0d001d4242c1c80d150402e68140a00c0d90003103207044000e4 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 362070359 1250 362069109 362069131
    0xb01031104060906060f090501051305041e0509100e010b09190b041113080c01390c03030f021204060e04110c010b190b0f090103020d05090c0a080312 66
    0x4140a00140c02080d0360f60140341140d18001d4005111504130a08001125990720f494003c59a9000150303503912500400f10002c8030740c004180020b00e043c1d446450241d20842d0003c0c1981e82c0e03234140b00100c802c10b81e2107100c0707075020758400901c2c2055402642d200252000003801035000107070101d1509403002d81903c4a60705060096001403405034014001c8000c001d1003030007108071012041c016540100f043c00c0c00512101404100b500c0c00041c40d055150301a0340e068058040015030340e03a280c6c0c810180140004a44e10103810040c407107801200254051081071007000c0c9103140180c42c41d001d20311010155041a840303200100164415542262803a06084451105060000c1c00611144440011690011450b040a280b0552107a00b6020054032402041005c01c0350340d1021001b07074481c0c000004010407001031100070000280c48900010304004d82842c0c81d0481441c1560030854030309280e603208003020351380c626000e0070305002011864040c40c940003a06076410f03007206000b00405104 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 362071609 1250 362070359 362070383
    0x80f060103060f0f05070e040e030408060109090c030507060518040e0d0e010207080709050a05060102191205090d0b04050d03020a0903020907210501050405010f05011725110105130b0103 82
    0x143d00d4101e140024000c00080217640780015010f40300400c64221140114174018011801107030001c112002d0b41d4180c001040315a1805203110013510f40c03000129503001c40902c0010025408021300005004652a840e85401000e44a10809900c2c40d041d24070550610b17038030000088010540c0c400007941454080160424840181d00d40003840e4840f022a00c00c1000018000100303520540c01200000000d004584071200120798500310b415284c19103004080100c1c000407045004002c0c14442428084e040052050000b4041036200c442a56020000400c0004001050000700340b0030945040031070a0001c0800000c05a6a00e0302000f8029088940415440c5005044440000e060309010303418841c1c0080c40c42024140c00e20605002e0750900c2d002040c241c81800e600410b441c0e041e07485010b466901d221807a4034060182c480c802d1416404401c1c40d03290441c0070804e4400c951600c58400b95144040380c1404c40e0801040b51000b00284100d40001400c840348150449400081c03000e01 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 362072859 1250 362071609 362071631
    0x30103120e03071d0f15011704110901080a060605061602040506040209041b0e0102120a03051306020a0f080f04081209030c1506100305010b2b020c060f01080f06010306 74
    0x203480c2c429005800904100920300e034400107000401442110070460031521758498017410408905c2d0900090301040c204490b40303d004007030384841c517031040c041c000180d80500000081108054283c00c0f110882d0807541083e41031012500a05000b408241c415a1502440011300c4d034204607101c1c0020702c40c0e525000421080c1e9a1601951102980180100405a811002112000340400d110004600251402c903802d6001081c2124001250603101d071801d00d035404120010030300244010b2003e030709241c202020500074400f8001c0080c082d10b40200d0305001a0020704824001400e000c5142c0451040100140c070030000d0300e950400c40341c04207007107803180301005040d80034030b068620052040d03020b12a0031075100300425016040644d41070f0f10384a0340707040c200c09850b02400b0380d00039200208424400304160040baa454940592441c0c04802c820080c032070140e90220350301c242c2d10360000c01400070340c40e124540c0a0040c680c01e0300419100780c042100d5030f00c0b08014400070b401ca50361f544040d18 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 362074109 1250 362072859 362072863
    0x602071205010e1207050f0304060c0b06011b0b1e0411090405030714031e07050606150904020c010b0103050709080c22050702011d0f060610050c0d0201050103050c06030103120e03 79
    0x10160310400c2c16502160705016140c40e41740c0014006807028400d101007903d240d01e01200b210151070440e6161305064840f03403140d100700c401c0038111034108034900f10088501000c0038046881240b01c1d00c110b041030b0511140b410148440040c1b4668140311a0051000040b12149587d030507000039607405589035510704003541140640d140c06804c4400004400c0030324440400100011580e080c0140704501701076024020030701440400401326400310b4085110b82c0740505050101c085800307182e500d8079901c00c2c081780a0303030088505031626a44984c1070040e90740c1c06029491b4007499902c0d101c540581b0705003c40d0741d5900702e0a240342c01500d80c843d0307c101c400e03810780300362810082c4100e0901c9913041620000f4000c0030200442c1c5041d980781d84800200200c040b03828039820381ca60b401070010b5110642000920300c1c04204200c244103040001180000e2305100d8400381010b00d0700000788a615504025061a4206a49c54421841000144001003a064500c140d6844901d003665407442801c010034 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 362075359 1250 362074109 362074121
    0x6050f09010b091f05090106050a03060e27030903030a05040503120c100b1903051c09051e042a080604020703081503150c070c0f0501050f0304031b1119060207120501 73
    0x903801070712146c0042082e41d041001041d03004240e5804100c01a51030410b42c2a0f807006450000340307000700120521150005c0916680e54100c0b80c000e4a10703240b0200002480c55206440402c04140e000c107040016281c203000040001d5104030b405842c01d9030818903c1d8481c1905a0040440c50b51440c10000d10388030000e1038110030130b8000ca1b1118083c0c803420010703501e40c80d4a400000d041c1d808040a440d8512407081c40c0700702e660241a42c510308408802038040f42c0b40c11407005401564440f20f58821013078041307440103003490650500850890124008010150080640c2d000e030340100a51800a5445440c1e2a8425800020030340f0941c0310744000f83c100080000049401f07020141803142d0014140000c20046201e420681401f40e641c81c082a200c00b49489000d0100f03109100481142808100940d0301030b200c1d01d0002e4100e11040043c420b84a070102d0150b4a20f113142307000701d030b440c104000141c0c06010f07486001400345241c40c00080d940d500c1c07400b6110f0201e454894240800900350003030 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 362076609 1250 362075359 362075369
    0x3010e060f1b0703030e1e120a021015050307061803020f011b03030c12060f0b030c07060218011409030601180f020f0309011407081f03050a06050f09010b091f 70
    0x2c42e600c482608004014101c954184801030280301d40084038105e84804103c610031140c4040e0001c0c000c0083e0541894010700c003240c040d401841c0c1e8a0f0010301c1c2600c80d54040c00d61540500c0040c5040009041c6480c42c41d401010600030021050341c00314004418000440740d045403d00c0c40480c148004903003080b45144448501c00c0503041e50010550150090307007011015035aa82103545a00b100e003419916140f00e0941d481c0002d5030306211100c040340080d40d0100440b4000307880d01030a039480d00100d900c00703000ca070720090003600c88017480d41c0d01041201e10703c4074500c80181046c1100001a0315602d046c0f25140c0b05040c072013003a100115913a04400c0341500c868030b086454144100111400f6070044401c800f032540780144840e2030030703681c100180c00380b1400c0e41d400e491696814240d14054241c0c8052201011b80508000000b030000c00c19011258811031001c038280c10f01141c417110001000d0700301c0d041641000c17156000c2e0f803140b0030308603841200407401c203c800c0c15285030780c2400802500b04c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 362077859 1250 362076609 362076661
    0xa0e0705060f0711132a0c030917030f071b05040501030209180c0a170c0109060f05070f0c080309090c18090406150b0712020118030302090406080303010609030b0603010e060f 77
    0x8801030b0f03100007041e00031070086c01100075a4060105070040700c3d01c4650072401070115404880a000107020100c00c00d070448076201c100c91510b49202e20701081900200d0f012512031208660304520150b400ca6071a00400e010f95081c0600e506560016201c50310041c40035106c205001d030714005085042150804e171440c09460040d00944424403e040c2e94056040c1c80610b1140b04e0321045036520440640d0110b131000d90301d80da1740302c00303952003158503a01018040d181c5e09103001c1d0117030100c4c0c5074004820007070418000842c1e41e51076500078408403030030050150403001d2060100f01203c0c1c030f03000380b1450000004c8802800e1a5620307d05100200f042a6640c0003051203007102151a400c0c0b4001031410341e000d41c54001c1c15083c000022400d07030300300071000403032000114141c2c40082c1c02600a04030000e070060001c500503485074a450319640003640880c00007555964104140109152441d42000d025002170161944826140c1c2e69000c0141040c1640180f080c0007499117413060f40c01c0d0074400e4101d00 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 362079109 1250 362077859 362077871
    0x301450b0406211406060f10090b1b01051302060a0f0c0b09210403020a05060313240e0c060f030907030b0103060b010e01030b030d0809150a0e0705060f071113 70
    0x402c56690708901081240c201408541c401312100000442c00e205403001007298440c00403020500240180010b6003200f81700890f400415035600381d8014003a0a02d070b4500060b01c420a01120500303480000e00042040c940c1c0b41c59180260301c545d02190200130b280d041501140a00c20b2003280c82c074000d410080d1211000c1c9042c428030b4440400d10880c401d424185003414003c0c1d0710748045061040d032000075840140b0003000c0100341040400b55074000c10701c40489010007181c3d10744401000030000c7d004401e07103405011043c183c0a41c171604124141c800001e041d0308011030081041849003200600350410088005004900700b003000001469015850b030545581d2454000082e080c9068030501050700d040b078200c0254442d118070301325050028020200360b4603850081d115401c1c01703441c0c481140190500c06000c010240404ea015034252100080e10b910390345406030821031550000c070b208001c1040040c01d042da0400a81d05a6030700048102c1640c01c01074000b69000c240c5203550a11b00f0b040031 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 362080359 1250 362079109 362079149
    0x90f030f03040309050a0b09040504060906090b040b0a0c0219080c03040308120112050604020904050705031b090f0910020d0b040504030816030516051303080301450b0406 75
    0xc0e01442c05280300381c0300c900e074241e01c40c8200603602406001d0b00f004110705021008451416402950308180610400a4200741d103403542c500f51000c90308180d0701d0001c0d03c01030008000300c2e4524164000e81c1d002c03003084402e80ea50002911000c0c08000e00750f418441400d050203000c001c2c030803226081d409c50110f940d900c0d628034054070b407a003101d1604440e5401c3b1500000d2420b80c030001d060002544840a00030b50760b00c0303070308022070240d0140095550f4410450003040c03c0d00c0400140b400e803032082c0003d050040f503000070001c21200c000c1c505001c0401010074003020800014000a148048000250715032051406000080100c1ca40580d801420802440103041d00001b003940650381c03c0309020f03800400c06c1000e40607140103540c154007039281410252215031284020b40705118591084800555030ba071182c43c02e6030070030303000b040149040d4080340c19180703140e41011a15a2030b0305c84c90f50341c11640380c2d00b0201c174071980e0300305c41121525658038481c5c1d81d903281c2c4980b010340100300074010118112 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 362081609 1250 362080359 362080387
    0x51906140c07151d0d020105031b130320220908040f1806030b1506040f0e0619031109071b05010c020c04060b180d15051501050901090b03090f03 64
    0x710010700045180880c034840f0b01c040100c4441450100540105d03103007152039004448680c8000c01c4449400340c146410303845030b80000000c12280c1071135030081d031280b800c504003009505668050900700c1d10030000880c4060300c6031300ca64081100c0401e8101000d058020180010304480400100f10440008000c2513120381010284152020042a0404000f440450004a401500001d0064481000041c40c1c00004035461822144050309150825a8a4003140e00720042c40d0412600b4405010811009040024507a442c9104086003600c1407451603c0705040d0f8507914013450b024a2500b0000b42801b0300400f0b060f1030007600e00c2c582c02000b28076400c029000f80215002140180070340348003c20145024001c1c18241c50692100302e190500070ba40751000c2c1034406400540003000f034402400410060800705001c1c804d5201c000c155468105204440c0180f0014a207050000c02e2021100b07690340071031340b2070a030f40a5030310803603594441001241c94141e05082c0180316210000b11f8125141d0a = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 362082859 1250 362081609 362081639
    0x19030c0c0e07080c0a02100c0507020913021203070b070e0f030d080405100c080a090c080312011406030f040b04060b060703120c0306050d0b070c200a051906140c07 72
    0x755248261922a0b51302c0b948288121000180141c0c001a00d50f50040441d5200301340300601410300b01d24208403580451341d684811036045202103160315400040d4144002079412540f5610302551501c0b403d07076101c0350703a008040c01038000c01c035000d441c0b8051910744c000225905580103085500c000b0b044030700109100c0e802c4a08995900501c404d809420046d0b02440b9040b440580b1018a690303944440c0c08020b001c1d826058a14845070301d8001001441840100464001c48101c00950741c1016600c0903043c2d04028614001d00040003007003c113205004400c3c1d0010382c8a03142a106440d00c0c00d100c006003030408407040e030200d400103a803002c0681124811250340d1074031805120f0181e0f2003005074201d0345140303d96500144001003000000341c00429542c2d01c40f0003401d21702c1c520081501e075035600400082812000341050617028402c0d241050001004000c1251107545103000180710070000240c80c400e01c1c090000d081d1a03025a17411040540d0002c0c05420704451410b95514802540460 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 362084109 1250 362082859 362082871
    0x40e010219030213050105030916150f020c010504050405040203071a090a12020a12080c0703060b031c200c040e0c011404050604260d1112030919030c0c0e 68
    0x75400301d0701e4801c601030f009980d00100b00011103007240745000c1c01921181d00003818000d0901903031804032020f034005601390001d0148104400302540c80e042c0040d040305081c00b0924250f501021045126a030b00c03000b2a01500d405445c00b0800781c5451011a02e81502070700400190100c0704508500f5860f000301400c01c8440c00c85003c1c2c038440d500c01c0c410401c04111f03507019410070340c442400d0061205c0b020a4030703d400c0c4070300f0722207150440820030681062201d8100310354103521200396000500c7d04201030080c000c00c43c05801d0144040f03c001628a010380f240c10040481e03a1940c201c0315050500002c000f42030301500c1488079000c24030341c1503103d2807405406070102e41c8a803220030a420042080c0d8041d5440030346051300c0c20381071441c1c2a0501c00c5030340110b00310141c3d903428414184c5d41030114001c0000d01da259900602d00320714003e41410903040b5402075000c8103100b08074040400041c4c507000003e400a1603207054600d400c044418012070a4083c110084820380090701890f00038080b4440e203 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 362085359 1250 362084109 362084137
    0xd050d02010b0a0905060303090103020703020a170a08070503070c120210060e01030b1003050c2407050106091b0e0603060604120b07080105010507151a13050916050a06080a0605040e0102 82
    0xa5104c40134032084900a40b40c00c0d030190710500040c07545501960013025918000e004844040c2065500c004c0c20034001c01e00e08961410124842c0d100c95007001500d500b1080c035080150452402c840014801d00e0140700c0600154504641502518020f0000c0700305141401c4090042586405000840150a100480b40503c0e81800100000842036800003581d5121000e4802c14401404114012040d004602201d140802e40c0c2c0c100c001c46031005100c168071450001c01c0c450714001a50040710080c60303061540e402c04921f03210000d0b50001d0360450b84002105c01980741d80392640851340b0b500658014018000d485004d00d0180710a0512181c41141c10350348040d240c0e0380310b1004407964012024014000c10125000030043d03030460700442083d425401150111110311070000b028040d1265220140665800900480010070b0100385600200c810301400b810340390502140c00400d10340300c3c0600b004619800315180d08a0307600242e0080c500104140300c40301540c81d8090013507200c0f2900c52640 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 362086609 1250 362085359 362085379
    0x40b030105031002040501051e1201030b0f060a050d2006070f0b06030a0f060f0e0607030204060305011203051c0e0d03020405090f0108030306210607170a020c06150d050d02010b 78
    0x100f50088038262441030351404d040c803201d1010540d101060003002e050301031040c08917180300184414518000d6000390000070075030401d10003104240501800c2140100082c4e402444640c503121401507a071544621080c501d1a007041000703105200d001d0315258080310000c0c584003406500030300c070701070540251524001074883c8001c0558a5109000081503484c07082e10f5440030841c254007080070000c0d1084041008002e585c1c0090800c0c1d411648500441e80c04142440180e90620806000d8211100b5800c8640015140505140180c40044451001004c40b0303401e40d482c1038004a020050640841d9a075603c2201e002d0040d4000d801403c0c042c01c050000950048810381e025030494a00c9000f071842d684414051002c00440c1c103990b81000c0d03403000072052583c7d104011040c4104015a103070b440c489480000c4541032040a4060400d00d80180403101c2c11110100b8800d402c0b2064030007070034100c079003913002c5465019501400b40a82c003641002c2c0040c1c0b42c040d08890a1003d0132540f8040f4 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 362087859 1250 362086609 362086633
    0xc060a05120c1e0c100f0f06030c0810020c1b0109181b08130305030915090606030106050915010f0e04050403020d021e030304080904150303020f0d050304110f15040b03010503 77
    0x260154a00b40c0b5003e034402c02800190401541c07180380c1b600000030000c1190024400090b0540c0c049500c2164001d450100400040f90203120381703004080c00390025840c3c140c0102045a80318100204800d0b410a1104045404d070301518044000740565000052203801100140d0004c108284408000d038000c42ca1400c1020710070340300d00c2c2c480c40c1e94406001185180703407030480302c42d00000c1c10303c8414402c8400e8504280d9843c80d44a01c5044854001c00e01c0c2e24046040c1400d4a50f40ea000030f00412400c410b10484040c0483c41104588003840d00e00d860455080b0100c2d500004e840c8080d401c58034050501040c540d0102d43c205030061180c0072146900b042c520030f0080710551560141864000744003090003d51050014040d103000104003150080200300c504a40045907407007140540e01400000c4003021092001e85e0b07020840e030610504502e410b0b25100c0e11100d40103d5503200d41803803015a003040c1d5415450101100b101d400e056203944d254a00240c0603407080c081c10744640700324107030614 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 362089109 1250 362087859 362087917
    0x50c0a090c02031c0204050a080c04060b0a050d11070b0a0905210703050c101d0622060b12010203070f11071d07030902040c050d1d0c060a05120c 64
    0x15a0078096009510309000400c405107100303400c614a950041d020840083e581c3d50b401441000b821360302e00a007001d1124842044100d80f41a41b085c402104d041c40802c580c1078001c0d00b6510401403090020406080740710b2a0555031183c82c400a1240890754107000c00d0a9140c2d1101e0141c80c440c4044900003140c14006000c403a907100c01c1c0c00c010090801000e80006d208101a02c8151588001c0340c10f038a11000101040e65102c8504140755140300d00e02c1700c1000703c10020250004010480800c8411400403244031813401508083c0140341c4074003024540f51540c003d01c01201c60100003c649034100004018843c0d03c08039602400034074140c0315542401c01c041426001c41e4000001004a4480803840c00c80e40440242050145650344a0380000360f103990262018406071696016030b21207100503643c0c103e0f40c8060032900c1c0e4610003c90440c41d1800003a080440c0c80c01120102d8030354280c040211000d2055010400c903a05040c400e211840016001420702c2803140d10043d2140c1040881380c0d0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 362090359 1250 362089109 362089121
    0xc02010501180f0b1003020307020709051009110904110405120c1c0302030d050108010f05010602010e0d050f04030c0b03010608130b060112061d01091a03150c16050c0a09 75
    0x1903140724852204212010307043d809101e0248880e50081100480709000800341800702e10110046a0000f0400a2090303040c01045d01901d0061000c0041d4240920799425048071030041000b013a5445044401c1c03c0c00d10020781e00750355001402441034a89900150f44550814030543d4050401100b255001030000710703010f01810f41c068a003004204000340f42d414040e6026000784c0c25400104031443c07440e5903030701a150203004000e00228260f441d880c040c00450714164031450840e454644101c1a0340404909180552424074016444000402502a1500c6141e000410a60705020300003000400361010790b04031003458989010964400203603442801000d40010803070303511400041d101e903009404544004040403030008071103840b04520030564804a1800d015002e03a9401005405154058000786100d803518001c405540500400c0d5100b045168202c0c2c80d414200004a42045600c00d4900c1c51400480d14210003405082698a0b1154960424002d010084001c00c00007440d000d64 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 362091609 1250 362090359 362090369
    0x506040614060a09030b040b0103053c10090b010f09020c0706140d0509061501030c050d050a110708120a02090108070e010e0a150908010c080c0a0306030611030a0c02010501 76
    0xc2002016030400000c0d0380b100f469101070112041000c00400ca0225200b8071461141c01c5e421115411030501c189448644201c880e040101100317000e04644064032000e0b03c0070401d40c450103400d0070540303203513040542e01145494050718040c41d150620030f9410390b80e1f04880200034a03000d1647c0b50885281a03114000891490b584aa90200906445007419040a0400015450400740084000302c02d890302940c08941a5101c20180f080e80f16200f542c2e82030055090904024401404030050024028109d07403040040e03560001542000c403a41064000d0440c1e0380740c040e900c0c07200c0d03e03040e1031030b8010800145001041c45d0000301000c0f10351003202d282c0070f4145c580040690301c90808440c44040b007030029040040c0340032404007584960301d605000d460708908695081b502d0800007440d001e500d41c488091a81403280000d0880c0d080b405068100900c081e400307a4075080d640c002d401030099507200415841c0782501400d0040c000030301071b501960703c5602c1400340f040303444012826a5028064 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 362092859 1250 362091609 362091629
    0x4080405060307050405130903030b1206010909020303071202010507020d140405040518100b03010e03181908030307020a060b090622180f0308090a08090d082b05060406 74
    0x500140c54580050b5a0040e15490818076007901c0c0d0011642d0b0a48800684c0000d5484407030b40002c15404d409072080b506c1e0305940c40c05641d02590040790756074a0600c11010095a524180c00554809000300c0d080030360400d40e40d00c4004d400700c0f4024001c0c641203548400500400501c00c45c45442180301c1c03d204209846010300341350030002041b00421014103964114422041c1c0003c400340103001008440585480c0004d9040301c1c0f20034142515a0000c60b0007182c0c208000203020070b0700041c01112044025240003143c00302c410010200241c030364108044038407000c005c00882d15400624400100d00c5610280024100300c070134400c0c403520540301c0d280d00c007510f2034004000040380c001c02040c1700721880b8007240c0a40c50800d002944216807006480001e0942e1001050540112000d03030401041c0c3c0042001071455143e003c0c242c01240021445505552492014801e1079426210314000550b062015079240840d0140a2844e0340003510046041c2400203c0c2480e25104490171100f0280e0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 362094109 1250 362092859 362092867
    0x61608010e060a0306090609052103040b061801030b04020a060c0302030313031e1808071203080406060e010e0f07030608030901121b050d0b1e010c03020c03030a0201020d060e0408 79
    0x341012800c00003032500b80c004440c2c01e0f0020106601c1e00441d000540a050001072000301810142d080541c88201500201c000403850040121a40222a4800c0c1c025802c0c4585881e1300000070350804d172460450381d52031100c02c00441803290304131407280541e02c21039101c50030300c1d912002511105500d250103400740e002803000602c10072184020303440f8140709107066003c80749a40e0745441880d10b01424000040c1c01882c162201003100119080984100c000400344189800160540c80d00d014400034108039080000c5010001140c202c24045c044040801e2004c3da1140040c0103122421a00c12501615200100d00d166000c1e1041030306440d42e61010354942900f820041d15415541c103000300183e0b903190450800c81062424101185503965686542e4441d4600144281c0e80c4840d036036841142e280c00140f0000b0060305000c501100282080c0b42184641e040c242d092030200c0f10880e4141c000060f00f004003a40c198006c00e50800e203803004000040e242e031703031800f202e602c1110020300c0100c1c100 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 362095359 1250 362094109 362094119
    0x20606030c0d0b06030705040204080c0a09060305060c13080105011203030506010806090606090d06020a02010e0f0d080a110d0609020c100b1c150c0201022124061608090306160801 79
    0x140c0159004c440074086405c030039500c1010400702d9200340d00c8000140c00c40380344800b4504e881005c06000301400c0da001c0c400141951907550301e071075000c3c014201c420400181000c0810b1640145c2e001050f807040204030b04e607902c091301e0107080e07207031607080b000240f821001841543c000d0089900412000d00007100c0c2d0355030441403040c503030300c400c91003039011a005035490005140c42c0010804402d045e80085441c207807582d002da24058071001000d03801e41014510940680c0c2c001c0805501c0444080c022a1348903150b0404c0c03495218600c03400d014030303040c008007080092840d001884c06909050844190100e0b20716403604031001001d04980c030620f4140304903540000c04011000c03490203090210020400c448070503040340c20024000000d81d40200301700300c54545041d44c100d44640c40b04600075072880d140191540c5480700c0e1100c60b90744100981420002c1d1900c10a46a00c43c24001c0c040c240c0c1e113a2402c00700d410703801050040b40300c0e01c580d000140c000074001f0840d91941c0b000b41c0751b00055034200 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 362096609 1250 362095359 362095373
    0x110a06050a110c010e071a0a0f050702030109112418030f0f06071713140f010c050903010c020f0a0b0405160306020307020705030304050a03030339020606030c0d 71
    0x80c020081040c1c6501542c0040761074074004062007036030b45000058540322009128208150f603031251030f40341048520040101500011252050160f00d080401c010aa4806507568080c0d840080c2d015881c00d158101000184000104095000c1f03440c0c0c461540c0318107070b004e0b4025403884a4540c181091180e2841e0400c12001e4560403800242615203100116803520711700040010f200c800c43d4401c1e0180041e0350380103400d18640c00340c40c1c140341055241c80b074441c00d190001300e94024a44100d04e16981e02c0c80e0320502c414050706800c480244203241c000b003002030440c0c11110707036540b0075440c00a43c60902c500018031002d8554150b005814415240c4d100c0030041c18000b0000c2d151402417501c6174404c03e05d10b08044020b10f118910043c2c072814407400007407404a040d0032032402584108820300940e5140e01460017100e5042c076020270240308420400c0d00d18034000041c4424400050046c50100400f1000e0920750300242e822a4411740d1220109540c0b0707444030322819007241c00090550046412 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 362097859 1250 362096609 362096611
    0x200405040f09020d12080f071b140303070f021203060d38090d090303020613050709020403080901080c070b0f0919200d0c2d24110a0605 60
    0x90301d000088101264000c29007805007120300729540030203030070803118158101075015002a08076541d940300386001d19018200000303030b0112652403040b90001d0801c000701310180011503603d0100307494032414103040c0900385012411104015008000b1030141c4540107006803440b40c88010b0460b44c0e020b001c0c0d1030705142020741c6021440c0f002a488000d8403201410384095020440d805044106c030315100d00e0729401e00400d880440200034000b8403c1000c0395000901c03940025505050036050407030703443d04615281c5240d110344041400410000140020100941035801007a00c0e40f0f10300b07540d5550429990300c0f4240004101c444110041000381c0364075100f0603402007903002240c100c00e0810189a030340342c040e003504131a61b01006509042210341c52422070750405098802e00f000794582c0d0b690181070019030150485621004414100d0000c0c00c0c103107e005c0e10160440700c085543c0b11002d662039151034060300c000c80c65028600c1c0803c0d030300c6071030210041607040c0c02a200b41113496440701c002d894 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 362099109 1250 362097859 362097881
    0xe011a0d0c06111911011103180103181a060405010614030411010c060914010b030c0603060d021909020a02160302010e010f03020f0408060f09120703030b0303072420040504 76
    0x4900c4076030b0090386000580d900303004d6004070452140c00512400040c070017075801d0b1031002107400c02e00c250448c50040c4440020300c10004d003400708250000602406614101c00c6000d0105402e982c5101001c0320310390032030303805048150b44c28461a80c03100710030307582151411805c804c804800c200007404038015410441d078a01c8149445a940c07002e980346d07502a9032218506507509100b5100c00300504000b4841c1c501c0300301081c0c01400780d551440340090300c01d02004280358003843c101021502150f0711051028400c03917000c40c0101c42c0603190500e15000350400c1d4400e01c0548106000700c00d00941e00c5086904403075059450911904d00c18004580c150740e00d01280003855020310036000c0e0b044210020f00044d05222000707004c689810031580c1c00542c400307440c204072078000030b180d80b03020361005040714603094060030049400c4d079012001c20300d180305245001d80500700400010400c3c0c201c880001080d4440070606000103004049800d145402a140118030503004110810450810340c000c004404 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 362100359 1250 362099109 362099113
    0x1b080d021303170403051905070f06080a06060e130f0b040c0f090608010b0403022713110402041d0408040b0a030501080606092a0702060f130905010320060c010e011a0d0c0611 77
    0x5689074642d005064203038022f080400d0090041003c0036400d0321450700200700510f490051540180040355108901a030030741c5400391130ba029620040004d41042c0116800644100840c4070100070081c24502c11217856030028605000006071681300300e0445041e5440e00c01182d25182c996403c019001c503140c1a18941302c07408060341c8111500034030091307100b0701d062031f1045074418140c0751106280d41815641c6120300d00c107210078040c0341306080409125a405c4600800700e61070701e0600041c503001d15070209618960019405e82000d80c1134204504a58020048403000d4450b40104542d000f0110740103588840b00400b0041d6411107484040c2e004016480d0552418010b900480d03401e84c02a1904203082d00e00050b0f5150101040820400904c0c85040800081d4115a1500d0340101302c800d10140c1080d941407130406039540c440403900082c592400820004c001c548000c1d001c2c000c424800400503500c00c4582d65942410f941c0e40c281d259003c804c1088450074200180d03000c3e402d0303540d003414034 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 362101609 1250 362100359 362100373
    0x6060112020a0e030d1e05130603110c030a050d05181b0a030816030e1c080a2c13230c041e14040902011b080d021303170403051905 58
    0x240c0c80505c00705482050603551501d83c0c150650380f42c000901040c0b1244200401000f10381c0d180140c0014002c241c132118a030220f132140200d50200041d0041000c142c040b4040052907060143d0840010840101988010700083d17440360440c803005e54102407404940d80040d4184030071200410200d1071071751b50003000440483e440b901c0e000201d0b0054840b2180301740704082450113141d0440580701c82c030b29045031000340d0f01510401e00d843c1500714801c020300c1900041442400c540c0030305866080c48181403101c41c41403400c0741a1607c00c03640001c015009041200700d071420204240129080d0406208041c040921441440e503500d0701d0052001c2c0969200b400301040c4254400c030045004201c0b55846114241000c01080c0c440498500030740c4194506240100143d0f0400c05082042e06c03101040c3c41c0c50011414114402d10501908601c00c41c400941c0c20911030810b02c00d00243d83c020205000080d403003081301c40c114031950001400c15400f54203080390380700b07004601c1e10a15108200365012 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 362102859 1250 362101609 362101637
    0x3030d110408011a040501120201022e09150b0307051c0804120f0507050a0e01060503090a05070b0a021002040305060112060b04060303030c020f0109120e0301020c0f010c08010806060112020a 84
    0x21500c600018000c04860303010450980e00d031a015880c094040340c0841c601445040e27001031358071420307480840d407144503113001400040325240d10b04841c16418441400301110034a480603030808814044000f451604145503007030b0400050001c02d6981c054504120590b00c07140880405510080031590100c0c1080046944485050b10310002485003111104992803440c049040901d941c004e40d0050030043d404200381d003070000c0140c2c1144d0141c10115036a032100440241040442d0324003038458881d1034400540343c1c04c0107009140808140c0d080e01e00d031000f141800020ba2240c0e00c006401540440b00611140c030307100c2102e400c0325102d6a400511444120081410b0320915401600032940c0d461010a81540500110317091480840007084010032a90f6071070b00082c14903031404100581c1150134403c41c0c500350704a840c0480018215403c9800140509020f0400c0418050000748480000100600c00040f0203010302c4058640c401c49140206034070009400004184040095440010380 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 362104109 1250 362102859 362102861
    0x2030312060a06030504080a0c1407081b040501030c090e031b01021b0c0a150212030c0a0905010906080f0403051b0a0605060d03081605040e010e0103061a03030d11040801 75
    0x90580d041205030141490400c00b00180d2402a501242c02d140c10b080404c80001d440078101c500e420349906000414540c542000703d403290380444500c4181c4a40b20020030f039142c0c0056108000340d4840454a200d0402c5000d000a4800a11000b0604402e550041c00719a1464001c0e0290000d100101c0f820010294044940440c03a8104202582d50000e44c0c060403800301c076000503440c10303100014000f00301c032000494031041c9070388a0f03140403141045404031014824400e100314000c0082c2499100e08221040c14100d42c45584a480842c0c50703448005a103501541c03682d0100c0e2074580350707100159034070301c62020740300d8000340308604111003001105082072803201082c0054420800408900034549056000c03690f02518070b600c80d819010001d00003036402988c140c1c0c803040100750440600c0102900b920280103a422191001c03c0070b9002007044c40d00301c40305a0490340a03840c00c2c4903100c40b113159002c8400b0700094a07500745d081081a2500081180c001c6002c14011805161600e550340000314 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 362105359 1250 362104109 362104117
    0xc050d0c0e09011e0e240604090323030603060709080d0806030c04110913061202130e060f0405120310210501050a020406031d0c0d030e1c0201120606050f090d020303 73
    0x4135120b40c0d650380d0710341004800c0028041782101141d05e504074048500f1004d0341207000516080c4100d03102c11030311081501c5161030b81c0c4000320105400321001c0121103040c009800859501703000b403281c040000c10b44c81c450500002203d07826809000501d4803918111382400c0c004041c1c58040c03094169200058030307584525225003c0d0000e006071141c02000400400003103241e000740000c3d0428500388900f804c5070000003c180d5045405801c130702982400c3c0405022001c4001440303009000c10040d41c00080d6042c10700c0b0314070400555400b62450744450403280030544100c107003100f8100081c041c80102d00800c0007950b01807504104502e0195a030103081d034204550300381000d500440c08002403030b014040c401d0308209515101c010a400e20070801e82e24805088410320039034800320300700c003170501030755094000104c0908001d0f84402c030a0019003540c20702e400101e0004581c4403000d0220710300d600c14002901e540e81d03510382c9841c400900410083d00105000c42c0d11803006001100140e60400c020 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 362106609 1250 362105359 362105411
    0xb09040f0506060a150f0912140706020a030e010c050f01050a0c260c09150a091401020102130e190f0b12150103080d090b040308040c050d0c0e0901 65
    0x1000e4050418544282070032809050701c0d01490352013a0510645d032030440080c46180e00c1740303041d03a0a0b4451040403201050035a11003030f91116654540d4080c4000c89e4000615100308900310f8424039a41c00742265180911341c006000500c2c0101c59228640c8504015030069009208940301116103154240c2141c400343c03105000e036961000b2050b480394001151456443e040402030084072102c603480100c86034010000030a120b40050304000740ea861382641c2040c0c2006840c541c1d00c0c2c90001c1e00291001c0642d00401c04121101d003403003211503205001701c50101c4982005411700341c1c03611000200f640c02c0038182c150841807480384541c80703e40c3c501c038220800303007a10404600c1c0d001107020701c54082d1034010b13441343e41d0708240400318400002001150459074440c0790350396207a402410640c02080c2500d03009200c0040c050900007490f51200b0154065070040c3e50940500340c0d80c40c10001d46544c0030764014411100003208010501d0b051200c00d61210708000086101c152212100e51050100545 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 362107859 1250 362106609 362106623
    0x120305090418120e010201050106090e180a0c03060c091211010e01050f0d091703090601140105190201020a08061c0f1a04080408060906060a09150305160e130b0402130b0904 76
    0xa00c030030646e0709010f01d500600c000d0401e82015400d1501140d000c0302c0c001d03d00808420510510341100c2c5080050303106035504004010129512854a00c005d44804403c200c0002e003552004185040b0a40c040801940e00c1400714441440d03410040d030300000f10350710081c103210f420700c401100d43c00d0210081c465541201d00015102c4d011f40340148148103035050070718411106100f000104640010380c80d05403088004120401c40701100103c5a034820002c00d440110140010004c03034a03015006451f0814150302d440d0107a44d600d80c01d000c1e0000700d40c0010b0740c0b800d905900800c003003180e880d0a20746107800303142c0301804c105803d010740c207160409840450f4000c1700098100f201040c1801015040402030b005450242400da0000311a80705a0181250b4182d540d1800d21648800000350380c0110351000c242d50002c04105402800c0e09083e04c5800b0810140c600007545030384038014090500d946c01104603410b5111078007403080c4141c407518054201d6940f01c0004055603510700c040341c411445007207 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 362109109 1250 362107859 362107877
    0x80c0703060e0a0503040e090708010f020414030d020c060a03020d0e070e0c03010509011403160602010507020f0a0f141204090207150c120f0b04020711040612030509041812 76
    0x2401904860200d401d20307078290020081d5000091340401250704441c00c21140034070b1074032509561814681642e01c09071481d8039103803c1d0280c00707001d50081e108591101440040f0354a800050545580101206600581000300840e4940ca810070141c005189245001810000c102c00c61400301d80100300605080e41c041481000440c91132910ba642c400e000b452075034115450513000c2102610f041c006e0b01e2403500800b034031080b00c0d01d081201582500351001c0000c84503540c0c45002c1d008220a486d02d030014090304004440700600003910140d1b040d40301441620044e60350703c800308611014518204a030040c1003070b0381c1c0b0b1303800c1c07203009000035100390400180c0c0c64460b841c2c024100103a00150070440c42c00c145040d0381c204e8002820384c46456060342c004c5441c0080840303a030010150501d0703042c3d2040c80841c21000b4040c0302000300a010070156000c20840f600ca100d201010b0042c0b00004001071003c101e2034031036040c250810504102c1c0313041603001c484603513a1880c2c0040c0c0900346910000342601 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 362110359 1250 362109109 362109113
    0xb04060b1503040b07030b0907090f05040e070b1e04030503040e101409090c030f030405040e06161211070303020c06181002130312081501030506060909040203010603080c0703 77
    0x44640d03906003104076540268881032071101071242c08000c2018100d00500000240c2c4903001c0d8000d02c0d2410b100800c4462103180290700a404e1800d64001d40289200c10039020030a8101403141c01d428000e640018551140303813114404890b801036540005803c6a52402c9142e101c294014101440c8550051601c0b03c0c108803400c00c01c800d009151032118130710003804010b1051424012201010150b0341d0b20810b95410080314500001365601c503406118820360481a040040702030015940201c41c01d00106c2088508655988400d0740c48142203510b039001100c0d41c1340221700c0e000c89194500d5002c01c0d40301818160080c0c5400800c0d043e800720381c001512035482034084c00307555400030661500c0281010351100c02c40c0d440c40d004250194481d400107400c46501c11856910000b1035004510004980d40285c000344101001c3d04c01c902518808103070107065601038041d82d0302c2007d002c0c04a80c10103d510f81003158a03c030190040e41c243d50303680401302c0440c00910080040004040060070140c0c518 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 362111609 1250 362110359 362110361
    0x20a0f06030c0905010e01030507030b0a0b09040506030d020d111204230315010b0903071a0a020d0e0603161101050c1c11091921060507020c1003020d0e0a0b0406 71
    0x2040b0344108028240c001888180e0300409049101c940c00e290001d02641c3d550700913001424000d03425030340b04100002c00505400c07101c00825820b02c041d541400b141e110607061688e1120211190070150b0080f12015540078030448641c92910121f004490007822081403c660b16480360700721400400c55802c01001c100c0400d0300915200209030000c0a02d46160300d894401e600341801074281402002070b010b003065a0800400300034280c0c5042c1c6112084a0b4403038030700598805455030002d03002e990700c1070f0b240392300030442030700c3c24030300a0011451130f5078442d40103000341d0304400c5d00340034445280c961902422091040030321030500858a29940c0e921001560314407242a070084e0495130802d2142c10040354410140c51071160203480c024100f0780d00e01c045521070902500129048802408001700034264921903008803409040c04210715101c00368101c2c0ca0740d15907403050b83c00419020f104608d0030721030340c0201200d00e940b00c00014002c2032101d0903818207840b40c0c801d5480610043c00c1c070082c0101 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 362112859 1250 362111609 362111621
    0x606091f030603331505040203090606191a030712051f0f0807030f030201020f0706020409270f060b131e18080310170f1b030a020d0c03020a0f0603 65
    0x31420605080041246413100c0d0390849000b8000880c1c48520505c2103180415076035026000c010310035503d928090700030503603031541154400d01c50038012441080700007031041e903001038940e07541d40c0140440c01c00110020550014200d1820070240100145401c18240306040c000e642d00300f40045250588581c02441300100d40000c00e851034048401c1080e0440012800100c81d0310001180b448815410164028020240c03e940c800a001440c1c00400442303074002c005445510000300a0a54444040c412040715070860743ca420111160f0748021981c403142c02200d01d84603901c04201e890000000c00c41c8420107904114085841e170301c1c1200d030081c408054aa40d4103882401b003005110b070065440134048210342c054011400000030801920456030040044d0031816003a0a8010351880d500d0340c3c2d007039031351380b007004074060746141c2d8026000000c0c5040c5490802030042c003059225400300600c034850b5030022501034004030000801a107503804540020700303183e100d5403580b503c0c1c80c1014007070303d40e = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 362114109 1250 362112859 362112893
    0x80a0e0a0501020d12020c0f0a1a07090608040203210901030506030a03020c010c0507050a0b0405090906010f050f2d0319030503040303020f0702120705010f1103030606091f030603 79
    0xc1054014400759034009044028401c2da840d0480701140c001062500910032001800c10900800180440641000a04181e0b85100e6000300581c524000d0507060b0714002a100c0c000010b428840030041c0307500c103d070440d401c503000074162807052000f4001400c8400d034007036502d465440e000c07503280c04643e0540f18241e88100c0c1a4090101d000705642c0094941c002c5000071414005408020414080200040700103888003400848141c0c0e10b5111070030b078517082481940d01c21400c61000508080d130119401c0d040310100d641484801b401c1c2020072a41d5612104401e811180d105a0b030b205000e03404441004450030400185058030708a000c1c14180105010300200035649418180006a07100302100d5100341c146c50b0068070f03104d0b003107101c0072144101980603500c040c00100b9016104004540b001c02c0717900076268000042c0c1d007580c3c1034404c0340a403903903502c0d20b400502c005909800d158004086076100240075001d4682d4a16145ca003140c10300e40c40300c0002e99101014420861144034120580d9 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 362115359 1250 362114109 362114119
    0x10c0e0f06040f15091e170d0e06180d140d020a1716080c251809030c0b010b03010f05010302190309151a04051b0a05071707080a0e 58
    0x20f042c4181003030103080714860080000b1211203885085031048040001811036400e074182c640c0c0303020420b0004841180a10904005c049198404444002a504921081136180c030500c50352801c04015254104290b4101c41c11000f565501c00b580d2410702403d101485420b403045a645101040fa240460a000314419544079140c204c0c04541042003080807401500c02455464402d20b5035100300200c0e100c1c0c020000b04002c134020f4421a0b0108100785450b10b00c1a0072486407500d0100c11000002e03d1049440c0078441e010144280c031190303084803510a002e800c010200540c95903030051310781002da210845501010005001410801580200400c024038044d8107000411a6a082c1c14840e5500c41c000d15607151128001c021010b00b4003201302018006c02c1028459042801c211a880002030610851600000174111a80325001003681c0710540c244a050145000301a56254415001036541c0b520340d4907000c4080500c0300061210522070500b16889018030500501a1420401d0640c07045c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 362116609 1250 362115359 362115367
    0x30509120a021207081c0f1b0e01080928060b030106061d0d120306060912051c050409020f0909060d0b061e031501080607110c060309010e010c0e0f06 66
    0x2664000b03911014060340c40000c031350340c1001d880c24003090305c20803007a402e06071140c85101c1d828680365440380f0074088a007101030103881840d0f02454040c01030f40b00d0060105003800007595855100f00d082d181d1280780001250241c510007507050881514034002041209180c0401000300141802890384105055009021050905202900c201640d200401c140070103214521f0301a0780f05c804188600d030b00550400c8840b0540440100603081500842020510b100e00c00035591103050301201489406c0805881d00c0d4021030403181180801d0f121203410000203120104290441d40300401c50381c40c10405141e60b480e5010203214640400070710040c07140500c10000c02c0407603001641c465000e242155610a82c04000c1003d58442a000104540600c80d2503049100e4910a00c181070680f803805048962a94903203108803004040c104210460360441480c0c80681d081c03030405190400d02d40000400e074203c42100ca5400c4a030880b41100004180040020490600c030030034000d0034005a030390503d4 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 362117859 1250 362116609 362116627
    0xe0d140a12180510030212010308180108160f090f0e07200a0803070c0b010e0a0b09040f020910090911040c05070302070308030c0f070602120609060d020f03031903050912 75
    0x11602040c8100f030b01440c01d4250101d41c1030310a90403103d4001685c1300351070095031030742840750090f001071450f5812a10010300306040e96004034007481c46290101d001c04156003414004851140c2c0c5203030030100b8002050004544800b41d028004040d000400304812036152410380108000030b400c06448800d07524444000e001080803600c880001e1304904500c0d920f4580b19812035420070301d41e00240c0114141400803424001d85059140148106001841296080d00400420340003e0310024803050308481130354010b040c4191116170160203031003203d001e640c1d42d82000081d6903001c9021104160307a0725204201e4542440364072850096890302c80d0400e20242e4000c0c0d6110b000b400060701d001800320001e0791034a0340a00b02c1c1d20900303503145859143c84041c90404e001e50425018211200040303400582c860800c41d100910500c0000c01c282c0381203005070240f01d1004103280109802d40001c00440018000c5000d44038a090700715500000c19140c1480001d0a00c8460382c40540700d86410804044 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 362119109 1250 362117859 362117897
    0x803090108011505070f050f0a050c040c05120406091502070302030a090e0702030406030e0708070e01080d050f030601110f1b0a0f06050306010f05091017100501020d0e0d140a12 78
    0x45c2c05038000d0340e00b4521119070500c5803620080c2c400301d5040d0304c140110b0303804001001c603070001084004e80d014024040201025181401902340003101032204200080c0420010f420264071540120404040a512020b004044c0d900c0143c4c00c0c0c0260340000b0340e0203282984002c0b450003c0c149021a1292410480b0009460384618840c107002c164541540810201d001c2c030507130000b49030250440340c440d9600e07488150328681c00d205028082c0543d4443c1071800d4043c10460750311402c040c81e42440c55440308019505c055020920710a103204900580342d20404c10020041c880004510240c810142e6600300051544150402086100b030244100616900034095940045090030400d0f1304d56442a411541070040002155011680d1003050340815049040ea00c0300c1c4007040510100317503035221080c91402149226140c010380c0b001e64640c0c120b0344512044000b00350f00400c0d80b0607000e03103074555150404c1140d00b091000d800511800c410040e01e407403804004003c80c1003200281c50125203003c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 362120359 1250 362119109 362119117
    0x10806040f06050d06050718060c06020304030e0d0b161b031b060203010b0a1d0915010c1b0509090d020d050f0c01150807050105070b04060e0c03070803090108011505 73
    0x940120340310701007104004566000074000e03020240075404401407a0a00b90082c0c0815a21500455108882c44080000b17407620102500e00c2c9440e840c6801a06948000080d8402030040d0708000800390401030070b40d01ea210300400b5034051001d05185040c80404032a0711100700d902e003814407070f12240d0070b0300450307039034880003081501400c019140016031010b030310343c460000390014425440000045010001c0401401c0080c4c0d00b5914140c142854100c0ca0302f07126004a030580d1701c0b44603100010f0704894900a580c039904010315004c04010010f95038441e003604980300e03003001c1c9401050207000740c0c00c1004640780d000a90038020081d62020403400f03516000b10503003540030010001a9500d00011450844a0445080b8000c01c54070204c0503115a0300e010ba0300424044e80030b14080001d9940c0300c1d0301038425030341d080108044262030300d0b0303594002000402520f03d0607008220341000240d41c02e01102c1c0c001d1403050055985e07104004001004a101600000c000101540003d00710176031005c242c0d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 362121609 1250 362120359 362120371
    0x106050d12020703080f0a1b08030a15050a060207081005130303050c090603010306151a0a0e12070f0306050901150e0601030b03010608071e05090714070203060a1410050108 76
    0x4598a96045002c038200020368001420301000018040c850003645001420400e00c159030b0502c1040d080015000c050480e6080034041e10030910202c0c2610740568814080ca942c0c000300312210550b1a004281042841e074011005600443e0041243c0301090041002d030000070442000a071900d52011560310b55013a001600309655540000c46420702a012030f04000002000252a90b0392880d001001d040d00074501c1200d4a10702000103500d031070417003441c90940e47d54490740e800d1061302c05085901c0280406056031208031a0380d0009640c0f418804103000e00700480d046c0146504500706001a2030300170b00089210b03858040e03058140ca035070360ba1030000c1c3c4803400040600c030b07298440100c028203914805150b16505e0440005054000010704c00200d681c2c001c1c8264103010070280510b506180c5101c6c0b641c00c0f02c1c4240006080c2445505054004401411924184a01da40100c4d1800e10300300c0342d11441654499140c1c51103424440805e5200f0460903611a481c0c2c10035000038003809005d845 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 362122859 1250 362121609 362121623
    0x120c03040303080a061212020d020604020307050121050405011b0207031e020105070c0e1f03020901050105130801151a0712030e0a020904080d0b0d030923040c0c0b0105030106050d 79
    0x115040e0621a04445c00410006540f1024442e641c101020802c1c00c50103100c0c0584140201070540720b002050305403040350001c0107042c42914023001503d180410741168032203000084043d5103030304940d00c01c41c1e01a5020b0800012000c113201b10507542c0d440710240510656004100c1040001d050001801c04403140c201e41b8445030340e044c0300607511401078100003071000b0b07030740080070451403040c0b03120b00e201d64a40040e02d00144805121070406002d10b010203900f110102005202950103800284513815416054400081d40c4002c4242116145800200d01d48034040003081040d104041a82150001410700c03840d20956a580011400d58a0505800d140d10b401e03418a050300c0030700c000c0d0480354001c1d005030980d10300703450308044540c031690105111902d04949101c1300d00b030602159a03519456290709545c40d0600c50b6598102410b0480c61002503006180c20075039480d540105002c004150301c501002d43c1d0685829607005e0b1050300000d0180e89440420001c6907074031903861300840d41103a2 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 362124109 1250 362122859 362122861
    0x30c05030f01060e1507030206040611070f0f0519030c0201081b030a05060a0f270209150d06050406030f0605090102270a030b07050c1506010c021009170708120c0304030308 76
    0x2c104180385002005c030f140040811100b01f03040d00403407400c2c400c61217420100700c20b14640e8140240c5010b03101c4003604005c00d00c01c440c000107600d0300c99010381e6402103003284c0c0d41d501d07003c2d6003a96583c00c10b03800b200006c0c8121368400455030000c00075900241d1521080b10400c0141d20010300394080202000e030384544a40201d02c40c1d817a4148030b2800b410421074814401c68031020000860741c4840a000030624103640700d40c265240502c01d40e9158100104100c00d01c061403001c4400c5c0760041403c0c0e48001e0781c2c0d082c1c002541d40e1280714190007580f051441807500165401c11101301c50f13005000400ea80d00410560f05115665150700703800c02e01c044840300e03550b8007140c04160a400a50001030003e00d080e01882507003504800035080380e0741321030101c400780300305902d004481110603907010303000ca10860400c1c4014503010000030060300d001c1c40c10f80017031540e4201c4100d0070001809611030a8008803070502ca09102402541c01c00110083d2740e03442d0668207518075071749201d58807000e010400410 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 362125359 1250 362124109 362124137
    0x20f03060d110a09020408100e0307020919090b040b06030604120c03090e0109060302130c050d0239011a0a17033906043c060c030c05030f0106 63
    0x1840d00b59036910181862501c01c1d110040c2c14000c0d8840d008001062245005403134054129000b2055060042005182024080d5080c844549006401402508150005e060031040701e880783d40c081c0d070300441c402c000906140c2000b40a030080942854041d801c000200030114031804000e0030075241518160392010010300f42112840f4154001c5000d51030b000000083c507000e25084401030f01d0080341c010071a001625004001c840c40c40c80000041402485440301501c01c1c3d07409071011270400c0201038030011071400303940140c0481c210401e541c285c40305110303080c0c076500f48250078500300b414090b0b9881d80c0c21000028250400d07807041c01401407449441c500c0e200380a00980345907490b4900c58442c4002c4c40c08040261020313109007109008410f1034207001071840000c8560107035401158840e00b2039114411004030101c481c0c044d8001c401d89a289880e4000d9000504c0300c154020280001c82d091070b054020f055418440184080000030700500051400c2c00c2005070450781c090410941e0b9010f01c07 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 362126609 1250 362125359 362125373
    0xa020a0e061e0d0f0f21091401030b0405090d080907030804030f0519030806030607030605060304060b0a0503030a0c050c0907020312041128060f0f14040b2101060201020f03060d 78
    0xf0a50007404e041051114070300308251031502c6200c251180d03030001da0070390130300d04510a044050000c080000c1c00c2c1c2401044142c0c2e40345118069120185400b03d80f1440c040c0104040e141d0640722600c040d404071001014080d401450b540e048081400541540c40c0745459202c0e85010301d020161907803400705000001c200e000c20080e220590200b42c855007891440c01e01070418482201c103180280203507000246524400d214007400c2d51070062521382541c0741c070307100d400c01080c956008640045001a0100b425a8100b001c0c042003050f030303030320003802c01e2180c0f4099040a2140ca207290054104d141400800d64020054400620800756048403640c1d075810101c003c1c580040c0c0da10b410801007500c0114415407101d005041301406012240c1465031003404072410004030170080e0002d4090003103021740d54400c101c001c4a64800004aa041c282c8581d04000c8a60001d0303040c2016049408945851038224100c0a00506d90341c0001c50a040c50136100c14902d2000504644c0b05c2c8a030020601c0800c220 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 362127859 1250 362126609 362126629
    0x80904020d0c051902060403091401270801060504140106110705041416020601060203030a020c10110c0f0703080d0905010f0515121603060b060403080703020a020a0e061e 75
    0x18064042c000ca0758840006000c0742d120310080000d510311400840c05a40c00000e03094011649a540c40d89264a800e0241c5041800702035054100148041d02103a1031a07a62440c0f080707242c0758440c10215138a040710080c2120b107a40c0c8428000e9007014041981110004e0900e4110b59050501e0404402001e820908100480e00404d902c60319020710f1450401c001c1d8401885a441d00310b644000c0c0c442410280e0b60344401b4455500140c2c01080068103001c0190050304101c41c007541101c8101d042d4200280a44201c0d01144d888500c1c04101c591421804000900c01030411030702502085003940c0b03880a851060701448606540c50300492400c000095000340c5c007884002c40100600c1c20440c5c45000024078200045104004250446884000100d820107086d400074000c803006514683e1a00058075005d0304a0b07902010612000005c540311130010459244203501030320b2280341a01c100b01a1304015041302e400702c0c805500b00a081e0b1540c00c03170341880c03162500c4010010f001c0c038000034030780c409 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 362129109 1250 362127859 362127877
    0x30601120603060b041116110402120c120f240604080a060e01051b09101103040b0703030c0503190509011d0601091b021507020a0f11040f1808090402 66
    0x21070014000248001903014a083c3d403400c030350a1007500d04075983c46800e40611912640124001211900000c5010a45149442020b4000341c10301103846a5074402070012142219420000510000c12010200d400740d8000e0000d0f498140c1c90a000894103162220010320180900f441900240a03542d50070540d8002c1c2940d0084655240003844c103c0040c0981010b000699800c10340807980d0307607803c22131214002c0203d6010324141000c06041012044001d180e00701880070712012208210380c140018006001c030b00f41060764030022860018200c1b003103028843c040203818014000f141c981300e0942c81c050529072034040348644540561600400340b025a90319503464008205403131010110b8464122000110108400c1e04403800800389051102c0c1e4840040c1c010110300f0b070020769110034140c2c010840c0e2040b142814482c0d0784103030403c40411390540e23880011000d00c0f4283e251501901403540821a0240101c945d440e5900e5600941d4000042c800640850141c102d5112903041c0c0380610 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 362130359 1250 362129109 362129111
    0x215071a1e2401080c0f07020f0d14070f0506030106051c060603060503060f01030209310b0a0b010c03141e120402031204030b0105010309051507200a051203060112 72
    0x300341800b0070005004a0840c08410081c0c0c8000420b4642c0602c0400d44101c2c03042010764076000e421180034820760711001049912201da000400d078261288079100713a080d442000400342c4110a1800e5500d03000184e40801005031201105001586403a030641e41160300c1801c241e516100901405100c01c42842c540700c801500c1c2c502e0000d822503064002c501107034401d50550382e19480c0c0951035060484c09000103504180041c0204010100715408008003040074012808070600d103404000700350b0402d25054034003407072013400d001c00e4030518460094200000d013000449003409a03005410f0706880c081d20705004a010070010794000050003201012034247c242349070303940310f04601600381007400d460a0f8000c6c0b0944003070004540d8510304880580780c00c8103440040c1d0303203004c0045000e040c1a5800702c41d50b002e002e81c907041045a02d00e585020b154192100340c0250b0100042c1c00c2150b581104210141c2d1200c0b01c0c80c404103401051000602417070045090f500c2d030302c03200141c030002101038501a4407 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 362131609 1250 362130359 362130361
    0x1080a03090b0f1e030718050f0f060d0501090603170903100b0f12030d0b030307080d0c0e190e060d0309090c1b0503091306030210030b041d0304030215071a1e 70
    0x1d803c850045d0300c9035100d40c40310990100c45000114441d0301c1ca01915411010190b000c0e60030385403031080c90250300f42c014040e034600f40c0100b002200b03907003083e403045004980b03601d4117008100c0404081e8940200619400d410b00d14108000b96992014107101c3d80042e03505c0700d082c2090307107591f958150680409802c84440c1030084007020750f65442500490000c0d80b0303018000480f860003204441c1800c0e0006019401c0030210f0000d54014000c1c2490719060080c070140000d0035888050070884045c4120889039540c515002d115155048020b00310707441184c038094802e0000350001c803038600340d5400002c0000e190303420000c03d640a00b4150300301110200742000319010410000000e02c800601501e41d43c042280a14070002a1801070200030f43c080045032030242882e100703500414801c0e00c000c01c003203841c601d10000b40300d42c0316448009280c55000000c0900070740c10300f071440c0c03058100404161307031811030f41b6182c036038801c0380c0040f900ad1a2108500803c080c040c1c102e80341406100801b58010302 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 362132859 1250 362131609 362131657
    0xa0e2215110306090105010f1e0302120a0f0f02030712021e0f04080c0d080711040f0e010c02010b1c08030a0b100903050c1005030106050d1410050901080a03090b0f 72
    0x107941003120310501c1540c010002044551185606030000301080c0c8a40f207003103011039900422501c18411580c2050f90900c43c0c2c8200509019905000303c681070000160b07500c1148100080c0c1c1c41d6800d500d030800d4010014040c803d9400846501010702d0610300603100d1035000c1c416500f82c441c9140f14034040340080b40081200c50510018400c48041d0702c1260b003006010010b10400c5002003001610404050003603401007040e00008600c4075100420000310b0003541a01c2c1000c47d03081046554481c1c0d903440030ba140880c0c091060803401401241c0d11882004c8444c51034404084890000b0310224011022a27800c007925003202500c174400a0601000c401c8160008003c4007a510040e166841004480d076076904003100c44100c2040242d4950349142e08082d4195042d030301c648802140f865407111400d0800a9400d0300314060720b03000b9a8100c10324a003c1c10440c1650b0182c02440e040d8100c00c00703070310010307401c4030004080b81e4030190110b46800c40083c510f94140100c1055005c40b119803481000 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 362134109 1250 362132859 362132891
    0x14070b010e0f070c03050a052101030516050109051f051204050c13050601081803070b1816080703030f140c010905010513050a110415140a0e2215 64
    0x840390b01e41c088050b0b0b071503540180803595252407250180115804000f03103111503100e0402005d01e10141c41541580f000503854001c0d5014090b4420381d06a000780384400448010385030154020102443c01703254075402e10b00014000080b01803849043c2d042420320ba41c01d07501031800e80b07241c6141140c0c45a030390319103410010389a00da4540c0241c490101c42696034143c48061003054010b007c181e545074495902c44800740381410310b1b091452083d11040c050702c80028844e0300d04602c5804103c0680b1190a0740450701e614001c1505003072807102c1920700041c00403540004030301e02180d0b00b601d45141016030300d10f41500c030b00d400c41255054051000481090081054000030b0006d403041008002c03665400300015210361176580f000303100341c2150b0300440c0400d080c020b000350f0080d00140000b0b040220350b025252440072503231240c4109220600c80b4440340c904200300308010940b1450624041c07410080f1108506041161550040c0d008845107041c0310620245910f00c483d00c4104119180f170b0412081 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 362135359 1250 362134109 362134111
    0x1a03160905070305042001020304120c030c0b09100e1f030903300f020903060106020601082a06030703060503071d0c040f120f06050f04050f070b030714070b010e 71
    0x603031441d04040201e036010b480703071203a903200c0e80d007201c04944030003005007800c00b8409004a02034110703c0240804120240e81414030b580721071199400e41c1000740703185080c1801080903800140141c13424000340d0f03030782d4a80c1c2160b602c464085e4544020a942000c0020714180d42c00c03030700b040d148400381020161086d01517000121140c001e4803041091010001000c0c407c003041c018101c0c1d031a90441c000200808950002e4141c0c050082d8050705128100011a150500c00d070301032070045e803140004001c50b0000303001c5013003903811440412604225103505104103810100350b25025680010006403003d00c641c0c0b0031800f03002c000b01640c010641e41c550804408089640e9104122000780200386c1c400d054100301c5040b1182e140c0900328140c80d041c10140000c9001109885801030180d445000070242c1c80341c14860707021903810100c030b4141414a00e103002c0a402c01416075500000301070004030650707003d803075100040c0c3c901641e280144400d9803085000300d120003044502ea001c00841d04610200c202 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 362136609 1250 362135359 362135369
    0x140d090f121205010b0a0302070f021206181209010f120905070f09020c070b07170325030203041a0601090b1803370602042402010e01060f091a0316 65
    0x2c640802d8448100d503045910030720440148590400514010303074042d4002c1e002c80d60055018000c81d05043d00418441460496554515040401040b400c5449020b150404001580060042e0b0f03004d500704062034851010b14505124239110b5500619215410171499840c060030140003842080c44c01d20b0b5144002d000f400540d0710151000700701d040c210b20135501a011004010001e040c540840004240d0048000351040788918000c900d0f0b07030f8207680c0110700402c2d01c034880c4006211050030000c51950445100030030180100b041c4404920031002100e442c0e692003410080c40c1c0c980000682c1c59202680c00f00130340402c0400e100d42060741000400c1402c02d01135055851013120052007414002078078200780c200c14038ad0040c42208004100e0301e1140346100300c000604d8a902c0b03000c003036590b070419041120030301d002d00c96070700c090381e4280102e0305400c1081d8028402c950802c1940300c0a05124050145282d540301204107c0c180c0b10303203e650300080701a055480e00050000c0c0743c40403100c83d002d0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 362137859 1250 362136609 362136617
    0x14010906090b1f0306051f0608060a05010302090306070807110a05010b03060105010309080a120b09010806060f12030a030b19060207090e03040605031302010e060a23040501140d090f12 81
    0x1c04000042850401d03e690507003900d1405403c640e00e0340c0081c0409840b042020804c801d05014482c1c0d0203051030050442e80e11910410300e8203404111803c2079031b40041d81098014000c0c0380302a240040d074550800e40505100745a0b039110340c1e0485106c404540324038801e1113110900005d2040662004990103020340940e0010b0fa200c0c0300640c16108c69407001406c1c0c1784100080b1408038441c44501d1159003054002007120240780d0f000070100907003a00004c00075000b03901400080d207840304a01102c981d05445451050801c1c415058036801103d00e081300789a100d4420b035403c0d40c2c540d504503049100f101c40b44d40740c003922440d0003550b41c0303058001c004003030313181c4481da00005800006a40880d0003a658151459403215000e10740d00e040700000701c1c18440303540241d42c415074030398011740596002540c2c6c8003080810200703c01d00764812410280311a5404100901040c1d0303008460454a511917000c0d990345032201d02c1508020311503c1009040c00c00c0789104c441c1004109500301e50454000d80d5 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 362139109 1250 362137859 362137861
    0x1106160302120c0601170c06030a051510052203020a030f120516080705160905090c0105041a0708131e090c0e01080702010f02071a10030305090d14010906090b 70
    0xd200c60a10510b0115849580160010404000039884c10740046000d03800b030724094447c10002ca01583c10680f100140c082c0c0b41c0d010494101c1c007160f00d010720040300301c640c4c2420490318500030740b49202c0c01d050b04152400c070f40c0e524180c1038070050f201ea00540c0e01030041d506490b502c0c28106030b9a600b5040c11100d56018642e4815114454819140d00d061500509030140040382d45411640d8403120f02290329025500921400c140e01041c00801001c4a02000c02c0610702144110300702640710000e1414030900b07000500010490b88940050b02a001030f209584010b18201400e045c018107040c4680c1c0c415198012400c4070301120300700381801e0f2429600e48031039140c50740c40041d562098030880009861941c010100d41c481c00c04250051a1400002050020910703684281c0e401982e05a91950081650341d68040b5010326295000915021a400540c21541e00516a10405d05058441c3d901405c0e07a0060100e41c01c00c12038400764440017088407122529064001c0d1001c2d0809480d140c040390 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 362140359 1250 362139109 362139133
    0xb1f3207060f14040b060405040201030e01050a0b0a06021203060d03091203050a08060405010e0402010f050c0109050a0b011a19050f040608090d0302090d15060825050d15091106160302 81
    0x30419000750f0340310400005c2c030b5807804240001080001d0060741090384400030070f16665000c1c82180e00900c0c2c56200403690f802e445040c4540c10b010303548080115807102c0c000001107003d12080e26000720003110b000703400c01003d0400720703104851a0400108207000e900c140c0105038100c801003680c1503c44d195410690350b96820403040326401d12031195178a0344440007400541c421004200c0449140c00d01a040032604c0d9400b0342103864101007190941e00c1500740c2802e00038640c0c44540140703141c0412107002281607543c0480b5000350601c01c0c208000d001c000b0780d081801002603400c1c004e900304410b030311556181001080d084007521125954000d00c0c607447d810f1480b900071a650070402400100601c01c25985a030040407890b1054400c403a950b2034013103000c80341444180c2050040c6039140209460448a21607000b2580d40481d05c60702c10304580c200060180d941d11090211a030074001025110350a01e0b40f140100d01100e19448040003850446041105442980d098065800c483e054401c01c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 362141609 1250 362140359 362140391
    0x160206090301020c100b0d0c0308071407090c080c1e16061802120d02030906090d06050703020304141b01050705010e060106020115060e0a090b01140d0b1f3207060f 72
    0x61034003800140c23210a051002c102d4920051980c14800d800150b561185031001d00c1c20040345030007054246481d401e68141e0a6407201285130030802c180c0c0094a48000440b4100e456012030b420070824440c00b09101c03030841e0103001403c41741c43c0c1040d014070144420000503d003543c03402c20102d01c030b0a00e030340c9803a1003a500016012811030840d0025071920611030200002c54000050165000c5108111440021411700580b170180706541c50240c0c0ba4101491301e00b102044803840003045174884540244030202071070101080b41030071708040f542e850f80b40c1005800762000c12007480795440745070000600264158803c8181012201d01021016201c0b00100c6903030982050580d44256980d205100f19007240d4055001038405042484404200800300c181a400020b1401182d40c1d0352003109000d030500340e81c445004d072000303414152054040240503088034480d04810030b00f0049003642c40442902500700500e800d040303203d071545030111890b1800c080c2c4002250104681e040c607148410119030 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 362142859 1250 362141609 362141629
    0x71a0d020d0b0925180911041a0a080703020304140a050a03030f0b06091203090a0b03190b180a06080a200a0807091a060c0309010306080c06160206090301020c100b 72
    0x1039401c4030340000303200383c41221701c50b000c280c00c005150f00044000407001018400e8149041c0c6080b0255200c41c5803000350381c0c00706080c4151040e00201000743c1a0307084c0c0c1c0a460550710610b80d09006840f41c4590604509078881002040d9091180001040138064001911403c0a2003594107000030300342c80c00ca030020340300918a0640c00c4001400742e00010310303044201002c8002102c040703c2c00d20320000300140640300c1503884a80389c28800001d00801025000003903090030903049091000c1d4424002007a90307441903404540c0c1280320a00030403003a410702d41100d40145403242c119070300d0039154100500c1e04c541c13141c804030b110591948406000d040c07104600703080f10740c45000750461516102c401ca025010116544510240000480740c50f60b076043c0c06040110b2990000b50b40b50140c80380090b007100c1c09500700c00c12650041a100b49196507140c11140b11080c88840c014902d00148013003601ea02134402c1403541940003091291008200080000c101d01c40d5180500100c81001c007030020b00c1c26 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 362144109 1250 362142859 362142901
    0x80f0d020c1e041b0507051911091306050115030614011707020309030304150f0903230708010f0c0f09080703030e060c0106060305010f17071a0d020d0b09 68
    0x540506212075804100b21862400c81c0207040414428011461091103c01120002001c01c00c08a450300500074200300c4001c004110010501000076a81c491050026040c6941b500c01c24400c030000e03001003000500b416189610240c01d00195844001e5440142000702c3d5050000e46403d10000d40341c503180031a44c0c10840b06846102c20f0742a2400e40c0181884001d000708190705c4104050510b0340c90400090004141d80303070710282d00403103000c2c000701441c0e851044201001000b20003400480c2105c83c00c0e02e61003101e02c0c0c1040e000144c045c407240c2404050303409402c580d481e00024850a80044e0030a0b0199011561030428203640380340159406049805a14480d610049061000034054603500020041c0208002e05044d800002136096440a4200c0e2000070f031240010403201c0c0c0070301e565030302610000002d1403040c0365082100f980c075040d6120f043d10000c55503880680d14000d41c01101d000404c50030702550342c2d080b0215004050030362585024040c81010002520310020240003162100b = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 362145359 1250 362144109 362144119
    0x312030e120d09020a080d080f0a05090c010f0c020411070b070c1109060f06030405070810020f09040b1513080c0f0612040201050d06060201060812040501050406081b0301080f0d020c 80
    0x5060140c00280030a610403a00080701100100703248004000310040c8500c244d40301c0c461840d00340d98603249049e014107541040c0f810b002c103000d0020404558044c410f03800b03207854a0140c007014012940c000d050b000c003075041454004107607000c6a81500800f0702c0d5002d0f1107400a40c0d03c802404440c84240340f040a070900106030f00340d000c58980f64441d590840d0009040d4000c5d14881e000042c103ea000b55800c0750f07a03900944003040b41c0c0b80c06201100555018071821400c0200c400e07a001614481ca190780c45c491643d03216207010b15a104525101411152581035480301a244400c0c4120007403402050054418110060f08c140340c411507850314144054411401d1000190864421000c050400c80c103200d41030140c80743c1c0c050140b16510040c4120740c00402c651b441c1c01e54003818086c02c441a00c0f81031404010501450740c000c4200c50442d207517840c4c46440c2d079580400e00c500d0f01100b0301c0003d4003d240080005a9000001200044c40c540c5100355041c400d25010144e81e2020100040394210f = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 362146609 1250 362145359 362145367
    0x26030a02060406200d0b0f1906081807120606090203060105071203090b070215010b030609041e050a0f110405041112030903030d2003090709020d0e070312030e12 71
    0x2da640e4200c0540414168401c2400c1c2442c010300305129000484d059041c0350743d0700445004c42c9015007e8006040301aa8004400c1e40d100c1800c54403818280a0350051066010110b4001c0d0421500000180717202402d4130200e1341c903000b540d601c8890901c01070f5817032030424502050140251080b2802903c050b15010300d010165500e802024000c500013906256a5500c12008038070007820b401c2c403c0390340354064200c1c0d001c00414101e54540680090b0000c00040c801c00940b5228000c10b26046900b00c00d0203412030741180034074800c4c2c185030300e4014418042c0740200c0081014082c0d0015085114030000589040d0346424041190b10486001e084680c070b500545406040912083c0c1007046000c0035685403800c101c000c21301d10f0f4000c041182500c0d03a59103211b00300410301d9020780b004480d40407105255050a0380c8590799440103004400c1030356400182a00780c803015510402c4034941d64829a088036690742400c510351a000038136400400d0038425684409100401d0341100043c00052440c24 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 362147859 1250 362146609 362146613
    0x40509040f0203150f09013b0a080409020307030c03050402130f0920040b06030c040e070504170c030105060402040506160201090f030b0105011b020319081326030a020604 75
    0x50a4003001d00383d806014822864681049210b680b45c810100005040c1140c240103007410700f11090641b142000045403a20150308007000c41c14060f2900c410140141c00a40341803e180c20010040402405e94070001400501540310707401951240c03126440c108481c40c0e0402d010f030300b41c5500702e400039401102c0e1824408005815444540002003031040052184100d584007842c0181e40ca96010304081c0710382c0c80c0f14407450140151429408156009410342c180040300451500490140300d04001d413480c0010001841542510000c15450391000c07036044410752030945a828404145000b9400c110009159040c00d008607000c4031b0303002d040c0a1405c00705102c07400703490000040880c10880e660a002805144e42c9040c60302075401002c0b0340f15554500b00024100300c01050140a1208000c80c940d00960f5020030b0740c40c6082441d83c002070307064030940751154041c49040001140034024410109074184000c100c0075000c01050151215145004801a0380c0d00919049030b00682c032003000100 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 362149109 1250 362147859 362147873
    0x7020c0414041208041112030d050108011404082d07060b0a080a030503060f1f03050703060e060609030a020603240a0b04150201090503030a1e11041512050c0c060c04050904 76
    0x1600600540c41103070001d0b11900080c0e214031f15282d07136580300c0d07201050320b1030456140d2060078010101c0c403008000714400c0310084103080000420107000c5200119056402505040b00e07a0400706000c6c03034404400c02141102282c1d9005802d0903a113151070300100300d1305810000049030950307454400a00080c0c3d9203035801c41c3c490f4001030100744c12014500c0c0c40407441e1200982e21203a01c010b202c1014400c180c421008049680c000d050004060900c00100702c1b180301c16000c90303004001a2071003991081c404001c40c2ca0a030000b1402900980008100000e0400207402c10001419030190380721225417140400a03100f01034082c000000b04100001c020504080b1043c09050701140008203040032142c0711603085400807903041d00650385413600716003030700340e1680c19100705042ca1004024140405140b407140c0d0069015010440700c43d00f00138034541e0b004000c00380e42d4640c0d1800501103440d02c6030350400a81c1210fa4080b0f80d6214900c00303e951000d003801507806403035028013511042d0b501c0b82c407440 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 362150359 1250 362149109 362149111
    0xf110f0703021c0309031704030f0f020c090f22081b120408010209090105120a20120a11010206093a0f1803051005040204060b0307020c0414041208 65
    0x40640c403510050040f203010201c0015141c8265480001d4007120508014180080c2c4800c040306103d100410000041c1d000f0202c00d003410740c0b51804501d081d0301008142d2030912000c2100b0341c06500c1004100400c01e401c01104d12540c2c0200c190310428404418030007503108003210091010205104401c4808003455003410f4049022044801081082d142e007007241d4010342101800f40d400003040b0005081c1407003200c0c0104411341d483e99940c420181810380300c01000d50000c0c11a14107420301c10304860b540301c18103408080146145c044070192201c0c80c1d41e0351400c1104a0b0b09a515100c400712a60020803081d100e00420030203058600c035007102c1f8205641071500a490714440e040e2040c02c04010000c44d10340503454980b50010b2990031918047c0c46040c2d0b1a40c20004404805801e000040b004502c0046102040034041215161840014040c145d640c01654010b2004020030450940c00621090701e00d0040d50308016014410341c05820723141040700c001c0d01d5400000c860380031307042c80f40e9011 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 362151609 1250 362150359 362150363
    0x803060a0302060a080f010e0112061a0307170d0e0d0b07140313021f050f0702040204091e18031e03060e090f0105240d15020403150f110f07 62
    0x40031009489600060381c030303002061042d000600c0c3d441084179000506002501405040c5610051585000448200350030f0110000786900d480d04200b0141da90500c5802040400040c140c07402ca0391240c80c189407600300000c1c80c03466407040c01c5a4148082c003032080c8413110840980107a01c0441117031242140004007500100c10090f110103498a00c40c00f5201540c0541842c102400011416004200f00d403030300c070280c2110112490840d0045590010b00321182101815125134545505000141c001c0c0200d900c0001524288010003070100c011038110911400004c000304440302046020b1400c1010b0508004e0101c1c2c00d174490300381d8102c2c08810046440d1001d14022440548898044081040550300d049460b4801c4a1810713090200b0b000d81940188000050b84107081402d030489190600010514054241801c124040c000300c150340d9140700c810300c14259035a507640e117089150f02000400d5040224035203208400007400e68001d460070170680140c842d00300b01090850b540c081e40b0059007 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 362152859 1250 362151609 362151619
    0x120e150405070f09020403021e0f120a0212011d010903090e190905060a27030c150e030403060f14010302120709090b041b08030a20060421030612080306 67
    0x800207440f80e1061080014100701003015844d5840c0d44140189a50b40740c61803081801d40e190120016140c0080070300404500f181c901c0fa503441345400c16030410701d911070060b4001403c082c4030141d004054101e40c0c8010700c036040c414004d0b001b20801310700b03e4500b40c000400040081c1020000c030b1245613801a000780382c600c0f6101000243d0a0260100d400014080b075098011004004081e901842180518880c0d092820070001d0a0f286203001002000d200409001280b441c000501903078a1f4089612031920030108010b4140402d0590f0300d400c188000c541050600210003600d90300f03801821503904c51007200e00a940d080d982081441e03090010317440424402c0210010b90300421780100044580989408210341c05d10303080242908094030300da0007515056100030001d0700000070490307001003514506106501d41c080b071409841e071040308920300c00384241c40502040c40030505114041004414000c1e4202c0e100e03000940c25031342180300f6084141003511881c2d01085010780203650180d0001c003 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 362154109 1250 362152859 362152873
    0x3030f030506040f020c0622020f04020d140709030b01050a0e0f041104090f1115070f050a0f11041a060f300901141902070507030c09020a120e150405 66
    0x84e60f904076040001300c1000c5600060071300c000d00350451001810b0b004c604d03103510281070b01c50300403a008a903c2c48081e030080e540064284040d07031465001c04101e01c1b182d08102e06034140311100402000e50350106586503041e401c0000345601d0089900c10031210703d01148601c56503150b030701903a5040002d00540c4d441d68003203003a48555071144202d0103058401c40500001700c0b04c900b8020001d1507040d04150040e8000e01b0380b45405131008054070401c0e0761103446003007200751700d18046003011035054009041d40e80c4030049108018540c84030201442058070304115124003002c026002001d070034456500240100151424060802e000f070081c109020f40304418100103010040548442151040c03c05440000748152030b8002e0180d60b45800688052040908107810690001030764142041c49060b4002240d02c200003043c02850019504041841c980300e0b519401c1502070f501c240c1c0c1c3c0e00000364101450314a40e02961080c4c5c0c2c88486440001d01701108101e4038003600d500d01070001d44562007000 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 362155359 1250 362154109 362154131
    0x21305060a081204180b03210c10050f0a060f0b0a170a02091c02010801180e07090e071205030313080409050c040302040c1706040f0b04090f0201090b0403030f03050604 74
    0x100f18103400b81d401502503a550302c1c0040d05281465042e241c10005030400f5901d0900f07a800082190012010012a0504450302c1d84451900d03c581080604940100d01584500619540c0b102e403145000e441402c0c8586d4600c0d501504454090141d00c2c5e0320981c03000c003841060a1400907024810090a0003405495100d02d1400201c00840e044080a44c0000300001ea508007501030440340844ca807403c0e111000c0950000c3d1031034205000d0101a2041c0100c00c0048a0b410340000c5803216580003a02c9000d80c0783c07204140130301400052144148105040011110040601500c0940c0c103c03002d1400d5807219820851000542082607400030400d000200c3c1402e9240b0416000d400728030071181d500ca02d1403061109488880c4207070030510001c04040c040300c0307550440701075000108980000d010380318120b0740d40c0203010b02c851007a00580380441c800c0401513126070340f00205001b41c840342021070f0b03989078062143c03245000080c00585e9184a040d07409000e60441e641040c801000400d24207085 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 362156609 1250 362155359 362155363
    0x90d06020a0203070f060e0d050705100f06050d060c030608160e09030702120a051606080402311a0607050a0b04050a0f15110306030705121603080414010c021305060a08 74
    0x5121700740c1c0c0c040d41d01c0c142200115000c2090108601840c01d20030b0601d402070b181c440d15034841ea022001c03425182c0780c8d84403054a40ba8483d102030320700100100524050f50904500424a00c81c1940110781f5110012581c01c00008800706c220802803070042080c0d00306405461003200151110311944800d201ca100140d4420242c0642c0d2802030008012000c00c50414500d000c0d006034107500c0d4100c01400a00405a0107500309902c0754050b03600f640c41c1d040d03445118241d00102926507100d0348004064004d0100540c00640040c200b40b40e0717003c4111a45801c200741841071440003055075103c40303040c0e800101100c0d4500c2c2d1041c000c5058842d00c1e4a25200d050340d81184000c1142d058640024880005229210342014140150349080c10b618110000c00c1d51907000b0b000d100d02c10074209140d041c0d0a9800c20680c00d010100541c0031034016a07030701d03011340039030040d004841c1104800d201d43c0486520074403003c80036030380040907800d070101c900194200030400a02842c0d00314085c034001045803201 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 362157859 1250 362156609 362156633
    0xa3008070f03020d080606030708040308070c05030f21010501050a110304150804060f09020604050d080c030f2104020d11061e0a030e0609210c0d02070f0605090d06020a020307 77
    0x20f0f00a400070104481c402031445000600b4a48141c105209010005500c43c00c130a900c25414144410107444861007940c40c0888040c0003415480006203000d000c0080402904100340d950041a000d000903030710304607510409010b05030001e04103001e8018801e11941403100c5803941c40c4240da00e8141c0360024420744820150150010038480c4040c002001814032429400c402011001c0000f0411580014441d01c9a8440c69101c1c0007065100c00500034007100315495060b000c0101c0380d44542450705503203150008510704158000d0f0811114414800c60845807290b6401010b054002409030703580c020b000250006107400146c2482103000c90b25131241ca100b41b80c4014480c4d2515070070440c0c0002c040d2104591207403c1900481c05206444000040e040700000c40355800400c404000c81010702a4090340402130300754030074450802c041079008a080e500796004258803080c62078440341c081e5164810b491601d03030085180315210012800310340c0a41081002031044c2da2410700b02d91600301d44151 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 362159109 1250 362157859 362157863
    0x307020303101e05060d141e07020d050405010c08070516050a06090602100b030c0604030c09110a27090e010f0501060309031706060904020f03060a3008070f 69
    0x8400418082c4481040380d0900080986000300088060b8501c40d01c802440241318035401258045148140070b601600042c8094094145003141803600040d8401c076540466000f403100121540403c030782c5880403892031300c80c4601c1c1d20390500e441e00d03000044070302c10400001603070780007030504c00c180000b4400e204c2c500c0ca40e038184400c40d48031400d01041014480d40d580c4400144a901c00702040181c0d001f0440000ba03048807a80001c1c140480d40201c0d040c201c0c000042d60b4403c8002402100700841191a00107236606d201c000c1250703540d04ca03480c0c0d000741b04160109011419904050080701c03044201080700c80ca4061060704443d51b40d05201c03082d111454031807405a51248410f030b810810382c1c0715103801051585014440100c098401821020000360080c4140002100040040d120002250100a0085c0046546903840d02d9204c2ca150002c4c3c4000f440750310001c10015820451500481c50300c0300301200c504100381c1c80602d100041d901c0e0302049500b040240080d501107101c2104010500d4 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 362160359 1250 362159109 362159113
    0x90e0112120503091b0f0307030b04110406050a0308070c08010e0109061413081b0a29070519090305030705011b180512160f141f0c0206040902030702 66
    0x20099150058458034044407480420009204100f6a10000039450b11a0090f85d2004c101804101002c035041408490046805100d00003001003000024800c0b144540c0c003030380036994045442c10401003503400e2842030640c08600c2e50410b1000c100745000510140713204020150000d9500d8580d82c1c01d40d6902c0c0300c58540d69548100c92003c0c85414000e401c2d01c02c001d230200300140d20341800128010301d500798002e0180007001c203a40b403000081d1219001c0c1101c0d550304403027024040380703800b01a5007800e4030036144a032041c1d0840e4a48140701c007a4140110240c0d01d40034109945910280e591078030111589040003100440007012501c01d00043c03641901490022500c1d400e8051501c0848118510b640d081010203d280d010841070140c0344820313a2011640305100d9030381501080d181c4880101e00c2035109030700340340c0041c250031003c4081c42190700c441c400c82034680d1a6030800a8001800380c1400c8454024410090b605105941100445100804603814141c0b0703000d40d00202c4e0802c680304405a = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 362161609 1250 362160359 362160389
    0x70201021f1803050d0c171f030803150f0301020702130209010903240525030903140d0c02190b010e090f0f060109271b170c150301050306010e07090e01 67
    0x98644c01081c42c4101b050410b41c1e402c103100a903148446100400c01e10303891814044160342c11681c00300801c020b541207000d103510780c01c0c01c2140000713000d0b42850840c840c410180300354900c0e06042c0252410b880e001004030f04d0340c5c0c2d6194890f0001e548618803240c100701307002101000040c2d03184900302407103001111b4076840314a001590780840da00170f071008031010384040d036145203a03203044202403000ca00c0340b4010071403940f41e1809581c00380e1046110700c07000c8004604150340030701c680d01454440300a03500301c41c01e0a4880a13100c02501020b000500380b0b4030000014030110341521481604082d00000700d46250041c40e00c241e0030015200344c44c0d8400e400c824010881e02c04580560b510042515451140714042c0038014480b9070000b03000109409040e01100d040c0c042080302d00e400400d011040d000480b0481b03d5019140c220f0b0060051040d40003400309000c00c2201e5003904e0513030f0303000350007411781d039090902041141000400400030012113510124280c0000b000c1c1d6402000904045948 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 362162859 1250 362161609 362161627
    0x40b030c130207150b0d170f18031209150c07030812090f07060801090e0f120c160e070c05030904060e0609090d0e06091c050a0b0c070201021f180305 66
    0x1502440d20a90794400b03080000c0d4110a64810360785201c0c196101d0101500008220814680723401000000c040c03049002c51060403000d40c0442040441404900740c40b0b11425003c03000702540101c4030202e4100c090b0388064140110002e0040031418800d50460f079051780c1c0c1741e07119041c6a02815600e83d504000340d091010060003000060031030001200034290042c00d0000082040005100d0f03421040c0c2c46110110ba951030a02c50200c0300880142134031030404811126001030391125408400b14031a01901e03c5074442002e86407000d030b4184820110440d05c8004003102d4444280606481c1400100038082459546125000060410380890b00d01e03450024100121440020201200b0740c1040b1001c003c80d582c040f10b800310b552002ca03180ba441e04e40b04400304005c868424901912001d0030112601482000560910000d02c110a041641e9a411290300307414001e00c5002030140e4020b40d9560051050a0034042199602400000300e0410300e260001800d20601d07019404220002100c0c81 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 362164109 1250 362162859 362162873
    0x11e09031a010602120d2408250303031e180201080106030203091509070b0711040501060203180108130b160e0a051e01020f0f010501180e0c040b030c130207 69
    0x100d440500c0407180760942c035100c0302940b036010301201942080400144038148107002e5000f060107283d4108400d100030441240d81e00c204181e40140c0d0801e01c10004945010b1010350414408050308101c0e03688001c2c075640d400d81c040c06500070407840a000250800c480c041051103081c4c1c041003410031940b0b20301c1e2203000162a000042c4c0000e020140100304000341000c0004112642440400307000126603112941e4a042103d690020784cd800350004010091000b2400e100019580840b010003d0380d03a900e1059030349204850081c648000c04000304001c1358024010a13900c00c003903d4600090f80419500c070040650102c4122480c0003034104440e81c810f074400b0a4900c2d905082d24024002810480001c42c1403500204203104240800b4503042c003a4405d00244120032100c00c11220342c51800030f60315001c1c02003401139108031800e070106000000414001c0307112411000c4d015000b04a1821300b4003018110000a1641500c101ca032007048644ee00899207512213600140161203000f07034030f0005 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 362165359 1250 362164109 362164133
    0xc0b150924312004050a080a170a050906040b1905030c120408090406080616090308040611011506021e01020c0303190e0109420209011e0903 62
    0x150042141101e0000381c0006103812428000742c41c84003070405a520210706010300400707071411144500901e061080b00d142039020700180c13182200c2d811580b6132509140c039550090800090404d006c1a03000c80c410340707107090041c20001c0c0546000c074a42846200456583ea02940c0144803080e0009000f039102e034020080c001c045c50440ca040c44c038600b025a1508940d0098076004014003444c10302040130031101034210391284c04058002c0c0710300c1c0c0d5111440d1341c981d8001c60340e10300d69403c503480b43c800c1244a040d012041d02c0e4001c4409080604000b0200c5045064101700c038111741d0b07510403d6401c2982241d441004011550003088481986c1041e400303e481e0964280c142a03005014810080c400072041e80c0d4003900c001c6d03c85402040050519000e814002181c608551030111034000340305101c080005056100800300c01d001d5030300788841d0450300048910f410384502e081d8501030b8418450300144800300e1f0515114520064030000e20000074148003404000c5244030800f00104203c0103c81c1c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 362166609 1250 362165359 362165431
    0x6071218150f0819180b01030b01180902030d110a1a0702010e01090b0c09010c060c0302070b06031c081902040b0c1501060210050a02070f030810080705010c0b1509 72
    0x100100d414000c4c4050800e203403180c0c2d41d00220b61118448000c200c10506411200c45d080304400009594038140024108030a0290f0310003c0400720f029071940750b1500540c030240d68090300400719910356403811505900000105215401100c0c800404102c0078060003420400103481d500307450502c0c200180c00c66900092403c2c2c00d07418650008081003c40c000a90b208005544155941c42d01000484403441e4a01d801031003d882d1156480c101e59043c0d01a04909100f0585040b9985940c0201666030b44c101281d00190b0401405000c02d040c400c81c10ba0b0780100d03031580c01383d025000300c0101c4da090b40c1081d0000b24149402040b2007007480b42c200024203800060b070b400d603040c2d9414084002d40321b0803070000c0038152a40310008200e040c08141e045460161700030401c2c180d6005c81d45001130201100355407040c1c0840c2a0800441e44c02404103400c2c04540b01615448130b14401641c0700c640310780c0c1c0242100001d0342550f0b104840350711783c1614244200018407901c0c0180f0003024081c421084241c5d11 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 362167859 1250 362166609 362166617
    0x30109030e03070f08070b13080703030c060b040e030304060c0e0d110a1d1605130303030b180601050d0504050f0a0b07090e0f0406200d06081b06071218150f 69
    0x42041700399004103e0b40e06549030380c4505942e80d004151040d491300e1880d80f051b07001d48280e00c400000d05a02203108034a030341c4205020311414116100300003e840b071802080d070300d075042080803c2c009642544200031030792103802c01c2c0320410520780020302c2e0500c040009440071020300d8448981072403c2c03986a4086c00c40e0b001d101e05e080040c02c0e460915488000c05100558001801542d0410b000e401034501c0702030030320045440b00740c407490300401401c69189868090b07460110011440c00605148602c601c2040c0d581c20b040204403e0301001070000a041642c15008009d1180c100840c00e0045102280c041d00d4102c8450600c0c2c000280080c81540c040c400c100c0750801482a101450b190494200750000804200d10700489118113114405610082c18854002005507055030030b42c000b80d040752450b0099515070411244440090503c122103160700500030401d50300011074102c1d2041d6a8260740c5007128070b407030780c0d030082c1c2d45440c1c0345403c020001e84020422070b44469015286900e056410310b0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 362169109 1250 362167859 362167889
    0x61c051b09010c03300b04141603020d060906051e152101080d1b0206090402070507170303042901230916020f03040f03020d02010e030109030e0307 65
    0x1080c165900601d00520304010a4500e824107041c41000c40c0c001c121203802800f420440300380c3d100b40074480001d0740054102d003400c034803400718a41442030b10841180c0c400c840003655510400640b03e0204020340005165007031148211881480c45410082c2c10090400180c042c1400c0c10400c0c2c0d003201840d850b24200c40c0c0c80042186868080c12481850400100d941e00c980700c400404103030818600d00200303440c250800009000c8000a06180904402c3c0c5845070800c0000343c005841040c01100613400010400039180c4c4c3c0e05060340107286250140056595103500d840d081d64001400b03108081d699800801400240248010a0081501c400401e80003d6100f0550080e02ca5414450203d1001d101d544400c1c1c10b801e920309202807048004d003018003a10b0200c400c03060b60020040c4580052241c120f614170289400001c0718180c071200c40034400704500d164200030042e282c1000c1241002009016281d60303072000d000300c00005205e600c030200b242180100707061500d02030394005510304030011 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 362170359 1250 362169109 362169151
    0x6030203060606072f040e06040b07030c09170a0b040c0303080f090d030b06130803040e071b11010512130213050105060d050901060302030f031c110901081302061c05 73
    0x50007140d0094403850b003460004000c1e4617140b100b1085505040c1c11030f040201c0c94426180220b000e40c403492242c041014a40c0f80c00900318102c85403e62594040382e880340c4140b203000c800c20405a503501c001405c13560050440da40e094081c21007030b035040701c520041341c81c00d0080581041040f0707440f000e120502c405030b1400490381513568402d0f108170400d050340e86003d0040f54581c00115407108075040303042c003226030343c48590701e0b134a80c070502ca20712041441d80302090340c4900c036070b1114110702c180a400c211032280e5a140d01e28001054044141409810031007801c07900c0000d801c1d213201c0c401c50038031042ca0024038010b00140111a00c50755a6081c039040062000303a07200001d54051480a14001401d5510710391500d004102a420203036240c807032621074120405000009110f0041c5040c43d641440201100440564160044040300701c901440b2030302241d48156401580900401a000141812a00411210750004115030b00c2801603502d207101d0210300340103031604810540c142c0d48040d1108 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 362171609 1250 362170359 362170373
    0x30b0102150402130e010c0908190c0513020d0606050702010314010503071a07020d2306040803070302070602090904030905030c030c060f030c040b0a08010e071107150315090603020306060607 84
    0x4000078130510000c060109a02e07003d6000c41e003a003500c0802003114031300b9a04041d102c0c06182c8200d000c0b522880506c0c11081003042c000b2000e40e03510038100c13017a00d42414100031200d00f00203200360115500f805018104003d81c056600240416181d041c0e0302d5109000050941300340c035013400c0040c1080c0700104100d840c0090840c00302c0d81128400e1a2000c80c0c82401c191910400c0c1001e540f00c1e00b8651010240449600c0d03c07214501f120001c84141c0d000a1403082c2c440108a4001d800d060060000134031881c02038000744401403103080014980150400052124035003618180e001950342007080c032880c10100603c1d418010f0880041001c000d102c80020250310841c0489400d144020011403003041c443c0341038502500c0d030010307181d454001d40c2d400202b00580900c0f501180e00192070204503541d001d030000170700c40b01e03540d0701900c9104d0601044800803071040082a003016502c00d000c030313480040f50161001034100e500003c603076a85075004151424a000e000a88900803c2007480002521 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 362172859 1250 362171609 362171611
    0x90e0612122709071403100b0f04091d0325020d0b0403030c050906041a04030f0602030405070b040602030a03050702071203051b011107031b020d0609020a170a11030a061506030b010215 81
    0x102217010340d40d035140285002d81100503401810504d101040b100709488142005e00256040d60808000300e101c040ba603d0500d002e1564441d1207074004101140400c00341d4143d80ca0443e07038644965901e0b070713415404103030801340500381540c4200700c0005101c201941b50060414000c820310b4000e080040120000307425204620580480540028100c0202c50180c1d0030380d07000b950000103d03400010f0508010000e544101e800b200c090190000100c0d40101c07100c20b031000e07502c50354000d505200c800c520a400420010707000605600c109480000c2d4420803026041d03071079100c0e503210368942000200c80a070007240e24507000710b40e034184001d40d0304925491060b56813a40c0c052914031035890981c404a481c4031154140030f5004051880305109205180d0840c81d403052099070841082a038481c5040000550b01e8440c03842c9801450044020400601703880d602550000e090b502c03e601290784050840342030300d07503100201000d030f4010440e407a0140300c1c40e048401c0c203002604652124540c2e6920447c4 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 362174109 1250 362172859 362172887
    0x6060f0f0301090611130f120b090705030d0e0306060a0e0601140c07030303141303093c082503151d0c030d090e061212270907 56
    0x181101440351594250441003600d9006501000620401100c030170346640a04202007010200034400165249a1400c0d80121604049980c80300912030360740141140300075207104c1d142d208040010030380d90303024080c0070323900309058580040d51385842092506040004080900c203000b050020400980c40c42030701984007000f46001c403892182c1c42c0c0c13081141d00900d11700700703164414200f01004241e01a40940c501c1a10f507400a0751a0751049880b0201d000310070740c000c0c00a4078501c1e003004200340000450324041c901030710300d54485510641d00c03200c405a03000c060030020502c3d8002c012002091280c070018110340b0900da14010f0002185140010103032000030003003010717030120188101081d4013031421403a5034003e900f41c51811201881d9200008000f103403290080340404071071f2501800b03000d022034084500900081c1e581d48104000342c5a144200d6400b405140c0c620841b9150343e00003480140c040e103a603548541c1402c1603401c5201d1f400310246014031800414071040e0b58106914110030b807 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 362175359 1250 362174109 362174119
    0x90402100504030501051006030e0613120509040212060906090906070e01030e0313030308010b1c090609140106030c140d060908041d0613020703170703021b0109050c0306060f 77
    0x60300500100c80601c5160300241c0694604418000954501403082c01101c2c060341c1c051050441680781c26403940300948030070410300041c1029400142c8400384c602d00700740d2242003031400d014074100420309981c070100385803820036103080130041c103131030400b41c81c0d40c0217002503d58142034941004402e40d2110301a1201c024042c54068220990b80300b03412001c0c1c0021b680055a44410843d40062200703440c9001c00c5000c566504004070f00c40c080c810a807040d025140c0851002c004062850358028080c0f44002d1303c0043e1110040e02c0411640060312500c065400c00018a01d45141000b540d05801c6070410503220f404515017414641d10480e100d100190021000138580d0300340c0c17070b10f280c0b10311403a40011280300e80d542140c1c400301041420340b03205e0704c0706aa90a07804003e04c0b40b41000c0384105480100450700c0000795a4010f0300540809a0148031400c00615118503800c0101c042c103880285410386070744548440b003c00905101d6247c0c8440198001d254600341038000500c03114011005902403 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 362176609 1250 362175359 362175379
    0x90303030f020d020a0c05100516050714011508071d04081303060c0302070c08060609040b10050d061a010305061309030323040b090601060206060f130e0c130b090402 73
    0x25190b0781c11a14490600041155107500714000500300c90b85914055990b40a10660b550220030a4051548030380c0c4204013030b9107005030b504410759442d086107000b612400b00d1600302040b1074400748030b1081d4a98514820040032031a01403024a4005650003403190b01c2e1002842580151b6210000e94000d80e00c038180e0780d00c0b0841645043d100703100d03d41c0064030050500e01649843e681582c003d10b40c45004600340204180c590101e00daa0351000d85410b46c01545400018012880c9042a01d40121402100101c0b0f666284001181c01d21521010786042c1c0d6203052400b15103401c1000ca40500b40d081c24240014a08000010001000e0084000303000c1d448024140c00c06200354422640b4926809085d80d003d59504001203a40600b1034044503000e07100d0001c2a0030382000540c15040700c800364003c10700b0750b03105000d02254003503508100340c000c10003c0c01400890010702403401c00607000d40003440c0e00140d000400c10103001200070031000900d080040402602d80c0c941c016445038041c1c0c1c0c14666 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 362177859 1250 362176609 362176631
    0x50d0204021207180e01081504020111060703050f060405040f0204020c030f07050102090102010b0904080702010f09051305070e0406120204020304021f05090907091401120f110702030f060709030303 87
    0x20788504000b290202d202e4104000302150000300b0b081040c15201c14401d4031588865054600d94000c1c0140c0c4110741c400c414002182c40700306070260f4443e1041c5401d50310742d811440218a014800c0d9010300110345c4450030413110180201259030700c407900703c5092019041944403d604502e9043c800780c0115000136107000100410011104003001c00700013950740708024280f09000b50044000c0328015406c100c00d00c010751400602050145d6000b000c200e00e4980d1076801910642600e60400b001d020405100050540d51600b004c03500b41a030380808203662500c03010052407640700000d1244603a1802000b4484400b5200361034041030b80c1034134016540c5c0c8543c0006005901c0507401b070f030f0f01c00402d1600c4070807507a84000a04414141599050b040f82c546810541d1400081e0186101c03040441c01e0784106588955405140391035a990f001071119903002925054600400301e90380400c02c002503010440c10100300e601d0000c1e100c07401521560400303020060012034244400b504140d265560108 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 362179109 1250 362177859 362177861
    0x904120905120a1704051f031b050c060603061303030f060909050f060106050702060f03060114190810060f1d030a20040902011215091a1018050d0204 66
    0x400781034000c00c2c034054006002c5440342e072140700c018203d400d41d404031581d14901601c041030301e05440006242c46c01045e01d22050401225401019030101500e400c0c541c4a034100c1e000480f14000d000780e54444da20078641d904140303820070242c0f0840c06580100c0411101e00e0300c201c0e04441d459403620780454040411015003003e00784c1a004407a81310300d8041c5070010010f000400f0282400c0c0c6600782c59440c0ea8986003650b45008101001e90810700400100111003007150046038084814100074248802c081154030844c0c01902448070411441840190000e0300217180b140e010555610540707400b81041c0c1c5c0184003180e40c80710b001c00d0001c1031011400c101e80d522081c0b4210321010703044a801d850301d030900a01c1c001d8080ea40e58a00e50a2640801007410329002d440105601038440e40585580d6036020300080101c02101108004c03108800724502c60725004116500b9040156a01074800b020208481820160b551105010803021400d145003040380e00001200d0040b22200256121400414 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 362180359 1250 362179109 362179127
    0x91e09061e19080d0809060106020d0c080306010c0b040813230d05070305060703020a032406080a0e0601030506041b0303170402150d0c030c0921060207050a030c020102010f0506090412 81
    0x2c00103004070582c0313140301a40001a05e1280c40150100c40259903201002da072100102c0801030000303620380356100c010403a000f004641112062420003448403964540b020560415101100c07040d00009200d0f01c3c900101c216071002c3c02d40c100c054500f000c0c002624030841010804c0990107449811060f07400d0140620090b001542c00405641e12880c0c4040e0080007588034a0144c1c01103494101d000d1007028003a034456031440c4c044020011258180341c0c06503000500100741030419a180c2c88800e9020300144621802188210010300d4a400c040c44d241000031a407002da01c21028041c00b04001203035220b804180070100c00c0da0600e0447d191400882c2c4003101010844440d400d000841e8a5190a00c1c1d000110200361a40e040209120355802140c94841500c034140c1c560500c14218100346030b402c00161401841042c0062600425603511400e0124002c81580404d01d152019801c2d560280203960300e008083c2402c01091400300b00294885902400c0a8084040c40c403248591500502d116 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 362181609 1250 362180359 362180369
    0x9060909040f050a0b010e07050306012003091302090301060e1303050c010b041803090807060f08150d0516081c08070207050301110705120306030703080f091e09061e19 74
    0xa5042001c69060400c0591428485d50000c1f00e02035001030f00262003441602c0c0241016503540128200102011120b0390405107001c0f0a404100044240d80d07840483c240c2603681d40040242e107540c160802c06084415960000410300072100401c0b1090514002c200784090b454181f40f5142c0c4510042c20b801070065044840c3c00500d007000c0e4024031a5803045240d0010720a964150425881d0321070141c0302e00c1248114000301c0c0d1040066440c0d18010020b855204c1b5008682c0480c652006000030000e4591610680e80b83d00a480c9940300c01c900d440303420024094000080421414403000d0f00400b204c40c4003904200040c0a02252045209010b41801082c000f4000c0c003070a28500110740081c0d002c64011203840c400d0030500310b00960000180c038882d02004025000341459500c1c6d00c0e540740e009020b40b812844007089401c8403a41c2e0171a600b5103030303220a00300d010340901c03001c18010b5032038000e0907051280b411840342012030300151001c0d10424006940720f1060350070f001d402c07081e518115001 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 362182859 1250 362181609 362181613
    0x1905130b090f03010c2a020a090b090a09110d140106410f0a090f0c0f0e09012907140d0906050f0f12040c050a060509060909040f05 58
    0x6105031000090a0310490032a4514115101541050708a42a416107003010a418107442c032280018071483c040c20380e039168a942881c10503031b400a090b20045410000b040350b51440325102505003c1200740e03020000782c00c1040004165142c00c414141c00009003446070b0020b0800c0020401c03003441c24500f00c0c00c924000d024143e10f682006d07800c42c024040180c105081c002802110140e010480e6a440c1c2040d6045034003100040180951001d0542c2955040f026881000810390f0007132041c69040c0c84213050010b10798a000e00024614400500c0031805c11802049004203982d0340700b4940c1c1114070741c0318060301c180c6601e4402200d140d189050101c001c040400c481c03051250801c0300038113015102c070540303801105490082c1c400c40503601030315001400511071075a208101c4e030003c045a0a84005460500c40e02004c107044494049a00705d610030107080301048241804921400604940d042040c02d24543c2d0011401034000c200302d85101d0054400410184941d821003100d800d508001 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 362184109 1250 362182859 362182897
    0xf060d0f030e03010b0103110d0b010309050303040302010c0906111c1b0c03020f0409030207031b030c080309090a0c27030503041e0602030301120b0615040612060f0503031905 77
    0x10701900d001c44650085009500741206054190b1191107001c4074041a59001400c0003100c941c8200280304c00000a814940e440340740d500420000c0000e1880f03241700341c3c00411008911800100102d105601ca0400e00240d00b440c84001c10000c148101c3e03c104140e822442c51a05820485000424600301e001c1900c03400840c0d01480455403401056074000d0701e8030900358107036030144022108000405401600702860510028800f04904000c0400341c42d0804c0b42c40c0c4c1c07203403900e0481c50389c260301c1320400c1da100040401c11401c00f800d44503407000090100300031309070f0b1104001d06445070502b200491100807050041207201613044000203550024100d030740716600d0f88106d04846203009085441c0070b45540c40010b00510000032641030b6150308014586040c03955684a00c84640a030419520100d58844401481019000b400041c0410703602c40c4a40b840c0c0382d040341d08550a03604100c1560000328001d01045e200081140c82a058011002a00318a407100c11205800348260704858512407030 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 362185359 1250 362184109 362184113
    0x2070b0c0f070b0c06040209190c11150411101404080307020307080f0d0c05030903010c02010209040e0601050607141002180108060103090f02090c0904050a050a0507090308030f060d0f 81
    0x1a800746203415039802c4407511a00c0340d49011242c003450407070a103d03500c20300029005003050f0a131190801444a010760150305180300321003d5404540100000aa030241d04440c600000c00c81d88852180030b00c92255513007010340782c804495142c058254010000165440c00c3e05100d00e0320751600c03100078000079844546444000e40c4a501445043e0701c680305034000440c00000126260740540300c040000c01070082c0d08042580c6081a50b003080e2000e001c20301041f08952000e0142e1a08050701358001a690031100d010007088034141d2241c0d111581c00b0000610894503047e04071420341e03030440c0036a4114416110380902d001e018016035840d140c00032035200d1646404d45210104018240c82e200000d50780d50004404581031201d001d0f140c002e00403410310241c2807074031055401503100703040d85140001c200d001c01c0607100c00741c0d04880301503599410071000040a2003195000121340c030780100000d00d0360b101c40505010181c1040e403904444008108140c1d00d64460404403944114981c1c4200414 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 362186609 1250 362185359 362185363
    0x7051605010e21030f0c070602030906041b05221d0c0a061416021207120b0709080604031817010c090b040503030d0902030307080c070911030f130302070b0c 69
    0x20040040184a00180000301982d042103c0c1124030800c1452030956884064405941c08058403505151500308052004920b25000440c807600c0301c1c0c0010700e920b00340751402d03400c1d030081504100500300e04281d05000d84e55500c150408001800d0401070080c032070949030b0380000c02a108070b00352030740341400451542c140082900c002e1040210f90b0301b0303000ba5a400c03054400004544003400c1e8204104502505e040c2d655034100c40705030019011011080038009460305d0304441d60006100c115015031a2000c1000102c1050b5003d401c61030020082c902d00101295284000350005060100c0b11000e21507051480d008172005161008503150202911400350340200604002c9000184000b000410b114150b00112022a807001e0000d61508803035482c0310000785402f280c2240d05000402c01e10001c1020000a48200401a009003c20600d0700302000300303c540749540d8401e1080180304222004418600c0e00da4045481c0d03c269018001c1c0c2e240c103e082500310380112403030190100f900340c102800 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 362187859 1250 362186609 362186621
    0x204090c121a060d0c0608091005100503160b03010e0901090606030b0f1006140f04051302040806130f08032503150803070503030403051b01060b071205070b0105090705160501 77
    0x74290450040d030300ca843c1800000302c0c070b100300a850b90039420002c200140c8a04886544144500306480c01484e1100780c0b90309480e0103a4180301d85405421060106150a1020071415840c0c2404030303210034134144c000d140074041440b8070f8103c0e89041d0001080828203400c00030303003a548148200a280c0d00c07464000070710841a21030030030340c4440400142405801c1c611860550307600d078503410000d0040241020103a0301440c001100c0003000d000015103601c07000100740c4462000300c00942c4550410180d10b2510b2401440c401c5540c40702a0640c0209440d006032400e015007204e555a50303951403005083c0070401503030010700c3c00003d10f40d002c080280e2690142c1c0705098100c0b00e80c566580d84400c80b41d035a0050100c0984039800800108000034060001041c0e40031030420260941c0d00326400b04ac0c03c4583e240d02909081070000342c40c00800c10340802500d0750350143c2c242103040c03d445841d44440f00805005590044507208040b80015004005580e40394100618400c1c42e250035281c40d0b4064a5 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 362189109 1250 362187859 362187893
    0x60f0902120106140706050108100f051b090f0901080a1202030a0c110d1e06150302130c02070f1d06060a170c0d0204030c2103080403032d0b0f01030204120204090c12 73
    0x2c03600cbd01c3d080401c0b0803400390138040d052091407a101d080006040351103550014050f2544000303a02800009912022011402084002d0140600444c10f080c07003006803035034035121011904108240c0038925041800c003c2200e4110044840d01c2280101140c00b0011005004e480035062100c2e40306400400c0001a0155210302403d0025560b015120f198541c0c0301c0c00000c1d40003910062440d01e210440c1d1000100c2e2085104480c0000d0b0f64100d0041505010b800002c0e40291362001001c407465019031040c0c0001303058a41c2860880030080081909031204941c00300c65060201103009103014206480d440c0501d0f940031036869680780f0340300002c92a540705110b200c0c5020035125a01a00110240c0c4410340c043d15096a03950325950300714010003c5440d8a00c2a502e1a0a1500461507801c2040c21030a1070060000e46c0c81e0300001003214410060613194101030042000340900c0c0300d00c00c10a40d1042e4155404500640146003441178895541c009642742440089208244455030101c800072007 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 362190359 1250 362189109 362189111
    0xc170a0f030c02030d020702130c110d0c08030a020a02071a071a1b0d020705061314060103200112140717060a0303080c12040303060f090212010614070605010810 71
    0x400c08054055a820508240140e003040c05804030030703041600100780180c4000c01f200d20364242240d41f80f048443c107108603030000392512054000d1010801c42243d4551071030905c16084026640c50250305d101c0208107410080e00842c480c0850707802000300d800641201903522450360448504108183c01c800c00a488010108136040e0307031261881c0c03100340a0150fa104e0351031020b060350048141c5901040340061801e500b00300c20400b2074418400a4000c1070048d101c82c85802d00ca0030300303400c10300380b808810700c260300404010400220003161052010050f2500c000c80407007541c0c016581d46d090001d0740b000c103604014031621801003000700d0500c00d1602ea1501c0d566400d00602e0385000840496529030428083d00c024030210b401004106d91100c00381d010300e407410500e034081c02c90241080c3c0f012000319403649030070b0040102104160015020145d01103003801d410300d2100d6881c800611491050017080f02c015000408a2022100c58135000341e02030003e943d5920034103595806c90013442540c1c03 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 362191609 1250 362190359 362190377
    0xd090f0b091203090c0d03021c1d010806332a07030f08032206060503060105120322050306090c091e0601120f0603031119021507030c170a 61
    0x2d04410360340103440003801401c041d0800018801050341c0340006809510450340c25104d00c25101c002c5140440090342c58100031450004c044081c0318200381410705000d030050800544d0b84038040048031100850109041700c040340315921164402d0361025040300c040001e604c021401191080f403c00c0303a0b507004880c02e209413894000da03d802442c0001040d40c400c0403044030201d04108050b640004025559200300002602c406410044c4088200c504645442003004107107024000c40b070040c00c06880c021581c52212010b59100e00c9500c014030100c544401e120f1070044149424040a08030117000c0343c0240c04d00301603095a640050070101e1156100600203441949940c050002d100084d02c2601c0031600c81a0040d50001308201071000d28681e80c00c010800da40d003600542c4021030103515a10f64804131101c50a081540ca062611500c3e14102811401600c1d48140b52000085c00c1c2081515101540b6048442e00d0340c094010f4070f0800c540191529020040c80104501103075a1961514 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 362192859 1250 362191609 362191633
    0xb01050102070f1206110c01140601080c040e130b07080136020d090503040b0a0e0a080c060a03020903060a050610021f0c030906053108040b0d090f0b09 67
    0x241e01c00e03d0041d014940c407510780421415107180022100144515800b0031b58003104a8802c0e9243c108001c1c50b82c8580d11180c2c45103c0c4000c07601a650000f01c286003209642c42c04e100c5d004800e01c120311a80124600741c07400211391809106075500d846034040092189400d1661004210180a0081e0448851b0285040c104041583d00c40ca07500281d201c0d031801010364000a940c025004021050340301a201c0c0341c9100004d20078001071025200c54035459440e0a00d11340000c0c0762081003d140c50207041d544130140154040000d04040c100c1e01120035075a211384031071049019020b4001910b40600c100400e000000d071860704a02d1040200741d034483d0302c8020b4040f0807070303a540f405552002a00c000d040c280c804d240242c0c11008075128a4100461601c405544030310881320304580b02500e818030b01020f40110a490061803140200c43c10480c10034403015224550244214820320445400000b01080094000d41001c4c2902c1d811550111040b01c0c0707410f140644c483c048a101c0e005000300000701d08 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 362194109 1250 362192859 362192863
    0x6030809090a1a01050304020d02090405060907050a0503151003080409020a1b0c092403110901120b060402180d0f030305070504080c10020f19050c0a05010c0b0a1d0a0b01050102 78
    0x45103441940c443c0007031509540151801d03031019009981002c40741d4103202c00341c0c4902c0c0000c1e004900c5030b0010300c03107803603d49681400c00c01c2d550070952280b003002500b0051561b00081d400c1013621200800869502c5100142c12864426880209103c00218000800c691030341d0144c203100c0c0c038903111000034080c0310701010081100b0f82c4d03005004003029030741445005038580c01461030b80700360f6550f110002424003ca16016990741d10490f002d010f11a0b1a100c81c0c107007101040d0050036161600e209048450350b80d5114404018001c600940d03010070310010400410f10202035254001e0a51724030321045e8180500700d001c0100f42980400d0a24021404251044040f01e084403030311b5025041c5450000200040780d202c0180342e000318440c0a4013007a08101c280004694000300c030103189540d050501e0301f50f0504902100c1e4074803a14482c6c1081020741d0704140e4000c000d0f07a0012040306140d85400f5084001c0c00c8401c003001d031856085401c00c3ca00c06000405d062054040e140306204c40e070713803000126 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 362195359 1250 362194109 362194121
    0x307110a060225020d0f050f150417070302030a080702100c0e010305061e060f19180801020703080a050a140c0405280e040c080a0812070f020d120b0406030809090a 72
    0x350080070111700341000c160b2981b02940c000f84942c1c2600d40c1f03500140d00d11890704007110352210301070440c3e0040c003080041510300040001510a4030504080280e00e019450740242c08014041c001c00a001a141500c02d00241441142001003045055441800100154440e2416501091510300071134620314012059021180e03148841113a8904080c06010807600322540d081000c50081c00848449031001081c0081c1904a58801e20580410b1850341440d510720752001201d82d20401032880400c0d8800d01c00c50b8088070583e00480c41340c60342840c54004013801880700900d41e60003001c0c003039854403484c0100200d0701d08449000141c40d9100206903e10084401982c0071a10380310100083c1d405d141103180d0003406014a0103940313694a241608011030394400310740000d00091008000c42c0354103a41034102809203025889880400d00c01b03941d0b4200220b400052201d041c208464242d8541c1020000810203081409020b0707a900c0c2109030f50300021f00a91113000f80500144c1d840280b032240c1c03 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 362196609 1250 362195359 362195363
    0x1090804060e030a06090f021003050c04030b15040c18051504090506011b030806120606010f0503190f09050c09070c08090402040e091c0f02060103080307110a060225 73
    0x42490a494640240c56124480b001280c05010f070412042c0410014420051068080c6000506204032441000780e0390080305240f0080c1846c01e001d018a00300310038280c030140c0740c0c0042d0074021500d5081e0038415048038960840c3d407050030030056600c0c055100000009061912140b01200e070740b01c004000516402041e4003940752028001000942c540d904215000740040c188044050b28035000400c40c5124587e0a40108110009000403424065101e1400c40700c0307203020302030b58106040003c1005041c81030142c204072003c404100f08000b445803581e40f2a0300c0800030081c04203040710140140060300c40564490098140034580c504041061030b06c01c400c03940c0e440c4039214035036440100c1a00a14001c0350401e500f800003051f0b5114a1452500554104000700454600307002c022200e41c201e20301c541c04101b4091491100950005101303415650301c49041c80e03c0fa6200e000480300c03d40758030700507402886081c1b104014403109034003c00395040744451040000c40701094985a0101c84240 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 362197859 1250 362196609 362196623
    0x130201180e04111809070524070602091f030c0f0804020f100e1810090e070b0f040b0301031b05040605060909040510051807080105010e0711010f020f0d0e0d050a0f09210506090109 79
    0x500010700c0ad680200f14001006040c000c501c0a003511600c0d0380c04800b020386012941d00c0342130306402904500d1142e180c2003036180400d8586050340c08680041c080311007c0d40903010026100101d28010780d1000045c00c03014001105419000c14014030980041e105005c2c44416208d0104d14803c846c0510400c41050600420f1094507100d441c076844d0f80151020b0102c03410a11011544843c024001e600850150951102c1000540c00300c1400a8050348402e1050b840c08108000985400703065071022203084401c00e180c0d41d583d00b001b9003400d079031a001058581c038001c200181c668007040901c81015000c0e0407210125180c10055003216401c0c0503581e02c4540c451300103210284142e890001e429108000403d44552018240e410398200540c0c80500b2400415400d0342c3c200c42d446400c001442907001400c070300f0028000035005200380d4022008018a90b01081240e41c00f9404640090040088105900040ca40040480130541204030707018040c500200e0608041400f5160740b8a4100c44 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 362199109 1250 362197859 362197867
    0x8060d02010c030c031b03050a02010515090105040f061508011505070506040803180f0c01020f07120b0408120c0901030608010911040509070e130201180e04111809070524 75
    0xa0941e04144c07482c20842c10441403202e04504404c030350040c210014820388030750792a0392400c80041e00b0348000a01a00a400032054090b078a544e40144250440303100303640c001075596050102d003000d440960001440011220240750315950701c40004c6040380c42e210600f09141c1908030701218030b407203665000b4085030b02c03060101c0e011a010000454100781500c4401020250341c0c0c01c4141032004a20541d2000d400991006180d96010b102d1503048084060141030b0103810a0b0b43c01040340701d00003018040101c1d407070000c0d0800c41d122044982c44104a0700d81c076070500d012a205141640305083d014006402d14400040000e4140174140b002540580b5180c070144075a0b052100a04005002000a1107601400140d0580551004d40600c0013102c0010008449000240503540300e2558080070f1405210100043c0d0088200c082c0c01c50352080140c441803110030001035520501d11800c91415035142c040c4a11904002820400c03036200b540c0710500340d42c4103001c00803200d02c1e03121000b44400c0100 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 362200359 1250 362199109 362199113
    0x70815061203180103020705010f060609050111030d111c060906140607020108091e03040806071b0615030b01240305060315040501110f12060d02010c0f0302070504021908060d02010c 80
    0x3000f4030183e110600d03005060500700c1c0c44081c01d40f0b04022051030f40d20350750388051102690014000000c0e003000e00b046140c4c0c1024005082d0f980c030903c0188118039955540e11000740c035100d4202d030380fa8640052442405c0203400b50070401030500d0700c00d004804d4a001d0000071440102100381d0b4000314001d10b01420300f003194006440d00c0750300a280704d40070701544001c00305185440300c4c0600000e0b00b8500858555090110390351a002300905880203228034501c104120752071107145a44000c0d841a4041542d0b40c8075045840800019000200341c00d4002002180c01ca0107070881c0c0c20529111100e568480d2514a000c2d422504296413054042d0080e40e4014000c0d0801403110745c116101e403000140ca10000240243c00b50007002800201f0100021b91080380b1400c4080303d43c2080041320181d0b5000c815a00107050722901c40c0d40101412440640d8809050080c041c8a0040001910035585c0d407040b0814444421400c10800001c0303010500810f1450400c06402c411a03075040c1c560011000c0c00d9 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 362201609 1250 362200359 362200387
    0x90503120a0c031814041409070302060d0204080d0e0112060302090106110f0318090a0e0c041a090103030e1201060e0130030203030109060b0702100e01050c070815061203 75
    0x3640c0280e052210b80c403886038103132200030b0410000b00841c954410150062104100c00c0c0c8584221200c141c0c4006010f000203002c001c5070580440303030b049070350307540e40c000364a001c20103800340d50300606180c0100c10b2413080309078001c070b64542d404c0002d03600c00700580d0303142c043e04040f0340042c040079400104040052181c0c80c0a01480c6402d00881c600b2280785507140c900301d0303286500103034070504c00c03c0b42e041924a0f181421078055130007226070708081c0301080410b1003141d9281d0300a1005441991100c0100460200720708583c502c940d006002241d141da1a81800b5004803d0110520b00a400c404407450b42c40806200e20001d440c05041d010f0066442d04660150201c07018414280c0c040801c43d1801078000c2e44d1400400942c403c4e000740d40c4035890300314140211295680002c0c0b2400c820402040140d649541c0603600d8121782c00c0201d0b844802e00300495113400340d102d003082140f01303188022440301000203090398a0104086181003591f40ea00c14007003004816200307102a54028014072001000d1 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 362202859 1250 362201609 362201627
    0x4031215080715031d060402040c0302070b070804030809161203020c06130e0105060c101d0d050309010e01021c0b0301090b160e011115060307080d0f090503120a 71
    0x240300c68121521641903504040c01c6902024210b4403180b6035520a607014041e1010300300c059140350000320465069a80c440c4001807000788a150750f9a82010924004d60554101c15004929681540381003c0b01502244043d070b810703030200300c0d964002849114005601c0400d034845402c5800c0caa480d264001c410b8504040c000c5055001d600c03448805900c50501915103e2402d40c00e05c1030316071509582c01031008041c1c000c40d0003000c0401c000c001c800d800292840942814410008850342d042154071084002c18514900500450300035404550380603024500a11400000b088440358040c842801c0f4031420510701c0c003e22400c3e400301001000b55202029011001e40007003070304030040c2e80d00b801c0326204641d8505012580010300380700c81da008941c2c80441d1801e0a21100c030f4454403584d941c0d641d4400c1050f0010740d103540300086054074288204402403040804480e551609544040d1168200401520006065660004980c94000348011207064180401494080301000444113200 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 362204109 1250 362202859 362202881
    0x210414010c080408060c030118050106050a120b041d10050f010302150f0a050715141906050d030905101b39050109050f1302070f0614040b060405040312 67
    0x8000e00001515504c10300c4528419943c0d04c941c19a20742c1401c1c00b9060314918800b0b0035000710300e40300040c409030350060100c8003900c98078184486c0c03d4200c0c85603070002d2b048144040390424140312450005080581000000221440940300803400125505041300c8040319003180b6104101c00400c0035090580c42c0d03400850f54428943d2800407056408115680180d2001002802c00644002071013501040d0302000076950a0510204600051245211001801d0300d005c0050b400350750700b0707012403542c003240080c44060b101480000e00c0b401d000e0862040e510505005161030502c80040d1480b40c001d070b40148000511410420740d464840c00b0b040d00e4580301d02840680d541200c00b425215014030300900940040c0301e40d00403420301000400940c4164420341c0600155580c00c0011758640c080c003000d0032024400141c544605090006030703209400c0001c0c085078a001c1d60307401314203440412a44120f00a84509080d80ca0304170502088641c102c078003400003240d40c030500c41c0c1c0d076581d0f8101d106605 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 362205359 1250 362204109 362204123
    0x908120403022803111e0d021002010b15030f0f070f03020703090b03101701061d090a020a080309030c01050c101a0301020d06151403070c0f0f0302210414010c 70
    0x10841c21108a010f0015003050b00d1600240c11701e2038651071300c03090005650424081e102d544440d600e0204c0d10250045c1d01c02031060a181c4a04129503200b5444003580410041089241000e4101448a00d0b442a941340d4030310340c038200c00030383c004491100c49030203400250b681c603400019440c4200c00a42011101300c04100e40d1400c0001c0c5000c103100a14003508100011161151030080311601120094000741c4099041000030481343d48440101d0000510071902d0003401c0c1c5d1031106690414000d450300941c003004003c00410b5800000000e0001c40006404940c1724151090055866028001030301440d540886260b024480d41a0010350503210380780a101e8050009100180c03d90f00070075802560780f545c84004024005581e14001c51100d42c174180546280f0f02400307883c5252100500d40c109100c200300520040111291840b0843c0360490220440c25110b81390003902e90801080c00e03a01182002d80034424500e480040b0b41c101d07614800138040580130440151400050410152002 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 362206609 1250 362205359 362205409
    0x6030a090c0b0703080f18031210091d01061d180a0b150109150c120e040c050901170c030a0908090406080c100903110f1c03050a090812040302 63
    0x1100070040038003140b130b00c241c85103040c5280ca03542d0401080740c010b00000352602981520100d1810101c103c1d0407026007103154001e16541c94211b000325500070341c842c0042520705083c2030500d81c3c003901d4030115080b40394002e0001c01d0f40c1780721441201490000d080d0303020168901181d44040340189481d9007071980d100ba0b50840340a81c4a02c10010340464241144403910109600a0340c6d00107e5003019003a580006101d100011000801c4a8401140100801078810b104c488250003003180c601c5081d0010000d00000ca502d20006010340c202c006141d000c2000ca28016544605102a143c8140c1c44100d145040d80c0e503600e0400003501c02110140c0d0032401c00c000600040e2114000e62010f0500900140010780b40c100030f100c0c1c4001c0c07031100b08040103c000002c5c00001c2130740c1401e0b0750300380d07046030806910b800000004a0130020f50025400100b0100110340400da0000040e00103154551030304031030a0b50f90032845881d15520442101c00c294204800e000500d0b054604080740d559400c22281c0c1c1d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 362207859 1250 362206609 362206619
    0xf060907051e18010906050a0b070227010803040603050903030415020d0b060d06080c010809070603090c08030712110307050613030e130207060506060423031c0c05070e0606030a090c 80
    0x400219190500b803c0340782c55005019080460050380010300040e00c84142c01890105035007900e00a0820003407140f4001514004858a0081d00381141d0f06021004507141d6518200150341c0c1d0712920403d0082410f0800140f141c45010080d01d102c0c90f008074904070020541180b40000b58840707409a040b07207a0f5001e40454075101c0300c1c00389c04003140310000041d006040889061520f20507442450411000c0e004004c440d4001141c9403046a8071070501044100041c5800304081d0080e03003003101c4511011a11b4000d110403805403403170480c1e1039190b03001d044d0450540c003900e1344904800904164050070105000c41c54214240981d0b03030103468101d14a59031000024035401e021480001102d4001c12008107200861041300d4108000f150004d01d0140b03400c1c600b0600300380311000020f032120a00500070450310180070083c00300654002070b14803800e02c007201800005940c90b05960700d10680d1004038280500042460180c10300034807640c2103640f90b44010014141c00789040b240007400c0000051 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 362209109 1250 362207859 362207869
    0x90a020d0204060302070203010f0605011416120305060109050a06020307080c0a020a0602060103060c050403170901140a0f1e0813050a080d091406060108010909030306080d02030702030f060907051e 87
    0x400303003c3d50b5401583e280c41c140109420360311001c110302d142c03c1ca000810081c40c1e070011000c6581c009220310864072035104038001500b20016280240c00005041c0410b240c841d4113600851241c00240c843c0e00c50309880b90309000500042d40030303440159004000c0a030100b0744410207440300008102c101c6420404640c08034413a50000c0d480b600241c0c0c00300c8014001c028140c040d141d0301da02c140c50144e00301f91841d2100c1582c45080c1c002c1c0810200009003603102070340f251203800e44000400107a03550fa009084402051075891441c10701c00582440006c07014402840b42c1013074200c0c03456035060429200d075510202a8400100101c996101d0f9400102c00503020b8000f501d05245001030000d0540c040f8103190045800400e1410309503045042084501c1e03812002e414151090650700040d90a00b92500b80c0007040ca075001a500d6100d0140707083d095607800802000d480d442541a1051070041d01e098581d02c0c202900c2520300303504501424041410f05100100260443c0b0100c0c9221042d0080820 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 362210359 1250 362209109 362209117
    0x106050a120b1609061202070204111305040203040c351b010f09140409050a050f010b2707050f0c07090b0303040305190f0b0c0333090a020d02 63
    0x100c01c24204024a0140400c0d0b40b11698062030404020001c1d00480800070004140c6000d41000d00402d0104010940200d84c107a846455016000b00107110391801d201000c0e4000c1e8400c001b6841c1c4501e000710300b90030280282c9005a40c007040b42c3d03260508044100d94500200c0c1121045042c4044d9007071882c02d200c282d000e05103502d030409450803070411810640c0710700d00041054103003c0c46d07035001002e0030ba002407008103d403090f801d8460b06003c401e000038007411071014050454401c0e0201c0000780603012446900742d080c00b900070080e0464a1017130010a0450200301419040207807240712402120881c0780750300c40740a150582c135000240a0301c030b038079801c00009010950300190041c81080100d02c600d280d20075049000314200340c42d42c4d45042c2c1d02c01e0200000f82a10002e00340b80410004180700c1040a1a0700c0f50000e901c902d0138000200c41500120303240d0540020000303c0d921419101c217855401e50054842e069546d254030428010380b031070054040300503240d00300015114545944054 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 362211609 1250 362210359 362210369
    0x9150f07030807020705010908060f0703020408030714071d040807020d0c031a07021f0207021302030705070b061008010311031e03040302121603150b040f061e08120c0106050a 77
    0x2240c1c070b081c0680f00915280a6400517414040c11580601c400c02d40051950b07030105280840c107050780c0d2011011400389c002d40d407141c012880080340400400943e000d45003100801241200c40060f03841c2c1e0301010450000800d2041d901c2c6a001040102e0a0f5800030300c4003500260009040328442d44c2e840311809040c4d80150b401000244032901100207441056130085101d00c000c0c41c840051026402d140c3c1c02d44031480102c5c5600240010840d00c40700c0c82d2101c002c41a0408640764502805c000c0c046a120b980700310381440140b000038110f85040703416000d00900342d84d55000280e08580c2ca16031445034032660141c0c1442041c605840c4038401100d100c042c8180705016540ba0b6283d8810300104551804295200d0b801070240343c82002c4018103100d007140c1e009008150718040d00004c1c03030b00400c01602e03e10b402c541816001c03400401c254101c3c104840e14264203500b64240b05d041005455918003078106190010110101a85403640203020142c901d1000021030030307628400140f1080c0c0030740c00 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 362212859 1250 362211609 362211617
    0x306061b2a1221080907060e0d02060c030c0601080a080708030c1201090605030c090103050a03080c070512070c1509140a09140601090609060504030b070e040e011b090302010509150f0703 82
    0x1002c00d15000c9000308440000c1c60703003000c00d0130b42892560b245d2201c480380107000c104245030107415a03c1ea1100d00100d59a90090030490340c4101001c0f020303072203501c0503052034118030803280005180900081c0028100c0c0e0802942820300701e107176540c40050b51000d82066038004090145503101380702141d24a0080c02511000078145140c90189410011800c980345e205071b0706040100003083c3c0210301c82c1e180c135038185852046580d804180d41b0b054003400744090004d05c40e48000e0180107c03000d008017a00740c081c4d414040307200d51f540145e0803500300d001001e07000038103000010070241200f4829600001401082501c0300ca03140d1480004480200c5117209010240c039040c400c0b5135800442900c0681141c0c07910400c070600300b0304090040c3c415444020500d24480d0002060741384100401002e00f0740051041c440503e043c1d040a010340f0043c03c03181ca00600a10008180d0341c0a18800000c6a0b03040e140c060130311050800304000c003007043c41d10807a0752408010300041000560020013585102c0c0e15 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 362214109 1250 362212859 362212883
    0x509030c100f09061805060c2701031107030c051c2003090d030e0f0609010f080603160e0402040c050414120102071a100b0f160204060b0a0306061b2a12 67
    0x509a01c2c104001d012315402e004108943e80d62009031200e60b09012036015002c000d203c12500040b0700030801d440300504904008500782c810181d010550201c07039805401181c0e691440b49800004160b4210444408110505401060b07600b80101c10741c40c0c64041021b90341420901c0011400a07120003004900040214041140a181c083c140021000d01580c81500300034a800c00603000c410440394a1040c000c0e020000b800030b5030f0402286210004800c034107403040c1c0d6282d107030020f611301c10f6604078481c070705005503007050a200300306460803640442101000500c000080c00b0314004140440803640d50200f00c404042040c00c010b40d102c1c3d20010030400524a04100754a00030311032600014810340b4100001c58047e9a49002c2e90300b0040c4015902020485a1001600030b080c140e00880c9844004031710807064a070035611a8003111229214101881c03001b07600e8280c4940128801030103842c141c000400382004200d0340c4200302c030124000d14950764035540c0b83c420b800d5000c602196050403240c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 362215359 1250 362214109 362214113
    0x6190c120e01121503080d0e010218010f0c0203210403050303010b03191811040b040f0f0b0306040f03302a090302040e030d050405070501030509030c100f090618 71
    0x1d50700c2026003007407030f081181d2141c0c401140310050711440050f14840022a640c8880c0106501000e1540001c500840d41d41440b407000c40400c51580005602103900f0f820803005190241c4017a02040d0b5004005d00f055202c11084c0d0386c0d030081c0c4042c0513406601c040c0700200004e0000c100550207428403411030343c1c480c904044000040d00402035907528407410130040400083c5036550042c440d95001c040c1c0b411004040d80480c0c01801088012a031190070483c61181c0700c207841d808404400b84454050005000c41401d141e51020250b90041000585060040100348038040010b81400c6a081d000044600b6915995405080020260403c2d60b2540300b0203458090180f4043c440452258140c2d545030380000151844400b4031000e4012501c401c010211648103004035141d0b0b0720b01403001c1106040600f0050743c0d03000940940e902191912010540182d0000b0070780302d40c4e1595900070244003d07035100c0071000d0900c04441c030301996200e008030340c000b81c800c1c02000344c501200403605610f42114 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 362216609 1250 362215359 362215367
    0xc070909050c10090603110c06040c050f0402090901090203040812010611160501020604060c110a0606080705090f040f020a0b031906050105090307060c020a030614070f030b06190c120e01 82
    0xc5044600c18001c26958820f000e812180ca80b0480c2c10038100002c0a402c01519690117116049400070940145804c010401c4051825038083d194152415800f8585030000d00c0700300d100e0050a03a5000d40c1280c01008580c0382900255070040c4520328640c20309500301c410240380d007000c0e0804800310b0001c2c40d81d5004d03100d041020501b40c0b002404139041c550318010000c1c0d203031040038002404c016200d1940c20680c40c0216030b140100d44a074822201100d0840c06c003034004003114000d05000c1c0c05030f02c0d00081c03c1e00c0c200b0304180c02420300498015182d00c0790742c0c540307010b0b8403404012600500000300004100b9040c1d4051403080d00c0020032140007400326602e610071903001c1d80140d8140b050600c0b80003072507100041c1c844203454840c140508904001d000140d030481c2281c0c0000c02260900300d0000c698000301e5545400790f2860384a0b9141030712658000d07000c0c2c03410000d03900e030429001d0014140c1140e82c0c40c1010030551550a01c44030350b144c59120404804604200c1501041384403680410a50b40 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 362217859 1250 362216609 362216623
    0xf030f0304061205040f02010e1801081f0203060108130501090807060506120a0302070b1e030403030605010206011a070206210a0e071d0c0c1014150d0b0613020c07090905 75
    0x1c01c3c0c01c0040d840e05d50345810200c80030120184c100034020f80070800302d46800d8050a40b00e01514074504e4150f03901c0d0021503440e4240c080c0c02d1640010400705c0b000040c501d000f542d020f1803058540c10140d075a10a0b001404240b00d0b8426283c6648400d01440401d41c00801080750b81c0c019000030071180b400d03000303000104e00d0001c81c0c8243c5601144615001c254003140b000c1c1595481208a0750b20344c1c050743e030078a02194000014041b80800030a220070140c2503440b030f000715002a025a8400e0380e90750399a01da8140c051040d1003008504001e503100514003040100000d9025180c18084040c05c0c8401c1c03080c10b48100e80502549650b0001a4440d400400050f002020782410144400d41e203041c0d1480c40d40c1005e030040c400708102143d0004010814410f03a1000301180d0010401c01c00080124813800405075104100300010b483c0c002180c3c2890602e500c0015040f40200b900d549440b42481080e01113512541c140c82d03030038072140049013400d0045200030503c0c050045104002800d0144c24843c0d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 362219109 1250 362217859 362217887
    0x21201120c0314070e0108030705120c030d020706020f0d050114030307020f04180b0f0f070801050117040203030d0e07050a0b0a020d03090809090109020c0c19090504020f030f030406 80
    0x1440e2030003a00040e1000710007019240d0001d400001d0b0456102c2e668540000c1d07401007843c0345012800460804000005000107038018800c0f034001200e80300244025114081a80402e0f4004004544904071207400800c0e0f107078801d010043c500010a0014007a0303801c806d030004449a103a00040003008030705514025429421000ba519040f844c0d400038401c07260111115008a0700c0d80c888507207048600c5101700c0003640152904a00b49001c001c2004075010803034081c01e071f21640300086042c10f0301c105840d07416140182c4842405005000b5580f094001c0140704a900d84020480b90b4040c0f00da40c0511030780703111503c0003840c09904100400c05c0e81d021640002c0651202485000c2d201940020001084241030800003400030582c20640703007a01c038600595400848a03000003039001c040760300502c1c401034240291402110f07079404111000c080e00c08400103800c904030083c46200020361005400c1480203005008440008010904140e404040101d603500007107810032400da00103480c4800c5907 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 362220359 1250 362219109 362219129
    0x21b190603052e030201032a020d11070312030203250309022701210f0812060d050d030e01061508160e0604090b041d06150d120516080706021201 64
    0x321458001c01050f528400030b41050b4482e581450744a4070500303c0080c40040391500d001c07980c40c03440c000c1c1d03441c99403001c3c07800050440c0a01100401d00841d043c81600d40c4031601d07441070340700242c049000c2e400207807a4180034501420300507030046c810f48035279204003002c1c1c8001c03070030386071600421501a13070100c0c031082c0125181c480c40a0340d41003d00030314150b4a00d107092808070903000e01c0e1400c40040e100c00c003d00000600d00458203015010025040c0400985442c01a983d160001e21a4480b80041d0051240e03001e240c000d1222030098000209001d580f100010f001c540e541c002a02000c0c0343c0c480fa0010408030014400b40d041555409610380701c2030308040d4542250034002c01d0f07040c45184244110180d40d403c2000d1103681d035420005000c0c01040800c000034031f816041c980c9514040d03c0488000d120301c401e855803030418040c603c4501c1d030130590745040c00c0d090400585e081d81c4040f0f00245942480324803a00061400360144c82c007903000b104010380300c0941304240c2d040e005040e048080c80d8 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 362221609 1250 362220359 362220421
    0x237030e07141c08030708040210110606040e010b03070909030e090c040b03060d02120d02011b020a0b040201090302101e031b14040f290406021b19060305 68
    0x1081802c088021030341050f0703480410700f41c4000904500380c1c082e00d40144070140000600148030352001c0401c1c011030089500b4580120f80e0752b000d6603040b1035402c205085030022000580140342c1507000004034240d01d00040740b0040f030440080e0400d61280c0220035813580ea50b040a0515a010085c1c44050f9415a80c00c8121308140940201e24015440b603d4621000080000d42e2074503011441142103034080c00111180e0119010151030341d900e62a100010340c0ba240003101758209000702100321542c02c0e00500b158a50070344814988000041c01681840b01c1346400000680b00d0300744c0d41e50050002da558004001c810340b0307038000a070704606400d02090b05003c916581580e600600761021202824144205420b032040b404442c019035001340480e4900000014007a2104071024410408102d41b141062400318412540c0b401036010b8940140d0100304007107030004103d80e01045500004240310550300c00000e6a4600e80340300c3d0401d20020b030f11041031041318141006c0d000d9a00014648020304 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 362222859 1250 362221609 362221619
    0x3120d1b09121106180108070302030c180414070c0b07020706052b060b0a23031303111b030c030601140f010302090d0f020a090204080a02040237030e07 67
    0x1614141d4010b91100321204412002003081c05905400c65500260a1903180c50610f41e0507643d03921800d40d29804201000e0000e88100d100384200c070f00c65404503000504090110307444040310342c0041c001a8006907121184100603c503000207511031051992024070f244058506102c5440d006851003003958001c0b10240800340d00841954250b451007590b20454405000c42065801c403003034003e02c8454905000440d03654402002040c298070b89880b00c0c501d500401d1118400d0500505005058001c02c0c4089031000740d2112030170421501078944000d006410f1500b09081c4518403ca40e0031403044e407010f1141c0e50400b84107502040c0401c9002d492a0341c50038020410001d0100c1c181c0d880781d0328680b008500c030b0f802541660142c3c80c0251480664805503e04039018201006080c1c1c82a0200200014420460b00884054452603030240c2542801c41c2e0900c00690005040c50800d002e035440000c1446840325588010480b2600d1100d8a10b10f5180015048a8802d50304543c00d41142e101441 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 362224109 1250 362222859 362222867
    0xd0203090d060906140103050706020f07051f140c070315090f0209221a09030406020a20041b031a030a02060d020705100207050c040606020a031d03120d1b 68
    0xc00c0740e410a40102d040c10152820304001c1c122010182051301d041c02c004010f0260000b440c50903141b0707503000c461f1152121402681d0302c003628401c09910100300300c1c01d0780070802e031031404002c0903580303091080c3e460242044004440e00141350041785540311003400c10034880c01c0c030f2210070590000312042202c108152650100c6829280020380156036500100300000007001c0c282c2510100c0c15519a6404001e10305900d540500e500003141c0204076601080c5184404021141214000e400400a0417201e50300c10044102c05518155805400c0040b000300343c45501445004180e00308040480c00745040d0060100d40c500400a1114030002008031025200002d4118141c1e8044404503210104100c11a001e482920b100600601400d000004940300315005400000e200e04241c070100f1b40001c09200031a0094403601c0016403110701d0705c2d80400c1c0111450042100b032001080030804814020030720b40001c44240441140c000107040352a103003103105500e500030329081407000d200c681c014014 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 362225359 1250 362224109 362224129
    0x3090201050324130f05070e0a090e031e0a0206010f050d150f18110423070c02030609070504061a0901050f0408010c211b140d0203180d020309 63
    0x241011144a810161000c201142960102d10040500012600c0c40011001403c2150702c10001c0c2c90520012500d91f90044c2d8890345442409048030b000d80c1d01e052068400b414290914404500003004204242441407441100111220070904e40e507003407001009190107016401800005990304092090f542c1d4000e58a0809030891508410382d0100c446e0072000f803086e40d0f1500702d11803030102440c0d00c201007540c0001c5140e00500c40c0074421030b899020b1005507206040c0703060213012910400c1d1000481e2445d820780000f564034202c89108000e6000c80d02c0d01d50103858a0702039500c4103034104150700d054081c00340a400b0b0140d4001c0c01d002442441400f50198000181c103003c000b180450454420f1801d440041072800c00901030040501c2014007000036050880e40050200d544201d8048450302900c1d000c1c4045540210008408181c11608a20000c0ca03591200000b000b0401c091a0b050000d0350150740c4041c0407408005080802e07e240136040d00c400401e5400a01030381c14207a888200907 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 362226609 1250 362225359 362225371
    0x10b0604090f020d0504060b10050901090905130b04050319030e0d210501090504020405060102060f04020609040212010b04060906080702060601140702030d020c01081e0a09080912010f0507030902010503 89
    0x820b480c5204205040a40980c042150815103000c08110074410300f5001000440d40a46d45180741080c003200840341071050758030142c00304071018010428042130307610036580011840e024000c003c000390b4800d1140481554162000d41c40071890064000c41d00700700210704070050500f0000361b885011100c0c1c45a0b03003c034000301800300400d00e0840030a10340d02d00c80803996080c04c0400c110368481d14890b0080c901070310140e00030341c507200019125500006140e40219404210700e06a9074640e0f0810902e0340c02003503083c0d049034082c0404058020101c03902806402030b0700e00c80703440b5820610020414a4550301c40400c021500c030030300800c160041361080d0001c9007031030000380415100c80105442e02c149034009401d0b201d0f11080d140703600da0100d22a84281e00c2603940040a440d0f02d84062008101a0390341800880f10a0100345100500c2e40030215080c8216155820701246000180d2952113200c25465a6512000c6a0a132500d5074418254440081c0c141000381a8981e00000e0147c0001060 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 362227859 1250 362226609 362226611
    0x501050c0a080d110a02060901180f1106160c0e0603030f040e04031808010f050c0a0f0c0f21030e070b0d09020a0e010902180d02030a022b030801031103010b060409 72
    0x61540a040150006038a100311082c4e0666660202c0000039600d400c1205c2c20400e03546801d094181802c0d000b95560480c40c0c0101c028402d414450711880c07030802c5040320080c4c1c0010100140c603100c0820000961a10380900c1c0502121850a080c4000311701004100b640310743c200300140481e102d2034806403000c5d030344078203108403885d980c615055402c80c807006075400d080c13001054000fa110005400007146d40001d40c41c103100644860304465070500490100d90080f41d102e12400c1030681c85240e030400268040c1580b01c00000d4151283c40a00c2084402110246048201f1340b12260701809074502550f2400e0013805580c0c508517030828240203050000800c1a102c4950205540d502e0704000701a05a100714445256564500e0200960101414000e50070140c07505442ca07152501200c020550050007030045441d0329170800400040b41c030500c011420a0400059172900c0560640e100d041c8a5102d0100075411340c14031001c1b018400008a229a050101428050b12800c0a407002c83e009150 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 362229109 1250 362227859 362227867
    0x50901090816031103040b03011e1809020d0b07050a0206070504060206070f0c14010e0c01081603020f070602040303021005281508030c07090e0a0b04120507150c090501050c0a08 78
    0xa41102c0f1280701600c42c900d1417002040100f00d00040b140214102c80d5040c1c1c800842881c6803101c00c43c9000140300e496420401100903050203840d0b41c00030301d0810700c010000d0810f0344040d541c0b41507405065801c00d0005201160910015804001642d0003100905040d420b040c5400e000940d01e130001002c5504005d0444c94104049008000942d02c0b83d1344044e00c040c0d906038491a80b8024201d403090003103e8440c410822645502031030505000c0e481d0300c0c42d20510b0b0418800309401944c070210002c0c00140d010803408010600303504c041e2010b98400da0160140320000c88000c03041e1000a032503155a10502d030003210760706030b60440e613000d0070010b040301080e02038400404208584540e03100c1c00c40ea0200050280030f81c0c0e004030b0502c06480c141701c01003151140d6940c3c569603a4164031001000342c5c0f50070000c100441d1414040e80d6003001c1c246403491410801e95100340c00700351130100a40c40d41c2d0b01c442020160582210741c0f4000b5200070300c0c3c407900305903008901c00d50314800e44c3d2000d06200400a = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 362230215 1106 362229109 362229113
    0x50f06190f0e06120a05100609110a03111902060f0a02030c0406050d180f11010f022802030304060906090e270a021203040504050901090816 62
    0x1aa060354000c0c2040402d00030b8000203007140340d020304410080b1215080400c82001c1c4503220724041c1a0204480030f00d01c083d41e00d2908041801804c1c002c40c80c00d03205400c4242c9041840910300071449880041200701e2910400c183d501c4100782e0030b027170344080540009004d030082d4500d0380c14a00f1603035a071501c00200d0109591640c0d40341d500300010000c05102d10007403e0b50303440c00000046c0c01c070b00c8080503003c284044801200c0c01e0070501d040c40144182c0c0409086044c4007820240601c80200000a458049006072070300708011421081941c840c0400034144007d501400303c0740e95a480f81000f40040f0078511411000a0507060b000c6602c9141c6038407d0f0281c0c80549058410340f107034604550900364124070307603602d500c2202c030700c0c0b00507036104011040c2d0200b0101c05150b50b203040100b403000b510740c01400c0380c100b40e041114803000920340c0801c03a0311140c40c01c5c85e213002c014894 = true := by decide +kernel

theorem cover : BRFrame.Cov 362050359 362230215 := by
  have h0 := BRFrame.cov_init 362050359
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362050359 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 362050359 ≤ n) (h2 : n < 362230215) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
