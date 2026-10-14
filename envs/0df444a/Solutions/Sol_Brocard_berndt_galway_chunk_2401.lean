-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2401
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:36:31.970985+00:00
-- url     : https://prove2.me/submissions/60f38ed5-c137-4701-a07f-8a83260537f1

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 431654676 ≤ n < 431834532 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 431655926 1250 431654676 431654693
    0xa0911190504020403050a0506010603090b0402010e0d0606030302011b020c030706081b0c010c1103070c0e131e02030d0903051216120c020a090603020310090302150a02130e071b 78
    0x100250b800c544000303000f205000d400100b44540034481c50864165070b0b29002d04405581588000500303840d0075202080040d030103060000d03940d640140c28482c89442940304c2c1c01c1511120391050300541d5607418140c043c00c0581e0705100c444070003030000742000c01c4c800000c00d80d510440d02c9030b101000f00b40808943c02c000d16143c1c1c001402c03106850182c9600c01d40d6083c034020718001e001d64000c00d00b0b8281400c803800c0007000380c3d038440341c010745081c945c0c0d45840b4801440c000c006103a10107010840d100a070008213600e0b40d5030b0401c4d4507026054030405141c8107040c9880040d114807018803001039010000680000703402d0610f01e03524214161240903403500080724440c80b41c0010080540860a1000c0340c1e03116651000c2d40b030023180c1c0005416031b01e00d284011501c00d808080c0d0190080895a2408003080e00a48226880f910413104c2c16010075105100301e134029120001c0381360300000c8039083c41e1810284040645103078130080040341000000600010002d2031003200d90100c20300118103001624 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 431657176 1250 431655926 431655929
    0x31e030c0c12030604060611060f04050309040c0c0b102702090a06050901031b0c1b0f0e0f100f0504180209130b01080c010503060613030f06020c060a091119 69
    0x300122242070850b4048900950011203860340594500400011003501c101a026002411040a081d0740e0700c0740b182c10220040001c2c001d5038130344000c01080b661501c40303104540120380156540b0143c0d806501d03103d68181800b8140303240310300c5600300910003880d8111790724244082e0441800345c121f024400d1600071b809540301942d03100101d0100010900e07001401070a510307000340d0f01000429206449076010381c1040344c2d1580001c070400920000900000d903090456005190340c024540d40e40d20b007070502c42c6140e820035030340c55140c0e50038003001d0103801403044d0f0041110303403906100a0a1030080c0c3d17004880d80c0305840c81103484103084c840486055044200d0160060000741141c03030100c8580500403540d49041b1041d086103800014041c00100e4200d40a1205030b403502e00c1d5449400400c0416044000180088800d00c2c0000000810550203c2c1c0c0d420710503807002d85c40f1849000f240f1300b00390000300740c041c82a05020308140020304c03900e0001c0345000c044805014601d03a600c1c802c405440a07 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 431658426 1250 431657176 431657197
    0x105250c0306060608072d05040b0a020304031b05010c0f06200a0f020610090902120102030a09020f0909121b030403050a060c050a090504020901050c03120105030609031e030c 77
    0x16a0340200038800c490304001c0c141c80c035a448025994981550071910b03045286542841300d00c403142c4403101401d00d0181c0c2025442d003494540e003440e4480800111130b82c0110069405030b03000040400030043d42c42141a4002241203a80719207501c1d000010f09a040860002400299039240003820041c282e404901c0e00e01e400140000c4008500a0000700c0b40c0c84486003c020554695510303000a20010b84148680d0900b103080c036140349806c55080103003007050380032a40071501702c82d6904582801d2000d580704806a010224803103041d401804243c0746040341084c000c1c4407410400200d050300150101034109036559250343d40d21343d4101e6880306803100010082c00e0000180c00000d00c5000280c03000c40900030001044002d522030070654961140100c0750001c203041103c204a0b83c5081d901410b480041810110b150010442d040c1c1c1c19075100c603200d20b41040c0400014455410b081201603072068081004519008000c082000340c00340c0105607c8003401d00000050004101d00c0c1900d060016 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 431659676 1250 431658426 431658443
    0x32a03040302150a06141e03030c031e040608070f0504080a08030609010902040e070c15230604060b121021030201140403140d091e060b0f010525 64
    0x3440d01d8029207409882030b40c031841e44a4000865040302d254462107040341c5018014544080d0200c003404410761220300c48010700340c9840016282920140300828840c0310080107181d449000c21040c090081202402c0c1008140c11f1006210050300401b480c0e802c1034686c18141800c0070b0804c411100ca01c01d54000c951240106a01002004a010081c5004400c201c0361141e0680e20b501280c0124082c230700c1400e07103404e40f800108028a0041c0141030179280666110b14042e01128920f4081e1803507002a88124002604035181820600b0301094021100301d50511600b883d00885412a000d10018404000800740100e2944403159015100604246c41c10308807046e224280034401c4800c41d1020307005542440119403610060502551059a04d901d074201c01d040090440b007130a030012401c001e017403680d070b4603e1404550040407860814120824103d1180064a0224144c9102808141c0544056001808181c1c2c21906907200394002d0070910540c04080c80c401c800076140c58801400180 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 431660926 1250 431659676 431659681
    0x1312150f020c010506030d0c020105070521180306040c14040902150a110c0105030406050711070306020408010e01060b1905041502030304170901090b0c160f03031b0503032a03 77
    0x650094a030b142c4401008001e16501c0c1d0040c16103900d6004400c00c000340c070f00030070400158082d4000e41500d5000702c04a85804107542111821580387c4001041140700106000e03810402c1e48403054482141540a0411400d0583d6841d8000240c1d020b4100c110742015580c40d030304d48496205d81549500100810204641c1288aa14503440401c04000152a080c1d102440040000300e40b0401071040e9075003451072392903464180061402820503820401507034000f1034140c8042000c0805503000e400b005941c2e40c80c20b0030040c02c681c4225000b0030301780d0416408104a0f04000b059030240e800049007d10441c81c0c0e020216600d104035000380010b0902c51802d8ac041c03d90000245100350311454034000c404102c1c031016001030241401e4075001400c1d0a00501100da01c0310080c0c50f410b86401e04850000c480078040b4403c04849400983c4800f40c0803201300141a03210b0070384003551811103540381c001041c1c0d403202616032100034544003000307c00f1030030400040d1070307800e01132003450201705c0a580382d0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 431662176 1250 431660926 431660951
    0x203070c060203010e0a06080f03090d0809030609060a0c170c07030207081203150109030816020102240f0106050f0d0207020a23031005070c032006010e090d05131215 73
    0x1603501b81c9024044518040000c603100c900000d170001140c440c0c800450070447c50340c04004000704101000c80300071200b44450999501e0802a440c00b86100310042c20302803911400803002c54203403600c180108000040b4080c08141e40340b00441d00443c54540596480e080e50400380e103881d103a41c1c420172003440713141503030b6401a040c60055401407181014080c44410700c07000448080c405400040c0c4130500400a540e40e600f00c070f01e480c51120b4818010303501c0349212003074526003003243c1592500749031108000300002000c00d11061805880c15040480c14000e00c403440c01664091505c1885507140c3c00251041556502060758005194048915020540900300000c45444004500e8040e21500d0400050402e05005030fa1003035496a03102a1001103580701201d69010701c0c48402010000b0841e200101901440328a001e05103070400c1017290b0519041c140e00d00720298400c601008010b02c4040b540000845028007142c0740008a044002c556090100c80316a0301e600c46601246004c0511491 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 431663426 1250 431662176 431662199
    0xd031215060807090803070c0612060305030a0c1506030803040b15090705180405010e061306120501022101080d0e030c0a030506060a0902030114100c0b0403020714041a040203070c06020301 83
    0x4010075916404240d0751140515500d018000c0018048c100e11401400302610454071924a10340700c050204500c0d40e00d840e000d003150b0041c1009000100c41c2100c0200b801401c2504902c14122070008100c06031031038035615000e0001800c0104515069008907040d807030304100e8a20b1818004027a098075082058025126510818604da400b44c04081281c4a1b45042d110341c9041f41c0074220105081d5543c14100002103030900607000071a41e95080116850104508210131705205400041c0d50303000300d08845c07824101040f0303150700054451005100784e01c1c02180c0400425141d05107041440c000000113420525244921034200f44c0c402800400d00c00d0000e09036000b01c205461000300c4544598210003a44807d00640060003a5001103419030305001ca40c501208059281c10f103001d0000d65641d4000240540e01500140e11124052003002121100104981c1c800c9408111504028070b04a40c8070100000c820721880c1d010000410300c2e4095101c1100c0369600c08001c40d60303584c580131441d81d0f = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 431664676 1250 431663426 431663431
    0x20f06100513020a080105060a03060905010e060301110403150b0f0d05060f0114150c010b090f07030b060a0c110a05060d061e0608010b030408040306062705060d0312150608 76
    0x205032450301c2c40c0400e9401d18400c8a40105040e51041c485a08140c10b012050388004030312410940d0300c00000490500901c5603e02809814050900b6820113500305402e6a00600c8840c2c07480100f04810000250300396200c0d0300640b401c001c003040d080480300004211030404c42c0301c40d0f00b00c042034a0410801501040007803203003020340c144080a90303c40b100b844c0070f1018607182c0b40e0040c845880a613601704405008e4278280e05068004030384441030002250402c88155510303148007900009001071680c16000d002c400100607984641040c900c01c0e401080740c41d0201d005401c03c802903011190303a45030070f00d81802038403001e005103030781c0c0c40d40582d85401051584204401541d019810405011600c09280e003120403556480b8516404c0400f1850154000b0b0011101030a0400002002850500070f8000034002480f844540d800310404401038000c40c104d000c0a06450030013045556039407074800144950305032605070305501c12401070400400040c82024400c518001c4002180340c2d01c42d0340d4a1 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 431665926 1250 431664676 431664679
    0x2030a090c090c09050613090c05070308011d0a09050109050f1005060603010503031b01020705070b0a0338030307020613030203070b0f0a0309050c04330b030c0a020f061005 76
    0x2007a82e99540304442240e40a00000d400101c40400130000ca00c2c122010700066000081c0da1411769540300700c0e0004460045540720049000420785805040e08240d8684c010450a103000e04003d000600000b02d2003002804002010364591040c01400000d5201041d183d6006049406800030002c03030603590b41c0000c0040c3e071207a040400058080c10802c0a40b41200c00240040d41060502d01a82c80c80855030342075801650b60901002d004110200300110041680000484c3e82d400c04a000400382c400b8030b01d00d4980c81c07031460030250040645000c140000c40314030303548040218041000a0851064103000396000d0004501d00d03c4104c01600b4203011684202c040321405655030300c0350880c80c0100d41c00250020401c3c070201910f60301940200ca8014450001e54006031a0400000c0480741c4101d0824102d89074600c904100c0700081070501002000f01d822082d107079241c218020603604c0020310200005d50040f41703031000380c1d00800a442282035944150740725443c00c0381690103956418030030301c1d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 431667176 1250 431665926 431665943
    0x17070905030d03090f03030b030a120309140c1305130609050102030f011d04021908030d060f0b0403020a0b090a05060a0e180f0f06011e0201020c0d080c03042402030a09 74
    0x180c08250292141030b201690000343e01070142840e403010340040021300d880c2605802000c0d246000540500c91900a04c5c40380d0b24005880241401c0014001d3b980c108a590303a40e101d81202c1c14035039074555040e5149550b07030501203502d541b1040803104d07803101c00c44000c14a50500d0003500401106401031032081e42c0071404109a6a80c60201b07205036803210020904e03030a811030200f8090b082241d01400c4046072115a03c01455841d8015840c690002d96120303074155442c10203000d185107440f0108001c202408005003094110740004082900c5482125078000d000038614240ea122039100c00001c09004156039164084400080c00240c00c1e0762505101c0c007015004048940c40010405006000c2e4604441d0a540c9060051145ca14084e11103030520504801c0b076000005003030010b1f544c0c0c2810f80e0026841e040304068091a2074480f40c265000d012120b0304001e080500003003030b03030f91080d00040c1d13525190703103d081e5480b128040b5000301e80700c60f8000410041c0c24046504a200c60910a9130070 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 431668426 1250 431667176 431667193
    0xd11060c0307051605060d0902040908031f060509031b13110a0e190608040311030414030c0d03021207060b030105133012020c15040c0b0f030c0a1707090503 69
    0x2c04003844541c0c0170305a88075070240b2550403541482d80c4800d00300c901c05400000c03800c6150311164082d800c1101d41461403140d500c6081101060303401c1c00d40c024402401c000c1c1c00c0c240300c07400103512100c07001c43c0c0b425599608502c40c1c40c16602d15103100074000d10902c003085805020841c41501c0d40c403060030071b40444c2d031b5518221300e00d0601990748560b4401c0480600c1c0c01138201001200c5c4142d01a00a0b4100b040c404054024503e083c4005d200600304500302075825041c0c031080c513040411410000c0c0c8103410003554000403d8000c641003100130000380c100c80e56180709181032002028940c860680640ca040c0401031106c06d0100300507041400350ad02034900d14401e84a01c01000c04844880425844a0000cac4941300d000e92491a8014416080513003001d403c840344030300e0962002d07450038203072192034148000e01a951180d5006840303407110303c51500021680c040150720016010b07105050b0b0000e0801c0d4101d02c140c1c0d000a40190b1200d0042c49400c10000c020004407650045a10a0040700381c0b = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 431669676 1250 431668426 431668453
    0x20a0308131104020d14090601170a21090807030c050108180a02010806010302040513020301030b10080a080a12050901060f080106030302060414030c1e010b090c090d11060c030705 79
    0x800788415400584210031848010511029400c0204034030b02c5180c032606030751900624600d09500c9902200010802585054105000c0780740200b6040845e40000d030182c00800c48803085000071120314031208041d01c1c0032039003c07900e80c80c559006418900425001008000e4045442000c5170350036a15001e45455007036500305c1c140130720301c070309112544504a004010750060f02801d40c0315070141070043c1416078401c00318403242c4101241001080d130000040c81000b018800041e04481c80d088206000f509204080e90b981600060107007104401103880904c0d64850041c111000e25030750014051414130185444c041c000e580501c81140f05605c40204900e10305106000c21660143d00034a00e94440d52583c140309527804003001400d00041002e9582100200030790000808441103c82a800050003414211600e40c0f03a4030307108030311000a20046440f40e00c10340c1c107c030508403040001300c10b56180024a06250282c02500201c011036042c8622038084007810030740b4025401e594040d0003028 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 431670926 1250 431669676 431669701
    0x90f060906080f060a170102040504270f020301091a0411030d1d0d0803040b0103140a0b0105040203071e171b16080d050f0619050f2b03020a0308 64
    0x2030071000400ca000010301d8200400c1c2c02681142e0060540184036131500c082c0d0344081c3c400840414103a40011741008541018402c0340341401105030007101911003501d4500041160160107441c6100c3e0a50103415580e00b94009800c65a114003001500f10104020320800c00088a05843d08250041e80c44540d090102f403144401c0c0072583d030b45071200401c0421300c0b03601200d070001c20b402c40101e1207410b001a604070019809940600e041034501e61440c5003038001a420000d1081e0103401c00f074507080004200450b01415100c0889002d07890341e44202e0700321104005401441002c03004107017810100b030f07004200402c80b40704a89036602507540d0000d251305a10405d41001401280401014000d030090900b042c00180c8243c822034030307101100101000b500c1d01a40c3e5220810144418050a840c03c000210000c008420741103d81ca03141c03000142128800a40f20303801a40d1290840c00716214200d01c0d0030441c66002d0088c1810040da04000b03540d0340340950200e0226a0401c0424030403003014 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 431672176 1250 431670926 431670929
    0x40f03021015060c080c0a210f0c0f06180320030c06040320070f050f0102010e0718020904060803090909150402012d02010f060f05131109060a090f0609 67
    0xb1600781000c07440c00208440f00340f82500c09440180003440103103c3c4207018080c15485078081d80b0252000c6422400041102d80a603101e6400d1150782024500280d400c4066090500d8001a1400c1154500d090420140018110040080780400110300401d608541014001d2031800b506490110300c42d0300c81650b0344600500815a90700c6400080d002904c6041d0113001e4111081449010342046080035189c02c46d0307074100d81450008150706110909207500a1005a33200340700a11040181c80c83c5035403030700700d44d00410001039079178001080c160206804586808a01038010031505994070a0682c50ba005200828803c01e000400305001c5840003801440c440e000021125080d120f50b070056800d1050701001e0104083c581d824040701c51489160208000060b80010815041c924607440c05c940003a000b40152001003202444a43c4a0b0800400740034840440012080d0b14060740c000603018020302194850800141d0f0390307140d503001131900b0803250b410303800280164a0310415103004185 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 431673426 1250 431672176 431672201
    0x308160c0b060d05010902130e1002030f152b06060b040315020c070f140a090606020d0e1212210705270310020a02060108060601020705190e040f030210 67
    0x22040800c50b24a4208000c0c0c819901c5500002002950380d40030824001c03800040c541c000c0e64800441103002d2003031103a40004250382000b1490342c03911081e840950a00070380701c0690040b80c06560800d90b11385404003002c065990300c0c4c0c030010107400343d10030880e01c10945080f01d45074240b60000410070032a0381070744c040d281e12103589200760460306485c50080d08116031a411902c1070350300000d051140b1100103000340002082c0e590180080d2000e000d0080e075150b00c4002064540841044038070790219010b001030019140c0b002c120602c0c5000513201220b000c20300380031400355030702c0c4c40d4080d91894001c2c014004000c030300034941040300b04601b066540c216282c402041040102d440c500900410065a000c1044c0000048e000d00c01c0c0440d15040380030103002c0c0d1047d03002551000d065010000c80f401005a1070040081d844c02c030f0f00003901c5078182d21503640140ea1034501241300c1d42550621601400b444850103010381340c02e0810140c0c0c040104010317030250080c60a202500400e43c01210406941c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 431674676 1250 431673426 431673443
    0xc140406080115030204120602181906050c0304031e1b0614030402040f0c0302030702010614030d05030709091104061d0a0302120a02130204030501050610120b0103020f070308160c 79
    0x18000c101c4006030800b0f0f82101c1056400c000101d9007c2c091003006406500a410040e124081404c407500031007402c00380c1c0c601c210309002d402c1031032055841c1041c0c181c542c070780340076a2280404000c80c1e01c0d50150b500024403484008820010011000000040050094465403100b000608419814506034040c1000040083e020f41d0203081c0074800840e04544003400001d072458065840804940113494503c002940000c140400b45609010b64806004940c43c02d42500381110000b07582e0b044a60450801c0c0400400000d40341801851400b0041c80810b070140400440d10307444404a510600a01020030707011120300165524040d529800300001a10080307000341950204000e4000030346078803031b00d4802e11300301c9001030720703002c1103201480c160310307070168541e42149031007802d40d00000d00440c050020602300920340d6030700c08054404030541c01e1000401c1005000101d01a1281c0342c14120640d10000b542c00c1050380c0115114480c03101c041c1080010303428000201c600407014803000d0030b2130b80d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 431675926 1250 431674676 431674679
    0x5060f0a080c070b0f010302120309030601030f0206120903040f090b09070309020f1e09070c1e1a010e0702060901110f0c010212090a06050f0f131506090c1404060801 73
    0x3402200380740c1d049107401124908040b81036441e001504421a00d013130100390b52500420841c10720040c245200e5001c0409542400b0050021075681c03141440003401c0c03a65440d9140040d910744204840000c51a0a5018414a084490507680b58020301c64052a400300090010b044400351081c08038024000700311008a0701d8a0404074050304444106076840341180d110501542d903140100aa0081d03a0780300404081072040410090503001403000b0244500910305034001801d44914060309400003800d090700c844d460a102505040345130807001c40040820010610281181c5075612a03142682110070682d144950903090301c042d0154100d11000a0081c00b11072090f0b038000d842ca40800400041c1030800a105405204d13a050307401c026617410904190701401000c3c014541d0011502c15440c0341ca0a260794041c04071140144028080740740366890008000c01010716030b10b8813450710b03024482151030354262001021140206400311705c01614000c0151070703c8098404441d02c5840f50b01c4183e = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 431677176 1250 431675926 431675947
    0x204050a0e0601021501060f1403040201080424020706020d0f0b060d1e0204060c1a060f090c070f120908070321200d080a2d2a0905060f 60
    0x1d0002900300c9040d07004424406001e190042d01c41070081c1090355550404448244010303190740c481d40c070300f8503010804004200c00741c5d800c070456a401c0303035101d800403005002403400b2403008502000c1040c445030000a41a050203241d0700500080960305030100401d00348034070104125041c40c1c2c6c0942c0c1004040c0500c015840040d8011070340200302c1003d502010b80141041760482c0c2c8150020008290f44c5000082484115903c030000056400e2140d501c604088000030b103004c00100840c0e00c0307123001c1800181c00c100c13940161703150950302070000c0d80001490b280007103004400103045070001e03616000c0001c0340d06000600e441245d8000000c040c0050066064400f2440300400e44402e1040c0c124980411150f0801d18111029020b001b50004036072121004000410240c040b05c442401e040c2111b190458050315001106200c10404841743d09030140a0085d15594070000301d840b03442001c03c9425001e100b078403000c414955454070f00c403d8480c003c001c801c1c0100140c1d041c1250742030190a0b0710 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 431678426 1250 431677176 431677199
    0xb011d130b0c210702010e0d0c0204180501020a0903050c2d01020a0213050411010806060904090501110c0f100c0f08071701060f0e01110a20040204081c030204050a 72
    0x700b541900b40b98509a80007a143e00800c21442c54443d802a114040108041e8280300710b803103000b5107a0242030040350080c8000d280d1403600502902c6542c0e2503841d5038180c0001041142103039400300c020f5480d41d4801c0c0010340208090310040d11203020b43c0e200340d401803a24400d04912030f4551003044105003a010f0414440e0500d848480d4158840c44072244007603aa40010592604030090020a07585014a00101603c07030b81000503040c0003803042800050b0ba9008295070b8400d5059070f000482c01c11908007903024043c0c0c10540740d840c040001707003e1300b000c0011803403003011001d410854201c0c03600106508111030510802e040000e0f442101d0f000e1079803007817110682040a601c0d103400d490f24a03e1050540d0502a8018000304002883e54420f0700d410a00e4a04411070908010035900b00200c1025200c81465078001e241100c0c2c10404640f441030000d4000840e4409807086440d41c0e100c40c5101d65a00d0314410a00000c41040f0b428500b007840f90080301d090302d40107031044c560706103040c0020a0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 431679676 1250 431678426 431678431
    0xd3002090a1a1308011505010c032001020901110c0901050d060908030c0403140c130b03010603050f060f0a05040537060b0f0306091b1801030b011d130b 67
    0x62040418500151080c07014095a00c60511180d0702a0344a0f0006903a2168010981c0652020b0341401c0710011800052103103681100c00030708004e0504501850100c42100c0c10a8104400c0058950a42c0b40c22905501602459201b030722120940c00c030107800c49030380324a030700744617544268061700501c0903061001460109038400d41c404100c0c80d220380c1e158029a0021a0900e004004c0410b0804c03d05c6802a01018442080c41c007902032000b5120125402e01288c41c140c008041d155040038000d0f071003d502150045400005941003140380c111002d484100541e00d042d103508045010078040000c0d0b12826001e194404000c01c10602c2001d440e6001c040e0742480002d10a500b6200e0350944c482e001801c085042c81600c00040544001081243d0501c200c2c01d494081c0c1c0c84401080509040011111403417940c0e514079000804440c000164011035400302c106000b130b05000000100a90b20800340d05a0b00880d40303090492900d810b5100307207002c040b5615a14810071128040104406203800398 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 431680926 1250 431679676 431679679
    0x909050112030f1e0509090c070201350f090d050a050a120b13050402030f011a04050c0c070803180103090b0a1509090302030913050402100f0215090d300209 69
    0x88113803000084841500d00c142c40080301150001521407424038180e0003065201440c1d0b61481d040c80700c40d40000344001d12a0301c404040c03210817821000700c1c0083e240321035071202c0b0720039010b81075282029400140100540f0700500d03900c9a410213024180c01002510721034441070b0345150410b0b240140480d0000c80c0319858102e0b440d03658400000b03d0321900542c900140405201240c0d40c207051050600c1c3c001101a4040315914019980300713040c1c0c20142110007260200c0f40801c890310740300c1e0072507000c0c499441c03162541e115109002494a4000c00030b01100d03001c0c0410b130b141c4120450f0040d070541d1500706009040304500c0001400418040d0b0040ea140000440038000641c6c907003c0760f0040750801041134000d0380c03011503407040c0c514103403106080030f0001200c01e0090341415800f00f8881c11010a6410501000300e1031024400d100f040300c0e0b0301d044a0b40b0740000c107605042100341e40310001150b1401c006800ca07600d0704800e959002c503100810b00c00e00d03182c40855030b0070307180c507002034000b0034109 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 431682176 1250 431680926 431680937
    0x3101131180e0c13110418090c0b25050c0612010305120a050304080d061a07050c120601050904050307120c0b0711100e010b0604030308071d03071502010905150105010909050112030f 80
    0x1c2941f916070140e601d01d1034052600003e1041a50501e05896252544040c4540b4410084004241041c0b41c180550040c0031501d40d000c1503c42c07411505114104004640080010031084034a10900180302d040360700920a460300b801001380701401034420311410f880403c1040020400140c0703400010a92074148080006842c3d07110340742035800000000e01c2409854000c0340490620005200c40c4096000c12680e5040341100c90001580301d0070144611446907000070b001406014040c821204159800000e000ba0b042e60340001500b40c03440400c0940d00300800d04e002850940c015503900400303c0c0102e0092a114068060a102624003080503000c19501c595010038240c907800c0c058000383d031183e11801d80707602d02560300400c12000d07402001009008001c50000c151404514617041d9a144520411070700c00c4210240e0260084001c010a140300d44038100044021040125068990980e95485000e45d6009030304140c403020300403090309400c40b00c0d9201c000f034014600c4005803001400d29 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 431683426 1250 431682176 431682179
    0x23c0a050901112b090b07050a020d05070b04120b06030f06040209073b0a0e040303020f070f0303060302150c071707030b100503101131180e0c131104 66
    0x148103940311844003083c0e2a54000083d191205e81183d05200130784181ca0700d2600301a10358854954031215108040d0260074255143e1090200c11b12506c4003600d286007036035650766a0307040d002003032100440050f903020039240e0100743d162601082c922022401c7da00208035945030794003000302c890300c00b400c603e040c44603088106042c441e4020003c2d02c5d20080c840e10035910090070025a00780b01000c40824450b00c00d03100f05001a41c012070007182c01c0780d05440c0040e10b170a4a1802180c0601c164100541013040740300d0b00e21304040c0d01d038000d503081ea48280e0361108029040d0741f001919004900c004605c0307401c0104c00340f120302d084000c10300d00c1544490450380d41c40c0c0e403622203161504058910b40303403c9400030014442400e082003a0481c035a4940310401495840c15241030090050000040f280600c980f2210340040300402c460b114001c0001400510725958945264020180d50901c040035003031801d0180c3d0014080341c2c490300e14074003408084002080038a07140c000e1220b80c85a0108a0f4107200 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 431684676 1250 431683426 431683453
    0x102010e010c111c0f0e0103020409021b0709050105060405040b030313080616020304031a061f12050105040605180403090906060806210d03020c01023c0a05090111 72
    0x51080a15190303115040e541d000c000800b400c1c022013410b0700c40710205803401c41038003962183c00300c040e600b81403514211507041500120080c3c86660300c00607140d0f0020450181c0400c0900c818075406980c90115149135660700500d6054440912880b03038081c1050004020714141074021144400b4010140c80c80c123288500c62410150607900701d11400d44c031510400c20b07505a6150402d0041640780011401d080c03650f41c40001010159446242201c071500200d441c50701c0e00300004c2e40d41080070b00054001c03440c071503004000020104490303a00c282440000a0141002c1c0b181c6030907140040c082c00c124801c0745510818103100600100c0411003031010000302d042c5688134030700140c000350b511003e07241888404c0041408800b040440b000d1015856103058000002c1e2548221003e4100545ca562210011500a014950788600320000e481d9010016081a00c00303200180413201c40703500c0000051025000c68003400320000c021079020051035640d036004602c2c0140990003541112070f200d40700d59 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 431685926 1250 431684676 431684681
    0xa0201140a0204081203090703020111100e0115050a0e07032f0d0b0415030b07030e0111280f05090a03050d0806010e0414041712010305030405091005060304060b0102010e01 76
    0x1c400d0108a50701150600c585501404082c00e0344034100e010b81d0840c109400744544500300c43c03200a040c010305002105a0b903030103210700c1c2d134804003c82e020051106854000d902800200c2803440903000b603280301040d6803508180e480d0070395201800b500e00517620514180d000304071031119000c020020f020001058100300b4420001c1004500b01140c03205008040e200c25070307070240d01c448c1c07107141030468035941001c076820100c084a40042e02c00145440c2c1440030780051030405e031142e0b069400c001201000300080c400505170700c1c0d041030141060040e08118001c0442c0042e080000059145003c1d800c1148a81c0180103186130081a0101c03a40e9a50348052512030b1034450000468241c03000c0018942c0c1151210800c890706480038405082c6008070490403420060000300014180040307040c606180f10180c0d540b661140c0345100c110358490405980d00d800c10300c81c01c1e200d0000c0100003030100d90242401030850f0409800703c1d0841d2996501d980181002141160441d965a02e070709110300002d0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 431687176 1250 431685926 431685931
    0x3070308030c180a0f060f05040803030f0a0b06160b090639030108011d16053a1205360405070e04050603010b100807110a0606140f0310020a020114 65
    0x44524616202d000b030407c000e0b824000c0e0074002c00344010420f401000c012240d103d000788624070004c0c0d5901c0708441c014a48103203103540103500401c000840444034640350115501503411209255503101f155661031100312035400d0403c281c250941d2203034410a000040f440c42080880c584450b13201130014040e0802d0740840d9080e0b440c0c0824140310010142c07030b0f2900c195000041c007030b04811802a111900d90610038039008e00e032801c001242d0f40388211003101d8805001401c101d222034014407030061140444209a4010070001000004a800703031044910248555182c0140e6480106804600620401550108202d1a075103820f05580b28410305100b4400ca07114801001c0e08401480101c41c00140954002d80c50b252150013150341c0e103c0050001040fa1500d242c0d5584d403c001181d1141e42510341c510b091240000303007020401140c10110585e54124002400e5500c841d0030000d800d800444850340507000001c1490624019400820f00c841031400007207a1443d5480d0b01041c2d0b60400c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 431688426 1250 431687176 431687189
    0xa0c09031b1e060305070c05070612090602130501270b0904020c0106060519050304021302090604080a06020307081e010611010b090c07050105010609061b060e0a061a03070308030c180a 81
    0x800342c0a001094042c800c0c6a00000c1528241500c400190780e415a0380e020740c0035440c24403888038003240100341ca84c1c02c83e840f0103078042c0c002d54403030488581c2450341d108a4040c45003c511324042c1543c10301c0102c00ea408098010080446201d03241c41d243c810103510032035000345c101d074007000740071090802405000000c0503140c0d035550780c401b103a00c0b01c4d0000c0802900e80e0b80800c1410018040940d80304c05201039110705407000180d4841214000a006d071080c0d6100700128013a6880060034404103901561007500f41c0e4442034281da4404282d080702e41806030003a01d017045100d00510141c0e201d20490004100158000641c03110601c00243c0580d504136207803440d01d10002400301c2045400c1c011140140402d041c040c091a0034064080c0400c075124204603804620814001d0510a071604411a01d043c16425640d4602640c1001c42c054002c0c001c50050b009110180501942400103081d800c46e07400c240c0442c155282c039139402806e94450002800e80e130383d801054180568500c4d100c6e02c0100361 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 431689676 1250 431688426 431688479
    0xb13180b091e060607080904020307020307120f090e09030d0504020a0f3510200403080309060f070f0c11120a03140a0f0e012705090a0c09031b 63
    0x4190b910341c0000400804181c055001409420006900942543c55401c41201c1c090303140d545003e4124514010b52202811130f800b0040c401b40c855070042c40f141c0414160303030360b4950748507120889007000040644041620350f00c10082e00501d10300c50392295403c40d02c01442d003d1956610441c0282c0192030342c00000c44088500d904a20744856040d002c032505040c003424000744011041c000d80c035003000300205003845484601d01080400301041c0644070030f10144829840d00c2d16070411015907042120041d0061140e10003140240f10b0003070201e03106440d02d5644811881d411001112904600d1001310380d0350800010307483d00c2e0340d111284000580ca1410040c984071400d42001040c0f501883c102e07a0a400303007013204404e403652091301ca5a540c403440c1010f0444100c81e400403281d11542c5034078114258007a42e1580303003103d030742c0d01030b441203039008c895016680e01c54689820444910301017080118089400c1040000d02800705646051160214000c81c95501c0405c84141c201c11815401140d8 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 431690926 1250 431689676 431689711
    0x161511030114130902220207081b010b0d0b0c0d0902030102160c0e0907090e16060906030b0f0604050907020316060c0908160303030e100609020706060b13180b09 71
    0x2407100c501443c8039801c00003401903100c1500801d0401c030b01c003c81c0315851991280b1070881000f06030100c50f41254003000403651102020003480d60842d424502000135401d001405919141091030b407254250070604919a07030304ca04240e50f0300b95119200070000b564076110130a0260b603081c8007820040e4241480419031240518100750410129007082c08107550341000d0006842002030300100717588681400240031403003002003914108144100844050f0f502502150040d4002e1b0104211511901c040c80005441400c200172180500d00464001106001c02c106034a030201741c05800007154010b0328601300c0100508542e0350403014003507421944a00d21404900c0d03001054000522008020704251a4601380c2003c0140c09444050101511400d500380403500900c168a012441c4c00010001156114000700c0603400201d003e0f502c4519043d800645e500d608400c860300080b0682541521b9410581c4181440b01e00480603a00c6965401c0140e81a80b00d441c440d42c01501d04401140408 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 431692176 1250 431690926 431690929
    0x20d030c020f01141503160506160609050d092111060f03040b0402090601090303020a02040f1e230705120411040501080102090a06031521170a09050105161511030114 73
    0x186001c0e20f4260080d1f100c506844080b0a150201000b9900b00b11601681c50783e0600360803407224141100900010314002111041100c0000e4004503060700381c86510240ba174034000e5030449010301e0344024500592148002c00600242100c1240d100d0041101d401c0c81c2a5022015850f00116402c441c0d01003100c0920055182180105910210901e8020821070030b540d0020b449041350b600c002c1c0295140c2d90b495010003002c0c1c00002942000701c0485c0350036040c244819001d000d40e1400801d50100c502082c503a8081c007049401c1c40f604003a101c0601c4c000310405030140d080d800800540e0f640203250111031960f6594041c96000b00001d90001d03840700c00640400031041655401401030500d0022104000c0040004500450f00d0a03000704495101003903841ca00800401c4000744100816044820004940d002030a0340c800517680e090b01e2143c80b0b0300103555030322078480941c1ca813140425001c40024114032240840202055000c222501c1503011403030623400a0700141d000c41440100742c1481d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 431693426 1250 431692176 431692201
    0x6020709110f040306021602120d0912030c021201060f061e0e360a0504031701060801090b03031e210615030705160b25020d030c020f0114 61
    0x104000030300c165241241c100b400452074400c0c3d100007001c1603000305071030380b189000c408a84003158004d09003110094010740e8064a40d081c0c0d0600c140030508190000c14141c03610b400e52401d86605480e0116035200d03035000c0200901920289079803940d00d65002140140050314000010581c507180c1010035200038072628150382c0307001841401c0002002000c25240d9440c000700e107613210b040c048190700c03800190300520b0622200d030314540075903036410902810750740303581c07000e0b225a0090303581940300c0b0f04006035148058020b05c16500000c440743c006120900056000381e4099a00904403841c0c2000345e1550381d028801d80c03078a44641c0c1404100c080c0030b00300c441e6500e03411400c0f000f0000302070324204000460600d03011159040007180400042e941c9400b8108030348042001103030b04844c000c40d9250500c0d400f80201d6030300f070132440900111001ca0f201914040300050407500a801030081c2c0344012002000fa01c0021011486032007040300301030100303100700442c203220804489158900801c00464 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 431694676 1250 431693426 431693441
    0x120430030c08070918060803070b0a110f09041505030a031d06280207050a08030a0e010806010516050c12010213080705101d18070215010807060509041506020709 71
    0x1840700102c20841e5141e4400f034041c041d98500145203424402c404d108070010030984c0c21481561000061040620030519040d5120750b425403024080065000d0640901303000d0790180007001c1c0d030240860000b0303180c503030041d00d0282158503c0340041c4e41e4600000b0f1405e11207102c280c0c085207100c44540800444a0b06420000c44280c2d90b040c0381042e0740310075200032604400c220007440031800200d010f551013402130341c00a04009000d907403525120701e641d0391a030340000804e4010852030040c4009a5000340b00075885907405854103800c10407001c0701c1e48050b0190450840b02d070b0142181c03044069035488000e003085c0214074001a15949403c940f110312184540120900e030703004000801c01750341d541c07044490764502c078544100803d0803c215244031400f965201980500324120407480940000c000c1d41c440c010a40c215440084010700c44d41120f2428068a00f2907008001c06000d9640110001d05000b840600006200007040000c100307481d03400d402c5600142c00403a010003118815004440 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 431695926 1250 431694676 431694701
    0x308010608150d050f010c170703061d061810080105150607120507051911010801030209061c0b070905151201060c020105070c080304181112043003 65
    0x100070b082c040c028110805209038043c0c42010b80c10403403400c1180074031a80701d213036114400a000c1000c803400090640c03180c3c00b089804128061002952079032090045c8022030380d2030364441d61107145c48a52005000c0340103100f00c1d00041000400424400d000c2038032071107010881090003080e401c00280c9800d640000e4814044101002c0f00198142e0700d51040b50302e100d41c420280401d009015106035400e0042200c003a003d40524004c10159025641c0715403921441040c02c115402c0c0b0340303c015507c441d000c0c040070b50040702100008180e805c203001171003000c288070103c1040f2640c41d0303614204011411500200018440c5100304000d0503d4000c2c40c1d00c1055240d1080d04181e5015040908403405124070400c02c844d0803100e00541e400b9004656601e5005130111107040c1e100c0c00e21958950052060a02c1c0d207038503600c0884185507911a841c5902181c1040a00d01200126190741420001d0400e035114400c1c64640301032108202110055a113107a090140040d441e014090119101d115418 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 431697176 1250 431695926 431695937
    0xc0118020f0904020a0305030f0d0b06031905060d200f030a030e010309020609030604060b030d020118020910050303030a14160c020909011104081608010221041104060306050403080106 81
    0x46005903078211035034070008015111642e040d5600d0002503800582540060903d000000c3d08001c04201400100b8034400006d405008a401800c144100c520003115121140000c4c207002403501c0809401041d003251005180091000c0340713455200424850f81c20100340c03458a500d05c844e19051400c49801d2111080303020340140380e1152005000f800a01c4025410190390310841d804543d9844180d4202c080054100e840a01d414034140c40201009400a1321032b21071500e1104010f44140551050758000c400f000220403401c1c0e00788050440044c000004200d0150710116007510100081c41c401d000700c40c0081500c01055043d00ea040ea40580984a00c0180c1e4080c10b10060b0020340700049c3c90360555800ca03080e520b001c40c003030040203c409848030352900020005072000000500d40031810388c0d07103a1090a80c3d40c42210302e080340f242100c2980300c02c46400410003034100900a480d8020b0150f003480580312940400607040b543c49420407140341d030b904c0040c0720038154001b011502400860801 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 431698426 1250 431697176 431697221
    0x20c16121a0702011e090b0f0106052a010e0304030c0e1b0a020a0203010507110c0901150c03030902061c0b0d02010203030606090103151d0a050601121116080c01 71
    0x16240c50300c0081c6195021841c1290100721070510175802081d03078200710100c2103856507054030600c014100a000a54141507003101080000d10b1040e1003a0480b01c0325280e4a203816038242600508030f00d120b00380d001c50340c0d40b081080d8102900303016004071040202d014683e15821481d107207140d646140c011052100c441c0c000c004040c0c0200e81194002c00e01081081c1e00c1700c1202c80201e15115550320300a4055007040d060200968012081c8800d02071558284c0300309102031010b1207071004091007a042941807010366168540e004200c1448124000d1501040c00b90158010a000340e000b440b00341400101c407208038812008520581e003441c0c1d070480311901900142d80000f90380b40005005a80306e100005491182603001ea80141c0c18480b04442c1864503985d80d035044001e5016011202c0c141110076000261404460301c500ca01c00c1405840d40e00d5501c00d0700800234002c00c0418001c001c1c01c00d041161f18880c40d404490780d1022841004520703a5800110b514900b580c55020b02900a444440c40 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 431699676 1250 431698426 431698433
    0x504081006150309061d010e0d020307050d03050613060b0901140a080c030a061206050103050609030403050d0e06041d07020d030b010813170309060610091202010c060609020c1612 79
    0x4002458814070300d0302013402d0074541020001403801e500c8403214165040e0321451040340642000d131940d0600015502031480340e440680c0c80b1300c91120b0080c0076412007610110f549020f540190f4101a01400f600301c0f111078440098226401d540203141c0b40d400220b800201c56a0008400707a103180321020540c10714407003030406410244023801c100a0310b5000b00028060845903404100200080140d04c4039808242c2000f40003400203020070340b21170080c00f00084c450350000040b501101d80c0b0a00030000245042c0b812520b1100c0103800d250300c10002c001c0081d1200c03101e0600344075500381d103000080c0ca0400380c10184c54485202c2004080c03608010052603680c3c1c018010a0b03108401c41c4891a40750343c00c0c980303500145480c1520b407038081d40110600042540010328140702f0401070b07940102c05103040c0001d032280115441003104c08400c007072103c8010352203505080340481c424030020400a4482e14410141e03040513036101500c0e400300100c0b84c00403070b85800f150014500070200014000e01a02c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 431700926 1250 431699676 431699699
    0x105060f1003050601050d0903030506180108120f190e01090e090304090207020a030506010602060406061208041829241b1005040305070209070206071d0d120504081006 74
    0x181d00141560740000460303613401503003240c6c47d40300c2c0d4810800076104a0326001e00240400d030340041c02014902d804841001c04818254140c46c080c1e0000c045642c4641850051507000d90f80d4801060000c0c401351100841402c4805802c44003600c0300c110151300781c400107006080350351040302811010014040400d42c044210b070103550b10075101582e980c0c0380d800454000000352f80024281d1003a03800004050f6404983c080c00340d480f811090142a5545500321301a421f8984040d081c41c004200811403a407000da410100c060a0a5000c1540a0710415420f03074203100b80010320991a01c401d64950318901410705522400d5203020360420350404150310b058900400000c16000d00b801d920050b813008080200481e000c000352818401c514040c9401019030f00300c424102e015400000215003110b00201e4264403864840e134501e0600700d0320845480380e032801c44045076000a04c00e0240d074003250712820000510b9500791245c91343c40f031070320003907600c3c20305080d0108182c04e1501c0801d06c91061441d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 431702176 1250 431700926 431700949
    0x60b090703110412050a050d2705030705130f0603050606030d0207080705060912030f0409060506180402130b1206010f021209060a051605100c02150105130902130e0105060f 76
    0x142d50020310020300e1715101d0b02c0d041016401805900c903007284a140c080c1d11000181140048200485198002c1c411403e1030b202e481c0a020391607000900284543d05100c0104181c107100da4001281030281c0424003802c940d10360300195003d803c00f41c104a4107003070801444035254081c0c401885031a240c214001d46841305030042071b20945001440420300e540d40b804801c0f03040d01240941b903803130012074281c0080703900c58414600b9071030410100203000d25141040d2240b28154441031030a0021070340070403000703622030404032030130079210b200100d001c0807800c1c0604640840280700d4086800d0060000d401c0e01c00c800c24010841d0300c200983d8030504906010b40b882170006031510380d110100e41c20180c4060041c41c03154a1216505104d6105110300018801400809030100b0808808284401c0b6221043c824220007101741544c01040941070072101c0760074000f0b0404c00001c1049240d40000c514000258804a6070790701c03064000080a001c0c810140c10580c1203c1d81c020030b1111001040602c400c1c0b = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 431703426 1250 431702176 431702189
    0x7051206010302040506060c0f0604030810031104471c03110c040c020607030c08090a1e080708130501050415110f03040914011203090510140403060b0907031104 71
    0x112400300d0346c2511080142e0703644841c01c40650321440d042c500029030320f210807602540000e03081008100c0803040c1300c0007a81600e4002c60300e4104400d400c01800007a201400000d10511140c00300955a45c03448142035040381032010003030b0703000003000d0000040d440c03554160b036129148510601c0640310003217120140107a171505103046854408009241025450841c3c0c81d00035003008000c40d6030990103e8201e200d1921624100134240d40f2207800c40d1900c100725074021b1a0b5100148610210ba410405800302c8409013440d81031452182c1c4d203418450700311041c126540c007004900310007183d144001110203010280390580c101880d0071903d201c1c2c250b40d0321151060058002004070519802e1103003070f034510030050440c0d0307540350790f11000d800505042c42003281e030004500c00840c001443d40c0c1c90480c003642642d10140058240303010000540030329035000042c08a20b90410000805250107400111302400e40019900b0700340c0188034510300f009003d0000c041c035161400d5403d00000040e2419540e8 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 431704676 1250 431703426 431703431
    0x516020304061d0310050403031d06130c081e0d0e03030301050d060e0a151d030a03022208010b0405010815012106050a0608120301030c0303120f1505030705120601030204 75
    0x401e07040001e030f8040543c0080c1c1600454029905103111504080c1c011442594200500004081c04440308440d20714014140d4100c039000c0f48586142503004013140703010b0310003504500d03500c0d83d0340c91804038003004214480b0a6002c0703226020b10144842d111000050802d602c180c0300080000f5181d01c01401402c3c842c6406107900801c1c02026407240023080201000c0760744035180d50804458101100341092201030400d0021407000500407070300440f00b4049001141000c0c01803c00f6000ba420000c080b820350102890760090301c4000102c2d02004044035400091000001403d110603144142c00190f640d600c084042c01c1c0704030b000d0350351a0450b041d4080602d03200f000c0f2000340082c0140030310050980c50401c0e017841014100795100c2011a5000c108441940b0390340e14880c481400244000707041590030342d90800219002703c900203c0c221800b68005130036540300001c98120307032508840400c03400203264140400d050812004000d410b0480340e03118404100d40c031703456585505000c000c2c02070b80c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 431705926 1250 431704676 431704697
    0xb0601050d02270a0504020a0c060209040b030d050307020105160819150b0c07050a0e04080a090b040303120c02010b030c040e010f02160c060503061804020a050301050901020d051602030406 83
    0x485941a0f40018805005103d43c1c2c0c4483d003d40300304400c1c84180c5a01c5000c0c07482000459203420301c2128102c011649902c0482000ea4650a0081d00181001c030f0f0025198891141c15036000d20400f1070388030365500d4850720780c100208000c2c00c4940081a9850441310f4040200038150040c40e01e0750700c14409a80d550741c140300314070120b02800c01c1c4115085540070301c1201284264041c40900310b201100304c12602015511820000c500725184103906400d00a600401c01186140707004040400301410038072540b03039a50080c5605030307025900036000034041c0082c4444150b224001c1c06074000c680d00c001d001c1c4a140c400003944496603c40c0252050f580d44001100c450000e400c200340c0c180c0066011500d0320b4503c5900001c05809900c116802e100308500450918069400ea90141c00701809103041c1c410a140c40210150000c2c00680c2e01c0003112000044591f024021140303d5014140050380300c1070002c010000352000a001ea04c000d0301c0e50746200d801d0a60000c10b8404032a80ca06d0040b8008 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 431707176 1250 431705926 431705947
    0xa0b010219141c0c020f0d02100503041121010b04050402091911041415030c070f110d030509030d140a2102120f070c0b0601032c07031109040b060105 66
    0x201003d0010850400004807002840c0d0000c505040c0d0758000e0b50b13001707500042c0c101003061a403520a8000e50043c00b9410040c2c005100340b0266a00a200f111100300200000000a5100c411007804120054840d080090030f0361080c060201c00683c10f403010320183c10315500241c0300520003082e404544130644030007140540b01c1c2e000795840703001c01c800c03155685490303031501d584030b04080d821035010302c1043c911000182842c8080b280319600c0400340d1401c00c26207039641801142da5407025185004259107200722552440a49071000e0b01c039848003a900c000d101c0600d414000d1541c0340300140b1042c001205481c00e0080c088460001ca140740650700b880100d030307409410031100b030303003080c071040c8040b41000c808411401e07e40d0040320380310384404c2d071a42d031444105c1d10544100c5c801080819840081903d550194116900036064880916071303002465102c00d42c9a04001e000d6a8a80c0c000402001444494000d6441e01341041e202080c1c0c5103010748a0f140d21000260040e8100180040c0441c843d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 431708426 1250 431707176 431707183
    0x10c0c0b0c070b010e0703151a0d02090603180616080a0b030120030901181211010b0409050714040506010f11030906030a0c020601050f0a0e0c0f040303080a0b01021914 74
    0x92607405240380c241545c6402d49800d03005800c07524000130034548880268030b929804c0d03240c41162a03040b190001c01c1e41004040c200c0f40c0000004060b0144c0a0100c000781b640c4900146201c2d20181c1c0f040e004110f4400105464054003618115003e915140159005036011100c1c55000f400c1c18001300e00221750f9000700f8010b0424400b0643c031440c0550036984000502d9000318041c0c00309c81c000788407180d1091800424a051000c00505481c007071442100007900541e908031152814100001c1c0e45c0800340041011355402903000ca4080e004070b5414018100744201c42c0320503c2042e20100141e20303000e000600140946e15144082c000003815082d00064100300304d6441800141400e134907414866904409020024000310150040d040007041508203600c100300b007118010f020b0006c1c2c0f86403042210ba464005425050800070030442c0319442c0400c5801880151b200380e48401b003c0c0340101898040382d9800071154110740094138003004c50004814418029604100341000a2204003952880c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 431709676 1250 431708426 431708437
    0x1409130605071d040506060d0507091e03051504020a1e030501021c1d0d2003040e0601020601091e0203060f040f061a03010803161a040b01050a0503010c0c0b0c 70
    0x141400c2104101542d41e002c0c2d0260a8440752455810180c800d9800f0041981c004445468000a0900c2501106107494205542201490520182c25038494103e80030a0520645614844003054410000c004040111200b01d4040c1c488070140c03400e149e80000d01c000214400c41441851000401da90b03808803600c4200216841802159208031107500019107094100705240d141c0d1800740d4000154420000d008103440c1c140002e82040503004801340c41e0b401c3c000ca4070450182105e96841074503c6c017040100f02920340e4070034400e250700d0901c000918010050308050f0f801030400c60101005d5048000c06692982030328005a129900d01011030444941e5400d141e03032280c20700c4005184600954800b406607002d201000010241d00e08490380103110a1086c0c00f1035505c2041400c8241d1400c81503501224070a040b58880c1d0701e0320024156940c10140c03410f8a40f12440d1004000ba445d00c48410070003031000754002e00003100244c0000e4030018a501c4068007524690002410340403001c011600d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 431710926 1250 431709676 431709683
    0x20d0909021e220f0e180a06020a031103090106030c06020a11010509152106030d09030b100b070b06030c0a060507060c090f080616171909060e25140913 67
    0x404d64403400c41c44585180d200d4103800d5910742001c0b490800b200850200e80100240c02411181035a5440038025404410410308050340d5210080e154180c2c1401540146003000000c01c41c5401e60402c84030384002a0301941c1554042020300c00010300f145000f5000c0740007400d1650726051540081140303078024810521480c00d0001d600007d40548520326010005440400c040940e112414555117a400c4291040442c03000c420400000340503d081d690710000c2e27075815554460750f8245d0010740ea003212100300c40402062041100c80d060821442c05c1c081c804a480380100b500e001c0d0007606a01c1840342c06803d564039040c0c5015074a00039040074004118044a29404c80c0e9035419480c2c41d04001d4559860071000071048210451144e000219560b403c080702000603261811780644020070402c0755404242c82d5514607000c25a0303441101404000701010348200c0420400c0c0320124003404500b03d03d000c1e5048004e01140d03c04001001c800c480954281005844141141080d40071008004 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 431712176 1250 431710926 431710987
    0x150106030e01142406041d04080d0908070b0708130809030a12020106290901110a052b02070e0a090203010b0a1401080a022b0b0907020d0909021e 64
    0xc042c42d4005609028240021401e0ba02d840295104121703940c460741c802c1448141007120382004042c4100181900302d40726440341da1800c0c2c0c4520071001070700c1100905890403100464150305110100c00700781e501c408a0710b4580e05916110001200070700190601424a400c04900702005031802c0040c030b4000c9400810740d52140815800080c0030b09540c0c01041000342146802d044541145041c0d5003901070098000e80c01e01e1540d00045440c0b40c114401340f02d02e0b220b103c0c03030000480e10500c0160861089610220090900403080320101d80d00201c04004541c4034130801c100c1850200115500081c55101c04148008a40000ba02600d02008050b6020803140d0b00020030407035104504040100a07251280c2076a0365a410004038040c9242001c54101c61203a0001500c1054083d001d4410b001c100c005480505407022a280c03c0d8226038003030244c2d222446190f01c0d0b60700002000024071000e071003546001c0001d06100c0001000d901d03070002c0740c400451540711031150141c00404458000e07400 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 431713426 1250 431712176 431712181
    0x230a052202130b21060a0e0c03030d02031315060e09060403120b1207170606011701060804030507081305010318020f062113060605060711130209060c03091002150106030e0114 77
    0x130726440b05000d8401b461603900e4000d00301d800800c082154081901d006000c0d6050040384412040139502c000c001c1035107080200140341c0012401c03161101c803264620701c009907003030411a980344c21904c00382002150b07911070070030000042c0e031004610021030350512010403e02e4103d0b01081c0444c10448004006026400c80454242514520140b03002244402c40783d25441d002c00559402d1014541c1d180611841030051009502440241e500709100c0e00c0d120340307042d101d529500b2650f000304251450030704020600300840d40c1e140c02103840ca0a00154904e1a04485500007070301481803900440c014080411408203001c0c108020039404080c01c0d045220070310b84180417148429424004964441c5400d2000c81c20782012003e40e44244d81c401030044980c840b2404010350141910649842c0c0c6408000320803041d00e400d0050501801418001c3d915503008000f0021b001e074100c01d006086501c6003240301c54a41c0b040c00c035607044403503070308001607851000d8003c0e034003501038240d52030501c095403030070f = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 431714676 1250 431713426 431713489
    0x1051f02031c1401150c140a080d020c0106050a080304090e012304171201060503060d02100f2c060304050a020a0e041a010f0603230a052202130b 64
    0x262440c10543c46041100c1d0780c9a85001c00c1500038903006000103801d035281c00000610503030502c160686218120381e0310f03807155a2102099802002c11590707803a00401d011304281000d0089401508084456481040c02c081c00b5559a0045106e000800e644440404503241c8007980700352010001c0568070149541800c50550301607106880440e000804407501803e55604001a0b80020f02e031144002c070076918041c4203c0b8180c0002d40525484140c0540400c01650307410030000920070580c44162000c807030920040d188440009201407040404001d809000650451010b5507801c102c910546a4590307040c00d0345050080f4100941001d00000702060003d80d041540344070301d00c80c60300030282500106038804414028030540c00c100c000c60800740300301c50290b0042c200c4d1440a02c8101c03c414904110000e40380e409880b40b00b43c2568901c148030f41010700303490010072007201001da410460865800b1601071010031140d9010640c0d21032400050303503071781c8802d01b035111801c07511110300b600c0260 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 431715926 1250 431714676 431714681
    0x15082521050d0201020909010e18071e0609030f1e0f06140603030a02070510120f020417030310030b040f0f1101080a09020a03060f020f0310060207060801051f02031c 73
    0x403090314980700d40c101c1050814414000c4400200015041140d0b59291116080c005103010b0305902049841c00102003c034002007007104000e205000344c00c143c0c8103500c45410741800306900f2100c200480810140007050070001d41d16009980620085c00030441c403400d889015104010007081040c403130a00c101031103d2034000ea59195040c00008005444100401da82d91045045000c056040300c4020230070340c904195160721043c400d080000818004040c900112209801881c60b6264041018000308a8000010b002c0550000c01145982060101c40b50201090310005001100700e0002a0030407904041210110354021009375400d000d82c41c00c003031520f68007886180000e070750343e00060110b6454000c0e040300c550054104e405150960301e440002e400c141e0b20003050250204484410204040020340c420785552501180a904000c002030400100741d12160070045550010f2017a6610104181203000105580030b2101d07000c10002d9040d400380c45001c50000c4080c081044c10140c2c01e4 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 431717176 1250 431715926 431715989
    0x5070501021005040f110301021312120c031e050d06030b0402091506091e0a120b0f070f0c030c0b07031d07080a081e031801150825 58
    0x741c00b990045140794400e80115141201c02400410b800c2c0e0700940400d001c40712440c800500640090f182400000c00c40c41440019401801f01301201410356081c00b036072020103507000040d4502040c0d031000c0d0351401480c5036801c03141148101500741500745498024000c540c1c0d40200c90009008041d603030b04201c2c0c07807014112404ea000d2864500000e12005141140102ca5240201650b04100c1402c0510084400c2d00080245031001075904010543d60960800d004100d0301c2d242d0700c030a4015103132942e0150305c050301c55802813000c0c1d010b000200d0307001b10b6003041c8048145428a1403480c00c2c14221100030a008001d0084420740b001d10044640c035422641440203031020a12600c030400d44074941c2d41c94540301d2040075801c010440c40c00500300100401c0d07070141410f4504860083c2880001d2290701c01d50302a401c152912294441200081c0600d48040075901c1880c00020716168000e616001062512900c1340e048441d14007070304230a031240740040c0c1180038003400020070011031500c0700c6080 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 431718426 1250 431717176 431717179
    0x30f0303020c0f010b130c030e06090105071d210123011a090612041401050903130518062205090d020601050d081804020f210702030f0430050705 64
    0x50f60840c1411020500030110030040181040003d460020700c8000103060100310001059180c08142c9440c86003000307410300070300c80d0800000710750070306c020003411a954007161a451080f01840900d40f41e619248405210301d00d00090081c0010a550120b00400d100c02c0c250b01c135100c1070820101c0e003501100302da506860307a0311034960401034008840300301c1d0f01401e80705a5216404100c0d1a4940c2c003000c0c10f17660001d1141014020a4050400d0142952000c603290b90f80d0364001b16808040829001e041e034000c10742034507007400c0b01049540101c03104100400e02e9004000f41c0c083c86110313120542509251226330380041140d410301403400d41e101c111141110005205030000400c0b54a03248c140c00f001243d01c01d1185147c25406907102a02060103407640794015030a0040324a0031080c031005142e40701c0c0d140c038407000c1c00300e42d01074034124020054940e000710f6000b400080b0104600702d0440d010348240c1d440640f55805a005030904c41400c0d0081c0c1c19401e024110118100f00300040c0c000e094820 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 431719676 1250 431718426 431718433
    0x40501051602181506040305060a18080406020a110f091305030c070b041e12030c06090f110406060201180f060b1002100c080c0a08060406031b030b090609031b07030f0303020c 77
    0x1348003007040024081c50102401a40003400410200203195005031084001c51024144244013911580c50703c1d0420b9106c0e00c00358000014803000c016205004500640d002ca89944280041d503001c2072041c2001002c0003480c8040038459000d0050400a442e0300e001824202ea0b4001d48503480c802003500240f082c3c500c0080340740c3c044104e90425601c02c105440b07155401300d075207013200d803005c46801e6600b80082e60356580d11000d882c0481da004000a550b14040c2049007607202d454400e0008031561540600116490000303500280c0044c000d02c41550340c0c0110030203980101c6402e0120003066005803482d0300c4014140f8014180d0f4021403059030100301e1381c204001d0003030406001d54048030112201c0190391030410418a000e40508003458000e00080c0000a0084c2c0341c1c0c0c0c81d03807410798030200c0c1040d00308010b00c03041023044031503c522907111000d40041c1a941c24150460ba680f4001c0d8000201e40e000c2003418400886010032990004580001ca42d1081c03514608000d0002d61104040310920301 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 431720926 1250 431719676 431719711
    0x30414120703111917040f0e091c05031302030102160320010b1807050d0c05040f3003020f01240512060106030b0406050a0923010b04050105160218 65
    0x10b0101c0c05520300c4940200c42025007650fa42e60211424150b0707040c1094900501010030070108540540001d02601c601d00c0002c1e09001518a12b0010080b407c2d000070040f0410342c00d840c0b640300302602c0d0401c0c015070304035003500c5462000034007a0040c094100c0d41101c3c681c1c3e40c0d5050640c011181d031404042040910400c00d94010840c3c01ea400140c00b0b42d41090f40c941011110349c0c03800303401540c800740515285041c000d80301007403002e44044014440c000791004ca01070084901128403a0014581001c100c010031401a5026503808145011401a101010300b0718081c9402407240c0e1401c410108000c000c00030030100c92141040380703c4c504241c00c224100001c1800d0400100081102011500400e810b0386000e4040307020300f07040d061650300b094841e0000100c0b62518680744001c4c003c00d26012030359001ca404001409410b400d000c10401416100411440c91100120307800c0d11420310b0141d0713403909103202481c2248280d20001b508540a0708a074090f1232a0032040ca0f020b0396002005d8041030 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 431722176 1250 431720926 431720957
    0x7080c150f0c03040209060a0e090a030807020313090b120327010f02030d0518100614010e1c080f16030311030709090e0a02150c060c040f0902030414120703 69
    0x1c010807100000c14503070420124015240901000380d10060052580d2612078803625203c0c4012403d0f0b07804001c581c003400041c000c058010001d00e510100600c02142040105180c10300300500510404241c0c50782c03403418900a807174540c0e031303022010007140440e50398031944001d680300329840500c2e00d921f101c9514050445584a0307406061042c4040e8029400e020b800d0855400414014107072010252224080444d00001032280300328001000e0b000107015860410740b0300e81d1210425200d070400c50010b0f085c030785c0361740c610740380c40242074454081201544182c50000c069104408002e081840d010031032443d80600c0c040a00880d600c290360900100613098000c40325400b05680c1e8201003580c480060040c420326a001740303200507600085079014461500850360503000544c03c0d416410700011014100d000030400150451400b901c039503c0d003854003024492054190192407a00b0780c00002080c180045085030b48908400ea606483c150110f107801666903034130011046010844065412011 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 431723426 1250 431722176 431722201
    0x3080a0207090f050f0f0603162601060b042c011214010b0a180219050403051501030f080f090406080705040605040e0615012a1406071706030307080c15 67
    0x1030755540c01d540317455100d400b00c0c900c0c41d4400030085030300740c82071003460100c40c5404100700e0010040342d01c200c001050603414803942c0c0c0070340710180f4103541e040600c2080403000b07042c00c880403103500c4120000001e108418200691520325010f1100c900308000200d200003a54640d4082203110b40e01f0010100303183c2c0d070729500fa1104001c1040c2d00150700d9104000c1c0100145140b00740c0b80346000b0052501e9003020041200f402d00f2078031030700042c0d0040b6080c010400100f01342090180c215185002641c550741c0c0707240b010003050400034003850b404282c03100c07500e0019080d10b40c1100000c0003480400d4444140554030501481401c1c40760b8145100012982050311940000b440c1c502c014250035038030804014150303104800802d0402190240c03081d0b50742380411081030070048011083c3c10000d84d41c1007002040d104200b10400c81d0300400b050001582c0c014601c1c0c80011040300e448901d5550f548002410b500402c2c20281000c0c4001074141c10030390b000309042c0c1007140400c3d000000b50300c0b000285202c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 431724676 1250 431723426 431723431
    0x151609080c10050c0c0612060a061409010521070f2705060304020a030804140114090102030a0f05130b03091b1305100b0403050109021305070f1803080a0207090f05 72
    0x704000480e120200351440340f801891485032182c01c0f0340c400811000440c0603030344140c11a046220701030082c007184d0316110401c02c0042c0035619098020003024a130b4a0002e1180c001010706024000900f102c1401b01c504211030031031154103501c40c4501d00003801074402510015031100084024440380c4801601c0040080c0b400ea2141c0404005400d0a050020687c40603200f6a4459409640040090100c00043c8050440c499007821071000180014102c95440851041e00744401c2c80320744000d036800002e6540c040c455151007941d030102e82e08296000d20910500c0020895503204c04181c0d1101e120045008142c008200c651000e00200300c280340c4030a2080c0d860740221090b001d030030005140d4020300d030001c40c8503500d401042d0b0340b064101030590166008813100d9442e041d00f034040d841c000403100c070344030f01ea090140f090345484480100084554848581846030f1300c1c0392044809100d025000107180e0028400d5a07480382c10710080e46e0742e0b9441c4151009141000c2c0c20411042c058040e250 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 431725926 1250 431724676 431724679
    0x140f04060509160614090301022205040506060304020d0303060b03070908071406030c0307020f0312011401080c090d1b06031d07030317041110080106141603030905151609080c 77
    0xb20f070a414038500726009419401d10b480c4135030f428800c00100b95020310041100c0c0307880b50341c41c9003203c00080b40f071844a00e90381e01c00c920445c5884c003000580d0b03c81000301c80d0700650440e207008c1050301c50314054000380000e80000c0140d00b07000c000c10900c2c0b41c02003200e8081d1803103807084400c504da42e40d29888a8189a85285170000000d00104141100c20340246820141d1401510601c403ca0110f071450f5421000c80d000d42e01403030700010000c151050303052200c006428680340b00385241c07007407201140384200000c503070107240011425000d11002201c01c00240085881c03c4241c1c582c1c484008010b0481c1a80507001c03424403400b80b2a030343c03c0c0003070b0b0942160342c113464640c0c1c01340030100c4c0480f01c4100108140c44894040084401503a51075103c491014a00c0d11040080d5042c1040181600038a003142040c5100401001800d9030b11400c44070205a07041c034001c660314503d8940907092452034031008540c1403090003440686036000e80c1d0364843c401155100e030300b4180c0d22907001f40c1e07030441003140d10b = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 431727176 1250 431725926 431725963
    0xf0b030d05070f050a030302030717090a0210090b031801050609090c0d032006011802070b01050d0305090a06080a050709060e010f030e030c2803050a030e01140f04060509 75
    0xc040c000d0062000e0100240103000182c000c0460791034183c1024280407040700000d034000100000540c0041c141b6840072646002c0c00c4491810460302581c5400300c1d200648602031250745801d04911850244010300120002c140c4c0780e0a1081c0032700c40302600003030211125400c01e03000170741c0f908016180034071684001c0011300349103031110240b02940e062060241c041040515108000311a60001c000e85220100020840703585855401002c034100c50041a10241c0100030b4000403c0003003005a05440d0101c5010940a00528080d9018498006002d81040080400250090704003040c60b100304002c090074410342d510084101c070b902c0d00c1030217a4004285080f507124050b5211f00c0804104024504002490000c242461407440e080243e440920380e000c1d90000302d10054402e800095903520541502c03002c00e481c4d40c09041c601400341307107800300f51380d601140c03040d01001d400c05100206292800221802d005114100c074040480e001c0c0c2e0680c0c24680031558200c800a010702088500c2c580c039 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 431728426 1250 431727176 431727193
    0xc0201080f0406021917091f020c07030501140106090b0f030109021b100b0f040203151203090d0b0601180510050f04030606060e09180601170f0601060e040f0b03 71
    0x7581a21500a0000c2d2007040d400d00003c00428644111507142188035202c0c41c2940160440c0e1440200c4020040840350b04110b60340304101554102c04000c42c84c20b032001607107030b16110405a01c1c10071240e20103086503090214408160300130348043c0341a0f0342c265551000c00d50300d50071004003d00c58441030010381c0404100400082c20550302600c0380106d100820001c0000c600182460506402461000305696042d902c0d840d20741408080c00c0a141581c041d0305610b803480d01102c00507410308186024039004416400317100000d204540420744000e180e6140c050035810b203044140001c4030910b0214071107214030700a0346c040314001011a20018807040d1900340c01c00301218a40c004100b04140400280400701c00038072140140d00180ca025070b6074180e828520300412800d81d2002e032500e4412200f000100c20056400b090044c10743d52000007040340c1c0c0c1000a00c43d4a0507250500703401d0f441c010b200c0007142c0355074020004000c1000494042c0300300d038050346510f0101c070412000d80d581580044031 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 431729676 1250 431728426 431728441
    0x1503081e0a1b030c060e06070e0108150409030c06020703050310050319110d06020403060e01050708010e04120504150306090c0509010203041202061306080703051305030904090c08010603060603120c020108 90
    0x2a142c0d02c0b52180c60300304c00114041c2d450b4400d0b102c02c00f130a011140c20410410010b1940100340e40307030414092034a504903040104032820001c0c41f1032001c0d8000d0340c4440c800003d05000c6c00000340c01941c424001c6541d0b001c9130070004c0041d002907034107070180500d420000859107800035110602c500e20354035800c00104a03655003220034903440c1d0129040720701044130101044261015100444c0030b484d0104504e0200410340703003160742c01090401407106401c01840500751444e0182c5d40254803015903000002140c20a564500540c1e001e41e410012034032518078100c2c0e140e080a800c0f541810300900003850400c0065456003e0030117030600590050200300319006941c128a01094006014107251603d000d41c5540324400c40d42044002c00c00300d5060000090b458802d0543c02000c1070110700804072140d0719a81c07648141803120348265100c008000074008000200390051082900801c00302395640b900b070010309240d10064680e04c8002614900c507500a21225040942c140c0d075035500e40e9500ba9 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 431730926 1250 431729676 431729717
    0x30703051503010e060105090a110a030203041b031202061b0f0d0b04111314130b0a050306090f1203060108011203030603050717010e070501020c010f02011503081e0a 73
    0xc0440e66400c0d5481a000e0740ca0300c2c04c1c4202030661490001400b901d43c103140901100002c041e1540440c141703030011502843d50004140c0d4085116840e0140e40c80d1030300d00340b42411240100c000b40b0801c00b827a82c004100f2551000c42c0000d4440d039002e44140d41d40c2c0e0009940500032504201c0d1051000304070032010544402c004104810080310b001801c01c032040086001c07103407510003900c5071030300c00960400340180f0142c26000400020f4645000500d001e00800e4220701c80e00010b021440c2c4031030000905a46500c400741c06440050304852071880c0a0109598403980009103110310f002e0840d95054202c841c000703d910504068450030300ca40d01c1c10f41400c980b40300b4100c0c10303400c042d510314002c8001103081c0514002800b14134600a0030040e02c40809084545540e80003540c0c1d804800100510798010851410500003402d0403404030000040a82c090404801810103201c1404404010409140d002d402c4424404549501e05600381804052901c07d1907003050200310102d0002e940c0041c1003 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 431732176 1250 431730926 431730931
    0x18040f0c1227080c010203010803041a07112101050c0315030102041410140a050a090b03130b06060d1803020607020a03022e020a09030201030c0903030503010504020d0207080d090b01050108090303070305 89
    0x2100720920784440c4c1403000742260000e0300107000a8100240c1000220b0040c060621110240e042c41c41c45d20200341d9518801010603100240100301080001e81342ea002c400d0b0707804102135003100a0200e0b00d0041e81802160348100c80711110711140384801c1255050500c00c7e1019070f0000214548800c01000c01c0200c80204841d5003820081503240040c0d108a008000d4a040d2043e038907020340312a00000003501703807143c680012020403c24810413001c0000031800070f4140b900b0070f111032199120240440d6917441045c0c403e944060801c060300f000c8880d414000c6828034003079800d682c5162100c0030100d072200d00d28040500181d0003500c5031640445064024240d4294201c0b90f8903030059115965020380e081754241d0400b00e1109c0d6020800d40d60076010703146440800340b0b400f694a83c29903801604900060080d140901e0f80410810f0b203112041d8121a041904000320540311101d00314004064001c4180480300714608100004040d4002d40b032580c09034006030f0156055580b001300480040000 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 431733426 1250 431732176 431732183
    0xa140c090411070c06080c0f030a0b0a090c081906030201020616030b04050403210501150509240c011425021608070e010803090a0b18040f0c1227 64
    0xa41105a5001c5040c80003003c001d8803504000100c03611303040000d4004d0100400050f110f1104000850300120010f080f40d0b8006c013262000101e0b40f01000100d21280600d0304004c0e0310714a04000d904005403c08400c0d0300c540030081112006001c001d0090007034401c2440300a015070700c1180030035144524000f190750b45080c0d5180024801100d400002c05680b01a102a000f040d80780d086c20b00540c0100220741c402e82110708080c841ca51521039181d809a101045120400c000402c801c3d00b07030799605143e0400102500710350203034001c600c1180308450b40700d031031420030540c42d02e103117080c000e00451800c0b480f44c02c44588401100c01210b90f5040c011344020000030460068030a40345a4600c0c070f0b1070305d0001c0c042d084002d141490074403511480c00c9030706812450042d401032202001301d075207087c849001e84496520043d102e19182a01607220810b0070781640e8010700380941c403800d540b40c550101d0b041c0d00155540780d02c1140b00f6910401140c01d003011200d90184082501010043d1307060200300710900c0b = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 431734676 1250 431733426 431733431
    0x11091309080301031101110601060801060507150e1c090b070b0915010e0601020d1107062a1a01291c1416050c030a180504090c0602060a140c0904 64
    0x14a6860070050342c402d800031200d050071480380d8006540c1c003640c1622100d128200906440d4106200030700707034500510400040020000b420710405c0743c0c01c0d112406c20344e4134103c24006200c4880d096502c6000c03141c40011140d002d100700240461140340244100d80080000da85040510380f21304c41c0420300202140c0452107486180c503441e5401e00302c01402419100c1001d542c6043ca8000242442c0b68401d48104004100312002040c80c4040b0303c91084440c68101400103540e02207400020740e00318a07002040e512080043da050008481c154a01d000e00d00f201203240c0da07210420100541c5910480c0c03d803101d211200d8050146850004000b2010044100d4a140e207000e2150003d8a441e00702d4440e03414040801e0000c88004100c40d038484c40d40f542049400c0c41810040d0540d80d0090f82178550800060081c07900b010004040c10704083e040140041c0300701b180c40e042440340d920441c8591030041c403941000941420312445021800e140003010014561224118a0080c1c1c01000c01c10307502c02d5 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 431735926 1250 431734676 431734691
    0xf01050c0a03200106180e15040803040506012301110102130f08060a020304020d0b0426130906060e0103050c250308090c060a180b0a020102041701110913 68
    0xc104107140000e84699188408100d04080800d11041c1d84840003159a04003d024402c545031890440c2d040b20050b98000f0b03d00d0078030426585060b1000a1420340e0782c0c681c034103010906c804d00000354030070b83c050f500b05c0c1c0860360b807400240501d2403021408418451109040f0314558030400074180400407000026091041f8101400d0035035003254448182c44000032420000e08209100940d40082c680104600f14901074000c14044e1800c020000d0035480310400050400107600e2401d8034401a84a088542011034804800f04e40e00440c5108512a00038100180388440c9000e440103aa0540d550080c800701300307000560240c01c020b4207103058458103004080341e14641c104000011850700e982d10601d000c030b506010700508000b07041c0340e04503085020311082c9a00ea0008894100c00e491034001868202d112107548094150703003040c00310010005022482c0c032303415000303401a180000035120304c07140740c20043c500721201c01850701e44a0505114514041c81c090f6410542c0300c05011001c5102d0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 431737176 1250 431735926 431735947
    0xf052112040504110702181e0a02030a1506120903090509072109020a03150209090408030703060e060306040602030714071b060e15090607080313030807020a0b01050f0105 75
    0x1003504500c000310042410400e5141c6401945140c0d0b004e0203425282821070340120704c0c0000d1055003601c1d420400340110788048034030f00c182c0080307400c40e0410106500700700c0d246030080d40c400c0e41c1c8881654207050040380d88554880d0b10780104e410617213950947d0640000d101d409040c0004c1c0030350034040341e0400003420340c1360007030160b1040c1c0d440d40d124190308400503c0300d0b4142030bc1c1c203041d00d03d15107414220001031701c8041e604e00550350050a00c2d04000c0d00d080d19400a4881d82203a03c0d003100c41442444108821309010714050160b5440a10005854101c504640c800c05c8508517410391118021030042007050b80115000200c6180401c510041448018015880064100c503149500c00c1500c18007580c10030b2260142c105031806480c0100d0400005418030a02c0b490030021000005401d1119900c0c01b00300c07400d140d8443c0c6c807540c07685850301c114011082121801d901181044001440480c40861542d042c0b6a10040281d056400c01c03062000c60680d0504d080d05101c0308110403101c8 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 431738426 1250 431737176 431737183
    0x150d0b01080313060203040605090f120a030305040209160203070b040201090f030f05060105060c100c09092a03020c07140a0302041d0c0a18091b03030503041b0f0521 73
    0x192103074900542d070f01c000c910403441c2d06070310640c048011508280000d120709684001254802e1400b1034244605501c18030000d1018440741c4041461485103c80c0c4404050f00b40d000144141d0084414100d1030780c451101c0650085000c0c2604016001040b00100040ea8034a0194202d4010725041040302d841e00e01c10b850500d80e43d0010386031640c011962a081200c100003032405003e0940358681000072111455544218100722203109640303078926100a2482030300170781d00526500c0d40600146c161401310400007001c50703889880448110602c007904c4c42c001d008071400c00c0d0050000308551860501818140386410105680c084200a00040903903161301524001100061481d00c0015100c50700c0361501218992281c003845d998081004282d0007000311304441c034814034001c00c01c400b507480c0078441e11031a0150f51100b00840c140c04018180d110015600c182d01c10658074905685420a1002e02c40f070704d21070751600e41020383c01800182000d101a551126180d079658115400400c5c81c0c504 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 431739676 1250 431738426 431738429
    0x4030f0602041203171b0a050711101d0402160209040302010e01020f1b0601080d030c0216060807090f0e010302060906130602010b030c0d0503090402030c13090b1203030708150d0b01 80
    0x5d101201801d541c009400003550000c518070a003035000310b4000c00e400813500130210014280600403c0c00001c5c4000f06140040d00c5030028040c0c100344d8448480500580101400c505c0c4841020300d100d40c0d6410540b084940c0040c110504c0348031601c0c29805c11405c16401070044003155202c04078070304d505000340050b040f5180c410401d80d0b102c4018051070005945a60b0002c00e071030744840c0c0100701c50180403400d200204940e140204200b51120401d910f4007100806110b4900440c01c0c001801c00e5010760b4030b034019082a80d52607c19942ca442c503201f2203000d80a003114003060400100018070b0302c1c100a1003d01d001420343c1d4104009284d401c120015164820005070b51144a02c8009107424041212100f45c112800d080c0301001740c840654030b019414150740103503800804a51035014600075124003030182040b09031075036150480349014003000428103024001a08851203216400f02c1524031504441c2c0c0d0382c06c42552007072941441020240c44103a0090103150620001c5105405401d0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 431740926 1250 431739676 431739683
    0x15090b04030f11030a02100815060c07080f030309100c0e041a090903070c091d03030109020c010f090503092215080f2b0302190c02010314010b04030f06020412 70
    0x41d02e65150400a180303140409042d40b20340c201303a040c48010394424a10301c458061038076150242d640c5541c1c2c40b40104210a141035030240f40402c401c80c4c030b00000100402603510960680e401545092503881e81c2c1c5c0803c0e0341206082d0040150b0751841c25041d40b011030000918a000d119542c04040420102d45880201c00d0860000701e1025100741008040c0d16005412403004500d84500b0307458004150000e801002031254507490844d201103484110180403007502403ea0b5a0707540e403503145900030340c0400150b809a5007843c804c5890320071070344290000c036500100610710f400650010051b45c0c82ca16200e68400060746181600302444510500d08510745100c110b00d0240d090841181c90000d2440036185598801c00b9003c1d070104001c10503503140c030040007011241081c14401074002c4e014513011000f408035140200001d041d4000d14828a5038000c1c1c80400c0714281804101481d1003003406a103800c40d1040204000049101004244240c080c12005040544800c4042c030042030000069 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 431742176 1250 431740926 431740943
    0xe06030727022a010e010b060301050a030b10030803070c060515130209040608030c0d0e040b060417011107060614100503070c06090f051e0706090308030402132f03010f15090b0403 79
    0x41d0300314100b442401f200b04001c503419070440d13240c40001001621135000003403400c4008400300741d1020300042250095035109010030745034074084200400e0390710910415180c3d03906200100c1c00e0b441020f0700010020030041c060740a141d500000c9072020394000743e5a60341040e82d454000550328810b0029240b040540800b400d0014100c5100514011182240e58442c03441c00724840d60070f81e1410110360480d011580892042006400e100d40145032a2640200c420400a268420080759912041c2940c601181191026103a5001d00000704c0343c00e9074110100e2400c0003c2111a0700548554591611801020518203541d41d10040d0440d5005003c45003a801055503001c03041020718640060041c40c00149486807401c0001810343d9100d1102902145000012800350f4076240b03058140802c3c007079414854015134500700d21407c00300380903100701210852940b20006540c5005c03a412605000303480300c500d03418540d9002104801c50300c80814041b44400014003c400c0c1d60142004501a80d0300 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 431743426 1250 431742176 431742191
    0x1605070b04140f100806031207060b0405131214090307030b07082a09011119060b01110a08220b071106031e04050102130e06030727022a01 61
    0x1000100422030400c0d40c481c3da010556103405482c2d060300e40080c240c5902d019091500c030070f000b007030800740c40c1c48402c4504000000c2c10300a00600350080240d081094500300100d648141c1c0340d41c84500e500c1c10091400b44106224515203200308030030440d07184030000d2149400d420b240000c1c0303403460560017250083e03070000c20401025000003c9a600601d00700107541700200c042d5400c40c611b0400000c40c45c0040c0081603d0209034451584503001c04400c0e4111001c0a900140355100c51038036110807208a4100359081c10154801c20151048003002402000982c0c1d4640d2b581c610303500001c5003414010401032401d451590212102c4000705640124603580d04480d040c80d8a1020580b02090b000312000c006000b0380704031405072803403201341030303110081281c4030351a00300d01a02c038000c0c86190500d0515404150115100074141c0115000c40854030207943e500180d0700d400c510307412005100020740c0703103a2580c2c0403240c009180d0020a9010f41d00002e9841078481d4409000e20500070050395201038 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 431744676 1250 431743426 431743439
    0x23100506090612060406022d070c1406040b0706090605070f020d02060c0a0e180c0901081302062a0718140f070e030c1536061605070b04 60
    0x100c07550015015030707042c0c00c0340c0704115a196640704040c2008090590014006032100c5125210316064007074000d00111001024461030400c0c0c008110948081c038540f9000184548241c10000680c50050403942c14180350104c2c00707595410003401a611a034560105200081e80c600c2038512440640d251043c828000b650001c0c58010380c9043d06055500c002c081c0015100741205852a01c582454240b24010032000801c00040c00080c01c10101d40c0780c0d40902551603035610203803a96680a03601c0006a035280014031181d1100f281000c0e400240c10418140e40840b0600322103000d00d8800b20341d03c8441980c0c0c50082c03070049113130b01840c8490050148250002d2480c02068100911041c81c04d0b03581c1003101d8400700749540903107000280442620f1100c215101800324010700d03074009081070341108a091807040340354403001c0c49075484d0f031050b08402080f0000e0a000d18040405081c20000c0b0150745040c45469445244009071000b400c02c0c5100c0090000c00ca0314015082c902c1031103450b50315200 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 431745926 1250 431744676 431744689
    0x304050d020d090e04020d0b090607021002160303090f0b0702010c1409090718030b0f0103030207081b04110403060903120b0a0e06190509011e09020906030423100506 73
    0x40035a0115004060540e02290348040468156800c90800c0092519240700080041d245084010180c40100c42000800c203000b01c0c480c0c0c81640300d80c003900c1002a040c55070404a1041560303100c180d000e04413a00d008a442644545101031040c809241e440b516911561030780c1074111461fa0050b910344143e02d040590100300034404107a2030082c6400e04d41c0b6072000072a841c100800ca5010041c52203401340c110070b4607048040c01140c2015513800c9a0a080c81e451482e207100740410741c090302c90302d100059031303c500103040b2412070b092462480030044d00c0c4d400c02002c0c090380d001d090791113101800040045481481125003951090310f0f0302d030040c85600c107200b05581012069902c292803040c0108000c1c9010030045500030390803100c090340e051101c0218070765500b9540000350002c07164000803602520f0040c002d0490003030341319100300c950381d91041e020603446100b0500d030f00315a0500116000602216080300001c43c10b051079079100e0220b41c04030340740a4018031284002a22101403244c54103105 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 431747176 1250 431745926 431745943
    0x60d050604140402090a09080910030603020a06090f060f02070f06020a110915010813120903050f0318010c050c0418020906030a17030a0e060117010e0c0a061121030405 74
    0x102d90304650300d01600001c1051300010a02003859441d40075943c10042c2c850119400510000c01c0d6917407035844200010001c080b40d0108900451603c080072844a000b0020301003154031f40c031281c00700c0d18204001111101c4500e0381c07c0c4150304c00e02202140203001c2142c0200600f40b290700515034004603050030840e0360030510151340903c0a890038840040707103c80007402d0004003802e0000e080d8403802c80103000010315010113015001d01402801d100b5600c822100110b07809201126100743d1070320304907601c0307100d1a110b000404c030200441101365405454080003541c0544280d40d804040507021409849100e209141d2142003542c2c098110b180000e17085070014001d0300140800b402c42d66070030507098609140c2a02910012001843e00512600845100400034003601c00c0381d40e45130031120041c121415007158550803c200d8246850000819041e2a20003c2080021070314169080e188250000e290f0385e450b015022161062016800c130243c410804031a02c0c60350703481d1a052260610611 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 431748426 1250 431747176 431747201
    0x41203051303020303060f01090305030a020102070b09010204050d0b130b0a0c0306080312071107030c060804030e0906010e040e0309030f071e14130b040e0106030611070f060b010e060d050604 84
    0x1d072080e91022a0380001a01e5101500b581c00a42481ca80305c0140e03060840ea41c801049880000b88840c000350741900038142d09882500301c0112919449400f6080c1c0c052070080701d40099050510300c01045071406001d03004142c40c0c041d500085115221183c00080496044100359224100f0103000c0f6814031818004018080156040501c0559001c44071840030346143e0410800201e02041a002407116400855000c0031700da180c01d60723543c4064100d88046134194003003504101076035003608006040910481c0141c0d22580200d8030b41c0104030080c00043c1c0c1a003003612090002482c15141040f20000c1e0042400060440303030320300615454203650422900d40d008150500030050794843d0501e5006044045035650000d0503a409880004c1c950751a09503840b0f030500707124800000301980000c050302c1c01500c080c0700d201d500303a040080e24415018000c00308070f070103200c000c0400c42541c050601243d0502d01f1041000c030b0000002e00c0c5401c0080c040c402d042d0b841050005030310b414032804002804 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 431749676 1250 431748426 431748451
    0x20304030e031902012312091e0c01030b0405010e0a0c18030b040b1006020a06020706090f1103010b0a050f0f1f05040f05010e0a03140a06020408070f0b13030210090e04120305 77
    0x113080414a08501400d0140c0e0403510030f80000c5042c41c0b506211000900a18270702c01400600c0310302445503141c90301c0c1c0080380030034035100901030a400c082c01a03a050303900d07000810001c3c3d26a003d25200400c15205040101b14500a40c500b11054900f200c00080d801031039032202034200fa0600303602c01c000282181d540d00c00310f0b0100308815500406c022041940141d001600c4118500b480c0340070b00385840707000340b440d50b4942d803100c00c01180d14018050610305800070450005505d05124101d5182d015040d1700406130140e0500a15000809241360500585611843c2c2c0b6200a052045030713808032180b003c035601140078850b902050039940d000f000c09103410042d240c0d01e0800f00b100084540005050000c50403480822090b08107c081441030784007004540c8d40e41c1d10390312161208418020202903201a407000548075490006961285445452040d00ca51940d820009620740f1a00d819043c0070300c03190001982c0300200001c51040d4080c0c0e041c4403d0007a1030f54000c08980d80100509442c00 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 431750926 1250 431749676 431749727
    0xb070207031b0807261f0b0a030203250302060705011d1903050304060b0a0801060906050301021c0e0f06040b01050f0105030417030a0f092105030910020304030e03190201 75
    0x3080020200c04648a81c0c01980f00310072070f040e05c2da40c01c500d1690441510b1103542c0c406c49040b0035202e51032211000c200300c1000007000802c108111340c01d003444041d6055011062501d2940303005145020480b14214440000f070341d403640402c56940001d54190751a0b50341e400003807020401c411805a510b0601c201500007802c083d100541916013040c1c0103004c004001c00020100001d50f031107a110454014403000030580da4000c83c5018051034060314042d03600345280010203003014001e558610b1400d8405600c20303007034080040b00508100c4201c0200344115107950300303c2c034024881140aa800b13548000700d203604010034003c1780c002ca01e0000b030405c0b40c03c20030040850035040c060f4860443d108900359903600ca20407501c001e40418500382010919000d100b10422000701d140f507200d6000b042c06240750102000095429000c00c0303c04094a0b048901e100c01840340369030045030300522a091000704842444042841c00351180a140c50780380d440c910000641da044000c410641c540940084400c4 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 431752176 1250 431750926 431750939
    0x2090901151a0304030e0d050105090709060b040605043b0f0115050d0c0e032b0908031b01060902220503030f16150212100b09090619030b070207031b 66
    0xb4400100b02801b00006010a81850707510002e4120b062604103000380454181801e0f00ad45500c030910809813014603203035000418024a00c00d0310100c032130039203030700741003c0c50300e4424800384502c07019003040700300c146c00541c68101c076440c540c62009004100d00300c024640000000c4504d0411380100c0e0003400d0a05e510320345154040c0440716001003141010a903a540240240d410a8280002c944d2602401e0590a00c5070412108040b0101001821800380200d00c1015201c2610380d0107100c1140c0c00400c1281d400e80b40805860442c00043c9000150b11681d41c00b80d50226001a003004c5400c8880d45041c0c214034080c90a0345025010132005149028003c0d4000107182c8144107a128100003c0c1003a8000e200002c1e108415164080105543c1c0d02d41802d040304c20a0b400712481e06407400c3c141008981d01480308144d48002101602800701615aa000c0140c03203010051495a40061000e000c000242c542c504240a030ba1960000d0028030f0941ca00360701c4800c1a0f24407002c484081c4d03507003044003 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 431753426 1250 431752176 431752229
    0x6060e0f0112110315040b24070809030106030804090c08010e01270504290408070611130315060b07050a0201050c1002190e0d03080609130209090115 66
    0x30540074240409102c6042140d28050a1640030f440491240402040781c2000700340b0146100c0b0380f0031181003280b80c3d100c3c010400f40005060703004100544e000b41844c1984010402003140c58010030784079040080720000603096581c160411204104086001c000400d01030181c030160694504100c2d64a604081041c00c800d10140304045448543e00c0100c545481030302041c015600403944284114502030074180319107946820303c145050300e882201c5484940b1422240c0c01541c0c001005482c0a145440c0c090182840350283e01e9200000c100103804c009488561400462040d01c01c9060407a140d034031002140c016900c02c82c0343c2c4c4020424040054008900748000650900b0300c40d0700c1c0e0a84100c0ca600d080c1001e0024586107200040e812000b40d4840e4150050f0440c1d130303895103075500d803803014028403000f802d000601044414010980f039260440042d584880c8045500411300c0c41e94000550f03100007520341509603590340c2c15040071f400038555258017426800c68a140701e4072044c03451810 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 431754676 1250 431753426 431753449
    0xc080d0804111302040f262a0d0f150605030304090509120d0e060726361b0a03030f03060509040b071d22060e0c070606060e 55
    0x112403040488252a030703950000c0e4105607401401c11515a03803030b0710384c4840401c203600030420501c070445625101d407034840a501003200d41100140881c0c0c030401c811f04054100255070984401040510b60b41c032900c89270712800003180210000d2441d12154204408518266542601e201c2d051020600c21600c0c008201c038202d460071540094540d482c007008604000c51b00d00b803028282c10008030f0707a5104209420407010a113010090352280c0c0c5440006807035681c02d48800302c00692071074030300000048100798040d60016280900c034490082111040c0c034045405800c80291004049038010a0a010412070803500c640c911249044c108040010700c04202e648001001c200c01040400100b0740700e0f8018000415010b011503420b414245000c8400400884080e0009030700145240308016007600429030b0604007410086420300d09200340221829803031114812030792120b000160070300340800321503c100e40d01c0302416240c0103c1d180402c1aa5450b601004c2000700c0316030071180544da0100d00c01c9 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 431755926 1250 431754676 431754683
    0x80c030c1306080708100c030603020a0909020a051f1805010917010905030d02090108070801030c21020303070b04150204080c060a03140f18010e0a0809060403050105130c080d0804 79
    0x181c1c001c0c0c4a034050201500950a80d002d09480020384003000100741c00502c414403418010301c03001803003c404440c0700703200c00381d800200340740108020b88103644015640c1c0c4c0051300e0b5071000b030785400104030f0702040302072001141e0412402520301a9400700807001d141d8515106200716624000c0002c0c482d190a024100e20050140d1401a08502c25448941460380c4102641c0e01d0300c2c840c43c0040000d411810410340030522920000e0841c0703201c0c0e24141c2c11307641e0203006203d82c6804d018145c0006100b15104403914400884000050380d0704001034017415116403058a041d15007490801c11708011901002d075480d0040c0800c2c0018000403c0a032508042039400ba03850766060313030046020701505041d01c01e0a014000610148800e12495144915030407100c80703498032100c0103070a080b1145521034181c42d800c000c064000140d00c80006006491004240c0d41c00c040d201c5d11060300f1a0810307a190407500500e604814104030004030060003c0000074054490f030014a10041d000001c0204010f = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 431757176 1250 431755926 431755939
    0x80f0109020d14071a0415050c3403060203040203120a093b09010b150301030f03110d0305041e122106090914030c100506040618020a0801080c030c 65
    0x70f4449407013001524020b06601c0700204041400f100010341075402400740b2205041c20364084002540104221140d00c10318800070106180c030302e00030551300400e0074100d02e501e0f10018020302c00380d10388580f40310207140503180060342d0741400d01c1050b1420744080003414551500b444418202504030040c07070200c541c03010420f00c507640d110164004525030381c0740d034441d0b610042811004612038103a84074440c420410007000003201d41d004101c07488034814080c0c10940e1003000180700080c0200c1c002c1c000302e84203052a0b1403509a40007403c0c10000714140850003e0364030403c0009002403600f15405c1440000c0c0655240d0b54a5100c02c50304000001c454014000e4941ca036a100d005071b00c2d8041584000c000c010440191151090400f03050541c03010760360702e0034040655511100101c1240c2c18001454024904500c1014a010281c07800801256000d2780d180c60001c1c0c100805128007074084007440006a48140710b640180c51443c06801c51365480d81301c082030f202c6a80740003401d01000030045818 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 431758426 1250 431757176 431757203
    0x6130c0527011505120c0d0504051c09080709020904020405210d0305010311040b12030d090302070b040806070c080d0603080a0314060a1e050d050c0a140f060705012301080f0109020d 80
    0x41b0405440b46075102ea28242c03078070080205001000c10f20305011000e802803060b0480490740125400246400341c0c40d016000500100321400c03896008148082001e880941030541d10400181e11100248014556820f0360b4640b4254500c140300c1c2c100d452030f05003002c0146506541750f210130010b541c6000c1d80181d036031b108c01d069503603501d601030b603000d40000c803c80f0b69034580d488081020b01002c440890162107a50000328070710443c0019a07043e0744010380242110fa039414011a83c0403403074042a110313003c007044254141c0703220780500340180d400364614565401610358010704488043d24400e4007072451009018441da21481f00c1012105441941d282c010320480d000ba4074001c0350361013540d000c0303051001c0c44108180442c0842109004881104100b40d1341c8140c02c0185020f13041680d0301842c2c081e803d90140c504000074240b954003501c000100d4211001c48000c4c0b21400460140c01030501d50010040c040b030800151401a800750000e00051200c1d07404602c004c401c4900007050010381406 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 431759676 1250 431758426 431758441
    0x13061110050a020c15040203060f0415061d070e0906101b06050f16020703080a03091e0512070203060604050c0903030f09040b010305040506130c052701150512 70
    0x184803032030850400c0c00c000504042c0d880c6802980041c5482e545802804016800c813504c2c26040c1e44959000740140c425540d4480d9070204481c0e00500855030082c00b510032000c075000510401001d4000c10341c0034202501c0c40000400d40c034100030900000c001030701140204a4950f18050364101005450f1051285a81d074802c2c0c2d1180c60209860301003101c0d50148005000040d04000d0183d45a800704031903030340710042c05c1c200354540d80c0001e102507070114000f08002021940104820011890b00042c100d0256840031140c524070224104100742e0141c40109000d0148900c4882c042201d202528044090340440d45401c00244150300c00d59458002545003410340b001c4803d5240024245c9a90b080d0101140c4e0781500719410440c0210319105001d50294000c6c8240c50143c1d400074000c00b2141e4440500030b1940b00590002c42e111b20b01d641c00061140c540100003294001e95041860181040d80e440404000d0160300620310b20b00301c412010201c50b0000102c4043c529046241101a0360390070 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 431760926 1250 431759676 431759683
    0x20310150504020f0d050604020702100c1a0f100b0301060e0d05122d03040b0604020a18080304030203120a0f11070806010b1801030605010e010309020a05090106030203100b130611 79
    0x40c0200c2d0040d000062144030b98940070000d214120550a041110392501810300c405c901030540000d4010340c0f4601e45041f002e01400404d10907606c120140c04040d9600140112208000d4031903201510307078034060105820000394a000500550742c1d80d5421580744c41402081c0c4d07011a0703005030180178001d400400f40b000c00e00840d102402d101c2d1505a4640c0d2441e0880408c5030315904084684402c9421600c122010750103e0b40996000f0b9240801600c0702e030b003080000c1d40011143e00038002e0010052001d5080c240c001d50051468030069526507145005140c103003007a80002d07a00036141000741e191050340000801c83d4100329460940e100002036080d403813802400d500481070754410301000140403000f0310014011644068a60082c0c10300420040d01991264021b45001c20701161100c0c9041d441381d4012081e181c00144507034680c42d074820204030140020f030007001c0003a8000003040300f0114041880b10061071901d071454a0401d56840d60b400401a40c02890b00300907904038240004101007 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 431762176 1250 431760926 431760929
    0x110102010905210f0c06090609010c0c02150d050103080a030b0901051c02060d0509060103030924080901060509041514040807170d020c1f060605221502010b0301060b030402031015 79
    0x9004a503107442d40758603079079a01400c03a9001c1641c441d248c0090340140d810300503c5003a004d02e4881041d030682d15801c00c0903170341601001ca50200c400f0b0006203500d08032401002d00850080000316507909141000074280d444a80d206401107201000401c41c5850b003035811200d604107500050b01c01192840002c07044d02c20b00002180d86418541489400c0340081000e80c1281c0c401d885030340d60306543e01c0d100040d04030050311090040c011408410403a5009000d10fa40c000950000000c1950311b0304001015002d05950503a088103000e81881c1c10041540326a0050100c18a8803980500c0c213540e40e90700070312400e24010300b50100248294841240300c4180d070b2520301102019074036003400da030069507200c0715808151039040d0001f181403069035403807058005481040d600c003450020440c031544450180001001c4003220002c00c009400310712114a00e0600d00503070300101d0341c014468101070a46142c0d4100080d018400c0044c400141d4001422000504001d1000316050a421400c02c200c07040a = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 431763426 1250 431762176 431762197
    0x90c09010602011506110c010806030330010504091205070309050d05030904140105030d030b1201020318010f0c0806120106030b0109020705070803040b040b250f11010201090521 78
    0x41100200741d058040d0010703c0c54241010084a519a42c1c0c0c1c03040703031081d5545030803035080c0d0888091640b50303511401e469948058041d086902e00700389200e01c00901c41468482031141501a540e0148070b0031010342d00b60040c6000c5809008511603a101c0c2602000284800401d01c40001404e038100f600480200c00140001008000d2214036401c00fa6101e41c071070b041451003985448103c0040801a5089a058950150082592601c09803042c0c1c01054020b1407a940700c4c80c5c03810701d661150f01c00d00041d442040680d1400b600e82c20900c00c154207482440600034810ba052074201c0035042c1c2c0c8561340035800017088550555080303101581038010314045c0c0001e4000240c0758004280d0a0482e001000070902c40d1049804d41550388480b95100d00550260410f041010441000000040300103080e00d41c000444881c403044009150161840000100b200c6014048900341d082c000301124844c0038210a0000f170080702e480c5d40e55161280a440039000d481d48501c02c00f80e50400c051415180b42001 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 431764676 1250 431763426 431763439
    0x605031b03072a120c02180709050a0902030c0a080c13080f07140d0305031905010807060e0d0c090509010605032a1005030c3006100c0515090c 63
    0x1403001c4000c1a8000e80d42030b14500e15180364000f03280c1907034140c4594003e03420264402180a0610085031803c01017103090760720042c3c103600386140490010809002d048540c45242481b071401041c0052506160f0041c59150f10507c10441c01d0b04007a002c0700c0040ba031520340048541d541751010b1003a4041e5504140007008109404558071400007043c1514a00080460b0b040e5942d500150310342d8120345451541002602c0c0341c0e01c0011b4005d00140d40c02c024441680e07099121440000310849030300b40e01500d01684070b010208000380d0048400b0400400542d5480a0750400f51640c880e602c00c0c501c2002c0d04544e95500140382e020080d4040c10203010020244c900466001039004002200510300c80008624048100721a1030803409804c110207240d101c15045036140b00d40404503410240816406141611086044070f45104e0000e01499280d6180901410b11005002c0501c454070210011320481541100101d5400034882000200080c1007041c81d075200d9030064200b28034400302039003045 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 431765926 1250 431764676 431764681
    0x1b0203251515030c080a0804120804030203120304060c0f0c120905150702040506040921090f06080703050108010c170a0b210105060d020f0103090c26060a0c05040605031b03 76
    0x30880b00a80300300c82c05900d07200401034407800b034261107000215004018030010002004012404070440040300d02880f000e909095481d0007080c00c0c03100d03044607112403000001c100410090039105001d0240100d141031403903001d04580140c074001520a001c1c2c00d501e02c0003100c10446100e22105005000040e155074070502d80c82008100980040c8403c920490605d400070700035041500c901c032030190700509105020078444404511003d04008008100030302c0341d0010070008007000b001402003509940ba001c85103413a080042c00c035581038001022130390614001e02403050b8040200c135140e280401f0b5403842c1e40c0310240424010000751120580200c55100740b10f404209040c481d11064815000034000365403403408105182d130302c0c143c0095120303511507424035055100e44d1181400520030400b012013507465060f02c00d1040e03012a41000400c0025880c02016101407000e1500000a03480074445c0e6105100044c119008038083c1200b000b0f0048000346803203000310500b5010180300c150701035490 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 431767176 1250 431765926 431765951
    0x40b010509280614090402030307020607111f0e0a0305070b0c01020408060c0c070906180207020d020d060203220b0414100e4206010c060f1b02032515 66
    0x10f2050f03106800d031074100d064105541c1d003040000d05110b02d60042c051850314101c7d501304002500002419240100101002061500c81e1500307181c43d00c0409100c4400002c2307a0390000d00d1000e1040c0054083d84000c0000c0000030b13800104182502c0520348000d0b200d050040b655802406640e020310a0351041205205000902000030302000b070304d400681c0c441d26122b411031020746035240304000000f1800240409203004541c040c0241d01e200400400c101b84440d0009902003801c00d01c1960516400802e011394807103030302d400444420611081d0304400110341c5810224001c020809820700d808200c01e01c005d010148107001c40b40210480402041c480707800b0241d55062040c0500305528042c4288801150301c4084d1a04004d61164403100c0e06007150104528084014001c54107011507011005e001070341c81d00441c0350242c46208001001d00030464500d0303402100c0310344c100540d00700b007201d4171032108103400d207403140c0400d005e080340d4004607858105038406000c681004090300e07040d0150a00c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 431768426 1250 431767176 431767181
    0x2280e041802030d0824040212071205011401020616180b0a02060c041809080912010203060f0f0108040308040201020a0b04110901050f060702150c030703050a17040b01050928 77
    0x6842c029401c0b42c903030b218002d1060b688180e06855041c4440148481000f100340041020020101d000d817025080580d500c05080d0303400400c0d6403030004030700c2045035404102c0340341c400d050041c02c0b08140302800c10480b80c000307502c0e040090488422402c881440b40c0116010340e1510380e00c000180d80c0307a003441e40d840c40015101d801c08503403000140901004100c003810030406480c00e85c1d442040b2507400c415184103140041400502c12201e4410602180b0741c00e80c1c5a0001c3c48151890368000341e52480d0440070010940b51410001e441440018441051641e00421030b80c1e00961504100045032110f00040c0d242043c41c180050108000b801008200710b426a40c403a541401030f600260540d803100c04108080c1100c09025811200074480c41c005440d0403003038038807120b9526802500d080e880c0d44115080d41e00680301900031490010b986400641d001c3c0c40500b043c03581c088919000d00342a558440546010301c01d1034440e801003008124201500317440d800000c621050354801c480950000c1402 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 431769676 1250 431768426 431768471
    0xd0c08150613030b040b1e01050a0b07151a03191e0507120309030605060108040b0a020a05090303072103020306030c01030e0312180d0c15050705040306020309071802280e04 76
    0x2c3c070541f14114182c0300301c2050f03000ca05035803009011486650500510040581200c1c4043d2450b00e040d1303082403002082e502c20710b042160007003508911680107000341351030482c41d4030000c102030704511300c260302085d42c0d802180b00384460001c0800100c0e1060070030616008403508400600c84c08503400c2c030304140d005003005046901c900d00902c4507513260b400649407038030f044401400050b107010001e0643c070b102d80d0041105100300d040407814050034001003031a580001c0002c64103001012803a0710320001d1121501e803400d0451078150b25614190010903110310380100c0c43e030705240c1c440c404080300040600546181e986410869000745ca08100540c080300240c6a180d0550301942480701c0040e80b050210a00980d0003034072500c010a911202c4400904000341900100724003400040b000407200d000450042c41d10600808490b0300b846280b480702c480304400a10110f20401220503148604050b03c5e24904505a00b52090303a400034040d17821420541032a64001e141400c1e4460081c00c0a9190700d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 431770926 1250 431769676 431769691
    0xe071407150603060608010e06060f010207031401050106080f0114010e0d21230306090709030506010305010212010f05030d210c021b0a050d14031b01020d0c08150613030b040b 77
    0xa065032101b541c0e08031414442c101034a03070010320002d0413a04040c000c50b1031713102040c130481d10142d9403500c0d150b40300d903200d03580c856050b5180c000401800d64000d07030786a04403410015009032545490702d200706a15003c45114148550907450725825039525440480c00e91b00700081d1805c002c0d142c04140c0d00c01041102c60404112a1541580c403100412946164000040e04c41c1e03145da180d16041140c0c411000f0031501c200440c506c004400a5410300c401402075200e080050f86580c0303040754064000b9016082503078002c004050411181c1c0e000110314400410a0400806e0200e0100500000000c0072010b001c03031b81d0406500074241a80011400c054200221144451aa000d1b00b000203d05040c801c1a900014070030b084d07000b041c20750804c54080c5420404680c6442141d2103050364000500b0b044540d6070358081104010000903001c5d0050420079494000c0c030500e05102c000c2c441504004450380500302c0400d2640301852004230803400b96401c907522003101e03d40351812002c4d65804407043c2 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 431772176 1250 431770926 431770931
    0x1e0403120609021602041a1c140d090611070f17010f02030609240307091416090b07080c0102300103030c02010804050c09091011040e07140715060306 66
    0xa01c800d0342e40f080d100740340750700d10841000c45166000c0002034840341b06c10300380340c80a40307046040542c0d891100b0100503074005c0d65030076051014205080004800442840507420998145010547c0009e103a130aaa44604007079001082c1008040c1c0342c0320f801e81001c104880e0310400424182d42501450f18051010802402070240c004161402c1c1e00050f1000780d003203003d0901140020075210b0b440514011013600c00d032801c00c259030000c2d180100c0c40e444040700c0c0e60b0b14120301489150983c0d46560202d0309100400b18070303250f850300410803200c0d4420541800e002080440420145504481d0000c0500000391340740c410b1b110f038840c90390501c0c00c03510100b2400d0b0340011150025203111a4100c0c2d8058854a42455035a0015038000400a10445207400303002c5d80d1094a9492082850045484a004261080380b500c140c6045031130071940f68180107003d102c100710580c501c45111303503c6256403a0446080f40d0718100455a80101c00b00100711004110b008080f03504550b2202040f81d0091809 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 431773426 1250 431772176 431772179
    0x1401060902041412240403030f09050c0f010504050d080406030c020a12030207062a080c040302150f0f0c030d0f020405060d1109040f0203040c05030d02030d051e04031206 75
    0x12007284142d100e4030150721881c81c4100550710340003803612000e10080095030910300340e003882c0b4402038592800000c100356041051005240d41031281a003d031141200401141ca40c90301c60960b2007518002407440750207900c5802c00143d110300e060304c00410002d4940c801d444458500b4000d290494014a000641b40c1007907403404c6440090380070025508401c0d200c6820701181da044000c1e500c03c01080e80c0040c2c80d20351a045040b10040403402820040d440c51050350840c0c40006c11000340a803005160b100c06010920259480b121010900c40581c93308503034640300054014103d018046403030326410130118400f01000008001011608441901009201651860103040340114014280c00007020720400c910481164044040000171468060074a280e01001805031041c101c0d5203c0c0154020007030000700700c81c0c0c0080700040d041c02c6003d00842404404000e60381d0240510268503d5110300c0032900c043e842840c080d40c0e6022090040da0a0b19040c1805802406103c00310a2a240341030f07170 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 431774676 1250 431773426 431773439
    0x3021b010e01150b0f0c0309060a050304020306010905010803040b03040f060c02060412030c0e011d040501090c0806060403050c15280807020f0d05070204110406080115090608071b020d140106 84
    0x20543d0581d40c00400c4103003490b00900001005401440e6804111b100c200050070712070307032040c01500c048166036690546c1c918052050500304070040c1c0c07203911818140b100620040a01000707540c01e50b1021050075032280d91798240071254035281d01002d04113600e40b4220007449039012a00c540300e1802000d8103144011000011021100c0d00c004040003d01004101c241941c41541c1400300303003200c04413515000e41d07004001400c0394000c0c0e222840c40e40d9078010000342c4135000002594020b00440d8a07031f082c94550345580b81c0324218001d0140c45403203501ca44080b10482072056030f00074070900c02180c40001e607401d011141e052002c4003480c0407403038040014810324400100e10081d03a04d103601070551400c5020040d2810b81044400b240d00c1522642544032410901d80a80b0040c0019542e4031842d501d006e004802c2000858060b0303041058035a014404a0740003144550404518900f42c8580250802d20300d010501005000303500c058070030f1503103042c0020140b10b20a4203250704001c0003c180e5811 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 431775926 1250 431774676 431774711
    0x6030f010f1406030f040203030d050a020a030606030917070f060507030c11031303030e04090b15100206041a1305060708060405060f1f0905030f1621060b0103021b010e01 75
    0x2d500c95032043c403c00025160201180026801c2817014044034140540d204100054a008507044041c69a01040325400a681406180000c003d107044c10001250603443d0030203660342c0c0d4088001d0224000482908109059800803e22504900c08000c14140072070010007504c600110300002400e280c0400504600100458981d030080c000e000d5040f81ca0755130185e61010f5043c190641c059620b6001c200459050500188500e42e5006000f42d0040090108070350404008580b000f1988540d0800c000552043c0b54241a500254a200c8143d0b60b5040a412003032850880180301c0e02030391040c0030381a50000500c2d400b8038021102842a980d0720310601a0300d89501700f259601540c03844200580403d54100421080c1d8185007070301c080c0d82c450700807074580f581c01001484264083c500c00801600c0b00f081e1030001e860155003400b00030080000e0401142c4019501602055440c003d042080c0e010394101d034004410302d0540a850548007074614003c00b00c1401c0d4500b035508008070046886c0028 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 431777176 1250 431775926 431775959
    0x311010c0515040b0c210603010b0a030605061306150c240c030b03030c03042711040303090e06010906030c1e090302210607050d0b0604180f06030507150302040506030f010f 76
    0x4110011074080b4001c006c001c0780002e0003454041d580e0b00780d07215a5031509140003000e1402030b04041100d080043c140301d103c940b00c10a81c101c0c00e00d4942c0510400d0700c403060400c8070020b00d103000c454800b09810700d059500d00d0342c1010a0f44848441d641c43da440d04035001a80c0c07402d05a101003002c021202c2c141504d038400e442103520a500b003000280122503412030701c2c13114001d900c1810030f1520741600443e4110748000100da814200085010402c042c0c1c00851071018140a040154003410800000b03000e0708400d0013a41c1c1419155600074031009d21401006030b03041a1884a425140703415000941001c403a03010982c007d100da1904400407240821707202503c0c0d519407004103496034a006045401d034004011080c0b00c5078441002d0290341e9110005000a480740316075100c1d06000c4801103104580442004100e00341c103003042003020403808102c80c1c00310b4101c41041124182e480d02c08a0080c800d5400c15a80614003000b40101c030200c1d03030401c6050b201c1411601c440b02d9291022100c54038082c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 431778426 1250 431777176 431777197
    0x9060109031707031404060503042d0b0711070905010501020d0305040f030e1c080a08160807120b04090804080c030316110d05150403020601050f06040311010c0515040b0c 75
    0x614102d000c01484181c001c0520502903e00025010610405c0c9409a84168405800504048148403e211a00c60f440d4081103c80c10400c8450407290346c00c1c90003c03a008000b905c159180000114014010038117012075005e00016a440c05454025440c01040c0c280202030040c07240e8011884800d000f4480c1c2d80c0580e82144944542c49500e40e0101c0d81c0c06580300e03110340c0001d4001c080403a01d6a0000c14481041d01c508517154940303c607520700602c1d10034014182c40564219880282c5044e420805036a08926540b4188030084044101540500310030360038540c003d80703000101d41c00c4c400e021001e072054076088030a070349034846030301c00301070756406802810350203034540c51580b4000442d800c5040000900c06080b40326800d042e51a035505211020040c8a4454030500070041010b905014090140c002150200761364195600072414034055804001c10780307514003555180b02d80c01280081c11959100e41250440c4850003400d40001106903400c4070341c3d2440c00d011402e00f242041c19103a60028 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 431779676 1250 431778426 431778443
    0x20702061c05180102071e0501140702010c0806060702100c0206041a1b0609030a260c12070203340203161a03060f0906010c021512010806070f0f0e0405070e0906010903 74
    0xc209906694424107c2e108403069960341210202c0040140d90b540c4c070030b800035000003444640716800030781200c03001011284640c1c03040218400507642d8040640e046080c600e404649071041e031020030a00e1003070741c02c8011642045210f00004d094400010100440301c010040007820500760b042c0ea81c2c00c02170300c01900c15002403002d0305490344a4a50103880308654642469034036580a111048090265903003070300c4003800515a402c03600314070001504502c0d14801180f501d00b450f80d17040c44d410f06620b050b05201140010800f8070130030000d4100016a0002e0a0311700b0301c071254400d41d45800c84c5101c2c002004140303144501041640c00d003503a1180300c01900b060036041542040281c4041e0007084141403045075030069026840303071607010f520008c2c1e60b1105035407100300002810101c0e005a00190303040e0303c40c204009500381d1240a402c00c82c0d502e402c3c4020080f500d241c0903100180f0014809070030070f107400e0801401d5540300c00304244e2410b040d2403180702074031100d00460b48480c550002a05019 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 431780926 1250 431779676 431779703
    0x180e0f0328020a080f070c09091109070801090213080607080601020709050402010207270e0f012405090c12040605011a072d1406072010020702061c0518010207 70
    0xd00300c40003048071718401030aa40c81c02400341d0f124030300f08071543c128040b01943ca0908004200800307010082c02c0c08102c500800318604080001c0042205000d0a100940c01040c0106032100b507840c4000030302010029154140ba251500030410002120705c00d006204056002030070702107521a00e802150180c0c06000070704d0230040988245500d020b0031551103003041c81300d0031102d0000e01c0b03002c0c3c426241502070482d540001110340d080d500f0245181d034508180c51440c0c0307d03406c3c000000c6001c4407001d640ca8400341c0c1c0c4a8524100c113006681d451b2031038100010401040101710b60056042e1045030b014400d43c5651003500304e280e40070300140240954408148100b4401c012408290b1010680074100c02d01c455607519007040344441c030604140e66014605000b4a0354009400c003102a101040e805152059404259a00d035402001c42c0c503902e82c0000c02d542507460748001c0b0340d006010201c129444022074828000107180450755040741c070382071810009081d04180200e60340550004011060032 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 431782176 1250 431780926 431780933
    0x20d0b15180604080d08060108090c030601050f030f060a06031a040f06051b2a010e0304030b13061e0b0619030e15010303050408010b03010603020a180e0f0328020a 72
    0x1400181c078140e0b010906002c00112083c0c01c02c5252015038482c1d81d5004a81080c1d0009040080f0140c00c3c0c004540044158808a84001a41c24110340d4100d5401001082001c040b85c1000b402c0801c48001d4011401040003c0c501c54006504a82c440c002202da0421951030001e02c030b040c01c0c1d50084c48078030f0380a40000031604035000b0503001041881417000c1d42040380714800c01c66001d00000c0004c40c0500122071445610180151040807918009020340d0740c0c1c95100544078030a501000b000c080380c0e4030104900d00f049040340803809500c14005c1102c60408104181002409034003c00c80f141082d0018040781130050aa901c10034604041c140186003410701a8003800381503803c0090ba10850702c5010010400c0c1e828507000314000c1c0c4910341e41c1c90404d03000a0968500d0031119019a042900c100300580301c025070501200c0b0102c404050444005501c3c0d009070541c04095a010301c03c03184c0003a913029001c0010000000c90140c05c0d054028001d0b80d5100c00d03030b680c403016005078105c2c44880307011 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 431783426 1250 431782176 431782207
    0x3031407020117060f13090212061003030c15050705040311031612060b031e15160302030a1506020d020c0a0b18012a0b010605130506090111010f020d0b15 68
    0x4131038010900340d842007408000ca0f054044030314400038080d032284035082c10360030801c0740048511201006440e140c036000704910407609503031000a0070000c2c0080880213100103501043c5203441408014070150a00c01002080ca41040c00103403100340700226241c0e41403500007401c02c0002c1842c42c40c910075030700e00909521458505041a1040ba881d001380400a560908c2950804403446125240801c0455026440c104215185c925034210300400c0c0006003900200b40317008104280f4006d0703601d0340e600c1c1070400541003183c0d40f0f204600b8401004034000e0340200b11340d4000c080350b0f400c0f191100071007820045042640e2064816006080154a10440c00010195030128060501f2510901f41c5c0203200c048509606616500500d49420301c0204003104000600410003031420034100b10350915000d040c11500c1c45aa481000c00080d5802940d02407455050b810520400030840041800380100c040c1d8412005c4100e064500500c1c007102c1d140800b0000480c2e03130080c810500b410680c0e0240f224 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 431784676 1250 431783426 431783431
    0xc120b090c0a0911160803010311090708060f0a180501082a0904030309140607260f271609060e0c091807020a110303031608190e030403031407020117 66
    0x10302d020800c03064003a61780e12a649460f0714401c4131616a20761460914109030214400001d02c15022441402003450b0f1103003070182c0020040781c401ca15402004001045102594003a0307003031224101c0b00d40d400203801e501c082c1c100c0d11040c0c02d03103012098000c00c20300b52001050444103800b8080c03d072408182803005206a015100c3d0400007956800b40c0c40d000740415020903d000c0a511103c10003a9840c2d000f55004001c1c101900f50b4611026000c042d00300c10000100301c0c481d00c0b0344440004a10022a1340c08481c0100a4403400112801d03000c16580c0780d2581501c45512040d100c00e001076080680d104100c2218401c40050b400350322a002c018402c0c0c0e0200300b40a49c84040c41017011300d0002c1060402e07000c0d1003180c0003003924190314501165104203010b40c9511a8009108000c0200148180c02c01010301500d400300c140c0d40c401020316910510301c040c00c11644c5c600400703031446010010061041c5c90007030702c480226940200c00b500c1c0314070450000a00091038040611a03901c44450325a4 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 431785926 1250 431784676 431784701
    0x1303050c21211e07060e0a150e070b161a01080622120503010302040b220e0f011a01021204061b1e031d0604050d02120304030c120b090c0a09 62
    0x5260503c6001d861a10b5942c0000c90007414000054402c104221803203010350580c2020054003d140c007a031a00440b0000b0001d0a6901544425681a0480082c0b1000c005400800e14840d100c840d12008804002c6800030216882d840e041111a00300d4840d8111b54100c6007130304003c080c0c56070342c22084000040c0e600c035075149561100c941e0788000750408108260310200780d560b0703589940c594010807081d500e04d042428000d00200c1c1c48503400c8280e4141540001454179800300340840b1012032a8a000304600e01045a541703030140c60301200c4100e050328580c44a0036401c8803200041982e0300c030280c6c4224072914000c030f50031002c400b005070188020381002c10b0060043c1e0982010081140d60440b4400100b00c2c0004e620048100c00c40c0a00081c0c03a20030107042e41d2803800e290404000c12a15035103018064031482c030081030b03190700d16410001c9030f018550002080010f903544202c01101040c0c2c14404850045c001e40c000788001c1c034006803c540c0104020843e0b00715034500060301005190602901 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 431787176 1250 431785926 431785993
    0xc0e100c0b1303140712030506040902011709070308070803150306100618030203030d050f011428031407030515220309080d0e040b040b0112111303050c21 68
    0x11000e14013004013a200d0240558a41e0000036242040101180e10051189100700d240504000140c1d138810042c0c07140c00080719940115845121041c0c1c5045815880104568000900d2008000305100954042c040709030000e540a403410040540300e00040719560f40c500e030b155404219041c801c07c0d60500144401030035903401600c0c2d4002ca41544e00010105400360740b0741007400201d003000c001c003600620307003000c21040c03854007180050f04008145000c010380072044000e9411814030940990000c543c01102901c92000d141521500c2d2603503480292403a000301300d14054000e002400d024881d140780c460079098828040700103860b40841020035400c1000140010400000c1000010400a00c03071315415003d085070b100300b1040d10400e1460340d001c0d40c100085000666007004555241080003000490724a15030754a82145000d81c99a0140001c1c51000000c24840d000c100c180d0344140c252020106556102e0324440780c03500b00740c1c540700c5580c01580c0c0e0500e102e1008200581030813000100 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 431788426 1250 431787176 431787197
    0x11a09060d0509030c0c030d09091d03120907060903080d0c1202130305071e06050304063b1b010f09030b04030e010809120702040f0f0c0e100c0b1303 66
    0x70101c4404442440f4203501c0001c074228408420481580704042c101d005104214440c035004010031014840c400c905901d400d860200c1185184880f0031401d1010304480c3c45c0c80082d8000c082040054512800c0d81c05003c20115400d4031030310003c001e40381c1003100940703802c0014150800519071010752804020403100180c400712464001840d1440114100c040340a0440c01c102e400c040640d4055940c0f01d2030b100102070b1400300366401d00100c0b501424055102e40d43d500703204015040c0040e03510b18041e15101c0302508079a5668151480e031500701d0030040042e090174042541d40342e45414140c1004074400002e490b641c0300702142d450103521458541c540a90b2640c80c10b80480068070110042180c00404200380c2d41d000d0300701948509070000500f414000e2021003011407103030f0080640200d40300e1116040561154010840703410503540c0030000301c158440024103012110007201e100c2c20351006000c403960312a003421440c064200000c41841d4490318114501070f00120022014004030780d04 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 431789676 1250 431788426 431788447
    0x10031203090f12090506130e190f0c08070c050a0b10080111070203010b0d030c111f08070210090b0c030919060e070e0903070609050c0a060c02041103011a0906 70
    0x28880030f0300c12600101086000207001d4002580c54124034000d080a014484042151408203001c40b8010303d80607410780c03107100110041c0903541c01e010702000c0c18041d420307003007000e1a80041981c0600703580da0742103a25070301011208010103060152113507020f40034202c081080800744940101c103989442c040e01d540c803007646007500c040180701031021501181550035401c0030301485420410444100d8058441076401620949680e94094500209005007290a84419070316648243c140c181300e202089003003800074460310048070032070300500418203158408000750060559407070740030414042c2c6541304601382c2895000104100c20600c1554043c02000c00c0301080e00c20450f005420215070308101f608103614001142e03010650303c1801c0da04110041c540801500d001582c40400407501e5074150070860700c0d0401d541c54250340002140d01c000f80d400d0f00010308040a91007a50280402c520a941090703550000b403080482e07200d150460b0003503200c1d008000700b252500c018082824a21002e0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 431790926 1250 431789676 431789693
    0x90d0b180d1101060512060115020115120302100c0e01180902070807110306160f030615022401050a0302010f0c06050f0108161a0702041407020102040312081003120309 74
    0x10000042000c80403020030085003130148001900090752061041c5894107601981d42d1014803951455942d280740740d07030240b0710039008914200440310003402c1c4952241e00203109104604001c80252003031946441d01c584e0180500044d00c1c03115120b04000402002c01521f0408030300024900c6d20340c031a00c01044281180c4090124680182d600585600c441d1400900140d201a4002d1190f404082003041140e25000c2c0b2100c0c4200354603108030b080301444020340280c40e880d08034241c00c2d84e1000f004100030f41e0019446c1d1071442000c2948044064507520f41d940c0d100d0a0003201d8004060000c1800594014542d040c03d0340d0f050f1515904c4404c0d140c45650465400340e034044034800940f001005901c0003000005450f16135000c0b0f6600c7c1e10f140c002d20b111b0000e1000c14141d0301e0340d000320b409015035840b580445180c88580500c101203141c400c00080c000c1d072080c08200c0d041c0c0602d81c640701c0020f01c1250703428400c024200c80300515030304607203440c0680071300403407400c0400d603c88002800182210 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 431792176 1250 431790926 431790943
    0xc040c050c0607020325050307030e040921030c0507050706080c070c060216050f0117150306090f070e07090303050d0204080102181c022b05150a0b0105090d0b18 71
    0x4c2c0d000e5520f92180c1580c940248010040000d20f00710740010860110f6800300440750025454140400000c24100201e40070f482c60710400b600c03107160b071214880d00322032010005c02888a2903038204035921607040c0566141c0201400a401a40048414003210340200c0425411084185a840c00c0840d01d55070620301c03004c40c0c2c102a0040e00400c4c1802c0b005850000b018015150441c3c1d5002c070124007200007428540c1c035a2947e5400c0140303801086c1c0115003544607082d00c04010b01610000d00e00307118502c0c0e86201c850410726440c410040c000a28110342c0c100c503030190b1529a10900701c580f6685080b14183c00100710030404070360800000a00050920003421000082c00c0f444a003000440100800400c044814500c108100b1b14032400582e6105a040030000500b000001462102908025500345200300144284500701002d6090001c0c02803c92140c00740c0007041c44081c001600443d211f000b2101c10680066504032001e0000300c000142036840321501007903980c1160302c1d45100d440e21200 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 431793426 1250 431792176 431792191
    0x20307140703020f060f0f0f0612071e0b0903100207050c1e040f02041208071703040b041202070612200a0908010e19080f04050604090b09060d03020c040c050c06 71
    0x4031300076444849080c04100e5000c409403c0e02850303450540050051084001c0c0140909588a000034405a07240321100000c15511070442d440300d901e91001044c0a40d03408000201c40b00000000100103142c0304c12100e00d044050064007407180ba009040c0003035041604111118014240c0f000710903101e24001100b2202e20740007284800d05c4030014441220020140d04a002e03004210034440112411424000346038040c00d121360f10781190929960081d1000c0c5d0700107400b10000f041c041071000b400460750046014691f1001d401c141484203981d030342c88900c41c0a000c40c842c2d441d001c0701106541e00c292a1034000311085940300c107403404582d601b9440b80d5000c4011512400b010b0029171000d00c00c1c0481150102c1c010500701c540c41c024a180ca60191000400b1000002900b05842d480501550020000580070070303104d42e20303005c03510013600b4102101c41c0140d040100140c1f2034604450030700b2010346c00d5005400c185c0c101c00c0500003d40080b1030180140031081140b2002090100b2115108000 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 431794676 1250 431793426 431793433
    0x7030e010c0804020108070801030b1b040b03090109140d2a02041e06050d05121e0304061b0804031218050f0706031506020601142806140c0303040602030714070302 72
    0x109131001408541d80584160200a29600107200181c09120490307042050401071030310048003c3c04d01c94982c800e40d0480d060f00040401071091251054000720b107500e118400c81d036503004821036081d0b07681419222000001c0e1001421407012203114051801601031424201403011064000c107080d070f0a165503201947c0d210070030080a000d100c6c4184006440c0c12a540210500603885143c0c0d24502c031681c610744107030005164425040740920002c4841c0c0790200d059140e28150824100a00c01840044041400c40380c1c030015840c400d1400c2886a581520b420300d1106009482c00c00138803058060b0007000d5100421600810010800c561104c5122402040c91508021004054130303247c0710301c144820507001081c048640c000c2545070644507000d030100d88030820400091200d50740b400c0011151005101d21403080000780700b5201c180d440725221507000c2c04001c8120000c0e0304c62081c123404070f0740043c0080380004101c0d4008541201c0d0510b40b44502182c007050300700c0303194400f0404a02590 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 431795926 1250 431794676 431794681
    0x60503031603030b0d0302030301091a1002031c02040b22180b0f0a050102030304030503091203040303021305010f170a020f0301081f1406122a0307090905070e07030e010c08 76
    0x607410300a02c13048040030780d00d281c403040043d0740c0a541c0e0f02042c002d1248080c1c0354442c1c4000c40c0848403020060503401485400002c00c0741002035169031140301e4809d40b800c074241990380421024005c842c00c0310700d400c0c1c210786040c580010100b520310f8811004401da0142a40010381c801715044003040145105500055071b000e40010070202503038446560f1700074000c40c241000241e8010007660b030b00640504100741c0d40d45d24512024141120f054030041d03140800300612082c90f502da4044c000155124000384035032500c90005440c6010704040450000b914405144ca04036074002a0b40e03088130403520058100f60b100032100d1a41d40007600460300e1a405484541580403544185000f4174400160801500d0a02004000c80050040156018200080d02609850320401c01582100c1c0b00151072121542c0e82c1c005011a002013030060751082c40f422802082c920b4981c410307040c94607070010050680c40d00d8154451072880d0300801c503800341039442014406600c000e004134100035990f9a102c03507407031 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 431797176 1250 431795926 431795933
    0x207032102010b040b0d080c0a0c06030230011703040b0301030311070e1b0f1606060611031314120d030203010501090e0f06010e041d16080a0b010603020901030605030316 75
    0x41e00700842c0300b80304e1801c08140d840d06071503283e40c4201d041d800a4802e075481d0150032415140c402e0400009158180d8281c001801c41d90560283c0202016144034800f44002022020b94034070903004503a5000c01008010820040c45600400b07880a0303031000e40c0d040c40e540d00c100034030a030001d92055000c0351260802c0e0700d00003c24000d02025040404002c5050b0400e09034400100d46101a140404000040c0800c0740c44008015100450146100321400350404d140c282d020740014491080403510180c103d000c403000110035189150b04217008407140e90b01c1c040c41d03a1501106440c52540000c10006481c02d40d48062000d007000114548000d17a403540760000041070b040ca81d038880320791a100023080c041300d10543c00c40d040c0c114000f442d00c00030200700e07c0000760090445511411a07840c0b41d07802d0207451003020840c0c0c8590a80000c007030080580d90f4044503240c450801c00203000b960804014080c40d80290b024020f507060601d000102d10f43c07281c010034a190312403000e1140101e1240c2070107081 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 431798426 1250 431797176 431797181
    0x10e06040c0f023703110609010614041d0d2102030105220209121e030306100c05120705031e251505070c030e010905010c020f01020703210201 63
    0x901214078050034510b00d5404001c1d21034010003c034100d466507030960b003503981d00d880032181030070901005008610030f50362401401c400c618a410b1a1907010301c1c80011001201881400111030a0025030180003000e1010000101411400d00d40362051416001042c20303c1000504c42c2c0410940f02e4a0305000d800c0415101b4100c5590f000300000d00400040c000b903103548005424181049010b6401c41c8a005c41080c068002c02c9101d41d0444202030841e02d020b00c00160024a0b0542c40e42c0b4a0301c01410034950360740300c0c8400c03590150032041011007441640d200d03841c5042a54080d2050354a40082ca144400c100c0c5d00121040d0b60550004c500e16803c0010710040d14031b074510001281d807805403810b0607140741d01000d2541c03031000c0c401030444005000055826030a9100c03410010499441c00c0131010f003001c00c6183c420781c005014841208002e50007404c106090380c505856056442c9191342c20003007000407448980f4114060070318000300240100f0711921960000300c100d44907000c02110003d08 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 431799676 1250 431798426 431798441
    0x1f030302060711120406080a20070317041106070809030d0e0907110d14070804030b0f01060c08040e090a0f0605072304050402031f08071d150f0a0e010e0604 69
    0x302a04403120b070704000707501e81c0f04032400c0b101103003414100c035a104801500102700801d81c11080000c0b00c0e4840704407501e51401046814807d88610b01c84140101c1106003500044600411000c5155004071040c94400301a1501600c99014a031800f003d11003c24146030145a500e4003190100c109035140381313840006140c2c0000e0a1a151902d0f4000e844041d41d00d140503060078052000642c0c2603020302c50b0b0441128100c5800c03190700d40d80c680d600e141c40942882d04503090400c0b0b88100b8000706085102d4108890103030b41051000c1c1c241800c05040354540c40c0d0203844013546104141610001a4400d0011950680511070000385498441030191840a07220100290340078030308100d5103001d0314481903400380c41060301d00680b80e030780c0e01c20106404241c0383c1a405010b056600d0004800c0400150441603038007000940d0071001e80000c100c00f000c80c040d58801c14000400c400c041403070508848240303541c00c3c0148401002699400c02c1115624281c1206104c81524402c11406040a006014 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 431800926 1250 431799676 431799707
    0x21801020309030c01030b12160602010509070f0303081905101701020f070f0201050903070312030b040903050a0c1104021612091d0a020d06080616020f0706081f0303020607 76
    0x1850b15411100003510f41000c40301c0d10f0b06165075000e180d1019290107007500f048003480c80c01c540807190f0b65903080e4503490061064100540c240710005203001c60200d07003c4216815406401e40c0f06046980c01d807000d01000b00340003100d41c072480d0065107449050240750300a240d81c90b180c1d860070707042c00c1341d4600c1c044141d205078009078010802c1c4da41804030041107a0482e44c001016a01c000200c1c0f0040b140c40c411140b06551521840b0004824029044404002100b40380c0f0100450000b880900068800e4a500900492014000103088078000d1086550b803e00c1040329040c2660b2100c001412600003516105083d001041c0383e0b4104a0019003011802c80c8500b0680e10a9240074038403800d6040c3e83c001120705000c40070103d40000c2c1c0ea601aa482450b41100500c0345507101d8050720307034802040b118801011444400d51038210300100340c21441c401d409010742001410220306650f2090301905c00c0061400d0380c200f03650380b00604031200018500c20f03030140c4514140401c0040c0380c0c101303007200310 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 431802176 1250 431800926 431800933
    0x270501060b1602090c040803070c33050c0f07061d06121603090f140c150904150b030408072108040609020d0c0e01091a03070504240902180102 63
    0x5010b2030722024408940c040d4100e50b49021584d9110491070140901e0340705180c11b01c404280c3d8030820070204443d400340e1341c002e43e003c075003008200401d203551101894200b0302407003584140401144503000501d030b1004500215094026280030316850109558050320000d0100000080c641210046000303500c00d04440003400d1003841608207549890140044000e407030000711099030980250005400700303401c401003406820103070506100075101820707248440d0090722105103481c541100328944a110706480142441944c07000d00004100c2509040c00d080c0203264002202c0107c40d005500c07462003104030300d807101c80518040150700315140d240c1001c482c100704081c100c1c980c1316900c694407540111012030303c6c81d074500104074400d81e810009003074140000b601148602e81d100c02c2604842080d01300b0428078907280b10441c0f01409003e6040d074550007403c0208070603d003e0700a065440480102105030768640180180c0d0f542c45688080c04c0150080303044010a0b81c40a60b02c01c080b1000e0024 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 431803426 1250 431802176 431802187
    0xd02030c1e0a06050114010816090501030b030a060e010c08070c080d0203130f0c030b060402070215070501020f1602010e0f090403030509070f06030e070602011103040f0501270501060b 81
    0x14103450390090035041e121200e419107080900307001003003001d0b07801d900540b04100302d50316044004040740c85500e406020075100c01c042014a500020b00900d800110364950340d43c6030a017401140a480c0304550300394948522003110002c07500508c034a0350b030036500e4000000c0101c1d612034040d0546900404480500072140c0038500030138070140890703003030584102c00140e40396a0000c0e1000e1549040001500018116140ca41004141c2da42034040d00d0080e00c0c0c081d115905c010400c4243e00c10040001c0d04940c0c054841c0d1050030210000d080341c2440ba8001505000d08010b08102582003000c05540c1301d0107a03064401556081035100d41042c005580722030b02091118003151000e200504024109542c81001810440d420b019400103404681404d5882c1e90b51181c0c018050704256000c45224003c0385800105a8014071400d0035001c03440040b941149c0c2c40d600c400000d680341e01010f8400303540701c181820030021150f0801b40e0840054102d907818029034100b03542190a150800d6441500802a = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 431804676 1250 431803426 431803447
    0xd15090c050310031101020a060c1d09160c060b18010f08120414041b0201150905010608040803130203061e090f031912050126012a170703020c0d0203 66
    0xf071030003e8036040000007030304c01c0302e100040385085400b0002070b00141c680f81c46804000d0384049240d482d441c5000204003608640c50800000d15019110041c0a02c189107803e0456070040351041d14440c011980001c45588080100c0c0701d180700913403441d5200c0490780c018080d0f080000800c0014040540c014240281c15500e83d40e030f144543c0c020181c10f00c00303440005215a403150018650011b15980d0072512442c12140a4080d02495036040070701000402d005c01c00c442240f241c241200e08075550000f003922035881d1a501035101800340d40203e100f481d44040981c034104082402000354189110b14059842c016100b036590152124215401848540b50049000400c0da9000345807a0303202e89c0040030042d42070307075038000c43d1001c0c00d4090f00700000082d10587c418018801e004003041050241b50640030428201d4a070301504510740e01c9a8280107402c8009001d12041c070640606010000c50f901c03101e4194441011600c0c2c000294001883d4800e4800c148040c0c0f01c03d188a00040d400c040f141030703 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 431805926 1250 431804676 431804701
    0x1309050304060e27151c0602070c08030f0901030f1401051c0519060c050408060c03040609050a0b0a151a03090c06040b180d0f0b04080d15090c0503 65
    0x49034000700982d200b040301240d5903441d1341302001c1044002229440c0c100300100c01003808111501820070f00720012000c61030500219007503c103000040200c090700004c3c0c0d5118001e40203079038140d034811041d503c049003c0f54200010861040004001500d4010300c000040655080210076010582002d0740c803090007520312104d9064400c100c0700000c1200c4612200800304180000190107840341c2c2c1d03c14480b5101d0360226004e100e000d640140b00075500c2410685407403090b40300b000c00c0d40e844a4005201c5c4540e000185803c64419003020402c614a600d0b0345140118078207040c0d03511014201071000b42c50007840740c50119032400721071401c1c580c0382c01009840c0e5002c54003400040003001000074900d074418090a61403900c0200280d46031a29208146e215800840c41020b840c00888111401890440440e07000303154024142e030f58081966503241da40800280044580030800d102c250044441805040c00c54081d03102d03101c0c801450460400d0681710b1364000b50f402d101c1f080007404080035602 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 431807176 1250 431805926 431805929
    0x20060a050702241c0209030a030c0b0f0906010e090102070f0602120f160507140d0c0302210708090f0a060e3a0c03021306080c01140d0f060e09010603021309050304 72
    0x1c034514850407408131000320281c070904040390351601400020000305a000b00d8298640b0b401071107100742944e84d5a40c0d1042e0300c0000d580d00b40309940280010041002101c44103a842140000094100300c800c1c2d4038594001001d80342158103640200b844010000282a51340d80a2040c3e121014503090565001d10001e41c41100c4104000001031802d040c0090b41d4841c8180940c6481241d000021a18006102410302c0d08103c006000d02a2100b1501c0001240030009507000400d845c6482c0342942d50142660001d02860f4110004100a2415a45000c6064010320094491014103260102004801d22010318402016110a99900740e01902149948107000c2d08800c04018402c0c1803c141050341d01e1030744000c1d44184903081c0c1e61301c55921904500100c90040342118001059040107490910304000c010341c070880300f032001100d400100c3e0822110745400c500300192094a405580254003802c40300004182e445000030030442c03c00f241c205198555143e0200030099584c0d4800781c5a201c0e0f07 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 431808426 1250 431807176 431807197
    0x1005030f07051e060c060a02040e0f04031d040f0c08090706020604080313020d081c0501060e100818120c0d0503100e060604050603090c0a0605130320060a05070224 72
    0x3c80303155402d9a12103808460b81612404111141c52070200040d40280d402402120030541d1174001007891400b402f03e02c140035581c90f40303807010300810414908003601c2403440010b42c000e44503110800130086a12031501c201c6c00030742d2010110701d81005100d00e001d0361a4450011940180100004500441c00f03894200300c5459007011120400d000007180001010405441c13480c001412030380403200082c0c00c01c0c8603001400140b0051781c1c3c880d01900d420b44041800c0d6000070000100c40001d510500c0c549074003002445c0701d004c0c20012006e20f1b6140c504400c071202e44107140015140600d0404100c414068041460700c07d145207054141c4507818032040c41100013080821012510f00d584040035500604005000b40380c036854000315176556509140002c44c0145800e000128460348103c0450301480e10040580c1e01e8640741d9684c000951601c0b01d0511a0301e5103403150040d0030b59580004261070495685c45580703a164600400c07001d4900010b5081118400003882d0b031081900906842c0b14034003 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 431809676 1250 431808426 431808469
    0x90b0705060c1e03100311040501080a0f03031d03040305070e01080703121407210302042715080d032706180b1602011b020303011a0906031005030f0705 67
    0x14110002804003a0043e0340e0b00d81c100100800401e0540740140c03804407400303014000000c00704101070000711002805400200d800c4441f4410101740c121800010343d43c801d141c00620100d9201d854259851814000400b42d01300007410814444104004805001c84100081180d4074010381c0684d950f14502c00205621524240c0340e808c2c0380250000d00c80c0340c9103680c0340c3e0781c0d9a0a03403a083d20944d071108001280c00d0445401c00710502d120b4400c1c1c6090721000d0401d0300c1142040002411031110143d01e98861645400c0c9021a91000c40c440700010907411004003100d070284500541a6040350700b2405202004101c0b1041c44400751070707001c01c2c2e140c000000217000504009140030802c2a080058241030030003007481018101101520b2900c00705034000c021032241114030346c424042c2c0fa42071100690007400144000c0d80245d074260b03490340e00c144115142031a4540401d003190000c6507280f0a00341098010002da0a00340244075035421000d021b4002c05040000080c607804c00440c50804108 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 431810926 1250 431809676 431809687
    0xa33030210031e0203090d090b0a030b0f060a0804030f021b101e0e040b04060321020a1509060b0d0f08030606130e2a0412020d0b040c0303090b0705060c 67
    0x602035840b0b075415907995100306007510081282c01001c1e40c42520386e01007611910083da80c10301d205111210070795406107021880c140c2c001078100c01a02904400c03aa110040740c0100000703582d21001049006801c0e01c03105100d140500700070b40f003030403015150f200b9500711082c12071341602c1050071182111000c50343d40c52b20b040201030031241500d1031079684e109007844042e400046600f140c0980d003044030898045c0603980040080c003058440c45d1000030400c42d403040c1040e0b200e1400254252107480d580c0b0482c0c24400e001d03121001310038900d10b540850b50707988084600030700c00303180100b900000c0150b070703040d450380140c5d40c4203185041c140b000030780680300202c007090241e5034650454400c51501010708000ca91101c203100705680050700c0d114811003c2c00b0080ca0709158516060b24480300442a4030f0801d840d081c807000c030000c0340da801240e0216400d90343c180052841e0103454001c6001711290b8022905600d0301030f0500c105900940c1d032880c0c00340105070000b00002007565009001030201c82d113a4 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 431812176 1250 431810926 431810959
    0x80a060b01142b06050907090302031b0d1e02060301030605101703090103090620031006020109231009060504020906060f1e07020d150b0604050d030320030a330302 72
    0x10041303908010fa11038030203820702a449a00c8028102a64022025a80600442d00d03c003107034880c601c20b030107800401041da201c02064000d009440b00c0d00d001e03c2c00c0c04409225900203122503109800403100300d079803041440290803c0da00700e60302403e245480132420704c03455411240c0c2e0b8002d4035101810103494528035801c03c9201c0e004078419085420045801071000c2080800c08c0d0801c80ea415020340e445240012440c0c0305000e28005617070098031000717061a10410030301134a502c079036050200d44581e001191196000d48503100d000f900440c800509420140f040007810070024018030f1142d90140544000202440203d48140219041038010780340720550748500ca024027036000c0d41c880448071407041401101030450940c0344212401300140d08040b01009400d0056000395a00114844400c2b00028003981c049a071080c100c02c505041805034100c00502a401143d03c80c60464865000b0102c1021000c0201c02580780745070002d4502041c045c000300b18003810301c03029200d040c03800800ca402 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 431813426 1250 431812176 431812181
    0x901060306020c030a12060e0c0c3901020703030e060703030e161d090706081f0303050a03061d0c03130b040b0f06030102120604020d06080a060b01142b 67
    0x40d40d004405640f00e0740695512612504188003000104000303940074807004800c1d10540017918040782d030664650b04c880b04024a035411880a8140038840c2d5801c8240f8024094540b115583e600c010124509007803d24410502142c078640905552103c4c02c2032002a801a4403210310180c02e58010b500c4045509080b40640013050045200340900040380d042c8902c0b402044050791500301e41d000102c1152070186029260072200116070345c00a4805210040c8140d00f50340d0000150b81110801019544d040034001c010360b88101c01141d000201e02200c1760700360203054020300210b4420500402d40c14000078030080c0c0108041030b804d02c004000740380382c41d8043c0003070b034001e407c40d429103200d107003c0c5042c821960003640c1c5c044c11200d5040001d001c40c50140206c8144000d0081140c0158551000f400040e410075030401c03400300e4650001080071041000320000503402034101140e21440c2d40005440e15010200c18150300401304040201210303140000c1c03200401c00540c0314907807000201000c00 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 431814676 1250 431813426 431813429
    0x31317060412090e01090504020a050108040b06311b110c060a091208030901060b070f030f0e060a0e130b0607081e0f0a0e011e050903250305010c090b030a0203090106 73
    0x30050301400806c61071980e50202d8840c600c20b56009981c5522076005540c800401c807801044043d40c0c03800238600341012900700b21201d6000003a5090007600500248007203105a0306244031541e80e400801e4840050480704404502a007481802500c241142c103444000308a00c1a000b03810015499009502c15403104000748046800c0428002003440e0041c41580305039840e99032507080c0780020441e04042012103000070307800820303074a41440555040d1441106040e20800307000a448000c00300e901d60701d0060650b00304940e01d40b0b00c880d046004020300540300d5403504d0070346813422034990740945815003141e5074950010f41c0191180c1d40c3c801c0500d4240a80c904400c000140418082c0d203542e101d1010b0955030181c0e8941001041c8a600112440501c0c19002071102c04a0500e12403039600640c02001b4004010701035441031162001c1c521100d84410808002c08082c071801041400400c0c420103d4610161400c540c00c1458885900903500002c0d1030760301a25070010115085410940c480710 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 431815926 1250 431814676 431814689
    0x20304110a0305030a09080c0a121103010c1101050903070201080414010b0411090f010809070b16050102130e0703020c060f07030209090f06120109020306070305101703131706041209 80
    0x1a100e0b281e2411a071603800113001c0c032020070f140003408140c0200202d11004521005443c03046054074103007a0030900d440c452025071b0312140d05044000075031400c1c010f01c018910386468402030700c0c14400303965003110802404c01c10b0350b0704107101c03210050b03a01c0311541d900550881f00d29040328850b000b40d60300504e81070714500d51080c504841c000112481c000542080c4071300f11900105655080011f403994102100c408006821901d0300784042d0034890068003415400b4408030135083d00c661740b22801c90b13000906d9030b6031440e00641c1c204481030b5109103055209101d40303000d50411340c0000040d0341c0ea404c050300d00c82000d940d00c00000c441038401e606544600000410403021820240680114840b045d0740c1a4040c004045041c1804a01401545940c540c050000e0055558000c0d04500605010341000031b000d441050004100c4a038880741407101603150055543c5400e001100d0308100d50070b50291280101d006110900c10300003056440d071013900070700065000c140c1c4100849004030b086e0001d1 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 431817176 1250 431815926 431815939
    0x1090e0403080103140c180c07140102040e01080d0c02040518060709061d150a09031709041401080a030c212001050c040b0d090f0f020108100501020c0402030411 71
    0x145544420030b03a04890082003840318a003280c0c8901915001c84400054020340032494a081150100540d154403445018003d0308080041d40d4607403408051000c3d540641c0e401240034442c1c0301d0f9000c0d80c00c0c01042010010501c3c1950000042d00c040b05d01d42001e40716559130000540005142c24110f8410002c02c1c0c1912072724a040c0c0e0010300010702501502000444803080754945100b0048144c5200ba0007c0c0410400f15224071030101039444003c108080051640e000400030350302c0003441984042c081005a11703000c058042c070049684007142c14054110142c0104100f81003c10240300150700f502d04601c00e08130342d040c650000070103140448419520112980a525840380c052003200e00301c0312000c109104415506401c0e140c041ea10300520f104100400c000792032101000303015036003841c1070119400414be1a04020314090300c0003961003c0258002c0c3e4210b40c1c4c000922a800507000304001c070411704180000f599107180c00d03402c41c040ea5001010030140030301d603400311100701ca0083c10f2 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 431818426 1250 431817176 431817181
    0x7090b130c0327110114040e060613031401050606270d15140f15060d060503010c0f110d080106030e011508030912031602010c03030e12130b040b0307080601090e 71
    0x114683d083c80444141d8201049400002244d072041041003070402e5004c1c0014146807c00c201c03590403200161060f6408401002010060030ba0100424000c0d806a1210101000e4003d07401e4207480c0c008092500c1440100000ca6015084100c280c021046400c094034800000c0c00100761681541d020280003d80450840014007102d80c009503000c40100039032425a444d0080f0365103a010054506880700c00386650b848400d4140030001e4020517000086c00f00784d81d9030714404642102d5035900e082c00011641800c4c00c1f03145030414060a000c28051005010001c6c883c2c80040501d541030040e030302059225171541c50b10040940000415280400000303a8666550540d59601c0d07212150141c0507a0100d03a400d00d0000c008010369540d0190a6a0074282080396401140e545040e0070088091650301c000d00c42d42c450342001408bc0380c100f03a07440503940f010220070304560103d95511030054070700304010038013240c10b0300c2043d20b41080365801d0000107074840c540181c81200741e079041203005410705001c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 431819676 1250 431818426 431818481
    0x30201050a1d0d150b0105030c0d09080d020a05090f010e0108070516061a031216034a030a050304120c03020306190f06080d08070201020415020f07090b130c03 70
    0x4440202d80c0e4061420417104039080010b6645000c00c45210321908800d0040000c007a0450b04484440c3d80300d011036520b4524250100002c0f038003c8983e03000026804900043c032820211b8140c583c030a801d0030004020030020000900305940140803104004010a0609030b2600c4a403150341c509521050602c8401d4420001940f03603c4e011a07024824411a808048040f81c92400c44400b04091644000c1e0b0040c940c5050301c9030a00c000210031807410362140014421400780074400c1e442903620042d08840d14101504011020710750011384280c005001160004000008850407034210b05903001e600f48450800042c04202c0c0e50005c3d4150081104200e100c041101218640a42c681310801c40d0f03010303d035241011070700030703010300714082c0c0c00340b042c0101c0d0754020104150700190f18400136180a40303820320a46c4c402e01042005000da030068042c88505d01091000c94007800c6c1e030480c01c0111110010014198801441c1d0b6242441d6a861072018164880e13005560b074a208280121808040f810 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 431820926 1250 431819676 431819693
    0x301060b0c0309040b060412030c2d030f0816080916080a03121503060e01150803040f09151a090301020a111507080610030b03060408190207030201050a1d0d 69
    0x10f44035200e60310706840300b6818030381407082d03a0a03194041e40042181640381c0d4291500720410409846586a980006148025210303607040c48144070741985e29941c0300c510f0042c1515040e14940c406000301c8804001c00d04044401d803010181c0c56107011240b50311620551420107045900308002c8076600c803404100300d2400500421030b14401c1c1d80e80b03140316520701341040456513851800074402d9003106003040802d0064000c100030351b014400015540c00600600240701342c1c581d00c001c05a400c04030f4200410a00c0600000c006d0203d01805c1c480410030200d150a172034640e0080c0100d002c00d0840e07129900c114401a140f40f048090000c6580f071003072040c040c0c5200d29400e0840399602c2102031500226101c05034450041d58142c03120f14082e02e038a41081070030b4208610309001c040c0d0303403042c00010703a4041040e24021405802001d507104020418811021b0003104da5600f503601c880310400042c0d91101c12118128103a1415001d40d02c2a46a004055106c141459901c42d074400341100a200d200c0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 431822176 1250 431820926 431820937
    0x3020405030f01060302060d0f0b090106030c03241a0705160906140a0b03060d05010203010b091011100504061b020d0207050d030e04021b060f0402090105090c180301060b0c03 77
    0x1c40803100a500c514000074203071042800020b410502c2445145000700c000e400c040e2150034031031404034650300d0003004281c1d0603000347c2c48a0300103600c1e0a104403a464142c40344502e81078480c4400d0402040c40400b03c0046042e500c41c00104081c030000c6401c0c0c606684003039913481ea41c890309680e0041c54480440354131f185c042c060141e0b0131f854004001600140e030240c140c040d240180c0f90300c500b07a280c00404622074000404640d0003034501941e510000350207100442c041c0104401058807070910318180054066140030010a0104039a000351410000140b1441e0704898414041569030352454000040d15103c8508800020014065801c6907000300d0001c0155046070f00316a419603561040064031542d40c01c001d400700707960709051401d0b03040c1a002050b40c00200e0426800561256643c0b40c5006405c81d6405244083c06062008500d401038070140106811101940d0304d0406207440c02c241c2c4a82102c001048500e400301045944083d00054000d1031101c145e9511000e60403482038480d40714 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 431823426 1250 431822176 431822179
    0x90607050715090806130c0504060b071a0702150a090b1501110303100506130302030d050c010f06030809100c17120105041802010c240c11151315050703020405 70
    0x3141c41c0c03141c0d1080703c155086801810045c211a210441e2001b0f14180c014400c0c0c40c400302980700032403651510b000301c0300100760789480180d4911442c01c2040b4403000c002050641801d203d020f00008a03800030300c0030382c281c040e400b440120391140fa42e0440102562607009001440c5102040303a840b20844100780d003a802a21a4010070742609100c545a102c01c13a0101024403141c1000d00032410848050103d010781042080c80098807500001d2914448840d0300d00000c0c00020f144980700300c02e010300b8180a005840511000c1c0c00d554030b22516003e80d002060060780806c4822100314496810840641c1d044402d07110074004e40b240c816410381c030140c50855041e00340b070700005540c1001e1083d107004e104800030000b003224541c2e004580d00e0090080544130480c40f00d0100544009203c01880100e50b052400907410410380c0e40a0700003203089000b41c0641c0c00822210708040d2040045551041c80c1800c82c0810155919000540810812300c030015140340c941003000e1541c050340100140c900 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 431824676 1250 431823426 431823449
    0x30c070b1017010501031e050f01182105040b0906120a0507030e0a08041e1502030a030c0513050402030912032403070b0d050604090f030305100f0e0414030906070507 73
    0x1100c40b56182030390000e10000385100c0800b440c40700b410851100d6104010b11030400d80300924414608070307003941e8240c0000042042a000640100034070320440b07001c0103100b0b242c01240180f240c8405485400350340f007085e401035000a0300c41003540d1400200c80e5903a182c0c9080c841c0c41d05210256400500080310003001182c40c0460501c1c00740d90000303d112246030322420030b0780340600300b4410070b100500450b10340700c4040000e2004100071a5400107081070700307200c1e402540c90b07805050005042c0c4510414690238020100a840c502c25078140202c42a50819200540c3c1c0361109454145031040070495070364611404814061205501c0c200102d070110000c2d5070224010900c010507071075080074825415002c0d4100302c08050305180c0e820142d400340e030007040020f2412060b2240482e2401c5a81c0850000b642c650401105800407110752001e0145d410b03140d85003030300300030b2001111400900090300f5030b500341d05503105018ac1042104e440e404090a010340300c500500d4402d58035012802401940c20 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 431825926 1250 431824676 431824709
    0xa180b120a0e0a0807020f010203090d140106060801081905031c0b0315271e0a0308010e070e0d060917070c090b06070b06150f0d0b0307030506010b030c070b10 70
    0x41000802e041d0f01d0340c010113160b14001d1a03a0070009500350011070141540000d000143d6180c1c2c40ca188144564052000c0c1007840884540350b48c03c550040c1c1111042c400101d005200c05400090380e1a5100c01c240d0000c04004a542403052450150316008403640c03144c010744080d523540301d4000750007565050301100e02c0300f607032854019500321044070008241700354100000c400da0160310040c8500c031060016110107001090101c00d40c1850090b094009920400c8114209940142e01c1da00400000c1c45801143c2004a8014410180c0070f040c28070414200d4582001c0c80843d601101100e94018040c0c03500d2040110710a403141c00044054521860460340080c1d020b10500500071080f01c0100541d01c0d060180d900e0303102d070210140c400c41e0000c01c0c19034010a81e0041a004125402520507096214880d109086054a040d214000e000e07401c6150208002000050b0307890644000c6040252240d40301504414180104800900281910380074030001c1d01003120404142d4090000541c0c0d02e0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 431827176 1250 431825926 431825951
    0xc0a110a03031b140703230109050309210a11030d090509060405070c140304210819180b041505161707080409050105091006050a180b120a 61
    0x12611018000c41c00301400034030081d00c40310440f840c0074410080012507800f040c84e10f44c13500340250003c580003040150621515444044421100d14000c0004e0102c07105940e240e64030381c01b460244034042c90f007004140541300e084820105210950340103c03003820426040c40350800c643c40301641e00038051070034a10310303003031148031650142e84018040401681380e400078000203243c001c0140c8200401045048000f4801040a0280034080d50080d030b156800c02084c0c00020021400f10b1718903905405c2c010780001c0c0c454050316031100d07808006034000340102d54190740c0c005c090980706455020109000c200203610801410036181c00c2c0840c1142c01d11050070035250f5116090b87c2e02003540651034241e00242c4498140c510810321004054104000c03940c81c11130036003254200740c000d541c1b00d03401400f0a05241c0c1010342d10100e198031007001c007498000c0240480c03140000d143c08101800c00c01145060850800100412003040d00540d1000e810503090710400081d11055220345c246007010012 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 431828426 1250 431827176 431827189
    0x1170603031e0a14120103030c060b030a030c06061203080619030210020f010606050711040902060405040e010e19020108010e0c041d0601140a050d020904060b04030b0118050103030c15110c0a11 85
    0x7a00c80000c0c446d9003035440070785105010020031a09103840390100ca0064130141300e00341c80707140300e40c50342a4090480d2422405850040d0801c0c21180040c20004c0c0210b40d0003003286401c41410b481c8924031038101301c43c010008000c1e42029403c15240204602c50580c00100100280c000500170400607407221400c0f5800d101d00d00380030f0500504070103984050b24060b03101d45c4a452006018900c3d007566040841c1c1580c0440341c0400c5103965551a00602000501055003852600b185404002000d5800601050030600410b030001d40c0c444001030071200300c80d04440280049510b0300140b103100d0f0503490041802215080d0020f00d1309049400b040240b40f081d500c07a100b0310f80b101b60500b200c4803040c6000790090301c03409a0050303d40000085161400d001080910301901c2d01010540c10b19000c030b0706014540080f02e00c4c1c28509001000841ea00c0040004001e600c103032120400d848603281700f0f001e000e40c40c411326014000082c4d001414440010404507e40c85030541c0e0500c1d032a04000c1004 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 431829676 1250 431828426 431828437
    0x30605030a0201051c0e0105011203090e060d0b070905060d0906150f210c0b04080d08010b030406020a0e03100605100203070c14010c06020d02072001170603031e0a14 73
    0x804d4080c02090b00103000011a200e50f204800c1c40060894002210b0740c0c25a80700ba8071007180804040f8404040c10303400b0104d4409060030b003101101c2030070210046141ca80c2d600b1400f626005821020400852060518400410005015a86a1030000001c2d0024030041500700d41d01c501e40054000700c0b213401c0c4201d02c100d8406443c0040d5540c076080711100b0f1500e0849103402140384036081c8500103481048401c0c05401d85071406512517040c80f5000e032401c81c201c9810000c0c40602401000360401c003000b16a070096100c0009a00c64110131001c1c1c41031070038488c17500d5043c051800c1d0007041e9401607108401301c42044800043c0083e40f005c040c4c1e10f070710a80d80090010241c40c0d80600200c8111410616111418900300300383d1046034070b0380c1c0101e800c036070020188140c0020b64042400300c240790704802d525401c1d808801c9500d0010000c0d22a4249082c0714058804d40340c00140349540c00d00c01e907441c000a0081c41003941007084425082c580c0700a0104002c100307401c0882650100c064160303138 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 431830926 1250 431829676 431829679
    0xa0e090a030809010b09010803040915080304150306170d1b050309120a0b090c09010f080a0b060402040b07080301090f051b03101d04051b06090d05070b0304080307030605030a02 78
    0x100903456920210b81c40000108450340135034aa0b22200c2c140c0e1034241d4894003d010201c09035854a0030101101c0581c1c1c040c0c02c1d40419220411000e0068900102c00c0314100e034084900d48101c0d480c0c10700190090922503000b40203015170300040c0e04081002050440c8010f080e0307650348111031a88411800d07035214606000e03001354070600034240542045030429034002d0031202100c00101d583e9030381141801c001c517a030200c2a00b00d941403681504001d10b030140500081c2c4a032460b8507091200c6160780720708c01c100c080c1c80400d00c0008121030340c0b195411a000b0f000b40002199940d112420704030115071082c41100c500514000d0703142c4548807030b8800d1a00039080e055804401207845004009103401c050314242000c851141c0000d56400300100c100360444a15641c00300d186004d050040c103124034484103002180c0d46442400d16550381e0021242d44503811a0340e04584005410550710f4100641c114400000c0000207020a108402000e14442d000315a400d000072902e0381c0606484105c040ba009 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 431832176 1250 431830926 431830933
    0x20706081003260c070f0602030405090403050a0e15041e0312110c0a0608040b10060e10020c030a03170c120c090607020d030908010c051801030c1403070305060a0e09 73
    0x1d000050400d001410a216440c040d181031030240303c005191580403c00c94040c9502005042000080e60000c8070001c1080740081c40c10286485d000c00c0003500001d10040030170800140005000c1d000f07421000d8450409028008050991141c1024503406802480d200d45444aa10005840100d450310151396000107201450050420107451910504111211901800ca403c003815150404000c008008660b251507183c24141801014494007401c148103242c0c41d000188038880d003046e882840b41c1e00503626802042d1210310300b01e085c0034294011540c9406440181d0b410702d503003d250b505a0100e0301d0300d07004064a655142062520600754070b2681025000001102c0c800310300c029011440011300301500c2c000c1194000380201c04844000c601103032102000780302c07907603092281c3d80c9600e9803401c160f464a20102d120007110480044414100340d281c0300010f540d80e225107400e07040519405851a140d01703011402030050070049403458050b044520000424000100e1024001c0700d109001c1c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 431833426 1250 431832176 431832179
    0x90e0106120605070c0807050c040f14150109030501060e07080106020304030b06041e0221090a110d03020a051006030516120b04021903060e0618031912020d0c0207060810 75
    0x11100645002042c0b0814845d1640481010401c400014125148110050f10140759107104000171103a400c0c101b440c0c03051801c02e445402401e0a10819007104005240da0241d149400c0102c0f012001c2c0d403c018015403d0240028020260701d031100d00909581e03c070018240c0c1c8a40d012640e0340a140700c0501741e0605000492014201075202401804640c00c4220000b000b5200d9030702030f81e01c00c491600400031080025a54040380020441e08410b401000d080d2920541d2034500e0400549004184540903c2062504160003000b08020f01a848000e1743c884a0fa0f484448000302090b10054425000b507580c1c02c2140101016024142c0b03802d00d8890801203860340303031010340400080040782c104014040300f030580049044802c1c01540301e0136020800b0603903007804c0c60400740060096004201da000311074034041000700a5904c1356005042e012803403004010201c580020003107114000e203200003200248e100080d0859546007107103800316402286c1d2000c0490303080004a4412180060f007010 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 431834532 1106 431833426 431833433
    0x908180f01110a03050c0c0a1706010b0a0f110c09091e0d09060f020109060c0804021801050310020a05071205040305070f030803130f0f0302030301090e010612 70
    0xc00d02c0249030528451941c3e00b8003e18010244803000c5010b10382c1e0b80b010400300c0c2c4524002841e540060f584d401c4c40081445100e940010036025000020a480802004030b8041107102c0d03440000640c41041c0445800c0c001412807555401008501c2c880366640a0585009520441c0540031a0f1800f000c0c40c58034114070400c02c255508180c0d600e0f02c00342d40010000d800c56038641007a4920101d8610200d00504034843e0081215103000e044206084c2d004146500c5507200341c0b108a6114180344450540c1d031000d1150651651021599034040c00594014090550003400c1003814041a42c0d141825801610301280008502080400902c00d0030409071004148042410880c9421512104910b00c00140000490341405a58104010110420340f0f9490f400c1200035003d1003c900d030094072a4400c2c03041801ca00e08021024a18080611400d01144d6001e5080c1480c51502d56 = true := by decide +kernel

theorem cover : BRFrame.Cov 431654676 431834532 := by
  have h0 := BRFrame.cov_init 431654676
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431654676 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 431654676 ≤ n) (h2 : n < 431834532) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
