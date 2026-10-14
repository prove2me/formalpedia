-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1179
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:37:48.111819+00:00
-- url     : https://prove2.me/submissions/ba3b16d6-ddeb-4045-9d5c-f7ff7031906e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 211870503 ≤ n < 212050359 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 211871753 1250 211870503 211870513
    0xa0308071202010b03010b032509020406080906070e0603160c0b10090509010501030c061214190b03070506031503030403151410030816030519050c0708010612080304020607080a02 79
    0x5440040e003150304da041628082c6c2d040c0b002c0301c04641d902042403910340c01142c0c4007107640100c180b040a48614181c0102804502c001000310b40305821081052041080c041210041d0b91b4a1404a691900040409401ca4002e0004c200d015a4003c005c21842c1c0541c54105c042c04880c0d01d814440d285c0c1a96600c409440b0310702c1c1405810614000c256101c1e00c2e020084c050765245a54560005a0f24072603070b42004080d00f00c60001e0a201c0e00200000007400c82d00011a0034807111061448100c41c030202080d0745404015011030401041050481780000c0a032425a99040550301c041502110040d61601080002000003080e400760611105450308000072030110700c0130050320650b0003510712041030043e01001c00002d0100400c90f00c07004482c42c002e81032070b00c4e58030302030b40d080c046c0440d070941c00c1240c640a1485940e101024000000d032801c1220b01c1c06594448403403c8918030300460689a592401c402c02044c0c84c02c0c0156040352003d840340d8500780310394444403666005070400c0001604a = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 211873003 1250 211871753 211871783
    0x21606030218011b0b04080714070527060405060109080f250e0106030c1101230109060501090b0a020c0d08090406090e0a020d020a050d03050d0e0106060c0f020a030807 74
    0x2d075000003141542c081c03c100c4040780c0302600c08111a603a401c80240143c4500c0002810003c2c0e5000780d0340103c2e8409910030401c286a40b100d40c642c1c40c180200d500800200111201980f01c1801d616100400000f2002c00358172035105000203014000d20041c18040800d00000c0e5900080050074809140d0402500d1140200b140c0315044003400b4040402c00c001580d8140b0204208141050454100c0d040000304140c0d80785040e11002440043e0005035460f0040b000c00e40c15010044880d0a8101400300d0b03060307a01c601d00305044500900407075000a9844000744802c511040040c20b0354405070044a5580b0a100e0004d845549481070844501c03030701007480a03c609240c06144060301d01500d042c0884080013184656034040400c0103881901c203a0050b04c255140c003203052001e00030182c0001100c40351800c02600a0780100d84078020b0754648540b503062404117101c0c140544000e6a6411504005a00c03540c44250400c84d06a030300480b501000400141110020010184141099002118 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 211874253 1250 211873003 211873027
    0x6070c050a0503152a18040507110c010e0612100303090f0302010c0b0a2702091303020c0d170d06050306060a03081e04030204020a032c0601090c0216060302 69
    0xc0650b2080f8007903401004640303469441e03620240e600c0b4001300e003c240352140e041142c0c0e106603100644240d8082d030000d51002e14a4084030301da0b00c8108151424809900c4a46044422004072154048940c1290580f181d40758408e105a000c88800200072a0070160000c0d0700c144102000d60703941003045a41c0c1410000c1580003d80d0100416501c900301c0311051840d000686941254040240000d06000018500c9c481c0c580c00301c0e051840c034210400b5002030f51803417000201550741e02039114004407000107600455114842d08400d9060780608108182c1106010504165000488000204600c0720008421600244c002881c0d0700c2c0c1c1c00b295640c6000c040c541000c1d40074001e00d0160f04080401c2c0301017070394082140c50441101c55941c05041c50440c4402d40b070301503a0070080d44240000368000500d9895006001c80c000320081d25000500319202c610414481c1c03480490b1107030004001080314101690201d9804816070040e501340703c503111404101e40072590000c6010990204100c0f030102c0d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 211875503 1250 211874253 211874269
    0x12180e1305010e0105090a17270409120201060f0e04150504051e07050a23120f0105130b0f01350f01050f0901020405130e19060209130b060703030902010e06070c05 72
    0x8c00154a018a400058a1160f1840b035007d00c40c8031580100e00e201811580750707944004042500902540d14000707111100178040c002c14400d0210061110102042490b25143e02900907540b050380300082c01121150380c406000001d1090b40c850007040316901628050180b81182200810042c0c2501e50600003003181290064100c03c0f20703e51818042068448130b00c54183d40001c00f00c0d1004007554105030300a1600140e0306256015508102c240312012007078910b803102192180b82c0c8210310790f0700d40000b03c6040d00244a05442d0b0030304030749101e9040c840b58540c0a07a20b0390614443e0303000000004524502081400542010380d56002084a599a2240c0454110700e404001b54a024640000591a1031055039140c01d4071b41d843c20380024444d01080411703100882440f0952521010303082040080d000801c40e180504400204031135004920300c5812240100140420706090182d10100d0050202000480c1801000170300d03042c203542d4041c0a00072152040d0b1071041030600700014020301c0c0c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 211876753 1250 211875503 211875533
    0x403020d09122414011d281103042003010c051218070303091502060f0f070306030b1009060512070b13050a0312180e1305010e0105090a 60
    0x20180800901c0b24030020700e015000e858024019120303510060300040070481102c04110300051070900c0c10310030002c00042c01c9048030308401035401d4606001442103c260000ca8000a4030305401c0c0007040c0072840b501200011500007030380001c085102c00c0d03200c80c803a80165001d50f800c42c0c10000307a9035101303005020540341880a800a1201d00004000a401405040b10b10b4201d048030f07030006612103000c010600955001502144c0310141d807030401078403030071171030061400411250084107500e0740000381040c0105003144000007103940b403001c00f21801c7c02c00f4141000300740c1c80750000800304404001080c0602e14445d00b055800b40f80146400880d0302a51080d401804503400f050012480843d61004403000d02c240c0c40e0381d8180030124500c2e440040d80209a0101e80d1500200030b1001400c42c040c080f221503200d810144115200b02d030001070403840b07204032802c1d0100008859070024800916440e01c14000841c035849944030040c01d440084855501d01e90011100406004400e1051140 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 211878003 1250 211876753 211876757
    0x5070812061e030d0e0d06060f030308010609080a030c06020909040c17120a0503040f0c030b0f0105010806030c041104091406030606010c0f02010834030e0d0c060c11150403020d 78
    0x82000b0305010a40769564582c0c0b03c13062102c102440304080d1200c4450f01003c55102800300b00b10783e01c03142000701900c0c0314001500064110300002c50030500584c6114282c070103000003008215540c3d501205d0302010810210794080d028825003860b40c0318002c0c0c0300c4c0a2485010314100003410401091200e03001c0e51103929065104d0320f44513040200385403c032110110541b42c41d590380c3d0b44c3c2c1c1c240404d290781c200f0f00050040f01000c2000003031284941100d801001d04900d80051070745e90308011075600f0b40c1034425035459041110320380380e14903069102c0140d80740949502c2e07041c81e43d1754240004031007004160141d4659050208078943c80c051000350303440701c82400c2040c110403a070746594840b00e146800007414060040085000d20300f05031144410003020f03807031072090303180030b410000c2c00016410220350100e0f041a0055040680101e044e55000f442966905e100210039201d83d800703403c0c0301c90803005100a2080c1ca0b0741d40b1344180480d0201d8040401921500d040c58034000345055071103011401 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 211879253 1250 211878003 211878049
    0x120906061003090b040b1b0f0a020115050136290708030a11070605040515090727090c0b0a09091b0c03030b04060617060d030801150507081206 63
    0x3c0040e1100c0c03005504190824880800d641e81c0034031040c0d0101031049058185070700800c800b4a04180f000007805503c00560007404800004819002a00032034010365001c00d01ea08080143c01c0310340356100c41084490300c0440d01c03104900c4442080040583c000304076425040000701d10403000d07400e540c08070207000039440b0315001039510346103c54000501703a481005d455800055000804a003912140703500a0b000b0007240c146440e020303646036101b04000110399004400102d4000c00840c0c21422100103585092400c1042106000b500504d000100d044581c0c80800c02d004c107041e88951800341650002d0550b46401d0b4140103003c0581c947e1008814a050180c030b406011000035144010000d5800c100c50b400440b45410b40141950b8109070340c1182c5000c40016025500c82003845800c0c5452250f004030751141c07018031606808583c009008100c80100401c40c000301e956007071013003401c946421414008d42d552076503441c1d48126001d01003d80d0010501400d482c0c1000c1c07003c034940544203041 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 211880503 1250 211879253 211879271
    0x3070516060c0f0303060306020f07020310090305180a0314060717011a0d0209040515040605010e03060f1b07050105010e0108190602090a05030f0a060b01080f01031205120906061003 80
    0x42c80b80441c84802001030405201c40b4080500942040000c0c66020710203646403a64404183d03480d0304102c0050b48288104070464000c0c0441e03106802015400d55075082ca840d080c540c040d503c03d0800307802140c03ca90102d000102003903101380210084543c1b4130150030385007840c02d0010108004280510307101117020700100700307045134503d0404003480f130031504640300d10038400590024000c440c56243c119081c0700c104032080c1c0840f0300d01c03490350030f08a40c00c00000381c071100115030f4419000c0d10160994418408900c05071b10190501c0d610152032159110391203000e03c040340039030700007420880e0030360744420041c031511030803415060241010700c00605410101e2042054421a1b808014200650004101d40c0703e442d00b41c3c503000501009412140c1002c852074000398ac0d860000c0e0f081c0d584600d090301d5032480e5840792103800e01450540150600690a41c1c940c85070400c4180d8481043c000100060442d04070010182407050721414054001c44c0741ca00c0500c901180398000071000c161403c0ca240c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 211881753 1250 211880503 211880507
    0x402090c091318120f1e0314090d02071a09060c010905160f0e061e15070c0504050c03061003020c0a0b04030c11061c050a200d1406130921020307051606 67
    0x1c6c0a08003000c1d04050711015946000d40061911032440300100c11800308101c0414070001c0c48400c14101a401c0304c6215503101811508034014030366620304004204080e045514001d13000e010791f61030f00e4000040d9602250741d8180703441d42401e03119030b003041002420007031008884d5200c002022156424000c51802000007880c0c24585107040b90619200c4106859503140c00d440203030f600030015a006c0d43c83c004c0b82045075625800d1b20843c0e21a605110008202c140c0700020b582c041c010107881a508010028001c0d07019411024104100d44210904100851951182c050182d40a903c0e51540c445044c206072000c05025040342e070242d9030030000711040c07028070300c9100c00611400c080082c441d150712803c003000d4040001640b4020941c4043c44590f940d03100300409032082810000c100c40c0700c0a604500c40514102c0304550711944d002c00c078058030440341d0465400c480c402c01040613481c41c030a01c4640a641c800850324010f030b00100d643c1040050800c510021805060000c0390305500e05180 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 211883003 1250 211881753 211881767
    0x2070f05060112111216090f2906030a11040e070f02010c05040515040506070c0519060e01080c1204050303160c02301009120302030402090c091318120f 67
    0x70007030140e0a81d45c059040b04009000854008040e242c412880d50307504d0300c41d00054a210648104011314000b1803910740700711b844001c1810004155980001d4940804010841d08000d100a5455464108600c500800d80c0018000b0b05114902020142040302d0001c205003146011082507a00d000c1c2e03001c0b00c550300041130340c003100e00840c3c11001c80d640c00f90003d4454001d42d4009a00b116001c0303201020400c08058000a4a4040e40d0b40c040142e4241c851248000280c824007011500400f012001540314148181d070107031300a115140360a04060712004054801c0b00c0585144d0004000c2c40040d55141e8903c860804151401322909105a000210702c407040d05910002582104034080710882040b500300f80c95400350064030100110540c55002030896004100d851410350343c008a03d460091003075034001c5401806080322580c810240344211b5000c245410340c450148454452524450701500410700000740400704007041600c0d04548101c00c00e600a02400b002c815000072803540885 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 211884253 1250 211883003 211883033
    0x80106081c210b010c02030109060b12031306030507050712090302040f090b16020c090f07260a0905010204051909050a020a080a050a02040e0702060711010b010c0206070503090402070f05060112 85
    0xb00040c40c2d90729880181c80129103040025019400c0407101d006024003139104486810065a0b191244016840c0090b26032007030580002ca180d100d0030042c8801d5110781d01440d8420680e0514a01d01132542d00c1d5003281c40301d500543c40029001000a00842c10140075074100c0f100e104909000c4507281c0d686280000100a2050102965003040020842c2c401c0118662000010f48503103c0c074108040041c40180e000c132404c0020505042821300425040a54217200040024804106031618440d980103013440c03410a4030300359001c1c44041081d03650b819880084034031465450018626000b00351042d600020a00d0340428814002072001541010100e50320001c1240000782643c2c54225400003401540c04c203552070b0040c58204901c0c0c0340c000a400b801000c3d00d0301c8006084030140c0f1079170b0030394030100c600c00c0c00034046079507003001401c0a60151010511900c156420700e04c01c94045000ca82000300182e48060000c6481c00c188402405030724058030714a1400007858021f03841c0d044c40d07090300f40 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 211885503 1250 211884253 211884317
    0x10f1b0207140a030605010e1506030709052716022104030201080a11070807140d0914032b12020a0507030e120a0602030907140a090203040804080106081c 68
    0x80c881d9580e58868240300d000d1035005e5410000741d41c4612511000e4441198821111840e40140481d07500d000300c1503921590701541c603aa803503400c01d03080c82960410710051070b41c034a08020504c20000200c00509104510a10892202422450009181610f8100610729004d000802103122556800841d4262602800c10507130544071043d090005046d03021a41030700c00782c0800c60b4800c010b01c000043c02200d0003030202d1140d86016000d00c6071600e24907614400802c610340c10401c404c40034200c06140c1c4200040540781040d00340d0701c407420580d903840300e44480420506403a104d0300303401c000000400180c5500071410482920000740161154503400760510541c801142c0c1e10b9035038511a450030025840540c0c20f11692460424041d4000380e4102c0c009014a001c0803400040c1e100041040c0300004204560b490b15001d00b58000358805802511444802c00c408518840700b402420004c3c07980400a05243c01660f42105540c80c007110f022080280a900500014038948441c2d54107001c25 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 211886753 1250 211885503 211885529
    0x2130b060d090302010b100e030a020405060d060509151015080a0f09060f050109020a0905100504050d03050915191808070f0806010503010608030307030527010f1b0207 74
    0x1480010305903000c1e21601d110796600388100c51041650642040259200c1543c11005040b0315840c207a48030311381d00d04030035015404620310328054030382904890707003215002d071143d40001701d585c45d0101520300894040300030758004030402600d010401c029641c054190984444501d003468034160001121039009400c0108160106050030100d82c006081000c0319403040080820519103040a003058402c00c4213074518160000450801d6402180c0c5122800c1d61460ad0603410841081038009003007001c003040000500000c64a03840e820042c1040c0d80c001d45030b083d216042c600c104010200902501154041e042c003a2001003c041c8402c2e208481c0141011026107243c001c055500846640c0400020310403410b001a41c0c00c47c56500105130741891080e11816038076407042c9400e84200744070ba800b06030700420000d0806882984200e4006008081d00000c248050907030020300e8a00320303440c001903595010a03007007541183c42001902c00003071400b111f8400c01e5507006902c4641504c6516211140 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 211888003 1250 211886753 211886771
    0x141302030702071e050618011d01022e050103032309010c02130e0706090303140304030c030c080706050c0901020115080601052709030c0d0c08030610110a0b061008040213 75
    0x4c00c180d400050840034009a0301d8801d4403004030302e0a150454240d02241d460400715200340103007258640c284106070001d090310f03804450425100300450b42c00ca240b4002183c00180084040e01816000314043e41d076440480740d000c2d084428040b83c0202811000004020f0302d40d5598201c0840741c0d2032a01180c444e0007038007061030b182c0301402c81c142e04001c09000e2110301154041e0480c5078101583d010f9511950a0480c04030701e00f1851100f641c001e0301054881c1404000203100b41112000b4921520f501401d100e0155180b4068400603603a050081002040c42c2c1d245590903c01c00918010030002203800528044005441c0c91040c01811300804007c82500c00e030703079890140000e41c40b03c0716a001e00755251000626480b500005444c1216014915481c0f02151040710005c0711148c00402c11460b686a03801080804516400068244502590f1000d00c02000384014840b090003071a140030306140c10402c0200904820f05004c1c1400084414840942c032091440c402d00f0004510026420361 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 211889253 1250 211888003 211888049
    0x80a02010207050f010515040501180209030703050115140f0a090b2403010f06020f0304090f1107060905060a06081f181a06040504050a020907090f14130203070207 72
    0x2c1000400360980c4183c0d020b444200d98150b05c079078420300821202001d42c0d9108420001a64401e200c1c05100d01c0041040081d504410384c01003040c45402403c441d103081e83d07984c6040c2503c0c0c41c0002c051340a0404e8804110031190b5442d001d200c07210803030b0b000b2003400c035001c0002d0300590303e402443d904a6480f8202022070b01c03900340c0960751305126004230070400b80900d043c10300e030b40c024010350600700d06030b001c0040c109000054201d04010344001071810182000d0402000b44224228803040c19110300c140e4550030081c03402080c415000d0803001c500c41d41d05080c52442d10101900001400389800400c0025482c04113009000c0e030507100800829040300c0b8040c1e03000c0c265011759038620707030440390700001041022481000c10844000100031640c1d2802d042000f119012a0003816540010003034000502d0943d0140c0d51120302828442d01240c0c55203186000071358180c000039030318800c1d0b40380d40340540b808600820000000c0c660a62562811031802500c82c0020300c0303409049045c01274003885040c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 211890503 1250 211889253 211889257
    0x7030815040f0905011a0108130b0403140a020a1709030a020105031509071107060801030b0f0405070b0a02010b09060a030f0b10050d0308070f091a1303021503090d0c02030a080a020102 81
    0x20329209428016000c10703081040c000c144415546049201c1800008440d500400c038451040070607070024007511809c1d886100c8004001002202006000c11180c0000f1050388080d00c000b85407039001b003141030b0036860410810204142072009907407040c072620405590015034800c0d100e9080c40c115071681c49204201c0a03080c1242020341d03000342241d0402c05119132001c074800800111604a5804035954041901e60303060038000030b00f00a8848000804aa039030005c140c0c2c12a104404942e06079940d100c101c0616085581d003000103075128881c121051408201642c1c000000700e42d071010710381c030f0341d51891901d03414004003c00e02c802c040d00240d801160041c103a001040060b0030040310840c0e42c500200001700444070840440c0240d0b80326424a482031070008181ea00305031021034002c210484409003608079007543c18510340860404801a00d0321501d036440c501050402a8130307030810b044114141541199400c042285091000b00985d90004842d0302c0c5981040c581541c4200c0703a14103c1c064 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 211891753 1250 211890503 211890521
    0x907090911090c12010b281107030302060901140f011203050d02160c12020906120f030d060602010606050708040608101d04030f0c08040e06190308130b0703081504 72
    0x203182d2400b0001101400700c010025407585950f07484080e0b8844a802081e4000c010f0720550300d00d010700302410700d0340030403100610b01e01c07540c00c143c40c0c120300c014082446c2080c00e801c04c0700141c0000702408000c81d0240505540c0340b02d803206030b040c1c0c2e2410f880d200203d0b2005100301c0c9041c004c074404220900d4001c41c100c2d4500310500d1019962030806205000950b03940031411202405c00000008225010081c400c0c07103143d00400300c07503154031610204141441281308402d0709000300703201308140c9002000109014500044085450f500c1d1050290840e0b800340e1000d0184203081124100213401c0e807080f1400d880b01c50900546030f072180308a5082488141d04007080054412806204010210310401d100e50312036a504140d5004203441115240440c550051000909210a112001490403021350100d0046c10032240ca40d5807905401e81e9480a03802550580c0303001510001e44030480906101501c2e8044101d0325001080d41e0041003800c005000041100000c0303080c2e45556102d8002080b0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 211893003 1250 211891753 211891759
    0x30c0f2707050a1b12180909060504021801060203030109200c0a0b060a05010914060c060f07020609070315020c010e070b04081e1507050903070e07080f0907090911 72
    0x2440c606100050516480f120f04039001c105804164101c0384501c860074059254801100c1d00049007140c001d880840c80d4561602c14a60152070100f40706c0c290780704d0504d12131700842c070200e00d0781868014800030205000c0111454101c4000620405800200303c0b4112000d5520001e10a1800e01161241c0718110780304441c003000015600400100000f60391415a000c0c3d4120030b400d403261002c00c111600d041c810309003c0b07403501c5010000400b05081481c031541010305903d14003900c0cc5445810000111610b20598000e0003d000415030704114940d4003c0c0c41c03100803c803807802c5803500d81c038000401c00303425942900014019445038003900724204031803000342140c40c0c2903200d41d141e0116410501841003a440381c1051101e468030f01c1c4e0300011800d00d01e4070203052461501e00402e650319000412031000e00a040128800320345041003034400806103240440114141444010b1a2001c05011050848074003018015030b1800401d404040340c00780781740019190308500e000c086481c01041542e46c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 211894253 1250 211893003 211893079
    0x6030103030c11090c0301090f0614011b0803040606030507270506121002031509040206160305041e0905010b0304120e0a0e0f0f011a0d050601030603060203040309060e030c0f 77
    0x6035004005e01641c1614404101444005000c595180c05c56119214204201000582024031075000fa0420100288001290340a016240d20740d499103500940b01100e2081d0764407410000d10005100d04001f40c9200080e41541180b912054007207829000f03030015544d995403002c102107a44102034540c044051000396403100c40007100310402500129448842c0c803c40405400e11841d0205109200b95401001d0505191100140326650030050310200c0074080d00300400b0a074034000710398040d01c15010788610302a450500f441e03101a5041a40801c40084052040c031002503012081300140040c28503002d4590035850000541000e4180d00c41c803482c03566003042c03118480e84902000d2085078251038840050342d880703003600c4c040311350325010b104100b106110384501ca400e07031380002e60403100514000c508140c5075101d06c801c80e0701c196000c402090350301a0811016800955280041401320094401316509102141006a242042c64485c0000a0348006200b15001d140c5521104c440d01c200 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 211895503 1250 211894253 211894261
    0x30c03061b18100c060b040e0307060504080936040f1101140d0204030606120b34030212010b04120201140c03040f03050c0a06051210080d050403060f0b06030103030c1109 75
    0x44d000c0104142c00b51005070a01080400d6400c1c0740c05030810007442c900c01180f4080300341e1624001050007510480e60580204913001700d5a0758100b05402e918141c0380c00b0304035800c0300c2c2e400882e4803111005103130000d0003c0c400c20012540c00d201c121a010740181030517221006402c0121141c0791120032030061008082448462556a035014005032413094404102d1140c66150110701082c0b086c1c401040c0400030710001d0034900403070020b4a44081440328443d011614260044c440c900f100c0c0605001035808180107400702541c5030054014186000020718003401d002021961041d02000a4184404028140d401420720000c41f40c6c2c01c4040405d80752602d031980d04002038491b051005550910400c3e09001040c504060a5001c40e041d40d122203103817004500c0c20341a103880080c02c0105011b516040001e920034280b1504101910541e01e0315078a5096180503403c49588600010485142945040c443d407592402c072130542c2c3d054100b903883c00d52103107441c00408401c40d2000c3e410030985d1040c0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 211896753 1250 211895503 211895507
    0x50304060e0a0b0408061303021507050a02060f072a0b090c10030506130c022d0f0a020d0b04020619030911030a050a120903051b030c03061b1810 64
    0x20714041002218040550707680d0320042021800740340103480710703500028081112003080706d950340c0003188240141e0f071448000c40000d0003038141c2101c4000103d0000100810090307410b00000c1d41c0200e030005040107500306510014441c0300041070354242408100904c29034052406d81070000d0b150f000042c01c40b039252000c0c09503102d07007500c0c2c0f09500400c504040076250f607000380140c0344209000b802c0b50058525180303498010f400181c9071107003580221002884811500419041800380304011122680074075000e0a01d84828040c6480d040d0300410000001a901c50540c00304640d003102c02254181c446000041140c410900c0141c813000d901c24134a6815070305074102c888a98000c0103040010010380c400d01d0b8032226a1000189a500200340d00400180d4106503409903c03241d02c0c1060400c2c0e00da0383c0c0e0380d2400c030b00c1c030000800c9203420f0f0182c0d0b41030745400c02c890f0b0304846059003d0300441c02c00500700060300600030003c0d80204c0f0089048501551070340c80801130204000c2c840c041e4602030400c0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 211898003 1250 211896753 211896767
    0x10306111315031413081309050906060f0f01020604060203060301060b040602011407030504210201020910030e060a090c062102071104110a020a080d0e0a03021c09060801090209010c05030406 84
    0x1040c404a8201810002810301c10110584517088180783c55808207682e981c0d0071510740c45521419007082050380041640d05041c4212071040001200410060034490104031910050b02403ca1142c0480904113107030b030361b0114599401c0780e8000e101503120f860300e1000134094502c54000c240c0303030170000c9000603600394150498154192900c400404a0700c610303800b141070369000c0740e020b00061901c8003103588001c00b2803400d51148000d4800142014011400111071040c3c403282c0c0d0f40040e0702c60070015a03842080c00f070b2a412008004040190607000e40d100041d869042c4079403000c0c40051001c8501c200c1c5c5d2080e4000d5003c0c3c1c402e40c11541c84620745840070b40c1403e07182110340034500c0d001202103001c3d0080104c8205440580081c41051296034507150340d98001d21760942e00a445040d91902a9801c010182841340b00b80c000c0d080100030701034a1403168480f094101c0800480e00010410b087d00f01001d1419038001100150b600e444010043e291540d8a440c0108180b100040c0010500c0d88a10 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 211899253 1250 211898003 211898039
    0x20d080703120b0d12030908040f06030e0102070b0610020a050604031110060f1e090e071e05090117030705070b1b010b131d0109050a11010f02060103061113 69
    0x480d00000702d819641901110700350240540c10184207414540810701c120f4425440701d40a14010522143d40d507650200f0350000e80c0082e5a010811b2070038001d480d0980118503d0402c05030085007071488649aa080c07642c80500202d004001e280307220480d0341c0c400d000d20082c186d04001254032a0500703103001015455214880c219500404000c050181400c0c0103c0c02125410154100f025040194000f481c20a24404450103804110002480c05a9004a4003484c0c00000034041b140d1901c0d5101d81c0b0400790500842a0410070b003000d000aa031132032051410740b000b43c0343c5c9654041c00d480c18a8038621401c00054050701c5030140c0000c407102103c0c014501003861007c0031a50074004401503084e03039031003130b01560300c2055a0317040f00401c24107500003444003221011030f9804a03813001a42d400c50309841e80c240e9140d0060008031003841159205444109420701e08201c4e02d000010000752200703410300009044684600d4042c0918522505071510090403054001c40e06640300d04040354101d0100e = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 211900503 1250 211899253 211899257
    0x1206240a0b1c1803020601090f09050f03030402040c0507051207150e0c1203071e03090302062d0c0307030e06040906060c0b0c090a1205120a120609020c1b0a03020d080703 75
    0x1443c0c0d040b0300007010f40740c120003551540080c40c0036403c010f2420068244007004003001e42e5074510000100f00e0401080740304c880303500c024540e80d042c140180300655103000c141605000b000c20846000560000f40e0b44c0301a40e03507102d0103440e0051481c08002140e03040301c20888850500202e80c081c0c610204500e0018541120850b0301e0a00c42c0c40d85d183c0b6030151302400f4043e80213018445110b100580d005055580c0702e451701800d02600e0361300244041e0071000c545503422203074003035050401602c06a240000350b0715105807400e0000070011180e60f841094401400c02c0740c0c040614240303440c0c180a4901800403581c00b8401aa2900402007102e402d507181540d8070110080481c140f2103004d41140c001c039201030800300a1b181444030045038040d0301201118035204a0141400061300c0e007018102040480d41e403005000c8482e0420f0f420340b01c0907003020480303910401ca0002d92280000e0100f669a40030680d16846aa000c0e0018580601950000c1c1d00103c81c44c5245e02000005c00040450720320035 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 211901753 1250 211900503 211900511
    0xb03070e042405030f03070303091110120e120319060e0703090203011506090510020f0115030212010c0503180708031216080105030a15291206240a0b1c 67
    0xc1c0c1c100b6030303200d60070340c00800d254208010920208c1d20030740100b96500d02500d0380301c50010443c00410022001d0900396800100200b040004014090003280a0501080001c1884c0c940300e50340741e0000d110107404002032403101080040881825013041d0000d00c40ca13500410b59140404007d4054241c4007801c034800e518002c448014000e6402489090312042e41c0d41c1001c45052400f4030040180207017405095101d9145071406d840024082c803482c01e042541c1030080207280d44140400380605030606d110380d13414088001c40483d40b007400d80354418406080c9d142e0255041038002e04010464005030110b000002e0b444400743c0155441034000d203007003c0c041807031b460364110855401c2001c1c024203506401c0100710303a0108248105250140c201214001150703400c06442201c900b01502561400c0b003007100d100401e900d007101c40c001d120201c500140c42549424081074001c0724541c004c0c4a12100c00144000c12500c51100c2c0300d001d4501508101d981d840c0d07920507020340c81e421220041805040c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 211903003 1250 211901753 211901759
    0x50a0603110a03020901120513020a090203250512010305070e0912030105040203060609030d0c14011a1311030a0506150408060f07020c06070605010e0c07020a0b03070e0424 76
    0x109124004896400d8141c1500380a00071100310040d43c800c08080d810000d0341c0001c080600803c0c4180b601440102610b8a601c50813881844100e0240740e03c80c0c1811441801000f510360b200703422010320340e20106190a8045800300c0180d84a00812014050f448000350011040150000d656402e0320408074030046280d0720250825500c03880001d180c42e4142003440100302c142002d4000d5500310b0002002d25007812000008030b1b01c1c0100c0803402d8000100010b4106061040646130312000c0800c0c40001e00c0b5078105c1c100c0c0258280c00c640901da0141e003484030250a4040580d121203402c072540e41a280e40e070b0401a5024001d014250340c542e1041121100c205000303844a4211002c440c90a80901000e03900d0843d2000040c03c010700803015409680408541c50396000c008054070b0344903450006040d410b024078031000100007040e8004a441c100070740405070f950105000211241c46d408180d680d070b00c0044c2129145401c0b0400e40d045401e0603017114489803e20b03c0c10020000c018900880195 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 211904253 1250 211903003 211903007
    0x8030c0708060108010c050403081c020a03050703050a0209010207180f06060f020c0d0b071b050303011e0510020604020607050102040504051003022d0d02040207120203130605120708090a0219050a06 87
    0x1046c1d624400100d5020801040090421713006000e65014911041c02100f141d1029074081ea070020f402480000d0380d0b0b03c200503441c1d4061242d980c004280750011030500300c00300f0010f55900d209005401603031013514a2030320360464507040001a822000e40522045542c0c010140c00c00100030a81c10140c0615000c0e01c00e1420b00c0480320442540010720a0102d40717075503000b40c5e81d030020202510b440c01c2c45080e00a000c50300c01c000031802400c1e0711202200303210781d50f01c1c40c1c0d807107800b1500800c1c410b08a80301d2002c880750340003521580040e01101c1456803010f00303181060080c410f503404560050700744020810119018442002124000d07111030109a80c24560260906402c0c100490400b90306072035485941007403d410046035201400052600301da685400340c02d41d030311018030f10043e40001580c014005070194868010441d9040090400c0d05142c10046183c8000708001c003000203140002d860a0030800c045000c258025208900008184030650700d03140030b5008160041501e03050000b4040c0c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 211905503 1250 211904253 211904261
    0x131b031b0b0703080c07020622090605030a051e1e0a1211060c0c01021e1305010f020a0308070318140c0a230102010603140115091a040b0a08030c070806010801 70
    0x203034140c3d254202585e176400a03044c6074005100c1aa0041c0081c484c2034503605060020f40441c00e080c0c0460040d43d4a000341020603160150491800781d0080c0300310174002031000036070703607614031041481c089034440340c0100758540108140c041e132200a50382c9440414402c04030701140c02d00d001e0b940105162500100642d0410b41602c0540c82d940c0c49240003580320720aa8000d0700184e100c9000241c900411840c01141103509081e014155440c0050b8900d003001180c40c0090082100307082600c2c410480e07140c003030f40f600d18006001e030134401464005024544254090b490b004041c0c152480601041d0810307000a026511040c10309110b001c2001c10545448000f032030458011401c4042e80200f405820081040d8540031281590348030000030000411802440e582290417900000c1c3c8103000f0132082c5018605030f88540800792800e94000c3c0c4008900c0303051b41261100792404168651a40301040d41c29003031398040c00c0c040c0008103542c002c5030300100d00d002c1212402c2c42200c82d542d880d01c2d216402c079 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 211906753 1250 211905503 211905517
    0x14060708150406031e0201020715030203060f010e180c070803010605070303060e1003141207031e0302130504090f1220120724021201050103140906131b031b0b 70
    0x1170111208424446000d1000d0a03480e51040c810380309001d560700e115131314103500c50100c1408250040100324860426a069900039071342403810f405500c98503404140541c500441e814081c15400d400988031704012421140d000303a0044e00c3d00c3e6070750b83d41c500040c00303170300014401c90000f4100100082e120b91803010850003004861403007400249142c0c0e82c034040d00e10800025100e8042c2c541d10610101140d0b018000c09030081e02d6940c1e040e07840c15132865005510b0a41c01c1d0606206208e003011102c0b08000c18020b40b6026500040d02c0c0825040055101c4082c02006145800403040c1e092a254052a038113106145041c0907440d8200c00354105848140c0c001c0b48240100c02484a10081074851f481e0342e00c800c220740c0d00c5a01c0d41b80c0c12454003069a212146041c04440110010801c950307041c8614149003200000200550401c144019144d00740600040c072000c803009603200901644242c400380340c40c1e008030964106a030300d00d440c0440302140d001c00407668490210014001100101315030300 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 211908003 1250 211906753 211906763
    0xa0603020f0d05011404080405091e1503100603060e0c0a0305250b130f05060a090b030717040c0303020601060c150c0908010203040c090506040209090109091406070815040603 77
    0x14644450901454079280c280980780c1390348510992075440c13802d0300c0c6a800b50f80110380c442e64803401c000a01019180181030040d03000d10f140c1d081c0d40b603201260101508101004914144440c166000900c0c0c00725414560300c1c01032900f03100108000071948950f00b6020944286ca40d8416801d0030410510654403020b003036600300c0045100c052034004a000108904048400c00e083d440f0b204008d505d0700104a0184007000018003444950001d0600100130502100c0051030a0000311000b403407c0411f00c10300c0e0301010b000c408206107074003035440084040711081d00d98036103190a0910805135030f207910064025000d0b102c00441c806103e13000c41411305400c0324403140380d001c00c075000384000d2400381018800c0214094001c02d81d060f0a00003103004501070070880307080a003842404e90413030344040c080314400c07441000140f0803a02d410000e03d04442c0c41640008102d08603003800c01f540f02a0240294142c020402080305440c1c0001c40301d1301460040600c60b50881211041c00200d680c54000a00 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 211909253 1250 211908003 211908019
    0x6050d150203060d050708010b030c041a01120e03131d040305030c03040203071a0c010b031618060504020a02101a0607020402031906120b0901050f0c070f0f0305120a060302 76
    0x40312440c241c0081d60090400f070080341008145445a41c10221290000340190751030f48504880d501d0304004140e1925000ca070b04000d403448884006080ca04007942075814020107030181c1500407040d5101c118620418000d881d03440c408000034950012050140203485200034031681d04c1c926044242921032036168032013a24503141c1d00410422900001c001302e81c584268000484c1f007030000320199960050a00415450f08001c03001d80e802d480407815001d00a40c440140030001c004030032801001c48030126440318104000c5407004015081d9600110340103800020b003c50b8099001815030280004400304208106583c4c0d402650b51011103811544040284580c0f0003616117580110303000104840d2249141ca031040000040d16001d6010003007401c07000c2194414801894005980003849800030055850082e011f01c0701000c003d001002032200208403141040615561039140c3c6400c6451244450f5292900a029a0041d04101540c00100d0301080c0544464018007007aa40e004107428 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 211910503 1250 211909253 211909283
    0x21507020112050f2806090905010f0515010c03030b060a090f060e0f040509010b0d050d0e0909030a0e0a03150b0406080a03080411010302091c1b06020d0c02120102030709080106050d 80
    0x4640d60410b19001740d150109102500011080351182c000100113113500410185403d041140c211810032849030050f5007000200151b6440c103850841140009080c0050b07101c4a504007140104200a01a84c1089000030000b4030250031016043c11240785140c400740941d22001e088565079140c150154209214146007201440c00d5000b443d48200319100015115100c00300050f4414428081600c45400800d40d103411160320003043c0c9000d0b041620303242a01c0c182281125500e20410100714200305804500283d943d84947e80343c00190f811aa00600841c0c1082880d8001c1581ca15418862032030300200241400010490703c4403a6010b85881c40140c0d940d8481600ca0180110440e04140e0300b080990456503401002e03038245801c4007511044404c0f50b01d080000c0000d0001c5229401c001942c00b0882c0380c0c2d0000f0716181008142c40c114809902d00c0c4007048004a15608080c03283d400802003040781039026151400300c60765400240040c0d5079800074440c09200c001c0c405006081424215 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 211911753 1250 211910503 211910521
    0x50610030c1a0d090c030b0606120105040b03030f072f100f0e06040e060a0902040b0d091113051902040f0e041407120b0610080406050402040603021507020112050f 72
    0xa6082a800000050303c3c00c84089500c000f15102414122540542e588082c0140015880307007030b85c014400d03225640392030110159009030341c905208940c17140d0f4803004010810744091044e6000c1c50036502205071986082d10f44482c0e403002403a00414900c05600313015a81c0c003030000005208410150190703803980344000044032902d40e5141d00d4001e01609041d000035a403100c800910040070074101054844c20403004020a1207900d91248440c180184802d0211124035804c41c0d0440140381e800040040040c03410585084088510690094041c03040390040f03d100c3d0010784c0700c0c900d550130640708950722224013001c038005c0f0300525402103841041840311000203c0015003150051042280c0000c0c001c00c45803405181d5000784c80c0196401c4c2400701000340000200c0e40104040750207030403030b01c1e040500504991000b0801b821068840e004141591201d600000155030040d298400c4401002130003600781d40b150318128000f43c80054040c0e0280c1c0d942c41007034010440441000c181d2385500c104 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 211913003 1250 211911753 211911779
    0x30c090603040c0e09030703021605030705012312070e09101521020a180608070e2701051207050901140a17010b1005090a06030e070b0d09050610030c 66
    0x444a00f01c00050110344031100c090307001d1003940709800860362541c01d407400034109100096080a20107021a0501c120799000c900030042d0351080ca030080030f09241440f000500307d10403441c803151950009802070400c03031140415104007041e4858038104e841c94400d1106035003044540c1a0190020782080c00002c08803820680390b00c00310310703042e5440c030060101344092178468804040e020b41d0000761250030a80118890b040010752840081c601898060090956940102035208101c0300e00102149e0b0361f0345411001c1c0100c0ba100ca90355000003445005004982c0078041c02e4441d0700402d00c40d680c1c0344000101d00c402d507080a010050580d1030078260302141d03a14200940e0380304030000c0011800c080440940c1c40d02c0101200045100340c0100d081c40599500344440314200a000c01100d1683c2d140d41c00f1500480d49180760005680040245a81c1480c0064003c0d0b08007050004040c9403c0320650041c84900340544140d48258a800310361400d986881c0c0300045c41e030342c4082030411141d000048 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 211914253 1250 211913003 211913011
    0x3070c0b06060d1104050108070c0c09020f0f0a09180207050703021509030f0a0201090f03110d1b090f0506042003100e01030308090f010e030708090a0b070b040611030c090603 77
    0x10070181800885075501c0e054408601c00e0f485082400305d4100400c1da404401d89030044070034105648076040720b40301c41580d0205805401e02d03054001034160181c4100100f25071031803002100303007929000201c0d40182114210700c164441560300c0c3c03201000a0340a4400c9500c2070794044010081249076134240038140750441903110710a6030920541c0030907142405012041d1a54101400c000d2030300d44009440c00b2035581204146603003000f41030000130070000180c00b03e0761041703441019140722442c0ca0005181c40150080660f201c80300c0010382201d65400104108001c1d19042c0155510f40c4188801c440601014400c03000d98410581c0c80d49a80074000d5800c060080c4c6c000100345d403107092046007071a0aa00460029059200700131a0301c00c1481018440b07030604001703203e900b04c00031006a40c0d02810001902d564400500c83d516540d9202ca003500501c0045081030310781c4901c3c106551004412142070b030b56a07041040f21400010300e401200d04c03071050801480c1c01d01c0c04a0080c4500e81d08024 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 211915503 1250 211914253 211914259
    0x60c020103200403050d170c0d0513120504050307090c020a080f2a010509010603020a06121d06070906020307080301090b220b0f0103050405030405220903090302100503070c0b06 78
    0xc00040d040503250b07030080014501503001415031081105006000c0740307413000c0c0108022000014091412070540407075403015000000818180c941c1c00710400c0701441a840100024088a01002c06607042009403040364421010303100415510b40381d00042d140201000742c0103812071803882c00005c1058018082d1702800302c100720309081c0300c5d641400d95a214370b00342c0012039403511900b00c140882401010b500110581c02070100c40d265138080340d0300f18000e015040902000000402e441d82103a48050704600302261204a4401509609031f100c1c82c0a0b514900001c1e4108030120380c060001040b5a41154003001c802c5ca16882d010030030000307044119520b51302140316020300003041e81c010b607100c2e00310b01e52a500244901103502046202582c81950701e042c941404100804648c000c4181c80407204250744061200e400c20400709507100007044034010b006c0ca060910812300d0760120a14090364400c0d1450200d064041c04141c41c0c0b400300300c8a010015680c1c0015200007a02d0b0b0b0f4076030b03030084005 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 211916753 1250 211915503 211915541
    0x3d081906240905010510052701111b150a1209060f09350702091f06080a0606090806040f03021f0e12120f04051501090e07080106060c020103 62
    0x181040110604140d40302d1450907840e00014803c6240112002c00040810700700725151440b0070311810540c12508820a041000540000d0007503401782e0301c0010040c4012041d21213130101200c480001c1c080886e080c6005000c0d40208000b01c41d0034004907030500400b6101c0408101c56403081c0300140000340310844001d5124559111403512501400c100c1a206ea24441228004003442e096140504014204446c02c042044900e16418171b08403014643c065810920941d14002c521110f0406c56018044002000c48001120707036000040a00807100c41101f404015a50340c0210307400e8031070b4020f03501c0a401801c0071030001185464000c00c0310b8840d005031260070800c45c0e0000d001d20701132907111103129103902c0200400803040c01141400210011801c0c2007012064a043c0e502800400382140f2050085c0070405000e03040240c0480c4440b08404950150303143c0714200f024025414000c0b4131880380c602e001c1001401030082c5001e41d85540d9030b40c2700c410304a030011800b8204039071107070200b1001 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 211918003 1250 211916753 211916801
    0x15150507080703050c0d1d060d0617030301150f0f0c0201170c0406020c0616200405150909071404270c0303080703020306183d081906 59
    0x207000003500045010b5141c1540b14030040c4009810072082241380c20401265011100c02c41c0c1e11003800c0500720302c09446e800d864401c1060514001e090030342011640c15188101050802e40c00401141030700c0d41c808070000401818a03081c0d400b49414400701d00420002c041440f5201c1c420b6410502d42401490300d1340c1c0ca00402d02a041d50701c0f009030b4882e064075078006000d01c102d60f01080890a150029038400345080705a040480d000d104d00030780108496440050846210b0340c004144203640740041c000c0000703041c07070480c8030a00034510b8607440c01403010000080c6062030109016007100c8800504500e1001080100030007000c1c0e0140b400398031000382c841d13820300c0c1014440b07641149100d1071000301100c0c01d504000d00480300040ca1801014010000c0054540303400f883d21582c815220402c8040707440d81c2c2c0150071440c0c0d200c10110301c100340c11007849011400000c800c41c840c101c0030b011441103a4888801c55281c0c000b50001080798030308114120001901c075808890050307100041800c1e5044 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 211919253 1250 211918003 211918013
    0x9090218010602010516140f091201020408060f060f010909050a02250c0f060509040207110315060901090c0203070b1509070f300b01051c0207140115150507 69
    0x320a8010b100107079503c0080045480d4104181c440340605402c2c400781c0d40400c0000c0d100c840c032030003804200d1a6008111100c0c80c1d15420702c0b8864030b503a200300035034403651188642a5920402c40790950380c19a070700c010656a04041110ba1402081a50389003051410140480d020340f00240001c034a07941d080003040c1540300c211950140d107001000c0da400720986141000700b40026036800a400c60308188204111a47d000b0080b5040e4803803e80c0c025880e24250b04000c1c1c00b814100d00b41a8260080605694401427103038941441104201c5c0e915000ba43c84401d031000302c0d00d10180180c00359004110620208117080741280d405082c0035041d6803001c00b0007005c02d044101c2601c002e0080781c03a10307040c03a000580110b0b108190034411454240700300d12900900407131318141d2548400c80d5940344210301c0e4030792203042101e510b0406400c1292040070380e038004400070346c0400c0b0250740038002038459030a200d82c1070185030f82c20035200354690895030a00d0303101251411280f0000050000070402a80025 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 211920503 1250 211919253 211919299
    0xe150f0613090c0e01080708071e05091207050a050915040c020d02010c0e0901050907030b0405150109090204030b010308030702031c020408011410090209010e0301090f170702060301090902 83
    0x2581c40324014011a01e800032181c1650b8501c0f04000c2441450110680c5503680400425801095480c001102d038903103d500307640f04002203400d0002010506440700940303030400c0c001c01e840c20003504d0110b05911360000c00c81e150b1956004490307111080b0b9008001c140340149003903400505144003d101d40c1c04510004044481c803001c10320140e0400c0c42103160540d020f11590a04203124103011040c01d0040002581101050045a204840c80004038400314400e6002c0f130410a0081c00400c224105011f480c19070718180706420780000c01080000c1081d11490081c0d0f411240c2c04145228a80d0031030740e42e5159900b0050500f02188400d201d0b03d5003121403141c5800740d0000002006036941d050040040c03e4400c0300c00c440c6022540384052296620342d1920840c1110003142006032035040503c0125900161b50481550540c2810000004d102c2400080c1c0c0707640d8400d00e143c00d20400450080f13801d5010342503019600540074001006424a1600800d00c89032004016204011510700072031300034 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 211921753 1250 211920503 211920517
    0x40b04060801020408060414012319090305090307080f030304080906070605010f15020102071104240801051e0403020d1d060c0d0f02121801051603020f0d090e150f06 73
    0x19801b040900003400100401d109100c000c1a00038000b051000044220018001031201c03400318000001524071912803070a001829150f81d0188000c0100b820010400c1d0407005a152090003441c4c1c002406502c0052103100c08681140510b04680e00c80d01d841c1455001075840c5034112604103e514002802881507d0103800b044032901c4019080c105801c2003a4190681c0c2c105680c810030072000400c20503a0310700c0007100704440c007140041341d0803001c2003c050000c0d010182c0000140004c24010019040588141ca0701c010b404072a9100014070010004140c1c0c02502681110344550031140c410003240e0141840100a01e10300031414022640590008458590940080c01a00030303403a4003d10800440289200a0071024001c41c01c0d07a07514424001103494540b583e00038051940d004005031941c1410b0f9002455020341c06040103900d4009201d0030b4036550142070b2076035050702d008081480580d001020044015564039862642c800100207003c0c6d8810036000101c002c6a560000804207 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 211923003 1250 211921753 211921769
    0xc17030c071a1c0218010e060306150d0608011b020705060703050d1e1a0103050c0d020d06080a03020a05071203050426030a0f030513020d030c031b0b06130e0606040b040608010204 79
    0x5907100d000c0310b5a101c001803060b601d04002285000b00c2c03a2355694025242c1101c0122035102030100380015040142c482d01c110351010a040101c0003505036010752141500311160400e001041e10403100072030311015240291944424180f14101c00b29106002a1440c003114202c002011200d0600003006c032170100e20380c800c009849aa4034040d1301a03039020306820b0781c0c003800c00b44258180b003600d05440e400381d106848226940840c035014180c0b00d81d00040c00400c0d40b40192022985c07a410300a49a03445c204096480c0e2191150000d5091402c1c03022905a903095600c0074202801c014108145a1b80c0e01c0c202d00b0015105a450700104805100030f103105001d640b01c032414040e44901c05025500018914001191707c0d580c82d2026846d042c0001005580c140360031403600002d03280030350b0003101c0f4080e41c0000c00054103c0384108022884150b004000461340c10f079614a030344000c0c4e015104035680101940d0803a01c0450090300301904054409840180f01044031900c500b10a070032070300a6400114 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 211924253 1250 211923003 211923007
    0xf050105270c090a150302060d1d0607020a060203060102010b1005031b0705070b07080d020409050f0f1005010e0303092701080a1e0606030503070c17030c071a1c02 72
    0x107810400344441c442603491040203001e48403880000038500110040c43c01d910562205885078540d004026040003450740140007030703207e84070b14043c24004c1c1080c54112904410744005520002c0002502c06d124092550051100828695400f0041d4001074000c505564035a44c8501d903554a04410501001306a610305480e86844280440326048401070002000010081303440880e80204107001900c0360154525580c208a01c0c0a01242c820201013840c803920200f00416420310b0b03504004d0240000b0154841280c40304600d0313038400d410a40c0c03003070000d01e0700c000104031075400340307141508406008090302c0c01c2810390800b0451150442540780d0040801c01382c1c0510b02110340600d036016000c41c1c4010682d80070903a441840310040098030400e030724100e848103810091507400a00c05140c0c00020b4070b40b120101e242103144050341c1d01620314000003582640220510010903262500f03042000ac020365450001035881d5804200411101c0f2081009404414440450385281c11002c80200503 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 211925503 1250 211924253 211924291
    0x1a1c0c08040303150303020c240301031103070b0a1707050d090f021002030403020d03110a1509062a0c020402070c0602060411030102180f0a0e0907050f09061c0f050105 74
    0x241125841c614642d80c90f540a1000e0010903400204000000025141c0300043c4a03011072209d41104140200b440780d8038000000703c10000b80180f407004101043e01191001c0c0d4072010b813820507009a006800026800d619480001c04c4800c551942100380790810302d140284481d040c3c000da851b03030001564045140c00e2a1411400e0020a20102048030b10145003000c0c159800511013440c030110150030804191040410580140b000101865100b0218800c3d8044030b925900a48188502526568540310551050b5841c003c3e180b007200300480507071640005441811b9a00300c03484c8609a81080d2309100340c500150100c103400000d0245130300200003030725080c5400d40050000c403c105c9d00030b9005100c2c44200984070003100c000000112601641002c122011410030307840340c1e001c03140c0709c801c503400d009214002042c1101a14003c0e070b101c0c136109680e94184803e216042d42d800340c000c107002d00c14500342214944c280418a11801c01c4115042071a00c40f2800c5da00260380c6803d900b05903000030 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 211926753 1250 211925503 211925507
    0x30f1d0c03061302012601060c050606010201050705040506130306110405120f0d081924050102010908030a0203040f20211c02100609051806011a1c0c080403 69
    0x4145064400c9008001c00c0c034000c100f245440c03003035031002410b00a00705c0000ea6004041c20303000302c004002e0f000c944002c4d0b94a601c002e100691584090b01c5901610001c104035500c10b0082c5407145075907032900b525142c40d10051005a5004500051440e45481808000107800c0c0c091744407018800d1000303644a03070801e402c0110340d40b03c1c001c0c00000e0b0340c403030b40f41615000c2000c2403040c50031095042211113035803100c0c0e00540354413100e51203841071460a0950546219401d10002240c080380f030032003600c244c4400044e405c803107400f0f50207004a40c0074030005111404940041d9406446032009504d603a081d5911841242080c00b117204042240082000c0181000450205118801c080001e001d100180c6205c0c0c5a803414451409009929000c40d10858020000ba10003110307001c0003005013941d07820035140103100c26144880d515045035a410903180300042c40d1411b0710300302d05000600740c58541051419600103469281c03035503009400c00c01e4110749489042c5541030356850b41a240e24140ca00 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 211928003 1250 211926753 211926763
    0x6101b05100509031c05070903060516020705010905010c060203070e0d0f020906041a0409022206050f01210b2202030f010803270301020c2e0c140901030f1d 69
    0x19090316a8014801d200700c105c20003c0540c2c551042c80c000203402d460b01c0e03804580300b022507017024100d41e0408052015240543c1c01c9405220340a509880d40c040e00c800c0111840302c0c01e84030b06e5000441500c06600412440c0e401150808050f0400d0489011a40c01003900c1d42c841082c00d81e55136480341a100d003542010fa64017584000c0031a000c10038107004150f0104604500c0310414001c41c0d484062204644941c2c0040c00d154140310025a215400990b01c41c1c003138550340c0519405948124410383e182d5004810403460041018041207c504010f41c03000010700d481c20f2120340c404490301e107000308050074429084225808000c0581e032481c009060b0320103013006a04c00e0801f9402000207030340c10f442400f4041880c1c1c076502c503a003280701c561400085c003a010340000d071380d0b550140900340c0003166961021150803080d500e031030f450720221a4829a0807500461074400c04130f404041c0840303040080381c00800540c0414100010394680c5003529808407070401820718140081310310080d2005e842085 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 211929253 1250 211928003 211928011
    0x90108030c0118031d0109180b01110307030c0b0c040b0403060501061e0e300303061002010b010804020607051e0601060e0604031106131a0307200606101b051005 71
    0x41c0030340c1800c920f0765009101c0c082c1700355449204a400164041c450f0701c10700c41c0c100101805079001c8500740300030080c1c100608100d2496404200a841c0d669461807010081e160020b0301910313906104507890303c038050071000c010200018000100004a500e100c1c44000d00055405040005140d41c1400005001003c110000e07504020540e1b8101036040c1d4801d03074010600c0c00a4641c210310503518010002ca20020100c052502405c0d48802010100000099031117009c2c1142c2181485031014826801c88080800300c90000c0e00490015025051440044c01064400d4007290b0500300c118991a24094041502c5003958200b00010010250310a01c816681e07101210080d291510f10f685d400c01c000d02200d100c6001c0d14010441c40514030b038403034244009195514148400cd00c291080c1c2503240e20403144200403d18002c803071600310040110002070342410100134155503e546040008416510103000208850804089281624403081d0b2440c00e106030300030071400003500034817016120010 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 211930503 1250 211929253 211929281
    0xc0a1506050a0b12011a090619140f070201030c170702060103170406020613080909040b07180e0423010632091801060f180b011d01050c010605090108030c01 69
    0x8400008080802e21300141150384030301c08510304881440014140303026202e00f880d8052404610014420035200f07590002c1541507881d010300421354030f8007040f18016540c80f0300f84e084040c0103000041d4000d50240301c4c1c04680d4204102c68010080b04182c10500480d40ca01c0180c109000403c204040d501034000e541c8900c20640d07003004c1c10240000d554800091408040b1802400c00398180b2603030380d00321662450003400c000075903d42410850303640d802c03c4e1004000036070780e95661888100ea2601240c01c3c0d48002035100c407503440d030f61a00301a402520b40031482d000104141003048000910400d030081c44101c1e20b103039550b500c07247c0e0b0007429448180c2c05200b030700d40b030511008ac1da511124403c7d81b107502186100012220300c40c106004004c0754205089002260078085046550f44013907000100402c00c060182010700030046903943c1d070000035000481c41c80d403213881466000e80082d2540440001c000101260303180009880000c00782d10210054000041011032130000b030080c400056000c0c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 211931753 1250 211930503 211930507
    0x302131203080c090d0f02272202060f1b072303010212010e040827041d03090111010b03100203060108091b130b030a0809040614150c0a1506050a0b 65
    0x400701160900c0300600000b8501640d20a24a0865462003801c50f265075a004500500d442d01500c42c8e40b400300e003500c1d0307510000b000c4d41a03621082c00040f840080c040d800392915041c20103200280c1c83c6a0401000300612181d40410126540c20402c05c100c0286590b045074403151070890311460700c10448500d414003a034010080e56400c050400e4401b07044804607124402c02d5075403400d001c60540030754014842981400380030f095006607040d208811080c41120b04000e0600401d2404800c02803038000c03016250002d00c00744a02c1c1d0b000380e0910901c9030501d80081884c0302c03010000fa050a00c0003200a10540c0c1c00b00a01480c0e580c06840343c1c5e0300210200017006014000300c201c5000c4042c410700c152044280d203005045154643c0c2020040e0703100a411a0300011641c944118690810218280980c0c40c250300081c90a410f1074141a504001400d541030100503001d14201a5001d5250540d19100b02c075640b00001d0b0411b100c850030382c190b4442c001402410300040003405919a13010031040c40d02 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 211933003 1250 211931753 211931767
    0x100c031a041103010311121c140c151e0108010f0b100804150902120604173c0301120606050906031518070816050a030f030e010302131203080c 63
    0x10300c8003240c4c10750b500b04041d0f950054940c00000c1c0070404121a20340c00b80145a038451022404507000440200181c980302e482c91100841d021240c02104402c000591018110340b0201c3c088040c299001a685a8400380c0908041c00c6070243e1030082e1303c044040c2c0c5d959640c024111900b0310030841042001c5821288201c40c1203001460b180c0054400340480c40c0b040200707409410386900c00104a03502414a441c40c07400300d10015210b000844c1c0540d400003542c0601d081c1035220700704480484003810301c0d07541100e90031701c0d0101c540341e42205144074558140d1b1000c41c0c500120300195000b80319031000413a0000b03003840c000d01556506d0703100c0d9015003aaa0240251554003092848400039059004545942d0300841c0c442c0c0015203122603d40c40c05500c81c003040c0000041140203180701001c0095590a5a480a01110010912000e0b0410912000020011b4490303d194040854149030140c01c0c000300e007a10605100c1150300c1005880003504c03d031800c160f00804215800000c00908a042041c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 211934253 1250 211933003 211933031
    0x105060a0206010905060f090406050402090a200d1112010612051b030619171603031b05031e2805031f030501020703020124050607080309100c031a04 66
    0x481030080b9500b417501d500c00526280c66101d41c10740340800091802c00c0505203410f002006080585041e8020786003a40010f00102c01d0b070241400c00805580041100e51f43c05007100c045420140c2c1e0798115544603d400c5008101446c0030b4401c0c1c3d41403000d80e10065160000180c0311103a1500d42044e028103100c00c2002000300c01d44d800741c004004a42556980d552000090b0101403554180007514111140204000780e82011002008001d00e04a501d080e83d100d509013a90780144c0f20080c0050710030000d0b02001c1804c0e1a104049900c01c4041b42c1c20000148080c42c05003140383d211810754440441c2d1040301080c0d80c02c0040d0b52000101a4110324010000e0003080f0b44401000d2004000e40c5403401062842c502102034000c41d00600219150300b490319000380a0504a0a1404030700c07101004440c8006420050004a41703000f00752a143c04d605541e10012900000c1442409010740d80f501402d074a080d000d004420300e0301e0b0740c0c002400303206034403041800c01d40b806040303000d40d1500440d114485 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 211935503 1250 211934253 211934263
    0x509060c070303020d050f0106090e040c030f02060712171e1501020a0507090e01200a2006041401050703022502030c061b1e0c0d02031002070302070e0105060a02 71
    0x242000c107961101507040c01d6000c0c0c03140349010521107143c80c04101001c5442d60880b81601e030507540f404055580d030395683c0c07220710782170300d000d8541459104100001031803505182e80807440030b01040e0610406803a02c405186a0314129030105000c10080c2003407400c41501030798007811501c292045409a8044103c0341c0c14001e003980480c1c0540d0031a8440c0e1f0b03008014a00320180d01100700c40000e0740b561a250062320f10002202c4440d0300700700c0d1801e00c20505a429010440312020428240303000800304950364002030b08c001403201102000e807981103109200143c4618007940c0495052044010383c03a0864600a0407003040601c1406809405d984e0796410600015500004a00c00e06540c0006800d12110074070f040e41c000e80004071010381c03040d10b81c3d0486001154501740c1c0c0084130340645444030041c3c02c608100d2580c100a90f400e2a80c07130552566005280081c04442501384c4a81c0a071003240c2c000075041d000b603880a0010011400c008440c2805048156165800c1040c0500069515 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 211936753 1250 211935503 211935511
    0x30f1b080a03080a0e010f0603020f010302040510032304060507080129070c1214010b0105040509061009081f150305060f0901020c010603030f0201140903190c080c0c13050906 77
    0x60f050001c03c10360349075a08405c4540445a00801c00207141c000e10100403d030310310040340144c0103e015a0015030007072094400729880903017044081512130310114001d0000108201c140e1801c41c0c0340006094115252030311684c4a10000281c3c8d090108010740340b81416031054050f10310380b0660301e884441c240010301c10241e0f14465280c8482640c9841c400602c0c03070b900001651107460309980140f2070346640c014038014180000b0442c0c41c0002004441c28495401016000074154001c1021410071500d0030309040000d24140d0161600e070444281800d201c403010003d04003040306d00d0306401155128042c60f00107980541882203103144e440719150f80c001401090910712074000585c0301c0c1001e40444600403120b800030003016442e4500a0031550303221211800540c0303441c500e4150740c044090a10700a1600d040103606142d40d80c0c200e8035101e0007000100003008840005170001505d00c00c041c05000040e4000740c030390b8004206c14411501039000070100000d0520081c441e2442000c1007440d00 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 211938003 1250 211936753 211936757
    0x70305090106051f02030912070e0709080c060901111204090b1c020d03020a080406031406190b03070c06060b09040c050a05070b130b1e06040905150619030f1b080a03 73
    0x4c280c82c10142c0c110700440740640d80000b070207001a0120600481d002040e11085030021007140c0f140601101c1c100041c0c010b032400c50740a122101c2082c5130005c0a0034540c00149030070b00a60703000c0c5224600385140751074107866409001c6030a000a02ea0780c00390fa0780d01101520031040310300184001c1005c03480202c901a00a254410050302814800d211102081e6007050404d40d0b500c1d40c0d000e0040060030002a02011442c1040105145141601c01f5100c141e000c8200081d1030b90500c041001a43d101404540a10501210038800510710780900001441804e05d095118180b080a00c010f6446e601049001c2020030407902c0d60107504031040d1401140c012041500a035241e000c1c05629003c2c403107010f0000400700c4100a00010b29540c607141403a46800e100000c0d4071074070140019102c00000040c0b481d040842c903529010f13201e40c50b03035030710900042000d0b2a4540c00480e404408500d80c04c10784006845020340020303c044c0030145c42c0140400c2c81135400c654500070b03110351070751026500103007 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 211939253 1250 211938003 211938049
    0xf040b0a0e043c02040b03090c1905010509040f06051507051213090b03030403150c02070b03011214010f0912020705010e06040b03150604080114090a1109040501020708030a020307030509010605 85
    0xf4003403001e42c1918042c0640c4000695030b42400200d243c1d0310302560408510800040c10201d80c02842c40401204072001a110036040007146c4040201519a540d50880180d58920000403075558440b071070100000f0790101c013030b90740000d810800d0601c140324800c816195010014105a040b845c036480307080715141c100002c1c074445207000183c1540b050f5440074100e03180ca4801e0b5084030509502002c03808580da000c85180d1a07039221022200c3c00300344102070003544220b28440100302c60f100c000822a200400003d0b0b104041004001140d40c0182c081d1901000c4862000f5080e40401c2880054003090030046a50800000040c1051180c1e010f203c4804401002044004a200e0812000d448004003801e80391038460405034000d126013010246d07082038403808140c82190102d02d440070590094201000503444000344054854081d000301c41540d402c0080b0808264048055402170854840140c1e0301e050480300182900c0028000014036458900100416540c940c81d0288080644103120 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 211940503 1250 211939253 211939361
    0x31a0a0302130f0911091005091303090815010806010e010308180d021201020c1207020906091801050c0a030609020a020616051b10141501050f040b0a0e04 68
    0x2d000d01120301405844604003101c030000c02541d400b002524007020b8800242543e40c000d2244012051440b0380c9801480e0003002c10030200e0754504102d04140642400c49219070b6074800d05250464001c0700b030314000595401444211420f2010600414000c1c0b42544036504585406d001841075181c20301b4030415203481601d90313484041e00c0800154000b4003c01c070040c09917412501039031040b04282c440b401480c5100465030300c0322040da01c2c0b03142c0141a40c200c0303a880030184104c8190203042103003025040003d803c0b0008007405090b200e514004152501d8000304000038043c0c2d042600504465030061102004c0130350300240341540259480020030002601c09000d44e5140305124404055100d0454404000e88000500f110b071096040781c20070810300703d400c42c1d0810071405d807501c0340b84441e840d103084825032103400900180d5852000b408e1410355509086000f9500500c0c018020a0240b010340130649094032030f0120308a0380b185010180e561005801164641020411242c1c2c440c0200c24 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 211941753 1250 211940503 211940539
    0x606023405100f022a06030402040209060708040503150f0f0c0c0a080408100b06070b0603120c0a0b1b0f03101505071b06090612240303031a0a0302 65
    0xd000107100140c000008010381003070040060001d10030000252041c84100a054138855000007811031500b0311070b40c4414500000c200b0a60310242c0140d900507000d0040121603a40e400060000d10b00c0340d00e44c0356842d442c000030b00d070404144400b850411248203040280350a0441c040700e81c049a4500c0001056641d94600e8009016180321010203100f920000010011400020400d40781a0030448801ca406210714a00b600d82c0841003c0d00b180090106000090407012480e4020a000341a00d03143c0c0c140803036000702038012002e19107180d80a42031440502c804000340d01d812040c3c50001c2c0c2d0011106464007101880340310b28400d0a044000005981c40b521101114050300c0e9800c03c000080d180403400034001c0e04021429150401d42c584842c0315112005c1300042101c482d40c840082162070305400761445015284200752464840d4440906080841168805c0111091801c402181142401021248141210380505003c00220b4150382e48020854085a83c101d0300d00101071801300038 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 211943003 1250 211941753 211941853
    0x105070c031e03080901020702100503100302040f022110060f180e01170115120809040f0e010c0302090a0e060316080304030312050708180a020303030f0a060602 71
    0x60010580c4112418a24035804004000c2c035010766074602c010745405d01054200d20480340c00a600001d0340c0c0200300e40c80d0040d0041c50303018030080960002165250086000d882c19071404480035a0f0010303000140801000070b030407164401c2100f202d182d01e4aa4000040c401c81c0e030041c0000d12a60025800c81c0c00c0c03051400c40103c1001c032429032501a60350324801b500c0b007820300500003c001c2504608a09a80500c100351029440b1050440c40c280340006500e1060300c02941500c8038001080382550139122401480c010f080703980d0b400542c050502c0111390031501d80c1c5640808040c010405488a540c0710300d45c5005490003510203032a151243d42c0000d2070000700d075034200703d0361141100001c2d80e12008400b6104403802504c0380700d580840848207100300d800854620000c01c941c0008940d0710015002c0105410b10074030112081105180c001031303e07580013100d001c0110a81a404c028622105000344802003506000510040e080c0240740350034509000b0f0b955015844d25841c0720032074404290 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 211944253 1250 211943003 211943009
    0x306230f04112a0c0d050a06052e0e1005030715020a02031501080c04062103020f031210080d090b13050909030a0f020c030718090605130c060801030803060105070c 72
    0x1502601d040504a28200207010f00d0030011031900031040781541c3d505003180043c80d5a42d016014010812035035445034020800500658401310300a0000b0152000e81070307100c0714081c3c1c4400060324651074180c05c8014010b008103040155101e0344820402c58400040320800d449840010032112414408106c1c90142c00c0c140c060741c13511440300241940240c0880c4241602d030340c041034421520f030540900054540300e01c0380000544484000e146075030090380f001165a4800c0c815101d9050741c102039a0300e19002200c803200e1462014080c05803512551484100030304815020b4954805040c0c4040c004071501e10501980c2c0c88000340300028411155030800c0078020050070b00ca02d81c03c000c05003998076044a1808030214021540e04100c003400098004648400100241051401c01b02d59010021090002c01d410759210445400061030350b0055610801c040703245100501e100e4140b0007112000ca600410034801a40014404291210704030b0b94024428242a0365840a9190480e0344050a074 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 211945503 1250 211944253 211944277
    0x109060c030b0618040b0916020f0303040b04030e01020705030106090204080c0d0206071502090402030720070324140708041a010f050d1e0b150117040201030c1e0306230f0411 77
    0x40200023804a000500c20352100555085600721711240407000e80e00c0c8010f0b01d000c0d1501c40e81e0000140081e02c140b00100c43c00d0710610690320003030359540c0480e083d243e00d038006801403600460203001c002010413004040d1101142e002c01c2d07010840d00072030f603103100b8407101a00514960034402d0710a0b480c0d40403141c01050150007155203142c0020002c0050340c014207040d2035140060581c0d440c08030001001000d5942048110b900816072122660321001c11720307440c1c00f007281c07109100016001c602d40414800c08903515100d1451815213032003084003400e0401d4203041c42c101c1c001030214044507244c1c8029181d090760254494070303950801408000a50703440000038607941c032000b010840014201405600c00401c0380714207007000030056402c00d10020894140464503000100903621130342000f00700d910141404c01000f1499110681e103075000c81c4004c00481d03162b010400c20001c0f0708800d54950851422018082c03894000080c4a01d4550b12041d8070590b105c078907503000604034808842c00c100f488 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 211946753 1250 211945503 211945519
    0x6150303121f1502060402040c030213090e010b0d110306010e090309060d0609020d060509090307032c0306070513060509060702010c05120d15050301020301030803220c06020109060c030b0618040b 86
    0x650402980d030301c5e08440481c0200e00300f02c3d090740b0683c0a8029162000d03080c05103805040d06101e00c00c0001c0c912142003040710364032604c81c504140c96540440c4081da00550402440d401e05030241480c207078040e40481400300921003040760a18020041c0c40100b0310442c0c81c1c9941f0440d486403c409802d03d5001021003030320004a0031800c21880e80440215017090b516499169500d52000d501c0e8020f4880140218601c0c122400c80c5018003402c8038200c02c2403400382c0c800140902c1c040303464900121001c2c000f003240081d00703610040d01520300c1001009a450401e1416444401003131050290304402414400d148a450f4200b010034402000543c03036800c0101e4803050f03501c1440010b0070443c806200030440301d0170f001c43e1904040c001c0f2070603642c120325828030b1501c2310644901c1c0481c1880307009210441d0380f102e0380001980480d8a8000b0685603001007110652424150201d03068a2808410f1500c0c100a90100e0f842e09000d950f410029800c403401030303d101801203005000100811a401451 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 211948003 1250 211946753 211946789
    0x50601050d1103330f0d0605070807031b17060a0305030a0c14060105030d12020d0c0804021e010f050a110111040f08030406050412022106150303121f 66
    0xb814010f90b200303202e00d0800341043d0100c0c03000d148080d502608501c511210810003607000d0b0500864085a109010f0856241e200d007644554044030007e56000d00040c103650b0500c649107030f050107030320303007003203024065456003005410003503d551048034050b00c0e210780c1c1c0d40004d00b559841000c1c0d9070040d84c2102c1500d546203840840103119100014085400101c1e815000440003000140b41d41a02c20141c0100707003041c03440d1016200c000c14078500380903079a003c0041e4052440c5078003400381e901081d9280d42c91642810710403c00e860245602c00410b210003c251301074141e074021003183c0c20f003074541002ea50783c1c4000d0004450039040c807400e400d12503080c400c0041034881e510700140700700c2340c20000306042c2c541c50b007000075103a100310702c1580d00052043c041440101000b041c50114540300608465401c2d08840d100711014800040e10903150b040303402080000c41c01c6001c2c0034140340c001c03400340d413030412004161102c85801402c003500c1c074810018804c02c58a501e25844018140b246598115099 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 211949253 1250 211948003 211948031
    0x1020a060507110f1204090b030703120e09060d020a09022218060605030727080610080c1c080a030b0603040606060306090b0f0405040206040909080903010b0d080d050601050d 77
    0x40d080f810302c10303a4030601030801030100c804070324034044656014003146001d00c1c1122810140141d01c80319503141c06034900000005840b001d00d036510000584a804100360b11a04106a0100003440c0c18060b501100600006030b442039104c9050300d00c070010050f11590500c1821950700da0b0180c00c001404190799004c0748160b501e1b45084910a0310032014842c0a8403448215614007041e900840410544e8100815004030600008000c1280c00d465000340d07560307846101d143c401c05540e94542c8805005080c000341c3c005004c0c0407000a01602c46080c400315100c00b003010b501d080740c000303040050049010300f0410301c250040f00401000918690b280d042c2410040d000703180c00e124610120746030420000712001140914000100c004082d82066616042800060035000703008a0b40480c0810010640586521a1014040c01641100e807076008000515086446c408032061003134800030381e42c100141980c4e0444440141c01e000c081380540710880161000d000f044207039800c072404d11800c1ca040342 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 211950503 1250 211949253 211949267
    0x30212070c240509160602191505011401020106050102010605010e04230403021b0306070c081b0613030908070f05190308160308070e0306070e0f04020d0c02160f050f01020a060507 79
    0x450b013100303442e80c042610442d20300700c1d0664410400580c000103658144100c600c01d0340e00c81c00c4e00409000e5000000d01120600301c41c400d030400044105c0c00b03031081000c0d50342489000042e24083c0000c0118a0800001a00b04c2c2c9a864417144134a49611552220611104425401c901e14860070b04030303820030f4513000e03446816000d102d0b600da218051175440145000107640d8003401071038880040b81c80701d689900503998000c080d028406d410013851030541ea81e0400c0007a00c58800015590350800062800800035234107940072644130340c0071810030300c007030040060b401c0110752041b161a91061160400340080760301d940d0000d485c0c03940100320f01103c0c5840348415024540700c1d0303a03605019035030440d06503080030030300c0031803501944600300242106014000603000c0300030080400b100c44560740002800d0b40c2c00b100383c60b46004c1e02d50f684803038483d4040020451140c000c180845040d0f0800b0a2400c3d400c80d00c1c4030302d40c41241d01910711603159009000d5800c0158206070300b44400c0c034007040054241 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 211951753 1250 211950503 211950511
    0x250e0d0b0414010504150b0d02150318030c03031f0b030109060e0705070b19060812040611071202010e040902061612050906040509060109051011010c030212070c2405 73
    0x1951404140d036000b0418440c50303205960102d9200e1400440001ca44001c00c0545880d035044503400c0726030f0380980e0700e04030b0311045401f17219121980c3e0319210080000c032100102c1c412120f81e0040c446018001d001000307803548045901005450040c403803c0500020004d0781c0921a001d20000c0042924a070743e030420b0084d25140ba6807000d6545403205c048039070740f00b181d00107030000c44c420010900c607041e031261400800c0842c09000c46c3c20350303c51b00741506003501101100748d1301c1d50016003009156005004a08842d050350050004c0a103000a200641040e807840241000700391100c6004541e2940c1c030140c41d154010b07045c20307100e1034418442c0e2502d884008007910607003039641203801c3d800d01c502c1c201e600107140070301040d0909150030140910b59802500d154140411032101091036241e9000e040cc8d1841030ba6a48007000c8132404840d801c444000c580c001c209801003084840d41000d00703110607006112403500d60840805814030200306c500d6214149084042c000c0c5040200703c840d0000741c01 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 211953003 1250 211951753 211951763
    0x7182309070e070f020d0908060601080c09030123100501050304152a030621060f0b04021611060a0906120e1204080c0a03050601050603130c150e0306250e0d0b04 71
    0x1c6d0290020003a80c0310402480f50703462a80c031550006202d94425201d10380c0288404640d030381801140700c00242580e01c0b8a080c1c040c408180d007582c45800e82d08000700d42e04428400c416501041c10480020704522005001525001000e4a1013492052980c003000350100081401e000603413250401c92100352011100c1c00000741407030004224000e41d00070386400384e2041c51813107604410903030f0f542000c0e2814082c006511035891220218985031030001748491101d0f191b0008003c82c040c50040d40d683e100c031680714001c0c40280a00704000d60029040780c1503c105040130104203150b4207c0383c000e080c600004428074003030b110b080b07039040c1c1c60f0070701500c1590081415100000c4c1014244220f0100ba0720029210703a0142e8010400c5045c05c0d001150481f11004501000704042d446200a01d50294400c40f560b03480d00c410000c0c0c950f80007007018140f9500702d000c0c0a850400703015842983c02c034214810300c108230000411580034010214500035940103002170303080d0100c034244808901f10031141510 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 211954253 1250 211953003 211953013
    0x311010c0e100f0201110d1d03070503030a052701061703070206090613350d080a1112040501020a09080d090b090109051207182309070e070f02 63
    0x15040c010142140c15140c00340210608080b0140219500c2043c02240800e5560f5054002c19244800f0b004000f001813100002c10407000f142d0141c3e0703080ca01c03000710f560190424082500000c80100459800800c040d401180a4840500d4206023400c1040b80343e801d04d004a8040e40031a0041d0800400c681c01e00b444030108240f11f4440a8480c0304065000307502c6001081844041d207001c401a010350020546088032040d1100341c1e0702e00050485415008400c8100c0c803010300740c04d101d90390704d09107541b0030064103641e501160060300d0f502c006051003d0081c1c8a000004904500c68141c4142c1d103844401d0030340f0340c200750801074000d5000d20301143c000780b000480800c2d039620004d00d414226829543e045800b030300d486603002280d003100e20074078100804204002039607a02c0c5000e0012400f800da01400c0102d281c0380c00c0d50441010301102c440741505003000040490540304151501c08400e184071341b0709550700233f0403070705061180d0481104102d00005100c5015401071070140e40400c25000c0320 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 211955503 1250 211954253 211954271
    0x30902010e03010908070f0302010623030709090f02210d080a110403020a060305130807080c012a1407050a0b0f1f1502010605040501090207021503060d0201080c0c0a031101 76
    0x1d826140c0e55140a031080c0750801040c0001207001c007100d092540244000032f4056282c031711200004100b60342c002d5803820306151035400740c50700340015401480e00d00700c1004200025a5800d00d44210841c02a2103008103542e0b07924200040100282912141d900351965410030a03000303404610240e8241100501d06041c4070992211401210140c0750000e00035140c9030318040c01140500b0006002011658860201e18001034140340a411030501c5114120b4440c0b14814481d42120440f09400800c041443d001c2150002c06c24240c522008052a200b020032030500c0e01142e0750310417240000c240348241803101b01400814107126000c1d44d40741801314030b161200c9800300348800e001c1d541402040d1100d01c0400481e8400b540005420142d07000204029503241c1c0000c0c11900241d00510074203400081500440c90031703092010000e01220512030550800302d010814030344841030024140f01c00314003c04c45c00b010708000e40c0c41070400081111900c2e0304034503004020101c001c058800f15070800f00c40c2 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 211956753 1250 211955503 211955509
    0x1b030b01050d11130e0a08030a0c080114040b010e09090d0206010902090109090504031817010606050c03120403050705120d05060402031b090a0e130201020d020303090709110c0d030902010e 83
    0x24952581c2003e48401d20228907010080f111281e0f003243d080c0d4550311480d944240009004140300f09000f41c1c0990380300e1604035095000e031910849104200281b40006001d0b0002c8001d88400301f00d000c0c2c0b00012009848001a034240c7e6045c015284d100d9144807c00085100000c2c614110300c0142d0709403082a40d0301c03501001a805003205040c00300740744171802d03c02d00c8072030b9000560003800303840c1109249980c80000214021070303400c82000c1c1d101100a81b4000002401540010521454840e00d007160f000403541e01c074003801c0407040740240041d000c98141842003043c2e485c084e400505807a029400b070381c1d2008003680120040c04c00d42d424200010b0b10340c5894821780c7d00c59080681c10883d0401c100507241c60075840542205d0b030000010a000c03450003600b401041c4204082101d0200009143c0006464450143c01b9001107510420400c0504c2101040d010212901004081003805811289101500035043e40440e00e209a0080584855041e086424050b00030380342c072480001c1c50014 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 211958003 1250 211956753 211956769
    0x203040f11090106140a09170114100b030c0d110a0503070e0409020303030f040201031503050c0f06250c0b0c061504020307140306040e0105041203050708060a0519031b030b0105 78
    0x45001080f00320030240306201d21035001b4841c1e04410703c0c2400300140c65000e001c245c446c41c1c107900a001ea65884034004007800c9205a03d0b0020000140900981d1070301301140c42d9844002c00c03900707401742c010400700502c0046420203c12082d58030130f540d84606030580700038520b4004603010000207801a070110140e080c00e00c200100341c0d40281c090352540e0360b4041444400c110241c4102e04045d03803649102c03400000c52030004050b6210300043c2403c1803040d02080462180c20400c584554010400c035103941310014160300303212044030f41080400026081803429902e8581c0f20010352180014190845840030803c03504c99149c1c401d0b0f003107480c0e0803403060008a000c101e60040203d212040070001c249036250141da03010100500201d40c14189261a60070740c1d00590f0212480203e02468128094141c0103950f40803040d45007201da2894000b0018022034600d101b254041c1d208204041d0410710b0300c1483e440599042441c8181c581e03d4007490003080c00e00d911050b100700b84800004903440c600164 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 211959253 1250 211958003 211958009
    0x30618010c1b03230301090905010608030315010f0c0507090b01030507020f03031512010603030c0512120417071a01140301060e0a0509071a1c050402010906080702100203040f110901 80
    0x101040080c41070b0390b040e18150405104200c2007134100d01a00320740c07100c0b400194041c10441c0c5002c903260510345005400e540d00c0c0d8001d0070880d0014410030909481c500507a040c02031003483d014400c8a610031041d200b02d82c0c01d40c0040c00e6409181c00114902c5281d4005807100e0b800dea808000c01c0d921107400300e8448011101c5070700aa0810004105032441c07224403146a020010030300d108190308400d000d403c4030100e600c203c01113006000ca840a00c0002d0202d4504240032402192501138008091802d984001348001d044011b900d9410804050b41400d40d551150f0048030b5028214188001c074803020401d1051b0500c221003042d010784281410b0292408540200c944108140c403003011501c0078002c010319410142c8200a030009880342d500b01d129404081e036024203651403514101e103000901f011009407403680c0c01e00040c04010b0340c0c0180b4003411224286461541500ca00380c0407410800007003488521680080284000c0c00f20000b00b030340c191841101c5003000c0c24016810702505100c244 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 211960503 1250 211959253 211959287
    0x10302011e0f050c011d0f060f010b09010f14070507031704080c13020c1606030f050910090201022a0901090c0c0f020d0f030806090f01050d02010e0a05030618010c 72
    0x51a61803102c0c0c042c074094001d14410500220b4000c0c3c6074407107004000e00724490f010b6a5402520348582c1c2400c24000c054100c04126450072003917060410141141c8242c20310345040000001c481100c4034419030343c070010140c1d182c800a54807030b050306146540300c41500040c0d03004d0101140011110000c0001c81d400c44907000007030080c20021408010300c03a20100031460305a9020052035821160902c411503c242c4e58038050456a400e0241c01408c40b501d29180c038046510300014004000800a80041e0100c0981d402107a080e41d540700407820b02d01c050307202802102d0f5580140c104100d4107003844100c070501380c070b90400d40e0780e0315182003094030b00d020b40e00300205001da50800013040320410300c03a0b04103002802400d0313131384030540e6402400140400e0640c00201c4a10502c9007503d444a03186402422070f130746140e1903505010005181d1007408500a043c0b0102c0c6078902e500d600d500a10301c0c01004003c041e41c1403403401242160340043d079070001c0c0c52b5551919406c100f095018242c9446928100 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 211961753 1250 211960503 211960517
    0x40b030a061104080d050d05100b0d0c0e040e0304061101050709120c0f0e06040b010206060a0b0d090602030103030804030f0206040b07050c0309030a05161d04020409030507050f0105010302011e 85
    0x181d150071000703115485450500c110204400f0408040c100048540c005076aa20607654900070a0030f9402c80b1030203003020b181c00407070b01010024a000c440c00d43d0900c00480100044e2641040c000340c400e0040b9506040c1c02a05142c0400c2010758044083e2084824a480f034094000075819202e00300c0d00300f03d59110218280308418400d44040781c2812294901c078482030a40030340c0b905c001000000c3d299101001403c5c6030002c1200354203043c013440501c0380c0d00f0b00061030141028400560300c90440c0c0070b010080000821180280025a0454480071703800810440d660b503100d041c0241540320855003036021a40408502c1800780c400504144590f4008012055503121407208444035401400004900e20090004980a035024030421b03c0c958070400003080200509081c48111503000c0d40b100141000ca5118021119040e5295981c03041d0b0460380010a500240b8041d501c6015186029204d44542c1045940e031110540c81035040e03034002d0b210300c15214045100e180c0801290701400d0001040 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 211963003 1250 211961753 211961773
    0x904090f0b06100c05210d0204030605060f010c0b06060c030d060b07020a0803030f06010804020423070909060e04300302040806060607022d0d081305030a05070b030705120a0902030c040b03 83
    0x8004018441606c190828608034510141d00280d800c55002078450315510001d00c5514500461506098442801d00d402140020744450504003402031003c4e000d400c0014188003092418030460390201400759040040b25201c041d440e04a40091104030b010b002c20b072401080404001050780c1c4948e5400c400e600840c0e8510004688001c03000d002244c000b51601030340300e07040d10f00100b10455001070700b503407083e20b02e42180014030000043c0e00002c11145003801c18013a4400815084d42c3c00758220908084030440341034012540040da61180307040b4002c000c010108075506400a1045038034820844400d0707211881007004d039109042c130003540007040b0b086004c4005075107018011004449040909a0302c0d4481c041041c0e5403c0303803811224150001b41448800c403201e408000a00b2040e001030900103110394030070b542d0314428051301c0c0da00300c1e000c8002001644640c00301d65004032540d064420500b4480300c980043c02840c10201c0c0729000b0f41c01550141e040c2441010110b5000a0003040a03a079 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 211964253 1250 211963003 211963033
    0x6090e04080a140c0c010f0806150903030c0114010f080c0109030b0a06090c170f060d0b190f02090301230a091a1302210706050904090f0b06100c05 65
    0x10288a4240500c80f212400510795020742e80034001000d01040644240e003014000108216460054101807102c090305108150310344040305079500d4010400165103030103441c006407075400380b020a182179608220002118003e1004118100c0d01400040303015035844450054580228a423454001082a034082003c1101441d0050b0400c044620005540e40c030b841024058880c0550040c1c00f0600e07c030034441410b403d0740c1403e98042101e4512010b241130500019180c030640d8038001d00a2401c80c80826028400038401409200c42400100030b40001170403004040d4008600040c030a510380034048a02c2c40d5181ca489001c041c0031391441c3c06540d0341c1112900188103554027610040d07000302810b5810341c0803103005030203030105d00c4104076540040c2c030400140d40d240400c40d80300440340d148002840100080d01000791500c5051280d21101c2c0080428014440810080d1111074a40b010714207110b411441c03030b4012103060b107142d007d2060816098a85058404c03005003203610400410450131 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 211965503 1250 211964253 211964257
    0x1a010302030c1e1c091115190e130b03250306090b090f030a02060609060d080a1e0c0201020a0803070c1a0115030e060a0e0708012406090e0408 63
    0xb800c424a00e81010706551040e14014142d01c0a041c0c1c4842c00180010040c04039455541611042c120034042078000303580301c150b04071b0742d10480e038007815082d0300354820301402030103803020f084848200e0001080034090060075084007001c1e4901035012030700c420b480072100380036036806000050b000b000a1021200100c54007866200c607000384e401c50440120025845000b100d10403801103229082e10b0a00c02c07511400c21407030540041d50f0342c0c41005507c04407600462413135400901121a1943c0c0d0340c500021070000703c0c10038801464030000284440603182c00c0911216100c00514901e80406501c81013902d141c0700c503000103405a4001070480700020600f0300155484503203841c0110102509658810500e00c890b4081110304d0080001440420302c60034440d8101e0301036107003e0201014082c4040c0d1500f80c081c011034003080d140d03440307004089400c101e4200101003000c000c100b054503800c05595012882460a84044000d0b50001a86c81c802c0c2000b83c1a1071340303d03c12240640710781e0b0b582c54040d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 211966753 1250 211965503 211965511
    0x70e040c08070e03102903060103030906050702030705060309030a080f07090302040f02090604030804090f02030c090906030a120c0c0b0f03070809070810060303180305030301090e03070c120c091a01030203 90
    0x502c11790101d42d5400e4003c0c080e8034403500d00d00c0380d160101c085246c2e1090003900c00c0c41a050084e8005001040072a5101110f10100c034900e09100760b54258500200b400e00d0340f9508050342020b4004107004c5510800070081941c000290744010864650320400007490000343c5d500800506090000c0c805450541d00c14a10500044401441c1000f00008103945030050351056408040c0400c0400a40015000d034600018010004520310300d003040d03801f0308502900603d240544040000503196440400c4002401500185d4218803900f0030b9400802d010b507000d06c215040c01105000241c022101ca080c2e50389188201166400c2d55a0b603401182c0001c0d00504801c894440c50400184c2c40000380204410486c020402183cad0508606010f00b9008441d000317003404d0080d240041020480207c1928103407002800c02054101c0f140300c0031880d500030440c4c06802d515151100007480c0207200c006009180c030403510400095582c0c0d541c80112188001c0000070000701441c40b08d00d941c1319a00031544 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 211968003 1250 211966753 211966759
    0x815010314060103170a0320041805060108131505010b1c0b03032217030403110f03100e0102040b030c030411030f0709150306091a0108030c030d02070f08070506070e040c08070e 78
    0x10302e5070308000692411050808c08121454002018400c2c0b0102014640303c0300c0b0f800b00c040c4100c4c140100000d10100c001051091007458500d10b15081240c10145d06d41c43c01d036104000d01055840c4c0c0c000c2e00c800d0340702d080d10300d824109161544030107250780d000d0608265401030245d402c0440c52402890420760310441e000b013404031603d0108854840031515040b80052100071a221401c40c604040000004075035030b032141414002542da640d80010707465400c070088000c04500001400300450190240c5d030004040514007004100180031146c002c0e6100e54062401001c00e00550300c10725840e0541d0031007105454008000510803c0380340c0c0c00c0002c0c4101300c01c842c6c0d03600030303560b481c4d650032078800c0081100d05000318035100c51721604492005025101c80c1010790b01d00448519542d07501d10501e40c410058913000728420083c0070a84000048003900080a90b0341c42c1d07050326113152180022a0203e000c076542e0302030004282002d10500503400c603940c50b0f00c450307600c0360201581c06420002c4202d174 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 211969253 1250 211968003 211968011
    0x6030c14031606020109060c0c110111010609020a0c1203050c0f0304050309040c03020304060b0f0a17011803180603110423030f0a0302060a020708030c0f040815010314060103170a03 80
    0x2c030103402d9044038005000381d50001500110300d1414a05607041c5400740001c0141215428002c1015590304403524442420b00e4900111040d801c203000d04055400846058400f151402c0d40541008045600920442c0510782c190782d108001e408403002920000300c503d50510003881044620001950054007900445e410b2a8410307000030161965206024000f84d004402e110401c14103000395010107108035110080c089506c1c0200f003081c912403040584248006090b031842c404290300152030000510748011802c0494100500700a1003c040d040951581520004000c1d200c1c1c81130310706966200341101e2801d03151403034502000804034860201c1c0450a00c3d640f031a95001c1084044461100c80502100c111900f03003e030170301c9001480b400c012801000600001a50350040383c1e0b014001c1c003865034580c101c140f0590300500403900032400e94402e1504561101e03001c083c009040701e102d0301c0c5121000383d10000301a140d039801e11000703000620f2100341410140b4128060640440e003498005 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 211970503 1250 211969253 211969273
    0x160c0806010f030209060405040b0c071b03080a08071e1d090108010f060503030c060a0903050c0313050906030c13021803150708130b060118031b05030f0106030c1403 73
    0x19052020a07070141c0b0804810120400450400250f4070794440001c540c100501c1c5801e8813122075040c40201515554800002c8580801c8006020a40c218042d516004030464407454010241d0f44805807860200d159503000034042d0b40300d8280440700340b00e85504105101e8204c8000d480e48040501000c10700240d00c02000c0b183c0e1900300c1c25500a0060000120f40402401c000c2e104403070840d04200d010746c00c00c011003d44010000350701c80e040401070600044d10981c03424212050302443c000503006000010300301d140000f45940d04000d644d01142d0b508510740f2484101503480342059411074010f114280380080041159002c6e00141c0c2c130703114106620b148500d00281c10312102c546c06007003011001d0184038003a0b45c44142e01e0741c00a000601c2032040d44c0e842e2180c142c40c2400800345810844498070300744100c5954041a4002c0d41d1003184004c41000c116120502c000c190301900703000748a084903032a45000140a907204a0340c00c2080042040c0c100b1120054420410f41440c8e05446038594503 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 211971753 1250 211970503 211970519
    0x1e09110d1a0a050102010903050f0f070206120604061203080414010605030703061a0f0618040f0e0f10050106120509150c0a180513050406090b01080c0406080d05160c 73
    0x3092620a8062041c000404040c20070842e903030700743c0149045a00d024885030010f07400504a03001c801c2001c01050311551515414019032007003c00023500604089401000e411941e1501801000120341c1401802c1c0ca52100d0b0101c18104040540043d1915003c9004140660030058195240d0000402d01c6a11000440c0c901905684200c45e5940e4610503900250845410049010402c5814460000411000603d980a00901c0c600d00d20807007604851969039a90011b04000c00c0c581081c4404000e400311280c0719210851080103a0017210310300d03d901c400320f104050590311903442c0c40201c4010f89a1042c011303c0d00074200080b87c419a030011844505006030a40b00728021802c2c2540c640450070000d00c64036100090070209810130344140300030b58507100c0400640c5036800000550f41d80e9410800302400041034080c0106c005040045001240400c0720742d0042e40540b002d01139140d90700c8080c1d584404d0a01c0c0c15000880600c61103000000c034500d040c0d2024000c01038014002d403a041d0b4 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 211973003 1250 211971753 211971761
    0x1050a2703030e060901020d1d0a03080301140102151f03050f0303060109060e01080103020607060915020309010c18030b10030b010b0a090b1822061508011e09110d 72
    0x11488108405000420415500c0b400003060142d0540c4c8140c2060504c400103035498900c09169828400485143c400700110028024141c0300001e12800041d540d909008007981d200780580c840d03e1a0035008241c055000041501002e10324441c1a102a550900a9000c582207240400001d03542c54400002148007007241c1c01d020018500516500d00384900058050b01c1244c0c018828455011107c1c5d249a8002c84102c1c11a6011381c2c440c2d0703032440f5900c1c20800815007058000d021699145005510380ca041c3e01451081d102c40000700700141d20110f06481103582c1c15500b229550a502060001608500c20250804000e0004003185500c990300d09075a0003090f000b4000e9540701285d500e141c030760300058140003030145440c10761408a8029600c00c00e109402c005d6401150065002d041c100410041000e00140c010303010800320740c552410740b068514100746500012035913000400c00076106080c0e104150381c40352000000f60b1400c076905d405405c4076000b988400505120300001c2001d5802 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 211974253 1250 211973003 211973057
    0x1141201030803100302090a0c261b1c0b130e030304080d02091809100608030d05060310020c0a020f090106020d110a12020606191401121b080103140a030e01050a 71
    0x9004030700b274040d42c1c800808030245031807100f41c9140d860300714a44845404020356004134502d885000c0000320f0002d04284c0b44510441000459105803441d40e02a0060b4801002c0c41c40844200c000c10f400340c101c0200740d5030744410783e1481350410004500050210300042c4505400c0d801c0250900c610390000485802640601c26100c0d415201004400e16007400011024482c0090070004607003004811aaa406a60804070b84160b4600c0820070550701088450340c040c08000e829950392840c1f00c801d035207921203808200e0140d00d46107500350092030a030754458165039596005043c4005100c204030307103c01c032003040209540100e84c05e0202094074001d000305480c48070740007844d0a041c00000c3c413190400c0658030b2030038014100700520400c040043c040a00600920303111182000d1810341030020a645903050003000c69100070030003c1500800054100c90088628144181030101d40e591100c1c0003440040004403d4040b621283d03000308060145044c180c03074809421012404ac0320507140c00c0d56 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 211975503 1250 211974253 211974271
    0x303061026040b0a0b0d0b01091d100b150c120d0b0411210105030c01050d06090f05060a0807050f12010209030f01150527090f06040c050114120103080310030209 71
    0x80f007080038500081c003078400102015a074000f401c00c3c285c1c555021005c010b014100c166910703004401511030300300d607000f10780500c0301c010b80b02041000f4400e00000c158075140c1d140120449040500b5584484003540c001c2e040c04000b03482d081b11480d9030305074690f10884041c09950350310f02a0407a20b0704c5a214090000700c0d0380d180e1591340d03805841000300e8006000219041c81c040c401c010312141d1404290320483c0d200378200142c48446441c0c4080c061314054010600c014034090030a12080309030b41255000ba1010364085058540b180c0c00e403515908180112600710aa502da0a111803d103405926000508000018140841c3c000041d06140c2c0640c83c1840607074481c10030460440407441d800c00102030842d6190541450542c4140d444429003111071040d0703405400003445100240104007540040605480440c603051809030318084007070060034001400e4800400718141c09400716208150000541e920130784c43c40d0b481c604254002000292015040c000001c0140c6504100d01d025590703c0d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 211976753 1250 211975503 211975523
    0x110304031a2508090c090a0b010f0203030f13060b0607051f0627090506040506040302070609050102100b060d110d1512030f1b12030e030306102604 65
    0x18070348005010005042140c0950196401c0c200c0b035400ca6020b1140c816036802c1c403892940c0c0304c5500600b03102c0c0780c9124640210209080100280d569409039001c110240ca0710b104030303042c0d51303012a92800704032030000c40c0291100110781500840a01124203c1c482c45c0082101c00c0303000c000c40c0c103d8002035030442e070f01d500007864640d002c10035134141302c1d00c00c400b110b0400c981c03480d10780300010824070023a12584405200e880300c8440080d9030009019103402204070355090600c3d203002a500c06041f6019401800b03050760202c1c049101d0305a280c100d4030160300411403c681e080c80da400501c0300c68585503200707004000c0140020070a00800c440d682c81680d00c9621041100d001400741d0303642008540e51100c20384014090100300c05c0140c01c45a41602e0b020303116603c40071040d100e0114290b655901c2c1c601505031442040740d10710b1001d41080319540c0501120308491107480e41c0e130100f541d03400c1d070203e804a440d04000f4840c5078001d60310300303c8501d00716182c0e103800000f0035a04425070f802d50b008121 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 211978003 1250 211976753 211976783
    0x3031e0e100c03020906070f06060305060408180402090a0b0901020f07080115080604030203031b040504090b07110d05040b0d020f040b04030b010807030c0902030703090b090f1b0d03030c11030403 86
    0x200b4401c0b41d0741c0784841d040079440c007101c2a00049107441404401441c02c010007121109004850780300320091a8464201c48243c141420a110140c000c2c2510b195000e4640c50702c840907003405d0094455284c0041c1040c400c02e403e200105109400c881c00680c1103100d819014100d59104200704c81c01011042c1c0000b45400b56002c2c036045001058000b03400316404030044c0000284c0c0001100c0e8800022124100342100c2c0080c912500d1140f680095031041c20581c1850a1120410800e4010113568940d0190a080c00710400c1c0c60b5090504200007182c0d080c8003c00003000250010018003400d0100185003103c035120351405500701d0742104001c190701150034400c0000c81302c00e0a002d00143e100030300c4628507507603a9000724003441c02890744158021010030000c90194001c0030f0840d44c402d0b4051800e20f480c001040d902c80d10581d0b00c18081c440c100d03145949100d001c0e6180240d0031b01030030381070502c202034900341c0152980c42141000c101c800001e180920314248050400341d44503081010391000 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 211979253 1250 211978003 211978033
    0x50319110d060c12020705030301210503070501020a03060e040b06130204030209010e01151806031104030f03110106060c11040c0e0d0b070807090b090f0301060b0c03040801060e040f03031e0e 84
    0x8038404911001c584104504c8022480c0082aa411507000c842f55030401218854a10300410941d6401000c91101142801c1001010340250440048540d030410403281c0d2000c02c60b88801054601a000d030303952001150050400c004104452802d5000140c07401f50340e0f90100e6440d2200340d20046201c07120340c0060051603000300f90700d010852203140050b030000b00c030b0700b6a401d001a01e01c01e140501d940c6040180c10324040c3d2060300c0055030041c1c50070803a250681000f134002e81078246000899460158081810390140305c00024207a00540b080050794101402c0c440200444103035030003800301e62600c000c0c150303481a000c44459445141c2c1600c050404d010f000d010854094507070010b204074407a06012040400d02074034a5040110b1720100484c1600010034010045500605041d130400120b0b141ca0020010003081101d207258020803005954613a206291101070b10001c18500c1034048e0303c07012034440e03040850f40c2d0840c1201101c3c00c4a0b030030350400441c1c03600c0e040081c85400410031115806 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 211980503 1250 211979253 211979267
    0x30c051b061b091c020109150305040203070b041a0c0f062e050105030c031504060602071403030901140c10050a090308090601030b010603110702031b090c04050319110d060c 76
    0x1c0441c41e41c26080009400004152960700f540c0c880b4040b480401084c01c0da80f050f0b124000030042031360800c03200d500f920f1006001d4002114264042d120b0b0500000f601e1a494046034101d0300e00e044c08203c101181300c4d02840369401012005000d12404000c9a4240e0701401407500030200c07901005200c42280011080049803c0503441c205a18400c1c10800e698000c0c0450394050708412103940c0d03039a40c45500f09101d0700320341c42d4140c0040c542100821555000600181541c42c4008001c0900030b843d01016500d12400e24500c0c00281c0e10440c80c0741c0140041c1c09004e400c00954142d9080804141083c8100d40085075504c65560b01d07200b002080c150421102d640004054020348040d44c1161510111400180f00e40001c06984151360519020000c0c20f0300d50203036008003556a000c11a84002982684030b480c0309120360104408101080c107510f0460302201c10140183c100240081c0340b90320441c1007950300b52114805003003080b81e00d5451000c00d520030341c45130400040403203251100400340 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 211981753 1250 211980503 211980541
    0xb070c0e0705251208040602210711060c0703030c05160f02132003060a050603090609010c1b03080c090603040b04060506030c0a03060c170705190c0210030c051b06 72
    0x500304007044100030030320790450000707540b6250034945c5070780d00c913441e001c03000744240740203941c504200100141c000e80c0c0500c0c00c58003e420741e68649103a15103d40c000703030320382c1000d5841e03611003481040900b001a01036081003020742c045003011401c1181400442e0801c00c2001c508441405071303122810118584446002d4860101c41d00c1081029141d51200c07115100d1080b0803142200d010001400503500c0044201c050200a0702c896101c2c189800225500c00041c0c50070300c520750a01c0c0c24800703c688550189a42080d039400400c2807a901c0e610f0680d12200d015044070600c031800c0000c1d45154462400860045114543c1450149404d00380f03203048079000b501c2c241c444d801040c203844807507807a030102c0c0069036007001001900200c034a40582c1c00500540406500d160b141007041144d07030700140601900342c000300742c2030221b10100030200c600000c00d1000a5100c0300c1e1401d000c0041c0e00c20b501c0224010348070b04145182114020564401101107841b0b40195403082080103600c030720f501c405080e9 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 211983003 1250 211981753 211981807
    0x6090c0503010302100c14010f1b030c051903062c060102010c1713020d050d09060203040b0a051602120c0102070506030402100804080702190e09070305070b070c0e0705 74
    0x865041d603000405c100c00000d0b180f401c008816005000f0f02030012005c00054150500800904419800450160040f0381140f0b6460700654480c03200030b806070150100082245e80c6542c80c0031a6405000840071961100d041015561980800c1c3c220b02908203c04441d403005035034022004e41c41200c005600000c0ae402d045904042c941d614054000184541ca110a03054150407503894100c802c031581891072010b90b0105680d40c20702c0500c98080f0304480300101c1a514003007040c3e210300303003682c1d070307101754030460700a00c40400c1490241ca105001038288030b0040820380d031414035950002603150034030500005540c0c00519500120350b804002d44001000192080c17403d51400750009881c0c1c14030040703074000b4800e1410014007000090411203200c4c5a000704010042440314001c3d0f001d0034109d00600e4103031000701c0c01083c1c3e01c00300090b0074400caa80c014001c0c40d045040140c0594190021002111011804540491030f01d800713003074144c412075141c0d648941700e160103465482e0040c026103500c3c032 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 211984253 1250 211983003 211983007
    0x105040309091a010f0507030c0f0305030405060114010806040b030a020310020a0207060207120f150501030b01171c030e0c04090b15060c0a170421020102060a0c08040b100b04080106090c05 83
    0xf2050340c2104446080d00c0780b42c104079480317800b14103090b01d100b2003807840108030030b80c0307050b80c00100741c0c0000155006038011400c480071680c0703d411801d0208480104640030071b000c2000181b0f90301e881d400c645003090010701501e8035030404d13501003071511a4100c529021309401207a0801c0d4103504003c11b00041221344003c001a070f180821030030701c0038031007040609001010b1907040d00340300440481244580070300701e0400640d81e50b800c2a00d07a81400f03016081924106c8010a01031003000100c540340101c40c0307540404010703212a0154000c0040d1451170f1018010415040380030b03035032440b8090409018030590810741c508010340103030303251103102c186100d0030b000d021160441d400041c9034802260701c040006071582140300c0c3c42d103e60060b0703800b90b18003c1c160003140400c020780c506404a01d91003a0211f40320340d21401c03042d000355000081e8902c00107148000190200b00114a01c9030481c1256210401d06515100301c12126445500641c0316031b91941d10401980c28a441500c0f440100c03460711074 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 211985503 1250 211984253 211984301
    0x70b250c0201140d021c0f1103040b0f060a1208072607030f0905060703020c01030f0204080a060b06070503160c0b0a0509190b04060f030b0312041502070503010504030909 75
    0x1901e015001c40000a100320040744403200b03903071301d64120340c046482c041c3c01e051030164420084000e0708030101d4a040590500700f4241c01142c0280640f4000e17640080c2001456035041030401c02d0b101c000b0a40d5030f0040314a140081c01049101c1c403005114003401c84d00b50f81d00030604043c1800c1c0607800f100070510200341c00c07101101c0c0350b040c152003040307505103016401d541c216030046882e082030342c0040303501010004ea01800c15070005480398940d07c0c20f072014010010201c0c0403504034003507440384008541001e07100340000781380c0f07503c0906071940003070260342007071900d8840610316007005401c0c03414241d10b11004401e000d00c0c0b00c51040140503d4682901c1c04402140082043c05012803050160b0110b0140002010402901001404000d5001074482d070340c0702d100a01c404031140708200800d160060b4118142030204007410400b00f02414603113094540b15501d0b03030101c5589004011402080c20114541d41c00317005240c09140a96546601242001d00d4002107030503414030b00d48064520341c030403 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 211986753 1250 211985503 211985507
    0x2f01090c141f02060f090a1203050f0f010302011d030a0b0f06090109090201090509062e090b04050303161e030201061a18091f080604050c011106130206070b250c0201 73
    0x180e17922044c590385504280c0c4981100500d8408400d40c000c1921388020b1110154503070590050344510480095100703d80c5800007040c41640080c00080d00041011a4140090302e0b42d0340e451829000c05822150245240c2d09c0320102800c041e56620004060746d42440081d1400c1c000286c050301e02d05004001d040341701e9001800c02d030800d00c16980281030100004096640d1462194601d80c035034010200d01003050511000310700b07121848d46011465010780072880c0c00d02c4d90159802c1e00c1001c2d00a42c5032100d4050382421101d40000100e500300c22020040e2440440103100c0c0004601ca6000403480f6405d00c0c0304501004840214901c1007403060001504020982103440c000e0303501500c400707016848401c50103941080080e424140710220b21070000d80f02e074000035a82c0c8160f02803015078900c458400011204485007074a1001c083e48aa4042503812490010503030200c0e100419140c42d0a0903595000d02092089480c02c48900000c0030f40d000d2203090b8900284244100c2c5004076400d0760b2a800 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 211988003 1250 211986753 211986763
    0xb040e0906010b190e0d0515010f120b060d020315010303121b0c1407060e0f040203040c060509190305030a120506100c0807061103162f01090c141f02 66
    0x5410390303036001d42984841d010b0045c01c1c05a10140040d202e00c0c0c61101a05203a83c3e81c100c2403c990075031000d20f03000001ea5840480760141641d0210b101c0c5921858942c07a105403100d4041d01446d8029002c841d410b006035010042064001d241c414145410340c55800d0192500e400070070301202440c100105003070b03500c2c070710914507036102500e0901c001d54904c241800303903940ca490001c01a1601c0740c1c020106805800c01c1900410344821107146a240308000c0900003640002da40080100103082014020f4a000d1405003c000340082e00e44000c4402c42c00c8140340c082401d40c0140c600c0d070000980c41c0354803a482020215400e1003950184401d042c0a03012400452648090104100006032490100903280303045a55080d0040000d000c6110b00d8011600c640e413007600e0400352400200c01c01001540540042d10005c030481d403021a1a0300784170001184085040d070b441345255610400480054210044640a0301a0a0344042021100e4007445038120351000820600591081c90102030750b80011 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 211989253 1250 211988003 211988017
    0x105090307390b0d05090a020a03140c130f0506011701090b060c010e150702060103050705060306060c0105010f0f05030c06030a02341101110601030b0705130b040e0906010b 76
    0x820000614440501c2c281500c0b0419042d5008988842d0005019420302c030140c12007540c2410b00300603540b106c40039282e942c500100001e4202c81c604030104081800c566035505040f02201c01d071121640f0601c001503000000201465206558104d04c00c842d61043c07045035804442800c01d076803010000f004608011405200750403072591200e00305a2076440b103c2c00d0341d032450700c4100280403110000c40381d5038407400c50140e07e030700740340810000800e0380b840000e010741241c1d00140a40580345c1050248a865031005150613040725041040b89245d840c00d100d098002e000040b8003a8615052041e07101e1507004540c4034510913440403a48103050742d65401125007000601100617990034420111140e01c0440559010005818005650205920b0701e0850420740c40303005000340c1c440380d400c015514000703200300c24a001c1d407080006000140d108000d00ea08008030b41080e41c01d05011041050304500c041e0400b662400020404000ca4030f00103821341e030807000c0d50307018010340d40c1050400140380c02229 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 211990503 1250 211989253 211989293
    0x60d030909020a0903050708070302030613170d09020306100f050d11120115030302060105010909050c0a0f200c12010216080d0209040f23010815090c060c0601080105090307 76
    0x160885940d8010302d404030045500000750f40302107a940c4185622041a4401a1b01a0080dd40000c1000821801da800301c00d074000c0d80001d000700307282c1c070703900360341e0401d0320f109000e82c1d916003e0b080560b600304200b40c40742e01c480000049050902c40f501820740c1d0a81d202c2d90144513a6072106002411810030744403004800e42d000b0140b406146030306809005411100da159045008000c014917602007840c5050340c030280c0b0340f4804296a00c010300300305c0d05c0032681d030081c0c000d00f48100c00913a84544c008003642d2495150088080f6440700f01c54031000c404007112906984074101c8032280c2c0c1002001d5550040c000c1000f1410300380902c00340301c00c24400c184c00421907007000a80300300c41125941650b0204401801c00c010043c0c0c48400c94000700124400450600038a002074030180051b4091a4140c032489000f8050002955031400c0652002030030340c400e180181125001c0740c0d1502e10140100c116450002d1405500d0084c400c1c1c2140c00107015078600d5002000140c01003625007080701c0d44400d4903 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 211991753 1250 211990503 211990507
    0x30c032702030307080403150e030a0906030b0a0b130e0f070906260c0702030c030606220e010207110111010606090312110a08040911070c12150903030f05060d03090902 74
    0x1d10001c1d003148103661000380241c201150106c01c2c0101480791a4140440b4401000780d01c480a07000d903642d0240a881c40d0020322440b80c2402090300ca50483c1d445558040d020302c0c5501c0d220348410026030840090744407403c0500c9810050029500807071500f001e00a14a81c2090901c80b400030300c10382c0d841c01007009004100400c641c19114000089802e051515050120390401070000001e69000d04001e92081c0704010100d102d0f85000708542c2e00074200101002400e003403500a001c1c1c1d82c2180314188440030f50300c42c000038000c40c003030000b49049440703007a0000b56481c1800004d88807009503d4000041ea24154080c05001c4d082a00181640e4020030028001c460b00c0f6421204a944108140101c0c007401050200f00060038000d4230a50b04c0000c4180b1030700951321010051340c000c200026120510003e001c00190b440312012421050148040182102e103090002041c0c039000c03002200040d03030344c04440034650700520600d90000801c9036240959450b90700d000b07190503218002d941c1400c0e40 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 211993003 1250 211991753 211991831
    0x60307170312070c12050c0d110a02030f0733031109031906060801021602040b01110a03050405040501170606010e0a1e0e071803080708070807050d030c03 68
    0x41041582d0b0100c090300103400c1c89180c008001406038940305001c80d595880d2504076425280100c0031394040320004401801d0f070f0581102c0440b00442030210213450b60003989007000160b2820b10001c1c148040d604001d144041c030780411123110900b000002c203c2c8900903d0850a1045800307c490810380c041d11300481d072900da1030601490fa214040003da8548502c201c20b5100c140d0942031488118001c40c0100103d942c1c03488110300343d11800c1306001d01d80040c2d1030203400500d019030100d2400360381032400748180c61041100b0340c9442c6410000b540804c0001c10100030300e140600846004d0002e080143c405441c661688079503d0801900355418003c14038001e140c1916412065001401045c1d11419110000c445070b8139178007824010421010410f0000445a900400c0c0c401ca84107048080032120910b5602e8bc8507050304070100c110760070ba0042040c140402d0701034025116080c0200f01900103044101005012260103522990a00d820907945400d2241441d03800041050105042128401 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 211994253 1250 211993003 211993049
    0x4030f110a05060307170a02090307061b05071e08010c090909050a050607030b360c04080106090e01151a0d0f05041103060912040b0a0302070c0603150e060307 70
    0x12850700520b400c040c01100308a05c50380e1000182c14514840c01c010005a2280103443e07090707100e00c0d41902c3d0541c0c01a501080710034811041402d1400c0310b001c01c3c2000d690305956290620705a03a2281c0c0910b400210340b040c0540c1590310700402004640020802c40018403406080d16045202c1c1c1107403240d40ea101003041c00300c11b00c540842d0356400401e80daa903181002000e801462818503072406080803405644a0301d6503c811180180340d0041071884d040e10024111810220082a000c41060103210000303419000340240d10140134030703c0020591520200c505400c403115400c080070346500004081103d2100202c0304002c5e40e0140746590b985280b050b0700100540205100c0682c1c00389003500b00018440301601410003510218143c1c2e0190b111030002e1aa2240580040c030034064013000204445c00c0110010903090009003809420070030907440c1c00b00740030066071241c400300b61125070b41402c0c0c220301c91300ca5000d070020b0700c91440181481004203580e0b03903181c01488014415251000c004030 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 211995503 1250 211994253 211994269
    0x30d030c200c1206012111060a181409090607140901050913020712110c040207030e13050106020606101b060b1507051005040b04030e220203180304030f11 68
    0x7001c040c100764840100030f1072040e0389000074800c80e401064000c03c2c2154403100f4001d191042070f044040181501880c1e001c016455200a0003101404004200811500e15120003c4010080400ea0801d54000c000c1844003440c8014221015a001007080081d807542107a0045d0b01c04d00c000c1000c1b81c4554903d00103840034400c82d0a003580c4001d024000c0d9208840c142c00514402e03124010641d42002003045c281c0b00701d02c00b8060440d007078200c0b4032491083e00b095805041c500b4024a41a12024400404120000c8015084219154503040103211241c3c0420100e5005101983c4004210709400001443c90003602041d140603009601d152040c031859400900103c0c0d80242421201c0d50902501603ca501485003120390f400745008004882c2107030b2043c0d5201326009458048940e0311307642c0c204c9805400d40d11407680301209161600c1d1844131002e003c0103580518000583c0c80c10250303001d4015a900e08c840800b503910030001400020703c1d40300c10a210700d5200172400c00015031500000d01d08 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 211996753 1250 211995503 211995523
    0x6011d01091806170607052205040204080606030c0f010e0103021804020f0a0f09051c0501140709060908060402241c020a030507030501081c11060103060b030d030c20 73
    0x2110b600c1145074100304069100303e04031003681d515190744441110300c00d034540c8800ca50b84008100144400c2510100c001c00081d101c848414042d020b1944500010b03089030426040381c0d174594441010400746090420a84004d41012116180030440e1a00001c205481d4100c181e810150007151070000d44a1f440d06100344403800800030341d1200155410411242c0110000d180002c1d0300b00c0003000e45901030b9040134143c0e54050940c200e6000c054034460808480e0100031680c82d0350350342c00c501c4440b03202c4000d9805015981d9425616900c1c101e401040e941181e0007002030b81e000300c820f110040c2e0301c4d80746400101d44140000164520904203071000340c0158200c0c00a01206200d42c04041351082d8000c5c821092540c804101548400e0320880807198240142803e43d80142d6282101c03240700740c3c20a002c0800e40c0b41005000310b14642c000d0400c0400c0e031044907a1901c84206a02c140303001d2103402c281501354901000941d01c00080204100c1da401d24450820315440e079a2619a403050050100e2 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 211998003 1250 211996753 211996769
    0x31614010911100f02060a02160b0109050a06050616060b1f05071406090c04111606060305010b1c11060c031b0127020f01031d0604170306011d0109 65
    0x140000d9810542000c0009642c560b204a4103400c0038442c0300c2c0910088107188145a004009681c0c0e4904c04000175441030010010b410602031070f1100203107440542902070444d2800100d85030800c02140c01c21b445668001c1d51141e68240042490110345000010440360003034408220891403070041036802d80c0568105600a13000c0c4400c85100e9000001400c02034800c1180500c41100b100040c3d4403010107a60490480d0080040684585001d40240c030382c43c280c42e4005881c3c40d494032203a094070408042c040310100d4075080e080060000a10444400e1101610840728188107280f2041000707141c07d400509107230a9035205061504c0c0d0b503007560309804640c1c003240e585403083c10000c60032124180c1488080e6092004c4003145144240c8a0071605000040350a03510090760300300505001c031940d459040682c2c0b094000382101c145050f100c00d040f40c02c0c0240c041820b00b410540c00010300e6007041e00c25020f00b001802103a03688070f211901c5080101c078440942c58582c0d00122540d220340c1d840051 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 211999253 1250 211998003 211998011
    0xf060e060403030b0a0e2203050408030a02010906111204060906020f03040609050f030406020706271205010b0d0b040f030c06020d0605010206010f0b0a05160204061202040f0e03161401 81
    0xc1096019840180410303021145c4d41c00d42c0e540c1c0c0d41e035951800c504450103240c0c110313212a0352404107440e020b00104107100e13051050a050b100c00e595440c60304440b05200041c1c1d100c200704801d02c0414451101d2400c1082ca00c1031920710a1030b06050b241340702030002040b4964680008040c00b01a6040d11100307410740405a6a070300707150800c40050150a8010348a81c040d991503032820703080005c1220100c541c560003404400786450b8081e1416030a90081030041c0740d03040540d00704400c0101000c00a040c04610810404245003040c0d0700311140da94885001e01c503039980910104805c0c034025039000d13a100c06240d81c070b0640b40c50104c070002200ba10081002c3e001158030410040290004030607541b013a0700712071241c3c2e40c0340180940c0b001d00f442001c41454080040c421a1485030340140001c03040c4680c003030b40c0c20b1055404582112040d5010380454031a01c0204000c610303090003031514610b07000c8020300c0707041c002d0343c2e08649900c03840c0100710300905003042560400c8660b8601580180390400204 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 212000503 1250 211999253 211999261
    0x403120e1302090315060915010908060901020307180503070e0702031201150e040911040c051608031501021b010e0a081c031113030b070c0615050a080f0303040f060e06 74
    0x81d403c02a1068428000c074008032210240d40600944203440c018406600e07600c2d40202c103400b8140b0110010704000ba0b41d500456484410000039010f10601c5d0001a540c0c5040e0b500149070064030320003041a54040641042a55030000d080c4041c3c2e4098404007805450300c40040c0c0c0303507100342d0040802070410040005100c412040107045403901948440b07544081140c208030440781e08480082c010b1039061424130707403410b1540c0120401c1c901030400502d0f00c2c1e114500008065550b6004981c440c40001c00c01c03184200c043c0b00b140c4255020b0008044207200403c0d450725500c1c0151200c1d0402403249044441d543d81c044554004001100c1642d107410310307400d114039803104800c091002280c00c111034001c0000004080b01d140c5410301e80404107445c00c596401c045000050009410013070440045d60108103540718510100300032740000070386036141c2424801041096400003410350481020610020804402c0707c1c0d1042d03104409881c01d07040340c5000001000000c1c0f03013816600c1404108 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 212001753 1250 212000503 212000539
    0xa1b020a0501060803040b04142106090d090803181302040e09010b011107032a140f0a140108130605010627030206070201030c0c0501150e0108030f0403120e 69
    0xc0c0680602a2000f03118641d10303450400c2d40c0380300c0d07480381610844041008016051080c40080324010004102c504455004000e92518601083c0380302d005810441c01e021420f01c041011580c503c0b9241031024003a0314010301941c482c0986100d0081c05071031950080703540d075945007624018a40c0d007a821910340d40c5031640003d507240e0848804103070398a02507881e9102d42c0145124101c2d80da030207000f442e0844c00e683e00c0447c100322152140050704484072564100c00d410305201005001c0080d140c2d030741c2503010030411004c0e414521500d4005c802170030040c44800151801f0303080b0000d087c00d0440c200c0e00c0d1212941d07c40448001d014010302d2400e0000b00c0c4480d48130000010302115040c694400c082c620000301d04200a03444000e40c802ea0400a03c8010b502941100c05040907a0402c00366084058440a0075180e000d48010101806140c0c1800030050340701501e809400400006c6040820075000e4001621039404042d10510700e00304100d80707407880307000d511061913005800819641c0550381c43c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 212003003 1250 212001753 212001763
    0xb0a05040c15090914010b0a050c03090a092c0706030b0d0b09010b030d0201020918040305070501050a020c19050a0b100f06031a030607080612010216050c01230f030a1b02 75
    0x340503015414840d411222603421750415050700c0c1c101103928a450100d10099686611580c650010390209010240042d560305c0707006001071491050200c2c00b100f01d1514100c038030880c080e220560211001440711204400030303080041d56468200080c800c5d0611001803090240c0d144002c01c5011640100008110190071503011010198122041020700d01c000fa8280d00400042071740210403040071829441c4460565a0064040d041283c81c2542a880b81800e44100325aa044c8035500015018010101041031084500400720110b010400f16519551601346014000d0303c2e441741c5a011071781d042e180107050030080500a501444070795880304044e0140190703040c00070081080250801581c1000700b00d09214000c0b40e40c0301c00441d65244100b02d1480443c1000d4685990300340154070050000350050658580100c0c024407650001c10001000c10b0041c2c61100380c0344807201c2c03280e0540d08481c0103464140300d00094090b100d0341d46620141c005c04046016189a07102d9a0702c4204013500424 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 212004253 1250 212003003 212003009
    0x30903010c0f0f0e131b08011205060a110c0f010b0109060507230f151902070201021b0f0d08030402040501151202090a0504150f080a0b0a05040c1509 66
    0x100a000e14251114242c500b02c0c000050240030a11000403841142c1c880e45018403080c0d8020a42c5007000081400e100840d40d8001460380b42d01c0c0d1581858404a8000003007900400c440100d0421070080f81e41c44a07251140134048803009600d451484003441e0451054800130684c0030215418810561400740c080d00702c1d180b0050204203640310224040780310303000326100c482d0400d00803008140040d0004802202041c01c0807480c2c06080c1c0414444582071107006c078880310400201e11103040c000b54005c2c1125195010b00a400d00c100308840060340c0201360070503940e0321a9461022030b1030860104242103030303110708070b81d0142c4015810790801c134686020f140218001d450400c5503a8070350500d9030340302641503200008202c03141444503000c00c15400800412601070030304403000d65140040340940348002a51682d48110203014081265801007100c000c00ca6040240300c0c0c0502c945411200c50000f50600d512076807100001070030300907242c0611006141250b5040750a040ea0300c001414156140 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 212005503 1250 212004253 212004259
    0xa061101091b1d040f020904030e10090612020403050d0c08090406030317181b0402190f12060e04060203090a0c091b08090727090f020a06051c050717090309 69
    0x1003d006205400c03144103204a5010524141000040e000c21000c420018011010000800f08221058a035144d10380c84e80719554540001c6141041d5000d407014a07902c03060303002d05205100c03c001296000611000741c03006030901410381c45881c00d00d6406841440400ba8015050180c00020142d010300e050f050030501107030080c0c807911080304103100054110540f9140354811038500e1000e1151a948114202e0001d00051074590f2840402048048440d00c4102013401e41d5001070301650860b990802c0d480300d901e01003210710f0402a40c910158400303400500ba151340880052500340c5e0030003a0400443d08000c11082c03240d0f807200b00801034002c80f00380d0b10320102c0c844040744042d40142e042d140a5400800a01102c5040204d607010584423001440c1c040c0c0c0e900e28206460b030703031284603400120340584205001d4000a0050040f100c21950049082080c20880c4121810342d007088030f20714400d42d400c041403e440d0164101d40423903000060701555060102404103001c000402815248019 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 212006753 1250 212005503 212005529
    0x161415060409020315150909010905150f0a11040b13060e0a0506040b030c040e040c050108010b0a021b01051c051005010206130f051c0201090507140a061101091b 71
    0x1802440700b03990300082c000390182d0017603480310b161401c00c4604640c00079905c4000c0c1141052203000030341c02141550410010f955414000f02807040070700425015401400705600c55090401500390740c904000d0841049071307a640107031200c45448004680007840d20045094485006110480110400e407080c40c02103030b0244200816410000c3c1050704a40c80101003504241c0340142404242d44000c2568030320f0041004003084c101044e01e034190046010703e006a041d01d0600b4005003407100c041c1c22109400300c0c03d0000502a13036001600481c81c0300042007005050044000507a240e020300031040400100100c1031824107412940f0ac50300c03881d01000c044403450b43e81c10059813a030000b0b88650754441001d5640f000800c0a944e039215540b807180c801c40f401080c55a0141c135070032210401450042c0d4540d141d20702403046c204420800340c6400611110720704001000515284880c1c480c8400340426181709004401c1d0a50080c2c5123650050b42c5003411483d0030740d03075098004103401211102c01c0c1ca = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 212008003 1250 212006753 212006761
    0x140d05061302030432030f09150703050d0e1b0d050703061e14040201050301120c0902030403030209011707020c040e0f010203090304210305030411060c161a0f040b161415 75
    0x213a005c0310200c4103a448099441c0c40030b90b070428092903014000254204001c074000c0c040c180c07243c4000b4440e150003070707561130b4560000020003030a584074042949403650000e8102d44509042c005c1b42d85a4004c1269140186c12082ca49681007801035440502100d01c2c0070800b8401d40014560f884201c0c014100804c54144040262526900d0558019001032000c3c40180549d14414000400f00c82c000c215503000c0c0b41d900c0701c13004180c0c3d00441e822030000e40c001c07903c40d05650300b140a140c0a034118150455061502070700003551102e4a039580c51042e5282e003814049500180500c0f80c078618054025580d03483d0008600b070303603603010f8401d00704da140203031004e0410124502c0110000c3c1d5890358915240d510f41e45c42d0802807580755044154801000c0104541c0d09800300301000e03990143c01000e100342440d216045640110404900c419810108520740702c2102d480d007110142e61600880945403500d41100c0d91074035841d044010008001040c80c6280e000000842c10340005031844004401d0352 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 212009253 1250 212008003 212008073
    0xc040c032004150503060d080408030d05010e0610050d090203071706091204030201030c1124130201020c120a1a0a06090c05072607080405090601140d050613020304 72
    0x86140b00b080002400200c090f801d4610600c011130f00f004000308070a05c40e0100740c841c0a1194403c3d40180b1841e480051410810441c0b0301a9030b0051880403082611031410700d0102c1d1450704211245010014006000b007040013407035015400f8a9009400c496043d51906049500d0341c02e8449411090b128400000340d50a10002d01100554006549982041c1c619401900a003101160040c24080c50356050421481e040021103030b10b08511150046901d4201d031741800e03210025151880041f194003c4c180540d0b00095040d05a2000f0303a039481030680812001030400c0304503c3c0c018200b0f01040c680031801c20400d07241c2405031260343c0e0208400f030784d2005440e0441d644030170b034000031030421702c000c6011807940b5240a07110f0140c03807501d401b005c40ca1001c000f4a030f400074404a0310325101107010b000031700700241410780c041c60070b0038034085094481040701d42d68000e90130755030f82541e22600007410503200c03541c41040c07000d540c2030107548904141c81c2c200b14191032540f00d203d8280c400020240c0c41c0d1 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 212010503 1250 212009253 212009257
    0x50c0a05030315030c1e010201020d020f0a0f020607050703080408070f080c070603150302041a10091d0705160804030209040b061804171b03040603050610110d03020c0c040c0320 78
    0x8006046c150842c40702c1051a02c03072240901045e041d950309004402c08411180001c140001d10b90303107010782c1c07502d800c0805081d007048003d600e01150703c0181048800c42d081003c80301460b40605000c003050f50f0301d16000b803851040e40f83c000d10b034060800d01007007001050805000701126010a980c0055112402141140e1286c030004681011220040002d0300b82684049004001705140c0961850700ba80810180c07051030100c403001541001040142da02112044034018904408400483c1010305008102c3e0003020403800544003140000340c104881e440469006542c050031842c01c900e01814900d2109004540150251204070110381d500000c202c6a503104552108020264070007240d01c00c0590740151038a403514500581c18440314400c1000580010240c0e954045081e1078810309005080b00c124449100b03010641540d000a420080307043c022566041c6401a11426080302d0140381c0184a41301c260030618201c005141c850b455006070b0590080c0c040c00650f9010300e005164224 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 212011753 1250 212010503 212010523
    0xe07020d0c0203010209180a0f060f15050c06040303140c09030d050a110303040807030908120f090a031b080f0a2a1a03011401030b0105030a0c050c0a0503031503 71
    0x5810031842842414010420051041d0001d00010300302a030000c08105042695528084e403044800104038114082c0c0c004d00e404c1000d008403c2c072100d49049015232628290f8000ca11900002d0f0602c403070b0b01840380c0c0030b03201c2d059405000c443c1117080c6420050000e1000e0b000000940c43e8202c00190140c80342821180c0708000a030040041e1503c4450498242d00480080002c01c20fa4903c05203004004101940c02207000d011010340c3c60320345240203044803000350f000489035084400c0b21898014094166038000d0410702904d60b4403440e5100007207000d541b41e00010702030101001d28061402c200210281030701d5106084540c25056200138907620f03610000014507040468000310740d072002c000c01d402c02c42c001e080e541e50025611081031048034160048030900301007004c001040a103030000d0085444a00c00e007400c1100952a500003004d500c00140600b813815107400810403502e12601c00c03541c18000001c251400310b882031400586941c03003907401854201d0240071804440c940401c084403d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 212013003 1250 212011753 212011757
    0x1505090103051b0a020c0f0a060909020f090a03030215010b030c04031106041502032107080403031a10021b06251703070c1407061d030f1606090e07 65
    0x60000450044010b854010040310f25484000c501e0084607900c0302c003400002d0626000340ca59205000c09100701c50000d01485841442e680b07004100d2103401c4802c480a5a03201e11015903950900d0a03043c4c0244107506255821840e100d100009040c0d012400600c1c1c0014200c0c402d10a90b078400c1c06504038041070301d07203c446040401c000c20004142c01d002c0d140030b41c03002d01000c0c1040ea8510341c84a21490039000e0301c01603000020f007500640c500104420056030a00321130500f41c00c000c00000c01d8007200803c0102410782d0360800c0c05414100216003820030400400a400c0003544900081d194404941111040d1004102c1c220b018a040e000b903604070001281030200c090b45503c1c1003410448541001d841c1c0d4245400c21034800003a600045200b40010b4503040d4808041c3d1600204104030201c2c52906904005010310100f5480b07182c0c01c407041c0103800000200b007800740019003428410044000c8610444a054030301e0340d10468400c1c00c85209840d43c100250f40c0e01210310441004851104c0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 212014253 1250 212013003 212013007
    0x3030e12070b090103020d0b1512070201060b0315041e0c0e0306061c300801050105091008150402030907060e18070f0c0f03080105030d030c020703080a02010e06010603151505 77
    0x702c4d40700e0340c0681070280c0e20301c1001c030303c205911001c01c0d200558850303100c80c2802d00003000c05846e08141070b643e4101c6c1c0588004c200051410004114a000281114800482c90fa0501106a890703400070002038425031800510300100041c40b00040a00d01c681c6004a4090b4110101c64500442c5c1d0b1849107070040e201c6420844d090301200c1c2c5818150908566a6020305484902c40d0031111410b02081c3c18244000d5040d03008000152246005910443c104081002411200d0720340c01c1f0000d000c0841800e1919041e01c1d004150180000803800e1160803920200410100104c0080c84800b164606d48134007003410f8000040c802c0c86900b1084042c00608001c01145d50300744207a95030081048140341c6040035003000d41c1c0e00042008481001e4001805110040c0420704d420300c0700204d4072006e41010001c188110902079100d8255210282511402044000505001f9000913024600d03110941c0d2442d81c407031380050000c083e030240312040038034610750200b1041045900d1000d4281c03191100c41c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 212015503 1250 212014253 212014267
    0x10b031f0c0203120a0e0c0901052d10020601030b130b07120209100201020307031a030703020108090a21020d090b0904050a09060e1e01090b061005090a03030e12070b 73
    0x40050002030342520110310040040036a0040e52003101341c0076500100d004584a0413010200780f82241c00b1000a2095441c60b0040150703540b1030701461500c801728800f140821100c4e826a01000c0281c80303100760423429414903401038907800320340241a42c1c482c491587c010b03140d124038280d01300c203641c10040111003500c0204110706d0140c1e603144400d034510361001d0b00c0c04c50008041142c5400f80d0034030402603034012050081e0541c15020304683e000100710414002c07200407000070342d01c141520019052084080100d680d078642403114540241d0007200f0141c0b031100315000142440f800303114110050141c1500c1406040c483e1403c1002c440d5803105140c180342e4030b03104100080030080c040c103c1c907641c2c8640d0040054a1806201806961040a00191507144821030054080420b40c821070b03034501801007000800d030314411a0004800d136100d2401810000f826900c030321400f0000ba40c428000100007040581c02241d0300310080090307c00c3c4041c1c0340f070b0180140d9111582d0007251414007042c40342c0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 212016753 1250 212015503 212015563
    0x6060f030901090c170c1012020901020705040e0705031209031c020a1505100504090206030411280311010201050f0408160c0801050115090305070509100306050a0b0102010b03 77
    0x280d904001d003000002281d11013076803140440041a44101c0d4421000480b0b820480c90511204aa00e5402c0e10072041001c20b4503001449082107013000300705958082251111a4802c010b82c10141402500801ca50060f0f1501c065840001d0b11859119210b4682e507811450311020a695610780b0140082500100b6600f000e0111199041400708500c9032078010004611041083d04402e0300155001603141400b00d0003001c520b8042c1c004902a031f081c01c102c500103807030b40421a64442c0d000a541640c00000d03000080d20301811b9440c8204030507086c1d61060071908403400d032004a0f4030880041408a8060006900f694800c40d006620030705028001004a80c151005041200d07103c80410458402070361646880748898103c501148c0d5604c0042c8926600b011410488000d60f0408400b60b03032071543ea0326581c2c00c00b8040e60380915503040128040300201c01ca1000134541c0107405000500d050251034000f4075203014098015801d0208641a5013804141d80c4480d2912206082c41010442d142c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 212018003 1250 212016753 212016757
    0x10c0921030e030312040c0501020a050a140307140c040612050c0d060f060f0f12080313030302040b0a080a0506040e030403020603150904050a1b06050406180f0611060a020306060f 79
    0x4254144040d4800900c090f80e0144000c001d0704e03807100f40e008020708090404455100301074000d2410340d8400c13251800860000034800c1d400d954840d0000410a07640007246055014000300103061005c80403003c449803c0116060385e0101d029502040741d90340d10846401c281e2880d03200940141c000b2a51100a810038051501c9854001c0340b010035210800c038044801c590659004460340c18443c4418012081a80300210080c601d40340e0f91061204503071180401c42c80080c2c4005110240b40020004040c029019180200081d5443c01e4507101d03150400fa011120884500c24420724100004a640c5400d118810030064601d00031410a42035030709000c826440a81003000000c0c007400c07550820b50b036a1402620552290303000d40700307424061615a903298a4550788541501c0030201c1840141d43c8002034074112034151611100f03186503500e654200381e00c2c1d034200c175200740c010307a0300400ca507a082240680c094a0030802c03140303183c0e243d08801d0100d02050310702070ba0200042001d0380c680100000 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 212019253 1250 212018003 212018069
    0x10b0316121a09010e01050109090305091c1b05030624011d030f070806070302070308070c0201050d0e01022203201504151704030c06050a111b010c09 66
    0xb03045400a004814030004040440b0240360581d1905604409030f1028003a4900410b10f801d010b0150b240c15a9000d00240103a4100c01d01490f6108c40e8103200c10301406c00f40040a40081d005082d90014141c2c00c00c19450314050300d8064032882010810b00340451100c0118120164841c81c564014000115105600d5103003a60800320b00e41240e50550344c00b0704c42c116a00104034000e04466142000340350410000524450615105010a40101e9007004806d0b62091282c586450411010310050303d141c0507400590303040c03524114440070358400541c018036a503001e1800080c04100b4090806000d100300303001c014004100c0c0780307680704040d2401490b189680b100808040030360446428202c010381082d030000094020700c1364442101500700c14040300c0d0a012a80c00704240c40e080d14050200c0c1e1105200034041c9030381d60001562031015900c50710b140c4500f1074066540c1c030120146400e821085507070310352495191424000c440d50007800000c00f12020021440c00c4045016468404030003000 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 212020503 1250 212019253 212019263
    0x60708070e06090319030207051503011814130510060305070e041406070903020406151d0303190809010f0b01080c070302010603020d03080a0b0621131211010b031612 73
    0x8000303500c05984c01d2200b442c00343c2020941040e2814107050003440c01c01d02c2d81c00381c1d0046101410514208c00150700700e82c19aa1400300880902e40c5c04240d14000301510301160003408500f10030321240700e0000ca002d03107686014204a4419280c450a000102c03100d900c0018420780c80310500b0050380c0b004481459006000c1c40300701803075409502241d414440126000c00010ba41c01e04240118034081c41342d000900b502c2405d41104481e075280140140301d0b855244804c600707211844d404182d504100300d4246141c00e00445503414121000078000750780584080d10b081d424843c00400058141c81801500d4405945007072903500c803169400000e5101c03500a078119501c4103000310250b254000c1114075241b003581d41c0709062501d84180400c40300e005081610680042000d21044c921001e25445412040f00700240c03540c0b503812803510140c80c50b00300289001d1000c1b101554040d00610b45190554015009000d078000b1101015110f65240240645945410380c0910050340e029101a00c818452 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 212021753 1250 212020503 212020507
    0x90913050d020f012405010c150e0c0306090d02060402060a020a0b24010c051e010e07081c0311040303030f0e1b01020c030604080d0203130f060603030809060708070e06 74
    0x25240d00703090403481c100d80d401580c08100c060342050700900c1810f0281070320006801d941004000c9050510415201e800d04003c0c140301e0715420b006860030109100c020b416000c00c012681c40303070310540310201e0f9000188a0f00070703d4002074000c0e1000c07400d100446480d6000d401c0507a290380c2081419006140309004511070b0500340d000240780c074010b59004051042c03000402509600e600c0301d410101c0b02c0b2090400101500d01c0300020b10028400f8405402c04100c1c5c41d01c0d000494030716004103098440c5a00c5d41c410201e00082c400004a900714040e110000720504001403481c041c0c0c29a0003803040f80b80503c0017008100301007403103a48203c2402c4d02e4400b0100384a441c1d540302c01d01e03010346032540c4907554242484580c00c3d582c04201081d240c0c04140d015081e00e00d441d450702c08841c098081c0c003000341134000001540c44108809000310441c0d00041038180c0d000c207410803000800c90303400704401189441c0f0108119007030009229200381050707035400c0c1d041c1d80d8007002282c211050740b204603000441 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 212023003 1250 212021753 212021791
    0x90f020c030426010501030c031e0b01050f030109082715031f0905070e01020d09060c080a020a050304030f0b0a06030b06011211071a07030209030a0f0516120201120507050909 77
    0x100317005d032600850290400405090960900340e0590fa206da450105e811110004400001d10b9107503443d0460f402195440d03114022000032038050301542e1801801004005182c0001840300e929850b184001030b68008145030701034060284198250840d032000c0b40701800000e000c0e1210740c071801405940210701034202d07980e034000380003514410b80b0054041220109445101d581c100b09030028845d1624100d0b400c180360031030107000000d05000c00f40c01900700241d0040040d00800450300c00c1c543c00000c8950760360340d9081c03219102d886000102d0b5040340301404282500380c503003d0003040d130360014140718103511801d0040d074006002e050320048941d10b90300640b24146050020f04800b602400704040c008036800f00c1c0c5070300103000921a009051040c00494015240041d0b0410106e0744001c0d1240e003020706080040c501040001500b103a401c0b0000003048031b0503031404070f0350464801e032036003680140312000520544030116014000110f00740170b62512890114a4242c000012440080403510 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 212024253 1250 212023003 212023079
    0x901090e070e010f0f0f050304020a0e0106120b0402030f0f060307030c0b1213050a03080406060e01031523160509150309070b07120f0315080106090f020c0304 70
    0x508460301d402066005440c000c4550308099209201a02403a000201d515501070240009010701440005c002012002030b00310740340c051219024003501d0050601035a90f4400083c810346084c0c000042c610305040480c403442c1818000c1d42d02420004264001a62781e15161204109005014507410b2040040000c003040f4001140005040103c9071039554820314820b2002880000e05050040c01f428401540861000300780021807950501d880c806548a1341170000c040e101c10340205d01e46642030800001041108000c0d07107400440c116003445003032010004010620407000c00c031368241d011b180004484907920680b00c2c58042880c141141400c05c00c40c081040401c0320801124895000020b0014030038040102a009100c18020580760004035174404508030131800e041c00c10300080000e42e0009030f00030380102e12442c40313110280d107016030b82c7d55190340a070180d0700c9202c1d0018904080559808030a0084502c4601e18030b000b145004d03d020212031a903440040f07000100d0720f10300748044981c8 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 212025503 1250 212024253 212024279
    0x18010503102c011d0a21031b0503060a0e013605010b04050a08010e0606060f1204081b06010b1c0617061603020f0f0904060b1303030314090a0308040206090d0803180c0d08090109 78
    0x8c8629903030113403030385492424007940c904180c0058100009400042000056580124982c100b444035003004241083c005044040140b400300c40c1702d241020004140301203400c000d801290f50480e86a90f400395101c0c501401c0740c01c004030060741d0303800900c0000c810b42401401003240840702e081d032614000d201e0002920008003507030121454903000400b00b400c0f840141c4032018a41d440409044613525155030341000707101d03400c80340703001032000c41d55848000400ea0003c0014104815414000250031040340d450381421290b007944c401c82510f01c824807900c24425181c840303ea62a80030700d89414200340420582040c0480340d0301c552900d401040ca0140d8002a1000100e02c201c0c1058890071481c0c09801e94082514480c003241240b0700b000398108002a168030300c0d6030141040091500d40d40003107501403051145154005810719503a03410020042c0013076105190700c1168040080703009105913107484c0505c10490303200508031a0302d004288254024010b44005040c07060340c050392213408800c84 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 212026753 1250 212025503 212025551
    0xf060f0d050a0c140a0e0f090106050a1101060f03080717070507030507090c0801030b091c0903020109080604050325060f06030218010503102c011d0a2103 68
    0x501d8840081c440c21844900030350108400d2820700d1500b41c016480452440d0040c13241c00420003030185440d600e41c1c0c03103040142144107409800c0d50036540c0c6070500948283d000d00c11a00028200708065005c4074810300c14201903c80c480305545c0b040f40b0b15180d01c40d040e00181d800392143d40490341016035020060000300310151244015009030380c654100a41010101d038401401e2504049518102c280d00000c680e05481d409586480f45403201c0e03406500d84600f480821240c00383e404500c4074540d8100d0250741c00c0324400d0742c4010340c440d21080300c20303200d040555008019610030310145070034140d040b26514a03800f20f0041000d09503441d45071082543d094803130140d0400d0b0340f41c40030300175401c02c002c4500d28410301203100d1110354900700c0070940d14070902600c400501d40d294014640050002010034500001d00b10303036001c005c5030401c1c89000309820000b202a4140d440e0181204840102d400e50310b6135084108008090087c0d001c418112000710005010190303224100b50541200b1801d0581c6 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 212028003 1250 212026753 212026777
    0x1050d060609090302150702031c0c0e030a0c050339030a050303040b01030c090b03100b1302071a0f1303030b06090d0b07020712111c050a0b1e0103020f0f060f 70
    0x35600c6e600d880802d6580300588442d04540040001c0003c100c040e40080e4640e5090b9040018407600c030480c02c84540c40508200d590501601c217801c0240000624a00150391045041d58000d00303024100c240d1003a0320f0303966002ca8240080e0f804400150984282c0d4500c0c0001e002d49111000ea9950381e0f0456100b01c808450b90940e0f12b00510900880b48042c5028056002040100c0c680010000b0340c2d82145000351858151552005178598480890007038500402840c19500c0c0c5c400381c0f070144600b0241c50340c4a89045081400140f024010b0300c201c5020725103907090741d140060300f6141100a010380c0841d154008004020814064175160510320a0704d0107489841e1160801c070000070300340b02c1e0540c403d10303132003008205010100f0f401c10100340211004a0352096034002c0f901c80b02c0710500c25158041c1c014018040201d0622042912041c442c10101c0001c0b490102c15030340c5043c2d410001c0c04041d4021500054100c624100200042090785005090b2403c200780320103801d42c0c50f808a000201c13 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 212029253 1250 212028003 212028013
    0x5011508010c03050a050f0f1008011d010c02070b0d0b04110a02100b0f060a05030a06030210023904050a1d0109110405160531060e1801050d060609090302 68
    0x82c0d080c1d40340c49016085404004c5c01d00c894148003071000e001e0540135282010b00d64000c001704000c501c0130300500d001842e51400a020500410b0210303e11000c1510074600035508000003018894404503c00003603034154980a410f18210011070710040c0b0481d500c05411582c0c0710b000c003a8201c0201e02400c2d005485900518035620680c60140c160b403905089075005101039142d4110700d81e039100c01e56601001030710f0700a4417592140b2600000c2e12050784040d400ca505015688400c1c0e50101c0c210504501c41801a42071000201010252000c1c00c80210f40e00003241d80345101ca0300d0182c00c010b4000a201701d002c920000040a43d02a600070000c20382c0640c1e54900002003003041d0481148a4041c0c01c490800c410310340f410320041c582a0040065080090020341100074203d807041450010901c00c001083d2013403040d00c1e440017028140150004191170320700c6d02c1c082e440c01d2442c1844000400ca010f15461343b8210600c0110214000c003107070342c551210b4001c903284102d441003054050203540140 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 212030503 1250 212029253 212029271
    0xd050a020d0b100f1b080c030403050d051c050c121501030e06150108040510050702030901030f0905070302010503070314040501020a1106011202090a0603060f0b0301061202011b0501150801 83
    0x8811030b9100740c40b0718003555000340d50030308440c0c010041d52203100d1507090800c2000503150460101c805034507001003801d9004250103001c048000090011340b48244c08580c1030103c40078007a00d890144402c40c080c0d000d0035071190265590f50380c2080d60000075406005091070465039000100720300403a84400743c844a1703504d54825607414040d048001603820050440d600b00b039016403100159a9a4050611240c00d010404000007001401d04114030541c1c104118242203034001d4499024101241c002800c2152a40c40100300b0b11405415644c09401850181c0c40c65005441d1508014805024103a580b45028050704c8142005441030344200f0005998001c1c114001c0d00d1404100841c10380c40d40241e006101d00094000029803050301210120b056583c1c5414000c0030780029017000f400a41061f04829060049070001951564210020720445488148040540410800180c0040d40c80442c5806030350442031100318203401040049400d002c21031402c100c1c100180d000304d00a0307664203180 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 212031753 1250 212030503 212030527
    0xe03031b0c0607020a030210090e10031101050301180b010909020c030c100e0a062705010b01090b0f0a080a0b03010501121509021e0a080708030406020105151c05030d050a02 76
    0x103030701086001c40d8010309014441d00414010589804028003030100302c0c900d60b481c2401014010001c0c40c1c4a50310740464a0400381920041056100860705507c5450810f0301642c001c0f801e607410b035042c0d03500398842015030400043c081c0c490386800c41c0c1403010030b81780483c0086090008044050b03921f40150358548110100c07525002001070000342441c40c1c4041108031000206070341504a411080110382e60303040e002d40a0811060b0002026600c15040605041000640100c0a030140980741c0c2000a84d83d084074201c0c500c43d00d00c50300018001080701c0040903010700d1038250070188524001914105684c0404d084070001c0c0c01c542d00b10340624075110208200031340744001b00410000140b020507065804140f103900d070903101c2907869200d4544a10385840d06072090006201ca801111880c558580d00242c8961007802043c0046d400c0c48001076a00e0200d4090352100751010309122044001a501000082c02104046805010800c000108100d440c006d09015041c1c08200607074800250100e = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 212033003 1250 212031753 212031763
    0x908070e16080c1314100c02101107050303220803040b030a2f0c1204050901060c050f0105090607120903170603011805060402010f0215060607030e03031b 68
    0xc018081000810405040c40380745051034440d905003450082c9880e0828020f9990180d6282c2d44500e840741c040019051280c0c030071003900003000340c0d15141e14000720711086890200c11103001c0c4d0080071040000003118810919100340f180550161100d07180c8030000a81158800501c0310307501000c05a0400250110354020001481c040000b18542841d1045681550000404529030f180da1404107a03805082080800f01841034080b550401c030f101c01941107040d0f0000e0001c48024802c01d18a0b07200c0050210450341070700e00051080d00b0a81c680f0078121030341110110204c60901034840e564900074402d00074280034180e41c0b0090704840c6004d03400180030141c0c0140356a805410135441502282d04150101e110080c1c2e959a1941d0340e44160209024256141c00d898104040300b205100380100820544d028074402d98030001d69034a40d440490796520306844030350b5242c8042010515a240c4100185201403080c1013a03882e14200a0000e030458005044801c20851a03500034403442c402404 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 212034253 1250 212033003 212033009
    0x609020a0806041505190903180b13090506030102090612010e0c1914040807061d03030304020306010605210f270d030b060f040b04030b090a030c030503070e090106090807 75
    0x100401483c9481e031a203c0c40709007080344604180d603441c3e012a6000011900780804101c001c0360600030508a0706e001071031f11060510300c0c1c2c060310304550041242040c650443c1c2c0e4410150001921850812100700000c0c94044d2000e68159800c02c0321081030b80b190000340000d0a401e11910308950301d0903050080314480100264800d4200304113600304c403d0508030044104116151240f0000100038a02c401442103030000c50240c81028000503680364403d40c070010741c1c201c500e8268800e001c9142856078074001a54001d605800c403400600c40d040c82440a042d840c0d11600c40f044607c2d00e154005d010380402504e9856089a205c4104600b043c41c0c030303c000c5440800c0d078101c2001000b21056440e10f03410201128010103454010700b08031a500c40c0c00341c81169402d48415581d50380c0d6030b5540c48282e84036210480702070045000140411101140f251803898250b1075600f800c11160307030704440070b600080181d020b12914000301c590a4580081940c0038090301c3d2290304a150034040d5480c47e202039a8 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 212035503 1250 212034253 212034269
    0x91f050402090d0f0201090512010e010b060c060402010c0c0b07030305061c0203060c1303060f06030c0602030c031209010212010305060603300703050c010c030c03050105031b090a14040609020a 85
    0x8100c6000f9281c1e0760789401c0c415007064900340c610740b540c40100c45056a5038081e551180c524442c9001202c410f502c502d50303581c0c0c0240200444441c3c00d0501c1518000e0061004540e0090f50014001d940150785030500c240c41b0391200c00c80d66843d60002801504000380c1030b07001035510b504020340390410600400850010305600006010943d0029070f83c0e0070f0052004000100120310a18008125512a0055540242c083c010030560108034001805d061200303450820090000040b09400401105c1c080104103002e149880100c5034801c6825002801d407002c0343d90300b0031548a10000c030307a06250280d84104050000c5003840e4040602d0542072900070142e601912076049a44600405169440343d40900655100d48443c10305940600070722035078280a500f04070300d107840c01e40e1542c404002074196032010041a6251003c0c036507201182c580000701c1c040781018440c40e6207400da000c9540b0440290006c50b003a50403440c52050307080162000c03580f40351601420000c42c078001446101505850b = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 212036753 1250 212035503 212035507
    0x20c090a09120f0c02062206181406070f030806120102040f030b0403032a031a01051e0f16050106121e05010902060a1706040e1509030702091f050402 66
    0x280c403501c0e99450781c511100c1c01e201410010f20951030007040c80b10003e80c2c0007401703030740c0b141c8003d80302400c0540c80c95a454500030b0300d5500403800318010b2900c1508030304480c0c2803116442c100b41148400b45818100e40358801e80901caa40005030030340c444124054469620042282004424441c1480d031850341c4c0320703803a40180000d0140b4580550322200700c1c1e80020f94050035803620b0074260010958400c4071a0680c00004c0d42d010303c00c1c4280ca0955480c0e00c644c1e420080580721005a001b060341030180395001070740c01c00645642c21103201c0c04002c1903a00c0a5101e00c0c111305188010078551003800302ca40301d81d594020b54000e101c4284250f41c0100114401c05140a43d2591b0390905020402c2460403a65001326800d814010250702490084d40d001e00303070f699100d0b44410050229100b103160715504510380ca0002d4018182030280c1d41041c0745510081c020045e080727075821404c002c01800807020b0b102c24400c88026030b495034100c40c010b021181c050080b40e21001c118498a4000380c0189021b2801 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 212038003 1250 212036753 212036771
    0x4061a1e0f011103090f1302040e011508070f110f030a03090606091a09090c150705100c0f03091a0a06030b070206070503360f0c010905060a03020f07080406020c090a 73
    0x80101c40b54040222808909030b105800042c0303007844c7c500c0584036100c0c4007081c007144043c20b00f1603943c1669407a811400d142c610510301151a100b048800b0700001e80d84070841c0c6e0481d80101e22a0a9001c0c20b417099811001000c00c425196801003040080003d444644000c1444035902c80d2001800e82c0c21814892100c090000d01c0a055058000324006c2000701c0000f8117030701041c0802c0402107002400d0911303c2000070201c046036044490241d881c4d01801c89103044e020040e200790610314072561903090203084408800e0b8014004031f07005403507440250014100310302c05c0d003e040b031080c055144000341142c198207164006440003454481998029410301c6202600f00040c2d07907205002c12400d002c1d500c120f152412102a00c00708102e0600c2d040f910090001c43d000c6004481c082d42803041740c003100c2c40c0f24011100c8031024031940760480410484210301d10b200e60000c10300100a11003403440d081842c1d584100c0c1c0d0b402503000c03030010381000798803182c1d500d0a0416150041c4803100e0510000300 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 212039253 1250 212038003 212038037
    0xa0c0f080105090d0e06130806010f0e07140a0320040306060f0e1902040308070c050f031209060307030b0a081501060801061b05070b0d09050606010c080304061a1e0f01 74
    0x40070034040350521840d49820315803591040d08507030f034081c105c103960b1500d903940e41c8441c0c0d89c9003803e0141091075800c1d0200072a440800356401c6102c1c0000c1c5d50303180301504142c070b10002c840e0b2214a45a003019240d492215903e030792034095904905800c0c11703d03030741c1d10325608000f02190900d420030b40f884242080c0800840fa1034003507c81c0c1124076888045420342c0c4500c000b1000780703d640d00042c25140c1c00304412060055071600308049a500740c0b0801024001c42c81015120550718030120111002800b4580c00c908003400078545c44a151700300042c42290711800620840b1042e0b000900941c031202c0c0ca094400d855846403401400305040488055050900c040e000482107008a41140404504a01400310030098600240081d0300643d64030311030b030f1020300302078041c112060740c0510840c07000c5010f6520031012001c5031f46d0440780e00790540e00c0350b640780790207480f110b6050b58821405019050f03d0350344006408144580d44500700845213220024064009102030302e0f42d051003100c000050b5001 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 212040503 1250 212039253 212039263
    0x60c0905030d0f02070e01060c12090810091401091506050409021c0302150c0901090b070305030105060c010603021008070e0d02090a0b0a150c02011407080a050307110a0c0f08010509 80
    0x9609400c0c103655400380f12904030300e040440d40c019081c080480c0c00000e03426804c09c3c2c1c0000030714054000c803440c0b103072414005d0300e181045103c0e140060f844001e0100385120a039012005261041d0140d40c80d150800e02600d00303582c0030f80310031303211400d0490384250789074194403421000388800d036418014902c55400080e0051042503524244040740f488400405109201180030380600040410b03503400c2422400085400042c0c3d110702217241907002141d40c803400426074107256032540d1030900c0c43e800e000500c1f286030407101d900c01884d900c88002000507901c0b420010a04041c0380d4400a240c508101e00400d49105103407240c2c016001c20781c00c80c0158640382d513041d60114040341c000c01c0e002c1c90303000850000655035008400d4002c507400214040b44d40040d442054031b000340c1e217525031148461401c034401d01c40c2c203030014130b843e0080103030803215401000a10703440f1840381017040d0f041414500c400d00b401111902100c522101c00c2042c030035042d103045ca690151480d603000700f240c0d1401d013410720350394 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 212041753 1250 212040503 212040523
    0x12030402090a0207200a060201061202120f03040e040c060c02010228020d0b0f34050f0d0510081605210703030e0306060409080901030b06040b0a050304060c090503 72
    0x11210040094040d80740b075012100d41c83d90050044210451403800f9241d2045d11405551003240313242e40004140f44140620429648142d1100c10b83c1480c640c200320f840521080ca6041d10300400c1045908003000f400a040101801c0c0045007007468a807a118482103a690030038024420002c0301540544d078000f8001000d12011900c0004102802c00300e582e0403400c10b200294044610360407007080200991b40240100c0e514620610b454a0750392486078568540302c501c2c1400304d04408280e085071103180e030b102d140100d1410701c41e140c000c000d00398400307a60002180602c4652900d051007100400c803044600106035000c0680b0f0240e8003410403800e01030851040511545c080113000481c00407002d4440820342c081c00440c4c035242e54a11700600508080b817103442c8640907400c00910141003030700600500d241e00c00d02043c0f92900c514015001407c514000c5900802c0511000c0b4140f8001c1c4000d0500c410340f0746419440e0319186c0303410030030344000c0c048980412128403030401050b02c0004a02c040 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 212043003 1250 212041753 212041759
    0x61b03170a0b060a02030d0612031e18081f150b092e090b09060d050a06230a09090c05060c010f0204030f0308070206090712081314090912030402 64
    0x440d2500c140740c8024107000d0b4140ca50000002400c060040d80000090880c50b20502c018000c869868062095141e0141e601030041481c50451a42c0440e000b1941403441c901410b0080310000d1032107148201c1c04072030300a85041c0e4464061805014a1200e11800d243c2d600c0d10f040c80b001c1c0d912000001001054498191402d5022503503009541c0d824400180c190414414907492101e1251f040c5041d40c061090701020401c11400810054410001c90b00c010340c0107441e0f5460103110340321032001407d0003080c50003c0355591300040340c030310310800d680c01621500b61105004c0301021404c100032794986906c4258480c0c41e14034988006040ca01d10241240c0048880d81e803255036405045000d0716021800310401440050040304105055090f0040325000f81d0381c804255032800003d90380d5800c01d450068056103d820300f08030002e001d50b40c00706000d10030707600b040c2000c800324403c400c060032603000701130000786c60000444903081c80507003580e010108400a010b815414110141188005480070780 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 212044253 1250 212043003 212043047
    0x712090308091509030d0e100c031509020a020a0213150305060106020c0904050a020d0c090e150c0c0601170304080303010b09041b080c160506090a05010e070f12022701061b03 77
    0x1508041230289a40184000609000340c594420000b4001d00d50510314a150000244011800710014400d8030000c1e0419002002400460b030200501020403c5001d100e080d00e8030714880c40c00b2038400400005503c5040142869410004080c0c141180c840103580030310386075000c110104000041321601180c0690352000d2080c95030509a5000005d40c1020002030f040010070900e01200003007141000d002d015001c0b0700c907107405034004a144100003820541c0e5010000501c113030032041c0400c808500700003003200e2500d81e8505031030303003181c009034400c451803100420743e0340c0f890a0600450450409411040341f1010958101404420006d070411726001008540700b4a01003150083d840b0058100d0100d030003629040c200d0342c1e80c2d10804041110a542041c5581c2120240040d10106941d407007529241c0702d50074070200c0c0444441e03840060707a11100000c120130f0840d11100c961096011509842d015543c1080c0000d01307800b0844110721941100701c14013102103544803044d02503c1e4240d040d001c0d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 212045503 1250 212044253 212044271
    0x1b060c03020910020715030507050d0c1e030207170412032a060b0f0a08070302221503050c091603020c1e0a1a040503030606030712090308091509030d 66
    0xc00900488506075001086002e40149141c2c00181941c11140b1002900d80405400c035812400d80d00c5c107884480c08030f8000d1000c4d400169458018240c103001c00c0c6864401c41c107046140900c0d29201c142d1303181c04290300040e28400d0004d060311450b00080d4a202541c070b01481c02d00b10004a04004c1ca000c1c04101101c0569441d0405c0645a03a038103241d0390198142d40052400d00788010940741c881e05200c0c10701034040d00a50704001100c0c42c101c070440c40182c088685180c0a10ac1188418403421142c2080c42100c111107628070720a15101e130303000d0320f01c0c0304801d405c6240480c509078074002d4071441032401001b0440519030050a50034030710030070324002d44c82c7e0b41c000007410301c3d0418200710f5007041c0020518132103800800048112015004516403216445441108079040e002520050500e03041040001c801d130500c503008540084241c03528029018510104004440c002001180011015410712050380020003181407000c58201902e040380c00c00310704003656841142c104180403516601c0300 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 212046753 1250 212045503 212045507
    0x403031416020d0b09010f0c020c060d06030b01031b0605390714150405030709020f070501110703140a1d0d05030d24080604020103050c07050f0c0a061b060c 69
    0x124000341e4080c0441c003c0180526140b10040c4049030280601d61910310a1607071240a40116003540440d81c01510700e61841505116107580182006141c00361035101c00800144c082c4d205074001c5029800c40e48004030b01354290306040c52154005c02c00c1040501400300322558501d440840001070316040d022004030101e0f080d0181c82801d110380b5140c0600c000004151100141e44400d0307003422100300c0180014002286102e000301d01803d50564000310090103803c40550050110403a0307001d0840c1001042d039602c03400c0d550b00d290014490030b800b146002c205070b00f0400c50342d09103100301d84141c10500c00c0e120003800500a4081c01d034a82c20035502c0e545068441032008102243c200c425aa9218585600080078000c010000c00885829100a207449071882c10418144c801080141101c3c0c3c4890b00110060310001d459009440c000304202e8000480411902c010483c004000e440c1e084413800c01c020b8604800c0c0d0280044c0000c440f24a044410700040c4242d140343e000d1400250b4500301081 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 212048003 1250 212046753 212046787
    0x6010f0f09180b0301051f0b340302010c020d05071403090a14011d0d03030506011e0e0306010503070303080705030403050d0603060b040501090209062b0e1006061701060509040e01020a03020c0105090304030314 92
    0x1640c0c041190003030000000c3c010012721580580260000d0107080d20000c8100e0351031742c1c08010840012010701980b000104d6101c449103020b07030340783c2c100c80c1002c0070140080d0b031b020207030792240044250317240045910b035802408403844c6c58281071038071000420b240d012030410240b0000003406c1641e1200000c03c00c1e8020b0000c1c48040c1054040003e9180204102412101c07940700e40034401d01c901e200015480c60300181d0401540d070715545008464480c840b041e60160400342040f414808117029401800700b21788903481c0194020040458140502c0003448219203040e00042907850041040c62120f0b2500011503d07005003407540000e03602900842010b0125020038400e415034101450181003030800500b85d00c0c040b4034460104280c540c0e07183c0584407080c1c1c1c80b006004229110004101c118001c0c0080c00e8101ca000c0e0020030301c5818048910b08a0f8410301001c000b083d4041481d80d42d07080248940ca901c40350110047d86060308544014043e40c0c00360302c1442e001c60f80056030382d105602c1021 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 212049253 1250 212048003 212048047
    0x6060d0507032009090603010510060f090e07080f0a090224040504050a051905010602190201020f01050f0709080705030c0904021c0b060111010506010f0f09180b0301051f0b 76
    0x911005010007080c002c0b0940d6104021307040c41030f0084000f02e0182d01d018031556024103204007200002030320b80b0034107591005500d0b03410b5013445410326002418250030801c0f248155026507403080d4610b40030141d41c0008a02a01500c500c1d454600d600005884102210300c03000c02c94500910bc2102c010302c6240c0074490b5400c840c0e000342c249010301c8180410394000d0b90003003e400641269081c285941c07541114024820240168080a072410900036208175012800e130040c810340752074074445640c6909652040d140d042d402440f841c10800d856500a0082020b0304840b405041d940d840c100c0065500c030549ca011a1040c0c0020700818219035070341c4c0d0b451640001987c04c10041d00c1e0203092020001e04100d40d0b0078045002420327401609803040c0b03c0ca62062505031102c055401d5159012200c0c240c100e2080c0c5c082c44029107003c00c2560405000048194645002250b5690202d00341030135100040c01d0141803131201c5a400001c620030b43c8180c02611003100305039440d0400c090b9800300c0156514 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 212050359 1106 212049253 212049281
    0x2d04260403060b0103090f0c06230405042f04030b010f0803030f070216030c09060902030907120804150c060b0102030f070201030504050f030a020a030305010501020606060d050703 79
    0x3a203d140182010b14002445650907518003000c24281041a500410b190304100203041c0d100c100c0500e580d50a00040048480c1c040c2c0c0b420769401640161032007691102040c0c40b42c01d60884a104041582e410524ac4440c0d2460b0b196055a015010503500208002d0001c00c41d1010012003034100c440000c000c40c81c40d941c03410348154180001e0220001c5000c0d594002c020300c01d182501c0741c0694050585400340600d4202250101c0380c0c10790155452034010710401c00d030042c0c0440e07503000b00e07109072442d608002003078503180c05540b00780d41140380300d000700c40d0f24101d01c1c940c0318001281c1280304074010410050030400590b501d000c1c0b0400c4105c0e80391704001036001035120350040364116110300101c1c0e00b100384805519003181c2012083c4801a40018690420315034035009441c0101800c0c00a001981030a4001c00c085200e50303000344200680307500c04100c44a20952041099900207 = true := by decide +kernel

theorem cover : BRFrame.Cov 211870503 212050359 := by
  have h0 := BRFrame.cov_init 211870503
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211870503 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 211870503 ≤ n) (h2 : n < 212050359) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
