-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2326
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:22:24.110301+00:00
-- url     : https://prove2.me/submissions/a1382526-a736-497d-8296-77a0fd9d4dc0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 418165467 ≤ n < 418345323 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 418166717 1250 418165467 418165469
    0x1c0c1806061211070f02010302090d030e040b0105190e0a090c050304031218020111010e01090b070f0c0201090b0c1c02011401050907080c0703030b060a050a0206100308030106200d0207 81
    0x40000c02c1088401c060018500501d406181d01c42400c0b49407072070540c4ca5030320a00350407400301e06240d020310400c0301598a509186650901076120801e400e07000c24100811900c000c43e1140c1805018040d802454002450342e04805a246c1003035030401481000040e0010550303440007660700d007821142c400e907541c03220155000358403070307114880490010b4000900741d8140010700380800a8041a1070090340c499a8850900e448480002803101082d56002c3c2c02d483c29402c041c2c0d600c0b50700740c003844211548466882e1400e6110326042c2d4442c4c00c55800200090f240b4172032610310391000702c1c94120081d4203202402040d010220040c115950a900181c041c00d60058841880a60708000151609041c04417910480c0641c0e00c0d2145503580b881d2920b40703600705c4001034040503a140400e07481d945811000704980100c81e25465181e00348200002c6ca8a01e0043c0901c100c80b040c41800c00001c2c41500036607055502c01c3c10401300014410307000e54410036200003803180354840e041c5248203080d001300d0044 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 418167967 1250 418166717 418166729
    0x10501110f0706031d06040308130206040b03010303020607120212070503190e0f070902120412091a040302040f0b030c040c0201092102060105031c0309020409060f060512010b1c0c1806 81
    0x700045003685c140703070384410f012980034022508943c0042c1d83c503400700429600c1c0b144000c1c6801d042c01d8851401080603002600204c1c0568400300910000e550400d16070b0080c00500c107030540c43d001c0a45916045410090241c4003440804004607020511a181a084504083d2270800070580715505081e5604003040e9800d10358003e00c0b00c08221610380d8022a01e070000540c0c03019403107459960b101107001001803061400c20400420119403004c0d51420441000c5c8645006510f446c110300400040300c42c0e101d40c5405851030001000c000341c03804140200c3c82c5108842c0007560551481c4140c2c00742c0300381c181c0100045036070032600c071025154407003c02030042c01c1d50850711582c0e250401d0690340c148090150f4411402e841e0769144451281d04403002d0340303201400104100360389039a01c00584808402d84101d0340e41340d000511071414003207440d0b500300b02d06500078840082000003240407131415078043c0800e6980480c48400b4044142c0f40704c0d000b080400108505c10071403545000080519010754 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 418169217 1250 418167967 418168001
    0x1303030807030e070e0702031b010f0b0d0f0b0a0b0a0e150d03021507050f0313033e0304080a08032505040b0306030115092c06010501110f070603 64
    0x1140d071a61292040d40c07031030b00120004100441c180080f491070002c004200d034013140300411044c200600351198030085002c0c100c0c004078241750541d0400c0c095401c0c2c10407490017909000480b401140f0f0174143c070001070303400c0020000a0740303428005174040c1611440c500c1d045003c02000141e11820454080d2040040041528942480700104a40383c0c0714100c2c040c0c016480307a20811411039040d03141079000b490b00d0800c0f41c5400400b2140a0803030304102d85507103104c0c1c1c1c001d0b250002d06401c01041e100080d5180141d8042c061252820021650852400000850400c0300c0a042c480300b00b00311400b40c04054100c5405400398680014640d0080f10350095140d15402c04000c1c4030800c0380004d99031080b54039001d050600381600c00900b500010810365066488001030032111000321910f001400c01407001283d4040c10b90070940030701421107400501d0103003031a6404030b00c00d0082040c50542c1c40034a048015600710181c194900b1500c1008044039000e110000a03840d50142d024151400950540d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 418170467 1250 418169217 418169221
    0x5090d03030e0613031403161805040903090e180607050a030e0601030b062715010c020a17070816050402031b0c0a0b0708040b06120a08040b0d0501050d0f0209040201031113030308 79
    0xb030041c0380829231f030340c42d08a0110350f0310000141c041d548140012603221401c0a8203584c41d0b00182c161100700d403050f404551108810b001482c00c40e6401c5c2e90240d40b03011815003000c5990101640c0703960080c000010031201282000c1200d11035080f0b015141c0f610000c40f151561603080500b00c1040c256400f41c0b181c5002c520b04850b0200c007040ca0fa14103042107044081d69507819400a010080080c090350411500000c1d09005030b6540304518080c09906001c0515004a0034a5070301d491840e410040c0558444001103003a124034403011025500291805612034546a400750084d1018410031080b804000c03030260002c5e100041e40c208518015480e0390340325102c0b040143c91102c02658003030041901100000c009040030710068681e8480002180da030044aa02e5004c2c90740c0040c0c0107110404800194201400320314000c0701e02414044510928040035950381181c0803c001c0c100030700403501c101c005015a8001d501042003030396421515540d4285019041003140384038002140403a4078600 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 418171717 1250 418170467 418170497
    0x1203010b210702030324040207060c021b03030316050c070b0901090b0406080f0c090d0b01080c09070206070e0a0906150f03020f0d090f050d09140d0305090d03030e061303 75
    0x7000c1c82c024501500070b54070710b4036072010310600d40303190040881c8003441041030300510703031598070051904a0103002c2c0001c2c412401e06000b07042106411844040744040e900700700c0103a40c08070890b031b0403500b4071045100410480e802a1968001d41644080c1d90040c1c07040000d2a4000c00001c0c0b00c0342c0d034260f03500c1c0182e640b241002c1d03105020b280200d40003d00b0110008a00c241d0007c006900551508805c0e810505500c0018005c2c0820030000c44000d000f0500401505404220155440c40d00b1a0980c81916040500960300c000040441d000c000510035a101e1070340358281000c02030401401c00b840b10b136031034201c080d82d801036401c035100008004802c5040000d10900c250b0354908012400d6610b4054440b9081d0041c1240701c206581c0401d0111b403401c0011010884100ca40502d5103582c02080d1030b01c580002410495022240299014003103940000e60010407996142001c0341d420105070341e40d0604074000e02010215180314841d00082c0203031f81c012621807590940c46a959801d95024802c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 418172967 1250 418171717 418171777
    0x40303090b0f04090911030106090207060510030803070825030203090f060702120f04050a090501080d0e06040e0712092d0f0602030601050d090c140904030c020609031203010b 77
    0x6003600003810000d10080c001d40026800c0703045c600340106210074a50412800107402c4403880d034010003806600256900c200a01400381603030101034000314600b4a03295484540e490b02c001041c020400484800103581803003050807504041d0780429030030700e101302d804101600a600503201c2e0345032407080c2c5205c40350b00d0380d002664901c40d950542c0035016840020810950741e41003064010030854080c08007241e50344078015403500400c0c80001c00704481d450194103c0c10841c8203d620010403050342c002354980d840d13450031981110045808106196a256400c890f440c031a00100c44c407040c140281001801111480c42400941c2c0400303104150010b80d031480340140b01c1e14401042008a200c2107000700c1d4103540650381c0b045041c148245407603400d5081404a0320b43d20012192000305030020f1000c0542d11b03e1031501c4e0101503582081034145a1005000c030f00c40c0040c000c1c443e000001c6c0c5145992010720401101401c4d003408191256150802041c043c0c201c0b4050510464414000900003001c078 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 418174217 1250 418172967 418172977
    0xc060a18050a021002030f0d15050a0e060d06060819020301050606040f0b160507030b01080601050f030c1315060c05060c040b0d200d0f0b030319030e0a17040303090b 73
    0x110040c902c1071615824040200780c400544010750205000800c1c09000450080a0620104c18001118041c655180060884070381000380500c40c00702c001c4c000c107901c581295800c100101c4e4801e0310481c0e6443d051014010a4100800c2401039001d550055002c0486041c00b0f14401c8000f484070755550428005103000301d02c214000b80c02c049100300300484c0800010140801c00d8115104041d200d5100e503440e00141d03600c100c4000c2d022000400c59082d003407181ea400f404d0222070801c100d030f40c800700083e51003021000e0740748103104458149111100c9540b101d0721540041024070320003603031400b001d414020800810b80d194094070002500104040080311b00303a40340581c505092034485001d400040c1003222400c0030006800c2918a04482135401408081d0081d90003c5003100d83d90710f060081e0303072016020318001d1f4410b200b0515180701403034007606883c80714a0009806480410081d10b40f00035400040c2c004802000c20f4402074403031800800c1980e00945822405507503500c1000300d03610030 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 418175467 1250 418174217 418174223
    0x50901050601030c050f03090109050a150e010506010e130605151b030a02070e150d060506120708070b070309030209010608011a040623130b040501140712030915020c060a18 76
    0x4c001b1800c3c1e02c1c400001440e0030007500400020151071565a0510b04401110180c07402c01c40c60b5814100001d06004640e0f41d100d0b50030007800103090220000c2c06156411021501c2102c071040b80c82e00840407036011800402e0010510b14800d8001032019540e0f601c2980c0c180004810b40d401c5102454000044030300c1c6000a50080820610f0000940c15140e005030107000203200f0024616080da4800b20045e203050f004003000283e5081070b0081008288103206600c4494200000401180c0408200c10044a945810b0385950782201d203401c0300c0d40d2545400003035010310540c0c00820503d51000320b25060f00c5034031000c0710700312091450844850099101f40c0340000c2051454001c21003641500000c400f000018803802c2554280740080b90500300d8001040940021800700050341e409a03001ca5008980801c0d14030b0b00446072540c074194011051800c0034075440c0d0080404000c0100d85845124200d02421520b42d603e4070815502c800c020b490000c4010300380312a080540015461580314070758 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 418176717 1250 418175467 418175477
    0x4020f09130f03031a1c08161b030507060c0c060327110f0103090309090905120f0d05060a0510030c09120c0528091815050901050601030c 61
    0x491104000000358001d045600c0d452154054000094882403070b40c1c845482510080307580500d01e801024400c0b12241c1c200c0c0f1403080c06803c10054100101c01d00422504800025a20745050a20b00141408050020064080c00c2c0f01d1911514084000100f62482007055511440e40c4e03520071030f100790705150050070a0b03c800004021060217980984940500c070100329114403110700d040b2010304411102a210b520204003141111b02d01003600780013010007424104180085624003c003215001c1c000c5191455a8007054004d0000811400300b0203819030402c2c598800520031a006075030442a8030150701400c000c042401813030303c0c0300c901007900c5000d0720140c18140b2034034089000d4280c2c2c0240c4004e2150742d010102e0b858551380341070040e16000c3e5004448582c501401e00041004840404800c48000149001d00040c607004142c01c940c0407410215424501c08504000610000001004040d010305054400902a0802d600c2200380d82c00800042c4d89040c01582030718100311700200069 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 418177967 1250 418176717 418176739
    0xe0a150e07081209010e090f0907081606030b13021b121602010305040c0305010c0207050f190303140f120103150b0a06110f030304060b1002011104090504050f0607120b090402 77
    0x110a22020301001c0030140b510302c2141b202480401c000741c40070364010700105002010060129010481c0030700401000006040d52003185112605541d19401000c1c00c040d15611100004d83c1c40030040b05041462000441d034404420b048012050104103601e006409158810840000b84105442e4091480c8403090f581d09100da00442c010440180b0071a14051100b03800710100700300344070389608490ba075001407000c141800c042040305d80112000901c50b44500000d40200b00400008400312545800c0ca40c104a901c0240c090302c601401511401000c404154040a4048020001d040b01d0007044030903603600384078010100703503284440c1640e00400403a00401c05140b00d1455860000302d01e00c1a2485200c1ca26681425940261022b8030340c01e1b02c403441c04005103001405108041854002000042194040030703205000e98841da6407070a58620019040c41001e124182d004c000b03020941d41e242c50a40805409110b01c2d40781c040105191007800301840c14208607041c080c41e00101851459 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 418179217 1250 418177967 418177993
    0x20c1203180f0318040f0e03031009020412060209060c01150501110f070b09180f07030e060f040f031209031e02010c020319030e1f150501051c0e0a150e0708 69
    0x4070004c005980c205544070250b100d020028070030700794110201d8001d16620705003201c242e550004c01c0c2e04903191417071041004000d2058011a400c00550f805000945c481101c140010014001c062014480b5401c08003900a80950700400b5000d5a400b40c0f2500f000b41816082d00c0e56402440220740d0007588a14001d200e0540018080c040444005103074000d51407080ba100d0702405020f80713081610410240c02c1c801d405816000c3c5502003100b4400610043c942100e18050040c0e0281015207003075552140c50003850300c00c100318441d81e100b1400a0148150b10710307001b0010428826007070100b88a1103540c02d400351043c000c005c0c2ca081682d00031428050000301800300030030301e200341c6424140d407040c05001e07a4200303102c3c520281814450100122581d5012441604c1e40d2004500e003004100009101c0e580c4c121050341d6040c4c03000c06100d0b6481e030101c00c4007001001d40405441e540d102d01d6540c0002c2040d000e0092081103c4068240010400704401c2c965079a02c0d4016a0b8264000400c0340300c0d2 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 418180467 1250 418179217 418179247
    0x305180a12030504050901050d050a1e02090106020607030f230c070501140103030306050621090c0405180f0c03070506180603070e041803050d0209010201020c1203180f03 75
    0x684000244030034061559144440000c0e030003038508401040d00460200b003d4503190708a1801041c06071081601500c01c1d43c0c5141e01c5002a8800030051411400c9050582c00050031216180c0e60213020000c0d656100d600103552200125225800a4281080400304446502904404003500b10310030901507031094203208240707801450800d4960061041c0008680d090003886240000003440803495410750800500b80c8031131740c103c180a031900b0410b07006c00c14511030940d42240b6014000c48826202d6000903410607940d1212598001c0c00e02041c000001005850044031900042c12644d20f441c82c0310460352950240020690305804c464810061030409200808007101d806080440380f0407010005411078000b600c1410009113029031010203802d140c421540b400f44641c61008148801c0d6900403c10304c0b81004094845d60081500030b0789034000d406a0304680844025034098101c03140340e02d0f20a400454944d00c02e0a402400d034689001c01040303820034404400040c41c5042015080e004c4 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 418181717 1250 418180467 418180507
    0xb0d08090114090a09090b010b030702070911191d0307080c0f0d060905070e0906090a021018030f0b180d0c0201170906011502010c021905010605090a020306011205040305 75
    0x1207072680030810500c8556500c004c5101a0000c80d0001500c80c0460800c010680d01c141c002510422040007030055007031700052007031b0403507a40c0d48021072881d00c008070258031401145814130600c0d000442d0007101a4014102018800031031129581841140c401c0581e21281c0e441030800d550054a403800250038920f51a00b001400540018030502e9035641d51012107203515000c0d9443e07000720340705120600f58854200c0e00010500018980342c101030b010691242c2840f00024411000d80b0075103e011030040c11451243c222012a1040e4542d1b01c1c10008519007002d135003201c0341107103400091407980960341541e40d45c4c040c880041c06c184010324410b5400d030f00174540c107034140a42031a800340143d41c036000081c0b18160581c00ba19a55141160301e00b081340d4000e19500c250f9040c40940c00c681341d40050203040800913041c11010b0840a4140640107110300c1e08055003140707907001007107244401d82d0015401100282d0314040c40fa80020000000c940e002c0d14000c001800801410360100d1400301060 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 418182967 1250 418181717 418181747
    0x204021e030a0204080c0d121808010204080106080c1504060c02041b050c061536010305030a0813110409060f0509010b0f0303070c150e03010903120b0d080901 70
    0x106851040d03980d42400d50308201d5404040d1a00020144a200b80510100b98051001d48109400302d03442c0d5105001d0303514914401040000e00c41628003610b038035560f0600188801c0000715690f984823401540a40981d004515042c070448802d0089801d09002c1d070604403c04110aa04080c02d002040300c00300604141a40c2c0b00e80ca40d440f01942d035000061100400c4040d8a80e155900c04007000542098401040c4298a0007080140700d001d48981003180c6130f01e0f1604000501041c1803108023042a41c0c110110341c84220008008030401030008020249160a80c41d03070081e40d0b4a2107e118801e58414400030080500c0044101d56410550071940b14035106001c0415020a110001c2007210740440709101181c0d100da0a0100a082c0036904082c402c200782d01030742c036000043e183c160080a5500c540720402e21b801a501092502c11442c0741d5202c1d6000f80244680c0805080c004c00c6c0404641440d202d191030500500c2c0d0526004000e1011658040100c0b42090180001555054a201448 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 418184217 1250 418182967 418182997
    0x12070513020d020307030b0906030a030f050d0609050106080916060e0f0303070209040303020d060801060e0c0c1905030d050a0911040510030c03051b060f25061a030c0303040f03020402 81
    0x80400382030ba0025601c15881a60006441c03400380b01004480c0d04082c10440c002d801140700320700401d031722400c1d402000d866414115a120b11020070b80004004c0b56001d00940c0d0b151500100b1500d0b4846500c0e8000ca80381c004551450400071400300c01c4074020311a2201041c20088464203505081d0b10300c03d10503000909680c2400c0700e507000b10700200c60458048000030340c00944280502510312601c0c0c042d244400082100c2d80c00d040c0900b6034000d0213068110240c80204040c1900d040422011449a102850001c0900e100c0e14205507203802443d5541d00c01820500000c1c200300092048800080e00f20301c0b0440c4c030796510824807000700000b92980504040c1018040041001c440c07040c3c000f07611500081c0302c4010b8005550040c1c01c2e100160b03900c40c0034100103e504e81c0f405c841c156001c1d841b010312460307131400e40c034184201080c8200703000620103420b04142110794070650100014004083e0b0607501200c0c04074040544a10030341c01210345980302200300388054105640034081c910300250786 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 418185467 1250 418184217 418184227
    0x30702150c0c0d0c02010f0c031205040512070501090308060411030402010c0809060c1005013c0504140601030b0f100e03030f040f03120302040e040305091801060e0f1207051302 78
    0x80d8201404845414045107135a0020303411540d120406100c41989441d00d80c503e0080d640d0003d00d4844a0503000800c151224040340500c00c082c00b03882c4099941102c416500da641c1d28145000e8010800150045011500007801c13506050003506180203184001c1071441d6160740c0151141000c02405807041d01e01800070100c59106c0c100101104d50222000f403010454841000080e1881604100d01a0362080c0d48041226003403490340780300c2d002081d5a20304410700b00d100102200540c0d80215409030902460100310100d030181c80c0d01480d001e07030b030904c4039071005018000d07600d40e400c0300d00703800c210010a40101644103420082c044c8070028103803441d040d0200643e04060304103420441103a1444d6104008012008281246d0600310741819810245402c1403a021020300500140c103001700050300010f107685007407821000c8080040d0906207075071244001400034581184550013415a0000c1480502e009001110101e070003000070102e2905040500c02c200c1084642d180707480303402f440 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 418186717 1250 418185467 418185487
    0xf0e0604020910110a1704090501080d0f12110703080f0708060105090105070309030812011806031a04020d061b0212090901051002101e0b010e0906150405030f01020c0c010203030702150c 82
    0x2400b4401800c1c86c400540d1164101220b00003150010b9000303040f25402141240c00300c1e0341045600b21490740380e0078200526a850113000000d0f100100c0b02007241c7c0000688070b8109500410018006ca010403c110610340e128103081d6036180f0260ba130140441c00078803200c52151b210360024000b440c8030740751044802e5076a50b605111500b1100400501c0e21310600148203080c4017000510b20166030f0f0101b0301c0809c1c51500c0e4840e400c0b9003d510380022180c3c00f00060b0554940d180c0341c0304401c1c0e1160341000310002c035403841c000e0306402c9020700380103000e09140c8250b00201b500c00c1c0c9962040082901c00a64640010413000300f00503000d00e01940944140c0c40014041c921840100c40032101030707100911000107050080721503404050b414040165880079098681581d403660018040d10040000c00c00d10020314803c1c06681c2c026a81841040080640201d040d000780c08030f0803120045452203090341303006903280d0004448400050b8041540e40503040c1c40c10000b190040003c040e014901003401d9 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 418187967 1250 418186717 418186733
    0x61a0a03060c03050603060708060603041703100305010c2604171809060901180e011107080408060c071707111f08070801180e030408070f0e0604020910110a 69
    0x5030080c1c030241e0740c5004500d04143c05000342c50b031120088000c0d1031140340c100d10240c80801c010300118001c89010000904200c042c2c260f480355103001c0c1c020a070300e0b854010807804810029000444042d428400c030710b400140a0600e40183ca040b400c000d43d090790001c19900080a00140196200d601001111b0400c401c0c2600070440c465840794294061405007090003807e01000d04035030301a0091200401007a01010038010307a03000803003c080748206113603400901508240714501c0e00302c2d100060000030421000700a0046410800c255102ca40d160a0000346034001c41c040a00071001206060500c000014020500d07a40700b10610344590002601040010044c03c100d0302c04449140010440070f80c101610b06e07807000113031415013032540c10b019900c00340907039406000c01140d44400d91005a00801e10070f8401510481045441056603038a04442d04041c030f20a0f100c3c44200c1d03502103495070034503001b196485040030744400c00001e0030031001c44000500c1901d00b00d8a001b00c0b10034000080c08a = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 418189217 1250 418187967 418187969
    0x60e030f07111c0b0a0e06011a130e1008190215030703020706061203120e0309010c030903120207291204060e100f1103010f05060c07090e1c0e010c061a0a 68
    0x1c9200a0316443d160011001b164080c5000340300b00d50000b0010000c510766003a9a41c0540c0302c005507541c032003504c011640056507440d001720000b584d0003005c100040381c11000c080100c90755901180e64007032202c8079049060b8400e02c030183d04588007240e0070540c0bc80c3d2600075030300a6441d00c1c006141c910b10303454100c21140d15400c0181c0002078810b08000340740d8400502c03480350b10424000c200301080300303860035a24403510500c1030602600e204401c091500074070600000710741000f510641d1901004009454403224014100a02080391582107001c1106d040701d56040103a800061070b01004043c14641500002c0c02112065214200c00000710030901c0541d16003c41d060011918086130540d07001550100e0089460f00c85080c40100528007980000200701c1e113066541b03076618a200000349040c114950001c0c2c40e0f007400c25981c29110900041c09102c0f0f030807500481081003600c0401140c200b412000503600140346011001d000c00d01550100b00c1400e10803c82c03c01041c41240455900c03405 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 418190467 1250 418189217 418189223
    0xe070207140108062b0b04110406080d09030305030a111201030c0501140d02070501090b090a0b060402070b0f151002071d010f0e0604061a07060e030f07111c 69
    0x4041410040c840c2010318101d00ca1809003000101454034802180d0404840400140ca0301406000c5e524004804090202c0294205903508550b2a040c10715031102020f4052240c0954908580000c0410011880c1c0e001012030341d0b1000a070070310b591800ca03200e030000b074294020303107030780764414000e00f4a000b00600350072644607040c0015614500788450100503551219052214a08100b0a6180400e0840b04003005071030300162102018100300d40100007007c001824406800140b05000d1000170780c01600b28031a4480060f6541c90340180820f901401800808242e00c1c01c1c041003032560140c20351640241d201203030903410800c04000820121750340b80c1800c0540c1008030140003a10324003031140781c0f1f84100c0400c558a54501200791903103169603ca40f40050140401080c11641c8035004500240300d41c4042c61001c1440c0c016024250b404224100c1d542440d200d59008106004015100c46642c415001c500b04611616480000851991010b42c00480300b03100c8404107610300c210340c5481e40 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 418191717 1250 418190467 418190473
    0x6050d050d020f19030507050a1a09100b0d030305061311041a18100e0d08041508010602060712020f0d05041502030f010b0705030d111812060103020105070c0e0702 72
    0x34025006410303c80d00c4414000140c004a0b07001c206224107181ca043d49540c94034106680b980c090606c0b46c00d180300c05030014000c40e41c2d0203503203521325000708055004a44003020307100f0128403418180b007282c0c14480c016070490160a0400702080c01b9500c060b1b07000d44090100d41c603c1ca0100c13070100843e8038441c80c00c1040c0310003180a00000840b0030a5081507200000da0a2400c1c4008000c11040c501c50078585216146803010300c0c420b81d10030b0b800a650761001a140b825a01c0306450400076a0700940105210032841810704100c09118030f80c07603412141c26030081c00c0151240001217605074400f0b151008455000c110040821003040c0040c0006006050009a141090b19001181c684c048080180641c0144213100440d80005462030454243c414480d90320120307403628505501583c9141c0a0702807601c1100260000200010403800e490b290001308250103034010000c46203900d00c07003a080c940c0504018030042d40500001c00c11140214a850312035035980d602194580340032140903005030 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 418192967 1250 418191717 418191733
    0xe01080c07140f1b0a0803041e080102120732160803010f03050d050c030a050a09030f230a0c0b090d020306191505130b010509060f0c060702120a080a06050d05 70
    0x240030642413081c0341d00d0440301c104c0d07190300c0d1001c019aa402a03000c0e1940b001c005071101c50062160351000d00050960000954640c1e03050130b21600f8411080307900c40040340544070f94003c00f07510003440814482070001d1038a61003a011400c0041c81d0492050050742485170802840070405000145000308100412020140d0a40c0340003800d060001d1b96020a004003401441d00c085004003d032542e0880503d4005e8499840c000c0032a4110140e03030006c3d10030f40e146510f51060241c000140003c0c22103090344d41c21700d00f0052040c0c42d550301e000d6001400f084000102408903012641c020300000ca001040484112581e0b0002800c000b416a024442e85070b008003d40c64a0340035019951320500c914107103941071490300c004141450740340717196904500d54480c5a46042d80c068802e81310700b0781c3c0c0505269110900280340c10040d83c06201d6140103481800c0001d001c3d10310004001040c607001c1010f0600340500b442040d5150300010304910b001d19110713140440e064a5443d86008460b0042004220700 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 418194217 1250 418192967 418192993
    0x19030b220902100c08070605040305070609060203090c0105040602070b0f0712080a18020f190305060907030c05040b01090302010516150b1801061b1a0103210e01080c07140f 76
    0x51000f000344030140000d040c000b0f00451090001d0b02e4543e500320700d01051580d01c900d4111820f1186480081c001441d00031544184000307540903612030705001044940940d861401034840f40600d11601005911000060056504020251003002e042c030302c003070b0b041007000c2d91100d045203004030310080041c04010400c43e960300b0b14000c44158034080d80001e151a0100d4000c11000082c80c003583c0d000314400c0c840103150070803d0354001c0066030054240c80c5242000c2100940306d0003603200599140400640225652400323108108074440c050310741d08541440c5034015155a0482c0c0f61241f07100413407480c0c0002051141c0300c280301d00d80904400040c0c0d216a04100300742e0b0100c00300f516041e1103894006000403034003c040d1074140b8908200740b1810300190700d491406e503007120f040d003001c200c0c950000208100c1040c00000c6d9020f90b00b8140070b821f8036031041c12124800a9020540011115800326103403c050070700924029001c0c81d000310500703201d44043c900c2e094199000300315a610120b03d071185 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 418195467 1250 418194217 418194229
    0xe0112020705150c120103030e120a050d0e0301060b0d090507080d090914041211010f181205030c1e09060a0c05060c1204060f0e1c120219030b220902 66
    0x8081c40201000d4200701005c000300c54181c00500000301442220005985256110504003540c04a0b000c110b6000c20b8081ca4141d032516804000f2401203160000e16001070303d13040c0140410384203080311442c248094804100d020709030000b41941d05000c1c0d81800300f40030740c051103000300390070072038a42d401114541004842111400000700c5a0110700205110008066011500035282a0301d404072040351102d0042380100a103451411042c4d140260007031034444020403440000740280b1440705821a030380c8040da520b00c4120b40a6070310300010010a407050007507420131441d003060301c0061400d0145900100f01b09500c1508507070041740c41807c0f1001000000c00066902021746841d81b07042c03885003c8050b14540001d08010405501da10003120710208039405a205c480d0311750300b101c0c424030f41e443d403190760a130807005014002000c4024004d0090424000c4a5076519840004061a50046421001894200c513683d07170200300815040521030f40c40348208001400c041e00000c00c01c05501c10000 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 418196717 1250 418195467 418195471
    0xf07050306010603090317102304050603030a14070602040906081b0a1d09010902030304120b101404050a0e01051e1501140a020f0d0c050d09050603070e011202070515 73
    0x201301410560050006a071042080404203a40180c5d4085a1200c200c84814401c20342c104081c105040900140d604140b101d11303003642c010035601048151111024589c880c07181011142c0480c07100f082000f44020b5200080c420503005440040c00c042d2901e840c4010f4270b0540d800900c541e8840586000242c05809401c20414401c8444c0c1c84000d15000000c01c601264a51002c0c0c580b10002c0000c20b1060290055501c044e40141a03070358072a1991551020401c505030141d5521401d100010704110750140407105641c00d05204403030b225501404c200180500510308152140c65000311181c41c0c00900449010321100326851b402058200080a041c48004008542c0e16004144801c05039800066072010000c0303140300640c1d80e080e40d00b4103a20704200810001c88911900301801c1c54240d01c20305045e4041d2080341038803201e0f440342034100c5444426000e01540034074104081303001503001e01220504a0810f04003225a05600c000100490308003410a84190704042001820340400d4101e4903 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 418197967 1250 418196717 418196729
    0x7110703061a220c0e0a08161203050706020304020607020a060509030d020105010e0703090507031b050f06270d0c08010219110c0d0614040c0801060b0c1c0c02030f0705030601 77
    0x9611001c40d0015031002c2d40b040400c00f40f00c43e5032603031103002d42481080d1900400c039000d042e000180c0d644900d0a0742e1042181e030b19030449400f0000c0440d04c0340515040035902a09130780c40900340410343d15902c00943c800782c02241c0c08030007081f4400058946401007001002c0b603407034568a501100040c036050110102406045900d040700501c05030130000d82898101c00240b40c0000c1900d030f18603001e8034000c15a00043c01c101c0e1100c420400d40c550074100d190584000b55002c00c2c606050f03109000c1a8020050f800f207a180c1140300c002c15a11a1711502004200001c00340084071441da11380d03040c0c5d04c00382e030494901c6940005180c2c1ca668580c0c41b14144070052450b05040c81019038101c203450300280c081852160b0850726140f418000710f80c001480081c20310f100f8451a0400e032901280c1c0140c1c9202d101029428010000785c80702c24101a11110200400a0420200c91460710848480404650000e1181060320f00e00940c500700020a0010080710040825034180400c01d0710b0450164064 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 418199217 1250 418197967 418197979
    0x81504050d26090304180221090a0f05071505070507061106071107181d0c0a1a0d2405060304020d0b100b18040501140d0b07110703061a 60
    0x1090428007802c180540c00a482c80d210006442d1508600d00b91300c2660701210101d01601c40f641c4138041c043d40103143e0b00719030a01071152400b650152182d0000304927201c0915400c0f00b585040483c09000620900502c01d40541d2401a180c0c1003444d0701d84402d440c1c940015901007005070401400b0042880600030303d0504a464070a182c01b03090f51008001d1080c0100320200302d03203150000d030070002c3c0c001410091420100003408006454001c1282861000c406001090720b080d00010228164101040240c030350920740d0304110b50300403200d0035585c1c00e2812910400000d1051340041c4590f002c0d0080342010084250f4244c0320f41c4410048640040384908820002d010050352101d4184800720b50104520380d503075480215283c3e5904440c1c0c8420b07454400000c40c11903101202ca43c0007a2101c0845d010003c0b0703600d50440403803446590542940001c034003410389002c10700440c9031560040300c1d8600b040c1c1c41c000c0f0100d40b0381000a10b0303000b01d0b40140c40300d45000307000d00c0d000c14101395030900780c0702 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 418200467 1250 418199217 418199237
    0x180204091401080a080c0c0301090308190605030d1107030507030b0402030f0303011409060d052b090812070507030807120e040b100815030f0607030c090807060e0109081504050d 78
    0xf10303036202c920740360703004015100010784072041c01c40500521803010307802002048211000c0c02c0c00752800270107c9080c11000c18449800b642d0311050301c207803000d81d04064000c0550500400080d41c5540380285502c80301d01c55401e000000410802039400a1741c03042c03402588909040c0306062500d0061616074181e80c205000602080054075051721400030101c0388003042d03843d101d0200741d130011245801303401802165003800c0550702c1c0b140e5040900c001060300c0c4000981c0c48904460b011901d0088004640190b1b41030340342c0744100006090458002c2058950480c2e40c0c2e9580941c079800000212089800c100107843d5040d0006d20744424480140c50500000384a00001110840485c4040050120320380200b44100410144002e0340b01000d001c40341101030031200195038402c100c4450000904042091007a80e03c00c0d58180121030320f050040034158107111050345c00b5050106a1410408001070000d180d45042003100541d480c4803420500506003810000d061074a0001c2120501c03400c824 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 418201717 1250 418200467 418200479
    0xf0908120d141504200307080601080604060b070f05030c07060e0a0504061212020c030a05100e030a0206010e1b0403030f030b040e070b03060303361f05030a06180204091401 76
    0xc60000301030380c104c40004948641100d851102c882c1400c90038054003000c420000304503080407a003401103400740c0b20354a03541e5401003040241d461a00650858803014044403001942c1ea040d4091461320800a980c145100344400b945040720f590b0011000400001140300300d400d01d44041c80242c08142d40a0003c1410029141d8503c000503078024048901c00380c0c40c0d85d0580c4240600a00d0a60082c280d0ba5500b0090616555440640c4100380704685402ca00240507040081240c0c1c0c0103103070740c01914150f031070040400380701c8c80001c01c4501011500b082d03002001006000074030180d8420f03114000d000301040350007001ca40c0703101c00e09401140307803204402c200240000c12008481d0840c0300183e03a80e681c1d1004c00d080d4040c2554000e6040100194507441c0c0500080d0903012910f80c0300c2d49d1000030384207003c22102d40d040c101401c80b21690020900a685d01c584000c503441684036601042c4696200303490200040c09400745140d0960118003131016a07018041e0a10000388802c4242003941050 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 418202967 1250 418201717 418201741
    0x60c01090b0106090608280b150423031518060705041d04110d03050d020409020403050d050f040306050402010c0506092109060d021b19060e0a030f0f0908120d14 71
    0x40d241025500c000302020b0700c4c07201c15401c030b003008d00c00140540900c02d10704a40302501d0f42041c02110700c0c0310990400d03111108441240302d0741c02c680080003040160958036090044480150404450506202e80c8a00101080042074082c1650344d0703490b81d40b41c0c42c1c01e0b4110f84042222030310920110074001404049800714403114641c2c00229440b8008541c940b03800c2e00e641c419076072804642c900104001500504643c060030880340140700ba11a07500c1190011582d5100d524080c0f940d130306081c0301c14070220300c2d282c2c0059442803060402018540c515192103281c201c0482e45004581d00c11003080300c91074100f5082c00d80340b003003e405044c02c209500380081d050740600c421142107540c0c04200c201ca144140e6041e0440186184181d50902c841c41d00070002c0700203000001e0f034005040c04a85105403030f0025050b181c1070340503034450034100694607040b5040195080c142080000c0000c021940c0c03c4184085401401c1790000513958410780a42d61081d541400030104500c4240030401805c40701c51 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 418204217 1250 418202967 418203001
    0x10c02010f08070306050d0c090c080c041809020301050406240303020307111c0605090727200d06050a050103020a080109090c09020c0c091501120b060c01090b0106090608 75
    0x50b04000100e560ba40b042100100110350005600240d03400000051042c090389660a851106000707020350b40c0041d00644285501740c504160680d41000108400011a1072040e00014000b5000c0340001d126000282502c0c42500c003600d0791940c4004101444414011a03c4070b41c800443d019519495602c2c00f94407401805c1c0c010f012100c0700070950b00d00b650742c1841055402d940241440c0f00031102d06003000188000c03222401030b880740c0c0307101080248110b8032012124100c0c02102810111011791807010f071068903617200c81c86840120701054075051b60041d00a038600e68000142040c0740904000c14500c85502441c18940f0402c6041d8040340d00c04a444c2c1960a061404513008007030f4a8411210081e6500241c0a03a01c08188543d04081c00700780500c005000711080790550700c1e0091070100303201e62290450301250148100309441001c507041032034045001001e070360601d003080c0402804e4030350072441101c6c00680e8400508c82260024101009421207180c010b81a14025203200086828 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 418205467 1250 418204217 418204247
    0x90607050f0306191d060306060a12020f0a080307030e040908030402120a05160503011d1b010e03011a130c20210c0d020115060509030708030f070c05010c0201 70
    0xc000b545130348902108030401da29103180007454076a541940d2050303041d1030440801c10544440402c01d189000544a8041c0300c005280161041c034105101c0e030700d0048410700f03c1e040b03078a5101c00401544c0b82c20400c2c00030b1043c40083c5648003510b240080202e051000030701d21035071a00d140140811102030039031b584207038140c910300d51000205805610344204000010305600c10f50f50b40ca5040714034103500004603003041c7c000b4421010108260314040065480005040d8810401d4820310300c102d151a03000004181083e0803401c80000100c1d017075990401c103c02000440c4800c7c9100c5041a00440b1080c11074100100130310740f076a01c002001c844c540020390740380e845112400050a20103009210407010000034441d400d503040070b414113040c0c2010b102005140201e0408140c454010f0103403081000038100300308480c90230b12100b0340d034a40042031255018402c119000c00d204604000901c1d001c5240c000080d1200340c1890680d501e03082d15007209040100d00080a00141d0b045200300c82007106c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 418206717 1250 418205467 418205497
    0x90f0501030f0b04051510060905090f0a0f0b18070206060607050c0103110f030f0103050d0203040f1a07020303040906180b03100f150e0f1509040f0317010303080f09060705 76
    0x41303908205103014840802189280b40141c00c1c41840310381c10042c44216582070b2900c42d091a500d0b4100010120100d0b0b80082c122080740c00988902441d0b400710f440c1d05a000c800151603185440400c0544842d40b81e40c0b514204030303200340600c06404020702c5602c510111000b91030890190b44003504c17003202800b014181505d9000d41c4801126034415210b9103003140340f800b912072a101415605554003031209031051700a03602c4400c103140c40401103c041d92642c41c00801c41c10b00e0904d103400d03210500c03e240b14040d00d060010b0700059900b0301c010401021580c401182c014141700c01c0d0342a807a01400024100360ad0588410000d4038082019000c1d892480c500040c8107071001d40030006010101404240d000b04064003140010700102040d00801000c80006080d03682c1003881c2c5035401c0466011984001e08800160004458100a0741d03a40e1103490500108958a0321060032100d00ba04110042140101008a03070082c641c04941d01c650300f1b02c01480035040c2000f010b0418411944100301c200 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 418207967 1250 418206717 418206721
    0x20a0f0e0103020d1103040b070e031b150403050f01060914011202010e1909050c07052503230114010b180a030c062c01020d080712060609090f0501030f0b 68
    0x1a00990507156041c40c3c40500303100c4c5d80c41050321014030b64402c8800321042c554480100300ca03030384500c00702400400050010000480c820440c0440c5412502d41c5551200b0340c40d003149401304a40001d040154407813401000728114080141c0d09503500350300311078030b5503203085109040005104106030440d0803807040744580303c20500040b100004050010703a0015400025a6000c15111142030201c0d081143c0c10000d98550100d042044e2040280150240c0d000c811150f003d03260000c0740303282c45104030309a0700c15940e03240e0303c0504072601c81a8500d850740c241c0f490010300d20000e00403002802c4c20070050040540c100322140000d80150000c01c1c06142d070740403010380561034088210b00a5600807200d005910307616403004050f2032040105440448a102007208c0303501c1c40358400000c2d124143c000e464081e10402080320b00490003007100c001c0007840e0114058502071407262501070075856450f0b01c80942000e080c3e40548a407440303103c2015141000400c08a803088070101d1960b540404454060303 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 418209217 1250 418207967 418207969
    0xc06110d0f05091503061305060607020405281a06030412050d0f0203161e0c02040f270c0614030112030e210105100303020d081f030f0501050a020a0f0e 67
    0xb41c007070408841e811410f400403200d4000c0307049002e1031140340b046564810001d082949034050b142d040c0c1d6495007081c07052000000500c1c0640100fa48000f8111583c010403c0c00d05001403946c0c40f09121103013a903920a0000f1a480070700c814a0403180c0140c62452071400c1c6580c4a410b420200c00500f4204040031802e001101c1c80e5420841415003900402d64503030400344002400144420080c86c042400328411a8135031400c4a12801600c00d16100c500d404c4290380c00344800f030504c00d100c0d2101660b4400300c00444014030000d2007079802e0b24160003a006103261800702c1140c4000e1700401d0074414290314110b900080301c070450341500c4a1040303180340d038280e514050728880582e40055609c90032348071305000c1e002c10408034114480c0300300b80203121503100c0c10301c800218a036074007003c0c0c0181c12403d29444040c0c000c80c50b482e00601030803034810b607a004c082e8500101c8201074000b100e5041c04000341606010090152507000316a42c1c41c114175144000c0030280030910f0840000c018000d60841800071 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 418210467 1250 418209217 418209227
    0x30c10120c020c0301110d06150f0309081e031605090a030212010617030304030f030246200601050904020108041406010f052809020c030403140a0c06110d0f 69
    0x420440a0001e0004404501030505187c0203c40f001c180300d072500e100001c60b4881d07100d06a095282c0340d21640c5450245d048124060880f0b00801d950441c420020b600120a0306064506d5041c11030f00d5503600c030300f400f5207540d82041010007118100300c010301030202540e0318540c1c800d0440740e049503e92920042900840d02500003030b8032000c1e045c03a903003080602100b000701c0214465442507403090f000754141c420950803400360038810b80310083c0702c0c00300072418141110301c0b00081c00c03000b2007003000301024422408103c2c009211840040c05150200c2ba507442c42860000007a40d0501c0500055030500010802e101c0700108082c1c100100007012409001c072010b928a41d0b0100d050032b075405980c40310329401070b81000e8450710740100f101034000703040c50444c10580c02500300301c01c1c0d1001d0510b18002d01403019403c01003900340b49001c1000000b0000705c081000e000251040c2000d0401c40c600c909141188102640c400014001e0722a8109421900418100880261030800000c5c060016400700e403 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 418211717 1250 418210467 418210483
    0x80c040b03120c0c010f0f09050906130c021629220e0402090717010b0c330f011a0a03271502091e0105070f0f02030c10120c02 56
    0x1d03503050000384010f502c40001c941c000030310700e00380c80b41c0300c02c4860840115510100010a035000a0170504240020301c1d2454030143c009100400201c14413250600c03480c04c0b82c4d400004040984c1c002c21030301c8110752020100d800204404918403140104044ca070b0b42c1420300348500000ca03684001008031082001e00701d40d403413405401e0205103110380c99021604902d801a20240d22402022000551840c480c5040d040e807007410403101c111176441e00300c031004641c00018004d50300b800740c1110a100c4a0002052070191002d06690354112511002c0d049610701020f4064011092030300010b0040440301c03040d4011201401d90081c1e03a42c8a801422401040600000725500e03034032400c02041c5607200e1416400450040055006001c00c03004890202e204039000c0075044003460444101c08061111400003208040c146186090036550320031600191407481200d15404200051084d414100540d00a1060a8032100301058a94170702400d000c04150420403075a40301d0360b0480c4031034800c2c00311007 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 418212967 1250 418211717 418211743
    0x5121f030302010501050117060f0d0804080d0c0c0f06231c090b0106110c0112150308070c0b090d08090f04021309050c03130b07020313060c050d0801080c040b03 71
    0x911900e038030380280079003c03c4c8179290008021100440200030442c8486004141c000c1c80e100d0241425020321000c4035421348251103130707a0b0a11001403641c2042c04003822101966660709030840c207e00e400249100b0075044808401850300c0c0c144000b07500a0800c440c880c440340c42c401002c1403552200801446920307142078a61151000e00700040b92540c0104440743c1c407441c1c0d044166070322070404462140c9082650030841e03000006072003c41d4041ca110024004c03c003000440e00c03144540d03c0440080e100d030701c1115601d00c00103110342400389005444011340280c0c52803a01d884544000200c00241c1614060002c050004444410355221443e8581200d4090002d540358003a582003251840c5183c810302280d14241800030303001f881c5500c21680300ba160080e900940e8103182d2101e03510000000c08407020340c4410090000c01902100f10b082c01072032250b4920181c800307580f402905200c090388940c0280000d05005114040011800d00c80344c3c1c03020781c0c0000c1d855004c00000b074541800c1d14004 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 418214217 1250 418212967 418213021
    0x3190216030903030318081b190f02091005010509060a030f0f1d030304081b0a05161401180603052208130605070b010302010815090a06061e0512 64
    0x8001c041e00241d03403104032406500c040201c880303149441103c0d0030764480014402081041500b40d03450314800182c0485000b08110b548900d10a244401c00321400381040e04c5035035521a0b410114070b081002180c0c001150074451b0821850040041d040b80035081c8554420742010419000640c800d50200c41c2c1120003c1042c80640369070b600b10380040c03103202410100083c0c0050340c01c80f0170000200b00c9014036440100c0c0361610301d01c40103003803065944041d0341030203008400c0203030080707003041240d948040c03011a8075607411882c3c40c0490781c0d809201001c03a410b000a04002c01d400c41003100c221320440c1d682e4140800c0660392200d00030b219010128030200720b10007040e5032006100300c02c00580501c00000f144801c4e070f1a201c60b02075409000d01800100b00e044031400510055208091a0f60442e0b40140d00c1001c140244000a5803c00101c80362030180c4c0d56284108400343d4010318030b425150554460003100382d0a0480201207100349544050114a0358000c505841c85e1101104010035402da48 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 418215467 1250 418214217 418214257
    0x80c071a0a060315021c0905010624030b0f090f0a02041206020c06060a0e0112020a0e130203060c04151404080a0b011805010b0403121e03092105031902 67
    0x440007008180002e940303868131004149a1054203100301c0e2203107403041201081407800b030441358000e400545d0742200d055407100c0300003e60964902d050402e118840c14400c2805170500d43c001d0854110703001e8644981410181400603840c2c801c54150400b542d0036411226544140b0302c48064407880c4d100180107040d0300906410300101d030703010b007111070740c01c074113860071a01c0300010000b4000f000d005100040b0300102c0100320014450851800c0284060a14102c079030b901c0100000e0b0b10003c844060000320207130310910131441c05000b10790b4800e019441c0541000e0400c01044400ea20545806041c89800d1083c00403110a550039100102000f00864a00d15143d20701680c02395001e01c6840c901d2011004044030091007405090306941c4803840041c102407841c5c903403880e010240c03180d50062106e010850503a83c403c08040100003041d0b914041303014040c43c03078000014440b02e040914455251080c0c142d0559000702100d4010f10103203192a5041d0000d56007400a2244000c040201117070484 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 418216717 1250 418215467 418215481
    0xd02040e1501060504030b010e07021c03090803010e0f061509130605060708040f080c030a020402030c160c080c03060f0403210e070f12020f01080c04050a08010e0d050a080c071a 78
    0xd00c16681f0814407111580d0340c84450450000e03080d605a800b6030049405460755446140d03203940c0002444c980812101580d1711080c1030343d4020b0704082c0ca40586181000320a2007130b000303c1608454165001c06503208818032036400c5004110710340e0310805045044281d418095003100d405130000400e810b5a80c102890b107a0030a501a1187c2c044200448030001241c0c0008549400505805009030640e014940c0c200002903000501d4091b50313200601c05401e070881400007440102d0322030101e0b400828100072200d494924904140f901ca03601003801c00c44140c0041030b4441d001070341800c0003164042d2103c0c883c0d50181c0c0340d4510201952130981d11744048a0300207072140c1100c8201c5e00b00403045842e00750080b41e8080455002c2d400c11071400040b8086c5d40300d002c030540e004010100180c00d003510b41c800030f002c0401c558048200790791903071001c822420090085000d21720790341c2816450070046003400b0341b00d81001410f0084451000c100d446c14018090340c1920040d000c3d2801085a2070040 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 418217967 1250 418216717 418216727
    0x4060e0a0b040506031203010b071a07020d02010b060f09040c2003180d0b04031812080d0b0a030f030c05100e1e010c0203090d050102070f030c0308090c0d02040e150106 74
    0x601ca541c41035041c980803600e01d0902080301c1c2c0e81c00000b440c40e9440c50703007081000781e5240d001000840d039180708464441d6481c0a40b0150b180a0442980580264071070014024251100540707241d2155500700070b55000303461840120b07148998190390118603282550f82c280c80001c11220745580c40c203060b058074030452001100412090400c2c031040002040c0000a05c130100b0404407005144c825018085008a03010b415a00d69203440d2081c0780c44010740341c2c61110342c980f0300c03210200c0301c80801085000c0c07410300c07074060101105030654501c0c007401c0c40c5840c3e2080c803819400c000f5080c400740d580ca040c2400001c0c00f100075000018001404181c6500200d580e60740c090201d19201c0c412260800340840006000705002d90403d58001c50900c682d0728104000d0820100e411640ca40d42005108000b81c5003211100c3d850b4000e44445007019074600f400760014a0045c464003042d0011681d01c3c80d103540c0c15021580e09501a00c0019410802d1262280f0f800e40010109454002800c00010341c66440 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 418219217 1250 418217967 418217981
    0x411040b120405241f0315020a020f03090a12080706090f05012433030e0f120f1b010e010f0c03180308041a0a0f0e0604050601030b0604060e0a 63
    0x240040302d00b80704810388404c101e6140c2030080d0180c10503a0004c20858400f010401c0e01c101e03450708840142680c6c961303c0c8840c031030500800c140b9094001c0307031451582d41c0500913804800e072460017841c6040306a400058840d0f0050003904510030342c04201409000c5c0030002e0ba502e445c1c0c03111081201c81c6142c00c003400048076000c4112619821314202c52030141041c0506c840ca0700c840181403500740d007030290320b68864480c038a1070307080c00c06036a202101c1a40100301903020030b07401341c50001e05003241130046414115956000c450755444820f00c1c0b90500e03038003000c0344c8110b200200a292592113002400381c10b03a9482405401035802c2030b5200c0705c00078040d0b1103012210340a6030100460462103c0035010381b11403000b404400e00f0101034003404a4041c400041c4d1262040c4c04c1040d0381c1c140c59003031140c040002d680c1100340c0c603650a110308500c01c0c10300c00c1d0741464801d80010112450140d0710380d41c5e5088140002040308205201052498070f46410400250000c50343c450100c0c540740c19080020051 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 418220467 1250 418219217 418219223
    0x90403050d0c090e0c070c0302120f0a060e070506040b0703080a0603050f01052a030a0506041803032c03160c0503120d110408120702012a020301110a0e0411040b1204 73
    0x3c0003011175186100e29046804066225100001c450b142d0b03020030503000c4491400710f003240a07440401e001b0190512140b4200740c82443c000500c0290294041c0c0751043c0c0307400032800f5000803c4140003549204083d00e80981d41840c0054055940c1a840c0d8041d1040d42d20081c9188940c40c00c9041101c0d041d0806c500c190104510b05d40d500e583e07110b1501a01003180d41c40326410340c080000c1021042c080d0000f0781d2003000640080384a0000c1024208502505902600020b0355140f807400c50012154002c1d1014040303104003e03003c5e002d080c04649a03c5800304c0b10400e400c8d450890010080a0319004000700030080c141c43d4a9030000b640d1450fa580701400881c0e049141680e404c840480310b0054a090320912002000043c004541d501c0a5034085030040c1d05000403a52180d03041d84c010008210300380b01903604264455650310526003500d1b50822001c0c841d540038040070100961101c036400a101c0125004103842d040901070003900d1040760042640c2c003c0008150142d031178201041405284 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 418221717 1250 418220467 418220489
    0x131814010e060c09060714120c03070b090a02060909180102041401110a0b010e04080720100206090d051e0c01020301150504030b0601030e1c021029090403050d0c09 72
    0x1071021483e14041c0700300c8600c10b42c800401e008000210b0414040b110320b4030300710ba0495402100395030f8101c0c442d4011036000d54140e0300006d070340420085011140c139000505440180810110359001903002c2c001c41803981c1c040c9100d07a0000f09000700b031190f00c030151505080210b5a460300d68002d5100800000141c5002c02e00c018075060181200081c040070b84c5400074038030611a4280080044034000c081c00c00d0368400d03024410718000c100d501400501e5407aa12020000240f102c071700b44401380c40c4851600013503401540812900702c0000c15080156030365031078055940c1400c070f04120114800c440580100013030114001c039280c103055004605881c02120310a211001400040382c041c07141d03000090600c07480b503000c94188d500940049140c2d000550941c2d02464421042c94207042104070880700613402540425000f01081c800c610034100006001d45256000d20046c1d0466160085014002c611202c00101414420320945002500c00c0c5d0b0f0600070250708050090007003403070b0700450213019 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 418222967 1250 418221717 418221721
    0x20322110a081c030b0d35070c0905071206030f05060f090d0e0a09050f07090b0f120606130b04050a0e0f2a0f040305120702131814010e06 61
    0xc01d0000f0035080304100c030048440808500340c400c9000c0d1103412021504030316544001720001340307010600d0502ca01c10b00c0c00c0c84440c003041c140840180c0142c450f0300445903410010f0314041802610080183c0c0e9060030045929103d4a0040740c11602014002a40e58642000030081001c940b103000313116030140084449944a1804201c0000c00946400302c1c036a11640071000c11500898400004840081c1403494469660f1300200544d4403c031502c04107508a0000c008a80390007404d84800f03072004807032030b904001080c3c82c1d42d01548a8045001d054021060000d4841c2c0c0e903410480e81d6200e401e0440c00c030300f1540c80f091810150042d01032244503100d29a40031a00a103100c446a02c100000c03a00c10309651101d0f503480c80e003804019000b11310010b903c01110030291383c0d070340200f400100070460349642c4c9155080403401c090701c0641c0d0801c140020000c100150343c4440841c1441000c850b4006600304460354559484107126200900b8aa80c01c0c05241c0044d8065100c00500c0b95420144e600503 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 418224217 1250 418222967 418222979
    0x60409090c05040209131e0f0f050a0b0d08030a02090a080a05011b0c080a090b0301080d0207170309011223040201180b1e0d020705030702011d0a0504020322110a 71
    0x19010b8500080c0d08546c44000c00311040311070750441c112001c008210200c11540801100058800c840000c101441e03c82c449420031251328407a00c0d03803203c0f548204001001003c0d000807020000e280340038200a4010002c00e054040e02c2d030403113801000c01003c01345681d917104045501d4024a440c140c80c40d5107000700c00c05a2228192050010499955444421881d40d0f0b44103503c542100003001e0800032748030004242d01c2c99082c000d6010317000200040c485482c884d0002880c00c2c40c0f5412200a071040d01d4006600c0d004c00200360b0f8101e020900b00104081d84110516000300f5140980c10012180c1c1d10f400e80d0020b0210a5080c00396000b0307a40e050f50301400c903200703016030075080c4070320900b91008001c46000205640d8500300c06000e1464071b2498aa10a070310481070b82c0003c44103071996080003c50a04541e04103000c51410b04100c80861002500d48000803544001c5100d12402250000009043c0150280030741002502142850014045e00c0c140031901c2c00c90485001d0041c00d40034030118031 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 418225467 1250 418224217 418224221
    0x302180105090c180d03030e0d02012a020a08040e1b0909010902031e010806011508010b04060c0f0b07080a050601090323070302090a0906060f210c05060409090c0504 73
    0x141c41000d080341005440c0d2201e4403600b54004400e410b411000000c42c0c0c1200c0e903410114002060080ea00480d8040c24483c4035401d2408400303020041d0380c9001d02d00707074000c918414918180c42c42ca90220480641000e13080c0d0400181e004000c202c0b000014000c6480c103201103840d03019110311021014070002c40348401c8c1851003503580d140c1e481010ad01c01040902455002103600078070038440c10504850504100c10074a400f80c114400039000340006108d8140600307050b880604540ca42001c1f15450006600c285120f5409007008000b034a2081c84240144800e203201d015500c200035003428905410010300307601c0c0644140d60303030038180008500b00d0f43c0700310407690681750070005c4844140550000c000609078800c25404441c051100700001582e100c42000d44121035500340420040c00d249001021100660803042004103203001c03c2c46100011a100c8070160104041000d0840c2c0508002000055640c07201e684110300060201d201c088030b410000003644112041030a280d114010002 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 418226717 1250 418225467 418225469
    0xc0c0302060406050c0910030603210f141c0b030c040203070512041505011701050f040b0403030213050603090f010b030102071a0712050a0507020613020108010b0c0106051903021801 80
    0x80180e1180c008100070440e076034080c1e60008517140c52a4905105900840c180403034105401001c03030340c0c2c0d4a00b0800d0101c0c804061200030241550264180200c5a0250202c1c20f281840420800149190a00058103004540b0107506000640e5066507050465001500c012402c16001f0300890360701d405039040c640207482c011031098036031504004844140b06546a801002a62071108500c510315460809105042c040c0080240c1401c01c0c8000d020400d003540d4001c0e0481051149050400c40032454810800c0c2d04107500d071030096500c0c1c058901c1d40e2036001c050740000d54040000400c1c00b29041002032680700f8215003100a0000c1c01c100c0c0101801c074040c0c41340103484050b004c1c00d29920a80d80c034a82542c420814205280c2c0302c65110903a0341198800c44581000a43d92000e10038090380400020b60312402800300e0240e1803182d54002004660180f181c0643e003070703000c510002100800e402090103040085c1103446042803110403044a07001520082c0d0180c602692030071070070041074103514 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 418227967 1250 418226717 418226723
    0x6140f04050906150d060e0607090806070903020108070507021f120e03070305090114030c07020a05040216080d06030503070b010e01060c0305071122140114010c0b0c09060406120c0c 80
    0x104803a81c5039044c038807401c11407285599100b0f5920080d003002800343c0c42001810300e005002004c036854203241c00341448255401006841d40003100b04044e142d8803503010816030b81e081ca840c03c03446d1500300301075030103000301240203511000384c03003030100c4403d031006c1c000014400d40d60315003c81d46400b06901044030030510114400750410041e80303001c24044d1000341401e0300c0c10314080580704810040950035400a8405d01c1621000203450019803502c586c07400041c180c1160110b2600380b1082c0d81c9500005601c42c001e001400108100a0103c1558403102c000c58202c1d05403030b0b881c0310f94609622204824060300c5000c40303a2400100318280f244503031240050f0b058540a00d040100e485100704200d0f50072000350303c81849550b001818031110300e000c00c1610910408200b0b15116030303880c800031a0503004102c000490741082d1000b41c0c0c0c04500300380c03e0707074004000c20340d29118000c26401c9403003042d540f140c100070300040010b4525448400041d0140a01c8001c01964044a500704c41101c001e034006 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 418229217 1250 418227967 418227973
    0x902030d090e181c050301140909030306010309050c0604030b0907090605030607080a0f020a170a110702130605150c120a051210080f16050901081216050106140f040509 74
    0x1400a01c51899004240b00c01e10210744c0100e49054034060488074004101001650100c01041031a9031074140003031452084695040614001c00000d540c2d00008064a04143d2511180020b00501b440316000e42500508400d6581c0d031241040340b0b20003800e4414241c03078414104009003510b01481000291500100501501d440c0d400c401c03a20354102078074540c00d41ea9101200a00482144000c0100d051684c4031484803e905408440e4440d8000300312454183c08c0c004101c0385064a001240c428a0b030455044404400700c8c2340310001040a0b41105d50442a0502030706100030090f000b614001900c502168a11180d1482c914100c0c00394002006c04510140071001030710103000e03403032581b200e40040110380c01a9520a89807426401c071f018600c0c103801c240803510111155401410290030241d4414429503d044000d6565403c03508124100b641e01141060308002d502c0c480a003005e0304000203100ca06c1c1c030340c152400b1003089900494490342c05150002c4050409019203485101c4480203 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 418230467 1250 418229217 418229221
    0x1050705070201110d20070e0403080702240c0d0f050106050405091e0f060d020310020301170f120304080d050411100c03091415030a200c0705041104090c030902030d090e 75
    0x79114010600e1006c40c1031901981d00040790035084008414440d500a984034181c038102003102038104001c0840c0c00d681c1040d85007901484c40c04038030206401c086283d444558480184030240010304041c441444054180b10001410365403040c060029030b0f03822103844815849500c07101d40380e420070205a4090041740d00004043e4810900841d50244004d03000c100300d4055540080e05014000407201082540400103000c0c0003101c4c0001082003000300c1c000c00324010750182484e0b0b1001c11856412903000700000003410029070b18143d0f000c1d84103044060026046c14503001001301f00501d81140144009069640d40703920442c40c038112300d900368550604184c1000e000141c031080300d41c2003076000441c40801f440d4a42880c4010352203111440800500180b00038228032800803a000303409401482400001003403c800b0443c03004480044600241100f048050900b080c0625400360421a15000c3d41566050f0150003401c0421310032030607552200c0c0c20074400e4a40f0480b50103018080540100 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 418231717 1250 418230467 418230497
    0x80c0a0c0c081e0a1212020c01050415270206130e0a0f0b010c020612100b0c1005090c09180709021b0105071b0b13021f0f0c080d09020f0301050705070201110d 70
    0x10f40c41b01c0f008110721026241030002142e003420346605580c01c60310300c82144d01c0400e0a55440c410b0080c6100428905125036000c8407825480604004020f84118000180341c00c902d040d00c1000001419110b286025a2401c071302e42800603d0203c2d04a0031443c1407842e4850651320590f001348009034010141414100c41c4600b0a1448500038103d40003c3c0b038122000ca070140b826006013040d040c0f460000c1c00d503000b20180200030f4880c007400c0c01c5481e61050351341d40003596404044e654000c00c3e820b1a09504503134026083c0c0f4103900c1d03a211014092000030500c05665040318003000c0152428002d001c0780c2c45500c01166400e2640144c4e6408007000011134002500b40740200d0f1b00038407440e2000d610303580690001408880c1c80d2a014841c500040c1d010314910390080410002c45034141421481c10340b8980303500806104215480810366a50201c10045503143c81c1000d0311341c0c50103802003000d842c1aa0014000380c0c00301506138041040c6144008480c0e000041d000ca4500c00b940e104540c4a43d100 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 418232967 1250 418231717 418231727
    0x71e02040903020a03032d240f050a09051312030618240510030b210304080f01090507031112100b12070b090433140303030601080c0a0c0c081e0a12 65
    0x3002300804403084840441d500078107007540400760026140c3c608d180303498201005610105940110811400d1104200c1c2a050764441c074581c15420244042150306032204c220004d14003070b000b0b10325003114013030480e480c0502a41700c809800c030001c4031181401c005e41d005480c040081d00c901580701c40703211100a651440b9800401010741c01030140003103003880c5050602c5007403049551a4003684042420040204204000440d161044000700078070310403500d40c4d0741c503040140400340010403240d80d1040703140c03200751b0030040300c0d825a000e46994024a070003240251802d48d040e24400d82488440020050380801c1c11000c03217410107a110f143c01d20810511004e003010340071402c1c000e004280e11081d40c1d0b4006d501841c4561030b100b580354050b8140441d401140031001001344c000d070700c20b1040101503600b00f013041e13801c0300a000a80303072600400c1c0300482e603640c5c000a00030000320821200180211000800c50524007803000180740306000c1880a550314010440058840c1c0258010701c25514028 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 418234217 1250 418232967 418232981
    0x50121021e150702090c0301030c1203110319020d02030a09170102090a0902030613020f0d0e0c03010f1a04090b0c090d0c06020a02040b03030f071e02040903020a03032d 74
    0x1031269100304001c00140040082080718051038100041c0c0030304501c4e1401080c0c1e48040f113480824155415522501c4c00c0fa0024003400d0000511700c1040c4c01854000c001d0003214403400300460f59a0b07400c00c40d20300301141401800350b000d40300f0420f25191607800403007907502d8400d450741c591404500e06140840006142c2407116400c1d5400c001203e2280c88040c8810080c0224440150b40c9050000c00c1c8000c1c2011488841c048520602590920001800840e892000300500110381c00b064510140d05161400c000250b1542c64081b400d0310541d03640d0000790501003ea460042d45495440074001a1180f0719001407102c6003100c0052a166000c0011708246030700680b960181d03c1d52070b5215030310380d252a000030700544d010400d280110b143c24004c501c0c106105902460070b16106003820710b6240561680140000b8004803101d090700f114481186505030010000c0c404408541000b0351134010454040d030000303003043c1240c5a125684100f6403040d0030001c1070b40d180b0004184d2400024205 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 418235467 1250 418234217 418234249
    0xf0d061a010f170a0b090c0a080c030403051801090e150406090507080610050c12040e0a0902010207060f0c080f030f0a050f0103110d0605090f0f1234050a0605012102 73
    0x9184818980b5494048441e07104404a0300025506e522320030020707000740c0c030042116240e07207010010000041d501c07030240e80401c001804240c02c24020342b00142c03580282e907000ba5030203a400f01c042004481e14410f01e1064500b095604004540d00c0310b0110050350300445800c004200c002c004100603040081e089201c0515920701141042e401e0003100e800c01000310f183c107009100120303081c0602508a56100e4002c61500810000104c0650020751035032428492a800d0108180c2e1441e1283e00800600303030016440a490f5903900f0014a04d811181c20903a4000445540c01c400917460115910880b801030384581c0c0c2250039a0300c0c41e9603420910a0080880b600440810f1480300020003d0140314014030160010b000320081c08c207400e034904600700980c1ca04940c0440300180d5441c03c0c00e0200c0d403c181c1d81500c0412a5056146200c0007400c001703540c0f0421a9003820000c0501c080414101004c1348114000d2140380d90364244031700010509101603800c03140d080c504000510b4050501b10725204 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 418236717 1250 418235467 418235471
    0x200105040b07240e0703021e0112050606130b030403180f0b03070507150608160f05040b04090c0603050f13021f020c03010e0604050706110304140f0d061a010f170a 72
    0x1a03043e40352400d8500748204800c4a0340440000e00071440c2610000c2c00441c4024100c860280c240000244001c1c0c50201240340103036200c01007041350b1a418115141c5070700040004030010390700c84269209502c103c40580015041c2c04018101d605404d56010459925014080005040c01030304011544058501c2003804010003131800010322500e0508407928007101c00003900c41c546030090b420813520310004a40549840c4050102c80580c0000d502a504107440008800c1100c102140003000d05410182000d010303100c00150483c0e058003c24491500401036003050740300c8030012400300100c810005d6000070442e004000c04c1800d10303810b02e020f4046204031141c1e843d020b408603003140c180010084490b0003141c01c00040c800100100401005145401ca2651811421450701c2c0e00590003102c004d00a002100d08250b9203000410340007070001082e00c41c5500e450700d460710042a550042d105c43c5c0700c5159080300d00b0b60182403284207003261030f1100d4a40608070200103d11000051038035803d0b503 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 418237967 1250 418236717 418236773
    0x90303050a03060f030501140705090a060c1a2809030e0409060b090a1409030903070308070f060501090b0310090206040909050a0501020708030f1303021c0e0d200105040b07 76
    0x4c40084c50004601030800000c1f83c0050728503062154000070a003e0600400304040d020688652a41c0821900c591900e034032090394514120b07906241c500041d40410840c1d005000000040c0485c01400440409100030304500d0150b10070705440f8000e0003c2c010031000e1204409a080070b800c40b0205610030300001604000b90310000780340d281e01ba036810210568030851403103282040e0464030b4200c19004021800e1103200000079555030f00720300000301004000329002c400c00c50300208280b60182e021409010640c1c45005980080000440151080c41010660343c0420017a10550300c0b11a00030b8107807803070141040001409421244000c490381e10540c02100c010074000c2c4060304409200e002c0d81c5540f410a145038850049020f4090a02c000302c0b00c40c5107000a8002071080707004a280041340702a8491140b040c2c804140704500b0320b800c021641504010802d007042c85110f464801618404a641e6444c0110350700c1c080e5002c0c083c0c004a08021744404140e0700074806c0000400c00d61111510 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 418239217 1250 418237967 418237979
    0x7170a06020a23030901060608060604051002030c07060816030203090606010e01110616091d160e030d020a03020106170634170601080c03070810121b15090303050a0306 74
    0x403640d400000042c0f8680031090080c038040a0085900074400ea14080390b0303500748040012101e1003640300c0c1e1441103207507010b400300983c000e2060f111541e50520950b03030b00d0340c0d80301d80c00b400801080340c444001c8160002000b020302d01034801d5a0080d1006c400503c182e9803000300550307044000d0075030706041c400c8090b0b11000883d000c1211501c031344a104114204070b007407020301134802c19035034118040e0a061454031245d6080e540118650000301950780902100c01c094040c2c5032030030710484594060107200506440c10790006041c10406200798000c114550f90780d02c040050740720002c0052407a8108101080d20001811060381c902c001300713407500c2607404000301ea0741600803001c03690802280c29407280400d51028208903607404a401c0c2040b03c0d40f4070340070041e004144402806407040c0326052010955000d06940c003440640100d0907450100100c5040640300b00b405640b9501d640d200054002c218046d24003ca0700b04020301d03803030302d040e00707415554240c40c01e8004160703d00130503549450020751 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 418240467 1250 418239217 418239257
    0x507090c020318061b031206010504081b0a030b0702010b15090d1704171b09070503040201030e0c0310090c1505030708091009030f020f010501140d0204090f05030c07170a06020a 78
    0x104000c5c034000c50351442415141848000028861414410f040c0304c1000584070105800c030b004079510081c0603010b40070340c0010750890782d00c0e00040c4c400584030041001e41a015881014440000c90310303816540780e4004105c0d100d118088110350028000e02062002481c00c0e41149613006001ca001c030700f00780c5c41d03060030042901c51140107140c550064121a8100c165140042950174080d14400c56514000030b01400d1444050030080c10565608000c0a81200600101c100e0a1004003036034806070809030090041e00201100f0796090f4540f8030700280410003580200b0180c04240c65050031039481c1d000555140d003005101c800b40d40280303a5a02c1204640b4840c2a0748180300b6190103100c9000c0d800c00038078010710b00d2000040c980c13500c801031010a540304070906801d54222442c042c850040c0c0b000c60301614100000030240e4410250140401602001a010006408003100c58a07556582c00c4510060504080140b42e04844200808202181c005184202d058103240403d100e0313103200c00c00 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 418241717 1250 418240467 418240507
    0xc03030b100e0a06020106060f0c02060928050306040b0a1d0616030c0305070926011104090e07030b06040c0e030a12080a0b0604090b0102010917070507090c02031806 73
    0x3503440000001e142c43d0189044018200610007000420b040071300240001c40d801e00000300b4000009005011035407202c00b19100d00c100503085810050040c80c0d01250040740e03840000c5440440803000c9004c3c180055101e128a0304120035030303150f0302c60b044044001c01420300c40c0b901100744020f144021900070070481d80580500000c64041030402c0314001d08451500900ca0b04041c00e00d400d010709590700082e10000e8501026078150310540e00f40d60303040c0000148104c0159942040d01c0c6140ca0104000a8401c44002000174090807030283c80742c58481840f40401006401860042070303050920740d010300100c0c0394034100000c3c0c4ca012900020700d001c115205c1194002d15000f01104100e0703000010382e811942d0f420042c0010f04aa10001d01c07103004a000308048140d1303600d601031060b8801d400c0154a0f40c0c02c446080e41d900c003041882641c9030b00003213040d0b4062040c030390000b400c2110741c421507003642d08590203513003048512641c10b9107003c1d0513544a9403104052056402801840300c02c2c01d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 418242967 1250 418241717 418241749
    0x31b0d080a020d02010f0c1d04020415031d03030c040b180a0e07020c04050c0702040f021b0304060908030f07110a08160812191b08070b150d0203030a0c03030b 70
    0x40c051080603c001d003903c80030441c0300606402d28109070100d0b9040200c0400b800c81c4074110300d40d000c2110011a00030700075540403804c0c803407010500c80311882d0180c1c4026000103480644071101c21000c0c807010b076603200540340c0c040231400c20441045241031150250010003d0b960320419040300840020b00071180d650055045554a0400d119509404001040c081c0c0001e607014021843e01c0e40508101d40902e0b80040d01031900d5020003811880140e0483d40314600b0458401032454030a8902d82d5203070018050040454030400003c40c0100b00081620400c030310607603071207282c4080c0d9031310b05918085030805260041686600442c0f5058203011340c00c0701101010b1240d00c0185480585443e0050f0b10030040b50301c401c2048031000e0010b9650326084200c0c8a170501c40720208d000c054884a440b01140040e21042d8086030510401c05110003550180c411842c80301d140580e400c04100340d51041c1c0070025803503802005600c1c516406103080381c800c0c43c028200090001d0f0490046400312080b25181 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 418244217 1250 418242967 418242973
    0xb04020a030f050a090503040b0f041d0f0a05130602250311071208090f0a0b04080618010506031509010605040213050301061d0417040305010e070e070509031b0d080a02 74
    0x2e010311a20764030030141d0104140009010101203034031203e459100c0d9001e038032a0040c000a82c80041007107035080300e0040c02e080b070841c00e01e0000c0c2219140c4900c01501c2c000700c040c0440000c80e84d03145040c01400e0203188a06040700020400703944203402075202480e6580310700000010696050204a8038413078860082d140d000b094140c1c0d6000c64140480c60f00b2140c0054603034a030860124034003009545852070140d40d60340c43d075507282e00040d01203803107544507a041c00000100814034000109115000c0c62a800c00c5214403c68a041607090b60b004890b003940681c8a1220030800c3c4607c0c0c800b20740c00141c0440001540c070707110408142641c1c881d000001c42c01c1a18002001039080c00d1040c3e00003011031002c3c028410040100e1003031448000303480a01108880d8202810b8803d8070400c55006507030000003000700ca8441001d458440800340f04d5444c140110030009200c05000c0c1084807880000200902445440502e002c40e000815804840d000340c00d00c910880054030079001000c0745140754000b = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 418245467 1250 418244217 418244231
    0x10509100810061a070c0b03040f0f03020d02060601112109030a050c1203130e07031e0903030606020c0a06120e0d110105240d1a0106030c021002130e04060b04020a03 73
    0x2410880e5a02c100240c1e4140c0000c020301e17800b1a000300352007010b841154018943d60345880c10514428207110a01074044210306529004051700094120390540d941d8080d40c8082d654000152804002c40e085444590030240508281e05001101e4441c00199043c04a0408018401107071500f00e10aa00701c13200c0d40f00f083c0c2100c0300e2a1880884d50803000c843d000b98a00320f02e048144540c9401c03407250b40400201940407440c541c2c0281c210800c0c020b4540c03501c81c007034a5091098005000000b1098022074038180c0041002d0307101050201074884050b003614481d6182150443c3c00980440b65410700a40e0f50746287e00100d000e01c13098a070380c840e81ea1201d604000341c51a0a00f100c41c041c0c80304403008035001c80c50b00647d4941079041141003045034801d0441c465030070a203200007015056845c8444030100007045032501a40682d82c00205a400c49032440e00d800c0c06c040c00c078462038001c240141e0490700208400309201d1021a030082c80b42c800440c50304809000300c0c00340d070850040940070a4079409 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 418246717 1250 418245467 418245479
    0xb0c0a05070f09060f0602070b13050d03051c05010308092701030b22261303051e03120a1e060f05010809150c0d020c0f0a050d05040e01050910081006 66
    0x203683c000d0400352045641c031714074011004c2d59419451207001e1481c038000c50702c2402150030311320a0004007030203405260b08188074540280240d021100c2040c2c41c1c0d030741001c0d02c18441c3c03203485000c3c16240c0c02100945081100010081d03c40e009001034421641e40c45005001e41c0d12640b8414000e40c840d4071914194100340384680d001484070f03810a4640c40303108905802242982c00d4004c2500c80041c0303141403071800503043c00005d21440501c010b40b424882e03c00000c1004c001101c12a07002c102c1c441050614008a00c1d0344c0743d01c00e15043c0d400f5560a480031400301c81c400d50000d140f2540300c8144803003403000034038014141c4540f507001c0d2600300d041c500100440d503008a903140e07100c8030110281c00c1610780d200382c5000901001d402050035090200740300004036601d0341201d036220f80401c1240c003442e42c035140e0140d842d00c80e5041281d02e400b420151803040d500a0050310280c0c2d102c9a01500140c0c24501407006480c2c005114006102c4603420000703482ca000c3c00110465040e0000209001d03042c40 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 418247967 1250 418246717 418246721
    0xd08090102091e03010e1f0c030e032701051e130e0703091a0601080a1512080c070b07080307110109120f0206010503060702150a0b06040816140a0b0c0a05070f09 71
    0x20005084a03001f4811810007035038031400002c000c6000d06400140c541c07091004400800c81800c6540941c4000180d090303a4098a000e080d00b01c203644450171814040315001102c0d0b84c0584c0003c84040c130307664141c0c860005441c0020384000401e0080c102c0c1c48075607540380910240070595506001c60350754594032060220899111880042c90a1000e40c60308050700000d040c0c11000b824066201da0b41e103038408a44084042c59030040c10305601d032107180210b904080b0181e40c425840c8060138414802d000401d80c441ba420396401d00d17002a44d040c25503490034000e03600e040248000000701c0d580c45031001c0010f65440e41c407400780d08030b5a80d40d440c04101450701915002d0180c1003030340704c0d60090301000f40540d800108021407005440c0d0310130750358030340c0403078036014000700c100c04e5074400e03c0454089102940010000c3c0ca0407011203400324100d90700c08403101140801000e035508030f42125403d000700c288560090030b101e0180400ca41c4411810745030241403119a412040070889410410000a1414 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 418249217 1250 418247967 418247981
    0x120705040e0c040b0d0903031d030a27060c0c0509180f010e0607031a13141e06060913050406020405030c010503090a0f23010207140d020d08090102091e0301 69
    0x901d040d1400d41050f181003c103004005d0a4140d007034540780c1903030405100741c02c00c003c0e24400c2404141c012900c044070940300d4218602d4100040c0c8100c0340d90100307410080c50001d003030a940200158040c103002c4200c94100d0520030030f89044030900d20009080e15628405441024140c1802c20420b400d07018082c14112903502004d05a030400304502040c1c4008120705c0d401c00c1d198200003812404600801ea812a10f22994030fa00071001002021206000d80101d8250200359140d240c0c00e640d0007003114903006515030316000c42c1c98201c00199090400c0320080140700030081060311040c8400c454402900c108503000c45d00c240d00483e04001c142010842d4001c960b20074202142036150450151756211509080602042d640c0e4460005006030030000d04901c42071b99860288400358514000c0c040e40c0b04260496081070101c0c9003015140c800f10f0005e440701c1c100e078003400f20010b24620449120300c000c0c03e04151954204402912a501c03114001002003143c0c0c42405000d007120b040508643d45 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 418250467 1250 418249217 418249231
    0x20c1c030f050f100b0a141201051206071d0d0f0629090606031503060a060602070504060b0313060b0d110a080c180a060e1f090b0607080708120705040e 67
    0x14070f800303200500300260600400e4580143c0c480c0d44580802000b101c02000d4041e14900e4002e000910b10305020310680890b040c0d540030b850b03540c01d5440b0801e05036990304048a20f43c000580001040348140340510094840980041c03410050801036180c0e6116a03003080300440e100d40e0380e072500801146d503c8a503400d10f000c010708040d0501204801041c3c0070304008040d9845200c000002a100403121a14900c6801c80641110b03c0b5140a00c21040103001c0b9008440142c440d4002c005002d1405002c1d010990b5442c088407403d50302d5401d1001440130f0342610440d001a22020300d0312544d1205007a10180070f00a0046251107240700044c0416010280c00004241d0031688015003a40c46900d4191030b1400900c40c3c2030410f5481101540003040c15400c41c1e25510040b40038001140101601013560340e10b07071052800810707525035600301203078088124a0f422038024040c0784003198803100600740f40f030300070b0f0486443c01d0015004020ba51604480c2a00030800110382401012a00e201c00c0d42e02c640 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 418251717 1250 418250467 418250491
    0x10150804060e030a0c020112091b0f0905060a050d020112021c15080d0c0812011d0601020a110f0d12202409100903051903110706020c1c030f05 63
    0x10781c00700501170314289102070305010a800381d40712002e0441d80000340042e00865407560046aa141d0b070314183c03043c0c0c403c0c82a0300c01d03c80008070301e4501a00c16680200030003808140c54072300d0304003446023029281c2010b82c11b100030510181100b20441c00142611161071910040ca45072185110003151190b5010f050440c01180c8181309407000014070001190311810301042030f40141c50000603a20901c0401d1804920b68000050a44280340b515002813074214202d5100ea07490b1001241c5e40c1c0ca10500141c0f110120801c07140c4507091003c01d01c2000d0001800d840c0052030941c13145c15100108001000005a80c44084140000c3d140441c50040c004280580304120420012855807031120704d01e4070002903040041043c5490030000b4100d10711794008180251040d41c1070181442d0030000002000c030082814942e0b40034070038440e038104404012600c03820a016500c0c1c9a00a411500c2c040c0e41c82d20896840701c081c9100851821850042a0350200d00d420f0408002801c1e11405404210808 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 418252967 1250 418251717 418251727
    0x610060e0d14031c0f0b060c301305010e0306010806070806010c0209041109011a1213050f070807060806130f0b22051305100510150804060e03 63
    0x603403075000c8056032a420640702000784884107040c60031881101181030a600f04141c03900e5000c10141c0111054080d0b403402084001c1c0c94005008403882076070070683e0641c104164080180391480710850800702d00079101003034400b8007a8000348a40c810f0ba0b50032110b041c00403080050790313031061100d10602010303805421203526000d10641c0ea108003510030780c18000800000340741644622240c841c129001044845030f070500d41402c114a00d40310f025140990426130001c100100390304a402c1c1101010200545050f00640c6a660344807005030480e00700d04048003c90002c034208106030b0094034402c2c0c0141002a25061481d880c000703140c1e10000a10642c0c0d41000070903603804800d8803024510714008181c0508482d42c5a00414120718901d900501404d41025540780c20a01c120090710603000c20007031500c402210070781e480c2030507400418030f40c8001c88284002e000340d04042e4010100044005010351151040e01e08001d00200300b2000844541c20002030201c0d50080110502c01d02c006136280c8 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 418254217 1250 418252967 418252969
    0x80601032003190f061431060209040605030601151e0e0f03010e060a09020406230607060209060706020a0f08070e01050c0f07060504181820030604050610060e 70
    0x4083c819034140f41072522481c00004e1119400c02d07005911741c031103810881441200e5101c0780c0150281d502000411680d6032054107803002c0180e850034242c03420440d003a806116900c000203035102d403007400e030010384840000a860710b080200714041e000c1c8000c0e00304030703010300d902c001c0c030020314081840f0340700100c03070304804429410181c0c020300f81c007003a5030101c0070100d10340119014250003540602d130780c81b4070810010481d00d545e119a000724030880e41802440c0d5103c0c6801036035045034681a0200b00c410380e140c0c0c001c0c82c0c03410080400343d108074400360800441000054098010b03100c2512016000600d0f5200303250320440c10980d4000310300b040c02c040d08150030010702c10301280b00944c0c1442000152440c1442007000030400c507817000301c1210341c040e1703e528009040c2d03049807042810320305000c00030881e405060f0164004416004059625100c1d55459010040ba03011800800b40341003803c440f070550b1030600885100e5800383d0300901040c2840e43c811b1090020350f41c880c000300510070780d0301c40175 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 418255467 1250 418254217 418254223
    0x350706060501141326100e1203090d0e031603030507111c14012406080f010e06010f1e080103150b01080a0506031c0c0302210714010204090204080601032003 69
    0x1540c51121180d030303a50040155118400d075600000c44091b10400307807a0f1a8030b400e80c0e005013075071010000580b4900401869182d055010a4031080641e801025134608200d12a03900e0001918004003150380ac250302500c1c0d48520300c8103800c02c0c1d0008a0020700d84040c0417945607035218442c0162280d80143c10400300b4402503100202e0004c1c034049004412a0308084250041071a8850040c078035400c100402442041080c800d01c9a94049903540300081c0c031540d40a85110304071920754200d0841c1e6134030f150044543c1c411105e4040107000c023507201301401c06000d1105d070500c0451078403001001d50443c207100c0506203003110205051800c0111344280b590307105030103075002040315402107a0b5071a860002828840c40100b400000008081401803682d807003030303040318400e0090702903461281c0704140040401c5175004051062807420048400001c01c000807071a00500d00c203000504168444e070301c1c24181da2050348940900e074402e070014418003092a000e08003010200f01c030f548007915081c0200352 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 418256717 1250 418255467 418255469
    0xa0b04081b0f0f1318020f01020a1e0303230403021c0c0b060307050d1b06080c07030f09090e0703031403010e0f040c050d0b01080c01020a3507060605011413 69
    0x80214520810f4803016162140c00c00d8a0000c2d2150520940006429006441c2e01d109410f070b228400b0180420015400820701508081d0042d04403105d1000a00a07200260301c010011410507070b990ba842610071000102d0242e1500e291042c003095270805d420002d2605024651844200f900000d0048404d40c1008601a50580c00066034003280d94040000f820b0840991000340c104541c9411602000641c039070111100d03580010480c10030351510400c50345070100f10f4199031014020004000880c0c0a9049002d040c00c95280900b01c4c503403100b46144c1952190724050755103601050050003010382000140c003825031021000ea040d58549581c3d1011540c01a06003980c05a15001041c20320007480d9440b0090300014121074481710540c94044402d000c01d10031102580503010b05444258408500071245030f030818466018264103521010440303008811410044000b1102180e60b600c0320005401414000c1400240240c0f80000140c90f040811104c107440ea0001c000389801d030206010810 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 418257967 1250 418256717 418256719
    0x15091003410304080106081612020603011a07020d141212010303030b0117010308030f0906090d05090d020901080a0b0f010f0306201303020a0503280f020a0b04081b0f 73
    0x200300c482480102e04612030341e00110183c0d42003050109203010000380c4a5100324241004a0003941d0b034a0041001c0146000004d41c00340d8200010030660f002c1910051000710011622440c200c0203500280c00b6400245048440001c81088080181c0084c40b600903440003d100151a044485204d901504c4050000030149913985141929076403250002a96480c10040500300c5540c41b030030195000e4008444010b001b807441c4000440c40b0302d0202c0c0c100e028800440003885030508031360302901c068104290403600b01404480c8100540c0d07454914900800c0644090050200385081c04585002c00070105007014101c1401000308031042d410100031283c000d1000204c045441c40c100c8080401010344103201d21010402540348500080e14a04480c030840782c0100007560b5400780768848000030a0034990341c0c07c60807120a4920000c2003c00d8080c4240c4210708400c40c0c507400900c0000c000e0b080300494070000b2900f4802d803071040080004c000100913081d001e2011070400203408100d0f421810f = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 418259217 1250 418257967 418258073
    0x41707050a1407031a010311100507062a050c06090a02090a0c02150c090112051e0603071706150604121b08300f030105010815091003 59
    0xb02c2105014400d0720051a4001d00b040b6904a008000d2440c0810030300080c4c5108068118031840703407a05010142c06506183c5840d0306042844d100c003802088500c682031202e8104400002140355011b10f41c20380d404850311510780761040085018a05080201800c4a1f5804a203e4a0159940c22030b0594170000100e40451112602d013801c90420312440c40c900550141c541c1030007081b14251002e400d40603001e0b6900c8484813510801502030b542c5c150303100c4180550604403411f08084c158801a4015409000c0301c0841f41d44240c86aa0755400e00004040c1d50480000d01001c01e80e03558a542c43d6000490b16641003900301022071820359000308004102d01e0074045011510035a1511a500800001c03007070340c022010740014004002920440701c60030188030507954440301d0081050303601e40400c80445a0443e030070000151030808026140602c140038140801c040ca80e111034a17030744aa0084401841821300c4c2d4139160561840301403c00380a03020389a0441c031a000000080700d4444140519 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 418260467 1250 418259217 418259243
    0x42a03021201030308040302010e010507050a0f02070806040b190b01360e011401050c1e030d09051e062a04050a0b041a0a09030f02120f06041707050a 66
    0x5a0081c820580454000d4200000000626400800031882180607400034040c1d095078043c0e0700e00700c68080b00d031807010a0b003e100794400e02d03118501c94111130f6140d004445190780c40c1e882c00380c0b41200031502203c0b00c40c4070000304203240b414000388444003040d0203000c2c4565554440040c00400002030300401d14025414103c550b80790f04006101001c40c030410450b24191241c0050000079000d014205d1441225200f0180d00d52041048500c000103032000360013003150084d401c2c4104103030300c07100116600c000d00400105071410700c511651944904000c181441004078618640b608070003a90145402c20701c01c102c1300031150803038a0224081d40c00180c0598840c5000002c80b40140e070040d54110402000c0031980c4554540100706031400507500030011700e495200382c0394600c996403a00000440300601000040d125a1202800506c02030810b6141c2c200d0301e200c1c031302d840140070000da01c90f4404011720003802240c820800301200c2c100009450311000d0749983e980c4622245000f0309140341c041d0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 418261717 1250 418260467 418260551
    0xd080a02040905090a050601061b081b0f010204050109050109060806090c04080f03071b12060e030702060f090108070e06070b1b0307080f01060302040f050609040608010204121104 79
    0xc1210041c240c0c1c2142000141004184c9654803a00f01c2030480b1075101c2e81002060143c00390b441c85441c900480a0181400815590329600744c0200040c4200380045000c200c45040b814400705102240e03580005894030310303203c00140b40c0f9030144d11140c1404460b141c24849071358800034040d0310403c15603041600c0d4403001e124602174491540707d030b200750080007a500e541c03080220081900134000d03a40020030700174110243c1c5480c0c5251164219082034160700d1400900190040c402e49520321301941d040c04825004560258040b803907000011800050500b425070708182e040d03410900030700d0071020968080d00400d180d071040c03100250040080c940016003880c21102c403c6080300902500d143c880c2440706e4040c198110030b41d0354584041441c000800c03511f00c24420b45044031804407806190910f00f00912401e075000c480b220741c100c0c1d10b440010030014001d00081001340400404401909428103241000548400165214a042c2802c80444ca0550460002554804131a5801441e0400 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 418262967 1250 418261717 418261721
    0x7030506150a020c130b0f0303180913050a0b0108060a0c09060513180c1b050712110a080609100b0d021c05010e03040312050c1b01170a09061107050d080a 68
    0x4544e40d02c8400e44c800c2d041c50710704941010120f82410fa07942c00c5c1290f940e00c1055102d02403641c03402e05000c0f446099400b0b42c585400c1182c0c2101000920764003200064440d01d0130301e20419030a4070600303c01001003000590802120758030480c0180d00300308150100703074002d00450312441740404100300440d0a824404251410f01300901c444c0108210031200e1481000180140040e201d01003200c21050044a10250722805201940800500340560400c03aa02d10948540c00007a504000c03103022507065a03c8004044003e0704144008120902d0841c81403403408203901d5440c1d03100e41c202115402d00d038030382c8a0b040c10083c0d41190b5a4540c900c00c1c5451180929440c04040c00310b6007480303886201c90301c0110041081d2405944071251140300e10f0010780b081d201d81c00140b0b9440d1b0002c000c1100c1c41740c1c0100201c5290005140080346d81d907a140c0007071aa0b42080c0c2d11103a03503503a0354000d4400c0081511a500160b91881c0d00541008855100c40362a05030110514007481b101c000092202c507042c0d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 418264217 1250 418262967 418262983
    0xa08131a0a060b0301240212090411120403020a050105090a02130b010315091506050f1c0f0c0207170d050a0f0912030302130506040f09020f0403240507030506150a02 73
    0x9400141e03205d60b998400341000c44402808072100c2e03d045107480a0103440440c0704103a002949030614640800c400c1400000d01c40a00b1306028079105001a0340c007400000031080c021400703540100224442410064211800906a1481c079889880e00d4001a120f8a985114441ca49000003c5158100d00181c1c05009408901b0751101622700c80031422041d503078030440149a5403001e40b915507458180a40301441100c4840c400c500c402e0002541441d05210388110301c0d0000e4001254010810b0350341020f441e1240001c0e8003507040243e0a1100c400004005004111307500020726030341c43c10b0f5401030400e00c07601c61a0803c11001000900e810f80c042d0250500030401240b24101802840c20300500940040400c0403480b0080e02e0001018034200d0251420b40d034000c3c1d001d10a95150114800080d4850180c1e480c136020305110000210303600c460003003580c4101c0d50246a424042028407030440b180240002d0916182c2000e0000c1610740102d5400a0ae1203214410360310000d0a00903840c0800d1 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 418265467 1250 418264217 418264229
    0x100e040905161706130c051c0209090c030c0d030e310c08070207080d050a030e03040305010203040506360f1e0706030e030a0c020a0f03080a08131a0a06 67
    0x4420000a40d64054500c3d015200c0c10315003031300c41680303601d01544404244140c018241c0c0d15075400500103031a108100b01201c0d800d01101c0801000e465020400990b0304407480e000343d400c019241d007924203090105840300002103c20941011840e036020f4048604000070341d0185124507074290741d240c4480042103540e0380d00c0c5e00052442c2c0f8640f84141c080c0c502201c0181c00070b95001c0c040f42d65940005000002c0d900c0c0c003c060302400e100c5074400c44860f040303c0e200f5000c0680b9203003900781680040c0010409540943e001507a00e1400c0d090252800340050082e002c02490005001b21000c861100b107200e2061606540740c030654901510f038541003564005001901540e24088098110140110040c000d00816920415039502003a01112020303400d401d00c1e40c000304124a80703a803203040c840c1c0b0000e200500402c201030700d4241700100032000d034008817030f070781c800240b841031068000b41b00030790110001034a2140c0e052280d490250004045180da4418444940484d901a04580100000d094 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 418266717 1250 418265467 418265503
    0x10210020d0605040c02030c0703030305060f19031707050a030e130212090d030c091202010516050309191512020c0114010e090705010504060f03060302130902030c100e040905 77
    0x6103550740710002c000a12803140306602d41031121003200c0c00070040d1080042c08001414203989561000e80c058071005061951011001c10200c00541c1c40c003000124075036204540340c0e170003411032030b02035422150604440c4d410341c4148a84800a00001040c1007901c3d41460818048503a17440801c0e030f101c2c45411106001c44c004900c031a5140400d2179901c4c41030610004880e8010343c0076606900b101c03000030310800042c8003250240b1404c400074014030380c4944185401440d1104040050a20180000045926400c009007940e45443c0074a50811030304851456200150301c0c0c2011071751100208810360f01840549241c0c40004200e984c10b44000c200c4040007400426117030f03507100e070001109001d42000c0302c444401041003290002681001e544040c0c5410b0328150411800352520811050b4203030800d40c80342c0c030100060302c541111030200a200500030a11504a10400d814983c01ca462170f400342840240c0d500415500c4028000e901e00181c0d000a440042402e00c64140201c0c41c0000002e45 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 418267967 1250 418266717 418266727
    0x1e020a03061a011409150409020f030108071e091806020307020d17160507050111340305030604180b01080a0506070e01020303061e040903110708010203010e0a090201021002 76
    0x726168106144011802042c0340307031401c0075001912203440784003a10075a403c050000404c5030600a104103036405519042078205503856496500380d13400340c4281081284003000400546500b00505800790100b105400b400e080740907905820aa0644100c140250702c5400c0002454080441140b100380c03c00e00541d601c1c0f034104400b0f540d0344d40090340350000a0f400f400d50382d10701304c000d100980260f80c4103082800141c07441d9800c507442d4200e4801a203140d5a81c4c00d0140300004010014811030f280398001e585d0000080e182e8a54a1100022a10192141d00c1035a00001c0d0310808480e4850800c07200001c510b01c14410303604241002d1380004101c46841d1300045000840064407103000d62051003260840c0d034400004940306081c4040b12405a8800d01c0410480c0c03a001090180c1002c20a00140702030700c81000203400c2ea04406425404900c4041d0100d1181c4000d228034805049840025403455141000c20080084c008203d039644030723501c2100c03c003168400d000e141c130103070342404081d0745035 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 418269217 1250 418267967 418267973
    0x180c0603020901140c0c090c131202010e03150109180f060506120a0807030f2f061605030c0901020316060b040b01030501030302061603200309070801181e020a03 71
    0x250712071002240410820070000300c480d2110800c0703840c0c040c0700002a005103051b560500c460148090321418841d00103020612025043c0120301009048201541c400e6020750300015002004500259009800020004c032209602c096030504540f03804400181d10241c001004c403042078440d10003040d0907104292a0244451904901c0c00b482080751000f00e011105c0380d28030382e101c0c2030b100b0041500d10306000d14000b282c014004221400c480e0704180400d0340d0303035105410b03801d03440700703a120081032448039072910403c000c00c4010b901020042403040e1403c0030250160403804014120310a0000015030000d0591080c42074801070307120000b00440b00c0c0414905a4050141c03440c5450007981741100c041150b41c803d002da01d040343d805801a0000d81c40710341606021040403506242459203070f0008004061205600c07103041180100220f8690503c912164103085c02c42e8440da1040e070400003495500c3caa082c0540c0061a0b000d0144221160143d5405c0c025481008019510005105e03000042c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 418270467 1250 418269217 418269221
    0x70209180f0a05070e010503010b090403051e0408010915020a140310080f071a0a08010308030405010b06192d08180d030212100e0a020903120304030203040f0b030c070303180c0603 79
    0x5d5840301083c0d9061603880300141402c961f020303840183c0c001300080100c1c01081c0500010001c00d032805d0509c1082d80a2040c0420042d0b001d0b601080c19603540d08948400d0121003041c07a6288614000e00b90710f0f20300c031500018841aa080910051441c0002c00b054442c1200d400d42c0c0e0040018406950080c4002511280c6901c0c20f4803a0044000e05804030794070740e107509021241e0140c4a40c6a00b8110b909688500382c090b00001c004484a640e10000c140283c3d8500c0042c2c40700018040b10300c0443d90754070310010010800292a40416414940c5001043c00051800d0200c00c03a5898603420a90300c500141900603200d041984043c081e0505040c0500d502d03400801076031040b01c4244200b52220008080455154483e001110500b1004100c441d030003070300207101d200070040484080c401a01101510760340152400c43c050380c03000600f08000480ea40c4018010700a0500071030552030480c2c4042d40901c102c882c024109503039008501d00301d0030210500010603801c100b0703400503c0d80700d100140c0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 418271717 1250 418270467 418270469
    0x20114010806010e090f060114030a05060c03060411030910020a09090e0307061d060106030e010e010203101a0a14031b071a061e060a0c1506030b0c070209180f0a0507 73
    0x1203004d441e03000410303044000403542c003180c42c140b0061000d80e02e441015072003075250a102070b515025100c869000314804014050042c1c0910175242d42e00c0c03d00800f00411900c2d00310011400b0ba0b424002c20041c11000b003000025021303c4540940e48082005007101c2304000354201000701458002c9219900c070f0000301070400107210341001c11055641248807002c07540800314110003944010014480540719070001d0181403d48000420100c40c0381160500f0381e08200c0d038603601d40380442410002d1525664413a10500300721000039142100101b4000c0c4036107203015010b01c440e04004007180002c60304408441016a804003400c0e142e250301d1a20029984180c02c2d103113180c1100710080307403040c41c0145502d109140d8203001d0641800300304091200c41e4101c0c4003660140000e1038450404181d4100b141e8607015070301c200005507030f0f0851811481c1200040c10082d50080103022600041c1c480501440e005007613688144443c07100c010f01340386002035484c1c9541c442d018241580d801c212000680c00 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 418272967 1250 418271717 418271729
    0x30912030e0a0f030303140126071d0901060e090a0611040e0c03040209100b0d0e030415210c090506031314030417060402010203071e2004050703140106030c02011401080601 76
    0x100005c45008408650b0280038005c00380e44000380842701c082c400040f00b8000c9200356030010390f461165070b038903030454201845a4017481454a0010401c0d107810a101c0c41c00502540c000b5120329041041407645c0d100c0c403080700240015955a081345a0301c002c042650001c0000301d14001041c98260120301d142e401c00d80e4100c0c01010303c40007040001402041c0c82c0c05840303101070301c141447c00301c0c2c44401c0502480e4540300f845010420020070540505031402c100c0c04003545030110540c8864130600800c1440000c0201c8840c5845100400140e02070381000458904458180e141e846901308a204000a608020140140507404040b040c0c004809001217441450380a0f1804010402c110345601088400900507001049440001145940f40b000d151403070140c40304a048180c1e03102c1102c1c3c40800390601880c03000074052400d030b1500d4000e01c0d0b84a06e641c0740501000c0c201601d034000004040c003520041c15111110000582e01c01d41c00485890036010084480f541d5485549803144d60a00680c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 418274217 1250 418272967 418272971
    0x6081006031a061c030e030f0f0d0509030c1302090405040c050a17280f06091101020d0e040b0f0d110f010c030203040306150504090c0501110703030912030e0a0f030303 74
    0x1001c0030301c40b0004a8807844024140003642050008600410000c40504505000031400300c5100781d10204403001114803050010428840301401d85458011010071440030014100103060385510080b0302101620410346804502c0802c182c0c0c80b001902075039110a4000e4549402c02007807000740215841200c1081c2d81000140d0307240e09490706c141400920403580b13680700c1c004190405010700c402120345074203030240c0601c1800c82d41e80d0f2003030910a400262074241d01d070001c4200380f040310804018480401d0009081899450b80c010700b0054048a90620541d40c41010010944a05802d00e062040c020040d00d5248250314008041d1081d14015034001c0c00540b410400a50280070b00540582d0540c00450801e840e50341c9110207400b2000701d10120070b4802c07400003042e46940c05024400c1340315082c9000040e050400040124403041c445a1007a40f10a408201194020310b16000344c0b10496482d10a5015505058401c40c41c000d20b40d0743c000c14003003400246a040c8440003010743e0b20070380e81 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 418275467 1250 418274217 418274243
    0xe1501050a09020a0509060d1119020d0806010804020d051606020a050c04050105010503010b090105040320041103010501120f0b0d03090e0105090c03070522090c090b042402010608100603 82
    0x903540032030040c13081d624042001001000c00b40e02d40000944a16000c590011540c0c20f96074a9410707050300701e100010001c45050300d00c02d600702e406024860760304840b4980750307882d8580640001c000540180c03000e8060703480780c00400b05006e014050000818064122444820741e2600300039684d052400b0150703424002d00e101d2042e186024000c80c2d049940507501c1c00d08690074406103210580c802c1c1c0241d410301004000000c0003840600c180380c6280035006443e40f5400c10070f001c2c8000e981c250400c810001c14100018880750307030041e9800780317580c9070550001024075071201c3c01c41c000c0401c40c402e071b0b500a065180b03140815610420074400c0c0e603000f10750310007a6640d801c10300800b04025207248210841c24800101c00a00c9a0042d01004440c48202042041c08035030b0525003140300d800010342c090701c4900400c0c01c0d03900000b40400400800c40000c1c90285408456003800740c00c1c0c42c81640703805004200b100c26074400d40000e03001c2d01c05081550710b000b5240100500034041032004880111040b92 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 418276717 1250 418275467 418275479
    0x702030106080f0d0f05210429070f0903020d051e03040b070f150603050c181302120327100f020a020405060103060b0d2313030804060e1501050a 64
    0x50b81c414410f2a00d001011500f11059090302c290b54810240000c10900340800c11092900c498031455640175454400b0103400d107428898009a0050003042402414440c0104c002140340c054a602002c01d00e018064581d06010032501300400b6400a90702c07200b0060800c0500001181c0301e960300821404005100c0010300308503407a40650701c40c1410104080c465440400c074044001c7d10802c0c49261108054016042c0380421240580c000307a944d170703000d031100c1407190906441e100003103c1c81d44039202061030400d0310004070018613440240901c0d004042e94211080c20001d95030040301c010009585103001981104510320340c048400d101c6e1040051802400e8000c404840c1c1b1003165501600702c48040c2e80a200c060300014200c2810581c2d030300e900044442250002e400f070203048640116112141030410320303890b06013500003402d801090050054012601e01ca80805507807500706188a542d0703905041c0c00800c0300c83c4107004603001d40c141c20b40450300c030f60b0380440c1603980446a01104d152212 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 418277967 1250 418276717 418276723
    0xf090f05010e1006050a09050619020105010902250507080a030201050403030b181b0408030a05190905060d0e0a02060703030c0908161403250603050a1b1d03070b070203010608 77
    0x1030f85120300402d8801d402d1092034424802420282124101140d0f01aa04e602150b10341c0d00060080c01c440c2e1407400341312501c2c8d50a018aa00401188000394103001c00d0440e202d83d80011b02c2d240928121606400c1c800300581401400001c192000980340c0304216403d000c0e01900c02224221300292400e89105500e2401e160b0030800c02003061600c02603581c0b921200b035070b10f0000912040d0311500a0000207141801003004210189040e600c0588601c0303600e5140410030500340c00c0717500b841840a01480951980e03811754002c0304408902291258a6844c03003030074000301501c082d4010f480050b042d014143c040c1c120030f050303000e1607980034040c070366a180d4181c40d4202d200108a00100342d8800304804581042c50311042c020050035111740354400d10791814056070440500d401141500e034200400380e0035128483d44840381100c140301c00c12891050142022110f1144414040008a1010003203004500c00001800107021145056260007082400ba04590000c91003582401303030200300e1080c04 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 418279217 1250 418277967 418277971
    0xb07090f09090f0f1a07090906091109060304060f060f06020d020f071202010207121103060714070807031e050414241e1603200604030305100f090f05010e 68
    0x40e490720b6000f4604d50b2021201e049003082034a99082011010303803041548400345000d42a542c80b91b990079454514128140c51240d841034070304c0c0d480c1243c24001c14045c541100c09c141402c44034550b0300e54552902c10010459403200d60340d85850b0910101c4c002d0040380140040e2802070b000ca40d4100031003142203a40e2045601c40324040d0300404001c00983c03461910528104d44140117a0b1002c50b2900c04540b50f508aa007015598502000344040311420103005084d0420041d2402e281107918600ca0584c15224016008144032000100310060512905a6111178207014908043ca99040d0800504c1c5030482e0040b0700003881010700e092030520300284540710b180c00c041e10010480540c1a03003196582c0000c0b400240c1c4c01d21068034400708a0391403000b00b00f02e0b4200d0500440304a0b2a0070001d041001510303404c02c61007a8000c0040e6004800221907900550500d80410a655605229002c14285500c4140f09400c0300c85c0103d94141140c0110005501c0d080d410001680d0f184500ba0501c0d0b01 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 418280467 1250 418279217 418279223
    0x901080118140c040203040b040c1d1501030e030d0504110a050d0803072006070e120606150903011e05060904030f0c0602090d030e1e010e040213030b07090f0909 71
    0x88021034500141003218800d1031190b514064400c503c801c800424184d0744100d8040392118076850411041140d0000d030803021300301070f03c500802e060f503680c2d15409441c0041c2c0034096000c00011041c20aa00c26000f001040741d004040da501c07208540211006440244c07421034a40300d048120b244107080c21842c081c11200d00500c42200c00b1280e07180d80c501c50744050076401c10004401c1c00b09400c005030b10b0052491141e8a0001c1449103058032004119550b4001c21a200b5a84090000c09c81000059500d800c507504940a410208101c2c0c1c0d030401522034151400d401d5420400070052030b03200c0114440243e030b030980003030140d0b541701d00400c030000d4411a4010007040400c1e010090061043e91100469441000c006241040c240d00140f0300340d0008508500003140c0c6c150781b1030035061011805064a24820003240e90540403c0040c16030141d02116901690340443e5a40004044000100003150889403986603030412243c01440b80d90140034203903590718032007400111120240f044002c1a90 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 418281717 1250 418280467 418280501
    0x40c05060415141c052a0706060905040809040e0f12040e011a03190b03030d1b020106030c0501210510030c06050901080106050f12150f030c0a0312090e01060e09010801 74
    0x409a916600105805080a011070824052400191441c1e00301b03500d003001c100c1c503070607141c0310145032800c1540c105400c06075040e8240024400040d81c0c04090700c80c400c0048401148a11450340701cbe07440c101c020049594148a4424126038403c3c407203000b40107a416690040007140c0e29012403980318186103030400081641040003a91007148001c41044440c0d2001c400300f1501c100d400040d05e160000d50041c5196030752940c1514021742c120400142840703850009019951075078942c0d03081d1030018401c0038148280d000c0302c80d0a0007642130060164100500d4100280e00300b84280680d181801e010885548201c0300c0e01168440c058030580e059a8016900d00e851a0700b0041b00b2151600002e00142c0801401e20450304001e821411461003a0540c880f071008804201003000011214952154003d070850112860961141c0400c43c2c1504c1e044940c2ea03540924094044412101690100d0136241c0c2140000c585190321205543d1801001c5540700075070b03600c4600c0f96007210090501911320b51 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 418282967 1250 418281717 418281757
    0xa0b07110c03030c060c03180a0c0609050d02090601080c0c06010e01080c0904120c0809120d0311040819051e0307021f0507151104060306031e0218040c0506041514 72
    0x902590081d80d00c10000d001c1c901140300b0003112642740c240c0100003200c8a002040040c01b00941c804000c1c0001c200464011819440d0f0b50007190300c412004e8030b0030341041003000c000381c0c080f12140101c0d440044030500704c4e4400c0d03039035410201ca407113030a000700030003400703200030130610703450301c10b00c61401a070300801c5054400d286180c09640d0b800b0000d00807503800e07000340710f03030310469494a0b540d04c0b0000302c002c0603003040c1030b14010040490f401d1005400502d442400107200200001403000c8121940c980750400041c48d42c2040ca18114101d040903083c0c000700705042d203002c0404006041c001344286c0301356000c855032010700c003440425102c01400042052010101040c5911007694160200207000038840444c801e5214040c0e2181d0003a00100741c4605003002000440c01d040300d00c5094024014084c1500c680c0094582000d140c0105403201c50707180460b0500000500d8000103041c010003140d82d9035070b9083c4c07081680086030001004036500d124503082804484c81118006680540392100310 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 418284217 1250 418282967 418282981
    0x606090212010e090c0d06241a13052e1706010c030c0510090302070803031b030a06080a0b1e010e0c0711040e15100308030406020c0a0b07110c03030c06 67
    0x4000c0884c0c0c214819030a80c4421501d44840f04000c0c0303401410045050b0120066880021904000f410003d19013540c0030813801c600c594240d5401b0b0509a031050707503031090480c019507411032034102550000d4032481404680c00409a0398000c80200d40f405188070000ca2000d445d9008070a40d811002000840001c804d5072007510b40e0490075120b41806054150607850340341c500fa014820112a441e0780303d55040c10b16404202c00c41c005c144801c002c6166103050100c4040004010044007111600800440c00740071143d00640050407584017104d006501c07a0605414040f0151143c00744504100800210007544a008074161008060740c90b1840e150050321181641c402070055680c1e020788140f03400196203078010b41d42d2440c0300c10020000035212405c030014481025040c00400c40e5419801c01c00078181e02c040d01d50090b00440c2c010784850410490b203007025128400200a80540b10800049076005080280f5a2070b0b4203048400000c0c05a0615540303208204099900354840c0300000d0301 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 418285467 1250 418284217 418284239
    0x15040b0417030c010e07060909020408030d05180a11090604020a0c1103100608060a150e040f0c03051027050a02130b061b10061d06010201021b0109060609021201 71
    0x84140e1110032249480032004403e82103509503d0491403035008030341d0402c05580e1050040c0081c04000800f146050310340305005640b84252260010380c6515240055802d00c0c1c00c3c0c1d880c3e1000a5810250340c0039003024502045401e208014451207041104040b80c09420148240e555143e559182c0098501e220740707070404540b0100422039858416980090480c031040e000c4d00d03008040341c1c001001c0c11b0a10342b5500707058402d040b68107481c0d108000e400704015008403034075070740064000355140e20465586c2048240008039030000b40244c821010710010398842c070b0703200d4a407a0006100700c188507080a00f481c0c41040041300041d0180d032240b4810005460040c01041910002c1c6c40d000542d4a410804515260402403090b6569421030055540e003910902c41802d40c031041e0300f400c0040b5410f0015001d6114041812649401d01c0b800005032943d000b507046035107070790060324035044078240d1211040c041d003506007003254403a042810010b00c0710310078000e44d03a000c19502e0126006a0074403c500302 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 418286717 1250 418285467 418285499
    0x8012a030b040f02040e15061303080f0d02030708060f0415090b0609030a0302100506010c0206040e0712020d061d040206040302100306090513030809070515161a0615040b04 76
    0x6802603541088184812144c070081000b0805140400401e2034001000102d5400c68a42d03580516401c00c1110711642c80d48001c2c900303a83d48170200070b4490002d5400c0b11000c0c014591408145480002444a11500300f51014481d40d01101c1400201c3e85600500050303600f04d9078400317001c0300348820502245085401c4020b551101400c940d00b40000e00c0c0000307261444035001640940c000103c0030300ca00303205c3e0161031390118003820070b802402941d60200711107104038410340d8420940c080108059500c118402a0b005861030400d64840500e144540b006042d070344108514100b103907041c008a4400d1081e2144500c0d001010716040919580074000358445408944d002c041d030751000450580e042d0304c41d0034002d903101aa000306841c4c03e4540900607540180401580d13030701c001010407181d50790018503002e407240300d170105444a40a40604007601c2c00d65074000c0c82c008000b103002c0700c01c005407040e152040c8005c07030318080c11a500320220740c8203100d02e0082034030481080005000c92101112006 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 418287967 1250 418286717 418286719
    0x21b03010905030a0f08090a050601090b13150807060206090c0105070222020306040b0f1e03120c03130b0418050c072111010c0203040909031e02030408012a030b 71
    0x1c00d00350110340c0d0312411544800c1806003c10b036a0f207a00080a98865840c0d0f501444110040450688503100c49035a41d20510407a030f456500d80d441c0d9000d5440380c03424504050f030413042c144900c2d8000d9025605551071402698428450100d00080242c07000825501801000c4060002018042c0c01110f01d0303031268100b6078000c00f20084801887c0c282010705032045048020058aa0424004000c00e581500480314807d041c860580111583d07882000d01000050000b6600710042006c04282801010010440c0c0520003081c04940084084003d06ca040040c0c581d401c07102d41c8400d650034240c0180c2c0175150384036950289811446815901c003903000100d11880505185250b9520b140c2d130307000d128000c12040200480820b14941220901202d0b00000f402403282038a0f07198025603074051803151701c10b05510b4044200525018403001540c090140c0f0000c1103480c440d24000e90b0b01d80c490701c09d40310a5803070491a034502ca03041c42144c581000700c840d0b003951150071055040703024040c1e039a011 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 418289217 1250 418287967 418287971
    0x807032f04081006090605040605090612010f02040608040606050a030302032d1801110303010b0708092b0c080d17060102100c0f0e0a1d0a0f0c0c02030609010606021b0301 75
    0x407586500401c81e103e415485090086007035400c00b4594000e440c141c2d40240d004506203c001e000e0b41d03548140140c0d0041c410b0304d000000d0102e18860034050a0381daa000121144001404a038150780b24686621035800342c0c0091001d03a40d81c0050100d03040083c403000d40160814000d800d654030108514002c1603000d00d601150740030b20041008642d60050642411005c28091021819600b00811503000e40d03000340034604542c50072604502c54464090001c01c102c000155400342580e407a0f00d60414140400c640104140400d51031801011460000b17440c035040c40d40000509200c000f6001c0d9000e81d05581d21250b50100b051201c444c010b02900aa0550180700050318010030180b00e00c0d42c006100e40e441c465822850107018000b12040c00d07241c0d01039141d00c403003400b4000241e000410380e11740a131080074071569005402c6004000200c10f0300107030b07401c00c3c1c085040d107680401e01408441c000c600351003c0303490782c1c44a1070803a6803911a200c00340e0400c48034038580c001c91508461402d1406000 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 418290467 1250 418289217 418289219
    0xd0b0a0e3c010f03060f0506030d140f1201081e030d0203131a190b0a0b070f0f0b06090a0207030f110c09011707060c030804080304150216030807032f04 67
    0x120010007001d8008800030b0b01c0120081040c854a401200f034201c100c800308020908144d40425100e8000140e0103045c440c40f41c610395800c00c0c043c0300300d0b240d292012502c940c8442688e02134040c40182031240e210540300c2d00c6000a811a83c000c19004024030500007103161208500300c10b8041d400061030b0303011760b8586480c5000450000b1000c0d0800c0204864096554a08081c0340341e401c010701c040e000720701031a200144200da1500c070864400d583c01008455100c611900e441c04059a00c0c400082030112805000410005042da07000d009540485141400d5683c001c40c0400302d0040c60405000030780c1050103614000c0c06000d041100c42074407415101c030403a115020039400e040c03e900629100c1b484e021090920007040c0a007d0150000d440e04408620091314000d100040142c030107400e40c80c0c0080801e08004060300f40d0402c059080500759141c4441071414604035068100540203d15801c00040b1150f2080c4110078001c49441c0440b43d43d40c0758000c41440c03551000e0302d82e840d510700800c0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 418291717 1250 418290467 418290571
    0x60d0213090501090302010c020c0303040306050a021308070f0501050307080406051009090c0e070804030203070809030712030c0201082206020c01020904090c06120c0e0103020c0c04020d0b0a0e 85
    0x54001c1035401080041034040711450002d08403580240e4000464001400d5100c203a5008801c440459070407400c0400c09485114a0800911410301200d01d0030003072100c00501200081058070464216a45079800e455981c001520640300803503051002030041400070740000d8103a84019040b5608040f41c100c80d80d194034100c01101c10705c00056481581c071711001c03c5020a400b0100d680a0541c2c508140703035003855a000b96490140802c01001e5010100355410661000c100000c0100086c0c3c61b20aa02c611034100a0200100b200c810390002d031022001440b4036181c0c10290f07000b00d000e020728000d02001522100700a40100c6804040355408104440007640e45005034071906000d0b001ca800c41ca4504035000d0300fa00d00880300c0024030340c181080da040160704401d4040c0b5422003828090b903214081144582001b20803d00359034020310200b41c1c608640f20325445100105802c0c0e40004c00b50b5100c40f214107002e241121050440d00000401040484035000d1285c41d6100400c401403800c04602 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 418292967 1250 418291717 418291721
    0x813061b0e0a05030c06032406030106120b0406031e0f140d0915021005060112050412090f030519031403010b071502180907090816050103110c06060d0213 68
    0x40c100c00041e903405060707141e510300700d91a6002494114010240c240000010802c10b0000600c10080c0182000b001e00404102401707210141c8002000300796a0760319002c002e8610080da45503042080d18148a4900c0307418030713200340010b6a402a0100e04900e00000c14110165400d050440313076403080005480009080c21040c01c140050b09018000351000340000907d00010345c6c0c801810307000b4240c0840060f0b600801c05c81000140b102c000308407960b5607001601e146070180a03985034903140c08100030500a0b10b4a10a1040086e03613a20b61a5a03a60018020f0801141c04003500d69040483c880c0008000c2440002c10140300381420052880700e2250042039800983c00b080c0010710015146080010018551000c83c00d03421085007000380103041d4804100c1c2004074540035003820360111346054003400481000700515421928280c41c840d2640b502c096080c0702c1c450200741401c0001100300c1d001000c0d500c1d0305408000511240e40e683c0100a0070002c2c02d4000d9801030110014462900914 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 418294217 1250 418292967 418293011
    0x8061003020d0f0e061b220302120a0201081008061f0b070602071106120a050702010e071409390d0903051e09031509070f030c0810020901081306 64
    0x12100004d001598980341c0c1d4100180100821101d03040700c00c1c126a00220041502c0403e00003040b004450000a15070a0070000c0d2508042d51280f0203a0f1040401000015101d001600c00e90382e01070783c0e0700c640c511620701d104540035801541e045040021060b40110710000400c10b54134400c0c001060342c910303c095030f07036001c1c240a03038116400050441c140310309401903002c155400c0d1147ca20f886a058010b605219000d41071003070784c945070f0002c548002c0c403d4010181c1c011841040d034503034a50700e82171100d180300b142261078014180e0000260310340602d041000030ba0000035404800c3c2c10308440d6000c0840c201103052011a95080c4180c04598400d44a151140340c800e03106c0b00d82d600c1c40030907184040205006c030060060802c0060130b106407000300d202007034044854041409a110442d49600300641e60b0001c954016004000005000c80c0c0030604084444840a59424140c04e00c042c0d0141d128107c4070a0204402d0740109102c1440c541580d268075004010001d9075088071080c0c02c400c0e50f10 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 418295467 1250 418294217 418294241
    0x41a06030c040f2115110c10050606090102031e0f03010f05030613050304050409020109120c050112050105010f0f03200a0f0203070f03140f0a0302070b090c0108061003020d 76
    0x41800d004003659000143c01500f400382c40f4040709980c140344440d004015650007030001c0900b0b0300c501c008903d07540044c1d804814040c3c0c2c140d00e800104000d16612013101101c0d14400d0b0820000c038550b03081c507034104d86815906034040d52411500c010954100c2640c0200448a2901003103a840a00048005103001c0c09030608000e0106281900300351510102816015207000480d907640d0004200004580842c0c0081d030b0301052000c0540010790320f07580c0c994002983c680c80c0380005e00810090181c2c200031794000344c80344400b0a42c440400821114240111408a0204260038140b180103000303401c6082031600d030124801c5140640301d580001103c0f03217000e0030b840204500e841c850700042c4003580072810744025070501509882e01140c20781c0e6640080d0500c15000300b8071650318040c10032982814941c0616959400070b094004009501c854000d842c13080d45203002c10103400001c036400d02c0610b416940e00b84191030381c40421401c102c1c00800f01d024160f08000c40c4060305c0d9180119602d4580e = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 418296717 1250 418295467 418295491
    0x20c07030506040b1806060a140d020a090212010e130204090f020409050109050c0409051c0905031504060b0d0206070311010b0d0b011818060e03040f24090b09041a0603 74
    0x5181009100d418241e0203203217072580008003000243d440385051002100d13120300070f00803000e502c9408074600044566000c0c4d0003a1040d1000f1030720445540090500e40381315014081c0681c0c0e503441302c007100d1005441703070180d1698040c4008090328094000840721802407495044002e0710b41e0001d0100d0b480014119004d07516540c8680603c138083c8000d25a21105641c00d01002042c2c0e07460310384170a500c402d101803024000c0310700081c3d58030408820300548000b03000c89000c2602c2c5801c1c00c0c6200d6048404581c0c2c00d003004240c5001c2d06050f89a400d899034040d00c6a170502d201c076603080da40e4030b031080481c40745907580e00c44603101951900c081182c01800340c90107100d5541000c0104000305403040711a030340c1c241090700100b0946161a40e442031180c215100195209000c0d0f4600c3c11480340d80d000d03613030f911002a40483e803140387e0054103141008036040c5102882d904030f403e54041260348500201690b051040b81d101d4140b640154542018400e01c04100b10003100c0007901c160402c1d544961418 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 418297967 1250 418296717 418296721
    0x204080d02100209180c0702150c01060b040b030c03041a010605071406010e0408030c0d02030c03090d032f0c010501090e0d140316120905010f140c0d020c07030506040b 74
    0x3a40520541e0000c90741c42000390310304500200428204004040901d400750b10303000c0001c644c40d1504090710760b50741e030040100360404003540b0100e51907045a44140c2295107071010000d020a21a8221011102c03840400390640c2d0f41c0c0300b5584042c1d0801802501e11043c103102e000d580600c0000e031b19028000d40d80f11a0303100d0342c0340d0404020031440340b20b0102e8554800401409030644030100c1c1d0342d20a030300042c1d160b1f8a03518407451128500aa4000078542070011052050340038003800070f14032811562048035a110414a811825115000d00c030075038604d981c10100400c48061000303c809210074412092505d0800c103107403800c45400b41d01c170718101503540404003014001801505083c82d00391910359003800194401c10914400a040b0507200b503000620b58062a026481d00e15005002c0b04040000305510b040440c040c1411812504000f450080c84c50800040442d10038001c4d07941c0d0100da41030101c0781d003c0710003e6000a01d0359426120381c0000000040040210318401d41c890000340b9000c0c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 418299217 1250 418297967 418297993
    0x30d02030310140f0f15180f03060f0a110405190501110d090b07061407080a0e030a090306092d02030105010e0103080a0e2b050c010521040312020408 66
    0x8072a60b81c2000c1540c42d2a8010700b0b83d60f42c0c80602094a5410896050180c003e0550010b02000801d1b001c0b210b40c5140490f100c0103c030404000000d82d0b0b031080d21405100d00d001d50405440301d00859001d44206c40440206041003510390084c1d441929010203d4502616003000030f10658030034040041c8040c01c3d11050000d075a0001450380300b0081c50700100075000c1138007c0604650308600404490150211b040710900801c1d40024201402084104c0b116090026000b802c6000c1145c20b269004d040800000f43e2060001c100c4a00c80c0c020b58070720b87c000342180d42d114040c10540d0030036100405030203400c2d01c64030b040222481000041c4280800e45074030383d0cc145401c0d01c0059020b50080d680c0080100045906101151600890307490066150b09003000019086000b0000300c2130782c51040061302d0b10381c03240d00d1701a82006000c1c3d0f0498240c01089801141c0c90f00c940c0061680811140d454114122048074040b9041407281c01d1003000c103489001f51030102d0b001580444400d0b88040c1d146008 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 418300467 1250 418299217 418299241
    0xb0a3308010b1c1101051603050309010507020f0d080604110c0f010c0219061503050d030e100908120c0408030f1b0a031e03020705010e0304151b12030b030d020303 72
    0x41c0102c1940c80a42d088038000000c0036640b8050000780c204204030a0460050380700d6021500e0340740e0607150078220100c00341402081e0b40c208503010b051561800c0046906113000052900c110760500c801444a083c02c05821546910041c00458019480b2110360705100317608030161074800e616000805c42c840d0300d442401e0a68a28103400d105541102c20f440803a2207402c2440b0328015049500411740c51035000c1003200c4284203070f0000c0d000d402007043d0405030603416080f000768031000100b1600e070504c003800200c08946100400074500c0e001088496101c1002402c030310703808000750440c02d040070360b168242c508583c008031a00e01c000074000ba00c000c25104000302d80306440b028034010100f0841c1c990b4054070700d40e05220340412401da0305284486292007034040315003040c0e00600034003c9526050700c050f41d03a04180030344030b07400e6144000d000c2414410718a024041079080003400d040c40c4140c4603140d154402859050405444030703941c04094030108100241c00185074019a900d10f0300c202e08080d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 418301717 1250 418300467 418300481
    0x9050c0108011e0506070203030c0124080102040f090507051b0330180703061d010b010503040302031c1409150105040603030903080f1201030501060e130b0a330801 72
    0xc180c0f0108070030b030b403c410703031155030002039910a4409a43e0b8401c00d00009245018040f070845c01d40d805c00b40302144e140340c0d40580b0003081c2e03c40b203035107003050307032260903035400e0b070243e40100903481d2501c00c0304111840e0f9a41226030407511506065250a4000340d0000d054046410780d84d00c10f5200043d0105102640c94400e1241d20300c00160142d5003000203110840044007030b002c400d01c0b107000e8115082c1d0070002d10034500191f6000504104030740c040c030300f0610904080010711200354170f0b14903811165405882141d22450b41980914600703554003078074031100302a01e40f05288030b503034400c42103174040008400b860043d01c0c50002417075a103140240c06403092205030030490144c1c3c10441d007000042d800900d0380090360350241000d9124061b00107011030703601072201c080341b2000c0d9500000092003c19440401074500700c0380140c40300d0f92074584600b40340c4c80e031540040c84c890360300000070601e06487d40b11140c00880491800d24150000c0e0150b04190400c0000e14810a61244200316050007441640 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 418302967 1250 418301717 418301729
    0x18010b1c020a020a0f0302030c0d0810090c020601030b1b03070c0b10081504080d0c12060e270c101218170f0405040204090c17162109050c010801 64
    0x261804501072002511003500d00c20041c91044580d4101701003500901c140c03502d0501d15800c9a0154241c024001c221050954841d0349494202e840400d0340304190203003048000c5640c00409440e4a5503079000041c2c000144003080c01d80d1440040070310f111050340250301600055488035026241401d00c2c00c03501201504004500300d00d44000c00030800c0202d96200d05d403074083c03043c104903035540c20040302c24811440000d0390b0928000c80714090f15000b00c2c8500c0f000d130380454108070440d00c5148079042a00f094411075100081c0055400d07641c00700305508041c0701504002d6860182d8a00040b40e01041d01100040100e88102c00301d01101d50144140c101111b1440980c010340242030f2a001785942260489810010340050f00d14202d0340c3c5076003100c000b8100a041190703515941c10203031005140780c1c4943c0c00050751582207041c44005400a990040055103a544042c071444e01041e503090034446017800e4000d60640d10a56211050702c90745480b140594080c01b00842203500060808605070051 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 418304217 1250 418302967 418302971
    0x5120105010f050607080705060408070c15020c040b0105130314010f0b0d080703090f08010c0305090303070207050405130c120507051203040e070c050102070c05040501140303090402030618010b1c 86
    0x1040b52010246902040710002d803142a0b8442c031070b0038050f665104540001d4010b201d244188401c000041008280c010301404a44403070b5603c44015035641c210900710031006a000a08454152034658811046420141044d43ca4031840540805a8260030341c0103a40d803c114400070000584280100c4009109252042104010000001d0030640b401c09001d8400f0310046130140415010300d04090141c680403041c03000c642c1d9038071502400b070107155100000080c1010040b8400c410b0000a40b805240907401038440c041c1001d040c0401420010000d0400400c00040400410f4081505102924503500c0d03612000d10740f42055854101d076030340594007425207081d80b02d0403042d0100070307078040d582e49075111074150b00e50200403290f005c00103d003c1d085510006a00302049540071035001121010741e002d000580e6034129140800e000180107a815400412003494107141c0395000b56804407004040050071071400c101d0000404003600008001c200002c0c0003640341000c2c0c0c041b0796090510a8007 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 418305467 1250 418304217 418304219
    0xe060a0c0906180e0c13090b010f11151f0603020403021f1b05010902042f030112060213031a01060e0f0a03030e0d12021e0111030c0f040b070c0512010501 68
    0x101d504503140301d000342a42413040410a010f40c2c01c0115140398204015030140642c0f14100980185061784105020400c046018494140a0b1815654507440d110282900c003600010b62592004024418501c80892052002e017912044900c0409460950341c01a107441c15441032125049040c1e0b400f41414094120140c02203501010342314046584000c050342e00403052030032902604914074002d61050030500e00c0c4452420b189801c1031011030000051032200c015240b0f00842c0c1c4028024002e4980381c4040150100d0a00c1e001444808101e04003107401c281d4940b5044080500c003544c120350720b0303100300040000c01c2e4004e078171031551701044400074030140d0101c0c0024813040281c80000c0500c06403010505072650b0f1030314002c3c011900101000704034051048000e40302c0e100c4080380c00745401d91061640d9181030501c1090010344841036054a5a2204040f805a5401a20101e440040100004a44c488140f0040c000840c072803a06040d0103420a030820501700180f02c1440001d81c07610300 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 418306717 1250 418305467 418305497
    0x1a0a0306081c0c030905130219030c020d0e03120406050703020f01020c10090525080111030c030a0b0a0b040b0d0c020f0a17070c0f0312110c10030e060a0c0906 70
    0x1420080d02c01c86410200b5000c051803030192980244e1b540242d40c0035450b401d450001c40d003650018071888001c825000390750342c130030307034056045500000e40540140e01255030052014050300c09060102001021103a0f0f0002003c02031045a0050304407100141005c950981090340400c0074030b4948131098025414540d030340034540c0c1da650354201d62034410381d2a0802001400010300031a2603001d80205c5600d560001a02c44590411700ca10404d0482d6180c00500409800b40e207090741c2c003a08110103840e15644460780d0705009842ca5010184d0300c2810b651000131183c48205c002c0c801000150320050b11400c1941d849002c44580401d403c0540d0840c00e0402003200011643c00301c510b40c010400490b1280710940d001c3d45005190000301000c545850114003456503071240c80c11603106005c480c0620140c84021901600c000d00003a14070f80c81741d20a400240303081c8030000c08868030751400040c0a01591840b038502517060303417210744565590010390b4085a000c40040040c0050341407100100c10a48 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 418307967 1250 418306717 418306753
    0x20c0f0f1011040905090d0806040903050702060306030c0907090f0b0408060a15050d06020309070f150c051002072907051606110301380f03101a0a030608 68
    0x20312810079a4480c40460b2514030002a5000b80c00c0424080140389001801c0940e2203000051a202041800000810302d00d4035026092145a160341c038242010403e03404c0c400c0c01d0300050601980341c041c820304154a900c82046040c03281c0314035641c4001891600c4544951000c9940120701c0d02c040421052241b0380b000241ea54001304030543c0024500701c41e035881c0d11b400310301d50003159100340200805400d00043c3c0e00518081c1c6420030a0b10700160b03480f8800c00040001c2c0c4204c014002c1c4561400702d110b405038402ca01c002d07002e601030b145a1001c81c00709a00f00d1b44030322011140303080c0c1040c80000800c02814220a0a200345203060760300c0c00d00b510003034018080d40c440800342802d41a843c100f00040c0e90015145080f1190302251a03507100c900303c990f00c0410490329102c0008026201c00d10007000d48a40381603136018a48580703080000b03103807515075600c01000030782c4000d2140300c000382007403440000003140350300240941e84440c1c040b5001170a03980b43d0b60040b6241d82c414000800503510003 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 418309217 1250 418307967 418307983
    0x2a03030a0e0d110901170f0105010621140112060c0c21050906030c0a1b02060906161406010611070e060904021305070804060b0102010c0e15040e0a020c0f0f 69
    0x1100c40c442d82c0907440c6007418003c04003425441e0032070780500c0005001d014804048608000c0303601691484401c0c0006942280d030240704940000d4401603007090024183d0003a81c011000c820070200d40e524040c060100c140c0d40aa2102822011440c02107041c403115125101c0c030f0610a1070b181d01003120a03264000c02c03c03002c0c0d4801d001d00751400d40c81c8054074002d070100c8004150281c07145480c2d00d07242c02c10307003031940211000d403012912020360382a00c0541800c4042015074000c1c05942050110002c3c0105a007040b4419030300c2070f03030074810300000c504800d1140c000082c03582d00030000327507041420041103d1052400685151310644044c032903201c84400640d4065801c0d01c0a01941c0d0f11800040c1000100107144070010b8982801d0198075544450024031035402032000780800d8105000481c00c8402d58a540e400040703031043d02882520300552001e0a122041c1500360415445030303910008140f042e11240410b950010381100c0e000d10a0140182c1c00400f4005400c1060b200542d8031344130551 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 418310467 1250 418309217 418309219
    0x614180702100e0604031b080a050a0509130504110d0803010909030e06030a051b04150f03061802040306050105030c0303031b070c0b1c02160807050a052a03030a0e 72
    0x1800008035031034400c015603041c07101810800d0240c401c01d181400d48881d415501900080d00103980c6904401d001800d4000b803990103880c6500c1d0022403541110103420a54048040000800840e4459607968100821282c0489000038550406141c0398021030320a41a05002d00e4400c1800408503146e00107490454400d01d00c0407aa8060518044038011003501103107a000d100802804401d41e210381c070080c07051206e401e0b5403101c81c0780081c17104a40d018521411603140400088220042d104a0b0720011500d001d04001c40c945e9241c0078001d610400c02c0346a840030f25030101c0c04105002c4075001e070700d004200507406028103002c0c02010a840c0c2c4001080040242d00b081005102c0180810443e4107a030b42021412201d281c8403030781100a98000f60010621500c40d5644c00c00c092001d00c00c403601c800500b65200801c00c0580e03510300c403a4000360405e5402c1d00070490a0004250300307100280c0d0100c008107903140b89a08206141042c54030b130858a030300a078801e11040340440d420180e09081a14 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 418311717 1250 418310467 418310509
    0xf250219060902090c120c09060703030b01120c030e0c0a301b0816081c0302070b09070503071a161e0501021b1501030b0408190e040614 60
    0x1580c0c0c01c000010380b00074000250400803140400020017074003005410054910511100d4940f541032480006004610005900c00d5080000c0c7c000203019a00613403460f4018189403c0e01003103040f10300125415080c0180100703484041054581c0303424045510341c00c1080b41c0c0b680741a410903110141103030400a58180d008441c215045400740350300084508550700240030a000c400c82d00851100c540d15100e102624801d00d5280103480141050400607140d07031600502809800b001c03100700306400000d2075424181c1c2004110302064600342294882e4100d00c00600940d07140c0340901d032510381b02c0d0344220f00014003440055861801d100444a0810044001031316507415401d01c0c411031490002c41c015a09040f8005c0d004000064010b04800750200c00c0250000d076428045680318441d46400c03401c59001c1600600c0051100001030307411034040c45660307040c0f040a00c00c1301e0400f0100d644507008500e10088400c940d203043c0c0138a1010301442001580b1121940000c1240082d4480035200070390 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 418312967 1250 418311717 418311763
    0xa09050102120d0c020a0f11100516080d1103130212063303010c02070501031505010e1e1002060109052202010c0809060703030b100c0312020a0c0b0f2502 68
    0x2031710030085a40029040b11860b101620249040030b800000280042c0c000c680708a91240964000c42c242c40e007450101d000c111200483d540c80901c04c3e40585503030001c8698072050001041d809501540c406c21441001c030520307190b0360040040d14204c00c0064842640007034104004164407806c00d0744c030b84030940f00e4000821061240701002842c030454a5415600c2c001b5001901603000a84008482007a00e04200b41c030140c982516032304800340942030205103017001c03110b4181825a11034194806202000410b80d4241d0300007240103400414010059102c0f0700140200580c40c42020341090b203100b000011040c191030f41c840009a0000701a05122403148002c050140c0e9000b00c49a1030801040e41d07507111303141c0c43c020780141302419425015032240c004400b50207000380c20a0301d600b41c0584510b0200c00d0441c0082002e0340c0041318010400c0114014040041c0300a140640140c052600400c014540a07550200c090f90200c020142841030a51405003036401007001c2030b00e05040c0200c80584 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 418314217 1250 418312967 418312991
    0xa15050709030f1110030c0e0f01091e0909031101050c0405100e03010e1204090f060303200c0a060f080609010e13060b090c0c070608010e0f0a1b050a09050102120d 72
    0x1032285040300b17822601084810700480d515a0001c0c0d0000090f4540c215070b4014030041c0800c82d5424249940820707910007040c000690700b10b401c1d0b040958142034111032151209141819501015070490210f100d4848842d010107081c018980e224001302d40082c146443d0000081500314282100804d100880461180c81d41302034104012001a00d41180c0100203100140f5100b40c0c0203100c0c0b00405458036806c428000304901a800880740c00d5594001085003944005000800380c24213001d0b20300c2104050b0425031100e010803402000f072600c071000501955400a824000300814961140a4020050040c9180315842d190400060058549810150324001c0010480c03000d1059101c40403108000d44410158020045060504141c560300d940c1c828040d02d09040030700030030309800240800191903800c0d8501440d0710040c051400b241f8518200401c6540f140400070b0440091070000780642d40359080703a103080c0206402c1c070040c1460818400d80c50381c00c0c0600e04614080c0c1d0f440d010903100e9 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 418315467 1250 418314217 418314233
    0x907030b04141506100201140109050613110301051e101107030c0b030103030207060207061e090506070605160e090402040b030f070b13090c17041b080a15050709030f 73
    0x1410382d5201c02c41e44440003582a2910380407085480601c182c0740c003aa5506201d03c11b006280060b464090300380d9003079080070445005800006c18040e001000410f048a400e00d5600842e00c1c09441003c2e4155a54100300921405840c01c40300703000d0124082100900c55203030307124204400d200e2403600c0d494400c12003503014241012940301500580311401c1c0411682000740045040783e220783c003101d18030703a51a00141c2e01e420b214445c1c0c2000c83c842286e8460341944003045000690411b1510064454030350000581540080e08240ca0700b0390740e103041242d0282214000b41d1404000e0600141035808000010b0302104020002409141c58a13985441074408110940898485100b92040683c0b5442200c080b80c0000c5040c05800c001860001006900d6100d108180205540c5e5411340d004c154440884680d0060300843c2c80c503d0b145010980071079a1464100035044040151440d8141404e149070180f004146942c60145008240103019412629000489600c400080c2064004d400d0640c8 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 418316717 1250 418315467 418315493
    0x20a20010f0302211005030708151e011701060f0e04060b0103051302041a04060b0703030501050a14010503190612060506100e090c09180f090a03120b03070506040b0a020d080907030b04 81
    0x7d01480ba65801140a250101e865104041080d05440a0b41c0d182e040041e144001f84025043d0895007e0040c00160820000c00041d40c0740320002054681d40c811441c12170502c0e0740c1c011203103034202c00c05100030040035001d580500603003440c00b4041d82c100002444900c07001058021301c15959008512448200c445499543c200000c0c010041c6642d50b03514130915030311410341140040c0c5460008161480c010b003100d400d8a04000352030841c0072050b80151041c0d800030b40100ca1507000c800311500b40301801e0140101420089030076031038808180c0741c064140c58003d01030324812441c408986461300d40c0000d1010355084200d0301c4000b1910380201812091013030036801030f00070b85210782a854035980c07030175214041c2c0744400200351940d9543c60102d454410000c801800a10843e00c01260000c582d0440700c0c03c0300303004040c0c3c1c02da541c1d1b810000e000e40c1d110358000c8941e90000b00d50307407044a4050203444556942c0c0c0c14404d10615141e0361003600c0d040207010061150740000042400d02c22550100c00c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 418317967 1250 418316717 418316719
    0x40c0b0a11060a2703020a0209070507020d054e040f0e10060e0904020103050a06050d06090c0f0305030a050f0f0c1b0111060a0b01020a20010f0302211005 68
    0x28815003414030700c00014000504d560030000015404061800030f07005800382c0000c3d0142c0c09004401c03542e42c00c000d4448409007003e0200407083c0040d1025980f000e8070050160301c02c4e130051543d1276191481a030105201102c1c60050711502400203c10301c0e014a10100146030f0f151303c00c102422103e00c6a07283d005980164041150501000c5a80f03c015004c1c60300406080c481c0848040d5200e40071503511844000807900041d120380401d0041d40030340c20840d00802c4a00340410030584400120f0010259103008ae10260b440d68802424040c842d01310b00003404080200303410321811a2580303641d0707114000c0900200000064a1908001000b041c0c68207808140c80e0b6941c0c60408012150342d541a0070f410381c840940348070765104a98001c3e409040700e44100e101500060303450143c2400140390040303000d41940140036000000810603a42d0084100c007001000b0007002075103000400c0380e05076400c00c03814184100542c81d251945020070300b5491a981a03400d425030303104628607224145036403042d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 418319217 1250 418317967 418317973
    0x1171b0a050403051203191104170a120309050303011a042711040f0b0904020c150718050a0306020a09090e0c1e0f10020f03070308011706040c0b0a11 66
    0x40c505240c1d0141c02070003140e006104503000720004002c01c0400d44400d4680b0004e0507a28140300710101d5039908800d01c1c1213800050b46c2e04065840f40b180003d207055000c0001140c106940920400c0030180d007602e14881949400c119131a45030341d43c20f55921060142c20032503402800001a400703035410841700903142ea0b040580c0d444201c0d50241c50554480c0742055041070900e401840c590703650600f610300700c2d910703840708900161505510000a0f803100a06c40e40094081101c892490f0301001003201070111110240e22a00e0013a40003008a20b5602140303100c40400c140811090f52402e81140640b82c102c0c40041e66241c0b180410f40300d00c1e440d640a40c40d11400c280c840d0800150100300d440744030700c00380d808000c3d00b08480c17000d51203010079114440d0300039040b154041c030780e091201c01c8074110b14403401101c0c240c0c2031104810340f4503001300f0011000110000c005202e12101141a1203c00240000420050801d583c0d00b0031803181600444800160110f0289035880c403c010b510002025a410303 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 418320467 1250 418319217 418319227
    0x501021e0408060f060310020702010909021303020a06020607080f06040b0a031407140a030b06030709060e01031e0c0e060102031209010e1c020c0103020708090306090708160501171b 80
    0xa034960410301c00c1900b43c0c018080014030114001007030911941008002d8104030112012040080d0401c007000e904100307a003440841c034000c99100405144000c820740081051a500c1040190b02441e01304108540100f020f00001c25004004160801e01c141141d100a03594007020500922060010f00e0388901c0503d000000d00c041089c811020002960945600340d0301e403000207842e03480716000b0300d03000b0f5040081040400c04281503583c000300c0080507038050301e68904c42c10007610817036001440c641e0941c0004008004e68001d0440d455417a00768498000101600c07840311540841c0b1030310860080301c41c005079603a8400c0c03044a0b200d550180703180400c0e04001c41d11500800345101c0c05c1c0b5041c41506406149003000c5007103052010100d034003c008100c1510300450194202c50340c1158110b10a103d1042c03903030b5051000c28854400321008006207860460344900d03011000c410032009200c4002d0a1119981c002c0c11510360020f00c244c0c0d440303030b52030321200800e003080c0500d414400c8a0010503 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 418321717 1250 418320467 418320517
    0x4030b13051005180106270608120a030f0b180406020d0903020715080105061b0c060a0e03060f01080c0f0d0807050d080c041503090c0305030a0504031403040b16050102 74
    0x4801401415901c82d0a0740c00c65542c2c40c002c1c202c0312a4060400c1902d07029621900c2c0c03a000311f50304010b21a1203400410500d81d104406840c0007428609000203040200c0c0c404190307a4180700e55540040424418002c040d16a000b107400034180d000d0103c0d40c0303c1c04500041c10b001a640444124040400041102541c0b034100251100c841c4c2c00b0784100300017040300d440c204e2840323210494140c0d4030041000e072408183d01801a068501c210084160f0700030741021000c07035030300d40c2c0141c02290211346615810800c1d400406041c1600103100078401072907000113005404002a8265040c4c0095890050005800e00010070103054100014904400090f401c420082d01048503401520359444042d280c1d1159000a04a8055030088560076144050b501400d140319400c0400094003842d418401113449403211030555000781c1070000424400101042003240c0500807092680f8000701641c20142071801140081c81031041192f49000c80c1d10017241404000e504442003584c00c040e41030440c2410103 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 418322967 1250 418321717 418321721
    0xd030c080a110106050f09060d0303060f0e0106021c0e100207030b01120308090a020d0f110907050a12140c280c0b06030a0b07081003060e0303011505070804030b130510 74
    0x4400c030b0945509003c00000c0e01d080175400384a00180092171148255266028000000700e00081542019114100090b03003064826440d00600f00c1440c1e658450341c104103019103400c1c810800301c09200f001260b01220154400f5075500841011a006030415001150403882d208568202412841c84500009800d01001100741c1085200e9201c900c0c159551808998490001010281d00044010300100020354400109070040b0b10883c4031400b0900e4440c0494042c02c01250f003100070410006048904980107030308644103041404003801141f1640a02c035400b080c000c1e000262025021a19030150005082c0300c040b281385281e5100d140141c0c2000040402200b6141580c0a59209000c21035074200401c84034145904014442c00e50340358464200e6403400001c2c0100c072903419044011000404038002d5141b514481d0000715125410003011034100d654055040c002d100c0d04000081c0091421400d48044035003102540e4a00e0b952007161141c04003d40200600500030309209000301c4d00d0701c0d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 418324217 1250 418322967 418322987
    0x15020619060f120515040f11060f130f0b07020a1a071509060b060301081504081c06031101020d0f05090109051518040209010c060b0301140c0309010c0503070e0d030c080a 75
    0x1340d011101036100c00140396604180031744014080c007101010440c003007003108882c00d9000c0c60180c030071440d00c80392254a01e0304d40c110b0316003600000301e110410040380c0c410613240009002080c0c40180341c454940c0c0021402e81a5100c0c4124180420302c20307602d500b020381c0641d51482d401102103091001c0048161005248011b403c1755030030310b004176114181c01e012040e00c0c1a02c08c0440200002010381f5199082c1100003081120110380c10414020301600f818426001002d84240101759541180360a059600c41c1c041d45504560010081840e401d50024039030740d07131000609040c0c0d070710040c44004813000e02240c0c00854200041c1038072240c82111072801070003110b00040d9a0401d021810041100341d00c5180301349800285015480c101055640d4070010498900500010310700c0140d41c00085003050803503440710310340d00100800502c130000303000d94000e4505a03d05546107250082002e0724008a080c401405020510b80c6441014000c024401c503a5401c05422a101d00141c03400804024803 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 418325467 1250 418324217 418324223
    0x804260c01060e01030807021207050a0f170105100e090c0402070809030f1f0c0e040507020303041b0608160c05071401030605010914061606060e040201030615020619060f12 76
    0x18152002410b94090f0b0322403070603130f64051030191502003550200000c244c81d0346003029103400b40f034500052554900401400918040001c00803161408000150400035009141c5c0b03641d041c4002c2007001c0c400d0102600984103612203403c0161150007180385084100e5502c560403900c005078490501281d00c1c0603120300310084040391b202007191000346480300083d108004226045500c2c0c060350700300d6500040120499031914070302d6459020700180540b542900c0c1c0c0000361b0400024002404180c603040c10003c0c105550f0f1031006481d2a00060140310000d084184401540010100350ba01c94181461000d810004448070692140b15001d0f500000003812404a0b02e8080300148a50040d9060000c82e0615a445090b140422041c0b004a51280c1c103000350481d503190a82c00001e00b948189000780c004c0c07081c0040d07103250510000d001c682d056004400f03c1d070404580c0520181d400102e90758400c141c2c450180c0c4a44002c2c01401c05401c0940120101c222422400320b25507074494072803100580 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 418326717 1250 418325467 418325471
    0xa02061501020a03020d200114010503010506192102030d0305090601050d1e050f0f0304050f04020f030601030f061a070605011706010311180103140601060914010804260c01 76
    0x38105005903503648900d071005000d07800040d0004540c3d4059000b0030511900a52100c00613680c40e1016404c4880107061180045581c00041c042d078102480f40b15440b490954000c5808046120100a004024031034641c4000105890b0a4501c0309622040304881d805021a44000c60403078003d4042e007003c495504030b500c1040000905480d229004402042e00116060450340c02e4a181c1000e00d2200502690a0300c00d5403181c0c401d130b070001c000c4103007039400d510003643e04c81d401c10041007000803a1913409882a801407200500030356256013200d03044003003405c1c0094070546040b1480080d1000d980000d036402c951a800311070380051b1b41c009000d0103200315030400480c0e17211096030811401c001c17903210340303070307100600620000d0301280341c0241d5480010481c4000d1417a542d0b031081008001d0304100c071140d01c2d16003c11003e00b8100889405000d5900309031200c40d09080d843c003212284481410304200f51076021906014107500010508030162a00c2c807500c4c40445a0075031540e000d190940c06540c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 418327967 1250 418326717 418326751
    0x207060b031c2003040e010611241017030703020609071a0307020a06050a060513060513230a1e050c04030602070614160f0201020403080d0509120a0206 67
    0xc41d0100b18039940401d0b03404001040401c549044400108000b4200d14103004610307800440d54080001e44010852502c06401c2d80d030510000400040c2440c030000c165910190038407c1c00501642200044d02810744140c03020f0740c41103100640142c0350b901c001070710865152600f0740043c1c04802005054003035000c40c0c00944a0740d0325540d03a4003070761044a0100762102d400d140708105000043d0f401c40203d1044031900a100c3c0c60b040200c1e00165000b198a6941720000c00c040c1c140710b0b00400608070182020060980303024049100b07508402c15410740306596440801002070344203d5070034064101c810703283d640d141c600351541c028a003941c0c07503281d082c1e4080040c11984c4d455009080c07184203056007190505165544031006500030100859929469202d40c00b07044025003903041c4510300d030600c3c0441078803400001170a005507900c208401c41e40104424408989008111a45640628800100c0740d40d0280c0503424082702202140e207024002441410083e40000c0e1140a402540c008120136 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 418329217 1250 418327967 418327969
    0x219090f05010c0507090209180709051003021801080c070f060c03110708040302131b0215010617040f030903050601180612150c140705160602010e1209030102040b04090207060b 78
    0x180c3c040780d00200300303070301096040c4688081500a0001d450016004554098881c000c00000c0c403800c031790751000540ba2400802c02c5280102000703071801440c0c01c00310b00c0d01c8907014541d0540541c91862505029050001c6800c031034104003150001e642043d600c80c8c2c06945450410007510b45003044200007818008002c2d07240c0c0e441402c0320301c01648a01c0c070915152556003440403c000046d40c2c540040c1c0d030741550a01c1900f00350234601400d00d0b1076000d4454100f040750180105041a0802c40806c13041c480c4011b1a58504000c550700f00d600100030601c4071030545022030300402c0d60b400062260152a0001038600031070402c0006031641d802051100585901040d4042c40f40210301800e142100e08a50300720a230070b0703404a0f40301c0c20249400845424030001041c81a4801c01017203070160700960136403a103400c0403590000038110f40d1009002c071b6004480e24507502c0ca0a0146040000da0008940766140d03000d45c1200c000f03040b42c09a081c0c58540d40c0444000a401002c400d882c282d042403043c46031 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 418330467 1250 418329217 418329227
    0x9020f0303130509070908150c0f030405010209150301061d150c030a0e090714030402040902100203090a090c05070b0907091a0f151c0204031a0702070b09090106080a0219090f0501 79
    0x42d502d8041c01000c03001c69001000230010341c00b600081d10b250003000240c0098204500440c4100e024900147c7d079880030b8414018040070807a540d0903903a0040c4010301203503030701510322100140c07140060b0000000c42c600051403040103400b818102c150006030540c1865021016040c0d50314181c03035502c201c0441c542801785c2100100d810100182482c0e54000c40c0410b91406075800c28000b07400010241c2c10b0782c1c00310f10708210038141d64015070b2001c1418043c910b401781c040b04c003820005c9000c0c445031700c8107031024105004a02c0020301030102000003a441c10400c21460005082c045024020840010500300480300c80b1400340f4098070480c9030846081c203010100e100c241000c40c00851808409004100c0d24400d0b0000c4149101d40810000010855900c2010642a1442074200f8203082c9140d01a18100081d4440b4031a640240b227403c10582d100e81541d8110345c1141010501a40e42000c0507000303214055600300c012028207082340301d296021513020251044044041000c5071a4001514 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 418331717 1250 418330467 418330469
    0x90e070504080c06030c1204060501090608030f09041830210c03113405060703050612061303030b0658050609061309020f03031305090709 61
    0x140b80d501052407071516082480013954800da41aa9007414041c4112246d8610882602c0950f0901e0b1100010f1003c004240300e1100103100300c5d0000d40c50145040320600326400741444162280d0f82d111110510000f40c582c80ca44165440705a0940301c80b884040e400c00200c114107034a400880c7c540000e40e60b07601502030000b421014024200813004804944000703060030160402c2015186e512160012444038094854200071050840c1040c407488007280030400010f408000528a104144011460104500ba00418039103000325503651024007080010300c0d4401d5195061081c4000c2001d00650500205442e078481c4c1d0702886800d01100030000f00b40156401407100f0076103440c1c00c2840c5060802c0d0f418124500c200c4280c1c02091000c62184445a07002b10b0a4542d5081c2d00480c640710140d100323083d40322104881c24850740c10008080381c1100409c01c5c0304500e0750307070b01c0840c00107641e108101c0398410382004003102d60b074000903051201d4002a51003143d0043c03c070000800c4080c0d0084080700 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 418332967 1250 418331717 418331729
    0x110f0306060906060c340b0a05070602091201020d050105011e0c1a07020d02010e070323011d03090a050a061e051909140910051011010903090e070504 66
    0x2240d59200d0108004088401400c1c441d4005401c10021801e0304d400e111441030360071581007410100c54100400710a00d10780b0840d00b160583c000009014403007000f8103a0b04569424500b0301d032120a0362034408000c0c803c0f42400c035400100005421907107981500180501c0c90a004240318a990341e100541d03040c4540c02003016080003081158684510820881e0384079030064070140c9200b60b801e43d03205040402550700300f0040e084641e00011305502405010500c2501d00010f100f03152568a80c4030b202110500f940a44034481d004400d42e40009401120300003070b49280c0d500701c1090380001c2d5507699000c000d41d203005030784814000640307103007210303c500403101d041c1c481d18461442c0d0000381208000d0904a0700510105001080000e100406001225921512062501d60400780b40034150310103914103070701c80e07200c4108000600000d90b00b11012074030151460040c40010306000e580302003401c14070b1a00c540c6014003000034036a201120340308035403240b04040b03026142c0401c211841c3c4200e020700 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 418334217 1250 418332967 418332973
    0x30f061a010906050901090f03030507020909121801121416020304180b030f06040b0a0b04200c0a0f08030a0b0d0c0e06012706081f0e0a0204120c03110f03 68
    0x8200743da0080e00281117442c0c0515041d50f642d81c07115204820340c00307960001d0300000c2c800305610085080a030010764100345140020300c40450003018428041c4903046a80411294035690001d03640d0146028128484800f00117126000d00c1008901c41e200c0100d460600b040240c07840002803500200846040d07494101000d50160400081200603100b4030062a0f094404c40d00c5000e010700050044500982c4641e2150310b040c105102c05e20155903071031000520071440c1140711000e15090004007850400c6415915807a40f0f0740d201c0090401c100e012028080c0c80310569104104408507004620481908904122a0380c189043c81158032680400420041e5541c02c10b22050074541c244550101e4140340010444040361040c800014003010f405041d41902c8e0310600c81e0a4000c00c0003984219120880498101c4900c110804081c072803084000c10085800406c1c0d050390070b40c0496000d003045400304143c1902c9891f0400703911030f00b48411342d1402800c6082c00987d2404038000d1200000050003 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 418335467 1250 418334217 418334219
    0x10c021903021207110303040b131a1207020c120709200f1309290346030503070306050109120b0702010f050112350a050f04030f061a0109 61
    0xa401c459000113010360351042c241e4815591070390200005e0000d401c26006403900c030301041c882000030307851a4000e110004e9101a40070b250020060540703022604056000072103840b100000e03410103400348881c940101c096822840581c40001e5000203c0d400a001001032001c0041015501150642c1480000314104248030b120784280002d0700c0c40300400300c0040c02685d580c141d07030340444400318052011140603c423400241c444158601742e442c0c01c02d07006011041c0f0348641c2d41200b0003404001c094010482c0b0441b2810891141074424a61805051010b10201c0d03070902518030340080350701d000060b042044c08101944142065021100761305800080d800703003030741d5024201d08010420411996203400c1d0742c02000380c6004150080c03d01c03417014440e010050400044221445558030304130310300c0114214413094484035481048280b0130520703444c0c941303415080b145803091300c40400c0c0b0018086808014069010790340c450f914420b980400042e1200348040040021820301c0902046402d54 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 418336717 1250 418335467 418335493
    0xb072c270117010b060706050a0c02071a0c0a05030a03140a0c0e0907030f0f06081e0c0d17070c0f090b0d12170109050610110c060a0917010c02190302 66
    0x1c03404012070002c5002181c0302c00074002241058001030400c5c0c494a465005000c5960207900c94464050380d1807003c1c00a0908191050000d03204203000710b90100d03000036541e49020800d0103c400643e9000c0c0c00c0c0c0c0d603140440c2c50000c015040309030265501110010109041c0c90140c82216035449039500c030000aa02448100222218000c01c807400b416100c0e00c4841694a4510401000d00d081c0100015502d0900444034030f030200c11000704000080c08110340f0200c80b0001150400b41d5003c80c1d10000b00512898560315a1600f48541e0081d54400314074102000f070301d002000c09881c2c42403a410005030f0744000c84000d458400841580040c010b162460110301c0c180d070703d1840f1001c3c5c0d041a003000c800c03500a0440141090707202030400b6540b04107024091410401a0311316002e5480c1280d25090703d86040c5403a1311004e01c1d058440d000c0022034404850141114800074036040401c10078a8102c0440d09018081030b4074201c0050191150b141400700524002074441c9400d40c1c002c0c124803840e46 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 418337967 1250 418336717 418336739
    0x3071103060f0415110304030f02010606031107142811060702100e010509100e030c0109050a090c020a020a03121202041d060a0506040602071701090f0b072c2701 71
    0x1109144100b038894280c05d4100b0103550096010300d00c2076941d0310203905600402403c42c1d4041e0014400c03d4241801d00f005041c2c141c0541d19119001040009131f403060603215454640c2c00c003640c2a11070714400c185920084800b01c1e101044c4c2c0680c091404940024080202622854600941c0190b0340c18001c1203a92007409641000c05060500300d02d0070503044001110b815034256080f00156202048c01d10300c0c10309012501e8154800e08040d081582044000b441c0d0000a0060840c0c0b03c0d90390948008440c400c01602000300c0e000303084c90100d6520303810162100300031030080d50042000046100c030000d110303108071070485e501c0a55021a964046c048c01c45054406010303140d0103400c41001044907581c0c940104024484c0350000d00c44d10380344c008502c004410302000d4191030391501c01848082a00740c0e004140155210f4121051a90755040c15a00c0c0c00000400d16070b80c81548a81e100c9004e50180c135801141d9003150030048481002019031220800001a0741104600f6001005420202 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 418339217 1250 418337967 418337993
    0x6080910112a162111091b19020609062401090b0d0203160216030215070b0f0a1401080d0f20060105010909090f021e09040503071103060f04 62
    0x41074102e9500e2402280062030030b0791891142074401c0c5007410410400501c1182c28500310000c041d10f40305880a03880324060407104c105c02c3c50248001e003001600341c2c0e4840c1002d0180c030082c0103125803030340c40407135a030128200c2038403940c0050321903403000c11000e0030002000740c030070840a040e019100746011480000741070044041410b001100b0300100c0d0080f11007003c0c224040340d41a006850b4984006101e0b80140042c507820195000544c1c3c0c072284000382e40765082940d0701036505000034844211204840d108840c0081c001034035590900100000302d086c164043c844910040c45000d10b42010340100000170301ca4442d56a000e50584159a4059010309031140164202040000f680140701e400e4117040b0b85640d419504000018051580c04c000713000b01412240000300420701c0c082d130b0b030000380190803507020348581440ca107421071040034500c01002050002e41002000d00f01460083e0303803604611011944401e66485580d42801c4c0042e08501c01ca90504480071192603d850302a54400d01d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 418340467 1250 418339217 418339267
    0x818180103110109090f02071101170a021602060706060801110f03060f03030f120618070512061203041d16020709020904020d060602101505010e01200105010608091011 74
    0x810b04c00001d0784c00c200d200310007104551150140e0750702000d140080605641d505800d040c051100b003524542503ca00b5a181d000c1c0680400603a6030300a2121a082221010b400035400070303000440c44100300254101c02e00b1509598020b0100a20140d0481b140340070381844494500c00500000b001d515100c2c01e14481c100c0068283d81c9020304a107000c0c4140d034082c89010078051118400d0000e1030500380404142e2001511032680e0b10f0405040082192282156405290002c0001720b0156a036004070001500c00d0b150440307a071a5510395107607152a001c00005110103103484001246403001c54403e1a0040065026120702e40c03c0c100ca800080d003000764001d80080e824000c0504c41d6216119040c00b9040c00c1d0003c00c100940e001c011016128241004055100b8111017045166080318000d0003030042402e201010319034140341484486074004411000d50700b08400022059003000802c1e002e5607039181035803181c0c0b5182840340c042d244411010fa0184804000101d41c0503d40b402400035848 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 418341717 1250 418340467 418340477
    0xa03240c020105330405100f08241017010b0306090d08070f0e030a0c05030d020d0e0607080c06180d08010303080708040602091005030612120f03100b0708181801031101 74
    0x185030301c00b02c0c08461003124500f42e28291a0014041004003282d0300000f805180d000b041040d410f000f0a03030364113540030b0300001840b401c0c00100702f4003980e802030035020300240740c200300c0f00603480c01c0e69901030980402064007a00500d8040f5203440700115105045183c140c607441070646840070112426281c7c43c07400c004000d2008124a51070303a051081b13186842c02420616041410b0204043c1410f0901c001c140a40d8042e071004c2d040d4641118411409030710803101c0b01c0d185c51517810142c140d8414180382d80381385e004603000c001800310058010007021000004844009442201c00d0320703404820b020207400305d07800f5400251140c0c49007482070380c0144900005070600039004081400101030a03003da0100e00d01100304803550610280207a4481503240003408010019103c242c118422010b894105400000018440b40c20020311000240307141202a03a0f00c0c6a507040070302c001e4100810060010340d051020381c640b0304c1c00c11024559420700c07001a0b00f842e40f842e982c0c500881150884541880 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 418342967 1250 418341717 418341811
    0x130501020403030c12230d0b03070f080c0307030c0e070c0609200402070b0f04050c0306010e01030c0b0306031c030f2903010504030503150a03240c020105 68
    0x50080c0080c1c00194860f440b18800004649003a2600480400c2d9100411505056030f806044402c003500c1103020902c550107541c0c1c0507440d40d1b2405070843c10f142e242c0520507180002004604580c01c6011a01c0a031300b500d0000400900b0541c03924400d200140818100714414060100031840707880d00841c050810b07240031000d59464805562654800780c400d0803404826118202c03000c0e80d1020401800c9404525140040e03889800f00c51015000c4c4c00c00b40c010100140400c0000c11210404481c020101e4441d5a034800800c86140002d01040350351030032441d40001e0703d00c140005d0368090140100503054a040f458141c40702c0700070f440c410608164640409003102001c80c400d41608800861350f130304690124400c102d49405580240320300aa26003001c10020aa011081d81d41212024000a00d00303141c000028182c103007960005807200b0703a4440040f004d01100c50340c0410328183e1041c14461030308507060a0382203c1c8100c4480203054607080142d104800e521101c80410201403401c00c03146 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 418344217 1250 418342967 418342973
    0xe190b0102102306010f02030a050310030203010e0604200127031b03021f0203090127090e15190f02040e090304031a01051305150d060b2b03050313 65
    0x248080f00500d41002842c55652200240e0b0314140780c3e0b0056003824068103448102100a41c0c0388244286502003010100101e01c0c0c4a10b040301000040d40c0041c006d002d50342c0000d050759110002994200c4421701c4801818108005c800c42c800344800c01619201e002c1c100c0c4070454400c9025211000e0300d8070b00003e00200002c0c1c00c44510011840c607a0b030000788038074118414460f81010079440c021200c005044014490780d400030827544a0704080c80c200448080e508184080004c551a03608006c3c2c0c90b84001103804060740d4005c9101900001c21100d080f2081804800030850544820182e685910052246401141c210031243e20b180d035001403919550340c03074400460005480039089508001010003c3c090014250b45d0340000d584500f4002c0d501d444000303881c4028840c03018408686882c0041c01015034490300d802082c1c0041e011100c000d0280c94000300608040351082d21401b8812030140c028200348684401c1c0900e0000c07554188901034606842a801c000d110885191500700340c0c2c400 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 418345323 1106 418344217 418344221
    0x210516051b180c1e0a020c15030910050c22050306010e0c030610030b0904060501050a08010e1905160305060403030b01110d080c0d14040c0e190b010210 67
    0x650403054580820103829001e000381300010101e480c0c02d04640100c0d003110120403c40e049101e40c07091404400043c00161203a048a81c081c407101c2d02001c0362a8845504100d44144070741c03c00c0ca400c92020700e01003070748162170302740700300756000700305504042024a0241094a0350040b03c0d2401c3e40800300180070013800d0900c1502500808005140640d010403020b480141102e005481d02e41040c001804c002e101e0b46005901c1c00340000b40320780041c49002264500710002e402413038120200c3c4003001c414904203490310b004c1c80640d4940750140c045410011071140020b401e40d880d00c2c8c1005400c54200840c480d040c480405c070207481c90500813400000308041414113000c180c58a110b00701c0a4020807541064561900e1482c090f814071344d41b03131070b0b2240340700f100c58004040c0c0360341a5441000e01901d020071205854980188000c610707030010040c40d44107104035091300040c0c08900c01 = true := by decide +kernel

theorem cover : BRFrame.Cov 418165467 418345323 := by
  have h0 := BRFrame.cov_init 418165467
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418165467 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 418165467 ≤ n) (h2 : n < 418345323) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
