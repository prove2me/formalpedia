-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2434
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:42:19.961838+00:00
-- url     : https://prove2.me/submissions/e34849e8-35d4-4c09-af4a-a07a3925c0c5

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 437589928 ≤ n < 437769784 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 437591178 1250 437589928 437589941
    0x12011205030d09050c0907020307030e0f10050d11070b07020709020a05090d0f05120a14040503120307090b13060e0a14060703030f051f08010c050409020912010905060901140c070303 80
    0x10800c441786281c2d0303400000c81c2001c0840391080113034404507007041856800110710141c00703804d5821859042103840400c01001011700800d05105001500c0e10425146600861500905055050711001649007120380c62000f91303242001841541004600072a1504c00c9401d0402c0c036444052074404480140124219090400c2e16109000244c03a0080355040c040c043c801c00000c101701d03640303c561240c05045499509241c040050701440180070a0b10005186400f8580e80c4011580340d41c0c07040d204568020064010980708031010500f1580c001c0e280a8080580305551100e0312915261020f1040a50040c8104080c0e0310036103200c04003a09200b002014860301919011901c04004100107080c1c94080c1c50307502400c2c0b11910f0919041180c019140d01800c0000020300c20b007901800d004001d800345018882100c1da0000355002c09580311040b0440d4090004024070201d040c906015444c1c60b82200c084145508145030180344004120505108110700b0b1891424020692401c8009058 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 437592428 1250 437591178 437591183
    0x51c14030105130b090c030601090e360d05031509090607030e0a0206031602160303080f10030519020a0819120306170708011b1b03022112011205030d09 67
    0x283c8084001003622001115482600d031045099948e041c54000100420520340c00143c10300512000c1c0f0500c01502035248036084d0300c0c89403c0c44820942002581e45000c241c1c1e406d02c031845504054014035400034082d43c0710340c1c000d0b51205a40340e042401c0c0306c05428111150311443c0c00510004a50380d000f503105c0d05400c00c10004507003100e20143e0205140e40d00540f2120624040316045506c0710358100030301d1001040603040e4400c0346165940c0a4481f510143c2101e00d46001c0300f001075900c01c1d0302400540196000030484442180c00580c600c038458a07040140d024843d581004150031200141b444c1c10b0216417050050544016103c03800807054480300d180070140c03500000140c00d404c01c6005250204d02c1000380032410303e001c00450841c0c0000d500d01c0450f59940d80450b66080d0010a00c00c4010540b01206c0c2d56600c591808a0074690803080c00d03075940400103807203c80702010b0405008203243c042c8102090382d80baa00003140320090141c0041c010b42c02085207030b05414558000c20001c0e031 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 437593678 1250 437592428 437592431
    0x32405060607021e1210050903070803043806010305181207020414010608070e010f09060f02070906090209030f0f030720150702030d03050702060a090816051c1403010513 75
    0x1512000050640b40d85600f4081780c1d46c1c056a42840e07690880d110b01900040303070b031000314034003003c80d5100d800718040104040c102d801c1901c0f0071501c005c1000784003014451596611880361a240148107402d290980361980002e2511002520a00c18a03204094117a008401000d11078401160710002d40c0c441c8204907081a140c1100070340000142900901a01158503042d4961a00142c020060350120208504200c5542c3c01102e906400441400a54221340713000d051042c0e1084081e8600b280e958440e202c1c140c83c1c8200042c1c03680461740a00303503a04c800c4042e1840d1030403100301c0640c1c1d140900b40b506220b400800c2010005000140c6130804441341220100f1803c210900080741480d04414004007480b002528204500c0c0510045c80e40720600c0c141088a4204008000d40d54072005040c0540c407540c840880e024001c110058a091030074841031280240021b01c1c29030385441070f0000c0b0200760119840083ca02502800328030010a0442026a0841c4c0ca02810416a0300101c8000e00c0c000d03 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 437594928 1250 437593678 437593729
    0xb10120b13110307170415180b0106022409031b161d010e0702120903011401121202120a032d090c0b0a1409030c0a03240506060702 58
    0x24001c1004404800c41c030240c0364540003401801c170002040030036203865100c408000c006042e084203800d43e40c2c0d410a000a440c440c1543c01029036015240c003400a07441034000003011980090400095a407a0f018290000c00e00c080c00b624174201559000c4603504107000d01c1501402c04803010032480345601c12212800054030340d1500c2c10031182c02030301941494261041c2d8440342e5408090050111140d0000310b4544102d009488042c02262013261079800071f002c083d1690f0940013070000815001c1d0b82e14032541e50b507100c003c80401c0030000701d94402d00c0c00c480b803051500100d07000c50103007403440d01d0601c1c200036404110300034606194602c00350b4800c500401c0c002c05c040a03084c1118100e00c000010079403824101200c140381180e2151900e49400c1101000c129480a102d500600c44440404d8076600c0c849d00190a0003c0310f144c41d6000000b0f48000820b102426590008805c1c0d1503034858803482e4281003003000e60304111841d54010700c1c00c10907100181030880c3e2a18902e0190f60000000 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 437596178 1250 437594928 437594959
    0x315030b0c07170903011b0203071101140c0109020f010c0302060412050f04060210060510050a050f0c0613030e040501210614010b1e070c0b0a030b1908010b10120b 72
    0x9079000d00041a40e12000b00b0450310300d0500348549021fa140c0c000c207250a403025540020341d01d100302d004c000e03d031221030010718903d40d01503083c0e0802191700d2101140c85800b21040c081c000c10307100100368400c1840094108455008241d5401c900350541d010303141d83c0d901c58440c80490303c15040107104000c0100440d0a9114203c0054005840c60354003508940170030049410903500300d40c001c14130541b4440100304c031503501725044504450840c14103917200c15001581030f81c1e600440d481030301280600c504103d01c207842e41254242081c0300741c5548404030803060511040b24803d00030021301c10b80e010305010002e20b400007081d5646105640c04600c46c030b01d100301a407034994282d000c00820f04002c038500e092500c900c1d030049081228818800d003440015151099a5000e9120b1907904070b03400a000321a4600c660800096940007500403d00e4403020083e1610300d60440c440c1c0360079946060108042890b021211215600d51680c070501c0c040015180740d4000c240c05001a40c0c400e1418948840 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 437597428 1250 437596178 437596193
    0x8010b032b080c25151a1002030408010f051e01030305070303020c0c0a06020c211e070f180612051b1c060606081f0e04080f030f010f05010315030b0c07 67
    0x5400c0c0000c0d544c000044003600c0c11114411641c000d885926040003500440900050381c40328007050110340c810100d064000c020703811882070342c0042030b05509220940c1000e1800b5040350f802140300d441c611110718102203001401c5403080c000140000d40400034440801d210384c01410f100300015099600004400d40000e9203402c0c103a02800168000d100715030001c5c03901c8004080c60301c6248210003101280032852a03264050100a40402070340901041080c03003041159002030104148600301c8144c8580c0000800310100c00c0714408907041c4040818502c00c1c0d02e0403103d520b40c1c4070004054480481000a50240c002c1c040c480c0c1100c0391110385042524000070380da86450107440009591030420b40c004081c1c60008000440f002c500d010740a0702000fa010142c41216501d85041c0e4040d211480c0803051381c810140515148100407042c8800038040b1182941264070b4849084001551600103400760383c1c2e45140d00030302d62621001003020800d009010b40d0321800380e2800c1e41c07070603038190303039542 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 437598678 1250 437597428 437597467
    0xd0f05090a031101020a081602030712020f07050f09041104020f210603061902210403030c02010f110708071401021201030303060812040306020a031508010b032b080c 73
    0x903029808101c025040c903403c10408012181000029440e0403d400c50103081030f800601140d00e480c10301441481820700c20710949200a501c500502c0103240c020743c000b51348130002c2005c20704078010910300140d145040b641c41414036001502405c10396669440f500d04090f0203014264100d6000c000540b00000c603200280211481c1644598031140c4640c95150100d82c000c0c00d1318080e40c0043d091003442100201e40441a80a000c001f5944904003095a51070a051401d42482000c400d0305210405405811404000700254003c201211076103402c1405d0b00da0072101514100410440340c00460a83c10042408500804034804000c4040ca0f0180c22a440001b030065600da40307000500825516010340c000920415005000c00c01c41000f03080124404e51200a00e00c83e400904560890f0080e088000742018080f00c10384000d03a104940c9003e0701000481602c80e0151280b5407a28000b2800101092003d0081840360101034a0b002d48a58001500024400d4424405111010305d02c80514 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 437599928 1250 437598678 437598691
    0x3020703140f04030c09050c030c0d0e0a080306030d0e150a030603020d1a0a020a0e040504060b0d03091a030415050910020f07060b03011b1d06030c031f06140d0f05 72
    0x31680ca5195003445c0300c3e00d1105801800340d90381000c051100c0454554103503a005400305145942c1c039a070030034024008055940246000e4022150604107014044000d1845a00c084e01a5041110044001c440c40041d04480c03c0d84940f114486031040303003000024101941c1075003400910591a0b40018040516000701151a041440c02d040094111481c1e0184c00200c1c5c010150304101e003030600a40840c82c0001605e008907640c0c2c0002d002c0c00b0650700650074007400506104080445401d0040010103075000750755040c42c0e9004c0c404208240002164411b175040801041c04170f030701000c90f40c05040042c0000307038148a4840300c400459894401085525024440d060703a410031854031006a40003c00064402d925040342c0c00074110a00b80c090740b00420901c0c0c00041401010b07611061241c10309420307900180040200180c40040600850003203401d207010000078001a5402548251580902c2c8001441c9426900300610030324040e00ca0f40303151410104040354640340304011104100c442 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 437601178 1250 437599928 437599957
    0x50127061115270d0e040b040f051305071d0c0304080f0d0606030b0d030534060902240f0c19060c081005030c0f0d0506010e1006020109120302070314 66
    0xb090b052441c072002d001039000e07040180c200344c0c0308044050300c8200b9041415014980f22410000103a071103a0000d031030391208000030400303401c000c1007003211803001d01c6088505100c0c00801050075120b000c4035003481002d03a4400b044542d0748540c4440640c1014200301d43c404c07000d000c542d681302c5a20004d0700d40d4074551403001900c0391401030020f05461001d44404e00921a00c2c02c400e020940c031030100c4800103040c004010003e081d00d000e104140d04030b0361401c01c0c101600e0140740208039407600f102c444540225540c044030300d40c010300041034041c0305410031941d00c010080d032040c000340d120103000f0288114055441c910080e1071006d101e401c80d040f0884002ea03903101000e150641120300107130003207034580d8032640039810721300480d0350307401503881c0c55108605800d06001d8550312405031500700f50b0300009448440d40c0d29089155140416951581c82d178000c0c660108a180c814442c1c0030134643c121140c01d0340112848425030080d404140b00341c040140e5010030340e41c0010101d0040000005041c00c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 437602428 1250 437601178 437601211
    0x6030f12080c18060702030c060d020408120903030a0c14030f0408010f06050f0103020706060b0d0b2e080606091822050318060c120301050127061115 66
    0x2001840594001c00408000301d0038802076000f400e044601c68150082901d0640c0e480025000081c03034030002d030010325808103000902200c130341d0070740c3c01030b00c202d034201e40840d0821404907007940ea45000304050710b501540103018403410607104050110f481d602400110f8003ca600c502241d04681c480076160045110000d02082505400d1050207008a99450100095401c0c040002c03804450b0b590a00d04140c0c001c10030750103010150b803103d8001c02c68507104276590281e0104680c00b8224000c0f002c1c1c40b90f11404180c1240c81000c4c42007051078101c0460401160941032000d44c0e078107101518641d0800c01c180401c84150301d4524014031756040b14450401d003454110000c0c0c2006204001c40201050307044030900000d1000426508403000307201107400c10009074404200c1e913001d402e0013500944204901404031080e68401075051307460a903291015600c0d203002c0d071010a01d400c517049203170700d40d034681c10049a4860b4001c103d00300314680550340780311042002010101810744803000744030032410 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 437603678 1250 437602428 437602463
    0x910030b0a14060906030a12140304110f0d0c031b151101050709030314090f03120a020106060318020906150a030501050321040902070507030c060503060108010e150f030106030f 78
    0x40040d41c03100f030494081c005403400303201080d10f070520008000c03e202c513110762510015000e000700640042c0324445458482c9440e0400680c014040c4444a0042005101181d2103041140308240c4964104e41e00741b04051450b038661100c030070351075450101070a400e01c010170300d402c45150101001c2540d40d04da21812a03c2c2c01e043d400c60700064401020721242e58420000283c01140341060380d114002c0003500d0340c0000002c664401020321045926009003000c0122001080c005408a81801ea0003003000a40710b04080e800c40d5513100d03030107500000114640005180c14410281e04c4003002e081d1403010780100000c0e030304640200c80b1041c08207448000600c12414100700509000e22660301c0c44040118100d000b60192140d40036121a1a40010f0342505204040040d00300855101c461006030aa40b0b002c0240160801e5466500080880000040e540018848940901c0c03058184c0e44001d2603880403c481d0100d141000f9816540741d80000000c0f41d000310148200f01d00540840311941c00c0f80c0e = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 437604928 1250 437603678 437603711
    0x70e01050405100e0a0609060c20031204031101050301030309030b0702011d010209010806040504080403120504050a0303080106021e10090f1401061701050702120705030d050c0a030b06040e060910030b0a 89
    0x740c10500801181044c10048c030740d8020a04030034582c004c500c0840c0e0002e0714600c03644410a1040e0543c043c8540484002103603070180080045038010070005032030045440044074284401c0c80058000755040703909101280307074800c5042d04501d0500000a1340b040b1300941442508001c2e0200c1a01e9502183d0b548040d40c0100910f540a402110100103510306561121050300441c000a403080740620208035009019a00315000f4100007000e080310503035286030051110500f4003840006000b0503418444107120030b4010078404400c44090128000c17001c2000e00200050002a110104042441004a40303100140300f880c1e01000c0003c90101d081220040c89020b10070001c4211340e150008100c00e041d40030070060080207200c01d40594890311420140d1560195441e045441d51500341808814003914009000d01021518148182c1420800b00401c900941c4a40b0b00d1404514001030f900b494410b8090358003440d0070078801090b0b6129161205a80000c03551031000c44d607680d441044040d0407 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 437606178 1250 437604928 437604949
    0x501020c010306030213050405070905092116060b210304030302010b0603040804290c0a150e030f0d151805060a0501170c090d031e080f070e01050405100e 68
    0x82c02c060041e6440d40d400300320114030151580c0d440542d100003107400c00c5402c4c00075400401c1c04c82818001420030440250f00d0700142541d68100f00d4080d50b02d4070b42502450165070214103900490b04a42c0710541b1100090886000b4683d44442c4601c110a003d2850160381c10101c13015600441e203450561802030b00712400206400c0c400c0800344104000a00e241084609a60f0301150b6200b0309200081c1200d41c452000058440c03c550200703110b0381781d0700c00103205e083d500e0103580e2640c1408078a00e495003c031807039101401026001008003d0903000301c41d004050200d12403100003180c1207000440c50180c0c19503000070400300040150400e500c0210b02540d6048a41182c1d100005454200007808580300c200e903400610300d172400014030001000080e901d6400340505181c8800e1114580181480c01642c01c416101c158007403c510042d2080314050701c030b001c80e02007546c0951a100d0054554418030381c0380e40c0c104041000701003030319140c0e4a0504000e040b180c480d001000303140300802a00050 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 437607428 1250 437606178 437606203
    0xf030702060403141f0c09300f02060324010318150905030f21010305060103080c01060305070b09040f050402060f0d0908070506061306060905040c02160f050102 71
    0x428820800580d03100c01c01c44080f20303445510091000c81076030b00c40b814860603900f0138115011549800340001c40d540c000c1505041181d413248071143e11252000c03144440c03a14410084030b25288410407003031010f4001502640030342c40038000c80c03840b40e0000b01c09510850f02440020148000b50b4401c03124440c81040e0900c1c242001d12154030707018521801c8100451025241c00c490414140c41c400c65079000c1103100d9001015682c0e183c41d071581c03801035640310f064410742110794140c0c0e41c9002c0781c4241c98035040c2c0b40c0c4600984400d9103103440c3c1381203035048845c4d188007955075102e001001910400040c4014520b4412207030b00c40d903294040004440820011444203400c100c00c0100603034841302202d00213008043c55584900e08070802c24020320012500030711503907002070754405000c1e00140c0b861184104075270000360482070034440c5046c0c1358244106004108154818001407904e9000404602040d00c121440c0059035641440b4070308282d48030066610000034188184e50781032095210510 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 437608678 1250 437607428 437607433
    0x50d0c0f060e030a060b1c030518090105150703170703050105150304120f050705010212010e060d030e100323010e010602030c0309060711030a060e011b020c0103240806090f 76
    0x748000b10340c513803a1460000340090707aa0402c07420743c0d03030311404040184501c4901c05402d10750a8580905268480b01006a005c42c1d0000b01440d03511b030032114030341600e01c003422020102c841a0042c80158200400c11000d1010048109074100c110a24242c89000140e4000c50b15514000c1808000e02480c5184010800100104030200c0c03201c030a002041d100e503251501c007a00754142c0848244c02142d500521950000881d0b2103003105000e03115040e40d81244400a282e21002c080041007a100e0b18020042070245002803250710348030391a034000b14002d050206001c150000a459406006280d240981d015280148020690042c1c00ca014001900046241c0f18440c0a019a64051000c3c028424100000c03003400b0003151a102810b290b0000d811903401020500c2c00381d018000e10150102d8640c40e107580f0002c80106800340b0180c1101c203802424155031070400440241c0220b60500f5109803242402141140c02d40e003042005052400c0501414103000701c0607404e191202000a400780d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 437609928 1250 437608678 437608697
    0x61b06190c1b03110102070515070507020913020103110d0c0f0206060d020d0503040803030f090c191e0e1807140901182c0d0306210507050d0c0f06 65
    0x140c2220382c1c542c0c1ca042003088245228000d240c01c9840c0400c42d200c907103c950001c914030003000800180240000c400c1000403685944052084449008140d00030354082c5520020801008820b10000d0990b4018500810034881ca542c80020303903400f103c14141c81a030b541c4034500c001c907031044440890040030710217042e0600304880040c2824255a0010740700324203480c9000c003006402c000b1a001400300c0c0041c3e907100c0c58070455051420742c080f01e101c103050182555040640ca0f0080244003103040e49000d5041160601d101001082070540707422a410084000c085005160b1420203803243d03500705000c019282d05054184e0030324040707034090b0002041c000061110780e9100c0d0741141c156450703500d2691200c0f80140702c1300d000c0c0850084003180740035550741d030030300803003a00da0005241140d4000715500800c000e807044040b41d100c0d114210300900c030b480c055008810100a030b440c0c0740c0d000381c084480581c1c803400040e490303020401d403c8400c0610703140304004403d10302d48050700034400c2d418101c000 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 437611178 1250 437609928 437609951
    0x1050709030503040b0c03130f0501020d0203040608071b050a0501060f0504060b090103020307020a0b01060203040312050324010302040801020409050f010b030f0708070c12030c1101060b0d0902061b0619 89
    0x103900070360285c005c4401000c1644558607100f00b007555444c0a0302c00d18a0302003035a0704400e406c00710302c07402a03d0050089041d07440c0c040b030001045508844032607a0b00205603495030310854250442000b40c54480000c4c0d05968003240080007880d102c9070040c80000b0f00707980b030000d000203203e00e690701c85800f560034410100300300c91000e41500d010b04000e0070056036a9071245001c9003800d2210310000c00c5051180c00100c1c20036400030103041500c0c0324031b07458143e03078940000545130750108640f4009d98103801b00c02c0c41d1404034042001070134101c0c107050250a0946400840f03099030005c2d000001682d98410803c14180d5400d1007280c01003030032100305499070400c2c0010b20b40c20a402410301d01489009030115102900c190710901c10070740c210100b40d80014201d01e000340508101c281d104006114000d00414071401032085000b1154071a0300141340c003205560400161609003801e07a88990144030b110180c1c0c10708000c1e11030600d0180702400b21440c2103002900c0d0f041075040f603031442d2458042120070 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 437612428 1250 437611178 437611183
    0x503070609031b0e0106110d0503040b1305031c240b0d05061302032401090f030201141b1522021e0418050c0303130303050c0f0d080405010507090305 66
    0x180c03030b08200c0d843c003000420051080c08203400d500c07444102c032074440005092907110940c2118030283c4003d40c1e014100340001142c443c0030945010740490607500124a48801c80b0800843c80c501c240c0949090000c0118124094009030201d000b607203466071402c541d071083d581d0000c9481021027540e004901d05000440303150380100081001902d55500120f8600c0e17491140b480c2d654003007681e00b035642c4d2a200d00d045024003824440000034800c0516421495809240c010040e14030706034110203084d01d560011100e40380f5a0031204a100030030005100300380750a5000c0ca07403c80450000700fa2503500d2400700c41e213554000b0000341a0510644c0d10408150300301c80c0301201c1e5501140c00c0107040d08188820406501c0c2d0091595000b8a00b001001c111089030200c0c1600b18012002c0d00c60300181501819102c0c0315030004101d0060b040c1c8018400240100054184244c05804650050f4403001905d49170980092094004c22014410081000070900805034400c50741e20342060078619503551541d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 437613678 1250 437612428 437612447
    0x62b0b0a0b0705030f0d0b03030307260402030619020904060f0614091c06020d05310b04080a0c0503040906030c0b0901021b1507080c150f0a050c120405010606080105030706 76
    0xc1c10090001b0f10382c3e002c00e42900603964820740102034a540c1d05040c1d40113032840200040c100c100c040740d551980d041e45003031002c80e44529005000b0345407a9481000c00060500c1142250404581c2032000c82115110b031711403003018245020341009107504020000d440e000480c42d070000d01c21010440900d00d0f480b44c02c001e80c04403046500b4992202501d24162019006404240c9850f0380b810041040300419030301810480b204880b0f041c9003050000400c01c500d600c01c1c503400380825030140e0110317000560800003429804000e140c40d40c800d0445d5640d45007581d0082d8842c5c1d141c0c5445040500a01000301b0710480140041010a4941141c01001035110401803106014000c4100d0180034070351100e21000e441e41c450341000d940e440207585401c002c99001003d044031207214400c559500740000c00c1d00140902c40c0682d842d00903554241c28040a4070008286031103104040c4640500c141c2c0340400207000ba8810344c00440e54906098000308003a00590080d84a07510007001040745c60303004607100c0d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 437614928 1250 437613678 437613697
    0x4020117090a121e120c030c020309091b071104050a0606020c0415350a02150c0c090708041a06130e19030203030f0a11030105062b0b0a0b070503 64
    0x1d40d00080304a00607a801c50300d0314130700d50107012000c51100d0b602e58084072810703003110107070820030000c0e401c00402c4003160709030846100503174400c01000c00c641c0352000c0055841004030f001a540700e5488226400c0542110904036041c0c81c0e40b41c1d59040c10303d017a0007119030180c06004c042041508d0400000d40d0740341c00c032a4a40c00f880d584c0c20210410410915514090800c116401641071a05603d80c44210204001030700388034807101c20076405020106039035196a4005200ea55003140c1c08043e9242584040b080d02c8491050b0565942d0704e464014555200b80e400f07840c1c05202d4609400d2081d000c1c0040d0220100004046081003882c2d03a8610552500000707020002803404110000e0380d2904101d503109001e00b0015200000405238008000d51150b05403d60f1119281c9440d0055015500791401c080d19940c000c0c0300521807401c01ca00501071000684001658094110300301c10030035220084440042c0b52a20300c862011300306a2064802406200e18613031415159841d201d460340500c2c81d55 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 437616178 1250 437614928 437614943
    0x206030109020a03060509090c0102100c0f180e070804060516050a0e03010b09130507090608070302091905040606170f07090c0c0501020a17010b09010806010e130f0504020117090a 79
    0x83e40c040e54466444507000d00009007000070341d828120b51707056130ba002c03040255006100d0080d00710541c4050340149450f0200c1c80e01d031951201c4020005650083e600b40368100d102920031400941c031b42c409281d03980111160f4561076580d0a15080040c16102e00130401001c401064a014103a2944030341124100c043c90b151035044040101e000074050480707400703043e520403400d400307010303c400880090b0380140c0c0c0f280e8221169566035842100076030b645446100c8050b048584100090304100550940c08240380c4d1040d400c46044d8281e610840d030058505680103070342c0344400c1c448440c8802207903c1c2c40220000820055070300c01082c0d0742c0c0341120301403108541e4883c6520078446004118950100f94044000d4ad201c0340540f1004100d15450200301d6941da842c40000209988000304503003003c00c1c1a96509002d96443c8010b60b1021110100c21390020010b140c3c8401c12903e600c5071541641240301d010540382842c3c0001019100d00d8104000c2841d00c01d800d2140c40030001603840d000a80c050078 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 437617428 1250 437616178 437616187
    0x212061914070807051308010207051c0903050c10030f050702010c020706050f0d0e0c060a020312011508040b1819020a0b03010e07030924150b03071b06060510050310080109020603010902 82
    0x101b1803880c46588030030601d6001041c41d0013000000f04000c1d00050703000b9401c550740340294600721040d964074840a400c0d500641e81441d10bc0c28500143d0403417031810708020a1415843e1048c0e8111001211b403400181d65500c0500308551b41805180010105854524244684010703640c005108080c01426029954000740500c2c0ca4184404000c4401c0180016200c0c440f9200203912644103408944443c400c2c10b00228004d8001e80031900b0703080c0c003540e070006140e86d04e943d0750807c41c030042e0003801d0520f2a2128550980c0c42040040c600300c00d400b5116994806601c140800b414441d0000b8091407414001805451220110b880e4030030081d00d40802c40e0700c0c003407c4c400c04c804a015075030001490b008040a62040303443e0010202c0360044628820b2103951142e020322180016118040060448100511114105841c06840324011400051441d13a04c0c2d000540210f1601505000300300e0200410840a0724080e408009201c9800240a8000c165000448a11050180f41c0c0f400f0303808035 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 437618678 1250 437617428 437617447
    0x13020103052401181e080606010201110316090812180603042d060f0b120f030315030304080604140708010e030403060c11010c020615010c051504021206191407080705 73
    0x41e5400010400b2288012500c07170710a030030f40c02c08003041c080c94107140706040104035194414811809501416a001c03421038aa91420299000f171480964040010551001c1a00341c1c0500c499080580c2020b2255130f201845604081021540b4120a01c00c05040c803c010102d18410003190182007112010b401d25403031141701c60604c802500000e88120710f44045090b17a280f0540c40340f04412001c94031030a02d010460042da913110702c2000c001b03555400c244080755482c880c0842c108280c68004085d070b8103141e151101d49241c0b0b0400c55040d43c1d8510242101060301c4030501286020341600c0f0024800039545940c920b54a128901c40104119914050a840d10b48100c6507440c580102d03070024000740c42074904c000d660f0302c42074581c0340c110004c03646c4016141d8000c42c080d440541c3d011000e060083e5029080020340f0a0003401130703800c5481504030300c4118105010181c481c01c5034905140801421041d0070040354001e110344106142c2940601040a42081c6a1684950b03285810b035074498840 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 437619928 1250 437618678 437618717
    0x1e020c09071812080405090901051e060a0503011a040c1407081605031303050613050a120e0907170c0a230c030403030507200a09020d090b13020103052401 68
    0x10707030004220f08a43c55420040042100061088800403614003200d034135031883d418200c9005071042c200150549004040240c40b200059a000c04000c0030003030095940d03030100342542c5540e401d04000c144001101d4296140600c00d00c2401c04d45440d146114212001072042e07640309003100a0002c201c0402c140c0c4e610400304403014411070b03001095039144c24010080c4490105280012580b9008410000340d2800e40101803c000c0d5401200600344174801d1f48030450b080060100310b804010001948401d59111046103600031039040d581d1480f682d00c030180d010203400014003d50b80c1c0b041c0401007030001d554007158100c0950f00c01d814085032012282140007680c8500c0050240b240808100001815007003030182119034043c4803114000c1c1c0852120300004046050080d41c819080b64061000f440035a02609024621031000218162141c840c10b20003242152803041000c136080004045503418020240c001c104c0d611000a0040348144901c43d402442112504110810002c9440440274 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 437621178 1250 437619928 437619977
    0x1209010f201812100c0201050610320703080a18021c0506010b090102070512061b0702090f040201030f0501140d05160b04050a0e100303050d090507061e020c0907 71
    0x1c281c0c02c1c1c007140c003690f203d4444815a8508540d18500143e0001541c010702505108a400500400a01210410507204480c0005500c41416048091241c2100b038030981801d0032a041801d19442701f9491400030140d01008020b0f003103d9081804c143c0040362108000340d2059811103074185402c10580310441c110040e0322001d05248a0440005261003c04004124190b030a07400d4405103500c400510046504190207200a5031210000a201c5031040c02c2494080541158080c64600c0540000d802c0140a94108601e2950503086c4402c642c2c00d407288801e1514650f10602041d8900b820218045255041d514003900741520300c5810410300344031341541f81c0c019010b46041c694455010006e190854002e99008000b80c001c0451a56036a07000e061041c1c01c000399841e452811650110741580058002e04040d40d01d13103035042c0c0010805e210100161440e5601c40300340d108035410008030780640c1c0301500b041d900f0400e401d04603612000d00d0309038030004504009903a0412450041626410f = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 437622428 1250 437621178 437621227
    0x2c0a0c1401020f0a03080601020c0a0f06030b030715120b0405090a11031e0c0f03070b03070509040b0409110a091e020a0c0c08060105090f010e15060c031209010f20 72
    0xf5419031801011b0300312003010f010345820780c03c481080c1c50050038044400c103140500c409088480300104082032107500468014070000e400c0e280030340d80c0c81c0a05c3d0b10076169124030b5404036150034040042c8505501c01d1f28407600d02160103000a04000d200103803a800a000080e1400c0c1510654a02540b01004590011401c010100b0000141214000d07115403006000c980f04605281c00340000e8980043d41800745c4546550852843e00e900c802030741d2541c0030244141d0003c2e03c84100d0341d81540d0790300c501296280120f0000321070380451001c00c00d200075150070240e2085d250004040d0f007108158041c1c403100003010001680e0f20320012090b41d8112001000901c00e625409010440d414089105412a030054034030003400e4641b2071165120300c07024014803824520260000c5d01040f4124081c03030034004060555071409116485090840d407004064a114a40000070b0140c0c1c00300900c114549042c440000b00b03c0d0807083c0b040000d00042800d0a01808100800c8054000c00410b030a25070991 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 437623678 1250 437622428 437622433
    0x3030c02010c0201210621210c02060c100507051624150e091903050306011e020706022b120f0c110c1509010f09092c0a0c1401020f 58
    0x4040e040382601401d094000c01c0c60003c1f00300083c02407a0380c000021864194000f0303c181000d07101c0302950396602c002004c0c440070498041070fa0009600c80400a000c0b01074200094104451044149016184050b152600b000b00030020400c0c00360640101c0141160300104655003d104620030001502074501d03982c0f04c2d28034100a8480012071441d5110845600300c2d062506170740c1d107902d4107407140404068004081c0070f00040c4070008e4480c10082d5800001418098100c28a0b2140020f028140c20481070140e03104001c03d0200e03980401c0002d542811183d038248064201c0f00d2034420101c003103120f181c1480b4000908000c1c04d000b030703000f40c001050b02c003404000d102c0078484001c00c00140010440854014510340348441e0a0079444045041389500e2a03501d8400d68000460f582c00282c602141008060321010403802d0060168080c24581e05442c201c00b445204c0c07800301c0d03d9001103903040142d4840035a0300000356450020608990384005100c500344007600060f801c109160280014a0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 437624928 1250 437623678 437623727
    0xf020a06021605060f090a140307060911150403110108040203120d0c0e04090b010b0d0e0f060108070b0309100c050d14090105090c0117220b0115030603030c02010c0201 74
    0xc19002c09841d9205015804940d903d4941c0340e0600100c03c0d0a855614254000c1191800407410780442400c0c000441000c07245866010744442d400c48106840c1100c21fa5141c0c202c4034003601e040c0c0b01c40075040101103816480c040c5144d482c81c081000c00c0b80791505001c0c081c0300060565505100d00c407130340944074806a66400c444c8000078010706200507128045000307001e40d40d216040912680d000380380d206070080702c0e82e403c048801c4015080f0790703c0b090000e62550a60016035005000c444560308003030006100325418520740608141d115082231929040500030000820000150001d00107040e0384001000000414122050310030592000078040c20943c4004019590030a41c0d485240008000c12150702e039003000039200c0540e501003900080c26140f0707400c86241c94610103500f015041038014100d4be80100c50350b800540c803d0054480317210060040040b0040702c140107010040318036040011500f1598042c001c0c4d81c00860107410001c1c107030030040c01c41e406034621240701000342c0000f0605 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 437626178 1250 437624928 437624947
    0x70503031801140a081315020403060f0b0301020712230a050c01060603050907140a05090103030503040623010b030916080a060b0f0f060d1b05121509070f020a0602 72
    0x700701c1c01c03581d42d00040c040a2502c0c0e45031044425141c4252440d913070300c901c907140c41c070f0180d4070082090002e0340c01520754110000034554502c018401540b01d400d02040103543c8415072001ca034000e06916000764010001440000c0310250350742001103a41c10180302c40c2c0c40218001032001d00c9204440540300303002427a082d02680041c0580b81c90030000009110080c1c0b201012410746400b0340c2e020107154800002031054810340500d004440740050000d40d84a656100000c1d5407400a80c010ba0100f5000011b01044c4181ca00500340c42c0d210883c900400c902514035803070300f061014800c4100044004c40800ca034080d09010303240d2191381c030000d00088241c4466050f901e40710540340c1110350901c1c00d80d640c0340302d0504c9805840d69180041c80d00004440364010301100c1d52000d100c1045c4195070300b10107141100301030040724450320b4641d240d90b180c5800480407444c0c03000181003002c1c584044450312006954001c2c00d940d000c50185000c07903024250b201d06038035010b0400700040c401382c000304039100d0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 437627428 1250 437626178 437626207
    0x512032802131d100f1415030c03071409010c020f010c12180e0108071511060a06030c050111060406180b01150305060603071e0e0409141c0903110307050303 69
    0x15441040442d80000d44403201803c81485a5200380c0c0c00c0c0c0e04a801701004400715052099030f0060000c2c1280c07102686503032202000d82e204652080c0d05190100070300c00c1c0e183e1b005508400001c0054150740c84d202d0002d002800d611000a4001e100c0d640c5142c440705184d210741810201c0c83d90245800084000b89100a0900980b000d81d1350080010b01c4400070b8500f0100f5075042c102c42010015000280c1002001660748801d1110902844500b825410003000e0402440f88940030100300081d0450031807804056a80702d41c0e00035410000100200c2074040d00214086030400d0380f080f000154000b81c40d540034461458039001030700c1080014000684074017150345080d040b4040d503408015a59401041141d139000c1035440900040d0b0605401e1000300b00c3c08410700c104040c500380300b070f0300c200500001420b0741d075120030440380c041401641b400c40980400129071b42d40c940010402000036503003802800d03241c2d2448060411045041016641d0300d0a100074400381401030f060300d03900c6044014541 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 437628678 1250 437627428 437627459
    0x1e0305060709051309030929030a020d180210080411060703050d0f15030f060f020406020a0506060a12020d0606260d05070c0b0a030608030a0c051203280213 69
    0x240500041c03030592160b56070905c120001980d05842c2c00348090706102c0d820b59002500080c043c0110004107941c010340e141d13480507601c90031420a001d070383c88001901c040181c941000d0190034030110480c01c1d0700160340310900040040103502c1d190103036076143e042800c1c4101202c43c002c0e0304150001158001d06500c00b00900b4141000e10040c00380d800700d2198002144c142c281d16408030104000c05200040d40400002c60030381c010b10000c6124040244804226482640f00d0740240e480726480d00f04000e4103110340c2d03a2110049804440262421f900304034242c2c1d02450003442007a44880303000c1084a560b10030400740c006048081c0414041589585030075604000b1030486124030405603122a1240c0c080b6807a055001050303d400524220380c19050707401c05800082450b03110320000c0345840c01000038090442195941c0b41c0440d02e94104603040c03440d6508040c0d07621400b002000008582d1141c541500303000e01807400c011074160190000280501140f07440039520114000030b00526004245 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 437629928 1250 437628678 437628689
    0x24060906030b0906030a030c1406070908010e0c0306070323040c05030f0714090a0e100606030e07080d050a121a010e0306190b062a0f070b03011e0305060709 69
    0x10045034000d0790400000b941c00f00d4100c0e6140e401b884603a00024820000d84a0680c03041e0310f03610038800c0c10308001e03050490481d00e40c0006a000e41007006201802d0244880c00300114014162415040d408030f40c454000a041078140743e1900500e0030120105184201840c01c1090415070300d052524182004c00080d2184510902c03030f06080422600303020a15004481161441c040c04101c3c079828805100002411503459079070340c1c0b0150824a00a111040014101030030008107207007000006401c0b5920304a0015559014034401d0000b40c00025081035603040340d0400d9a100c0142c0070080780d0181d9071108000b4a1400c003031803c065080f4a00b144101200c2c00d888010101c0700a07414941ea0340b00880b108181103100c0b0742c0c1e41c4050080360b80255000300c0080d1800380f5000251aa03061104006003c03070340042d040a214a246801c10300c580c1a88080000140914525040c0d005e0210300060240905410007040d500e00c41640f841104070056900009231002c070302c1d04040140c4020f60500c10f5 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 437631178 1250 437629928 437629931
    0x90608030414030f0a031206080a05011b0e01141b03190f0f0516020a09090c030203060112080708030601050702040e0309030d0806030d0e040e0a0b09210d2406090603 73
    0x78043e2034085a0790b02c05861040003041c02c1e0540e610200c0d60301c0329140c0c210301300c241d407003202290050307051000350002400342c0000710b0403410407801c00054a800b09100c808000e10941c800a40342ea0010018548500713824890703407164880700c510414441a03206000a5110009880d101201d4003050b1424142243d1100055107456010a844080d030f045c40120014400700149598216002003d25055001900010800e5100c0c4407002c11a060004296032441a5030f5080003186420440540504960b0072180075100103662a1a4540240a4001d043d01c5021001603916440307041a101ca9940081c02441018030342e82440380c581d8003242030103000f405a1300d0782c40d070400d0144411034007450001d8001e051290060f101100e4010450000c3e40d4002d4845d142509460410003490760114040ea4214085007400944a8582003008503c0c900d8254442e0905018810000a543c0d42c0f01c0d0b401303070228015014424210350040302580d41c00206040d19404943c3c15401940181510741a840 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 437632428 1250 437631178 437631209
    0x933090608010c05070311010e03031512011406010c060b091905061e0f010210060311030f010504053c1b0d020d0204021606050403080402041b02071e0906080304 71
    0x10602d09072600a020400410710400034480001d206c1d0f01e403100301580b44800001c2c821594160107003190300039a00303c2045928410b0034112854009160481912100000c1003005c102401507200c0307580003841641440381014210781400a503400c10700c03034400d0003084c0303c00c0761030100300f4255100e05103090031240b0b910303040001d480c6040414400c080c005518071010784a00c0e0200030000302803c030b24440c0307046000d1080c440c1e0b50600d0900540019502ca080c0301c020400340c3c003052500c1e0280d4207061844607070500d820b00c00810703008103620f11200284e0025102d01000308125100d00301c165031400d91170820317440700c00e030b92110085480241d82140a0322800110504010459030098206000c0d40c42605000c07404018942a07006000c1c0c06148905074100f4140d03a268041120011503094001c2008802044110301e401d1144040001203201507520040610b10001d5030b40f03a6a008018140045002c485082624450b4210040c40144801d02000e510303102031588130740052042030b031013000c0007a = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 437633678 1250 437632428 437632439
    0xd030e030f030f18060403020c09100b03040f060c020a11090621061b0903120306030a0c03030314010b03040809040c0201020f0a03140c03090d0804020d15200f0409330906 75
    0x80c846010744d0305a80205000000200ac1041c4450301404504440c2c880c1c42e40042c10500b5800070310710071801010382e045440c41506204080e60000c10221703046400c50302d03080001441c0c05c403074a220004190f4490703130180da5000200d600036203140c085500d40410160300402036100050041e109080c00e40042e000b8480c9000f03c0b1840c1c0c058903542d02d5143d00131100c100350703c040b4000611742c01003001701100c0d00440d039502d52580d403410340d82061380040e40711701c3c00d5100c0f0300d081483d440c010301c1d10085052641c98540c54406031401090b06242c0f1654680444140091007501640c030180da81c00301260782c800300308002030000c0c440301e582a4404001c0c0c10000304aa1041e07400e5a215400c1a0060454091811030440b5081c0c4014001c0740c0c031000c0e1540d84c0001c11032803500080c0034403613440005070702225090510405004002c1d50240c81c0002c00000b40403105a1098070102c403803100c80406d824500b0b042c1c03600c0e4404290341590302480354219a40d9103004000b05070b030840d07010980030840d060300ca6 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 437634928 1250 437633678 437633683
    0x6140411030115030218101814010f08090a0606080313050306040309030f050f031332040c1106100317070c0303080c0712091403030c0d030e030f030f18 67
    0x24443c818810325076080003a0300700e00070740003005a20b02400e084100301643c04002044812160241000140c20051800599002814040250804c10903100c417101541000804200c90001c4420030071a100f80814411081000810000c43d031120043c0981501c404856507243c0008583e400d141495100005260a0205d102801280c25540305040e00d41103403110340f0604801d040c01c0300e0a01c42e44200d440800c400344064020541c0e12a41c60309068a4010040b07000e0f0f010300200c500003010132105000140300211046040c0c0c0080e01c010440e901108030075101ea81d402013008905025000420080c20083c600c00c0040d24071507030940e4902084039004a0b01c6004084008000c940b101c102803010034050f80c0b080354070100c2a50a0340c60300c1140e40d114010083c00003003040c0410900070081c0416003034410f00c0768000d030041d0000c504125600401a80d14800341c0003040a06a0780c9500183c0c0540900442e0010307003003411155540d003801907200094840c1205e58603000003078440407602c0000701 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 437636178 1250 437634928 437634931
    0xe0904020d02060c0a1a043305090a0606030602040305152211130501030b070f021509030c030316170f04022e11070b040b07080906040302040614041103 67
    0x40e0151090000307039800d0000c240d0200e0000c0070710f80700300c800a0000850b0a02e88803000300c40c0341104005402c00b49401a06c4a06503800207e14590b00102c1d04010303101171082c0340704103010040100c0d103134880381c2e031050a204010001410050515401109000d929002030040301d10640c201c2c0c0c0c903c003070f00c480c496200030241d4426100401c070074504560022a07140c10301c0554040c00d41a0022407081001402c070301d000360a0001c9460b1600010006e100002e049290b11010a041c541c00c80303050900300a499000c010013400c0c5000c100808601841020402e483c0e844a810045070340d6818040040940c0780211020b00d00042c6017000c44c007068960407200c0c01d00682090080238a50f4407070b5400c001c100c60082c01702d000007206044014402511480704000b0021003501c41d2407814448014030303410302180e03402c03480202204000410200822208440708240c0004078191145501070000e03910b032103141d01c0039501034180403001c81c0c1210400f01c0c988046100f1030703040141d03684014140c10030b03000 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 437637428 1250 437636178 437636183
    0x706030e03040603050603010b0a080109050106080c010207060818061e0a020a050f1b1207032604021c0501020417160b1c1808090118080307140f0d020c010e0904 71
    0x140003c101d00350007500102d0b0480c00c000c0011840001100114240b903c81e64400b81c0c07245e4541c10b400c02440000e102e06c1c0b000d017040d04007601001d088500042d5950001d88284801c10951400058020a40c501c00440e4682c034a13080d5052424071707030040c0c4842040c0f149030b00010703090800817031541022413080f0380408140391101c0382410305c0328030b0420641d0402d1502043c40407040e450207640c59024070080c001c0401c0105100c0e2514014103000380004080000ca500e41c00784c0c2140301c400101c624079403039401941240c840041200e02e000080320f05003441001440c0b9070020401041c1317200c10318820450064a881140e034581c143d60885e900e000c0e60391148650310002007000b2002d1350072566080701c0402c0c2c4000c003c44d00d41e9030130505001a80480e10700303980c01640461107811942e0b1040a429404e04080c02c40101c280c01c2054807504e0b403040c1d1000401e203e48005072000341540600001d04c41d0000d00b416200544280c52002c0d4071900f091401038001640c10030b2001c094604004807a0141c0e8 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 437638678 1250 437637428 437637433
    0x70c020a21051501211a070c050a0b010e070c0b0f0c0702150a030b0306041718100801030605010b1201051201020415090f06030513020d1e140706030e 66
    0x2071922400d0344016034410000c0100c44aa6009080460300c02c00003020f401d946400307000020762425200b42c0300343d044841512291001d189100000c9403440303485120b2100c9420740301c14643c9500805072020034919400411901a4002100500c08840304aa040383e0110403901c20a80c0d420f1000c035a202c0c18100010200714090011551042445480507070000d80611010701d840580d80002e400c180070f140c4405100900082c5145501c0d5250090118815095008000c80c1c2480e54490101c501c0182010748008008a1607251012241010040709a80540445e0b00200c4040c0000c1c0307158000d02050300e40034204000041c80c94041d10031a900b4101c155000d601c0c9908100422041082d00320f5040d42d5590240008248607200f0712040a04140e1507c84560203440d081c8048099030707064ac80b000502d4640710400c181c07031001c0f035040d222866048030b0f02061000315140c00c62024041f14258030348114240515010001e60200081400140c0c01c11103803810382d5140c044040e103264066040300c1d80c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 437639928 1250 437638678 437638699
    0x1e030b01061b121214011707030c03260c1b030d170a24060e04050c0a0503100e0c0c070f060504050d0303020c010207061b020c090c0703020a0209040501050f070c02 72
    0x1071070a03410303c05158103850094085580f20140c5010f5501406540c1c088142083c0100311101c0020300d01e202e603031010b0019000241c61910f8515103c5443c0c03001a1103041d485540109040da051088810141c080640d2900c030340f10307810945c1c1d40344100b2610b252511450660840719140c0040c100101528682d42e0400402e0201d901a40541003e044869025101c980c0e4080022081280071008503021100d11050b0746402401400e2010141c612401503182005200c841c0902104032001c021250918654a8907180e104050408682c1e01c24000700c0524018007140c3c8a124000700403450b038800454100799146c1003080042440d0344034110100718200400c0005040c500d000d9101c25019040050400003002180c900b03907885084100d4103d40d944214843c82c3c4000c0070041a000314510081c207200003441e000c200050400740202200e50004514042010310803c0315561743c4d54041c01601d0b2600705850554080c1c4003d4809401c0300790310780000713070030244200d0364201200c0c1c005243c240e00c7c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 437641178 1250 437639928 437639933
    0x4030623060105090d0f1202060109060b03131b030c1833080d0905090106020102131a091e0f0603250c0f030c030201060f0f05090c041e030b01061b 65
    0x32a40445040c581085d1000104404a1a0f100d00c4011607130184901505ca50041c520083c2000c0058001c1d10906107080c0c4140b00140390072003036036032107241c554084200e52a64103212000900000b102107031000800300110410011884003400c83d42c0300c0d1205411104851400e000b5039071080740b0f10b8840b1916001031400034400118980f03e0318840a9070704100741e219032034207040000001c0084089a00f8030340820043c01d0000c8598010703d02c92000b1800c5c107240e00b00541c200035485c0700343e25417214090000034107030f0030711030458440010007082081650b00400e00e4031301702521100ea65114200260f061542414100c0440b4480d04180072483d204940141c285181c03000405426010010903021980000c3c41812801120501a1f21984180380c5145002800d55148be007240c010b0050400b0100248180c40e252030741a10002c580c42d45580e5102218081940601d50000000e40317216400c26aa1461014004041c0d0f40503005600c0aa81c85600944261000b4a078075440110301c10010400b = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 437642428 1250 437641178 437641187
    0x1020424030b10031b0f08130201050f1210270e0c04050103080c07051005070303090809031f060e0c0304020d020103060302100909060815040b0c0d0f02040306230601 73
    0x10655558100050b80c0d07514080461010303903010280b900881d96a07035683c3c00da90000c06010b00044158030303200c5140e80006c1c10040415001900740b050780c7e000f10b0565021a0f004205490b807940003070349550f444080c2491171040810040d42ca650454040d044080394600c00038002055030041c0ca48281203580d400d20300d401c001c3c4014140190725000f200f0481017203586600806000b98002d1600c513031a031380041005410501e80d49d1005100760032001da06d0a50541000070740e501d00d501810300244130055402e2032183c0d0b215450b216503040c00f4801252141280043c28000c0043c1215820049143c841c416640e8150040e00c8003151000c080c0002001881c0001010603503520601d030100b0102d942e036002c00c52002d02040d0b050702180201d40284040c08841c1301e014020b101c484028a80011070b50580984c0c8400500301030010b44a030b00002d000700c00510211250280d01420400078117410001d00b1009401500089881c20708204200010390580410b203010004164280b1a0316140e0900549 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 437643678 1250 437642428 437642489
    0x1101060f1502010e01060b0706051f050402090109081912020c01120f09020a0306020c0d0c020904061d061003140f0c010e0102010b120303011d07090302010f0528020f010204 76
    0x1c02c564070b8040f00d181580c001e000f0321008142c0d03400b54640700c01d55131030b06000703070b5100608041054000c1142d2034823007000307542c00f0707800ca641c203442c010b98401107140100d6425106822a5886210391141e0300300d541e0284d1003440c0041e0040c8a41c0d022444884001c0ba11140c00c1c55030700d8001081386100c050040619400240d58130403c0c1000104c02c0019408102107140a030300544e030301940403c00c4460310070240605418003d503883c000c00103800550016543c400050006860141e0b03400703031155070304041d40b150308041e0743e05011036006141c005d0344a45c1411140c0011170b011025001e0440607000e0019011207410004405040389038094001100c0920f040c1c1e14003411036484132030300300042e01c0e1403510802c0c0300b0b00c04000d10b92300d604089050586103042042d0640c800b00c6c120400c0062940601c4402c190f82d070920b800c0143c4801508122018014452407400c0d1030b482095584600c01100060207000d24981c09480d002c00e1050407041c03c07405544104501c1192003210500640800384094 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 437644928 1250 437643678 437643719
    0x16020d0e010e2b1407030213050604020903030316020c0405061c030201020913090c060216030602030901090b0c07030e1504140301020f04080d020118110103022802010c1101060f 78
    0x28007070041020b0210540300c40e82c5a0b0074407905400801c00060042c40800d119004144c84010012140796601250400031741032558862583c5d2440443c69995545e0110f44130504000e04503612800e0000940804801c1075031002c0151080f400c01d046541058012244580760003015008040f840c2c2ca801c0d9844012100100d085560030050740d14603075285c2c540c0c0340c40304000703840010b182034042c90005100002508003001f503510040c0828801c41c400505c0314140c80e48003101503266190440001c1c003400c4485c02c010000401401003200f9070411002800e12140681d580070314105000d07050020303180d50545485898642007209000e150030010448010b144054001403801d41440b030607807000c1d00035406c00f0210e50030000030414040c2c2d09005148903032249040311901740c1041c2e82d40313030524400d03061070314181500072402d620240c1154481599840d50300d4050914440c0c02e4200a0081c0059820355000c03c5000f0084600d40760148224426613140300c0040c20300a0820b5420101200d10300306c031 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 437646178 1250 437644928 437644939
    0x50d1e0507091b02060c090306130519060506040b220207141c090803090112052e050112050613050606040b040e06090a0b0a2c090616020d0e010e 64
    0x16054003078483d07101c0540c00d10700c1c900880403803000024140303400a071000c500c10074140855542583c2c0442c0c540d800000422158494070103600e00a400d002000c5032103460040081c420703200788601a0046d52140a0460381003102015070380c00c01000040800c2050b40707800d2400d5801040006a50081c000e0340e0140b84a0200081c14260941c03810f0280c8981031940442031071070105464200b150074010f400c200000e54241040765000800d0498041c1c40da0a516464202096403100c080100703016a03000002218090201ea8228081c111254401c250004000301841d0210480760710556019150080603a4010281d152004010b40381c090041a400780041000041e82000718004100501520303403120080e2400800704a1600401070082408a003844010b45041d51078004044c20380b07134107555050340100c280e020164280401030324182c0394007140c01441150000000c2c039600ca203003158981840301060350300482c0c803400d00c2424000410003180341d1f10301c0d542c0607025030308c41400e000e0702 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 437647428 1250 437646178 437646193
    0x12040c060507050a230f0a0506101404021b0a03020f0601151704140a0302010b03120307050a031e02130515120406050a0f18032309090402030a0515010f050d1e05 71
    0x141503062103c0000350800d691f0080b207440003046002c1c04a9a07101084090307001d40300f458491000c018100c4000d84511555000035004001e03044020101202100217003100c0c5a8101440c021f07544100c048881903403482401e000141003040342d022038440105030b5a40c031820100c201041c22004e90041c104403007850002002082900c4d042041c82180d9002ea07002103810b228035004e01d4100480340c264501700140800800503440c1d00030b800c035094a6074524001078214514802c040d400140e00c1440410f4900000b202c001403003420100d42c0035101c2c04c5881540c6042c0c43c0340582c10500c100300c482c54195440b00700150104545078040c1d0350040800300040340040c4049400c0301101ca1140451f182c40ba0012912802d0507800210364150600103909024164500f40c101d01c0302d4018a1039132442040e0010020b0700f103440a202d04524542c1c02000c0f110580103407000c908480030240180316110780d4100340040d60b4075001910007811904080c0003230a079004100404001454800d09949603c1000d4 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 437648678 1250 437647428 437647493
    0x40303050c1203130c1d0f0405011b030f0605120c0d0602040308040312120e0322050a06030b030f0a021c0f0f06021c0203090d08041712040c060507050a 67
    0x100118401c50b00b0071500c00304c0029620f45410004219080b2030701d504800c4000d84000f49aa6280b40c0c1c010101c0314228030940d5640c501180580603101200c181915281001c1c031a40343c06410001e0803022500091001c80d88031800d100345034150802c51452540602003958860401c0080c01200728002c0030003500d031a8072a01c4100259005500484041802c002214013890740000e40b84074201c15400c0c00e00003441d106003050340d24010102024000e2074554001042c0240b0084108001d01c030140240056a47d2040040c00501c00085124068060031000200c02d072008141d18046645c000c1070110032a18002c00800840b00905c0122904001c4440c020045042c400000a4992140703001596030a4903000700f0100c0300c648100641518010700a00c0382c8450045019103d01c505403038482c01039a0740c3c1c1480c03c603a034009501d0284050f0005001424400d240866502c110301502c02511401d0361003104035080d2140403405004c1c0d40000140f4070004e054050081d00d022403010302c511400c2d80e0311 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 437649928 1250 437648678 437648713
    0x70312020304031d0d11100201060801050c09011704030804030e010c0501140420030304090f021201120302190b0a0c05091203071a040206030a090f0c080d1112040303050c 75
    0x2507500b43d01241030241c20003901c081070841d02d911000c0c1501e00400142d01650b668800f20b00c3c40715480d00c034040542801003098400d501031001000300300c0003406282004400004283d0010010340d001501d01915000051041d150082c02240d15540d03400ca0359440341c8085540200081800d41000440b22103600490b8090052080003504100b07079511074241498400205481d9078a400c481209101800d0015135010084c0e504580340e03120b011440c603030000c51000c004e118111280250030710040005ca89482e001e22243c2c8464840d030215800a02c00d54064440000002401400c40c68a00001040e0424542200010b8011342c28030b24144a0403000103800c0e031030b140051400e107a00200b0850140451005d540350034401c02003035a4590704140c0c021800390b100003031411440c00c2d21083c1d00410005184401c0d907030160440500c002c0d40e500c40c4d1005880f43c1118100000003550b40e100d8051124010451007040311940c204545003d26554099441d40c01980c0081c1395406080309010400411 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 437651178 1250 437649928 437649931
    0xa170405060901050106081e191b030b090c0a0c02010e040e160f0807030b070504030b04030e0f010305091f150e220215030a15030311190206040303050703120203 71
    0x54001d061207152482d112800c50314140d0111041009400900084985051043d406c000c41498071400c56500c003603120113280d0240c0300f240000b034500000800d01d50b840c90300c280001111a54103004a2403600d0130405465000d46940224200412049042e18050400c0c403070301c984181031462031400c40300c0005d021500a0700c007a418540058413150880549100c0c07140c05000c1c101c5010501500b004403c40d51071500d03001c002c201c0102440468031003801401642d00455004201c08040d10f814503006240d4001d01da04140101200900c0e101d9660082c003800f480340482c10002c003e111000c42c502c101441c5507006004595039241901d10740d4a20140d2800041c000c401d22404190525543c10001640e10a411042c131218890301c00e401070340c0b62030041444420380340500762251524240c14000b8680a02404580318189000100301900081700b400c1c14a0034406036203148000c401d107041c004008400007580044200001d200083c012400b5080250207444c8c0905c151420100004c01c0341d00 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 437652428 1250 437651178 437651183
    0x606011d2205150102163501200c060f0c0c0102030906340e01090e130303051819050a1e0b15060a0e1302040e090d0203040501140a1704 60
    0x101c0b002001000808040f164001220038802052000c02006170194504243d029a400d0b85150180c4008180782000980342d0203000b090b04000c00812052105008004150a410a440054400d04a01011102510300c1000040050026907590400128403014028000543e4103820b02c0150706101c000d00c0911301c2180800020b145a0500002c540d80c0201c4140c2c00b00d0444015181090049110810505010f256400c140136455400c000503500b010b081d41200029064000404c06000107040007109481e010303440411640e00ea60400d164520345100c04441c03142e0040c9a03600c00c86103036035180c00c4518022410340c1c00010fa15507424040308010031800d514099142e0212042c06001c601c541e400035841c01c04504020201004103080340039110f8010180007102a06462584a4040e048041488218110740c6c176030300c074a0613950807042503403905801d208140c0007a1901e0b00000440b410f90301c05031140e0752152318580d0300d040e0340d0f4400c4000070104606490014550700b10414058050351 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 437653678 1250 437652428 437652431
    0x18030f1817100c0203120606070807050c19050616020f0a0e01061209121808250906060c0b040804080703060203150307030804090905030405100f110606011d22 70
    0x310141556403070701e0b512040503000503103052110200c3c6500001119042502c1d200701c01c0c1c90741c2e40c0b080003807664040c08802030050031001031034a00300180416450001c510854106414482051448000d00c0107401065000311b000c11400b980130002d032920a01d41c0c0c0c8000c250440310440312001c80d2402c4099401490320b01c00980041c00b90035041a03216042c08112407013080f0300034054440c1d001880e80504514180494108030098548a408003440030b85040d408540d002d2110001c040c050801c85082d00328030042e800720110b0700c91500d020301c07001c90702180d51340b0a0408490f00c51406421010700700301d44982003000700164000042c040c4000850040b200140c8a2402d18203c034001c1a091041d03e00c00c0d08020300a1001038008020784007070f0340320b141c000030790b02a191400d50310b94411500440c1e44010b15030045a076071a40161044078010465988034440f2f0f644100035a6240c006458460101d82000020005603a51a800c468180c40c020080c1c141015a24001b0700700d1000761175541c5425 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 437654928 1250 437653678 437653709
    0x82a190c090b0406123c2033040f14180405100f0504030903080c101b03060b0a120209130f060504110c030708070f08030c071518030f18 60
    0x4101818030600e59844a20002d2174004103030307484030511506c90340001c14140780703901d24034028140001d8008003d00c003c4d20f4024039240c2e40c03610201c0030300c04044001c281071030640c0151f500b102e0071043d03c1c212100c000708201d20504000c14203001076460780040350007140c50460786540c03c00c0034443c01d003d180a10082d0034000d84403403408042e14041c0c00c3c800c402da4105400c1c0000030f58130045540031a50450602600c4400d01c90101d800c1c1000f100c1e8400e00310341000890400381425240890f01d103456900c0030800e45965114402007400f8809212010850070440170201d0f03802038000b413050850040019501900f12100c004c00c0f03134441b4140740c2c24103544002c203103c6424540f0480010074881a0018240b2000214095481c811010010000c490119800d030070066002e1442c0805948400c1051b10781c54903020317030301854012100c203a400c810130f03506d080034100301c601c28035034081e0321b00315010059400e5480986211082c0c581080411a200389004805001c1144140c0039000002100d40107 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 437656178 1250 437654928 437654963
    0x40b0306010f0507080304120e060c030316080906070c061b12110408031803031e031603050c0901030c020f06070e040e010c0c0f082a190c090b040612 66
    0x2030449007002c0040c494208403020201d1558810340390b10542c80804201c5200480b4401c6581460305010f50b03400502c08a050035500d58040041c500c075868280910001416801044420355001c2e10400003c1d0008400304101c7c901c91040f0068981c010180403410382103400c00c4841c869588056a800030b0f039003c00c2c0e200b144039140a1030700010314440020b424142070010f919141d00c1900c02612000105104001c4581c805106a510640e2100590b4010b0803021605c0b41a590080350710b00d5100c00c01d0341148000b50b020b4802c280c000c45401c4082400d000a50006500030144200d00c5c00651252a070801641174041103106e20807801ca9690044110f00e80c0d00344004d440903a40503129590600c89130010196018508074822900201080d440000e24105001c0b148604903041c07042e511122600c2c28283d00008141c911300d4540000c548081e14000400d6030b420f0f458560040602407014001c20883c107081d0007d08003540b00501c005001641c4009c80c544003c5500c0c0216040f0305c1101e0803041e0f = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 437657428 1250 437656178 437656187
    0x302010f14091908010509010507180f05010804030302090a031514250504090c1e020a0b070503270d030606020703111c08030901060f08011a090c0f040b030601 70
    0x1949120350615030380c50400d81803621102e0140703810351409103001a994090004507620070400401c0308070020072450034103c0045000c0c100031a10500030440403842800e50318001c488410440e600281b0f6583c6d05803d00e001100d03400030150050301015000c0c000c0c400c240c1d580702d94081c01988035600031001011584250b45c10754607a04a00d07807208007900304101442c100404010200e0420008100d0204032f49207090b986406a904080b98081c0b500c0c543c60724031a009540030840020002102402283c10041213031f0360305042000a000c9400c000114503001d010740040d503080f04018003000045211404080440514031650b0185a4400701c00e506401c0d82500c1100090803031031003d000114210727150214510a1400c003240220020782002d40e601203c924056116030b40300c2c40c905e43c3c1c3c2c03c0c01d20381d00d806010180552607000180c01400110b0034814410f400c0300e0901c1c1503142610f600c5a504102c07105e98000e1008001280070840c0c0301030420b5860060019040640c2c40c41e4813414190300050 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 437658678 1250 437657428 437657447
    0x10b04020903060105131116061503230c060a05090a0e090a171207030b030106050a050d0b04020a031a040b060d0308160210060906030506060d08041a090a060306030201 74
    0x1805644104070034503650718082005815aa01900c111014020b03500d52040103140c5044a00c4440c140030072a01da80301e4451141103602801403005000f9040590400c2e10101c240e4440109550340b80320001018030456044100342005020650b18500003070b80109100e07070f01c0403000100251000403280d03824a0f091030305801070b10030494603000d0f51500140d010703900d0001c80c0c00076051502d502e9200181003100000c4031608009088031403058188100c015010b003c0c582440b07442035091900115460620381448400c03121300822000b0164030a49a1420342c82e030281051303805c41c008450100124404049907818485c0307200305190b0303074502400c00c0c8400c400f020b408148241b41d0041100c0120340d1041c481c0342c0205a4200501082120100c26032030944200e509080701e83c14501c000411603000d42c03240701100e01034001d8405031f50302c0c0405c000070200d034440e00800a50003031100b80445030044009840816080804521380707004100041d1130ba076000d62105000a481341c100b802103590107020b21 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 437659928 1250 437658678 437658701
    0x9060501060207051306260109021801060201050a0c2102070209130c061110181202071805061c08071a0109270b07020703200f03070b0304030c020a05030f010e01 71
    0xc02002c1c0c2010300c200c0b800c2c155410f290180c000260180d5260400039449270004550061540b0402410100010b100c0e190034840e100140d4a003c000545204c02401380040a507110798925280381400c42d4110b0000780c910307c04c1000d042e420300c201401070321000e440714000c2d08040400c02d0340c00440c0c0380c00c0c000c8905581101c4d00300a00c0e10551420010000307505040400700f6000031512440034049000d04d03084400010b011a2503150500a14640225601c1c1c00c0c1e55143e07460201041d04412601c1c1030303070700655105402030380c00007211041500610144448030310602e000c1307103840c009840f081c0d0b0007185501031300032640b04103004018030026032180d080c8184a06400d0b2015080b079400e10301e00c0c1c000c00c03a0b01034081d5074030800203000740781b003880080041c540c01030300211760105030101c60b501002608420741c022810860b0080c40c602e00020424112807aa0b0241440c60b52940e50443c0c100410507800c0f0f0300321900d000d0120381680c0a1042001c0041013500005103030310700020725070950340102c0d402e = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 437661178 1250 437659928 437659931
    0xc0a051006081e030306220c0309030206090a020603010308030a1122090b010804020f041e2003091b04090606031b090203010503030a1d060304030c05122b090605010602070513 77
    0x40f040c003c0011060700d91140c01100e6407490f0760000c0721070449009003403070304401c0645482801c030f4005405501c0f02e106580280e0032a55999903400100303035520444500a944440c040c001040000c58100042d039001e00c8040010075805940d5950240b00d130401d01d0403c1184140101e460fa00b461120045002051185c1c02032144202007000a04441e2000d840a0f025100580b54040291129086400e43c000c810b540d00e19220b01107903020000780b10012000225001c120b02c0c1f01d0548441c3d40549016106001c0130f01045218000c6e402ea103124000100c54100751580294404100b9501c0740303c2c0194094810340f10300030700c21628007140741980e820011203940f041c070060080b500c000043da403a171205410b004294007982c400ca0000e0401e801900d80e80140b00108010030941e000f030b5420302d010300c10400c03614500c0a00240b8090781c0990710115105940f648107042c50b10000040c0500109540c202c0001e00410503150401500c4c0300340c0024026a0207000204031070f040006135201031a03000d810 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 437662428 1250 437661178 437661223
    0x1b0d0f020601051e0a03051e01060801141801060b040905011701090c090b010e040203010b09031b010c171207050a021b0a050402030606130303020105041e170c0a05100608 75
    0x14242c50013808a602d00540700114401d0903111291290040e6800404841142d00c0850390182e076103144454015007942001030004840340705004055042c201800354840790382d25180c1c0fa070400c00110781204119900d803031001405400b45801400a45410783d00420b9030343c14218a030380c2017010345800c0c1820340e00d0034503c074020032480200d03801514000341020420000d11801201c6e0003403400d45041d070142c400000000c2940340d4030020324070300001313600b591141100c180b80d400c41d6134580540140424019800200018200d41c41181c68070b001c0c007416814880910b287c2d01300e255003181c100b4041640002e0003110241c040040b0307003845120300103a10001d40088041600c4003002d01c03846000310b801001180c40b503600d10702900c060031009030038007002d1680c03810b000703020301700c2641c050341e4034032034400844e0360b006640a01c556226041814540c04004035002040b281d881002c01d0300c0a4020030186200041c024014026282040080890340a04060703415041204403256298070321001003 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 437663678 1250 437662428 437662439
    0x307020a0e0907150504050901231005040905130605090a020f030f0a0b070207080a0b07030c1e0e030c130e0c0a06021504020301060314011a060903030904050a021b0d0f020601 77
    0x41c0b01007603c4c1d41d6041c025031619449015075280c041c6400c01d075800404000081003100360000414090038440750b001400d20f40e04c03428800b030440c024030840e00196003000140a1b0100642041d500410aa2102c8480020380c0e10395008894040c2c40c81661134010300805815494040c1303417000300c098110003404210001541c81c2d41d90702080380b8020540c03080c0b200081e00d07584c020b001b04002044400d0565101c1d540ca840d20607100d000c11135480c1d0100780381c2032900504238400e003020b9418100c030241c19480c02140c00e0043e20b500020352880c5615110300109000d150302c98041d01e2802c0c0351100804102105500040c40c10300c2041c80c2460700450000c0c9042150030f600003441d4486000e101805100c60302e60f400400c0c0034100d99040a0700240804a4510302860154065002d00007880400f2245081c0032080100510900000b5a8180d1080c4281c0c4464078095120340d82140c44542c005140524440640540700658848091160880b00d41010040d40040c44d2080350001c40c8007601180d810071 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 437664928 1250 437663678 437663683
    0xb03150306070e0910030f0c061b02010909090c0f0f030512070c0522091a09010912030c09031202070e102303012a0906020708030306010503091c020307020a0e09 71
    0x14199440b520b00c9002040c1722512196426005c2d581064243c00500e5060806012004072840365100041c144003140003680001078030315010a40c16034480460510704140b54019051100d8140da20b03039003005000454520200c2800e00400c1e0304191448114030b5402e00c141065441414150800e0040042600060404c0100c03c1690400c0b0f900d5805200c1e0400311500701c8680a00300209140380c6002c1806106409944605d07003013941122812560b0341c61040750a82c0d07201d00b002011504600e118040190003500009010081c926014020b40d6483c0c0301c010410791200461009a08240780520007815900b0115030b00c1440001d40b0103c140c60400f40700078100c500b03401c0301d1045d0320075082100035a500f074100008007a4440a41d1030300c0f0b1111001c0840e110840078403000401ca03007000018907640017082e05000c42c0c501c44040e60640d80c2d6540152075a50004050b00c42a004000c003804031a01403015003054020154020f6840d14018414440c044038160030000501d10610100170000000 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 437666178 1250 437664928 437664947
    0x70f120206030702030d0903051201080f06010b03070c05030d0504060501050d120e01121d1c140304020103060f080a1703060904020d08090a03080d200f1303020a0b0315030607 77
    0x5a80490382ca6031026812801d50040781d80e03d00d42c0c80d04201140d4181640305002d811000803190130071183d80da03180031315903880010300b020304401e40008004000c17103c001e03009954064881d0502c40c0c0361408540c0c41604550210200c015540d43e5001800184070b083d106181c0509000d071103038001354101c0d44403140b075508100c50034007c0110718804901640d00c51020102004020b05050040c0c242e000452103104c00c1c4008582078034072a9040000c0344445220350074581c85c685484014040b40140038a04a6070720051059040c1611207a0002c1c000700194a01001840c011014250f4030030140307401e508003100d00400b81048202842844a2039964032217041e042a4119071490003141c2524120016008081925500c6a25008008140b01c681c0004103c01515240f0400c412001c1059056945400a80100010030248040003c0d0410080142400c820202511000c2caa49070f0004d500a022500280116100401403100d0090034880b17807402e11508030050116880c003500c1c004c3c1009074 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 437667428 1250 437666178 437666183
    0x50114060f1c02030406090b0f06010c0209060a0e0408030106020f07241403100305010e060106020c010c031103030c092e0e040e010e0a03020d0c030c12030e1608070f12 74
    0x20001680d041c004004440040b80420030a402d544074038040c2003c400805c07105c2c40907101074a00000013990701103034041c10703840741e4170503118442021070980a01050140c02072140c0c0d00f108032004041442a8400f8603284030b14860405280e5075810440c1c0241018101c0d1401d182d150300c001300c1031004a4900312666000800082407080a1107892400ca61b220b461002d0018030344400014800c0d0215003070541d10a50b80180001c1c04a2200caa103035540d6204240300d0440180c00070002180035622400340081c1310ba000f032070b080c01d42d0070754100e48a00b150300a0701e890030070396030008d51344076181480c0d040e00314518080c0350300c00410100d00c084060001141c1c04400c080040308403c0403160350b81e0b940900140c118400c000c114003503d21202035650381c0001800d401501ca041c2c2100b0302c41d132144c04001900e5078980e4400c028031030180e98480040c02150307107010500d910b481008130285410000c824028580e07a400d171482510b807440791800c04070181c00080124414600a108022041c0c4c58501020f0b07 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 437668678 1250 437667428 437667457
    0xb190510030f0b04060303030e0d180501210c020c010e01030c200111030a0902010306211b1d04020a060f0e060708160303020c0105010905090d18080a050303010905011406 75
    0x800c00b00c1e9800400f03900c03014650240c5000c1c4007000b85603041d405a99095410000c0b20709114029105507244010b41b040307481040580c0c0000e011035440380c065181400c99005102e410410001a1001910703000c0c94003c0050340402d80d50851580d01c01c020822a031400e00b410850711504c0d1304001e05e40e040038940002020603a80300000010025801040c8041c89500440d0712401d0002d5110080c04581c801070713000a051050110304011700e0341442407007420b40e00800c4150803407503591024031030501c0104544000200c40c0015000f90380135240c0f0350140107201407101ea24180c410000d064911303810030000c2001000000b00c405420111141d10b49004480f01501c0d01420300e09a41c003442508a41050050301c1400c020406400d60040c1900c0700000000340010f03a2181c024500322801121004002e40c040c00e2144130041c090301c030307007400300107c3c0c003010040a842d038204030303d0b061841c002160036900000c010080034101c1d104243c09024403a04040703030560041c000503403500900c0e61060010 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 437669928 1250 437668678 437668691
    0x1030e1005090f011406040f02040e15130c0f021015030f080c15070f170103020607062a02100b0102120a0318031d030723030a05030705010b19051003 66
    0x40d800f0800c0c1081c01103014028058041214568018400103036221405581000c0000e46028a50300a48082e2051810440c103982c2d51716001e4004241c5108070b40380c000341469950000c1405030f025920b8140302076201d100c0800c12100d0001c0c980100d1002e01c3c2160303880c0609803024450079580e04421a60042c1000380c151004d818148918841e2041c50305841c414a40d51200044000038030911034180c5d03441d154514142007074180c40e045445840d042c80078030044014001481c08802528105006050000e584d11000f804061800128002ea0300181904000344550503410400001440304016060100c0303252880041c0d13075603181c0c481d00c500505000c281851000e00ca0341c880030640351901e0303400101e442c1d11708010701720f600e80703800c80c0100001c040c04010b0503060000e1100b088602103034400c0106503003070400d880103a0700035400950600030310032a071b400301c2d13001c00190000501440c0000fa4004c02071003089881c04422a11400d5101040400c2010342d860421003017011840b402c0110301d0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 437671178 1250 437669928 437669941
    0xc0603110d0c030518030a021203070e030a03030f0e07140603061c0c03060c051206270103080301080114010305030306100c0f1208010b04080c0d0201090b04150206010501030e1005 79
    0x20300070301041040d100d180c10384601d41282d143d04404e014180d42c100130041048013616817616845040a1900507a001141c041c010441500040da03010b103080c40c09561418910700001d0400c0704503502900000d440320a40d40040c4207612034190008080c4004240440c80c0c0403100808900c547c031130600c140001700001d1280c0e241d03000409541d00c05c181201001060a29203492120b04502007625850329004e071581106001d007040744d544860301c40298000e0b80e00d00341001032408003141845111400c0a6540c2090b20141e062680618480e45242d6202d40c1003501c494216808200700b40308a804036001000070410220440c0e41000042c4d9206403010820071003910742c908007d900500560b403403101c0c2d10a00044041e442c55207959962030016503683d070028950180518041c00681e40c01c40d80000541e0302d8001d40c40400c291040c100b2507080341c1e0b501c8640c0d144c0e420540c045e502c400803110500b150301d50306100080c0505000d0074200207901a051540ea03851002c11a11b80c031403641d031000f1484 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 437672428 1250 437671178 437671211
    0x60801060c02400609150e060d0302030c0f0601171c0503100f091a0108161211040605040e0901021612030603150e48031e190c0603 58
    0x80e2028a445456035541250040f840100010b00c200031100d0700e000c0d4464503200081c11400110340d00703660a48600d4a4690410652001c140000c03401e521081041103461042031020b8803100344d205020b081c06602d4650040014000307280c0c0d07130455030402642607000e41c010562407080c0249615085480c0c1c0e4411f2003641e4071840d19000402c4107130181c080051000f65a07040020b015004e11003420326559910010340c0c8056042c1c60030b941d10503952503295280c40c4518020040c8108201000c81e041e101c0701c0000d05582d1181c2c104030000341000806210400c401110706821420020085103005243c0d0b44180f90510068801070804001e1010482d00c644660007d00145411850180080001c008c040000b040e0168008419000c0c5240c1995a584c00700058090142019064070070030300003c411200040d00f10303504030b03041039000d06001c1d01038404200199140d41c005801c4140480c3c13040907680390110200e140f1030000044140d500005000c102ca04040b6181400d010907071280c01c030788940b0b = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 437673678 1250 437672428 437672509
    0xa0908010f050a0e010b1c15110316141615060f051002011b0c14060f0f0c090f041112150a060507030905010e0a080a0c060801060c02 59
    0x8015801d00c00304103204411070307100901070511001c003005a18450503a0a0988108841881e4400070b1804000c4039a09040700d031031200b900c22948070407040006124030046503a211048998100e002c0100114407070602d4010480036034505044c1d01c1d80245600c2c1c506540b040703155440400c01e402c1005420092110b0329141504c02c100402d00c1101d494400900440c10380e84a080d01c205a01811000554018440c4164110400300c10100707020309000c040c3c4040d003240b02d04894248601c4000f989035141400824095121082c2441e0142001c200070640804c000d0940394a8401c108941040303999241500e1300d00340c0c01500c0100e01d0061303a00012855000d0b408065260a03101d004000102e40707a6100038500b594219441b0051540700e1404541c0d500500c2c90090114601d8002813001d0340c001c004243c100b0000810300c40150740c8921405042046400c82202d0070505283c091003035540108003a07000d0142c910300380a4462103900040e490841d0040da50107025241c80c0314841c110035503600003 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 437674928 1250 437673678 437673689
    0x7020d0503120402040b0114030c090d2406060f0f080405120a020f0d030212040602130306020a0203090406051207061101020f0a08011401030209060f031509091e210a09 74
    0x1d07a1628000c1100041000040b6000c904c2240741c030034641950340c000c040303003004074110301e040700e08540d140602100369a0019010380d40c44580c1076100c5000403402c00e48034104804400803a2000b143c0440e02005441e0650007844c02d000385880c40c0714465521100e140410b10491800c07101c80d860b903090060619071038586800c8045c00c002103050015800281705250007502404a0302e480e80c140c101242280501048844080e4400b00401d0204180b034010b003020264141d0782048250303807070b540d06040341e2040404001580001c686e90f0305514091041c0001018243c451104010b55913400703e4555819014890602040c0815601141025416034010b5a84498159640c45c0f0786600904000f401f48203030000d022200c1078081c4903502ca4000e44a1104000d49540d040507400c85004800d80c000034440c2010403031011020760b03169102c42440c0d000b940907101405140700c50344440781c02c80042c0240c100d5540e0149003c3c0303070003d032222650b9a141561003a41c980f030b13010303c1004580c1100c055012 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 437676178 1250 437674928 437674933
    0x706051503070b0a02060c040e06010f020c0402030a0501030209160e0103020c0a0f0b09070b07080f09010c170c0f030306130e030f04030c05010806030c1807090905010909032d0507020d05 82
    0xc251201c0d41070041244101c0c540031070f2020740e2810211001c2e03110301c0c0214480d427858200801c80ba075008040c0900007040c1d90050301c5400b070824010504a0f0404c07030721400840d880c0d01c01002541013940c01e10b50403043c2c0030009024585140c1d00581660580c2071428101036000480e002c03882001e01942038035507842503040070f0118042c108000c420005075103040703282c000c21070000751a91080c0212000300d0340c001e940600702240d4030481580742c0c01a0380740905104640900a0020348042c0301d49404103103812500f903c401190742c406203040300644440300543d10401c140300b05592062042c0d49910300c07980022aa00d466005800d00718000c004811007801c7d03000c03a01100700005034003a01c1c1a44e40a9a503044166202c0c410144d40b0b103411140150080200350b42c50f19000161101e1701da10042604001070751a640e144607000715102648054010395580300b2103000c00d0f900c160000004904401890000080c80004412800c20307810b800007403105c0080d00b1411501c2d114610030250360060300703 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 437677428 1250 437676178 437676193
    0x61317010507080f09071203090503010e01060e0903071112030403022e080112060509010204080a0302160b090a290a0c05071a0a03050408091009090e120706051503 72
    0x260a0180400381c4419022544000c00200d10342c2c00c0a00f040d1003911808024400907141c080059542114884280e04201c444180800c041d04e090007051031640350800006030207031900780041d4403072001605010345a0004c01c13645002c1003401103400b1207090220b4815100c4a4074256141c91882640e00094000c2e0f06031990844508414128407184040b0803d0141000b00320b20040320f401d1000d0280b1240e90545181aa0205d451070340215070121800d0001450305890300a024540321210300203d0050340144e411a00e00b6500942100c01040c54190766410310008000164041d5a240210f004500009906100801341018403055040e10490f0480d520142c0c3d00001300303242140c036000c7d80e0f03031301c6400000130300c3d0310184142e25a141034003001d2605001c580e0340201c0190002400c20b48211100380600c0c1c915544100240c480c5c5a00b80c1c0710b01444514181c80780c8143c0b00c1d5400b40c0500c5802128089506940344403c407100d082c0c1c4803500042965a258980c5120200c803502071341c041c819082c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 437678678 1250 437677428 437677469
    0x10e0d0c050c01091809030201061e0918080403080f1c2a080115090302031b1c050714010513080d020f031918080105090c040e01090b04020613 63
    0x200e4144140c0200107580010882030019244100d4074801c00349a84420200c07980003450b60792011a4861091001290240d52401c02e2409030041d201000041c1c10380d04c0040040f03c1191088072680401210208950302ca1902d8000b481d02070361102030040d690000d08075802940c1002214100899020219041c0d40c001c803201c0024029001c2e0707295000d0031f0300261601c40341072148110841c40c480da00c0100d985e0a18501a66aa92621143c014400e4021021005980c240854621442c90b90b080c414440f041c030040150186007503401035000030031007404001003140440c4603c16601400904040c41d441e5a00403207030340c45990001640000505000304000001003103040584842c0e0f42201c0044c0c0e5048a425100e02c030315443c81d04a1a509411580d03140e009080b01e411440f45240700b80d40282d900c1a02c1402e5038000c444c1c483c0d01e130308905520012881c0c01d215000318021070744020456540c4540d50960796000182c0081c0c86900f0118000102c1d407902d40c2800c0180000d00c2401a03086000c1 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 437679928 1250 437678678 437678687
    0x712060b0d0c0c150221150307050a03050615010c0203030d1509060b1b01020c030703080105090a09230c040e03030f13030210050408040f08030a2309060c010e0d 71
    0x512500560780c0c244012442c0051084040d2403034641c12000b04070040481e10042402988801d070392085000030b050320721420607045010301c0d106540036442603881e43c0ca1841014240b90031b68110a10450103508240b01180d00004c21650110349500c0302030341114145d00680d00250303081c074000d516200029001039102501e40200c1c40802044c0c1c2c01e0380405444406180c150b030307040c2c054034074004000d100d5101c9070303c01207034004940500d0400042c038000061007203d0841e0b0003014241d010981150041101d4104200300e0355000468190401a06140740e4694034a020700704110344a00b00001807400712640240000340100000400400001030b88a82d0241c40340c0040700c006010300c2100c2c00003042141182c80004c0c3c4181d041d0f000d4040c80308650514801400082d009458100083c0804101d601662301300710b014044000c011501c401e00010000c1401440384410301d80108411004c02c094680342082e00d4582c40229070050b110031008107401d0050a0031400d08a41d4418000381407c4142c10 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 437681178 1250 437679928 437679937
    0x304050f010f060612231e070203030f0403110f06100e0a02040b040e04060b0d030c02030f1c0f03020d0204060513140a090207051501080d02150c0a03050712060b 71
    0x100c100034480840081c0d101011520144030b980081131070f00042c6007900e06180d02181803040c81d5200d00b410800141c21400781da000484241d074406483d03902c1002c2e4110b94590140d4050709a00c000c514514021050302030402002c2c0c0028140803c1c000603c02e811030901c8003441e050742d00000c451142c0340c401d4184100340038602c148480728050a003c00c444050f2402114117980b9558081c925151030103403200c54050b0010002c0e100f007580c0b00700001e91b03035136080132104245010b07a860701c7c40c2c0e4400f80100740c244070b040302c0c404240c0c4d40501d4219422244645501010300742c1414100c071902641c030000d5020388681103000050610004020400c29001006405560310344905075009039200c80d1491000b2142515040e4456540e810402c802200d41d00104162842101603820052140d83c0718104a64281c00082894215101d0401c900e81d0410944610100e0b0360030026450030101c0d0444014400d040c0c6480803d84c50300e00080e0014080e04040344511014101000721595850110003190003 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 437682428 1250 437681178 437681203
    0x3082b0509070512120417100e0610090902090f0a0908070b0421230c010f0b040e0a03051603170403020a0317090c28270501031223030405 61
    0x1282d407240041500c00900c0305d800c0f076003411140d0f243c1410f00312900d00c10150400c980c5c0480c480c025141e4a21a40340c003030242080154402048182852a41100307120811703009020940c5c50580154056901c4e601c90540040050211070910303200c0c06100300c09007043d0100a03100c5e070000100b01c810000416102031080703002e54548001e015031141a02d00c504a00345840c000140300e030303020b003943c400c100140701620500c541c80c0500e0401c90034107050946000c0798040c0422596060912034a0510340904040c00800c440035211003c80e6943c00342090241d050055541c5600c01809406c150003a88024452540b020f06030b56a854a071a00079a00d8000c02c0703044000940081c00c07062240b02d500c10841c01403110201501d4180080001d00c007248000c240381d818070b040c0400701e80c2000042c00c0c464030058030b10a211039200c3c50264090001c010000c136013940c549860500100003044a240743c02c92006c802d4600032a0030220301d0001501e06007548180145500000248400c00400042ca03244402 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 437683678 1250 437682428 437682439
    0x19030b01050105072a051e0301110a0c080d0f05040b01080d090608040b041716110307050d1403090a0e06010e03150115020709090f05061003082b05090705 68
    0x20380700c400443d01c0e03021380c02c002070a68080c42500200a0312561488030050322120100c15420f07650000600300c90b101c42e1100281d0105000c4034a0241428017621200381e4004006503d009500d150080500c0780701d0304042d11445020600c40341c109407907081285480c41d00b1034144002d007042e02b84203402110a200b2140a8422aa00006814040d84e40e1074121207480c0c0b0b652600d5030712600c2d901104800101304a07120080400880d403403070844000386c2500c8001030700f0383c440c1c40e11a00d005090700400c0c8160324842e50082d14100000e030b07251500c003c6401e9214441b075400c04520306e5624594010056240c0c0d00c801c0c1b01d003000c1411074007043e05070710a400907a964616062000c1c141a02c4084690104501c017240c040148504102044c51070080181351044500d00c0d41e54081410444880d0f40b0225200740c412882d00e0b0501204100d003640101c00d1004c2500d009146945c3c004032845034050000300c0b008011fa060150040ea01070702c9070b00b0134112400780010b19100c0c200740e441c2c284074003444e8881c4 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 437684928 1250 437683678 437683681
    0xa111305010302060405060307051902060910050f07180305010e010c0806060703080103030e03032b05070203032e0510110609010209060d200d090317071b02060919030b 74
    0x82458010241280c0c1c003c3c10640c6440e0401e010f204865000401c2d20b01400320402c800340088487c1c4a505180a80030f034064422800c005020608010a0462003000b00d8104800d0000b9020445001c541044244c00d0a01e40c00c0c0007145180e01003203c070381c070181c0154a0800c0285850006401c00c1c13140075140d540e603800941c0e0380c0d01005003a00801d100500003a00020043c80041d0081c100315000350002411030b800c11080f40f47c081d4840c0c40c1800c6480180081b00c403132526004550148039003141d180e0002d5415850546407100141c1d00b54515021441003080344600e4084000004802810015242000290f001c1c071001d41803002c00200000c60384690000107003965010310990b003560000600e050301d00602c669980c4080c0038940d1000c05511900b1644000030101c1e84000c1c6110b1310582c402041c5502c13a818040d180c400c1b00c0c007821514081ca54200700800d070303102400803410301130f844188084840c0d80c00455000d0180680154001034280000d4110307030705401d14041102e21484642c85507 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 437686178 1250 437684928 437684959
    0x40509060406081f02040b0417010c031812051e0903070503070506090f031002041701050a0c08010326030901140c070c0b0a0c050a110102190b190209030a11 69
    0x8440c81c07803082280f15041003600035001c0c0c0b07149001201c844040040582025120f490b09140c43c0d210354002403240042c5940f4822004007030007a242c04040c681401c00608480039a01c040064461400030040340d4071481000c0c540380a47c00740c1f084004100c0041c0c015070901d0226084035403184080d14880e100784080000e5924000030820b040e00c8014040c0c50401801d0001d1240807881c00a01a038140281c1020500303801440c405030004101c0400c01c4081010201e8045007150710243c0002c8103e41480c0c4511803a541000e034a50440fa48408400c03054501c0c0140b400f1109150164007100d5007001040c84040b20054100c007103000380c01260460079031101c03a683c031400d1003014001041041404001c00000140d100a002c1085075418240500c000c0f594440e030030324800744c404441c1030659500b0403883c4d580c1045460072110012440315542030a903205c82403c8800100207208035101e003003084200c840b207901540c904441c060102c5802d81c3c11441c2484203545101070983c010915860251007 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 437687428 1250 437686178 437686181
    0x303030e0c090723090310050717090c0906030a0f030f0306061d190905040c0906050609010e1c08070503070b0606070804030204020a030204030f050a060b0301140a05060f0a0b0405090604 82
    0x20342019100c3c4ca036503440c00e045030030b420044a0308030301c0f107888240f00b25001c07902c080c00750743da00b04e0070000005224a024103015140c1900a208049410004400c000d01041c0004119050600c00c0710b010b180c5a80c2c40c80001e1400c240e918005105020303d001c480308141e04400c012501c400d081c0c4092101ea074441c00e0072170b141c003d00c000300211050106800200743c2007080d04034807584040300c0c094600d191140010415102c0c241e030200c3e000d002104040141602c2c0c0e00c07030755001c1c0200710703281c0c0e1604503002d000800039120000094480c08a0700b0b041d040d4880080300509585030f1081c1e20607200d41150500d01d07100d070850401520304004070341c0028003d1500d031013245c80055204903100d007840d0039034003440000c2d00014000c0090607420400407012500307511040b004544150020055642c90f45010016183c110f004203009030304003445081c20703600482c880ba92001c0146000a02607a9a000061100b81e42c86071007500615000804160312aa1400030001c6e5002500c0c5a40103485440a000 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 437688678 1250 437687428 437687431
    0x6090f1d0c03120d0204030c080304060e0109180f02160b04060e0a2103060b0412031d060414030709051305060106020c0d240e030c010b040e070501080901020f03010303030e0c09 78
    0xc2d03040c2c100401c004000b290300d03000f8011a40c400c000060416449580c2c0007070400541e080755034158404201040107650040d0440c035070ba207080c40d00140c2a49014850040401003030081c0d0b81160702d5402074040d001080e13041d83d0707480c00a1819001003c3c0e00d414600c1c4a00d2054409076600c500780307208041da19000040ca2143e903a40016140450440701004210230701c0303030407400d10400d0b469060005da0300741458054405007003200241c401c8d00c1800d15010385918049451089203040320094400580c2d00c5500381c408584031500320602280340300001a0801000c1d4002d02e050900d02000d0000a401610f66030711100d104e1012502d540c0d80300c2c0001e907640c10b02e15168691040d03c072002c100000e181c0d510031107840342581004c13038071604050105100783c40d600d0340713407a841e5800803411485c100801d010300f190140094900b088080d0a44000d0b64413001103000e924184034810001c141c0d5418258115600070010084594403540c4900c0c008002c2e00c4107025084039403144221703103803291070041480f6 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 437689928 1250 437688678 437688703
    0x150705030717090301050720010b01020c04150e070c051002090303030705161205190801120803060607080d1e1505040c0905031b042009010e0406090f1d 67
    0x118200780c0d4a5070350114041c81c0881280218806010358041c54a00340501806400030b5210301c1d091442407401c0c1d195030001c0c42005c05150703050070045296030740c011503400f441c4002540d003c0350501c0510040c0210f241c5c41d9001507403c4e00d6140c10001c0301d95202e03110b01c22040c032400c15110094070700110362041e8014000910f900d6002000810b545500442c001c00b0501c40d800ba03107000c030800d103840d140ca856502104c0203001c41c0c40052500c60000301e0103400c1c0e244580b181002c2c50b165040003e0441c00c6089020001c1040c0000070101d0650b5a5442c141c07207000e584000499a10b41840b51000060035900305015414071143c5800d0340b0035a03d0780642d1905100804d60254520300c1e160401014054080809081c45180d49011402ea10240080031a00642d40d090300482503220080c00102d0790021000d1005180d0b2154012a00307500d1000c0341d611000900e403604401c3c5072440050002d0400d03500c0840007a16007000091003c40d99004004441030310305818501c03240f080080d54440310b414180c1c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 437691178 1250 437689928 437689933
    0x2071d011a040f0e0406140a0f060f1a1e0c0705100806010c11011101151e12080322030c02040b1909091112150c190302030604090c0b0405150705 64
    0x13800214100041a60701500a00020968100c10101c281d5001d405032003a003442038071403c180d035030035240c0c0c0105401407010100304a44140303000c0041c02d03040c41021100c8084800040c01000030b5507040c1c498266034407280318440d921824442c8042e6900010710039240a100c405010a003014016103565100304010385642c05840364540e1400070b0403180c0498507043c0031540010035074441c070034490310401a500d00c0c0101e1146040484020f44c070b80000729a444940c540c50300c103000002007014003020561344841c4840d02c984802100030341c60030500500b103040400741800c0d1030615038012480076689000355000c1181e54000020f2000e0030100e140003003444c2d58444420400d042d1283d00860f4150f000d80068500012404006583d82103840340040690784040c190034190041c40801580022000884600d00038040141000d8541c458141205041d804400900e2980352500990016a40a00704444198858044d4180c40c0c1081c001d2030300032480d14140d448068491001c4885581c0c01500 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 437692428 1250 437691178 437691209
    0xb0a0815010f0c03020f0d0e190b12100b0a09182a0905040614010906020f06060405040302031605061006020703052808040803030411040912080702071d011a04 70
    0x9090f102051800c0c0c3c1241144075000701000b0700311042c065481d46103030396036030108010307820320400111000c07400d04040640b48000c42000025130136411a080d0107440e400c0440c10f595a0710925054050a0784001002c0e10001083c06000d68048810700965140c0b807000c206603104551810708855103804002102d4010311004440d4403950884007000010510300615400d4540010034140c0f0700541c091100340510895180d20341d80c1041c000c0018080768030050018a10b216001690b0358805000140141da0300d2011800f80752080c0100c5807402443c40301504030701c0c04ca01d80740380c0c3c1d034808880784011113140314000314085101044960860303420100401000004c0c405c007161043e000d1a610490100c4040780390b0006051402603c020b040a1018640f245003905101103095040e0812a10440c40c00407002c00055068001441880e49481c2ca51010b40e070f0380750700341d01e0f141598001c0d00d4140241445100c40c0344486000d02c0c161407040382c81c01001d8650001e030102c2c5008601440d848004400c4 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 437693678 1250 437692428 437692457
    0x40c090c0c031808030c030405010e090c0906090604050301090515180a06050901020403021503060108060f10030b04180b060f0108190504030504050d030806180709050103090614010b0a081501 84
    0x1903541c040e0300340c441c0d202e4200603900c01ca02c03460361b80442d12144071500045810400d641c4c21501c4002d5100d01690780d44040c2c9003510811003c0c0c82524001441034901103640640c03916000c0c2078a001e0100900200001c40301030510640e2648031140e41c5181040b641d00151044011000e001041c001d0940105204200c2d55203c00c098030001384522243c6d982400000096a03400c010103a1600c15003141d1540ca09000000414140c3e004040b00e02a01189080c002e1903140d5640180501011345030006000304903070001005844200025411100001580c40c10710001d84109401008220303019040c00d1812070054980100c1102c2c414044920300f64401e00c00718482e001603520611138a415031030607485100003044a19221130680c00035003407008020060410b520803080a64892048101600c1c102c036004192032014010707036040503103e0422004203d0386401030341041310f4850840c25590703110341c602203260300320303003600400282082d002c01c4444a050403081070a02c41a500c0c0c0c1d4582d900e84 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 437694928 1250 437693678 437693687
    0xe0606030d1704111507062f07030c02120c240a11190b07030b040e0712030e030a0b06150301030f080703050c010c0504060e09091b060c03030906040c090c0c03 70
    0x1d10a0b034481220220b05a400e9440c254203085c4400d4005c0956190302060a19038203c900a0040000c10301c443e15031a50305010009100340070443c254940c59072100301d440c0807500c0f0003040308000d4201c0b0030400048030944021607030060031141985d0002d07407101d600071011500300e03400380316402008080111000701486420300305001800c2c1c200b01c6184074a20340d81c3c01d04110503964140e600c201c1020070300c001c6030ba250090149565084400340003003402460350540747d00c1d075440ba401c0c10303d900c0302c03405040500890b0301090244c030081c282c0c0c220460904082042130f40850f6650300c90080e14020720400d400d00000d482c1600d400841a1201304c03a552b41e40400c0303034414401941440000c2c00315840c842d400f4042c220620701c4a80d00c40351654030f00000a4400380c0a400745621a9034800100442200c00003136114180c0621406811802042004140c0078810204040a00c0c04000f04000c1190400100b4500892040311404010f0790350329900c20480d20a4486540010082c01d00302021905c0b5 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 437696178 1250 437694928 437694931
    0x9031e030408042603180a1403070e060d0203120304050114040f0b041a091b06043b010305071404050402060a0e060c010e0705040f0203070503130f150e0606030d17 72
    0x140113103141d0001c10b00b054a4510380042002181d5050180c45d0724440e41401041000101584014000f00949240c0007a8450f403160007200000040003000455640e990a98500d00300d8020702a5002400503002d1000d49900469068a196080c040c18060f07010b0200300c0c0602c079681000380032080d001155900d2001c000b000e80141c0707510341440c44a040380c80d01c9101c0103000310f00c03040040c40181c2c2007268102d82c40510280c0c2c82c1c4122414882003005e07120302240107030004003a807454450501e03510618203100000b1803088140141c100300120070001c00080913010b503029001c20b0244018075504001c07d6887c12100207400090501240151501908450041020045c2501c0c00c0c008904640c60840301241c0da6081c065000400410260820b0700c151000520703074180c10f5155180402000d0910b10000d00320601e61038030520150240080d0b80c0c5031400342507000c41c44c0000341190342102c9002e414003000051032130191201082e118500014821061646500d4400200e03040080c1008804030 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 437697428 1250 437696178 437696219
    0x150e01080c01022e090b010909050709020a0e091b0f040f05030109080901180302040f0b0415031205030a140a1b0905030601050105130e13050708071215021209031e03040804 76
    0x80742c05c00301c400241c0c1691424040c040a04001846412a0826038a01402540201c080e107104106101e2110b03401002043c50360025100100076480301502d01c03511120f09510004422004501511001e40c610700800c01ca42e8002120700030f261303c0b441003600f00c40d2404130040c4551400c2002c4041d44d40568650b654808217600f8030645561340e84c010906442074008269410303582c40b050b520741460f06100b901c43c0c48200711403809180c0d04660700c0c500301410000054081c0900800010a4008503812911900042d200c40014504103841c0c40f101800302e0040c0036101e07050294501f0b41580c810b11503d4201c940003402040164681001512541d005480020ba022402c8a010410b00244051540698202050b0721480e0700ca03424024100500340d003116596806c040c100f04285605080342c1d030580d942004a1030410300c52040540020721070180850001d954407020844084c02c040701610b0b031844d013550015442c94916151403260302c81154010801c0e0003c1c001403201c0500724a0f000304e600ba = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 437698678 1250 437697428 437697431
    0x1b0602120d1805250e04050a260a1e1706100509030703050d110d0c0b0a0b031507030507051e07020f030703110a0f0302060a030e01150e01080c01022e 66
    0x107010303190301d801c10211030404c109400d5144e8012150040c04030300f0000900003149000c1541c18203984064555280724409400c040a0041240c42d80009501c8414420001c0d81e03c0340e0317600003484001d0410300501400b054041d604525031007000703019000c500100c820107041e449441c0d035242d00700b040e0104984200b10821406100f021031588081055a010b10f0085005100e402c40320000100382d0760000a400700d5940108110f003110740c2e04440d40c3c0c0f070003e905c00b0038002c2c1030760f03140c1042004000001507107501d40700340480040d0382d13001400f6050041010755018001030741d4020090786d180c07082e03403401050300359014001c00021011a000c2c0004e42d2000f4000c60320181800c00191411029030025140100e5003456001c15182c10501d01001346144480d0380300b59855030300001c40e64050185040d00b4181c80c5d82c1070340c942940a50100c1e101200040454841c01d40350070354160701241c01d0107000854861449000d1466000140c90000343c007803c80c410a42600030307480c420352034000720550304649 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 437699928 1250 437698678 437698721
    0x31905130915090e0307060b0f060406030b03010c1e051b06091e0105010506121308180f0f09130510020f0a0e0a0501050f0f090402071b0602120d 64
    0x200c00d41044001032688120104500740c500d240220052000d50040309582e180421034083c9600100981e031a03c0c3e045a0005201c1d1810b1002c070b80640003804240354080400603000c19042e4055111300c000032803d4000b080091695501a501d0208848840d0a60340c0303401c10141085106000a1200c000c0b00595100c203511030440c4140380105c262031030542c0da0800201c603410341410540f000ca02071f1410b0000e00076541740002060440c450100c401e003c0100a50010704900c9400d04002d42c1da41d0708c03854407540c0d0b0622000210f004c0148003034151007007203c1d15a40c003451520403a400c2c40c03144000c103031412503182e400411100500c9030710112464012501c00c0b410b401e405101400403100b41d002216900d6440100c010301202e004450680324000d80c4d0420301c20742c0d03030100985008c40070341002c41c3e03900c1394400310300b840500806c400d19921070300024240040101200300c03100c61414215281c000e00d51039050070303619007004200e8400b0461040c000075925010303079003200c50701444003202c69115 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 437701178 1250 437699928 437699947
    0xf070b07030f09020f0f062a061f061b02090702060a11070209010b0a09230909060f01030201050918010b180a120f060902060a17060a05060702190b070c0e18031905 72
    0x341507607040400c070760140f232038841c1146400d00c40d041e8007151050106070558078189007501d001c1c1103409208104100c1d007240492803d6103000d12039202c2c3c0c00070180441032512840082d80c0b81401c4030400031490a20342c10082041c0307260240c83c05c0f44e50051101034182c0c2000959038481e04286100010008d00c1b2100003520f911700540b03c48000c0500c030105580c40521418820401c10141c6699490384c402d604209a03001620540c031b040d0b80d424a0043d03035480d20240004c14465012020504240280d000041c406030480000d0071520048402070b050800b44d44100007001c6c0f401e10420242c0c040910380700d030000b00901c56090380c240c414400003604881c241c01041c1f0351341140500b440071980000d03c02d8420403425000c180e11650464248202d40d0802000c55440d000340301000b80108003540040e441c485900540b072000e0090440b00b03980303409041c1070400303907041c05125150300c02c8402c001194000c0180881035001c0351000004514050051001424201402c09094208402030096550 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 437702428 1250 437701178 437701207
    0x2250c0b03091b0a1211061309020d06060801030c1427060306060901050d0b0408040504050702030d0b060a0c0f0201140a09090506030f0703030807050f070b07030f09020f0f06 77
    0x581c07182c9004101000c203a802c0c00c041c80c3d820108161082d650040204a00380c90040b06441c2240e001e811129495180c40114803980280ba0120109241c20311300851800603581c09003c9600c0e031102e043c4096544c50900390b528103c28000505020a049018060034102c00080540d80d40003411500e00c0c0c00812046105660185540d00090b43c1c40005005192904002d41a0840c90854401405502d4007000480c0b1074040c00b0000d0010310460300040920500c42c064400800020380144420700d080c0b400251250702505115581d68504031040010341441022303200642c030541c40d0303410301d00150b0300e400c10b41c001c08803422410048401d00d01a03d042130703030001c2c1500400a44404200604080744001540c00c000e1906000341c1c40040780d0300306d07080c0000d04582100d41605001d001611340341c10440d010300c59108888001400021740d1020488000c9280d4814112942c04000b62030350340c2900c0301a24400c24000e0340c84411032001080303502d4550240035410790001c00d00361901020106149 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 437703678 1250 437702428 437702431
    0x409090605060108090d2c090c040e0f0603030f091f030f1406031905070b040303050a110606010207140a09050c030105030d02030322030c023102250c0b03 68
    0xa540d552500705001095070072103c2c081d00321026070040c000800d400b000003000002910301580ca500903046121070a1a1030400e40b19001d5000f8080040b180341c4440d11204651180c801c8140200c070700c4000503003010002d11007074002c0c04020050352501c402c440342d02026401151080703a004a1011381c01003030404042240d801480607860202e0b00c1c1d0103a91000080701c175640e40305090545448204005079a0204030702c020340400c0b18450489000d1400e003203140403019001450303100c0c40014080145900310b009000103090590b00c85541d0440c11104613214801134608134007507480380f40180030103080070300070211103103011f00040245a03031842190140c1c2c0d015921840c030120000014041d03420240300c01500000c1da40005d520f0742c08d1040402600f104450b0306580c5811120940030100f40c840c032a0400c0807038008103880480604e0700000a10606802c500a108000c11540c07046401600d0080d00d01080c00340f03030401c2c040c081c00c40038000101001c403811903000c083c0710004174142c10700002a5 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 437704928 1250 437703678 437703683
    0x20408011b030c020102090d15020c060106020105090c0f010206040308090c030106030c0302041a09010e0910020d02030a050108060106050a080c070c0e010312090e06041a09070c030e0d030e0114040909 88
    0x80e401d0303007600a000c03201c00300038180859004108002444c2c44400105442e07961040c0c9803000940d0590118000f4010760039881658000c40c000000d00a40c1500300314040c1d071402e426215032486440c100100008504032160140e000203000070086405121596441591031040c0e17482c071901d15000030308403101600103d82004d4520000d2040d0708141c4a449242c0e1611908004070f280e0450001b500504148078000c0d0540c080030010f00906030034000140380c441e20100941d00c1c0c5034845c15040c003940086420414a51500000261040000485604951f00d903100e00340341c05e09031502120032450050a5480c00002000210f001a00301a00c40300104035070b203c061050350561808007103039031030042d05004101038505c0a02007507240c41e02c0c00d600080121000214054141440030349510b10000d50303a032000d121030810000c00d0b0045100c0100314480e64507110740810900800201d0401e511004c0c0004000704024000b55015110800003144643e04050420f41e5a170038600540348961000c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 437706178 1250 437704928 437704961
    0xe040c12110c0105010803030702060c07150204090609050907151d030706082509050d050c09150102010b01020610090513050601060509040c030212040312020705100e0f1b1302040801 80
    0x501c64182c0082c45a54050216180598a18142010025070340c00d030240101192180010f565000c20a8204480b0b064011420f0150340740d40e0b51701c40c1b2030024a80c5101c2c03c403605007002d00140d45442c0124512090707418502d010104091240c508032600c0c0b1030140c80e1009086107400c01c05c59950100000d800404107603032aa580341c07821140c400540020031100b500208158982c02501d160005400e006035041610782d0b8900c40c041d41005031410340d0445000da084080320090041800d00050030f182000d82c00e800901199540d8001280d50740c0c2c0440328003108118031101401001441e030040ea030042101c90002000410b25200d45042c0b20080e80201c01181c0002094034030703428a80101d49080100e130a0442c20902d010301074070400c4e400107000600b0001d00105403602d20580c2c3d81035404050700071080340e00f2080c105079810001c028160b003002891203040c03041c0c4403c1c0000208090f46001c40d031251583c8400c01c5040c80428400c0009480089400740000700c2e0300c400c03d01c60080b92614410f034 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 437707428 1250 437706178 437706187
    0x121e030405010e07060950010f020705010e0907051c02120609010308070b090102130f30120e0405042111070e0406090b010b13080a030e040c1211 64
    0x101031804d0071540c04101440700c1d8000400046051401070914034048403118840c4078480343d01080703804032801030091181c000b801070401d1541100800c0b0203640e006c0e2156503c1007024907013070f6034500f07007441018005901c0c8090007a5030705201c1d2200781c10a000c1d04105003000c0342a6221140030a00024030050907502184203000a00303451500340e005201514080e010b541151100c244078411140e001e00340780c2a00000c22000b101c25412075842d1408001c40040841d1107000c031680d0803409208440802c0105618110f040070302e41e015030f500000592444440440e0b0b0b9460b0020991a40a02002d02c0f82c20500d509890b21342d801641e124501c81c1c01028000c03103461201c0000e02e0344861710102006181d0716402030b981c50003d541800e5404d011a0002c0c2c6a8881c5018030140c52941c1c4010101304814000044c6000310501402400c24805154000140c84100c0185c3e2803544000140010300c8240b035140c1103040503480f4040080c0c42d46000540e00c0200780080c404c0d18001c00450072681c10004 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 437708678 1250 437707428 437707451
    0x8040509041a0a09081605120a030e0f070f1a121006170403020c010309230c2805010804030e0a060f20060f0907090f021e0c121e03040501 61
    0x10420359100c076034001c1c10040c40004e525801070700d0040841d9041d0300c6007071910361410f1003000c001d10045144116105540c0d00400300005001d000841071031240e03482804456032036860041411400c2d40c11041042400320301c2d0440c00d8183e9009605180c000c10360410101c0d103001a010407240c407445403604202201031500500901040d8030b503040c08400007da806100010b54040340c100c080600c01d103008180d80400d030424412400c0310398820100e4a02c1c02c81040300c2034a021584103480e000440e070302ea442e2080e00c01d18900d03080241030840e0100c91025414056580a40d20030740d08517000e8500300e00b43c4050b5001103054600c0540010700428050026030751450792100002d20403583c09240f070000480a40411a070b04da0000d0b044c400e0b2840b06100160f001c00e420004034001300b00704002485055880b00e4088001d40c8940704200c10310718079281c0c3d901c0c070340d040c201220403003902d00e00241050786111110381c415400c010004400361205e443c0664203103091401550051340200c00001d0803d000c00c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 437709928 1250 437708678 437708723
    0x20403031e08070915110109140708070e04032321071704020f061201060c0b0c030c0a0e12030c030d0605150a050a09051509030d09050a030f0804050904 67
    0x403091031081000150030410701c01da101c0c84013000c4440724810043c180d13003550b40c01e8900c410a580c00210662800c4405c5060100100045c5a0007068030159001691a90040d603129142070207084281d04e402004200028480c03e05280b05288416810780b1082c0c00b95052500b0360b1003000080099800710055044426100014542001d07907414201003522074422038858012004001910500a90f010311400707440340400c60302101d00003000001c041d030b150003003d03080c000802000e03510103040000090b030b8420f040007200d0203250261800f50030070118030301c210343c4e01419250723a07904000c2d91400c088a0314001c00241102440003070286440b01950030145040b00c440b03510051003454201455201c12000004859000c602480c1c00e560381c1109010a9a40e00602d0380991b40041000c800c0203586074119001d0000000300f14140d4585c1030792044100d8031456240a0180d0042014a0401c0041c903148020700314144944019414655103000181942d0b004031800d6501d8040380c0c1000c51182040e = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 437711178 1250 437709928 437709977
    0xc0a0b010321110709020d02091504030308070c0201090311010c050f0d0216060f0503040303140c031504060302030c1011030c031c0207050a02061615020903010c02010612020d140102040303 83
    0x240c500007019041c2084101d544d032059205841589900117607000d400b04051701103481c0130714050f103042c2081c1e52842141034568007510082e000120040041640a0320a401114189805030f49400c40d903400c584403034005c1f043c443c0b19281400271104294002a209124040819031600007400c4010b803142806070170325120602c0f4804981144405122054201c004240e00d02250f280c06600e947c4d45103000c0d4001c00700d01114052004200080001c014400c0008500caa0114002d41d40028200c0e03003031209441060100961603081010390310310720304103034080c0c0c00000c4503858106242844a0402411a03020001c07155250b0400914142c3c800c0f0001e02802403865000c030110314082071078030386503112440214000e1152000250303015010b520040160799441d04418514160080d102451000b5407020f00018083c1d428610900030300d81c01845a10704440d5088020b00c0c681c0003981c01c1008800c648401205c0341051000b406480701c00900c0648050f61194030360480f01a080d440342e0131020036 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 437712428 1250 437711178 437711243
    0xf0f0605061215010531090509060f07031118010206181b01210b010e0f0d110102011b02030403020a0f0b1605120d1b0804080703050c0a0b0103 63
    0x80810030100c03a4000500c80c03e0b400000ca540c0d5443c4000c0e01d90048446104060341d2034001e4100d200d0b030f0750041c1200c505400c4004101c80080071416503030120b800907500d04580c0304e9500d411541c0050001b8604040307440d4040e00518000590040215192140b90030144402c3d0300f00d40d0701039010420b035070100192074104072204a01e0700d054102003e0b03d95149010500c017002a0504404558640d0045010100e0034200070f145000401d0300a00100080003403440301800150000c043c262517007800d80b02e03410481005040240311014a07283d020704404220b103424110741d6a000c0c09030021508070303c401d070651035a90265940b1882c60040180d000301c507422002840d07005941c200300f01034905084880d450362640d41543c1403072076802d155062400078003d4040100000800710300e005050361050f107012911000b10203801e00510001c546c4508203c40040c18084100032020200c2e01550290003100c107101c0c200c545840c0345a460750341e0a40d0a17441264081d842c00450802c0c00c00c40c400c0641c2020 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 437713678 1250 437712428 437712439
    0xd0b040509010b060403170d05070509040b060f04050409080d0504030206071d0d0308070306090f060302190f180b0a331b030908030708071203060b03040602090607060f0f0605 77
    0xc40300c0f03001480c94410f40c40018802601c2c15070b00d200c50514081074030640e0080c003000300450306d00b958000d800b95200c40301c5684035500d4002c03202c07428904401603036020108400d0040c24982401d0a10000301811202584e5140d010b1225491700b900f1405020320a501c02e80c0036003820b0510f00000f4000b458410280300c001d461020314211251144100d2826a603003600d0220f0451f11545803e41c01400300b50018011039013082d003203058240407500240c04a9109131200c2840d528106180002c20890303008210704400b59031420451102540460102c0c00c59540c000140340f42014002001c1000550141e81210100300805603860309419516000d58041c54044484040d2804000c2c40741c4107801f9030020141c251940d400905110398414406840c215007240c0e80c42c1d400e814582c4254010b810212a140444000000820300c40d001c0c2804454400f040c490942e1500d9035084040c0d08590410750b08520180500b9020032003501a1020420300e03181c0005001c1a06c10300340c001c0e540d040e0400303402117 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 437714928 1250 437713678 437713691
    0xa14010204150912020609010c02040f0b120102120a2307030504060f140612010e010e0705031c0503010506160f0b010f0603090f1509080a0801081605011d150d0b04050901 75
    0x40880c11007030301004c0d604541c496601d10300600160386441d20010301070340161801d00c403d00c80440c1c0d54800c2d20320003c100c41131603008540b032498038241d100d075114900040c901c000200da01c50025800040f041e54440e146020400c0900e40c07890b0714058115100000282c4a0041c48207001591081d04100f00c1c2308103040c0130034140c41c0030708204c0b004046e01c0b160180d07001480d0190408020761103034400c1d140d90380092114080c01ca949980e55800790107803a01c41d0282040010100c40501d1010007685d89a403252800c2d80e1800381001a40c0e04a0100410240c844184800010344844010041c480c818000407980d941003410502021003250841c0060502d40064107000c290706d140c0403000d135940008550a0b900d414902a0043e1a5440005006c04130219104421a401c402c3d078030705840c04c0c00110741c20b49800b8184010600305034490307103001c11003000c1045541007a40c10044e0300401c014002e050285001083c44a07a42d100341038109560741c0c0d0703140591544c40c080c09015040f095500080c4000d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 437716178 1250 437714928 437714939
    0x603080304120306050a0b071403030112121701060f2a06020c0a0c180f09080426030c0304030b0c041a160f0f03170f0c0c0a140102041509 61
    0x191001910103003190002c00b05520340c1a01c03c1c1c0214001d80030181001196a680d02c464410540141c80102c5a0303560400c4036501a400c0002940d0403546604d00803201c040b42612942c50313031100f07100c01c0b100300320340d015040340c4c4c0360300c00e0b01c02d14020680703542d0b00401840b403d14000c1982076108441d11a0417008102141c0029040c104036032090340103800144d44e103142502c15494000d140100402d201d1401ca4005080103060340e82d44250000b20b182400b403030f03c4550300c2c0011a480440c005184020601060084248110560000e8031404100ca000440442c200501d903402601448401e94030002d0244108811002190342140b072039001142803d0400c014548091000c6581d90340c40b017404140f5500ca000300a41d40800c494000c28000d180c03245904000440b4020035070142c1c00702c0c8c04c410610100e041d50480a5106490800340002035894006c84001207502095420000384110b101c2400441c4001202000700750a1400040e42c0c0c40c54900c0301291960595100001d1081c0c1c107074100070 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 437717428 1250 437716178 437716193
    0x1109070824040605120114090c010206220f140f010e0606060a230702040e0c010c14010e06010e01030309060507030c03141b0114060607020604090e0c03060708190603 73
    0x40034125610800514480000070a008191a03400076900501d56a0503680200c0d06600c000c0c1d40c0464100c10760900e0b5a4500c42c1276484c02c1004580c0d0050303118a001034614a003100309502c0f14100500c0d100120708564680c405460401201954420007020660300f01d4941049941a29003103d80284810500c43c8441d50b22139800415041c0600c030b00040d810140c134030079071215414007500741e0030078160000000c0c034548a0b004428120700070b5107070407110700c40c5403000030700c003404554160740c2d030040c403010340c0e032200d40340104640e660503550340b00c1d54001601303101030002c14068201403910414640c50745c01e006008006551201c800d0190400166011035413011000c4001905406c01d98803c00b85010f10340058828501d00c40c1c9038440b40000291103181c1900252000c0e103028500d0301c01d5840c2c2100b0070605105148000f54402c070100070402c1300c1e01c41600040b4030361290303106481e0310001000101e070408404a6034a4001141d1408220044403035a250720140e8000c107204001c1c50781903030707507154 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 437718678 1250 437717428 437717461
    0xa0e01120f080a050418060311042a120b090f040b1017010b0a061d130207060903090312090605040e15030115030501050609040521090d11090708 64
    0x1400680c5551032a0280a4070310181804550700a440300c2d955528103800a050340c01a00503180746000810500900390140d02842003507d07040781071000701038207100400000300342ea0a641388002d844040c00400f40201c5150006417034540e034541e01041d44200c01c094086440d0010000c0c0f2442e1810184a8001000714032a070f4029401402410300380c8443d048c2d900ca121440d8001c59038400c0c00c101c1c240c8809010b4000d005c021201381d80d400c1103d900c0c0c243c161243d0b04540281200300040041c100034a150a240c854003914036400e00602e00030083e101c1c0c00130394906040503008240d07041300c20400c01489141a42c64078075a0301e80440e0050418400914130b1080d807080e81c083c03030a83c6c00812841c0e4103200d40044901d80050080010007208202c903404040320788002d4039503501c0c000c00580107092a80d040c0388a240e00c9000343c01c950a0704601803100804840130005100b0051185d46030030340f502d0b160300315114001d041160f440d500400c10403c4d4040001c3c12441000300a10a0029620740e60106a = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 437719928 1250 437718678 437718689
    0x706080901020d0c05040501030f0614010f03020909071815020a030815030604051006050306151002070f030606091107020a09110c1f0b060c070909060207050f0d030b0a0e01 76
    0x465a8903a80e600c80d01a02815401d12406032420100c119440d030048010030440301c0c20b880600100c00840d00c40d130100d482503c205110340340354136a000c21030743c41501507001015107802c0050804a803080491050b65040f2103035000324406000d00b110320850343e88900000e008800351201c1d403400105000b0b40b03480780008014280034a40c0d0202d11080c110401e000910007024040b1002d81c682810314546e1800000c842c0550146001c20200c1c56083c0450203070b1052141501541064562105111500d813000301002e0842c06003101c080361150314105200300441c091000480d00c0c6013040e03114002c03601e1200708030401040800040700161204114070741110502070001500d00c00b810507054aa00c0350400d50702c268000c4110100c9080c00c480c505072900e0f01002ca0800c40d07035403244288000781c440e814401c001a807001300c0070443d424840e048801c031648256000f504042c20f07680c4240c90442c001c011404117411810b170b103581c0b40780d1611954260355000c803982560b0a1400940180c4000107000e40d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 437721178 1250 437719928 437719937
    0xf030901060b0403031416241505010516051c0c11040501031a19020c0f0d020a0c090f09020a1404050601032f090d1a06010203040b0a050706060512030403060b0306090706 75
    0x80301c6117041440310141f180342c1c020318040b10307204407815036080c03042e03c95500700c0da403a207030003440f01001013a00444001d41d403040e102e06181486a0b44072411800d8154411915481903000075800b4403003200b6545d200c001c40e5100c1c420145803c4c07402580c110360700055280510303e440010008110b0b100b60350000c44a804c41481c05603265031001008181ca80b440c241600c5e400090081001c0c01d0003d01c0e070100c1e401c0b0f90b00361090756075030010032038070b07588001c50180054a03151803e200c0314095038040c0000610344840000c0c101d80d01c1d80481c04d1f804540d404000f40d102c58031010b1030030741024000c0ca68810024a410040b24000c29080c00000074003002d50a10704140050002011006804640000c400200a0b00d880300480c40c00e0078400480c0b1100720350441c072002c085581540000192016207010714451030400d40c101c0c6040b5140c3e084403c0540e042a1500e40001e0329889141144150090440155581c2d600710b003400d030191042c014007203000382d0006040051120012440c9010784200d840c1 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 437722428 1250 437721178 437721187
    0x51804020c1c0c05150c0909090703121e020703032c090a06030327061b020a090f2019140c0601031406100605030601140f030901060b04030314 63
    0x31036142c400203070030000700c04682c0160509040d4104003a405102c0c030610813140003091070181c1c4205042d007516503072030211041c070a006092030110b0000c1d60140c4400200c3d4981640c0b6212911021080d181d4400031500c5142d600c0c12241c0e1204011a203c0f41c90300003810368500e1036400416161804981c01e00303400c0000107101048075400003075404280700824100d4075041284203030000b00b50512084021481801c0c0c041c00d00e1001104d00350b00072003500b031581502131828405030303074403481191176680701040150307010700503680e6241d00406040c410000080c1111180c3d0a10203d50303806c2403802070869132a07040c8208689240480741da00c10001c0e2980c1101e004400c0c26110300a8820072004020404101800c1c3c1c41c3c000540c09040f43d000b255100c100e0110002d00a45030bd0043e00c1c21102800c2200b420310800340680c00446d000501031421600e0710365009049007580e081a254400840030010502078060070900840c4040c1c0f150452452901e0b1039603401500101180140108a840c0070a = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 437723678 1250 437722428 437722447
    0x20312030f1501031803030c02160f0e0603060f01120204091e0c1e170a0f1a0601050903100b06191706060a020709090206070605072102090a060804061b050703090605180402 76
    0x1065800840e42d62000700906d41cbc58107a0f83e400c0b18031034080d054100200c400022041c0ca00014080c0c0503200c4580058901d0342001001c960318540800300b84d8202e0344513500080021713491620000e4540000e4510700010b07510749001c1034001c580b40d00000307814681e2913408100c02b03071b000043d40c00c0310309100b43c4602a40007141a1402d00d1082c840203060403035201c000c1020301c100303005485600102d02448441a540700380c019a03103800346040603034250340800e400c501d11001030b0b48252036411005141d00d08200c240c1e4611100d414103040840002100240d480315201d04044801e41c002d07200b103411038106094448005e6032501c451199240d5203491741c80e11400d5440341c4d0210713400e6030f80080051000303180c46e03280a0700c1d003507020740241c001c01c440c8440211142110301c250ba0b10030700c0040c040e03200c2910b01002140d01250241058400745da407410300342004242000c03c2844100300317455803901e8140380d0602800018080e48480c041c01010003811408274180c40510b441071904640041c3c07540784a2 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 437724928 1250 437723678 437723683
    0x606050f030a1407081b0f19030b13020a020f010c1b0f0501090809090a0902010207180f06060201060302150c0607080711120c01180f020607020312030f1501031803030c02 75
    0x40000440912000c0180328201740d000103000e10410407807107404509103064085484c980b15540c1c0e009010042801020101c142d503083e809450364040ca000b04c1e2603403c1e00002031803810513484114490b079001858189054050054040c414003490081014000c1420054041620000140241d06141108108011600180184060b0040002c0080300d0543c07420842941c4075810440c072540d040d5000071001e07201c4d8028618000c0d0f043e03014040c8030b440c002c58030140b2007080190076401d5441e0402059044039034491b20b001400319078004100d0914600612110044052a6001c022810008216143c0c00060450303000550303894104010341d01c03407038101ca24000910003100c09008000007401c40f001e03100090444911030728020000020381d01c114074020301203024001c102e52a44130414000d0325002024007560f40c000b4044e202c490200070340348002603000725803254144040320144074088085241c0d840000c0400c1c00d0030002c400c9800c561082d42220031034000d04040c1c41d800d036003114070710a = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 437726178 1250 437724928 437724941
    0xa0e040c08030d0204060806120a030f230a030b060f030f070522050f060c060a0e070e070306091b050304020f0f0a1409070512161809020702030d02010606050f030a 72
    0x555050301d854001143d101c00c040c0d0b0040c8545e5002a508402203100752030500f141ca01d807010120000e12032031003180e0303058070310409800c1850240b1040555031041d02c20700c11181c00031504036920303065881d0103440300a81214008807000d4005c0106102000004900c181101d41000142175408a20b41d50008202e406105407400308084030388440c1490b6036030a089001e101540c0003241c005e0a890f0300001400341c0350103010707050489503005c40045a51011540e200300e10800c0d00f24140c0d0f002545070010000500800e4825400107507840c402080001210701c04d003d0343c1c0382210310383c001e0001d006000529074000640040e100d450248000c40d140da80c0c1c00e11036415134501401c185d194a654081d881624244542480d00466007400002d2600c0c0c41901280d024240d0050100c5003511034064607400030520940100c1031141c1d102c41d00009a151028060081003c1900541d45880c94810315050207203801b0305800707680c1031080602c03075180c020003502d41051108040e152a96926140b00000d49107 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 437727428 1250 437726178 437726189
    0x160503130b030f01050306100302010e1f0807020f0304030305030118090b0703061a0c0d23030a020a02010b010e03030307111203090109050d0804080406031d011a010e0f0a0e040c 78
    0x501080000d000d201140c0554401c1102a500f208560399800900d606c0310811035071044102c000c5c100c2840158042c0392548a0344202030028040c4040c0010759a00074003001001c1008640c074502003249a9130f0400103c080788079488041c40c02d1502d940c0d0701405a020600540d4000100031103011501020b41d13100c0f000640d00414000c00394240518007034001c0c00c09010321789403800500350f410700840e100300c100e58400405000418120315074a004882003030400c000c65100191448540084040c0c0f00d001e9030050041ca040142d0301c080c0504040d00310f032a400b082606001d40950b88402565020090f00c2e0320074001d05101c6da50000401d00c03507080642c1000000c030291004018400880b0301544003005007445403084a480d01403228095a101d10211801440c5007801c020900409220380c005100b84500d000680580d02c400441c408c0c2500c500022040325184070261b0f05080e50ba200c14450602c68055034040300008407000440c0241400c0d00940304440c5044004c10100071006205600915 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 437728678 1250 437727428 437727457
    0x3050c010e122136030c0c0907030509100c02030c12130806010b0306010c0c0305061f290906071505040204150503030d2a1707020d05160503 62
    0x5642e40c0c2c881e00720303402c0080380c002e44031400c25020004900201c0d03c140251541040034540c1c0b11220001c0070440d40801500e804140300c010038000320003040028014140307409020703209003c1d01100b4000c100000524140c205410070040c0886845c011070203945641e0000300c04140485000001e034558400c084071403400d44104826110b0b040c20b03580c054220600381008401e80e6036510030070140e8461080c0640310324000c0070004030700250f02588601300ba041c410000030503040d940b40c6506081c01d00c102ea0a543c42d4070035002c80490320b40080192805030079580380b04c408400c0580c072105036000c8514040320304a0320009402d0969a1202d044c3c3d001702d50f0004d1104201d0a0380c101003405080c0a542c02c9001d0b07424410103448401d080d21a08040e984041d0040d402c02000100070409806e103000400031100010a5030041204070740d2840102c40000e8070b070315110980d8021715104929005048400310f411500703810fa2450b0b4040104c5500d103111041c0a8a0840c031410840d09610545003100041e0f03 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 437729928 1250 437728678 437728693
    0xc020d110a0510050c01050a06060f0518060301090b011e020a080c0f070626190504110616030206090604080702010f020c0319050d09050a1215090f0b012103050c010e 73
    0x5030b00a00800b50101c5c03000003840b03103848915281041d640f4a004480208480f1910313002c609100d200a030059030901e0134040c00c1204e550001c83d6040e48203030808581c00362101010b204035600030300784125070781c00b02100c2d458000d031054000f9214000d42c10000c1035030000050a50380307200100308000620340300e0b609541c1c0e11071b40c07040040d00d5420781245039507510b0700804000003c8100d4204092048410300e0020100d01d48c505003a40050000800440d040c40c4480c10801258859001510b4182c1c806003002c0a0380d505414064985880100440360640c4a4401c1000241e480401e0f648515030a00703000f944c642c100c000603410103e81a0f246034040c840e0030007040e064444281119180c6000383d00345c6510400808089483c41000c0c002c9540207040f01c0b40401c00c1c0c2110380b014040550241c612600c405a020141d8016139500490542d10900d40640c440180302500f00164014409001c0c03590481403070805006006601c80c8016051110100310b10a940b00301f9007010780122003110982d00c0c403 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 437731178 1250 437729928 437729959
    0x1110322081507050d09020117010803130b070210050901050d05070801060f0f0c031112130504050c040e04020409020d1217060301230403030b220c0c020d110a05 71
    0x6002078881c41c2003511500b0042800320000c0006540560600d54609142403a908401c001420301100201e0400810b6046106801080540a8041c12003580a5136450070030b005405d40c1241c5540018000c1031041128000503900c84541014501c010708100380c1b50066400160740034003490341c0b250b540d07505100070000c140d5070003803009059071280d880c1c0521003040300c0000c50b4038a42a10508011908145c103240c0824000c803203201c00604440b0440d11340000030590710419070002140da811859a0744001d01c1145810b00030a60f0140040d426141414078084040d080780102401c00380c0219039072a041010740d254489410000754015040a01c1c503200500002c00603144003080401455007003000c03404528043c01445400804410b24a007100f0701c8900f00e0700500b001800c1102815550400c0c81410703141e640d014945180241075200030740340705003090000c0d42d101e40d52010400045610400050343c900032150005130700b2044010700b204000f4007054001d2456000380ea4403500500d0981107 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 437732428 1250 437731178 437731237
    0x30f0309060210021206012114060f030604030207060c05030403140606040606030b0307061808060702070801181e05010906020d09170705070b03150a0b030108010b0901050a05011103 80
    0x715405542210b154901e1560144128003c9041780040000e8001c0461403e42c0300300d11a80070100f4105c1c4010292403044c04001c22520104d08a031140511001004a585000d2101402c021010342c003500807850107175070003074071849a8020802480b402c229a8814480d0030001e82e0007941d031015440c1aa60090000207680f82c6085170618413a60a040c808140944039000d004040b0a0290003400b0507070400703500b42c48100411400400c03e440d078200c0080c240c4020040d55000391542e40182c80c1d1141070a540c2c41c00d4605403040e80142d1803030b04105c640050400d030b860204810940755840810146881c0c85800751103c004050074803400843c1d6032020005a81c030040c48c8910030180120f04007640d0b42c01311800c0c00b4030840941039400c5640104084004034000395030114540307103c000b02d4480707480040c900b404560000d07031119a002c401840310100034480c054800c10b04603140c8400d90b00d46000503180701f10307500031541000f55120038101241c034208250b8514120301460141c40d0303a01144a00e0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 437733678 1250 437732428 437732447
    0x708010b0c03120f010e1e1512010c08041203110d0902180703060819051504140a050a0c080a0c090b0f12010b0f010804110f060702030a0c180b01090306090804030f03 73
    0x29040c6c082100401e038a008004c01140d0305000ca015800890b9807115808811800d6000140760441d40340c003a20740d400c80003841003c0040b40c55494400709401e042c2000d403001d5841815030f030149403a1041c248a0b2248410990300540c5e6041000b1810200070b2021070b000000602c41120041c040000703002140b47c064001d00d040da201c400441e481f80184040700206525800340180060700403640d15801200d10340c1909510901a81d646001403020040c3c46150080700107040e185500000702c1c080c00c10401410031001002084002c0001600030303142d80d40307011281d01c10f0498007036541031101260345032100c0c03048a0031001001c904040321264440f0340a0450005c0713451190601005488496000704150350080360065800502e10552006008141c0040e40300b890b03010009005508c01030f43c04102258030240b0a45080011901d00b405d010480c004078940103121a06154040c400d990b803002d4a24201c0b40c120f400410072a00900700840750784900e42019040403900c0307030705070145904a1500e2 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 437734928 1250 437733678 437733689
    0x31116061b05030f0a060522060e0c09040c120227090f0a02070303020d020a020a0c0b0a0507170408010e16050105120106030c030f050a0e060f0708010b0c03120f01 72
    0x280681c04610307600c040d148103502450000302c0c0007070020550912a80300101d60100310640000340b2551581c000810005409186800128440940d00f0302580d190142d20000c05280d4607a4070a41008080740c0340c0c0f406500c865a000710f50b00c00350211024445c0d03609010490350101708541d0340300440c0d81c0030300031503a2204640241c07408a981c525a030405500051088070980701d450107035101d458440700a9406542c065080603004e00070803041d001d46100401c0102d009800030011620a840c04555201c0305a2041c92103540520044003074541000480b403203036074000c002180e0908020800700041c01250403000e90b0751b10f022450704003070b00c0018030b402d81c041c001e280c0441c14070385c0d92004441611582d420140c441003180010055903010b074000b9400d0031483c0c20f01041c1e4200011110045402c112004a81591143c8952207401e0301802034580051325485500840e00d00410094103428061096150000b00040c4d40e1094910500503511001c111041000231802e281d08001e00a11080c05038 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 437736178 1250 437734928 437734931
    0x1707090501080c04050607020d05031201060908010513020303031501090b0f0324030c040f02071506050a0605120f0424060911070c0308091206040515060a0e01031203111606 76
    0x4200c00d80f140400740d90813610010001071814041d9030a12880110406048400d440213024064402c01e40c1060a40606041e1703403409201d40c0751030710303150070b488000c1e140e00308000c0c1c4075040a005d600c020085070390102e00c40a103403408003c1c10004950f00441d641c0b1110b0090004108a043c1c2c0408400950144402c0803400008100071100b078034101d059140324a40c158003500340c01d2124241034002a9820000081c010b0070034072162030754a0014403425074444181c1e0385010500c000d14041e0b0484020300308514026017800e0301100310502003040500440c2c01e003240400001e0410450300e00e81c000756126603034404040485c8030381c084050240782c00b0b0a4151402c000300c0b8146042c03c1e5060b118903640005101b1070705441d54541c0100c0360b0040c54030396000700c803102c010f0b0f00c0800200201406070388640010905c900804c0206802ea507030280c69148103078030170101007141005180300c0c141500d070031641b0155a0f003e2042c040d4001d0500e15880b038440240421042103040041e04061422801400f0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 437737428 1250 437736178 437736181
    0x9012c0910060e10151e0e030105090a03050301030b060a0b0d0f051302060d0e0316050609162418090b0a08160e040203010e03040f030c0b0a080105010f170709050108 73
    0x46180b80c81100d9214801301a60020000903500030340e01005061582808980e0180e0903003a900304141c522464404503546111000389420f0034070a0340c1e40301e002100500f00c212010740d0002c1c070a10040c48040c010006000206240b95111041040103003114443c0959800301c01041c880940300548004015524102c0018a10383c00c142c0b141c10342660040580d803034580740d000361100410301c14a02c9035a0788000d10440c9881c5004080c0448003600840090005103031451084c2c2c500801042680c3d4801001141000304010503003010601d20030f038408900841002034421592f0320f601e420140040c2d07041100000300d5102135070012501c00e10545229141c00c0c0c403044520b1f55084d44408410903401d01d154204105510228600c2e0403d00c01400891001e2141c1c5140385150416004034000e0303140701d941041004248040c40c0014040140d211b81004100d00c0c014006820500c80c0c3c82c1400b600c030044404903481001012140541c41e0070a82c15410302d01c000401c031075081d00600d800b1824560 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 437738678 1250 437737428 437737439
    0x405130c0504180803041a090a110406080309060a05120118050a05040b0a0b030f15180a03020c010302090607240c02010e0616020f030c010504031b0209012c091006 72
    0x3070b02c1003041c18070b40c01c80c005a8aa6844e82a1a44020300a80d10f044848403480c050413600c411143c01041080001c010000c0d00d420710031303214180516020311030b51419004100c801d40100903100400f00480390a43c0340c00801c00142c84a1003010b52000d50b244104001064200546055010b091030440c1c0410540c1c0e50220700704204c90044d507005d05036540840000e071fa40300c915044400f8a280250565602402c0c1c01d20a62400c21004032400781c0084030005c10005406d070300d42c0384d14020120030082c45031001544001e034803800d4840c4014101074001642602c19201c140480d5226640403800744001041411070118514081e40a00304840c1000306a402541c4140211001c0c82c05400103051251500c11071411380c0601c80e49841e0550140c03003801d18203280c00b4400b41008840801c00440c2a25017842e00601d62030118640e4884030b40703500c0121000d130719541c0ca07090550307054800e141f01c10300119100b1145065161180c8111070002d10802941c0304d00407941c10300303850008405018258551 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 437739928 1250 437738678 437738681
    0x50705031314030417060601030507090b0307030506150a020105010501030f200903010e0304060809150103050d08060a090204030302010911090106050a05090607140f0609060606070f0203010b0405130c0504 90
    0x10358200007900108810300300841c5003904021900c2040c9000c50340b4080e9248440054180549250700315a000242008515601409a107503c26540d00d0f202c031040307040600d9109540005400d003c100f550324000110203880c4c8a41f2101240c0e02e0141c0703207448802c40031000740a020700f40102030001c0d080811140c0491054003440e401d1042c419552800111507240c07190f0580c110000c90342d0306640318030011001100c01d000030300151040b90340340a000e2400c9074000e03280001c5454070201507540900108049080810148180e1000d4030b0710075600e171100d4001810340d0744190041c0d1915440000c0c004109601544035021603842291074006101c01401044102c0e2800d01c18000410403c00c5802c8070103118800070803a5180003041141050384030703111510b40c6090480115250390102540206540b400c0040300da1154600703008103414540003000c04ca541c0540d200c000c200380d0a0662030000c6641c2900480d90811003e04200b01c6890455148420b10b44e4240c0c1c00e440c1310013282e0001c80c10741040e = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 437741178 1250 437739928 437739931
    0x170406090c0602010218060705030702040219020106052209020a050a08010e0c040c0e131b20011a010c051219090f06090e090102071406060a05181f081603030305070503 74
    0xe521461b84004c01c0c5500303100300c44c1c0c8001c1003120180020040356005070b841d4405024941c0d000c1030b1400c1e2210841a01030b08640890304900d114800001044204110712003114203080310041003c10542c0c143e00c08074008006e96080380341d00001c041008a4070707034015400410403446200460f412010402c050000300c4940d40700c481c0024a5203103107070b07141d4184020312107100e1014050005003481d0488610f01c2c05410b00d496074001480c04221000c040b9020026a80721814040081050202101c0202988410b20840c0303414004825045414010b05001d40036000b1121003884c4daa50f100f60a5000300101000c01c0040440c586602c049000050200030340c06480c030b00d4840c055980e04020700c0c040720641c0100b5550040d0340030401e01e00001e04415002030306801c0c14005000e241841c1e42000010601504140e010b46103081403e40110a81c03200960407040c2c40312010800c1420368091410700d001500a0210ad204450407840221001c00040f001c90b4043d60302009240c480c10800c8807180300 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 437742428 1250 437741178 437741197
    0x120201170a020c1e0d08100906030503120619140d1515060c0312050c040321030b0312030a05090a050601120c09020306100e01032004030506070c080a0e01170406090c06020102 77
    0x81844950b021750701440d0003982107054214072040d03459443c40307030701e082d640142c10031569500089801e40c2020000310880390032440407a00e0010120b8070b50344849103440c0130701c1200180002c450b18070307100d0707100c000c044a030098000c100b001c1d40581c030300c6080f000b9050724400f00150b00c4840c01d0002d4082d10030110080b52991603501d400991a8049901c0090300000d000c401440c10b04100003c0042c0c200ea6203c00c00400d140140105103084140c06002c03a1040c03034a1a00a800605d4101e10302081c0404072a07020030304200000311303034a0703110300d16181c115a9a001002845480000b14419100d110703c24049480f5500400303626031100740361350130390000362000c0e81c02c42c000c0c4e0801800207006031460b80f40c040c010b140020b0162081e401c51030340d0f0800c0680c03859403404001001e209008050101c2640f01d411800d0800710040c0c2940c1d07094061241a100c18100041160464540d030301c01c0c01544588000c8450714113181c282410860000e000a04080340e0142c002000080c201d070060098400011 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 437743678 1250 437742428 437742433
    0x5030604080a0c020a050d110306060105041208030c07020a030302100b030a0201201501090915020901050301031403070b07170907030203060105060a020c0603040c1e0f120201170a020c1e 82
    0x5418402c1516141c807014800c13030b44603088032008034040c2c881d5548035100c2405106900140d2000c0b0040c9400d01d100a402c15040140400c420f00024882c404c5030ba80103036015075125601d80d00c2c0c6007c040240509900254032020340d50000040c5540000c0400541640440c1080800e000800701591806890002404108a031501e05001c0d180c0b06004407100103c40d00303407101e45041c0ca001c03c14002c2c2c260810400a580e0303001e00810320a50441c0018031003c1e00100310b03e0003203c007001030300c1400140b100600b1000c801e00e100e02490400d00070b030340d04241c0c01074a95403981071075000a0701258824550421502000d4001070001c00c00045503001c880d000b802800c0240d0801c414000580d005d4011407055101d07601302400607485034401544168055010000614105068411502c20742b9981e00d031030100c091028007003a140b0310401130032200c0d81d030b14409141c2c00c5440180d038100d60b4441d0304030729840c140041066010f00e51b0024011030108c001560310000102d01d40b1040020071329000140d56 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 437744928 1250 437743678 437743687
    0x702090a05070e030604032111160206070b010303020c0f03160b1b06130201090b031006030c0c0501021201050a0602190b091c020307060605120a1205210108070503060408 75
    0x20500d078803032a001049072800c2c1c000d01c2000000b00e40381107800d690807000070382000343c082981300c9050000000384c0441041404182640040c0d400342d8000d001c81849413181d4140c40348119510707003040350407490307015802d0782003036a4174100652582c0000c0d14003070165040d102a481e02d441d021890f16000c600c146554551203041505445160300b148103420070b6140001260021a401005018403034003d440c0c1d01800c0c2d0380f00b44001415102198082c01c40b20320180f00b1b02c41c6014411030001c05441840c0b400081e0700001d95400c491100071890054160b5100107075407510641c8000015050b500b099030aa0705907541c4078022655401c001400b611100344a07043c0c0b1001400e00c0c0e0788560040386d020101d4101103511000b0411611895416101584c00046c5042c10001d00d0701504001704002c5070500560711803103c150fa00e90050b0b2800408135141d49401c000c3c414001c0b01502c01d035400012680788080381e8210204904002800303806801c0c8146180020f036450001180b82c4910b500c9054607040 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 437746178 1250 437744928 437744941
    0x105090603161b05010204090c0f021203100f0e04031d01021506060c031204030905030d0e2101110a0201061514030406063308040c0b090103020f160b0c070209 70
    0x1804100c42c41541002242030055841c010140022091580540f000603a11480c2109142c1250503d50b410030600c8101319100c1e244030780200300c140484000f04192035490340c50b030012502440c89901715150341c01e00c054001c210720f58210700e41031007940b081d283c00d151041c41d0b500c0c3c80d0b4002c00e040c0c40180142c1c012800880c40c6480070441517005440a4000307400c100c00c000d491411234025031206214091000104001d142d48a820500280019000344c0054191040c0041c403010124604900604c2c0d01d14082c0d140010b990516400f00a004000b0400c500302c0ca400c48840b544113001a000641c20480b0104801e49001140b500142d01615007080c440081050280c003a00000c00969031150f985a0000b402c4941e6808203010004400c90100d00c2148910306120807043d9408010410203002d08100001c0c0307103e90f240040e154040744c41900c50b409640124081d00c6095264100c06001062800c00380081c9060181c1c00c80c480c06103441560f44003501e5088c0c500401e14041e501c00040307000b0605 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 437747428 1250 437746178 437746201
    0x510020a0c050609030a08040603051905041a06010c06090b19020301080a0f031e0525030206040303051b0d020a02070510020c01180905090c03211806040312020c09060105090603 78
    0x8061010f000c6c0c4500d038219444154658002c0e51002000c203482c2d108200415510002c000a0ba840d070b803604004506190b25401c150b10840301c0c1d007510000c00100410350aa00401044210a034020000d000700d5030340d4500396100c62010b442811003c280e5030f418880322100c0b402034030b06861003900203140703401403a100d0a62301510840164280402d81031a00e088070740f4251000c05440a0b503c50301d5481140c1c1b040d403242d140d101c0b1111000c4003a84850311000a07408190380d5007081d0503160128050700c49001c05060500f524181010032140025000160725898024100c848040d400392507810303956009112090403a200c0310340050300601342c0c1c07202035801040544e10642400e0b160f00c8449450340204d03402c45000743c440c8291544020300d05d2815203010069004000160f407010300600d54201070a2089000e07107050240b008011400120107a112842517800030341d0045018880c40c05c59000180d221203841c88282c2c0a2044900094030950080f0101c0340d80d444040c140b0740ca1692040e45400c2d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 437748678 1250 437747428 437747437
    0x2010207110f06040e010902040f0f05030a060e010209030a050f0f120a260c070b011512020f0f031e13021e03070b0d020409060f050f10020c0d0c0510020a0c0506 71
    0x69201405000c040b03500030400070454042d051f400c400580d101c0c101200d06c0d2092505da44504030590240c10305000320303100886da80c03c82da0303803101c004a001c916402c00d01e40a4000c01d1441d982600c20b841162060080c001541e06e1050280800d540200020a01070717501c40c09111312650816001300b082ea64030300d02c0307210a0340e5058910a0341d0b045407510310120088002060301c6800001c480800e8990a000c0403140881c01420203048848580300240300251000c81c880c2c2612900d01d81c04503500c030340740d0041812589043c031080000f56603460580401006440007440d8421404480e40020740340000ba2071400d285640c0007061041c0008480702510007600719403a6a0b0b40500600c440061101151b002030514801c003000090307150307400c01503103208841d61503200c40d130801c5a0810400003502c0301141805090000c0d80c04486034131582006230300d00030141c902540c1101c007042a100501100c041c0b5241a07507002c942110050454020880c0d4901c0c284001a00005140c50104104d00c1c1c02802003 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 437749928 1250 437748678 437748709
    0x309080c011d0105131212320702120c03041a041a03090c0d0302011e020c151b032205010b1005121f08030f0307020115080309190504090609030305070201020711 71
    0x8485407c96100725070103952a00e1041109445440003100000c101503140483c0c8a40e01c2052030050710b40108001c0d0754051f02c1400e00c040078030005000c00300c0304061046901400340d8056918a49030401c14420346da900612825000b446850000002031482c2c44c222805007281400030881690310300304100c4d180da452003003101950f5070348554800e03a80555821007504400c2500058440608104540c00e01620000c802038440741902004420215199000f042000c0220302c42e48903524003160f18801c0110180e00d418452002215030200b200540002a00881c16a000b61101c00002015100c602034034840400c6d400d00c120008801201e0807855a601d0304c901c0b4560054596100909410741c0d220038442e81c9202e1002040050007502402078118400b05240c00000440ca01607a8544a000b00c44560380700701040040608950b40c0c440b80040034000090040149203160710309003000b0101c001040700401d00701780006200a0040c400c0d03500f010f4001c15000840042807040004100740212103 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 437751178 1250 437749928 437749937
    0x507030308060604180506040c0903050718020f030405031e0a2007051903140f0a060506010e10020114220b09030706090b01142e0309080c011d01051312 67
    0x7140b1041031070045c0450460100041d00c0d04292062105944c81c3c9000482400200d900820004600140d407800721440800d80c080408981c1013080c010303100300c040c852400500441807000740107000c00184103682080c0c45060030000144108219400355980311000f240c41e0f002c40200c112000d8080604d802c0300c8400ba104581d0b10346001a941b00030a4611005d06001d828042c020801c010303580400100c0000003d001d46400a01080e40d42c4090700401005d00c1e80b604085103003640243c0810b85042d000408161201d0b2582c02e00034024000303c400b1070100f12504000c40d401400945003031b506111190680715400741c06c0d445440c218180038104510701c0c8020001200415201c4c17180e02002c0388100c014148551601100c07041c00700d41120064815155680d034240d0f003d000050038420b800ea003020415055521351400e80080c800b120026040c410000741d04000c41c0410f500c10f04505d402c010380380645205882e266400c0300d2048944148104007403517180081048864603044050441c40c0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 437752428 1250 437751178 437751187
    0x14011d0301050a091506050609010f11030d140f040210110c1509011706030606041e0e030d0f0b0303030a0203060d0c081c02030c060c0913060b031006050705070303080606 75
    0x8039003103600894803d2001c503615203500c020000d619195032030160715202c080c0002c0d800c200000700e581c400c0c040f145050040390300340f242d0518003c20706010040f080209480d1030b0a200c03844803010b483d9001102244102c618001980d5108038150381d401243c01030580420300344041c8081d00e895800344a940c8140c49500e5810300c007541d4190040c22540300303a4031902e868850420014200030240c42a0f5488140384208000b466180011aa6400380040741c0c0843c0e01c80c1381c0c028000c07030b420708003e0040000341002541c550500300040100138952060340e04204140c00455940201c0380a8001d142d490b070001c01c04070b441e040082d006980c100303400905900200c0100e58032242103c1d038541c482c02d50b641104c40b400145600881d605005129140051464035002940705d80e2104001419042d1242006c94680741503251103000c2402414088810040940c0328240500745420031501d003407025198042c0400c100c1d2103001a161150391080c0200050b50460380d0590300e07400f00074002c0e60881024807 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 437753678 1250 437752428 437752487
    0x3091208100e01030614010e070509060d110304050f0c0f0114130b0c070609091406090403030e010f05090c040c0203030a1a0d030507031814010309080408070b04080d091401 76
    0x241d4143c0294030807140015111242a106103078060140c3c8032081901000080000d440c0e0010111030007840212000340c0d91321900480800100203503000c2c14000078020082004200c80001c803505001550012034500c1c200b404200b1a50158402d80300e40010314000c0b0040c54145090058140c070401068038800c801d0301c655100c0d0f25a04031541401003079024107006c000860700007a60740058000d984c81404042e200b41c034400c1c10100080d01d2203004020810000301418880d5002000d00c102c00b03402800410101060030010301030944a005007170250034031038000351600e40b11f42c00130740040380c0180d4103540d2002201d01c000c10b050300c0c0d201046180860b25155030760f501c0419031800f40c400c1d101c0700d84801007410024820f07000f104502c0d0049200e113030203000c40703020f901050382c41d14024600800c01e40704503e1302245501a5600003021031181e1400441c00c2c06080c8050804e541440c012200301000e1250219400d4240c0e1003840e03240551482540b085521448111980d1661789680441000420 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 437754928 1250 437753678 437753699
    0xb0f060f16020d1b061103040f0b0a02101107050111460801081902010504090903090801060803030106170f01050d05031c0b010314060901060c2108060406060309120810 74
    0x2113161801200100c0709000b26a000f054091039800308900071401e01c0d04145903184108001e004206004c1008126131004510800c00c0071200c01d00103009010104c0300a00401c0e854000d4202202e46500300b0481c01d42c1415000e055403131604c04040300001f48803a205640b0006205011218400350100412800724022441e845011100c50369410409624002e200307030410385410050440d40144442040150380d124041d9002d5032902c032000980c010144c98141c409a0789944481c00c40e5003405000100040b002c40554100c8103d40c4440e40c0d010b00300700900d40c00c10b4007142d000d40c10610346001032203103050159810700f60074400c1c001ca07480e020141800c1d000421008440180071520b0ba410400705507454003e0800400c1a200303040c0060400d040091000d01050103841f0030880c40d00b0407801404a1100e20020070283c0e901130b020480400c000003403910208440c0a4000c174104000010014480c5c4101c07a19150004c0003c913000035441c408403404e0741c0c0a401d8007042c4210100110341d10707504 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 437756178 1250 437754928 437754953
    0xb2e0801060e1005241324020a08030c041d043e2106070207050a0b1603030b1203030609010b0c06130501151205010624030e01060b04090b0f060f16020d 67
    0x561407003d4030140340c1f401c000510340581c01222017242102207000d02c010b400081229103594403980d10754503655204070000b5a40600c0e4801070394107a0003d44034617450800500320303021741e002c0c220940c2c042c40309001c682038806601d450b2900305458035003612902000b04026030500400100313607039515031040c3e0a44042100c29072540381c040d00500288150190100301c031400502d07056600d28a014541449628680206082150020903070403042040511070b40c44003c102e10020210300e4042508240685ea0303800489082d4061a8500c002255020940c1c068445c0c1c07900c00750050450b960341d000c80800300508480308039070542d00c0380321200704035441c810b002020341011500382a0b603c095007041030a56041e544248a1410b102c824091200b82a5140e11140b0406013404590f02200070300fa01d004107083d40c040306000c0008074000c1000341c165000391071014411140042c520f81170070108481e03882a0001707502c3c00c2d03508000000840c2c815403007880c500d500003016803d115001d0380b03030240503020 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 437757428 1250 437756178 437756197
    0x102031803120414040507110c090c0c03031602190f02060a1119170421140114090d02070609060e04060801090f0b090109050a0b2e0801060e100524 65
    0xa130744208442c2e41017a03c84c4503844585458100c00d404068030700f0035195038a8400c2c99005800000002c3c1010810324200e4648030412400caa9803803509040a00e10385101c521880014002c8141c1604030327104902020804a4201c10821120045030b804c02503035a00941c00340e0244001490030314101401071107900c85810403944d80210100103443e0011540111a0920125080501041c044e1485a002d580700381a03070100358500204450503c46511001c000400d0100e41c00d113080d00c950000400c1e0703030f10f0080710b85004640810805540590726131415020700350000d81417010030004184070300d000c01a182d901a20000c4d0103925001040d003500d40d140c0050b5280100c5c41c00d960200a806407919a201c252403000f08605095030381d4583e1038291401014100d02c44943c04900850700030030340f4490080741c0381461000020081545e4035a80600e104602c0e855280003c00107406101d480340901c00c01c18844040c0e000c500344070401c10f481e607a9a0b41c00c1c030603410a04845c80300c61100c20041c00e0408 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 437758678 1250 437757428 437757449
    0xb2b050706230d09150c090b030c0d05041a0a0c080a020a0f0e04021201080c1801030c030f02130c1224090c0509060406050d06060302070f121e03020301031407030201020318031204 79
    0x5a02140071f02410541d5008001105c0308004210608241800762407095130f8000c0042010b071a2401d0040045d044244921001206081480706840007688400e0264002e5103811050b81e992501e20f004900900d14403d0105280304184800c0e9448cc041c02114072000420050500724012820414040241c000036103550100c5040a01c500c1c1103020b0318558a40501c44000d81c0d03040d075952841c1e105040c84010286495881d18030115503600d000d01030145110740003040b00c5011a20010185c10800c01c0d010140340c03414030702c44401d10168512060941080c3c20101c0d40710f141840480c001e00c1590540701c1085001e00039040c442da5000000d000401e516581c094441880c0400b5204882442e0b00c080c0074988104410400150305038030040f07260313030008602032078403544940039580d0444c0700c018043c1d042d071a000c981d00c035290954043d5060728080c0940342d04070400c4408655130f4006500020b400341e4000d03c820b03001e081610b19061080e840250541d0900000c0000111140d00550040103004 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 437759928 1250 437758678 437758691
    0xf12050c1b01050a0b0a0b0a0302030c071e030e0306070c110d060e060115030603170d140702160f06090e180613030e01140d0b2b050706230d0915 64
    0x4c500ca80030320400039808035030481060b49003c52500b560700c2640f480b0703014540c01000084020040c80141c403011900660b00229046c3e40100204c03d003d00340350110302041509007640744c02c0c1000a141c030720514145d10740135654040340c1c403000f120000c50004254440f03104140d5000040c1e49000c1d0b50203d00841008103e9941032078030300900680f00c140d07404105440c0c5035003040400d030141040c0190320f2010000c01d03510b0064100080c050000506002c4005800c94140801154001001c3c141c05400009010b1300c0f944030711106040d200e19219a00008241000901c4091070030701182d60441a030b072130710440390487c0703602c0581008030072207880008000444d01c1405054011103640340f500d40901c0c1c41145403c000d50310300180d0040c11075007041c03c1d50312b4424020304c0d1200086c905051813840300c0d00440e0f1440d4401c11405040d003040448281c000e002c40092200e0080c19614102480001c10302804920700190190b10307040036240800d016101d84050000c07910031008110280c82040c40490705 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 437761178 1250 437759928 437759941
    0x219091d010e03180d0218061e0604090203070215010816081f0e0304090501170d0c030e0910030b04061b020c06070f02041d0105040201030c0f12050c1b0105 69
    0x1054080c044031a92a414010b00c25001d100101c1201c1480c0614051348400c0442100403c1040150005c020741241580402c0714010945841140c80783c0c10466030b40d00da15034941212003462054400c4903420050500c400d016100c0381382c019551014491040341d980380500d51840051180a0707101205a41041d1a1002102d0a0000ad140038180ca00000e004041da41c82c00c1c1c072014907080c0900c0380c1441d034550510080600600440f8020041c11809200c2961103010b40d00f0300704814030010041d80f04212861002c14003810810850580580340c0800c100034400c18403480d64802062400b00c00340c664400300024602140c00d030700550040d00300140c429025010a00e8400703003d0301d01030175980010000380d030f940e42e0001100c80980d8480051000090644041405480118501e8210b480c2070b190062040f1415400b29100b54001da07420701511300000c0040d25414032041281d0700042c003002d0001330850807504040e07080401012114541131030501101484071814162034010394545050050 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 437762428 1250 437761178 437761211
    0x4031b080d320601090b0a1107150503150a09020403110108060306060f010c050709050112030201140f011205120f0a030615090612021903020306210309010c021909 72
    0x181c15064010566211188220100b14540e90301e00c55244044100081d00b07a481060a040104a6800300940320050b0100c0036100001050200c166071045882c0003c102a0b45c1c1d03980d00c2400b2040d11041e2640d00c03641d00e8079203404203404116421007241c0784000392040841c40140000c5001c2c0d14117040005621000520704031015100622a90107042030140c20703654441640b1031a0024202401200200d1030300038180f90403641b14400301450f2800006607900d0301c08900301042e102c3d9008200b2a805010320081c0c5440c291450703003d146c4610018003c41d08402001e20f131042c000c0b42105c1084580d2041c82400b540070555500d00008045031060007640c0500401003d80b00c9040302032010400800300a1034148103209100030031000c040014034074580780d0304884442c0f000d8030000381100e00100000e130181d40305440a0f80140010804421070503954003111a050403210090751505a0000044070b1441d20311500742e80c442d8a191000e0034107a8001c851100034484400d01190b20081c1c07004140 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 437763678 1250 437762428 437762441
    0x70c021806060d0c030b09041b0b030c0f070311071e090b030a03081f080109120e0f040e01140a061a1c051b030906180c150304031b080d 60
    0x550618040c00d028956550006503003d9945401000884011911045014000c00118070390401e1039203003480144800090003220142400004554107581e80a07000c615101c2180d0090f20f548003440085c0403001540d0090004600901e010302040052052490400c86035900600081080c4401c034010324803041c3c40b400003082a403004100c9a0150382c0820b40f04d12950000400304514200064180b802051100c441041d614581012142d141e451040c002c141c601c205a40b03d8140889200010f0320801e415107045401802a08034003c5600030310024210300c0c8480f1055540301d10704103244140d0341381d42a2050802e820049074080c0380500421400c110a90460007140f000c0000d004400442d520080300c001c10044005002d075110496001070070800075a0340031111000003032081c800380c0040d0103801001c0c0d961050608505113945070350755226201030075801005c02ca0b44410b4020403400a158060f019040c44036441560100466030540e852400300c3c0c142d03402241203caa00f00354444c0a = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 437764928 1250 437763678 437763709
    0x102010f0c0e19030c090902030114040312090501060b070c0509011e030b19180b16021506060906070c0f050103090c090f0e1e06090120030703090b070c02 68
    0x1c022088200324010407448070b81d80814040c0e4400c201c49030450f0001c008800c0150b030040200e424040d102d16041e00900004001a8441e600304000010045a200c950314065a4142c907102e210802403240000a06110042500c080d5642e200c00200c2078500b81c0100601131040d400141658240320801540c058103030080036080c0e42d14814041140d440112000503640c012102800b20b07034a5014143d907000c400041d0800d081c0c00c050781e03c05100010b03030b6001c0c040343c4140740c2825540d0359045164442c44400040c500180e20158010681040000c0581d030001000307080540f40c4201d40000c40d065a106810451301c04044841c01c010100e0000315040141c0300901e402d00a0300d186407680030071541903001c0c0c2900d030343e903c0180b80602182ca501400702545901e054414081410058a00c1100c085c035440b1403601540f000600005010701c07600b10000791410843c0b282144900703011445030402030054081c9640d444800c00071800c140821031240e5015619541160a00c1c41400744440c0b640b44d00 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 437766178 1250 437764928 437764931
    0x230a0807080606120712030905030f0d0210020705010608030316080a020a120b010e0d0c050301060b13141305040c09061d06010e0103020909130b090607090510090305031303020102010f 81
    0x344809200403406540248007128030408583c0f02004c001e00b05441684803e10084400ca000020113400c1229002103030401c03820307940c0d046402e600045d2030700d401c3c0320110300580104a20b061175840c2030703010300340da0340c0680f00000d03900d629460b1075440c40d4402e94400c000c0b042010f40e401c00095101c03081d0756006082080a5041035545840500001450705116880c152600416030341c0e40d2040c0100740016600904088070b0250600b00a00b00d540c0c0350244c1c6010b9400d000e004601401120100c0b40c14814102c1144005403a0241403103100880701002c591002c40c0503040200050700d80219070046003d1307009420207929100c0c42c50210750196200c03000c0410b0140b006019507008a440d40c1c2c1c0000c00b070038086110101e01004070000e22030041c0e0366034001c150302e0610094005510250303401d58400d20010031341d5140d0206441e540d08088410500041f03011a00f4482303800d00d002d11365040055800e0201c460380c1c8980d64a401d6411079006900b040f141c80504000399030b4240500c21012020700700 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 437767428 1250 437766178 437766193
    0xc03180f0601360e0c010c11060f0405030d0806040c0c08031609080307080d0c111906020904060801240b0906070507031209090f0515090a06230a08 65
    0x7600e40105119581003180100c6903800c540c54500e105500348a07102c421040b05112600e511802045915901e444a103d2881000d400c0c0d40182c01c5070030700030b400803415031200401c182080035239030040540700d018200c00c1c0000541c2d03031410400d4584542c2c45442e0569245405000c3c070040f24800b000300350805c4405032041c0c0100c0c55940c100c076080201e0300030340d030303044400302c1005d8407030640c598061078403407000140303000500040b50042c0c074145800c41818400c410100c4070480300302d14034042414464002042822a0000c514021581320340f04071400341c10001842c000408660565006c1d503556515105990000359503503114103014010300b000c07130505070b0408400b000d650161548542c0501750000d1a201804010003152008644c0541c602104c44041c21000345a15031610403145c50604140c03412101c10141d0141a11408400e203076528503100c154208044250045c20f94001a50f98a0020404002141500e040d03d800320617400b950104200c14030030000815032040c1c00d5500240c8 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 437768678 1250 437767428 437767453
    0xe030f030c03041103030c0f070806010f051e0d140c040908041215050412080106020a080304030f03090f200a030c06140d060e040210032f0702090c0318 67
    0x101681e4000214405250316030380c03640340880340f241c03a00f61074550500c80030030341d11142c0200085da1002c1c225184141c03584140d4640d2100c0d40d0700428000d6081e850740041c010300c0720781001c20101c0111522181c465a00d911040d01194055001d100e0966400c80703c0d2090030b100500c20800c1c41500407058804014498098850420030f000318010340d20003c0e050b01c0500e06000c100f1594007092445188104501d041c00e262007035084166540d01804100310710000505d050010a00b842016000410b2902c2d40d0750781c0d54112203038055924400700749075a5804c00f80110700c032174010628a40c400c1c203600c0c111f000c0000c602403002c002010058401c0c1700281c02440000c3c408000882200c2c00c0b030504501540d006082c0070f405000d034000e01c00f030030340c9400c2001a44001030342d105400b9078002ea54091503c6a040d40840c26200402d08400c005061031900e04000248041d585004256210340d1500381007440c1e00080450500b079a000d880c210020040c42849142450000c2d003041080001b0002010f260 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 437769784 1106 437768678 437768707
    0x1003060605010203070b01060302030613020a121d0a1401111206010801150e01120b0406090b0a090c0f030905010b1824220905060106120e03 62
    0x1403002403254008000c9660310f40e003111010805a08100b4280c0180d48007801f0f15400000b8038101c8084c407100c91020300003548141d650203c881203160300b1f0b101603e0300d04094105280d031440c800314411400040c0c010740d255000c80582d4400080780d491600404000f520382e08031100010706117030340d04805400203105600980794400180d807100c000c80d007884081c0e590600803c0241e40a094a580107404620803041c020b5004034840301c0d4000402c050720a55030101e805151100b80d00041803401c900710380040c100e4848108010300d00064000c003a591542020401d040d52a0052000c0c04000c0d0007050002070f01401900041c00280b035840180b110440d101503420902209102881002d2914483c4210b402406c29204040158001c06640711240c00700214540c1c82030001300049091207407070300805080e15510392009200103074000307a4030010320150f0150030401540341d003920035 = true := by decide +kernel

theorem cover : BRFrame.Cov 437589928 437769784 := by
  have h0 := BRFrame.cov_init 437589928
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437589928 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 437589928 ≤ n) (h2 : n < 437769784) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
