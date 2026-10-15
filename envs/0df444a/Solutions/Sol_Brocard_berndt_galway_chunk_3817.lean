-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3817
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:46:13.599754+00:00
-- url     : https://prove2.me/submissions/c85fce72-a5d6-4844-b738-dca75f1d2f94

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 686330935 ≤ n < 686510791 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 686332185 1250 686330935 686330951
    0x312080a050c0307023c0615042306010504030237061205041e050a060f05070e06030613020c0c01090b0a0c0213141303120501180e07180606020609030715 68
    0x1246d001c3d481c0034000d034601c00201c1200c182c201e00000303810380318200400c422414200c4103810300003901c80da04039862030148009003000345a409019190351104044c90001d060030b50300e0b000903000e034070703640b2001800e441c000940c0e42c2c40d00441180202c01c407110a408021840ca00200142100039890040046540d50404281002005d846032051000c0a640506160b071070b60601c2602d82041302022a0715902e0011a02d401640c1070103a548900310a881d84203c040b040020302849500003400a03600c07c2c56203520248010341c603c05010b011580d000209607000340e03840090080d5002c0e4109000d146420300c50300c8259584031201011155040d0741c080e102014143d0748038060141020060f1001d120041080203802481450900b400d000350344e480d01c0c0060101c19001210028081d103a4922060009684c2015543d040414850010000c031901c85995090380707000524006a0309260584403a020800f00d90304002007a0050600c3d00614a40300341a0380301c00140d02c69441c0c00c030140b6150054 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 686333435 1250 686332185 686332243
    0x60a15050f0405030f030c06100312030507021c080115081902130f060503220b0a02130305070b090316140d0206071203140c070503030613060312080a050c030702 71
    0xb541c1c001c10024045412030301c209403003961280c10080074403840d445900e000503c106601240842101d4000310601390002600d001200a00002031a880c19481848040700312418249080721402c0200c3da5240c1055051202000700b007210b4103191010001c00c10306105042e01c000300c0500b140c0c401164010399610300140c03940d100c0b20480e80450b052176160300e0300080c0c80e508100210f218411502d2121010b0303100303e503070801743c01c40400b0103400141c2042c0000c01008103940180220801244503401a965a6031038a00d499080d40004500110100d8078030741e80c2c1000c110391640da8402d66540c00501c1d0030640a0703400c10b0400314032280315164081444055481e22011101d61981008a2442e14040e00202038081c04040310844181c0710386000040500d0248401c0e00c07005a03001c0065861510345404006900100900b444119552208000005a01c00020203403140039a10340007654a004410b80c806c48400400c9090030b00130410030403000582c049008000740c0d040742c04124076a403400740 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 686334685 1250 686333435 686333437
    0x306180b1501020c030d020105070201060504060311010e120d0302070203060c0309060c0d1b0e0a060318151103040b040b0a060311191a0903240412021203040305040509060a15050f 79
    0x24050b0f0507006a806d036407103450f81904110721440c03040d002842403d941c1c00038001250401e1202400000040700320400d5980b01d841d00691050004000f102c0040e0001c1ca05800c00d0429114403003c02d90014a84007142018020140d2109035000f29504501d000780d201601c1744c0d001442c41c00607181c00501e40321200b0743c03580007808a8031545201d1600943c0030320003030b101c1205d01402c28030400840b41c0000b4000e209021301c500012418030302281c6e80c1c040350303502c2d0403e0514032500e0030b0b40384d160b5440341748040c43c40000c2c42c882c5002e04480d0486081a007081d00105401030140090281810020b00c0410020486240f2540e8140c0300c03403207000e400304419004a0341ea6000301d82c03400c00c40d1103441c0d0504100c401402d4114001c0b0309441e40c50203500e00301074a41640500c0e01324814404000030700420103d42e403100311010b49005a6031403201004501c070b081c1d80b040703408401003100441c0500960400003509079108400740c410440803401c0150400c14140e90b00120350030820001188100480080 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 686335935 1250 686334685 686334703
    0x41215020d06320d030e03030307050a09081209220e0d2007260102040308030406050c09010210020a0e06131d130f0804031a010306180b150102 63
    0x8101103445048901120000d0802c43c851070310300d802400401c0240c0c00540302010300031142800514800390301d4405218000030007032819414014080199403540c0c9003800150310411040c2e4030b4031703039600c100c00018050308903035000505240e0240840c00d507503031010000c4030408030302104c020851900022002d000d03080741c2945400490b00b090316a0300302000010300b17100041850346646155001c0b0181c4c0380311452904c5801c04159205941c02c110120402d0317560358400f6401c1040b101c0b0700d15885071f290f007a68040d500071148000c1c00410030081c820588030781c5030000c5090743d05500e0300c0c1890000075135820728541d1022485500140c802c0c0a1400741d5234612030000040c2c601501c803e006e06a403641114036209a068004402c3c0e80b2580e00000c00c0343d00c44c440c8044185018140c04103488000142003490720880d12140101710100100340886190502e440103044031403415811441c1500030344801c041c02c207180c05d007005080390010f032010003807031384c8500c00415910002c0ca4400c0100e140c00c9030f00c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 686337185 1250 686335935 686335973
    0xa060f0914060703270b0406061a09011b0b0703050c130b091c0f0b04240209030d0f0e0616140f1b01090e0702010b031e19080412 57
    0x100140c60740c0600400c520384036181a440030030502c1c80c850901420b11068140e15072642e102c0340242800180c1200400b42c000f80148800a5170395100e0f800049001d10f500300c20740000d01c020400410b1036902c07580e44420a05605807040c2041e2081d03440b10700c4454003400b1401416140c90005645418a030143c902510102040c07038552507880310a0840c582c4000001405164076140b00c40c0c200d4141c00c001d16019034040c030442d411428944401d4101031003c3c208540d20300241105e00e1203003900846a07602d403c0c070f44c0401079030b40040da4201072900030744000c03c0040c80b0700d01000c01c150341d400c180e041499031380c00c0d0f400c0741c0e90302404499002628010070000709a204805618850743c1c400040411144196008980e0456000705c06503503c55545500a0700140c9444011f001110801680c0e070b40001701c0340004599031540740300003420880f811103900e40f01404079003181d605440802c00000380c2e091103009191000b5294881e00390601c12070054003141c18540084008110300c41070003a40304011 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 686338435 1250 686337185 686337203
    0xf0501050a0e0a0b0406030b04090f02090411030111270619030e010501090204050a080106081e0a0b04030f0e06071a07050706060e1b031519090203010b0d05180a060f09 74
    0x11000d11103c4d40e0401d0203004000303403074801c1001540c2441d11030188010307000340801044c08101d508020180c80014011604280598000c504c140c800340210b26001420380905512884000c5550400107a448a2105090302c21403160310300d44c880c10211000340725801c107102e101d1006035100307501501446803501d00c0e0350701c0c2c00d0000030034004540c00307042698801c5038034005166590340c200c4c0c203903501801540429003203007521904080c0504820324842c180354003030720341d950050f131110324040b01c04880540c0410320a68a88081581c070001d001c0e00e1640481d0708a0030801c49d500c1c0c00c0400c40422060400d40048030002c00c41150180c401e682440e58018020301209403110102e1140803410b40c2d10801d00482900103013400b290b0141a203104401804441c048d00c4c0d0400100072280c103aa480d540c170301d0445c1202c04240c509045c0001c2d4013074100324004e2642c42d030301e84801d0780807140020858070f00c11240d00805200341d40c01180180300036401000c0400c0d40641310054500600e0705402c02007030401 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 686339685 1250 686338435 686338439
    0x15030a020f030a06080c090c1206040609020a110106060c0308040f1b03050d17010303120b060408250b0a02100213050a120b0c04300803041a0603070f0501050a0e0a 72
    0x40759130495030590701c102c800e170390000d03584006020b060801501d48e00138101040c4803040381e4601840c10745900000090000c9843c0c2d607540d207100e040340c0c0140100300000340003a8500380c0101090103043d0040c080751030308090b160342d00d0324000d240c00c1002e8002040020384c103070b8040501461750260f023082c4910070003040d8030345d42e240b41190303803034a07030b4407070310000c150b81e2000d1151403a01c10010078100c0790181c650095100400d10114010710881106560040c0d09100114902d8070400c40a215000e2010300080582c03141c40280c00c0480540e030000d504075008110031002140c0c0440c035005d969102c0d0201588400c4211184e01160f203080d081640c102c11000400030b508015220101000350240700f0840003501c50410035a9141304c0c078007401d00d903008414003003030921481c1584c00c003030403068040700c0c07200414594840145620544043d1810702e01c49540c40400000d14110b9030f0040c1c0200c004100c8940780c20b0a01f1b880c00d10f14800c643c1803280c0441c0364032039103010340c8048a000c100100f03070a00350340e = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 686340935 1250 686339685 686339701
    0x3050a0e0d2610060c0201020f0601090f05010509060d080309011e06031203060303020316030504030f050304030212061003200a0305061f030b0105060a05040905040602120f0615030a020f03 83
    0x91001205110314450001c0411140d072502e10345004a00e10360180c0748850900b002900c48000310f079004c03411480707501c904ca100844103000383c80c0a48a414000706491502e400030400791141070300814811000c8605102d0341e5a1200c02008401e0380c003100702030701c07541d8018020340140b91880303603848982c0004900303619280580d403011081c1c91055501c1c41040074074000441c125a0180030007000b59008100b4020b2200f01722000d0100c4c0c41c42860302601d0542c60390345880602c550400c08890903800403405008500d80303580c9050300640890024601407030150301c3c1540401c07181c48042e0098070a41044203c0400000045850b844054204900035036a80752090b9030b200b003110740030000064040c0700d80209040c000c00b581181c0d00a209800180d003400c0c200109944070072010418801d042000042c48900341c0642c0d841680281001030311031000c07007002501d1600c0140902800015881000b0680c0c1e42c6400d100402c903e24060715849540d4424110f00034814824003465000001c01000004 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 686342185 1250 686340935 686340947
    0x30f04080f1602100c050a03110102040504151419050904080c061501090501020703080d11070c0f0f0b0903060f0a0e03130510050708040909020310050406090314180103050a0e0d 78
    0x207100b50b03051561034061300400c6500d070b0b80f42c1800602d5078001c02600313004603204030039800c071a41c048000113240c0f0359148005004c4407403581c103a01d034207218040c0070010000e8060450691000a66081c407a0000e000c04032985008a0700545101e49454070101d414410f440092707841070302180c0102d9409040842c00000d41c084180c0140b0b00050303070424086015480800d000701201e502c5440d05090005030100340014040c80101050860000d20950010803100d0407c140203006800100180f0380c1010300540440c1e9894101c8410a1820000d14140791000600654803502d801c03103030b00041e15460900d0000c0d026092081d02d041c480400c041d015549084121412501c04a07000c0b03001031103411050b41c0302d0042900290403011b0a0008104190080d0071290000344014140c43c50040744103d031004445041e6000d07600f0a46d1041d68104058000e0111042c15030000b52a9090800d01f00c10b003821070343c408908504060f12200401e142440c0c0d900603803000305442d0155401503c8100d4002e01c2c2d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 686343435 1250 686342185 686342227
    0x1603121e0c0b06011d062104030c0b06010503040f0210020c040204151209051c0c0807080d1a280f06030c021006210812010f150e0303030f04080f 64
    0x2030582a0b000c40c2c101e40c002c83c49000d41e0210b4031800c00d040c5c1841c4040110f0b90300800e01100709090403140c0324440d0392542c00d020f803145210762586518804103003852100f111004000c103060103800c100f40000300d01800340c8082800c0d03046441c001007240e03014080b07081ca1411032596800500106000c101041b00b1001440c11950903582d94030300c440ca150b1072000703859140e0005442d03a002982545001071805080f110105010304000c880c00c40c0c00c4e40d51500b0340e4071004e410340310314a001ca00c010000c40140900d0110300c060520200400c440c1070005041008a2840c00d0010540c3c0c001100501208401c002c004041c401e1444000b107640300006400391100e40248c50050280000001c1e040d80184078031010f681e12146000d003101048002001c00e0103880360240d40b0b4001c1032044a070b8800c000307600d0a019000003412010813910300005114032050668042c0d0601443d410030340d155450000a40b607001c14018440c2e4002d0700c442c18038492901c1008800034460200003404000c0d900c9803680380390 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 686344685 1250 686343435 686343443
    0x30f050a0c020c03070513020f12040f06050609070207060e04110c0a020f24030604021611090a060b0d09030e1807170106051e041d09010e1603121e0c 66
    0x540070701c00c103042548403405c074080c20740c0c00f200343c0560800d40700e525409412517080e174500040c60142d142281c0058102d0441d001c980320020f004201e002c0008034003d068000074140c5590049090610019445000c603000300c208100c090000301415039585d0b08283c420440003042241d070f6800202c10381d81c80f00e4207840305034010f28804101110a04084021402070303074020b034561807840049000070490350700c0038200690042c1c09016681095182001401d40c99102e003142d401910701440a000c40214000c0a4038009850300c842000030b4164031089924880a49000041446840ca000ea800a00c20301c00242c0096a03103e040f24013101007000503000e0711040d00c0b05403034101981898200120240a8800020020310081d010544641d4a1590007001d9914040c00c2540340e5005072510921821203403014402c1105012000b80203100b07412402d6401005410042078010074082d40007402e1100500340c040001c940711505101c4e50302080300400d0ba042010402e95405801480b40c4000d4100f91 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 686345935 1250 686344685 686344693
    0xf090d032a061a10050307050d050a0b041407090306090f1406240a061209080a02010207230a0f06110a0504091b1202130e0f070207060201090c0312030f050a0c02 71
    0x9039a4140e0003020740f81651000306203070b0910008030411141c942001d8000c100340309091000c5613048500e4040c262107010545000a801c0c1c0c110401c0105803501c041450360321068500c10b00081690200d003080a880d08880040b500d24054944941031805054000d0503001342048050801d58003c00c1082c010400c10078000d000c0c81c01070301c405030143c0f12121080d41c003030950402080268041c01410f00d548100c2c2100003a0500c80e9110300101c0d900030429100140d41c00100802000780314080c0000032068403180c51800080d00c40b50317503a10154660043c1112400600180070040b4a400c08902032144502860302c0314501f81018101d81c10038014044841d0410045141c000d640d9860801c503617845036541c141c1110390020940c001d501c00d0141c1d42c11548905400305400090b0384006020300c9060440300d02a1401c4040242049180c0c0c01400441e41001a00008500220102c1e030503250010350043d15080d90704801c1d002414036609082106007041d08101403001180e104003148400d5409503 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 686347185 1250 686345935 686345951
    0x3040318080c031f15030c1508040506040308090a12081504200f04030203030c15010f0b0708180d050c0901150518060c0a0c08120f090d032a06 63
    0x10640702d01c142070b815600356102845405030f0840c0060020109220b0300e80014045801034002d02c0b1200281c0c10596001f240c003001041703a0810016202e4110f2850314100c80942080d54440340c0302c200251014080160a20201b40c844030240101c05040382d20103220b02c03140040b0840a00660400c848100c07802c0b2603281000168102402994038481d007000c1c07001090803090f42442401c1d0424461254109001d110110040c1c07000c10041c103114444000a1443c1e04c0d07044e0b4082c1c13002d4016044204c12903a8141d04000d140ea0000540c1c000300e0f4010400c42e11106481107480300c00410b4a50b169000d151050b034001070103008501c460800713005944d0b519081c1c3c2c9505c44030341c04420f0f046642d000603008120081da01e408022080e04400d200800d82d41c68a1745103001c03580381410740780341070300c501400c42401c00480c10304006c0d1140c1104645507040c10041040510103a0f03001e8101054001d82001d29120100340c0310382e29084045000911403060000c1c0302c0d4420003030410034103040302c015140c4240 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 686348435 1250 686347185 686347199
    0xd0906032711040f0618060807060f0e1c02040e070f032a0e220c050607020a08030c10140108060601050c0718090201081b0301090b0d0803040318 64
    0x2004910071410206203a803400c8000c407801d10003100c030019a11001140144001070b80c0302c0c0102030029500304000700e101801c0001000e511414506903004442c98500200044140031950034100c03522810a603021a15510058403860030f0603000d658403a0001803004101c20a40340c440b00c3d01d038000e0302d01b040502d240c07a03511591010240500644017480c20010400910715995580744220100044104000e425220b10100005a01f050600c4081c5000700150640c1001905411414014032550007192503140d118401402e400380c10f0165034006001e0096445480c0b540340140003080460766101213141d0180d84408032004682c004030f0910b42c0e04189050103c20f0302d41601d82060203032883d42c030b6070001500d44d0b41c0039050600742ca001e80040054400f01c3c958032010124803105020502454602c001850860002c1c0302c81d0700c00c416900301c2102d480710801a81d0642d101c00000180c1000c0890008291504c0b0b1a401414080004104420550b000c84880051400c40c444011800d4503418 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 686349685 1250 686348435 686348441
    0x905100b0906060d0b0405070903120c1a0c0705060a02040609050405040c1403150f0709090c080403180e040602070204230402011b052d0d05121b03090d090603 70
    0x40103548107100d000418420724143c0020304240d43c5030000000c840701c800003c54141e610844030b0f040031030000072040040c0049290020341030b003104c3c038140d01284803540c0e031087c0c03406071140030410710504000019101d004030b804071810182c0240442e9840d140440f0000d01943c080c0c000c0000144840344000303014107050060500842e0301c1504880b0090a207005451811720803188180d0512440340342030031000d20800084d00070a005200e03a541e9140000002d0440c104952000c03900c14641400c4140c1c43d98011030441d0000c0e4145010b0000302801c4c40c6240440350543c0090f541840c00800344401c01c5055402010740c0ca10a50b014803088000c07451750800892104102d03994400150b002a0043d8841c0086d02c8080b2142c10300601da900060721410320706182400c070240e090031400c00c5056840180c0401c03071260201c02e0010000c4000680b0020150301403107100e040c20410703d1010602c1540a00c107003000208030a00126102c0c035104c07450982d5040556038060100d00307921008120300d4801c0c0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 686350935 1250 686349685 686349701
    0x90e070806041514070507030e0a061e120c02010213050306010305060411040f053303031c020f071a09150f100b0c0c0f03030406081b0d0c03090510 65
    0x101405059403640c43d83c0980102c0400da00101e1990384114599030103c0811a60141010f59a5541c4400c220b14000e810b201003070580e0380c42240048010000c6540c40980c0b44840c420f650004070303204501410a68001c0c44243e00118820b0515680c4115a45d055001d80203080c6280744184170a5951000e158680e0000c0c00007406c9904074400040200f85201d10920005801801c0020a2260888910100d03001035602c003e9140c0940b0103040040c140410b41541c00079600e0780c0c0541d1901a0300001c1d80d0344104050a00e6013a620000c030a0880f10300c0d4183c0b07400d40610010035076222554034116030403140000c01a05144030b21408035000e180d000540e103c003039540c0c0e20400032549410285035680b48000b044499102440003021900e61100e0000d003100030b8122000308610751000080001042841030010300a6000344410403945e03034000e00880d0032805980008581e0064440b600c0a684194600d4607c0c1c01d08103240c800c00e0320307410341c840300c5024041c800f40c410441d404181c00741943c00038 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 686352185 1250 686350935 686350949
    0x30c0907030905160b120c0403050304140103050a0c0f0e0604051008042a0306020d0e1506030f03031909050f030f04090624080601030603060e0c120f0a0f030c1407090e07 75
    0x1400803d11407146c40d240075070825803c406103030420b5036070342e1510300e5507110b1b03017000410151084030075915507014001d05411248209050210010844e40144491010b07170503002000340740d14610495441d120200d402a00300603203030b02d100794800200074200c114252000c0381c2e00004400c80d04814281034117230f13056030400510f403045498034640320000a900b01039800004190340f00742072601034004100c002c4a0840c0d1078086580c5141000416040a424819840a42e0010010404022682c10030b030810b5034411280051003d0003414068508005c80305000e0701031100090705c4420b2069100607004954001409001803516559118090101d90340305074644181000d825101e58000c6c14031541c05003061600040480d0340741c82c1c10f001c0e41d000e0990007005801c007041d64003660038030810b40307020708400400420840c0c1001c1c0c8030680c0c8c6c07048202d01420b00c84100410604141c0708142800c0b0359078004e4152400810100c40450301c0b18113522510401c03034500840352601c2600800e124040f650b003 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 686353435 1250 686352185 686352187
    0x607050127030c0f02180702010c18180504081e180f010f080403051c09060506030136081210051c06050c0904021c060501051303020f030c0907030905160b 68
    0x143d90b550705041c00d00c440c0200c1e8800714400070341115042015440b4441c40d9103074000b090041005001030509030348000102541c60402e07a040c4088038a00c144210440802c5200090039a140e08105200d03000307a41041488071900d01101e03000055103000b0f021000d00105008101220702030403c200080090500303030102d04498081c469950144143d0350303006d8000d0420b1803600e4028240a441d45c5840807042d0703010750b540c0200d2070a0250074407403c1d030b028609900800012050080d68000006c10006c0001c4200609903401000409404c03110140c40e4010260b0782c513002c0c8015071000180d0211840c50b13a03113006940000d85850080b034058903009110310705814110513a11582c01900c00203001c0c4107282c504100079203d03901d4034801012240402600c5502c0d0b591100c0000703045e10703100d5024a040100c00d2000c000040e62801c000c1040303e50440341200c8030381e400e401007801c00d2140e6403015440141501044170740c0e901504080501403007807080e00c0550130f9280490610310380b20301071035441c0d00d0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 686354685 1250 686353435 686353457
    0xc0801090b0430020d020f01020a0c02060708090904030c0b0a0902330301030605040309060f09060e030c0d0b01050f040e2812021005090a170d0b060705012703 70
    0x498448500041e0303c800e40c0e040c1418000303030001a0302803068611006911820140c030702260b0602c1203034044180171000354948041c07420018460706078048041e201e00e40c0042c0a0302000302040441e0403000700940701552610303141c00c024081c021712400940c2d0314400c52b00010401d00540c81022a05540282440916201d080001e580543c244401c2090007002d440030941d030000540c0a1070095200c1c6a000c00d15240074500101b0242c0e40d0b80c8007406003c007401c0701050b034a4000d00f181e01918018900340c1c03819410000068a00080e52440c140c22418000010080c0880c0c880d03082e06075041590090300d0803074800d0910049070b009010713034541600302540d000d4000390310b2840402d22403032013503030713080e041c005519418404644030b0031007400361307124016640e007100203070042c075a024400c00041e00240c1107a44803c00900c03800040c69490900016009580514a501c4243c0c00344003e882e1b0b40d01c3e101c0ca454003a0007403840394401880e02c040c0c924803070800710b489543c1048190340741c3d0b5110041c071 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 686355935 1250 686354685 686354693
    0x1a031003110312041203030b012610050d030c11032103040c03170d0c11030a080a0204170c030115120b0603010f0e011508070f0b07020d021c0c0801090b04 68
    0x1803a01c00c68194180500d80d000d036103c100c0300c07020704017030421500f49101d000d101380b4000d001c540e646000c41d8103000586100d49234000200d002100a482080d0844400c2d03070700c0b06900d031032100c41034001c0c0340e22400c1074003420280340d400814030022500c1a00145414035092080542c0c6141e002c4420031039040040818a80c189828080c6411902c07400360345407459129680c4410050604104900396803000c1001c108800c0d041c01550303100c200038140503181c003020b030800d25240d00c42c0c0f8144c982070004440101d5180a20360b4102c0d001408020002c5c0e085d6034200010544070302c800221248290f080c00411408201c0200c80780301164800e0440f256651440d59442d0302081c0c004200b20380c103551311242c510b0303400c0260161064040d40100005018103000d1500002118241c0003403126500c184070500003811340e0041031003903e848000302900ea10003440002c90b20500580c0003500081c0740c400c96029034407a0490202d03800d22844001100d80d803a41040f508945020401421410015001c0f070081 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 686357185 1250 686355935 686355953
    0x1080f03160f0b0c03100e010506070803070e09090102040305010b2e0203071b15020d020c150f0c010225050d0c150e0322030507060e060c01050901061a031003 70
    0xa00e200391500c5240d50029110f00d401e5400449011340307500000020820400d081c01d0122005e042c04100303042d259414030f00803400b18012548001c111800c00004505014011445008080c9000780300c0880c0d4580200054007035002444122a02e60903d10102042c4c68494401070b1440f040c1107800000351140103580400d68134000e081c3d01980010002c10703000c00d951000502900b19040c0d0002c40c007901d40815012414000c00446045400c032205860b60b1769800304506148030b1007103c0c40250750409108540307040c444c003d0b51030318a403c0010900302d070b4141900602021031010361a0128810300240588020215120060050300f00e003102804040c0522407002c110b500031506140b1103642e103a0b046046810582e0340e00b040703038000718076040c911f0728020b44c01c503c03c0440a01c8100107459a5501c560720949070042c42c050101820410b181503e595040d101d01074180c2d030081c85981007501005000301001d001d000c541c844c042e88610b0801a25004490040d400940e91549141c60b5490300c2c0d00b1 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 686358435 1250 686357185 686357227
    0x50c030604091410060303090608070c110f0306040c051008010f03170906121f05060f0c0f07060e24030a09170a0302130f0e01030b10171501080f03 65
    0x100d010b0144000d40601c0c41000307139020340b04c24660001a02c03402c50070042c0402c48181d10a10810550384c0400c102c4540c0700a19800482d4800591094140c0480c001031040917144203140d0144240810401405141441c56080756030503101f10005045030f25007115404401d005110410404440c208001503801d0050284150540e544604114000d030000b030041d404841c0c440c0ca48602c140c00d00c9003951010b21f02d01500c9070030b041803489080c60301d4003054042c000e0622040408501140200c803a081c01d1012000032911401a2807043c0c0d01e941000e0007000e260b10205010f440c003402d84aa19000310b00840c641c219000041d54215541d004221001d041c0d0301c50304550000d000b00e0090651840d0b0809864061140d84016803109808424041040c001d540402d000545c03030442000104001150710741541c0e0008048100303559003070301d115204081640100d00b01c0a510740d10b00e0759400d01280c00e521201c0741840001450f680d40c14040ea0301e044482031059250420802c04203a24548803c0d841 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 686359685 1250 686358435 686358443
    0x4021012090f0302010c02011d07140f12030d1a1323281808030c04080703080c010c09030507050105131805310303050c0903070305100f050c03060409 66
    0x7030032940030354600300c4a400c00c12088025030344410300c42159540a00030795209407031154144040c1c1030004d64440d0348981c1881840c12160064007110699240d5a4900d00041c0000c4d04034030040041e800c030a9542d500c083d002e151940d00d411a0b08001080c80c0818030350040f03004152401030090350045200400011140180d824850500448868107240b04184a410081d07030034405682c5003075003001038500308058000424a0b001241c14280c000040c0001426000b007041503d0350364009000009101e10382086c00d103481204030000401940100500c07c0c1200600244490289108140c80c0c0400a000c010655000440280a2544075001801615030a100507807a4941d0b01c1592007120704140b607140003929200d0b000c02c54050480801080030b040240d256501c422680c1c0080740e03030b80d0004e40008040549800c041802c00400d40300740c9008510003019900c0c03455885c030b80250341c2c00040b50710000090401c2d05801400540e841520310502688001900e15991070081100801c0d00d507404a07 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 686360935 1250 686359685 686359691
    0x15150a0902180907031d0f07170a15050610170402040203130804150e010503010609230303120a0b0a26010207050a2603060f0d02120312040b0f04021012 67
    0x603a43c11100e1406140103460002e003840365400d11644402200030343e0aa03d0b441030503101c05109000403d070007224101022041c40340d00c003030452800c1000c039480103411080740c2c2d000d0b07403400d103200e0340302e83d010304c80466840035150340c8a00107580c7c84900911442140b002000050050f0600760004c60307103d10b81104e0340c803082c3c02c0c541d80c041081d003140d000008010703e406010303c642c40d0003441907001040c0900b8164210741c0b41c02d10050001c0c03038a001c0d041d1544005c150080d002c1049042942d032404000703090381d403242c08504184807540c0341151481c41907401d003200c0b0512828072403040425183d03501501914500791503880002c42d4007589959007159820001080461b000b0701c6220801880b901c02c0b4501400d001191a011421031080140c0c910020014040c0541c0e0703440b0001100ca0058610040349041800024250031494003182624007002031900f0f42c0c010501d080720b20480c4114141c0c401911791203000c1011070001c4400039040002c078010369035094001c41d503c0158905002c404 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 686362185 1250 686360935 686360977
    0x409060209120601091a0d1218090e013210170f010b010203090904021c1401020405120304050d03081305010f140603010e100c03140915150a0902 64
    0x42240c242911100b40301c0341e0070800040c41001c0300742c02480181c034541030104000750304140008540d144810001056189a1103c1c04403041c00313103000340c4841c0251420800a02e0f83c8041400150002c03580d1080654a4004031903041c41b0540b00021b0301c0034804e0080a5055680000390611040c0a40300c0bc0307004600080c0004c0d001c0b589019144210490b6025011f221400c10b403542c2074400e00354103103040d90014030052240740c85080c0820f03441074040702c1e6008503048007205120241000d800142900321200c040041450054004004030b03034003522a1110a44001c00180e180c1c0500d0265036800711060450902003849021040d4111100c80c1010440d916656900e80c212807440c02400c4a0689400003404520208400950304c01300a070700a009000b03620842d1900c40200b0400c2d444020f940704110381c19144240c0c444104a0b46842c40c240c0281404c00c1c06070b075582c0300c2c2c0c41650040d200d15400100503030b40103100d030740c0101c101400c1412207a04140000b8003075046116640f00b0780c039500c240 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 686363435 1250 686362185 686362189
    0x6090c0203070b010902070b150117090601051002070f14060d0e0c1305090717190c150f05031506070615030209010f050607260f0c07051c020409060209 67
    0x608041610150001c554031a62441c10503190b8405070320280f903c07841032100802042078000c0403030f44080c260070420445014440182c464040f00d0301800c2d881c504500070001030b4100001c1d034a05070303881103c054a498007485d40c100d07500d050602404880001d400400c010708a101b60701801d0220009000318201400025200c085508503a012501e1340d0004a00410600b00b6030030010031a00c1040c400c2c001440d00d0341d100c59032040c840c42500c10480703032003480ca05a500c060025100d810410780040c40b400c5990308003644e4114050183ca0345058803200107594490160444d040d0756021902e0b01821996038000181e8001d80804d0100e401240400850740021664440d541103c15100f030041c407500e0860041c842c4498050700300c00d0310001d0885d0b0901c000c3d690842581c2500fa446006400345140c8068400d00051107a00450170021001c99600440c6003c08041c103100c00800045400e015501e0080140c40d00802c110b502c1107610190503000503080c50b4011884150082034050b10b06521040 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 686364685 1250 686363435 686363441
    0xc05030a0207051f0f0f05040b0c010501181815140a021c05071710090903120f050c030f0711031b0705030d05030c07062018150d0b03010609 62
    0x410100140c0002509100030b181c10504c14510304034070011551400c90406014142d02000e4420b002401707440c03070612684a10540845000d000c5200c030301d80d112200d07251024003921080c0940c00301c00c25071089052401c06540300b40032401d0100b00307003410300042c1c43d11808603040014031100403481d1a1000c0b13400b400040c42520780201d00c0301c280181e40701c291000246da40303030074043d9042100b81000140711700742c1ea01c5901c00029aaa08548c1600d82e1a404038000c0d407a0b01c00ea0220b1003460401141c9401d05800405054619002840c24050407114460342e00032100121800d00110105001242c0300c8010042d03e25404912420001d4200d002004401e246410030404032162210500b44515120f00900c00400280b900390000d1071986104040032704030b4000281850400700000c40c8400c1400125003241e64035001400860980700240c001c881196401394168100030b526040d42403090341081c86041d28078000d500310035414a40c41411001c0609000c0c0a07440c1e244d0b490309408666151144 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 686365935 1250 686364685 686364697
    0x1602090a0222031e0c0603180204060e0f09010207080a030e010b15090a1e05040b0d1b1418060927010f060b0c03040b030709170c0102060a0b0319030c0503 68
    0x10b01004000c0d00c1c503e0000c02c115000040003545002c2803040f9800a0b08941c40b005c1a64010300703021a00da0b03000c11042c00c0404079043e001e90300605241c4000351701c8840b0b0300e0450103a6840401031035a076075103125070703420703481407140c000d0611070100204840e85120780e01041801403000f00200d0444400d00001c3c00402000c1e40e4480181c000080d003203058540200104014251151200c4010340303aa011140403110501c5494000d50329410700c41c1060303a0709030b1200c0d41d0582c0082d4140b010790304004114440740450003890000d03111040e8010b030300c3c5040755224a0b10204070f0302c40b400039601d00041c0036144030040c080c8440b080352100020800080c03c0c4064594803a40030000a0312a400043e441c00c3e09d08646c0040e605070010403513030b101e001c4088215019242e00007215a0741e512218400c8507800c0d520741c860b145400d0600d9842c3c40010340441c088100e070800b682102c80036114154458111a02882610f9040c3d0094034801000940b1009556900303000b4101154440e070319856080c03d5502003 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 686367185 1250 686365935 686365987
    0x3090f0d2907020a03020c06090a0b0406030626060411041b11010b1206010303030e150a0207031403010f090b28150e100e0409080f070b0c1602090a02 66
    0x441c0e08041503800744607100754885074070700c02401042c0007500c0103074443c2da14040d0345000b00000039407094562980070a1800800d40e0039140365a440d030302d000c01402030180e4083c00c0d035480d40c00b8080b03008240d01e14000c43d1620403d94060300341768481b5528580340241c0e111a4a4205031205801783e4101c0081403004003c00440d21140c50b040c945005250849162a42080c071541e4480c40e0310614090008480e4152641401e0002e212201c10164618040c80c90003d1319580c0d40500802149841940180640a121b6140d107804144030740e09224040c00309010b102900c68200500704030703101ca25041a10740e09405002c198512051414504c44c180a000b202102c03c2c100b50780c200881c050b0340c0450030148100349032081402203040000b0303c00d2910b00c1070103010001100201c41240c0c1c0e481d4080d056055111048941d10901200c2a0150340c10941003034501400440c00159100c10303c008407031048040c8400c0d01c00c0f540c010750800c0030300c00c409050004a81d500f07100481c214a104d203032801e000004 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 686368435 1250 686367185 686367233
    0x20408071d0103030f1412040309090c091401031a0a091b140a05030702150f10050114040b2505070f1401021c1b20060c03090f0d 57
    0x504104401001c1d540c40200a4010020010808680d11141000401d4558a070400c1c44199107000040350b8010a0741c80b03000618040103010815030070808003c100c42445c042404080031105095401e03141c2e0b4400c1c2103a130b45092050103a9036100f0303400219861003080b040342d401c00400300801d00c010110703080004802e030b40303024103e484000c2201046010100e854000401c0380e01e2510000c181c051418440300b8044044040f90800f40280408128014000c81c220100c1c40d100f147c81e441032b01c0c1965980b072100030031000441c1c9944145c48000301688078a02051a1618200d40d01103158803a56210b0f001c196504800304112041c0032021083c01e0042000300503141c14154203001c982141c0c0d00c0b540c3d14a40c0514410140c1c2d0300415503407035080602800023040b0510603030650f40c0c6940c06401c840c0310803941c001017080110340b0180c2200c260700a60148015030310b5505002071031040b45004c45d0750b98018131500c107540c900854864981d540c080c10700810400795944444c01d03400700c140c0e800c3c08485 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 686369685 1250 686368435 686368439
    0x3060e0a0e01061211041505060c1506011701030f21030c0201140106080402090612030c0a060b10120203151c03030b040216060911060c0d23030a150902040807 70
    0x502409650301070400d40002041c112034075918000c1d040000c0010314051615103503d1f9200366418002c4500401000c0c0c0f040e651441c074002004d488000b41008410302a1515010540ca54403500440b406034214031640d414030b03400d584440011007082ca00884540848007580346104070a403200d101c10780311030345001c034802c80820006802d44014004100407541510300402a0039400541c56802c03540590708003000f40c43d10800310301040f044050081c642c2c4000984000d400d600000c0c00106640114001c001001e8100100b02551240510340390009800c10703000007800c0035507030003542c210103141c0790752041d07401960120310790041c9142003a003035200016203102819054010707000028000c0310118507004284010814610060034040d2250f5a224003c004021040a07880000a001040d0755100c07040340b481c0c0c41d9110100300e4120002a070603507e0741c12014000704120204150600c455041da030720644420010881d680306010408a504400541c2c1101e510050024100306006844114 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 686370935 1250 686369685 686369711
    0xd06060503090d1e0f020a0206040f0306113105090709060e090c0d0906061805041a040f0308040312060902041703040515031b0c010b011202070c050f0103060e0a 71
    0x2107894000405210300700844402610201c01c4c0c14010324201c5c104501c04e8841900124580720515034029000341c0001000f0941131440703403030402100d2250700c05006001044928088501401a40480c9114200c0c41031260310384043c1050043c14014007070849542e03448000440102050341c8000103d204d01000b4840c00d50301c0035481c2d0a85034140da81d1040703030030040e1000249110700780d07241c1d840366580c00c0008100300c0320341c10a03c010004c0443c0c48000c1498400114000c03d0151821544110b600d9140500882002001c2d84201c1d0441029001c001998030141e40ca1a0000c104504108003148000d40007280e034030861000d40700c5000010b07142da0402d130061404c4c84664001c100c7c2540281301c200720b19502c102001e41d61415282340b90b6182d0b190340c0e40701d81c40300c3c004014030640c3c8000880c141c002000c0c150700c6010125000d03070310503402460314003a1900324401c84101422040c45681e082c011400c0c10310b071011100c00103141c0000d2041c2d642250803480c181c1925126001515140314850740 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 686372185 1250 686370935 686370943
    0x120103152901030e031210150206040b0604020d0e101a01050708190201020702130c09090b0d020d050c04020c0606030c01050a170c04031a1015140f0d0606050309 71
    0x103091020401c45044610100c401c0071114a460550304164482025452071034003802950748141d090807040340d82e8140040c2c0c51000050354001d0140340f070741380591480050300c0044d500d806590800040340705070f00c0300403e01004c0c2d0701903004000166112040313200480000c200d010505100010001000b04100c2d05000741e2440f00d04255040001c284840d00c04160040b0450b81c194616440321005008200c00990180c012642d020758002d001c1c0d900d84444150941021811040039560480d81d0303601c0b034510004a414843c0c40c0ca0b003004255507590014244504103040c04d50042c1308486c03a002c924400181030303034070080358600340d90000ca080c0700300d500701003185150515090a0080c108020340070300030800810000001c40394031a920114200100c000b04580207507401c445031110700c80c4c240240c0c0b022914241d815040c2081e10340c600050706109a44070706a14151640c58041165510341110400d41000100d03061049042000c0d070f81104051081c2c030010201c036141ea51304e903c1c092101d5030030 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 686373435 1250 686372185 686372201
    0x7020604030b090d020d1202030603010603050303010f0f080303040c060c051513020a1706040b040311030301090501180b0f041109031902010f0309050a080f0d0c051b1203011a12010315 81
    0x940d44801806905a90412200d24001240400049c2c50b56110b00000380174185540c4044d02d14080000003050701c00c048a9200c0503141c40d6401d065a940d43c452000d65603110441e00a00f00f0f0f01c9503107080c400380f03225003c1d2048940c01001100d07519003018203000000502078804045040c0541204021401c0551000b00104200180c000c400840904103a468620080006000c4c44940f0001002c050140700307100c482c0259070b01103a84a61310340c501c00e4018030003806039480445034200c0c0701c040b1258034040c0620024014040c0e1465400c000240b03c040d101c001c1001000307007400d10051009803001c00101036100403001c01820182e10700d00000d8005461216020304050901074560041200090306002c001e0f40007440550390a11894850464094511518065801e1405030480f00e1750081c00740c5a648045580d200060035048842540c61001c010550b01d9003030f0505c0104407420b5029040d040ba6006a071002d481d245035006c613085510000d8008881c007030b1210940b0000a8018401e10207 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 686374685 1250 686373435 686373437
    0x408010609020f12070504090203150a080309032e090f0c06050c03090f010e040216030207060908190206070f061a0a05180a06172109010801060e0607020604030b090d 73
    0x4030b0f00c2d842208040091044404603001c0300116408100954424021600140341c00388085480e418410450300e030b04000701022600c13682603280c010840e0030002c811140c1c0200b008000313103c1c500c2c0c000341c0c1c02d51603415240004030032000b4007070501c0c0700500c500640c445036200d00c0100030111450b150007607a203a429002030041000a024441c2051030000480f2014841140c00c2410441c5400040b610008002c142c40d401178000f1407141d03601241c84119442d060b210f5002d40701d01c0c6894000031a5820403030b226041003940120303030340c118044c0c128400024050000c3c1005181c441541c0f24160000741500c011108982c7e540b81643d034041d41190180039800c0201e402044182c0750000041c12480103141d2012140741e40004150204074542c4810002d040110300d540d125820810318544030b40b51005641045c03101301c002c01d82519218411542ca0b103c05850343c00d12039090000844412000f10074807900300c0010042c140150b95440081c0c8000c600c201010080ca01d4170b502c809081c840d40c03035100f070 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 686375935 1250 686374685 686374687
    0xd080103170a1d0f120303160e01021e160816051905090a0f050a0905011410060f17191a0102030f090d150203061207061e050d11040801060902 63
    0x464410340c04000c1c00d00c03400c0681d480343e1009044500007400010400201640002a00c0488240c00c40120145204070541c440134614190b1040c029507016005100c0346d0f0042e0000340410001d06241c0c16520590390180049605240b1009081840b40700d1a170860312081d4071003840c2200c50a0390801e024098134003aa64400f0b40f2045424070301224900b40101c6104802c0c6000003400300f0324542c020202c07400d541c0d034180800d0601c40040c20003131110075010b03185942070030081ea886a01c9828500d001c0e00740720b41c058484510b8000e044170354a05071403140c010000301c072a640c0004998441b5540c02060b80100690440c10f21124980488460865416800308400e0007074490343c2c0c012013940d061101c940041c6503a9280c00c00060408908800010290914001c2d41c0507032119a9000c6c0d841040207403403004aa19880c0d0070300341e0310082072040e0030000d8030f081143d86200c140010b418480c3c0081b03040c03603810300100c210b40d90b05940310500f035040841c0c008a000c0101080c01d02400c80200307404c41c011 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 686377185 1250 686375935 686375947
    0x7031806140d0b0d020a090c0f05030c0708160c0e1504050405071701140901090308090604120c060f091103010f330b0d0e0d080c07060507110d08010317 67
    0x742010300606451121055071914212115201c0d134202c9807210740d0050942c0c503042d458280010041c580d000b64680001c4001000c0340307020380284101d1717020782d45c02c401c103604003031310359403180043d50160300c0c5005c0c0e03444001c00e01400107440300c03084005030900340b1808a01e40340c02540c10500c4910814070511550400c42800085040410310f841600e0f01003a40c10f45440d0a180c032207000d000c118406501030074580042204814066110703800d1544699903110680e140d024005603510401e83e0080c2250811051241c0071340d01820700041c20b2842048042440c0500001700700466542000a44814107045034440c0c0515080c803d0146092130742000300a1a114507100502e0b1203c1c0001800c1001083c000d0303050000c01c05041000103086100b0070f1075480082009020103085824400e1040f44641c801e0060414000c21400c0c0c417810600103154104a81d0f515070320701902016103500203000d41d608140034403a07014401d480c5c50303129035102c04440d0351452400c00030894040800300e440784028000 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 686378435 1250 686377185 686377217
    0x51b03041b050d03020304140105070203070b2802060a052a0309011d211e070204090c1e0f060c0b04050316120f081005060c100207031806 61
    0x25240c0180e005410307603081003034000200209200a4106550003250746890904141d4004014400d68070742e01000050140b0030401942c19004802d00258590803002e000c1c40201990741c041d0040d9408070040707085051041e500c01c0300c401d410055401c0140c0100b410050414001c0c094581c22000500400300440c150f104001a4201545010b080b500c20010100707803d0b8209400030712003903000c540741c1c01804112000030365440d00c07182a85200c0010310b00303403400b240103000e06032500d41218001300441011503542d042040d90050004176030041c0e5500d040c0000c43e05c2290480041d20340030113170b060010407440310229440010b40c0f00000e9502070314024007000340d12610b00c09035654000c18242094540b89002400c6008119500d0040f40c050900b880034420202040e05034a00182c03036842d48030019000c101c81c0d004040703559095910140500300541e00b02200184141d01000003030f10001c403d00006001a03a0090b081500019001103080d069200c03500b02c014014055418080e03004140b8001c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 686379685 1250 686378435 686378437
    0x2e09080c01030216020a091b050a0504090b0319111c0f03030b0a120309050909011815020c0a06051509010819020a0312080708070e0d080a02070e0f0604051b 69
    0x206541003580100d48640c084044004400c866517005001c0b034402a16052a4001003d100c89201c1840002207050701e00640150100c070300c00d028a55590b4507290038002d01c40040e0518440c4030750584922140842c00303000d0740303490035001c6115600c41101c540d940400c1011072400c462175032000d03c0141d00000001103081140c04012a854140800c02210510014800181c02e9002e240d00040756148642010303070250418040d20000c84103001107883d0780c4c90081c22140d1050100e0031106000c4055004241c0d8801d80c2030200308040005071074000c0d1010700d1820308003695030440701251103605014140300401c1038021592000c0d2016100c941c90b11000e65030b2104401a80b04203403c417400e0450a540780c94045c0d602840d0042120310010305c641f032000b820010b0880b850f400154070b200210f01d4640c8128101c031010040141540131660007512000450342c000d070360440030362244603000956190480781c00c91003154141785140b440d203800303800c0c00b081d41c400030100e203a00302d0200741f0320b001890160 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 686380935 1250 686379685 686379703
    0x509061e0409030c0f0602040602120405031b2d0a0812030a0e0c060a08041406010b1b07050d2913080c0c040e0a06110310180207022e0908 61
    0x100c0128000340340f414107075802040c900b0081c02c21000c95600a00740314031500140211125a42100c160f1894100b660615024030701685505410214004440750810294a5490100107007070380c0ca10240f04103019030a0b0003282481e1004030b000d0b40c0050301450035058400041c00c00707102600d41c0705020214001c141c840141328041650f924001100c1c14602041a600910301c007a211580c4d4502907070b009000184c0c1124212803440d0200d1074a440c0c2140401c115048a014008480c00c103801080181c1c1c00d50b8031070300807010900c80c4410001d29540d8030b0901d223601a000380d08803415502c1260340e050207508c814682e001d40c100000244100703030f10045e030b8004203d90040701c10768451500315202400d02040e4114254068180b07000c0b0080e00318041130807000305210750800c00c1500000c62034800180012220801d05000d48081009007100501c010590b100640d04014034080c0d80d90b001400714100703050030000300000181d80490039058441c2001542c01c1a080a99696141404c0030350342d51240 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 686382185 1250 686380935 686380939
    0x90f09020708091009030507030b0f1308040b0d0e0601030c1502030a0f03020c0c03012901020111071e0803280b1021180501180503181f090509061e 65
    0x1213041000034440c800500103154040207075403882d692800d100f260707041d003502c00c070070b20001183c003081010400038840c8603d150b1000c0902d04040c54008965002d4104506c100d54281c0c8a000c01c00d9008001d000c40e0740698815650b0621885c01d00d01141115252602c0420541d803042001d503001c1c9400400b03801e1845440d1801607594921441d60a042100110b811601036090050078503a203454554902101c1070940b540e100860480307001282078501e09003803a000a042000104045021000382103c00400d070745891068001c0c0f5607600240c2d5000703c0380e9414010946461078034002e00303c9606c0480c13605104003407200140c4c2200090460003240002003d104525a844220314014074003180b0400b0480c100304480011600c1d0011a400d2404003241c0652801d003260104410040301c1880480e0410025824902c2d640220044020354035101c03581f166000314001c880c1c1c00520301900207031215580d611a43d40c40c0100340140e00b603025021038483d103007089030000c9501132024560304550007 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 686383435 1250 686382185 686382199
    0x2040b0333190b0a080405010f4a0d02060601080108061906050a08010f0c020d1d1309030c030f080112060203100506071b1e052e090f0902070809 64
    0xd85030000ea101c0034a82c4000d14030040440c0740880340741c200c180c040c4641d003d08000d114450700b98000c1d40444581d480c0504000e4400c1070010140b5104440d03c0d190308642cac90f80180155980642400302d40c0d000c1780da00d081a4000405080c100c0d90510020307401010a080c400010f50401d60783ca510f030403004204400901041000c160340160680040000b00000b40c0740310340003610780c14040d0203000c81d900340c000c11074180202c0c090058400110a905800d40303640c1c52034038a500c019100785003103c2d0155030741e0000b410000c2c110084c4007840341e40135407071007a1075200100d40b45103005006c60843e42c130f254050010b02c070300400c81401c05656040034168400320040e9a595014060b40304ca0403240c11490b0032103400b081040801c1411210010807010034240c21016a03521b80712100c07110752440441889140c040402c01a1f030410526490040040c980708003d41d900c80c1c041349000f400d540c1d8904001a0a03072100300501402d203075450010701401035055244c00019168004c86114030840c00d030140003 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 686384685 1250 686383435 686383459
    0x1060b0a0c151b03061a0906070807020a0b1207080c0a0e03070e0f10090b0f010e01020312162c01200109030801090b010507021003110d02040b0333 65
    0x8901d04a071440100070b42c00f00441505810b40ba801c2003503c2e4a41d50210340740150204002c5140244401881e5041804c00c0c42c0440540a1200c80d411004045800d05014840c0c9001640c48022805c090868200724544444401c8a12020a0b002900c2d15003804594070520446107030340c1049075002c031110304051000d400c5c05c1000c02c3c83d00100f58000e5003032070030000900041e00b402040d603e020b110211160403010392140000c00071100c0803c6c1d070b1540400b18522040c5603502807046110000c44c140152410010610025201c201044030117141c80954010f0b003003620b40d00556907045500c4411070740984844000c1c81c204440450112240c18070002105420038001e000201801180c200d82c000d00c8a28400d20380034104400a00840592509100011690354468400d4034201a0010800c0038803404014003a0001d002c2100800200c0300108200c01103130b901400103100501c3d4540003195a80303070070700140380e0700c10a0075442c1084054050011000440541038120008001c850b4080c0c580 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 686385935 1250 686384685 686384693
    0xc0a170c070305031201061106071d04050405010f15050901051302070218091b090a0e190305040e0a0b0d061121060906090c1e0702121b0301060b0a0c 66
    0x8020340324100368900c2208000720801601002901c03d15034550320340861a601e81d2030a440c4405c00f003010742c0c03850307100000040480d4890702110151181c1d0192400b80384442e5070108065460072142540c440e07448d2000a5807488651149002e800c1200410081785030030b15002890014061241d103101308041c0544100409260341103134007251340101400e20507080c9001d405030003082200d03c1049400340301c1134071031800f910404990902200500540459896500c0400200307840082070350036118000c0c400c0202c5580686e00d00b1014007039115641c84d0391421041714481c120041618250500b807180c000701c1c0713842d00240d0400c1c20340d0100d0040b880100000c40b600c07141c01000c17400d6803105010090318a40c0301c03001242130b0092509581d03091140d50742c41d06001148506848058485e00304100180c803012515183e0341d1908170340d503031180c500003c540000d09070354540360b80f1140d1900480380d142020045c070115030441c1c000c15030080c040c0514000c2d82030114000c1c0c452080a2011001e044070401c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 686387185 1250 686385935 686385937
    0x601140f1207170a0501030213090c181e150e070c020d06060602150c041e051206011809020a050127060e1003201303060501290c0a17 59
    0x40c0c070105040186a140009004202d000c400c400585000c43d401c2c04542d5601c2e03503000b00c078141c0350090501c601402005405074020071003034800359a801080c41c00414160942403081c2400d032056071002c02e007041c0d00300340e0301c2d680351146994640c69403504c0c84030318400c4010080f1604440c0c000135166a03503a200c4171705584e80210908025403001c113554a240c00c02019500c1282680c01503402c94003001589440680c0ca04400e440752558284140020829110940500d4502c1d0300d170b0744200c045040d9a00c01164406011f40080c005a07080680140180d107403a03100c10020214140c1c05101c1401d00e6000b00b181e245803400780030b04118071a8100131130b04030b4103803d42074900148551112901e591762401403e29540900303040c4522002240c1d101000d101c0e0150780c8801580a0616880d41c0007852503107120703031001852a000000030100040032034854400e881c0280304207007511114420b26401c41504004011141a442e00103100d418205140041d170f0f903001c00d50200c82501c42d03040c000e400c0507032 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 686388435 1250 686387185 686387197
    0x50906060111101104060f0215040212030405060c0106031b030f0803130503160b100806010b070f020910030c0509151002070803040603020405120712032a08130e0601140f 75
    0x1c91802d050a528040180c54020006c540c03655031480000002080c0072030700d64020300d035a191502d04660209026241202c00c2105910561003181c0c0381540d541c012841d190403c14800c1120b03503588804000780301581000740324044042c0d0f00d0010300c078219078842c110b0b40c000c414040c01c1002c001c000103070b15056450740400c107039400404494844030b1901c40402c0000c0c45d10802c4034520b0904001c549400c5185c1c0b07040c019603680201803c641d80c209415500990001002551907400c030004d0f04000d0f0305d034a50400e001e0042042c0415005043d42080d1490000560240d4001c0b503075682045020010031944102880040300c119000040c082ca0480c64000640c0040005002c00030300000d11a1b0160b0003001111000e550012006911040c5c03d40c586045200c1d107204056540384900001c0c3c070030391001e01c000300c0f001c4054100002440d001c3e2402c41d40d2080c110345648001070580040e9040031491002002c0c0100001c4261030801e00003020781070344001440c0c4c02c02021a0343c2c0385904d0b204059642d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 686389685 1250 686388435 686388463
    0x1f050918070e13151a060304020301090209010305070f0b03040807030e1f0215161707110d05180a03260c06070504150302030c1c0b030f0309040e01050906060111 71
    0x580741c00c003403486030160520010101c84130108285030380c8107108503002d1030300750000d809004185008040b0900025900052089900d55a0781e14600c00580d03800440c80e01a501805c0213104072400c0481e05c6215060700c0c0c00c0703c0d01181003442008006101e031801c4034903059061a154248180520101e0a0001000a00c10a0040702c54104051a900003282040303442e1140d41c0d011079031200c403800a030002c0804e03403007400200004203103881d0f507250b1100150041d1562400b4061940385440090a1050b0300307a024000401c0011015a50b03d02492007404070402220b1601010785180e40e1003a01200c00d44801624800e03041c0415400d55101d01900c03032203201d04041c0c0c0e1417407402c100020a1680540180102c4229020030301c190544a8400d6038420502c00e40302c80e24201c0c1001035480000c814110f10404980c4441d011b05003524140301d400d40341c5885400450300d1700c2c104010002905c0a00303c046843c0da14000401c0600040090001d801c11000e0030881540c681c2409250304254210351444 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 686390935 1250 686389685 686389709
    0x50609130f0e0c0607020a1511010f0b0a050906100305070e0d06060e1006090b09061c0f2009040207110a08030a0338010207090908031f05091807 64
    0x1224180858202e400742c441000d0907504000c0488040222a001d8010045d4209108000511030051000e8040c084c13030b4401c0c1400220302521582440c251400413030000000e903142c0c1c500c4280c0341040b81c01040980401c482d01c40072807a00d00c001c80d00035441198541c0c01c02d03403200040340d4560b0250800c0340310902c01800040700c084030f904150002d45424445d500451600c80001004a41c08880c1841501d1241d5110740c4071a01e03048101c00c180d0004e0101503404642040030455002c1d03540c2d03405000d00010400450110a03580399601103a841c04024000c0c606c0d964110400400e140d02140c4030001d08a90050725090304d8103007a80c561505015881d00120001c4000c0b54840000019024070b01866170203010f24121705203260503074503030b42c8100301c00356140380802c03035200b200c02c030410ba82e200040c811503803a55a5142650300380c401140b815030301c0c0c0785c0006c00e0200020140f0751144144d40250700d40d00000386031401091f40400010025079032040d0381c812440444c0c8042c00034a0060805140078 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 686392185 1250 686390935 686390951
    0x10609140f01140d14060411190e0603240303090112090606080d0c110a050d020105030405010e0d090501140a05040618030210030c1d01050f1308031b060a05060a05060913 75
    0x1038401000e08100381035285c0d00180009031113250078060340c10700300e100f074030103070706040ca03041d03011300d181c0014086c580c180240c8610542060b1100006540300c0c100c544441c902d603041c0d4817481903604182d6a801ca009400402400003566004040400d0b60000341000262031400b9040003402000c00ea0001102c42c01800700042e845940110100070b080d00554411041c03404902c1002034816507445481c3d0045000c8020720b02644c09500615441402a0004220454546000c505060201c0c0074807003c00c0303000d0310a201d07550784000c1c51a4000700d518002c515100035810050301c1400740d84961010001c1122607045401690925500159030180080d81c01011400000d005404110070328400148041083c008041007070140344200c90060b11940c0c0b0f401e082c032002d809998000030b60303413100c81c2a0100c0040d6060040006000002ca06c2c40030ba050490408809030030040040c0502c00704a040c00c0030b1203c641e44031403e0b1402c0740c0d403c66110750b85031840e5000c603c81c0038500c40e401e58000d245c00c0748 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 686393435 1250 686392185 686392207
    0x9091303052a030a03060612050919150606210e07050d14010e01020d3209012c0d080903030c070c030206031311010c080f030703180c0e010609140f0114 67
    0x4940240c90300b90308c0d02640300f10100389101c04c40c2c0c02102c0d0521140c2c06038030f03a490304403c8041e001e2811400b80800d00c3e4005500d400d03081c159040f691218001450460408910200d0440c075411000700141c405d001c1021034048844d0342c0d174214042c1900c03d007203880c8060100301160b1000c6030359401580090000701071040c0424000e4200d0351003a0071a50070150b68084c1f030361a11542d000801640c900c100c030007503920700d40d00000b010001c00c8500c0a41d41c4070070490b5007641490b03443e8860317408090507600350301c3d194100c40d04000e2200c140b4010b010b000c074180001c1500100a5940c002c1903400cae40c075151507081c20140341e480940c0d0f1003c1e400110000034001c807218032491030724400c1d00420000384011580b90044507048242e52024088810502009104a28000086411010500d8046120900c807c0c0d44502d95003031100884d000d203003c3c1410424522203d200700c1c0180300b50b05068494a152002302c0441d80000c8004034401c5041002e04c00090380110442c2d03072030882c0d501419840d805c03800c007 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 686394685 1250 686393435 686393441
    0x20a090302040e071214010c0504060c0f08040b07050c0301110403020904080a1202041509050907050a0e0409080c0a03030507021906021b0f0c0f031b06030907051509091303052a030a03 81
    0x1010303250365403c3c141590105805102141c00315a48cd5131801661001910b03841c0070f1001c1100103c415100400002643d603c84502801c0081c2c0a07a015100781d10300c2008250865801013240403609000f8001000503139228000c41d03a2081e00180e03c1d0360384c0e01101c14112040b0308400c01328a031107840400d0215500104003c880e1707002c1260f4503100c420300d403076100308050310700c2c2240d000b000240201300400049110b00790039008160050000304028100340e42e1400c03581c02490035131060b50b010101a10600d0380c9401481d4004c4158009404101e02459201d000c50410070070181c0003c0d00001d01440700032a40180034031003150001601c80d540b0f240d6645030303125038012004900c2165002c455814600d0007288441e10704a40066014940c0d007010240000d903040141640b1803801401000a003a031548048201d840460b02c140c5a41c42c3c94150804c0418040509444420462109110000f075048000c950034201c3c01460703044500124541d0b40c0c100b0001c001d01102a000c04900c028410390107030 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 686395935 1250 686394685 686394713
    0x11b0905010f030e06070c03020c030f061e07020304050d050f12031603050f042402161703040512030604110705161512050a1d0d080a020a090302040e0712 68
    0x10741e410110555802c0124107481d80e55015180d80d400400110b8150382c0101107540000348240150f600c1c15100000003820000700380440c00258111004100c002d00040501110038014800489403506004400a55078000e0b1300406010f0107240d04000140f08003003105407402a000802ca03000f402c017090380000c09070029101491003000c0848904281d038002d0045c1407160300301d210702d4207284c3d40c0c03a1904540240c0c010503051903501221107070741b0a80e0190000340103150b800b00000208669510700701440c82010851040161000e005200000f00040303406038220b055050003030b44903183c0e0305c0090002c01c5501d10002c01948d00045c2c0c00100700c00811044110143d03280038060482e0b59203413413281003845400300c47400141700110710fa0082400f82d02007500510b51840c001070728040b0640c40030070603004515104c0158043c40250b040030350300a010a41c0681c0c401d50650900c04984006800d84081e8007000b03100d603446641e40481041d00300081c20003000300030b00441c004141c134182168014442 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 686397185 1250 686395935 686395937
    0x111b13092001171501180803040321020a1506051c020406090b09070518060301180e190818040c170f010f15030b19051c0c051002011b090501 62
    0x20381a00c01980583d043d016055001c046498450b5129601110740755001011241842a0b0001d0300c0c4811100c2c501e407101521340000250780d501d00b141000080503405081803036128600020b03203038909a000c50b041d4407030369000c002040318050807034000c005021607400068001d442070800d0351404d140c5a0044070882d000741e404210030382d00e449011043d5040e140c2820b030072081c4036020806180c464001000c5400c0090615041d5100d10000a6031a6000382e00052042d01c2c011140d0111180c00c0c4126411000075034001d220036a8610304541c1e070800c0070314000d03041030340c045039034171031100b011091580003e00103200f0000150005000b41181f4450507000c12202260f60000300c84180c0c129803d07060380c0c4100380300568a854007065102c82071502610204154441c0310f1329020b501e400103040a500c0081e0303241d44025013088144404600c410080a103036039404100340001c14500e820703110a5a0065800e00011701c0314400680c050b16020319140c0090500c40191003400794095282d030103807102 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 686398435 1250 686397185 686397233
    0x705150d0b010e1f09090506150a0207090618052415090405041a010605031b07480f05010e0a120605040b01270b01020709060b0a0807111b1309 63
    0x100c80011048803000c48041e40c0127030012581407960309662000d84441705441c8104d03000c0589031000d4100b40d44184e84005038414010100c6100f008090141c9903020300088003100303d0301c0d031074a0400000c90403480b04901a4070180d901c9129100c03000704403648070720701070428010743c2060700d400c1c0807500315482d071941802410000440c40070300ca00102c0380a8080e48805080000340c10442c040c050380a45c0003180c0c2082200342c80703284030f6690000703064148800c00300f400d00707003601c00c10082081308190003021b00440d29a500740700c000c1e11352007a841030312428641964110301c207034040b560443d4107801c52503603035202c2c460710020040107402c1503209070300c600402580390741da0b107508103007903018084000c01e911a00c504c00e204c0e04803141d01c484000801441100e040b01c2e41d480c40d910484500b0742001c41a090000744412005070040c14240d007043d050314041e4078403000030039100e84414038100300c080801c41c0c82920070541d82d1061046c0f00317000f182080c10400c5160760300d000c1c8080c20b4010407208200c10f03 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 686399685 1250 686398435 686398439
    0x1c092105010b06130603050c0d0e0d030c020f030313050124051813150f020c0a05070b0306010921020622050603010f030201050d0f0203070c050705150d0b010e1f09 72
    0x2416800d41d403010051012940c51217061a400fa4003810f0000e240d41e41240707040c00711450051660090a210b42d104c000a866a400c03d0600181920304c003610003030035540715158643d81824000220f9a00c0541a440c91840120038035046025004018006c1074400703821005403120440a2001012120100c2d601e0240bd03401c0454080c3c4400221040d40c1030301e06540400700403e007072034079403800400441c00000d90141541c4072941280c000c0c06c0c507000b00d548902118420030030f0401c01a0098682c0c11074590a5142000c00200000c4590082d6005045895880202101d0088003511129402850700c0c1e101c0b6115549140030390320528551241006609001500c0d040490480f4140c500e05032104115508540042d155036201440741da4403d40e03a0f00c2d011071642035504c00307140900000c2e50b640c0382510381810242d1074000203400407032042c0c29070581c0c0d4128130107540407202c100969800101d4003240f040010b84682c4403580184c3e41050122a4501e428031894044a0343d010103522104030340d076 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 686400935 1250 686399685 686399689
    0x105072c0105040302011805061b01050912030610031b03090b07030902011e020c060705011407081608090a0c1403071a12061302070b0402040c0f021c092105010b 71
    0x30310000c806404202d041200b0320240d4400c80360401a000a02d10398486142e82d0310116030194007212211200c0c10701803419900001080c0141500000f1070001031034001642d4031003c5107484050440c0d44030717005181c640c0d01e520f4003031380100c525864641a40c2102c0610301c1c002401400350000c0c11280902080c0021700400c0c02403203003411083e0107940386a208041c100740da8800480c6260300c8819845044129901a03541000814040e03119030000320341c1c0d40125450400c00c05001d030200e13050020b40010070564950514504031000c101745407105c81510340d070507010304041e1224006807200614100124400403800d2010741c030190b0907404c441d4150fa4441240303c0c0b5010940c243c09000d0801c00007640d480c14a110050340244005055100d000c28a952442c1281e0100b14206c5480554408102c29403529200d80d071400d000d40d05200c1403003a0a420000d45411400d503880480e4449140200403241c07040c0100ca01808108488080c44500b8510159045e5540d1000301c13076540c00c0100900045c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 686402185 1250 686400935 686401007
    0xc0b0a0309210207031211060a0c03060b18040207140102030f070905060903071e050a030302010903030606052a190f0b060409080a0507060207061a01030b06030106021504080c010507 80
    0x20140343c0d028203442421a070f290034029083e001701008212090f18500528007044c03110b82d001b41400c10001480401c000341c05400e4540c6e42d844800c2451052000c2c00c12203031000e4140d16a85811900165550307801d1034405d00c960300d00300d88081258804003c0040c01020325200c103010b1325054403898180c41c0c0d00d01c10001d0a100f010034080d0142c110020401149151040000c958050365500341801d83d00c540204208000b65441640140c0d11004c1c4402419003520923200500150f16106103004981d0355900b40362203240490100318904903100c050000000d1103d200e00c4600121201d04604140c1004506800400820f682404001340890101e207004d108081c001a480100305040100e003901c2681c07150403401d000e2342e00540811000001800342d00c26401207010b241890700d070416403400010111040700c01c02c28040c24040005109207a0009a41d001e000c4d062095407003165610710b131020190041c121105035075070800051000cd180c00101d600b5000ca03407000d0903440070500c3c50b440e03680 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 686403435 1250 686402185 686402243
    0xc020307051c0602070c03050f0303160503061c061409070305010e370602070c17010b030601180605100302281709150702060a0b03030c060705070c0b0a0309 69
    0x96010b4040b03400c00080c0d030340d030003070a10310380915115001950b40b81c95a5040c480344080079100c5401c00420813114000c6240c10341503403041441c040f4218a04500411400d0191900c4449400001000d01c001c2007090703080b80c101d81e45c0d607152a02d01c2d410114140c0f540c2e215580800c8a1a500300744400080d080001440c1c002150b104580c80c52068541420401c0420802055140311007001402008120b050005000061207a4908901d0614080e00b582060300520b040000a9040c03241c0e001c5246e90000700c1506461303200e407404c20208135400c0c25030001c10190748400d412150100f05d1009064055009d840c1543c01010290400311030640084c22994140038040302240d020090511258500020750303034003040000446802d0700d0410301800340c1010480e451b000581c45401001400105401444002001034008604000054410640b80d0700002c1c9800100507010030f42206111641c0002d600500018545c2a6590705042000340a40488034080c0c5004000c410b551a911540c440c86880d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 686404685 1250 686403435 686403469
    0x3100e010b0402030c19050c0d080103060b10020d0503220b0108120f03010e0720010b030706030c0909050603070b0c210702030d0e0307050a18050c0936070c02030705 73
    0x11401646d65904c07148140c03412440c10030450180071080c00048100700c1c00c0074585203500e40c12403640c59480c04038295541c521046000fa040d003071990b010150000703000321092040b42480ca4903552035807541d4000b0700d0340d40b411b403240703a040030003950610515110392816590300000b5a0020f2400c0000910f20f80300720240700c04180010001000035501e4242220340248952510128040c8100700d0b0120340403c04407155002e9546044200a40c501000404010604c074102800740c401c0740340d03010348203240c5c0d840b8040b607040c0c540c00003079001da03018030184001d0705500d450701c2c0d119181419000c0d614005054021a800c0900e204100d001400c1c0d0b054a0620358010010420070740ea0100490f080e014610b8201d425104810010a0076600c03000144003510300d050ba80d400f01e5041c5600603044d29000f600e031164920040001c09159221040601521640d0303084425003021450500380320707122000c00194400c101c030014460300340d5100303483d61001030003102140d08450711074040005429200340048 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 686405935 1250 686404685 686404687
    0x7050d020610120501060b1b0705030d0203040603051f17061302060702010302090a050a090c0216050f01080417030a0b120c0108130204180803060915090106051803100e010b0402030c 80
    0x980e40c8146004100f90300c10000441c0440d40da4103450001e803c903410640310220520590801d6030f0b42000204000d0500720000c0441c2080e10202a44030b100d0390282c2001c05454a0002e01000d401c0f01202c1803005100174081c03404e076540c41180d220100300d0070fa040c0080c010440468240200d18546410720794000b0102ca10b400d4003540154004d6028656803900100c00080008280e40c40c106034000410451001141a001190000b420301d00303034080f07040f0030b0b0007801c07400d05c83c0707445103074610714060802c0c2010300c00c84d140c50078801c9400144820050188500104216100e07828be00031070f46020050301c001c910a85200110342d00c0c3c0d80d88800042c001000000002d44802049002d00c281d50b00203400058a40b14044415541c1280c085d0f05660f0102c00006000450410403081e070380c400603604011010500380800103040f24010b101d05001c00c500881c0380b01000c0c84902e0080c1c146000142110b6520b01c1c0d00340c80b0006442000d071011069440d001c03a101c176a0825000b16841420084070355 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 686407185 1250 686405935 686405939
    0x62d03080a020d1d010503180f0703030f0e010c080409020306060d0e210a0e04050a020408060408070b0c030f04121b0b0613020c0a0204020705010b0a1d010506090105070f140a0807050d020610 84
    0x8144048808c6240304058441c19480c100031840038403541c000b40d8001d0fa5002c2c040401e0390b40181c000b94503000e0460401601d40c011001068410042e581036901140d00582d6a0b00c41000050050240c40f80d44200c1d01c0c83c1c00b0b0352040d0050001a40ca0300101890518a00c0c40450024a402401001c85000110703c107000590200d00c1c240d03001c15888055400c0060601741c8074001a460700740b040f0f4085a5110001070401d046c01414038031503a000e242d1940743c03031962603d200804203901014000425288112441b40180d5000f2034560300c01da1000d00c0d401190001e10304101c0c58414041d60000d00076100c0d0400095a50b8250088880340301d4250000c0101c0740d116403c0c04020340c000707841a07803d556944800303042c0d40d0f24120020014180d4444a140800018040313040b82801070780114841e003400c00901c003140c1d0f001015600803940001c408100c40d1281c1c10038840c030003501d00c6910382d24000e15801800b009000c00140080700d019200b16100d441680340c0a9944480555500e0510440c00c102 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 686408435 1250 686407185 686407201
    0x105090403080f0c0409090b010e16020d0c0206160503030a0b100f0509151605120901270308030a090b0907050102030403080c0f0601060309020f04062d03080a020d1d010503 76
    0x10f0183c204da030901c4011300d000d40d9443c442080303500c88581150717440c078043c004001c0300070b40584454011000e18001c1559594025001e55182c408007100c1060181c6d0f01c0c081c40566841200390303642035944101c051040e44079841c1c8262a5407003210002ca1582c68060300e003000381004a1201d03a015115240c003500e840103080c0079207050300f144821991240015010844032029940905011070903044c1c403150110003403801d40c0c1007150000d111030008005110310b80b82030f80d11010391001c0704611015050004044031080d081500180c10140408100000b40001542c0c141d001d001c0c002e004154580071600c9164040344c988206204040c01a8002d000c144080345858008050281c924811142d02400a2281a04041c000d900c40c10100386d032444a4029401c16400500c1d000ca0111400c00c01c01d400c107200b00000158103c00303114446030201c100745c01c0200b01c50b5540c0140d40c101003015114030b02d1480c002e50700d001d21a091000a40c00d20700e480030f001c110640101020300c058480e242980e440c41c030 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 686409685 1250 686408435 686408461
    0x30d0522110d020f041b0909051504020a030f05090318030102190302090a12050c1318150b03150411030f0c060703090b03130330020306030c12060f010509040308 71
    0x74051380e22005031045280c481d82d40b44034403481540d1425000d0b901c0750a864024041c5007683d80f258500c2c5040c2000c2101d400c100c0c0d9042101300b00100c03001611140301c0f80b41100103003440540840002d141006100a10f40d00001600c8520310b60111000c0c1c0311088030900d400c1c0d0040780700d48901c03204050f840c012403074002e8020f0f2070040e00140800fa5600e0350744400040e4141c0c9180c00341d482d600401c3c80c019281c00d1486080003041d541c04c00901c00070100307950345820340082603c054110388810b2248088501290403100c0c0010380241190240380043e25200103241040e201181c1a4400e08800a40e03400d0206081006e5520341000e04081701202007403110b00c0c1d100f40c5048041051029000c140303003240c6030146028101490310440060018a0b0290284a00b1541440405008075900415844c2103035641000ea08400001d80c480d10365a0100e03160103201d030301d22507020000148540c559200000c000b07200d07007401c60301c540140e41e0321014418803600c1904d000d00000c00c1d520024181d201211 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 686410935 1250 686409685 686409709
    0x80606090403031803052203020913060e031b070f030804030f020d060609091401060b0d11041a120c03060d02092824060c17070203030d052211 63
    0x204010131209040b0008040314007841404901145000c511100d410341e00943d00005006003003013207078406c4e040d0b03000501e10303520007852101c11403900012403007003205a801401740819284202ca4644e005c0f81d4031002c85c03003040c405101c018030803a0000180d20040500310300813650458441442c003800c640311801071996620041e40c221101d14002030002e500e0b4400e0100401d044100041c1161462800840302142c003500009180e0400320144900000c00003142c40400100c840001c015280400c08503035800389030300401c541d0358800a500c414400740002086054100403580c9100e944030350082d0254001551030582242401d40102e0041c01e00003000c2d40c000e950f2130050024031005080c14582d100360307044503015864441d003003020800c11500315901d120340d00003130602c2c2a07410058024840019014040c0c00104030328010540110100f040740d0340c103074000e030075240c0d1440c01403452070143c01d0644110110f81c5074114503101c840c1003100e8440c0f4480d4000f04020003420350508200c0d00340020 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 686412185 1250 686410935 686410937
    0xd1e050102070c0b03042a0510020127031101140103110609090124020c370303030203040c0b0a0e0105030a06120b071704080a0f090815060a05010504080606090403 72
    0x2c018401c045100ca201c4000241440c602141d0b60703182900e405004550301900420481c46022200032501e04000d0404090304e8059410100c0c200203101d0480c050840c24031884c21007004d008151040f060003240c0244410702903151038080720500301242e422141e000c0c5001008840700380040c40014991880b90110501c000c0a8904046003440010020768081e40003048a24011080318205050076a4409141c091400580f08410452010415020144003091001403c2a20f040d8094001e840d50007454200d030004506c20503140d1a026009501c20703103003514013446d024000a82c440360041110340f401c00b55544c1610315040e810041d43c46400140c400d5074060f4454002042507a00c010080100b103015040d01e0b541da061400707002d00803442c0c03942d42d80094000747c0308000101d8500021903500340b00750700d400d902d0899881002c542c45100350b00019190700498210220f82c40c41418010f004600c221821813100c2d503160015140c51055100d5a40c2039003007007002594520f45844900e600c1802 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 686413435 1250 686412185 686412187
    0x31b080c06090f0c0103090b01050913050a06090b0a0605130c051b2b0813171b0c010e0a060809120a09140a0317030603011d010b0f0d1e050102 63
    0x40080c410708010084900c030085030301210540146010410501045500c05e00b4104410099074507841c0c2a6881409003d02565400000c0303100d900c000c8030003804c1941c0000a4a81c5110545419405484604400c0e9810f401c1a4040b603001e9509108160440308000c05440841c1e8210001c2400b41c07a20a890405001d1f081c0820000300000401e40c040b0340c4219030107042c440703004900c14031405c00c0400420014000580980c210140c202400c80d8000d1141d01c06690140303003501c1c18400d0801c0c40c3d4000760301c2a00220351240b00c05080701e00e4a86581185c1d090b43c1800741600300440301c9240445880b40d10980c00202040698019124550040f045500b680c030145491500716005900c00540440040c074180c5081000d0410f400040d008484111043c0301c020740345481d820144081107401044009000002c07035205d94095010401c2c1c2c4090390742044911282c1080a4003c10301042910f01034801c2c0c8400542c1e43c5402900c40c0c07025036004c41e86c81d101c2c10003c0114811642d1a40080b141594 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 686414685 1250 686413435 686413447
    0x15030221011a0307090b0907050c0f011a1201050402010e0d170f0a140702010212090d06050906061c0c26071e06051c050a06030204110322031b08 64
    0x10007030160300395400e1190348190301d064000d4180741c40c1c04c000f03600489007280b400074180c00654410352810f400610b5407030a40d8a5000407010700d401d0104c0140d001d80035600c2c041a0402e000804514802d503000203c0c0c0c686e0800142060060a80d0b00c100d81c000e000600411505d4107030310b4851082e0740010b00507100c90b00010740351303050003120780d02040d5400309500340854000e0030355502c0300c0c2c1c4560071140b450100d401e007940c0b580041d6890301706103070082c000b03080032621100c0d40c1c40720303100b901e21990071803007c0c03000c0e04200005030b840d81816181c0c0c42c001e210724060758401c40d4840d00740c4a5110341c40030954454503d054072510144111003a20601550400c1765282d030081d081048102811502080358010366103141200c90a90f080e60100341880000d0003001224529403445001c20b900722180400c0c0d0b5901c0b078140c0d500804140d00700941c81490616240e038422680d8000d9441b44484c030111002c04106102c004d0701554440c480100000d00c0b0740c3c021404c0c801948241921a0301c60b41c2400c1c2000 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 686415935 1250 686414685 686414749
    0x3070b0f0903073012050307050904090606061b150209040e1204080c090903031f0510091e05030703060b1813030923090c0c0a2004150302 61
    0x86101e904c0602409000c0000128408810042500300c40044502c00260151942d4900c1c2440f44407522a046c0311022000400c45400755088441030701c4010010420f4040f9490241c006050034007542c0c00245001040d40b00c030f00020341c071103080300f038012502c046a5214000c41501035486143c0c100c1e0416110b0f140342100420401500c0c080084030001c1c9031303e5074140100320703150640140845119010f403909119180c0404012030342c1003d03074030000c00f004d00b626010340c100107503107640055041004404405082544400b504040d10180c01c4000c100d181c8014800b00d8170080b50103403580c10340000390304000003070321580302480c2d642c0042e018080b0003248005402120750f04070361240c0c00b00e0913060800e0400d82c0c040c50340702c0074120320801c1880d142031513103021140503119090781c0e0095003100c02240c2440c4880c4155014984621704070f600c8894280f4000d0304011001c1c50300d410700c6840c0c0c0e4491440340b400d4090003042c04c01503c01c0034521403454007081280c0c28a00114081480e044050340308603 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 686417185 1250 686415935 686415943
    0x9210c190602040506032802030609041203090506160e060309030a08151305062701140a030602041401020615030a06230709060f0305091506010210020325020c03070b0f0903 76
    0x10f03821f8100c1940c082c540c1205070080c9040f0429459001603c10410403205641d02150700d604941c0080a88050b80004001900201407013240078186103d10380400880c10b02c0c443c1c0d540000d910740d42c3d5007109a10040c0070702106010a69131041150024001d071455188034402040d03000041c4020f056007117001310003090740a0744210901c19103503160001c01246040040506200d004034205203449021251884507100710b06000304e1070b40c0107452100b10400d03034640d00084040c5803c000110b542e01d0b907035480759400340001c1c4045400341c0110b9000401d510255200e40c406880c010380580408015951024018840690041c652600c4058100300710800c44080301c0c0b244003e62501250141400409400d00049a500c3c108141c140010451340707910110356201301c60410a0440c81c2506d136200141c0c00c00b4114801046024404000c0000d40305c2c25140c0501d4a0100b4440301400109481c0201c1c1c0b1210340f100710580581c0301740e0f070420044010310000c1c0340301ca4061048904001021001a0070 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 686418435 1250 686417185 686417191
    0x20c070b0703090609080a030e0f0f04020c1c0f080a0506060d020d141f050d03140d2c031204060b040c0509120d09060c030905040509210c19060204050603 68
    0x5104040d0134442035030061050303000307060820001c01500b24682da00400700721032120b2480c090700c40d141d030f250721503100e081c107003001950028001c1d500d98801d28a180e0341e40390043d02c1c0045010358140c040c0300e0076000720030421000941e581d41c504d01c0e6583d03800c1c00b4054000a0041e90b0020000c010020214400b031000c1c2040c05611840440c006d0052940c1c2c920028000c0c00b00542050101d55990307892001e642c54000710b45003624103500018540c00e054416026800b060303699080000340d03216440629900c4201817829501d481c81c0e07441c144400512000300c043c58415825481044003203039400c5101e4440b50310600c074540101d1a8078929010070192041c017502c800c0403c07800b040310b40c05842c000101a0140381c034500240a40850304030010000c2042c0e2183d8001c1c02078a840120030700d4031880030300c009044041c9c0240001d05101f54526900c01d0102910101040c040b40080c5071011480111001d41c00300da4000c10486090242001003010301d44070071500503608110001d9551284409144 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 686419685 1250 686418435 686418437
    0xe0d05130317031f050d0204050a2007200904032003130513020a0c021009031703040b090607090b130f300201080103080d021608030a1a06040603020c070b0703 70
    0xf8903030a08410b0b1907102541c001425070280c540b0704003848951034507032804100c203404960101d4141c0318000b405004210000340d0345800980545a41e0010010000408500b817080101e03080840385030404484140388210903907444a070040c040b0300841c2c820140c403100400d4100102800150b210151481c65000c282910f60020702c5203c1008907141c845618892444038850a514188002600503e84506450028866059405110300f071910540404014540c440da00c160300c040701441291041d08203e0b0201c5182241c6000500300900110300d0034003419141d00e0340c1d015281000380d1544590005512010802d1402c200000c402140c16112001480c0308420031403510144c80c00c18511551055080180c8a0824000e50060341d12256090460b50001881c0d500c8002c1402480060f00c1018108520001d0000c4a141844040c90085000340b081ea6801c0081070b820f00300e6413612445040125034400d10030320040003c5406a0010880e203e0100c043e10711107a00c1e244034050036040608107030 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 686420935 1250 686419685 686419687
    0x6090f070201020912160e0606070605090f1906061d18010212270d020c130207060c0225120b090f0a05100606050f07200a1211040e0d05130317 63
    0xc012400300081b440c024001c44140740c452468040007003556482410070041400c0c0d641c2c4000340b24140240030606550500304241c0c3c4044d5492140210301c0c1c180040b040d00c5181c906280001c22a201c54404c03505c203194402c1301180c9a445107200c403c05029030100980381d54023007040d50165280402441d1203006200c002611003210700d114500c1c0050044080076255002490325100310f07800107200c600e85102203624850010262036054043e001d4080c0042903141482c0d00442c880341c000c070741c0001c00702c0201506550220901d800e103810302c025115642a00c0c048020740c0000c1008940715551000d02c607000c47d0007652810f0441c91030008209800d48054005810030b001452840c06075100612991800c80c1c200b1180140041040c41000b400504001d4104040242000c020a403144104801400340e00c840c0d644400480000c60080c038100c0750034200000511592805200b80114411002c00501c41c0309016081603d0590102081902c0c11000d00340c004001202d0306e0b00d0003e440c0000506d5 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 686422185 1250 686420935 686420953
    0xc0f150f020c100b01300c1e180504230c04031b1d040309090e01021b070b0f030405010603060603080703021b240f0307031d0606090f070201020912 65
    0x2504050311600f81c1d0300310500340111004280c2e40104081c6030b10300006540c1c01a1482203104030b002205850f4005501070825260b0351966400001001191108403c25203450828907000c0b103400c09924001d20f00400ea220061184c0e0515510035001101820492202050003010b02c042e6004100c48190000400003400c0c400c0290303401030f426051508006000c1b005040c0f03140760303403180c0c064800041c082e904c100000d018580300d9141d8000419001342c00f08510200400381d9030203540100b060300d10103183c140d08841d120000007200780468148460150501e050011034140301e500c05002580d0031364840f0801700201e103c030b1154200441c41488181c0e601e1a01c0d00d00a0701300910886000e104410008229516403a8010f65400c554803c0b00840700101101540704407602507400340ca14150703000b100300101c1580540c40f8090140c0100d87e103c0c1c030184409030b283d5441004550391a00302d00c00300c02185080b0801010f540d00312082e80000b50401543d00d011405400e50303000540c407642d020b4142c0c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 686423435 1250 686422185 686422207
    0x103090c27020c07090504030c060507031b180b0703141204021e090114040e01061e150e0d1e030c0204060803040e0c130812070b0f070c0f150f02 64
    0x1d4000e4038120358203606240021507120780b50071980c40340030702064032000098101449030200703610407036015000f08000c0c10b0019004005104030034280041c51404400b00c2240c030b01909050305081c0c1c42072215100b0380d06004076041c00303803c030300c0085007402350041c00c19066100001c050114a800f4410104551406004110000901415035110300069480170000c586510417494155000440030254208001000c60014030300c040030101c180d40703006000304030100300d42e99101745c00c0008071682c40c40c2c3d80c5035040100c2c001d900446105c0469498003104107142048826a907403d40200c2d5007404000d080702022254036000c0c10200c002440c0740d4800002c616191240c2d40240032410015030a02d8241040c00341101000340c411461050080381205a000d407103000c0c0c0024110341c10603207140341204245450250401881142c4400b00200000c90071000c0044081c400c50507507451005503605500c501c1d0080b0106071040c4c584800b07002ca0007000801c2c50086100007800041c0043e40c802c0400c0c0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 686424685 1250 686423435 686423489
    0x5091206150a030b07031d030423180f0702100f1e11040605090f1c0501140709050108180d0c05060901060509180304120305180312180103090c 63
    0x210080c422101d9038003c0c0040740400b000150f0000c0d01c1d040011300413501400341c01502d400c0e40007440e03603031100140c0071618a6003001940040c22210164515a150b40340c10001138189847c2c904102030988000180c41d080a610007640040c8140180d4a0303500700d810040082d903013804034000c142c03500e48000050003a8040c1001d001c1c100c01880800c40c02000002c98030180c49107100b00300170454081a20789050340c5071025280b503800d00605603441c0e03040d03440300c0b0303200301c030480f00c043e0b403954680407402c507103451003601452140005540c5c160b211410a0010349580c0405850340c2c1d20903a52600c4d00d49031040c100310018030380c401500d03440340d6070704030785000c1d403610500511941460f4100340b0100700c0c44c0c9031b04150700c1d00a820b4203120300303482125a500510303500641e8810080707150412510000d05400a0050604242c0b502440c14485034550a240e43d68198180750306001da02040400c3c002c1c05071041c400c00c003000502d00415001019107640c04002c03010f40103545540b05000d144480d40358048 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 686425935 1250 686424685 686424721
    0x17010f171b0112140f0106110304051f0c33060b070609080f04060302090a0909020f04020c070305060103050d020f0d0c030804110915090c090901120305091206 70
    0x40c0c010311410414144110000341c1c1803406a051192107103101c0210005a00628900b080b5010300049903d0711840041040c00280324080108001c841c655081b88800300c1120150f540161610211010740c240800b140f10445d0031610401410a0058000034a030142401c13102241600000760034860301d10800e03078065508034810350b4030b217003031401c00c840d0343c004003500d144a400000006181c4080d0814040912500490350301c400c10000c0c0110301e02c0d130164040c3c001007005591300c075100c6407203100b0201151021080650f0011981e070754821245030540090244596900980350310950341c1c0d03503103450040203070070482c1c0907000740900c1c00609034104990000341c6461801080614001c0d2400f80c42149445405020400e0440014003400110325564506003000f0340203080900e00010380d02ca501d10301d01c030218810910200455a02da4158080e00c4e80c5000c010500e217900e13464040e541018451201044042c4201840386122994540e4118031508403107201608240c64840c0404502032540 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 686427185 1250 686425935 686425979
    0xa0309031b06170604020408072702090906210a030e030609162c16020c0f012a0501020304080c01051320030708010c020d0201141b0a17010f 62
    0x324508004965102c8a611060300c0c41143d000c0300e903191600460080d10498000e002c0754031590302c00255854400d20200550310854503076401c03480802000106034440d03c40700340e074000b84010219030075181620242c40c1010002c00b0400d015000c4826950400308502d0050b004240c200e44110171504040c80030a60000d0141c0141c010034107641d443c81c1c5400c1c1c19000d4030004500741400004240e0302d142849090340d0201400d0000ca2920703010703459400581c141e003e001801000003480346402c0c50300c14800740b460161104002644251a0408200015607041350b004210150300c2e004184207100071401580184021036650300c414501c2820354102800e02501408048a420045121040b103101580700440e00b05038041e90320b00009180c000683c000c8942c1d940707080c070a81280740c3c0026116400c2100d64000740f01c03840c52441e032242c21103011500c1c0e43d01200c1001000660300080b500800c2284000d051001c0001259113480e02c0d0604242c01100e00d4405552090100541c1a15440c0e00d50340c803 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 686428435 1250 686427185 686427233
    0x8010801060501021c09240f0f2304090212040b071b061d070e01230a05060906120c030106030501150905040e030c0102030a0c140c121b0a030903 64
    0x2070000001e583d00f290321401840c8800c28040300f05c0c803038401ca581c01c004200c0040200c18007000e2110700d48100104002c001d0108140c2c0c04101107490007600980ca408500e031b26900566001401400c211200c40c1105000d51141004041445403a5202500540d05205050500d034a018502046c1071013001d0101800c0c089485c200103000c60000c00000041a44000c0124070820842d084482590050070001614050304402080e005140700c070040c12a541a00780c0c5030b008540080c11740e0303483c490603200d50300b10421140510850401d80000d1483c49005011246010f40c4c42076002064501038544000e4240000010401a9458050503015003102c44400707840601d07802000d485507085d4400c0500071501d8000003088840c090041d280104812802556240313421100c030b100400282ca0350002040015a0841c28000d00e4010b0340d54200c0414000c0c030188059120011607030304900141940e210311601c52103aa0f15003441a608007501c6a00c1c1e809403c0e00318501044683e0800e01a8808500 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 686429685 1250 686428435 686428439
    0x6090803070c0b090f100804030e0a050a17160603020c0705010e0904150f0906090203071d011406090604180605041505011d0a03031106071806080a06030204050106030b010801080106 80
    0x210400944003210740d0b03d05004e82e1242c0010104100410341c400d00c80c3d00c0011261741d2416190040007035031144e4031030b03036440c900791811108100300c1d6a443c0c050140c209200110522510381303100850007440321a8000c880a5410b1155403a040c2c941d60b4004900107500810394103074120f02001003c002d88400d00742400c2e44640e5801013908080300038000391420401c100701d0030301584660b206401040300243c080c0003000c004d00b480030282c030810000724040c2c440c0e60400109035081c02900300000c0050000da40c41039181c05186050070848484069005030104070720881d540d101002800200045181d4442045440e080a000c036484d590040740100d0401400c54a0b02842c81e401c0740c2030740d03801d0820b5075011a940e107116a40d841c1c030040f050f410414010700441495000901ca000d4601c41c4401c071205a6552041100c02c030030780d4455007801041110082c840c690140d0135840d40494014000a201541c90300024140c03074080c0e00900200e0ba80e241e81c1e84095a12107415405000d60300001c0c03041078 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 686430935 1250 686429685 686429693
    0x1b03190905150706060503010c030e100216030f03110310060806090601021c020c093402030723010c030c14180f1906030605040e0607090303050309071706010609080307 74
    0x40d1008001240010b00007541c20200103059020742c000d0a0042c008000b036031020340e8041c0003458440b82e00102880b074070180310120301050080b07460721681303e0222179011241e0b640c143c883c0046e40001e181459212989143c111007c000a144951507601c0e10000301d5107010806040003001a14584c007c00220341003140a90300007408071000c0e0f8503071898000070248044100c1c14005d120030f91301d50000121060000d50000d10040000079640804848103000300200305a00007980410030300b015800a10240f00400c0c3c614001c0c1c1d00605046152180e20440c0180d1903003100c00c00b10f51040481c0e030750b1040e800c5081d84080c5203c160751040e030342a45071004102501340071540c11030a540c03043c0140d010780d6a15403521140028032a0b8080030240810b52600c0703014020341124015240502c0c50000c00c60114600020003a01445081d20344c550740a0035920225110340c030052035400c1d584520364002414035140340d00c3ea05501e031917102070005035040c07240c000d0000100740c0c0601500d41c0140500720200e = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 686432185 1250 686430935 686430949
    0x60a09050f0c1312050109060e030a0903060b0103090b07020f241f051807020c010905091501050f0c0703120525021816080109020a020a02040504081b03190905 70
    0x101805564442c105242100c503c82d4450b0408041801400181c2013040015017016040a1003404c0070f218490f18840e403995a8016040c0040004401110130000320709141c0c1701c00c801c44010714000c03598600a883d5006c0c1103c080d00d41c0001680881e10307607580f0f04824080b17448030084007803000f0005c141e55240001c0d20800a4a501048100e49180c801e049072244020301c014600a01010f8120540f80500489004202d500c20b015002e90313604084603611403044a0261580100301185540790300001c0c54a007001201003a05002003040b801c0c0c8089240b801401c1c000f44080024a0420309600d8000700c2010844440300a200c411b010300b134a8001400f440b0301300d80284540b41c120401c201c1c00005e11174032042d84580e40078140281400390b01545c0c00d02000340700505443e41d80850b6620007119040b8071a600c4180010f07000030002c1c900610f45500080e800034000c013032460400c455200500941080c0c40b00741001507000188079000c1c4000420b6080c07604d486400c0c0002001d2501000c9154 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 686433435 1250 686432185 686432191
    0x3010b0a08060d0f08031905130308040c0302150a0e042724061e060806010f0903050d03060509090a0221031905180409050c04090c120308060a09050f 66
    0x2449803410002d8015140d0350425508660842030f42486191303282030060745944180e03800d210f8642c1c90034118100c0d1409009541c040c0300904c040d00308220171510125100d990180c8201c41819003108004051707560b003101080c11702c201f09030040c2c0d646035561000d0501c11a200711103002d103041c00081c1190039909816451958002c05100310030400c01c2c50111122840181c0340e00c0080414900f0545020143c0d100d081650f0012418696440d90b50910700424a594403488001a810200050240d489081160540e9407035081c0011510f0b1290f4800303081c0704401c0c1d16400000c0d034902081100d4503710385115040000e00d000b03070071201a141c01251500310090904501910315694544c032080040049410700401081d6602c0080c0072801c000b41141e000c0c01402806007454040003d40340343c42d00c2034052030740e400300041c03804004080901000d010090000e6030103c0062400043d5951405601000d0910030741d10402c5030300c0e01204101d040135403900401c0d030486c642340811000700822400150 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 686434685 1250 686433435 686433437
    0xe06060f0d050708030304080301031707050a140304090e100605150304080f09030a0303050106110d051626040603060e0903090d0206130308070203060702030a0906030902180f15040203010b0a 84
    0x70745440a06000d803030440184d00181d80e500c000402c201c14084020059410390744544045000101489000d42c0c090107039100c003403e03a4014404031000180310b060340c030070181002c9083c0c9040550f03407800300c0200c03101813165480d982c01050341d0342c4901c030981c0301d80c43c098401124540c040641403021544035005c0284010031041002925200b1400c1071401c0e85c3d000d800c02012035100b803001e403138028090319081c854200410603403d151070507010081201c9442ca03a4a55420741071100414809a0785041000140c9241c0d41c250b0742d5550070b18444911040c05406d24030426030b02c501d030610060803104281d00c000318108030242405544200402103d142c0441100c890000b6989400003e00318424507030802038512003108004100b25034100603100745030007202a40d019907030320359003a80c491081d02c52a5000410a8200b40081402a4440580300380003415010315202c2d07a65039007507940d105440d251a003002c0d1808100a8814140b000e242c40507090b10194150f52524103100e040c0d000b00c0002c44 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 686435935 1250 686434685 686434699
    0xd03050103050d050a05070606140301110a0e0f18040b07181d04150c0207090b0907020d05030406200301051908061503012306130908040b1812010c02010e06060f 71
    0x1104d0512400587da60142c000004008540c0e449203841600d00710302c94460301070350030030309981201c0c00e00d0010303111403007040c1d100d0144810340f11b010861404064419280d104030014912900c18040c41c2400780300e01e10803000400750741000500500500804842d22100000c81e84080c404a044060300e080c815410303803022465503c4501c1c003062a45405012002c58505e4424148140c81e400507010381184c0300500c041207842403c0060100d6104115412170250340b00b0300440c0c0d60700c2e10030343c015070303005004400025920701c0c80342801141c07400c05020441590000b00c0180040d180200001d0401c2c030709140c920040034606901c003521b4040c02480550506d00702d80800350113480c203420036400d00d404044000c420307100355803408106000c10746920b80154501103d445860000c6d102703011036541c10400e41806c00d8038005264031141d03c030721500d60381d8400303a01c000089600c601c4a4400070718904000441c120005010003800c55200c801c0b1840543e0080003802a01d4465444020303802006407180 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 686437185 1250 686435935 686435947
    0x1090b04140601030f150f09060605010e0a0b0909060d0c030b070e040c0e1c0f0f0303180503030f060d02220c09270915020919062c0a0b07050d03050103050d05 70
    0x70b6001001203e1420311f0340380c1880c0e40d03842006403d42c402000e840017601d680b401c1c1e092038401c0c009202e0342030054801d02d010401103907500d4a04102c0d05035002c03100410181c09042142c0c2c0e01000c5685943c0120b5040410b82c05100d0466003103021786050f110f05070340801903101810001000d68441e0425180181d85022a50802090038071280c21015040608000d07002800d20b4151140001d814003034000a1814280d0008800b6181c10300009a40080042d4255142d000c1042580d40d006010340e50303c01056803580780181c40e1118030f0840b650004101e1010a141e46803880207071413180c495002000300342034003800111543d4521a05028201c141c188207003220040c04402000b0607070b0b010f081c400c01925070b0140c00045030000c00a4880c05d44001c2c0306442d0307901610300070350614001d40c004640c0400c040035021003010f0028403040703c0c03040c042645101c000045102042c0c50f801400700c1010018500061007410016a030f40c0711401d2a04002642c50360b12010b48403041c0c1c60078030080050000300 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 686438435 1250 686437185 686437223
    0x60b010e03010212100b2803060504140912031b1b120c1506090a020c0c090a09020301061703031602010e1b010e0915060d020c01090b04140601030f 65
    0x80d08000d0014008640d104074640640441401c102c6022400403290b5001058021410b0140c4042c40c4003c02101e003003d50080441510002c550602d0040603a560740014960b40d45010380d4010054070a6401c0d0641040c3c0542030800e01c0f448c0d80f40741040c0040080c01500c9161284412514100600b16a101c40d0041c80703411040120503605100c0303206007070501108070400310080490114130400c84912180040c400100c0c0e01d801c603403081d0312230404000070b0749150294000741b41003003910007a14000000080007400701441038844564803580d41015034118142486a031026040050f00c1403030f030060600c03040d50b60b40b000030710001602140000e061041c0313000350400c1326541c1c00d55094400d41e85201d640c40d020b0601c20352826002400c003140b010340505241c400740d80a2614a403102410040c02024084258046c42c60303005169400c0000b85142a420710510048a01c1518071045034103090410f000c00803101943c0d9412a00020010000600f00b50212200290f101407a14004071030304e58 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 686439685 1250 686438435 686438447
    0x302070209071e0c031d040b04050106050306121b01050a0c0506070f1d3102070c03020a050604240903080712030e010b2b020d06021c020703020a060b01 67
    0x1400a41000d804402d12024941000781104a4042c4101d942800604000211042c118806018000c100b039500920318403842c040808040c1c060213800800d1440b01003000c0340440b24240c1c0b000c070003e600031041c01520324101c0710710240c1c619610010041688241e000b036000440580c2241c1c1489000200f800500d4042d50038901619005030980d407041c9008900981480002101c1800140a80300794003080b4561040c20700c074140010b498001c0025409140641115034003c6241c41102c1100105810f400c140c0000c003403d6206452811901e0703c0d40c81030211414150300040d10410b020710080c0710b0000841d4030040c210101004201c00d150320401c091300c142d0142e0f000a82021400990311044c05091190703001c802200759003c02010101a14440c202c400244480d41c2c003000c4019801001c8010220612540003080c0d030000024060394001040b0a0803a48100d95494000c200305441050340c546000e081c0208070f00035071405200350f8000352205100320005001680c0c90b09403040503407043d0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 686440935 1250 686439685 686439697
    0x10f020a0e091f0807050108130b16020f1e150606071707060c030903020607020118020111070f080d0806040c0e2e0e030c0d021503181606080a06080318010302 70
    0x1d41c20f9044d0300d907a0b149803141d81d00e0045501103494640030400c05400d45002d066001d401071024480c544840e00800702d82c2041c040350400b14030540f05004015402400750005e03600ca078183c00300c10800d524480c24103202c0c45003e4002c1c0000c0b100304024260305c56404454440354890340443e0080004841c0c18014010103001030159440d000312064015010760004820350301030f80843e192a61101c0080742a960b4106903030b0845601454030000550080481000c4112100151010f250301c411241030741d04034079800303400e50740e1207040070079183c0381c100c46541d4100746c1c01d560a0160000c0103d010701942c1c0070396590b1f4000c008102c000c1c03038000b0305800c040a009010000c000e15850840f900108103000c126007052003405420502001c61902c500060a52503010304031000d134100040807114950402010710030002007800104080b18020320143e140401c004141100950800c00000c1c89204003c0c0180e50a034079004041c0440000003007a2609100c12800301404220b181c80105c019000f90 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 686442185 1250 686440935 686440981
    0xc0a030908030705030912010e061003150c020d05070303020912030301031403040e04021003140a0b030c040204030b1807080d17010902090d080c0106050d051b030307030516080903030d060602010f020a0e09 90
    0x300301030211072f000f400c11000840313000c2d103d0703c03140d00ba0300d4007503004650300c00c805038015922008800c2c0302103004034042c0884501a00340142030906220104180303003428509035845401c0000103008101c070403480c10000c82883c0000718113244c1032800c190303031181001c0c7c800b0380303d2042041c41201c0d4a2094000e542c0c002c8641602462500300004850060001c40240c1341c403e003c1d0100c003046905103842540c04480c0c1002c916016a1030b9058109408102951220303000d008018010400300c0c010416841040001d54426507254005820360140c81030682084c003003580100030710481552a80d82c00c40c2c00903008498a030341c650003a0b2600d401407082d40d10640e00842003060003018000e02003034000d16031641c1c4405807a030360384800c10540c40303208801000300420004c0c0064800a2030700c1250700d2290344a41c0d00300b440d04100b003000a25540001c1115202c1c5a16040240600c59083c05800c1c0c41061070399096080c46081340300034110328a4420709500403a84600040c00b4206030000054002c032030 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 686443435 1250 686442185 686442193
    0xc04060f121e0506030f0c0603181c0804050105070801120b09030409060b0c01060603020720031e0606040614010c080f130320090f0c07030e060c0a030908030705030912010e 76
    0x3510b40010090082100c10074481d00400303400e25005580415841c40030b400c010605860740e41c3c0d1500c15490b5043c2010494014810381034a05196086080300d601c42143c55119030605282c81d00d051800cbd220000c080b203040100c0311004100c0c0c10110364620020a5012045140a5070345100080c81c40c025980202542401c190000952051001c000c211120000000b400190745910058040c0d2250350002448100d5018580400d4271608200b01d4510b80e0003010fa84150041a81000e407005032500008281c0d0414130a002242c5010b2044400910505040201425110001909040407440060705902c3d00041c0e2200f610600703012030b80803c00605d1000302464990400f01d02e01140d18950342c520400b20403071455541380000d6400c0c40391070032041d801c410380c0d1101007502098201100807020300201d200182003965850340504003004042009003000149070400500180c92a8441b001c6038104110710030100d0000b00480700c1400b000e42e44202c02000d90030603e4010202504031140c0c9000d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 686444685 1250 686443435 686443481
    0x1d090a021f0c0512041a130302060c12282d031b0c05070803040b040506090607060e0102090a0b1c0b0622500604030c030b0c04060f12 59
    0x43d00001e80180c0d9242c0c0c030038640481b02c4c034107000502e01c0741c0120700300040034260f0200014a0140c1c018210f00d003c0c5410b03510350301a0345404191a8000017200c19603480c8298180c2e007000c1d48a031079001030703075280e00e000c20b105040542c2181c2d199103c8201a12170f02114009000400c2c000c0d008020700d0341c840b0001c01d2810b54a00b100910f040700c200e0080b10325001d45e030f10014095000000391402d498603911464501843d0004011032540100005500300c0740c24070509010600da03118580712136007190300140e6903001c29000c0203140c160304d8020301d0b208842401030005840f0908241c0081c00045040007176011b500d000020b030a4010604070310180000d041d28050701488040d8488115544500105200d059401810480700d4003130046c186500000c1d00005101d08103031020240090021142e0391020032000d02165803680160025200e10803451020802c020010000c0c6a002d03001b5a085400c050501000502c81020341d070540c1d04211258204c0303c22180396a10402103200e841c8250703582c1c90 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 686445935 1250 686444685 686444713
    0x20304170f120412020106080f0607081506030411100207060519090312180e04080a030c0504170c0f0d0c060c02041b02011b140a0c0501151d090a021f0c05 68
    0x1e40c0c0905003100550824000049000c1c0004450f2714051070341c80905060769400100312403040d00288520b880540703090100c080c649841000754019809901128181c0841e01d003404036420609880d4411036024986c1002400c0d44182580c0c00003004861480510014000844508900390800b070010002c6139011202c1a40150072660040121800c202c043c1b66200f4000c1600f510440300136205100801c283c44010b44070b039102011241103030410b2414a0f031240940c42e0600c000b200d450100c0d5018407201c3e285840c102041d0014801d089618401240c0d060765800b07c0d0803060b12450040c8490f10306c0c52411075403290002461a00c10f0010721008000c4088000c0c043e110880342c00c51003030310420010384c0c8944075416040402c14021140d502d0819013002c00c0303402c0e000f2444151801d550b0754044200341c0c402800384a0042400c8602e0f40d000103d44000d1b400c071010050003010707081e8010304980006803164509110160517400c00415100e601040a94521811081c000e040b8081d05401e4000c0b1 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 686447185 1250 686445935 686445953
    0xa060510030b010f0b0a05090d0c080d0e0f2b0215030f06011812051c03020309071e1214070806071d0306041101090803030f04060c0201020304170f1204 67
    0x164060400400141d130381e10b0b82505848881d014080f2a140100810100d0902070001001d0760b58010380800c0030504c11340ca859642a04941012200350011380103c0e6002e03500c01400c0030001c104596049a030b4446400051a08100e000d40b940c2c03076800203a09880d000014084641c1a503000380101000c54030780345191000703a2040742d003000001030000101d4600e51054084003208a513140d250701215052204454403841d020303030201d84134860110240210480056800c0340e110351904c0250300c0303042c8003120a040095075000f00b0b2146c0c501030f01044c06c030301c00700c07580c0c8003212550b1001d190340d1007079401c09942c00c07000c111840d2824440e540002884000024525104529990b01d1024021b0b074504030440d044210480ca961541c48000410301007103400b8190080c0c1d083c141841070720344c2e80d143d106038110b4104840403143d881d0400200014000719009103180818240300840c958641a621503040d050fa0990b080d401c00008200000e00b4600e0108407103010031140c2c6100021700d0b0914220902c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 686448435 1250 686447185 686447189
    0x30b1b03091f2018130209030f030a05191b03090f0b093a03090618030b16030b0307290307020a03030213150503061807020307080c0a060510 62
    0x290b94510784103912a5802d0300c1515406618500b0076400039110350385010040d0000d92414549001c08910894581c3c0c2e404034001c1090b807074010150300e4400210030142000000401401290810011490955400821200e484101482c6102240c00e07400085420141c00c60050b00c01d81241400401816002401e107030864880741001e4545135126800c4001c507001705010070360404030481e29500fa048220060b003440601c50000c0c018000c1e0040c041d0600030b000c0060580106490000034442e10b980640c0c07000354041817181105120b45141d5400c5505000284042c3d8105500c000d84154244079400c001880300e801000c441f50580c0300e00c0d199000400022034200d8000c0908100f0389416080300940e4440c10854001e80450390b91a00c0c242e020303501010f0121640c1c1d1510308040b440c0340d606660f00d240b610341c996813292203282c0711050268202040e070307001d000842d0b040300700107a059001013202c8059902c044002d4503158440400da21301541400001c10341400c0204020100c1ca0500302101 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 686449685 1250 686448435 686448463
    0xa3503010b070c0603270f061103070807050f03040308070e030f072907030513030618030206070c23010e030a050726090d141e07080115030b1b0309 65
    0x25065591100340c0840b48048600403440b41c41c606c441c4420308031091290030303442c0500114008460280d80764004c880c42840e08610016011090012050380120892750280040c10072903d03041010b2100140c50100a100408114040c400525041d206102c2c2100410004e42200c1c0309040395980315881c0c520a001d407100d0090400c200d0b20364441210701c0344141c5040c403100b2501d02682c0c1d8808131a01d601040c58600b040d14105000400100300d0f2003500c44c441e485d06006448410140340080c00e01c840a040c51040208030380045001c02d030041e00b0208040c41d01118803290090354081c0c5e501425030072500702d00301e000200b40b41d0b080c243c101e001810014841c1e882c41800703144d103220035003982000c00c00629080c04144035615150520080000c80d603405a40140016000344070303400d2130451001c81d984d03045c0c8404040c0000950040201d03901030041c1c10001e0001440041044038118060720014028560100101c0c2d442d20070101e20101120031078080540d02d1400080b0142d40303400d1800206 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 686450935 1250 686449685 686449703
    0x10501020c0105120c0c031605010501050109051f1110060e011e060801060305180f070e06041a040b040e0a11091501020a020f040f0614040e0a3503010b07 68
    0x440b58070880072941d00c00d04240030554240c0300c543c0d240d91140c02c0f0324a85062844100301d4045400d0f481031402036560f2084001058540c141030005002864683c0f040b4059490b69000c05a40820000105907045007490054440c0d001803400525040c0c030f00399500016841d100000c00d101640b058124161400715624411070b0030312900c200140415485924002400780006115140c4a6081503400040c10400140019025480341c3c0c28030305500700152a503403111074201f149507502c0d16155406542118100503a8900003541c0511982e0540b40911491b0745400c910555940da40c881030500e1444021139001c40ca0030303d041000d101c1c8007903070180f194140301c000a0b900310110080819075001a4098506400c0326800d001c080e0300c12403d144e9001ea25800000518052407203101c0007411116103005510240c0c806000c12101007682078891600452058004030780723060051502040340c40c00000507861202201125400311080c007600e1802d00100014483c0310100290850360300808140c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 686452185 1250 686450935 686450953
    0xc1e040906060e18060f060105071514011505040b0f0403060612030e030105040c0e1915090e06010302030604080304080c0601060815100e01031a04090c06120606090b09030a0f0b01050102 82
    0x10824454505403407080340d40c40580021031014030011b05a0f0004818103110f81408015030321307080104200d0328025070803681d440c00340744401e03901c551030360040c01c40c0142481c640c02d0b1900000c04ca4400c6000303803410a900010101003240c182d1048a0065400c01d0302082115100d0110f6140e058031000143d000902c4680400402c2c5410b200391401941d000e801d60070f01d03a00d000510985d62400914025503d1982c113024511aa828050354000d02100032040c41024100f140d6507080310340301804030303500d51311681c01440107840029030250880e82000b14551a6611480d0048007441030b060302003c03034080ca00000036420340050307d20b40150400220b94501c020844227000c28401080228000128058942599540203600c04507540d00e8106c003c40640042101007000e98164050807610014200800c000040d40098009004051604280803162802c4001000c00e4a58010b444055400042011450f074040041031442a40508a0303e00710700b2905265201e11002d205140c094000c40e054 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 686453435 1250 686452185 686452201
    0x912090902180405040213091b12170c03130311040f05040b07030c17010f05091b0403031d091306180f060b010e030313060318050c1e040906060e 64
    0x2e42d81980c8580070b00c02c0400d0010030401c0007070304000e40180c0c3c010005c5080190700c1000340c0642c510150080341c20b230302c1e041c00c0b00f00d51840800c6180c0c40070a820321540044030000350f80500d001c5110800742c11158a40d030203041e446003584940740d2404843c040c0070b40300000308142e81900c071440700320484080180800700c100c0d00e410f481c400c42c0c00030010b0010200180520f03009511441e01e802581c130f4503a40302038034880c041040100c2a00306108401c40b16404220901c0e211160301d07481a180340c1d06c1421305104a1b40118240581c0c0402414450a20103680d54880c01d51005000d00c1d1004143e2040760030307c0c1c00d0884544c56141c009482030340c100700c1c00340b00303d50291708203501c182e41c0402074219000a40d11000010074200c1c3c81d09040120107120090182da0801c090846c45254266000126180c1000601286c03011240d21500c3c251071030a40f40030a2000c204804515810344030180300500c2c00103a68911030120024070b51081c07906000e6414003540e0751141090351403902c0030340c41a403142d0031 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 686454685 1250 686453435 686453437
    0x50910030b06010f0e1908060601020d0c0809030a0602030c07020a0807080a061104080105041a0105040c080109090c0b130f0905100b07140318041503020102030a0f0c05010912090902 80
    0x2014120118100126096512400614055420300d02d849920640f449001440d01d00f9001c41c218409901d600d028040f47d40305100103904060309000414842d0031103079000c2e204000d2240c015088520129210758180c409000c0039000d10761205003150340f0718000f03201d00640d4121403c00d03070061180000200e014480002d00000345c6001d0801004002126035441001d055551a40b071300c0d816042c440029918404d001d0140110b1141441c2c0502054822581c442c01030141e1055104074102003251070055000110303075043d980300c0c2c0e00110320341015091485d4840d5040c0c0c01035801d01c0000030301045408104003000141e0b030f08010141019943c3c2d26054041d19801e032100c41500107003803010801d02c00d010340180300782c52140c3c422a603484220322041e4110b4114550b40e182d5500c0c2040132501510707081c4101d5005414064111000c1410358000039070b40d0082074201c030148100c0400d0110b2441c0540e00c0303101003e40c0400240401a1945004201c81048962400205011000100725030502d80 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 686455935 1250 686454685 686454689
    0x40221060d210504030b01060c031d06070305030903120405060709080c0a15090f0905060406150e212407080106021b041404050f06010b070c031101051c06050910 71
    0x10007460080b1480704000c1c40116204a08002882002c020000024100d1040a4002c12054441d00742505080c100906640304086402c04c0001d11440302c90440e503185025942c6050b01440d00741e48035a1546540c0e813440c8290001104003800d80d0f0104001c1000000300d040c865040d43c3e6581c8040f03a40c400c115591628145100d941c4416145000e00003000301c41202d41078125540780840c589a41e41800741c144c0b80c0a9007041d480f03a41ca13402000f03d5400d081c090440109170084000d402c280441d540208030000c00740d8810311640ca07150203407218890640508200403498416142016820304400b401070f0040c80c0c2e10000c40303a1100024403e43c1c040c60300076040f1810b940241c00c10104055441d540d0016245c07541d584a6603d54030744407140c112111a0344103502c034000511b070944103068a10b01d0000c050388651041d0350100950400100d0308910769048039030080c10100a59002001a0f41c180598078034030031034010b40c01d03025404081c55003102044640549180345140c50702099848281118 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 686457185 1250 686455935 686455943
    0x61c1a0d2a06140c011b020109020a0e070e0424082a0a06080405011b050909010f050d0b040503120906041b06082e06110601050913140a02040221060d 66
    0x2440c004075140f0403004000020550700000307410020303801c5841c02c00c4845041080141c1d50303480140300b1820b0141041024002034000c0e05514036149500400400070520540d002d1619001850201c00e250010303624400c85c100006008652203000d01641e54280455911146a2441c01000003000b000c500d2803061001603e1290810700701103007035880c80000f070f10446640d0750383e000100b01d9044050750025024225614559600600c1041024010060f00055020107403c441000190740d20010b245042e5031054660005aa403800c005043d4040d0075030200c840e540e89c904205030301e03c004c50054483c61140401c0d501900d40f03032800102c54115030081c103010811020100f440400b140b00c0000f42c040da10488000094401070113100d40311444e60250700070681200048485142c284203090140806690301c1d61035180442c07101d000d000100c030300900070310307004562a2000e41c014819000d54640280055680d41413608450300d0f8942001e03500c036143e208681c040395451802c95600a049604 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 686458435 1250 686457185 686457197
    0xf070605010f0f0b030c09040c11100608030d150f030804050321030408160f03050406020f0f0a26070c06092301080907031703060a05061c1a0d2a06 65
    0x4298102505902c041c206c000908001e000c0c0c0d0300c8560303550040b0980c0341c0c05551444c1190300200f840920303003944000021406820854207100000002060322580c2c2d00782070303001c1140d05080020138120082c44d00400424807420002109200d00c140050045910a0b003c5484000c00510028004103441c10043d02402c03042010802050303041e800350081c000c0340301c020032880381181e60341d600d0b4900500e02100030480119003001036a406001101103c00280c000d00488041c0100c056264060840c00400002041c01c115007034810b41040e009000b084440b5032980c41201d410048241251072103a000000c07a48030002c40c603072465903100d0a000d06282400348034a85039400649082c1e500904a800c184511000040816036481050302d042428072b40b04c942c0c90500c5424804000440d420250059400b00030990b20080c0c4140c00805a192013200000c200101101c41c250951003580c440e9808401d03a5005401c2c8040401005090140f101c0c0c0d2070704120f0801420b820401c480e11440c400700d01 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 686459685 1250 686458435 686458439
    0x19051009060204080109150606020c0306010513060e07020a150c080f07030b0d03120c080603070920070809010e0a051e040b1807020712171b030f070605010f0f 70
    0x5a604a81140c9200720005810719441d850054211903e0398015902c00caa040b9170100c042d0720b1849440050292742c4080c01c900320075000820303641d403c18800c5e00d000307400c0b400c4481900d41c65588a40080e052085041c8690706009900940d55020700005484804100c0040f0440880a20441d20b00fa0581d48900503d41c2e2060202056154000c0010051688a220b9548030baa2015141c010380e500c00d881c1c040440c1d1400b2002c500315100c4c00644800e010b00001400b0003a81d00044101c1141c00441d004034034050410f105100c1c100e401e20000322122030200e06802081020006400040401e0740c0d0b4501d521410400c11005403280e02c01c0c01d030021190729114071081c03681400c01035401005040400e40c1c03a810f002140300394075580f6221503184012800d10030905d9040c040f1000421480075803070382c00416508c440414104005212100450000e4004422091280e071508002d0020042d030b0380741d1104039030489143e48040e80031142289000000310321005580010b00544020700d0080400d54 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 686460935 1250 686459685 686459713
    0xc061012030e010c350c060f09151305061317071b171e0d0813020907080603010612050a020f0105040f0906090b040516120f021b1905 59
    0x24407525a0b060400002c0000d010206901e81d82e03000110011002101082a1030b50040c0f0641440000c03c4032841c1040081184010001440a41002c08880d4000766501c3d8682c2803490b01c040460780518411640041140600030940c004d81124080c08c10341d00c1d19079070070702003011000d080c510003060707050854000a03441440d07002400480b44240009607034000fa4100462640d0540d5102c0d10381481e217400b01c407403a00070070f102c03000185000c038940ba03907400c801405154580b0205214481001003010001c1c0f644408040c58461a6402070030f000000d0074242070007841000d007294841d001c0e44c2898400201485400281180d0a0b0040c0c050700600c1080e81c01c0001114903080003d0402c0303810b0202091a105602c2e143e4014200920006a0b55140600480645019401c0584290314090401c601d61004100d6050010220315000030402400003050b00149a0034640e0010b15201098100500c007041450903100e41c04c101c116852108100c480c1907040241950041c00c030341106012501007 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 686462185 1250 686460935 686460947
    0x305060d170a0e130b010207050d0f0b04020d2a1a0d05060604031401090501050a020f0a1215031407080a080f032d040c0e011a2a030c06101203 63
    0x82c5034618103007411010450005032402d088140c1020b01036580c0e260301c9025a010031a0b840200403d44c0c1c6640040041e807102884000c03803000c058680307941c032030003c2c0031980c0340f06803c10055440b0b1842d0440400f403120b00310f0006050020313681441c90841c4046030b070211a0480410003411a0742c0b052400c1821101407000d4907001c0c0003560000c00500001c0001961b90030029807102c800000020360440608019003035420180c403400c07550f81f04001004010180d40101c1d07080441b83c2c1880740d44050711004540091002c0040001310b60016100482041070b001004c48450140d1801c899040e901d070307010180c850101520041034010204403420750142814041d607030041201c2d0040700c640744049000c4418071410385e1000d43c4458504200b104000340c0302030800160001010142c969030400c000c001c048180302035045070400707000c0368020304001c150fa900c44281000a0140c1c0808030070100300740c0d4a40042c6013101e01c1d03002d2400002d0380a881d03503511008441c5079545115581c0d030340391415284 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 686463435 1250 686462185 686462197
    0x60a0309060b030d020d090e010f0504050403170a0b030105010e0f071b0b070504080d020d021b0f060a0f0f0e09040305090636150d0b03030c070905070305060d17 71
    0x10181c8030546040d40e6601032010320516130700d80c0c02404100241c4600200404c41356040046110220401802010f8280300030780305444080d1400a0a43c40c1e03402c054401c00e840100842501e00c0c2d0340100140e040d0950041d0b0341101d03081e4001d00c00e6076200c464074424960304982500c00050301000040c0c5031803184c00b906641e00c100041350b40c521443c1d44c07561514102d04075044008120009810004840c00300310000c00c90401c0c0c4054101170f040003000035141c4007082d420021403941b14005912981c1d5448a6044008008100640d250107803a400350030800404407203000b0440c42d50202c0e404a0060040748404a0014240f0b580e40d038441e03406556980180f8403490700200240660356003e003910840c3d400c2e1207a00d603610294520f075400038004030101d40701201e0080e10b4407603405c2c60010180c1d050301c007003200702600421540342400100c0e1560080400b03540052290540c009500300303260f440180940b190350340900c441d0740c480041c02000e940042005007100014042060200140000b90203 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 686464685 1250 686463435 686463443
    0x302011b090b090d080417012003040203070b030903130905060910030f020d031202070f120201021806030406020f1204020f04020306030c01180807080618010606081501030209060409020712020606060a0309 90
    0x10906d5100d07540e100780d032501007000580581d9100e015000d20f910382416804d24030108020329140d4a496400b190300d0344103d105407041001c020010541c001c6043c0241e40c510400c2c080242401d03a0f8401c11305015010984d07060340121410b8010501102142400005072030f0440082c102c0500c80f9400e0042c015142e5200307408000c1c6190311241545c070140018204580580d14410a961590500d110b0b020300c26414042503a2040148d01c00c02c2c103030403038141d034007090171681d8903101c1c0c0d22410000068414407035242c3e40300c040000c01c1e01c20548042d0800740030f10b0003510000d803180a404188412440203554196040d0310200310b0300b02d82d6100e030f009920225200741d0342c0c00c0015501e44400d480c10441d50041040c503001542002200c0404c00c240110301300314a070003403004520b0702201810094002c0d00800c0200790035000c051050340650103d44003841c0180641b6540ca6480b40542c1c000e400502048170980c1ca0442000d2080d4800103c1c20b00643c0000c0a5a24000110405500410031203004035 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 686465935 1250 686464685 686464687
    0xe04060b0a0803090114031303030b0607060219091a041223010902010201050f040f02060a090e01060509190b091201090210031b020f1f020c06040302011b090b090d08 73
    0x104191100401000100702142c011a2502c2c0081c00140c412004002c50f1000d09000703104001c0d1a0042002124016405042c00100d0307c0100001c504c0c00d115080020f4a01400050305481002030324014a202c040240d650541d1940c8490301200c90700351360b02ca10110590306000502c0220b0070008107403103007440751024081604503100040c500c42e41001301740200365944d00600342956020301540e90b004100900380e0102c4e00e8203036620052003a10103c00381c0503076008142e11000500a51130301d07000d07101800210302d4540c0e441000401d50750102e110180145451100c02c0b0318035842c4042041501c00c400191b9040550050610000c800d08240c1054590740b1802c071000540c942e044201030140551740c0106801e810518131810100c1c1d035000650440d4846003440c0749069011624140c056107060011070610b03050803250000e801908038001d118040e03881400100741d01580300e444540e0100c1c49600e15644403440582c0c17108524800c40e0102030b01040544a10301d002000c0c406d059108403522 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 686467185 1250 686465935 686465951
    0x10914010f030e100f060501090609150c0212071211010c030215060a09020f04141f080a0b041802010801060f09091d0a0f0605180d0e0a1503050114030109020303040e0406 75
    0x7290a840000d01c0900c81507907502c00031f01080d41e000036524050515801d1824800d460000e40700340d0002c01294940400c8010b001c28811582d40d268942c1c5260a0700d002c80e0241b42d15801051590751101c0b804840e51300115070020b00e6540104081d8100a03055001340c4090300c00000e444011000051005501800c441404203c0c903a241c805030624a071003e804c240c96a08200003c0c4003164042c885611800944445107010b491054030150850241e140050003038840c22002c5003d0500c5a00803036005050001000304034969030360620209000740e170b90345200d1342e81e00d505958005420303032290001202e4500500010b106a04240c0d43c0210b10502030807401880140c00e418400c02610031518004d105070700d0301c1400a44c2c0035894000c209841e01c2c03040c401d0405030084d502c003c501d1482c41444020381c01c450269688040f0000140041c8500c2d8060002101c801001000e0901904206c060741804030500c50070305200d20b42c0c0e2244d010700158a001e04110f0302c41c40e00c03d00200111212600d40d205d07 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 686468435 1250 686467185 686467213
    0x90601030e0f0708010b0a050301140c0702041401090b030105061207030201080402180c03100e0606040611011104080f15040203031204060e0307080403120215060607030201020d0e030405010914010f030e 89
    0x1850003003460b03400018401b22920100324201c00690b01c0944a80c0c104044007440c102d01d4600542c0203000700003601c0d51050b0501c0820701600400e0228250303144540c0c00012505119041580c006204074003c000640e94002000329004000c00601020f034840c50301840154000c0400320340140c00104080c1101c000b0201c0c64103102c03030480711002c03840c40c0031041c001c2d082e01100b160406081c031041c1440c0300e440d106010a001d4000c0f0f114800422205908000c035015080d440f005160160500c407503a52a210031000759283c020860b0002c0e2440b0b5987c004c1425071142c8a840e010f10340c000e02542ca4610100680d12036244050402c0d5180c039621008072004d800204001d00c0f0052085091580351465814984d04c4a00001004400e6400c42e500b049088501d0280495000c00304442403034a4003070a0404030300a005100d602d80c100da01d4840c1d2001d089000202600446100340d9810b0a041d4403101c41c0300b800300304080c0e01400b00d42c00260b050099402500403165072183d00040318207220385001 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 686469685 1250 686468435 686468443
    0x61211030720160312021c0e060d060b2104120305180712020108011e0504020d09080d020909060307241b0c1404020f070b041e060f061202090601030e0f 67
    0x4400e0800c079000030800c01c104038003180170044148250014000b007100e028416980c2610120b2405e0030400d01301088203082d520346040c0c030f540d444101000c0140a03228031440070280c0c4845419030700402188440108049040102482154040602c00c1140385000054016200142402031841943d004800f1541000c02100004010140413100d0100003800003612001c0181c105821844401208500c200400e48010040b24001c0d24010382d2034082048030b5009115500c1c2c02001130400140036103040b0601d402421070000304880d900566140e51003055524119445540181c1c0c003035403a0851451403c1702e8000c2c01c4416420240c0c007000f03150b000c209850614880480b80c0030150402481460b68450100c1044a8151803c601c3c00364000764402c101d000d8403100805400c200300000301001114600c03105e0010076122071400040e864501480a00b189131880034445140000004088000d14121000650090111500740c0c0314207004401074a401400789031144a20001d900300424204 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 686470935 1250 686469685 686469703
    0x603100b070308061302250c08070905182d07150c060b01030506030a171b0714030102040f090b0f060d0605030c151c090516061211030720 61
    0x50f80da0070305031405804002d560b0510000a4240901c140113501540c01c0038450081b8158580380c1d03448200030307075150001d100d04481d0840c9245000d04540007072030380c0c400e030005030003800010201450440c1e035260569441288207603891481402d0103408440304142c0100b0380c1c014030404145c03080b25803039015401c07070114640f001d0000189105480300900120b841440e0341c0d50024a002d022504103100020740da00c10040c03000d400611110225600803800308103c45204050b0840485c60390000c941d2203403038090740c1c4502010503c041d031002da198a41031003202c0a45160302c61011070503041c01503010040c42c21100081d0422070105000500c0d6694501500519458a0b80481c0c2c00e0304040905042c0103202c507106010707003450310303034181200111016141505000000d100445404100d85c0e40948030705980601940603900d021507982c141c210302e000c150703046500c0300c01c04c001c0780800203402c69401a401c4444240f05001140701940320b01e08090602045c00b403081303007200300b0003c0941000c1040c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 686472185 1250 686470935 686470937
    0xf04052505040c050403140a17091207030b06090106080c18011b0c1508010b030408130b040837080a03062103030b01080903031f080d120b0406050f0603100b0703 71
    0x1080070810044040c90b500d106010610180001c00c0c050741e01c02489c403509400c480c0d90801c000c20301d1000f5444030902800020040e030116000140d50741803500c5031601c1619428050701e01840045940e03405000c20134098940c4c0c100c942c0c58200f0022425415107004101c19040105285040905003019100303800101c0c042d07840e480041e80342c0002088840304000d0303010244130005004000480c221408d490344290040d00403661643c0c1034940c13466181c03080d00042c4204134040f0340400c0714003001441e4050010480198004022400551042c7d0024500400f02e039698680700d0000040c00c800c00b400d060b401da800c0101c1c00548880784540c4800030480107420702c3c01d042000c0340c18141d00d4000e407000000c0a0800003103c0c00e000203140d40342d105c0208004181078124800900b0302c01c00e0740a24000b80403d201b5030350440305154006203e074817030b80710300030155040c50388481042c6882c0c4114001c4500c0240703201305810080003440b050b13800007050b021070b90402c000c0008000035202c00a0a010f882 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 686473435 1250 686472185 686472187
    0x130804170607030606030c080114040608100507020c01110c131506030f05010b031e06030a060507200601120b0a20040317070f030e0f100c0203060f04052505040c05 72
    0x4558010200c6413168426002c16080010441c603ca42008209054566494070540c5a0b604400807401400a540c0300c02030a100d2040b031905521b0841d030040f4010400ca03030a0328103c0603494011920001c01030307101c100300d070441041c2007000d1030101c00003070901001d020f01040c038030035005100740c441d415540f1210220303442d0052500010050311500740940b09002101d421030500001610b000307100d542d5119012181000858000d680410610481560126040c0054940004010010304074810560100c0a01d503003001c514103804038056050386c16103c0c130214640e0308c83c0c072160307249172001d80000c6c15690790b5100001c180600c4070b40100b1000010b91030320f90380d525620341041084c0842c440200d2105092040700c0000391059900020745800d032500c50714940c94800040c840e0940c17200d80a502c07091341c8a42405441e081100c10381d9441c000c81c03d44401d0703a40c406806e5180310084a0003009034001511036606400348591040c0c0e0300d03086600c00290991104041000ca5841a44a070b0110324 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 686474685 1250 686473435 686473441
    0x601030b030d18092a09030c06110c040e060c16020a1e21290906011802070b1f1e0905010605090a03060b121b010e03070e1308041706 59
    0x140201daa82c00618464000300921754501081c4d601081c4411070b100500c1003010544a038162044030b0700806140c011150121480c1c1c0d03100050500c1c004000301030000e02801850720f01514242c410060344003c4040604404d40e00c05400311040c0e8000c0850604481d9400c00c0d03400541c80d4015403001802c5a041d920600c0c6c000585410800348240c0d000e0b40249003100030491144148180400310a648250b1010107041254a012004c0c0c04441f0f06481194080b41000400b8100054884c100c0e000c0d4407107600006450f4030200145d1140c4040582600b06007400700d034003000240b607920300f205a00031020724410340350090f209aa41301c80d80e200100b010300305414058240300d8030078940108690300340540b50040501c0841c0f0014047c0c84041e0020ba503e8220034641d8031502e140d59183c00c2c128042d996101201c002c903c00e10341d80090700e980040c0e1045401c42c9282400600d002c242c90b4040301c0051a9074500e450701c440f80501d403008030b40d016800d1100242c0b86420740d071095000035400024103410b01d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 686475935 1250 686474685 686474717
    0xd0e06040209090703080901050d06050913060b0105070b061903080309240402030d03050a020d060602030d0c050324030a150b1003050114010c06060b0301030b0a0f02070314030601030b030d 83
    0x60b60180c01107896410001c0c04000046a11007200c007109000e0800907151162120ba40008004560050b5003100410042256008070381c08001d0405d489007404005c0741c0100001162940603c0e0002814000750001007001032911401d2070070b100d140a0301620a0603100d80e2035005940055030030400c0e03640b00c00350542406810840d03010080015030700c6140145050b40000796035040d11800300040c15594000314240f101c854040700c40e0759030301103c103218966076800d00079543e07401200a001494a4802c009500710b00c00d40850b405081c00c048245d200d074014490701018500c4588c45190315108804035140002d800f1580101058948200054440039010a2081d86000b61800004051602c001072000c4e03003541d00c500409e05001e10b040c940400306850301c0da0041c61580c01c1480302c80e0001c400082009580a1050701c5458030003028001003464031840c0d03090340128140100401d41c4102c1007026a01c0413405158031080514000c20f9400070307c00820f080102605030b41000a1074050522110 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 686477185 1250 686475935 686475949
    0x34020d05070302270a0203160806040b120a0606050301020c0a031b0215030402040b01020d0f0f170f0105100e031203040206120106020f010b0a0e06090c040f090606140a1409060d0e060402 82
    0xd02c1d050006d6140d4074000b03403495030303070656089000c05000d01000800e00503116540800e0780004090000300ca81e0000c01000b03071303840e00c0100d01107070000e003461808243c0b81010700a8594140b5900001d005407a81a076042e10400d510008441074625054907240c090b90310031100b4104843e46403401e582e01c0c01c090040c803066400c2c40e0360180c155880068440202540203080c20f0040700b0a24140180e207004102c1121090130390800b40d80c010302400244214200f403d0600f90403035104644000c2a008411410fa54003089031884642c1a0410150b100e2001031041c010b40d84544003c0c20039140c4a2000c052520680c000e810001c0140d11081c207070403008a003442307149108a811035840c0017044c40c0c8107410040c290000c25490060140b1170215141d03181c400141d802403d4072161060086441d50001c1c4000c03c400e104800009440e46800e0b0b580030003081c00c03034034618110303501c03101d80f03d01c3c02e00003581940c03281303c505030000401c020b60f45909005126220245605601501e01805c0900401c004 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 686478435 1250 686477185 686477191
    0x2120603010507080f0c0904050a0b03073c080a03080f0c070b04060903051605060610050301061211040801060e0a1a090f040606170334020d0507030227 67
    0xe40e142c8070a0024498000c42d00561048601d801540705540d080030340c1d01c03d4016607402c5600301d8281428040e10743c10030b8000a440740b0055040300c10b9140d40d00501100382001554540f80c2400a000d8800505540c01d001030300d049c0381c10780040705140d032401082c1c41c0c00804801640010440c00c00d202d01c2e40c80291629400091003c03145017003c143d43c440503464100504007d00a41e80d8803028001c15000d40700361001410b00c29100c821051403030070400d803665422100f041c82050741400d0584054007800689040c2c0710705036614060881140a440300809460f05070305913000061100049504090151a0103401c0360403116000303091000319101981d84114210001d90800740e08c5075810f03255115566408120b070302d048400ba8079241003140080c40142c100c0c8401040a003501c15031070304000021f0201159000c0c440d025a206100080942040c00300059441d00d00f418500c0c016141004141100a0240c820347e48000c1c2e407030703001030040d581c91002140700000302c04404c5522440f80c038040e98 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 686479685 1250 686478435 686478439
    0x60b16030e09010b0d090c09060f08010506100c0212100204172404120c1b030b0a0c0e0f1801060216060f02150a09050109030e030f19080a020f010f021206 68
    0x4603d5040504010682c000e55200b80740160341c0b8203201d030034008481321640003072070740c180d0030450030b6114068900f0031030107030148000c030f582007102103003c07030601490056001c840b0783c0e1140340e0f04c10564204540c440c0d04800f4092180304078501150481010b1006000400d068112011132151540c0c01605100480301b0054140d403009500401d44030300340d150264025441072900000000c0b10500341c900d10280480944510007074000400c00c56a42c9107140b00f0380340a0034480c40c043d500c4103480d6042e9014004518001151050074100a090403403207001e0101c401403840140300308220071074840e440240d2140005900020395001182d0b02d801508014200300d180c911001c182c0848003960740c20448034440303111410b1b9000200c0306a8580d0010070f806a011000b4407d040c01800c00a20310b21a54590611900a00c0c0e060072044000203002c103500d500340d4828010342c0000f5111103c46820080800c819070007a4442000464800c2c812020000c000131001a02d0714030220041e20160b4004220324 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 686480935 1250 686479685 686479699
    0x301051f140907030c0c0807050304030b061f0f020c030307060b150c19080903060f010e090724051306020f0607170411030c15120c0403120e04060b16030e 68
    0x2071001d46a900d0841d501a0082c1000720f180e03604408120307000d03d0105409024a400411070104002c0c003c80100b040301d001d03524154482d1654010807101843c1d10743c08150481200c030100b160217000d400314051803482d90050b13510784841c1c2408642550b00c0b401d0211043c41d41c40100d00070914181c1440b81d2104c0451203c40c0c10a0002a4620790700e08101d1248460501003542c0c0404010001c4215820100080c05031000c03424522025400410300b8080d80c26640c0d0484002105018001070020480300031035142d1050820070701c941d071042070a403000042007280c00c01551142c0400b00100000402856004114454504031071908100c0050510340c10030080091104022100340e0000d900142c00c60340365070382c210036030000a14201444010381d030803403c000c000652482042029068207100b50003241d03a00d43d00c14580662900c5a030100604c3c00f18502c201d0900135110341c3c60a00d4408028000040d203e4482441c894140c020300003a6018603850715004c000c0650000040c00103c03025982c03c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 686482185 1250 686480935 686480969
    0x2070b06120a08161104061e090e03120a0608060106080103140105061503100e010b0d1a010212071b030f11010806090a11120901091b050f0d020f0301051f 68
    0x15641c42d03c10421310500625000070044240b1040d00080d480d5284000c02c20800c007a540c41c0c3c007117912070780303039550300a902d0b80b901300010b10300c20302d028515002040c8005140391640030045500d241c4001f40038191344e565241d8010aa0b09030410515010309030544810320745600d1440c0c18808000030036402c5450b03074100405d01617141c456507005403103080c0243c0d000e074490380c1d07a0300603d085c100307075501041281540c0d40c000070306c3c00140c00c001e00b5031610010f020f000c254514032606007040d44466a60740143d200000184280b200310b40031342290303403103409886485041c0f41580f480c89071040d0000c0e40c0c028800d18a502c1003296602950500820078209801503160080000e04600c4004082071070140c3c4610441c958000110211400e25000d050ba100c86801c00000c80e038000c20441c1c40840c1d04580002c0c07503800b039016070440c1104a80000703100da418120700038180415846100022a048869a90480b030783e07036820300a60f849090030040d0100c800410845d400740b44103ca43c4040300941d070180b09 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 686483435 1250 686482185 686482193
    0xa1e0c0c140a05122d0d050f0306040509071a03220b220606030812280c050f07030305090d090e0609060a12060906050708010b0703110c0402070b06120a 67
    0x84400b110b000704c0d4504140e0b80c2c00e0007828100010780d02c10001114241395030202c0c0481c1c28011900080b0000c00701e4408520303500040d944d92040070041e041e8144103200050316840c19030005940a030100040d80e80c1c1c560344183e014021070819803920031ba0400070003000300008941886221402c50310070b504500c0d91803520303048003080d40986590000c1003140c02e080210204070740c0c8a001c140d888081040300680c3c03800d2402068000f50703454031004200901007654010b41d0380802c0c2c603000110159401c80010081d0940040688400070001d100e000e05c203005003181d00d807001c1c0126a00036200400c41d4907111903064100842c286901091103081d00042c080300da41a50b410798896401d54a402071903c030300c000186150081d5000c800311400b402c0c0c8006c108812500aa400684640d009002a8450400940d0041000d000c2c1d107002001c14404400824450308203030030100c1d0020b0a4403d16400c0c3c1c8040b4060781c0c42114140c5d042ca80c650140a91420044840056000c46201a000a66081d51 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 686484685 1250 686483435 686483449
    0x30a140a08040b040c12060b1203091e0a030c080109050106050a0b070f05030f0c1c03050408070209041110050c07090c0e12030d050406050103061404050d050a1e0c0c14 74
    0x8058041c01d4140f00080400c090110140d001e400e5248800d5540d1245161a00242c2203480e6020f0103103140c05000101c0c040000251003900000400410032111100503a080880b44a004242e2002c0070030070020101d05020b1410024122810000c24841e42c9800e203282540d11681c044c90013184882c0081006890000c2038480aa0b8040d05036440707181d16041991a5000307030805804a8200050031003800ca00005001084079281300600ca184804050280e003100c1007100c014050080402200700180307814000654014070442060311708008007800b1541d01d010b021195808110300181c0007007640d00400043d0000c00d0002c000f4040015800c10045c00c0c4080e00c40224082d000d0180684103095061081c1d64030424064030801407841c00341800809043c080c4400d03a090b5203010b81035a0148401d03046240b149402400410710000307054801c4505502903001002000001071040c616007207a4a010a00218180d460412102c41801c05c0850345030300d0b6000c1d0500c0c801da0b00e145141500c3d20a = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 686485935 1250 686484685 686484691
    0x506010501030903170108060717010f050603090f0f100e030405030c0f13051338130209040b040b060a060215130204150306060b070c03020f060f0a02030a140a08 71
    0xc038020815a10703914090380c1600240d110176682c40504030011a04280000d003003440740201d5501c0798108042c050b41402c0301e034420300030360310400c100d420284424204000255080302c85001211b032440041c1441600781800400e5240094201c8503c1802041071030045800060442001d1864a032030400060381d200080c000c1d0a000304c06074000d01489545c3c0c040c40d002408614001848a4035080b103102450300040362045914100410075220001902da050121400021180072080e501021452900d52002809981c001800954103c01601d6280c2d00d14007a40c0324118a81590405250506203080d00a00850003580604001c00c0b0890f4001501f0845030a100d18401d0306456042d4141c50450354507802075046801e010204a1128254840c8401c07a40500300401c010751f04c03240d81d0a21841064006410030f06440028000f44c6481d03442090100302c001c000d070341340607801e641045072a04104030100c09a00040368602010b0b811000101d05184504411440d0000c40c003000341402e0405 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 686487185 1250 686485935 686485937
    0x16141206091b1605070b090f040e01020417061602010c082e03052413061125261b0a080f090112060f17100501140306130506010501 58
    0x80045203540d41002c080b0120101d0403400b00b583c41e02d807083d0914039403120b80400c540742c1c415802c0000d21001100151070407604010b10311403180c0381e801d0401c8043c04000340d000b04995801c000c006010b041218064552050030b01c040d00c6149881ca551461804c1042141020f42e414010404140d590000320150f210758010300360442c80c100c18440e000300760125902c04400841401011090002c0002c4022880b9078818090f80e0300040400c44800048040c0d414010800e05a40340100040c8607401018007602c1e141c0807a0300b0040a10301000d026840760f541281007952204a0009122021040181c41c0d01403c1120740039204885200c1020700c03403c448000c01c184244094000b00c07401f4440e141c02d164000d0409601ea00c5c40900344200e581c0400240c42c0880d444207212014001d1501440c0100ca51a82c059004145001c501d0701c2203035400843c0071030500601440320160015441900d028020004e1008014682002410310301800603044c40144c0101200750700000d94000390341070668400b = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 686488435 1250 686487185 686487199
    0xa02210307031d091801050a1e18080d051807140f0409021002010f0f05010513020309030f130501080a4d03090c06250c0e16141206 58
    0x2114840c0c03914190b469841d840795808081c00001d100517031840d8060054a0001c225130345424406000301c8001c0001b03050a10441104904400d900341d11280c9080d48030b0034010b003280c07190b91b81c040c190b038400c110072040c01d59a0014050744982c000180c4a200e00004000c05049080060b0a086060b0440d107880c41041c4051043c54544c886400a084e110b90141c0554a0b0b202c00340c170080d01030115074044c0c040c403a240030004554851180100c40c121040501000e031801e01079111b80010f548028007164852104201a04d62104c9060007404d42401c40020705007a00d0400d40010729220020340306040079410b1200d401000710540250303029107101603074111800d8001c008160300039901d4110010f542050004188051443c03e0001c512a803465026155044d0f020801c010503801080f0400d501c800034510b590103407006040b00610524025141e030803c1c03d5a81c13044004400c41140d2a1b05071b501c0c2c41c810014541c0c3c014045000d1013184211040c240498400400b510103002002c0c40d2007000 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 686489685 1250 686488435 686488457
    0x80a02131811030c041515030b10020f060106050f0318010b0d03030b030601050607050a060f06051005070303060902040b090d080c0a0f11010c030e04020310080f0a0221030703 77
    0x4041c0c0c0200c0441a1069030350140712854149a09074942d80407400e0b009001d04d40c0014a0f520b468400e0420a070b44000c001e0214a09101072030783d103c00c1c415840700906550355103403000d507940d04a0318940c5040640c001e000b03880d4440f462a05021041e0310603401d01c0010700c02241044000402e5a074048094038a528400d2022032190b4050207815541c10342107402c50104805051741034201d1100947c055088504e5640d031a000e0188a20407210041c00903040310200c10001091740d04101c82401d0341c08000704049803101c001540040c0403031052000b00304006107890403d501401850003c00c00840c045080070f207031000e04960380c460301d10807078843d510001458003040180003e603024041080300300c17103e03500a40b4012840c11a4502c060300d0340906e0130f00d0082c503984203e14000707110f03038150755888864400300c0c10300c00a904054828145100301c0140070400070410007002080c80b59403002000c00304614010b004154031400061546040080035001d1252000411555040d030b05290030507a001c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 686490935 1250 686489685 686489719
    0x6090d061113090509060601021507020a020a0603020a030b19060e01121a120a03020307120507020d050102180a0806070513120609060b0429060f120718080a02 70
    0x1000c0710010981c04900400d048100700c1c581c000000c25078180503c00c201d1501c884140c20fa84034011912680140d0002e9125200a1900038146400a4041c0116400c00e80c0a0f80060500f12035504910000782c0c3c00315a0007005549400380d0107040e9001c5d5404007503d41c0041d1003101d00c4a04c0e00954052005103040340600380d11590041707620745c15450042000300c190419100c045d1446000140c800e40e4900201084203c020030101e1a995040c0c0041d8038280c6981e036420b08507031500c1d05175001d1220a000301005030b1120000508441d00c62400140c0c1c51602c842c80500d0200700d40c3c1c0b81030203000744403c1440200ba0008040350014942d081554803513107003541002c10700020b03030000300580c0d145000c5241045925004202441d07c140b40030301506d10312000303200031261806c4401041c0d21501c29484014041f018110740c2c001005021300d80791005400c803008243e4072000454544a10000c01c1015050b4404c6421000741240050203100d0341c90030010a5813400c43d000c0182c890395070101019051 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 686492185 1250 686490935 686490941
    0x20090105011e080903040b04081501150518011e020f01051006021b1c0606030201030c080610080912160b0108210309010b09070305041703132418120e06090d06 70
    0x181100c006066823642c540340c1180e156040c00c8000c9119450b41400840c1785c210188803403448141a5503002e041440521028540040220103c0d042c02821a58254a648a01d806124003411500101010504d61343e62900b1500000e041c03005800e075001040c0501e0340c2c04114070410740c0c405401c00d00303c1ca28400c002045950007907104641100000b401d5010030600360131401c1224002d8a0030451410000c50640b181201202d00d5640700301e2402c2840d092a01a441c0c4940003d40c1c075080762248142c07590b03200005c0c0e01480e07058802045000201c3c04110305424864090000f80c0081d005894a41600c03103524407421a8a2559110105c0001e0351040254031020009030001d101c840d01e4242520090000c0c48242e0f41640c00c100543c281d40205414202128098845c0c044c800240c940304d9122898410401111034100728590050850352040c2401034001d0500c0700d49511903101400d00d402620070342c400036183e05010300c55140d41000d0f034a4006540d664001544c0d0004107080602d803040003 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 686493435 1250 686492185 686492189
    0x60501030f0212010b3d020f07140f0108090c09010f0f09020f030106140c010c0f1803031d0f1305070f03090302280b070f0f02060903040501180320090105011e08090304 74
    0x10701640ba0344845021a400500c8c102013004580a640f0110f07255030300380c250000c414042d03a80044690100300d0f4294410705826138070800f60420780f00700a0403400005d64155082e07106981c243d0941d041445aa044642040300070301011030110f15200c841d04c4a48107a000500c960700c107100c40207808007410855801202d440070055802041082c02c803600150507802e10070642000a40c2002c06c184290240701c41c5441901d030981c8402d031886404140c0b5112180ea4111819080782441e01c09001d0358851100e001c07445141240007141c3c5181c200401401c031546843c0450406003801004030201b50040f03644240e0880e00101041d085440c040c10050b8030b04502030091211242104100b030143c0e02142500501440d555565a0340013901c0049a03034000a9403100d0150700200020130403503009004851117001ca030107482001d59601d40301c1414015a611510f00e2224080e081c0c0cae00e02d031802048280c0034000900b011040d51a21440810310320f007091210109002a42c4003041c01c0351020419900 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 686494685 1250 686493435 686493529
    0xf0822080c091308030403021227010e0d140708011a040b0105030103211b060507121a120c03070b12060d030203030a050c190e030d08010501050a1803060501030f0212010b 75
    0x141d184c0009940c0c003494402b85002c040c0814010b0340e5598990310400024030903007402031283e0b124a5031500c400d449103214641400881c464180001a00b10081c0140c5600000104028030a0803000040c0000d58900000703031810071204100502c00200c00b80171070104860301d11240350840c08680d0301038400707402d104031075195110300d0702010f41005801c0d00030345d1150074280e980c1e00000e801107803000252282d1044c003650b01c04404103200a582000030382c0d0b05004004170100c07455180d400340440d0410140b50410384283c040010940d202c4843c10b440c0a401610a0741e02d0b070000c407102e403002503e81c00017410a8a28503219000329402c4e103400e80c10f032512020b2441c04400149400c42e0040c0056580443c11400782c068400007251441c0144a9a0f04844040c1c5943d03180169815040380c070512203042c5c40c0030860741c005022010805502c946400303075100d42014a103005032070041001200740146c1c3c1202036810000784a17105d0b02c810705d201e06803110f10719a5240300c252980c000341520820b4034070f00c1 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 686495935 1250 686494685 686494687
    0x403050409050421080c070b06030a1b090c0c080f0a0e0a09090308060607020f0d08040e190e0106261002190f0f0801030f0822080c0913080304030212 66
    0x13480005244903211400b0342c076400e41c0740f02040d00161000a0100c03001c101442c2e00b486100080741d11296042c1d4000402002d80300610303919501c41c01c420122015400450444040520108005c1e108244c1c4505440c1014a500c490660b2880700c50301c28200c2c82c0c503500710007040601a03540113052034528060002c003001c20b016180c031544030007009601010fa00050445000c0f410b6410b0030012203004c1fa4002d40840c00c41c160500c0ed0007181820080b0403543d800d002c1100060300b001109180340900d40344e040340740d41c0c080d10b000302e002600d21903c9040034a915143c0b040120440503054a032482c2e40c030003407200d168000c00c0240c41c104104ae40020058500026000340386280b506000d5500c040c1540b40c0c00c50303401641c181182c0d05104c01c0e2400002c40c400400600200b0114031000c1e060b43d01c40d07401c2903d056500416020b02d2441d51800c184600e0304207074203001c61842800100c0980106458008035894000503a0400c140c0001c405046144008040703010705200780090315415518030007107 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 686497185 1250 686495935 686495941
    0xf1502090a0605091302090d170c0604052d060105040c051204060b09010e010b0a03111b062707030f06060f0b030f01050f030a060c1b080d0b01020f0312040305040905 73
    0xa0481c0d44003200c520305c20014440701042e000c41920070f5808901002c0c0c103880c244d411035034529149540d40c5000c10020501030040c45e41040e0b0821140f0310451051014208004004a681d00c07500610b0036580080380a040003084072440000301c160440d1411900450701502c00700d000c0e120f030f200365010100102007080c200424031850381c011900a043c01e0380c404046aa030f481e18841c40c00e10030f02904403c3e013410410a88400d100c1d8000e10f8070428203241c1e21385090500032140840500262210529804c61400c10080c1c031407000527200904201d4550789400718103240b80d90703140d030b400f400010402d284180000062161591115000d4482d070100604140d4442d0340e02c51460b00300300e0b101c10030402100004651030502008030f90842d08041e005011805569070354601030306c40a03030b1040400180328840004200042c500b4500140140b284550320b0182800c01c0c01550304243d9424150750100020100c0e810000045603000003d001800f095500c40d8541118a442a64400e10240d0b00344018 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 686498435 1250 686497185 686497187
    0x1b06050411180f060f100e0f06030109090b0a060f0b220b0315060a120f0906020d020903101a13060f031218060503060f0f0306070c05060c03040f1502090a06 69
    0x90743c000c40180c8180500ca54407141044048510846590340001c190303910811181c1c09210000e12400c4018a0000590035001c04605036800036400114100e46440101040c80030040e10f55800003503190090290703c3c200080101203650500c00e29188402c0002d21051010343c40ca041303040200344a0507801003980e28085180b013500242c41170b5803140c0050020420354a807030412980790322030740d44030b682c490f41b0000303403641c001e25059101d050300d10380352107440c00000d8462004007c0003150840c01600c62142400b0705180130252440400c01c04e140c09078424000391460b4010ae00b07807000319141090052171085d030001600d05c960001c100d180c17081c68040100224a100644441c0e210b40d84c041c7c420404100365010702105201c0d00000c11000c001007034460426140300b02400001400c008103900d0104003291401c642204c00c0000982500d094204105040c000d140e008404451601e0a60605032200301e140012640000d01d060030041c3c503454152002e805407400c080008001e003c03e01c0c0d075400 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 686499685 1250 686498435 686498479
    0x1c050a0506010f05070c0501033c11031510051b060618060108010b0901020c031f113c0a1d0303160206071e050102040807061b06050411 60
    0x50745808100100340d801240b40c03185060b513074105d820146411240340fa000064004004004000340c9002082201d0881c0920307004000e4540802d0300c0152503800003c030b42000031905100c0820b491528104207115515500c0340d00c0c12000711007200c0244105e00024007d40305d510403039101e81f8803490307405640040450003180c214850402a00c407003400b0450380d01610031600044400c01d0119442c02d00500c404010070700503000c1d408040c01210841b090700f000087ca440014500c0003880b03e04c00d0300c00002d1b40030b540107078200700c900e00181c9400c0699242c000c0e1906c0600848501500d985403070042151301c0d0b40c0b0698040c40d10300541c0d60f50385a0f521040240311031b0f45460401c0038081b00c01c20681443c2000001c843d40d4032002444d50f00719551a500300161a400707048140c400f64003208155541c000303602c00311000e543c403030380c001a9503c0c609040a800c083d8190700000c01e001041c801d6680304000520700c1ca42e0943d0000e030000d039980d110701d005550b9001144c081234002194012040601002407 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 686500935 1250 686499685 686499691
    0x607050d110c040204030506040b041704090603120e01050d181406040209060307080304120c0b131d0106080f040c0b0a0e091008072102130504060c03201c050a05 71
    0x140c501c0140b11600307200c140e03c1940300041980d0f01460005010030015101182c00610070f40e4109a9000d41c0140b001e001d4010350803128000d0340d1110100304018070888800c0c03042405040507100702050400103409800740030700715551151201107000c00840106150b03e5850307401603a4056a1505e00c1c140381e41e030b500449080307016808c40030200e4054a4005803c41c100c030040002585450f0070700c5000f1850842c04001110400c2280c1c00109201050401506648011502080000380b86c802040c0342c0c480a00c6071108003414120043c80425030084001d50711614842030f0000f5500c403494400c24607085070b8041c034079548001c2600b18203140c0c01040c80e0a96002182d01d0300c42512120307400c0c411030066100340d10159124040030000d190159800c1041203c41c003950390f070100c00d1070b0040792601c800c2c03690010002d540c4608000c1040100d104140003003003185400c10014a14451141c217640303502100502070180491140040c41d004943e07684403015042043c440c42c1800c040c080007401e426 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 686502185 1250 686500935 686500967
    0xc06030709050f0a0e0a090204061511071a0a0c1a01090b030f061905090f030c010903030e0c10030e0307021f02010e0d080105010e010c0813060206060a1a090607050d 73
    0x840030000d007070f2600130200c40689482c44144c640988420100030011b080008007240c00680b91240004c0d205e500001690410b41c054892941381c1c0502041c42d03061007065045550724a81010580b03410341c031510155626a0180c0c2001801503040d0304202d51a400a8103101c160a18140e00101d01c02c20389801000300098280d003100d10b0740c00007502003602d500b01218204601050309400401e084055086250800400c60988010206c507018843c02c5920155801420b44e44902c680c1c0c04055241c0f01c0d410381c0d0310390704010301212000800040d580011340d01c4000201502d0310700b0045070541c180b0407900d0080c4e000307092086490036030301e619601541c0303c014400503520b004000500e052000c201d40e0b074040401e654011803030b800d000054403004aa4a0218100110200c0501c00200840028a40d000c08411002101460000021b152100c0100920b020307450f9800308010350343c5144520500462030003842a107039a03ca4001c41c0c114003a0b42005850b0744141ca080b01c0085400c4080040200d8407 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 686503435 1250 686502185 686502199
    0x30b07021b060f220308040b0901020c1002030901201e0105010603020a08040609030215253b041419090209070c030c020303131e0e07050a020c0603070905 68
    0x20381d41c108081402844460200150100700030000089883d22245016084000ea1240d25480780c85040207a007042d080001070712000112020305680400c19480c114004813280c0b1110b082c0b07a20020b44a0180c00c2c81281440760702e0084461400303040c2c052000c4901da0b607084642144589007500c80700c02d10144010042d520740000481d21510a00031504000d404da2204000391301e680c0e0310540100740d6a14103804501131000d100c1d40c0b00020981c024086c01ca00194100000c1d8250000c400e00700c0044030690902c4188001c103002c0e00d24070142110b010000b4480c0e0740103441c1d00300d030096040904d0a40542c0c80b41c5440801502003860480d010301038003840400360404145401d41c0c50880d018040041d60200040c000035600b2442070110740c0d603682c828501410f2000c1c0c1903000c2403841d013054544180307041c6200e106024145906501049076201e030940103e01c949850040308403510040c00c10420407500090040c0503a0003003012010014015000346e80e2403030100001000301e41c190107030710704c1825 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 686504685 1250 686503435 686503483
    0x50f1006150912030203090d060203010e1513020c0a08030115110a08070212100609061502151303140a17070f020d050d06030501061d1305190c030b0702 67
    0x705000c40a0990591120340b0030b641442806114a00c05a41c11011440100407a125648410740e40c0381d03880e407041c6001750f180d50419103011100d80c2c0c010410b075182c408080c1203105d0369030742c0000260034004caa100107a680d40361a8440f810040025400f03048000000000203070300002034032a003080781c003039507840c51054491a0b0703483c0c0f07518101d00040c2c100700c402d2151401502c0c0001a00e00f601c0a07100840d043c0080318880072081d030700598020780c0074691301c61041006145000310800746080c684080c0590240011800190b690041d00c0d070078031043c0340c03a0500b0401d03014300d1140407030715112510240c4460410350020146141c94000c60200925a00483c1e8050b0103030864403c209041e40292906d40c070811012203164002c02c1502e0440341e140c050000202d0801c0c884e03030340600a10b40d0400400e250111030303580c1482c40234104058054072025182c0100744081241c00002d04690940c0343c0d0310b56113003003038503c019654002904900f944030510845a030009403c80c0f4001251451880c800 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 686505935 1250 686504685 686504699
    0x40c050f040228080f0c1e120a06180b090115020c030f0109050106060e24040504060e060a0e011511120a08040b10080c01081f061d06030103030507030e01020109050f1006 75
    0xc8141c0c2c102c81601c500b40407402c1c08032030f41038047ca40c00b512210201d06002000c49030354852441580d060b503452b541c40c1c40601c40d4024910b0500c0c0440f504117000c0c000c0e01c0c030f4400840d2241105100c1c5400c1e00301d480c03140b03d4120b0701c24015180b50311001000c550b108a10351482c60700030410600115050f6107003c030001110760145804c00a2000001e240412042c122180180e9440f2956203e03d407541d4100008122540c5a104060103009016001c0d0311615141c0c0500c10214902d4000a00c0820f07504010020640c0c1482210410781c201e140c40d80007220520721a519020419084210714a0040b0b44010a246e00ca0b0100c0d114a015003500c0300b00e515040c81c00103440002d4043c0c6426504215684d44542d4065103540790000307020443c4600b0040540a88851120107401c41ea00080300b41000c20481e41c10b80201c0f805000c402c8905a02d15451035070003610500c10341b6401400c0c000d10b07481c41ca40c50b80c001e41c0b1210f200b580103000e8031045080400d03c41c0c0c840c05014038944945180c41804a411 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 686507185 1250 686505935 686505961
    0x2030f1c151d0c07030c1a0c12130f0f0c0b16111e0d140703030e011218020d020f04050f010603380a0b0c060a1103040c050f04022808 59
    0x784600a940d00d00d0040030317450807030381c503280b144040c0c07882c0d0303905016a40d41d00049003d013445281c4c0100556211401c524030040800c0f0040c200d0742d62115110140b5010030324000c0304461842c1e010001d266007112925121881c80510ba0015010307000101e01011000a000b0002c0040c900c66440215882412030800035035000030310000e560701186546010180c20b003004210442c50090f400702021181a156083c81c10f076641d0030407000070329000c4000d84156040049100707040e07c002400c0c002d0303401c0c034520440444089a00a8442e060b8500b80382c0554079a40168884843c0c00b0b0410f02c51854211060030103d070081c0305540010b46442c1d0050703051401c1040017280e150581443d01e5403904c00960540c1c0b00c260040c909903100c0c0104c03600051084d4030710010080c1d491000c001d412249001c1040c501100d929600d10904801c0420811001032500403401c015203804449011500c031405001c50020700441c1c62001100307c00e4005070042c01c1c00d007030030511410071556075040329580d042c94400b94 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 686508435 1250 686507185 686507191
    0xc12091501090f0605150702030c150d0209010c141b1207120602120a050402030c012d1806021b03010e03030406020703020115030b1006050a02030f1c151d 68
    0x1a180080006001c00a15030300144a4000399180106003581c45c2e0002449100548502402001c0001490421400d06003e56102600106ca504030040c620405c42e00c424401c54102001d083e07030008009a55031b019400619180740c00c940c2da045281c41d54030340780e0390ba20741c034541410b0001a24400f1a00350302d40210048000800040a03001075868000304a0040560100444a035034007802080406c1e48400c100d10f00c200d11816001c541d03400c1c00d006046c01e000800203014100800545801c40c4291884c1807902c8461400a4046014910980c1100d500c4079114009004200c2c261000489950010303100003010100c00f64145802c0c5008201801c071030403c0b40441980c1c10500000b80032a002d540900080c0340240004682504160075010042c20660000c035400c10001c1d0a000180007408c2c908406010346040171072901456040181d0f0720701910725542020440000c54401c080845c0000c3c7d640302103100c4082c00088908013003910f40e0040c600030007507200b6101c01c50a0050320380e0a00700380 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 686509685 1250 686508435 686508463
    0x4123e0f0c01120204031e06050604090c05010806130f020c0111090a060503040311030307090611010b0a05150d06270b1305061206070f09050904170a170c1209 70
    0x100229000103507a02000143c05100580d0300b4070001020a490810054549520000301c1d40520f04a05d0000d040754009000700d8003032442d20318200c0004018400e01000c1d42d009003000b20b01596144000342904070111480c1c20100e0500d04194481000354010300170080e0060000d0041c0c00c1c042022036100d018010489910000c01c04007006054002d400440e0050b000780f820821401000d05484e26507403040d20b40071b000884500d003c00516500c902c04030510002003001b0710030780d802040010100c0c0302038011107211b5030591840f040f0f0f101e404802c075100c0d14403021003030060360755594010300c9194001307419040c4a01d1a50510800140c24460300100040c010301794081207040c0440c000042500500068100f0f01480c1614036041c0d04106040c4204640c0d560000340c8108107200034440040341e030056000301c0030b14007030000081c154612915400ca203660000d490f0242c0010446140ea00d000340d804081c08110b0601c1128290b6800506442d000c120320172085803a20782c000c2c0c0d51400c40d103560403 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 686510791 1106 686509685 686509693
    0xd0e10060902070c0315090c03060b090903043510090201110a081210050d05071a040608370204090e0102090102030304123e0f 56
    0x24040d1440c441c0a508054090391010144c2c0c42e6804001c24a0700c80e010100412025580003566040d080351b40100302e140d503818450014820070900c0b50041c032003007000680d060310002c103c0f0100c1c1c07c140c0540344100c00c86040e010001e010082c03190301e640d00c01d0303024074661402000455001981e07120001282a090310003d0a2101034105072003180e005010310101141c8100103840d19010314038191081a0394070310000c0d400da141074001e01c1e40044062a1030061040018441e0156a281403608480b0ba030841e0414a2a0045100b90030006417941c0001d4000740001c080d82d445507500f05140350b400c05546100703000003c0e0800b00182035941c0414100040b00c90790040d041303081001c80c002c501e0203281d640000d450b480300810242400e1400480700011a10808582c02c89103811031030034800309000c6a001c02410b007060300d814455005d0807002d41c40481d005c21403c0216558100034 = true := by decide +kernel

theorem cover : BRFrame.Cov 686330935 686510791 := by
  have h0 := BRFrame.cov_init 686330935
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 686330935 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 686330935 ≤ n) (h2 : n < 686510791) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
