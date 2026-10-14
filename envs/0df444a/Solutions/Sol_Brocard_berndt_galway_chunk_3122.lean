-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3122
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:43:26.089985+00:00
-- url     : https://prove2.me/submissions/8a69b3fb-ceea-4aee-8ca4-f716668c3f2b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 561330935 ≤ n < 561510791 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 561332185 1250 561330935 561330941
    0x3030105032e0c0302090120121c2c0a050c120f150103060636020405120a021011101808040f0807050d02030c121e150c04031a0703 58
    0x400c2e0305020f070192003078014002c0d5015000f0940014101d64030240790380304400814144501c07090107049004003003c0c0d08501c50304001200c0b000003040400c519512007040c802d070740d07009461505084e050000790302d0072090700d1440500c2c031019400503c004000507201190448008000300c40d12000081a00102d45c50030b209010104042d00c80c40200c462042c00d1100309604036131003220180131a80c3c5601040e030602c072000c2030034103600741244001c0a17216043d07145850078441609005003040e80d1200000c25920042c42c2040080d0490350109056003464540034800461901b010b4800004030700109a94000c0c400b0a00360703c5544904411518007200c0a20f1038068000112039140c1c0d442d24040c01c0010140c0c0301d510070b20300c140e10380010713181400c0e00012582c94008001d01542003050301802611908007140c03000f90b02810b15004601c00300d86510301903450209006042c0070108003541c010402d1f014100c0c3d002d003c03003400100005a122269411900b20311001d818050311201070941c05 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 561333435 1250 561332185 561332263
    0x3090a3809040c11150a0b01020d0c24090303050a110438030f0a0b0a050904061508010f090201021b0d02012703080702030c0904021c05210405120303010503 69
    0x203001d000e191442c0d6941030640c150091b103000104000d502a00401a80d507441050030740c00214124110035408100f00746506c01012a051400c050300740e000c100980212090b0708000c070007296540c024040041610300ca10b512410f009804946802e04050140c07038042201d050001d040c03440d20901003005c49003c0030541c0c2400d40068155281c1c1800100300c3c444010889400c103846107030102c45126403405800040413201d0103001e80c0e010752503039104c40015121345a020743c0343e58491000050307009000d00c03c0031002500844002101800c91000a040c080b17020800c0d40030000c01140030040c3d40d41c50600c020b03d03650908042c2409201e0b02a9213a0485410720255810380c000300000045c461000c009050540c0300314182c566112680c010411007920513035002c1c0d08501c40e00c6d0b0280708101000c0401a8040c011400c03600a044100b515a00300c050340d101ca0b00a00c0e0000c1070400041c00e010b14000344098000b40994215810500401e54411401000d624011021100e0344080010a1901c0d42 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 561334685 1250 561333435 561333467
    0xb030f01020a020f160f06080408070f060614060f0301210c03051f0513030e03071a0706050f01150513260607050c0a0b06010203090a3809040c 63
    0x900c40750100d030040d46800f103d100d11880d5005045c600407a0f001c00403106025074a200c041e40400328203105c0111103981c1c009104440c003ca08106100200d40c0d00700c1810f49036031103a5400b00b1214201890241545202e14483c0e0145a0500c500340c6804500f1f1705aa040d00d141401104082c0d010701c24010344d1101c41100034018003c05038020050100c0030641c0441440c0700c00b00700b10010a1500b45004944c02280c040c0030101c000c001902c0001d01ca981001041030b402011100b6984c0c03a0003c042500451080c03140d0310010000303100c0304202c181d005031580070031b1903490b113115036140c075100d010000c0e072808190041000000d81110a035445100f244041c0407088180c554040e001c0c41200410003c10507140c0085c428100081c055502c9041100c0c04554408044c10000200e070fa03411000b0030f00a000241940800d0084900ca0340b900f1900c003005124034030b01964005c980d94081e4141c01401c10301540e8024640c01d420001098003402c07111040c406030f0780000c2002500908890b4810f035009500 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 561335935 1250 561334685 561334687
    0x70b150f0d03030c021506030a030c020111010e0c100807021009150609020304210e120c030a050703060605040606081305070801180606150804080f1312052e0b030f0102 74
    0x79003450750582c04130803860020717003c0724240c03034002ca0400390900f001c581d0301d6850350128140c080028800e403044c07a4614418141104980c828101b000d094844003002071100b03511161410b2002e1511006403842c44500d8180b0b180701e0b0902d20300080d00d904581c0b40f240101502d0380302d100d040007015282e00e40903907464401001500d0b15446e41d2000383d07100b0b680c1134400d40d06803c95266911803090403400594040d031242c0503648044000d04c4003907240041503285900402c4100c446c1502d0a0003030100052140c00600b40c4903043d894120200c0d0482c0d0000360040340303080411701140b41c00c4403115420610640d41400c2600080c6840e1b441d200150308580d05550900110031012078040a00000c01c901c501c809104140d00e032820100302c168480c4803800044c5004011602044000d030040c541803200009440c504000b41c401c0b854070b4682940000241501b0b91144803c0c0a000e01c5802440c440d0302c1028002c00c925107209440600e218119410345035038801c2c802c6210383d000c010701400c542d8171030002c0d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 561337185 1250 561335935 561335959
    0x1b0303230f040e180c091501030e0703031e030c0906030b0d02030d0302091005030408090405220812150a1a040f03051e0a0c0e2e05030d05070b150f 65
    0x12401c99207054a01e803484c1c00b15585032542080c1d012031140412500903100203265070340c800d65000064114079240d41450f030340f407100e800c40d09018480c2d200550f009845008080e04815088283c808405082404051a002c1c034840c007264024005030442c0c5a500d400f09110040708000780100b41a550000c0d4503116550381c100142d505074003d040110300864000e0645600003034207650520040b940145030244c2000140024038056000a400010860b2510480b40d449a40c210b26005c644038150b80c030368800b00d20b400402c1c22101718213034451000320741c40c1da544807050040752195915000f1403651410191022000110340d03002d40b8000e00d407045072011125502d04100b9200c400d002640503102100705004040036000054280b03104d83c1c46412041e01d140340c01208046500c000e403031110b52400800d5007003005503040d0030007000c4c0d0340401c0202e0700076843c210415291003684130040e4140001400110040b0b03225568069100c820008006440001d4200080d2004207078007009920401c00700d84 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 561338435 1250 561337185 561337199
    0x15130602210106030b0103060b07021309050a0803060406050a0302030616030209040c030911030d0516020411030a0b0f100c03051815120a05010f0308210901091b0303230f04 76
    0x1c0ca04a52103074030100000c0018030011016180c0c03d00403071284d60010000200141040418501007030341c1c5580000c0d004026580d032609028145c441510180c0d404814480540f0b800e2148030020001114600c10f0946994007080d1201c00c0100034140075601c80a039501950f0003501214120940201f00b08611511501c002e001002100c0c000d45c2d16182800790340715a41800034a800c440b46d00ca031100c17070820140a4001103c001d0000080380c100b61220a400c0d90310340715002070f6004000d040310114418280609000304681303d4074880d441b41080c80120340500b500247d11000b040e4040c03616580e902a407041c00007080303082d0252103401500010345015020708ad040649500c100441d031100381070f00e5000c10700d0103a400c03e0080c41142c0e504800100f001500b140300900000c0700341d070803006a1415001d002d082c3d010080b216084a40d441d6038020003000800c1c0c010001d01306202c07554003607060030340e2070041201f100c1811009072030600420359a0f075404468159640030304a5800550340303a4a403c0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 561339685 1250 561338435 561338497
    0x5070504110d110c0307080d1b080f07081b0901020f0303041b15020c131404110a0b0f0910020f01050103030207182013051903110315130602 62
    0x46100c100d83c9849030a007a20380601c070864941d02078641c010b50a12000303845e68080c0351310100541c45419034581c2280c0742500140b0034810321925940b200c503030901e0302210101e11928001c003d0010072641408000480c0345283e8006520b803d086001901e0b99038100050345840840d02180314244001720030031040001454000040790310011240e070380325039221003104404d428840d1020149c3c0010210200c0c0d4100082401c1c90300f910103002040c0c0c02d508510b0440f251000780e80a44103042810760803500713810311484031070007848039010091411040d01c2040e0100d005450115109940030134500510901c200103980d00c1d2603001008100c2960340f4075001c0e5541202e0b216281007200040a40101e8a82500c11101c8200005480814009021024500301c0c2d0204500f114071751031406001c10b180d1918925250003605e0b00c0000f0301c0013411130400c41d00b4004050a1a8400d82c40f24801d12124500140220b030444214804c00c000c1d84010b16013440a4010b100c280c5004200f005524031100b90380034 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 561340935 1250 561339685 561339697
    0x60b12040c0503211812010e120405130917160c0605070b0411062101140a27090b0406240b040e0c041509060806031b0402070507050411 60
    0x848036580e5034507002d041c1c4402c02c03014a05010b489010340d4603e49000d06004100300d050030445080e1500e03400e0001070000003802c86c00580c582d0b40b0a20190b000030104009408220048102800c103407625001a20490003408511800c544440c1000b04101409402c480340211300075181d5100c2e0004100c280b440e44407214242d40c0075590f00b000040355030241c401c80312429001481031603980d0b034070780b144241c08103011589074000904014402540c280d160400d004800305004001082d490043c1e4540c1654245003203e103c0ca00c81c40040103101c10002e01181e143c000c0460000f20034000700c0125008115803c8041e1242c08074004000c00c0100640c00b400620300e824040c190b410144c1d0303545a03841030480c003c0e40301c1858100010300610112071207043d44103001505041c0b515880b4280c13002074400011828001c1081c240042c088075400c4409d09503c00c5080d8000c1550086029510305074a81c0a100207000b9a4001002c2c010310901307000c410042e000160050000300609015216294401 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 561342185 1250 561340935 561340943
    0xa0f0b0f0a02030606030402040216020619020105090d050702091515030a050a05161409030d0201020c1c09031101030212090c010e0409050714030304080d091401020309180604060b1204 81
    0xc00000340481c8007610030f403800740c0e8002d02814115078603a404d01000f940000b95030002110344041c0c0300c0c0140c5d18070009040e03181d8929410301109002d4607019007921400b41002d0701d240c0010003070903e443c0d44070303040d20289601100c400d030312600c800e004442042801d002040d0030403180c44541d820101d0540085016803918001000141e070b4040c899000c0710382c00e40c1c201d003a0b14108076005061038403981d0034010a0781010300c01c0e45403045010010703240c22078626000000d030f5004641046488818428071010491034000301300050701803980140301c1c02c41404018504001e0082021069209a06440e001369100050b0407075400d00000c1e040d03541501c80281070020ba10703c0c401c404281454018104040e51080007021a00d0401c1d803021f400b200050704003130f0903202c01e010019491800700103094000310507032612400c3c58240a1001145000f00140f50b040d58400c018030b07007260300c5903095584505951003c440d015202c1e4400a8003a00c55980302c070200c101701081c440c0003554910a90b501980c82 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 561343435 1250 561342185 561342211
    0x17062809021c0902010c060b010201020d05090c04060611150703061203030b1005042303010b0303072103050c091306080a06060f120506011716031a0f150103020c0a0f0b 74
    0x103a000100d0a54003c80c2009002824020300200003803100d0f0411092600140005403c1a008812840440d03508403118200740e030091004000501b028800c2e40090042403401d0310307020404d00c22041d81c60740340203210880c402c08000040e031018030070303800503000d0100c1c1500030580110504005016204404107a88101c01580b80c03035040c3c0707020700102d40c111803981c1c4000141c04000e070398000c64074841101864046d52030f01410040c030b980900050250911503910301d4104031541d00d019203520400b03900311080c1803030481401042c4068030165199444c04480c1e070b049080d04003240034040c00142e40098900d101c2ea545903420400b4a40040301074428080c281c0d132503540d8940c140d030028046203502030070f103810090041c4100304408200c944134810100840382e00e0303403242841c4100074209030301c1900c2c0c8005002910328485001240c10b82c014080b1690001182401c4480d201d00c04504074015050560005140c02008414401c1590254001d090b801030701c0442e003452507020004440d45100710716 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 561344685 1250 561343435 561343477
    0x2180f0a0f15030f06060f0308120702060f010324020a02011a0303130506070f1b0603051f15090905010e06031e0c15090d03021c1706280902 62
    0x10040c4160b81844420404481049103152240410803500c92810344d0f81039203410010070124246030000000314491300c803a680d01c8101012080d00c1030343c080d1014045401c01030070f2040d00c4200301c0003503054940090b00008d44120701e085001c4003110b03221944540c039001150420b251174040d40140c0c44501d0050300044007880d031070205510b07446060345401203402300d584188032038181500070307111152140003c0162055a512030118407450f400c110600c4140240d07041c03040a03818000e03150409034038031580f54110400704291941070000e000d42c2d40c94141070142d0038119485080c0d444020300c6002d03020041561600021141c40804541c03c500034818030744900103440750090003a07554041c050241c02e1642985040009018241d001d000514009204003015035444200400714144203400030071180c051498510410081e092103142403080e4800d42d614a030b40401615544010101c80c00306040c030b5035a161100c081e088440e01c11001e900d1500200d0f109045038001c2041d40c0156010151404c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 561345935 1250 561344685 561344711
    0x50c130602061e06030304090f1a0402070c0501260108070e070c0c05091801021204030305061509040207050109050f0703061b020d030f110706050a0f020a02030a0c02180f0a 76
    0x24100703903070120940d030a00c0381c01d6245034074a11043c3d0304150020103607890540e03266a260295014049121425a90f8400001103080c100700d5508032520280c034158209040b82c1c460705401401403188505222680741500c554403060711411910110030480f44d092035840304000d582d207601034014626a9411800070030a124004d2005441c0a94488400ca10b101d0800043c0040807902400c0704030751203d4907840d201c1c910801e002a101018801090308030030f1900341401000c0d00c42c00f80000b40074100340308140340b011007100200e82d404a00dc1d2005030340d450091408900501070448054018011250720306810040865090708513400b85070f050043ca41800180144030b256a0202000f69009401d582607081c060b4002c84420036940b600007501c500c450300d010404e0380c0412022a1800d9407175003001308945482c400c416070703008450300450402e600c244010f592489419203400c01d000c2100c400c1411507031076100400c28413240c20740302c403420b0600b54600c40f0260300548101d46614100207059083d8 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 561347185 1250 561345935 561345943
    0x9060e01090b040e0304061b20030c152a0d080f070503160e030a080f1c06050109030b1506040311040b0102011401050613051507150204030b0604020a050706050c130602 74
    0x842000130107076140c41c0c40c2c500c0075601c180d082d202c8980c0c03549114850f0310220f03095001c20455401c13035161004100602100b00f40c1005031100c101845529840c450036091121071059a10741c0c13480503200301c282050300c064030300c40d0045105440ca06d88111569090120f5003c500240900004404513507551200d51064465010450381104010302d21190000e1051081030550111040501039800c010305586680310654072202c0003101002c000100003500355681e802d4810040b50502007000254181030000f000c44c88640b0014042c1104000402d00324607030700c1c00d4007100d00001001903030707225560b1804a8203d43c0005149100b20310f081d0742640b8550040c01003007544030701e0000c07200769a030a020410144c1d030009041001c50030000400440d00d80c40744a1402c071039909445645845e100685024004048003101981d030460040c0300c20400516040348950300058107d071b0141c1c5404001600311980c5c0180d07a4082c1c602401c0c002441955098500141546041c1540310124541c4410099075a = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 561348435 1250 561347185 561347201
    0x1e0b041d0703020c150402010302070f03090f06020105040c2601050f0103020405010b07020d060507050d09080c0106080706080601050702040231050d080f0a1806050a08100302031504020a09060e01090b04 89
    0x201d504080d003503d02c1d21768072103405075200b4070504005040030001e49400c1c60208004000718040340c00c2c2c05040c40104005a80f44004018610092140d4a0940c0d03034910301c44080e10821000b9406030707469140f0024084003031507150b04000c0082100d443c3c415901ca0741200b00780301c164003c9141800200c1d83d0504c800c115074000342c01801d50f40c0f2020300ca60356a0001c0100410403401c000060000c110074503680e0148400c0d003401a8642c60711262050001400c4410310f44c13100300541c2c0046003c00c0001d410002d410390041090070103d8a495060021030040d210b0380c0340141500f5100030f0b0440c0081d4041c110007600c0f01980d00e54102068550060060340c4220490140c030303406051161035024447c0c2d03401071440358000d09d030011411400c400e000e600c804883d0000004208041103103d9041d610451059101c4241c41d11004640d1440e00469100c08090f0b800191607010300000070159160f184a1500401c4850420890300f50f48081e5a03822180a01500c101c807070510807144420310703090144e030130 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 561349685 1250 561348435 561348457
    0x708060103150b3f1b090d0b060d08030a1e0c1b06060801020316030509070608040201080406110c0c33070f06050c2805041e0b041d070302 61
    0x120f0160303c0c40754131550310091098501080311421190000c1d03ca06400b69806200a90f041e03d000c3c02d20382c6003914174400c450031130f001110003072044402c3ea90355090480b0503543c22030340003206034a80601245003000d072100f01800e00c410004c140100341205611440084c4000c0e104071050041030314200081c0ea040480060004018018004031203002042110030940f02d44400143c0c40d0340ca94956099030411914003001200701070b0f181d0750040d007500401e5030002c80309003c2d0509030706218000d020800d000e08013a041109100009040016a500408028001e01c25240c0c0310b204010302107940341035205d9128022002a07042d440c000c100c03050078200046502c01d019002840d11000c05015401c060410b03903552214880300004580184661409100514015580c03050b800d0302c07030400d04102080300150001400c0d203070303102d15920070255420788801e110200d10480701e11800440940854101508140c4001000200002619a40c880120800103500c03031079540c0903019800c90140b0381040d0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 561350935 1250 561349685 561349687
    0xf010612020f030a17090d0c0803070201110a03021005090f0a110109090b091315020406050405040501050904021f230a02010509030f091036080c0f0d0206070b0708060103150b 77
    0xf145c3c04458005006c05103405003d0030010b001136140c00364107501a40c0704d098150000101503043d540e11045214540c48820010502003c0310f40d4000e5a4007a140c18006010ba40d46001c10b260003814422a404800404201c0f90700003214103240b4034100c01070307080c24040744941c08001901d000f14000c0c0b14100100a04c6040aa540d10405c0c1c1120309040307000b04d441032510900315000041c1e034806880030741001c3d91515141c0e03003044284400c4880603000144516622020040107985a200140903000c403200060102c6040000c15500c00340301d00040d45c0c0403a19880010491a440001780540d200c00d80d0091029031107002c2915180d1080340c00014515404014203c0d407414040004511426a032911805a8040300c01100190550501c55442c18a800d649aa5040c10040342c14000e050348070041c0020050382000139024054940c0c40d1405130b10b88002d030b0001d650300c14081e2905183c0114034a480e51a0541c030003008044111001408286000c96425040e42403004560030b6690b507107011 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 561352185 1250 561350935 561350963
    0x3080a0c021329180a060e010f051003020f0711030c0303070b06310207081e0703030b010206070e040902060904021204060e0304120803090a080c0309031e0607110f010612020f030a 79
    0x5461004d100814114106480380e900207411a0042c02c40b0303009080d40e070a90f80f8054281010070640200c402180010140140320103180074842004079140c46a21468508640386500e0109080269004115905020225007441481310054660f8443d20044030010910503a0708812010f884100100d5203500c00c107a0601c403410031596008000150007114058100560b11100043c440501d030002c071400c150100c0c40d402010f070103026035001a070090001e4030561070300c030300c004088074008124184690744906900055440f03400458035207480150080d50348000c1046030300c2e1174110540c0c0c101c034420318000ca00d220840340841a2422b5503c031860024254103d92242c11441d040644400c1e440d029030003811002500d2000103119840100002e107465110b05010181014040000c5056501a40c40c0e14074084034040307051175014455040078690726032400314a6113401008007005825610741140402d030440c050400f0451144212840c032101d0011100b07251b240d010241004103000c00340002c0d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 561353435 1250 561352185 561352219
    0xe01020f04151e090305150106050a05070303060b12041704060503150f180a0e060108030a03020a091d040c05041e0c110105190c02120403080a0c021329 67
    0x901e03501c2d90910310340400c40300900300710035488809140c24500403c1d40a5410010000e041c044500d41e40c1c501d0b08840e0242d850114054201c0c45807404200800c100040d40e1000c0502030341c44600608202100152110726008104100140c03c0e030301901d4041d079500415030344c0070541d41101d06035400307a0703910b50441c1c4490b9000040300310603d0a855100c01c0d11550342c84562200c3e210b01d4804d000c046031201d941c2c104446d07003034116083d8403000d8000307400c140014012090004201c603a1a000c80c903005aa901c40e11004903009581b07030f0094207041d40001c2d11040e07952086440360340110301541142c46c5a6541c3c100300f100300c41c50015040741283d4200c984a0703106100d82d110454490441c2082d80070040049209421a00c0480d402180e02c17400d12006212840c3c14402c51a141e0003a0005140b000c002e401d190850380a603100081c01510f00089607042a4400c4510f15802e40d40074048039403070b07a85040054050f083d0710316403040000b40d030704c100410741c40030300d010320090500035050002007034600348 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 561354685 1250 561353435 561353459
    0x601060e0f12060a0f05091603020d051c0c03080c1809270109050c03070305071e03020a060c050c0a0b0702060d0902091602060901090c1401020c030d02010f0e01020f04 74
    0x414640c4091280005402c610b000d011035445103030000780020340e00030070704401012a0400741006843c3d6002003549940500030300192410380703404a402c4111702075145083e41c0707041b006109540603440c1641d040b180054000c00c0002c4940c0c841d03200c5e40b00c96513500d4880911401241014041d01c1e032800354a03c9503052040c00f894010343c1b0320031401c51a200710051007510b201007610025840e0b65030030340d502c1401424021290b001c4012400b5050080c5951a1190f0f038110900809040986030b440000d117800c0a118000c00955000e014141c1c5295250405403c00000103419915030042d140c8480840c50070b012480c0c261740c980304030181440c4980d000d001d0150807001803a140307180e86054100c0540d80c0c03105c000380308100d622030902c81769003001d10003814a440541810f40d103a06005076400002d00700342c0550180c60108100003005840400100d2502da98042c102d81c25010307200c000c090456042d04140d07260305403a1414414106e07540651b030300304e1151402400100405000510011400e10 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 561355935 1250 561354685 561354709
    0x5030f0103081b010c0e130506280807030606091a1f03022718041a060612010906050f01050909010e190f05040b0901091205031b0c030a110601060e 65
    0x5103c12196080a0b20550300311624820200d010400c918041c070003c0c5007003e034031a56000f01791410701060400b00d0101320034920801c021410706c00b282c11400700e0080ca032440070000307006c02000c0b43c15a070354031304241005000c14000d045100d401e000000114100c0700159000d0540302821007052403250200c001d210514000c1d0360410140c0070014881d01011502014446e00d1144202c142c1c2c8000907020010480c0c400b040100c61401a90200400f066a06141800004c500454600342d9074402e00064014400c1d045c400d101e042c1414000304860100341d103c10240da4050710700d003058035078020040d02c4a004600343c0c60ba1000c120740c014003400d2580900c5a8001d15283c081107409060301c0351000503610b40c0812104420b5a950801092100d500c1c2c410750440643d00c001c000c0f9012585500c4030581c15044041c09020f80000811030440c0420200040715402c2c0002513181e2408061454881d40005030541c0001ca07000c00000400d5030214155048a000c0c0d101c0011100c8408240101c4030442 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 561357185 1250 561355935 561355957
    0x16110f06011e1a0c01140106050702040f0f1a0307171f0b0607050a020405070302070809040b120102280504060923040608060a27020418051e0d05030f010308 69
    0x1450014221495032083c1650001c003801e02511095404109400c5400000d20140e6000c1148010040c4942000c00c0740c00190301550041031400b00c05203d900a0a4070324481c410552070a12801001c0b00b9200d0801c03070802048007a5444079a40e10300d41050703102d0240d001d6045070450390300c4160b4140d10000030400403030034600c08104503112500243e560b0b0080030301610690000c01c4004210700d07113032089552221503801c0450a003102501c804041d801011201c0380125a24104545586e81e100e0921a8040410b0000c2d0364078007000c4210075000029000e4002c20b0344111403940340780c5000f503060b1400e0300e070b00d60381c0c0540c6d461810482007800750045000d000110554048010951160301801c005005801c000b8031184c204142503004071811014500803868950300d4401881d004000c404034a139404660100d0000802c0541044007c000440103096100ea243d544580c0020048030070b58022000341550036074443c201040d03415200803078950f161030000c1070040c0005003c4002403d034030528 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 561358435 1250 561357185 561357239
    0x100627090c12120503010b07030c05070509180c0d0b041709130509190308070e1305010602070315060f150c0c1e05010302040810021b030316110f0601 66
    0x9140c68040e103001c142c2d002880305042e4070b260541400190701c0100840d48103803070201d00c1c0d03614282c0815040e001c4c0740742c01000c0001ea25009070501400b00030000141030018126403c0e410708242e00f00402048d100c1091a03406440c014026030710b4100c155210702d03130b0000100079441c1d8a5940710110001c580812a05070841401b08207174030744503025920100b0000000004c0d20341409070106203050070001006540c00700e41e4466800081d4410101600a0b081d8104004055000707000201d020b0031045050144a150900008150b0b500007060302c00c480c0a110190345010070520742130700340c846038040d603d029030000c1d0040215200c40c1001a019004900c1c1c01403070070302290740300076440ca02d41c3d0014602a01e1045103d01d04000701081c0c03070082c0824282103180a2a104071743c0c0c0c9886c02c1110740303281654040780c41401c0e50143c56407151003c044205490780d9141030000c2035030004041042c42c000803544c5000000000e4002520b43c4260f00180040905030304c1e0213294142ca0441108442e03480d40 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 561359685 1250 561358435 561358451
    0xf06030209040f140a030302070b1f0b0306010908010e070510080108030703050d0e0a0c03211e1b1203110301120b04060605030d050403211407050c0901120203100627 73
    0xa1100c1e100d900d06c40da40c096a079515500340000051405056a00002c504a854605e5140041c1c3c421044031195990551a42d0710903006a8040c4100d80c003040c03c55007403009200c0d072110003007880000c0e1a03088881007d5800c1e443c40c2150242c50900540712164010058400820700038000351800031141d010100d203108100c1281811701c000a4001c44940581510038810407159403000c08600411020f9508840d41d03e040042203803410007100c0c03c0c0b001650640512152040c01c09601280c0d00860704030b134441c81440d03c8a165182c8100e100c001034070344103401c4c015088100032139040342c10784007a0010390780550301c0f5000c110380c01400445205503502d01c00a2152000e02c07049400e600d2a4a0b5141c442d80355060400c00031313883c00d00c201040811030b417018100c2604070b8000c40e5105c10f500a2a502d800062906518100c3c50502c1c07a0741c0100c81900004e4030700503800070010074a20980031f4034424842101203030181ea249000303140d420101c1c4410180e0080c01030109024043e035440300861f60728 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 561360935 1250 561359685 561359723
    0x60a080910020705010507020f010e0322170d02010f15051306030501060b0703031a01171f170f0601032003070f030602030f01080f030d0c12060807090f06030209040f 73
    0x29021260403100c4d651507008000007039406100c041c160800110003800f0301810440c029840e48a42d005208041050103030882c00d030012255010064040b03081956503c9580341c40c41565130394500c030b03190015800c00301c0720000d2a00c24003503001d0702c1010760310004c8400d08013020032810ba0b03c0050001d07240c9640e448004045a024000c03440180000384d517242c0e54a16a003001400c2c3c03041000d1030380306610310881207003059901680f84e000b100001100f80d03117580c42d402000c039241d1040c1c0003030345800701e1268030100e002c1810b5030701440100100b401f142d401000b0798000d9611075409110150401c0c0400342c45c40c0b46403440528400c0116002400e0307815031602c5180c51560420140c1090310910303404410020702e51380c4104450f0140c66640010b080c0e04c141c00c440075550340b041032001c031416904d501c0b80e18551402004001d40032801d5910a1150a0b15011081d42e503c40a1094203400c0d400c105984040102520984040c1c0b60007809481d801c1c0d44035182c40c4074400d1000e00859100160b119040004 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 561362185 1250 561360935 561360937
    0x7020c011e0302071505010f0909021509011124060d171602121b0d2d02220c0306180e070e0f09060703050702060609060f100503091902060a08091002 66
    0x300c00204000071b09505240741c0844000ba00c0d00302031031580c40c0c40000009643c80388081c40740007200e070900d44e99981074000105d484c1c40b0380c06010203580c42004805000050030b840710100041050800b10815030b982400c0001452500324003400c0c0139690b01d1107405c5212980020b00c100c204040c0856100d011590200c1d21708803520303442c9001a0800007014400c5440c807d4003140b104c2d001c54003100c164581e034980160720014032400c007120b4a104110b8441820342e02407030103a040d400500b801c10104200864001c1d56005641d00000141b13041c3e072001416002c2d120329020703604545080c024580d50000c0c044010300844041d14000c0c0701d031b4080003441c0a0000001c1f4850b24600510010f54188403c0c0c136460003101512100505d400c01d4100300c0082da002400c223134042421143c07100b090702c540011440820310400c000b500314603469405a14039401000a5001d2620801103c0e000070302012150510700400400950185003040f40001c55881502c132660032a440340c0c00d6030300d00c0e42495040307412 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 561363435 1250 561362185 561362213
    0xc0210111e0106080f03030112020a030611090f0118170106090c050c0f011e0221160e03010e120c0c040204030320010c05040909060b0d0b04020907020c011e030207 72
    0x100c40002000d640300801c0038020383d0020140c600051184110b2040016243c0c08140500b01c1a5007040d0740c54402d540e035600ea803400442d0803060802890815002002203a8000321010780241d00000c1065103a500c109185100e541441e40440b245a0421750210344d195101c2a444081e59214503001c12400940d00c078210911285441e41540d03102c80c01c01c51410070070004c0a40030940d1500080e601c9820340104122010000350000696446601d5040c220502c9290b00c0f164415084008025200020343c07900c0703100d1407440e100d001084440100301030170b0319044000d80c402c13038010442032111401031601034241e0f00041419a0f60020000020600326005940250000341404103261307011400301098081e1005404000c1c0070341500001c5c003816038445c502ca0b00710181da95120007014404503a2000c070507003200401205d4580400c0c2030a02141d94291010b905c40c85102d00402c4105000080c045054041a103030b59200c01d0004010782e55801c090344040c1c0506808000040004189801c40c40c1 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 561364685 1250 561363435 561363463
    0xf010f0504020a0608010803180103200a11011109063703060905070c0206160b15040c0507030807081003051903030506030d0c06090516090203070e100c021011 70
    0x1900e850640100541082140c0c0f190090149803030060080441c0071003180c00743c101c00782c1803940c20515080100c0042222031009040040c881030341c17500700500100141802c207610380d1040d1091003444091070032250000141c07038601404124a0a460400310003401c425144c1a00090140031003211a480f80c4034103190003441c00300099826404560188180c00280000b42d000300303c2c41c0b40c60301010b082c118102c44042d11403103003c80c0f03d0351441d917010242c50480f54010000c10044c28070844408200c0b41001845110b98280b82340c45072054861130039100343d00d4050780c40300820303180c500c010b03288000081c0044107a286140e10100c086138040103445034075185000c00c1c04c42c0c00404e0500034200c1da00980810712a410100c030390329503168404244004aa000349000440140030320300140781090112030503112100c22440080c0f002c6c82940030754031801194607158200e0804100708014059a41d0240000c503946e010500c01604014144088180082c200750403284c0301c8c20000c900d8030078442c0c0116 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 561365935 1250 561364685 561364691
    0x204030201030c0f20011b09030203100216030e030705100804050c1c020114090901120501050f0601170405070b0d020a0e030d0c030f09091506180f0501030e0f010f 72
    0x411940e251240c8036807015240307850540140720b8030000300403420001c5c1d5120305840c41348010303585040a500c001d00c80d0400100c1d40320395070051400544520303040d21060f8803078080c0260715004138946000b100d61040d0420801c2600c1c0c14580d4040c0d69001c28100015003500c6181c03c0070903662a0380218400a01594480c0d003c24501403034014588810941d82e540911130400c0030f480c280d102810b240c188241d09082a20040004103011080d80c010a010389600c200302078000520340070b50000400c45a07005900078001c3c0e5075500783c0c4100081043d2849400954060146144100030b40c40103a0080e1142090350341059541d40e8400b0740d50001d512544201e5030000d030b11251982c010920b000251002c0d800ba01e408441c204016125107403400c40a03043c85045550203002a07c107421b604e01a00c4030328002c000c895962100080c2c10302590082c400807464084034020f25816803100c00303040303074201801110030303d00349001103001e840f0301c0781410443d00c514000c07802040001e00071814200e013212000 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 561367185 1250 561365935 561365939
    0x2203050715140a11090d0623090f0d0c110105221d1e13080703030f06050306090d0f030b090a0f0b0d0f1209050607350403020f1807030204 61
    0x4407a04200c05080380b404586442c5084c4002d00f440340c156000c41c941140c5c1c0b0001c2c1022410801d014001503c038010401d564030021250b5103481107452800780c00f080e81103800c0100413010303860380c40c000181244013243c1c00c0c203407100c0001c150003e018080c13a03040c0f5100c0d0030551401041c0c50b2032130300041d00003a100c150707180500411103184204050b00052041d50754a0f41407043c00f101ea043d0080301641c0c2100030150001301c83c00640000303004a075a1009030290340d07001c030f814018001c00f040d04003800002c2c00c02100107424a00007601e140070341c40e400081d1944888003101030760000400e107884000e00d929070f500d00c81d40c2d50710001e0300e601ca58900c1d5000308001440810180480d0944180d40388980d4000c0c5201011883d0158845007060b8003112100462005443c260790310301d050740c84203a10260004142040100324000012003020090b0a004040d1810413624482429039443c50340282c0e00380010009450007501c4564801c1028018500551300c5050031011b0706002c85000380825000501 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 561368435 1250 561367185 561367211
    0x15200615010215062404062705030c0111010e1f050c040308070b04030905060c03070c2711130303050c1915020703030e0f07060809062203050715 64
    0x240d03156064007440a000441c4030140c0f040b68214002d40424002c8080f800f001480580c5450000100034171045034548980d40c4000007440d2481400c3c00040c001900303d0180c044d8a00e01d10300c0d50a640005010300700d210450801114106881021003407603640341c038080072410200340800b66140703298010301c408007480ca10070841a20000f85c81d100c3c00d04005c005c00c00c0840d44110955000e154480c0c80c1540d1902c8030700701154034a10a80000303500180010300c9030103569000004250a521031160910582c1d03840740c0d4402c9100181c2c40306aa074211000c1100140da41543c0f02d0403904060104139410440da0710205100400345070811408590700107844205110300b0815000c9114841c81a100c01c08030a0f564040048914030414031540c0e004960502014000d4004030303081c01c1140100c40030702c1d1407090340580d01c08462107108080740d909404510720160100760b1500c2040481d603450010b1002c01020a14003501c0c0806508014052000c5400039284840d000f40d4601e0300c0c90041220040c9511f = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 561369685 1250 561368435 561368461
    0x1512040309150c03020105010f120f051c0309061401080c011116030b012d050f042d06210f05070315020a030b040e06220b04060614011701152006 64
    0x4109d0700140418400c0000d12040080304585550040c0319007000130b11403030160320301182c0901d20241c018141180e00d0b50030b98554006034505015543c14045400c94441150030044280112115600840d050071a02d501a031200350080f0360396011a0720140d5032110000b0081c000343c204958014190b40100408030103601c0c07045044e00c1d02160407100b480e045000f03060001d0603105150180240c02c21084407940c0300d41c00041440704049082504c44414100f055071001102c4008001c18a440c00c04500032003200ca0b0401c00510140c00301d9485840354135031900303030300f412241140c25102d12000440001e0120b860741c0e4012038003a8025855080012001e42601c0f50035038144d0041e441c061469800c000c00203101a0400c0c40300c046c00b01e241c1c003003c20180c642c0d05403140140c1941c035071009110400640f5440f580803038800106048403030148000450703a0041c001d0400d42d0334140003005200046030203002112550130303400e042c4035032500741400b403000031140341440480b500301c2000c03c03003ea28512 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 561370935 1250 561369685 561369689
    0xc150403020c011407170f19080c040b0304020d02060415021501050f101d03010e07030b0c2a0a020901170607090b0406050702041413111512040309150c0302010501 72
    0x400c02c1120010713800144007580c060500040c120400110540e00158040000c4171140045054820761324019400f610408005d94044480000d10f44000110442103100c00ea8054491310441c851941c2c40d44c1d020072081d0110070740207903030002e8200300006c2d05a112014130403200765503801034400450950102c0044010590100b8010b44a8840804203540c8c3c40d03400304008615400c10009440e044024a81040c4100440755010b602c0c2c90801d8001c0c06000034410104c80c03041c0000000c598440820110301c5c05480c04200e100d203440384010f68000e007404c840c0b418243e40c00c0d0842c0c82c400301c42d4000030b0840c0020382c040d000c1404841d001d4150b910313040c0105588a411810102d507400c0c5230103e80b00c030034480ca100d140200440418001d04542d2076422174110542d075040e0904041c100218400b1a03c811000704451040050003901d070a81400980704541d10308800602d07081c9410303411420101c08005204401300804c000b4040b0340da0b92011511032098003da0360701406030b0007500c0c01a003121810f07 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 561372185 1250 561370935 561370937
    0x204030b04030f14030106050c0c040c0516170d0b0321030714160809010809010b010804081804090b090f0c032508152202010e12030c150403020c01 65
    0x40005201040034030111a400541c14030704a10b0850740401c04076005101e81d09814010b100000000942607170106c045d06020120f0030a0300e0300958140200801c40304803040c420301086060101e20308240c03a11b0326901c0c00354001e0390038200b0035044008020065005640c4410b29a541d01a802d070035003030400000070b64040000d0198030402d406130000d40c090200620480401071071040c050401d1441c4c0b004e94403074a0008a80c0d4000c00001e1800d1030213034000c840f281c1c1c00181c002001030400310050042652524060f1244c007100c0d103468480803666404003a403601d40484503500c2d85030175201d41c4100154140180144603060030480c1c034550402d900a210042c00340d20800c3e6001c180d54010a038044200300e4080c031141c818155000103114010b16034000d0051b03024501050300500c80b01e800040c421074242e10300303407503100714a9110007640a10801c040d000440c6490031a4607800c080b030100c0c1310700c2e054400310b03400d24040201c006d14001c203010750641400c41c54418401055010480c1094005003 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 561373435 1250 561372185 561372187
    0x23120d11070b072d0312180b040f050c010c0c360f1104030203150703140702010504030e0625030912030215060d0b1f03060c052101050102190507050406170c0402 71
    0x2990305c0080031142c1040c51000d0940d52070503d800711844400480f9103441d4442e80e8070030350b49003a083c00800011000b42c00e81d650300641d81e0701e1400398031615003658002c1d0b202120050083c2000d00c20103801101082290700c0b000140d2044001c11400f2030004262000350101052495489842905644410081c184c28031030600c010700042c4c0d400300b80c00d000d0402e201da80d0312195540d480202c2c058401403001d02628213101050121256040d0001440713580203459603503801d800c01c0c080c40f607584203491403032203805181140e100340100e6204024420314028a0b0104006441e0800719139543c010b500c0490143c5d001207000c91150045480d0281e11900131248070180c64a2500c03404000c2100402c80400240110f080c0e82000700c0f0403602c80702030741c1c00c5901040116008031018009030300c0348088020364600c6880c0510586105c0720918183c490690140280060041c0301020b80300941c10704440c14010000007003081e41710b07842402e004290003100b440c030703a80c0440e00f9141031410b520b6160b8003c1d40 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 561374685 1250 561373435 561373523
    0x91f0506090303040603050405100501080a0c0501050a050306120f030301140108010503030403020d0215041e06031d250801020d1b0206010b030c2223120d11070b07 72
    0x10b0048190350131581720381808100c81ea100c0c54020300b45640c100c64002d00780c0c506000881d101c40000348440000c0d02c00d650100d0344585507801918140203042016000030f01c204005549400e040c01400047c440c440c0445000b42e02e9117903e141143c0090704140c5101d190080804074660b40300c1103041c010141036015514150654020584596003030f08040c0c0200300b009128104040040101c03402001600303036910955400080452901e502489840006420464511981150b080780f1048100700c5100a22800c0c80340d240b050302089100e03120074400404a42d00196042081c001413202c1c2428082c00650817420842c01404280c84440792821940514014031840c0b03400411a03400c100da11072540d4690002d9150341c1c0b11076010755901701c4018006100042e0380728803403074174400c4021201016800c0f01c0c5078505100d18a22102c00d403582560081030031001040c00b801d1003880401024082d00c1500b5100c04007001d490b4401c140071201d0300c02c001d201058441322020301c1c0c0820020103841c005009 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 561375935 1250 561374685 561374689
    0x306011403060a06050309240a06091802040e010e011d0d020607081b0706090b250e040b0402090a14030615010206070e0438040c0c08090a0302091f050609 68
    0x2003030500491060100000c007048481c7c200700b0989603000c100c0c007680d441d255440d034100c0e44480c00c261851103a45040071008540c94885005501c180c01a001e80c4000c43c002d26020000982400200c24050355641d00300c48210200038092001c0c034504a401e20101042600081441c1c4402d1b1601941150070000500c484a9070080c219500141c0041d0700307850142c0c60218030720562017900401840b07035141110000c201f0081a140c24800c5043c400c0e070b518040b04030341c10844052504524040018440c0d43c40801034905a0700a4404c503202400c01400c00b441840800e0001c0e4180d0054030a1302800d00c1c0100b0145010024668081150701c1d0640000b68403d001070343e80c0070007900c201c090118001160032641c0b61a0301600110340c1c20a4407204454a96000c1c1d5040c0c511240340703a00030001c455103614182800c0c011070319413481300c0d921000e000b0b006444d8401d00303400c002c009a600085140d8004007598840724a5406500304000710540c2686020b86445a4102a03002c50700810b400c4c000301d40741c0c0d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 561377185 1250 561375935 561375949
    0x60f0907030b251d010516031211040609090e03180603060321040501181203050309011b05030a0f0606210209060c030a0206011e090c0203160602030601140306 70
    0x12a4041c540d2945a100c60f90000345261007491000305162424812010590b1301c8a018440300241250b03440b400c0c2c010100454080c45000221918000354410a80019100c1ca0f441c15000040b8180058840c03d050704004407540107078000000900540403d1146904074410002c521300414015850001440c0700300c1c00f0480b0840c2010710a00c400710005405803014488403806800005034802c3c908400c1203080e000780c000d030090324006860300c051440552580c001e1841a6015020449060743c1240c1d81114141d0004122000654172403c035610360105408540d1050140c0d61a42c544a01d0410074020442d0090325142c401181046000c0100319003009243c02002c040300f2041d8603502003c487c0318068031508080d580c11030740003e400c201c203850100142903040b50741d50070340e5107599852000030320709080002210a400260707a020401c0d03603545c0c0c2c800216904240150790502c04107810340800c0000b46981503402540000c20440c60f580c1c004101c18003004440b900c40e0642c00d0400100c1c0c10 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 561378435 1250 561377185 561377189
    0x3020624040504020d0210090f0504140604090c1703030403121a090a0e0f0c041508030306010507241401051206041101091703040306050a1107150b04090c08060f0907 73
    0x2540d642c0b000b05080d9169220b1341542c0c0c54001d04181c0034002c4900d4002d14420042c410074044c981088030100d06442c1500410a1144502d00c1c6540d10b0348406017004002d00300350404a0b00541c140d00000ba100300d006040c0c041040d401c0000d192030307103404d0402508002000440c0383d1814903102c1c03442c488100c040c0039289802c5041c1c40c1400c0558510030786074001d0540704812c2c1101d01c148040d188c414840020300e2050305c0b005a50038068150b05e0708495840078424064215281c00c28000525554401c6000c1d01800f40645c0c0d00002c3e403600c2c15000b0006003943c01c0007080440d01c81c1c1c9052100c3c02c0354842507005290a4480c5910044000301a944451000c0d0009040c1420307242001c216a10800844001d403810580640901a14041c0c6030b51b2544688000c0710b00906140c00992400d1503845402e5840d0381032800c45192101c10ba440b2040e04d0b110203402440320782d85006500a41d1074030300c43c00200074450015440100d08180402d80f400e1401042d55903482c0e81d074810002103d4000c928001 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 561379685 1250 561378435 561378439
    0xd0305010518070e120703060914010212012112020102070c290d061a0304200105030105060c150a090614070e100e15041d24030f010c020a03020624 65
    0x64003a0035403000551716110303100d00400307078407402c1004824407040d980440388043c030859030300c1e0080e40f66105080c243d0040c0c20066428842080c010000c0281d01500920301f03840d00486081d100155075951000e0040c0f06c4180e0700142c0d80880c4607410480d1914004000c1d180744070321902071405024030100c00b50f555200c1c00c1039910021031161902c41050b003040c0068191280342c000105401060207070306400032542581d400c0321008401c0c40078032418100203411441a900c43d4516800c0038144241c6612005000314944150f031007680c003c4500101c402e0168195400119101c41030f800c00c01c054a0f0000c0b54419440243d0080c01485508141088000c800035120542420000c0c072050b280030700d00800352604034000141c1c10010200707420051041e10407041c051404a007407000c0090300190300b110407140c41120345855144c0c0104035030154040d41c50080031030b584070031524a07a900355203140c070301100942e014000c3e80301055014000250b02800c00030150035007860920881881c400d00c848014 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 561380935 1250 561379685 561379697
    0x207030c180b0603010801090c140a0626070807020d111b1203032d0618100506220b03040c062102031e090a0201090915080d020d030501051807 63
    0x40307001c0c80141c01008607a4401070001d42c4035030b0f464113414060820002d040310405080500803601a46194a84103055400380410851a06000c01503510007808043c1d80008011b0412250410000341040d51148284d940e0f524028241400060701d03040d0120b012000703020750415a41da4000c0d00044484510354002500301c14229920f001c2901118201c00e402000e000000c204070f8180900e121070340b0405a019403c070f00da00da402d5000900c500d8251072050344852411518040d0400035614079401111454130102c1e8070b41c1d64400500240d0000b031141d084c0c1d041e541c3e01d00a6040517040104000c1202d400c1062840c0342c142c0c0c81e90001c0f60180911000e0058403a8155003d010051440d04801415030086580b802c00c190981668035004034a0501c011030350000400024000c504942081e606849041440d824105800040c101846240450303211051002a0500c001c02c04501e0700c50050300a030404c0e0110741401800e8502c16000280161824022003090b103241c600d200d07a20204501d026 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 561382185 1250 561380935 561380969
    0x70302010c120c0510020304030f03050609040f110a12020f0a1d090325050f1b06030a0e010227030601180b03010f0606030f0b0f0306040b07020f06040c150207030c 72
    0x150786488031050060308178840c00210221012a076801140614026110b8004208814070f088040d514101c90032500144a10b0110700044d1015200303840c664031401401c1200c060980208400c000340f42d116450360201302200d2819414a10480c80c4003520545900b103030300341040503c0c8079070300191103141010812040040c52140c4241b05a43c810b024152507031907094805030003040c0201d015403056505000e0440b00c002e00c1400041c030300e004408a5200d10407000c0144081000d25003000700000ea01302d031201d920741c0040381c081c40100b94460202d0312541d9402c01680e88035550401e429581c901a03401540140300c141840100e5641c2030030417000200c0c1c0d00c2c0c100000329015001d10710020443d54101000455115015080600c7d88050317072208100006810080081c05c020001c10281c060300080045404564008106a0f022540d07004130f8071040050900b151134000b04540903585103c2d1024244035039500895103040148040c030040c0061350554962a10007080d900c61440000e50310244 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 561383435 1250 561382185 561382187
    0x9060a0c080c010c21290a1a0c12070203060a020309011b030e0c0418020f15030f1006110d030e070b03100812040609090504020103020d1a12070302010c12 68
    0x116070309480380c03100a00018035802400b8080005601c4102c1c64107040300b03032102c0d00c01042c1c07041005100ca080a10300005220040050341d003803034400f040b5044802c2c0d52002c113060a008c40e14440d84406400c07055500e0f03140c000e501d82803d420000f0004803420402c000d00150350700088480c1c104081c0000140d40ea103410b0501801004040090102d03c01c00841c0c021509805174040d400d144101801d46407a10884001c2200b16a010075211600c41c0220004c1c00260810f0080e14400c0c240281140300340342580c042190310342d0411580900d0844c200020020079a50043c42d80009180c2418950203c200d104a580d40f42c520f40b41c81c141c10141e446180e081c1008080000e000240100f0004559904104203001e8091100380110304083c442c0596400d9191135000440d011039956541c0c05c15400e007040303230f40c6001d414040d0090381055002d0081e565000320714440e2284c0010b43c2c40550104040c050240002c084440640340000d030081101000980d07007091100c50b0041e800b1400e00e001c40d002d900 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 561384685 1250 561383435 561383437
    0x1e090b1905041a0909010e240a021b030301120c05010f1d01051909080601050609010f050a0338041e1d0a050a0c050a23010e060c01140c09060a0c08 65
    0x160f103540c4044c1c00c3c000c0c040341c6801940701b05c102d20300050a0345c5004850302e000345440840820f040c0058030900700003402c018450f6003e1704e2400740d5000702c0106a000f02c41e40c280f65070000e80205226528460b03217681041001e041c0300004190a08161501110a15002d4055001049010010119141a003179140e1082d4112140203e0000304202e0400c0100030007071000714580146000c0c2d00c81d201c0045554680403054401c004416514120300c0b10305180300700d9094009100328014592101d40c01d03903102c0b103010150720801815a521124000c0c1c068141c1440d034511a00d9940100d02c0d00500d80c0c2004050030405031214516940824050b0b80d2005d40d040c0740301003003c040258000d00c030102d82000001b00e042106103020f00d01403980942c2701c20030040d00403902c0c8203440c08094601c0e402100e42010800f4074448802c1418402051001c000c0498841d42c04a50240100c0e50360740791085850081e0071056800c000a401a07504209401c1d010607c1841490048010700688209036405c120100e0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 561385935 1250 561384685 561384731
    0x17010e031308011a1c060908040e040317070e10050f0c03092409010305090309030601030c1502070302030607030207080c16090507020f0a030e0303041e090b190504 72
    0x801120766070300311803065552000040c0038000702c6508250f4084010f0720384245210b406500204100c6005907490151000a10701d1002101c00035120206800440c1456014200824810020505034903061038000c0800b0b6601030300b001d0180d4403009000181747d00c400703055420388055444001540d4145402e55090003954000b5503a11800904550700c1c00c0040003030986084140c07203501e4941c1c4040d0b5045c01c1660515075001455000b40306a200540c4290415a00401e4003000c0e0b0b0b04d00040f200202e801c0c041e098100781e960002c951001c008095003030041c5890290580b010303101450841d40000d86a110181102041540200da40d40503c4001c1084411201595084030500c3ca103e800d5002034400c140b00d1204500c0c54400001c2c111400441c0814007422107102030011800c41d6a8180c400f65924a10b0b60340610082c0004100d160b60605002c1240002c0b60615004600e483e0040c000c0d610340c0540140141c03a01c4110704c600032044181d0500340c2c3d8080f1404504000c100459110101c918 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 561387185 1250 561385935 561385961
    0x40f020f03040c030309050307030b06210a050a0b090703080d020a02030919080c0108130f083001050607052e09030518190303030e01140c0c060f010509011701 70
    0xd10041000e20f1420758201e80c403d40320781c0d4a00b40d0f200c08064545807688400341030840188009005860603244c141c104080c10041e0002202c00600c24503c2d010361110110b070030340c0c4009108400d003c5003d21040d8003d13206401007400d14250380c2d40307100d03a024a1420811094010440c110114020b0003622203200c800307031882d080016508071113200b024041c0b042c034029002d0740f90002c00e9548102d16440c80786110710b06000c422042c903501c54680c0791582c481a80c80070824440c210710140d45840f00d44540a16580108207003031444040108184117a00182c880d038020006000004c40203c1c0f405c8a182c20300820a1102d040080507440f400010840401039610f0582c1810070103401038050261401c42e0360042c0428001402440349080c0108002160702c1d21300d4504000091181d00314030754900c40786001181e0380700802841681840c00307a4a00d84211008200c4080c40e490802640d07034410039500300d040e500d514110100340600c0040c080c20f103000c1c0c0c04800916540c6825041192010300d6 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 561388435 1250 561387185 561387187
    0x102120c0f0d18091514220b030705040b10082e170706020303150109120317090102030609011203030e10020c0c01020303060a0504091712101502060402040f020f 71
    0x800da40209040c0d00c18045030004100f403000495112010700c0b94000c9104244a941c84c803d0070901a583c050300034107812548000181c0350554a03902d90024200070f00b40c3c010007c031312007220303504060400b601b41d004580100d140c40705120081d911035642d01c55a022a0810044d180c4642c0300840708980c52441e002800c44a4205103040c4910845120301101e1031001404c0900c0341c001ca482e038a1b501544140030042e80107001150075141d40c10001c1070780781d038141045a926a5145419500c00b07041c3c0d0015800f04041c4d1007100394441d81a28101c0c0e1100e6104000c604d1460000e00151007218180100e6820b10140d18054003010700aa2164041550030021542c01e03c000c50030403006075106001406281c0501c041c0741c516540004283c1b8040c0314004c181c2d415950a0400b804001c20301e418064a1550038006510713007041c100300c0185490b648007407040d02e0900d8603100f0a029120280c0c0075091441c240200a01510f41c0420f62079003080c0d0454000c54014040707203003140a4040d40780f4051080304 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 561389685 1250 561388435 561388453
    0x240309021f171003020414041a0603070314070f0608010b0f180d1103100c050d0c05040b040e04030e06030402010f11100c0e04110f1917040803060405010f050102120c0f 74
    0x541004a0489200b03c86c1400a0181c0040180b154142030f14000d003000400648407030326150300c00080b5130210024041340c41e031956a80300c2400c20f035004207050760150003104091104140d00c40c49080035001740e080c0a0b40c25403500d1703100c20040c4203804092040b17800120f23400d10030700c40100c40d011295034001e11500003400c0030705041001e00c004804581c4640300700d0002410080075030150142401903500c4480c1000c00d483c001c54054240201920308107d0b0421010506400e1035002d00042c08520020484510345854040d01c402012800710744201c60500401c00140c2e1f000408d003e61422038a0070f0440aa08006032616010008405165080c213010042607169403003e00701d5100c41048030140710001d40404140c41ea8812200c1c2400300300000c100081c60703c82e003c034642075071514919005110f500b484185014404055504a40c500b20020a0002602d000e0046501400f40c10750000b0f441481c0500103540c610020410700600300010a04903030300a07080c410403104040c500180c815400d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 561390935 1250 561389685 561389701
    0x21060f130e0d0f09120203100905280b0601030914030a23211f09060618050901060c061407020d0206130807060e0313240309021f17 58
    0xc03490038402118412801510640b40c45181c0c0c1c0401c01c40c45032078103030049080040c03920045080704005d982511542002c005803d52070310403000c085000d80f01400c0007403040e40c000c1080400514030000c0c201046255000421141d844030f640040c000d080008903e840b42c540388a050b040c40226240c1d50101040c0540f610b0381044807464104211140e98030200000f404a183c40c1c01002490340c0242005100d20341d240e00210340030f0f0b8000c02042d694000d03101901c6903101c41c02e40d00303030401810a51120001c10103190032048185030801c520f40b01d00003880c100070128005040501c58902005540c000840a001550303010080300400b0010308000e41c54241000b96442440c8521400184144000900c50041002503050229070250030f692803c811601c2c1c0801408940d6100c42c0c413804104580d840380900c0075900e600502021032481d103081b800d40d500100001d018070400c0c040c1030510b40600010780e556922441c0c2c00018540118a40b8404102100d280380950f1115402d911441e0500c001c0c1 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 561392185 1250 561390935 561390941
    0x30d0b220614010336150618290d060f0603020f06030903090409030e210d020d080406021303020d0605011a0f0304060b030c060d0509070b21060f13 65
    0x5210801c00c018405007407800110111075010022000198246404403800c0c00da211080d03041c031115624a0300044410f4841450140d080c8040c144010f503607c001b0000300e4035000303900344110101034040046404400c2d1010503070315202c502e00340c0032502d07a103940703055076032505035100040e008403040120800d80b02c2100e008100d46d000591103070700c1e10050102e0915009048038450f281c818040d40c1061103880902c00640b000c45021010b00000400d000640d80394044800440d00310030203000140d50034012004c2c1003400d004a19001c540101d042c1400041d001302046030040d5100307200590b0307043d4444c1c00c03040a03010b41c2c0000f0752181c110b840040034400c003034000724140c9842190170b00c1c0700100341041c1061071040340d09501d4940800c0c000a4081071841e4060800c50201030150b510a078401070000709070b036108a04082e003840d030b640c09029041e071040085101400314541407600c0c000d5050000c0310546681105032040000344400a2100e81f1542c01240880c1e90203050b804034600000140c0000d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 561393435 1250 561392185 561392189
    0x1e0f030f071409091c0f0c08070b0411040501050a03020f03031e0d060f0311060904060306051f051002030f281d09010303080a0e010e03130e0c0309030d0b2206 70
    0x480d40784940442e145207030200e010088201140145d290418041d101504c003940056510030500140c030080d00c010a00701e5008000b400d2042c0034517002803402d81780c46481ca00c000a4114011480c010051020f6190300020340e0a8070380488450300c00b608413100081c55441542014a6517658048111400f600ca9201510105005102c28483e10f0303203c069005a400191002824281aa075100e008900b07080c001800306110160020607165202e484035000d4410654400382c240b003805c580c1c4440400c50041e1800a41ba003103d0383c111898200340025920b0060304003040c000c1300001903da06101880c135a9600f0304001c8101100f242c1031018000d02041800f50031082e84480b0001241b1161070f02401990503a9410b8603107810300c0c3c45042070b2034001e2601d144090388642d614041468610000c0024042c1c04003405200384485080010b5085145009480c14102c1c0e5804d006000c016003010095488802e907140d000181c0c994440c1c000745400440741c184050b050f801141d501e480800c0c0e40c2004007 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 561394685 1250 561393435 561393439
    0x1b030f0b032401062a0809030a260702030606150c0a03120f024b0d0b09010b090f0a0e071707110c060c012a08061e0f030f0714 56
    0x10380c0e0365803055803805c2c0b08902124100f81c8288484031212401900141500d0041410394100314900d00820300d4146054000d90320561410342c120804c40c0300d9003401d1200d010000f106c0c1c3c1400d180b940070a0351040c0c0640110701c01c0803030500c004102c00b5901e0964030100c40c2c1404540301071000d0305014141c20450b0b4929030020703050000e40880000c031802241c20b0b03000c402c01d1200101c94410b0441e501644021010400310840425a40b103407184100702c3da118035440d21506640e00051031400d001c0f20840607146004504a0004001d040c40c42401e9502804050300d0780c69070507090f4400070345042d40d180c01c0000442601c8042c04085980715154040c00803000341d4081d00c5448501c429a98a5101c102c0186a603000040040b02414050064495800e0000001c079120140c41004c8440110464802c031201d4041404909400ea1080c1c0c01600400182c81c562401210100005c03602e66010003d24003641c01d41c00003403c0754500700311090003411580d040d02c030100d07190101c28001c9529050003c2c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 561395935 1250 561394685 561394753
    0x106050309060601031b0804020105040f080303010f090603030504120602042402070806192c030a0f0c0c170a051f2022150e010f031b030f0b03 63
    0xf0b829502030300c5120051240100d8801c1c00c0100c41c00c5c00c48030450020002c82c100841407100151052481c4070b440e02404000c8007441e2658180b40007140c0c540441d621400c8c1d11400e0000c10004030303400000b240c2c103491f042d03004a00a0f542d2410008040d2103180c0c024080341c010810f01440c002501080303521140200e81c20340300300940d41c500031580c0740025078242e01104901c8500c0001054154032405030300080354940c416800800d0100425034002d007175580701c103030030001e054034540390b000455101d03d0500d400d00300003280c22925540d5120b012800b4004040410720f8001000b55010400305001640c0b000481d5488109402210b410300194420400300e00d0030103802e0310450142900340740e15080a203c0007801d00910b41800d02c3c4d81c084d40c070740d4140e451f28225408200e200410b020003070900242c1c1c90b84016200e4900004040303a447c5c02c43c2000705803825040742c00f100913038403d5052040c80d41c42c001c0317045044078482034002e14250b41c00da82e15229402c1c00c141c0418143ea000035060750303034030290 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 561397185 1250 561395935 561395941
    0xd110307031409010b030607050a1b03110f0f0a02010e0315040309150504080604030e011112040f0b0304031d01030f0612050c0603040f02041a0402070c15050705280b010605030906 79
    0x3e01d090392500351031170f64150040700c001100c82e0b2203072004c0d0060310018a0310b4030180480f510029151f04c80000154005006820380c506210010081914080310a84c010700450340e440c0b5019458015654000341000500750021020b50380400c2004c49001a03009000ca05050610f0007a1101c515803080c141c00c3c070118903c040c1e06074016030030f07641143c402d00084c3c8003035a501d6408032103101001c103250f0b06000940c10300d0f1120281c20400e1940b00708401214540c0c80e070130300c1e1820b1410803195128803800c403c1001088000baa0202043d850121010811101411040c0c016800341407400342c0048060300e0000d0000b07403a00f11206828059000e20103031090741d41c1860501620344000c45024050500c00b984c1c4200509050344459281c5a6888001c0000042040060b0aa038028002910b00301c4840d0400d0014140103002c100c084006c5003444c0e8548001235903000d44030039000d98500c070004506491080c0d0300000301507881c0920f0b4843e113101e101c1c0d030b110a0082c2854000340c5501155102e48000 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 561398435 1250 561397185 561397201
    0x80c0d0905010219030815030f030a120f09020f04050702010b120a060509071a03040503190203030f0121110a030c0e10050d110d03120e1f1505060d1103070314 70
    0x80030342001e8040c1d51b86040c59548104100c00540c500c40300743c2d0140b003521588403452a060018182d00c002c982d070349040340d00b8400c0b03890083e90641541440c055180080d0540141d480c0505d0f003402d854142c8001c50a40c0e21074a003640140104460715821100c00122922031031804a4085c031498401d507020440303a12000181d941d940654040c01400c0c0f0840e101040c03100100344041c41e44607200e00300b100d00e00720010040459460310204103002513480401031216081007910f255025003200d00d42c0c0004028440f850075643e0380105000b60810615000c406120703103034800e85101840d0002030002045a642140c3d001344203040318480010b164003c400b20b410b19255250342011500f01140d41c12443d50101080100c1509640490900140c0d070003802120416001e6000030a0101000e0002c0a850740d0300e01006404400700d40d000c10f807500203091018501f00340d8040a4410690b07200da220480c0c5001d40c0001c1403034a00c5c245e42c0d40d5010040101d0698582c000c85180740d502d415581d00c5071202c8034 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 561399685 1250 561398435 561398473
    0x10516030e030c0d050c030919170c0609010c0f1a0106140c0c060904140906090c010c0b1501120e1c051315030618060608060102030313080304080c0d09050102 70
    0x20f0004400c4e08212510740d9001d10490182c04490701181c2603a161401c41800607500075215002c0024036089480d040200300d03c45a120711001301640c02904c0e280030038100058562040c1354469040c01207144241050100340440104000e03441480c0c0800040740c414610f2500b1030920950000403074607004248191480000c2e2808031401c0402070200313811a00401c000d90300110b00d115085035603048a0b0500c03808138032669002d81110340c0509010f05145450381d040401260b081ca0611115100d48400507004280c5281d006d048a4100000c641e2184012560802151045e54000382000e622a00102e0017150081d1441c8650310084030040480034207a9031801240804060b02ca04000200104a111900781c9e1400032a490b00196080e1540600400340c0403109110a946035542c60522001d5000840190480001d000440c01c603d440f846040c044120711030010002a40400400c0410542c40c041e102080d6004d03050b1000c008100f14010900882489054014422403008841c100340c920 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 561400935 1250 561399685 561399697
    0x5090610031502210a0606022802060d090f050102131d0708060303040b040314070e190c050d0f0e07060908071403160e0406050105061c0518010516030e03 68
    0x940503200c1d04454000c0b2200a40112002d18404400d00c40710008030403071010164480c1c04107140000300d503420400002e2828008010b40a10100c000301100c000c2603192150600059049607126a5109d1400c01c83c0041e028410303004001040f0324616400b0441c064014050080803111000d0a03e46c2e200d008203107001040b02c80003000501c0102090645106904840d0310000c0501140d281c2641c138a403095856100e40e009071441c00003189038241000c000d204540c018207201c002c01000d41007a801800e4185542e107109840765030350b1498000814007400030344505040d00103003000541440c25040c0d02408140e000701849001d007074400300345903000c1e81c0c030705081c0c890203002820b01e0790401d04091106807942d0b811079410300c40c0520b00c00c460410780301d1040c05000100070300e144900781441e1a00a550060308401c0c03080d40240409100401c0711075445c207080070380510116890b102c026140c03201a04000c00200554205800c00421078101060040e850070913603401c011109001e61290745a004034 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 561402185 1250 561400935 561400943
    0x20304200a0e0415060e0a1a0613181401090b01021e030a0e03030f0705030a0f0f0e150d0905030418020702100807141303030e030a0b01230a03060509061003 69
    0x2100200740490b010403001c0c501150b012200180c0381b80c4800050f281c031203040700d8224841e91120f40c15544000010320021101901391170090038603021f2003c1d0414412076004c0c2c004046540b0302c8501005131160031441c881ea002c1d02c60303020596110042e45c0007800d0130303510303890151041030900c0f0031061a101280c40d83d54800c0c0065400d005442c4c02c101c85a600c4800c045034148024407054841072007403001000814030880041d0707031300c801a91029100c20f91080302e075000e01c07120644508950307070000a0385004160846407000303001c58040b00b4184501070000e090701d030a0f151110750010004008014400e440b81d011300b403000b03098a03a506905900c9040c00003908a000d04074500781041c041e6000c00c0d00b090403401d003101148000280b0040d540c0125001103501d11601c0001c1041c140c02002c2201c0c064001d03000350645e4003542c0c0392100010b1040c0301c0c50490780218105003000319511901034044920080058020954030304244002d00000d807540c0c803842c0a428040b1305500a0022004112580 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 561403435 1250 561402185 561402209
    0x206100306052a03090d05030106090b0a0c1a04051603080d0506180a1a01080c090d08220314070303080112210216060206090a0f1104020304200a 64
    0x541e51044040e1002802e441c03907110f45038001c40100d942c011246070054001c1c0420584a14009518914203244003485005000c0100014003203103a0200401e4240d4051050071030350f5440030710007150046e004150203400420380a880074045010031012900a900a80071a41b640c050284072248a44051000a0402d001003200c40c83d040c00365008150302c440300914172031150300a0b045152102c5000c481c02d840751036443c41b031594503102c9031290780504803081c03038000c40c0c615100b41c00c44060300c2803980c1540325840d1700250a04118a0b08101c812001c01078411000220a07001c00201c841603a000031600648140c0808a85081c0051124102c0750195156100b6928116041c500d00c000118252240d01d003051441c442d00c0d0003500750340c041000c0ca90040201080e403080c1e02d5101d61030354201d00110341040040c800c4500300041d005100d0358010034030420303910403454801a00c24000403080e40090020042009000e1b413840d445000241d00c0740b0700100c40e10038008102b4444090300032405110b0f8 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 561404685 1250 561403435 561403439
    0xf050c031c180302090c040e0703020310030201180308040b0a091e051c0602120609060909120a020703050114220302030412020d02041a0a1d0105190b190f020610 71
    0x2102c0c11807503941d40040d86121400c1a140d40100b60741c52001c807a503191907240040e0800080c506c41c80b0282d800020ba260440c1181010700002c01403640e0f500c006410405d145030006030501404030320a0045500400c0690346603a80d0404500c00d03008050003c0108650350400130b40659180d00e00c3e1402d12000c0d641c0317a40300342090104102074001c0c045088400030500b2000740003a82c5403006020741c8042d403201ca607042c41c0c60000c1002c0c5880003880750380518040c80c203100e90300c00c0004502844603166a000340d200c0b1003d24049192000c0c982c400f92103907007002441c27200403220b00c88560103203038000c00103148030708007400310b42c580c10000d031700100141d0042008000001c070807090b628080b48024107a254104041d0001002c0c4d404c1c140790b4107207440407a40070203c1c5152080c098030040c01445500700f003200c1701219446480405214443c081d0306084540d403074040b4a40c1c440c00144c114000c0301500c6040441945a0140500320702c00045000625071204103400040c04a00c1090311454090354a4 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 561405935 1250 561404685 561404687
    0x1061706040320010c02100f2c01090f0f0308060d12080a0605060d0b090901060b180a081501060201230a0b01020c03030406111504080706091b030f050c031c 69
    0x9032100d94800e040000f501d50342488600c0c02e0041110010040c1e00402001081c03500c00e00440d0b000c004600601c91408024006070748852207005100d110000e40010300d101c800c2c0340a800351000503402004400a06140400c05c80c0683c06040100c0c0240d8600c0c800356101c40501c103441e54070400240484a4003401e03103000512403540303560701109101003c2000e80d81d41c80071403100d4020f603409490032500c0e140c40c1e42a604280b82c0407a40040820003d0041e1403070a00c3d0740d400c1b031250303a081000c22103242e844603100e5120543c1a5000f46031070811606099070459160850420070f0103420015420b02c0d55045603249041e064400038071251020385081d071200c06005c4014042c9880715419801420301442c419030702031000d00010b2865442c0c9640c0403854801c43d03410031841099103400e0314503000034000840d03e1801914400365004800140d4040c050411280506c041b070941c403131102d40c075100481003100300c610b44a200340c461411194110910010191035008001c07429105440081e0081c0c052 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 561407185 1250 561405935 561405947
    0x90509010e0307120215150114090a050613080607020d030e03070b011203031103012607080d0503090106030204020301181407050313080c03040902040e0c090901170f1e010617060403 80
    0x5044613004030b40d071025110600e400740507000c40340c00487e41d40b42c07681b403006075801601c8010100079a4042030702d864a500000b92220b002400b54030300030b48011940300d0200741c10211f003c01a140580803900c80e8030b41140020740e241f000c100031000190801c040034403040c00c00000d070f400703643c0e00584100c40c5a081ca520301c2042000040c05500309a2a01c0d2030301c0b074070810171000b103010303103807000d205c0c04c1002907135528840001800f0f0000c052940124810049564049049203c440b1a40b0305680e03203482da00e040380d001d000b0940000c1d502c1440080002442a5100100e04000e06c14210034810b00305482c01290300d0110442d08007000c11010000202d102180d20b00005459104180042c10411901c10b0246150050f0b00021081640014280490083d82941a51140c19009114030340b822450106008050610885012455100400c25016400d00a4100000f07a8078103c40104101c08030080e000c03001d250b41340009510b404170200d0380106580240050407801d00017404551141c0d5421030344 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 561408435 1250 561407185 561407213
    0x40311040203040f1209060e03070f05040203091e0303180c0a091e05010f050a1e09231509060f01020a0f1103030703110d050a120908041806090509010e0307 69
    0x46075038410390341e90005d0100807421320032510542d603426079141001c0001d0a80a001d0003664400c2c0e12540c1d082213845001e0800c0010348406407805030300e0741c40740455076160400c541d12070358020110708605854684000702842c402c0b103200440215905a501d95030707407241990300409030071000c0540184102c281603081440750043d50032403c441c407080403d00c642240d0081e0420051402008020420380c80d0281d413130800742c60003502058000b1048a201d442010041c03060710030076610b404c4c0d0711b18147c800400a1004c440c4840080f09d40b845d01101e405440514880407601c00c24454001c04c03260704050142c0a0901d0040e0000e02d542c0e001502c5990705104018803c80d040401d41d882029152002e20241c4050391180c1c9501c1c081c012401d5905013400c40b034216071002c010050060100e111b9200400d0085840305010014039074109062802040c1b04039004000030307035102128450509815445030040742d0048004000783c2c1c035480e40c1d442c00d032011114403841c00d5005014000c0403850a02c11303842 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 561409685 1250 561408435 561408443
    0x3907021509041a04241502100f02070c142101022a0606010f050a0f030e061f05030a0f0206341b0e0a0e0a150608070b04031104020304 59
    0x4180719107000020240e4400e43c0c42240c0541664445245030b09180c0541000340004541030200d17000191054000600f051250322400100810074080042c002d01c951241d01c4000001804880ba0304603030341001c2c0d031203d0800c8400c40707545040007d5950346040c1c1ea15003803030001d20b00c078520740e1001d02c4e04c1070200ca110b00000c3c5655003081001030000e0300362440301c0c101a01c00e19030140201403000705400c10034001c008505005074182c44402141d40082129003103440c1d800c2803803803280414801c900510a583c01d545442c03103004144403c070540c1210003010f101c071158020804c586c0321001c0c19110014800c00612200a5050b2031005141c1440a0041c174a20003031000e241a014201d10f0000306d090701c010320344a00b030100d00d100034018600040c640010201c42803000075031401032034040c030003001007480c402c1c00e644807440c015540d401d200210030301c4d4200324040c5506020a140d90010010341c4502c03036107403040c1403000070741700304800c140c8040303079040044085240111014000a540000c0041b2 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 561410935 1250 561409685 561409687
    0xe0610081f05130b0909010b09060d1505010b0c071431150315020307020d03230f01060f09030f02010f032702090c0c0c120703020939070215 62
    0x1c1415107800050000c00e0b083c0703000106a204002c02400280c20000d4140c80c0f890b41440840c50715522120380d01600b00c0400c0d1828041c0364903904095079903040c5584404038840c200400000d40d404020050031695141005450869907500c0c440c0303807036140c0d60022980101c40351140e100c1482e8400d820003107914101c901e03840400d5110074007600300c0311641d0807940220011007080c000d12058010702411442c0c0c03010214550708003004080d642d800656801d0040580300d14210200403030f410f902884a0101868101240c00c0004060290040c24010703070001924400207500e21500c034041000031a900400c2040e44d11140390011a10f40c03c12104010516840740b42040308030b001d824240c1c00506041079000d408141d588100405007501038081008450240100d071a100c501080c0c000641000326020381c041c0707451428550030b051a0781d00c00b0354490211400c1000300d6026481e465100d18400781c6100d42c89244001500100090301d01068000c60280708440c018148907490320340b142200552a = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 561412185 1250 561410935 561410939
    0x4050d0f03020a080c06150f09040f05120a0305040b070f23160f0302010b0301051b09031203040f030801120b070e040905070b070c090b031504060908130e0610081f 72
    0xa103111740d22800d06600f5036801413040010500503141102000310301111114845503410001642c0e480016002800c0300a20500c082c04101080103080c24280042e42d0182d11009600c4000c0d00030801240c00341e0b02c3c030000500007022035100d04421030004160340c07125114042c4d9028000c041c103042c96580101640d00b041145041016000c0c44c0c0301003445100c98201e50006460300900b0f41f00b00010440c0030ba81004203100d4050509002d1115668444080b40e444028030300000380380c240d44040c0046038800001c180424010207101c040c50241c0241c50745199640d0702c801002c404864088040c041052040120340100c0c40b40c1100c1410104c0104003256403121034580780c0c1402c2d0140d11040c4283c5c0e001405508100a500051004081000c41042050b40c03104c0465100c05c08001c0061071119814000380c1008410390040c03840d01e4204040e90748900c0d104500844079280ba0041c1d10a0140c00c0b4001071440ca8000e201000104107955507042a442e4032000191058401d0503113070201d6042040 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 561413435 1250 561412185 561412193
    0x61103040807120501140106020c0f0a0308032a0405090601080a1d0d020c010503010506040902090d0f050d090b130e060d08030c120115050405210105070f0e0604050d0f03020a 77
    0x94003e040440c40300f00f800071075854400e086a0312400f14208842221004108840d004500050700f40c40a880b07450300520302400054078154190401042c001011003030020403408a0018402442241c41c04980800781ca11000e50328000c43c8a8581c3c03000c5d00c00001020765202d12200c030b0708098140710104c2c0c0d074240703518803407604610b404542c40765601c01c001ca68041e66041100050034042030030aa0302d10350600c004a403561003a40611185180c001440c13441039103d42500c00c0a407500700c40034125100703003481d1860f00c82012180384800580c02c0c1c200420700d024010200c4501104100a0079007403840d1010014542d40700402e065402014086040003242d02c800003907104803040d51045513070751040b030700e403000b100070603004031107800301c0c1a19840c01150484201c074180c1c3c0007220f15440b0b900080608056840d0b0310300d440390315942820306000300c0d5078101140c08004859a220508518688410300886005610649910200c83c0217042c0100c0c1c0300c0c0440000c09800f91042e41c1c03142c10301c0d4036 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 561414685 1250 561413435 561413443
    0x50901051602071815030209090c09070c03091205161418060f1012090609061b02031e0403080c062a0f390d020619020d0605120a0611040605040611030408 68
    0xd01c0d4049d0740148051859a15103400800c0d40115103003000412410703d074a0041121809001e048110382c0405081c2052000030044501032221039044e000d69641c45851185070703c0f03016000740f4041c1d5186024076036403001d2036100d2440382001038400c90840f070851007023104040918040c0428411851000d040c981090300403906080d009071004500c400703251800c44121001d40f450418982c440c5848024565404012200c3c180348001503080450030b400c602829500c2540e00c02405200300085020040300c000c51028801c620503140000141841e0505c0015140b031901c00c4000110b00700402c14000e05c5001c041e120510300c0c2507081d113598690191038004003090400d003078152000f40c0301c0035401d01d808000c00d0010821500c040c5c405418100d101c802984450681c503043d540c0c004c01d070100e509010707521810040800420000c0300c20301405003a0340380d071a400c0081c0ea505081a0842d00704091a500311030031070756241d864910b000d2610b001140c5481c034105200309940000c000024003003200f00 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 561415935 1250 561414685 561414691
    0x903030f0f14010b0738040609060f050705040501030e1207060902100f1706010507061a040f0902060919030b010305060f0601020d020706080a0f050901051602071815030209 76
    0x554006030b02c0160741c4100e01901416809200c01940810540b000145003034060781104080e02e00d21094004103c0c4142c65810780d4243d4008808100b1003000280440341c0c21220071031f40141070410004500042ca5000d4540072500180401e1042000308401d52080e0301804490b101038040d12111000d281c81c6988940c0b000005981c1191a03140100540c5003131122101c01c1d40c1e0608007039061494070000a042c1010907600c0c800e0700344000c0b0003c0d503640d014208440b0341a0740410708102021401344411a02c4070903040b01d600461615484011081003841000300071600181582d0805032403c04101800300864229625001039601c00000282100020f41c065031284000d0810762500c1f882d4a001410018000390440d0300440380c0724452070300480c403041a10000c1c034140200b9690300043c00040c01c4144d0091044a2405d010401606019070040d8060340c0c44404210190490032000c0784d9450b0f040c042c410a404422032180e03c050701c607902c048101302d0b80e4400510526075a400141c031104040b = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 561417185 1250 561415935 561415961
    0xc06130b1303030e06071502090d0203010e01090302060606091e0103060b120406200313050f030c011a010f02060c0d1b022d031b010204150f0212031302040903030f 72
    0x201c00103108041e04414198202c4e1000e40d0b4807400c1100c10340318a480d4400c4c442001714450344c0002c50b0117043c1c541152038a2800e8018000f40050204c03514a90700034039401000b50014000d90001c00c99500d00322044506980005003444003441081c9001d0310520108420a418590303101c0e40010340104400103040300e40b01200b614000c0e0701d0141000c00584001a409441c0f203400b035074104500345419401e6079001004142100e420400502d407581ca000f10100000c0503605c404141e07880d0b0510150002c40700300071800c1d042c100b0310346860015251146509000e02c00340e001000018001040708015000e41400c00c00c020580c94882000e504460b18901481c00c01a0081078a480c0b281d001050f80300d0100c07002030015459811407030b0740141c4a0003064407241280050b07001e0844031400940642d00a0000380206460078440e015002d450781002800790405801951071a548201040083e00c0c8241010b0040352000035480e0b00f04402050130a600710245987e61010181c12061482596050490 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 561418435 1250 561417185 561417217
    0x3070605130b07091d22020102120f0d0605040b0604060c11130c030c020c03032a070806090d1106130318090617060c0a110a20090105040902030c06130b 67
    0x14045d1a11002c41a078048507200f83c4014207001000d0401d5050140d0318201036240c444004807440101d00701001d08139040c410110110b4003403500181d8100070540c4406802d0100180b940d40c4080c801511902100564400400d00007004001e0040107171410a074420001406120034403400036040304551200b24101c9565507041c80c050b950035200d5040e003241640010102c4504440000380c1d81c3c030501c000c848039030484c040030005003080c0300c0f40b00c4007400840f01900c00d02a104c0340725541c4e030305c03046170681000d12039484005174480c001d0104024810030131014001a50750340040c0c0b140605440422000c1005065044400c48056090b0300c004c1d122205002c20282d15090f144501c1600c3c020000b203240e0006030604c0480c0c1c280ca02111405403a6040402d50421142059400c0100c858005442d1501d032003a0b0079200807c001c441c0601c0c1c031007104c06a030143d880d202030104451415030001d4055010568038103286c40c00360702401f02c05070417103450b001480d10703142c14440f10f0700080c085c0c0e002c0100e = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 561419685 1250 561418435 561418439
    0x30601181a24070f08040927060b030304080102221e27020c01150b18040c030b0a14090c04080303070c11120c040c030c050a23070803090f030405010203070605130b0709 74
    0x503148c082d040150984902a81d2909054840c6c41e088868000000749410b940302e1042d0380c25142801500c0003842c00e0b6000315140c000c100d54070791180c841c0c40302c03e90070f400c0b00d8940880e000058844181c0d071401a041d840d4445070404010b10000b1280152040d0a0007078448001034100c0c00e4001020b40590000010802116050482c07401c0345191b009001012014818812028000e9100d103041c054100c9010a2604006905400502d28200410340252a409000c981c1202d2542410105e10301690354042503034402e40d404e00e039801a030040c08035070b410800c0440ca000344036540306841c441c0650f500084c00402e00d00000d001c0340040d80303010303819044240010b04628241c0b03d000303d80045402c00307108402017084000c10a1140600c48024040300944c1c410200d081c62921249044514114680d00c5070b0760f0030a003500740c01c11280c1110f203115036400742e030710b46401000340c400300c81d410303001981005030942d580c4002c0d000080400701040042c4100e0340c085690b05040c18000d99143c0c031018030680c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 561420935 1250 561419685 561419699
    0x70915090525050c0a060504080f0423010201020a0e0f01030f0c170c0304050d0f2309101701090f020705030f0a090801050f0c0711030601181a24070f0804 68
    0x240010805125084c04a41c0c40858086860400a548040001250380c1c079450411080d00030725a900261010120703001c41c0d001e000034481980040001c24000510040c0780049080c1c0c418000103800003180104400d0386401c12800030110140141000316079140c5100310402103071210081500020140e0f82400fa040c5001a54140c03c00400700b659455490302c3c0e03c80f2a9070700f0700700001d4410014400e03814020b251284000354444800096018001b140880540301e854101700340c0b0b40c0c4140000b041c840c0850307000708000440e0700b030040d0002030b0b680e103400340c1d1200400c42c0100c42d5102a400f042454000384082c401032034101801412581c0355071038084000d0500143d604040041d038542000c2c4480001c040100b00d0380700700c40c1070200c2d580e0f440c10b142c003141d0400001c52290b050302c510400810ba980000e101c0c00d00c240104141001443e21400d24810381ea106900c1c0c1541042074001c41d4000c016440607140450b1541c80042c502d880300c01e13a1141d40a110031402074401020100d0300744190 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 561422185 1250 561420935 561420991
    0x50d120f1b09060e0619140403061d01150e0c0c01110403210c060b062b0e0102160f0302010902030709050f0601030c02030d0510120303061a0307020709150905 70
    0x90201d51405130303a0b076002600030a00c148146910541c000603503031340c030b0f08680e8404c12a002d04400c1c54405030752a00d980740380c110b01030480c030254a80a0885070b400c2040d1640148225526000e00b400122000c80c50a44950004a400f03440440124402c201c030f90a110000d0094041c0031024401c280d070390700d10391700303201c441c90200c2038261001491285600e86002d62103203031009400d40100b0009070f108241800503d07a481691320840380c41c0b200702414200760740300022440c00310f803003044144030300714030466041d00302e100342c508007600700307680d2000c5c1d4000c40c3c1c0099909500720321a000004050019400003458404250b22a010b843c6d2500d080103951181030310780c3d5411800a0070180f04000058502075120f0142c1c040840d00d840e034a100141c07011040840480043c91101e020901c1c480990500602410701401454003a250008922110340042001c9a104051a50140902c1800c0c040c811002c0c5c80342d14a070300b5485606010214100c102441114094901d5025900700608200d451348c2c50 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 561423435 1250 561422185 561422189
    0x30705120f061608011a12130203371502030c0a020d02070f06110a140a0201030b10050304031808070b0c0d0207030c090e0a0b09070e090a050d120f1b09 67
    0x202c510328540d0f44140780c10542e5581541c85610140000d00b801e81d07002600d034001c0c041c00d210703409003400500c40c000000400d141d8080c1e000703030107450217128080300401c0742e4641c0596031443d55440c042c4038210309501c109940481481058010203054a40c40c0d25000d036041541c1021a20300002505c49003240c04222510600c0d440c1d001414005151031000e51075072006102d031a050042a0030082c501c464144010342d0b4081d400700d8007480d0741c0d007000d0459544101100c4102e010a00d0640000000e02e002407002d407280341280e43d40f910f5a034882e07904941ca18800182d0110701c514503000400c01040038051000130b440c10604031515024111406403420802050360400e542100c031084c40031403880f04440060b52440480400d005107002d084502e840da2040300902603900210502031080c02c0460700c0401c0701e84403540302c600b9886403603060751034148014000740240d2054522401c010f0007140c00c4a485400400c0006043d2000314464064500020500303100124014a90403029006054040 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 561424685 1250 561423435 561423451
    0x170c0a050a271d0d08070f031802030a03050a0318110d03020f060103080702040c0e010c11011134180b12030a0306030b220615031b060e0603091902030705120f06 71
    0x3655040c62140501204080c18487e41003640b5541c0a5100001050014032007541c05821240c1c01255800d0042c0b9a4020312800c10029061410351408466400320001440b500911901e0603400d2410801141050f076600443c154000c4020a009001d41480306a000394000c200d4943d45d0902b030310400080318001c9040c20240000c02c1d000440a0340c1c001a07041016610501002c203034060400142e50000c000702410b801d41c80360200340c4008000414045c0780c00506042c3c036102c050340380700307a01e0240344d85402101480f038011401041502266001076086100180c10340d0801d2900b2a28203003554025101075001c00c2d1034150410030041c1440c121a401038440c024030400320308400304d1140903040c149000d48000e490390b0980b54a105287c00e640c004550040001c05840c044248841220043d4407488000c0b80f02055040f641e0304040e0100c1c0e200300c0314840034201c1c82001002e40c01d0020180d14090760544100c08000c103140d1507200202201d01d08410003010003080c00ac03220792901c007000b08480307 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 561425935 1250 561424685 561424697
    0x60301031a190c030e0c010306080a03050306180f07090f0f0302090406180c0906120809130e060910200703120e010204170c0a050a271d0d 61
    0x42034103040340855001401a10285076210311072001103010100207900c4482d0700c0c0407100303040141c06510810014514070140c411104619006404a0b561807140e00340d150082c96800b00001d2242004517804040201201070010f140051070380801c0040741c006110750001c0381840041a0800c19410044c60780200007a802410440c100e503140b440e51100034018200440032404105c4550003070902034520481d05c0724000c090b0306002e4200d030803c0c0f0071511040e02d0000c0c0861070311000e40e03001e9102a08181c0007840c0074089401d22000e0b20040042c4d200300e070303039420a03160025000c2c00400d00542c1041c0090031024000000f100c103c070b2080b56092801040403111000a180b02c00c00d0391806070700741c1004045c03501d048004402400400f142c042d2076500c00100410b0307401d20808065400107490040303545041e01141800001c0401d8007031140c1c000751000c070400010085030003211045e24140011005941768038000001d46040441e50704942640c00c850681c07020080252080a0490346051 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 561427185 1250 561425935 561425939
    0x9020d0f05090f071505040518040b07030212130501020d050114030106080307020d0204020a110610030c121703060d020a03060906050c070b0a050402010e030f1b180109020307090f03060b0906060301 87
    0x1e1540c0701c100d440380280b05148004030a17046030040c4291030041c48040c0211800c0c6000030112600200125000c0300d000c21301c00f011481151003071080d80c42c0110b49890021007901d0383c0c07181855086110b0030850b0950340030042d00d2074250320350194600070400842d03071040020140080509490041e004002d0907070090007600c1c05030b507407003400107a0150183c40041e9549460202240c1d504803408105405101d01070500220015a400d1281103902622141e03690584400c42202a0b121601000d007042d01282114640005541c00868100390000c2074425401195408203450f1015a84199089660b0b01e00c1e01c802c0c08001d000381540240d0b100030085c0350090701d035150014504050400900c059035000000c046900404045070b07034440082c1169044060060466610070403014130b281004001a1141c0c0c050a0441c810b080d4501d2031840070f08144c0c00c10080c0c3e00250801460b80081241c450320000d041c1c5141c1c860240030f0350203244b01041449000b401d0040701000a040603008100170401 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 561428435 1250 561427185 561427213
    0x60402030c150f030a06121101031506050909090118080c0601080c1503130b0406020a090807050312090f0406080604032c041e1b08010b031e04030909020d0f0509 71
    0x1c0b100030311004840702e41c494895882041c000e06c81c075000501e500400340d4811080c040c10b44444060004241d0b4148a40c51410800c68001c1a640c81100040342c1d051114658518100b00c56680c0701d100c020001940b548400050941a500c554058548030000104005101410b010250251513880c00821210070340001042c4500e2040d011110601c0d0084081170f1829400007088074140d402001001d20f83c14a810710340c000754803440d80000440c03040703100050019030101d5010107c1d24018081c0c40341c460741d0030361000071394001a8a2507100c0c40030500720200f940e0391712645018145580c01071032103140c1450040d00101800c003549003c448641d0f1a10960b088850f6504102c0a040e14007080483e40b54440136100d2881c0340310028010b0800426580d20350008803942c9241030942d41e0080c07184d80e80d451450051005aa805202036030300c02c201075144209505031a00a4440d107008005c940c0e540c0005002ca800220140140035200c03e810a00390070103001c1c0982200150b40905000080e400c5 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 561429685 1250 561428435 561428437
    0xe070602030703051c0609050901050f01060516020a0b0a050c0d0c050703120516060b03240109110d020a1d1c060b15030901061e060804080327060402030c15 69
    0x8001002c101d4001076030082038101200780100c84104d17038400d000464641c80150041c1c11b00311150700c269841c2100241c502610303182501d04856140d110a4a00300941440328070030750380c0040a0b078101c0f00c461030014541c1c0c0a5401404140a2586c910303481d02401c1c451103040c012401008002c0001d00300056000c260085920300480742c0c802600108800f8540c1e00f039a20340120301c03481440351101c1c2c035070a0601411740c04c0041c02a81c1141034039041340d11101c01e50b01a0345034000394007004500200500c80d0003002e520149448081c02c48640c00e0100d00803880f001d992000d41ca1400113114603902030595000c55402c2d81e00c080007110b24a200c11041404e88040e041101c4024003561f45131100071035580c9940790004000c0400d82035156403441c20251690103007540d0300c5034800f11000d08407140c0304110340140103002d48407a030740d800150b91600d454000464001524210346265484078404194035480c00004003801104040c14091030940101400c01c0010300ca0700d40982c2140302590712900c5000 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 561430935 1250 561429685 561429697
    0x81207090e0705030414011803020705060a080c0a090b1602030d050306010c0b0c040909031106010e011503090615030b0f0c04082a0603090a1e0206072010090303030e07060203 77
    0x45041e545170b50766820100c1c0c40ca180001e4100165291001d00704002d00c5040c10503d0050180e0201c5905a80d500b05000051142c582032200007510740000c9401d450101000340302030a024070703280700d800b42c8031080c100041d8000594030b2035418030301151208508090162543c0900203041c81e90441c6400d0002034802c000a00e0001c1400b002350001402c120030010654000e09881c48003000300e00c46614004e01515903000780b900047c8101070001550b90003850803941a99600d103100c0d84075801051054024021310a4212450f41e191505040b1018001c0d00010080d40150300c1c04a09040c1080d860301d5802002d1704008100d201003200740182c1a0000e50303001482424040e2400840755511048403641c004414143d10003800401c2c03090420000134a88807071070045100c0340d0040d203900c0804402c00c500c184000e401c12814455003001c28880d045007400341005d480d40505c4240345600148003030b80c7c1c200314100858a00700c001d2050503810b110780c2d0481c51803103008100315410040065904d001d02 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 561432185 1250 561430935 561430937
    0xb0c0d230f07021606032c0c091306050f0106110f030a210501060216090e0c150915180105090307290d0c030c0201090b0103170c0a081207090e07 64
    0xb00d001c1602c200702440c4100d60f16003150030080c0d02c6a1008016201c880310300c440c8543d54101d0350b8400302003080604041d5207800c00810584450034188000b4840051640aa0741540d440c80380101721540943c502c1912640c00e11400c0d0342c104400500841c00385c1000c009642e11808400a101000108660448201e4100f00130800e04070440b003031050610702110704d00071303040800000300030b500010000c00100c69000039007011611100c10808880c4c0503061582030703900004a05c420f5003003000c1c11030340c480c060228244ca800140d02c08259542c8040701006542080042c10b9081000c1c40d1b02c400403010000d02c1d105141c4910f11000a41c4c411482c000d50502c0050440701400440c99440d082c2820a02050f10640703070070310201004014681d0b103402002003810241c1c0d44000c0c1e88184250b001260f80210101e00503421030b2191100e0401403042030303180003070805c0150500c003010840b8a080ca8401c0719655628900c0e010a0b109d14103001e0071103000d0111640f0103005200300b8890040d804009 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 561433435 1250 561432185 561432211
    0x160609050127030b10080f0106050f0319080a091d0f18030906031e09010c020c0d12030e120f1305030c06030103080d14070206060a0f08030906070602070b0c0d23 71
    0x7070304104681401c02d6400b10a147c031990b00c0004084006410007401c50300c088a03a450701c4d05421042c03540b00c403824080d000303500303209044070b0b400a4801c80103800d1000c007900e4083c03001d03a142e8006040c00140310702404061441d180c200440b50085c501d1290f48031a0308030b062b003031455070000807982c0ca000e45908544103203c00700001d15980b020241480d00d03181300160f150501d0501440c254003c09850030038a0040c010700c190007a060030011501e0b584182d00080000004903050b00840042a820800301c00b28003071103012201c104000d0002d0229400060411035845295480381000d04010b540124000c2e0400400c00c40759542d440d058904494108a00954a0504811803401000d103100e60b804981d05d100e003071090f9517500042c8240704810540b410000c3c55100c01014001e00707400e00c6030400980c810031102859041c50b00290250522a200c05070030f00c46207503121817014004a030030005100d8042509803201a841c0074081101004042007180340034402104949210024013115030070031 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 561434685 1250 561433435 561433441
    0x90a0302040f090b0f070806060304080711180c04060801140a150e06070303052e0b1b060c07022404030b0c0d0501090b040e0c030a060509160609050127030b 69
    0xa0715000443c4080d4800540700080c85c003210580c2640109443c1e020010b1001d0001034068180201220700a5400c03620050a10030155502030644100d20015a00000c4028160200b42c036104506d500459400c0341a60f215030402c1001442c03860140e100507416030044c00d2441c05600c0b80c0500e0b0050742c1c1103d00308880d06141c0c40e400e50347c01e444403c0135900f0000005941c41810761542c803103030203802c0840110440d000c0002c0c407444609200403049444010b18117041004100500091005501c680c803030003072007092140d115080040c119244040c0b210300046080071490f1040580607414040c601eaa56880c000548810746402280001861012207101103a840345260701550410f08404a0a000c15a140c0c10804041c098501c4a80c0c01181003456050050f2408a0815911f840140045c18881915200c5c0c6c000780c10007a0501c1018000c403a10000b41801d84a5000702030000c41e103c0200c86460180014020540c00c154407001803036942881311030840c50800d075030860381c02c0380c00c0002e035032 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 561435935 1250 561434685 561434711
    0x70305060a08070311040501120b28020304061d0d0e0609060d0906060302040b04020f091e030613050d03021c0b0105040f0f030b0109060e0a240b030417090a030204 72
    0x4041c0d90032400301e40c4503040c40002007100e1000340c2984400d090b82c003407245e80da03109241030681e40b081000a00d1001c11000246403103202c0c2e19040c03d04480d810061044907440307514403080743e105480c1503d00c961902e074800c104001480c040b40210050200411900d0360b070700001016030303850442c018466000081e1402c0c15540d000c1c16901c40a855a100300030300030107490108008c081e10310049000c0c0d03040040d0f801031890305200b612aa0310310300031440c0c6444100b00070030000c09944881d03154443c0030014000d4258804021413403043c14422890b5801d0401c9081161401072550100c82c00c06004000d28600c4050b1030000b14248030301c0d144089500760b0b1400c0182c4d4540a10303005409001c0030307294005042031030010380d001101c4c010350138007005980b07440444060f42c0980c055461955040d00c00700d40d8008443c4c1c04680c92541e07844004441c220501c0790100c6141c3c1030361184181007008028001440040e40849642c1804d48da12107240890100118810304114800688690307038901c035000c08c80d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 561437185 1250 561435935 561435949
    0x1804030c03081902120601021002040b0409020306060d090c0608060a062007031704030201110d0503040b10091b08060109060f120e031918060c020609010e1e03010c08010e07030506 79
    0x803003031081d9120100089085c070320f4032049074101d00600c140012210311805910844040e588000c2c5d445240c00d080042e0b41010f544058a482d410000800450408401030700c07541188600c00c84205d01c50502e4088014506180608070030310075480031004000345a0402c06030340c011030500c005001d0309a1050010f03811300429610181c104141c0381480300580320302800910980c0d200340c0310055083c2c444d501d200d0b0390721000c440e5480410004c102060110350300540d8954441d80c1045002526600e8844460a8400d800c030703c02c0417918210480c448040e00007a00d030707501060a282081c0c10b1883c200d0001d000d4560410800140026040d100340040d00715009020715010701d9048951364400322000c80482d440c82d42d039481c00980403454000115080d5071207402200e284e41d81d0248940c4264081201d650310040320b103170620240b14040c40440d2264070101510f03030300811404000f880000103250035202001420410010400014000d020f42200f03000d4100300e4078503000079140d480340003060318 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 561438435 1250 561437185 561437221
    0x5060306040947010b0a140d021c050f040c05040203070c05120c1608072c0f09071220030c150a030b010801031a04050c120601051804030c0308 63
    0x8040015615440d40c00c030300b4030082038000c001580d01d114440c80c3da503440341c040300038003400410307010400c0764001e07080c882c0da0110f080702805441c0e280b0700341c80303210300d2001c81c1c1c021075850414080340c0018030000031032480342581c4856101007000040c50710703540d00c40c810646030145511903607001c000308541900c181028074100d980042100d00c074848061f040e03500c603042881d58881c94412140d90410102c0041140022038000784000c0c8156820318031800300c22005070701281c1c1c02d00480011004403201003521240038594400030f42050781484658a03003070030401d410402d100301400507003800003030f802e400f10001900d955014000030a10000040c0c00d1500c03001034a80c0c064001540c100400511800502460815480c10483c007202c0200560700d82e802480301500c408402c047c61001c03480d0000d901a8011321940c181c0e0780340d0080e400000c81942130b40aa00b03142d0790000c0c00501031810714001740d1068051403617424084e0b03c1e041e0360042108606480c01000c2250420108080310401010000 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 561439685 1250 561438435 561438473
    0x10804060c05161a0a09030c08070620090a0608160c0f05070602030c010e0d0e040c0909020c07050f0a050a05060d200a0305070e061b0c0d082101050603060409 70
    0x3e5283d06414071848290b6961804041c080c14900842c051140a1003602c1586038140c0b100c0300b480301207071550034407900320240569429485504829010b94183d40400301c0c81c5010401030748902100081c0302240580c0d030400400d008101c01409030304030650401c10400382407460300e0180413205d07150456901c612180c1c010308a1043c403802080c161b8010000c1e14860440f98000c1154851070195581d40c0d460006a890104480d4802018142450b422080c01250750b41801b04c441c41d07884403050103c0c1e1001c21000c41036046101c0501c00751410b803121240c0c2c4e41c802c98846500f10b05140c0081e400302024030030306120303000025600c055030280340c114010705260034803103a111800224000d401e55120b09140c1c400203282200141402c2d018400d003d20b00107015000c0b03070070403134180d440c0741c00100405c091900e244114807407203420f5540c081501603414427a1583d10b480740c0b95200446040000301c0c9008000302d510000511607030701e034181a2588840f003264003080311130450504102c259500e002200e = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 561440935 1250 561439685 561439717
    0x1b080c101101050705121e15030c09010f0801060902030f13150207030c06140403020a020f0a080601120b07052b06051806010f0e0306060f031f0b03061005010804060c05 74
    0x70402c1c80c2c0090103000303052a80e4241807040d55030b0240c010502d00d080c4102802d607203038000100c2e201d481484c52406810340c01504544440300ac2500241c4064000d91080308400401141445002c600380140740082800e401c0070740c10740c1480c1c898045480e10090003032801e403500220038030510400c0000f554041c80c0d80401190395080c42c0c1002031800c0d42003e0280c0b4168244100e070341c46041d0f114002da00c21034040c0d0203400c8000b803c1e030030000c0708460502229402400c8000105441001340465402032100c40c1500c6542c1080d464962041c840c020000d1091050034011141c0d00d1240703440313480d4039120400c4070082d82008460210000d00c11900305981181c005d00c0350a0110000c2218103000704001d803224820520610720032900200e0400000d81c00d60400c80c0171403060305002032a01c40b20100107080d00c900c05403c0442442030048481070b07600661701c80850b514507040078801d40303401c06016403040218904040c0041d281000140c07000300b030940d03504021050300c1e1180c801e50f00b14100d41c41c901e07 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 561442185 1250 561440935 561440941
    0x429011403011e12030507030c470402090403231c360c12031701081204030312091407030204050c09180901150f031b080c10110105 58
    0x140c2d4110040300c1c500302500d1100f100116407044040d030845402a03140c0d440754a08607060b541100c40d00c081c42011901000d0304030250b003680800f0400380c6d4140300c1980d440e030348440c2480c60544004106061039600c80303002c1c0d0284009a1a40b004240d0b2198060600600c50703268583c45603c8031440c0243c41c40c1651001c1181c0c941400c01d40700c00000700d00c4a200602060104c80301a001c8038101840115251200c044020640445200d00002d8240240102c5035295552040c00380e0303001440b4800c400203459032600c0800c4141108205015009032001010b1400d07040c4441a210f105078000642880b0502131400c145c102e041e0842602c4c545e100014450f2900c80703203c281d588807901d002c120310543c1403070001800204a10f05444540100a050003100e41c5811052410078402a10911403035495000d51120240c1d600c6101000340031054503601c22601d1424022450503a0080750310020702c1441341000811000070708401800d0088a0a0f203d85c1075225095551182d4484869041c1d400c000070 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 561443435 1250 561442185 561442199
    0xd06030309030b090f0d0f0c020a030f02030d051e07050a0f05010e07091505270f06090106020303040c0312091805161403070c080403050f0d02010b042901140301 71
    0x803010859101e1a550075113500d034400000d4643d01001c100340b02c290b1050140488a52188100b0340c0d52070003c1c20800b0130b0a8058000c01c1e1034500c950000d0720b2400f0302c16400c0c2c0442c1410401d03002945a1498810700b0004181d14071081c1d440030f1441c00c00a69030211384841441000e0003410415580890500d02f412400c3c60154040d000b109c84c1110540110500028000418014020101403450b00c040c040d905210400000340030301c83c0c84503208038051400b0120303141c034013800c1c0d03004a5400d0f21043c1c591a0900400c003c0d0f1074140c02480854101f841480300284070081d0000036240d110000c8114000910700442e030010480d4001d805403087c442c90203003403c12640c400350140410459104006138580030640b1034002c0503200320683c900800001d007042d03106280e4940902c2c0f04000c410b2a0079604e840340c0d8588961042001e526400ca401c001d00300940907c10340c04070798410340d01803001640f04020544039895211074034510103480210180c00380c1c4924011051040301c1003480d070704c0b96140d601d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 561444685 1250 561443435 561443447
    0x250309030207080d090b030a061a072d0f0203010e011103180309010818030d1e0b010810051203090405010e04120320070507030816061505030a02010f050d060303 71
    0x4140c025000340e12000c01c0c00c1c0c8001c1042c0220301c0745911210f40051805180482e03d520007440100490341d900800704500c0144501c9542903c0b442105a4031048981411420740400355500120428161210114102216520340340e068000c0e5850084502e14000302c2d0140c4400d680d05c4816503e40506251700400180c0518065030100544c1c0c600440e503403008179524412003c19501080400d00000e8404847c0543c0d040020804410341e402c0c0440e049405056400720131403103200400c1c01254100031400c40c45101d07140b442c2441c0c003030100d041080c100c4100751428050384d8000c0788800740c199114481001241c0e8241c4001e08200105c0d80d40380d416900c594000d03035080300d54003040700083c2d00301c074445d0190140409014881c4654407500111445082c2d00020f022a0540901000000401e00820161501d034002803d2100021101d00d0841c080362201031140c205500035480600043e103000401a03003aa5080c245900c211030407810680b80e5000b030a5041c5081400c02602204045d8845 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 561445935 1250 561444685 561444701
    0x70e070903060509010204081504050a170301140a05060a03020901030b18041205030c0405090601020c12060108010e070b0a0305060a0801021804050f0610050306220603030e0d0c0302092503 83
    0x40e03403c0016842e40c103405070a0748224810ba00080d13000103a2280c41c803025280242c0c220388030754103c8080300565910881023000c05100340c1c0c104440803004000044c09001010700e0000c0840b003040c0c240d801c260008005000d009841c004065020a610200e03034020760000350042c81c0200100031151406502101110084600300c4200780c504144800007400f4a0a0706d01494484a03c03500709410700d030a100311118000c05c15411403240c10820082c5803500e00e411130f4032180c01c03030241180d503050500007400d544007401848416440b0f4441008400050350a644100285203008203190300d0303081c00030b00b0400154000a000c0d5200187d00c545134a5407034041d03800b0040c16181804596620360410100100444215411403503c2a05500141c440c1000310713404031f802000c0d040c04980202c0b0303113071352540b4a152400d940f59480c901841031503000580440c1d82c50b421150540381495941e0380701c0072401c083c80000d01801c3c817207003c1400201c400600203621101e1340c40040700301d0340103075008000c0c0c0029 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 561447185 1250 561445935 561445943
    0xe0304052b12091707060e0102070614181c1203020405060304060905121b060c07030f180b0309031305040203220614012408060f040905070e070903 65
    0x21803180719180000680c016011420003440002040c4aa101c1510341c0ca20801080204000d51102051201c0b0901800c030a5076030500007040340034100f0401429602c070600780315065512054041201daa44a820a40c81d008455440303503c039075440301500c8074149904040c0d0f0780206088892032030500c030483c07111203141c02040361a11013032418200364124401d60207100d41140c401c00000d00030030741c0d50300f04080c0300c0e105808941d20070402e85042d00064102e0000c0c1c2541031030400f410f14001c1004c008030b0b03800814400361646000340c9540d018045c0b0180d00014014814080d2008200301000c000c00c00041c0180100740382c0d2440c10300340710398407a40201e40d6156204091540400c581c107241c401d0f64410701102c009283e0000c0c2250454000c000407140c1201e000b0345075501c250801e070340d605910b40200100c0072454104184003000c00c2c144020661600b080106403820040315039112910354805c1d0101b0b07100000e081c9421f080c0f89042859503000211503004100c10710419a52060b111400c890107 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 561448435 1250 561447185 561447199
    0x605060729060a03020409032d12150312050c0a03030b2d040b0f04020f1e030709170a05010606020607030f020c0a0320070303120f1509050a06090e030405 68
    0x5480301c46603040e0007034420a401c8500c404052005082950100504500a0829000008040003d40c101400000f141e403240c0d404840031407407064100c1040700540e91500014802400d0603002514540313010b100c06044142e481101d100c1041c02681150900c1c1420019100501500d09000d0040d220f5411414090003000a0710309280810000c1c4100d5180362140134507907508010b080001030031440038241d0340843c90080010080c5c0c1c0b0761005043c0c0d00e1100707008a031039219040301201a040c3c450b840b00311442c0c0030400c002e80c03c1e5120780000c0c1681e0b002170040c00202c000209680c9459401d0b00010001d62900c0008524290005a5540b10b1145554107002010348886018180e008000c20b1601d683c3c01100c248000030b0080610300308803100302511805070320040e04024901001a8070640100d102e03109400c4140350203000d024003c078a000307000d0101d251520200344000c401486134802035544c03040480e001c1445500000700800206400703000010042429548985c058442d251140c50b03 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 561449685 1250 561448435 561448493
    0xd1b09060215070f032903011503050a0f0305120406090b01050a0308040b0901020319230a0804033e01060609210501090c03061a0102010b0d0f0606050607 68
    0x110025403810015034408008102c1d03112403030b054440c0740c40c01030100c050585a291420b4400304000c02400101e102d9261021501074480a25084071540c0e00c2d0721021401c00d4809001140700001c10408440d0300c403251790f0001c030003410300b1100c3c0c0c014050907800d20a550020b00c800d0203265041307907070311900841c183c10347e507603a51041141d404502d1100500000090100308442c01202000e003401000c180181c07490700b0244816030480403241555900840c0d4042910b4000c404260441494041c00c00e14081c902091004007820050b4010002000c1201807414040c400b00044044031400c4444180c8000710002c01044007241c4500d504801895072801800003003240c0b24000d02000c40710083e028201922401c1c1d484030403c3c5c0d2840e42034680e0764942c060a40082c581c440b001c0c0046004900001c0c0210680200c0c1c43c0b40501994180d0440e8104902400e031350744d0b9803103030002c0b8581c0b210001030107a90928003040544011f40c025507000e100400c0c1603042c0038084480e085100030304440d650b4018 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 561450935 1250 561449685 561449687
    0x3070e1c03030c0e010906030b300606010203070804090513060e0102040e060f0108010605070f080a03020c0c04050105010503072001110a090905010b09091f03110a05030c0d0b0c0d1b0906 82
    0x84c1c0c00c2c3c11200d00041503c0810005280030b6130160002c1d00010b0844a4038840003884040d1a540d441c0c030710410514119200440c80e041440811707085242480a5481c025007030b120071150340541e001d104119541c610101e42c8440130644410041170f4030081c2400340c40d590091080c000c2d00103120394103018502c0c00014009191a0a2145813000142c4401400d030742450801c844640020000f1250a100316000d6000f02e9014005414006070035540517a403449503e178107509180c0b038800f80d280902e0a03c030041c006a138218040c1ca5000b0391603c2c1020074030341d01d8424000a02108110120b4952918282545850902d401800b20202c151201c018460344d40004000700da80921a610b9140024001e01e500c40c501a000710b60040084100310030f402c001c0041e10402c10030a98400c8400c0001c0b41100d042c242000021034005000890203002009415000701d018945030351002000198040b00180c2007600701c0c415110380c500e22590070090305201d60030005030207200104080c00304080340e81c005205 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 561452185 1250 561450935 561450947
    0x5011104150e030712021504091508030a021002030c04050a030602180607051b0a0e0f10140a0b09010522081005041a07110f24040507060503070e1c03030c 68
    0x81a000f078014030b4014542a1402d980e284e41d20b100700e0b8014103840301140103d0415000e4405010918400185030201066007030092503a0352225805420501454400540114042c1a00e070000c641c051303500e5807007084109591103582c00180c0d10a40d12078010003031207101c2c0e0242000c048208041001d02c0c0388841003018602840c100140280e01c051400c598030054200300e119104c001a1810351142d03120600201d004000329141c1ca0465400020843c2588561b03224000801d10181170040c0c16111402007036800d80c40e8010500c0702d06001400c242181d1060302104d0709001650002c000030700e18444080e0002031584260700462064111440001c02d1600c14907028952040e590300181c540f075032042018940c000c000e4414801030544d400d444140034082e91010040e440050180c58103021014140c1c050020819210292040b08210014400280700c03010340c0c0c01e41c107005031250b07500c150480e610108156042e410008112030111a50f18200d00808628440d40707042c0311746403e04a0860706 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 561453435 1250 561452185 561452207
    0x30102040e2d010e16051305010503092404030e060a050a080a060b0d1d0a02010e01050c160f061101050f1f0302030d0c051605090f06030a0501110415 66
    0x18101c600000c100c10081035100a01010b049400c0e80d07200c140860a18888400300360720200d11004108108041c0240c0b28454411602960034042c1c20040c080040103547c55071400b4090604c0030000115015034400c110200382e1114089082c450754500c074202c072000220a503000c07804501c51608090071072400b00c0c00c0e112114803540e0f40030304104010000704c5a00d440031f42641d185641c1e9020119400c240b4100510403400741d4400468000300c12103000c04802c9144242e41d00c1900041081c000503a4070014140c10300009107400c0e0313115441039410900701a42b44685400f4034907080400034551661006010443d441e503180d000480122011081c20799004859103261000300d500090a51b0403c0c042e03010356840e20314610f1f00c2103074807980800d2800b841c001e80100842c02c80509078040000c200009055a48051a450002464440030034501030300a000c11100c418240001503103510100809036006810200a001c4803403c2203003003138241c0c0070b4051259003000000803240d04501030440016 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 561454685 1250 561453435 561453449
    0x100c090e0118050c1201090b24071106040e09070e0108010e0c13090f1109011203020a150e0a06060e0714091903081b010609050402030c0d020a0b0a03150503010204 72
    0x21400050410300c000f014000d1250020036070600500f5240707011002d20501820302c4c40d80008000300c2440401c02c5a0f40c28510400d100f688403185101c18605590a42e09455403200054810220364000102c4c0c1d801240c010300f2207001003008001d101f0000043c00c00c202d550b80c952000c0c959032504c00c09404c1c0c616200c40c1502c0d80c0d1020b14030309201d05068407641503600c504640090b65400319511601c0102d44860284d55811319001c0840c031720300d01a030f40766004181e2218540241007050303401035207480702c0c408080c0c042c50102415101c0c8184a0b0400415000114190f40c1c0d0a020740c0703004001040c03903018070f81c094a03280000403200d40c090a80d42541c048100c2d6014201400300b0200300d012040c12404060026a80e4030000c001402d83c40980b81440d808017000c01041c6d0b442c1c40150845107180e11107442c2504150911000d40c0f80801c0c1d03c1d0052a0076200951050040d0000c40d41e0404660311180b3381c8540094901401c580c15400700700340c10300350142164a15030b103030100360a0340110f000c0d0710 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 561455935 1250 561454685 561454709
    0x140402030a02100918090501060621150b070f0501060806091f0f09150507050901090509041103030d0b01020618151504020d0608060604110301050d0201050c100c090e01 74
    0xd840d1884407240d43e1412441e03c0700320075849400a00340104031307045000c0383c41d07180d0408004001c000e00685020704520310304103411034200e109030341c43c44400f0840c8040b025540c00c0301404030f605080f0310354050800c50002c95520301952030280c4003d002c49030250b031103503e03104010605c0c03c000316840d80613400010040c120310750690584d02c495903601342240381240c1c0d600b0300035a00d03544034011205540d000d007107400110701c1d5050030f00055403001401041004410000119103a802c60b03c4082a41c00544420380310b90740f146031065a05032050762070307a4113100c04a00032141019541150b45214030030303404d450494840195041802050821030000d03600400300c14007400c68070620b074552110034072403078250781d160000200b000c03070780000200700030a2f803502420303c1074040c100040e5801000c01c2e00d08014403602030000c201c1030f00041c0502403050711005031503015a0f100714250307844104560b05640d8410820078001001704a10208000442c11509000038000c03c1a0001c0b1304841c0445040 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 561457185 1250 561455935 561455953
    0x1e0f0501050109171905150f010506070f0602090307030606170c03030d270f03030b2e020106030b0c09040b100507020409020109091b090504021c091e060f14040203 72
    0x520252502400014440c5440640d440f00f40340320280380d82c4c0d00950241810700900d90341f20110020040c408000c8400c0f410041190b0f131240c1701280c4e42150400d0fa1000100860b160100291080142440c5d0500c0381000101c18005070307900c000100d0b40084c1d40c490302c0d1005840380380e840301c06c49801e56a05030400d01c245000368440f900a88010650342c410241c5007144a40f0b084861500c8500c1515500d000801940405400d80310395107554004955070700c00c01c211030490a00a02074203454807140c1d000604001c42d258000d41010005c2c580c0145040d00c2480e01000d84042604903c2c0070500c141d042100d0390040d8104000104c44541d4640d8640386405038580074040030340340c0d0510407810018118000a011000b0b40300c0c03416151801e8507540450a900f4100910072179032a007115110300d05c100001418880d02c020100184200e05102003810000d500308503000a00700d03102e00d02800b100440e07082c00c010300da502100d02007141010130080303114841040e0020807401c8038001e405078800840 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 561458435 1250 561457185 561457199
    0x9030a0e0f040f050727030201141308030715050a05090604230a0336031e170703080907080703060f0603120503071d090a02160210020f06130305041a0903011e0f0501050109 76
    0x600ca200c1c440304410bc0043c0c0d88901203031070b55014203400c1d903c0010340546131000c402d66000b42034004040010910090400950f410384608018000909800d40b49000103102200341d450030309949001d1068030b42028060030040c09101502c0c1c103100c561102e48201c0c8060040492800d9600f400078904080554207642d282889145640c0050903006d01c1000c91b280041c0c040306401e42c01442001140d51980c01da4900034144240181c164042c1c0d40010308284a0705c940080e608044036048240804c0c91007500301c5020042c102500b01a203c5a0910400009990000010350103030015a64140e981180c014052084a4007110f80790740c042c075100f0100d119030a041c0c0242c6820140f0281e11640d58403203a0014201084c02c0c00c070000582c00c140003e002d1200c06014550380004001c0d10341d032030a04555070041441c1f2440c0540b51040000080c0c1ca0401c030544e00c1604c00c3c0a1020f0020421071032504031070a0481c010b03018030420141800030f124400960b81c01183d0491340180c40380e40b0520705101c1 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 561459685 1250 561458435 561458437
    0xb03061f0e27031c0204031a090c1e0603040302070806010603020c0a03050d0b090103050d09060809060a0c0c080706051506190f05210f09030a0e0f040f05072703020114 74
    0x40e000240d8401030003d0304e03482001068009081380c10b0700300140d549281d4a031403942c2981040c40c0e80074050301d2001b085000d450202e00c8941226040341d1b1901141ca01a144e40002022500301c80d400038800700c100010141c00003602001e0722840c1e422205e45030b985200031402d0303100d00b842c200069004610310800190180000d800c0c422508000130489103d4940402c0d03d091099109a03005c0d40004000300c15141c014840f800606510311f40126a8a011861196030781406480140041d59403030110790390314811001c084c2281c1e0301403141940c3c0c0f0f0341e604002c1c024000944480c01c04400c0c0e81c0130003001d07190210840c2d03040b034000e201000311484d8070501500c1ea45580740c03070001440b600700501c0440000380f510384d004541d0310b0441c00d42c450501c003100e0313040d030200205042c0d40c1c1c1c1c1c02000780c5200150080c00300949460700722002007c40c61410041400740c81000000c0d07444505100030300400e00d8000e4a182d40b03d44030844402551058612020320184483c40003034041203046403100b8000b21410 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 561460935 1250 561459685 561459751
    0x20f15091005160c0e0718050f0a050d0b040203010b09250e03030703020109110a030503040e070c0c0303020c100f05180f031c080f040308010b0d0b03061f0e 69
    0x2062160504100c03c90341407040422510403200b114130303418184003040100322610341208040c5403014102000441e0703a0503030a05400f4030b0703204040580c7d004a0f00c1c0d541039101d0016050140010f44010100d144c0808244030a550407031003542007640754125400c0110500748200c3d5213a42010403804c509a488041c0d050150240e420030000c003004901c507407010401045035034801d41c00000c094035182460404403910000c9248190301140c0c0820114a001040e03d00351490216581034030b40307480c0000e640181ea240b00c010f000c01001d860001c10b06802181680d86030405881c14074007410030350b800320b0b6000307a8880c0307420219900b0b0000131840001c803a400c1e545182c0c003400a0324240c00c200f00003480c01170401c072202d0a43d940d00d00351340f24032030380680107580080003200d40b0519400c0075903000d030820700140141801145c0c04203580c00050f55075000f00c1108100502921500d05000c0100065907030140c40d6200846922000001c440f000d02c03420078401c12250b0340c9144840c90b6604100249407d803 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 561462185 1250 561460935 561460937
    0x14010c02010c050f07180501051c0b1302130204030515040816050307050f070510020a030e01050f120a020a030c0c0506010b0a0c0b010603061404050433050a09020f150910 75
    0x4901c0c0103404613001c11140340a04044494001560b182460050503158142c000c54001c07036040d04000301000055a00ea000e0036880107410702550340c1d41d5078400d1481c11051000e588500c543c486403d0f010764990042c03040d64064401d44d10800035039591502c40d000184d40041201d1f2040064040d081c19918210b10200d22900650b403802040d81c441c18038118003072030314041c1604101c8040000e841c22108080034152140040c0a4009040d140680320b48070111900c1e06014000400b05289a0b00d03100300c032484480c01415140c2c60404070040002500000c05080100e842d1108141846009000c0109690383c400006c0480d80c0c01d01c00501c1c200e8002c070540009000d034081c23000f00080d002004840c00781030265000180d00c0d181000016600c10680415402140f522003480003142c105243e0604641c0301c626281062201802c540d880d1400380c00603002c1092806c1c00f84120b6400d282c208110b11802144e8404d008440301c8204010401000070800d0707400c4040148149a0030000ca03d82c5000d042 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 561463435 1250 561462185 561462193
    0x1020f0403020f180c0c0f01141e040812070c021f020120090d021c14211204021c030206040b010504051608040317041209060e0f0609030304090c11010614010c02010c05 74
    0x9036507c05007900c0700c00c014440342e5690345040010100c1c201070f804603904445031401400c2d00340f5850b41c2d0103911031030141c0b1003908449000100c40c10701440d0f600708a55030281541c1c4d42d85034601c2062f80d00c1c81c908070aa10040d400c0c00c4a00000c0301d4125248480d03041c0c2c5010540c0703051061400c00c120400252022a00010090303103000a410006500c0ca54142c01100a80f019403141c04520781058a5030241c0e4485448003841c00c200940d40006840442103280d00d01540c0b521540002100c3d140550f0403000300c400710349649020542e0214145024a228408100e21644c8450810099500840785546082c101c0107640146900c40c1e031404d60464000d0a111003001d0280806134104c00c801c840981e5240025a124800698000e040300d000b0105498107080c10180800011403413000480031920035003002c9202c1c0c103595020b20850780101017610041240881490019012140769440b20300a94a0003000050020389251860540c0030165658001c034120307a8019170b10311604500580b05403007 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 561464685 1250 561463435 561463453
    0xb090405040f0b0c0316080708040609020d0b09030408010501122a3210090b070204020c01020a020708070902090901170c04050c030a0c0c0b2701020f0403020f180c0c 73
    0xb4401846006103504850f50361380f4074161b20040c01c60846159420f00700a02e03042000551584042d0301908698000b13004919030744036000040c0200030041c00981308913a10018000706100c0000140101c454400007400707240ea841c0e403c020b02d21050440a040b2101e0850201c184000004840c0380c0d2082d20718020006039203031090440c105c0200741c40203003c403151025031051201609072841003c1411505211001d44400000748076070181d210365401000041007900455031150150741e2848100c6000715220180000001e580d00c242d8464000c0038011060080ba068905e402221241140078003107600c81d900e8004039540022004066491078043d40c82c1c4a030b12a500d80c09118000c09417800306075140e0901c42207040c101c540d10210502400b040f000d954001483c6010801e034041d440300307601c40c000803244400080340c02207410402032a5100185004030114410b010b4020b50340203440c80d103552410300090040c1c00c131816500c0300e1480f450070001000d602d03c4000a151000e41141940d100710 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 561465935 1250 561464685 561464693
    0xc140705010f0b09040c170c03060f0103021f080f0a1803020601060912030c0f0f05060c0d050a022b11160203010507020309090708070309150504030f090b090405040f 73
    0x1820140045a035a511402c2d0801244900c2c010a075003031800703d40784089420190707074a44010107a449000c4440485800600200d0303024001111034000190558009103480d00b0341242880d400d000c00ca1244804031302100c0b8018070b1400529100e409a107401c0710903201d40b18580f00c401c074000d22901e54036031590342c0d14900345440c03600d0741c13038040c0310390000c0c2469418107401403e80380880d041802c4c009102d905240100e54480c070300d00d12258015041d590b000c3d0050621700040c0441c03080280862003080705001d14200340c0c0d00104210000400c0c100f0813a2a0b40b44d0400c1a4030840901140020801c1400c03800302ca0b06e002c1410061041e44d1002911048001a00400390410800c4000c24159002940150708080c09029441080c910245140c180302c3c8000595444000d085e020401505900040c0854000e9201c0680c0e10307001070703084c6103e07002d20345001e0207443d00300c404400081d403030400d1880c03242c080c080d03800964a601c007003541403640d0b0905200090400810958ee200c0e00943d2041c046 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 561467185 1250 561465935 561465937
    0x10609180b060f0409120f1b0204021b030310080610060815031c0c03030e010501210c080a06020a1206050108010909110a0801090b0f040f11042009190f090c14 70
    0x85e612480104a0000100344050841d12401c400c400a01c0040308629420002c4580a0941d080e411100107860b410710684090310550b40e5440e09101e031200005100381207520309800c004031030b0203108a95030303a035030b20b0f20685110103d4408c490104000d8030102c0d99603d8002d450190015015044071808a032506da2040c164100c01480e8007c82c014001400034507038103008840c43d40c41884001d0203954901b00c01c00c601240002c803240d1200c840b4003111001c00950741503c000074440001210400141e90078000c0080d40981031090206d14249401303d4082140d019030300407124140c6440c040d0f030b0300c1c10008001910100d0400c44080200b201c4141c559502c081c0c6201c05018040c00001d0b51558914100005200c06401f00388402c004204000002d44134074a2031814640c8490003101141038800420301410207001800c91032040b10031107007600d41156003e0503030180c4c2201d5120400b010150544654070540c01031803c5500f8800c0c0034400c9070a25089100700703901910301841d5a40c0034603048006 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 561468435 1250 561467185 561467201
    0x160b0d020904291305010305120f07050a0b06130b01020703021e1f021203090604080715050a0902040b12030f03180d0302070606050f060d1a0a0e010503010609180b060f04 75
    0x7030030340c030810922420f013825048070000d140149010455541180c07a80ca9446005c82680c0d5041e0800184010003665454240c2d0245603104044500700c0609103407082d4414411240507015064100da44255406180103014003040182c0117480d00030300b141c003840034034590003110380300055504500175a070b5202c151205468400050b03003c4c841d40c9018030020308100400d84c007100744400c2442031100000b03000c070309507070400c1c2d01c00c228607510641e928041e030100300c11021441c00c4914000421110b1020394020030365103403086404110032401d00c0c080050310108850030780e03055030060001c40d603200d20341001140c02c03281040b1382594540e4804035241c07810220350350040020750041102c1c801c001140c0074600c09000d04030340c0c00100a281074081200e80c000d07401c00b101010f859440d01e2704040c400b401550b03440500036241030440c030f40350740a811501e0000e00c102070096192000018682c0401c0c404c4510115a520401079507000c942c507a00054070002e05a41e41c4000c3e18495031680755114422084 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 561469685 1250 561468435 561468491
    0xc1e080a060810020c0c040e0d300b18090c060304080904060b07050f1906051807080c03100203040308010b0a050418240312111903030b03160b0d020904 67
    0x45c3d01c00f00300300d49605018070480b15500039400c242144200030300104841d1200c03400b03460500b07584103081d04100c042c943d4800485070aa078546202c501240c50300c0d041416203840554003942311000c2ca000c158094101145c0b10004c0360421009204145481030045810500410400e42410b03c0c01e00090704803907113944201410240050301104111060050074541150750340038100c2c0f802800c0580b0041800c8d01d41c0141070325a18800108148010101e02405a50140c03c450b10140c4421b1070315a07580360710801c02c0c400e22801039003c945028500844c4d100b95130603a034500c04c591a1203052602030b081060418180041808003042c2480810110000c500107490013181c003604900708086180c00c0c04044140b10002082c080c0040741421820f00c144405501d40840c1040282d6005410400c0516454013801d00d12103082061560582254402d0b200440035281d21000d01c000d80c0b512403030140b1860704000c20602c002940640c0b20b030301030b046605011b800800e100c500b1054003c1c441404001c808 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 561470935 1250 561469685 561469687
    0x22030b0108030913020403050c0f0102030c010509250b0d09020303070503030a27050d08090708030f13050102030712080c09130606030c030c0816180f08010c1e080a06081002 76
    0x4500303142c0881401d280c24000c1504506c2c0c03906540303442d41c954101a0300c10b8010391440021a01c2c59100f0801c40e60542103d10081201e410a600c280f61a031000c480350403098000b01802007210980c0e040c6840480751a4401c062800410031481360241401200607a454001408a14089001880110b01c40c008a40c4001001c600c10000106010790950b422421000c03210800000906e000400074258050380c10242201d03501c25042e80d2400e02140c0085c00c0701d0001045c0f1a80c0c0d42e075204040d18006c0d001e54401d003880b03920303a0012640c9000341074000d08800032411041d60254014162035800c04d00341002c85203031104000c00f00716940c420a080d48141a52642e0403c506a454460f040d41e41c1c01031714090000d0030084000818102001d0020303003a4500b00003020701d046000b0781c1203400b81d400303000c071607152659103400d0a07024050b24814140741d5428180f0354280d0a22070060000f14403156501aa03280c81e045004807401c400040413508610381e0380201041c8540708008196048030007178005 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 561472185 1250 561470935 561470947
    0x3180213021b250b090f120d080f01080a0c030f0c0b030103031701050123030c07020301050c0a090f05061b07050411130e04020603220b040f0203160b22030b010803 72
    0x18407a400c10741e0307031500360016036014140440d8144000f1980d03550012201100394a00c0140010402088510b07001d0307c0b0711800c400c4c442c000c2c2c1c0040e030440c403c120b110507079001c580e07175699081e490310341d5070034010804a08420244005490301c0000c240a60081c40c07414605501ea202c081c0b403c4d802078000b54003103654480242440c5003540c1c452030240100707180140340344c0c2c6c100006403d00140780c078850704a10030110000300300b2504d003800d56003410b40090080c855401e20ba1086041030340029003240010384c18040104034801c03107100400403124064095850240c8141ca42412505011a200c802d0b02800c100001c1703070f40c1c40e0700030b041c044c03000c20b03080c80e540d5600b14150705002c0c0250740c03001d503000744850100005a500d00040d680c0c0100e01d0b2600c00c0d006401c1015861040300244001002c2d05100010b01c01072021444440c498148248c0072550ba0208400999030b403490540304070602450104400c0502c4501420808001c100c42a03038880b45985950314160a82003d8201108a038404521 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 561473435 1250 561472185 561472213
    0xf0b01021e0109021c0b2520030f1b030f1801170a0c0e09100506030402150d0f1a3a0501050a0b0a0608040209040218070807030c03180213021b 63
    0x7400c0d410600d401131132110051016403421100d071f01000c980080c85118500045005401565001502c038000c0541b565140c04424a101b90380003285840e44200c01c0e458400603041c4004119043c900c800c22400781071090492181c080c9199810845042021001c0603408107818841e0440c00b840a41d0400710380c1e1115070034010301c007481c1c3d000114420280c20f020f0040c031032030f01300045003920700940b000b599a0341c4900100f006070344020346440e1001c07400900b511420003c2d0f0b200895501501d00d00f400300c4c1600041110341c2d01a200c3c0000e52055481390140c940d690390022018014940040700c4400110700b10388003000d4961440f0070745441c3d44403020401440c14a03ca005100c150450b01c01c4881414200010550040203000a01a00046000c2400d544d10000c03811030910380c120303030300f4524034081c580240307102c00070356600c0003280c24000251040c07806402504181c0c908550350585d8070310640c0800090301e20460050384019400c0200e210b40e9480c0f4001400081c0c405c10040140c00035a450f = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 561474685 1250 561473435 561473453
    0x4050406050712060e0105090a023105060307170405070819060605060f07030e0301090c09020d060f05030a020108150612070806180a092d02040f0b01021e0109021c 72
    0x103140300401d2030301c4e400b03104c1603030500c4015042d9441a90f8026150f44c0da290480001d200d007404040012201c900da400414401c00c1000c0e100401c82c0c02e04402440e614400e000140c001aa18400400c1483d45052035244800000c2c40c0d1050251080300d2805a541611604102c007411244149900020070242404a1030040f2001003005a0b2403905e807004202c0d0380d20084c01000700003020400c485052201c1340d41c003500718000e102e40250000c002a80d0f22a2201c009602810768605c00504001000401c1404036030003200321440170300035004660480d0700454000740010212030b85c44441405c13200c0d181e01c4142c0540103d0403040c1500d481402d020308058402c90004202a200d112211404e0b0303050701d600030455810503904140802d0f0080c0a02c0c040c03c4260005040341a00b040f54180d40c9904080c603c00e1040b858000d550030090b0801405203c000d50b009420070b280541d10140400c0340c0d9007082c041815030b1003508000080c1144c0c907a40024006540b1000040e40c10704442404410721403482 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 561475935 1250 561474685 561474707
    0x112020d0309051017061c140703230606010207060f0f09090501080705011b03090909050f0d1d010c050d050304020112060b0301090c05070b04081605030f0a03060b070b13020d02040504060507 84
    0x3c5540b00385a6000001d1f880d40364200c0002425510505038840141d0410000d40000d1940195040e080c0351410210861411081101031030314807c000201c0c2c1b155001003600070680c1c0441d5510b02c081040c02c41c003030f112926841e42c4481044020f100c0000c0d0311500d885281c0c0a800d0740030241c00c003d442c1c88001000e00b00050043c20a920b0944500c6000075005680326080305e20b0303042c2c0891000312500307060382001c1000b1405203450041042003c05664003911580c0300c42c2450340604404200c0c0d800454041d9603a600040c51039108543c0c00601d10f0094003d9a40144145000d414607004026042d0a0314a55445110408030200050040b400c29001d409000800f5144c00c90a01600791103212040c0b03005000034121500014800640c1e52a143e44840e10740d030010100d03940c0f81c00002034004036034426a00c1e440028988403000c259220084200c0b03030115048100d5440644849075417031081384403410101d0741321100d0720081c0300603125401103920483c0500380c0003c99140401c00901100000 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 561477185 1250 561475935 561475939
    0x1406010f05040b04260d051e0408030a0905030d02030a050301030b090c060d060806010e060d0308060f0d0516080d02060a0b0121090201232a0a0b1e0112020d030905101706 75
    0x43c0e06c0b5171241d0341d40b0405980c4c082000d80c0c40c40c5451144001e01c404035100307a422140b900c0c0030004e07081905d241c110142174100c070b00c168112000a21404c10480e128065011000c1c0040c5041004102003080448025000b0010700300b5a407420102000103605035200c40003413040c0781e484101c01c00400b5401c1c003a550040000601c84c1c56546000d200140060946c40d0000b0240900000810ba0390b80b41d8803840241000040d040001103442c03820480d40d02c00ca07141443d410347c0d6624101144400005c940314080c504150000d10042e2554684c0720042d1407094807080c100401d00940b1540c004c440c110301c4021180c3c284001a01980c0c0d40001003681e44503d280780481040041045140060f00003282c3c1c03031052049291200d040030345070300d1040c01e5803140407909134441d50310003000b4481502682409044c2140c0401c144a08400070881000740c00d1149070840c05c1da2000c40d002606011480c0c18825100345440d0845c0381d01c4000080400701c11100840020b103c0b18800c852003404030a60a03040745013 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 561478435 1250 561477185 561477193
    0x21020109031b060609060b0403050f0a050712081204080301090c02010902030c1302041703031e0103020306010302060a03471c15050c0d0c031406010f05040b0426 71
    0xc180c030060000e081c110142003548a840c0c00c20340c14000a80c0c000400f0b407060610a2000590300c48400115030014002500c9a000da420803281c1e044000503080d01c41d581c4040503001d00340c03904c8140124400c80140545404004001e03648403d8a840748003441284181c009035125414000090100c651042c900d406683c584503c00001d654009401c1c0038013801213900511450040194401a001302d81c00400c0c14a80c100c080801010040081c1d0311a402c81c001f103000e0400603114020110300280310280d015000800140058108007009003088426030901050301810720072800346002c0313401c10b22620131008410b000512184801d40040100c03181b404401901014000280c00007c101070f65255600d08000041c100050f1350070741019000aa2810000762600b004134900c1948020364a6500e540352030308980055019209401b402e00c03290b030300022542d94075401035550304a8010341001f404414000043c00c801074100410260000c540140100081c501c100000710000c2002c2c1c81980e00 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 561479685 1250 561478435 561478451
    0x406051608150109050406090606080f0408090f0f1009030b010512150a0e030408030301180c020309010c1b080c03100209100c06060302270f06060702060c0118210201 73
    0x75104081503001200c501d880b01c599845440143c600c50b6455000030b8219050010000349080b00358000021a403154807104045d5460181140824000302c4009107010009e00c402840303030503c1c0100180d503001c0900654007100c1c0c2c1d14002400f210004042400242d0401818010025010721050041070281e800443c3c298030413142c5d580301c11681e0740c1800c46440410010384200c02640107000c85286110550341d441c2d48a03000c075900c9500c01d020b041400d0040040041d4080b11902c00c040402c00b0b6a03015606000110300111403e1110590070740341150302c140703414101d001c00303e0590001c00320500140442c1c01040c040c90704110510f03070100c60f4944148144107264555401c0680c0040341440e140c0c0e014103441c0b80610080c119500080d4025507079084000d0444228120910080410050f98880381c0c1c4030b1101a285074801c580b0681c0090f81804480014103044001e0700d5142940d40c00801c1e0302c031b6010441080300174450000e480000c2d22013603e450410090310035290040840c40203000d02c038 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 561480935 1250 561479685 561479687
    0x150906090f1a061c0206070c080313080c010914011e020a060f0b0d08031b0a0804050c040c0f14042309090601080a020d030e1905120613111f030504060516 68
    0x203001d030011050b046082c90401d000c646c2d07040304031800d155000d6407900790552101040e9950350003008040c01c002050400108000c54005400450708030140d54a440c07480c14000000c424159054482d814407001a0f19441c4074441d15030b071050106d840c0da000b0b003440070540c14018142c507415080c00d14034900d03100744c26030345031240c00c1c019000c035030402c412a6032030300c40c1010400e4031241c00640745036448010840c001d48543c0604800c2c0518000c1c001c841c28500c0c03910401048900b130b40071001c027249821030f81c4540e141c041d030101d80c614444442d49a041550380c0242a100111703884041d0142801d010f09294580742402d0010b801c41408001001c0e95814407003420746d41c0c40c0c801d90192084d11a1036130042094403030703002074001709006010034100103080c44200807001901c1c00342b00d00c42d40101d07040c6014180002742c4d42d4402d0300c24032400d104001d540d4958028498044d44c1040d04003020b04011003c0c0c900309000113000200b1640c00040c00c1ca045d061103022544064003220008100b42040c5984d1 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 561482185 1250 561480935 561480949
    0xc0c0d030203190e0a0e0717070815060a0801091d030f070215070525170c030105071b261c0b0405010b1804060f060201020c07050f0607150906090f1a06 67
    0x14543c0c806d8802c9154503a01d0b030648030103205c5e81c003044c3d1880500040080d0940e002d81034038043d141c1c3c0e00c0b4400200b050f500030400c0c14040d82808500041440f001000204040e811036a4004d680c0000d01c0001310707041c0c20060856121000c1c030210098001024411401c0034062008241210341e4090b04000300759a071642c440036602d2201d40aa500500980400e000a000f00e40081001c615056004144940ea8039190550444510b119528240000384014002c040c5510080143c94905400303101a550301e641d10803694442541c0144030944c5040288031803001452020801003000c030b007401405444c00161111210300074041c50800004001c2c408003081601e050300d09441d03a004e110360006000ca0014611907002c840444540400011242d4043d0300a2031f501c0110005d4801d4141c6540504c1000340710340c9032580e00b04004000c901d0108001e116640ca000e0104a4049449092034440d801981c0031801c0984031031405138400c04c20003090403522900c02007800000381203840d2000006040e = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 561483435 1250 561482185 561482189
    0xb0111070641090406090c08040b0a0203150603040f05070f170703031704051f020742060e0103080c060f070503060d020315040302010b1e0907050c0c0d030203190e0a 73
    0x450b00802e12400c1e59580d600000f01806030f00b8810018440b4000d002007915100b0b44040e990395841501051003000d0500840e84510620060403130320b8240c50f42840442e07440108240c4401c500094050000350301484079500408610604868890138801a1b40e0300c5842d5640c2e55540c3da000040402c0003d4014422144000d0104c0ca40b03c455659800c0060502c400c41c88e0746452105205206800ca02541d0701034404a80158102808601e40410600e000c4a088000382a210141a003500704818000401c140050502801241442e41c0b0000340038465002c1e00101c6503c0c2c4042032080301c07807800304261a40035504000c103003031a0170040c0300688a1302c00904501c0c01100008100710075501d08200313030000051609628807441ca0a814024020700341c400c1103d20074040c607040c40d40d1150b0340f03510000b1035000050800c1d1580d203e8400a4850f82e2011444040501410959203203e550742c46020180ea4081d4016591310030307401004814400c2e4480c80c140600c01202d6203a40c00d61501200c80d01 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 561484685 1250 561483435 561483557
    0x100e07080403020c130c03060905013005161a190e0a0e1306050906041713121a160903060c050f03040809030724030b01110706 56
    0x519031030342c0c00c003281084d54200d02c00780c0001c0c081d2050200c580c056031010b01040302690b41040f80680302c40300c0500b40e610038410161114031011404035100c807943d00302d0404000c7c003101ca081ca01416a5890b08205032080700e4000302c0d502032020450286120a10b800c1500001c802610700900380300051a02021034403200f080002d00010710b44291200340d1900d019240324600508246014107a8000c1c40407406c008239002070800c4049031200000142d03450107950300580002c0500c40c0c410301d240107a0000b41444680a81c60080020001e403c04060300196004482d0b0005484030000010100c00010305000180b140283ca0401515840200c0405687d48258042162405410211903a0003030100c01c001c2e801c000414401007084040082410880c1541901c400130b81d41d1000015003600e0442c08551040d0840403903070007911076171011442c000141482901090f0f2102c0403480c2100c0350f041000852011803040c2c040403500e1103a120a8801004c42d071320301c0c1c58404801005030030000d840038 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 561485935 1250 561484685 561484697
    0x71a01090f020a0f12060b18030f0307020307030807020a051e18010b0702241306090603060e0c0d090b1806092d0c18010302010810030c0b0708071e0b100e07 69
    0x10001c0031158021b030004003203c90009840e0020052080705807508284482c2c804d100b141404003c0e03000220a03150701d26001409860007500e0754442c80ba050340450012030380701700807880200f01c6a031483c2c030b980120002d0750101c103071024201e0184546078210f01c2d0081420b00900703004000c010810400c45089c903a040d1003a10030349200f403001c1c0c00c0d4403161610b54021140089403000c2c50346002d14070308045400360765812040507038890301542115564050828a6515032000401c0440460010911040c0606000544107101e8a030b407412958240e40c0110f80011103111840700038810808184c000491201030117030800e480290340d10506a041141e5002001c000010300511414800e00e650100c029142d107902c60380010840940b5102408201d011480c2c440c0031031030800c0c819600744240c96102030001c01082c02e00e2603020503074001072000c4680c040100074480018201059044d183c3d0141c102061501c055880c1880c4aa00002c140c0c1c0c43c10400c16032308200300a20a180c10750400c240e82414 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 561487185 1250 561485935 561485957
    0x609090e06040c090c050d060b070c1442090a05060f030a0504030c171c0227060904140405071203080403080c0d0507020d02060703090506010911071a01090f020a0f 72
    0x10307200340c002d90006201f0f10f40340c424006240404000100811441703500403082d030b1170f01c6030030405401d84c01c980d80e0794001d0300c03010401c000004502e0300800078083c0c03940915004100e82c2e446000c0400da07000014030400d0041150242d504101201c0b034080c1004030b0f2220f040c04145158600c1d0b5020041402192a1b00c0c0c502040c10305000301540741000b0b4008a08544160009412640c03a034410002c0801090340041c00e0442d01140e48280c4150f101681031080d5556403114034001001118002941d1002d810020f005032070365284646e0010340c50303040750310b4010f14160506504042e2a540910807800d5410309220001c0c0d480076406621641c141014056515140b215842074010303401b038801f4042c5000c0030b1050310340c3c0014110600002a0f4229919540d4900c0d0031402d40c0c02c0401c008195038480310051100080d5138102210f0302c2d07500d108180c00d10600752030703411503803001111140619401c000144190346050040c18101c41c464070080d40b4190781c00e1001080007861040b848100000b020070 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 561488435 1250 561487185 561487187
    0x81f060602031e0d1d010e0712080d0903021c09050307050108010f03080f040312020f06010f1d09010902030706080405010c0c150b0111100b01080105040e120c0c09010609090e06040c090c 82
    0x3090111030000b100004058102c880c03011b0007000407840e0342800e40f1409800166401c0b089004107001030340451405d080c000b90703000c600040d10102400b10250302581c24901101d07601d01107505e00788100e59452641d5a07282005040c18492541c01441c100103071400103020501804c008881165480300c00f496540d8403000480d4614091a080141464496800c000cd402c2d8009400e12000001e40280c1c0c0c0941d036038015240481c1035510511880d86840940350782042c00700c240a035440100c0d40300110310001c80f64002400c0030516002180801c1e480c40600042c00003d214031900b240b918100800b1600c0c1940f00c01d07081322091108042000e0b183c03074102c0c000345d2107200800c0a0154280440e810080740c0484c0d0390243c08100c000340d0010740c018000192a1a046c00744103a40d010801c01350104000451011001c0d6000d506201c00512544000c15031a442e026410340c02070003251745038600c1030f040030f0541701070300c40006c1e000f21503500c030a0610000c200c0c030500c0441100d6454000280e1100b461070 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 561489685 1250 561488435 561488441
    0x306060a0e030316060c0e03100b1c03050c0d0804031e120e0102030a0c1d04180803090c0f0f01090b0307090504050f040308070512070e010306081f060602031e0d 71
    0x4000d5405000c04110034013114449880c44200342e1159009001d0092a5442200d017001c00390082603140d482111489540c8400c5c0d80488081d050142c209007076103010800d0400d048002c11030444c00214002000072440034240314003040c26206161914050800f03880c02001d81203071418100032031051104580d243d034040d00c1d03030301d01e00c064610060041485078030b0000d0003500121403610000f81007070081d03003800c0c0c8180011020a003203050f1004090409200340001059a2014143c100f00055071030310201d8500b40245200341e01c1d000040003248200000d001c2c041c1000c0c8402070007400b03015a20030281ea0806d0f401416240340c2040c0e030f602d030356801c041200c44002c194040780c4c0240c98032051020192900705064410b1b4003074ac40700d5070182c1f905402114107100d2004451440a207000200e128540300384031500b006001454042405a140c02c040d50038045200c0d1441000008100c40d00d0908446010f00f100422850001d5820b2000c01414420140309001c22118424030008902080d1040ba40c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 561490935 1250 561489685 561489707
    0x702071d100509090703060b22051503060f040303110a210f09030203090a1205071a120108011d010c09050f130c0f031113090c020715020d170c0306060a 67
    0x82080f0400e0404141c3c0c1c9445100074041a50801d0a1480c014024208070204582d841e8605d80021034490107080801c0091102030f04210b030b180d10303911010034155001c0021901030003050421000600746441c014040320f41010804100c0c140c28001d02c00840c0d0400311100d60094840680c0061016030300c0941c0081c0003240b200300145d89000700240c1071540c00809849109020b0301d004242c0c0c2e0700c0350f010340841040c0940050040c2d124803c00c3c030540011082c0b400d002c1c0003d08005082101000e032044c5d00b85000d07080744250b40e40d2040e0302d0a4000f20121030340c20715840302c0d0080000c01c0c081c48000f04410781c14084c40b40038103892640d03008680c0340d14210428440c00d0741d10070000c0c003220450040c0300e605041c2d0b8031000207041402d0010085403600490384011080351030312501031b1a003c84180178001c918404000e42c061240d00180b020508405030340c260f0415405010024041c12006d0134605910501600ba50b5506081010603030000d402c683d0012000c0b204070f80c41d0710510008440b07901c000 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 561492185 1250 561490935 561490939
    0xf0108100b040b0a080903030903070212070302040f0f0b040c081308072108150303070303090f021e01120608120c070f0602010510081f023703050702071d1005 70
    0x2c0c0010340f03c86150160400c2d600503a03606032103840700d044840c1e480c0420366030000c0a820411441c0014a000d02401001d08408015034078820340d290000750450b501086000e1070251100c1d105841d01101c3d1241c0154000c0841c2c0c00c01c0b03190038040c1c0003411940001c04910004000184840c244a0813034156a1655404041c0800d454001090030b151444141100808643c0702030228040110741142c5140580000c0c000314100509a00c08a02a083d050410f44070f1540b4500314201588a3700c114907c0d13558210b01043c3c509000000042030403444181c050407441c07900c0428030008501007218813410344610f8007142c40d000090480d40c1003108a0340a80e000001001e00026034940640006200b000c010030403204207580c40030000d403200302c40002d100002c009505a401c0e24000340d40501803800d080d00c1c0501024406c12004200c241e103500d04065801102000d62103010b51500402c0c3d0301682c0c5202408039a442d24003c03109441c1a502800c81c2038443e64001030301a100714500000034100 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 561493435 1250 561492185 561492187
    0x4060c05042408161706010c02030a0302060f010f08120d140403020106150804030e2202070620090102030421020406060e120102040807061b121206050901050f0108100b 74
    0x9070303a030101401c9202c651160104120303a00241240d440d00320f4000400c0002d13168075294410b010034003000601300500e980c3c14018240014000368400f003144421051003500103201a052951407901880f034141d1142c83c401030928030901500c00c003c2004554034040122a81d1918001c0d0f0344031001d0495840040c0903040132100701f1040c10381c1500074100b19140f00714044407103600b00c181210009400c40f80500410303071040b41000b06043c18a9100141200a06040340d000310400000003039900c40722080c0c5407541c07102242c9070100c40c6d4238030b00203640300d41020040c50540d0f040000f075104e00072072041c040c0485410b031170500d00d244a260210120f5600800c1048540d4484e000070308180e203480702c000d00403200c5035842c65240ca014400c031016500b15000a0002a142070004c84019120303884210030104c619440d1030005020101c0003594010702d40f108450040c0581008040b2000c584c8501c4c410b07005140108050380f50461001c0c007003042072903da100f90381c0359040d1499001542c1d0008542d400 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 561494685 1250 561493435 561493469
    0x1b040212130308060303070305040608040c09020d0b03070b07170711060703050d15050108060d06020f04120212030a080705181008090d0309050607050c160602100f1404060c0504 78
    0x28103040c5007184502c81c2d15490346603211813040c141e8a0048840007800300303c0070041807103580c0c050500c041c1d06c6032103806a5a101502d403107072807060340c00080742181c4403500c43c80120709901c0d00b480010094103841c4000d0342042ca094592908801105042c3c240a600c00140c1005010070b00499070510400600340319520310103464003c14941c000b84900d4030490fc1c0c08652000150309001d40d1701142c40c140e5800708543c4030f110400286c4200d814086601c10307820041001080c0c0940c01800060401022901c2c180300b05006200403959a9070000503907400030041f400c01d00360000c401c0ea4015102d40382064650018560340d4804648004101c4c1e88040400d44038100c040c0d00c800390034801c1c51090180d90500d0010541035060340d401410047c43c40c1c02000c002507449201d030f0042c1800180c1801103031004480850140c55020b901e401000050300f02400e1585071518034080c4003061908002c2c10005d0340f84080019105840140004001c16140c0482099840c0704500781c2d4003420304505c03a002160 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 561495935 1250 561494685 561494701
    0xf0f070309050f04050906070503060103090b0f0103030806030d05030c090a050438090a0c031407050702101407120e04060b040e0714030c070c03290901020a021b040212 74
    0x200c80c1c410b56104038211031042040d03003454050786000e04a40f0000f0700d40754076016810703500d41c0c0000740514100742da01c1c0c420b0408602000f130301900492007204d4101c41541141401030100c000141020301039403146000c220b400ea88041202d40c0030212102c0c06444405c110000382c03d0030640d9100582c0a0700340700f80c0c8102d0202c24401c00000c000c0d000003c031016221000444410628450081d03030009003080068280159070300303c2c581c1d015a074a0009401a56202500d145110541e0391100184011807580f003181404640b900b41ca01490400c00c841c00f5070401c0030302007446040c0d0010b0118079544854081c03a409503c015040304402881413280503101d030841200d5401510440038802c0755140810711300e6000d0218210303105012030101d45982d84425007400d03582d01a0000703e4a10b81020000000f280c901c82c1400d12803046a44401d90002500c031440749a8103000c0d00f2856079910400c00f03182d070320b40c00003108881262407240c905440301e20071f000140240112241c115810be056410440d44d0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 561497185 1250 561495935 561495947
    0xe0406020d0e071805061f110606010c0b010302120f120d1b0906080c0c150601021006211509031809020f0d09080c011401080c090603060a020f0f0703 66
    0x70300741000040040c08200d400749a500ca0151055811041c030b1580204040c286940280ba03102e1406020300e403070340c05c02180100201e00058001300c0000d00c64106481d00d0304003880003640142007441d21900024050300c4502d41030a061100901c1140b51271420b55103d0000c2c0036698000c00600203440d00006039807501c007050b51042d0301c004142c6140c07285d00c012558a420740c0c01c14211240d0b451040541c10407038241c0b03500d08050048003204d40284a0701030002010410881c816114020351040c83c02c020001901e001041c801411036142002014820b4020701d00f150400154941c404212400c401d041051600150050407420281003840c03040c24541c110600901c081480e00020f03803a00c1d9036108203400c03030041020841e2580c20402812030307420b605130080754146002e0084c481c9081d201503442800c5804903078124030501e4000e001000045c20078880d8440c05002030340c00a94611300340340040c1c0c903208010415100d80c3e078046945140c00850100f600c03d80d58000c044681d40c2c01540c2006841 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 561498435 1250 561497185 561497197
    0x30f0403170f060321030a0207050307080706020a0801090902030d2a0f1217011505090607030309020f03120d15030503120405010f09030e0f03032b0b09131103070e040602 75
    0x9104201062070740300b00c8031102d05481540305c081d035825500c580d08500d0180d4019582606e00388001e222090228281e44006c11030144102e40c016070306c40154034064400300c0140c2c8410001791800e400200075840108005000140b2450410401802000040402c04141c001e050030103032020140070401121354084022180982e072904c4851140c10710403280d201c4e5140c904648580e05a004220f81c08a5043c007040103216814280c0c00c0840d00e40200301030790820349080d0006500c0e0781e03442082d4200102412280300080c0c002d4000207a8240340029988540300c012844107903190040a142a03081405501451f4080d05603941c0b4801c10b0f07905401b01e042513409603a10351810a003100c003c2c050f4450b030200103601d07499000011003902c04208840c060f40c0c40d5103405000070130262411070500c480c0c026840e60120501240d6030000b05018080340c0d01c0c2e44d0302500030204841400300e003109a84444e505503602c15203c801d0296650003003030405c0d113150301040c1e80c091a0014802008290340140035 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 561499685 1250 561498435 561498439
    0x200411042606042102030d0c0c0221030a0e040608070308030f010e062805030105100e01213c12020a08030109020f090307030303090323030f0403170f06 67
    0x2001d805094054a91205480013015121580e0854218041c0840c100c10301034064010789003403030740c084841020f841c41c1c0d00c40703c400100c240f44e6910861800c0781402001c00308100038001d0b001c000003041d0380d8a1041c51541010300c04503040703030406550380e504050043d0a40030250303040e4a0343c07482c040241d9001611189507800440740080b500019004245101e0b050091242010140c441103284a00c0d1003078407041c10440a600c004242a02c0074000d07107004403c49145a80c0840c03418041d05040407044c0c00065588494800c4090004011040360403525001480d0406144400940e05070318514100e50307501d4405655841d21040440662080c64507000b020400481c1d040428100e071911100f8000401806050006100414040d4082c100e0241144441860100c18100017031504400e9403041340080d0305c2e0340360101003641c03140d00440c101403c0c200c0414402d0604207000d00b1400010141180d954042d0001010715104032a10340b203100085001824505204100a5440b1000c4603198 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 561500935 1250 561499685 561499739
    0xc0c0a03060c080c0a080c0f190801151106061012090804030c06030509100203070e030a0605010305120414041e0504050601050a06050a080105100905030708250320041104 75
    0x140c2030000e0101203c5e02c0d02c0d120b81d110340b02039855036110b200b99041210345982e010030500c8802680780340d0300d00c1d40d41f615105896881c40c0750b240803258580001c0f00402c20003000381c03ca521f8940c039a0700040880c0c00c102d007142c0207501401c5200b42190700c2c0601c40d44a880d0103090134991030030320003050300610030342e40240e00301c54410707854220a80c01e8402c151a2402d540d4400180004515001d9000e16001841490580ca205414000091512208010507a0301ca80d0b1140100b042140411400c1443c481c000e00d490b007800c1c0313080040c104106001c2c0b0a240240c1d103a04600140d0342ea104000c6100301102070301042941000d0502c10f640714024012030b401405d1000002c51414014001d0700d600c00723241c2d50380e4000d0703a00f40f03824004243e0344070030080148030040c540491141d41c2400143c0c040c1582c60000e14410000c80d070008104203c00d040782000e00f50503c0e062011801800e949038080d0381e0000c26180904141021400a241c4881508125080403d0203d030380704002e0b68108815542940b12 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 561502185 1250 561500935 561500941
    0x302040c050c06151207030b19050603030a05070302160617010b0405060724020307020d09241b14030c06060603010e04140c1e100c03050f0c0c0a03060c08 68
    0x1d0710284121081031106501900010720712aa4442c41d00700e54103809403040e41d0042c1c50450091921100f600300703c800b00226010022041c1e181b02259150508a150034802030410301c010a403a4400da0761300e030040100c000f034442c06040c02001040d541413800301206000ca0f075249001003090b1110052240b02c030074104000201b41c0581404c1d10283d40006140c94904031a550341c28051403449000f100c05642c080030b4165160f81644041c611505441d00500625864100020041206504210303610004520101c038038140031407441c200c5020904192510080d04461425407452a24004008210031250440d01402c01f0001d00040040102110207649030b100402881c1d00090041c40354440350030000401045802003205000b01c84802500e0103640582e01140100390751900c2d004c1100041c41c0e80e244c041c02c0455951203c0e800d9803405587d039180c1070b039000380284600c00c2c01103000c80003c54204503098084c44803254500c8000c01c0d40903030503586d2400d134000d0030341c15110b074020514203400 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 561503435 1250 561502185 561502187
    0x150a021908030f091615030b0603010303030902031207030219060b0306101701050618100b030405030711010c02091b09090a050a0b011e030c05090d05011b02010b150c0307080d060302040c 82
    0x1503010210701c10820903801400d042a01d071b01c59940c04034080c2055190305024045480c1c010055010758040c0d9800f0810040385e0060514016803c215290001e40401c8900302090f40030500250b100c03100700c00741038000074908000c03000e0300c614240141d1500440040c0a504132101801c8401c451200f40c81d603040f62400300081c2e007210011500507030020203030011074619100068020f9400200081e81d02e035443c1e1103030b5405080d0340013201e040f151070344001508030a01610f00c0e01a00c4060003440c0940c0200455400b0420100000d8080b1100b000030340a0001c4c490060030540d0704e11680a42820064648101184041c103010f4482c842c0040c40c04140905551055154202d28001200303556241200304c1021801401001107903000c0010600080307030300c0c4d038842c14030600d00c90051001081440441041c01c1d14040c035a8851402d40e850400100595101c200c0740490849440003510384801c00c04100c1405c40c41a1000208114400103181a8230905a4040c0007079030700076a03003042507074900c0038 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 561504685 1250 561503435 561503443
    0xc0b1e21061203041a04150c02040b0402041202040e0111070807060501050a051e0a090608160501030b03070e0c09040c0206011a04031a071806030f110702150a021908030f09 76
    0x24500d100c40d0004c010a1188110841210381d0719440c25825621b05552403001c0603c2540600b404030011700803443e4802946003d0044038154017045900b140382501e0309448082c45440042c000740516202c03207034250441c100b98014880c168000000647d126818136020083d981300200403901d0301d00d0305001240b14207140084609648002c0c020f10140e00c01c1c5181500c080c42404062940312403034180210f080e2810340911001000301d04001c04103c103418500000a42040e040705041500d00b10f01c5494a81c2d0010f0000200d5801c00341d94103040e00da02483e410b0503c210818680c2040c1000800c5410b26800180141240c250058080d10001144048081445188070241c02c0503681c2a151303a105c00301c98a900e4100116042800c111104101158180c55090340608040307a6a08034032041c170b240a0288044511009841e5850034095500042400d030051500800303008000c00c0c0c40110742c0c003c002d21035901d0700c00500b0b00c0e8400c00501d4602c1d02903008840e543c2c80100081c01180100720001 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 561505935 1250 561504685 561504709
    0x60203190f0917180a06090e1515090a051f1709150c070c03030906020705030313030b1f18110a0c030f0203070615091401030c0b1e2106 60
    0x320011800c2082450b9101241c1c00c040c83c100310a440061544c0c584d0f039038901d1004000c0c000d98450341e109500e00741c0144c46801f0014001008082c1414507a082d41ea1361503550100b8058044c0e240d61074040d0040800d10424030364015a17000500c01724682070103649068944001415680ca4040c000900700316003126002c1a1090440c40c1d00c90f03010b2021b0311034410304956210101480341c1781030505540300c1502d00e030015402030340440c002c40428404160306100a01c090a400c0e4011881d00d200c59010441c0c2c04001d00c00038080801c044040341482158400c20100c1080b4a0b40c08103c3e203460305030f4101d001c0000d10405540b189400921034116030400c0950b54600041d403200c80c40c0802644007502d1304001c0c03441c030108502003000343c980001c2141c411001410b55401d2000c07081401c0c09084001c0b80da044030764401001e40f41c40100001081c5200c1d070301c1500d4028691644070462000d16084072040b5003140d141820010807681844400000b00500011501c407400f1429100d6005018044804d4 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 561507185 1250 561505935 561505943
    0xf080f0d050301030b071403041101020607050c061f08030706151d0f0421020c0a080109150f0f0501031208060f0d11030f19050706031503020f0d060203190f09 70
    0xb800108085419184419404101400e210205550b40e82800d451503004950444981c907000c2290b120f1540d04000550b481203081c2003d900d4500384a074038076039801004046941d44099509803071105001c0c034101000401444044139159510380c581040503180109030700c040c200141900051060390800781e0740300303914003d08422660301d83d5020185045002172099a810000040c0d1036409a60783c1908030543c01c0070b9000c1c140500b4850100100688558003010700d582c186207541e0045009100c1040808242150000b0308580490300c0c60040c0044041203698503182c0000003062140034403100b10b0100e030542d1101200da440504000b02c010080d0103a5800030300c42600134002801350004800e07255002000c13102a100c076607103150b01e0000e0300444010f601c1c00009034201017200811500c13000d403070141424040400b5140101c10512814031000c1d211360006014841d5036250300440080d05608000103556900d0805484070101018415503803042e0f2400420484030a054440d00ba8440c0d40 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 561508435 1250 561507185 561507187
    0x130515130201030207030c1403090306010e040b13050723011808101a12010e060703020c0c010806040e1506010e0a120807020a091404020414090601030311160f080f0d05 74
    0x55078004400a4002d420114148076008010002040d1002050b4600d07c120350001c55590100c00306143c01c0140603413241d180d240c050070500001039000008035500480096070383e04070144a0500c0b500d81031841d4045a11003800d0103140e0910824501d403540300b50800c0e200c00105d0388071950a010918518883d0080e1504945440b2210211603085030351642002d41964951849103800910044a14a2800388680d5100042011150140952540100d940c00c0c110700b09a400480651105040032849040144074000190703580e5540e40f201c00e0802440c82261003e0008501605801c0d2041c0d486074040fa025003948802d034a019100441900d9060380c280103501c005564900d070603040104226404054071030081001602da104117510800400d11961841c00d003070052204480b8000201700d100a000300401041d0301c2c2c0080c1c03242c1181d505142201e004038031900414105080103109008221440000184900727142c0803503010741d660300e001d50b588040c0b84c60030603542e6040c801201011441c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 561509685 1250 561508435 561508471
    0xb090f041410020c010203010302240304030806150d06032618030a1406100509060f130b0d150c030606021b04110f1801080106121d0303130515 63
    0x211641810208808034040750b8124140c4100041aa0080794109100d43e5000c00100254585070f40042c0141c090f84200c100f908040184000340c2d44401030015050001e07840200b80c6584589030311004099408400c180c96450061041000c0c02c860300c03050360800d615018814521080301034000e0f100d10406025480c2942070151142140071050031241c2c180038041c044004207100541080c0740710180b10140c01a490a20910b070000691500880e0060a0284c100815501c4500030800c050908403507103880146240341c904081c100529000c0d4201600d03025210400c2501c06411112081c0110217100309032000d24202d084030307211700ca0003005070302c66061f101e4007055180d45502141c0c4060b01c0410703080c100c0119103119500c18104a8190b1000190343c0c06101e1140011507089602480d240c4150751418200402c94074a50500c0b55469580340403080100a10840d00100c1c4100c0324140c03a160720f002184c11003480b01c903210540b507a0280041e0000c0c4501e40c2d10120707100e06a01c03d80c81031211 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 561510791 1106 561509685 561509693
    0x50a0602030421020a021813120c02010809010b15030705070c0e07020f0604020a090e030702040c0c0201090f06050d0905030d1119030209060405240a0c060b090f04 72
    0x90411100e0170010390b55941c074064520480f10460302d16840d90041c920340d441844100601814030203810b50717085a000032030108900e000340c0302ca080f80daa0740011035080c0c62090200580c40074110b82524840c00c00000915080f10752443c05031704100d01aa40c0c20403400e101c0e080300070020552810418a958100325200340780d00008080d180c81c3c01d01d907000c205202d03180c1c0212031a29490b410030861030310707040080d101100d40050052001543c035100107000e480020000b80d000412034032011400e01087c400d03d400321015580da061803c865007034841e0041c62164400c5449010812803841110b819002d503000d240404481140d5034006180030303003090854032142c10113260040c0050012580c41e0004d41e000c0310015182d1800041840300307004054540c81e4280001160702050300d45038958001101c00c2403070b10403181000f83c11382d904100005c01e501111100c880800030000070b8009 = true := by decide +kernel

theorem cover : BRFrame.Cov 561330935 561510791 := by
  have h0 := BRFrame.cov_init 561330935
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561330935 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 561330935 ≤ n) (h2 : n < 561510791) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
