-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0711
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T21:16:51.968846+00:00
-- url     : https://prove2.me/submissions/4cf4836c-c472-4302-a9cf-0abd5d638d69

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 127697841 ≤ n < 127877697 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 127699091 1250 127697841 127697849
    0x20c010e01020708040521150702010b0a06050c070e010b0d020a0203070501020c011d060f0c0a09090f0504061103040c03020906040207061805100b0105090409050111071b0f051309051e0a0606 84
    0x1d042d050010700c0d84142e07100d0300c40310300d045540656030008030f058ac402d6002174104030000713200008042e2348920180942e44040348060f600e01900e08007042580001c66418100d9102d00c80c2103142808502c20003000790007d001c2182140400c000c0040418401d002620600c0d041c1c200004e841a211742080020f0010aa00b120a0790015020400f04c81500d400a980c8150f4413008150748504074034003241c04c40b540c1d03000446464503000588030440c1c00755115500c550700c03c039401c0040b05074042003842540400c55000b0710568512905100504044003015017010001c0c0016050446075560b500944881b000b400c103000c0703c0c2040c44000d004041021103021180c80904000c01501c00c000241103200f180042800341d5218103402e010444258481086441c4004400d622210249022512088903c000b21101401a0350200b140b1414003da0301c12110020440c4103508150260030300904045607040c0c8040c09034211000c40080c1c81c0c0020603412400748003805141c0031070310340303001140d0150304 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 127700341 1250 127699091 127699129
    0x4050405030a030e0316060b120c0a03030e0409080409141f06050f0403050f0703060609050f070305060a0302040507020a150506010e0112200405030c010c020a09020c010e010207080405 81
    0x910010900100441e401c5081a28011130818284000a4598070403444005d105443c032603c2c14050124942c4610f0101c4002c444d807400c0664005500350f602c85a01c1002540021001c60400000c0d00400718504c2c012070240c40800c0c3c030481922284042d030425440900e01d00c1c3c840710008455201035492540c0400e0598040c08007800302d400400c8c4100c401d000b45420b000d0006029480e4415040695004540c400204d6250651024409854000500c41100c1a03414408049041401406118445e000080d040481a950351400b1400f8210242c040d039000104401c020001d40c8960140d184038407038a800405001e8170514061000c00e01a42e42400300034a0641400060380c0c1c85001c0120035142442c041d148010f09811050041003001c0d900b4420319000d004070307041d43d5080b401030000c8030400c0301580c0c180011000151160494141c0c004d5000b0403080c01440300c6803a581c054040048120000901d51400400203400c90f407101d00d050300c04100c046010881842c2c24401a004103034100 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 127701591 1250 127700341 127700351
    0x100b090709061b120e190819110a08010605100201050106080a1e14151509191d1b030f010506130503030d06050a0501140f0304021f03050a050a0c09030b0403050708070b0108060604 79
    0x61f03040e0b4072070640c82400c21010325004090414014107280d90318041000601e06043d640da5142400c3c004e080611565015104100300900300a0042c410b0034104d0303055440701640ca9980440040003000003141480a0303210590701200c4a1069109000741c038503448090f0a2075040c034140c01005500304861813032241924891854401030030700141c1e858401c01b59040301d1450001d142c3e1040340c59070360b000004020300028082d5140b21b098460070b0f0084184461014484150442505003407108445035100200800d0042060341412001401c4803400811a41c0d02240c44400080c1141e01c00d600c082c43c9951640020f00c030b00d1170103440c42d03001804242003203401030304a42d081d41624020910503442007180440064255112005181c0c80784481c800c0c1410024411600a0000c14060303a411503102c1c40c3c200005c00d008041d10881242158a85401b4001403850380c600c81040c85c010011410080e040c8514400655010050f243d0750b4412010001d59605100c4da40d480c2440040c04907118900340 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 127702841 1250 127701591 127701599
    0xb01021902010221071e02010e0d030206150643120806060f07030302030a05010e01081203040507080109051c020a02010509040207140f100b090709061b120e19 70
    0x1555200b1aa1482c3d50008001c0180c40213204c2e80150312003e42000c0c888046035100c84005089482418802d881d548843c84c501d00c24844140042d02c4003e0142e804003022410f10146503400385000c000040880345002250007004d180302e4015070b045050340781c2d0a045000702c0c0300324407540751080003d2000c01e0100780840e00c0b00c0c001040640410400d100c0b01341c1c08522140ca03800c0031100000e0550210540e511070601d0020000d501c220342210392685002c001188415030056514100c03a03405009000c3d00091141c0c540030b660010304216420311480703400043c1007502703016031421140108094100714041410040121035040d0494003150020068000181e03005400d5805044c404c1e200103841d070f0041d2404401000d046d8280742440e1042c40012010010009074281c10000c10b241c0501902d07180e6001e00074011015680c00022401040e0280910f074271603804510290039413481c00c0341020158a91007801c00d880c12615000a071020a86009400d04540740901c3d0701030150140713a07840c50 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 127704091 1250 127702841 127702843
    0xd0507082107170d020d06060c060513050706030c020304090c090807140a0909060902210c0604140904050715051b2a0307050a0b120f070804020f130c030b010219020102 74
    0x900d442102d0401e00100c1c41c4078134050750358180c90328407201000c204102a01c030403005d40054111481150351900344800241240c21001820051320361203c0185050740c1840421b601800c0d2000f903550451100f4400010462114083c41c00c02080744e0322a818594101250182002882c1d00002810380f2035108100180d11141400300480b0400070001800140c1450804050501e081c40a50b1011082c200c1140b031a80f10000050354201a00031038038802c450209200d424080c6201c0c5081d03000390005406070600304508055401481082640c0081341c0394104200314001502d0a80005200812407040a5803101c064214481c0c00c14024054040200b030020b00b0f5080003c581074103500522466492078904225480c090500200012074051305d038000074840742c00c10304580000b1020b0001059030440b410b258a80508801d50310124950390f1a001d1080b40201103500031381112511162440905151290351418416543e0100312205054002480c11a00020104090480301e0603100180c1e0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 127705341 1250 127704091 127704113
    0x17010e03130e07030e0607020706120612080304170d090b010911070221030f0c0d080105180613021803071703120a061a040f06081b090d0507082107 65
    0x80c0d00c0502c2d159032031034412400343c00c17450080c5c2058031071721040c007115a8000c580784080e207032540d44001400070380040c0501a180b142c0b04030241e0078440c02042e40440c0303130f001c02140e1090286204800000760490390b00c405511407195000384654881d4464200000c20b030703205004021069040c1701e2007442d0010b81da82e511809000030b1080c02c003c1084c0382c4010f15080790140301b81c5c8120035a51140090150504035034001e0b458a0b105001d0b00310001d403214001d20303207039060b5030010b00030340b492140c000400d0600301e5014040c2c992240c0c040300c0d0a000f0700070030300041c284110451450340207002e06109051600396035801c1034442d2413032241038226505c000000d58001238907917040c8110680754500600001c00880d0130640703100c9040002104450105001041143c001d42c007603882c13850380d8075030458803043d0658900e085800d20300d0b029107111000d100545400745004010b20321007180c41d52020714004040d80030018541040d41c450300c5111001e4094091180606040740c5002042e80e180000c2e03030 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 127706591 1250 127705341 127705349
    0x3070506070918110406051309063503040303050a090305010f0605030d0207150f110a05061605040609053c1302030408120910020a030506090703090506060f0f030717010e0313 77
    0x700d808103d10240d232a480324100005c000c0d500003009050303160695408550a452448200342c551250001c8a1018044d028121042410081d50804d819640c04481c194000322081040100c1528040013154084c400d0022002c511000090340a02e040281410018020078020131354100d0f180c200505c1c1c101742d03001d1039000210324018100480b04441682c80c0003680300c2400d81c030b1040000007410040001035090007054000c40760a40005030346004c4a041c400d60250600081d41041c0c2000f141c1480c048204142d182c040030f4a90030701461003c0b06c9520b61042c079001070a07003082036003106403d005d030210030541c0448a0945c55842c003a01d69400d180709003000c002c0c2c100c1000000031054502808180560f040b281025552200b0942000b07010300402c0c0d03030003807040b001e034004219580d01902c9400c110f158000046e010680d20002003000c501201002250080c0e0700f1103070343ea80c07550140b001d2409000e420f84078181e100d64000b4890b0840d1005854400c11394010080081d030240400303841c40c00c417 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 127707841 1250 127706591 127706597
    0x90106061d0901060809070e04050d03060e0c09010302070618030315090902010518060c06070c03081e0411060c0a1401060f05150a0c020a06030e060708100b090303070506070918110406 81
    0x5606d46038507881c64204141d0114029000302c0081c00204400401d81000c8404680d41c2400001d40b140000c03d000c1c4000c2d075aa0f40007035010400c0100c2d65010390050041c1502900e000500380808581c1401b441690450440021790344900d0b80c5a041c9060103100080e2802260400008000d40c0c0040d283e845034040000d0034a00d4184201503941c0c4150442c0c1c040310ba81d9060700d41504000740058044031044808030b0103d1030381c00c0040d080e4411505900303002e0708845814030268544c2d0b101c030645a051070100f16004081000b2001c04034070100b20f20303010544900c442c2504500145c08090844895801580003c02004030800c0a552018a01e80200324a403600c140d40d01d0792140d0603070341d4080011009400041c0401c1c0060800e0301913120301100c1030350105482240e500e0700011681c0202c110741822403075003a281c0034008800b0040c09001803542c042c040b02e25209a54032041e00c0d010003120240c0000d0074010003031144c242040702c146070041c809041400101d20044003a609030103075005660170 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 127709091 1250 127707841 127707857
    0x1202012a1509020a0f03060b0102030f030c0703020f060106020f010501090608031c02070204060e01051f020303160909110418020c030403060507030f0f061716120f0605090106061d090106 82
    0x84545078040b500d0554020850f0791030503600d00c0c0000300c4030340074030050305c3c454900100c0c502154000b2040310100c1d229080c0ca6443d5a031400031241054001090550442c410030500c410075a00c108180f5000c1c0c803850b0001d0444402c0d0307045442c01c0d580c05810400040c4e05003103080003011400420b0759202c2006c951030030038140b2080c00c170710000e006094000c2d5001c1e0608100049451030287c0c15410380340140c6041c04600d1226108030001d000342c005100040c1d0007000002d02e51900d00742112401c1d440c5192214203581e880c0001810f03034070701521b484c0d40d09000160412550311642050038003046003103415400c03c41440b0010792030b4020ba1001914054440c0c00191405200e548070702858180345200b0003111100507480302c028901030180e503144484000840407543c40014400c000010704040c02e40341103080407105082400e101d81c0440340034407800710200003d4194001c4c507103d21040300c000542946050402803500d80c0d00c4014104440d06000883e0090f10340c2c00700390341511001e00700400 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 127710341 1250 127709091 127709123
    0x3092404061d070b0403031202120f090102090603090304060908070e0f0a0f0f090506010f05060f0912060703050f0610050d09050309040e2103070503150103090605011202012a 77
    0x310b40180c6500d0440c0e10b020f0007802042060300039014105803400ba075240314040134100c6501c41280315100106e0300780e2400c040000c1100310700c158425404160480051704100b034039804075001da00f09071503452450b04041800e0010702e078402803140041490034000c100300c07840c0005038546404090000c140500000c000200e0780b4038580c200c50300d001c49145003004241d410a02c0c4500602e510300c011103640c000c5500005040a40309400c00030340e500204400d00c0c02c06c0b42c50001c18141d00c07203004940c00c41e0041146080d4074605004952141030756403030100e09890940d09100840500402d00c610900d8001c542c0800240c0c0041a1505c43c03070902000109908141041440e40c0540f0320103d610130306040e44401c060700301092003c0124076040c10083e00300c04414028403640400c41d506400103000303200180440384240c80728481114181000550b003100c13a00d030502581c9098010740c801d648070401101c11541d12a034019052081005004542c90320310600c414007a80c1c00034064541441182010 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 127711591 1250 127710341 127710371
    0x160201110703020a05060f010f0e04020a1e06030b041a040504050709060906080f0102071208070e0306040b010302010f020601050114090111030a03050718030209060111100c050309240406 82
    0x840c60300300d81405032030300c005203402961508082411501401040082401c00d00700c41390590689241c0c04005c41d10ba41464560341a000c80140242d030300c10340368400042c0150103000d00724060417216694101450400801900382d805138034005001d1071400301e5030208044508490400c101d0102c0c2c000c240c60f03c4500b001460001da60308254180e51410750005840c030100e501050480b0b015005031a1580815a966401c030300580401406c1e140e00700804910644c0b03e000c0c1503a01404c542018688950408086494500225000c03200b07880d106005009568000d115180c0000c0544000c1ca02581808002412000c0003540020080408210910305a0103400340d840d035001d008080b2505c402c1c28000060281200382c8803600032519440d0031207550400c1445d07940950b90050030384282c5846850044410f040801c02c070340315034080d81010507203e1015008000c1790a42d03d5442d651281808014241801d2850607448148210b101d03800303568120b001702e01648640c01181c00a00341c0b00380035880c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 127712841 1250 127711591 127711601
    0x6070201200102090a0608010b030f0c0d020c0307021c050c010f02010207050105040b01030c12080a1223070315030b060f121903020d11030d09020a08030a2312160201 73
    0x400525021070300003484820056020b00b811000858800d0300c16903442e00e056074548800c3c0a1210f034010104009242d1031814078038590091403950035507180090080c80312041742c016008002c41030b00700092100030761400003c100c90304011500701040410303840d6500395640715071050550502c68103044801d10755000303505450086400c480280024941850142e58101c02400221520701c3c22300700114200c22031488a0182960104105140c00364000c1c00392200d500322042e03d00300585484040c58a030f00864440d001d25503040520b6081130400e4107002e81520702d00d550034600803400c0720080010494060381c064011409071a480c1d0151074072004034010101000c00d10b421841b80c2014840c1040c103000c89412403030b000f5800c1e20101e840c40d43c011100d440c51528072810682c02440090300505d025441036400ca403008100c0c07a05540d0340c03071180341190010030300383c000700d0300340074041c210200c01000301c50714039200c10700452a040ca10b468000e001400589200040c6604200002400c0d000b503102c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 127714091 1250 127712841 127712867
    0x315041104090905060103210503070e0f0d060e010c18050418020a0305030415030207020a170106030c06110c0d0b070c0f0c12150c050406051e0307050c06011d0606070201 75
    0x42440f480b00e0500b08140c0d5100d080c07104032061054241605107203d015a401c807011390050369424510303155804102c032030000c01c0202c80d5100084070350f81da20990b198011100d07968413412011030154042424a402c6031010102d4006200408400c01c016605080855003912340464000500345401214281c0e4ae042030341000350005500d440c0030051000c000b020704203d402000111107004207440c000c4060340a80d0344025005405864141304100400381c1d500b08078910000002501656511807215401169000001090640110b00000201840108403014055806440e0301043e03645055122900625960070450040c015800b080342504c400740c203890708191050303a01511078070300545d4200101001c4881d5401d5025400c031100303c500503404901c01c140ca0b41c90409207001b600343d13299400521004c2000d6168407402c05418611000703140174407590781c1c0b41501c1724480c003605480c01070182c001d0180103a40807007031194080c07a10416036106030306654603030b150485440161900007070305103 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 127715341 1250 127714091 127714109
    0x60807030c020a1a04051b0a050d03020a020301061e05010201061511030732060609040b18011506031d030706021c0903110715080c0901200d0201110315041104 70
    0x2135015078007000d001c0307082d0040740034500352401d00c440c2103c181140d004070f00e07105030400203c0900b0440c51410702040e001e01030280c0190364030300c032030b55001030b085804e15000703012004c1e40c451210241c4540d00c031004014060a00081001604003008103000403800c46080c070400030300b154444000803080c01a540401d9100b003003810726a105442011a0405d221111070254280307007030034071440c0000038145029100291290000e03031103544982410b0788009040f054100d800410800c220502480f8540c085507003002d00b07040140c00c24030020b054039004480c50503541c02e40c0f011a50890004000c03100c0542c0e00500c0140d540c00c1c0350842802142c0441d101900e00380c64140e01b1000c2c9a0003524114411950341c081c1c0320040d03180c101c034400b003814140310100056032503000102c03c20440c070f00908248405042c114030041c038090035402d42c02c03440d00b5400e42a42052011402c0039809002d1100303c00706180c5102d00b140741008902c0da0504072160360601c51074032203038554090b80b0020125805814001 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 127716591 1250 127715341 127715363
    0x302060a05030f0703060308031302040e07030b0610020303070207140406090513060f020c0c010302070c03020406121a0c03040201050307090801060b1803030901081609150c0605060a060807030c020a 87
    0xc0006800c58204a611115510320b07100011020b80c030070720400d1300b603c1e800180c0509588070142800900380242c20100e0304507a499240f0030030014204944002144544494170503490b20b001440010320803004a101594000d009200d241c03a0042500001d441941c940d0000b608054000903002d00402e50103200243d1a24080c49401301041c10103001e00c6008010911003c001086034401b24071400320700701280d07001043c4800c5903610940042c00a54003d1502d2590551207400003002c45045601141d03c01c0000d014000c104100301c0219a43e020b5085c0c400200c0c0d02c1c0c0309010368410704c4002c000071704016001000030140382c000c2c900c9002810540008000c01901e40d104d04031540d0000300350440030188202e60103610b24001045450f10700701a91034006945402d0091803042c410722030030005200b50b092000c81d20040030351a21165012075641c40c0f98044c15030500e030302240c1014100c1c80c0540301c0e0440c103005207904041c07c90340115003882c0004285100c40700490404101c02c1d001484044a1 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 127717841 1250 127716591 127716607
    0xd030513140102060618010504110c0d0206061201020301060206010302010c0f0b040804050102100501140f030a120801150f0806010f020a05030c060702060105011d060304080d020310030606050d0213090507030206 93
    0x1444081a2524081e000c0700d413182c44620130006c0e04041d04012008510070080103022078181900210742d5252402c001ca801d0082101c4c0050411410307030742400045c1c0c05841002514174102454211121400008510315410054000d4980300305010107414801840c01c0e0204120f04203040b503050540028021b202405c0514007095182e025200e0580144660064440c50440398803681e030480303207030a4100300d0f20200300c03052210640c0e01c12040d503814098a0740d0000403a031a544240c01d041019680d2007115070500d04180380d00300ca40c0f13000c00100030480d42c41e0320070207402070303840c07030f0013070000d007412510100400001c0303150801c0070303c005102d40400320702246e050710002045402500e82d80c007680c000740c3e21440111920318200c1d8071082403d4150749941000e00384200259001030148460030701c0c00b0502240d900c1030760300a0322020f25800c5811420001d000081c45008042e0800300c5903800400c1c61600060403150ba840984034015596611690421004200500003154080c0c038468a400034 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 127719091 1250 127717841 127717859
    0x50403051c0f0509010915090e0a061d010503100e031314040b030607020a14010b06040611011a0a050402032a0d060b040501050d0518070909020f0a030506060d030513 73
    0x61841c89004552442002c4032035500420a403801404181e50709541c0c1494404107814000c1c40880030402d004c4c0350706010591700c080c45c04941c401c4040f5500030801610344001f1035480c4190781e42005000b04e0190052089680110340f10050702a101d2004c0f51196050440714114400c03842030510b817041400c0e0000d40407075450320724032081d4800c6508104140b411410306807520004c032002e00040e0891280600040c0094400500c40907003030000180a01c0408085402c070b03402a0445400b007079102d00c0700d8103060400d00404440e0082259140b05112b4268081a80c0c0e4480c2e01030740e4070482d00800040c0c2400f082940c0480031104081c03050411030100c1304003c800c2d070b0081e103200e0b03a107a080640c0850b0790602c0100700c81c110f502c10307501c651038008540b40b440b0040c40041c0540031020980444590700c0d0004101d940d02070001c80b500001d04032081d2040165039550203410038040d40b1492000c00c0800c0021848544c01f420030380704042c80c580c1b00d103412aa54420380308030506042c2d40b14008216001c0d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 127720341 1250 127719091 127719133
    0xf051c1410032d02010503090a050109151a010503160e100c0c0806060d0b1e010312030c110c061303080304080310090207020f100912050309040501230d020105040305 73
    0xc040c0c20030010444240020015281480c40240c1e4000042101c3c0b400651090740115801464002621400c11540da0b0741801c3d00c01816060711001c0448d082d82806060500c2000005101d801c0910880c94580e40003030620b000c001c02c2d0794001448800b03c0100c150003410319038445140140301c000d600018100c0588401003101080c4c0f00381032020800b080344100010f886004c0c40300101841c00042c5180d03590854018000d119068440803503c18000740004081c0c51070103148108802c06170005600d00040880b90b003130501000700851494030481c19103012030804d50307540741500d26540e910034215140c0ca0781c002907440201050300000800080c8544600594065880c01c9190f046a964a00240d0143d010700701000c0d502c072100c4401e09050385000701482605003041c0c100a10480c2d5545d10208103891188426105c41c3c20000c1c1e203882500d8240300d402e001d008241402c480d09140c0e409062100c1420888840c0551705110201081da0b0240083d02e00465000040743c3c800c403c4104100d038188 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 127721591 1250 127720341 127720343
    0xf1201080c030334060515040e010b0105073c0201091d060409030e10020114100b03010605030a0b06040b0a02071a1806160b0f070f051c141003 63
    0x70003500a208210301d40841104d4072403030f201c1a0703a11504400c0c041d03a18007001d036401c0343d0354203441444400c000540c5d034000d0398400c00c8880c101518903113201003400107075404c2c2c3c04015900d0b45040708080c1a0303a08001035450b0700b6081a580c071000003800c80e206640c803000011361416000c03e2489000404003101d1106003061007030781c507565070642d01c070403802020740c40c50700000e0582d2940b000528079041540c03100074510b000e403420a6407500c400021071094402982420010b035142c0410399850baa0020086404c041c0d482c11816090f843d2440d400750034001805468200b080000c00325410000a03000955110704c01050b0319500e035a16014004968032100a80015024203800011402300c1d841c0010b0052016178207052500840b030103015559400140e0442d84a0800d21000240d2944403203286031407403040100c81c61074103100c4000010328200600540410004080092416600c001507a030000f03c900f9100c00c100c40c04652180c09421500401445a02c0c1c107401c00203500c480740040b908030703 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 127722841 1250 127721591 127721593
    0x30804030606060801260c04050703090515060105070f0501140a0518010504170706020409050108240c1e1b0c0a140a06180f06080403030b09100513020f120108 70
    0x690740d07001c040d100404c091040801c2100c11820000c403c0070100541800d01e10030800f030340c00d482c62140c0010100d400a80320100021303039610409007040000c000301c0c006124040003805403443d1150000f011446044001410703100c4440000d000c201d4250480411000d000c100c1c0c0d0311920342119000002c2c001200c84082c483e61821788100c007648180b01b80f502503600080500307002c000010245406a02c5204211402c0e90708100c0000da9464a00c2407501034060038024025440b400b148901030341d1074040000740c0c1d0b00003c0c814051800006422282410f504820348004603080c4201c80c0c0c550700514915414590400380d0303070214038030040346a01111208030340c078510300303a115052040c400351180e819035080065088280551401000c2d103050307010015a003400c042d40c0b83d40700420f00340703d554003410201d80c00d4002e000406405008181c9030f24020b5441c07450a2070304000c420f5051075244a010701907000c1300f0210150780074613011038000c001440c1855586082124004076005806d01c2140c0d07413 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 127724091 1250 127722841 127722851
    0x1b06040b160e0901090e031309020d050f07050403150207021002060105011d0a0b1b030703020f0d03090206070b060103020c030703020a14070b190c0204110d14061c0602130308040306 80
    0x100750281a5042d8024030140a07480942c5c200b240510080000d101d020039144401d1040d0a4114080c85080380540f0a4000250702c1c2c074091411141501c801400704072500a801c0100100958040c0540c0d04403038001c1022300d032024072140c01000074802c41402941001c400075400070300607000101d05049410a030fa03511124408944030446482ca0755001e903030b20403060b0104100b040703e03500107002c0d15403100c484010a060080900c6107142d000d100c0c100e01682007101c24405e602814404400010250b040c24441d40c5d849070300080c214412004000e06040127440404d125902c2a8103640703c40c4000000c50780e036072866050281d42c030200d408003100c142c4c00e0405104840240499014111024040d003e400c0a56449018120180103a03816041081a0100a0141c2d07298005d40c4502c4400210695984038030900103800c1d500d00c0302c4841040d420442c18400380780c40f401905142204440c00120360105140b030528080c1c0700b40f60b4580c50010aa180100c01c2c0101c680081c02164403a1004200c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 127725341 1250 127724091 127724131
    0x512060102010203240f030a030804031116030b2e0504050912070f0807150606030b040c02030d0c0504050909010c0f0906020a03110a1203050114030a02060a051b06040b 74
    0xc00e030310084694a40c080317a0348200c4000001c1e020701303083d04010010320400c22002c525011900d0700903082c01c02c0e400940344000307200038543c0140c0ca80603151400c10280031174980058581d6500c02c5544401010900c1d20000102911241c1c0702c4801c18003000364621041720180080d01881c0e210314002e45100b18a40000300ea0800c100145041802c40345540681c188085619644200142140195040c0d20200030084c0055503071000300c01e105900c0304c40094a10b0500708001e0480710390f0300c88580100d1404e0803a20f81142c0000540d0b0345624046e0000c900352001503801c654601481d40056005651001480400035042d00200342d5403000c1e90ba02120707021507071011220310000f4480ca0002d81c110040c2000868802d800164a0350386242c22602c1c0403032039645092035441d92080c0c0c8000681d482c4014848405a031003e036a00c01c800b10020320000031180c001a0b980e1003101c10f44420322100141d0104805040e124281045501d07006880080c83c180c10160504c61080320b042d00f1a440e003c2001c1 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 127726591 1250 127725341 127725343
    0x1d010b040b0f150c03030903070c0b03060901270609061a03130f020f0603180606040608101d0601060c0611031311061b0c030f0c010c030c080d06060512060102 70
    0x76600000c020080b036070b640381610030b0000c8a0240307600f000300288100244040440300f0402140205004002580d644401d820141050a03558214004424042060100541c1c1d4045524151800c0269184050000c41c12000348818061241e0500c0e6051070303800500308040b54010700c11100e80310180712683d11505a41030162200300c40580801450f900c00c60007180042c03010311402840901040ca511101c0d5000a07040e4004462a08000030160b0603031040f041b0a12500790461740a84040c41014101091252204017007944080c54680da44995183c0c0c505040c45151424014001c0da4541d584514008054100c14801590914203041c90300103036802400c1164030410f80317113480d209218829955288811417030054140c2c044410b10440444a030001015900490464000c11440d5600c0d8203050803c045030501000703a400401c05100719036041414a141c0a074580381090f0a0700503407070440018028040f20055580ca8028089141c9030800c0c0104064903401000da0010380d1200012 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 127727841 1250 127726591 127726601
    0x60b010203041203050c010f0f0b030c10090302010804020d14061006140313020d0503210901050405070302060d06180f0e06010302030c0d020604050303161e170711041d010b04 77
    0x20303c071040103800641001c01d00c5100606016600c3c3c400210300303111900d0884082d01c04c0e103042c0c0740d020f41da613200f03007846450108140c0200400644401c522140b00140140066070384d848041d0500c010200040c0c01c65461001c003003901540080015021310006811541d5840c0803514080c1a428064012900d90700801600040c0580300340032600d503903503610360104500711340c2500f240c00110161102d400100180003070405021034406251120420310074004000c90301400102144c4d00d881c080c0408035001146d00c070284c2c2d0301550384681e03400303c03680148020802548102c010f299801480112251143c21220149004681c00d0002034044421541c4484003840020740c1a445400340c800541030500b400707103081d030009084604044e43d81002c04d065a1280058005007072746001c000341000701c880c440e02e2090304996000785022a95555628250700b071506140b4030b01c800820740400300600c000880720307110000b034000d2010710440031050403464286200d40310203500303000a082c21030a2134450 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 127729091 1250 127727841 127727849
    0xe090604050d050a03020712050a030c080402030703030c0201021f06050a050907120e0309040e030306090f0103080f030402060412030c12020d050d0b0a05031b180106020a11030106170307060b01020304 88
    0x141014004081040e5980d034004e100040030b0680901141c0080b07200006007040200e0b450302c815948641c183c030b0050407580c515901e0814008008240301c0543c50000751002a0303941410045c805d0586400142c0c0381c40141041d12214440400c01040390070315640181040711426204600980e486104001c40280204c4100f400250b040d00350b56600712a43c1c1014070314860361408e4928180f2881d02080949510903280d10540d400041440928184000c209500c5551040d07280303010350656840f00214481c0c0c0c08081c60301c05004c804141590baa8004650041c081c001a01e40001c92500d006004031401c144240e40100b5003240d92181c460000ca4083c0b4041403039030b18649410300401034180181500c601c10364000c0810345021469440400151240303081c85001162040011401c00114000582c0711120072408140100031030364000074800343e083d0344101082d002a66560100e8010721841d07000452020010243d003a94040100003042541d00548043c03140c4d81c0c460f001660340e44583c0c4a = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 127730341 1250 127729091 127729093
    0x20901030c1d0d140307110907030b03121804060e040201080601111f090b0106020a120207030201080f040f080a0c03021b090c0d0b04050709140108010b1801020102071406010e09060405 81
    0x401070040e1030441c0c038503c50a03101c1c0c0400d00394400c0403640f02d0300d1604a0001120718403060b0b102c00c2c3e25442c1c070b020303800e40c080c1c07007443c083c0030303217181100441c0e10b03181a105521000300b00400c65220086c490403001c8421800a002004451ba03903250041c2120070036039050b800304520202241055201e6102c0c48101c192072001000c0c0410900d025442c80642e102500c10001d9071241c1210005000a09442c001c24482d40104001c0440d4100101c0b8030310010021805e544c008142000182d070401e14a03940440c0c43d0888031405c3c0d0740c07170800c29110180810f005044600c0001c510344010340200d07200038601c0c029400c80c2d5002049004076810340300c0580c034203a88211003900080c01d261054008108031840c8040110340034241c0d07000725081e05e0040d1403010110781d441c1c00611042c1d179004074890811009107480f01c919454464096030a1144440c8e45924503a09450424164002d404072008107501c140b0707109101144c464096100c113401c0c046c01010700c4512020401901c400643c0b2030290750460 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 127731591 1250 127730341 127730387
    0x30b1e0a060e030c06070b060102120a020c1005120f0711010603050304031218060806041a0a15091d0609070503010303020d08060a0e07170a09050307060903050405090406020901030c 80
    0x16070150303111951040190b50502c14441d14046a84458006d0504107107d02002c52050502c0c40000e400c011000c2e2504400a0041c0a10f055003540007420060380b200035110401803500d00e480803100ca03c5000d920710301e20145401031040c100d41c400c1260b07224010359607400e00007092102c42c2c90b09880d180d21000d0400e43c0144801d04c04140180908814011981840000c10706a106803020180041c1d101031b02044814040208904190046170800c54071114200740180449d00001e4614070b55004440c4400a05652a60b201d40510a400c010305203103030501d0004031030113800400030b0008458160007056400003044440c4d014005890580380e25402625202c21000011510b84c000184500d910080000c40080c56029040600b03000300c4950742d46005501d0341c0c10281521400c042c21031030503580340569000214070b020041d44e408a40c003d401003079032602400c04482da801950001c9900c090380d102440f0402216078001c00d0451802c2e2414007004240000a0340c0306401620104000d10b514 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 127732841 1250 127731591 127731599
    0x815030a080906120a0608010f18030e13022d0a05070b0c040b04090504020307060e012c040c020f01110906070219031407030b01050d0c170c10030b1e0a 67
    0x1140141c150b0a00140401c0d05100302d018142d4400c0200b80d0310064490303034030401808050000e015640046112820070710441c0d41c1102202c10100d1031080c0501000410210790080c0d1340c5800f02e50702200740c84001035450304120000500350703c0c8103003200c2d020390403004172181c0c80c0d00403d02654110f0409464660804146450340030a401c4014240b400c1c034203007008085802c02100000c6e0000d1b10729048001031914051043c9480d019494101c070701404040700c1c13100384681e0700000312031001e2016201c241a459098012103460101c200042d90302c281014681100d2542c0010007001000d001d000900c4860b03c00c1404134101c3c8562850b0701d070070250400840f80035040042041c4c0f80080b900c02c003400082d40da07450381c0000b050760400140040d00030450030000d0010740c12542c5d01605003203600c1d03000400c1e140d4846013404914407900c116000100071000d42c4207000d00a6040c02000544070707000d50002440700400404007101a00e10502e80303251101c6103c007a000c20005802000380c0304013500c03414 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 127734091 1250 127732841 127732853
    0x7170601090c0203190e1302030601230d1505030109030c0c06090b09010c0203031c0204050f0102010614040e0f060c1b190303050c0904140a0b010503040506040219031b060815030a 79
    0x503c4017206208403000549450346451034103c5c66040c47c0c0f81d0060303e0b130a0600006080404071034242c140c02c0710142d42105e4500301b0100300c0d4100411034000251044118968441d50540ca82c0400d6040d4a050841c00c107054105003d00d50142c400d0903900035642e00e41c14140d809050074000e200d1304450510510383c40354043c8003500100b50000b01101d0030115518120b1228a2002c41c0c01c42150360046401c01c52410701e1840028400c000740000c0c0810350070400600903c5e00080035803032040c4e848101c5404201802d2254500711480c80d070a88140d0b01d07080e100720344180e0200c0149a4220180d009000303000d40042441e000905400c040c102c4607007000c4d28210050f00b006001c44468100030400070030755030790b82d204140c820200b15860ba8003528003800305008540d40102620306000d020030800000580114100d42e101e941140c0804000f00c40440340103030420b10b500001d0440010400d00404180e010111000702c4000c1c0d80d90402c1079803a01c150500d0300300c410300d1458043d802818001c0010308 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 127735341 1250 127734091 127734127
    0xc16020906210c03120705060a15050a03080c0d1718030408010c09051003091511040b030a0203091204050d06110c07030b01090f020f180409020307170601090c0203 72
    0xc0010200002801860350a0b0540003418280096660010041040f01e05050285425110100f00054280134058488a4072143c00402ca04515030f03a800e0502c003001c1d400700960340901409044031207800d0312454000c016512056284406114030841400f43d00e00c0b98128400d0845a2420810b0316201c258808540a80710b04074003800e030006100114070103600b445004000c03403ca5582c0703141c00c0d2030501804143c1c0017400f0010b0405d820701428002107200109039040321031a0400014940c0301403501c0031414003403900b10340980c00d0004240004c0007a2034000d54001c4a018094400100398010135400f248034512a146c3c10440110f4480042440703948403c0c0790310894141140307009079143d4143d0500c000f581085800c107061b403005108000d11481107480d02503c1102c1189400142110310304140100e542090a03a00c8800301802c0355221038100001c4c0988c0030782107450300c903203c418288449000d2003100c1520b208484c00003c210106010300c2ca2551000c4d006035152118031644c01810340 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 127736591 1250 127735341 127735351
    0x906130609060b09130209010b0f0313050f06041505090f0c270403170f0907050d0305160c090b060304020a0e09030705070b0409111207030b010917030705060c160209 73
    0x503074504100020f502c13145100781c40780c00b40c0c00218092039503500c10004071180603000103401e4401800400038003030010f811682c100c480c0c100c0c010343c041c1451038114a4000000503007466800f40c41d0a0108100c40a00e15188421a9280601856444c150007951700c0059111011740340c0d100300c4013110103003480081c1d20003da0341306c0011200c1001160303040410780d03400e0f04c0032400200c0d2402c1841e00e40a2140200d600f1418241105059003000082a42d50b0782d00d41c010a4032921503509813008050048040350440950940c00100c0a01130341031849a0718075500c41c8030803240c10000d18103042d1070140200c0f882642d000781050304e01410100c0000c0c1d6480c1c010b00c0780c8100c3c80100b25102c003090040042c0001814040944c0b42d88900f0000c1c01e000ba00c0c0c0d244a580c558030010b20282d140d05206800e19680070905144c00501c4014140048403c0091070b8040061240c0c45405164076160101c000d1a8150182c0200c443c9074640d000a01001d126940c5403000301054096500e00624100507501e41103 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 127737841 1250 127736591 127736603
    0x70f1509080120160209090309010801050d0c0302040c05090405090c010906020c0604091802030a210e06030a0e12070803010f1a07140a0803090105090c01090f090b040908130303080906130609 84
    0x485496021580000f4207940c01f904036030000c1014069581d2108419016080a680d16414601c0d1649d8040500310035010091280307441d5009641d400c0e120304255551800000d205115034244034003129210840c02120600150021102150450001a1081c090070f07001d0400c034541840d282e150b90051642c052285107042c0140817820159504012401040f8040d0517084071a40004419905015400107400240000081502c42555a10341139079400400e0400101d00968000412800c00c1c1c80940384100c18003012520406201e00070010f141a1642e030988420100c0c0c4400340a05c088646480f01e13040c0f10130400800b0f00090508023004800d10090040314002590f0b5a580c02c582c3e001110302d10f1490790740360100701551001b0090300d01003801c20700307258101e0b50815201e2000c90a83c1c5c0039041c071040d01c90100300455100c3d5030100254682001c090703911094034104020b00c110032403200341c00240030200070502c0e0700c0000c584207024002024084803105100d6031070401030443c01005542d4 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 127739091 1250 127737841 127737877
    0x20f04030804060914030106030f06020703090e101a0301082104091802031009020f0f0a360e0d0806040207020d03020105010510090521070f1509080120 67
    0x3030350740340c050b0000e8a015258011054108003040500141301d0480503c26070420104001240644140040c541d40002025a40e14031038141907619000c2c552003607402c01c00351410000c4080480030000b0544516465040803100368801090a078002070050f402c080e0030160314900c86941d5203102021480c50082c48a0609540f0a00c90f805c458170074006015842102200400b1481d040c00a49000d41044804008694064011030f19000c200c0024a004100d10345001d03550f03949021945e4014460700e110b482ca400380400000311050105540303810062041c0c64004007180340340c014040b520140301c0017055000340c41c5d5000c5508100c06010243c000b6401c00c031213409a21100c516103400e074000c4d000440e281d458101800441141d03000302d1410024464004d21042c1d8400300b510345120f016110300c50680190f0310300c280c10000c050307010300d40380800000e00145c40420b6078510101e0318095125a55025a42c2100c02d0a9940c60b00140b0389a035411004901d10792607c42c00360001281c0c040b20124 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 127740341 1250 127739091 127739093
    0xc1e071203090b070f06060b161b12050a0203060c0c0303040303020901030605030f1b010c0803010b0c010b090f01051302183007050f1002060c0706020d18030909050613020f0403 78
    0x29805000c0c00e840d81c0160609400900820340200401000b20b01c8c40c551420100d080b07141c2041048030703070003441028840c01c104910140110020090300c12100c50080030a200e18081e5a81c03516000b049000303001c0c4030000b443c104014015a2140b81c0424040e51955031580d030218000d40c000c0c031390603040c10390754a07020406460400c0311080403440600100922020500801c800d442c900800701e04003c824080100020303101d205490440b602c110280f81c5450000c0c0d0764038050955804000d41203084041040034040c48206450b04880040e144440c4165119a140d020380c454480b52120380200b0310740098603401c205c00d0701a11a80c0b4118100a03410080416200301c2d4038410760480c840c0d101032001d001a1400c100d110700048000c0311080c1070840b1108000e526000c00500c0848104404250b00301445071310b0301200d80c0e002ca0303088200710b400e0040c2030348640c50f00c403910300340c000404105000c2003d02062003414094a0010b10b920141410008003070301030340c0320080d242c19071181800000 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 127741591 1250 127740341 127740359
    0x50a06030f120908030f18030721140d0516230115090212060d08040b0a0903050c0102010605150901090b040b1b010507050a0c1a0901020c1e07120309 66
    0x1201c1c0340700c1c4580141244103020014003404043d0080c00481d001080348442040c2081c1c100c0c1e42c503021107288540c0d036104010010b4145600381c1d05c40e004e0180d0707840c6c0ca00d80f135000c11000c5c2ea80c240e11401050580383c0d18000c040356600001c880010200e982006103420502e218950340341100d20402001e850060300407841a000014581c100109a4448034101001034440180c40003800d4209411400c151018504a10022010b40094046d81d600309901e41440110780c1200e02a20307641c80341d19038034016400010f00b0b0440314070040da0305016010343e1649542c0706024039400c607040105a5043d03101f4601a64141794080ca00d080d06108001000050050007103000d44028200c459440742c94400d5135509048808504210400c982d15010402c126540c0150030b541a648440c6461150107402e85090401d000400c013503003211140c400300704220240c1c1500103010680a5006075031001075128400002c43d1b54001d8006c50300d420128007405020714040050824501915006180b40d548103012 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 127742841 1250 127741591 127741613
    0xd020402190305010f0509040b0c09011b0c032d080f09032413030801060c020a050409060b01031a01120b030106030c03080325080601120f06120b06010c02010c06050a0603 75
    0x148040b81c0c0390401045001220b620318030061030192860200352405a03262414000300600340140c01001081c0351117140d209442502c1c294000d1540000017064904004d60079040521046440c40703500d00000c2c4140441c07011300020303a2310440c82e80d440d150040d641d41416030044075003e071450f0014841020913607000c00100400364940105032081d425000d00c030f14148140101205024903c20400c040007951145c912411680c8524007060040c0c031a20014880408990010398410304000d120014070075941c0c0144001c95090300c04000c00c101d90f0311001504940b845665020850a040b0015250880e82151842d45001800054200d03100d607075603070400500d500b003559090804010080000e818064044801281d05940358003c40e000e0130007041680020245810030172b0f14907000780500059005a10f903071074071070400e0180319118102d249100710310060030340b03a250090020540d1540611801c07110385030182c1d10080011a1a140c1c40060715029108072f010641e1058000040745801c0383c4 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 127744091 1250 127742841 127742887
    0x1707050307141213080c030d050a030c050409020705100b1504031104090501050c1c061a07050f060a0b0411070c030f1b0e041505010819031b0c080615010c020d020402 73
    0x8241c104d400d2016031440d03d10040030340d038029482141111180c1d0340000c15078800009034030300841d0007000180111941d021b254402c1040c5800400c44500f0884017098000200a002104109003290482000f2802003d00c0000245010402052010600801501d405040701400c04a6286000d0f40d410b401c48004980040c4524404580b1749180c0141c010780162014020805205080c240805c0070004040309804201034400003c1e080304004080c00500000304020040e6a044c1ca8200651000b61400e0001c5c180f0491900040445040082c001d4072403998120000120040c00d5039156501c54a440c0d00565159010301a1165400103540c03003c0040d003601a60b44c4e000e800d040c80d00d81103510920040003003450030600140b252010000d440068220243e00940c42c8440c28102600d502c0030311b02d55201400d0500642c80306001406540c403040b1492003045031410741e0b40700360480d4003200e160f240c640020b910300001c0001d460099005448140002c000600d00720301c00041014800030380c10 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 127745341 1250 127744091 127744117
    0x1d0d0c0807050907050304021309110a0305210708040608070c080307020d080604050915060d0209090303011d09030a050d060e04110913110d06140906010317070503071412 75
    0x1c0501180c00c242c1d0080341c0020850802c43e08504142c3d00085004403092500141c070b03680c411042061210400110b00c000102511090003261607042c0152929040455020815002c0c880400301d984814110380400750440d4040d400d060402c4402c44040801070034200c10032122030504808169550011400381c0303480d030000c02c0b4134080c640c03019242d401c000340150b1041d45480b080044810300072600e645110090319040d051507443e60009008202d08003006500071203001c08000043c04000000d46c16146017040e200d400203500c4c107035088006000c880d900c1454005019884500307001d1009020f18100052002c04c0041d212040c001c00e01c074044030165143c0c891147c0301403550030190020342d0803901c040a2a2001c080d1a11803c046090701c40c200c5d03000d80c200140d04000d01100d548021001c2c008403c43d003881d410f203441220360b1418280010f031042665001a038041c094940d080b14001035021001d5418a4483d0311600c6000071060551001400342000034a01030307110400611461800003 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 127746591 1250 127745341 127745353
    0x7050603100608060604060c030c081b010f0b0301050709210618120f050702060c0a050105090604151a0607240207030207080c010905120a050109080a020f060105011d0d0c08 76
    0x10303000f0070800018201c00e00032002044144513103a8084014000d03241c05050544800d8141e14013030b0450b00c1400580b0748103088090518a0385034040d00008441a0180403c0c00401d54a00c00c1508844054462202091820744104400342800c201140c01d4540040f40361801304168459030706480e02104c980030044414031001e410020148107018000c80e151a2607141e0400d2140040c00d0340c428860040c7c03080c2408941450784e1030040140c101c4003a8002c0080c01a0304096401300d6480800351011558217260300380b004007082446c4940030301031600140003400c581c068030601c6443ea1020704191108414002201401d000745c4019812051864400690310455414002e0034600c1c9a00710f039a1030b401c07403c641d5181d44c0e809800b06c82078034011118090307004203194281c0c2ca0712800100040443d400e0101e0001408465005044c0d5084140c0949541007000c1d51000d8985009000d29404107411400001c8044045c01d1811401400640b0481c007844482c1c0340c0c1050303c0078a50040007164480 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 127747841 1250 127746591 127746599
    0x2107121503120f0206070302070606050303040b130b0a080402010e0f0306040b0105010f030204050f060903030d0510140306240102070302120f0708030a0c03080628030b16200705060310 81
    0x449102d034800d82071030001044040400000e45030100039001904041d0003040d00710901c00240c1c043d10040c10020112a40d555980d000842d05401c482d94080303905812100008520348500304903556412140e503481e0f40c03a40c03a0380c01900c1035101784030301e2070300311208040388906900c00f0820340e4090342c05484059840e601d0b10000500c3c02034500705d08810540144000c20035915480050200d180d4112036443e101c00d404004640366001e04204801c0503401c140c10322030301c80382d4811400141c40b0040508064003000c103051682d58807040c3d4014001c010a02c03807058060a140000000802c81403044d204420b5807600064401121580304a000d500f15483c5200e81c1d500070810000100021000340d03041c000c500d000640140c078006409402e0144900c0054090380c0d0b641c4101c400386010310007411825154081d81c13041e18406000484400030414045030303a110710b0b01c1c99026002c110343ea500180c501c014001d03203e0b404000c0000801031241c1480401c07a0742d6904003030741c4961910742d41190031b40e180c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 127749091 1250 127747841 127747853
    0x3110f120411010903050703020d03050c120309011401030f03080a0b0a1409090106030308070c110a0315050106020106210627060b01081006110a0501020c0c0102122107121503 77
    0x682c007241070510424000c1000002e00109450013101e0b01164005d0380100142015a007510800d000391a590144008042544042c00301441c02002d20100070044030181213100b201745c10081c0000b80c40300a202c003140380003d214580c810381c03001c0007480200d003251a08020620324070481d000500454403d00d0383c403805040c1101982e512070903100085c0002495504e0151600720060b00308410405c0f43c5040209010070103401c081c1d4080050049442150350341072102d01c2c0000c1070f50500e40d20f410708000182c00d80c41400f03900b00360b41e0945503426820344501040c012081030038900311907141d211300d0a04443c440010420098440441d1040c001c45903900d0b016007201c00a04402d4140032080d020300080c0d05042c2d21a000f82e60060601c07102c3d580d040c00782103203003e880000042c845d42c0005100c1c11404404180034071044420303000c4039002c42100c40140c0040c02001c40d90018401003048000e074004801c48800c1d00f040c201c0c05c00b03c0703030100141c2404003580e5a030000e90940f540105003c00401c41 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 127750341 1250 127749091 127749113
    0x90b0a03090605150f13150b0d0507020606090109180605010902030402030609010603080901050702121f0608011a010807050d1b080612070e0618150a0602070b090103110f1204 77
    0x852030708602c458075500060210020501c4690140c0301c140e074129981e51887d408030100014050320b10102d181d682e24201490b622144140340a181404040b420050001402c0c07401002d000b055003d90340e003031030100300017031200300010100d401007102e001c0003083c0c862080d80e0281c54803d0015a8030f00d058010f1610b0b219002d0110465685000410400f00301c441040d0f903d815400d180ca00e959901c01d0000076000c0c250744144d000c0074010803242900d40884e80035508240d0f1440c440034401c85544280c03550886000c1004081e0b008581013002c8a698030608040e50b0141c0d9074204641003502500340c142c100c03490076103404040c1c0151040ca17010660003440c0b20780d1103002215101314070344025011984545040c85240100760411012410300ea80b000356034081c040f41c180351451589801d01100c0c0f40c0004d4403218a01420f00c2403804031780d0620200303500059810303541d40185800e220341c00450050400a040b0040c0d00d03014000c1106001041008105c0b62031142004c60700c1d800c0505121403103030 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 127751591 1250 127750341 127750351
    0xa030207170c0108060a030212010506040612081c1104150e0f1e031e030405121501030b100302060a12060f120602070f050d09080f031206060a090b0a03090605 70
    0x404001070340030700800000342e0760868070000e103040095510740b800420281030031600300035407100d0b40902201608005600c42d5101e94001c5506009035665140020115268490701910259003004001035842040100d01000074804400041c420080081049290015084a800003100843c088095580710180c0d2101d400200c400c4011413008000003900d107540c500e24104a461409108111542c0500600c0d00c54501c560b0460301d074113a00200d107500d035806801254801e64400c42c08855284d00050b00d00c0d0b1101d22220b401c1c1c43c03a42191a84030500748014440b0400d02034140002c001038980b00003600b03c0e8025500e40500c00d207240441002900d03481d40013500b11800034641005124401c0c520041c03d5030300084016500c9d0818200b5800d0403103800c0d400303012482100003032251030b544110490100c0e281c03103054404222403410515140d101d10255503e8111010f404101c807854641d0080c40010302900b48040045d82e00c0c1d10361a0315030801c10481001c241c0d910601d13000d0140b280142c540c00 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 127752841 1250 127751591 127751609
    0x30302010f110304060e0f0111040e010f0501051204050718050a0c08100b0703030f02070503190e0102070e06010e03100e011805030711060403060e1c050909060105030c070605090a030207 82
    0x220b00040e18003030345020083c805000d1640b40c01c01050304076418860046001c0c40b8100a00c50608011682c90341c9500a02c82c039802c034481c40c03000007119200d042d5020b040d204169101071802045040700301c00940c024006a4850050490001d034032081a11004010316105402207603d150848008003180e1441d40c0c0304041c0241c40d000c00c0213031a00c1c10704400517242503044042d00d500b068202203004001c1e00c1c140080c0d4a01c0001d400090210010280c41c0001c0c52320905043c40100d5242101c40c8074207840600e015a000107009c0c00408940c1248552040e01032409000c0c00303e0000001c0d00c2c0c480000c0355545904d6452040c09851b400078041d96241c0200548030940d01c9c145a81c3d82aaa032148071406000a1891984100d543c0c1d0f42c40215001980c1180062200c180520f0403e0340350680c1404240b001d9501c0751014800e180100161460610b0003048071307810f60768140040d62158401400d00511342c104102c0180055000d02c9094080c00b058402080d02100518010b445e01045070004508 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 127754091 1250 127752841 127752851
    0x105070210020a11120d0606050f1804020c060412030e070315020306010c02100201140f0c03040209270a050601050109080d1d040c0806180c09040e03040e0907030302010f 75
    0x6095000500e21040c86000c91006907190051442101c140c003045410002c24052416074a105903070890180c100307681d11500030003107155109400d94492181150042a10009001e0035510036040c480d900b01c8810050405480c02d09049400e60403c402100e0403614000a03202c0404295414460340d00c00c0711401c802405150b0460b100d0b00814528080c480c01c0d01ca400000160b11644604220221107074058442d074500310313800c40d000e03020b0300060031416020340800d07000906941550403540c2c01000c0b100031a51460300e0741c1d024000741a01c005d00e03c540309254248441e200f0603c2030406104543d80030081d0203a80b4140c07a00c181440d2060344140e0411038060024000e06001107590329107840c841c05c0810310140340c6001912200107050206500524000321140d0a64100f80d0b6a0f2061304108e81e91307050140d60103904d007941c0c801070f01c2d1100c6802c418010b01c0c0351030500758800324400300100c007100d003090f60716145501d2070b0900b2a4401c41c039800204007001007507024061180440c00b07401c2e0030301ca = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 127755341 1250 127754091 127754101
    0xb1b030105011407050a05070803180406210203071a0a110105042f060f1c14010918050105040503040611010203010509070e012705030c0301180305280e0a06020105 72
    0x11520f1001510f42a00a00064080070401c0400200544950102c2074402260b40c50700201d459800c45803521000203481c803c40c040301d1038184200002d0b00d4940c400c00085100c50000f402408104070b000301d03018030940c403010507502c4d11402c2d0304070b49812050b85039503554081d540003803443c5034400c0c1c018003aa042405100004540103c1e0000300200c4000c000c1c1940700802e0420030703001082e140243c02c18800520207008490031801011404104110104000409561403040390420701414564207401d1006019184c0c968101c1034403030803001111b40d1800707030f16141c1a00f114010780d4110741c9a840020104600754104640440016904000b1402e5601d0704c80441d460100041c2680704000404443d81c0850f030191880c410801c1009840c40040481d800001c030b4444000c0c0205486032107503ca21400034036050140420016481c00309201c000c005d660281c9080d005641000c024412001c1100d50b100841558480051095030f20003218140e04024070030402e209030400d504590601007040 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 127756591 1250 127755341 127755347
    0x30a020a0e09090106171506061e031510020a0c1e0308040b0301080c09090a080307030e010207030309020f0a031104021b0f2d030316180b1b030405031f06120b1b03010501 75
    0x48e8400e505580c9965a0303d12240c03840f000c40c51040c84441040e0000c4140103502d080880141007494003610600ca040748218000c2e60758200342140141b040211a000b404071059130103050200d04900034000b6040c64917680c0d034080e00e4015400052695601000400980100b007001c602c0781c0105a50900550a00704413184d2035070040030300a1700d190b00000100707180c40c2c4254011920a810707640215100e15481c50010050f2000d0041640b00c2c101080281400d45000c19802e0200c07548804580c495000030000d10020b50042401c80070307210241c02a01d08920018000000320140074800740250111451030041c400007041190403c1400943d00b9401085001048076002845850b42480d540440784040740c005142500100290036100c2e800103180703d600014040c030000d0601084000c200440741140d8a000302d1140c00d500da4841c1803070421502002000450b10740380d118011441c592500d05400c42d42101c0c0b20704403081d2401400304040d61900c1c100140104452071841c500d1540350100007 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 127757841 1250 127756591 127756633
    0x30d05060a150309030c02090103060e0f060c04050405090304030b2505040501210f06090603031d10110307080307080105011d06030a020c010b030d030902010f0311030a020a0e0909010617 82
    0x8902890707513441500d81890702807080100040c0d4001c01c10481c40d0384074600907014000717000c1c0020b00d0f0300ca91803020b40418401b00f0660312480341050000c1c1043e28000401c009804040e0401f07015000411001c40401c1c03442032228481c04051041c1c0c5807c120400e098110101200341440030070005100030701503030380c0c020814a250540c80c074103490b035500c08400c44001480307e800502460317454000000b900065940017401228041e0b19040c03070100491111596040250402c2c81e4442504440d0031940d40c0142c1b84902c80c042c50804503804d000c01da60b1481c00c194816a26403012405040c01084990f90001c421007000021803081d840c20390b0600041130090001809019403183c0200728502540001d40c4001e21140000b411a6054059240c01a000308940c0f0400c0e400214100403207803c541c080e00440148200d481d910358556947c0051507402900204001c500308010091614101e030b84022006000e800140000107d1626201038404c80c0c2642c0b98400c82d4581000220000c0c0ca9400009 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 127759091 1250 127757841 127757879
    0x30507080a03021b0f0706030b0906010c05100527011b030506010c0204060902090a08120a050702011e2d02070315061a0d050a0911010c03020c03030408030d05060a 72
    0x3009481e80028502a8064001e1151441c3d82841d4912404403400340001e0b4815801d0700c120590300526141c0702d04805444000440b55085070014010035081c2d4813415544000e54040e6092b90392008554110740140c0780d09882840c10f41c2240a01d40c00380b55030b0809200604100203000704031425500b044403089225512180d0285641c440000d030030b0f03901923818400f0703540d4024410484140c480441070025000051024003d0440500c0030030744810008062650080420542c0d09000801d50300311101e51008500328100319041514880c54a00f4601041c8142d2854640108104012000000c040c50110051400030780142c03030100019004281d50068a400660200041d5250740b984005400243c1c003014045041071b004003408100c41c4044d0004142e0b40c54244600e8031040340404c03e440a20402600300c80a8803001d81007903003d4900e041806120307005070740c9000301840020f4155002036000e6243d603000000c60314070810791440b440d94880c408807148400c0900303000700c2c40102980034007 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 127760341 1250 127759091 127759103
    0x70305090a020f190905010806060402090a030803060d060204060e030606061303030806030a0507060c0309050a050609010509030106090203070e1305070e130f020304061e06031e0f0609030e03120403030507 90
    0x11030300825454200740c5020b01100d041d05501d001741c5c1c44c2c90f640c00038002440b82141501550011810503d06802144c100003c010200c07880e03503040d5110821b0316840500120b44c00f80000c8804000650305001801c003e04080d190161a050340d4030a1504011000300224840d02c001c011a68461030441a01d81c2503a4061815074680c1e0344080200c0e190000c07044001d4402d02c90391000043c040e91051103000070510940da15100079a5604c1804000b50060085540c482003d1249101c01d512410103030031a1440113001040070740e5a0904681241e006894501c00a20500d9240c103103418640030400001c00c1c1c00200f0081c7d49845c45000703298040c4205100c0c0300c0e84566103001d50101d140d4000413007082d10100219601e05051800400030b001280c404d0310040c00c1082e00140c0400320b481420b040320740010958011154040002000a00c0c5090844592034200c940364086822841107400d014844e8407901c5045242c2c008040ca010505803884112074800c10007400081c3d8000140c83c10250300207 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 127761591 1250 127760341 127760359
    0x907030603020916031e09020a0605040e0c0906070c091d0606030d141201061e2d02030c030301030b0a0605120d03021806030a06030c0906260109021f0305070305090a02 74
    0x980220701421200d0040305c456003044441b80060f9000341d01409106200300c0703015169690f42c2205a92034003580c03144030400b120400c0011201c44442c3c0040802c02c60003000e4510388940c550741d4101621b16034103c1c0303c6a82e50340c86181c10354003001c0031142a0304000001440342e07240020010360780e0b4421014a0082195540031106841085001e0310f0303074040c141d2440b90040d03854460040481d10004c02c03168501046060b40e0981d5800f41881c294405510390200c03070b804210a00c0a40c1c070180a40030b01007184003c0000c0c40e14004144059030103035208014500703103418400554026203560b6000980720341d4082c410540103c00000b1002403141440c01d0241e00c545441c0032203000341d4070854030660841c0000040004490b150b5001c0010780c1e1084102160464441604808445c258081e402900c030b13514010403a00745040d4114607005940340008215980540c1c00709040300c1084202c12224040c804980d8070710754245c004d003548444586003c114928092001d265560504075029000c2c0c6152 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 127762841 1250 127761591 127761631
    0x51902040509191401060f021501060c0f02061e0903010f11030a1e06081e1b040504110604031a070201140103111201050c07031d010807110a050a030c0209070306030209 74
    0x250005403d960b6002504c69481da95900050a964100c05140d1300500849030f905c00c1c0542c1503c2c20505079241e940d505650500720765a0f60b00d00e6410648242d0f40408107010b45554486803004440340c00019070f50085d1a081072900341400d5480e207050142901d03040081d04010105000182c9502c1aa080400300b0060798007441d0101000c07007108120312486c1000c2e004600300300d00150001d8a080c40c84070004411540411003034540510f1a01d2000d00c01c0d0344540d010082c076064005ca600680182001d901c3c1541c081c0001c4e046a01035071007180c0b9001c00080740080d00c16410768440d030107030050000740854002e24140ea031440307005020082207c40e1084c001c0e0300d10f4403045440012442d100d4020401d5041140b1081c034103800c400300c11000110590103a0440f0641c06000c91030f00041a11841441c0d228060155846541c07140040043d204800102000c10810454038441500941787c48661300d0846c01070124424000384200c080c582407420400041e00c0c1c0d0701e0070760f5008068075100c2000d250300f = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 127764091 1250 127762841 127762891
    0x1060509150f0a0e01110f0c060f0c0a050d0809030a09030303180b0f0610050c06042d030302030708131205030912130e160509090c0c0a06051902040509 67
    0x226880e2040c42000883d242c600e00b90010880b03000003009890b004017107540c01c041181e40384031841c556a400c0c1c0200555000504003c2d0280c102042e04501e400d040250754010146051050030043e111640700003403030704040c0c1d00259601c6e00041201701035803916204c010080e0032040d0038407004080540e80c0c030a4003807140320f03140c201d514542e001c0d6032100d4a040c02c6000450150080d10030350320071030040402d03400860003201141c499401000182c02d040d86c850700d41d5140966201c007421100b44511f9100c1100d900c00e840b4030200207109460040c1c40e030500c40c0000700b2210004061018241e1628a00c1d40807a5080394192144009803803c00d58940c3c1d441c0c00141170074441c0066101109000ca07408100050401d13281c001c1c0e03840703a0814280b03540c43c00b800000c0440c042580030007040c810014405103090000700c5e940c0c0042034016503840c104000d0181413800c0d40c0310720242d4141e5552028003c842d55488400b111920b0a40403d505090400000a03e01000500140c11f0005035240c0c507150050 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 127765341 1250 127764091 127764097
    0x303100509040f050610050a140904020d080705030403050307032a12211a010512192309150c0d0b0f150703020d0c0f080315040606020a11090106050915 67
    0x1031300c2410b5608604008152100441c1d95026180c8600000c02010400d64020b0100300c0d801c4400524502041d20746030280011841100701c03c0d1200340080204c2c00110314204000d000440c4507074010340d40c0d0011790400800c154107124130034000c101c00c031000603103041c003a00444400301d802c140035441c1c0c0c1c20100019200c4400464844103100101a160410300c0c41c103901000c80388240582d51803211941600444291194001548007644000042981450054041d080752000c0d40f100007522000c209001140041154554000c44c08000401c00c5441d01440450000e51811440340e0080c2028610301c407450040e106a00412a43c1d1403d451441e0341b43d034004c0a00d40005846c401c0ca03044d6001d925440e5522000c002d6002d407040511540c0e20394404c107009402c075504404102400801c41d0f40f841450391010349003156202101100c19002e0b5141c0c81000c000342040c0e002400c01e03888502d00107070340c4485018018420000c81004003c4030340c1060449500d864100d400c19645105011070803c0c83c0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 127766591 1250 127765341 127765343
    0x10e060d020907022103060616051002030f0405010c0f02060a020a0c2a14010203040e15150d06091b200a05010c03050c09010c030e0103061a040311030303100509040f 73
    0x1001c42c8051006458011501c5003000c18000c1e081898180301711942c4103984030a440f041c5d0030100c2007010309a81c080100046101900c284107889100000d140e410050b030b0030070364255000c100890103010800c403003445601e4055001d8203095000c07113010780002c0e4440000a004960040c0c0024207070400724030640381058a0f50b400301c140d04261481303260845414600d020050002c1007000d40100b65881c1c1c40d0030024107640141e00443c81c01e03060082e584103004001e4031001c0c4c900d240c80c1d110728541d51030200d01c0b04680118100c0b92b440f8402d02100382c050b03800f690b00814800d8030701003181007800c981c40c1e03014140c01ca403820880c03040d5401205c00b03162480441d038523894a024480340d40042000c1074103c9400340c041c075602485162a0019000b1151203180c901c580418407203038034000000d0103403080c0c1c0303103400c0c2c14140040c80c1540c405041e0080003852145ca0b182a000040074020000c2e51890010624019030042d815032030041740c041141241d40c040d40c0d00c0b13400030b40c00080c07c21000a0b0400340c5a = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 127767841 1250 127766591 127766599
    0x100203010b030a0506310e010c020d0201111e0304020a030f05030702010807090621060906030f02040c0306030b0430020115090c020d030f02041512050c070803010e060d02 75
    0xe6a507074030080d4058205981c0314801d5402d02c03000c1405458040c001c4055000c40012150341c10005440c8981304120501618201e04e80b14103110109820a00c640c9014041c50780241c846145100002421a80e000c5800300b00d4003014050400c0c0b180d5551450600343c9800c0042d2581d9440f1400051060748442d4002003412480e000310310b0402c080440038000c154402c1c2c80e01d248a4440580680358000c00e405803100066020a10b40d40c9508100314005c240c000c40e5800080c255240c1030280706840c026002510340404040c000c0b011803e00340304403403c000c1c503441c08020445c11695058145070002d000940103440104980c0800103c020700042c201c0d60549142c0c02d00c001084001e4041c3c0742003030614604025481001a403511580260b1201800d564080d0a0b00c40d22413006a0050402070303000c01120343d09000c007149540001c052021280540d03140c1200f501c1c801b0a240c4150f40000b40b000d25288020300500c80081ca000068a040d02d941c200e450080e80d8600000c00c1382d80b500c00ca400707548 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 127769091 1250 127767841 127767847
    0x50c030105071e090311090a060825090e03090909010212181e061b160c1a0f0412080705060703020919030c0b0a050408010203010e220f0308091002 65
    0x2079040740f00c1401c88912101d90003408103e80d031003030711124050310011b8240c0e5110340c40c6140301e01c0c0c4011200d51050345040e002501a071070304003203480c0249a40c131824446a62100f481010047e0840304801403201c000300f80580700844211507140d0080c4040f440c0200c0d10040030400305002901038994100c6400101a503500c0c1c01d1410318642159554642d0590140d00e81303080d291401c060030b1041c03000030500108102d4640481d040300900c2542030342070105200340700c1152a08400e000030080d85001e0983d040305c3c0c909100110304103910220305220452420004000810424402d940807204101c400740040c1c40325083c44082485100c0c0300400c94012041004003103130701540034140802c030546440d04076800307042034480d00200e68000034100f0300001c2020001c000607800100024501131520302d007040c1d96042041d0aa030802e8102900039409641040800318201c10304c40c0400d070390040c400503070700c0302074542c040c48400d000c4000e400c2003229030000c1d00e0b90703504200030000d02d5041d05003155 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 127770341 1250 127769091 127769101
    0x9100e07090c0c0209060402030f040809040b030f010c02010606050a091430061503030301050f04090b0106020d0f0314070810050607050309120c031005040c050a03150f020322050c030105 82
    0x1200070a00e0f00304a116140b2140851503030708052090720f04c6035900108107060313030711142c40304821078200303a81c0745074819102c2e04404960380781400318203034103d07184002080d4442d04000290a50b41950011020044280400e08c6c090b58028000300c100c80c0f010a80000b5207404001064980b1000c40d10080040c0003103c0440004644500c0802c40c036400c1070598400741c850300e04051103100f107140080d5255206200500151070b004050307024180e0024400907240040f0741e20064030020036400140560894808803815a030017107030203c0754a14918007007141c0c84122000040f440000b030040303401c03c10b5000024005003d508594405414000c20140d02d5133001d20303045075241d014400c928040d400c00d03e10700b000785000080820074060f0003000780c901c1501aa14007001007000130000d64100700d010302d00060684460042d840a14028031084101550641f00c6009407001e1141c080e10580c81001042521200034201020510700c000303c0320408107407401c1861034040c01d025040d074154a0302040c01 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 127771591 1250 127770341 127770347
    0x3072103090509070f1b1a040c1202010503070c0c03081c1d03030112031814040b03061605070203030d0c08040215040b07410f0609100e07090c 63
    0x851258441d5840c001aa912281031005540065400c0300100d016046941100c0303004040042e1404840001ca0b1543c04090711401079160004c20254008500041840b0a00070743c424480007902c405c0d42444640500c680c00205a4403006180804206074116500c0400c00e00d505207000450300302101300e440300c60040c0d19020155000c8000b800c6980391101c1d2000d0300b4000303d60030b81c2e04044d25020f54156840c00c3c2d500c481009420718102c04120b001010348403983d180495800141c00f0343c050b042d4102d4a114140011120204001c0d8400d41c401d1003000065041c80d1524040c821035880c105446030703440e00c042807039130017005050070035207040460510072a50300800441c0b080c0d0081300c0030001e80300c1159800303200d842903014407444810100007a0010603036840301c12030384840c03038145a159030400407025601e1070703615020102d2401c85407010200d5103031301700070a886801c5620080c0c01b0b00e003480400070382d460018244115a20391035044500840c9014001c44008001541d07040c440d41e401d4400007 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 127772841 1250 127771591 127771649
    0x108041401140924060a060e0102070306020c0313050d020d033b03070501080925080105040c030209010b0406230c0706021c050928050604030c030506090606100302090307 75
    0x510301d0258000801c0104c8034860800c103004a101400e10510942403c0c0c0c01c44400411000460640c0f140c1c100c000300161141c402000c0f200e1034100a940c40b444004005c08403943c2d10b50042e44200310700d4045c403000d40d40d00d000c43c4030a10f0785406e121003803115410005c140d0341c050340a4001603914140c25280b61721401035502c41090341c2101038400c030700e442e030005480d901000d503886800c030740c0b107266006074844405d541441d212022803210201d05030b85404141c00c0d80c4007240d0896110552410800440c201008103034090312980c00d0407420030342010802042050407444030390700e01980d0b020301079440440e1000c4400c00c1d582001505c690680b80c00e8080d41d154620104816090082d91600000303c0c0b2500a841002400504041196a00b03160f2003413a20312400c0450400701c0c5003031000a141d41c0f07800042006500c81d01602070000e181d81030683c2409001800c00409070010020001e0564881046000755a40c81c1001030b1070300d4240c03000c40d01d0864203400040d41c0501851340d140d4544010b40030 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 127774091 1250 127772841 127772863
    0x30b06030d021501030f0302150a1a01030e190c0f032301020412030c02040608010606021b0402040f120606050307030f2001020c0d06270b07030204030201080414011409 74
    0x1140c01e8601c41040880c2c0c0d80d00000b1481402c514540018000a0b076180510182e890017441160751401442c0d14150801c0070035200c0b2072400e0b640c0ca00e91200c0704040ba0030000020745c02d0800700000300840120070749542c100203200b13402c828010702c500200024059075a0117170448080b02c4090f10385030701c0d01c0291054442203611100717030102881c4088480500844068a01e4031642110b04440c1c0c5c1d4040e110300148802c202d03131042e11880301065480d4244545c2d0300403c255402000850b600c81248a4144522040c40d40124010041230000f0150070341d19000725880301c02e0511091b1000d0500e1402003080e6040541d042c0940e500010a0012590380042204e008000c4507a524004030800d06050000841050144c0c000c1304c586070051030441c07082030304a8060351001c21b0743e22103c0002c00d241d0108804010381d1040ca4030090f0240f05413420169800801400d0451034142503800103030160200405c001d103187d0602203900f04085c000c0d00f008442c01e400301d14040641c10680656901c03030072034103a = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 127775341 1250 127774091 127774093
    0x6020a0504060206130203070605090117040308011508091b0111030a030506120c010e1005070204140f0106080c070602070f06090308061201110904150f060309060b040b130506040f0204030b0603 85
    0x8080303055405d000c4401286a41d006006105c510724014043e40e2a07041710f15018140008140710f04ac041c104040c00350310540c425603d88805606041c0707000320856600044000700400b02c2c04010300940005184040103800c905030b031100744420390040701d01684101c0d43c14100c2c000031500d191040e402d070700001c1c051401269144140b541c1d03d03118503601c8890038800c600041d808038904e0101e00380b02c1880442c4001c40c0c07034442e1420701e454000c80c042e11a00407001e00e0041c040004c0103507000c070100b0f01d0f0f800b520a900d040d50540c284014200350500a428000e0b00e100c0c0c5c0080d8900400c1000b402a07400590b03c0002401380a01500303010341000011540c0900a2000c1112585841d9062003001d660103481501c0b98100310110382400000c0410782161842100d50b002d001c951800c0398400781e00240001c1d90081004502803030000d0940701c00c0c00364507000700c0c03c21004801690760101c00b41c0d402c101050700001c143da29080010003030000b0001e8070a44e541b0008007c424041403403c0c15120310b200360 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 127776591 1250 127775341 127775353
    0x150105010306120201022e090507091d070b090102030d06060203130906060903150906021902010e060c0909040c0513090302120306011715061620090a0b010c06020a05040602 76
    0x40001240d041c00302c4000340160007d295040e900d00020290703c1d41d0212174081c20382c030329403002d00c1c1d031040320060034098a1982c403041c01048003121501844116400c04031911006542200d101b0ba507071407260003030002680c070204200c0641c2e4800c00903107050388103802c01400000e6071000b02a40360352007051900c44040d200f80d8003290707540d0140940001c8410994440c5d1070307286161a50800c507a40b20401d001010b40b40c0510030041881c0d4005050210aa241c24013150160380c0006400c6410109505c0401c1c1c1166007081034800003c801d8072040340061319001d80540d0b0741d18112a081e207c6800203507000800c0c1c07458a0034032a03194040c000251003502102d1005a407050310304074600048134401c0c0000c0701c0021001c45e42200d0103003250000024003128a022500380c000403495040703400403400301400d0f031020340203112182e440c00e0000019031010800c60400000894690100107042e21180da44034282000e031648105482c50000740c01210441d112600d15100800d0390f803241c03150200612400c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 127777841 1250 127776591 127776599
    0x4050c01030603112106010303020c121912020c030106060e03161a07021c0821060906010818070902030406141306050a02090d120f0c0b060405090a0203150105010306 73
    0x2480b40000b565000b03404d01c5940000c9100300052080d030702000c103200362803090111002d00310800409000e0746c80b94015040007042c000c2404231010b503d2800103007550140002010300008541c520711080c1e04090710210380100e461080c1d00d005d500505440d01586404000621142d0040030850614012026503d03003440900058000000074042c7d11210080d0300e0344042411103440c0103060140c4050301c0f10074aa00e5000d041c40030041074903015110100000703810301a4090112a01040c1d20f01d00c0310715041400e28202144121f5001400c8605002036840451000500322401525a0350020201c98400b600e820382c040c080d41058404450311410f09600041c607030390b21100f45100f4040d01d40b80c501071405580b20ba01c060800a010b4008150342080700c036106403110200120594005d8002e80801c80c0100002071898100d001d00504104000351101c0020301610345264125104072000315842c1c841035486401c00c8800100290315111f80001c51102451300040d481c100da82c26241004403644c1c1d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 127779091 1250 127777841 127777847
    0x708070f080612070b19140403030e1306080a06020d0501060c0b0c071104020307020a030207080303060a032004090f03020105060114030109051305010c1110060311060d11030f04050c01 81
    0x402450350010400c504001465800e2040303520039855a0307001119450b66949208141d15408000508007003162500a5500340f82c004215401c040a4481c41b68a41465520010202d403091640c16101c0e161300e449102031222503070001c0028001d02019198218002d1501400035030120402c02c2199042c20000a0300354002c8030620909034120252402c9542e50084070703086644511812540fa40200340c401607030303803200c2c8050751040d085900201031150303007428045d14008143d032011032030354030800400020b611418045070032650f000e00c61030340900390503216030090418050320a4006103003e8000b01801141d20040903003d0103900208101e8485500446000d1461515001d082100700010006140c15510290380302480c02c000c0204100c40b80c3e5000d0a482402ca80140050030009084682d504248150301e4a003041c034008101ca240303940c1e0b55003101010300c1c0e119842040c0120b09114000010780002640c520542542d5a4919040c42c0d209049801610243c480d071103442998112540 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 127780341 1250 127779091 127779107
    0x3040c0f0830041710090c080114010b0906090607050604060519060501081915062003180f01140309011b020115030605070e040e0c04150b1905041706070807 69
    0x400c105468030f41403440c80310100030210701e10744040c42442c66901e01c00c0740e54807030a8101c901c1041d034000c1f2189403084940c2900d2040034401c0061014a004110807092082100c4280e44103507203c83e02c6d8541000054060300502c500500b02d40140b000f003204002c1c45620141c801c40d040e96003080940e192030710b61400c8464034000c8502007841d802c04180c0400c048901c0340c40d610304c03003203000c2000b80707078a04102010380c807a920450100700307a203024200c0b44609003088090144002c00860401901481c0f0748580c08148003024010b5094984008140c1d11500b1810741b040940794056540307081203185075000385000148510b00c0011158405941c47c4103015104500481d2403090640606513182c8100400000c2c00d072800b4040340c0e0b050300019484e5802903804400c007050140c0030104ca0744003440261045010f00e0400d4845900e028407041e035028090b10805d404180c00b80384031700242c54007911a032103035400c0071030701071500d02c034403980d0303800001c0d1140c8544095075400649440312039094407800 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 127781591 1250 127780341 127780423
    0xb0309190f030e060f0d2f030c0c01060806040302030403050c01090b0d0c0e03010903080402040507090305030f0c0307081206010909110a05031e0f0919030509040203040c0f08 77
    0x70198010302091245001034030074075000704014035101d150f240e9500950700003111008070030b8032400445070298072850182e003041000c8200c044a80781c0d03440080c500b0301c0000e051444419010440700c401140940c0a40f02030118101200c03082d04003428081c0d5650010b200845191160a043e011903501c1211003608440204040604103445500004042c1c03000103429020003010130712181d600c0e5001d01038040c4841c02600c03002034506003401400207440004000c0344c103001c80c10900b080000d0001080310740341c40c5003001b8541c840304046040c50840c410403901600022022035501c06820915841500595090702c64000305a41e40d905d000a441513520304003e151003d0050704142c6000350000c540c05456002d006001d688005021078907000d0581d510580c0c4544901000304111041000d110580300034200d40c0401c0e0f1803581c0041c43c0f882044141c0d0700807600440072a04124034404048060000504c84103800d80e1546c24040e610000500d0f0030f070b040304580e45180300c5010440341d099014 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 127782841 1250 127781591 127781603
    0x81005070f121a0303041e0b070819090f0314060a090c0501050906130806180f0601030f1103060103050f01060f0f0501050703120e01060314030a020607180905010b030919 75
    0x1001c984042c01c0040149003c1d4110701800f900f645900d03560f0a00061001d422902c5400000d43d209052060205085400a00d050f0380100710101c0801c1f00384081d5140750980015550040c101c0603c222101d030320030303481054022090003022040112560030b04441d0803030700040300e800e959002048015650810000350a107031f8000e0052220794441c80c010803e001024210500c1d1a0003c0d030220b50000480d489680304e40c00007400d10210741449100c103a8207400401c01003500c00c2525035496142c10040c44000c090146c101b2459081116a02034060341d004001c050302d0a035070303480c1401900c86042c800f0200035540380500125240a1807515002540c58601e02d450b400c0381020019500e03a1700040e410f40501034020b01d10500055140517016a00d0b5907c1d0021403d42d00d149400c0103214100741d200c0c00340b60014440034110541c0014070540c010340e5403810b10034507208041c40046a02d9a0740019814034208000810654480c40c019400f90091208a07030307061b20801d40c2e038803402031012070007040 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 127784091 1250 127782841 127782857
    0x4030503040b0906060a03120512090a030e0105070819030e01050f01080106060c0302100c020313090204053d120e0604150501030c1502101b030501050402130308180a081005070f 78
    0x8580c0b190001014043d239810103600d400100a0349007220036088856100550101c4641010545c0c8140304840e085000e09080341080b91903070741c1c1030081c0074181404510381481003082030950710a801281280002000030030030b038142440d0000c2e44040c03d0050109079070800000040491086068000854256002d003000d088071003104400360201a080b50114813041c091050000b03803140001c030081455900051b0380b1403030a428003003024003c00c1010ba40710000e4640c09840c045c00e2000344410b201c1440340a48102c2c840b05c0550300c00d2118a5000c84452030169100c482e00e40000d00e140c01a405104825008240751036414182d9000340801041c041c0301040400108180512111141d330f051300541c0c0950740f411201c1000c40740c010440f01d92002c51080000303449070f007502c01c0501404c002d503000d40c40d05000000b154454410340c80000e010a4000560b01d5041064200001d000d4000915601c5030315522842d2554844007010549403d030300d0030002c40c000b01e01030107001840c10b0450b00c0300c0705 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 127785341 1250 127784091 127784093
    0x70f0c02010c0507050907051c0c0509011101090b0a0212010503010c0f1b0b0c180301090b01050d020a0305010f1e0501030b13050a1a0a06120b0408031305010504030503040b0906060a03 81
    0x803040e941c40b10440b07480c03103280800b003842c2d03607024159441451141d0f1050b0f00d4400c2d40c0600d603000f22040307032916007440c40d040c0503400580d40282120b4603000c00307007400e03015000c20001407401403c896801404d1402c003082400b252034010b40041c548002d01e0a0182090307601c880c00c043c2220103542040e8085089258120400c5010f09009894250f021700e40c0405c2c022191038451a0341e0040311054025040000d49008079450740c2d00d03502064500740c000b00071306035040ea50408e4101b018003901c1d20822500c007001d030855491980420145500a00074800c03030700c2c0d440802d0050100c1c0a540c0500b038841c4042075901204070700c11541260380103c50100030f500c900814600915a0707920030f5805025110746c0d0300100e50280c4e9500310710400b004d0400f00925204000c03804440d52a000f1200510510540002044142d0030f00d135000303034104101980e80d0719000101803405000d4000105a5402c15040006164122010794850b5000d1080f140c50381d5034001038103440d900116041544960312100c240 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 127786591 1250 127785341 127785347
    0xf1d06011205040318140d031101020c030c0105091510030b07120212010510050a0e09060301060f0906030605012403090501020d0e1e071a0705070b070614070f0c0201 73
    0x64110006042020140024032450401d80720100d80130350114424200103205101d070071800741d00070308101d900442c99010710340004000d4a0140409002c118006800c802d0200d000e60441d07210701c05640c00c483e0748540340c0b0026800303801c00b02c411a0050044c0250907200486500d0000c0c800c0204802c0d10307149a0031551814505a0040d205008022034504203103d000b0082c4000c0c05006803118000d02c140d8505003c0040d101e945180302420000140648440302d03410082620580c0785c2141d032221a89d5601e004a801015a54130000610a09040009415940d40e2055080e640a00c00500c8503a8840c145001004208100c8030303c04404440d08840d0203220768884410030f80701d880054903115102040300c2c19141d0351504504550458041040050849a01c091300841c2c0d48010b460381504c1c0a1102e40281400c2241121010000600004208040c403416016040c02c889044c0c03211440d003407106c0200745d40740c22003400340940700200c0d40281c043d816151030709940340d030b96a441509540c011 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 127787841 1250 127786591 127786649
    0xa030620030103050d080a1e0203040b010b0c07030b04080d02030c1b0705060409051b0309030a020c0f150a020a050115090b01021203180a080c010e1b0f040c050d0c12060f 75
    0x1d0241f02d5940c03a03544000c000082c886e046d00100c0f560002d6124141410b15043e800d9040e44009a6034204020b0803005040205040c01140c0e0170490500d150780e961304058009115900b02482c0301407000040102040780b000182940702912140c0b410404010b58159940320740c503000d020f51205007804208800045e03500b14650040105101e58051842e815541d003627600190791108080d04045840c1e40d41943c100103030303040060202c48108842800d140452238100c031180d0b0007010402c0c00155031848a00030440004d030313070381e100e002000320040d4801c0c500e1340b026050261041e11814420041312035840040d00000320381c2e0b05d43c419803841d160340c40c0c0105441018030700d410581c000d12001c140400d0080024200030740200001043d08510200300718200941d0a0b0760300300e041c00c4c404500c5483c0e00c0311582c40141c4881940c1c0010100761440741a02d10740581035041c3c0d081d9090021400416030301ca4840c0c142c140e00b280060055035191504005508464090500c8845d038403061300c59900072000314 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 127789091 1250 127787841 127787851
    0x10219020714090a050a090f0804060e010c120f1b06050103020f06030412080621060117070b0304080901052713060b03131b0306151a090118050a030620030103050d08 73
    0x2d03170b40407c1d03520b11100c0100c00b1001c0e40e4a10004c00d0411159030402d5440415603403d10f4000c40b004100c1d034400c100d40407502e10741801c12001001c5195014050740e05140c100c00140381d4084020300314a081005400240000c038028926001000d0381402d02c1f100b600d005940c04100b4000002020104a543c4e44005140c0c41d401044215030106150088041414501110000d090158101180841c000308060400441f0354490b0100300301c888081002e6a070030640c80703400d0950341d40c14100100c41c40d0040182028176061400d090280c0740032440d14a10100009990744810945101074460446450b44207903003201c40f0410004100d20700240844c1c000d40e00c10400c0c1d07030001c460513001a61906041e04110380d800c0d43c41035094100307014102c00d0401404541d00324240c0b42c5044052520a005911002d030511007412286014084000b07940009081e000c0c1080c15815540d0074980081e14410304448800740c2e080310003140d0320096204683c1030b030313400100500d400301980504440c07240000300 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 127790341 1250 127789091 127789111
    0x90d0c111201020c071202150a050403060501060f030f180809271506070804170705040c170105031c050a020f120909161d030f010219020714090a05 65
    0x180c0040399900c030040c0c006800c1c007400040e1038507076a000709854209150440d0900c1c0c0040368000d0016036490b440b140c55003a21400458a0341d050702400d50740e5028680000f48018100b40000c00c0705a031024088040c0795580d80c00380542100003690008860007585130308100c40c0c1e51901c0c200840e0018005040c41e01014000303941e48084072560086441c84410620301c414100b000340a006103aa8010148030441152a14a80000e1b941e459409118900c07402d5450790070080d15002c0c00c2406d2000000508024000384025019201e00802218540c003264003500034000010426040014030762207041c540c80703e41801454644010b482c550480d5410f9000c501c50404280d9a1030381c24030262002202c9030b002c040d11071005004100400400402904010305070740302940704154422000d49010844220803444c0c00c602130701207810041e10350303e43c080c2c070740c0000b40c5002e241052400c0340b18006816429103084030303100d10781c0700310359500c91a0640d03210031050081145038242d03500a68000403005 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 127791591 1250 127790341 127790363
    0x60e0f0604080601050109080724020f0a03020c01091205030d0504080c0111040603060e06090105040c360e040b04060c0e031f0c020304031509020d1e0614090d0c 71
    0xd00e403540190480c10380d07604003000401079540c04c03071401006059901c020704009801c041014840300386151041c8942c0c03103510240c0510b0784c028089078128901050035100004800e0038040d50314102c04000c5400690a1000061a844031301d07035a2104540c0f0801440c5820345480586018100c003030001d5440b10f00c10460310300d59031800d1142c0d12025808140c1075480714509400541220313280d0b03101060024002081120b02e40e1004a85419510100c40c0042d40f1200d640049501514020701c10004410f4901c0c2c0790b110b031013141024040f17011f1200300d00c0c0c205910b50340d02140c60041070303c0040004000d40c0c040750002c0c0083d00066442e10342885c00c00d079020b0002c4001f91400c0100c0e88000d0b18230282001801c03042201f4014000b104c0024001986402e155543c0ca03054a4060104034010381d070b540081804568488010014050300141000364a9090b4030600605580d0281c048452038a02414900211084a48184a9034086c00179010004e03c00000396880c04030202c0483e0896444 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 127792841 1250 127791591 127791619
    0x80304080c0a031205130209130302030d020f180301060305060f04050c130207021206010602031e0d0915060f180509151017072d050a03081207090b04060e 68
    0x20041c0c1682c06000b6614495140480ba110713a0484101401d40801201000100c001588a50020a42042c80c0788108811040c10341001c9003140180b0141d0b800460001420b0302160400e540030304035840a03840126416030050003010708840c2d040c4002450760308181e002031070034400440c1c0c690b4414055410780d1004503010001030f42c64084500e088042c0f40d804a03804e429428415080c1c00c603141480d00400d40d41d41010f07406581c070b0040d00d450111500d00341c43c2d450f41010308001540c40008941e035003400240340302e24200012030604040f9001c81807800f00005144100412039200b1140440702c4001c1940d1621002c03405880002c242c104c80703110310341c0344c2c01c40344110040c1580304066140359240480c0c103100c284d100310090540d040c4002e0340005010b000b03240c0800e1424105940d224001075222b20751545102d0907040c10390060790300080d610710000c18454080024024090100301000c1d50741e6800c0c1e026030b0130803064090419020301c240414410b55000e00c000c141c030071a0041c0800310381c03030038 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 127794091 1250 127792841 127792843
    0x60c080c060f1f03021f05090909070602060a0b060a030f090c030602090a090b15030907031a010f051c08091302040f0510020d050a080705120a05060f061204080304080c 74
    0x10566420140100760420069078828070340f1900110201d0240031154903145400203050a0b1340c46003007032004070140440000d07640c090f80844100041c042c10383c41a40c81d14000c0b084d2030724080d01c6220050700901c2d000466220043c412440c2c3d00c0300080c40c1600f403100850045004003850034203886440daa600c0c908001c80d40c0242c0c880e00462044401582c0d44442c002880003900c01540078440a5061035408600ca036070b04002c89000b401c804201c9a1a80d03940400360b890300300c4175440036001d40340b02c819182e540180d0014481c10ba910544001e500ea994510906c840f18030304d005940108002c07000301c003001468040c0280803036400240041a46080f0000400c00c9a000354080c88112400032030070440740c106551500364078000e42c0003810b492200c503003003e4003034800c1c04461410005c9903800200640d000340151072201784580344040301c03031400c0c01100e001030000351401c0c0e201342440694529207141040480b0345680740060700201070f858980c1c17001c0d61504054000c494034007041c0840c11b48184 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 127795341 1250 127794091 127794103
    0x1060c15230a06060507020a030602030a0204030f030503060a060c020607021e0301020d0209030c0105120a1e14090f070f0b0309031908040309050603011a09030c0306160905030604030207060c080c 86
    0x11504070741d501c241c00e00e030190314120351582c2c0c048818090180040009a655024240200d0f40c00c8040960750b542c4200e400c000a10481c0c0000f82080200c1d008003062503800300c003561148806440c450112503e41005a03030001d05928000c0d4421000c10060005080c19440c280c00c00c400404190718001e1158002070983e00254207c10f20300b507011440c0c46035841d040100b20384613282800d099144c901c0c1001c400e038400c1d6000340100d051a407181a14880719803000c03004580400014000c028980c50066080101401074a0843c0c07544142c0d40076100341000031640e42d046501200c50041a203261040f1070025400003400c0310a03c2c08144001c40788030f43c1e010460010340f03505a44054a40ca820300d800381c2219015046030380140d40a0006001484001071454206200b5514445c0c640490030b001a281c984e580e104640c06001d030707809001019500800503609180b880c2ca0b50440c1c40c3c3c48a05050742c540c0120340207030043e4400401040524011400300141c907024001e040d140142205c0a2442c1c40 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 127796591 1250 127795341 127795391
    0x6050a06021510060206061005160b01140a2706030c060809060a0504050c06030606071407052803060504081b21130303030f090606030602071a01060c15 67
    0x281000141d460b0600e40500d541c1d40c40b4500000c0fa106040c1016402955818000c1c003007030003039150401280a050127502503a0307091907000410703019000e00f894050341e003090030b1158002c8501034580f0b64041d46020100c400a13121131050591038801402c0310503107000c0e00c04103000c000350342d04c03480407010546484c03030702c4080c0145854903c0d1600781401c2c01072620400901c5100e030f091400c4140000600c02045100c090402118025100e84400b000900ca5101c1d48200910481003034003a100c0480002c2545011100112800180c0401040f0904000784030f18280d903190340c50342d01040c0001921b0750300c02c2e84c0150084414600303140c2e9003903149403100702e4400d40021030352012008150041400c58808100c4005614107800d12085441461415520b400010b00b815240d895407902042c060340706035807064003c2403d00c82c541d81c80c2400c400a511108040d1400d0038114201180c01e10041d03408e82c122a82c968404c00c1142e40754403052034440041080f002220b84a800d104080048114410202c03 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 127797841 1250 127796591 127796593
    0x1e0103050d0f0c03050a030c03140a0c02010e01060303050301090509070b0a05070b011a0304150b0d030e030d050c060109050a0212011511010e0712051204150305060402090a0311030106050a0602 85
    0x11100c8140d01500d90316048800400f005660803801c40082d43c008142c500c0e4000d1030030042103004100300f09a002d802e414041e0490a5030303900420004150a40111466240a40081000c8204102030600f80d508500028011604c00c000420422886602440c0c0c01026041603400041c0c645000d0742d4030358040d40314000080c13030115101003401480c0c0701003401028541030b031000f83e041c00300d003291160000609c043c1100144040303418110150f6003020588407401000040940c51501d00641305240d00c014141c042d102c0c40c4440e80c80540288102d81019030010001d02d0b141c3e1908081d64040c21b0010305010b070141d028001090801c85040c24035000c0d020160541180c01e2042c20014131a040080014540341c1c101007000b044440041458030941e00302d9460180e0325400340c10a640b40160400b80600003050004000680c20256031030600d00c06031940d020302103038541404000c260301840046980c40704204a0401c00264010803044044001500100d400360b980c100085a8580d240d11034005 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 127799091 1250 127797841 127797853
    0xf0504030c15050103150207060e0d03060801060509090c10030204052110090b070e12030a020c0102060c040e2404060303120b1905060f0409020301060519050306030c01081e010305 79
    0x1046810b14081d480741030801c000708010f41c51912120708051701c610110010550024010003442407980002d203944c084c6004540d00031403031010007402010541301d00e40c4a94a01540481c1e5031810700348043c040c2c02040024840001402e0400007031384c004444420926a08000000b41074036018103100c050034402c40c040c00303021030800c21036040c41d2808101c50300d020702d406482c00c009501c2410841e00303c4044e00d803100403081e038400441c08032072401d41c1c0c0c0700d241d2001091080c052a800501c1d42000c4500780c0c2a2190364031003c2d000700250060380a4148290000c42c001001d102c0040344103440b900c2c2c04066080c1c42e00841c0049011201d06400680014003c0b1102c01540f000764054501c1c141000d880140b40788814110742806a1154000d50b0300c510310000d0401680c0c105042500c024200c5201c9c11580d0b542c0d03482000e041a03000110510b85540720b800c3c400480c0340180b003928071803000503014044e803850507401124001c80c018058514031401c01002c4402c0d80c100500030b03000e54441c4c801859 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 127800341 1250 127799091 127799093
    0x603020d0f09030c080c0c031605190f0b1c0e0106090b0f060304110d02031c090e0405030d110408010f02030612030405010c0b04050a21031508120d0f0504030c 70
    0x1003980e5441100010490620b0109000240d002141606554004444503100c0c01000419801d01c40900021689032064400415000c0c8461410308116501255041c0d102d00c1c01e2410700543d094944200000000c140302c0070050070711010028402282444210240040d9071a6507504031000752358061591303036440500307019602943c440c0b11407a0701c01303c031068010780b0103000040d2688030091004018441c841040b01203a145c8101c19003803070b9401010b5402500e500f00e1900350008401405000080f100030000449030300e0a42b029024076046009185030854000700200500084403407081810010080052810740a21442401418030940913075241401d600300b00c01c0f2000071600004070b400c00c110410880c1e80101402c90416031001890890340c4d07481c1400c0c0d060505401e0081e001c8075500d0611000c01c5000c1c03074012540c400c0c640b0200314180b0f504002d005400d460f4020400954000101240c0b40124400640308420344064046034207020420f0b01001d5840566049002c03a00c1588218 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 127801591 1250 127800341 127800367
    0xa0209041a090102040b1c0b0402040e070e09060906010e030a0c081005010801020c07030209070c150506090708010509010501050d09050d030e0d140403060e0102131412010b030c04022101060302 85
    0x5070300411142d0013541490300f000740030511071040c0001c41c0c200080c0100c058160034003d4001031000b000c028011900c8940d21b4078101800c9000310740303600001310b8808444801c0d140a11a840c003136071020380b000f502980c0711001502d180c0040b402090f8944103428028000076002c02852000d003182c070014214000e60598508113441041c0c001010a074018001c0d00421100043c2c480c041f00d40490300b22a90b502c4404080d2090024400c0c060942554000d482e04030408a410031406020291070410f00b90359070140480e171001c07003030162650060040004010941c49100038110003600c15100041c900300d26074842d8074001195610001103900d913010f0303500345101406400303c09080c2d0f00340201030003240560015203100300e000c01031106589411424054400754195444004400302c4551000d40300e04800101507102036200f4841c00390003040b07501d80e00341800341d4004c048014004241c1168100304020194000142d400111410000300011052000c039072076001380100d850040c0c0e500b00c090741c41 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 127802841 1250 127801591 127801643
    0x80f1c15141008060d0f0c051c0510110d020c0601080c0907090603110d020304030206010e01150c120e0a170d030507021902040608070b0910021f0e0a020904 69
    0x10740c08014100c00410401d4441d510000c0d240c540324035040c42c06544500c0040c01203012020081e10400b039414541c000c00030800c5809003900c900f15006280c9c0c0d1546406814488034214008000350042d07a0700103071400c0b86820401d941034150b01018240f00c1e02c010ba00040b60464102c01d203069104000401079140240548164504161401c065902d410200945001d0a9100300d40c00c0541d0b078441c42c01c2c1c1550b448250345003001000c60030365582c182400c1c001d41d500c4081c000c4c54108060348000288008603003a0300702d58441952165961880030340c4403850540718481010701400f03206d200c01c0d00d06584d4511840041c02c14a400314545000c94060ba41c6000404042041071500d494244121075400280b24115203010300600d8054800c5480450040c2c400d03540403981034490503401107030021581c0e018bc510100d040d2014490445582000caa07503102d0080d50302c070300c40216006141e0b004482d4003c041d070600d06000300c40004000d40e01059021500f1101550307071503844009483c4810602c404 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 127804091 1250 127802841 127802849
    0x6060501030b0604140105070b250e0a060503040c090c08090606011803020f0d0b0106020102071401060f03330b09061801060f02100c0504180507050304080f1c15 71
    0x70800140200e0008260540b10707a02510b0800b200034512808140c1c0309808450055034840c102d06e00e130742841000c0070040410041d0704a19131106114250b0703901e104a001c984401e800500800506142001c140c0b01548081d0046d21408404400415040c06038004c0c19101485076442030080e03e00f844001e8188800500410304000340da402001580d5040e0000c101501e030102c03070300d1601c003026a001940107075400760000c1007003074640000500b40ba01903004c1c00c4120300800c0f201b03c1404940151354200c41c4a4041c1c2101c0020684080c00800e01d021080c0060a00380d10451540c08880400e02502c1218400b212410039180c030118030071820f02d150090340020041d1800c0e056568000144610008140515401c20098400b5000307424420082c2e110130032450340040062842c030400c000c191b540507024103080c1120040c800c1c1d09071129849024416039480d600e00c0e04685039640c4622040e80220b40060480209100442c1c404a5024000c8001d24078280d002031821a081980303180c0704d6107680 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 127805341 1250 127804091 127804097
    0x507180501030b07140d05040c060e0619030504080c030d05070915020c130209151e0f180402070b1003050c0301060b0d05100e040c0303092c040221060406060501 71
    0x41001500c101d00458011307409081c40b1506280035540e045a83c054280b000e2107032401c103010701050066203007a0209aa08660303038110078402e0401030001521819a046100c40c101070136105209200743c1c0800e40007881000501e140c100400c00d001e185401008003141d0056544041c00300440e04004a00300400c039600d4204114401f110002c0e441d01c0410b140d0900610140204174800805da034110b0741e0101c1c0c010000840075610890790300b0356070090080314181c0c0340110b41950000326680140c5170365a80b0032084c107152007110309000262840e90300c4ca090b0043d80900406000030f0318058440d12403004a0070808031640b9606080d86001e0b001c080700e070300a901d048418840c2c140401d04441400107030040214894850b0790311920144002e5102c0002e181c00c090501040050245007601100d00a60756501c481d83c482a80c5a1072044c1c52110707903882c40c408014444070500049150380e005000030014540721601c00d40159540c9207481407040d940c0c01050803c020480c00d0700c5998040c210070b103 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 127806591 1250 127805341 127805351
    0x408150702010b010c0b07140d0e0307060b0f09040318090e030307020d0e060f090d020d0b0916060807081e010f0503060901060311060322030305160c020603190b0409050718 76
    0x46c4071a002c1d0540900701c202045101070a20b01c40f111140222007001c03007910300402420013015252600d03030b00300c50000c80f0345c94202302e05608079280543c0c2c91030960300f0050640075a500c032980d003a01d8184440d03089140d45880b0400004100301548100c003036080400025580c0c03880c02c00c10081c140300070b80200301d0601c01e4000002001d82c9440040e02c41c1030302a50300c19940c680390b61000580c650040c100095000c195480950304005143d403c0c58020212002120320105030720018098203100b40c0a41000200d80200191106100b030071019048806101c0b42502c0c20b1000d4031180c5200c0003604054031925004804220741c2c1020003545510040100081100714119502c1380c500d0110083c8151141e400480810001118007075000c104036115440c0d414079641614001e40900401c98800c0800000000741d00d20042c0a010001e22282d40102818555034a0041100e5051030b91400c44e4581995281c1c080c0f03080d203451141c204907500130030050408510308000102c2c4001e184a441140c1070800d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 127807841 1250 127806591 127806593
    0x3040609050f150114010302070510270b04030806041410050117131202071e0510050909061c0b0906090f03040605090607030e061309060801140109090203030408150702010b010c 78
    0x50103620341550885081c0100c202014070049000c0e02800c9c80251482c043c0051030f0501d5105580400c00700d54001e4180307541c1c03a00d801d4a0343c030329110505010b81840c00110000e00040d01c50000c0d40da201000030030000f180c640009018644c00b900b21071500700300e100008203008035a0000001e401c80c141d280412401450405490420910314000092801088600114407640207100c044040c014681840c46268280e402ca4101c441c041d201e84c901035100e20078241c12552040c4121008400068021001c649a240c00d110b205c00710a00c140b00345002407404a000034221000241c001c101002c01061180ae16510742c07401e00004044100b003662040000700106a04070080e251001c6003121140d0f143e59403420107031a54102c803508558070810002d1004001020341440c0320071b0b95240302c0c04200300354540b941242255903c0c0114001c2c219258010071280180e42c000007800c038400f8003902d0a140d520b1074524600b460190301100080000303010040e0941c3c5c244101f0b03201e48001d2a103440c40c2112 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 127809091 1250 127807841 127807873
    0x30806040b0d020d02061b0a02040b0a0302030c012003070b0a0605040b09070503070201020f0301091a0102010605130f020403021207091112040b0a1b020106050f0d050304181103040609050f 83
    0x10b1500700a0241c4c1104221009540d244815901c038030b07842595800c3c03c0841d070607045440301c180a0342284070314544201c50f44182448828401503d9000e4018959031a03c00010344015a20a5901c00c00d8000c003004840e618206002601c14540300c2c000722a41405d280d10031809907685908002c1c06240351a501d22426500c00c03440a0708040181032031507485c4c44502080b80640704d13402c464000c41e039001000081c56140d0390700a00c10119483c0d02e035032000c80440012400c1c1c0d0024419254032070351140200c003056a40341d01044044103401d10040c0fa06a4a6000c00c1c48a52074030003500e056002004d0400c00c41c15103000303281060400182d4507103040c00c0e815100450b0400900043e000e21551400140180d40d00d5011500d085003840006045c0c2e00c41c100e00038060001070082078016069035071644894141000c11004d81a449009507050904113524845184003012510a46c19120721405008100010055000714010040421146080c1c1040d9141c6000150103090381d500010059a0b5201 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 127810341 1250 127809091 127809109
    0x203012105071a0405040e21072906030d021b040f0209090103060b030f010605010c03030203130b010f060e03070f06050901020a0f051c05070c030204240b09010f020304030305040b13080316030806040b 88
    0x5028040c5682741e140c030781411b00401ca003c3c0340c1d0400b03d6000c142100320020704d00501500c154800c4048680c00f584568007203031501003100400c21814a001e48041041c81c15410503c3d0004170f000e401410608c11200003580c41c8000ea02c2900c086559105420039810140100390070410408028040342d45032030002401400603480123001c140d808008581e1204030107003841fa41540124510100d540c65400f0420481703018811a0702143c41d07205099468100865220300320b9080c0d20380603020500d00541a01e15901065a1030b0440c0904c0da007800025100d80ca0040120340a00c0003444100c85c03441c600c0c00d0316070f800700c08076041c0041488800002080c485100042d2541903c0100d110200e00c0000ba5502c1e14000c0c1e104183c103a05807000c90f109800c0ca0103041145426a03481c000a5901002a62030740f1a600004e000202e08110901020410400a29628608003ca805101d6032041d030300e4110b80100c2501c3e030581c002701500300103040e80044035542254088608200c01c1d2041e0000540980c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 127811591 1250 127810341 127810393
    0x70303150e0c09120a11010f03060602031b070b0304120f0305040f0f172106010c0c030b070e040f0b0a05061303020f1801060801080f010203012105071a0405040e 71
    0x42c8001120700403600c510140203900494241180c040042d54982084001d4400c02c440b4000341a042c500d4003440d1003030042c0002c451454004c1c5180c0101c0003c1c084808a581858044a100e030b6400020240c04500043d84100c0c010102084000d601d00c000900300c03102070314054105800d250903c00461861150301005540c410f400c000340c2c0145103400b039900c404016041f020030304017046404840080711076214041e98884101c0103150350728401951011610340f0007034403a0064032401c2c8005602007500c03e811403c0740c1040350030040700c440050240c9041e81201c4030895162091014942000584175014110465030507003800b07013403911821000482d100c0684107004e441d41000194860010581100032185154451903844007000303000c941081c0f160701000e210b07000500344014070600c00e9a05868607840628070346c0790750450220828062243c04d940a00800340c0020760106502c2070700803480f40d03801c101e0740c5540c038003400c10003111200c841c00c00301e0360002e6a02e0040742d01c840700941c42c12 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 127812841 1250 127811591 127811611
    0x1b0509010c03090509070e0a0b030411091302030d030207030f020106140607030302120c04030c170c0f0609040e0105180102070822170714031629030c070303150e 71
    0xc14102101d081c000c1380d002d2504489034030180304007150300c0000000c00c0841540c2480002e544c6183c0c2c5170007440b040b1409030885010418008079858410380c982d4000300850101c1100301c0c5e580d00081c0c1000c4281c1881000b095000a80c00201508800c10125902050008001c8285043c820040007100d0703130601c0d4031441002401780308243c080d0341503c064035010341d0700e00501d240c60000f4020a60082c00300755282e042c00040021881120103001e0100040030025183c00300c880e0087c04907802c00d000c400c6503c03400922103d4116225442046411214100003251300d04101070008608550284084510b0b4010040400450404011942c524040e00a280110142ca00c20010401c2c003030342007805000840d28480310001c40024600050307440e580780050b0781d100304804041e52102c0305105000482c82c3d0b02c80400080c0080340c40c81c0b4503850750f986c0c80f01c0d801c0c3c0b446000e070f0140c2d4001c0741c4842c003034480401c900701411f43c544600d02c1e01400921092841c1760800310024131009004204a00c0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 127814091 1250 127812841 127812857
    0x3010b0307030e0a021012020c0118020909120702060a05040305010e010c08070c08031b090a0303050310050f0d030e0103020c030406020105090706080408040b030a1503200f010504120f170d1b050901 87
    0x3412490340d04490589c070601000704000356200d4071507c085490f02c0c0c0140e10651030400032602c0701d480855007104128002d4840707840c011050b4244203054211880a0003031250510000011034401e020f0030b580d200c10100000362440100001800d28500641031600300540301c501200092007101c1243e0300194181051075045003120719201b0b00303100700c81e24290006114500041016001400386003d6045081d4000400b501d0700c00703128511010b000f81c01c3d800552042c0110200e0b0181d030b014107200070b041c9005441d02c0040b0107080e14540c000c0c2d2100005039903500030091100c40c2402032a01801c1d075807030080558100360f2034554031130182d8010300819210020201e151800e1a5102204480c650185411029030342c0c2400c00c0c04080b1044501402402d10692008514040c3c8d100290008141c45040c01e03d800c0c0340c020141556500d2045589404000c9164041650022a0302e50b82c0004ca0036281d64901842c44441555000e00307001c003050406002400065802a043d140a1242840c081c01 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 127815341 1250 127814091 127814117
    0xc0a030e1912080105010804020607030302131a040303030b03010c17070e0a0303080106020d030e10021804020d020717040602070b0c031e03060a08060f06040e0f0303010b0307030e0a0210 82
    0x1c01e004110503004482405084003100b003050000c2100e024503880e0321100c00744c1e0380c0d600043d513000da0700301d50003580590100140d00000740241c0c00b03031001e84080e210800f100c80c1c460341030301769075601107103000301e0074030007041c200201541030040341011141a0000d10500d402e0322805840007208600405440d0002170000e030300c1d00d1203500c0360480540d005111541c003d64904000d082510280100d400500a05013401e0030a4064002d0f541c0012540b0010003824000015000c001d42100c6003208500c0503824000c0010f03542c1c0c0c00540f0b404d80c40076100603a503100c145042c00f80203801ca038101c0207800c41408104000d036000304d02081100c1c101c00300c00390350b01c0908110500758400c0c140c5800621300e200b01d000e6070920b82000a544507001c00d9828100c255180d284480d5203003001c448840140042c10000b80f964102078110707400f8181c180c0100d4100d0003121038814110b801c242c00440d09020084100080c55a1501407401d000181c18083d0001d25a581c020604100c850500402400503801c0c3e030302 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 127816591 1250 127815341 127815343
    0x60316020a050102120f0708070c3201020c0105071d2b030c171c0e16230a0501120e070512101104060207090905030403020a1206140c0a030e 62
    0x6190540c428021903450300c91405c40070711402c0c19180d149034416081d001450381ca01070480540142c01d0340d203d009040c030540d03440c1e14142d20701c2c0f81c00c03096803005a00c120300030a04e000303c0e00c040e10b0300000015880d0b81c41110000e0855000600410030010f6014901c15051070703030b07110007003802015507000c3c5e101034640c0012000818104001c0301ca254000e0f000c070040c140d1108615a6403440b86d0b00f01040c0000d91104541e407400b801e1880329189a0f865400320349180543d1143c0c0c800303172440f0300b510006002190009140c8220b60701c6190750a5030162038020503003141c0011204083e0031641008104d09050008041100c0140418079a544da10b0725084005400c0025500400f0000c1000d941c0312100b4000540f21405182480600c50900782808000141c1c441580c0c260b49559005112440c90705602d80c0141c2108442520303180001c020110140e114099003001a0484a4419640300da481c0780a03006c460506440c50442940a41404468032003402140c000176042d14005c43d082c2810004a = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 127817841 1250 127816591 127816603
    0x180c06080a02090616150b0109051207030f031101050c07030e06070309170a02010806120c01080c0f0f0403110a0506090103410901060303020604030309060209030d050408070501090506031602 84
    0x8503400712010031702085800c18072022040185c403504000114098010311b0030155407403c00709501141c1600024003003401c06c0307860104a18414001c50b0304640c4e032500d0b240b091071010001500010b0801c020340710074070001d000b001c1d08030500c0c0030000c1c90a49243c500400004104500e644183c90001c3c010050500c5011604042c0c1651a010701601128003c5c040d522005060201e01080214000404914019030300400c01030016010349003100c0f80304c004650354600184400c492a40501031400c01d02080d03006040c5403401d0300c0c0f0b0181d40b581182130a022009900780301b90300c01c03001e07810288800d480b20f8040c0ca410f02e40078200481c0b081040051045200c50340c4100040e041d1014100c45c0c8441d04440000c0d00c021000b40400740c0d50388401441500ba1151408042c0c0507070f000002040020b80b180e446901c02034001d17103005050001c0c00300005d003000541800d03103002450102e8240710410051044200424003401e20340100c6141002148541c000100039041c10a00d030507074400064002c2c086 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 127819091 1250 127817841 127817857
    0x605011e0819090c0b13050103110d090f2906040e0c060c03091509010915090e0402010c0506130201111b0f040605130905120a02030d0b120a0c0801180c06080a02 71
    0x1191316025181e03004c1e13041c6900030001d800c000d454429800101303540282b03c0d14100103524260700d0300d1320145800a1000d0062a0422281340301d5a0709004089103c80c1002c0b000b0400c9003481484011540c01003000c80c00e0f018004e14407c905c0c00801d2070f109840001c100a643c04180e501c151146240c0c4801400c50240d5400300380c1140b01c410f03003444101d810500510a020003600c44058150f02c070351601c101e026000d400440070071500c5800b442212410071030300e540284140350005485c0348a645203410502c2c00d40c1c41c104100b1900a03104119a0030a901d10f07802c8401c80d00408510101004c140140150300100328049c46488841006c1030f00c840e00600c01814000d00b900c81c0cbc050b0000710003402056a15070658039401180403491300a40e0080407546041050740c000c605041d1503600c1e500040020b041400c3d403042d1b80b20940c4801280a0103101021402044080366017072401389540d003034404801c03217800d02d903c614040e1030010781c80c040c4404c190366061400c0c00d2140c0d24000150020305c6640c2c4 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 127820341 1250 127819091 127819103
    0x20c040608071a120f10051002010219020c0d02091b0309060403031b080a0506120d11010e060618090708160315060e0c070606050d060605011e081909 66
    0x1804900050000b41c8982140c0321040103000e2420502803952803401514081142180d07504082200715002c26159900002d0f10140803c01070303510b01c0082c1c0c07001321400c20107003d80d40106140190220501c0d80020395201c5002801344c5201e480d000403507140c2d81e8003009201d05586008100e0a00020383c03160610070030202c04aa0b04d080c0448201c1c1c1c0d6000032502280080d0600031801071001401e000e510354992507407225034440e10b6051700a40030300707402440b080d0084a01d03481404034000c20412600c0c86981512074607040e484855505003554030304900041b0b503038450014005580c0b5001a51448041216601c1c40303035031103ca001d0703424665258000c0e1034500c1046624958190040c0c0f412040324440c02c010308541d00c01c49507413020b035079451152440010b582800198000000720062100c03520403100041c01580703820029001c44081c00050b07440541c0c808013804a942c0140c0034a014525069034505400724001c001844880010044050070401c0c58510700a903d90350844404658084 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 127821591 1250 127820341 127820351
    0x40603080922050a050f0c0a1b02030102090307030803011a031009091b03230d200a0606141914040216080c0604060c0c02030a0803060105120c03040201020c011e0f020c04 75
    0x38a4030003a040a4503040341541031b10380820424100c1004072803110166880d1602c00c0c0103152070a200700509828180e0f0555000c0001540355030b414080500a1071080320303001c6d03c07541001c24041b000e00b500000722607001d00410074008841c402c07644d540100d4000c0740001c40c2029081c40c043c1121500200d8070380c000441d4400100c200324050260001000030654540c0c000c841c404000c0d0750300c1141e4182d01c404500484842400e0000c401450402081240c0450f80700364065510241284d950741c0c03280403900d450540705490741c9021074404400d813151020003582c0a050415a855030201080380c0b511443e40003c40c0c036890080702602c4000b9a410000c000d0b111b84c07034407007042d869900131101160458501082141d41074003c041d041e81550700500100008003880e0343c0c01c1c41d140c1c0040c3c080c505001c801c2c4001703849a05e0310360403541f050700f80c1c1c0e126640343d05080c4006450000c1104206040c00140e0708608003544c50003d00119540d114900b1959010002100ba0b0400c200074017120f0f0814101 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 127822841 1250 127821591 127821601
    0x1e0e060c0601150e1e03030c10060f06030204060504210b0703021803013819030b0604050c0d0b0a03081306020f0a050a08131d07080604060308092205 66
    0x2190081c12502858180016100f4440701156900031010350164000c0308032544645030000c036000900743d940c020301106d260a94442da2030307140c09200740300000d4154450340188006c4090b4024078004085600f025401c0c14100440a005c0307000303a020750356207030711190141c502c0f2660b503540030420243c1222002d211428050001070280d40851000045404c100c54070304001d040501c2071001400c10500c0b103140c18040e0341c05007490000c4890340c00c0e03c1070403c0981e1220f00d130340d00700034400200800d072500c401e07007455443d142d805608014000c0e80308524080400000340b84007022225003e07048240001c1c1403000d81d00285421155400140181d00046a0f6081040408200d01c00303507071a6400b110604803400000a9903104076041c0281140c00002c103060010b003859000e003202103010340b031041c00180c070785a9440220308071002c0701c03400380427960602c1044d40d007140c411070f0800b105940510506007191240d41070f9120380000e1034010011800740c000000a10703070000742d0034982c0f444e0a101600704 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 127824091 1250 127822841 127822843
    0x30f0703270303020705060901030209042a030c080403050a03020705060106230f07080c0a08280206101523030108010b010c0c09110408010c0206090f030403031e0e060c 74
    0x1c010010805104407251025104201030504045030b502d40d006108460500c810310405400c048112411706409001050040d42c40d8010303007000303032541f4140c41602c40850092502075001303583c031101803525140b100c281c001c0e800003040d0740c030503018204541c1d0f6601f2418100d000380701d047c40180ca01d000d001c0002c5645507110100a10300650b80c0320050042e1055068000c441c46600038002003002c0400c411300009850b0000361001d24107035030a864280b103207078856200503440401201c1940580302281c1108140b403800c1e0311405c04642c8003c201c146400d003c0c2280e800c0c260b00501840901100710443d0082c850b401202030703014555000b01e22000c5c03030200c160f105c0d0000c0c007480005502b0200c034070000b54800c1c03a48070a820340102c929031005280814100c000d12075043e4441c0221010072001c40c4002e024029001c005110703600034101490100845820001041110201f0741c01c108020404a64072240e2107002c144000408844106a4541a5548200c500c00c0542107607010498004640e0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 127825341 1250 127824091 127824107
    0x1101021201081e03040317040b040902070203240f0a0b060c100f02030402130c0309140c04060807150e0a15020d0201050a05130305072f03120408030406050c030f0703 73
    0x81d2000c45a03d0b000d0503059101000320410810120381c014801000031452411460500c0444039090038545034555904215a41c172541110350321603000240384046040c10003981c0001d4010644035080010910a01c040688014081d16120045038001c911042941e030700121841000600311507691261030b0303046031210f4000c1c0c48040b041c0e10700b207003007aa91656402201e1056034010145408424410001801041c2104448082540c0c43c002d01c070000f40c00c041903006a0070154002e08041c8848401c00040c0d07041904008415007000c0d05c2004640c446204e1550380002904210000e50751202c00319100c0032131944088880201d0a41e00302c0c4194000c2032410b07003050b0326070091140d82d0300c182480c41610b5040d100c030300c1184600c0c4d81140219203e100500300c01407082d051036840c0c0410401d04014404101548179900400000707024486c074040213040d90801a491005050a19041086480c1c3c0118807a00c0f083c081c0014412211050074421601e10100f2075883c1601c81046007001044e0380 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 127826591 1250 127825341 127825349
    0x3090b0c01060f14030f063601022b09020915040b0a090501080d0806130504150906060501020706020a23030409020f0426060a27050a03080c0310050d02011101021201 73
    0x3010b030f8410303405007001c0455804d114000c0c00c02d0300c3c454501c65000c00c804100281c0c5864508282120030880b6255003800181801c000c02c204a04966051501d12f0048103526058482d65600d00600c94006885102c201d940c00b0404c03c0360b40c1c01c0c080e41d10000c10702414400011941c0701c03a1614020820010661120b8140c45c1010700b12621502270b070000307481da00030941c2c4480d8030861030020301101c80030f01d41081e544284108501031030034001502c0c030401d1302c412040403a0b2803502c038a070034001540d040003c0b000401943c03000300710000c1261038201c800403000e031240034414500051003120404c1081140c00406d401c110842d81e401e0b41c241c802919410500491041025224004003241440350260342c50300300b1341e0003400042d01c9072014013000745a6042c00fa880c00582c030b0107201780d0009254696003041d001d800501880c1c2e2641ca0001d0901c0401002d0341074051082c401d00c5120360030f0030031038801e50320305940e440841c0505000580d511800900e6001496000040b000101d00003401030387d04075 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 127827841 1250 127826591 127826593
    0x90619030b030a0b06090c0d0c1106070c020619050403020303030c1314031e0f01020a0206010e0109020403170901020a06020412020f0a06050d0510090c051804050403090b0c01060f1403 81
    0x1445407030201034442e100b00b84040c0136070a0940c00b10700d040c076125280c070740c001c01c000d03801901e40080c078407035042524204180c4501140035481c00f121000c03000e0104960020340c910b03015501224a0740040c0c001d00500d101c04000d003c4500c0c0c440486806002198041c5400400301c0b605e03450404a0f50305a540003000e803000c800d5804a0008076201c0d0700d0080f40221030028003034040b485480500305d807684c0403480c245185109405000803502c4003803004015503c095130240c000382d070410040354014501a404501120f104210810100c0c007001c0c0641c0d81c11011210180d40c594000c40101e10700700364082c014090f14400200015405c042c0f02541301103520a442a400c007440708000c1100c00780c0039100c0c51000c210100520405090759074801d90303114040b60f02403104292209244800c480c507100940c000700d0b42c0002c000d586030302c001c184050849001c803030078040c519051742d008140184c1442030510014004c1240b240c1e00000b034001c81d010300b40c01401d00c0035081c3d8400410071080e140891071802 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 127829091 1250 127827841 127827851
    0xb0423031e0d0314040b0405011104060504061d0102030703080c09130504020907020c0f101101020a03020301170d05070b0402061908180f0c06030408070b1005040b030c1003020c0309061903 83
    0x281d18040d00a0303204400310034030760544e10390701c6840344600000024421034555580e01ca40c0c1e1203003075618000d040582500d580341e81c1c03504c3c2803482c00745c041c07001d25401024803540c1a12109850ba4000200ea200790741c103242c840f401d0748892011400d50b0003010541c0d54058258402c0c0c581190031540700380c0c4124002c854420b45615483c005985400440103110f4100b01d98651100490030000c00d804001c0c202441c2111190240d11003181c2240c0000c011140040e40020041108100680c100c248101646001d0300c140c00a4640262480c0b0410000408440000c0b00046c01d65407050160781c510500003080c2500020f01d01c100030002d5008070341e4013070403001d01d070902c400d402800181a80111400002403c0500c840000c0000b1500b000304220340380c5008100c54000580500f041500800b84070b00705854007801c040c00c00003a5440610141c1c000d5000103442c50741562140d54035280c0c20014200183c0e1520812040c60461081d4600340781c0080d00001d60441491511281c44c1e640b403402c0e581048 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 127830341 1250 127829091 127829113
    0x20d06050603040c0b0c03160b1b030903120a1e05010f0f08060112140f06090723010f02030412030206150d0206250f050a0b0705040b0423031e 63
    0x8102c1c08140c4010345000092041800071301000c00c01401d1407501001102d041c4000050b81000e000845102107401d007481000788100e10880b17682505040b810001010b09500c0d0000c0610f5580c01400300d0030070840300d500049001ea60043c0d00400340042c4600000345c15070900340400c0003400083c81307118110100104001828600650480280c42c008006010164a070080e00001c0d2502d090064604d04001003c588288504002e043e2140c0802000b0713002d20301c1d059403a03e0809800760b02040c1c030940e00c181240c2c0b01403213408180c10892400d003408401c5040d142c100f01d1071030065400c40128007030030111394028143c000940d13a100d00915120f00e9441c0d0101e030280542d1700d505480081d08010180143d000010140c24004450340345407110004800c541d48a0345132407a1240d4054405400017409501800321101d1140e501c03203000e04045290a10b80508040070307124601c14080c03580364a82e40700d07100521114003c1c906d028000c0480b05900c9062071941d00b10198401c00c803011f40f04402402c5 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 127831591 1250 127830341 127830349
    0x50f010b22051215150319021c0c15020309010806040c110618240610030e03120603063306070501020d0b0109061d0f0f0a03030509010909140c07150f020d0605 70
    0x80101000740c06455031960705000c900c29813207c0c400490384601c544091440d102611041c3c1041540514000c09440c0d160100e100c070145440d20000c0704641082100384e003142d0b002040d1507046001a600001d00d800340c0c1d83c003115070814811544129000741c009000501503110004008641c4000503100342d0029416240c92604448441d04050700c8168002502890420b20719501000d043c10042440c00c11101740c54215440903010844250b903130310a0141c01d0408001e155400700d004c10105032501d1340d00c4610400c82d2072a201104028001d040f803a09261218010340341200d6018009540702c06102e610217001d01806100c1900041c011140000d406104003100618660041c030a003c01200100602c003030080307410100e503082444543d0b022216122a000d88009501a5407036a4032641150001070240e40d6590050324000d0824040641c48034480035400d0b0800142c14070560307036100500c2c0810f0b168a04400c1c0c0026a0314001c10b0400501294000780350b16515a0010017546440d40c00f04 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 127832841 1250 127831591 127831621
    0x4060e03030c06010605250b0a0c051204060507180e0103020102060907031101030f11030405060103210e10030b030f0606031501060e011409030102040303090306050f010b22051215 79
    0x55074003940f11800400c0307102e0040006080c03001074114076034500c1d441219584103a0748000c40c1110040ca64070100305900c080b910514040d100340b45002450045160b0410121400c080c00c040d03c0c4942d5040800c0c2607c1c021110940c18516000c2c580e4038041c2c0e900c0705d803095001c0c240b0050b8054000d020001d200c0d00e002044c5007060369030140400c0d80a00ca50801100242507803180441c0055840081c0368041c403001c0c01452103079104034014076581d810352508072112140c0f44d44220014182070403041c0400d4000000c0c0045410503219002d4440081c0400ca015060225000e60140100034280c0c2c2441408500c642c4a004180d0484500400081c581c070000070003407148038000b030401c1040781c100e58800c0c8904d032904050280348904201c1c65a001070308990050f84102c010602c00382013001000810301910f80e1040700c100350202d00b5890151729400764406c140910300103080320743c07000b402c100c0030429020182402034090708019120604c0c244d40da241040000701450201d50008466035140606 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 127834091 1250 127832841 127832857
    0x102010f0e0f0d0e0a03120c150b011107050109090f0605120f12040e280f092006030c07060906050a051e33030604030f09090501050609120a05060c04060e0303 70
    0x160709161b0b1668442c0d607194412400000100001d0380009400700d0410861090f4418441d030001483c010040000340c240012002c2c640016000f9010400442c0e801c44056021a40c1d410310102d194000c81e1603e00040015820042e0300c00316814041c9405a8005500c11030200c81d0f40840740c000e440c18000d021b5a0140307202d8608406483c100044514001694982841d4002d02440b1004803459800e88181c403180c01940540c55520101402804255644c1054032510844a800791802d900c001ca60385100060981000e0b0100246610410008d94860800c490f04980e041255040031800314015003010365540400541c00c103100c15181014404140c0144042c0a5010058203490030642e44101d1000c104501741d40e0380205424152030501060380318510031782d0385020100b0075510140540569170007d02809103880010f110707503100c03e011510511011500031007851190920746291000f0070b04014545d001e404140003450f0403010282c002d50324035860b620b5651585c041410703543d0145c40750f = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 127835341 1250 127834091 127834099
    0x1e0301080712050a0b07030c02120708030609040c120c05040b04020a0903110604031a01060f0908070308070c0306090b06030c061c02031005030601080607021507020a030e0102010f0e0f0d0e 83
    0x403040000c2400442d418485610540650f0007035000c0c1c1c2c403800c81c0d40c10101c40100200e0345840b0224202c07541401202401464181b07102e040c401207444040c2c0c0e5000c01048140280c603a4030200d403d024440e04510014405070b15069a509841c0c508a02c0000d4075205041c062810302c44a003203140381c00d000b59a20728503d9500c00220f40e155460340c0385d43e00a54600b4540000c0100004404260b00c1d02c030960807240340240e02005541750000085c412916a0f03000c1c0300f04201c40200780300c01000460420210b0303822005c80ca444150034282440030415035800200000c3c038005680b01000a00000503100d400214150f507200385c0d0500a000c0142b00740000320050703903201c0043c00c030300040030340c050f43e0080d2151440038020ba40384c00100e4a060402e0b00080c1c0d950b402401001111981000b41c649802c440002c56405402e044101950310919010000e090010024404406902c00d500814040c04031804c1030000c3c0d0300408003a6124010400080518082d1500d4104402d02031550504000000743c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 127836591 1250 127835341 127835353
    0x82203050a030305040311073f0f020423180d09061101020c0303071806020d05040510020c100c0209091b060a03020706050a020c160302061902010609060b1e030108 72
    0xd50304800420001740128140440030b09040c4840b017041150304050161000f02c414032080c1c0e02026540c0040c940b180d115003504142e2081c040e00c001441040805501010749452000c161000402074200e400303509074840300344c440c1d03a0506400303400c00c28095140b1101d112800071503245180e4035a107016080d1340101d154075804109480c8950004103000c4602400103080c0b400c000710440c1980d0003078400800180459180d4182e040903105018000c041e03d00050000c0d914149001d02135005910920344502d05010030389501313074001d0007804244d102c001e2000050702c03913044019101507140c8400741d00400c0758074001050b1303a01c0000c5003c110002d4081d0740300d00640201c10010158000c0b42c46008144e001d014100014241d0f005090103421161005a02e80b0858902c482c9080c006080b5034124a0801c0020800758a0b4130341152407502d200780e004190040084c2c42a0b0150505500030079400f403401400052010006001c1c0080072810311031002210154060701c0d046000c28059114030790010 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 127837841 1250 127836591 127836593
    0x3060b0a0f030e0307060203041403091c030e12060a290d0c0305010c17060108040b0f1003020303030901020703030b0306090c10030f1e06080d0203090415080a082203050a 75
    0x30700030910500d1200d2070040f030244608041c03d4250f400044007120b0141c0c020091004020002c80d003494544414801542401c0340d007800205504080d000c110900c40007101190245886429445a81c000c041c10707021004038925075059079094205c42c162407061418800511112480741440c0340c1344020030349215131589440401108101109007110071600501c2d0000000d4001e0042c009080d640d41c03076640c1d0103001401903608615000300781c02e04003ca000b0401c030000b95211161038200010400b4080e00356140e00ca800018000e507000130398180b001004102c40313400305400915040f4400e55082c41104c69140605917140360603142c1ca00d407600701c42c40141c8a41000141c090041440703280c0410b90101c00b404580c1110b111007074484140300c000f1011020580c180c015000181030700c40003020314030f04c242d000079241d0107035145080c400c82e11901c00701b0200c140c030b901040c00b4040000551313503200c20a1904042071380c40780e40d43d40365010000004550800e40b480301e0070101d9400c6006800c0c0c1c0035803 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 127839091 1250 127837841 127837847
    0x91a011d06070c1e0e0103030203030a0e071214010b0d02090c0c0102040f03110405100605120c040305030a020312060d0201080411040f0609060302090f06030705060706291003060b0a 80
    0x612900c16400200521400b030102d142c1c400c01d1002000e03a1100f03000249010026449282565080203503014803040040000a600104a03507200180749000036038cc522800c1640c0c10460580d0010b00d950030383c01300240c00d01400e9040300c100030760640b000700311520510701803094030803030081d0295203c0c89403000a25080300040003031103600b180c03000051030700da140c4000490500c05500242d0303448558840064150400d40300d0160009080000754921600d84031004165120380070700b01c903042c0c1e82c030320106d09942283c0c816540034507030100540e512550507200083d80d0b130b008842a0b031004026040400c0d41401c01186458400f50180e540000b10fa540b070310340c0601c1c1041c403841c00790040e41e11028002501c90a11840340640304c070304404a03080c0d1450041040112011300b08807080c0102c9402d1094130381e0002080002c90741e041d240c80352030791600c0c18034078014851a01c0005109540b00c007610310b0a141c80079102c0012100b2514000810107800040702180d115005030030144100f00001d020b5140 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 127840341 1250 127839091 127839137
    0xd030b100509091317030901050a06140105090402040302030d030b0907140a110a050610080d050310050111030f0f03041e0302070603110d0f06140303160f02010e100801091a01 77
    0x711402900c0c2e403405131681c0310f4148216016242450500100034001c541c5001e00503103401c003103618001d01034242010540100340740348807900c5051042c0002c1703d070001c2d1901e80603a801145c0080680358088407981c40a0080c10804080e5032091552500041c0781a0041030341030710a00b421141c083c2094207000c07003903402650b800c01c0f1303440760700c6840702c14400604100b110921919100002030078091900b8040e500d0f0102d90004801888000d104020184001303e03400801ca41092a101400e25086013045046d44101d0968500502d0000b4000b4071141a840007580518030034110b01410031030000c004072008414602c01001a008160200034151081d001011401c03068080d0784e14103001080c085007214065443c0c0444641c441808010714000c402c034420446200354091850304040210b66210f0f0a640040101502803171440e0313405592050060031402c0308050310302d440c4160501006004540c0034071034041c02c40e0610708070101d9542d114040c2d110000c81a150b01c00040603008440b81b5082d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 127841591 1250 127840341 127840351
    0x10b0708070203100f05070201090228050603160f09030305030a09110d0c03050706050307120e0a020d1110050c280c030b0f06011416050703060e0d030b10050909 71
    0x80c00600094000d0f0b03801340040b032003494008070002500480d9468140a440c0700400b4203003964544112900540c541000340c010341005e00d040445480c1500e01c411020384150b030820341d0001004001c014041d000300e214440340d0220703030b191034000e4800038004980da070820740001030000d40144040b840c40302254211400307140c4541d035440400c4034004041100051428016101080029001c03c2440400d10000300608510314085103103142260014003014a042695481c40350b4400c2c41a10f000c1e018041c049506074010714a000c5d0680e14280380c850401c03409a11841005c412111100d40d90158040b14041842400580080002101c0350810001034110540d008113184851500240e81c4c541b0600c044c61054914100c241420039140100480042801b41801000004a11080c1d03102c82500d01464108640706600030301071030401e0a052041c0d0005080d1400c0c0725500c006400c0c046003d0f401441c1c10b58007003082600c0d810800c80341080706918607020400410501c00309050000c20745901c0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 127842841 1250 127841591 127841603
    0x91507020f031212010b090108040b070903080a0309050f210715060305010e150702030304022b03020609010c032a090e0f010e07020a0201021c091e031118010b07 71
    0x159031140c0842d09110034081c83ca00e440100241e941510000c140d40c1d580904000403419003004c860200281000d40050000f6060140070800906914070543e010b401469006a801e42c64401d1060090040c0040c103200b15801e0050040d61001148000f5840c044d12150228840140108000400c485d600500c0f040d42c0702c80c400710a01c1c1c3c10194900442008501c9400002220b100b640b101c9428005009044810004114148150f941d40003080d213070800e80484040100d80040d00302103e084e688810231038092030359050010305054000c00e01c0d522452410b0002d0000c1c7c2c070800c00071400c4400801902094541d6180804901503c0c1400142032001908041007041c0d143c1403d0364510004030380200d160285540140501f040c0014450340220280c002040c10351000e07400070b0b44440000900030000110040e49241c0240714104441c020901041440c510010310701c101d0303140802e030340403d49041d80300c0c60040080c0c2c103049924104044100d11440075030303402e150110b001d03540928002d44403 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 127844091 1250 127842841 127842859
    0x50c070902040b04030c0e15041d010c0306080d0507020607140109020a0801020705070611030a110c0a0306090c05060c0d050a0306030b070804060f0510050609041805030d060b09150702 81
    0x55540c49100400c0a419007401c030b2504c0b1482c5103004c011065140d0014a10000190305128020300c83c18010312140e03100320340c00300d8108c0541a0704682c2211894a204003513082c01240c002550701036003e101640d00080c240c40340e81c071001c54140d4040c4904400250007507420800328010904011103400d2140303400002203070318100341d00000c200c0b6440e50880000c9950004504e07081220410900340100303250300f441c9000400e40b103861a240d01900e400c1c2d10602c1000300014004400610845208290003010030340c006440b41007070802061010320032155078142d44008603031031408000380c66814628000803e1320454454085640c1e801881c078003820f00d0745446003c0001914486042c1c40b400c080e5552000c00e14240c1071500540f80001400e44000745080c00744805281801004020b031074050703c14542c1d440003080440c0050400d040c40407000030f02610b081c800c0200110051010000401c410f005040d207558400c4114481d805185a0000444100c90b1804140c00d001c0c00c1d106000a0142c80 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 127845341 1250 127844091 127844099
    0x4050a0203070b0c0709050411010309112101050a0b06030106210603030509010e0a03020303250f03091a030105090105130e0106060203040512070b090d02130f020a03050a0c020607050c07 82
    0x12030b20716103400003240d00a020441e65065541000450003c04402005002c2c03403c15803260040002c80c401c0103410184c071200006e06211001c0d4910343c1c0314601810070038140c644001e129584111aa01204041d42024045007034801a405018041100100b48519591900d003086d18540791400700035040c140c400051901e5170005205d081d00441c044d13101c00f903668444000060010300b40c041e00034401d8103182801d0000d03031000029242421840202120742407003410044101d220b0300f41700107016842c920380b000d041692000e040c0c4102c505d080c45148030700311505107541c0180804d0007a1904a840c02004000031705c1e0920301280ba90a04030400a11400b01000b41400d50308250005401b581c000070381001581003001c2d00303410018080010f052160304044c050f00d01c600c5000c0c0c500d07100d0700c43c41c81c0c050159a602d082e140c01c942041842004a0f8030300d42003000180d004140036001117460240018140031850240284210031035003e40401c1e990b4801c1075540b600030032502d1115102e034400c041 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 127846591 1250 127845341 127845343
    0x2090112050403030f0507110a031d0a03060902040b0d11010e010e030307060c120212010b03040812010e0118020304020102100f02091c060e010b060d020918010b13060f0e0904050a0203 81
    0x281c001e40c004e50700441c054844641407002e50340040c04140402c80c048036201e0503000046240441142d00d46002c00e80c816540c07020701444131103403e0b42d95000e1107954000041014540c0b2004400748203507000d008014038402040781c40c1c1500c070b101600c00e80c0c024404440c150b2041010400300041410040c00580d401c40100e89036410210040b40d17460340c1c8440031110590070000c0201e0040003003405619010444c142660301e8241072091981c00384012021400f0419100d083d81c0000243c2c400c104915a5a140205100442131048010f001103440b102101010b40307000716441950182c0003810000700d8410741100401910380106000d40d403e00c8203c01c03903035440c40190403540324408440c400c202241014011500300b07c10310740c0d00780e141003441245600c1d0b5400303039904507007640001a1034440c81c8010804110480c000d00202d1800c000000c211078054002600c2c201510700385144001c0c4e01e940f010303290f100400e1881c1000c900c001c0079400d1146002f0103a194014400c0d81a1842113100c0c0e4046 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 127847841 1250 127846591 127846601
    0xc08130b030a0507030b06030c0d090503070812010609080d0509090402150307050d11090d030c050708120d1505061b0708061302100f0806090901021c02040906081b0402090112 77
    0x581682d03038503041444450381e4503000380da42c10003080319158034500749a4442e120724850302da594010303d91500002010720106000740c548080d04001d0065039240b0100c0228500c43c024082d620209651500205422000146018404480d92a0540340440540070411041401807007240d0100d1081d100292444d00d01018501501c080c0e15080d48a24000b1841400d4540f0607442000100e400d001d414066942c80750000d05541e010b050100105409041c200d0a00b155078012418910440c0d01c00342103124128000d20000c0318022040141e44140d04000204c4400b604c20a680700700c040c801000551691220740c5c050001500c00c4074070060f610235450741866812102070845104400c1204c05504260030349240081441c68411174040b044103024000e2200500301e0350180010000083d4550400d40c104ca155100c5030410306a50700000070080060360007401010021801c00c1000207041400041028045c0d13010032811004007250380c01d110094009a10350307030412421a0111041c01140e01c01d03 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 127849091 1250 127847841 127847851
    0xe1e0301020d09110102070603090206070209130c030b010e340903050604050601052701030b191406130c050d020a030605060d0b0f0105040303020606090709050a06120e010c0c08130b03 81
    0x1c0c41d021100413002900b03150007503120905050034107030700d000169540d07012100103e50407a10642c168032103038113003031030b40f034000d40f0040044006540100901554240c0c841c100c600c40541d2420650310004210300100d0007004151400b0304940150b031801806001007408140c1c40d1602036481944c07a02ca240c5400d8040d6001d84254210070014481410076a441c5034803c004000f4407030109407032140401b00340805100103012505900041508031002a078842003002c0d414100b40a80302140340295407142082d01c2013440f0324200c1101c01080c400c0c90103030314000d80311a00c0302400c0038a13800c6028040e40c4086122001c00d551000003103401d0b0f07141c1029100c4506010000944201036074140031003814850000b03814000c0a110070800a030380012019800309050302c00c3c424980301c0d11019a503884440d00890392105400381c001c148682e10030b20072980c00081d11010300440281c813034070501326100000300c0c1c00080c142000a802181c080002005051400100078001e1542c6000c1803d06800076a0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 127850341 1250 127849091 127849103
    0x305150301021b010f090203070618050d0614160e0f060714070810021306030209040f021605061003110607030203130303120b010201050705180d0b070806100e1e0301020d09 76
    0x200003c00344030382280b44003400e1080002410039000685e07100928829041040901c24165078203150300307071b64000100b001a0001611900340e19014001c3e10362118000100d89404001540308011400428101c4800340c59581d9850315140501c81500c07810b60803c1c0c2c02200400c003050018800c10000d500010f00360740076081107414890458101107510304042003440c010f100c10302d000c026000030401180d0150400581d034503240e50100b005002d4403281001840e2005c02c02400707a074060401c0c0c00d5081d100300207407403482d5a503456003507122546003c00740900402038081d200e9030a10900914403280240122070401c290b09581c02541d80c015002100044c0b040e6048117000e22240c0a582e00b14802400248040d14101c50700070921b005140451040011500d280811620b901c5481c1403203e4000280c1e00300c515084d03c01416201c1d041daa8035009070008888070031114030600310881c0c0d414004094400b2010303070380070315a25103c138500d440d6030555082140c05401d60551049145140c4a09 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 127851591 1250 127850341 127850377
    0x2a0d0207050325050f1507030209191404150b03011203090915030c0603050906070f030e12030103050706050f091009050d0606060806011b1b1d090c010f0f030515030102 74
    0x11801c68107000480700342181990080c0064145618041181b59112403540380c01078231141c02c4000203010514003440c041c999940e022000c281824440300350081128241d50034888200d0781e51102c000c01c03020384a4449580f40034001440718284101e9401d060340d02a243c0780200311385402c4d40c00102c600455501a449039900c3d810000c000080e210300009006a044c100407510b0011012621024020507441c02c02c500401c5c2c60030290b010b07600c01d210012509003129060450014401041c0d030080c04203644500c54410009030300fa00c52030032036000c00726140103241441002024043c8bc2400e042c00c0074240f000440700841c45484410324039440034064500422030030318050b40540040005400c1504003ca05c4c0d02001c158041b031042e00f520a64070400710a4403211f440300c0821080d03407a4116581c2d409403103503540c0503280c5c4910501d0051881001740c0d0000c80041005680080c42d030b43e24540070502c0c3e035550b128010b019a102e81c1d80400d64040700803402c850200040e003243e0200a070983c50312405 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 127852841 1250 127851591 127851593
    0x1b07050103110a0206061003150602010e19120509040209061206040b0a15081e0403020706030f0203010f03140c092403071a0a090510082a0d0207050325 67
    0x1809840b803028208141c003403909400300002501e61000418041c041c01c841400b100e68240302c0d900804181d551500785440043d00c1e044d00030b0203030043c801d20607c1c6101d00068203180c1d5003c0e0103d13005c465031042040940b0303d407105050f9501e40007400361503807199003071021004540f1480024800003102c140c4241c01460724800300000c960035003903070a000e89071005090109000e10405540c01c07091505140610750346a58016200400c4160050840f980c44000c6c442015000502201034a80c1628240030022500765142c0c00c80c0424412246281d100100800c0861081c20302c1452002034041501d100000682c045070101e034007643d102d81d01e1060188900802e680131200c03c500404210003401003980381210301500e03441039240310984c03500c2c00240b0810080c090180c074001450042e1100c840d03c5825040644604002c0307482e668001350304480102011240d00091180c01600e5003050705142400160f8402500013540460742c0d440108542000110000641c0108212545400c1c00c1c804075 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 127854091 1250 127852841 127852847
    0x302090316090f05090c0d0c0f0b0403030206091903030915090c1707080c01110f0d0203070b250305070c020a1502250e041505071e110606040f021b070501 68
    0x3c00d6051481c00362500041c04034051000c6584c18480e00b040315495580186c50a1250301d029030340e4000340910742c1c085000180101084090822a03000e5001e03030301d40d03070749480001c2d03210b0342c09254214003011441401d800090007a40507440046c041c402504400401d044420300b2146200c4064401954409080004091000c6048640340201d40030700701c1c051500c01d5071541e418520400718140600103d1008818000300000074010074000300b100d2160014100c00ba489510008050300c4114074400090445d80840c506090f580d1040602c00f0302c0d507080890201c0003013101400071002c029600c0d012601607a54043c254011382009140e813115800300001c00b918000d140042e880b4140d14014080d40c1d0300b02c81050b46811922154008000c2d0396aa1030803e9452148162001c40d0510300000c1c880255441541030301c1c000e0700b50688101c01a02150107030703540ba081f41c00c5207075140c0c020800600e55090030307005030549100920000d420442035131100d0340904003084a40c1d04030750203194100441d6074 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 127855341 1250 127854091 127854101
    0x6030c08030a020705122107030206010918060c03060f0308120a0b06070f0c03080d0e010e06132402210a0204030c0308030402030a12020115050405070f0f030209031609 74
    0x3040c4001c52a1110350700010751521464401e95110f4000450b0074600b058051103000707620381d8407989000500038845500030460304642c7c7c040d0014802e0b440040707001039240c0700c0c03207003c0e003114070010854565075030f101d0000e4a400c007001010142c07105030001d062a40b000c08900558800c3cdc400710b44a000c001c0d0182c00e0341e80c1c018580c281d0241080b0703804580d6120482204d80207604600c103186003001900300749120000c640d1008000c030350000380010310341c40183c0c4030130b116940f210000e2003000e0444520030303030b5014283c46200c0d045034034410150024504864030310190401c150391100a00344110f03044200d822011202c1c1000545580d803118001e5a00e0b03001f588410440b504500301411a1205898003c4900008104543c0000440e056640c00c011005a250703010003007040403554184003d004c1d000f22681c500d400462400c0204140c0741034080c5074800c0482d0f45c0d030702c0100c8a80c00310460b41c2264074007140c0c0500d54204004030303058506100b4000c262000424290405191030200c0045034 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 127856591 1250 127855341 127855349
    0xa120b100e0606070507050604090b0405150102060a020a0201060f0803030f0702010606170c0d0f020c100216030e0a0f141e0306040b0601090503060a0f0b0a03050a0b07050c0105090106030c 83
    0x10840c240600c031100040306075641005003501c1c0e090300c4200600c1c11914081d00f42e00003c0d40301001080c0043d04c407002d5009400f80d030b038083e2424040307501da00d284955071032422501d05025030826000520303075546aa0280c09059007620010aa00d5928020940c4080ca0b07500f040c01039030000030402410703007154034017075400212920082008500d0712500811041d01c29000e100c4005540010801d043d6085003540c50064004030104417013108840b2480080d40003140f00b0074580a000b001005000080c8203440c1c00407200030b10030f198413810340e4003143c24165048100c0c0e4848644c020200302c400305909410007034042c1e40000c05201d01180100300f81805a0b040540c0388400e40340505140307484c0030540c55041680103016850540396200142c1d4031000c0b9800003901403040e20200005092503070420142c62200800801c0208410f105210000b030281c00043c1556100d03410050000b41c00707165041e40102035240803420145807180c03003400c0d11800e50303040609a450f80300500500c800c819040c4020 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 127857841 1250 127856591 127856611
    0x30619150314090d3e0c180c0904140c07020a0b09061e1b2d060c031b0a020f07050916030e01150803030406050a02070f140703020a120b 60
    0x161801d8419640e83c0c13000340b02000c0402c0040f481d040600f280701c0c0048036207240c1001d03190304a24500e004c1c9410150716003010750407510817406000705506101060049103255100207504d83c0c2c0d11402a1030f4150b100445e6140c21550717400c020740d209400050755900072464007000f183c0d20440f40c01004132a40b40740d00322000c0c02c40308018004a581c0c1d98003c9a14003011041400540c80014196200710b0041400696a44045a21040c1d000380040307000c040c1d40d807400040c1c40031060580340a9840c1240c1c005400080ea20a02c00f0030303241c1829801440d4001c05030700104c03440310004054403005401400f110300150788803403000c440080041c401503020342401c1d05c00c0000f5107802e10380034100ca00c0e00c400e01014103136608030070b003a5903e0a400c81703101d1110a02e1280310550740c0e428940c1d52036104407029907411346890b001c510078002e24000c84003102c4d000f0b20040d1130040c450322082c1c0b803014091993313021486044800030050b00c0c0d40505000401d211107401c4106202c50500d88840700000b44115a6 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 127859091 1250 127857841 127857881
    0x9120a03120b090622060b0a051308070602150907050402190806030615010f0504030501020708091306062f0607030203150f030618070803030c040f06230306191503 72
    0x451703104c00549402920341105044201101d51903203100800980d009140c00c000002918410340d43c0080003040ca018031110030603a41c1c1e58604002c3c0d200c2d00f150040c2001a0000c115450a0441e10000d007078010700314505440500303071f5480c0050102d92005407503003100d20b0709901004400341c01006469010780f090700600900d1411089110200340c0d01c101207410b001c5040e030100aa24411015507000c0d5034000003c650302c10b1310381401041ea4101d0b0249a1040d990201642e00101e4039018402c00c03030300e05484803459008600040440b0b01303411100c410084240c50386036640906c0400c146c501a04180d1001030342c80c11b00300d060300e1803580780000d110f0041c90640d0032044151000941607a00042e44031100201501542080b030410ba281da01a901a1001009001000d21110020011501c400d100342401656812041c1e80301c0138003540c1074540b109402091401c200011004681c01900100364001140044a031080189041e4011261301103034000d51821aa415105030100c190307850810700c079 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 127860341 1250 127859091 127859101
    0x40c080d0e0111062502070e090f010b0a08060c030a111204050705060403020a090c0201020c06070801080c0a08030a030b01020f01090803150607021c060612080a030c08071409120a03120b09 83
    0x8108540201a900c205d19298007400d8124403c0c0080c0000e07006600d22a401800c00c61107641d9910000c80c08109a9480d0154042e0749142400307000003140c000c000500300c10b07683d2180c40e0312150030003083c7d078400036150200c100c600c5419600034031032440b4034804000a0304043c107049140003201c4d0000d40c02180d0811050015179207960340e9904803014480c02040c404d000e1201240a8003c802d9103c2840c41034105008140d50031021281c16182c5040488194a40040402640c0f410b01d11820303186400070000e42c00098170030b0b007081079503403411300440e1001d51a401d8100d003102c800d20b20640720801c020003804008282d07116401543d42c403c840141c1015682e40000751070300040d0075030003150f20b050780c0100204800c50b08a2001404128180c09c440c5806042c130300c03940e50046840c040040e10300030002076000d009030900c034010007056542c1703e04035030702c0c1d01d800b40d042d03000303000d0715501c0500c84081d47c1c4404010005120f10520135601d264403248807190b401c01342d41c6d0b0650543e00c68424041041 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 127861591 1250 127860341 127860361
    0xa020f040902070203031b0d030c0e1003050714041403211c0e0703060b0127351608070302181e01030809011106010e04030305040c080d0e011106 64
    0x8054450307503400160b85090500c002461403180440a0001e0b12503034280700c42501c404101c0c0d0810449948081c042444002003c4554010440074958008600804010280e20940c000f5034450f4060031700e0356411080b1903481200b5003181e480603102102c010f05941036810140711860482a42c0f08140301d80f0010311171144054051041c0c3d0140c00b489001d0782c054468a1500451000114201900da400f038480c14518083c00c2c03004081ca020a1585100c001c14210072002c04c241780da079020303000000a040c03102c0d144103854003545161054620303201c800342042000402030300d0987c04400410030082442c0010a484503141d10001d6075800c1482d040000da05d540c440c02c00701c113006003140e03070b000e40d42c03031600203015802080f91804204107080044104490714008200c400000d803180c5100b4000c10075040c0d600c0d00d00b4003481500319058404900080c1c02501702e282c101c0d201e000d10002c1982c517880110f28162400c0320a00026503113002d42c0000307581002c004a8170048001c058802841c05069007 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 127862841 1250 127861591 127861597
    0x2011d0321090312060a0b040608100e15090a0f0204090b0a1a030109050c0c0a0b04030801090e03090d0804170c090708060d02010f030e1006090c020f0d08070e090a050f0a020f 77
    0x104290345013030700001d82c0035543c2041c0744010300703c1c080a403500c0d03e40301c00340201030300300c11944c560040c981400b02203110b80000034660700c01d4031403440e0b0080e00309000003440b00d00e02c0003503d10310b103003912900440f02181090010704054150b4810004004050308200007070400b69a210380310761180d1004041c180008002203034151520b401c0c000c201a1149450b1410074418030810345030b2400303a10359410401040b070144a000342d00a40c0c0b04507107640c0340c44c1800202e0b04001d1440426500c00c02c030f280c1040c1003082070b500c81940501100f505061f80c441448100d00030301c0810441c29002440d0000300c52500140e8580c000f81da504d011070b101c2c9040c2020075190240e60101034140400c0c410604400c0744607400850b03004103210252100b0681150009000d040039010301d41c0d15070309261001c0a0300c3d1000032002c101240b600c00804000030040026289020007078046010024400045c003007d4540307043d1030380a0081080300182529041a01426214000c0c0803404143d0040200302ca542c0d4141c0c0603 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 127864091 1250 127862841 127862857
    0x131d0c03060c03310c090b09180a02011809091217040b040f150606020709061505120907030b0106050703020c090603120d0e010e0a120516060504020102011d03210903 73
    0x4442e28440075180801480303060100c018100701740c41c04045032070b0340303da000300301c2441c000d641500c1b05031601c805c0d0382c030406550402d10403640e000c048002c01661240b001641031700c20140504014a45480c0b52106840070554151542d050011442a101d80d001403060715800d403500400c2030608241e43c841405803c040c001808200d100002d031802c0c009660421300a0f80140301082100550312500603480f00014400d9104035031818000041c880c1800c0960a001c2e00581c0d0b0300c41c40d0449903a41c4a41c8000044e00c01d81c0b4030300c078000001c000100c0526001e4040d201390344071740c0c1e1074448900c5e0091a01d80e8945055004904180500031241c9001980e07012208040c841e00e030b21400305c40c3c0610003c00041108013195800e0a120076007411002c91003510b00380c0140320040035414040003e40d13980c03084840009010001418620218503541d0149812070b205100110320320403a03103000342e82d516082004440c01d0308002081020a80c0e0440b0247c81d03070718110140e255038a0450705840d142e000301c2c49 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 127865341 1250 127864091 127864141
    0x70504150f050d051f0f0b0301051c05061512192d0b071715060a1103070b090f0c0f0409050c0303030703021201050915131d0c03060c03 60
    0x781c5109040e0040054074203803214400e04000e6890102003000c148114041c030b2039199a4400404201040701602c03810079201c10514071403551b440d01d01030050f102c00000820b40203140019403540010000c2c411180500421100860020b508608220070748a5840d100e02082d0b01c0701011403a0400c000d141c2180040e00310408081c4c100310300022440101e46c9800e031480451a0210203000c0141c5514100d00803401c0d40d4035605072511210581d400c000b816a0035040c14460b5411660044c0f03009001041c001110303141280640003c042c100d40b858002001c00c4032801004002c0000b015010000c009060000700003c000b24281d01002c54000c1d82c1c0c05003103d0080b40c8a003d40d03018404200a40d02010002804595503441c21110042c000d40101c0c0d5601c19060300f1100000700c900d020300714031b4050100d5129441c0d03006005410812690814000403c074103841b2a00264800c8000400c0d2008140010162a41082c600c00700341c1001c0c1c00801c44402468148180082c030444103041c41b030032480c128 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 127866591 1250 127865341 127865357
    0x2070f030f0e0d0c08120304030207120507030c06030f0b030c1e190b030709050906060a050a170903040501030e03040308030c0717031e060a0b030a0c0509040f0c0807050415 76
    0x101e02100c1070b0648a060641000d200c402900812280c4141c00d4121141a0b003900e01c83e100009a02c40940300984000d00140c7c02200140704440002c0d42010310a0300c100219001196259110200089203038016404a03a0703c0c41c0004484034075020306050f2660440103080108007180004411b02d000184010720744150701c0040003542c172181000302d1010300c1c00702c0962000d03603a90112101988125902000114585000074541c100000c0032800346000619490800348020012503141d00494001010010704c0209030402c2c00c0200c0440d8000c1d8800c2d0043d40d500e50510001401b035410600902c507441d03008110403c08550950141d0f504014095484c81d50790750542031a8a0300624900d40c03812002e07002040c00406c0c222554250765020241410b990559280b0382040409142c5118414002d80104005004a51241d12a81da41d00290802500745144000403e04803610040321841c0580e4a2103070604550300000640c0c0e110301a032608a2900d03042410200044c5024001c44040c090f02c6 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 127867841 1250 127866591 127866617
    0x33093f050901020a0609050106030212010603080702040b0102030d0c120c0504080604060c0c1203020d0b030609061f031704030501110c0d050a05040b031e06040b0a140a0506040e090601060302070f03 87
    0x4d0194141c83d641010080c8012180c60501900801c10b07444101c0c070520034800030080f41a0306000d40c904a9410141403420700203103409020181041095150460008001400403000340c0d2003002c160381c81d80c1c0e1728101d94140e84a4200100da24841e41582031180520081207103180008005500c250300500104032220404002c4d1615010303403500500b2564641c601c0d540d0194158083c10030804468030034841c1081c1c82003415141c0405445000c2c040c0c11010000301110030b0407080e0707c2800180001400c0456a07601d0f010000d4041d03e410400c02c10002038100b040c45405d0049284202e01e00e42000e28104280000d01e80da500e10392021000d110780401c0681c04140118240c8006200c40584556a403520402411140007820f0116281c1c000c1d10001c180113060511414004c5a000742a2016032402d02c2c40124001203544130741d03030b8004400040840c2030784407100548000c091a11610701e50341810100142000f105070484000c140c81400640081841d07100724048103605407d00401c00a26 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 127869091 1250 127867841 127867843
    0x110106210203010e0d110d1407030c0213020f130501080c0304060905010204050603011401020607050f040308031503030a020d0807020c100f0c021f080a05010333093f05090102 77
    0x3130400c000040780128034485080940240a050103d2144e01c00da503204000101c0c10388900d000d00d0b4900400b44010300ca07280000b0301032202140c071580001c1190703c030007c000380348001340d03448141d070f000e056100811350a902c4001300481d81c001c1e020900b0440303100d00d8000c8110495000040001d071005803a8100f400502400b035048038050003024202540c2c2e50784682c08140650b1004034503e006105100010705918480c1c0180e030703514007001103880c0c5028515191040c1941010b04a44441d22021040148983d010402043c4529841e005060f0280300144040e0401c20014902000d54220201301030143d80c0c1c48400001070401420032200d500310ba1001250315048014000350020742d0f100150480c00e501c00d995292000480c0d84101083c1d50380d00120301500c000b0f100c0107100d001e100f007596919100090003400d084800150072a1080d00c1c0c540c61030146c40040e5010340e018100445164000c1340301c00e4000d20b90b0840d203a448101506020f240b03000d0740b03444031241010400b010814442030780c4 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 127870341 1250 127869091 127869101
    0xc080105010506030c0f090904030528090b070201030e0102040608190c0507020616020907120f0b0f06090613030f0c14210a0212100b01020a11011416050106030311010621020301 78
    0x2000780c81123803a0f241500e400f81031b95020303070398480d4201d401072040411825400d40360312000d005940d941c07040314a000743ca000c1c1e617040300008905064803038803a51803420091024000030300c03866880d10701c00d0908030708814960040460b001081ca0800102c5c0031719a402500701e41000e9030641c0c00c4e507a103081100b07038035042507881c8400a41c00712a85c01880103055008000e2134203220324034000c018003c0108a450111110310304181c0d00b02c125460741c942a0b250641c0509841000900514684545c1d4844044d0074140c0d50001c942c119995a40c903010320518400c003401a00c44240207a103200a1040085d08620344071302c0c142440586103014220700030b401e104034040d9035406050458200300540701180c4601c15424001403040c5030034400c64456100060000d102600510340b10402c03140c1704011290543d0403070082100d02005c000101e25050785060b400b44090003400006807050031480c008010005403550040c3d243c0c102003042c01444100c40601600310b45200550f184a149440030901401c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 127871591 1250 127870341 127870357
    0xb0a0c0f02190209280f0b030a050c0402030403020f0703030908120906120603010e0a0308010515040f0e0601021c0e03060c03060f0f04180506010611070303170a0e0610030c080105010506030c0f 85
    0x2d940012107141170341c0c4d03000642c42801550090152240c0942410f60f00c41010501034000c1d485840341c1c42550503d603000b15042800f0784180e4031203080c80da0a180c0341140d154021000100c0d1003408012855041c843c24103a6412001800d250081c4d4000059090007200100510940b0034400f1400c25038003503200c02000e402c603000761210100b02c3d00f4068004002441018050420001da030581704410310100c5040d075541443c0480d0803401c0000c100700c0c000c0000d084a0540c4075003c95451101600701540496012694494600b10f540b0000d1609000d400b80225507409800e01c140203441c0e40e8185940c1042c6030035955102c8400c03da100140c040d12244030110f41803810081e0001c14440d01244035416209a51a03d000320003814044a513500742d070780300240016003400d0340c021500030440240b036000311440c400030501c0e119056032941000d030107a4001255a0296404104101c2417424400041c00e84000800c02580b40c400815040d1000a2200c0181c40e00020302e1441c1e25410000d4910300 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 127872841 1250 127871591 127871641
    0x9050f191509020d0b030a2301140a020301320d0809190e0f0c030f07021005070201020a0f022404030c0c1811030403090303050c01090b0a0c0f02190209 67
    0x2e507a100c454009600a4030041c1c0070f039080c0f00450f40d00741000100c07032103c150f202c0c03078603644c010543d01822080f040307229004285548981c10801c00040c51130f4018090100b00d140140e89516204181149022a0420145070380c030444035030250071482081c7c5604204152644c14012600385020303122807064010b2640e2204001481800b5044e0f10021001921500d050400c45900c03414041c03040707560103c401c6070701c85508000003280403540920f601d800c800c081c0100c8400004008030001520011940c003001030394041050401f03a50702c02ca41c004c01348101c1c000b0304114026a03010407182102c603840d0000720880c55020800b018840c4070000b50701703030304121160000e0751140b880010031155902c0d5103010605141003044115540c60031280225030603103844401c2c1d803031a68251076a8010a40030003a03550303600d010402103042884c5562064294103000686201e007a00064450504150000c04551003125084403114040901022442d01240e60307801c6070355108001c03200c696070820b12080c1 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 127874091 1250 127872841 127872881
    0x61c090606050123070f03030603020d060506190812030c0705100203010608070314061e1c120201051e040c120506040c090b150f040f08030c0709050f19 67
    0x340290340d8840810b442c026a41c1c2290480d1421601d00441d40c2542540e000040402901c0005155110b21003e03880c03203800c003c00c00036601d800003038140001d124113a440d02d07180c408000c41c0c1d1a203c2400c80c2066604490380280d681803100c01e0b6a10011030031500d0401400001207503ca131001c005a8132040d07030010850700d1244d000c0140344041d400a2043e00007050070b140105041500a00807102c010840c60442101544c1c0c0c1d904200b0021003841d412a46032810a0384e403082ea4a0341d080030381c001c01100e44c40d0b03070b024102442c1034110340440705d8140d82164581001e0000813101d040100700e01c501400b84100356900c1d9030900050b51400d640c4a1138110744030030160010090301151180c841c500480081e40381d0750740d40440b10f054408040110b940141e000400310040d1048038042c1110000c1640c10714140340d101d2400071720308245030b00108040e50000c03520030390800040058001516400400f4001c900f4980b02d4400340410140c036126006491400c48800e40384107520079100c0d02d50420b1403400d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 127875341 1250 127874091 127874093
    0x20f0d0c06120c0e2d040509030a02120723161d130201080a0213170312071107050607021206010e070f02010509061305031c05060901090c0905061c09 66
    0x90b444246114000b4241499402146503010b4252406a0100074052405402182c00c082a0700103d01c058010410144000944c99890724420584a07118801c000d560314840f940c130191a00690081000900d00f040001c80300140c08008401000070604409000600402495900b00031a4070418075003812030400008403980050a000b08640a041e40031140340c039030b1401904130f010b81c1d40c00039000c034002001061404405600502d002c90381002c0e00e5002e40e40711785800061520740700c8031030300355880811070307034142c07500036201d6070b0041c0413420145400c1c0030a103203290f01d464052041c01e1140002240341819900c41c0940b0b420140540025691103685640c01c01c0d960017000c1c1e0710140040c105400c1c81c00064014802c49008200e01802094640c4c0c032104011031010301850b007200c5500050296055500740c08a544400f410040790119107450004103014047e08140e0024103030074106826107498580090802045e90815111240d48003500902c1140d411802c06c00e40801c20b15201d1260 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 127876591 1250 127875341 127875347
    0x350d02100501051804030e0609040f02030f010e0906070e151605060106051215040b0607030309060f0504020d0b10080a050703020306070306060f050a02070b030106031401050102060c07020f0d0c06 86
    0x3003948801101081a80d80b140e05115070300055040c034401801e80880401c0100b03020b2000c1c0140361038000e12007454160044003140c291410400080074060b0048280301d0828800c07800306000d0301001c080c0c51701e0b6250001a565440700040d10760402d01c0100f001c000d40f151186951010146041c2c0301c6540c0e1215569038003050717940c0300b240c1034a142c02841d00103e54035100b881210724109540c00c0400050f03c82c400c20b0801b00c807034004081e40c000c0c0c0c1c81040c05041d8031140054251180242c80000e0710f0380d0345040c0b000988059107028004140b41900f0000140c0c2c07910301551305e0300c0e000b04071030a0356036403016a68081950703034000543c0b52140c40d80c2041000070000c0d40c0b8058920070b4003920f1050b222032006406036100d50085401164035407141c1d041c001d110720007400c01c44005104886648e66945891039066000ba042107001986585110310742c1000b250a0900601c02840205601c0c038200e11058182e0003001c00c0240b1900540512401940d50101800c078913a81001001082c00e940360005 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 127877697 1106 127876591 127876603
    0xc030216021215040507170106060503010b09011211090f0405070804020904050709021b0f0705010906051b0106150f0201060f0306110c0105070201060915350d02 71
    0x10900940c050f582d80c060381c013070310180020743d04000a0403070301001d02d200c00d009a030405104104281d0700c1030031281128102d0400a4980c1c4e0a000100d5480e841c5001400d2514140344030358000c0c40a0100400304444100d91050700d840c0b6110512068401c100d8101010460400004d000743c2000440c05031f10038449d0301542d06c4240c0700c00f1001c080342c01c50964880d0303103000d0ba00f49403e00c0c0d20030072000c070704406050001c14055281c0700000340386001c0d6001d51010004040b07501e00c8000032039400001200d2107107000340030076038880c41003482609100c424040090601c0f465080b00a0061060340d003a80d0300c41c0b41c1d49580c00d065840d91070140141c00030140d40036808111014041d08284140380c003914841d800411102c0c98485210140c8000b6a0321046a03000200100942003500541105245081440c0821000d15410007450145011b074541294018022800341d980d90218007 = true := by decide +kernel

theorem cover : BRFrame.Cov 127697841 127877697 := by
  have h0 := BRFrame.cov_init 127697841
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 127697841 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 127697841 ≤ n) (h2 : n < 127877697) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
