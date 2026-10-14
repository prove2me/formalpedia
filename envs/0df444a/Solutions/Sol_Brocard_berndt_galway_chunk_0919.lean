-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0919
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T23:56:54.384007+00:00
-- url     : https://prove2.me/submissions/7ef738a3-5872-40be-acdf-e00ef3c7c372

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 165107913 ≤ n < 165287769 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 165109163 1250 165107913 165107923
    0x140705010f0203010e090d0906080c0d060e040c0f0b040603110405090f060307120b130618030f03110403020d063c110c03040e09030403170705160b0d090f0b09 70
    0x26040c03800403685c2c0030034880d0600141510464a498541200702480e0800c150b40701200204210000341d820800102c0c1c002051042c01c01801c100072544401d800c2a0600c1d00780200c60360002125040340d00d0080c42000c020f00107a0781183c02610300030802c400c6580f0115010f01655100980103607203c1c05020403241000140c40c03158000707030119040c055441c072690055a840071400340002000c4008902e1b05050341000601c101d000d08030202e51032103c1841c01e680c084c103000c0c0a500040d1401d8502d0f0b00103034540103150410342c1d5400c0309406d00e03003140c0000d155503009440041a2507901d01504a50210000c0084404048040f4100c1c460281e00d1450044c0c1c2501c0b881c118046203086010600495408282e1b030314491454015030816050000c5060701e048003411401d40c40c84180300000c0007507104406041040c1d03401d10801d880d15a80e00d01180780085000d800c100d000000841841203402c64025214508400342e004696552142000324000540c1800a00f21070f40f9902002101040010 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 165110413 1250 165109163 165109169
    0xf0405010311120c010c020d020a0509090303100b0a080105040e10022205040203130b130203120c06070801361d060703020c10051f0905150301090b0601140705010f020301 75
    0x2c020900c01210203c454032045046411404038814048510140c104400340d4101c0314409059051035070b0301d640000d41c05200884039030302a907100000704040710b07100641c1d1400800c0841512801c12070300e9403002e0031480d41401500d00840d51422000b14041c1e003040070084900c129041107503544031403800b403400f0180c4e0210358406980d00c00301c0028a400c051007182d124285136a0b03040e2865600340c0d104040300c60040c00042c04030f0080250400907079010300c96050100c0b42c02038060303911541d0480c4942031260041100c1d003800b00c4d010042100c02903000201c220450b20003a44102a0800303c00c0025014000050027121442d20951340d002d00d10500c07061740031404210490f5100c0ea40c00808030164890311711a0103281c0c100c40101c00811015801075500441118261048175a1607842125000c0c0345510a20f07072291a0000d01c0512000b9025800d003400e8160001e114901c0585c4608148034800b401c80c6040140802c8542c02d00c0c1112000d0310a01c41d0b0000c000d00824071118503500107500280 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 165111663 1250 165110413 165110419
    0x1709040c05030108060f04050a0501140a050a0b090a020d0e1903020105060d0f0f14030a02100c0c020d0b1b0403050a0201030b010302190c08090d060501080705030a0c0902090f0405010311 82
    0x650a4007070007001981c1c122802c46008283c80d030303510550418001e0300500115194450300303603107800046082c080c1035140413602428880c0c2d403170300810400a1b21400703804920307601c1c5480101c0302582c64004542d684844a040301503034990004200f0300080c03070841c202205502902c0800078203609095070714501c680c0a64000d0220351a003074100406007160300c4c03004250b04090003680000800c0c980050301840c0c0590301e0400d03076142494013241540d1005400000681210040807060780c00c0c2d00ca40700d12914035140003000044942d021414825414002608555040300060450100b10000445900c58075010702e8840f50759240041e03503540c214030100d0210341000b01c0d0a01951207803007a0740c94420b0400c015410241c0c960380c252090781c3d501e034040c0c5400703008001c180c5460b00d4003821000e8030341c4a900c00040540c0740c404a81c0c18400c903604814440c1e08000410404580c5901c2c0003010394000408c0142e40324241c5000512650000e54010b4110b8100000002805039220620184081c15 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 165112913 1250 165111663 165111671
    0x2031905070504060803090619050f0d05100801050c09010516080a090306200405010c06060905161209050304170c09070305150301060614090f0303120612070302011b0807170904 78
    0x2c540046e2a400703010903058000206010119008840b0001c0d8000601e440c20712500d420001d08135070b01039a21144403c0801900c0d8010700100c00103459000740103000d500c00800640c06d05c0340c40c4801c0792003102c510a04001c000301e04a02440c00c01c080c500003466000c0325059031500f400034080c1c00030303a5500c81501c0640c80c0c2a1000c41c011508821100c40021504500340b4041c200b800555085c03900001c280c5080d0340e103400105146c030980c4a040c0c010302c0c1c0600d0007170742015019801030801142102070b08007035080900140008000209503016510102c0d03c0300e2840540121081c5002e100f184020b502081c00e605000700c0b29090340c407160041940318001c074024a1894141800d0b50700b0341c811040003401c03006031800803140d0b00340074100814008100c2d69241c08401d00203465500802c05001c03810b51901c003404210700c1d200b1010710669180c90041c0c010310f4039540010300340c51000c0580206a2007141c0c0124200200381d412034900c283d201702203030394541603100000d481c0d4201034441401795140c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 165114163 1250 165112913 165112919
    0xe0f0d0501090515160f0e0316080708070f05210105100306050606030f010902090301150e06030705091005060318160e1810090507030c0303030209090c090d0605040203190507050406 80
    0xb00d40301441750248141c0824186084803084440b000c5001c2c100c0108501d03504101510341c0c2c24031400c42580c0301041c8800c410b03414000304506184540d0300c001403e500c00c94080000000c01e44548080f50812a0558070b000300303552003029100038002b08035546501e02000c1010b5080780088610581c1c0c024030040056603074480920816100560750a55070b0b0301c07680d004010000c0b541d0000c00520b40003a001007005500d18101c0b41c445500d40d0002040034000404003c51820b0400a25005081c00c403000b12890424010000418211313004440c000d510010028645020008543d80c20100210840700404d114500041c0c031202c0d180601c00c1020200303c0444d00620340040108040728520340540461102d42442000420515004440c180540c000001c007152050b01c40e000114040c0e140941c1e120783c82400c000308a80005e288485880041c0540d0740e1b0760300c4d01c0041c07003141c951141000541e92650300009107040c00c0c88035501d0404ca094601c0004021010039014101d8405a138203004a6803 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 165115413 1250 165114163 165114193
    0x12230711060f09040504050c06040b181c0f0206041802030403030c1e030b0a091407030e030a0c120e03010c030905011404050c280f03110a05100e0f0d05010905 70
    0x4201040980c509005020b03c1e00781d460180c0c005600a4440d104440c80c0001c0000840c0c0650425800b49007140f202150b241c40e002c2101c0440d00a405040b03d884519018400036509003160803000900b007103ca40061004540790741048030043c0c05c00c44400c48480c60070301c2051b40a58002c031422070002e030a019034071064502950452843c030b0a0b1900f01e50920710388030030440c02481020342259201812903000228800b09105d40c801c051841510700d406407801d81c03805803e484022202d428250701c2088000302003984000e200106540c0007040c06c502410081d801c4070024444c16120703505510f0310903922000380c0c06900c00c1c5500c0d8840c2c03000348141464202c038140c0250084a001c0c0140c2c000c5510f9800d245006c12a00200c24807003203031100d8000e0302d49e041040c2c164243e0407000303441c02c50f900b081c03040c0a160505481041021214280031310300300030104422000c40d00030750003800680d00811846507507080040d050f810016040b543c0c040781d181449400380c0007450307040d82d030750245000d040d070140 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 165116663 1250 165115413 165115417
    0x103081b0c0a14130908030708090316030318050115060e01090302130b010c0b0708150607030909050903040e040b0f011e0b0306040f051906080f06041223071106 71
    0x10070050405001500c1e01e80f40e25442c1c40890f140341c0d0300545004402840b1050761090007602809080c200b51a407070a014007030841c03c8083c2150500b5401841070b4050384184601c0702800645c146004654020072072042865519078144c01041ea50a0500301d03003419854611410450351541d4560400881640055440b00072601010b904144205e100740007081c4190444c200011043c0f41c400c908001540360b0305e1044101781d44a90008407800c0c14800440b4001703480600041c0c0440b54580b41c090140d90140032000d1a1191407006078440e40040d4080c01c007071080d600108506041203605160925054821060450b010800c0004040012400400b50030035001403010350010983d0072402c1440005e0240c200602c810f5100391158034525100c039041c024940500010100a4100503003001c0a1081e90340c660800c40050b4401c0c0080501548001041d60700660041100310171813410042c21120200f00d1139210100e88040c064a8405041d44402004024083d600c54044072040c0d4080200318 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 165117913 1250 165116663 165116683
    0x3120b011407031b120210020a020c090709080703030e1e0102030f0f0f040b03061005090d02090c0c151e060108070302090a1503090b060a1511070504050103081b 71
    0x144070701c030035a6035440c032040c02400000d001c0d0409003400d040c54050407404404c40c000c1200e801d8130505101003400d0701006019844011000c05500b0718100c02d42c02555601842c60082c030400d05000031859483c0602002c101811000040d0b58401e901c2e82009409880303c20141c5014070540c2d00c0f9100c410040c0403161044c001c0503400303145040011000d00469412142c0b519012035010031240b20032610020090000309820091030342c030f80c40c10401704100d01e801d11104034103000040000700700d02d40e60403402181d1554101d82c0e02d4019101c41e400c084a500502e0a03d410b01d10030303a04854440704d0961400741c803408201006400d010508080c0d105c842205640c4c50303011a5121000c6058035004c1e8014041101c0c020b04a034400380e0340c50f003030219070b10301c15007400000c01c0e07442e0060800e0003c3c015119511080a6071880a82c514140c0c8095144058014040c2040340700400d2954201d01480808011702004009001c0e84d40c4908040c4031561201005514410324115444807080c00842c040c225 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 165119163 1250 165117913 165117917
    0x120c0303031b190801080c010c080306010c030c060203010e01030b01091b0503070c0c090b0a08010603211e022a010206011707030b0408031501050f07120e10030903120b01 75
    0x20341e110038201540481508000144882c0140180c03103000350702035a410b102c044240c1d91001c1c0d0b035140c001528181610040c4150421403232200c00c10204d80e1078400c5a41218080c0b81000c400c12140c142101d000d07420a40c0101a02d000100000e602540b00c0c80b540d058078040d18048450ba6a61580390040f00ca0715650398408c5420658281d10b298042d501450340102181070859141c10541d80b40340c042c030780f150000002680c1e112a603c1c014285218204060010400208210303421912020704040c107400a80c024011108401c0d0415445100340c00b40800522207010030103015018065101e10702d2424040a440304440d60603030b10b079000c00c0c00701502801a0007130042c40e428034800b032030300605000b2100150300c145140040001d2148070507500c01c0f8040d0301901c1d1031703007010400700c8024a03043c05d100d41004414018401c1d050101c81c11101401d522801095a2164a020544803050780d202d0080d84849030b44154201607405800c407c502c2442580e40702ca940420b031120b002280d45010315a40 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 165120413 1250 165119163 165119167
    0x70801030f0c0e040614100b031506070b09010207030e010e0d03080c0f0a020106031a04020108070302030907091e0c031e09150903020304230603042909010209120c0303 74
    0x10a441c4000d01e200710b401100320454054075828403c0b01030034191004c50b0001d980c0d902c0c40d0320003141040c105801c1161400020003039171415049003002d010140c054008001c86141688840d9115000c0780e503625408005120b191500c0c0310254000d4014803410340c0414405904800d496215190000f03200d04000d0180300001e00c0340d14201c818031802010100e50807002c00045c50b4041c1418098054110300b640041030742411031034030510705450303d0084802ea00c1d0360800d0200507a004154035600008501d0016101d5861000062030010142d0201c0e0440d8174001d8145c4d580c02d82c034200c0b0138811243c940284030b542e407038210440c1100c00e0108680020480500e84088170320660300010086801403070b03800b0002c404204000100d445007201100076901c0000c3c10006503170103c1d82a9a503040a189003c01c640002d000300d2030790300c8010402440d02d15201d5802d88e088966900e00000d034000c2c0d1410700d6140c9084842e6900030740c46068000c2c45035496400c8245501e5000990320004000a80a14 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 165121663 1250 165120413 165120419
    0x50105090a0e01111803070b04060519020a020a0906061707080c0c010207020306010e09060a02090d0f05190c080c0d02030a02102003120906070e061c020705010204050103060e070801 80
    0x1000611444560b4441952101c0c89442004c440001074207940d100154205000c1c1e4919041501d03200c03095000c04900300062000b009441d42200a0b50080d07441c0c0b01d02c404030a08021130490800c3c50b0494020362084030803030045110f10039a4030807019180c0e6a00c4051030035440324031100f80c00d04121070b110009140100040e000c421200c000d460391021100c009030504a20b13a000906200c8240c100100301181c00e000c200884908020175038003d0016101103140c04861004603100072001240070f003120100c1980304007000030030481441001212000125000c5841c030381a4407402c42407281078020310a00810340040e00c1c1c00661f054084d40d00500605030504590300780500c81c0c02c1e240c2c2000900603416003100340110316282007078460f40c414024564441c481c88540400d100701600000907907010204001e10035401c4241d6205506048822645400030040c6120b21001c54038215656507001180540400005401400030340e4802d89040c0301054a400302481c105404941c8032002902d210010 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 165122913 1250 165121663 165121681
    0x40201051602090c030403030c050c06010e040206071a06100513051203090901080a0204180b06040504050102090a180506010c03082d07080a0b03060105010f1817160905010509 77
    0x10840c120710000700464410650300022680c040403140240b00450003c1008101036051140304e0084040f8100281441d4405003160364031401400f42d1819440460046000d5590740002d03140841d90121942c1204c0e10300701c1d1410000b85041d10000d016248881894100c1c0f4041c0040d40e515060701c08411900d135140c84100101055103600d14440c0703001c204103c0c00980c80d40d030940780c06030400100402201c401441480308403520410034992464090780030200140a20402a801010440b80031900d13403520305045d8024410148159030000f072450b400202c07440d0103a002a60001d039604c0c2000039a6403003005440c14000d011004001908980014803050701240820305101c000d514502d165040341c0d0404501c0040581c0c540f4041a0424100f1503c0e9029019642140c00300750b000d8109035143c400041e180500c001c4a4106001009098210261082d03003000300414004810320750a07800d644840d0384900003003a00440c091003000c0c0100d0126130300d00501d4101c9001409007000c95503070b40c1072 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 165124163 1250 165122913 165122917
    0x3010c0f0e060c01060815010506070c0603021c051e0c0c03030c0c070f0303030f050709050907030b01140a0915021902010c0503070c030507090b0f090a0c0207030b07090608090a050604020105 84
    0x84a940710b42c0520103405030307010901c103020142c034460006000380e0200e0030f031419640c24140d100c10f01c502010000c0d100010000c0c5200e504445003030501580f02e50480c0080441c1c00c0100d041070003490316010401c424610f650038201c1640b2418202480c158072009403220340e40c030915003095500d81c0b04001080c06040001e0003020503111980c00e4030b50040c0c0700c89040400000035401980002d40701c0140c2d4107103805500c140f07600042c1e01c1c1002410240303058085503003860018000c5d401c3c169107401c600c1941c4d015004e0030300ea401ca007410030f540e0f811040c4005464002c82d4025804107480d80c0886a800f20700026a10351003502c0c1c40d101d480280540e0b030044481d0844040e044895010911034800050a0498418095481140580351103414400b4403404c03110b50700c81c00785c41141d40a0800803191180a8850b4200680c104040352a200b41941a0b00c0c1840e250300041001340101e0810040c2d0b94080072000588501e960b0741c11a03078803504001951100c1c0050040c00540240700031034019030203400 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 165125413 1250 165124163 165124187
    0xc07120201112b020313051e210106060f140a14030907050301050a1503020d0c0e0a020403030f08040222060801060806040501060e0f0406020a02030d0219020c03010c0f 74
    0x9007002d80c540c81e940146003440c1c4601e14200a2007500b0840f441d40d064a80742d03501c003114061000b1130406a1a8509248100c024444d50340102007003140200e030420040d100c51080f01010380405241c0801e1140c18072110600144242c85500e01400850034500c00c802d4010040c080e80c0d180e405207081c3c03a41c6154941d000c4035040c018401504942c0104440000c0694814413030f20014043d900e10700f41c103050965400404804003e89000408144001d0440d0010300741c1c0e40564404840c0940340c41c0c05510701c0c8460300009440b8902c1410020320743c51603002403042d288203564004034a0f0040c0b00558400006440007984004400501503140040080000245241c05004602240e84107625821212580c00c0303d11035030015020001800424040d40d401800d0500e40e1060515012096406d00350300600f008120980008000b144240300f04123541c0c4a035441407086540d2900010280760303070b00001e2400b00c094051120a50440e10703040c4213050241d1400d403aa540440074203101200c0104500b0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 165126663 1250 165125413 165125417
    0x1f080a03050c0a020d1406010b030106050a0e0d0501050414101e02031314070303030b0303070804060507050c09100501030f140601030902030a060e01200708040306021b010c0f0e060c07120201 84
    0x1090010140c5e69010000c0f031303041d014a40074529803640260141c02e00d18140c1001085030380c05c200402146a000d002c5130049201407a114640107000c42c0083c80940c02c4020181480d800d00052006104c1c01c0084a4130108a180403a14410284400e000c291a15071100f00300085206504d1900844d168004542c000c9296080c003103405015a5029000340034402c0201040e40070060034420160580704404441d64114019401d016055407480d02c14880c50242104101c00415050b0410008019007281030350000c0c00d41c079403890309400240d43d000d000c4c41541c0c0007a00b0640013903a000340510074020f80042c500b00c005029911000150040d05c6180002c9070588100c03400100800c500d03101d08074050383d40b00000710780145620f041c0711a0415440c5440001e007002c03c0b07041c0001d42402c0c111030880385e0000003d44c64a0f5419203401c0a0300083c14214400e50a02c010142c072a075100e0020800c01d43c498030b5002c0c032504c5240c103014580c021819651030340d6006030400d00c407004219001d200218814 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 165127913 1250 165126663 165126673
    0xc0f020712080f0c0706050315040b1011031c0c030605270c070b0a1b080709032012070608010b04030203030315060c0d03060e0a05040305030a0c03020d02070b1f080a03050c 76
    0xc240c91302e00d4107816500c0310000401c007005000134000e5034802c1d030442c600e04460a1210102d28400140914000002c0200340244005140b25410303040c400d4502d0028002003014070301072400354810203000c1100c1d902c00082d10304600417845282c035680401ea040c0d0740c800240404d44a2600b20004044050f001514030141480f88000040c91b82c1503040c81740103100000304040b4440301d00d0201640241c13041c8020710403510200300803507601c403851500b102e0700501fa048122401e441c1d45213a2010104066400c0746110946c0100002d000641400301c4a15aa514126a0f6175040ca0044c1c2d0146010013035040c0c0007007021a001c41c4146000c0e000100c0000c001c98034051071043c40520b000e0450399080d0100361500340030864030b00102c7c15964000030b5000244018586550f00030024400104183c0700d403982c0350320808449200741d040d03c0d4420000700c0e0071555919641840f0305123042c101c0d20324010200312280188041c00b17456040c4102d8109400501d020440c50350166a6502f1281e03140d000d07840b403 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 165129163 1250 165127913 165127927
    0x270624030c111e160603060f060c0203102f071401050108030405060708040b13060806011b03030c0e1003140a09020d080304030c020913200a06120609060602010c0f020712080f 77
    0x20113001e500043c91103440019000e403500104070507080301e6a10950030f02c4501c524250250f02d001c80c540c0b46e0300c031514a0024030346200240c0703030500340d841481c01c006508100000050064016000f001540d00404c07540903100203151126003a207100740a108001c2d04144010045030400748045d0680760f1107000d006041c140c80324080b000c107030003e0310120b00d448440b03901004a143c000060541014003071030102b103121007510303403000392a0b05040300a003011b5446c002d020400384512054401503200600000780003030340d11002405025113903840c41035408048040351682c1d02d14490185415406003207002141a140c40720402034200510076070074070502c0c100e52401030340c800703090364445c01c50038100440000c601d04201220300b481420400d121301103c03003003010f15036644010307104880ca246091100e40c80c0281d80240580341e00d51002c0f480b1414540b021401e02d8040d0130030010001c1d030b96200c01c00c1e1003a428007242c0d40e1110748641c0384851203104644c000320703400900800864055031041450110 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 165130413 1250 165129163 165129193
    0x80c04110c0102181314040b0c0910020601080f07030c15111510060509090a05130602030f010815010b2a0a050706080a0204270624030c111e 62
    0x110800c0810071320301620007056158541a00c281e070007080ca03140204120206500d5450a00038050000703001d051900d80020744c009210f400301c1e400f03010007a00314117803040c07043c001a42e201420b0107043d8040c0680650001d95910000b1424101ca4104a00790b18084c90160700345140c0d000e520f51582004a12100801108001c10004481c0860340200300c2503898048600d03d01d4214a03042101000010081405150390708501941c20000d694000a0161106666983c2e03403080c1c80c00c0284040e0021082010800d01c5a55940c100c60315074041c2e0f07058501030803040c95a0003003400303610326a4a05010004124000e50300000c1440d001c1020003005200342c00e00d0903c0d04410000468503540012814815107a12030640f40d040340f0141c0c0250708150611114440340300100c00c082407008040d043c11541001140c01040040040020400d401ea8501d51580050320709118040c01081c24500f10019051096698181c1c0040f002d0240103c0796050031420000c0b40d9161428004e031082d0580d5107030f006 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 165131663 1250 165130413 165130417
    0x40506040e0304031b14100305060324010518040305030f070507020d24060f030201050306061201080a110901140607170a0306090e01020c030405010809072c0a06080c04110c0102 78
    0x160080302c500341a100241013000d072000c175507040b508282101101d103011036140c00c503c000c001032007070802103071070368404001c41d2038682e14880c1c01412a214109003080340d408820304606130781c01035030b0501044041d845800340d002000c4c1c1d40100010400c00002e40d549041e4038455800c0880b61030824500081e42c2c002484000f031008081c0c03900c40c070648002e40140410500d005484001c0038051010a182400b01d40303844001d40b0019052010000003348569244422101020320300b00c030884195031514081c5941d00b41383c079022182c03807660032105045490024400d504071400c01146403c503040c0441485140d80208000720b8044554041400c041d50384000944080a040d0390005200c40c0b808080c0c2d0150780551000a1544e441080051048400803040701c0540b40c0a00b01200551901045640b6040c0341c0d42c0a484100b00361115200c00702400d076400720301d485c070b661005d10745521400c050f08111a42c0b07100d010504c1e88070540d0000f00707082903082200c0d007403081c0301c05900700000b09060509a07 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 165132913 1250 165131663 165131669
    0x40b040312020d02031509010303050a030b0102100221010b030903190c06050414070906080607050306010903060608030409060503030c0d03361a0c03040f0206040504181202030c0c040506040e0304 86
    0x3c01e4002c0304000c14244031218001c401d9a0031903105a00307500d56200508240b0914400740100740d22004007001170790080140400c10380f54060115615a6800041404040d44601c1c0080f030803002c0300001401030812082d070f4004c0001001540ca41185c2d4114010818002a1414103000002c840c13403010669500c1981d100f54005e01c207114071458a8291300342410074940120344224a011006e11a01000188144e0b00c40c0050800c40ea482e1524801a0740400b001e60006200f81e00305840801d1015020005d4000c03100e001c0c405015041d180c00c00c058490050b100700710082e501015800c00c0c107901c65080100c228681c1c40660227954212810365036610001082d49024006810b292403c0201407001d0003c211840740c0c51410f18104501e408107613200190010300341d100c4200d526802c0d956800c084600a1600a00c20071001c4154203d042000820344400e4a818038880400202e9030b0000c001c50f000d401c2c2c8e02c800b80418880ba0300c03c101c02018082d0031541c00580d80e410513002c44800b08024005 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 165134163 1250 165132913 165132937
    0xc1305012f060f010510120c020307080703020c0a060e01020a0605070905030d050301081c021f14090a0c0e0106050906130506040816060c030e041a0907111212040b04031202 76
    0x700d140560700b03048910782c182c0c00a4042c090084c1c800d1034140c2d02140166a110031050045050118080300f00c0c0385002c0cbc06005440c020340010740600305900094100408d0000342c500883e095582e038030503110307041c3d524a134502581000461b1030002d0441d07403200f079001e00b81e828585106612000070030703d426560740035000450000030050120460170800100602c801032104026000d52190003501e50f203510b550807500003c410790008154200343c00002045401c0c1400350150303e42046020f42c0c81d1000c1409546005502c0303008111a130118010506076600b136111203140501007000d0101c9980301d1100c02e2140c24000502291654070b0400410041140d00c00500000c2254640b403541c003025517004070280102600724400180d04905800c140311070888000941d80c070100c04110308121150821030307103c5801c0c020031442030341025074940f240d124102200c4404804005940c024854162500300b801c2d5031400040c001807034915001d500070311034681801d81550b1404a642681c02c090135041c8 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 165135413 1250 165134163 165134173
    0xe06010216090c031406030c06030a0b0910051206220501020f0408010501061205010608070c030210060323011109120708070b0304120804110108130b0906010603050c1305012f 77
    0x43c041d985800713004c9041803200c5440f5280c2c20105c0009030349401d00c2d560f2500a21002c40015030800a5602040da4a00090003c0340f6a152451100e0341c04e03811802450320842443c600c1c10900c58000806521034407a4200118140120b23030f50f000c422000008045035150340800c48682c8441c024409000100190000400c10b0b504107031000e400c882c450300d400804585001c004006659124244540203100d03820040018102d0742812402c10465000758000703281071510000420201c070403130b0a942810305414444240224100a0076aa019030311a0030150741400081c03c18540b10390144442d280c040202d8008a5035000b0716400c2c6903580e88901c07288000402044103000108442c5401c0e0800c0703140c110b003140342941e03a00c507910242e65041e034100860000081c240b03264034a0707807030112600507046402a24011141c0c0f0390300d80090056100007130412002c240c40064840685070300340c4640202c141d495003000d004442c0c0c0070200710401202c0300d000805001c135050301000c000b040039200700904 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 165136663 1250 165135413 165135431
    0x6110c031e06090f0c060702010c02061206041a0a1a04081507020714060a0e0307080a06020c0f0c0a0b07060f0c1805010516140102041707060e090606040e0601021609 73
    0x40c1421001082003016810054480201d0507010503405c584400858805441d4101400102c0d080d5004a00003504100c0c0050304005000407460810b200d031170100d40500003c07650b54407050034100c44038295500806000028019200c05850120501a40780341841c145039507654550b1600b81600c142544039100b030400e00030803c0c3c0c14450a8050860304600c44001d200784c0011135094072546214004100b6084816042d6940922404004040301c04c12503240141e1428014020341c0042c5490119109160751008003c40128808103000b01c001c181c5807065290070f0104100e603000780402c03a00f00d5503e0303020011650307291085402002042d0790b002e50114400d02e000d03580644542001c0d0601006100d040711f41e001006100c1e9107580e02c10355032103050343d02c81b080f14064000c0e034111480c40c42000800ba51050f10010740041200d00656913051a44500814420320403015076680760080c0c3c0400060180c101100310264000300c042c0704640c10940c1403850856144099040811880c0d240c8401d1 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 165137913 1250 165136663 165136723
    0x50709080d02120904020307031e0c120e060c030901090f140d090807090903020a060914120405030a0201080702190b0702010c08010b12040309090509010524090106110c03 75
    0x1078080d80030303903000816462441500d481c41d54044c1000c018481e07500040007030445031094004502c103080d0310141c03207001011105040003606031940804002641c1d240c4070141e0304907038061500c101d55010302400043c3c444080f2900d0540c0000c01d20b201d590b40303d25101000480e01803021841341d004e80c045480754002c99110034205030380b519554080041001040c00401c0c00800d40030111a014040001e11040302e00e416070900c040490050035031454546207038140120442c009103158002010303109100401c0001040601480c010660158040946140154051702080d07402402e0750045542a007540c0c0c4040500c030301010002c0310350a41035814095144d03024003031440d01035910b0408150a6041c20f1841060380076100456000c040c1400209050601a5150070003504141d241841103181c01ca00c200d000e41001e440174545441c10746490311412022a00b4072544480050484903c3d919202048500744128100a40180100303510201d071603400f001078002e5058414126a0444200381c10 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 165139163 1250 165137913 165137923
    0x170103060902040b0d0c06080a150b09010f09060c030c060f0c0e030c120c0603041a04080403021c03122c01090b06100f03240303110d05090a03150f05070908 69
    0x2055001d041008240f100041b44810058190b813078500d030540da0307541c0301d100740f0014180700d422792446921221000314202e000c0740c004054002e0280c0759083c01442a040440e02c030724a42c03250200058207803601000003031150744450f4519000341400302c0c8640c0e14016100c11503117400d0f824404101000c1d00649503003018400250a04011120407056042d2620002c1d1250500384045219900c008001001c111036114581040d042500c4080c1c410301d05460141c0c1c2030381c0b0030302080e80300d4a980080108051014030307043e881c2e20391540d00c08005180b4907240d80040c00c0c250032048030342012005c100c415481d4078100e16825078015400499216905e04208190181c00381c07c0b1070190401d0444030348205d801100e00001c402e4240740c0002c0149081c046940c104c002604031540b000c480341c00000500d507001c100031403020014030949502c00c9000030107841034806c241d1403903040b0708414010004152400080c04142c04000e1020070750900c12160b060803264100c030104046085440c0c01d100d007000c1040 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 165140413 1250 165139163 165139181
    0x6080c0a0b040501051b070f080a0c150f050a0314130204050c030403050f070501060b030c03070e090403020d211b0f140910020c090108031b0c0603010b0a17010306090204 75
    0x20703100c1c501414800001c001d44203d0340b800c6428200218140d2014604200d40c1000f41490001ea004607900e40c0440c80d2036501001082c2d520600c084030120703409415002245005c181611414420502441e00340d800360000140d6500703150781c074032140e40b03c58451051180708503200c2c0d5045c03a00c0402e610400007120000740004020650030f00421002a800404880300001e98030075441e11340d0700d14a8418094030301d41c1c00650800201100740142028200055401401180c0343ca00100721100705214101d4000c641c0a130040e40b0828803594000d001d010b034020b031110072074065034000c1010301918041e1041c0911300070703000e090701200e4109594407141000c4140034900d403034010340b894060300560a004801141d0322035403841c620005490700070040e181d6003c0d005890034400e07680d40d5203a01c0d1030b500905960718658803280c4c1003460000011407200c51243d80103060b1419a420002c0048042c1c01078195241031201c5e101142911003060640c4500031342c804c40f8003050200b4644140010303100c0f005 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 165141663 1250 165140413 165140429
    0xf0f030509030706020306061b0c0a0504090b161103130e060306070c08030c0921120901120c0507021302030604140606180411070f0203060c120a0902040f06080c0a 72
    0x820301039403000100440f28115001180540c0340e80b83c1d040002d015102c0d0440c5507400009440285c02128404141e0480034282107850254280c0c0d10700521045c0c2e20030407002000d54103d4400070b03809004032002480d0260192030301c880c02800340d1005620310361215101c1d10a180d8024800c1201c00500711010794440016000307403500c2d0408180c007a1030040441e0004101c0321011000600c107203031803030540300080300082140c0d10044c611540d0610190035420b981080e03000300c0d580901007032102c00407a0040001a900c403002e1480303181c246401001e0105400081050070011800542d80c0d041480201c050300c0080140c1d0b900b40fa00030001141c01d00c0400f0a0b1b0511070b002049626900c22040d035088084c00201400d0002043d0700003801003207400c2d0b1820750b20001050200900040300400782103107100750101c525070307251310f55070301c80703d0048440342c030210515900022000c40c0c0640119a0700341c40030348003140a082e840c105d5401ea4610750010b405591200039180b401d8030b440342a51000b00300207 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 165142913 1250 165141663 165141671
    0x11100c021011030708070303090b1315110a05030402030703020901031a010501091802030901111c180b0402011b06060e0906060a0b090d0312020c06090f060907030210020a05010c0f0f03 81
    0x7079020030351a8007074400080e100705c00205a01083c940207400c0041040d03882200c4da40a842d046009414110032103105a402c9028030100c98001e000c10b02c02c3e88a03003159010900d0908020842c110707020780c0003e0040b13806003c1c0301030001c01a00c0f40c5020501940c85041140c80c4030610300d12501417984140d109a041040f004002c00000403c40c03081e04c03004021080159590f9a015140c034050404a17640c20f90b03003e00003481801c00c01d003101400100d4261000f06200925448500c40c40c00180480081c0c14402e03044003007001036004880c04103500004104001d1420440d4031044202c3c0d00320750000030307240c0c5040c00300300003480140201a44401c08640a80100f802c091320000c03103000d1214180e00840c0e01804d0101032600851804030802d44264007956604200e081544d159981902d0f00903c03881030208401c01c03030740d021401522a0100000514100e131440d002c01049003520710308c46096000320103000300420000e004d800b11540746a22080014007403084002c05e03100842048404242c64 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 165144163 1250 165142913 165142937
    0x3010f0203090102190207050603130303020c0f0d020f07050f041503050a03020303070813050a150f0207050c240901120905030c060117071d04030302090303032a07120c11100c0210 79
    0x20027003900d030803401a24601d00740010600e415070007840f4882c0d0426281c41080780c10b02600d100000c42003030303a2440e0380c20744180e00c6c1e510a869640d80664040e40d6400342643c040c6d40726504040e8480c428551030340103174501a698076240c2e1400e12041c43c10640040e013001080003e203680044115030440d9400d051441c20350b8030340e00d546449044001d4014100c01c4210081041c040854202103000e84000000719512203071441c08507a540c2145840074001c0c1c40d0204c1c41844844056880ca52070510b920031507180c10b2000004491803900101080c02c0240d0b10040c0030b0110310100064060407901c49e00400d00795050800040e200881030f0b14a85155102c508140407030090611800c4251a855290141c1c58450b80740c280c01170300a030100107405100100402407a04401c114030015081a0140014041c100118417142845890000b8143c01e1b140102009050300c00c1610801d00c41c0291741c1d9940301000e01000034503614116101400250b003440c24502945010400c0191130041070600e5040350720 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 165145413 1250 165144163 165144169
    0x5030403020c0f01020f0f06010e0705031603110d1803020c04021327110a1b020a14011106090106082407051e0409051e040c050f03010f020309010219020705 69
    0xc45006101d0260340152220803c69000700050802481104d00755054000c1604105e40d40c2c1100344030700c3c00c5400002c00403c0c0704a014004590184500345106455030140c0032044e801342100d1001090741e05800c004e00c0502107413a101e0301c05503003a41606a40081d005007002481c2802e0749541c50312a0b4410490441c0b0841035074402d504a404621500707603208018065002c0001c006c848500f9804c0c1800d9407100304010f10401041403001070307140c01103100442d0350101d116417880f101c000d400203054002407288410036903d00b8485501494114040a034003454182049001d0324090b45584d11050144180141406080c03510f02e001d8402c112079043c00d8607001c5c174001c0c02620000034000c000074000702d0034480032007201c076480411000036943c0b0398990403840184401c8526031880d00c91640340144000c01b0403041030240790032a0343d8400150801c0c0c100803000c013200d5040c170b615669503003541c1d12449550000d0352041440c40001a08e40040e400480300721104115141d0441d001480180040d0f9 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 165146663 1250 165145413 165145423
    0x4c03050604290102010e16030506071b172214040e0304090b130204060807090b0c0d05180409080706060503061003030804150e070305071d0604110f180406060503040302 74
    0x40b000001507030100c20000142e00400b80110f91000501541e040310070154050101002120b2040c41142c456503a1f50108a0703450701c09503824143c4400e030113601e00104079525510703040382000e5803800d450311540f405011034800c600303815601210b02c0404c0410014500907a44210391030180c40c24882d80c1821004107440b84201d010b026400d0b0b580c0c0124100d01d48030b0b1440c166070716040304c00455886891710300280500c2c404959800010741c02c0500404c00481400684084035401d8005003060b044001c02600ea5030454150624100c2d00120700d401d10355154003400c803220380142d86055448405042a00c01e440c01ca8203d01d000c0d5210340248030126501c422500e080700d4152400a09a484502d003031184540d03d10411071209050603e0460700000c00f0807000b04030791103101201c54007561904030446842d803150f22914545107600c000303851400c154100c0d00f4041c140a81c030901d0907000700041c074003e410241034550220200b10343c89510f4100740c403d85002c0c20550410701c0c114545550025614 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 165147913 1250 165146663 165146711
    0x20111090604121115090306150102151b07030302090301060801090206160f0807030215070e0d0209100e0906011806050a050607050106030c080307050601050405064c03050604 77
    0x9484200031301241d110031000d0804004c00881e02c9001c40c00050342c19401c030806c514440d01881e40818071410b00502000c2c170160040c0c0160041c906001d1551800d04e0b001007400708034504802e6018170794100300000380300e841e20940300140c89000c00010306084030b560741c00004150385002e004c040980d07103000c00c0e680d0741c6c0840d048024610000b440c040300c00d841c49400080c03545401207029803c16030085024600c04259403088c00080c2e84489048030f21061201c5500e400101c0c2c40205809410a420010340c440001d2410b020000ea9407003c450115000702e0b0300a03900d400580051011140c0120345441c40b404e0500180202404c00300010941c00080c41100c3c890f29002078140d08001d800c0d0498001180c0007003a07604001d0340d07004a2a140c0d80800c000722500d00a030400425180b0705442002d00400c000361980c8850b181d0400d002022005905000c0496504500715007c40d0980d403d00034404c0b4201c03220126212180c4e2805001d40e41c01500c0340d40310364205036860f01121b070002c100c0810 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 165149163 1250 165147913 165147929
    0x15090a0b2202130204090506010804080a03020a0c02090106170c0403030e010c1b0803090a09020c0303070e010504120503130603140604020f12012d0e0a0504060e0a12020111090604 79
    0x1804040100c10390040c0781e90701000350071a14005107895a03000544c00f4108560041e1024842e66461100440380c510381245d006000c0181400100201807003070740988610a220304000d5528280e81e000940c0c103160076400303080081c50400b4400742a420b4441e6042e00440c045101da802d050560340c010b050340401d07181c100c1c100641118418180040990200e1010308075448a10000e9207030703a50540c807684004c14040c01220041e00000e081005c6100301c54220000304091421030f240c1c0ca00c00c80340c061010110904200080c440403513411040c0c106030040c548902d00843d80e80240c000c0c54122600f49921540a151403c0c468001c1034000215440c1c1c000000ca60040c0c0ea0100c11566281500500d15443e0480c01c04500200c0c59246080315002d80a0328082d080440e081071416440e4015503d00440c60071545180100e041c2e0002d5800950300301d84075600114000d40c41c41c1205281c20420711040e51010101043d00f6092a020301c20880a81004100c0c145000e15034004503403988224454480 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 165150413 1250 165149163 165149191
    0xc1c0f020c09070c020d1110020f030f0a051c0218121903050c0708011e0c051c1e0b01090906080706210c0c110a06080a02030403030b040e15090a0b 65
    0x1816920915181c81860350003400b8040f50469810554105031ba107c02a500812140c045044694000203001c400446003000541c9030050b00c14042c82150440c100005c18000e007030240302c0c200d4840d028220501103c141b801621a03014120540c075078140c50f05141d005400602d06054903c0010440031801c0f040b8403030400c1c00010618003242c1e81c3c480d039240c1400a009000d0003054510043d0028426800007100030803941d03100319089411110f82c131440c0400306e90100306004080340d8480d00d1001480c0d840000080883d64582c0c44c020760325205281e40c51883e0340300c0c100041d0750303044124007021b06401041000441d04281d0703860303501c4407103004200070700c0100c1510100704000302c40910700c2144506001d206419030450007a00161107818219100ea490850b80300143c2414406401290000d64804403076403200000c0d00001d44c40034000780d040607120140300b0350399241d5024030700400c9400703c01000382c1b1618124901010b68003505024103600885010700c085240da0500c541c001c000d01010031 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 165151663 1250 165150413 165150421
    0x40b010501210203011403070803030903090108090c092e050307120813062001150501030e160e0a061a0702060309150406150509040f080903010b04020c1c0f020c09 72
    0x42c1206100d440740c1807035000200106901407510382c40020120f0030b03000c4441260f202c074a801e4490004480ca0384c8141d2040c84101007940c880d16485400c01550300c26250303a4002d0a002c0f44402c00200d40401524511100400c040e04031281c9601070071146900015285092900280e11019984101d81080703e4407000070050285100c101e4924800124090408541c0da64000e4100207218080c1d00d860710840c078100c3c503210f0040c09100c26100c0000f148030000c601f0000194000c0220ae82d00442c144540c4800000c030810a01403070001d0a99220215180c5ca810103940b01940e1003030308085c4954490000e00c0000000c40016a800c0d99411540076840303036100075801b0f241c008171980741c0000f5a041d6050005100e01544a40c41409202000d0121a511a024410310382c80036034005100f400c0590710000440c0d03210000d0250040001c0010500e280c01900003000d036046083c800e20641c01801501b940c803100050216001881d40c14980c040c440c544c14040c1d01c4070306042c00c2500a40d4000d0001e = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 165152913 1250 165151663 165151697
    0x706030c0e0d050106052805150c0312060f2b020d0f032607080601230403060b030c0d02010503180a120806010806011b060b0a092f03040b010501 64
    0x400310120010701040b21031105030600c28003030042c81c0b041034001da01005007141e00c01640840c00c0d40210325000c40301d89040c64042404000201540060401c0c0028080b002c282c40c024402401400c0500d001001c06e41400ca00308039000c045003441c80c2c850803942c0041c12425140001c4050400c08030343c04031000d02450700120304504c454180c000c250704641e9040c3c1d4201074000c0554240b0fa02400507035a8401e00c0c000c11200c0031081990010041a03840c0001803a6601c21006c0050001d10807020800c02d60782c43c0407000702504503030011658180c9480c084805802c041200b084e441c14100c4161020703450302e40029080b44801b900400c8c044504401c030040c0014100040c0c00e0159018421000c07038080c00d031000b00b0a41041c3c070018001403440003c1502036100d0220f43c0b02c16103855100a0551000e90786000040003140ca41640084107000b00041441e0079100b5040c815000c20340a500443e17030182d40240e00c0c8802d003400d040411044c8184000304000304509410744200703003041090aa009220 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 165154163 1250 165152913 165152927
    0x1e0103060b1801060e220c02030d0e03041d06030c031902190f05010c0501061203050903060a14150103060b07051c050a050702060309012a110105091b01050d0f0501050906030a03020706030c 83
    0x42c14200347d042c1503a00070040d50000003803070100d141410410202c6081d50342142c0764491132140416080110b58450543c009010000750482d100504860f40e09000c070700401d0900c0c901c80040c0d0902d6621038410419400c08141484071044480001e10b40103090054141c0d181c0c1050003891304004402e1030f21020002c01350720240150000d1756810b0440c90f400e150082c40381e402200014024041d6502160400c1c00340c0c080c078a01c402c450040071010f6a81d20464607a0480c1d01c041c5281050703156031001510402c080c0060070800c0c002c0e0050800c4282c045991000c01c100540107100708102040201519540401628022541101d4075030f9207494190445000d040c0844000c9400d81c08801908103014209816803042038a0b0303103406a000422401242c22214221359504183e005001e141c07803018001c944401c0c09900c141806401c01d00c0c0c060003042200c0240403464041031317031a00148014540030350751590007641180100703050340340b699002303455410340e01c90f5106140d298140c141445002e005 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 165155413 1250 165154163 165154219
    0x2190b13060218040b0618120115080309040606180302010c06060b0c010c030b01140706050c0f0d0507090b0403030f080c1905070b0106080417031e0103060b1801060e 73
    0x109540315080c800e141c4070085a1203c4241c45645000d03940440b50a0040079244010702c148181c08410300d2081c1480b540b108085403a401c55541e0301d60a090005e460080031003c0c00d40d0400030b6841e10080010b00c400c584080c0c00004c00d0205100540000003502d21407082542c4d42131070310010707078440c601d0260b01038185a000356608141c00305080c025044154080c4018000d655021702010b02c2020041d00c5480314111649d2400d4420404500440e80c9508241d802201380c2442720301d400125140400107411400307002d83d042d500c0300c0a1003841caa100d07400001400455001c2e0f840c0601e19500640804840d204030020b120504001801d552005415a419040784125101d8403054041000b0000e91000000300c607040e80c030350b001103801c603c6404010311440c0d1010179095131071031040c20300e4141d800042100e0040359035800848032201c0103682080c0203510400380400d17511030000401c000c00c2c0070700410a0b00ca02048004001c041d6120740031010101045d502010341d10204d02490341d20a1340b2072 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 165156663 1250 165155413 165155423
    0x1902030417071a010608071710121523010f0e070c0f0213060305011d2104032f031204120507121101020d020f03030105090a14070201020a0e0102190b13 67
    0x243c0000b0b0002d4000407400c2c82a1626031b1038491078413504010040100c020784d803a11040d0500c09003444140400d10100394220300030040c0b01c4643c40108422015540c02c641d001c40360015104018190280d0544498050700b0f00c0e4960442150920700c4030304a03484003d101d01d04206400d1496402e001020840e400c1042e0040c060040685070030b951900600007a1000302d6140d86018370615841400b02c4448594501140c083e140c0006240c019510300020034103002c4628104010000006a001381c1c0300984054070020152103258408000f0388182e1604080c80c065084403203228a42c0f0403210441d000d440520f4010194110a400c00350301d80001d40d0030a411000c0d15048190a004ca03808004200010981c22200100580c420072a181c851101045255520074001441503140141703000754040b08074080080c0c111841c0c02d03442d00d03600083c1c50400c0540d42c0000d00e42c14443c3d03c82e01880d00312100380020900c007030210302d02201d110380651003c1e00159012010601d2103c0c1c00a072030001c07503009 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 165157913 1250 165156663 165156713
    0x10f030f0b0a03050318010305010b0702210132070c171204080d050c04030c031101050c0a06060e060105090315060414070e0a0e04031205041b0608190203041707 71
    0x2d2030a25581c0c5d0081d03064178185210303a0701c3d800e040d41c23003401100c0c1a03642c1e01c41c401d403c1c113102d0380c2440050b5451200341d034008042c0518295141f1024030440c0b1808244070f580000c0c42d100e4140c10031240e070a1100d0500803210500800101039000311100929a074009640001e550a60004006030700400c5204403000000e0f109100600009001500408551a504105c0d03501c443d0664100c61007984002860720340c000404001103030a80822050340081030500398940300079042e0113820001404c800b00d400d80c2e5502c0041c0807400341943e200754400001e00303046180c80700703440000e565040841d40d40c00700300803014001112903d070740e045656a1401004802004e082c410310142c00301c01240f14079400340e01004000103d402a44103442e0203141c1644170141d4882c0b247e101d400150100a009031841144c044c81c580c649549080c0c8900281895900e20f1500c0c1440700e401a031880c00c19201c4440c0c01d005005100224000d0790300b103560718100d10035043c3e503a203043c50001d10141501c1d040605c81081 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 165159163 1250 165157913 165157919
    0x6020d181e140906031b0a05100315090b030c0405060a0504020310060f030216030f090b0d021305040b01051909080604031e02010c020d0c030c0519030f020a02010f030f0b0a 76
    0xa07103005962501540d4003100b00c02100340003201c202258001c0d41688030700c2240b030521039200b2000300c1104001d01a18955a258400320b03254000b54814040002d50703860748030301c0d040001040300d8041d00500505000714888400020703a0341030403c40c0c0510581d0b840d00800c200d96a0844440c00a00340984299120b103403541030350380d0805a510494000c24250100d040d015482482100c800c5500f079042c1e90b286514907141141d5043c40c0c0b5400c80140a0700c5400407418400c158050288088190405070792170b50700302000072884041d0b900150146042031008245e90ba001826516900340103008040651340d01032084901e402180d0003102e440c05441d080c0002c0c55481044034048182080d0400460700c5181c408a0880e03101d01640c2c00180c004004003101d2912850240f88480c1c041c0c0f600c6007502015403502030a0003004080740c1c0b0098206424030341056084110404d01e080d0a002602c1c0da51500d4001800f0f00300800c0700b0307104260f40c80141d42c0c40c40945a000c0f00f82c4910143c40c1018544d2 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 165160413 1250 165159163 165159209
    0x150f0b07020306090c130903021f020307030608160627080a11061602060306010e12060412020607050d1d0f010605120703020a030605090309100c0c060906020d18 71
    0x440303034405078007070b0166600007403050340d00180b4003103558805403041c41403004144010000b4a5050421002c501510103081202c1c6030555035070843d5200702400681c2d900385048054100c81c0641d100a800703400c00800301090f04010151541100c0ca41d007018038000310f403c01d940c004a092845120325400d001c1e880811a981e00050380549a84998440380b01c2540d90400c0024600545c40c105058500d9550348000508041c1d001c1e541000040c140154600151000501c080d2142501804103a00c50800c00c030a112500c40742c3c082c1d01c0002d0020304154204654000e080d40300340a000000140c40345040e0b4582161907811181025560b0141c500106452402e507002c1d000390700c5030f01c1c4114038801110700074a001042d0003048075801040c9000705459691080054180100b00408500041c00202407584071030201c000c072600c0350340e650081090305140400c0d41e80c0d166001042042841102401129000101c00c01d0b000c80034200f0481c1c4008000141e8070f914442d4014030241c201d10751980040c04 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 165161663 1250 165160413 165160417
    0x40f060302100f090611100c0201061d0402100804050a0f08090406060302031005011e030f090206030408030a0f0b0d080306031c0203070201030e0c0102060c0d1413060c02010c05030604150f0b 84
    0x101c1076549031300075907980f12003c0760f00329021034007101503130080f0025406000155000c0800c1d00094000803442d1a40c40d03c0e8103080445004201000c1c400c40001c0008605e881017403240700e080750341005115402c7c191210703a80c5040300b030f00051810f40c51504420030700080700161040e0440042c0140101d5894100c018040c0d001a20f0356401c01540f1301000c2140e42c012600001d0035a050340c94116124031030722084016250740103604050f90355600c00800981c48140c001d510450017031100540d207050155045086540c0110f014103010f2a10640022070750302e00702d1080045070080d608030340b65143c940000f41054540c45d2021044c140c40d50803149902e8002c07010b8030b02e450007601e040040c404410b00c1e8a071610040c21034a40181c11540005400e82106000f518004e08409800540d01d0f40760103070040346200c19501c0c0c118000e94160950308000881c056403050401c44d00c024481380c5105100500540070103411107100c0c2c5e03103030000c16440f07103050500c00008011501c01c00a0b01d9135940300707040725a = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 165162913 1250 165161663 165161687
    0x1c140a090203012f09041b020a0317010819021809071e0305071a07050105010305060f0c0702150a03090506010e070201060e010803030112080904050a0e0129040f06030210 75
    0xa9400c00b65541c1c5072400e80208446030402d480d00312244000ca0903030043c05070303100e17104255001e640e0f5515640145c0000c4103800c000c0e005900145001d00c00d070b04002e4051100464420882c1c2c600b000107000c2d9003008078051103441c80c41011090015070f0b5100081142c804203810851440d05902003204040340002e522080f650305101c40351669000800100e2460381ca0b010191141d401404100a001141600600113103d030462850405500b9a12a801d456080e4425202036000a050081c00b00c0010740e0142c001700c2c8940c10f986000c11941c0891118820030905241b954030120309100400e00a4010b410030781d51100607202d00d9a141c00c4e040c0d02005040d80c0718801503181030800304d41d090701609564142c601001c000d50079030f860304e036a05407020030b10441190519014800700f00e0540700d5004442c0a2040003101003061002c41d03001c907007112103003440e40388130b00b100d0007440008240209007040604010740740401c0c14100f812480024040590000350071580240d08820700c1540a0204029 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 165164163 1250 165162913 165162919
    0x90a0c09020909010e0c0909010905240f0f0a0801150312020601230301140106020d02010b0613050418051504060c08010308040512070e0109020414151c140a0902 71
    0x694840c08800101d004907000560001500302c018040c3d0848042101d030700c80d815003134040c9403826510201d03c3c030386000c2e403000c5085a10b035410310100c1e4218445060000503590000c42140d11200300054015062010180c000c3d0840c0306d040601d921581c8000c40642030010003485040c0c1420f04403845400389110558800b201a20310101d003501c0410041c0c100c0d45000741244d4807825007030f00d070402a007022041c56807540d070f500c44004045204c030810f68001c0443da0003512410fa0245400390941d03408040d1b01d44900030400141c850401a0403880007039a00a80300050b045400c50100d51a602490030003410900c02c024504000c5030b8070b07030310b00c5224500ca2030b818000302c0307125202560442d00a01004102c46d401b03100034003150520b1051582039001c1d130011544a1b03035a0b0030b421803000c4000e81050b0074503a00002d0a00044003590f40302030140000380e42c1020044036402d803d01d00c0e030180030f00031003410340f844458a405a10540000c0903070403c0f0349009041e8204010610000c0c035481c01c040340 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 165165413 1250 165164163 165164183
    0x80f060a0314071a28020a050d0f0f0f0212071401020301030803100b03040b010b07020d14061e06060405010e13050f010f0902030f04031808070f09060e011a0d02090603090a 76
    0x5070307400d001019209125450005c121202181091a0701440e000305c80060451103076003004804103104003c000c80030000c6481d1506000108100100882c000081a0040c000801c0700031500741e0380060039550750102c1d0301d03d15881c1d038054074011700303003801540ca05480c03036002000110620800900550150000c40b44450081c0d036108400080b9010440300034203030380340c1c645c01008a910b003c002070400b240300034501400380290359110100d19000c005803d0701944014208125000264500e101800c90490804150301c0c00320f0008000f031113075020312070400069070946c007010340761741c2c0200c1e0f002e00c000311080c4603a24040d01b041001001c01d12511428810b415400500d110462003224006c4401d4000522265a151000d07208021840da00c180159508080000e4510050100174041d00c916050420158945050f01059070f00d550800c5004c5944c2d180104030700c002e0b072b51410781031201c5e07820b002e51070310790307447c0c4d0080240101d07101c42d030f0040c10020400900d120b0204044d810310788150b40300780c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 165166663 1250 165165413 165165449
    0x607030c05040f08100516022503060c0c021306082517060601020d11100e10020f0c160510080406020d0504030e040e0d0903110d29070c03080f060a031407 68
    0x541020300c0c2010f56000341c0c1210740c07529012440c0b907064200129031010109c401590b01d5403200100e42c2100144400034420b0740d2100c0443c0b078400703d04124285800802d02c082800e00b1910b9440301c040c280c030715901b06605d20111281c0a540000c0d5030081107030ba0444141444240d00382a00d03813034100d82c0c1c80d005014011655074014080c2c0002955412084020300d114181c081503200103040300c0500c1c090611584c640540b00350101d00080c07109400d03803034906443d2070b59560524a42004c0702c0284045043c00e110034440c40e1124045582d403105a0b151003c255211030411200030311410b61b403c1c1c6140e0402c0301700402e00d50412600281c264091760100f051950a0341080d41b2000034003c1c80c800038100c08408c01c0442d0321000000d9044000a2071446210b24036607a5065550048041c20640d4540003280041704421103c610b60010080c148031070504450b40d070080801400410050501c610f4030082855502c0ea00b1582c030103103a1004610b80c03401c0714101100d507603142c207201e41707500707400d030741040ea = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 165167913 1250 165166663 165166681
    0xe01020105070512070207150c030e0402030f130807020a06090509070e0a12170d05060a0f08060c030a14040b01140a1404090f0c1401110f0607030c05040f081005 71
    0x644596402e03555a4109410180440004e14024113103400318807901501052105483d81801000f0329aa1220b6440c05504c2c503000e0081034200c0c210398850307407052040119410310500540e500c03180d03000c00d8040b80c85503880c141c0301c240180c400107900300103071103800b152031a08001d51310261481240d1244140e81e800c0c0c2c04071181c1501040e4207030807681140017000800c8444007440411489002c001300901d01c87c00c03d40205030015801401a56203400030b0044a040c018400300240501180030b04013142012015a65a680601680e05101000000403014110340e0b00c40016540d11000b05807a40c20681004600b0383c40038000c40081c00f6141101107030394945100c1c00c030308517180201c034242c0c801455000c220042c042240281d0350750304009801e43c0000c9040076280702406102012403c00c042801c00181400031115600559034000c010341000e1903000502c0360b034800418030300410064496070044915001e66404145c1001c400440804c01c81404600007024602001040149580b14a10b07 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 165169163 1250 165167913 165167921
    0xb030307110f040f020d05010f0b07050601060c1403120601090f030203060a09050f0609010f0612021e0a1a0c15010302060a03052a0702041505100813050703030f0e010201 75
    0x100440d01442100c200360800c502041030402d0010b1000850301040c00c080c0099901141c071100c0c5e080d82c0c03440140070a0103801e507480041c0c50701198060810395950b48080d036031b401c10b01503241842040031448081048021403108003014900030340ea02c0d14808130301a260500e05940460200307440c4880850300307000c20000130003101c3c1c00400030b000c0703512090b5000b03006103a60401503405000e01415103103000000c00145001d00c8852000081000411071004200e84158000303520301c0e100f8001200140e0b8427841d400b07000503025519440e012420000080c00348440b903101840c0c2c0b4001e004480200d1094a001d840115203480540b0b0f152551040c071116503c8090000a51002d42804622081403107030384040c1d40042c0708601c0d0341429008251342d02c0a400f1021480f400000009040d4046090138041c01015401e9410b4031510b090528001668800042444104000c001d40c00504080d40565501748481c0c0c201c410748a6954030780c10000c0c540303080d080d10036022407005075207044203510502c1 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 165170413 1250 165169163 165169177
    0x70c0603090605160e040b0f0a0609090507080c0301061206210c1a0304080a030905030d0203090d0311180f0402030901060e1602060a111b0304080708121920010209040b0303 76
    0x341d41200e6002050401009000e8103013490b0300034041d1704200300d8540750f2451303c1d402b40c0921345441c00b13032615149005c826124000d00c4a410801b0340418411841000c20a5a06491003402c0001c0348550b4481444000c000030b5002c940030081c200440c0d03000250301e40e6106203440c06030320310022443c0c880e900b00c4014034103480303000443c2008200040220714448041c01015910b0315000c5503602e86900c0305440e503000386060450042d1300206000c0105400c20410800c20101c0c2014014880310075400d080714011610f44072800541c209491402d17503108940040580d000410864907800c024454038000c1440b40038007210714507100c0201d060406145215109040325600400b0542d581000d410b01810006850055000042c0b1800b0f18800360303c2900303112840940000c5895610304500d0900e4008258031103400340c1c1051340c1410410110100b2035016940924489001e02c0003000704039140c91415500b12141d079920010303a0b95a250640080c4000038013150180100c202d4070080548030b100e002 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 165171663 1250 165170413 165170417
    0x607090f0815010902130306060305010209010906030c021509011508101103040c0b0a09050306040b070801122001020f070e090114090a02132408070905040c1703070c060309060516 79
    0x2e401000340d031919800801402c0b014a840c003d840c1d0b41d0743d450f60306603035080c0c20455141c1d401042d0a22196401110b0301d000340b1140c07034248031044038664069114030f1120792024a00c150500000c1c0c08441c250042e09200780607030000410150380303200d1141c54154040c0c90101881c01d0001e905405100c03042517900075a00003001445030b0b40750424850701d5510112400050080000001900e5a0b0030b2100611590003410240340300d28103404000e040480581204894400240f04140400c0d00713900c082c0c40d0a81c400f440402485c1302200143c0c90905180740b10b424038070502a000c81c0017483c4c404a9401100b5000c0240181005100c1e0504540d40c2101da440103948610301d80d03405032801d82c80c3c0d400c54141040c8002000c1081d030030841840b04107a88004c4100340e48035001c0180348030800c200300081041103402c10031800c055480e20200c004030f110b007200d41d90a9050312280300790180119980554001840085140d4507540640508070008054400350f207824005802d62041503001d8400512503 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 165172913 1250 165171663 165171703
    0x10b0a061e050f2b0203010b0c010b031920031f11031909062408070812120912190807030b01051903060f0602010203180c090f07020f0607090f08 64
    0x180c0c0c0685401c64413015041e01e1303180c0820350710225031070b00c002c6000c0e0005000d01540c41d03481401c00c4d0701350f42d810000c050007648043c10310103209080001009007140d1080c4201a0a622440b640840500e802d81107136040c06692246002500d4012030303404408012441400010140021030b100380c00304440815140e00403800d2109200c10503031180f40002c5c82030074000381d40c0e10013038180d8100f541a02c44c4110040c051100c140900c40c01000301d80018500345004010541e059001084140940c0b842e030000c40d214a00800c0144506001c3d15075244076500040340c503246080c510201c0c2003170306a8440040307903d41011400480c828003814000c0c0034103031242840c0c100c9086045046a520301240030030160307504d0022955180344e0144100500641e030025859090214012004440038006c02e0710b242e2040030071200b83c0e1940f6100a5002541c880855810754600340280d0804801107014406805100c042051454114080d00c00f41c400918141d911140c40b00f20040d642c000e044200c1d4629481 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 165174163 1250 165172913 165172927
    0x5040f03080916030302010c02070503030f09040509150c03010320010207060e0406050402070f02030d090305060c0a030906150e1803040504020c031e03010519030b060405040203010b0a061e050f 85
    0x10740780982d04507402c101101c801d2128920092882107064000b10300503510344142840003981000b03c40050581103001d103186c40e076090905081407103504000d601a83e140c1e1300043d610700051015500c10482c003070a000c03481c60f090940b080190b009000803aa03401c2424001e4401c50389c10b1030480e4a0203c1a0010000d05007071420548a00c401e480400e60301503161840407955444a00113860303481d20072511f100b075030400ca2040508040c02504d4240802c64031180c20004500c3c001030581d08490a80309071540c400140b0300403005410590300160030141406d503072520790907108000c90210740314542c0540407521807514441a4017154501b02d03845900c280414815880c15a000708040d455402c02c90740b13800e414902c00704900d2403206614a2008010004001c2410280040c0c000c05541c0e0764441c0846083d5641e9000700c0d070028190798001e540d1070001408640302544482c0743c0c0c0b10300400b50b001c400d40e1080c0003080c02c10516100034599101c144090502030040050780d80700052040181d0078100 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 165175413 1250 165174163 165174167
    0x50d0c0c0b12040f0203010b151e0c120304030507020a0308070501061a070605060a0503070e10080c01080a05130b13020f1009060f05120c09030c03070f1a070203060906061305040f03 80
    0x28295001743e9041d5610341101d215551a0030007502400703151034010b611800c0849010500b03009000c0b0f5500c070182c0400c011882400c02058580080c90726021341a10f0340ca850404543c41d0080e0000203400807c0344c4804428444140c002c0c08115100741c000380f2215484d07942080f140c149442840d5402c81050004200007200380c4c0160b0703480300c0080c021074101e540c0e44001074a020040e0b07000c00f00180c81802800b80107030040b2060400b0303003484001828070100740000209200401003504004a0b643c001003070156030f03005105000c4a4120303a41421900f440d21a141505d01d280300224407030b00800054900900340000da0300165441511219800c1c8d2809006580240c040c100c010300300082000740720101c5900103402c902941d14491400d0300c5139511818503141c90b41d5104a00d00c2a400080200700709400c1017101d406698003010415002e480499084601380110fa000039454001c40041084441300020800d02c2003504480c020180c0b0700316031f135450440307505480150140c10402e2040e03001c64 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 165176663 1250 165175413 165175433
    0x20a03062306031603020c030304060608060108210d0f0e1f0b0307030f031704050606010f0315090e01020c071401090f0b07020d0c080f060f0117100f0207050d0c0c0b1204 75
    0x800c3c17810b01515064845404504541c021501180e200b076881e03074140310340c40d800c000c1d8070301400f801001460421110701d0701d1503041100171044003040d540010160f041c250940c0001400014450083c04501c610400355a100c4810f030130b0343c2851603006415003142d03400c0380c0500c0b8a07517a0098080d000090660f119a4080d004492080c0e081c00302030071200400c0082119007038401da00400240c0744c0c03810130390001420388020795100003c243c2015001001402003030030b050100c440c2d003100012204030400b9024062300400714a04054080c40100150400c100c140002000e6000da030340210154450b903c000c0da0501d54000c011480300140000360050410480503a1142e000c2c181001e005551080e115103007a107810461600342e00300106101203414166802c9016200c4c400709a45166000e941103903981c2e180200c0010700316220f807510801c4c001560304a61700715800c1030989820052450707028045003100401252296801c842c00114002c110302074032004503466651103850b4649840e04e480035 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 165177913 1250 165176663 165176701
    0x9050409030201090c080a15140f060a0503030a090e060d030f0e0d060504030509010806040b221b050a090f03030807030510150c0213090209130c0504020a0306230603 73
    0x7541d66000304c0e102003502e101d8070f84014200d01006000c65103051411908010004610072015800d0442c0d440d0604c4540540340e600100c446110021a664071f000601e10901c9580025094080001c03140d80841c0d11a4095013607070600311008003561904401d1244d50300900d50040c000440300b003803400e1240d10070f2095103008034008003903d103602000e072900801c4a03000d540490115100003000203589d40c0200640d07034041000c50341001000300c200c010460300351020f06101000843c2c1550b80340580d9040c0d0140d000942c86200651500851602c042c002d0392040000b4008038501d040300007a41d842c0c1c080580d065030351594a14105448644e025805460040d0000307500050449012548052140c81c000c9071103482d0380c640803540350900510000d540621040e2400c075040100381d4000d0703210f0040c00e40c1c01c00b401c00390300034041c41c07503082c034100e0451150800c0d03078014000115001190b505030002000e42d007150034288441070702c105c007c034814a0208081c6030000000e02c000340d2101d620500840340 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 165179163 1250 165177913 165177917
    0x307120204150f022103070c02030321040201170405030f030603030910030b1809060f1008070f090609020313110118030f05010b0303070317040204060e04030c1b0302010905040903 79
    0x406440b201d0700492802030754031100010705440d0710b26244075410008001c0e03a040c2109010802d803030851403441c0905c03000381650148440030340c0c20400c5440401c1103c401024190b04904010100c04400c0884842078405a0024206031000740400e520028100e002d582c4c000d0082d858240416000019030300010602039050000384026112038239100d2140024024aa90008209034078501304500310182c0c030410320710519881d080141c202c40c009a074681001074081200c000d5903c00540d40c1c0503418580284800d40201103000441c404025642025207400d0a018811070b500c414141080740011102c00d102c51900700d03440300200e18494031a1140040c1071400d1201c4280c0c0c12240360006071030358001c81d1544202c03c3c0a40074082c007880364050403101100038500d8070009403002031800c00075040e4003200c561f0710070108086645581c0880000c03d0424010f820324945400c0c00781c13002254400c141d89402d01c1028801610070104200002c2da9416142c510b021400c200c1400b00520a480701202 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 165180413 1250 165179163 165179167
    0x90501080c0a240f111609050a0b030604060506040b030f0c03100207030e0904050f0f0c040608070509040b13021f11010b0121020d05180d0e0d0b1b0f040e01050901080303071202 78
    0x54180002c1c005186d080701401c012200e40c514040009044843c001c09a54440c0e2510854a84c51740d4041181c0342c007d50095004a110f8407140d00240061043d00f00140d8144100650400c07089404209462880307812030540f400d940600d0650700c2640725584000340041d030004560501c0e845c02d5468190000c1c023034000c4403d111103010100d458040546082846a800a02c11640520f414000c40010f841c9a5014080c02c034585804200781032009400140f020010500041c007604044d100c507c103254009000400c002c030395a403044402000b001c6c00400007441903510400544050180090000d0306039101581c2e1402680c48804010a04c0e61480840b9000c120080305440305015850103180110801c201c00c260301d1080c01d10706600441c3e240c0074000d04412161141c0d8031004103991a40d00001d02d08e2083d5200c08106160900810507035208280200701400030700c8015010b841a243c039501d20449990301c0d41d00b000044502481441e4950348104001905c02c2c0c442c1000345074080e08540058 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 165181663 1250 165180413 165180437
    0x13050702010b030f0a0c0b1806070f060501030803040b150604051003020c0a0305041d070801050103110c010c03050a0f020f0304060b030a0c060c060605040b030a080a0504090501080c0a240f 83
    0xa082200001032241c466200794045c0701880f90120a6500601c0c0c5039803500d00c1d051140315071964103081d03005864495030011031380300240135015074441002e0782d211030200055a141c3c50704007042e80041d0380a58000c40344100003004000c00d200070308038544005041508240c6041c3c10401d0301e85400c00807000701a000d01c011284d2207410015600240e1103a16826216820620201122580f04002d4406c401001013806101a04640264156902841d0100d2144c01e03140c40e007007880c407600d2401140707586001012155580d244d071009003c0c241d10782c400e1001ca0042049401039000c0c0a8081450650410200340003582c5580700d0165294041c0951780480711545071b400144045034850070106404401ca181044514844d04002d0308003201e00700403100c86074011903600c00b500180203100700c4000071450012070081050301c00070072010720240915038499001d10380300c034041403503e0f008010f04107000c994510703800d91000006511150942924401f210110340c8440402840380500807460818 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 165182913 1250 165181663 165181669
    0xb06040b030f060114030a030c0305090a24090504090503120a1107150b011e032403060911030607120b010507020612040b0108030a0c170408150910020913050702010b 73
    0x40e540b01c0c01400ba010365032620216581d54500d80c14954825040841840002500440b8807a803082e0103207070481d2160300a1003c202808070503000740201000000d8859102d0402c400054040503659507019078450340c0b01e00b4801a9006041c004000307800a001c0c4c2805c000304040400e501191700b20021808040c0c40104003080e5002c03c1c020f459004890650040c0402d4502075045607082c00e107802c201c018440500c1880030311915004c4401c042e12035104441e506001c0f4410b48a40040620200c90a95030385000c0004010344001111418801e44210f1201c0c540450a580714400d15105c4c125601800c0f49001d0080070710840c11410310005011523805a1168001307041e0380700d00000c0d90440c40c01c0500b09884980c005900901e5940d200300012403046602107078408066510203418254a280c903480360b80680a00c0e0052101d80c40340f001c161052841e2081d81d540203030300100584032614401e00310f14003030740b0880c091150020718201400040c0f000c0307a4010b0354445160b100001d4411008800 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 165184163 1250 165182913 165182923
    0x120406090b0918040b0f131e020307050a081501140a0317070501021b0f0601032012240106030e1f090b01080c0f01030509060a0e030f040f090b040b09040b06040b03 72
    0x1003a96101711035003c00c50010307001881c0640203d1004040c580c990180c0c0d40300d0742020350744031540d0002540403520204544081180e076020f404010940b250322911101040e64505241c45034014126001000043e80d2018007116640050040c207600c48003421512900000c1a03e0961071165080c00c02c80c940216100384060405200541c03140380030000301748402840d00741c04086801142e0000c10042001914064229581d030300f0b50122070320f210b48501c1c00600890208451140c6a000c2c510040e210307030201028113003400c254a00902d03402d9032580011012a940340300b9030030082c0d000111a030042c1c44407a1020340042e070040d9020a01c00c18550f2401c5c0120300c20f80c00300c4201e0b8040300070541e4030f01d082c0000c000c2c0500d080ca0704004925003441d41030350350080030700649101e5541e8210703100400c8040c030454a2841086481998481c2e85840214940d659072141500c0280381c12010007191a2601500c100800000c000d1034168403151215030080202402542d4080d58544a111007600c3c1805 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 165185413 1250 165184163 165184171
    0x10361203110601140109060f0e21030d0c020106170a0807060f020a030b040e0d080c0702010905060a12060b0c1b01020f16090b0609090406021e070f05120406090b0918 73
    0x6136510103421100d0014200c864680c0020043c024009000c10300507600041c0b2010280d070440d403c0700001c00020004400c003c2c80650316070980000504070b000804150000300d40340302c0690013004000d50f601c15500c030781d80e02c081e001c54290b08140c03200c4011914160103490803501a5100103039190b60100d006049038030840012000c262900241c01e12480c02c2d00c107242e40703165040041c04140d2000702c401024008028040c545031100030401d0b00c15a4070030200c1d02c3c0a40f1014000c03e681e803c2c100c01c080d040844074521908198100f6030041030f90076048080e501a1820300008048052550080308040c0c4072030176080b41184244421814006000c01c041006203c2c10f2034500d013041d08212445c02900d40c504c80c0c903130061004100c14403560311500c0f00c403075201d50040d100580750107210a42c00c4c105100f204096613175410204440d8244003080c18095485841002102d2410031401704114541c0214030031407000c210b9800d02000b50b00d100c1c5c0004e200100b8014846802c0b00940e002035000001c05072 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 165186663 1250 165185413 165185429
    0x3020d02270102070609060c0f15060f0e0a110f16080310090b090105030a0f06020f030a0203180606060409182013020405090c1810361203110601 64
    0x700030500656014007007000501824600030b5452418010040d10850b02520300900310490361001100784000c0034101420840c4108003404010754034101e030200521300d8002c1003402510400030501c58042c512a180a45090205050402400880075901600800303911820031300d003800d400001456450095115007031a0f1043c01080341803a21040c200c0742e610301703003500400c4404010b00140da0005502d0640aa004408107080c0e00c5030314000019020b10040030441d5a004002d10030003810b5900650b12410b80039400449101070300d100705030785617415201c01e80c200000300028099040b154021302c2e45044100794801800320f566aa6640710708072003101524040d20642d0b9201245441e01020b8014a031494041d41001e013400002000d0a03006041c100e000c0350b0020f03101c88543d11030080c1000c0369200038101c0301c0c0050101c02c09007101c4440260010101c8140d240c00303072034003449031810850055060702c00307110380d00b02103281c0045070f06803800341c050008100050481110411519010b0440c2e0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 165187913 1250 165186663 165186727
    0x62e050309010605010234080d05120703090309090b04110304110f010801080d031e0c0201060509010f0807030f0303110307030b0306060405010b270406080304050a09090305030703020d02 82
    0x955042400c40f0529040b090442d00454084220b00b03a0b40015503003c20343c0d0f01d4400044001d544540f1141545550210700b050068640c5a00b040d0740200c090841e14501c685001082c2c3d0f00c1c040100d0840ba10320b2402004244481418000454168410494100c0c00f510000e03a40c28041403084243d002143d04036900c0c0307084416054641050300d000540d080003070801401e5541000f2000380c035140305002d01002c2607a0389001800c4900c000b00e000d15140c420800800901d0910390b40280070b4070140c090307140214912800000d07907207410240b042c00c4801c0c54024100e01410343ea0383c0d624409070183d0540801d51189080118001300c4002507000d0070141e00c3c000b594040d450103060030540300504551045240c00010055030b02020201e0707d100e0f03603258140400101000003000d40c0119015115041850000c02003900000000200309940c1e040380c1510000f56a1580705081d502174246c020b00103542800071600e800e029401519a482500a0141c01d0a403403103440c6100c91001000400c1e1007403d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 165189163 1250 165187913 165187921
    0x6020613082713140412020a1703071103030105150906040b03010b0309010612030c12020f070b0a021009030c0209040305070f03090509070801030b15030f1c0f030b09062e0503 77
    0x21000b00001110062811311011101d5a01c03102000030040000d0a41e0f100c8440ba200311030710034000112000d0340705030741c540d03201c0704034034015560b0b08201d41d480081141905c110700840e00c00403e803412190010550381c0000e8a20301510300303940104194079005601440041544603030040954081e012410900c7d44a150440b00c107420343c2d11035409100174040d040c00d9200400d50004c500c407032460300440105800034460304100d2800c41d6106c202207450040203c0401c0a414890040038907038031303503401c0741d03145a000807036a01100c0c014200280030404500303040005040285ca2241c1c028005d00b051820201030751107000341264441c0003140046ca006c1d40a121a01e4440c2c012a04080071f8941161191304580e101c00400790007610000e50321300800c0080c1b0083d58100100c10033f010005c8151107218810350b070701c40e0180d070174122280017044248100003c000e00c2403060100d942001041c0740700c140c032120f0a01000c01d4900042881c03988044210740159440c03078107480d4400750690356943d030b2440c0c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 165190413 1250 165189163 165189169
    0x807090902150a050f18221d1c02031308070e01060513050f03010b04151a0a170601110313030204110f0d020d27050d0504060206130827 60
    0x40d44840c203078204800e104110840d640301068400803219951301743c1d0b440790407081030080d8010302a9515070002e107070b00c14060701244030a02156402e0000c1000d110040740700105c41d04420302c0707100803409603001e00d0060380c4210980d640c841c441841401500d1400701d415000c685001401e030401080e540c8a0103040159034500445035004040625065003040a00c1042c0c54101145108080c45554501d001c010142d800794407520b40c03204024010003040020f40307010031954096100b844c20142d5541e41d40e50b64001801c3c21100c400300e40e5501c2c220f04e110402c04e135044600e0040c04060410000041e0301c603904908100600f101554204980c10242c40e510411055880d0212021400203040c444910028080c0d0141d407041c0c001004c0160301e030b40c040d1031000010030907459200303400888a0407110041001c0064240003070700590544080760108141660756104500c0303014011390069001549900e1941c0e640045144a10105840e1842c1c0ba40f48106034440c0004030304030840980900803a81ca = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 165191663 1250 165190413 165190429
    0xc3305090c04060803120a0b0418020310023f0c090a061d0607080f0703090810051b03130b15040e0a020315131709030105060307080c1302040807090902 67
    0x81c0215000d00c115030901d001e05840307004600001d020048074002044414040d904501a121409401000b0400701c18000841c4042c4004017603020740100d80c0d55803c00341c0d0500840303151341e1310070802000d5a401d041200e150403202400c0a908840391413206081c140c1080303070203400394040e2201e00e03444440c0b500070415842615407280c8148052440031081130310300d1442ca55006402110459115412030a04990174070070040a0240d0090008a8a08054101e04a03400356043d40080324840c4108500440854500b80c6000c403403526403126040c05030300d005000396803011306901c2451038403516a54501c1c50075004d40e90240700f0402d04100c80403030300306841020800800c1c08010301d0078100383e8010984030000341302c003007005044103400074809900100322100360750342c40710701d0720100500b218081a0a805c245c180a00c02e5080c540411107600d000222102642c1001d00034100b49107052080204111090000c2d405164081c8030004040400303011100c002c1588100110380c050562040040003 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 165192913 1250 165191663 165191683
    0x516061e0906030b03070305101e0e12070201030212040309050f041506030203061c030315150206060609031504050c12070608011406040503010c0c020910060c330509 73
    0x402411940440e2903940700c64a141210a281000103804020802180c1866495000500984034481040030518036a0780b11701000440002941c0d86044103890290a03078403500030800c1254440001010160074400c010300126105040042c90700032490110800010126415070100380c80a00401c140d082c440c800680105003240e04000d1034460360101c20801c9050b0281070308040e170101c0003406645038002049000c1d0080824414850710604e8001c019001c192040c0b030144c010b000e8001b695066448400b818540b81d90042c055aa48620910850742c0000d95000c2d45032203412601c2c0c2185a032244054055805400581744013000705003400b01c0c15034101c104030306544c131121042010550001c0c2176815100d10803111084c0a01020000700300d402150886641340d4a0500b261250540101c21140d07107610a44040c035890313440c40c2c0c054800495034800d55010640340c020381c20000301c1244511903170404060305500c00e42200d0b085200c40408803466424000c0d507910511020301020000d1201c1 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 165194163 1250 165192913 165192947
    0x1e150c0308060418210e0109030b070905062d040305060a0507091a19050c0604030e0d06050a051e06130209060705070e090105060405150904060e030c03091503060906120109051606 79
    0x124060203000901e9145a44006003102c82d400c80840d4409119680380300060100030030203a120200f503980211390070400a40701e00703d400c00d0035002581c3f034031000030786017140e8114000c0c2c0420b41c0c07400890f2020b0b10300140a4820082842c401069107182d40351500844c800303104500e07403611030a801d4664002181160f44050200a0005079516100021780b2980a541740c5402d101c7c50a006000c50040c1e41d01d10401030905043c035040000c1c1201d2680060706c1001898411113134183d1001c1070140c0c2c5c8078149c410507081850000c4445030301040e070300109612403000d00030b9883c0c10f4560320f0f983d00309103c6820803030354102060203000c2c1d813000900940c3e8003d24126000c10140c180b40410b404c911130010509400740e00500006030038030140390b0040e07108403480710a49580e000ca00300829203e44c4074840c014031807a02d405500000c3c440d468242d9114070070107440c07020245c45600405c40031425074000c0c50403a41d00c0342c0742c040020324284110088041036841c0d0080345800c1c4140a880046a040c44240c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 165195413 1250 165194163 165194177
    0x9090603051c05131211010f02060c1608030108150c1201090e03120c03010602070f0e181006030308010306052212031103011e150c030806041821 64
    0x201041000c59003a54680d00c90320450b1000c4160303002603502c0d0055207103d612514800d00001400680c02c98402081c6200744400321041340c5d00001501e01c1c4003581d01920050744800c0015800ca800c14006215040e10055a0300d0941324a41d02c6692962007608588116086100d00c80f4a1130232170309005403c91043c05a082c20301e030000d41d01c003d0b0302e081403207044607054944040b600310311414001c070303003c104080a21072214541156040825802032003000c00500c0340c0d410014140402d02960416640b0300449105562100103089032000300030100540d00d0b00a040c140171001000e03114900c001d40c82612100800e41c5141440d0303088804c010b000b400450081c00c0c2c039804c00d100b042c0e420f0006550000100c850817200c85070031030003000000e42120010400100101d001c0b070100c90700b500d41d150010603880c10603485400034032130302c0b6004603141d0100f6021040200001d000d9514950300c054050000682440b0401c0008080a0b1625098502040ba0301d0601510401c40300810352140644c10800e0b = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 165196663 1250 165195413 165195419
    0x9070c1e0605040c290327010c0201090b22080f1209060103020a06080c070308090111160b100503030d020f090411070201020d0f0e0913050303090304141504030303021804150303090906 81
    0x145c82c8402031410713411400c0c014017014950000358000500c1c003403001c002c21007941c0683c4043d0003009500030590340c0e10320b034900141c01b640f50020881152460b0740720b880e035240d10f03a9986890f103402078441204141030a000c0c115084071250540740c1b24074252002080294518018020800c449402070303410403a0140400c40c01400403400c681460b0750615061046585a110361030042100010140f0400000030b031039402280d5002010010900400c40040301e511000148040d540b1540b06240c0c068000703124890304002a0b50190965802e580c2c40c0c6803410b114900044d048400022003c00400070118500c0c0955034104500000d0400034103020030b0f200070012000e00f80b00c80412000b48504550340c000b86005068880350103000303500004890701e030300700105440c0d181d0f08940641072100d5035100d440102842c2c0703103860b0400c101d40801501e00d4981903803021006940401c5001210881450349070030161100d10824161a1005091030030705400c5190007020042c19522040c91142050024 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 165197913 1250 165196663 165196739
    0x1803022425140a020a021e1503070c020d0c090f0b0105091009030c03080702030d0903031b1b03050d090b030415090f081309050609070c1e0605040c 65
    0x7040604600142105055410761811030740900c81d80c12182512201040410006400140c0c0011a031310840b6040d4500c46845184030915800188042e40000300406080c20315048000a6170825500e2030810110361150f00440c81100f420742d13003190903000100e41040254058803400c1c010b60f05850041c0025459800000c01038041c0380f20003481012004010140e0714054085a401554414155003820741c2e2420240159080000b00740c1c068050041c5000307086108010340b106036641a02c41c42c0b000320b032203502189401400c0a045440d1030035203c040b8201e5041d4103260009500c104000c10f19403c03c0c03030008010750b40a6000c4203c0c45400d00034003000800b80403403901c615102100c00a85092141014001c001d44130402800d2908001014025910f81070105016101d101500f40541e443c0e880c203010300d01d81c08585040000364406e40100c00a0702a51652441c42c3c03a5501503c5024620b403105000c1391015102191340c070036050810040e038441261114004591038078170141480c152404 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 165199163 1250 165197913 165197941
    0xf0a1103132d080106170f0607030545010b030307080d14040804080c18150103060812041e0303050703030f060b0a0206060f0a050303040302010507050118030224 71
    0x8000c0d08802d03030804a010104050301c4054002001c100b45242d05954038011402410f183c01021035a0500ea051044000000035003031850408050050000760b40e03c0c8001c030001d00001c0c1c0003c2c04601d070754101d1001000020000307082421984500d501d48000d0640d120000350f50500043c04690502d842c10710f4541c1c0c04401d079940c081d0001c8840e03644241701c07010300f40201143c0c0d48005040c1854428001488032032070260003600c079002c2c101c0701150300b02020081181010480004083d02c9600081d811042a00c1592034035501810042080c0b9204d00502d41061a9040600000f00d0081001c00062003604000c07080b1040482c1e61000322401c540f401040e62269a0014040c591501000040f884240c3e00c004020254020481e480f00c054007402504e840007525201e100305890a882840e516103d40000d007100c00060083d40780510390f03801524141c203c040c080d6007035542c40f201845a04c5c81d40314041801c034840d40c0a040d02d200a040070000303920310014202c00080240301041010000d00354 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 165200413 1250 165199163 165199169
    0x180504181104020409151703090a12060f18060609021e071b0905090607020606010915030603060518121602040e0c12010f0c02150604110c030f0a110313 67
    0x1092066440040d01007030180c426075010b2040645048080d940c46e0180c00d20080030f80341c40049801c0b00702e544504040da64007554095940c040c41d815401c020450700034500c401c0551155001190841c04002e90008491240c00240c0c04440d41075000c404000d030754861600075010740c00b000c5081c01c81e00240d081c142c416401c0401400d040020f129800d10a940c661310b400404096125050140c554075550040c0400352800325440c440c0f40081401e1600105210784100010307559502c640d403500002e42c0808031440d03008401c0c15580d010120100e081405824031a05855550054503890020745030718040b00b9503040d070b09100c000d102d410012a00c410900300d14640407034000c0381414061010780d007080403121280e9031040c407548100c02011419005481c886928403000c000101c0040b40907038850800c888010452803d000006003a4503003580800c50908011229a0401c201540100c2c40c551000114807200c0c4008500c0c603402650000c403110074504030001950801c1402c2103513200740c1440d40 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 165201663 1250 165200413 165200423
    0x41818030302090a0b1903050106030b01020c011809020c0f150f010905060f180709080c0306010b1e07030903110105090d0f0201020c0d0b0612070602071701020405040c18050418 78
    0x44007401c3da900c200c144030107020300c00384043d500c0d480d03a20181d010a2000b659500400d00744000014207034024443c01c2c59169041e0064841d010220004503810900c0392402500000c1400c2d010400c071030248040c00b001a510002022100507440e0038601c1c20303445960f075850280004007000007a000b9031018604503041c0d5800801d0b00c0e1900c2000a540b502c00750b1810b84c20181c9804e4240e11008007158241c01007030f486d10740889550303c072160f42e504c9011b160051a00b640c4042e004002807a4807000800c0820903e000100d0020402e405450b1507921212081d00050049281442400701c0e11245840044003400c045203000013040105866800c4100060440e081000c14070083d03900a0124900c4000001c0c10005000721078074200600c0ca80585034035001f241810707103445601e840082d608041e20075580041c00302034038024002c24600c40324181001195000d00000920380c03a103020301c520b08112034550440c0d022030614800e80e040c0240c1c0c0418800c41c1001d407000e02054886849803c80d582107 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 165202913 1250 165201663 165201667
    0x906150d080c030f0d1508070506160615080604141b060a09030204060b0c010f09050a02240403150507020c01052508070c0602190c12051501060302041818030302 71
    0x3410002c0d085000c0e04914211445000070300c80f088540c15030225034a606082690050a40c4540c070407a41d50300b850181d10741150f02007040d02000400903141d241d178948184400b291130420025800c1d13601c0c04c00d901552003603002000f84000c00500c02c116102e1401e004008103144a1924818408c00c070030031042c14050070700000d2350345030349214442c03405c0615000b40c8140076641d07444034255525031042d101042207520b0544080e0805082d402034803000d5030004001d080124840e001c100d003958001e000c0d1f181e18882c0900c0e180700b003001c0d030000d030000714000c2c0441e4420641c40e000d90340c20f540006010108541066400a22503a0420151226103c1c00b08804800b000010394000004059070400b62065074003250841c100804c12030304105490881d829a80c02450325040c0d14081e060882c8000d140c0c01007600107011420200003110076103030051045400c10400c9254030f45140c0340a80203000040d40000f01400341a2088411600441180d201004002180c3c0545030110032800d40043c201a00 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 165204163 1250 165202913 165202927
    0x905010b0901080d270509060a1d0609010602150403050d0204090e0a05070b031303080604021903150501020a0312050702011407050a080109020306010c0215210906150d08 75
    0x940c4000d514140160011605584564516070340d1116400700d080018040ca90440b40740110300310755903c10303440840110744c590900781044450316000705540e4000700c01400000386980142c00104014013501d02c20011070800030103001c0b001105030049029980703c0e46030051082d400c8175240b5031082d0189056612003c5946604e4081e06c41c550004000a041c000810050140483c01460319032040088a090302da07102d090f903001d40401c035422450307801d0078001c0401103406900c400386c4c466401800140b80074080302c640074280001c1101d42c0c001a94030100d500e010751100c04800b01400c400d0005020801c0130f6a4000c0c003204000c032a03104a00c0d190400320718424006d4000710b820760744195403007203140f800b030b100140540c000c003020000040c0c0110000812040a100b124040c4006039034204880f01c0c01d80074460060001c0441540c41e050400c034001108498004002142111400c1503030b2a04107000c2d2946040c1c03001d41824600302d200b254619043e641d0348608454070358044451510380b40 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 165205413 1250 165204163 165204173
    0x60d02040e030a02100501050a08030f09040209120c041d19020315010e0a0609090305160f02040e0102070201180e161103030c030106120504035406020d1209 69
    0x1c162001d0301988070100f0070380495074002ca00303d001074080460400c190707030341e13502000309900443c0f04000300d50b00200320b00030309031076000024401454040e101502e80a00d64010a0300e420700090180f45039007014860000a00d4140588851640c20680d04100006400311441d15030000055060f03030420980384980464a0038410f07801262000181c1d0710483d07039545005422064102c3c0c8000c40d0740d18000011a051850340b082058482d01030381c815040c110700c600d1100b4141c5038544140c0310440ca214200006a07120b0081d080700020351400580c0320481803001401d06000c1c00c0c40c40150030001c000501031070601e2401650f0040f0610103c440c41e0140000681e031210b0038902c081a940000003c1202c151019401981218407030354801d9040d4000b2001e00d000c480c01500c000300018107c40c48060890042c3c074070b041e104001024045040411004056850080c06200044181c11310f1000b06518094601c0c541c010202400645070070407000d60010642c600c0e00e0b046040390b6546015030020b00c5 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 165206663 1250 165205413 165205421
    0x1116020301060b0c0609070b0a08040803070c020406080709140c07060507051303060501031a0f0f06010203091305010e0c0a0207030b10090903081f080601031401110304080301050f0a03050303060d0204 88
    0x11000d448603900d04072501c0c460703145c050481b8141c00510410f000007501e0b8403950111800000942e82d410210307203440c4d6510140d81d20241c01c031010841c90309451005070792188500001461804020300e000d910b0115501c00781c440741c080d00318190f03840b003041110700d401d8181101c613010381c08040003800340c2c0c4640054a503030040c459500e0304021200004010044182c0c00715040c1e138000c1d01d0046210040440f281b8050710100c0b201c10740c6a0000b0f000c2012013207049a1203030014070500540c0c0c10052510003040076420390f1710300b91000c15224401000042020712200303400c00d041c036684910f46a038541010796a01c003a40f10080240324940000f6181d0101c4d089070350080d001c07102d028881285141001003100c42e0689005901c03152582040f41c41c0507d0040000460358400080c0c8803d0380396445018091091110401c02952910b4522028a03080d50007148118494080c11307489504000500c0706014010416502414501e0005c1c00810382c00001c4e01d0b4040c0e0f046541d140108581d20104d8068 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 165207913 1250 165206663 165206669
    0x181207030312090302100926090f0603270705060d021201080f1902040207020d1218050307050d0203010f050115030f0501060903081602030f0a060509010b090612010e1608010b04111602030106 84
    0xc03401d02141242c8c901c41d448003e11407102c0407a0001440c440000c01c110b181d1009495503020741040d519100341803d01082c2d5031607410311401c03d442e0750687d544086041540100b062405c11030380000c11243e902c02c0c02518601400f141d200821484c2002c0100c60740e01c084660b500714000c0485941c8504568035501254545540a42001d6004186140906403050030722888004258482d9040c240c0c40503134602c95088036001001082c070f45150a0500c110b0111404043c2d0f01765403a881c1c2407600c0c0519004090091002140241581004500c02022600344a4034103811505010040141c6980902d00c1416070390041d04c4c16030f8440410b030f030604404044090081d05409610800202c00030085808268540501c0b001d004640d5099060703400c8a910182e0075510581134000b0500707130708010380710280d225002800011401d015008241c9004880c1000001c81e0310039000502802c1c500f07001d0038041d4035060350103200c04c8000c06c4c8080241d02601c00f460040525144c443c00a540d0250464002 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 165209163 1250 165207913 165207953
    0x305040b0f16060e1005040b0a0b0102100903090810050108210702090403050d140408070f0c08010501030807120215040818060d05100b0a0210021812070303120903021009 75
    0x1607010518103c005006681c0c4000d4043c01800c404104000041c01360754862039000c6002e507102d03a100b020800c010460756405134111300c00d2180c1000995070f03038420200310b64029141c01524501d441c852030726003564029442215410100100141c1d0000992540c0c10703180300000a03029809c01024404a02a030b1030040d5101c40081c00780414560040003e2020a141090621100d5110380151003108425030707009101520400403036000c0340b03000410340f01c0d00f40700b20340780318070280d40b28070301c5007500e01c01c0e0015580c44c00001070060070802461444100c8440500192485541d400c0c0040d890580c01000074060080002c1d0522745483c804e414450240001031400c0d48645031007030300701c008000443c0c11000c030f021541c0011a031240300c00142c4401c00316580c0103084915042c20071a02a4118100161100e02d5100b0030500d80d82d10b890400460740850f000401c030091031402c00a180040440d020009030345080e00da00d010035808100d00241c44100c0a01050070b448078a00100c90030001803113041 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 165210413 1250 165209163 165209197
    0xa12050d02120114060703140306120601030507060e10080f040201030f0f0207110a0b0a11010b040207080304050d031109010302130e070203120703021606052502280305040b0f 77
    0x301c2c41d100580528140d8009a115510090b080c00038800c080c440c418003c2c001c0341498850400004000c0e0082d584440082c01401d0401415011581740c030400707070030855060300301e014284105580718060002e000f1003152000d101e4031000c0f4010b4a2404040c00c102240d0125100090659010341c10050000200da08200003a03405018a28000d41004c481258560b0380009075014070710304880907605803401c0d40710139480c0c0384800109032102c4135201a884038035500c031603d000455440b0b1001e8295140500b0010f0f60ba490b0034030b010b41c02e04544e40b0201060502d0076080002c2c0110100680300314190a00340182d460b000c5a0b280e80d00541349a000d40d4694092008104407c3c0d408009091040ca0621080712180c07601d51080c0c040e4042d5850001d22030700300d04a024003250241e000300740c100000b402000d041c00018840410141c2e41800c441000d41e100c040c040708405c1440400141c1400501e980440c2c408041d54000d1091156124001584101180d0000003c4092044505100c5200c1480c4 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 165211663 1250 165210413 165210427
    0xf0c1b030c05040e0619060e0c07020f0d11040902030102070b0c070b07090506033d081902060f0a140301180e0d020a080d060308070507080601170a12050d02 69
    0x201540840c0412240848001800140d60806019155480c841980602556a14009410700780f80504500300d9109032603a0380081d120920100b003c0c0108943c0028660320900760060201444281403058010031031034640358085601c0e00e903c03801c4448100d0f400328000050f030002074060700030580c026000390307091000d224505010744010b015161286207005526664031106880d18001351081e190050401c0001076400e01d1074600b9800c00706044042c143d400078482d2940142043d00b01c40f482c01030b10036003405010012007008003250701e01c540011a4800c10469001c40c4040c021222603041400c008900c03050032500071007032082c1429000b20410785030b6946035011064840e003e4890010701d454507215910458001c200b09403640115001094a8507513661140322507800f050344102c1d01c0740d44901c0400051940002450142d0203080140302d4242064101d608021040c5d2020100d0004d0340400f04420201003010040c0300e804c44848030300140200700507100d501c14212000d050310f200103815 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 165212913 1250 165211663 165211703
    0x803010f06030c260c120f09160501120e01021b03030a0c0f0c021302191101050109020306011704050a06090b0f070906120b12010c0518060403020a060f0c 68
    0x40c120341503654288400d043c41041a1241c2c40c6040c0c80503168400391402c90025101e051000d5000801c42c004240f4028a0b240c205412003400d40f00800382d96460400c0c42402c0c9030030814000e0b81c0c90112801a541d62400002814014000043d214416110451800d11000139815110150808404c2c00a003104885240e40c0302d510450340700300072501e0000c00f82d0342103100d031110540768000c0f070719140e0640440e5020001c0c5920b842201052858080048142c845511a0380d40c9401c5150785401c108600400d6001d400e44d88143c0001603024414010400c407aa0300030380a03607694440e0300010032952110b041407801e00c1051600602002e06080c290000c008035141024440d004003440c0d0032507030303c82d10001c0328903450611a21000987c486020040e502041c0d0000b070000c0e10040c580007a10221641150a5514070310680b0085000400c203420045600c28104243ca802144c020349090b09560008449418a015030020404101a00115130b80111941c00d10140c01400740070221243c0390f1a = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 165214163 1250 165212913 165212939
    0x6060f12060b2b020708030106050c07030501111201140607030c05010204090c050918010e072a0b0405070e06011202030c070c0803030109060e0c071101050d1103150d030f0305060607080301 83
    0x2010300f241d003160400306240540307100b038807403055101d20000e285034a8010110f5050300070380e40803940ea000346000000002c4092250407114009010207135100c3d80c0c1410040180481640004040211416161125135555089410403a454144414244618107040307009003e203030060111030703181c003800280083c0c002c030140000940071220f0420640358241c0002110b8001c6c4120001a0a0f01001c0750106000da4840d1010000c002814695084c0100704440440000b000980d01d80c6010014401844410b00006000c2c084400c14014241003000009011070090034050041a5000c408039000c20100011501c80c04d82040c844d4120725150100c0c01d48a070b00c20701c22082e006186c0480050403104080c00c5a10804010032020f0034004a920749103245c409e600b0009041000410a0440c3d002e130710322500c80c682c501025a540c07a403410301139594088040c040154400c200c07070702089000030703401038026006600360711740030403244c807a000456958042c1404c02040c00c0d6010001050038100280307 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 165215413 1250 165214163 165214207
    0x50304060509150901080708130b0f0a0b091510050c0a060b090901060f05210312070813051c020c040c08100f0806160c0b090114090106060f12060b 65
    0x2480f0306404800200740101c1d1062418081c08034846900040d003080c0551446a441a000c071441d51810b10070703641711495200c00311030440b24648020244101d02c201c074412022002d500b40e8101003a8140070000c0c40d40710314400c800d036224100800e880352215101c1d106503200908204c08a03600007050303181c0a0042d01700f0081d114040da5004000925250b014001c00007140c9000c00c02d184001c2c145400c1c000c002c0e02d0a48150f03e010360711529941c1c0c000d0104001e020400d40c0400f06140741c03e0500c0700134801c00014000156507183e060400020a00c00300d4420307241815112351600188821505905003541803910560261034440010303462904610350394462040441411062900e4060300c000d811340324010034100f58801400180b05020301344002d030442c04542040b462442050391342d43d8054404441030030342a51a040c510310030030100d04044d6004040c020082c04614240500104081d8102c20350750304000c103000080c44035001940c01107003d8114508196034800b01424000841c6403088 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 165216663 1250 165215413 165215419
    0x10909020109030b15120601140f0a0b0a08162c1f0c05060a0608030403020603090106030b010306020403020306180616090905071e020a021804110d0308070e04020c07031b03050304060509 82
    0x1140d042590000b080f0141a01c8001294903800944a010720580f54a10814ad0307402c01d40645010444003184009869840000d5131444280d00d0603010b914072606501c0340709424811140954101c0b480c211076101400b017a001e1214a1310081040002c00d451560840000c3d800c1c56070800200701940110a640d55500400442d041d0b07443d100d400d413040341c5080c45404c416800501041c001464402c000790f41104550380003242940d1a40c60703400c1c1001c2d00307034002c0b905a5400501041181818002c0b507501c507814018840c51905020202600c440b80107140d40c0281c100c000242c90868050b00070003014200c0c010003080760386001d44e0080e064032006401c015502d03e00503010080c86100082001480e58040c04a02220030304070600d80c501c0c2c9001c2d01c212100070007444082415103601000d0f015881c007a54625059040c0000042c00000d958002107010703034010001c4003000480081c88900702c96128581d10341c06601e00025080d03102560304010402e0000140001c1c1c0d16a1000c05403840400c11 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 165217913 1250 165216663 165216679
    0xf0504050d0221031b0c030301120c05010f080c030a0e150f0c03100603052509030605062706041d01200403030807030c090b0708070b01090e0303010909020109030b15 73
    0x1405080e150041a440f000207610f00810024095281c80c4000801c04280000c8060400040c244810700b0b6410907001510650450102c14080c40f20481902c00184002c1c00c00400c0f5580c02d42c0020010704001780102c88043c40000854400551503101348000002c000c01d840108001c5081c03201c0d8100103842204000c02e0440203d4aa04040c100301c038002d44c0341d440185000c40c03404000f40c024000041690f4040c0f40135511100c41c03c01d611802c00c80b00ca0065464600d403030f0a51a0020460348080c1c03c1c0c42c003406601b1000d511403019580b04000e80c4040081c0000d40d5039a06002030040c014518041e041c0060721b0240c04007100b01500034a103138a802c124024101d14810180b180f081c05a88406000034501e20086880c0d9402130f07200c840804054074020b03d0030340d2a0035080c8429400a04100d444e41d000288413414051000800fa0140c0121300e8144200341c410100d207913481c0410301500345169640c0c10408110fa02640d4507500842d441202025980341c40140c0c1030b05216070b601120301078910 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 165219163 1250 165217913 165217933
    0xb06040c03020307050304060c140a050c0d0203180d050a06060f0807050411090108060a0b0414090a06060c120e040c030504050c03010c022e020c010902011202030103110d0203010f0504050d02 84
    0x900030f0b240300c4c00007642d03414156035490701c0b004003501030000903d05104492900190801d203600080004004a4860543d10f500301c1c00d40624140480b040c80c41150000c6c040748522030420145519000c40460720500d04501500303055040841170500104032a10300790001421041d502d1454017140d08800940710181d94800502050b518040c12542e0860340404c112074940d070041d1030290700701f2005880407a40a448141c8bc1c80c07aa03000c2d402030040760115078051f640604d001c005940d404410560203000b4503281c0440507250400e4000014050300d41c0c2d11420305c0e190b00c0780c1c3d5440d000d400000c00c01e002c02040c0103405402404140c605035214000c0b24038006507820140039910350a4807030390041030341006126440c90300e004940d42c00c2e000b22100600c42d413405001400500408201d14000180c008806e00c0003412189000458150050040c0300400c0402c100850003043d40c0c07030980d298403c80082c0c0c40003a00402c0900b016200d400e15103003e01060010000e210a058141902103c070758410f = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 165220413 1250 165219163 165219167
    0x6080702060408040b0f0c010507031b09050303030a11070c14090601110714030a140615030d0f05070303180c030c05060403021e0a05090403020d02010f0606050304141002070b06040c 80
    0x1c0c125400b40440d001000100210b1071984024440401d140c01c469041084d2804003a0035101c007903c40e200021b0b00e6003040c001680c540e200c421124011800c04064480c40c2c000030a407130740001490032051340e03078660303c00c0015440c1d14102c2d444207500c082c0020103507844166034a6104a642881401818603034001840342d40110707428101200500c00410449151031000407600401c0d40b946500341c05450341040000c1c803081802c4084c43d0000700034195510b0710360303001c807085400c11060078400d9000b50008940c968002c035040b2841d00d2140382070b0399181601c2c141980600306e0308683c41c050f01490001c100c01c0c007030320300d107850240ca02c44c3e20174860942c4c0d0384c810041680180c0c00007035070081c80c4400700f6014441100302c40d01019405000186826960700004201200031141035000d40c200040c0240f190764203115500c33a043c1c4001c0100161820700d10010918040108000c01c0341444c001200701e8030a00304941000002c80304029581c9501505d40079081d08003c3d5945030003203080181c42c1c580c041c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 165221663 1250 165220413 165220423
    0x30617010509100621050c040e070905060f0a03120c0b0414060c0a0e06030a20031501030612032d030207060b0f10080c0904050406021b07030c12080f0d0606080702 72
    0x102217640380d140010003d4240c508460f0746240403111446003641010454032103004014640c1840c0c000342281d5032034040b41d4801e0740d500800f03a51060319440040180c40d034900c0300a009480d0402c0761044007440b03040040e00c01c0c0400e40d002910b942072003010030040000c42c01c0328a0320790007024103441481c0c44128410100380200400c01e00814060a0041d5840c1800c81c09140e00002012001c11520345240405000b03101c0d005503440000300000811003151a0401a5504860700380303010420240f918411203614446c10074010b00300146100e01c01c000d5070b000c01403805504040f03d0003815592181e00003030002e52014404607000d40c1070000916162900082c0c012048001500266401002050864003648010500c15808009000001164a075445034520842c070400f40141d072a080d044041245001c0303407420b1205e17540812801d1002070300c0b1394040c84c111000004040c00c48d01c40ca141005481c05890315522010700d000c5008884020250054030442d8869210a08191202c640403600c40e = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 165222913 1250 165221663 165221669
    0x618120a0210050a020c04020d051e09030702060a170a06080f03041a03040c0306061e05030109020d03080601020307021806090718030f0c05042c070509060409030306170105091006 79
    0x70842040c02110594010f00c0140140d104a00c15243c9054020002130120707003000309a82c469541d10000c0010b07820314522504070345000419000030601d400b000d003c0d5a84614a0006c1c02850045002d16000d801703141c24816648400c0d003005807914011911000802140c0300740c01c800c0c40382c8450301e07030740e01000700c1200c040c1c2382e00598403441128261030b003142da0751000e0011191440c0742d06c03001002c50300d144910340281109001038100b80f2000c4100b010301c0803403608590710070b916109000f00180d0b50110038015071039150a02c00c1440d0344120060b4110b0084040c0690424101550f103a818880341b070386a880754108488d00700380d9807103040003210f1141c191017102040d0306092209102041001c3d900306c507140c0c490000164a41d44400114042d110512203101e80381c81ca0700002421900b8101c04038a1450700da6008003c46454980060b1541c9405880e242c004e03070707844890400b414403a403c140003524440103035544000341095018001c00d401c954400540c01031901d1600b4103541400b6000031 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 165224163 1250 165222913 165222919
    0x20a0504120201020c0307030b07090b0c0303070e0a080109060e0105130309030b0901020d0204060507140c01020d0e12030f1201090c050a0f181d06040506010507120302090618120a02 80
    0x1800d0415285801d1860381140503819403049070900d038075075078007041100d025511401d00d9501604010744040c108280380d802c802c420035014002c0c0c3c05441400025240c0c04241c0c1c0ca0003210640c0040c02291080046412580d00795082030240c41c18000180c104e00308642114000304013030764480714818544a011000100028000c4001300003180d06207104a812050100005141c0903041d0308001c126401944550b000c54404103000c404d00001641c4c110308080c005024001900142000035200c3c2c000825010a00c802c01090b141a030b100d1483c40500d408010007281d5446150b01c07a006e04503000440c10310350a20100d400417403a104a80940004080291101d6042c440410b4050f070314000c0d409014000c0100207182c02d008003007200389030710091004210806a090f00184414a060002006a40140d08050501155991240848010395045000a403a061aa0000f01c011348114a0328a501035400300c2c1603901c0117088031a4048200b03040f1402d9004030640482603464104200340654 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 165225413 1250 165224163 165224167
    0x210c03060907020f0607081812031603110a030605131b0806040905160609060201050610050c031c14010e15100905030a050304081203040c031e020d050a02040f020a05 73
    0x4031904186140c03941180300da00541d4565040e0032800e038079121080340c020000a031a10180032010500c850fa07000314400d51409000c0905015009188510019108846000d80c04c1c4900074603a1103036010b494699000c4280d107940302039404008000c0c1c43c1d140289d80c070800103d03242c81c007403101501c0350380750021412030b002e401009610760a954202004151541050b120b0f2901d00000d5402d00403000c048160340003002c030660401c20001e209410541220b17080d68944414442c40350340700d10410800320340a14186036944003c01a050541c0a0400c0c03a40d5680d1107290241445070858010030900c8805010b04a15681d03206442d4100040550360b00d01d091140d41da44c0300c801d0608400c01035a1300c10a0505403089a641c201092400d0054403090702e4581000c14140501c0c00d0901c040c1c0c40350007264601d141541065201c1054141d0b0360700c0700038a503218003030504070f0f03c40c9200781002c11681c0041030802c2003102c03828126100c3e02000402c80c4200e15041114806440901c240c1e03842041c01e550b07940c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 165226663 1250 165225413 165225421
    0x100602060c0a260a0e03040807051306180911010903080d05060a0506040e04060b24070c0b03070f02010b03190f0507031e03090b0306010c03050a03061a210c03 70
    0x100a075030140d40da00d010005203450b214524441c090500c4507903c41202202c0080c0b80c440003044c00c4031005031000c1c0c1c4942040004100401c000030b400b1080c0c03403007101d03000091403680c00040d0040406034031141c0061000b4003c0a0100503036800305034a80c4c0240901042a05510300441d500348880c00020b0000318280103070307401c1102c9980555030241002d40007a5480b0b8940001500c190010f500442c0d44050007802c00003008442d01a052040720180c800702c0c1c0422101c11200c000d80800f4580a411840114100c018400240c86203c0100b400940040c0d0b80c0c24218002082210541811070140d800c1c208402d0407400c00050100120800034644494110b41d075649102074451554240c902c1d10501700040086050302c2982010401400201c00506000c0d10b0003a040c2c85030307603205a00c2c0700f00c203104124060f40c1060003010b41d154149450380d030350a40d114003074006050782c1c0c01110000407a5850f600302414007000414030040001c41100c0c0800c1042c8500085040c11540c0b070344241d100380081 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 165227913 1250 165226663 165226681
    0x50f09060106091d0718091a030307020913030207150804022d0103092a1e03020f0904020d12050a0e0f10050c1f090209090a0c0302010810030c090f0510060206 70
    0xf030b50080820300d05400ca491b010020f55426111384c0e04000f41140d0b81c2c0102c078500c008190740030040c18600783e02441c1099110303000502c0c0c104c0001c00451903070030140e018a0401d4428415000942003d51041c8008031800b03a0086c0101000c40d0100d000d160010704014411003880d003200420f090b480146115a0100c400440c003415110310100c940c0300060700703006048aa400c0d00f8821491504014000851800380386061f01c102c08440c0c0385e041c4210100c10300143c2c0301c0d00c20901c0207400c10382d4103160949451001c074078808002c090181c0002ca154440f1340255621074000d159400d0965a401b062010307100c00c0004414880d084035600445003c4c86070742403030180c1c000d41004600039040d071351451680c2c0841058491171508400c4080d588140c0700c000c510b407440340c160b0045903000c010001c05d0b800795503050200e525400064180700d000000200c400d960000041c001d1680203080514a550fa907080d0005443540150700b0102c1401c0c100040e6000c0d03d01500c1c2001c4608a074000d0807541ca0703071410 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 165229163 1250 165227913 165227969
    0x1205040f02100302070c18060b0301060801030f02062110080111042303060406090c09050c030a0b04020c0a03020615010c08070b0a06030c0b0a08010e060307090509010f050f0906010609 81
    0x380400d064090201d034021694200320035000701141c5150312054440c0c02030247c12100c070340d002179000f46000e00040c000207510901e554152039000b0809520890140006001e5009826510000c01869604c1c0c400c01401d1110345801a02c40c0d800c0003842c241c840034a5400d0790301030750700c02030154401d001c100103000504200e401400c1c400155450181d011030b01080c20030340c003124142d50b101e441c9d500d16810054502030000080126190030481802e00704030f0700245100c050110110243c64046000080c0d443c3d03811100b000c44201d085406d24421450080d40b00ca0702140d01d08900742c1c0d8548115642e50249a03005495544408032138680b5500d5580c1c05248040640320302e80c16540c901f0084009501c0b4541400648801e0b070380035480e581c0c800e40c000c00509058001040001c201c40030f2240e035440c000780e00300545504100100d02e503510b1540c01c50040586c002040142c9040100b8022090724144145004d40300e15402e44059a0300c650342501d0b6421140315001c141150144001241b850a9403 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 165230413 1250 165229163 165229189
    0x30909050112020d11030f15152206050907090911070f12110d170912180f04020339030109181b05040b0d021804030507050a0b071205040f02 62
    0xc917014035030302e444010034035100c007004807207110b45c1c0071402502100505440d090f0380b02c000c2d60340465402c00c2c203d01003500c4a18030b40709501c140640191002000490b030f04440302070900601052900e01c1d000e0340040010134207111b10b0144925010703a00420300394450403940e241307800005110348640f03030340c0c2e515513080e40e070071208000c100958052808030703c01031052107131143c40c075660213010140303070400f81500c0c0601414440c402c2c1e001c54201d031a0b001e580d40a80b13060081d101c03102c418014498000c00c40c0e84603c2441c0c41c0d8800d100004000d110111490000c0d01021031500961106500301e01c0d030b843c810f800d8108038145100c180010008003051f90881550403402c8070744034841149542d030781001014004111100f00c2c04c0ca1009106a09040c03242c2d00c1081803c03511884800d2007034001c125240a100e8002008040c94400a000e03d80200102c07142664000c04071254003485081c000300d0310805aa03030074006041d0400152100000c4e00400b8004e90f003001c204809107034258200300e900c104201c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 165231663 1250 165230413 165230423
    0x150f0302190906030614010806040506010608090c04020301080102040303081303080402041d1b0910030807140f07030b040201020607050f09120c060d06031209061d060f07050a030909050112020d 85
    0x4800315082c0318074000c00c070003180b203002d000c01c03900c02141040061003416049241c0c903600030010000801d01c00070394039044401c60305000c892a250060074134202400b804003590001d0000000003018030b41540140210b9002c2c2d601d840c0702d03465009c1600daa083c10710b140940001d40980100b00549843e600c51045602c005450200000e0310340742d12400c126403041c0300d800146076540c03691201e0428440c0e50398011345511111032a6411584d480e03103240181c030405001c00000102c0310984680401c141003403040030350200c0342d00e20b540c0d02c0d10900c8040c007100c049005001e151b02254500d400780301900e451002c1e081203641480c210344c0a0054031b405001c5200490b1203991100c498989802e4001c20000b2000356000c15800c4c110f05200403c510240410410006550700c1001086d0340021a000a0000d004440c001220319100080c0030303000349205074550300300000301c405c200000007030005455807180e19007480d07581c2c3c0c0346001170444409105001c58100c00c07904460042c0303001010403014900c14 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 165232913 1250 165231663 165231709
    0x1090819020c10110a170912010e0d030b12060c030a0e01020a0504030f1104020c030a02010b1203041208070206030c04091a061e0c03040f0e0c09100507060906110d150f0302 76
    0x5074894000310b20300106c0900f010311002590850604100f06d00c940c4910400000b17010400804482c1540c5c6c0d00d402c0c0780170301050768038495000259500d075114170a000505040b9071040c1400080c40d210343c2e10950b22045014179160041e0551803060096515030221500c800e804c1925580b940c00c00240d01001c1110182120039503000240d4561028095000680c0000c68403180c0058000e42114114441c032841000804082d02000d0310020840f0103554516519034003090040c50003010901a44400a5107c0004401c200d0490039410150085905c0d140b403c0c000d18001a00303229010144590481c0c101c072041040d145074882c0d18500f400740702142880c00d40ba2190a2208505640140d0080300d28000d6180042010640440c3d031130760040c4503a40e0251a208401000640092803036007624144000419140c0902c00c0300d6100050145d0822018024000046030141280e80702039004083c451410150f46101e075071420150042d01c00c9410b042c0d00b82030071034080021a03031401071020600500c0d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 165234163 1250 165232913 165232933
    0x305031807090e0d0201110409020a020a0b0702031911102004091b170402011d0d0605040b070906020304090f091a01051503090309120c0301090819020c1011 69
    0x304110304402480181c03000940c10001e0b0144604044448000c10b08683c101074031000c5821180c0119421201d08031070040c1c2d980c000403410703401c26042420103460341307070071302c00300041560040010300705d000e03294181d10307050011014242c0f00348101c41810900365008091070490304049500c01031446002e0b0841981e4480e103460700030940d6100f40c200c412210b4882101c02c800400e02004165889114240450198260070340340c010000014806410441081a1402c1c01c0e04401e440e80039040000c2c0003140100000d045c800040d020070750b0116002400f010006034418420307218ac509542c40d9902030f41c6050b00d0042080c0c0500358001c20b2058482c0d0342c03d0048001151050f19507100c041c2c1d030f107081d0b140d507240c54200400d140c070f5505100c18000b01002001450940401100c002c84801c544014100001440603407070300240e405200d40541c0703425816001e008803503001c0c1450000708204240165226001240c8800c004200c2503040401020b02d900c0c001d019507800036092071004103e0700b118031 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 165235413 1250 165234163 165234211
    0x5090c0c03160c080a1a010501030b011205040222090201140c1027120210140f041103011a040b030109030c020907021005011502010b0108010f060507020a050d0308060922030503 78
    0xb20500c00321496101d46d400c09500c180030880460040c0301c01d0900304078440c0f04500207040c1018001c0344100301d035922000a0704642e00c0115060312450f461510140c0c604c1109000700c01006090001e0340455201d82d00b840d201c1e40000d0032159480b40b0341d00942010703d0b10000c3c0001420320200c3c3c0d0340d4061341403855010500d585d51191440a8081c400410038a80e034050064104500b5082c80800716003000420309498910040054100482c1d400d02105650f40382009a100b9030480f0b1004d925509106003200d01c00440f020f4200b2b601300449040240703540c1c1c0303030425003207422000d0010040303118880034001604c1e24040043c0c0c0050140113484010b00202d002d102191001d03001401b8002420302c080d58000c2c0d091151200e244d5085c240311202d03504003400924400c469200707a200304600014610219259007615000601000d007100b04000418034024010301c0003114110300800544002481000800d0303121498101001da041c00c0025458804a800c1d9000500c200308000348510b00d590b200d2 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 165236663 1250 165235413 165235423
    0x203040302060403090b040b181207090605100e09040320030408060103031e081f09020c07170703120305070e100e01120b01080c090102010b1905090c0c03160c08 71
    0x10312030750162038540f41c645009406503045401c81000c04500344400d210000f848400c070360048080240c1341c08446803140001d40400c141220100c0c80e406500000900a101c541141c000c1c2d5104540c26002e801d5216030441d4104541065982c1c099414400302d004a4003400210070540c000031084040c0045100e1110320315417040c0d01c000900c0c0d009600400a05601521051201701d11004a0b04c4011002d14001d0030400040c4c1a00220740021141c0211142031829901c003c1c81d00207025500d030070070040956110304680c8200c0e8804044440300009141000c0785110907203a0184140c41c0d05806400c2c128014031005041009201c643c41c1e0180895580a00f034491480050740c403048121581c0740018041980e4080c0c0c01d101c6810301b1005156030781c203c02a00d501c118035140590f15190201d00403809003040a81194100c5c492984c680c034a4403c600207801503801c145c80e030740e40986901d00542550301c030700740d0b070100f058000f405407200c586080301c624003009000310540c01160361925411400c103 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 165237913 1250 165236663 165236671
    0x20c011503080c1902062b0c0918060b0406030209180a02180109081207060914210a0503040b0a09050d020309010e0a050a0302060d0e0a11010210050c0f07030e040203 73
    0x403400100d0300c1c2c59048403c0040d807801c044c54100c24642010581d012540c1802807542e250900c0c0390b02c80c0105c0d10080541880d440700741e01c00702c0c18012040003d6000c2e01002c40740c01502e0450b261300d501045d861503103000300e800300c8001c018454030785403514070100c0080d0000b06100d64814041c488815110041c803102c1070003108008801661400940010842d010b030f100c5000b030500030100740402501902140c0340c0d1280ca0012001655000140790802c000c08140d040140b00ca948400180c1001c80005000f801000c0e1204100c2003520320a1001400d038005c020103000050b104000240015440300da0180e00480012070110b21b140e01641c601c4d007881c1c2c480d1a030500691010031120003940c1e01c45511031483c0000c0d90700b0f05820b400c00c8045070048901e400003a018500005c1d03000340450003a07022605104d50407090320400c521900d0719818124000000030b0044c4259854505100c001d40f141c7c500603c0100081071514840b070206041c942c02c0070605905000d0548401415921540002c500c1 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 165239163 1250 165237913 165237923
    0x20118060606030b040504150e0f0313060f2307021801060203030a15030203100b03151509092d010e030d0914030a0e041812020a050f0c030709020c011503 68
    0x1002d0519400904032540c49100c14400c1d0f0602c41440040340e0300c40c0c01100b5242c0788080100c0c18a4507181441d29044001c07441e44114031000501301c20001c610305050341a07800c681e0b1201c1c03200c0b03101e440890f4018010000041c4440b1076125020b81050001d00910303009201504480108445242040c4d800000364003600150304008100481400c0c030b071103410040300c82c016101d800b143c21500030a55030307036201001100302a038520034141d0300d540c01c03c0141039841d411407140703015107002d0b089508030700302c20300801340150500004500303c500c0106c3d00c52a81d03280c07414060908029000051030641110b0008a90b656070b4182c003082c6400c080c001088807901009c80804d03041400d1800410084101045201c02d800c14017003800040d072700c1142e240c0340344411203010a2016080342460420310800320010202d0030014907043d81c642e004181c0450301402241511200c0b81360303103075003900c8000e541d402540c0741e040040d01f4021000c0c5640500a9003500761700014616040600d80c401c038000d69003080d12 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 165240413 1250 165239163 165239171
    0x12020a020706030c1d04020703090302030d020d1b02091504020d0204141e0303040b070219090c03050a0b0a03031409030618070501050702090103080304060e1002120c04060206011502011806 83
    0x2e9941501a0f00d400c0d240504d4920000d44640c151089031a619400b4684540c0d0001114410705108203c905c018540090544602d1034004801a42d520210700c01d01c00030480c404c035500062007500d48000a0580c0180c410107079070396136000ba500d9120000c510382d948a5400d1090440020700743c4080d202a00010452000040780c6800b0462041e010090610140390562101d21058402109890403a51840c0e000c0d07443d283e82c1d10002d418140c4002e072a9054600c0590009805002500480c00c40718690b1810801034488540b003005491510074407540103268800b04100291088a81d00401d80c26444824101442c400000b414984241d590400300110700180030801c502c2401000001c08090038114a01b80d0b959000c903440080520014050050200c001028000703036801a00c0352030b509506941508882844c203100940dc140d201a1441d01d4401c00201700780459011202660718075002008641c1c41c140c1c0d414140110383c0c24800441d500d56600c402d15085110400c1c40851080202003 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 165241663 1250 165240413 165240419
    0x30f0118021206070e010c05010f0f05071d09070e0a0f030b06010206150a03120c0203010618060608040203100b0a120b0a1424011403041b0803131512020a0207 70
    0x300003030008040c200c90b990014000d0019498010350200088035013803c2c900303213614060505c20f00518031088002c9c030f194103107650810f0380d01c1c450744030f21311841440c0c941c02034000c0303001000e006d09000d00f401c427034010119401080045004004000c40c0c80c20003002414556110401c164200441c0d40c004c444008401051000d290b0701401820f40c0041c18041c04080000c0440015503040c00e68400541001d00f0070140e03840c1c5a205d54504220303190094020310116030b803010074080611905480142c000e103080c80c00300d10720380324150141c0155001030040c000007840400e10001402681003403a17000680f040000b41d500b048080c1110307074902407481f10007207203030210007601580ca00e00600c0084840070000c00180314101d112010303840c2e000083c1082c168600d800140c41d08602140c00020182000c41048100702006030501e1000c043c400e04002c246903901d00700b44e960b0189400d4400743e02010b0b207080c00485040405440108614a0700707440c01500c40070704004a80c041c00740ea90050304406428 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 165242913 1250 165241663 165241669
    0x71e050318121e130b090a170c03070504090525030f030309051c050a0807031d07050a060206040f060203090c0405040f020405090607051e1e0703030507140403060902030f011802 78
    0x5a1120310100c0c106a2a100d20b8101201c0c03e01c1c4d031030140030031003240480c8502c09a180c0041950150140010500c45510040102d52717661010300c82c818403a100d1a84003040501302030040e61005a4014000d2010b14241c0c2c5002540020340d900400302103107500000004180701e000e0044440303010781c600190516050910034108401404004644070000f0003440c02c031a408000ca41010203a4641445287c8491900310054000909040702041d044200544d03003280120700e080c100c800c100c90980450756215016a00d4807812600a829480000040c1c80802c9143d002035034450b81480039200440402c44c0010111001a181030b90560701150b1400c085003060303c550b42d04280094001c00c03880ca00858024114490901c1c02c400d81d00442c810444030109070803e036034592a1040c401d0700d4181081901008a1f0810768042e000241440c0200c1c203014050030002000042d01c000003482c0074119141d000c05070200d28012a0503209801072018440006c1c460700c0501441c0e0400700401d45280c0c010 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 165244163 1250 165242913 165242947
    0xd0b04112212110f0a08030408071d1807080105280504120e01020c0303072103050705090103110702090109060f06050f030403030903050c0105070504050108071e05031812 75
    0x1102404640441c1071004103901407445107102d40c007801c1900300e40d101c0c03808900c00003506000190081d4002c40c001c9044075000c4042c10940b04070108881085555481d02441c5404400c0d42c80c040300d240f4808182c00202c1101c50b0200c4004003011140e64a590798010f6084400490340100002030040681401c4e5101c0c00300c00718803940c400000c1c8224102070321040028110000d1910078890318034960002d0340d00910202c80c240b4801003da9440c0e000c2e130704040d04e45405099410401c109980c040410050092107428043c0b0010340d41e075821310100900640088c04c10001e403103020b107024000c0c0c000580d540740045000e400032400c0402d04501d055280b42d0503003035603045102400000d000700080b410400c41601d42c4a03400d4078010515609030304007035600340b00f00300010401c0d500704002c100c41140c001c00100119202070b0b80b204050781d0360190841c0c90541c031390204c413650002c211031403020921031b80145800540407260003100b42580880c0d686000002082161403500101e810301601480f250 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 165245413 1250 165244163 165244207
    0x230714100e190306140402030d020a03051204060f2c01180602030a0608030f091906050a030b030709060920130b0c0c130e060702031e0d0b0411 63
    0x800e0300029103080400340402035a1003140b4010001498038030700c4a07409124150007950000410040704844800000c901c481c100e6041e4003070320070301d003d610a1031302c006904200660075a0301c441c18603242e403510485041020b4000d40f01541c0b111714107809034a80384609424120394810801207038205038024074241101c1320101520364035040d031200300c0c481d40780313004900103a100c000147c0e01e03662504000700500650b00418410322020409802500c102e41c000c00108408940c03003c2c96203825000c024440000f0f00861002038070038005018171034025081440d20590041c1074500b01030b200d80a0804039100d0b9030002da40b058580101c200c05c144400c4040d002848080031903840d10b2003029000315085207a1240e036240f02400038040340030680601034403005c06030043c03890305491142d10f2071001801441042c2402406030001290b013144c0000121441c1c80313582000c003400f10f884502c41c0c46854000164000c4059103c1d61113490a0740e4a1045040703110341b01c1c80075903d52000c903c0541d02c2070b940c11 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 165246663 1250 165245413 165245419
    0x20a12020a092d0506060901111207080c0105060603010b1215090a090605010503012f040509130b060102010b01020c010f0e190806090a0506010e040f0606030b071115060d230714 78
    0x71342401020b0f1507140846244c100207080c00da1401441c003034a40d00d00360241d41c10316064200411448100701219008020200100000707201940340c0000700714082c402807180880a010402100c0901d9180034845580080c1e400c83c0107002c43d00440c081071206504607426284280d9401c900c03010407146214160240a098008214030301d0105111b0341200d0140e00c1e0181980740d9000c51040528060086034081c15010301009428206114410401a05c4040445841030000c0004e14254414469100b004005034000c040c09000b0900564031044a08000010800303030300b441e450207445060110000d00003402d40c5a403a10325102c0054285034000d400391006410502c07410b80410000101b10b4192070312a8120002a251071420183d03015018a00411441c04c0680001c02d001d00d802d42c02d81b041e440d640f500c819000303100c588580c9079000c242113103410200c2c0c400800c60030300348030070001d604502c00ca010040c51500b90103443c00c01401008200001c1e0301c0703007809010212210215a06200c405e03 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 165247913 1250 165246663 165246671
    0xb030a180506062b050c0112021e0a1b05070303020c010807050d180f05070602010b04020403150b0609030601140f040603030e01030c050f0a0815090103020a12020a092d 74
    0x6641c0e1551141c101400603440394144d110159180c1c041510503040a514582c2d0500c0f90081925056454401244407140450140310903060054500e0007200e4812641e1740c0c010540700e468514007071003604040e10400030000950b01503203900003070321402140385004038010440540f81d443d00a103084458030f60b590400c10690f0038408a25000416614012040040401c458260440869203241c0e500310203003400304001418070034070101150a10695859500030b0240510403c00e000580c880e52000071f01c802c4180104121070050307075005c960708401c010a114580011600000d2420f4000c2c3c224100c0d950505080380320074075042c0e0b6941410081500c0034008186180ca0190842e106645000d0616498490728801148500c040781d050302c10148000d5215901c800004000b034108607130204088c1c043c0c0038400c0c0e2900d040f1007500e04032a03000340308c18501401c00e8042d000c091044202240c124010301800300301a0303d02c0c002d00014250481044803102c40600300d10700194100b010b94610540b170 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 165249163 1250 165247913 165247961
    0x60302011e0c2103060f2105032b05060f0108010e060a1505040602060108211e041508180c010c03050c0709060f0b0f07020111010b04060b030a 63
    0x4102000d034121003251040ca1420101d030416510610744034402003030141c148002d0300d8160406240500d1040c440c0d6810056503803136440340c0d080d100690251042640f04915504540d540408540780d600f4410001d03a0f041903d0328031102c00388824441d807040300f8421065502500e0366207128455020b00300f01ca016100c80030313040000c0c01d151418040d243e4103810344800110a40c43d4002c4440c014400c03201e8440c941d00541034000c000390090301844005004500000510041c0080c2003001c0e000c0c4552207020181c0354180540240d0b0001202e0071b404451000c0444284498001078030007060500c003480043e80030b421006000303020080c0841000c03440c0101844001d1800180c1c519246c100b8240000c0c86103090906071041d000e201c0d0b0720b0500c2c1c45400c0d0003140000300e58010200f1140c00c169203940d81511840f1100c502d00400c940c20080c1281808405c001d50b110303607aa60758600d0004000240010360344040340a844154001210b660300020078800000700e140300e03242c04a404011384408200b0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 165250413 1250 165249163 165249167
    0xc080703022a010b100203030a0b09161b060e100f0e0d030507020111030103050f060106020d050a14090301090b04020a090e10090203011d06010e010605030f0412051908010e0a06030201 81
    0x4803501c50202002c007007000d001c0807200c2540300c4240000020240000285a204025034030342c000c4890751560340c14000031400a04204503054003443d100b10180340500d034a074008030b0f24042d800c840200c3d00c4440306040c002013000e510400b507242040b2005007807030b070380c0d9441440182c90682c0f00c907803103141c40c1111211000b50041002090004070703140210b020b48640c40d04078090302104607608440701c0000000402c0143c0080c2003c03442184000341c0d9040d030380e180300a90b22074854100100102d803080048103425481600004002d00018039004e040181d02e04c0071a0031205c0801c401c0b245840c04100313100544c90303c04401c400070104410207012031401c1e5241c094680f0b55121074810210744a000c584215642900441d9006084815070000362040d81e100310340c0c80030300384601e004041c6031a0010440500c01d4040324401d50130340c64525250380f216601e0b086204640613035842045070900038440001800400718600045564504d100d40d4100488105034600c0a044900030524003801007006036 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 165251663 1250 165250413 165250447
    0xf1005190c0f0b0c2a1203090304061803060603030201020d050a0b01020709051911030711010504020108070f0c05030c0a02040b0a14010534140a081c0b0a0602010c08070302 76
    0xc0c0e4803c60048954450500051190045035401c0300c205080d4510000089806802420352800c600300f2240c0081a0800000c02c41c48183c03502d40c03241e0010081440014001d10300c2d0000c100110030a030300320796603075214a001c907559a0030440041c3d40006441c1c1040244c4e0240c140c2081c0024400c101d54814040041d540d10f0251040030042270300c80000810000f020018a42e40e00b900711405d000001884244001c15401141c080d4085555180e980040c20014840c0c03500c5a03a040c1c441d25501d845450782602d0a041920441d810041c012155600140d02407001e00b0055202c58001d101c809030f01e10400c000e44031466402805040201d8081203d000c0541c4040404d038028240b0340ea85802c2c0801c00440500346611411520141c003c00800500442ca0a440f0803402580810403503075110203641d44500030548090a05c0b00107100c80c0e0840402a003c51180f003d40000010300c104045012540280c070590105002d40d55030310000b1011508540600ea111610346070440c030348011050030506403 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 165252913 1250 165251663 165251693
    0xf0708061503030705070f0810270f06060303020607111506040c2706140c060f060604050a1401030e0d1d15030406061403070602030909060f1005190c 66
    0x41c20440203140c1c40c9440a1080318021500306060f16050380d1103d18000120b60b19102e258600c4c86a29034040400015104002da01203001e406007090346030382e00401100040660080c0c030156120805200050250700c00c0e04000c51086d006040c251034188809002648500c0c0c860003240c1021000400040410301c450360700080071107002610b005e141e98200c5252905094000401180003448226085c90a189030100e550607601c5290400140c2e1003035000e4000da10740b070030300d651100c0040344048404c6110554013150203005541429a100c002803c80001c680c4000003103014004100150f5074540104a00d0040750001010100085080106404841c2e08144400c4a2258604540790740b00c00a18140081070340003503843e4201401c0c5076004100078442c1c00030300d82c0b94041c038440da4100459454102c50300c54016609054809043c401003000040420b54852128000460340340c0d40c07076500300141c01c01c95841030740300c0800040c401c01e1160580c50070014848643d107101c0024949440710380d10 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 165254163 1250 165252913 165252931
    0x3310c0314120d06150905030d0e01030b0d0609120507050a0f03050403140d020c010f09180b090f0a0605152a030f0a08060a03080f0319020703030c020f070806 70
    0x441c0c100401c6150401c0800040215841c00010f401c0600c401c40d500480e003941c001310104d0403071840c1c990382a100040e940c42915050342102d03d060000c50300500741c06540c64018100458120000c80004800d41e9070713108119400f59540b142007040c001010801030443d041c0b41009442c00420742c40e1075955003418a401441c00c41040d4a1200b014400c00c1610000c2d40d02c00c01480c14a00b00000c459114000c04000c2c3c801031040d100701c0350f0158814550b1105550094a030541a141059840340d078120410103418001c5845641e004400d4540055903403082d19901c01090085c10035403046030a076155540010310136403942440c80e40e1030b140002120413800c0b46c0c032655600342d43e003040742c94580d1310581812003040c003012079103409034440c4100802626646503a5141182d48210130001840564040035218810500410034208045402950403440c00c81200305841c2c004107c0c2d40690b84448030803170000303455500284116030104054145001a90064180796003003a0740f4595074807004200c620 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 165255413 1250 165254163 165254183
    0xc1e030b09030708030109091a0c180102010b03150106080a09110909010b0907180806010e0604090f0624061112030a060b0f0c0c010203031302010509041103310c03 72
    0x6007000c01c1100c1803181d00003a91900c030342c0e50f40c03107190003003440c1041940c41282c1ea00100c04840400c0e20300d144242d46d1481950f04210045412800c8200b00c190180d041d07640c1d80403010466a805c1044154403d850f4107040255818030310000c1c02d40c40040e00c010003903800c24800c1400240d641032145d11400d41901d4409465071802421405801807461541d045807929052011160f0b11580d403c03408a0706110b0303004c900b40e0b41e01c0da581c0e03910802d10800300e81c15120004503d551400d600301c80012401941490b144181c0c644a80045400c107220300d038441000c0c548030039030030300d19007025800906c018100403102803881088a503c0e00c0d0400702c00143d00100000040802c10b00394400e1000e002c4890401f6100d0154044003003556018402d40031851080701d0404000e9880002200c1c0710ba00001d50183e407403121030380192002c0d081110f000d40e010ba141e05d0a0560304024101640c8160703811034001e0782c3c0804064402907080040413000c0740c20361200e401d801c00b01d0080900c800c21241e010107451 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 165256663 1250 165255413 165255421
    0xf0605010908030412030504180b01110f0601050f12030d09030e0f1309021203070f05011410030b09031e0d0c03020a0509130209040507020a0302010608030a0807080a06031704030c1e030b 82
    0x201c1900c101c4e0084c1c2d64059140b1006040c2d00340070352020226802c00c3e00d40c8001c0d0744070cc035110765580130b140340074075156442403006201600f800320000000001c09000540309400c04215141903800c40044020101d9548400c1d005140d802142e001000c2010780e82541c0d100c1c10003002c40c1014210748160950141c0320090a01192140007c0300322010120040d03a072103290341e180000303025210f050142c2d41e035800c05c0c3c551501626068090303401088000c80b0007254928561390f80d9001c6100400d1207002e0b000038881c4408a2080c402c55480c000007500009550302030260281d403c03151500084802c251050204050564110003250f100e0001214401d1841c450856000f0291244d004025005401c10040c040180c2e00041c0b030f0310342c851294000340a81c0f038881c01e0150b50382c002e50fa550000030301c0c42404200180d00036518a40c00c00010031010036030680b0b075200c10403241801e481030030003402c1c0044c04105005200030f90f14083e1000915036000008244440314a0b524580406081542d03001c5c00301e = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 165257913 1250 165256663 165256667
    0x902010c05160f0f080c100507061b0f090807061211070305030f13020d02040e010e0a0c08150105060d0b0105310b030f041103030702130f060501090803041203 70
    0x300c40c035640041290348402c1c540040740c00010300ca1243c910b03c66100d601c042207409045100d042580c042c0300090140090032420002440100b00c003c90a020b000c10001c0c01007003035401811002011000500038030607042500800c001c1001500408020b2211028840c542010940340215909440c0800c082c80740d01c07640301c2c014001500030264402001642c2404c0503004030103141700c5c1d180b8070000d802d190386407503040c001040c003100025801038031102c4e4480145044d07070004502c09216800001c110616041d01e07440c1100f000c4081d41c80500e246010410300c1e404000000320580180b8280190794500004a2500c0c0244460980080e481c1ca8504007076910942c02e94064000003082c0300080003813146110000e110105660304100c0020300042104400402142d002c1c0103911000000b40c0e4950712071403035555001e40c807150305010030000c50300566590001c41d0010f2465410005251015003000421242070358040b40c140f181084041107034203004401d130344c22500c803035040f421145914941 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 165259163 1250 165257913 165257927
    0x5010806270612070311010315051206060306060103060b400821030f041104020f0d050106090f030803250e030d050903101d0303160e0103020f030703090201 69
    0x466180007480080190074001c000e03031041c0c05440300b0303030b80c09024661454040381c484505000107442c0e5480303829440c030154803a6001d4061b00018180c150085a2607900040ca520743c2d08011503120343c40780040c0031640c6405c1c0010f64200d102402c04000c01450f150030050940a12418542810b640e1201c540b9003100e0054580034034038003401035071307841d0707a80c281c0e10240070340107000310100340c030413480100085250b80f030003645410b40b00c000e45405c1d5500d17a1401001d803c0e00810856861011213403e00b010b489074009001480e1114103160b0310b1700c110750740340340480c0c074140c0c0f02100308465020200140a10203580d8000c0c2c80e04203046a50360b43e43c41c1c0c0c00024001c601400d403480070b07101d02042d03007820758406450a902d02085040c2d6607107559a4034101e90394090200b2003a4107412402d20000d01946607840b481e1204400c040301b41101110060b400c0c1141c00881d5036600c801500d044802e001607104695002000c001d080850400c02d4031400c05070135001c01080d03001410b542e001545d096a014000d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 165260413 1250 165259163 165259189
    0x3020411040f0b0304060c2a060605030601060905041505010c03050724020c060610050d09020a05150a08010b1215010c0501060b09150f12061f1709031305010806 71
    0x26014840d52000da21009078011203059603000c0c41d01802d1007c0c1c40c4030b5601c035140300d104002e42044400708104103038a50081203404940e4203996040c002415241032181500038071881d20f610b14044e14100034401a0b81907400481036580c0380c04014846a030300000f80c031412642524101e81ca510703041c50211100240c80784480090910200e0707120390f48013190028404c00125809940c510344030102800f520f400f10303558000c08a0400e0021030b400c84816403110311021700042c50680501c2c3c0e240c0c0443d041180b0700f030121040360b0780094041111500305440314018014106002d21380f40001001159100000e06a40030308408500d43c1c403020383c441c1c5140501c49821000030031440342d50b05040541d59015066407801100c10051080180d803641013610f4100580c5c00b030080c80c01ca40080b400500307440c000c0403503070b0107144031000805410311204044c01c00f214544424003c040b00c0045d900810388000d0400002d644200051003445042094850445800303080888003034035001c0024000b8003290b4 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 165261663 1250 165260413 165260429
    0x5130305060c030402010f02010b0d0b1506220608011802160605090601060f05070b150105041e05011205150907030b0d060b091602070e0709031a0423070302041104 72
    0x1c014004204000c80003140100d10036203c1410401180341305070f0036a41000b514550000c9041500700c0496843e602c0c0990003007110180d010400c14040008007c7c0e00000c014000300c081da20024082c9803240b010820140440741805903080d071504610340350385050140141021900812149045180c0b00a1001c110b640461305103d04c2c230345a12115070703c1000344250400500c2030b2030074001c4a4051812600c107076400064242e080c0c1d88051020070140f2a0f4180d490402c481000000360110510070614800030080010191031881d08000402c0001c0060703009801502d820207004c241801502401d01058003078980500c15692560264002d04000100076003100490100d0406c2001c0ca50102108200455043d0030707a0302d40044036200109540d4615000d680006400d1003446658014154050034500d080002c00d1707101d81e1000d10020744801c07180180c0268006200800603000c10341c9071540607c80c41100c100404d0b07a4543e503100554440a0700403030745d0380f810314003c1c0040300444005d00710030 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 165262913 1250 165261663 165261673
    0x603022803020c0105010b090f0103150815010e0106022d070e092407081308160b16030b01210e030301031217040507360501060f090503030a05130305 66
    0x1420301401079800341000311440e5180900110b0303186001801d0780c10311240940512491005030005500034204450f0204000c115450009504141003004503040401c4071070b940329552403c0c170410318a010681010302903404c1035091300c1c50407450403140b80500d1600d1024002c0135148850700c40c106041d5800c684100e550700310400c84454000075042c0d41d503c4c0700d05802075000e2040c08400c0030040080d103444001604900c0810018190341440c052654001e8482c2460700160440200c0c5810b61940c04480c040c1c501d070b0811401c20318001540c411886e15090034049400120002030000040c92110700315001c0301c0381d10040300e212a034012002c114040003100c0c1e0320f5849040000300110042003900003e01a0100e5015461504106c00c0c0100d0780400140103240c14514111040d00700e902203888841c08800640070300e801c200c1c42c0d000203210007103c002659418070000408201002210100f0300a02d44002c0025450000c1122500e0300c03240380c681d440ea01004082d0b4010701e5507900180c00d0f8410 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 165264163 1250 165262913 165262987
    0x915011706070503071e180803031e040c120c050a08030c070b0a02010f11070501240501030c0e09070801030201021002180402030903040503030d0c08010f150c0302190809040f05060a060302 83
    0x12141c0081f01ea148032040070a6a1540e42d10359a1104960352020b8040100720b8004250740c0305c015680061244258100c0b9584881696100902ca00f105603080c25801600700034a0400c081b0180262028030051450503620304400d650321012445642c0102c140001c8204956100b940038140805d2089801c1c02059200405105030740c001c2481030758036510380507010904203840c022602c0305020907203908030860320707001c01540104902c02448042c05860b041a00703095035203510440c445c2e2015203c04e501c65045000092500407800c5002021500c100086190385c07503501b4030784c1c1c6840340032580981c0e280d40b08001e40382540650348c400f580502c000b003003d1514103c035411500566205946030081a030b81d650008240010700d10401d1700a0b0308094024110b68442d82c181d00d00d1034002e004640045c444003010304402c0840040584007500d0208199030700f49018000c0800003400c0b52000e00460428100152001209201c0c6c4004d0650015000c2da0100780017694004e1081402c0c00b14031915a = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 165265413 1250 165264163 165264167
    0x204082d031215040b0109120804030803040f0303060605161407080a051f1802060703210c020c0301051e100801110a030b040608070b07020a0e0915011706070503071e 73
    0x200781d0b60342c0a810f50a1080b95141d003441e1007190100341e4141e48422003180f4104a1441d144070058080d90482002c1001101048c110700045015501c2221a102c00b0f640a003002021540d06030040000c10604100d002c20004030451001c11180d0099041160710961482080c64003100e64060802c5005101b048814231002103282c0303d84040100400000285001556046403840c580c0f45a03400741c014008005404c0500107402c5181c408d042c1780d442090001410f042511026000c1c00c03516444201c0b00020070390500250458003000e4001b8411030800c2d0202c900300c455100c2c0141400c004000c000b80c030083b414a5510000c044a10007040002c00d4040c01c080c0d035074052400540801e003024008005414140725a104843c10740014003420303401d2071040e01c803a5001b40000d9912081c905008101141340085d0240100d06020080c51031505e509508250b00105900012039a609036074004420040401d42a03445080d6103071555880c0d540d41d80a40340c505940e07c0007481c8040241c0003030341c425 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 165266663 1250 165265413 165265447
    0x60f0f030d0c02211506030a020a09020408010b0a0b0316051306170105120c0f0301020c010f090b0606040303020706051b0a0302060106110d0203190e10030213090204082d03 76
    0x9000342c4024620b100041c1c2440c90702004d4200104940e41700c41039000b240c000585d01c031038010307000405a1302d14003502d4001951810303a07508091129980080d0412404900344980d0205050a40da164102841d203401c0304000d010040c84007034040b40a441a84003144140219412405001c3c2803002e41601d44100038501c7d0001e0300403480980030f140011400b890710200c04119840780c41c0007050300d19080424006481030403803220b5010342d028030002c030b000e060a0113054143c211041303002030300525074100b400030707054080e140700c0c042e02003040140046036000c00d6003c1910854100150394822040c41c080e0701c0010800c01d89070380e0080c0394000040550101d80d46040380c1c403a46d20040f007241c010700e015840701101240c03800542d0081001c004400b400010400012400e807d105051100b60350103e5221072000d0074000001e0b500045500c0200c120301082000b03003004080442c203090a01004640d5901c14241c001e9401c0403540218001700c2418400e1462894101d00b9262204c0910380f01845031 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 165267913 1250 165266663 165266687
    0x2040506031311010e09070f05041502010e0106060f1b020109090f0504030e0130020c0715031404020904021e130c03050f0f0601050f04080a110108060109030b060f0f030d 75
    0x10b40081891075807036105050030f000b0411700820580090f04c4905068035103141e02000f041c1440b0081c84001003202210366100c1e00303480c0580001c01c0d9042c080d400142160250341082c81413100c0082860703180ca920030030581c90900c6444c00300103030301910300040e2403885481d4064004281800f0325280500415086180a035201e510303289003030482c02e001515540700040080101045d804a858600308521014000c0c080d00c2e04d00040c508047c444015080c0300303440e0080e07540071018801310f01020303a15102e0001507030040d864513580c0742400c1d800201c000c180a040a0701c10100c0001c19513500514001d1101011001046448040140b00316140075000325510f0601080c07034400022403990101110502c1092500c401c8001e80c0d0720400103458642010548401c090014040450700b49800c010f804c2007180190601d44000160800050641200134030f15410080310700000c2002940c884101500304808440d8841d0ba00c8842d004200d001d5041c0f0305980d4980305544086888640190307200382c00c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 165269163 1250 165267913 165267923
    0x90c12060c080603030f09040f060e060a090203010303090603020f090405040c14030f0a0611130305070512010c020a11010e0402120109060e091c0309080a02282004020405060313 78
    0x407003141d104069900481c01c40c0c040c3d030142c03c108a44a2644041001481d40200041c0000350f100c0a00081000b20307207440d005102010900f5040c4585031500c843d0f4080100100d070b60951456045540c01004a4085c2c41020141030300400c184944200480984174100b03030280c0208020716143c1404c501d4403c683c45120742442041c604803401d8140418201c10500c0b0000040400f86007a40e00c4100510240f1a8080b5011041c404000c01528200d051001107000e4401804100d003030508000d0b2802084022040d140c0c03400540d0024650049000c1c1a80d541155040e1580c02d42200143ea0301a582002c1c240e20070300c0000d016064031243c03800c00e411303a0179801c803c1003601d417511040b1103210005d031441001c0742d00c043c0030301035804080360302403040720000c0c0340105066038140d50300c0c50560031850003c00076801c1200d8802c6541544610309105070b08003040010860400d481c0e5406544c140001c0d0303608141243c49403a000e03151501140c1c018000945015a42d15200e6103846180c1054039003160 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 165270413 1250 165269163 165269171
    0x36060906030304030507050607021c05010207052b180b2d070312050c0f0304030305090606100f080a021e210c040b0a120e01060518040f03080a090c1206 67
    0x45090000580381138a0307104000381a120704140411545410001c800c0b6409883d464203100c580f41d0001d0720300b03c1c0318425000940c41b4995407400b1420040b40580880d4049007071046542114000c141030000000c0030708020442d5407800261081100381da8101120030400013404982d4404289541c4d510009007124548081d11381a043e0582c504c00d2900280000b50580391a2254101d240e1140b0742040d8400c0f1141d2512040040240c82c0b6001182c0c10340100c0d540b00104510f4100a0280c2c40d80407108035030000b01c0144c607020240600e0700780f00941c41005418030001e442c0480b640c0c115405845002c000f40601000e2440d4141c440d808a030075030840e070310101c500030a0940c5400d1618000d5114980542c1400e040c4548a00310381c10014000302005207a1511640010746407088040c0750084000200d102403c103020f04c4180d030b05000011840c1a0a1b03010400031460b008014040c40e94103240401e000d031100301c496400b40c5078251015090540c8a000040c92541e4011944006440b494080c8 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 165271663 1250 165270413 165270421
    0x23040e0c09010e1e09070e01030305180307210c080a0f030908011109040902010c060903120c050c0c091e090106030308010b09150c01110c0309010e0d0f02360609 71
    0x1102640c0c243d070421282c04d81201c80360500320b403658885134402464011500441d0744c8001c4044641820b03072003030740811000a61000906030881c2c0110054605400418032a4039000c0c01c0801d0446000da08249a62003030a0300b000c00c400880050010810340040f1000614541052140d031600c281c4100c001c10f0880c00001402d00c0103008155880c1d0304a10070608114060092001a21254100300d04000100030440d002403800e101e01e404050290342d074502100b06401c80c1710203d0704100450014007000f4812048a03a10028140701021070a545222040d207a01e0b40780b00804504680030602014000c013001050307041507215a04580c0283d5842c52180da032241c0b03440c4248100182c2c41c0e0024a080130f0011201011707002401000c50340d9000090303004c8080a03004894101c0b425045654200040d030b19803d6a112900c0c060110044071007401d0494156550f1041c40031408000380107056816641c194038a40c0700c598160304e66000d6601c0c1121107044180c1c981c0d2081100d00e42c0c0700d104200086 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 165272913 1250 165271663 165271679
    0x30b060910060e010c020d08030711010c140d1112011806050a0602030a0c05030423040b0913150f0504050307060501080c0d03120204050a120501060b070c23040e0c0901 74
    0x7103030440305107445640069142c4001141c94188607202a1b0308058451840c40000e8038182c01148034004940d2411301c64841c090f1400c1c250f402661648080062000c00640d00005043c21203405a2070180b00082c00c3e8000000d442c03950041c42c500d03500d00c10075400001100717001038201c810050002441004110f40b80c070104200c0d03041714040c00340160f00038043c000c4468000c0c0d0040d20028002d00460381480d5441c3c00090310400800321060005000d4107000145082c140644c2c1c11301e43c2d04031642d000a15004004071021115130801608014003000342000501d0a44d0141021042a01051185260030301f843c50766640411800c4414a10f41400040d004e88040f498a4011034010201c000e40b8003d40c600700ca42c60200c1d00d100c03a00d17503030804c00000d0b6907994890b08070050a11070002c0013003e0140c2004d07800c482441e4880900c1c1c010801c002c00020314005987d400f564601301540280c0b049001c09928410180720405400c9483c0c0208807001c190005448002140c007140c0d6000140e03228491 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 165274163 1250 165272913 165272941
    0x60306010b0703030b0102010e07080c0301050f07020d1d040518060906010501020d03091b080115150903020111150a0203060319020a060806011106041a01090902010c0605060a080304030b0609 84
    0x7031640c60742814004240003a00c640c0105010190500c008101d000b0b0030b400150416000b039021f01000c0d40000440485820207004240e0300c4221032081240c60b282031000a91a015043c10f00310030021806035441000034400285c0940081c054003c1005c1e16016020744031031442c01c03d00d82c0703491141d640001c0c55400001107150684006030301901958a10800507000b8020099003150781c0b00c4407204d40720003c104804084000c10306080041038001d4210110340b1156600d07040106440c0b0703101c070600300d0950400969402c496086c83c1000f1018680055641000c41444003520310340300001c140301c44810150050750181c48100c007650801c070300c40000c175031000e15078040003500454542d2040101c1030081101950105043c1440d00080c031080ca00030741417410854048071854601c040c0450203143c485100c03030152800302801c009824050700080c100705160340c07000389a5500e0f0340015065448008201008110f018200c03500e0319102d103054501c030401111018001c8444c400060050003034509 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 165275413 1250 165274163 165274169
    0x60513080a0321062718050604031d120106090b01181503090206030708010317070209040611131206050a09020d060b0f120606010f09060207060c02180103050703060506030601 77
    0x110390300c0125914114503d160b086101c050041039445030000342401c1c5c0e02038814100902c0075486480f4541d490440011600605000e03540085800103003400194000742464200350907013400b803182c6942000148a425103101d001c0d4011810b0703000038808500541005003035038420a000e0155850120044130040d0030f00720101100b0b000c0c1e102c00c2118004402081d0847c3d00d4600d8007060303010381500410891fa00c140c8038880024400d5004005011001a00340d0812142000c0e503454504290009140301c5009400a4881951060240c1c03001071514120350390108150f04034072409554010040c1342d001071031000d51341c4905140019223800400d104100e0b075a5401013100c01805040d4444000912324452141e800c80c0c4261500c1041d5a502402c516254041c040104210302c0c064000511903485000302d0414040400790a0000c26004200001034030010b01e0320021a642a0000480c014001021240300203442c01c004000c1c418041560000d490084100344100c1c1c0350034040c540c0d6450244 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 165276663 1250 165275413 165275417
    0x70302130b07020f0306072a031d0f0a0801200f0717041a030105031009020918030d060b0a020d050a05190302130e060118051c0203070b04060513080a03 67
    0x40034403210000001820006001501d0a02c1084d103490210780780000964400020440002004216110009010100c44484075900401d01666034028008405e0b02640049580c0c0100d07003981709403180f06003400302660080c180b1080c1562208068005c14140e01540c00398a90760703404803900b00c501800c90340f00da240702d20403034a007138160f8480501c0a40d03440b03089032501008000002c0e9107141c3c4031455a10303103410840503940354036103800c2524220b605204034884504218001007d40e03261003000d07601c522008002d000d00c84007841440e045100703620090ba9900c2ca01840402c041e00c1d5903015100c860a03e0302240c0c00c20f078801790250303003038054803800800040b010800701c00311442c40301030035840700c1041c1009030504040c004450b0000040742c01c0000c141503170608118503036901603003141490f032103a120146a6810180400d4001800b9040c83c0e044511410004c811500c04001000042c000d64821940b96912000300a1a6a01081c0b12406d58032018002003188240460070725000c66141d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 165277913 1250 165276663 165276697
    0x601080705010c1a04080d141b0a0309050319030c05030c040b1303020d03030506010e2b0f0f0b0103020f120303191104090203010e01080c2d0409140105070302 70
    0x1c40c0044441508103541182c6803085805590707a5010b16000b03030b5014510440035103456508229041c0104c80d40e0519520814200c4000d000444000a524045220040a44c66511080400168080c4c400e20302d00800c9480000303145418810700a01410f4070703e505a034144040c110506049a01780004d50700c942112008000c100604004440107042d0301d20281c2c4014401c50ba039170005150800c04403001c0c0c010a4944c03040112541e0301c08154100440d04403100001100c2d40e4840d400480c5041c03142212500c2c0380300008090117000408070800030750015404107400c00714680610413240a2004a020f001c1d40158030b080c524024242d4104041004015030031076031000740c0c03c1c0030300412616504040d5a10142290b6001007400148050588500056940e51515600850800e0140d000c600c240e0428400b001180e9201207001c8235960010111920111814101d000c020503102d0600d0361061130011000308000d42850000c41c001d101d40002c12555030341b84000e034207901c106054003002c0041 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 165279163 1250 165277913 165277919
    0x180506060d1a06040e0703060506040605040626100f0602060f04120c080c010b030705100807230d0e060601020109031b06020c010606051903020a0504270c030c020d0206010807 77
    0x55004001040c0320002e20325850602d100460656032054001e201d200203074008201d04036415014440003008151081440e0501e0014024014001c50040204018600031465084648401702d06100104a407140380142000010010013414034803a1059900401d00c0001d505d900228030b561045a41d0070440303586940e10707075031143d003a034203c01c51109010700928030301c01080038600075001184403440000703422071124080518004071980201e10512003c50703c0e060b200d40c09084242c015105050100351b00451007890301d0441e61400009208840102c1e208004085541017107592044000654215490342c500490a0381c4401001401052500900e001c04484000761a5400342c0100401400c008194003e01e080d60080e80c4808000b031000700e009400d000b03044c02ca09560360403c0c00c04502c1c1002503d80a0000e008a2040c8506004826580b0310004003030b10600c00c1001e158481004031089909001d4001c00d0070403c0c0c20014030510200e2902e490000900b1070503604554001d105086c6 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 165280413 1250 165279163 165279187
    0x270603020108060f01030f11030108010b0d051522050303070305180a0311120313050c01050c0c04050403030b04050f1b0702090a020f04030506041202100218040906200418050606 78
    0x260441d0304e50401da5580e0528041d00e0692259240c00245941c80316600d500d0b04000c2c0f401d452000700703030512034a009126000002d90014136262005031212500c600e60382c80405500320f2044645060701035894a0305c5d054100030300400154883c24058908014030b41703030344590008541c017400c01802d0541c04800c0c000c001c40d00404030406242d40400403120070500c0802c1000d000c2d0000d45862074080450442c403010814240140300c10305a007842c045040c85d0003031036020f94801e06100418003a41e5680c4c00300e03090512940003011400c41c041c006005505006030b48004640b0100c2e800b101003100c044007145504404001c941219400900da980e1986031b04905c20300a41c070980200300260400c020001c00503505104861003540180c0254461400603a0007030b003056850311400030030a1041001d6100050074a8061402c034006541c0040c149000b4500fa81c02040f13200b14a0282142e1000340e5400320103d20010001c0c1c0300006025548801c1e04d00150090311401c0c2d60056014070180311042c0151 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 165281663 1250 165280413 165280429
    0x7140702011413030f020a170d08040201020a08071101080606191b051608010f051e10091a010e0405040203060403050f070c090c0206060f010207090e030c0727060302010806 76
    0x29648204a03c0d01a0011038600001c0256000303d8405030084c915206500c0e003c0c0e005030003098580c1d89800d02d200c80003a00c2d521964031131410000d000d2140003240c10359208004407881268005106070361004281011004920780c1c1e100341c3e001800f60000201281000c1042d1071018410110f00040920328503000d490b801c0b010081002d2803c4801d0f100f00100e08100900b0303000c90b01c0e032a90884200d080042081c2500c10406141c0c007001c3c1130030309114403500f0390b40c8800b1410041c403690341d10326110201c613149078401540c0a41c2c0800c0c1000358550340080b841c0b00b4044070f600240c0304c40440c240f107030040c8029102c0868004c0c0d4183c010500041c082400b41c40240340b09581c02001034600201561a0099542160000700c2d8465503003a150f82c4013a010000d40da0002c0c0104d440d03e500d900030400003507482d601d5000f40c2c0e0340d2984881c0c1384184a401001611204032640040d2004d031038403401800540071801106510459100c100c0280038451441401c00343c0360180d45941c81a51084203001000b = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 165282913 1250 165281663 165281687
    0x1c08250b060d15020d020702030a08040501090b280c02040c0f120e030a1107030b09010c030e010513020f0310051e10060903120903150920010c02040504030c080a050301060201050714070201 83
    0x3440e000c10007c801030707405000c03d00540344038011458a0b141480b000400a200d143c00008010004001c598880003030720700d220744e42c1e201e00c1e10f04240182c2640c01c01c4840010004000390018101010310003015002064041c401e481940c0d8481043c0300194000c06844205102001705d03041005041390152190752003441000d001011151b84542ea40d440340380361002105c0e40c0320280d5441c0200c440b445da25005490b0050380d110001d03c49070800300c0d000210b01442a000034030905200b07007200e01c40d840c248001c00c0544909882049a8a809413105e1107085140044000818880e80081c00840b90700ca0341c1d8050f50801d42c1d0780034845066603503064144030444210401d0007540100000012a42c00326601d490541d1040810071030010300d401c001c0d42c072810502815102400c10324000fa640e1041012180c140c0403140450942c490b41029201c4100e0040098642480002c01e03000e4150480003c41c1262025802004242c0c0c4001e001c4800e0b078108160543c900000f04000030156202c1d8140e1180 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 165284163 1250 165282913 165282937
    0xa0b030d053112050d0807090506160212010f0609050c0705060f0c0417010c0216050d02240703110d03050601121d010203090a0c050301020304021c08250b060d1502 72
    0xa4281ca90401000d43d00e000034049615600c16000580300940c804c404940024041c03c1c520002404d040014900f800750301307070f4044030b0002014080203550790242d52204000080000700400f00b40c1140c104050700680c040c162060b4100760105030a0007080040f1030090381c100c000381841c2e03144c400c7c07900a41e0710f000e031029495040510002c80c03060041a104404100406c3c00082e01c03050354032002c0c3c28541e10f1b030840f0f051400701807000c001c0b61703c03421069100030b941121070b032a00c1d00b040000e4460b00902c40d00750111618021440004140d00b003102e00700760304442002c46003000000b1900300c05035401103030f445001030010401880c00c1d085c1c43c3c01c00800328207144500c40b80740318044a26400ca13001204c03100002e0b0301c84c00f40442800328074154503014081c264002e5165162036004240f18034001d101c999101056905c3d648140310b131074010307100059a02c0f0f4040710b02e46481044070744d405e5400380c0141c0e902c901d40e20200e1940e183c070320b4820404a07030145c486501e0000341601031009401c20322100308 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 165285413 1250 165284163 165284257
    0x70c03020f0d0f020c15043b100806040507050d03020c18010f0b0310120512070605040606091b0807090e0117060609010303020a0f15050a0b030d05 65
    0x88100c90070300c40e01c03424124950340c0c010b420621003c000c4c503241000010360301401000c40780b00084402c0d4021501540d100c0c07584080c815501c04442d818001411042024044d0319245081103000d403000310300d0203003801c40c10220720f0f542c540f2500c5481c1e4000307440c010019800080c040009003405805107030190b00900541ea1081c1040d00419020001d041403c4c86002d5104014007004107001c540c100909100d12403942503140640143c011140c0900400d0a0910f000c08001d040060030413101c40705000011300151100300515101d0090b18090750b04031480b5052803800f040e0503e403403240100112a980500d111004200020745000c04003601000030809071400100702c020b04146050f00800e04031b03c00c44000880800d40368117060014166500c28012007004001007a8006102c1d003100360010840c00388501c29182150050112945c40b00419080204015404c003240c0d01451140b00168140c03100241204003c40d1603110b0001100e1920010611114080002e64000c5403443d403007626041c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 165286663 1250 165285413 165285433
    0x60504020c0a0b07090501020a080304050a080f030403030617061f0f081b030a030f1119030c030e09100e0c04030206070818180403030c2106081b0603070c0302 70
    0x28180c1e0302100d400e88595000e80030000c104030551542a0b03126481c0e24020080e5410b000000352a4a0a1000580f5004000c404581440030500003400703404c1d40300b9000380e0380f440c45001040131600100d400740d0100749041c00000d11201c8000500400c1c003d64000b5250543d80c900340c0b09241c0e01035a0310002c15410801c0007041181340d00768110041c1034020000c100e040ea048803429441400d515050f40a504015469400250030113244007041510b418005081c003640741d00b0b940350810f400c25130541100e05038900c3c0705164104540c5060540259240d00b0500d0f1351209118800c202504e0290342e030161950100701402c0904a0340780c01c454401200c80ca0207a40b17030001011a040894143c078416030000740d0b038028020000f80c40d07400034025144511051200700002c2d00c5150014800303820725031038050600d1914031410000103400c24280202c48084d1301400d100000f00300c90b01446480788038042107516200b007a0491016400c500034407152842e43d43d010b00301e90b1a10310100440551283c8841d00b = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 165287769 1106 165286663 165286669
    0x43813020c030913090506041109160e06070813090b09070c03020d0c2a1806030507060c1b03060207030807030c0206061504051306090c0203120a0c030605 68
    0x84096006900390081c05045c0c69000100f55020707090400003000b800d1050052000c0c1c060703520300225543d07054001c8420001c094603d000c42c0d4800800f6240d807807d04001c0030b2451090784c2103070800c3e001c0c42e0503c2c0810000d42042229684801e01d01502d0704180c81107d600020364645568000308944002c0c4d110351034074010000300006448600e080c0030303c511004e9255524104034a04c030b42542d134042501c410a502682001d0360102000c031780b9106160240905423a01300c400380002d289822010b8400383c0f0030301e03003c8807244d203401569401c00c401035504400942c001c1002503036407122450010009a0020050707000c0c14179111420440503030020780c8a40c40300e030644501400da6250011403000d03014a5222981c00220012040100501600301c03c040b02d103418400d2050024003c01030380c0303038003c003a010b40d81c0e240510000f4160070041c0c4c12035a24a807243c140007400640722404 = true := by decide +kernel

theorem cover : BRFrame.Cov 165107913 165287769 := by
  have h0 := BRFrame.cov_init 165107913
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 165107913 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 165107913 ≤ n) (h2 : n < 165287769) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
