-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5487
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T16:01:11.486393+00:00
-- url     : https://prove2.me/submissions/5b8f6a3b-ecd0-4b56-83fb-afe722f9cd32

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 986690647 ≤ n < 986870503 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 986691897 1250 986690647 986690669
    0x130501061107210602031f06090806061008013305180405100b0c1204090b040b0d02090106260702010c08220b0403030b0d050c03011a0a0b03060a0902120709 69
    0x3400140b0040b100c031981641d0040c40542c1c0c0b07568040c00074807220030700184121000c01c06540464401d0b00101134005503600b0b0ac0c2202c105a40e65020400e81000001c40c003000b02c3c0380b0000601142c0a211016911842528115404042e80035144810050032000c1000007070008114000b1031403514600116803401200d0a00c65030400e50302c460801004d901c14244640b00009040003015414003001c02c0c102c2c40281d4090302c0350b9544030b01e070001d4030740e920301c4034459071500c00c2805507840c102410344640307a000f921106039031f0b0901c1c0054500681c90000e510790580d505403450314011101110b14800c40c959070010500549078139016100850190030000000c5401d000c01c580c2d20486038007040502d4000300480c800382c685040540040c1445841c49800c0821040b034441803260004108035015000d030000c004030103607072440f0f40c140c031403d11400b540008500c00c10001d1100100207036400400092681c0107555446071034100303d9000c6a03286419400040401500940050350440141250020303 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 986693147 1250 986691897 986691929
    0x1060912110913060c0e0406080303040c03020411130f0602060f190b04020405300c0f040c11030304060c090b0712030c0201020906040e010f0b0903070311130501061107 74
    0x1d610070520304030481c1c0c1e0080d01480300254503880800c00c592000d50b085007040141604203600206540116060180901e09080000440d64400012030b4407654004103000340d200d05650801c8064845200c151280c00414080c000462041d200d40d01c00a122019041001c0c0d854000041d0038202c0081a505100307031800d0400c0708030100040317040300200c2c1c801c01c0010200d070f0000009000b0b025a0304110303000720840100304510300304003a49003840040c0041c22120092010a1a42e072112407c00c8a078001a40e4600c144480c201500103268402d41410b00a004007240e0110350b1842e0400c8900f90358581d102c49881d521036400c04142009032034800c18280c034040c0c190f2a820400034442040d107040507502c001285e05e1920030760513034607952002011165190703a12000301c01110b1081c0075040600300e55020001d5200a600220307424800041c003e007075118659102c0c503064880c03900d040342e041051070a00a10102c1d552180ba4041c15060b02eaa4440308000b004040c03510300941c00c0040c0c060300340d0103 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 986694397 1250 986693147 986693153
    0xa11060901080c130306060e06030f0705010923060304080d0507021623030613110307060e060c01020f120708070804032102090301090b04030f0318120c050f0601060912 74
    0x82c01d03d900000c08016955114002e8504510100e99507002401e200d1500d030012503030120080c007080c040c0108508170340c0300710480c41c101e03a02e541440c03241c00d0114000000402100702d16240c8101c0160341110b440d041c0b070780c208000c68480d90088800301d80102c0001440000d000151007040e82045080c4010b0606941e0700340030748180e041502070240384404c02101120000255903c14030040e8000c3c0c00d60b052400c108103440284103080744101c40d040e102420000703c5040002c0c803541200c2c540e6990319590070b002c0c011320902d079203c2402c2010b195020098188006882030080441c54110721031400140b4040800512664015041e001040139120038000070a6100c0c4440020300d01002602010b0506804140020f2080c984000c2c0c0550034801c899090044114001c6d1040380280c0310040d0500702e602d030840442d41e14905040c484018280b03080c0c04a03180c0541da074a05891800c2108071140c1e1074403003515181d54580c0e60203003075010704010320159a01c100c65200421070000303842c90004040e5 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 986695647 1250 986694397 986694407
    0x204140a020a0818060118020c0115090f02190f0915090504141e060d05190501051b04060e0609210d0f0914031504030e090105010e030312040201110f0a11060901 71
    0x1c400d1610038100410391f60b65145103581190a40c40701d02c1d00800985104c1420f0141c0b04400744030b180001480e200540840303110074002c4449801824614000c1c481840c03500751401000512a60104080403001080754001c10220110b01d40b0315451b85d00d042c6140ca410031041e1080c10104c09a82307001c560500400004016050500c25103032529200580c0d1031101060006650706006403062044210b2480300000002d807003804c130750249000384100e50f6010182d140940b070080c100381c2641e030708000400c0050b00c604099020039030018406480e14840000103140c42840201041c0125880031004440340010010b0082c01502030805c0310010a4a0602802c96011445503008400802031101c210b9034060080211880c024556000d680c2840d0a00508040e46c80c140c242c054040c000010402d5030107a06c2d070307403640d200050045180c40461101c00c440e0010140c01203050018000300c511140710180021900c84020344000c180413851804d0002c180d09580b40101c1c0150010046928140d03801 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 986696897 1250 986695647 986695649
    0x13080a150207320102042d0e0714090d030e03010f060b1c0e030a020d09050a05100f0207052107090209030316050a1e02010206070207140103090204140a020a08180601 73
    0x60b0000c1c4080c0d503000c1c4205000103800001c3d00c051035100103804200704044540003404119408058502c0b21640c0107011400c100902071a01300710030100000e25402e100c0c0b280802c07200508a0310a007405046008240b80700351642c0d088000c0fa040956034030a5007400d02c1030055415003145d06100f000d00e00b40d0070f10402c0c4a084000c130300480200c4220342c0340c50441d42040ea1500d0450301201e0380d400d6041c40003902c402d510301d10800000c0e01001d0004582c036000c0510025101e005061000b210308000b015140300c041c00c000842580110079000400b03645074608083c481031107048400d9024072044100781050026040000c507240f0600005072103840c0042551400075200030000c2072100107040c4a0f191100c8903a00038030003003108248400245a10340400300c0203100380c08440351501c4440060b40c44407060301440c202c100c565261007071158485e070441c0e0117190002d4800a142013454400c0c4800c004100c034000d21803034001850200d150b40c007010f11a0b001a26003007403081402004980c940320601 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 986698147 1250 986696897 986696933
    0x1808120a050f060d03091517070c08030c1605070902040914040507050607020a1701020a0801050105070b0609070509121c020d0e09070e1c0302060c0408060c07030513080a150207 78
    0x4100380f0f013401c01d070050340140c3c0542040c0b01044425413203010300420158482c02041c0384185420003046035035010b60442c3c01a1540b003881c4c1401c5595000c2c0c81c000030340150891804404900541d0b401190080c450740e00904218000940d0355406c0c1025801524245800c250803001c41d034082102090300030038401c080d10340c00c450503603550b00300780001781902c03007035401206504840455441d50420b05500910109c4560744407024580e80c1d5000542d2103004022001d0003084880001541c0c0b85400c0c1c1c0800d9000d909802d00505014410000c43c4811119012030262a0302807600184900c0300d00040d4200e1803418401000215094140100345032100c075101401340342030b04041072aa6009031030001c0070700009040c80c1c2032011865500340080008100c2036000d40a0400802c807180345c0c2104407002c1c2d41e01c5c04000c00d244d4440887d10301c1150300408040d810014280070001440102c24100700c0100071480092a1011160400c504525151070b98602c00900c1040310030005400c0405080517041 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 986699397 1250 986698147 986698159
    0xf020709020d0209100f080c070b04060506030f030f0310270519020d0507180b09211905121e0304020301110307091403010204060c02060d1808120a050f06 68
    0x11410764841c020b4004e09200f141e0100f400c2d081300000030341c001412005240c41c1e85e10b601854991200710641c611680c50301030300311840f000024000c81c180d40c0106400410160449040d19060800c550454011141818104200006100c01c01401c404908090701c0116618250184c0701000f9618420140021180b07980d01c07100040c8084201d01c000c0040815000c0d404c0d0340e90050140c80400400d000c58440b004200380e4900490290303141c290b42c2003940c0e5190303111840d00d440301d010043c04045050308940601c00b52a1510141141403140c40012002444059061041071920f54140050140100c1220109200d8032020b142035800071345115503e001003654940b42c0d40003090140c0702d9102c20001d200e0001060001241d40045500129482e01403c103c0125103042014280d110303038411103000407042c403444809494940000c0001100b8a20009031800800d940704c5103a0007035620a40d1000c4021540e24501e0750800c3c46030342e010b28420700c104000c0c5405610120803020240289000e08 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 986700647 1250 986699397 986699407
    0xa0e0c160f020d120f0801080d0c0203030d0615080108160504050c070b040803100603021e1b01050c040603050f0603460c05060f120c0d02030a0e0d0f02070902 70
    0x40501a0200c000b0780181081e0901103141c24000c1041200c0e542070000142c40140f0008044e101c0d00c05281611524005011501b1050100f100d10308520300d8141e0b0700d80010090524003c410b07208180042003a80350072455413820100c041c00d2800168006440b9820050440c602c0d0b0144e01c13800360079a0000c5400042c00d4550404d5030740e05000e618401402e5080c03402c2800144140a40958412a010315020441940340d280440503030107682e500f010030941020300a02e41d51a07031030141c10700c0500c00759145000300c140040503080d00e2058030381c40490714000506200381b0303605000d6243d1068000c4600b07007150500301c0210340e0b00c01c011848075038400300040807040619401e88a81070040c81c40041200419184100845c01c00c0b90210308494001866400003150b041241c01d54404141820000342001391303041420410240c010014042c01c201001005104050340c806140a1055142c0c0002c840703007038134412392424102d00601c1041c0030345000b8408030107500045080554010143c0980c1715 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 986701897 1250 986700647 986700653
    0x6020a05040801090303091b0303050301091a1011010506010c050a02101101061d011203051801020a06110904050a020c120d0207061103042604090e0f03180a0e0c16 72
    0x40e00550704002d03459420040d41c14149941500302d003440e580503c018004c00d01c3e00e15401d0003488220310004001c9102440100070807951540110341c8103200c20300d1103c8040d80c0b400020041044181060007081c07180003401e1800b8403d10136903034410303c00e003800c0c40c5107486074603580c0e540c180007c6c0080c031031500c000a43c124144500600c500f182507640c028800c403030b180c2c2c000035040c51010301040940007201e80000744104c003101e980009243c054075060701e000e10028030300400c0814191000d055104180c81d5000140c403610540351030703441e100c0159884248240401007603a5001d0302c1481c0c61030061146000070306012541780401000ca000c040da4a501191040d0301a018000c030150042d442c04280c0c86e902c00c0a60015407090f4407811480344001c0d281c0c52140c1040c4032210b0b0300c2d900e01205010602000002e503011245900d1a6022a000344005550341495540002006612410500b07010806401c052034040064121f148a1850071702c0d14440907021400380703090880210707821483d81014 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 986703147 1250 986701897 986701907
    0x907240e060a0c170703030b0906010c030c17040e0720280b040c1a070b04030804021f09050f0901121e060f0506100c0f081806031e010501090b040306020a 68
    0x1641d6813110903e01c0c410692103190721035800c501c4090300440d040c40c01a010a00c1c0504005100b654161a00705404040762070848042c6417010b01102c4080c0d80c0511407090b11350210142c4003c0c20640c2c4129450710304008024910042c0032090003109290f0915001000b5000c160705403114a030001a071007c000300c5804410444189501810320002c2c8807d001c240f220905048040d10411280351b03151164654004600340f10395107019142112403804500040c0c8100380580e0400d000030600d07111603d4800d41900b26080203d44800800c44200f8200a07500f000711a9241002080b202c11640390302d000c048002d09400581d0042205038803402001d03841c10702c84828508a900284108451847c1d2500f0034010720003510810301c074a20008181003400c2c401c144058200794025140104007030301e5544c0110035042148035468031416042c1520440c0c44501c06507110300751500701c29650304050301140340c5203401a04800d0420600802c10300c0111301850031541269404440141e5440c54924201c1e0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 986704397 1250 986703147 986703167
    0x60907080a090206280c08030a0911090a0b0f03030c1b0105130902073305060307051009030c0b19050a020a020901062d1d0a08060907240e060a 63
    0x54041008500c600322040403000304800c0c46510f1000c1d101c440699071054946c60604400180b040900700b00041e04210039070086055280324080260b0b04c503800b18001050145c1c2201d2400c80719942d45e40c2c04406181110580c84104820303805107281080d07014403541c45044403429840c96446541e0010207a902c0360086802200d060345402a20940f903412110195004100c107075185a1190030054070a1100358952840c18209401380e007150500102c1640a45401496568180030f40d500c0011603403284000c0140b01440741d42c071080c0d00c0c1e06500e0030050114264200c082041810305c40c10782c41c5007001d0b0229040036100c3c10100e88030b40c2c070301004924040b02c406000f9082200c1000010b040380d00020700c240383d410341403590000c2d000811000319000604620400005851800b0a170001e02250941c0d11031400282c4480880c0e62a02283c5241034015510f421131940181c0c0100588003019440034841007036003000610f2415560720003003002c421102400c0c45840005180c0b5070060140403041 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 986705647 1250 986704397 986704399
    0x4030f020a050d030203040f1d040213090b18100b0f0105031023040b040b011b020319051e07050f1201140109020a110102040e150604080604061a0306060907080a0902 73
    0x22008011380f40094403900309105d04a00211040e078041510b043ea140d01640d5001e503240c0c1040e00e6078440e02004000900d0702c031001b07200365981004101040400c00e046114002002c401c1a80d1481f40c8810352a040c284400c881500d032400d030460341959640e104441c0351035824608142c40b0344030701d00d1840d80148070754055000d06052045095040c01600e40d920703002c08040350100001c6a1650034041558040007500d40020200383c40a11402000b0648001c0c19002504aa030702d00c1c282134100305d0315990300b2000d5a550703200c5c010421010862030300d601c004c01c045c440070b0084a894507000c1000c400500411a00c42ca07041d00b090800071009502c00544018040c000b1441e03947c0d01c4410324002d40c0110341102c0001c062078470400c011001402224222201c04005089a5035030301e03004034078100d1080c241e9511003820000056000801c1141341c3c0140d0242000090b400d0070718503d10303124058513600f00c4c0070b5000202004005e5032091901640312190b42000c1813155500c488150040444210007 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 986706897 1250 986705647 986705659
    0x714040f060e010201050915090c091f12080406032a0c03020f03040e06040e250f050904030e010f02010608070e04050706020304030c03120219050d02012004030f020a05 74
    0x19031080d000c80c203404403151511a6100d21003110012403d80c0c1084480c00d1a55103c03202c0440815540010075903c9040384c07040d140d920340010006401890207407020305036060420318125030040c806d002c620051080003c010a020100c0d030700d234410790080b0700c611014959200c4054042c44500040501c061203421403000780b841a00b0400b401d00400700f9000e034014410a2100100c05800004031780503a078101c0d0704640995514002c00c4050000c02074040c049009548400558040301425202e0441ca58a100036200707040019100b2401219400340e0310031000c440a100c00319400030442c0c03c02450a10b0144a46022200305070301500240e8421a410710415400040c881071444085000300e1040041e14140ea984500890b52400b0f50700000e080540007100401c0041e50541e03044c0f20303440e01ea00643e1071107442c840000c2d096640e1520142e920303170446141480a20390a12401104000800074244d0b0f089080003140017502460000030300c24460301122400759501e411f000380040034000c0174 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 986708147 1250 986706897 986706899
    0x917070c150f030b0f03070b030a09060e0f1c0f030b04060b030112141b060c07051918060f1818051c09152a0305041e080a0b071404 58
    0x9080c141000000c02c0080c1c94101404618503061003500d044035001401404240d083c0003002c41564005400c0c2d480315a903441044000909900071592506444006040000752440d200d43c101142049801c50b105252080da06000390403100071000b00d0301c24a000254141c14202250085c82aa00a80048803011000061104814a810b8001d510550360562800d196940305540d84d0640f241c0041d951829a21145c07007418000064500f0804c4c45085a1409036500046001a442c4050f4441c10201c21001402a503a14556444407c0840c040801105181011100071548130b802441d0440f40c203941e5120780d80c895504001c40c0300c010b84c00007907020113152408940e1000b0940c4402c0d54980341e688003041150041c01c03040101c0d01d00b100c1030480300503444411140070064105500e0428041d460401321062400c1000c41030900c26100c2c01d0f0382d03d0a0001d001d8169244512055084c80c81e810306000a100100d0036066140c1e021408a2807a16288402d4a4403825080b040c1303600c1a000c10 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 986709397 1250 986708147 986708189
    0xa1b030c150f0f020906070f23150124030b220b121903051b151f050a03060f02040506130608150d0f03021009031e030917070c 56
    0x2c007500380628040310070019003041c01410070990041d00d582940c092000d000c004041000a03501600704c030300c10741034000c2ca0b05902499409030b02442c550442c0591009444d070101c1400070b0380c0180034005880c610703443d00000449a000c01c0041500c200205521640051145d40b140d150340300446227164075411084442d45000c800a060300c00c02c940c4504001c1442c2809008003184072030888034000186100820552000d54166120280360b8612340144c0e010b4081c469410302488100d0b04819810310303161b00b0498888140303100e003d0264090494960000c1007265600390001c01100d038841c10200d020310345210414000d001e15070280c0d8003ea4005602c009038280c403107000b010750703e8580310611141c07a15510a50545081440d2a80010b1800c440c040850ba0796041448198441c4c0704075171044001c4103201e400e403155018100e010590880741d07900a0484c0c60800a40307145c1a01e0200040d0805494015104983c1c03800e440d03100c040094401c0603c00481d4912020b041c00519013914032030444 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 986710647 1250 986709397 986709401
    0xf09053d0e100801060518060403120e101103070b04060b041e11210421120b06131a0c030f030601120501030b07030b12010c0c020310020a1b030c15 65
    0xa00098800d00908600101030390044800f0f82c1628115500c4c50304200d120071414019903002c0c51180d900510900000001520340344020203070021659402c6032504881b03091140700207201041409100c1074050001c4043c100100382c45a164110360035580303603203560400750000c14494022942050514401104044088a1112000b40b8203001000003690700301890155002e0b00e031080c0040e000480ca0100e03c8640c24507401c2e0458005c400d1b0040c201c51a8600380d07900c0a05502040c082038100e0090300e01c00e041c5204500380103000f81d41c22443c01104581085080c46540200144484111450301080c4003010030b8504003040c6c10101c0c0c0d035078500c400c9100c006401c22100607002412004030042c101d0000c0c0645070403294001103034036007078581034000d8015044903d0140c4d0428131510b40004104c009000754066101a0b480d48410b00e20740d4018941050300422110407501e004001c0494450761150350103080e81c500010010200e07650303241c122812505800050720058101d120b203000d0941035 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 986711897 1250 986710647 986710667
    0xa03060905092d0606060a030212070809010c0507050616020a08070309230d020f01030b090103060b010807020a0521040e070314060307030c03020f0a0b030f070f09053d 74
    0x501e40c200c08068080b010760f0782a070f100d041e1100341504200d001c80c4160401401070800740c0031504015050000003904410030f50750894080001035409005e020501e2000c1c401c4d041059540d1078000d151203d9615000c0c0e0320440580074080140001d81c0c00b0b46102d1081c8004007010781d206d5031072a501d88581c00c0080002e5a1030003240e2086110314400500b5403048102216200ca0103095035554142d80e40800c10304044c035400507418552a5400a0401e0f03840d0902240610701c907040010b60448100001400204001d0140c01036500404809010410000d0084410501070700d1030804880e405908607100e02884e4450404240d00c0ca0a0000540d056080451100c50400214043d903488404240c0e41d10316510019081c415403010500242c244584041e0350320001628010300944d50b41d03401e02c3c070340c0c0c800c49103420100d00f00024409182e6006c4410b4240c2c81c1395180290380c0c02c5c200400521740d55400403602c1040b48032403a003a5154446201820001d80700c0c80e20101503c4800203000e4010404 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 986713147 1250 986711897 986711923
    0x130b1c030206071d0907020309040914010c0206010e0f09010207140c0f030c01052208070f030b0a05010e13020f03010f09150212131e06060603151a0a0306090509 71
    0x40d001c0098242c6106071841307400c08900746000c100c0c04002000b48041c0c08805881e0a0031400108003545041d19140901a820703841000c04060607400368810030300b11b0311110300f800304540101004105d240c80480900360000c103100c81c4084107407108030f01c0c240281310f000c0006046140c480030500c90110041180c092586090f03c1c40503109002c6400c25440c1c0710f0703043c41d4070302040c020b0184480911640d0b01900c000402401c1404580381c5407881c6600d00304099010151038441994284100b02c94203001a8101540380340034003455040c50006001c80000608941b04102e0300f59180c000d5603074440c59000e504102500801614a440e1000005444145011b40304001e4601d6105140180c51085a080c0802442c1c60302550301d98500243c41c0c410700180c00e4411145402d032031021007c51080780040b56208080000b00a8030300700000e81a56464a035001c200b00c82c8c0c1608100908544040c101c40c245c03c00f0f4400d9442107100420b800500300e81e00117100c45840c0034108640130704000f841d001c490b50 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 986714397 1250 986713147 986713153
    0x504030e040b01140d0c140706020c0706020c130c02010b130b010e03030c07060309051006090f0608011b26010f03050c0907090312110f1f021305130b1c0302 69
    0x3510200661310000001e0800080050401039502040003540c083c420002080c0380c0f003a0450107200da25170940d0444002914201c0c0d00081a82c003140b0104010b078000c280500160181c1510480000c003845001e100c80030b0003545500c52403081c4c0e8030070340c406032003601c005046400800036514050001c015a20280340881d0401000b03505503d000030a48005440280040500f14101301d0114041d2540c124211441c0c4924004954488130601410300984042e500c00030f8000701401d01001610a1a8401e07020b136490b1203c40030040d80000a1a0440c12480c00c03c1404094140c1031420701d6074500c00002038a0000800100e0074901264100080700e009208641c4484998001c1065501d001d42d66100820880c40040001a040c40700791000408603050480462008004403410b01020aa086801d41c004241078081641c0c48081d105901082a03421070508000c04d40d49018503590303009842c4240000c80c50380700c0d8000710350440030034050050111300e03e40d008500c0360041a0701c1e400302100540 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 986715647 1250 986714397 986714411
    0x30060a0b03240607061d160b0d0b0d0305030915010302011d01120c020f0c04050906072616020723040203060307080102161104021c02160506130b0c03090c19090504030e04 75
    0x480002a03d108244c00d241460003914034060140100349e0080c140c1100031620b5003119085503407600000c941c00382c003031785035140d507464502c82d980d00b082d442e45030840da0b0b44003034801400981d0b40141e100e82810402d543c8070070081e0000340180c03114605000e49001160922a503458032030703404a400c43c48003580104590103103010804000503913504a81c5140c480d0f0058000810b041e1054202608041420701051a038a449107200c81d43c940b000c41d80d005485910300901c84259504000c080c0c000d040481e40f168046540b01508500c00d6400d80c1c11b45c0c4a40d40100104d21640e038207005031401046900f0003150340c1d0701c130595203804403910040c0036900d200303500740001c082d410725008407840d108003d03148804d42d4400d19140300003034001c0040075100c0c4290550440000d0001c0220a0042661900c5845248114074100070300c020000c1c450340c01d0b45000d0090080740000010700c030303150381340840c0c0134601059a41d005c13860b000d850341e000240e014101001e0000341608a2300741606110151824880300d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 986716897 1250 986715647 986715701
    0xf1609030b072f01022d09150405040614090702060f150a050a1508130308010501270e01050f01020c030a0224040923040b04080f30060a0b0324060706 66
    0x1070302d003812190703c1500b0b00308107201441c680b1100e810391103c0c2c0c0411039409c058403080444e080703501d00c3c0c000b024000c0d0901c110302c409141030380603168490f405100034882841c1201240000e4040501300c030550040c400c075160510380d03461030305c440902009481015131355500c2842c0340941c660362502034049a050740105204981038007415032a1901926414926460040119001d854555601c0002c0426041c010404900200c052005104401d10310690754184810010750000f4035084505551044072001d440e030304c001c14020340703107038045602100c002d8a8286502c0b5200010034103d0b6189000100030a0b80c01541d40001100d241c402c0c07401a03170402c14044800c5e142000d60700904007922840010b00041c2059000b414990743c01d03540395052000c4000d0b4070170f400d1031b04902168090140050b0034503403a03d000340b041d4040403c80d00c2403800c612f4841040d100344000307400900e41d40b1906843c1494000c81c1d07103107a1070300440500f00599415050805500802d40b20742d840320883c0d4842510028 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 986718147 1250 986716897 986716957
    0x5070f020a050604120507060c0903030806010c020a030f020102030f0c2b3c0c0b060301020f03070e0103090209010618060807020d180e0f1609030b072f0102 69
    0x103465102c1c00800d229121a110b07080034855041c84c4008102e0100400000202d48d8094040c800740541c0307580301444e0861070042c01c284c41c01850f007070401903950f09a001680d280040342c4226034001c1184808903129000407800e52007114840118528009803a071a80c00c000950803040004811001c4260f601e0003142d60700700e030080581c04000801040700e010400410720f49114505810302200080c1c010040d042d01403001c1005000c101090b6188061414003000900075540000124003c40c50601180078031241400042e2043c0e04202012500c0c00859002c0d80c000b0101640091070303181c03250381d1040c0050a095103241e0f615810005440700041040c000d0340c400d4003400294002d4415100d622600711998100350340e051100764544000080c0791111000c4047c05503030405c070100c245280440c427540c2845200103443e0b0400040800070000316454645050304a0302c1460050318204200c40d9142c0790300c0803807214180b11704054650b03c100c814158010400001d8404400b2071401d080c04148030 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 986719397 1250 986718147 986718163
    0x21303080304120f0e041e1517071508040c0b1603180e0c0d1d06071e0203160f05010e0c180c090103091703010b07060522020f0a0b0c0105070f02 64
    0x120301e4145d0300340c2940c40c207600101c07a83c0700c1c8030360024401c1102030b2650381030350745072404240c160f0340e1003900340f1143c0034000c0c0c0888006034010090180a19040b00e1000701610504500d0030024004003240811070007048420003040003014454079050b58641e219203005d000702003140845c0e0381c4030744101840c5140350301008a545440b00ca80d03195582c00080740c401d40c000c60340d40c11110760762011080c00e03000b20a45100000020340c010b041d030345000030010309610f680c071105c0d4100520800b041c9843c135a0000458415011a5030340c80744404d514a000440041810b200811550910031f51071010035000414500c1c845085440920f000b00032002842016804c3e944074000420800480c083d42d406908500c030365601c210364002400b0150880038841e0f070001e0300000c4480301c0008909080c40200e028498128803610100342d6003100404810a912a00c1c40c4028010010300051500a6480100b0383c0c00409500c40b90595078900c40c02c5a50081c0401c0b904600480c903080c00721a003191000503184 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 986720647 1250 986719397 986719427
    0x3040b0403050132010b0f0d060f0f0509010b0a0f050705031c050a0207170a09030203060106020a02010210060b070f060f0c030504150917160f06051005010311070206090402130308030412 82
    0x41403070b42041c0f00060564041d18503003159810070042c1c400d08230400c3c07151100a100407a0746c9900f46082682003000002c41c0e61009102d503d400d001400042404030840e4006c0791503082000d1180c82e210710981e400c7c01490400340103404003190310709006241501a2100010083c070400c10350f030360130700d606080740038a181c09081440000003180b01892174100410fa107c0c864185404010b640e80c2c00030340380086c02d802403001a08025410011560108484a003443d11103009000007800c2040c0b6103d107008689006c0c0082c40124111070074041c0070b070701c14180e0403d426001d0108500980025000d0202a2021100c2d4088600c01d402748038024031468407016400700080b0307040c80322506514460341140e03180c55034015099102c500014010448100c0d03c80c81000d0218a0f8585580d9442c00c4910302e40c0118145410a015010342c1ca202c0d40840f5069681221050f880301c0d000c0002c078001f07010710041c0c05942c41c102c100104c207011204000c1c51089100361058003103000704d04000c0303a11a00e01c8001c2 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 986721897 1250 986720647 986720741
    0x12030a0c032105131716110109181d030c0601121704060e03012003011217040815150105040b09030120180303090607030e0303040b04030501 62
    0x4280041d100c2c2c1e00342d090600350003402c003202e036080341001400c5a20a44280601000d200989404c01100309680c4000200282d50740341011540b80c4d4500403010380d4240102500042602211541e00400c21070b030203458036108049441001c0c030940c4008010002001900700c601c000700f07501007100041142d00366a1600d024228a9103002c4540284a0f00694100c80400c1d101c1810703034040c2c82c074802401c0101420360320312000d41001018582180c800e8a0001c0314107046400361800c0c16026802c0301c2c11aa040302403100744a080b030400060b06a174041043d0281100024001810b5100242c600c0303901480a88204103a00c403034508070a100010046c46002c11410302042001c23a071031002802c41c1c1c58001c4c0020035a440001c0c3d20f0b2018004041c0d003d42d03041e80100d5280c0883c1c17a418044100b60100ba8001d51505007000d001a4050081070070040400a05035541006a201841502e00034000c0c060002d80700c80d00c80c605940a03001a03280008c001e1408131800c9019198401c0500c88441c51f4909 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 986723147 1250 986721897 986721917
    0x9050f030105011d090a0f1a010e0f24030105010b300c0d0b04240b0705100507030905030a021b06032703040b07050c0a050909150702070e0c0912030a 66
    0x41c40089544c0104154841d00980e0f04000100310030708401c1110074401d00f004038140300080743c102080d80b01a00400031010b0080e04118000c520b422034590030190501210305241651100c1ea015043c060780403d13059420305000086021509014003402d806c80c900d014451400b5500c0c40000c840105030034a0300700f5550300030814080341d810003040c4510140c0b174085403004141e8042026a54400c0321007800b40350072400e1000303d440440d20390000d8485828214038014a5403200356460703004545007007042d03542c0c0001c04c900074000d40c045031349686d005040c3c80e2a131458440107911004072030100e050114a2140c0b21015182c0b10007207911602c401c099000792032410701d4031840c2d19003004c2003112003484100008107103215060301030310301c07248a6001041c0d0b8000e041c040c0705920380198482c5010701c441c1c100748081c0c1c04000c02c0c800c4043c0f2111000f03032040d41e51803000b285421150fa100031000c111040522490121203070041ca00840c080d41c0c560456a010008079580f4401d00c3e2147c1c0025608c004 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 986724397 1250 986723147 986723189
    0x90901180f0303150e060a0807051003051e0f0a0614060f03041113061d010e0f1306050412030b150f0f04030804090207050714060a0e1f09050f03010501 67
    0x40540322402840c0029007503040c41e8115504a03050703009514035a2070102005044e280c47c05248019010400c06015410b240c8800700340c2001c8440007c4c8145034440c000502d007942c00340c05c46c0321108a400c81a44c241e0805c40c0da0807000b15020b03980a40002e041400c080303003200d02c5410844503044007620292402103038002101240d000608111840804000726054642d1445d020103103110640000054183c40c0001c0c4103503046100416000052800c401045610b40703c10384594000070510307a2241d141d4898482c607401c0c948034030000f00707070078680b40c01d010034001700d20080307143d001c843d4400300100c110000803c010658450b90b00360300c800080041c0004014500c001e014540d003224402e90070242c8030303950545c0c2a006608103d21140c0d01260304424054100800c40c020200f125208500c01a0071000c6a5030344a52080712090200c1d2281003c0c041c0c41d03042440d07101c114100d4800001c5590800c00803d11b603c10300c03406110f004103c51000580c0b4040c403030383e03048a1034000d042c2585e45c08a1 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 986725647 1250 986724397 986724413
    0x170106020c1302120108100c030b030a03140706020a08011703091e15120a20092b0f02040b2d060408030c010606120c0f080a0f0f06030209090118 64
    0x100c00b01c00c0c090b02803250306590b280242070a4040e010010241c01c4d400d0340040680f0031210055421010036050011056140d24045605260941c1520340346240130040e00441c9414810084003d00340f078800126125480e5002c04c2250507074201c172800910741c2015170b84150756400341d184425030001d0f601030492000c018a204a04c81d842c0050300380005007801c20030900701600308408680c08135840104009815403d40300f035884400d002c68168200c60088108000c0c1d034010710050703030701460008610949400c2c4244036910390343d82603004050862100c0c500201003400c3c41c003040303005500f800c07021440741c0f40c8680c002e1603000ac0c841101980c54054406100504810102c3c1c5400200800c40411882401d10080507243d98107800401d2483c1b07042c41c01030240b1104100b80c08c0c16854280c940300072aa000b21501d007000074034a00f810741515a007000320024044141024002c9103000e0130102110620b07005002120b008451201285c2d5598030614280c910300051981d10512003c541c4002032081 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 986726897 1250 986725647 986725669
    0x1060611030d1d01180212070602030301060539010b0f0d0b040821010816030c440c04090c0e0c0d0501090504140109080f0c100c0c03170106020c 64
    0x1c50036a8019040700a0014215001d035070403041a83c4410178071030158100120020200d20082000705511468100000d4036800f042c012170382005130001c2c00c000c0c10089807180990702528407090025404035078044107441e5a40f40011a115400d004102e4010300e40070314a40d8a80310040c2004403208034641d00c8009200c4001c0013142c1880b401e0101c000100c0904c036580428608906150340e465044c0f1640314501007000662603004041203c051001a55a9030305404496005240003044d5040b01c14201e01100002046410b102c1c140300d250074690300f100c0d8007020385415001030720a44c1e640d860610041d80c00d5943e0182c0450000300c2c0070015491948003081e4480042c02d40c190400a80303103100025180c003079010102640d02d54040c00705120326501014a0005800000c0284890036652206070340968008141c5000b4045508002d1110500c4424a0020303000c02c20414031040c080040c01581384001c080e4009407284040e000c1318003407200c10a050302da0903002881d14201c1501000001144 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 986728147 1250 986726897 986726921
    0x90906070f0f050c0d110f01060b0d09051510091413140a06050a0506011b0f031d060c0304090e0a03021c0509040504051b03010b0f0603060406030b090105010801060611030d 76
    0x1c1040600202c1c042404481c250041c075a80c1c1d102c0707036a011b0809915204407602d4010503a403401ea020800085103400302e4219859600e00402c0060240c14954140408100b074121420591003c0280c40b814820002c2c0664054210400c040365070744015802390380044031140c8202e2850008480400c0b20168020000f00c4030000302c8000c1001603603000240c03501596600c5c900340d211401d000e40d56800042a0080340c0503210300c000b406002c2c1d242c50009503c03d0394080c3c284540c124114404070b0310140d44100007100075198a50700c4104040d15039490740503125130040b02d46408030600818202060a561141d0554001d14801e0b4485510342d03c49084803d48106100c0304000f640411388560140354441c0340118090000340b001480d103000c00074000780003184a0b0340340078042019680c0350504640380d04c4095910030380f260764074000b04005090350742000d41041c00b6007040180c3c2a0054000e03505940f04100203125582d541c200696001d6a02c0348032083e503030001d03c01c0740c084801c42d40c8407801806c8 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 986729397 1250 986728147 986728157
    0x5041a09060f040806011208091002071d010f12080d0b040b150a020705010302031e040206220807090218040207020315010f0e150303070b1503160302090906070f0f 72
    0x20301000058095480700c908541c1c902c501107420410f0010038401c007401840d217004801c490011596848107903100342e03030019104010b110940c1010900c01c00c021406031030a0700c9008810b14082e200d2010312b55007403060740201c51085601103038000c400c1c500084125030000005091120540403100680071080c0240d40080d590449840d0940d120440d00c0d0120000e0880c075580c964080c54001d05151301078001906250040082c4819040222202c9040400c0044511019112440001c01e180700343d90000d07418100410940b6690031b800c2d09940c3c2100c40c400d00b110a002d5407000354401343d0040a01d02c1082032250032004203035090980050050a200a0030b84488220307041e8030391030356402038001d80c01d04003000c5428401c45002c103501c2c5810803803404250074056131031400643d9034071405c0c0c0014006846900458407520340151061170144008040d038032500844c4402100c0b0344078034801a0710801d1850045068807401050b4903004410582d6000d0a1302c2d0301000a803003810401c0d00c0601080 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 986730647 1250 986729397 986729407
    0xe0c0d0902090a0501150311090105091903120f020a0b040f02030a0203012a090e0a09020109080106240f092d0b09030f031c090809060313030906020a0305041a 70
    0x2c2e5034140164428140e1500000c0c903541403045115860071441a98028185040c0418503c00010000e68071424803d10300950f031385a550000c1031094170004c81c000c60207210203201104001c0035060047c0c0c0303064280d40d014841d601c4d0640803a82c0d0a68868041c021031015400314020494081145104134005011a1001c094a0f40070a0031108154040c6086c40c08807920029010041120702c40e40500b1450301c0d00845003080300c0c84591510103008100b6a50b40d92031a0411a409081c0240c002c01400000b009219034801c1241c10400c0f00e54128440c0c2c160101100000c07902520390a11841103e03a241e514290816544041209400300c11150741a003021b80313006040342d0407960501030001c1c1c418030380e100c4101d0700c181481e090a000000300c050700f040c000c620442c0b03044a88048044140900444c003000541803100741c0384101e03054560880030010030008203960450050900701d11039a2100a215902c85049031660b00c030260050008508000402c584c4801c820301e281605900d4550a01d09 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 986731897 1250 986730647 986730649
    0x11010e1008060f1005250f14010b040203090c090a02131d0f040312051506040801090b062b081306020a0c0803130519031203020903160e0c0d0902 64
    0x403900da40c188a000880910400640d03081150350344031494025900011480410300000d03005001c0c060b16801490500c0034124260b142c0c25146103000c40d0480c0c44a015503084c2c0c145860402544980e076260703503080c012102403a080ca48222481280c3e00e001904001403100304001c1210b0004e000d103088242c090201d403580c0f5504005140062a41060346062841c0c0c590307280700522030007003801c0d00c0c0c460300c00d042002280d00540740030000c61604800040320795544805203400c40301d60404640042c0c01140c0411030f40e1055200d203540f2030060540b02156900d8070708221141c2c0b0702500c074040c8050380b241c024064800e84450019250711450441d4180b0305500020111280c82ea80910f00603888184d00c003080c080f110055002520191000d517180a8100c9594000c4028034800d05000716101001c1c1303040b24140116010144d644542480344e080b556140041c0a50088480c092083c040c204e9895001c498280a0000301c4815800d4481c1913502d54502c010756030855001858640e8031070300d0103401 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 986733147 1250 986731897 986731909
    0xd02090613110a09090b0a1e0806071205062d01140c06010e070c02030c21060109060602010e0f0a0605190507050703030509160905090c0a081c02160311010e 69
    0x38500c0c5110585855030b558990091010180d54005c2280c1454076402c03100d262a00c0d0f00080a9a20040682ea0210f0025004910310752842d40718030705c2e80c01a0700901021a50040b02205201e01450741440b0070b4565400704000105505460030401c624001c201d4442410428014054a07050400030311494801300181129800b0044060140d00040c00500403002c0785421240c121599140400c410300c4664041f030365445000c040c09105418400311032810040d403100b01440e0744440400d981841d6900d541001c0602624010513015509010b1a81c900303c000080c00346c100005d01c40101a008010303201c6000400c8082c1007900f200e960284c145125000d58003071240034298075035942d9900c020b1420010100c550141a880523070b00030b04a03000d060601e00c100034090b07e8a03403400007010385600315075510386000c03902541c0c0c20082c0e542c0002040c0501195990700e0f13a582c10a45102403200880c1243c03690f006240c5400c4252012000388081009410f4504083c034040c10200c030844060b07000580 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 986734397 1250 986733147 986733161
    0x140c120409150e040602030c190807091509150309080703090302010909090f110604090e0f1506030601120204140a020d0f0b1804020a1715150d02090613 67
    0x812000050401c00c04105200da9041010b03802c0049036040d0800c568860515000b13040507042580200104840c0e854450842d110000000d912907420803007621b000d00581d504a5851000c943d12440003c0d40c42c01e40124202001401c0c1e030340403a09400c00103606070009001d03401d041010350701d5040800050050380109141406901c030488141d2071840010600c5101e90887c0c812075081105020010f580303110002000c0364000c0c03038129000b6104d030202e031040c021584202003041c2080d498055443c004500044035104400a40703104010004080602e80001c0d584140c241c2d01003001001405904050340f05020310003800418540b0f84030240404c1000c00340c401d00c3c0441e90000e42c01000b400684903107604070900c140c0500114405d02d000413841c0307404078000700941080c407000030119543c448a850150003500e40c075507000840302c3c2c942c1d556a005160a2618208001d001c203502c82d910740001e040a0070020324005403010240c0c01c1c8054448041d01a90300324100e00f4105840e16040c0c01400c0c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 986735647 1250 986734397 986734423
    0x3110d020406021c02030a0c0b130b0106030b0f03030310061422290f0f09060403060c02160e04020607030e120309190e0c1612030603020a0e070c03140c 67
    0x140303061480030300320040701010704c00c02c00350750003001418245600088501e0031141c01c8207034401103a403048506c1c008074001d000024030300400640049800741d0154085d0900001c1035503904101080c0e0310500d0b5070703844252400b20402d0307030b609410000300784a02c2031842d0b001e103112401410034061020b001940c2c2c040d10403080482c0240402440301380050094440c1c2d0101241e0b012981079100e01160a1501c50000070100602000440a010761441002c990b4a1180a0061039581d07640f424404001c0911440342030050042d403074a49240c00c0e544160405994404a0121581e02c640c0e0070404254000c800403001e00400d1803036042c40e40d5940b084280c5122014001e150755440d04020481c550b007501c045543d400b11050418400010482d400907800541285850381d18003032800b07085c40d0900c003500000e0214084c05414840700d9032640290044a100381c43d079519440c1c40340c241801c4e01e0421210039001516050041000c42d1140c1c2c81e8484840f41903a41c5885c02d82d6480d0b455003040404c5080c0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 986736897 1250 986735647 986735653
    0x14060a05061008040c14010306030b01080304260706210e0c12011419091e06051005030d0c0311030d020c0601050a180b1305091f0b030d03110d02040602 67
    0x116060030b0500d625040c40340d1526001e14a020303a10301c04022801e002e0b00b09110b405801003045039010740e02800281da0000c1c51a0100d42c0d54003509582c0394440c0c0282c00284003900302c1c40e4048803121502580c0d03c1003d50250440b0b1781041c4007294a050f0b1040c0f040702c1c80b5240c04071000c8101180c0300d541d4410781500054200310f40c49105021810780c02c820407910071707032406074251070343c1a4604035030341c2094450040130354008184240d08040c0403031541c041c01940128246090041d82014055049032044900340020b640c3c8200800200d101442000d406801080c0c0c6954607501c1003c5413180c0324881e06012034481a50320b2642c8c9107400c402d241e0130303140380e0008018410700c1e81000351500502c0110313292000301d030170150400001d003140e01c00084480d890312001169955600d102c0c1c514202945800c11007071030320000540d901c03000e1582020050031560018011025a0702510b60a020060020407030107406171011401480d01c6062071600c00c10500103500c1085043c0010030040501b6402 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 986738147 1250 986736897 986736901
    0x1020307020111030121082104050c0d150504020a18020d051609030210030204080303040602070b151e04090b0c0909100f1703071b0f0b070c0e0414060a05 68
    0x8041c2c21200d01c12000380e6016001d100401c04040c004031060300307102c240030091040d603005d450b0142d40750044400070064200c151071001d03909460140230b2403080740140201d40602d10208107026000c1a0031001800111a55504042040c0c803908101d0300148094020841d1710743d12203502803145074034214040d000c2e030000354454015030640611a0415071002c003c5451140360100688040a5448000e0048480319081415079009a041da0300030400102923940c0c91030036150680095001500440d0740310001d1001c00c2ca40201210b504036070100103440000039040b01001f500c4c010441c010626485600c0e8041080091381d1141003a000c1c0c1d540240450321012080100311059078002d0a0700c05200062004118050b5041104000c40d80f840d10000e0141c2000e07500070341036116000000c2c0c0924500380c40004048280c01d00001241c0300344188030101c40d107500d00d5070030380d10500001901c0b105d00d030102030000040c010110380d0454810311b000e154601c0f050340502d091181c01c84080f120705644000f = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 986739397 1250 986738147 986738161
    0x203030706051515040f0e070215071e020309010918110d1407170c03060f0607030c14071202360109050f090d11120408031b010c050319020403060c02010203 69
    0x4180042d02113100c10650405040810548880d00c507442041c000030250004201c0d0b03e8000c0c020554040008003d10800d0b180030711010300303000740c8031900300c100211424032548154400720542d9666a0140e4a40d20400d20700302094035020006150840c2d600c0d610300c00c1c2c0d001211088014070b1080f149140110b07040c40e80c6007040659100003010041400501c40c1c91000742840000360070380c00460040d6007a1652112000325401820005216030400303800114941491303002000707170440038410140d51098002c81c00b40503488518030b1056040780100e1501103401890002c0b0041145c0c040c0b1100115190491508002d410500f00280a03214000c9001440070403960b0145e2075100d000b8150007105070030300b4801d20703644503c0942c0c41c0003040700003081100890700501a491052000d102610746854030f64a400791030754416040750f500040b1a455460403000180500512640c40b42c03112803e50303461021801069501004079000c80d60708000110000740700b0302c40c000000b1700c9903000503100d2800e21 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 986740647 1250 986739397 986739409
    0x1815060a0b13060c1b030503190f12050c0c031303030915050906030a0e06070e0a050f060a05030702070906180b1509010311190825090e0402030307060515 68
    0x181100c11004000c1028160049215000d80200c6500389421941300344107040108803030340000760030802d041880d000041444030000103070151000e065504004120241000d450310040d80022030003144500107124030003882075001d10b5100c07503c04003843c82c00c0e400501d002d003035601200c0c04103021600d0203814410f01d40c0c810181c10107801c45c2d5960081c50245108041e20300d0152003e01d520480000000031a800c0442e0814400411400202c51090030149409001180181420347c01424507003000a4540390402802502c0c1402508452605070f0403101101d00d980000c2a0505512682030001030320000c0707100b820300620f100c80011080e00c0c140c3c00c3c0c0030150740c9220350a030301c68a0008281440002c02000300d8400301400d00740010003910900101c8003500841c03d00c0301c036030540c1241640c1300903001480d0700d110740c1c24000c0803032a40c408460802084400381d00d0302c10010320100c00521150300a2100340380c000d80002e0440c0d0411810703541e04402d0711001c42c0c00044c0c0907070300d002a0103641000 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 986741897 1250 986740647 986740649
    0xe0427080717040b030a0207030e04060303051c27051603030c1103010b0112150e0a0207020a080a03020c0120011b08070c0b06040203070306080d0e030c090106171815060a 75
    0x82c5030410314140ca8228000313400c0c00040c0003403000380c1d4001005010075000d41c0220164103c003610078800240c0d80c1c28081c08507000f404840703011882c541514103001900d440340710700610500303000c00da00c1340581b007000b280d10120080880f1a0300c10440b09442d8480c5401a1a000714441d42e1072030a400f00300c0c904079030841c90543c0218020703818843e00341c1c0319a810402c0d05600b010031042c0003e5030440b800c00900d1115065200400d400488401e101540341c003034005040841c0255800a1031a944401044e510030240a0280060300564008102580308503070391503110111000b5a03201c44c50b07254550b07085074003541554504050400400350415046803100c0d074411020b003421504480369450b4900100c5005080902c1260f0020014400c0c1e0700a0340030401600c11107044407001c000f6108058080030701344460034402d10a0510b6140149403000c0310328180c802d02c1d07544107541680b6003100b01240d2000303091041d40f01903400360f601c00c080e410401400c40c00e080c07860204050070f00d007091001040035 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 986743147 1250 986741897 986741933
    0x1b07080615120d210906093f03090605090f0c0909070314120c06090709151202010c0602032409040c1701020408011e0b09070e04270807 60
    0x30b0300c540075002000c04501d18144000303030309240309403401d01078034221a4000c08580c50720303152820b0782541c140300f0f1a40c401c0c0e40305846820b8241180189085c0000a402c4050031514000b4088003141901c0f00d0b040340c02c4111000340d090129400d4440d58030030090340d800f2903940302190301585031440d5500c01041804002c02e4241c48a80442c20f01c1c8030b4960325080b0b240800750401e12003512200080d0402c020a00039413200e10113958071303800411003054460300295501c84480c0718540002c20442d0b02881801a0b90504140c2400c0e803e00d000a03d2100400d0068181e0500014101c48030102c2d02600095100700e4800e00c6510100703a8803940144407007034004440c0d019440700b40400c400102060004401d4402d00c440d0801f240c00f00c04a80e0b4064031030b5030440761a95080200c011625210401c0501c080184220180409003895040c0100c0080895030000043d0480c80750b2100350409502000040642c00c4122108400b0b460030181a00113400c0200c0d0301c2d200c000340e030340288207544111400c0400 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 986744397 1250 986743147 986743159
    0x5190f060b0306040b12030406090f080708070509071701090b01030c050c030301140d0812010f141302030a2a02010b120d080703060e0a1a0f0607081b07080615 70
    0x2041c410260080c0c00000c1c42e07240140da079400b003c8030b076a0319501c1d6001d12075148421607a50725216140100390a0b082d10594800c01c407804008a43c45001141200c01c0c1e450410051854903d00f00400090000280615050160340548420145d00e1009802c3c003800c40d1500c045460701c132081c00181203d07410024202000418452050100004400c03241102c14507034450200440b080e00050032043c0160f40141041c0300041e414010b000036114450407a4040d9005081c1c007603458400d40c915403c03019800340d0007440c0201404a040080e800b039030700074210f1200080c0700c0c0c0c89500340c101c580c40c240503181116002d40343e203115010b030309000c1c0d540c00e00000c1d0f5142d1880d41544903220356a100c4901d1032400c4c00b42100002d0300081c400e610040041403a40d80d25056810310390180001010203899942c91500700401c01506802c0030540d180c01100090542450002c19131500c042c3c82d00f24003411843c44034810b0042c124042e003080090301410301035000d00040c0c28423102700c076031140b0f0b0040114001c03e = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 986745647 1250 986744397 986744399
    0x1e031812070b0c2104030305101d040b0a020c1005061c080f0307020a02090a0506010e0a1a07050c120d03180c0b0a23040503060109050603070302010c0c050405190f06 73
    0x180d00042903d410545210000c0c0d22407203005600d00100c019413032140358914019007040180359054025a00805808010f40440e07a128507190903000106a10100200c000c0008100080d100d20380d000d502010802c4010308040d030007110039040044901d01c103040c1580b201f0a210081c500001420208503549070340030021907240c0c0c2c8010180c09181c1c11070008410110024140500a2140b0000c05500801041c0d81d0314001441e036004000c20781d907a41c0040c01e940d5011056090010b846011f6449400c588001e02485001c0c802e0907600005046846001d500d00003a401c2d00c03041010b001080100e80034140c2d04c131aa1000500700c0705801c480211040141c01c819000c80c58892200041d20b6100d450242d03180c46000c41aa0004d00c5050040d00880d09904503514502583c800307001035034811815502640d0b610103c0400750745054941301d0789074218141c108010f600824070280bd0502c5200140c7e5007030703a0b9030005812600c0481e00d19006950341200d4600b4075800340b04001c0e01c03028841c0b04001e01c07 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 986746897 1250 986745647 986745653
    0x1103030306010c02061303021504080c030c060316090306050408030f1f03030e180903040503010c08010807141914040c26090705040504061506020708030703051e03181207 75
    0x2000e083d860203805500002072410f614869481a0009560007070005a40250f4511501285034800d208183c854010041c40004d1341c500421200340a81f40103090a0554941d120f11121603440b902c03c01c4140503008000000050f114080e2510030790048203074179124030f041c91340b400b070010380103000100d44991440c80060b071001000c234460959404d46800109030078031801042d640c06400d0110864045a0020403816034800001041070b60410341c000d0001e01c0340042c1c10745e5001c03800e014602c80d81c2c0281609010004500c00d048001c904000c001d00d80f40d40c6c403000c00300c18010494000310040c440c030010344026810075020b54009405c42c1e00d8402501d808100c3d10040b151130055040b6641c0400c10301092009d04100807620180c01c000b4020061410302e80f81c034000801d07a030b4081c3d070b0351003002d503c00154071400829034070200c0380200040c0d4504241a80d049a0680c05200012103980d0340e141d411500594890180d4070500c016031714508020f20340521240341c0b00c07a00c403201030a018100018000 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 986748147 1250 986746897 986746907
    0x3220506011a2101030210230c0c130b010818030315041b0c0209100617040606091823030901030e010f0c09090f0b1c050708070f03110303030601 64
    0x1110185014420306010381c4002c0400b510030302c5043c000000a08068241c0c07001e440920504aa108035400007030303c4c2c1541c0b0141e5095640b046982100c2c0d00440c00c1c07a41e120080401090f50300e011000343c0e104a110314000404016003907540500d20703a9106004096541c00c0b0b100180c00400e4a12114010348a690b4165a40e110003004141302c18100d070b8005000f5115900080c60101014143e040a2003490500800414811000340e100b015800c001c40e134402e8900407a0320540e00142c0d1001d2540740100301c480d4a50801600c1128095a10080091520400d200703010081840a80071440d24000e07081c800070100d82c030f042c0d40170b050000000d550f03090340c2c0020031038121417002e080110b00048501310b4a4010f01e42a03e07584022820500f0701c0740b0007540021146d0640d03031101c00070488001c600b0f00d00012608408001c0f900801d66140114007070401c82218400e0034840e100b04c07600103032036000b12400c0003803a921109210000410038000c0044404031409020703c00d4005500f14a855000202 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 986749397 1250 986748147 986748149
    0xb13060e060a0e120f01151d010e0c0f0318010b030129060c0d03020c0d0212070311030c011d0c01020f1207150606050901080a0212010e070c060905030322050601 71
    0x2081c0b052200d00c0fa4a941c5a44000f050354050060544d00005070940f103407030280503110201c0480e0300481902041030901d202c45046c0c0b40c1c1c42e86406840e41ea0824003c0d14203400080c01031089030300c084c86060514101c100003507100d02d51864801041c00290a400c900b0350b80c01c5454503200c0e07410f01c001c40211248100f09840410280101001c42c45983d0740411f25a21900403103c00b01d0140c2e01400e007026030141c006101035411003040300c0085d060104202d8580c030100f041e001080710b041005502092050800051602031070b01078904d42003d00f2400c608440f10501110210300601801029aa01c24012001d80031030a00280111607050310340551210081000f038091043c0115501d402d10101442c090055190354204020480d159100a00150030000445000030380d6480003c00d000e84900030781d000480030344807490240c0d081940c0e041c81103c00800f04810483c2244890001c5001d40c040c0c242503d005101842c2d40b4204000350f0006410800410a00c0d00002206a000100000b411038 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 986750647 1250 986749397 986749417
    0xe1c02040b0f18040c0518010b070206040905130b090a03410c070603061424040902120603060f040609050703151d010507050a11160b13060e06 63
    0x141500d0400014005041c2d464a07140c000c0104410700340c94100c0e0512803030250b40221102a48035940d0010049485d00c00c159224101030f90000401c4443c11520282ca51a88005d20503030401c0c2e141d003809070031118100e61001903400694080070900c4409550a0b030400b8244001e4000500213450107007005034a00c6402d10040b43c01c6810310000084043c5040201c851310320441c14400c0349580314295500800c1c0940200d02525100203001d074001d1054900301c4450301c802005450100c41041040d00c3ca001c0807c1c601d040001d01100c00c1011500140090072011500584450621801d11700b02c201c000c0c01c460090340480c05104000340820718466015500040128542c0b04603d005820240d055100925147d000c041540480b0226088200403104914024011800c03005086007600d0741510401c0229200b08204001e95204000c1c641a540600b002c0b204a1b10041030b800740e81c101c181d889428944004030700d949110008840e0130008183d02c1c544890360b02c286030000360382881922000 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 986751897 1250 986750647 986750651
    0x11030702130f0527010605011407061d10060b07050c0904060f14090114010f060f17010303020f160608061c020d050d020106050a080303010e0c0c0a050a030e1c0204 72
    0x1088891009030040080b44030a1003060050381845060300885030300456001070740c0c0034031520940b03241005100700c0d402c842050f524401c0b840c51005059005038041034080d5009a00e401c068108000d91040504003e1220401030100c00400e9a00c001181e96a42003480e48042c10860780001c980e000a8242c1908821503900600c1d450b0303480c00c40014291a1961071003141040141c0c00040001c000480c401c6400380d00910022040701e005002501c801d00582c144848120390500145129040440a201a909100d00c04010031241d449016000b41c0c81100160f12001404200e0881441001c103d507040542020172181031a20250440d180240564000c25944c4040030750754400c440d800040580140030f00e202d01d486400d080781c90304000f410705405503081242c00261811700070964011194a00301860640e42084145c1080f1a0060b141c03004d04202444030f0202c038042403084200c080d201d5001040c0d80b14140c038010349400b46100041e4031601034803251a01441210502101240c0c0c11580 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 986753147 1250 986751897 986751919
    0xc0405040b011b0b061302070309140a090e03030627160c08160507080706082419060f05070302152e14060304020d03110724080711030702 61
    0x1220010100d00b25071000712814141c5000344000c4c401001d000d04801c2e6204000e000e0030b41c1c020400d0b4410680c0040c001410b44c0c0041084480d0b80340c5140d14000007e00341e404056480301c1400555010300082aa550000001e100b11480d203c1054025a500c400c0b901e600404003107081c2d5203c000040c1603040380303000c099041c29414843c1106c0b01721281c0c0518034644841040000b412002c4000200301c8041c0300d82d5401261760b981c0024241d040710641d070740c0c0e000180d0310145d40302d240c000b404440030607c90f90b80c5804407a6a542801921050403080d80c4070076000d1401e04024814043c04080c1010f0203810490075002c60360108403060b00400740f0714012155100c0ca16244d103921649841aa2202950052505100c00c0318002d8001c6500300b02c006014000003004004081c4401d4034001d5202007505004400207015003402054084043c0c103580c1403950301c0070341e07243e41306040c0c1800c4200c40d0411000c1007482e402c407010607080f40007850320384450f40081e81601d54920410401070b2084d50f030074078 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 986754397 1250 986753147 986753149
    0x5090c0706060b0c16080705030307080c010605030f060a0b09070c12020c040c1709122205060f2d0318030d091406150a15030b0a030c0510020102030c0405040b 70
    0x1071001410381c0f42040b036803080c04400381e540b900e0f140c1c0102c400c40514800d0004800000240107400c0e990018051031404080c0d0b42d5604040c0c0c4110302c182440d5489220002d82994107118000d8003400920143c103051502c0c0c95004112041034902921441ca44011b100e65994440030036603003168800200540c1e459906016440d0203c00b0781180e038850f0038a00150080c17503122840c4c581d900501d480e50300890301c60b0003580d900c1d14044004075502130400e11113041029000c900d052041030054a103910351340d4a800204125500401d40c5558188000401c0c0440d0400703142603a810b5910164001c0503000c1c803101525103480060100081c503207070003c0c10302d45030b03205100715a400d10030342e0402c2042c1e400b645000003440c0c0d0501000c1c9110300030b681c0082c0c00120041c0d03003203084a6006200508a500b080002d0400603441a9000b04041ea14070704030003d40c6488080c5c02c06540204003402000d45041d0401501c140d00342e00030710031a4010700502141001e04402e840599501705c80c007040d01c0348200 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 986755647 1250 986754397 986754401
    0xd05060f090103080a02010f181205040e040c05090f04231203010906140d03140717030405070e01060e0306060f011b08031021150b0d0308060f040605090c0706 70
    0x124941d408000c1000020401034203900a0081c4982500280b0030481c565400d48100c03440d0848071240301903014403800002d142c0c150021030701202410228107043c1c07258500c000504003150100c1c1d04001c61602408246404006558801c0030300002102518003a5148442c0c6150140c54203170f1007500c4c10410314030600038400b80300c0c407040025019490390703036a40c02c49001d03100c5440303440c5c07942450624000590904032a940000398250301c070f2015900e44021420a030368401c00c03080c1c1d134262442004400d4000c0000045004e10300800052403a1401c1540c100c0006006906c50350601803c07034000307000c03904d012980c59444041100d0500c1500c00510050720b0b03803044041450203054402d4800010400d0140156000d00c8984003200890754036190350040d20031a00030201034440101c140c170000180540d0300c07208041040840480d00703940440c04580005100c0340d0031808075140b001080018140108108240c1104550600c9003524040c0130072120341000d0841c4240c0400002c1013818482c0a0b = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 986756897 1250 986755647 986755669
    0xf051018050d0302010b041406060a0804050127050f0721110303070804630225020d02060706020f1b060f0f1f0306050a052a0d0506 58
    0x5007a4020400c02d42c40c00a00802460844600c1603141824000d0848200103201d0710846000c0d1102e13203814000c450070f54045800070821120b543d01ca1048007565400003d031b69108800406100c06101b0b1070303240c000d04010340100710101030760103181c0801040f01804220450300d59421840102500d05091004a28010071107a80d014480090850204545030303004004840d11228503050003001121414006034510300c0400360301e030009a880040040481450394410303020b035611109190a112261010190032000742c416540c003142880840d0003540803503c00c51800440b5504440e481c1c2c0c0040c08903610210040d000d128045030035030410000754110303505601c0d481e140c103480c0c07482c00140710b00c03006500500445070302804c800308000d21801d40d4254000c540c004603140342660f0784000b52001c44610f01500c0141021030310000042002449807a000d0030030600c3c041170524156890078040ca010340d444000300721292040b042484e640c0702c00d444041d0ba2100380401c883d1610000280803001e4 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 986758147 1250 986756897 986756899
    0xd0207060903180f0303410a0e090103050d0305060112050108070f0503011407030c0504090212090106050d08030a090201110607030c02120c071424040501090f05101805 74
    0x5450110301c00d15401c1004002044030140c150449180c0759451300c103084101e07200040204013100c4201d011141301c046100c54400000d80350714034030380c0260b107814404081c1c084071a80001b00040c000181a80c030010000958205a90640c401e500d9595050fa0310503403000014101503981000c6000b0340e218115042034490445c0080c407403542c40700c03035081c3c890946102d04000c0d160b200100150904041c029820a11040003003007080340d03246141035002c4e19011501c0c10800c80c0030000403d10714402d10107842c114030948680034251903d03421607421214581c212510503943e100082e0002901d0302d0480c1d500c2045600c003c00c08034018030060b9009a15019400850301807003081007043d644c564400d42c030600142c0c0c21a000d4840e401c40d032101c5031140c00c140800c180c0000710240b000500c2048900324515007c1e100609042c1100e507191080c061801582140c4400040c00b002650791002e1807001400b150740c0b040150034517102c00210344c1e0f0315001500d828130000c101c62403072406a441c0c1346002444 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 986759397 1250 986758147 986758151
    0x405090c04170c1305011220120a1b05090103030318140604050615030307030302031b031f090212010e07120f020a03050c090f0d051603030c0312051b0d020706 70
    0x80e031400b246880700007000c2d0581c060b940000701c1c3c0002255a0107114103c500c10102c3d6405072100e921002041c00c034075003490018003254181140c0c01c0d1516500d01d4003901011f40900440c80d1035150800e4510b00700740ba00c009102040c2406d12996a03030261071411242d141c01c002501084c41441d00b03400600c801005040060686102c00e00800003080385880750344200c0c1a14041e030344904a01003620920b404043d0164000c3c4421000203000f036000b1038102000407008180c094024409407840c4d4401c88850302039401404c00313009141022208100034061074201507017401c0c1010b951807a40c4c4014401c1e1510300406002240010740100c8607000741c600141d000f44140d80c126000721001e0760061020100180ca00000541d00c0c0080d0801d8508662004042c40b00601c204020444084148482a503050107008504207800030402e00030001903210380c0301c41c0c01c4903800d07050203040d174401c80142d440c049040000b00f00304203a031803582d44041d0902240d0a43c94030b19414000009008036800142464 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 986760647 1250 986759397 986759429
    0xc0604030b13210c03020d03060f09110405060417060c030c03073c09050a05060703050a1701230616150f02180a120b07051c09060b0108070309080405090c04 69
    0x50384842c040d4a113078020340881c0c2c9100c03005902142200c40500c1429246254104140249140b540064480080d9060a0360520303440381d0001d0003540c056480191040c485c141120039142c000d100c41940305079900c03026805d51900c1c400090700341c4401030184c4100080700c0c50300d0081070159980c1c030204010074107509450b19010b40882c4420351070300181a020800241c00065a4501107410506807600601170f14104421030741d054545d600041c00c10018000d07039800c00c3c401c109059256038000c01e07460b1440150011030710108000e00003000c0189004107001c004c440600480000d140c1e0600c1d502ca8280b84400542a100c00300501c5082c000700003150000855461035107c1101108519004a406880490755001c410409079064000101420403900014106500420103000c440c0511901208400c0105411504417458400c08491031580e0b0644000b4550303200304a030b03a1260050030704000f082c038035441d060f07024001c51182e503100d0000c2d10700050300ca01c000000d8500510b040c80240c51aa = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 986761897 1250 986760647 986760713
    0x5060306150304110405180a23030705010b010e0a080d27080705130519020304061503050d03053727120201020906030112050a05060c09030c0604030b13 67
    0x2620320421400e120310b052031b02088003101d41c0c0e0807480c005050180102030180c0720f9618180f030030550b40c9629003c1045101c89400c41d000500003880118440d030000201c1020040c00940072a00710044075024030305000080c80251400105110700307901504003200c6c00c95801c980c0304184482d80c0f5160210f40c141890000340c0240005011003660000c482c1050441c0c07102600c2d00c11210101c4401e00406e406282e8070344034180541c011030708180254008038001c045c0c1d074012075514240c0d900850700c80c3d011420f0100b2044c2e040c411f0541005c108420b00042042d105800c88408400350000d804070b13148400d2091b14100207603c0b00c0da04401c0c8018401e10300d600f2040500389644030003415200e540c0e01c5036020081c85d206200722014054001e004a05690804070b00d8038141501c0d200440e000e00c02d60100701c0100340308111052142c040c00401c2955001d8030400c0c9402c1401046039140100c6082c00107200003030800101039408140e40e40c691000104a0401040f4000f040d00c288499a851031a00101c0e = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 986763147 1250 986761897 986761913
    0x90705120a0311060c070215071703070206090c060d240b0702030d02150408030603011e020a090501030605090406091b060503060906011115090f01110405010908060f0105060306150304 81
    0x1c1c09000b51540005400030105080d1151403ca4002c01d4960081001c003005203410400013044203ca0580c4609140556490018a4003244d24071000030b07902004101000d541000400ea000010001810009540401052850103861100c48185403076a000d90301000c1c08815240d2a40d4407611090492556003411500c00c2d800280180c3c0280142600e01c980c0600008400c00c24442c90790401d2000c2c1d480751102d00403500041c07c03e03a4035540f00c81503c44c00740a4002c0c501c03084a200c00006940360502503000d001079015a2000b41030500700542040b180d0380d021860369010f60001c0c0046641e20070707498200707200036503501210382c1024482000725046034458007a5108031001e903000019600c1d80d200543d0200810102d2004983c00355481d0124980349840481c0c001125004581c0d18400001540342940c3d01d501c0c0120503048086404c000e6980e102104800070007003840030303020034100b007039404a50031014011140600e0000010541540350040780410114844000d5900c9040500d04220 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 986764397 1250 986763147 986763163
    0x2041a03010c0504080c010e0d020d1101090503010c2102040503070801050f0a0207050613030203090a17070e190b13020d020304230a020f03010902120f010501080304030210050309070512 82
    0x40039600e040c40701d0203058024422502a9400d03600206828011030004480000307550b003400c0e82004075000840016150020780048091040b0b80868a5002c20000184440825804148240c0c1042c041c107800301d400c0100800408250700807042c19882070102c040c0640b089a10003900745c807030a20300107203286d411350105004002c0350960480c561500080502607009035000505550445400b14601c00c0e40c40064540c42e43c07190040c0c2e82400b160f00c00141d60a419036100c1040c841d440e0040795103044044c000003029100e908002d0580c0e00b02006440012540c3d01c101c08440755880c01d03064080d0b640e0a541c003801e9081d12000b0b40d03070f540e101071802000e9041920b0803034001c01401162520304d082d40505445280b403400041c01d20044035001c0013403401da20642c82e81c255503904031100c0076845850810072140e03680e9004105500080503842e0840380c1c142d0004500f50030502c000d10041c0d964216601448003946859a16500d409251328280402079001d140d10520703620303140301c0701c44001c60549 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 986765647 1250 986764397 986764399
    0x709061b0c0815093f0f0c0613111c050304060e010f02060601051c09020901080d020f070506160320011a0121150b2a1903030506040902041a 62
    0xf80c4a41c444502e410340d580041641c3d5500030744400e00216a442120710110005a1240004501c2480c8901c6400b0780e41e1040102000c8650006000c10100303070100300c0142c00143d01c0350512003190103a01d801d203440f0380c4140310314400c00b048000b045080b5a441001a10307150003500703596485a071503401625a03240403803903d000c20054803d040c8400e0012500501c16581a1902c45c0b4020321051458100d4620751000550140e82d07122120160300c4149041f4064425072006104e09102180c2c042c0c500300b40801a004582c0c03044405000c02c1d02c810301030300c020503100d07048240c0c8a6600d1805851800700c04225402c00344081c01a00c0e85413034150400da059000800d1901c0e840c00c0b41c0b400440741c80c10f10b80b15030441034100310b04803075003841d20390302012001c40c105005859564440c5402d00140c2d10101d040704e2016898003071110300c1060301c03900890205882006041c40200300000c220750dc940e1480203424160b4032030015000f170b19907810620b102d80d0300500c1040a100943c0c4030b001406a50314601d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 986766897 1250 986765647 986765683
    0xf010509160509070801050105030c220306061505090904030e0904051005070f0e060c1218040506010512040221070b19020106180506060409020403061b0302030709061b0c08 76
    0x1074074140f0301000390081c5642d5442c034030360307078200070064801c2e50000d89030302a0290708000c0e0010b0340301d041200c40080345005500d8074046245090075016240700da00089200f843c903951140c14640c018044641c91001500c002e40e440c0d0351410141c0b1600c81c00f10070a41c00258040c00c21040181c0030904200340c01d2401ca081285482d1040f0031110705203980f201c03201085039907550a5862a048002c1c1581c400440c00301e80408030001c0c54502d20b908050f8041555110403030300b003c03d46c80c0900030154002000e03e4081e00389001e10036005101000580040d011303402c82400108102c0030640c001003c0210300086a075425a100c3c406a85503100005004004226801c00041c0c01e2040c06440115603101c0111030014a040c4c10303240041c007000c0c10566000301c04101c00100c1c1c0640b030010380015401008001001c20380c1c80186454002040110710800d4070400030800001c3d000441c02c0c064601e00e1419040e15800ea0034130310500800c42d0305c0a00f401c4456100091400b600050b03001c8480c42880740 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 986768147 1250 986766897 986766899
    0x290409092315040503190c0512090d060e070b0c0d12060501050703050c0304051903030e0d03090b0c011413200a06030c030f0f0c2a02060c0f01050916 66
    0xd0101d51045144803100280c02505207000714001d000603140d00640644103a13440d211400c1b40e0f201c60000440c03201c00c00708055030907240a001c03040c469050703801402584203240c110407100040c1d04a9a084005051300c0c1e4500c150b1103400b004110741805403500c2e100040da1005202c452a0741c84600c49204400140326103031510b40c441c0e46002d05c804558042e1035181c20300300c0da540c1c20f0700d40350403611070010148006d000004a581d2501c0c030841300e0700c840310314860700325045083c0103049100e0030484034011064080d15200096020000c9400c4400c030818440c3c079000e5521100c0d01524101c0000b0781850300e450184520f0b980420640e14240c0d2082c42540c0803440104030541c1840055000c9ca58007a0a00c2d0040203002c1c001d410124504c4c25524000034484080c40400302125030200030859501c2e030f5003401074421038004408084110705070008070b00402248a56894a0000702c40c0240602c2c008610400841d030200b107100c000f040a000240802d09d1310350f00c0260f5070383c2d20030780442c070358005540 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 986769397 1250 986768147 986768183
    0x20102090414150d020306010302090402060d05010e0612010e0606010f1202030103081b0708191110020f070609050a0909050304120f03021005271011040e0901060b0429040909 77
    0x300030101c1c4c560140142450ba0300e16000c02100b040000c01c1aa0083c02c100140d41d24010144a000e010b880d809002170054106501030180300c3c0041c0d803100c0403aa140c055110030400000505d282d01050034039000d010616031005c200c0d8888805841e207038405d80048004001c1060501c041d168450711400e8038071a07035403040c0010782c3d03130281d500caa084560041c111201c0403169034030b80462128003a13101d611400c03403200041228140c441151740c005070420195000f0416007441a240108110300d4a0b4110301d0810740012107100302407103140d08172540c4860100401000b8000d80b03000301302e41d0292121750980d070704107920207038001c140031030040c0900f507400e80d5110a10b108241c02442e80b842024000c01c9400703441090601e40210507803161040e0005504924614082d1030209007103805400d4446240260183c050000604600c030aa4113260341441450748580071395040313416411510a000c4403070020404151412180c5e0f00905030001400320789207184e40c1103840e100340701e004517403287e0070813070 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 986770647 1250 986769397 986769409
    0x30f0a050d0c08070c0f060b060304060b01080604050c042d0b130f030f060b130f0606261909080a030605031e1b1f0305010f0e0906070c0302010209041415 68
    0x907403104c0460403031480103000c1001c242c03101c080c40d881050005010164000002c1d01500b040750120707605074841d00000e03181d5910200c1c030760b00904155414030050506180040c168003c034000c1c9240000d0b212000015903a207000c000180c3c10750269407440e150f84585180740e00c6d0b8081c0144840c010383c50f85000500444a00700502140e420401707070601c1e04000d9135101c01406001a01c541d1140b00040c2143d281c174a14414204060701501c2c0009005103811400fa0800300703400b100c007a030740021000c403510404408001d961b200b1490140d65009402003c1c000000301014440980b80360380101e8100782980d01030384a44143c81d021421103c4007a400e2441d589803491861003d1995041140481c40900e81c2020f4086219002424504424032001030924140ea240d482c00000a41f90343c0100702110501079144003421102c42849910305e004d210840c1c1d280400b800c210b007001803605006052500c04c0d4143c0321103800007441480f10310240703000c82e41086030903070b0070081c820440340c4440404e03d814 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 986771897 1250 986770647 986770651
    0x27050c01110303220312050c03090709092003070e07202410030609080405040b060c0721020904050706020606010e150a1107030606090c0827030f0a050d0c08 69
    0x5144c440c800c24421442c1c02c0c1c15484804001c40074400b9810310300a2403400750060610a081e40041c0c142c13249400c0c420a45440b06540c40610381514100703020700440c115680e0a8844846103d0030060341022101180c902406940310701c824040e04428807440c190302c42c410300103d0303546000099420716524010b540310b1826401c5050040d04801d06107264491002d015980900f005801c40d200d03d07901d807612403d85256a00032501d80800140c14020b0349804e101e035181c0500280c409a00b490101306940e0341d1041d0b1070060601c40d070840e01022502c03082088419155940c003820003101400c052130404c1e5600e9440c0100030150184100040c8a540f003011040010940100f811503000100e10701e14280703070712204100c010045107640303035510b4400402030200190b00ca10340c00200075143c6080d401c101c8003c0c00c0020300b040f51200a201b01140d2801d04000c01c007100a480740c40204400658510798030554034607143c49080480c001c1c07812908000a0910800b48490511404c0c0340f81750122480041 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 986773147 1250 986771897 986771911
    0x409090308072d05090402040305010605030601151209062d050705030717090a02270a0504020a091812111212070c0f3306060806010327050c01110303 66
    0xf01440c00154254420f0f00e040802c0c01400c120b89008840300c0810240d034440c2c1c0065038169110b000030041400c00300303c010f0042400032840d170641c0c06a441d0060000d00101f81c3c0085146d240e4a104081c0030340b45c2d03c203a00341c10002500d0743d005401500c0c41262400c0e0754000100440c030703101c001170016020b80e08803403103400180d40300c90043c01500c000d481c4401001c0c0900c0034a01c51003040c6030041c2c0798201c07003001090a5601c220044509043e814074440b100800403103016080c0024000103232a0280c02100b503401940010814008201d800c0d19803140c0d07410042c0400c4070260110410f0398220303070300703c1c00710303d01c40141c49043c08050405e902610504100d428015800e900088505128041c0c07402e05500c0381c4e0141d6a00d000036201e0030350412410140002a40c00d811040070084130720305038418002c4883d0401c0c40300c640fa00002408011000302801c0c10f02d500c50540b0350811200090442400d40d82499130386540071742d818415a544800340d04240443d04121220025030000020740780b00c0c0078 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 986774397 1250 986773147 986773187
    0x11031b0609041d060106021510051c0f021e13021903090f05120306040c020a2a08120306150c060403050904060b0a020c0406050103230c0c03040909030807 68
    0x2181e00030300000b441e02d02c00b0401600d503d0301c02614140410700c4414024001d40e8010303e002d504500e50160740300400b0f050b202d92209000c0c4100302d59142c4040c0d200c110b00e05450b1800c03d4200c0d500300003500d01c51040e0002e51101f0118405030b010302d4000800300103000140c4140c14090400300c3d8a50403445180a00c804445041c1e01386691a8480d80058050300d10511416003200a90768903a40341450090703031283c01803804002c00407071781460f2064110204051000b03004a022a440d84004004a6207100650341d0341c04481010000300849040300818a00c0200c51950b02c8180c803610751500300b684d901c0d1085080d40c1c20701d4208100a419a14003483d05405410741c0d80722036400761481e9020382a6150499140d9000040020449016168508281d0046d111190200c41040110351168001d1030505140031010b00420850141504607141d100600c0b252545420044e407119005420003c49035210015000c200b0000c1500944c0855200c0d071248000d40d03c41e9101554030100c3c0f000e113800059 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 986775647 1250 986774397 986774407
    0x60b030a0203131a0a150b0711012115091104090c0201090206070f0302100203100b0304080702030706270e040303020d06150c020a0e1302011d0d11031b06 68
    0xc0c040c0c0d40115000b0710002d1040c00d46a03069515486802840b040b000001c42c0000100402e210090090b403e405151403c4444103e0510200d90142d00405001070024004080d01d520540d001300c4595000d0f001002c018411150360703801045c050490001810f4540f40b002c0d800151510850007812102810f03074200e14107190070030450300010b250010341c00c400c40d03403620042400f58541100030040c2c7c40c0076003264150600d007810040d1a10f9032a42039030500074410801c101103180004840020340c3d041c000c0041e901e0321282444000d502500d04042d40c5406640f8002910a4202d0300c1c41491503020316419880040c41c90000489011500c03861a404031030000050022703209a00501c0d400e02e10520000e006034481540305288101c212400c4046042c0c0f00f10a419881c211541d00c0041c200d0384001c144503c0c05050441400d20b403600000e0510060100204039111200c14040d910200a04802e05000c014107001c4880e408040c005070082c042d00f07444841c2c480e038464200c01c150001402a40c40d00b = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 986776897 1250 986775647 986775661
    0x9021b0f120c031c1d0d1e02030f0a030608100207020105030703021605100b190f050d2301052d0103080f09090103110f010206010e1b040e1003060609060b03 69
    0x36030310840d5600c01074002040313100c20780c01c40d0184e52121240741083c001180400090382c09500e44202c100f074180c582c00340d59442c100a601418510074940c0321001c42c070903c43c410b0000d0f80746006401007001c0c0d052020070400d0409a150713111008803070642048403107458400d40188200c0c490840040e001035410400644441d02a0f00100400302c071968200070341e00019190a4205281100d800c8103003626201b0318185032508030581c40c9104225007041070608d10300644050100c0580c801c450003180c80752241818003604425451502205003090140c0024400d403c074000c040407550410000121052090144250b102c0400074010b1080c0306030459007981c80d8005160001c01c680c0c00303611410450010980c6803582c45c2e42c000d51003548007164110003d01040380d000040c2c0e511504550000004021101d4140f0000d03410400c485840c40100c0f44100803851325110320b400079102592900184861100d1140084040324000c00c001c2005c51386a65640c403c3d01d002d40718800c0c200f1003d0011a0f14 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 986778147 1250 986776897 986776933
    0x11030105130c032003100e0d1803021215010e010302090709150818030a0215090c090c0c280b0c0f091909060e090d050702010f050d060308030109021b0f 67
    0x10b1040c02c0480f8080040c60140006d01e8101c60301e00d50705440340c8a05911644944c200043c0d41c4114031820505205a1809090301c03901c40940b00c042e1083da0780440811422340c041c054035a5150104070441c4503503840e10b52200c210721007840202c0c069001c110025044038031924030001512218650700c00300c12603900341183c0c54000030f012500f8090945290035a607200800003080640304079006400e00344260500843d030700c0002080c40701a604040f26880189d03480c2074000350b114148031070340c580310086007008515003842c0d504200b40c60380c4032048071048222050f5000032114403a070802c0c4056615031420b10b0890103030000c0315030081800d10420b120b07031800760552603002d0815004100c5a0380d507034402c0020350314590302a0500d1803910b0b0600105140c14004000a007480341050382c6041450707400245200b12000b0f07200200100400c0a0702c00c0b180642010000b0754010004540303958440c10050005d6011a00b174010455618903aa0700c007400c04542d01c0c00101020000d015804100790400c12 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 986779397 1250 986778147 986778173
    0x90608041104020a09050405090109030f1404090f06050907020106140609030115060503010f1406121302031e0c0102060c19020f120901030b2e03090f11030105130c03 73
    0x60701224451400d6080d107852014203130640b41a520811002d1610090200b100d101600402c5143d040c42282000b01e0707005200c090b422215403400d02ca4044c05200d120046003d107411055051742002c800c0d40c62821650040320581c3c0d002c0720a210340d51500300f016405ca03185445011407512442c0301e060883c0c54500060800c0c050b0180c00800c9088404103402c0800700c59800c1500810000f0006104818500c1a190064130269000c1031000c0380520004403a4004d0042c0e25042d83c00010004075841d0240b41601ca213998080d08031554040c2400000508840d049010080d920030001c21401c50b41c4005100350150741510005440c01103012020107032007078280040c00552003018081082d4140c10410354030000800ba202e16110a9158001410f4502d504180d80c8500c2200000030503c1c0610203500c1c060400d003042c030400c01114071009070041d211192019003a10a00842c04061005000070744181c1d41c4120000c0040d9078074481c1c0301c0300e505c9122001828482210303800740006054800c4c408 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 986780647 1250 986779397 986779403
    0x140f01030206030915040b070206010b0408120d09060207033f111204050c040c08060f01180b0409060e010807030f140a0c0b070c0e0108250306090b180d09060804 71
    0x20340600003003c00d17800c0341d601c02c4d14203c481d85100c80401c184503070b041c400d49024080f00f40203a0702d402c0c5080411550780200f05001ca001902c0011083d00890441d40001c11142d88030360f00399141d40381400c1c0605404400f120b0a08075160480201580c001d40c0c0300501103100c1050704207160701d610f21502000402101e0964a044141044212940c040f841c80f0540b081c2e114078014030301a1030f201c05100c2921169034101041c070101009022196460144a800703000342840c4c003e020100400c4d03144103426143e401003050303403400100801c00c0c0d0000d410803405da603100040501503990701c20748903654940a00c8080c1a500100c5613510000b500c4000303a03000301c0100000c440e50100c0c0340e10381640c07120281d0301400400b0310002e0410200003009040b035006060900080039a5894104099151840712007021103144058103c03a101320840c500c45405140c200d1000c0100441c05c3c504905031190a5420300040c044010380900046070015481845000d9591400181c030714015056524881c0600b0071 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 986781897 1250 986780647 986780653
    0xa06120204050319060c0e0108280c0c11030c0d02060c160617090a020f04020d110406091701050402010e15160605070311040b04060e0a080106140103140f010302060309 74
    0x2030b180d034100200380b07102111141d0800c1314009482c3c110f040b1000310f401ea0b41403090392003080d00036a801c1382d0602d5200514640359450001d903001c10b02c0380319114940210809140030400d0080c65880b13021064000e00c1156044618000c0b00300f01b41d41c40e003500e901c0540c000a83d003860001403c0c542d015120402c040d0f000c03141c4102181c540092a07845030b40010307000445003042002e00c4500400b003550804064400352507c0c90a58020482c901c510015141c01103400040401055156038081c040f4030480c1815640c0355500d401004207410400d1103503030380e640c1038108200c0710150184289806103505171100c070b44d80002c0f0310500010200e44e9144e100f14650134030041c0b07100407042940140b82441200005207600d8845005030469501450580000780188010302510303141e0411a815600750381442244040e0600c009108105d20743c205c4c1a0b40e500b03002c40002c03845110100001a81002d8070180000b5030200684d07107000304100c982c07031003000d03a0000400140c28034400460300080302200b5 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 986783147 1250 986781897 986781899
    0x105060a120c1a0c0a030c230606060307090504060807081c08130303090501092f0d020d02040605030d030203040303140408070b0c16151d061f0906080c03011a0a06120204 75
    0xb60600b0644070207415000300307018001f02e200b0407003071443c13070680d06088505c035644480a010180c1c3d40c5680052140b40981c0d8004045508503002d2040e010003800028000d0100701c2d10b801038241ca850b09031140110780c1c40b0701c409507942c1d1032081165505159083c1d907000490340d00c1c4080c100c11583c1040013507050554504442001ca0301c28003400440c3c83c050940d840b03490585d0340180100c90307030030403040029886c41c407022144d0b503940c5814142050b40460346403442e02c40d5030000400030f240582c40150b00d03108500344045183d0701600910b22032402b9031820001c5001c0e4114203c0c0191048400a080e83d03c02c001180001d000c0b5084541c02040c00140b40341428440048920794441410040d5000340c04e2580001040105008185d800300c0315002c001a000b0b8080b03030340c41c2e8401001e03090311070b8103058100310003811104928400042c03039500d0061280c05e9507148001d4032400c1000c1c002d4025400c00f8859075005040380360183c500034000c2d003086e051078541101201c0421038032600d15906602004 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 986784397 1250 986783147 986783167
    0x30f060b0c0f0d360f14011206080c13021303050d080a0902010801030210110f0109140a0804180f02120603061b0d0e010204030602070809100c0f14010b0904050105060a120c1a 77
    0x18848050f00500c2e9502c0480c61240c00007410b81c802302c110030407015003403410902c9070003804641d0078030700c92040d1040c0c4c51004034910000c010307008500020b101b01c00340120010a100d0005412901c4050544602e1020b8139800802c0080e120302c124042d0215245000400050400740040010300d080c40c584181803d504a41480c02c1034002d5410f00901da44800345134003446124005820156508402000e62100300d40c0c850308540117a01c598410405000e4102c81400240d400c605402d1711000e80455503105100f028035603007071003074483c507000f4801c103400600032281450301650318240314001d0600380006c0317800040c0509107000b110f03012550240000030009a180c009480c4051081d42a547c5a010040c180300c004c8149059080402882c1e025050205082a40204101d40c01c107030000240c2198442d41409013403003400858005045a040109004042d0301560080d40203c0b1a0318015598212030743c1020302a00c0082e0100680c0c2d9020801c00f0415040a02d01c9503429880c039041c413902c60 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 986785647 1250 986784397 986784419
    0xb0708070204060b090111030909011401021501090609060501030b010206060f040b0306011502010c0504030309030f1a040b01080607262d0907090c0f030f060b0c0f0d36 74
    0x5401341c4908600490408415a0080c8001c128044104025400d014001d000103001078018441c0d0306400ea03000a201d803150344240408481e0a0b4004070154030395a4440d602c4008102c148180a0010701c0c001010540d5032183c001c0c2030110605034024402c91f04e4034030070094000003030035841c0d50050307072212040d0194405006c014003e0a0038040122000b5200b50080e00f03448141003544100a003c0009000003608058102c096076003001683c00302408070716081c14120060f400c40d031104402c46040004000030303542c0340c50503190070b0400e448041e21107000030790740000d880040032040e002640480355a8a507103a02d0b140c1c81000c0c0c14130b0160303100c0354001640500d81c10100c24110481c02a0400920150410004000780fa12840410503d2a400d000030a211680b00e44c0c0020192200d2002420f4a169003140c8081c10004507030315514080414816070b00c048030103a0b16040e000c0c1031920f80d04030b4081c4030b211a410000c0f8030481a2404100f1035419030591142c859070841e039521a01003622048a = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 986786897 1250 986785647 986785649
    0x301180605041101080c1608090d0f0c05060a091710050f010f0b0f0a050d0908040f0e0a180f050a05100606200709090303020903030307030c270b070807020406 70
    0xd010005203401d290a00302e0300b00c540611864103000c101c030180091488000c08442c0106400c41450030076a000340f410301c005e445000d5006900c0b8094120b0803080c403100044c1509a03030320a000341d410079039031031045c40014004c404c1c81d070010448120040081c2c0da00070b83e4900010b0341000c15240b82c200a80380c100c04491066420752003014001c0b005100c4a24030a6403c40030b40030710400c55007030501c80a5403a2a074891940c1e41d904100002c9013211048140c0d070040c5903e10350150303400d51035644420041600705814841c1c280034030581e03400308060003486c0c46000382c0c0d11503030b4002506605107071715081550456444105d4440c42800807042c08100c040c0001841d00f812100c1c08140d4524004c0c00400406510100d40b040c040c051010002d110000103e9408640510b00049186111760906400070b016029490b501030000000700f002ca06c0c1d02d580580c081c01002d860724003000d11030454189000388400100144100704840074072001c00c80c032000e4102148038010351881c140c40c590101c1c00781c5040d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 986788147 1250 986786897 986786903
    0x60e011104050a061403040f03020c10050a120510050420130611010b0f1c0605041a010819020105030406060312020c040f0b1509030111030106020f0d030204061d030118 74
    0x494244210f00d442030340f0200421a83c076040c0144400c0c11000d01413444007030401060301d00403e407880e04040c0284544001d03890001c01c4c80b0b884401000000e00294841c0c15000c000844000b000034591042e0b00c101406000303a4607200f00c0d07942c10301d030070300000344091b6184040003030448003282c49500c0038034004c1a13166840801d070860240341c4440030308034921072102072000342d0400013040785945a1080d07241c0c4d42d00e0100d0707800c00a201c10090088100d000c01001808803400c00042006128800056131600380800c030b0201d90ba07a03a214665034640c3c9a20b04100038004504510401541c4150302a680050280800080150f60b1b5912184c03a11004100d0f000942c1180b14004020320301071207052130351610040b0601900c10303141c0004100d0400f02181245109020a00003c0f80d1402d600031401e502400c00703402c0c1d81e56141c64010f07580d0b08400201c0c40e4240b20740850b8030121442402610304a89090322502c80b600104401c00703203d5001a40d41c0ca8141d0b6072180b030900c4550143c40350f4444540 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 986789397 1250 986788147 986788181
    0x50d0914030d0b010f05210402010905060a0507050d09080a031818050603060123011202120711070501031b0f02160b12060603070f12200c2b0309060e01 67
    0x2403c00050000329683c0302d114144035007403103520000c000e03100000715800b1041281c84410341d101c1c0300581ba0224a90011500034201046280b282c13900100103005035401801100c045810703500e030854003104140a140c3e1641c11404001c0d0000e0301a841415007040c0001070320030020b4545140c04030b5100301b0392444800503101d4081c012641400d10405014006506100c10a06480420038907800b49030402d0504008065503c0c2c00c000300e5070342c1a10301e0009803441200c164108184000c0c142c03810840fa4030201c2c0940800015158000d02c01c2d101151a040f4803d80203030000a1300340c17411802c084014007903006409030721031a0300740780f401140a400f16107034071511110f16450081015400400031400f070740d820001d00c011150005102d54500a65240c4a101e8090100c054030142481220201139003a80c0f45009043d065024068180d500035401111070100c0e19181200d0fa24a0518100107000c28040040c41c8051094006007420b6008800100b0803402448245003144e00c0c0e1109024448 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 986790647 1250 986789397 986789411
    0x2120703080a14011a090a170c130504030804020913170c10060f1e120c05041a152b050417030108070b07290421050d0914030d 56
    0x1c009407140070080401281d64034025814202224003034034400c000342015540100c0e01442035500c0030700745800b511808c0c40c3c0c42c0e030520f000c0c44125651703c41107003210301c540c40d5242c14040120b55072260354411901681c0e2038016071030320740078081d1031840070f070454480110b243c0030680400c1202c0d82ca000800080c1c1c040aa5a031641c0f15120f060070003080c010440d69061540130801c80c146442008140c0e65030080c11403c4440a428550800440d079202e1812108000c417117400344840303000e60f8012154255020f00034926011b1441c43d01c2016498403030343c09160303208072244069940d0058400b040b5001441460751050f0320000006501c000b04150483d510349042100b00010351040b440201c1c0143c0da4203055504052101761034540300c3c050400e049001080000034000c9218008400031030200c404549148280360103042040b0855090707034292242501c1c282c0758244110298070050107a620b05081182c100304040280c25818000d66203c03e4414051600007002c0c80280103824600d40002044 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 986791897 1250 986790647 986790661
    0x80705150a05100e1b071a0103020a09140a24030b010521121c06060309060b060a0f0302090a090533150c0a05070b0720060f0a0212070308 61
    0xd500020b10300c030841c4aa507107013000510310540741c00e6002034902a41d00b88008203030503080803030b0040f410003416000c2c07440c03203510b02c2d0110080c0c014103881c02034810740348054541c1440020764520410040008a490000510180c480d80c00380320402c120064540e05114030030000386107444182c000b900e6007600c020040240c2c0c43c0401c10141c410301d80c001c807000c81c1c1141502c0c0e2070300d0304000c030030014031072200040c0f00302c060085845540eaa609807070343c01c001301511610010020040c1400442d0020f160102c58002031a00b441904c000007001e03650f428440c2002d023021000f0b90070500c4d030190489280ea40220300d1034413501030310780b09404101103241c101e0760780102d24a0505090041f03040d03d00300c814885100751204c40c11007c00c80300500c0d1550341c45150803842868007064003070140040c003480601203080b0712540000d00c4003034091650070000043c188483d414290406058541c8042c0410001d04004159000f41c65101c100e40199600787d41c14000c011999405010110001120f4030b04204203 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 986793147 1250 986791897 986791901
    0xe0f010608011802010f050c010219260705070804050307030f12090e0c0c0f0f0c01021212010603181e02090a09050a03110120040306050121060504080705150a 70
    0x40041c04024400e901e600d48151040890036903019042005da440c0c814601406a02100c48021144000319600e1070301c0c3c0340c0e200c00b0204032208440090b01400741c9030f810100007003128001c02d602460b0007200d40c1710190b0646180c1d0062208464019007840005aa5541402024000c2d8080c40c20551000303400d1419100d001c0080b0410003d002c450003080c400743d41d2328402d2513807040800504130f9030f0741d040c0140107207442100d5201e44082d100300c00b41007082450200c2c544510320400e0302203454100f14a10122414059010180311140103a001040518400d40182c41545400d94850600c0001c039118080030742e611064078800c000d69810030074114241181102c1e4082007a040400c1101256501d9580312010744a001c0c08100c090a15005100d0b400e610034000c0100c402c500543c41c0c0840ca031707016029002840280c2d141071800300001980c8643d146e409141494500740c0300b55821036507580d10300802010300240d8482400303101d100b0019074104007040d08401f6034017840200f0f02d010b9040c502 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 986794397 1250 986793147 986793149
    0xa02250803150a03080a05031b0a1107080f120306010c12030b0a0b090904150b0d0c080f03030105490c08030f090d060e1c110d0504090c0c02040e0f0106 67
    0x4003850f000707041000411846401e0714200001441c24030795035110300e01d10943c0c070b0340c5200d8902415a00003810b8101640c120300700380b02c2800749030141c07061141d0f901700682c0c8880d580a00301c40c00e50801d62014108000050095900c080141005207400d13500e51102c1202c161001700c8540403a0f6200c01a80580c5490b42c0604005c00311111030500d414024000310301c01e500f000d04014603665503100243d45045140c1c00c40e40803400301034074607412101d150408040821040c402c0c0d5600d03005c1c030b240c000046d10700407044034107071350f0090040d81c41240990748450301d10b18106030f088203a5102c003c0580d0f0407504803e48107101c2c40300100b9010040c2c03041c1051300515071315612500312980200604483c104042098030b00b4518120354a844d440c1035410b21401a0407070601d60140c41c00345400b002c3e40000c1440e10305900c2c04440d83c034244042d01d201152561501002c0e0702901242c8140001c0240c01001d401c841c0c15549186840f10081c0740e9907000c541038840c00502601c1d2600700078030320340040409206800c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 986795647 1250 986794397 986794399
    0x1b03200406020d0e2704020d021306090b09040b1612150302120715031104080d030e16060903170d060f090b030c090408030925030c06080601080a0225080315 69
    0x29080c010702c480d80030a041e4080314554180e480c020700080031f541d181c5d40240000c0f5000fa00f0b4120200b1002007074001041280110540740d0b280010b11001c60030030b54011480340d40d000140a400c0e441e040000c0c0607801035101e5010420604d41407404800500c0d00030000e6100d140385000030424190300c104003034a00341042d54451984175600401051485a18006030443d4504000494409598210490348520b0300511181e201d60780b440c05190394190301100c40c0c03500200984a00c107400e50300486a0f130009103e46c600182e403806091003c18440d0f20310329986a4451815481d104d00021001e00740c40c415402140340e80680740301005040014043c0d0300010364100e01070300b628580500041c03c1060080c1c03014000c90000710014200001c100801c0640e031390201040e4991038000d8040c2c10b5140703072500080b9404031010314009100c03030203000280d024240584440c48103940c1c0388030300d00094000d0709400a5030b403624604407416000405645040340e024610881d541c2c9031010700002060000c8540c1 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 986796897 1250 986795647 986795659
    0x90d05152203120209010c0b0115080f01060e150702180403020706020f0316020d0503040b09030c06031905091f090b25030917040902030702101b03200406020d0e 71
    0x11400290f0203c80e6030300100031007200607101c9200300c0049036200c40c2c150004120ba003102c4004281c402c060100c901150f0f1055541c01d005644421b05405601800c0c402c8101194601c0c603400c4103843c00010b0083c0109000c192203007818000e400141040f00090f4031588240d4075541404140756040c041c000c0500704c640000e140c440a8a81c1040d500d200c3d0612000c0081070302041e100c11561902e10341e1614507002011640c84a803900d01c1d040050f030019032880d00c280b1403001e2082040c101f203401d0700d200d880401590340343c409103c90018003400006004003d50b010f4022020355101e1401c419101034110100005200152031411507600f500140035a850001c001901040c503402c00000e00108034914940801d0400962519103000e04003850400b250490115010070150400c3c2d0143d885120030741e088401d401d109000c50021150b28524084011201d01e40070703407145000e50049040c488910070741c0401d001e01034000740703210b4019400400041c2c120940e801446a40881c2c0d6950b668030840301 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 986798147 1250 986796897 986796961
    0x7060c050a12051003110423160309150504141b01080901050105031c11030a0e1e090a0b011101020a081803031918060c08071803050a08090d0515 64
    0x2e5425107400e140305c004c0017004401c0306410985c8864200203407026081007521810000c0d1059860141412034608094408800c0030f0600139100f402600130b071a8009520301d120308204001040a040000c0c81558048038643c0002d03140c0e5020800c1002000865072035100312072081e400100b2484003d456004942c0c14000140210340d400f04038584600320440400480406004003511a040c6401d8004041e000114448844036040702c1021100e01d81211a4460705003801888100840d8804256800004210005040200c00d500001007154141002c0717509520110315142a68448401000042c0c0018103001801c6c0e0b044028242c2114094003840c250700d041e124080210000910544100d615281074440014140300c0041c04a03130445001e2001100015000e40745120684031400041d51444048200010b40a881ea0699500c00c001e0b00e500c41c06038440d1810380d0440510154440c0120a4000010b5810420407809041d091402440781c644a28030f000b1124440322081c9001c011640 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 986799397 1250 986798147 986798161
    0xf0527010912051e0f06090c0a150c14150a090218040803040b060f100f08010b1312081c050402010e0609032509110405040c112107060c050a1205 64
    0x402c4c0d501c0500d0064820310b000005800545003441c5102444020700405c42031060482d8040380e0302d05100d901359058900c41d40c1e206030040005102808400008141412a80c0000e0b4401c85102141c2c00c0c1004507125418100268404910305440c58903c481c0d032050000c0c00c60034a0884440080381c03071081c1451034580b40d21000503d100c01070000b01810b00c06000142107555500043c00b500300080e0918604c185030307000c05016420401d441038086483e51000140e0128004210707500c10284001c0d0480e100e1a00300540c0c403194803c103080360f06240900c0b000c1022114002e004110309039800000c01c0c1420f0500014240340e20703610005009020801c00607250351800100740f42485404610f2100e10f030440407041c140d943c9903400c54220070f03003090024141040c0c0900a0000e0700e004030340800000c4c180401c1641c0c600700061400001e40c00004441c00a4050380741070700d94400e10b646001e4600845641c40208540c848088200030610106d62540102c0c0d00c2206030301444080c000800090034816 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 986800647 1250 986799397 986799403
    0x70c051804062003010b090a050a0602030a0c051e0706030501080613240203270a0c1502120a09031208060603010b07050a081803150c0a0f052701091205 67
    0x20809814140c480c0f910788039884440030044456003092116075243c0d40c41c2e01c00b00d0000d91080c80d10344e1140080a0010485160090304070048038041e40055142141424060b604803025080a40d0540541150f00091a588800e0b0700076084a8130b018204060a09a018040b142c060704a103545500c1322081011000b105e40c9803114903078104400381308500c21603c95030001205800c8030b010041c004001c0c040e08000441a0f03101c04800091044403803024580f4070343e5900903440c8041c240b04030b002002c00090181220482c002c0b1940c0c41604c00544280350310f0380c1d071079100302c5807000060704000c002c1040c0602c2c41001e12b8803001900d868011824107100140aa0106019070345140d0700c0010b042d4204003080141c442d00584c001c10154031042c0c1d1031080c80e260b442311440b6501900401c0366000102c42d85151345845103402e407140703e043c03108101040f41c400200a001c0414080c00f0006c02d007400112200e80da020107a207801c01000c4050002c00141110403d50010880302104054540015804 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 986801897 1250 986800647 986800651
    0x8090d0206071b0f110a0603140f100b03070203071e02030c011101060519090c021c200f0c0a09090804050d080708030901240302010e010f031d03070c0518 68
    0x645040f140e44004107803041034038404040300620703a07000b212070801003100c090f294103d1030307104031403110220766681025025036547c03014103084034520000081f000381c00c403040940c2002c8000d4403c00b0007520b4140b0310529900503a02240542c0c00410104100822640d00d0314186084c0c22a80d41040307020340c003080d40c9200042185060052503550b100d0f07070035825070100000705001017050340c0d01000314544041b000311901034103000381e0402104007070441c0001142e081440140d480d401d100b04507144200e03800d085c01200824240208000c0d5207002c40c1c1002040c0000c501031b40a441e02c0c1c0d420744c007044810200c9520114406082901c404007060146090714100c44058421114440691600c106a13100308000202500408801e00c07601e81030552042400207804c184c00500c5d0901c1d020858803186644c80024000b9826130001e0102c0d5100b0041c00489601c581400306500714a1207841c10780c109a113184240769480030a0450600403403900c00c1c0004d090036107400c10201a08040316070f0b02800 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 986803147 1250 986801897 986801911
    0x6090c031c0507200301061706070203090a0b0d11070305030a05070207060f030506042408160b07034e05010f0e070504030c0b041805010b180a09060e0708090d0206 72
    0x100705443d41c070213103541140b58400c01000b002000b00035100d0200e00c95a03200320008a116200c1d11002031042400007048504500d8002d08800550389007054580f581e034415007041b003006032100e08103c05c841011026111481c42900c840751649442e10340081240d9000f4494011980f28000402909410a04c1103604986030716002ca070542e12100171034058058400b05a02c81c540034004018042510322414003a602c15400f9510b14030040324204200141038041d94041220401840d000640610441880e56078514100b05025095484c030400030486d086648098054624100f00d4588100380c00070004400c1c40c504000c5035040219641c007158280c01101da0441c800360220340e0b0316005005607402950b00590102425441d01952101038106d881004586031003912a1502c0ca801030040d10305071a02003030a46d00309080483d1000d21040e0075000d00340c01c0808440c1c0030440e29107500960f00075000e491103481031410080002001100c1c001d00f000e016420a0101c029502d902098176500510b0b = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 986804397 1250 986803147 986803163
    0x305160c17250804080f010509033a0501090f020313062a020304090c0302091e040b030f070e250e01140c07050f01030204080a150e06090c031c0507 65
    0x1900b40c0c8001c4510b40101041e20100c2510007940e0401085400a1040d180c610042c0c078142010440c0751820390301d00750b4003690250400c0c42013030f1002c18071001990b1918258404580c004048440c042c40300c01507045400a008e4803680140480c00c2d140c011080b655514880c118907524054a03200c07004c030940c1000416090f158644480b4450811032031140040603c3c0c092404106483d0f0041d66035401803280240440c101824026024080e00c00e03203607400b2001c0d181a0317006092100380c034080c01c44bc17051158403a40e21541c0f0700071a141005000c0d0311004002c024202740303080026001403618020300c00d20001c0003000d00c070000c8280b000f0074100070b00d08505150300d00303008031801601c1029002c101030050403804628000d1b0f069000031510210798040d00c8420b602a0001c004506038401d40c0106045039000c03400c2c2400140c5042042a000b0641000c00150005103440d05418000266222880e5030f1042c41c0b8098980390605c00e40e0b40b0b81c40103900c040f01d0903040c5040500b079409407600280140b2 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 986805647 1250 986804397 986804407
    0x1806270b09031902060405070515030411040f020d1509090503070308060105070f050114010f0605090d0206040b03040c09060b070309050904060923060906010e1b07020603070305160c17 81
    0x9000300b040c0d800b00d5011021000300c0c81c0040c1da00035035641e0300300c406403070a2151020026807820030324140e218000600328060300d1540c0c1c580354044000ca50380030251700301ea607401701800c800b0040d1024210501c06054081075a0781c00040c020300b5002c1e036410120110381b07010340400020b04008110750010303500d030a1413020b07541d412006a032075000b12880a041103200d41004002c00006500600703200c0d03107031410074015907220041c10021344d031640200c002040080150f10014504511b030000f030240300603c1c49250584907040b0030104e41060fa402c480d0860140701c240200703501c0b4004d000141007402342042c00c001103524014038800c0c2a00c00d46018945a002040c2401159044948110307004245e010072540394000b00c400a02072411004594068040841c00a24011481504980020480a44946510820301070040c544802c920f850802000520300584855003d10b1042c10542c400040303078917108400d10040b400f4111070a0403c519000210006030858180e26400c90601c0c184940752 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 986806897 1250 986805647 986805661
    0x60109120503071a01091a13090f060f0506031c0207060e011e08090d05070c0b0c03120906070e04050f0c090a0f080d020708150c0304151806270b 64
    0x18410004040d00907103035182e86144184c28101d005049900044080024041001f402c0c0944288644e0306a48024207040345400c900150300701c003a4860186940070030f019801d944510455000c0d08c1d080382c042d601d1302e00700000b41ca0184540100200300035184800300c00a204000e459450600500c03081c0240f04403118540d034400d00c5c081c03400d480044240b44541030b01050240000c5000c85143c00c20344624491441528440e005451049038840c0c2880304060401a1006054000b0b1044c0c1026200030f00280b0750b4980a41500d50150300d070030b0007070101030400800090040d94009007007800b031401e0100303200440c0300801c950399001a82c10140c03621031040b940011403140882e80800c00c040c88451011403035040c0404c2e0b0082503c295022a0380b515600e55100f5261700325001380030314840421000035032986030305008640c0f251141c0d5002419441d28014002151700c3e0014841524580854450400503113104068600c1c0d490341500039000b190f070700000c0380845240300081c1000caa08000c9080 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 986808147 1250 986806897 986806903
    0x10f240306050c09062805040e180f031306140403120e040f020f1b070605071403070b1f0812090d080c010c0804060b0a12060209180117060903030601091205 69
    0x80488010031740c42e03a442d80300e52213416500003104a1240480038640221085004000326000c481249482c0c8207682d40e000c40d101c0500040215445050042030054400020300b480109420051525107c1c0b1f95402d0120051420350350119100b09020704000c140089180c850b07032010401c0491a000056041c1400410045e10040300c1e650815400450180c220318100800740410134032000b02400c0320014198408e588060b2440350a011820070041d45000c5250214a001c0c48059402140d00d048480e544020301c001c012650038210b0002d040822070300310030301592040280000401010b800070802d05144c4107100f2100070b039200e00b01c01203c1c8400c1044a2040c0c4229203e00f00c02001440700022000e0320404040354101c071500d1a001315811980384c412404400c0d42c0c581d0310401100c40031551480025406000d4403684203141c2d51301006404216a00b5501a281091018941d039910140303103441c0c12400341403420243c1041c404c12481d40d0380800b2110855400424041210700b9905085003 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 986809397 1250 986808147 986808157
    0xf0307080601060e151305060d0204050901060305090609010603120f1404090507020d03090302030313020f04050a0e150114151306090f0b07021809010e010e010f240306050c 76
    0xe85070040500000320140c20440b40d0210440654a154100c1c010070b4131034015100f03400300502000d00484060065003469409400008618140140351580b0b5000003035024400347e210f600002e480d034040100d041c905202ca107070080780080080c82100d007180d551010002a070114502044610030054414500c120040000c00135030341901b551b15600c0e246420702a001c01c07200c030005441040c0503402c009100e4465881b01e0354055020f54116141c0e2803292103146400300082c0d81c81941207801d076000b66214803c490080046000c00645520129685800c1840170b07003c01d00314000402c0100b00b4401c0400711a1101102207800000380040700050401c1d5000748407855144c800002404140c507600041e003903040d500c0c4003940c00c62050352954082d03031520410b07000941000c0a0301038548590203400c182508915480000b2038182c00c102199400c413600120600c20323980d12400503c2c0039450520503044c0c1c902c8008d40d2414080c0c044612400400003500c030090074942e4440000300c80b07180d41d2040e20 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 986810647 1250 986809397 986809409
    0x304212a23011b0f110111070605180414070801030c12020d08030606070f0b01030b011401022a032d0c01140306030a08070311070e060a0b1c060314070510080103020f0307 75
    0xc81030121342c2000460155188011400301e128500c4002010b040011040201d401c4c0340d850fa0716002c014800345011081140b2100c0e0484e4031020710200c804a0003080e94030070203166550703400561440c10244001d105680c4140d200040c0c20311094090303101d409020001c0750304580d26a5480c0c6507a00807404030310801e80c01820341407079480c00204111034003800034100c0c0d00404102c0920790301c407500c241c2a5546260307501c2c00b59000110200c0134005101c140da00894446005100c90125900480d051031000ea841c12440028424145101d10000c02034014840a26009120403007900c00080e00d501503007500c0328198080800040c8066504009040d24180d01c40d40302a03c03400c0b00e02e4007420707030703c617400003000303980134040c800306510790364651103441a07030000c158500140c54055110380641c4030b03e0f00d009a507506414a83d40c1c5d0343c1180148001036118424400c0c48001c0b0500643c14844c068100c0c80c407680020041c00c40e01617100ba101410349030100c4030081030100b5080003e1038250168008 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 986811897 1250 986810647 986810663
    0xd051617070b0609150d1412040501020f07052110060e0a0c0c170703030b040213030b0a050c09040b120105070909110306030304212a23011b 62
    0x80c940088180c05000340c00e11070070040362551140b808100101e40c01300e40c80d6244001502000a0034640178108890250140d1600161503a114100e18186540390101101d103850005040099581c10014600279803c1d481c0a003034447c0c00d1200007441d0b14401c0e400000380c0c0030343c0b480007400080144903007024110089010445250b0740c1b104d070781c0e00003400c407a001100c5140189644465014001c1ca8103940d40c81480f03c032400e4840941c421460300a41c0013542010703616102d00000707440d60300c028603000c0c41c11201501020302d0340c034200b000524010420071915003800c082c010406940c800303544802108a03400f0610f134807000c1c0801c41c05d000358807580a5940c00c0109111906803c0b44036981508c440174000e000c0d40c1c4890001e0045440161580c03505544100800c10107035100001c820380300c401207050a001042d00d529210a10345a041031450060309404032450300f0700c0c0306101013008085001c403036858648400e8400034000d170700d10700e03030b5060004075850250855001940264401c3e400350403 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 986813147 1250 986811897 986811923
    0x1806040209011b0c0303080c030f04060e0a050105040809040c050c030a05090d06140405070801020901120507171e01150e01030902030c060c0a020406140901060e0f0a08100501170d0516 81
    0x8044c51302515840b00350b0200d5200000300d910225008100ca00c54012251860b000c1e0300d403665000c0061200040055080c0203c42e00c107000500d00380a081e004c0c90041081c203450325209001c000894907640b00580602c00100141c0001c1e5001000b07aa4418403241001d03a10b8112070801b0403441e40440c0402401d1518014031240803285801c0e0050090307020b1002c607102251921070150803803082245090204005000040c110000d913080158480a2841d000c0d00c5082c0c0c4003441007a04800351032446140048120f1b0915040e480044903004050401c030f400d010320f0769200040c0c820170200d0100d030304264035a98100c040d910104440d505582000d031000c0c0da00c400c03012100d0f41710b03e0342c4d0200700d02ca941884000213281c0d030194244112008000d0003010300d4ed107000343c1a00c0c1000300750401e035040518240507100d55580d14102000502414000e0824a2904c109141c1141c00582145540c4080c180c2d00e201680c800296500c04038116007040707503880c000e40510f003d2401012000900303003000384031 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 986814397 1250 986813147 986813153
    0xd0b0901060b030a0e010c0513030809060409110c21040b0703140a020106183b030a030203090f0d020d050a120f23092a0406090507020c1806040209011b 67
    0x403101ca0001781c5400200f1007111152400c40b494401d51112904007050514240b001c204030500912100d0b500400c0d080c41c00b5a02d000d06004d0760707030f0302c8080800418045441c0403a28420300c0701412131202d204200340e8016100c210350b03a0b01d010303a014584848001082c0d01d010140130b65483c085602281d1001601c4d0582e0b5080280038001d203001e54424403091401065244500b80218445801030718400e10305c01d84d14403000a1800803440d2001c00c40010600c0c440e00c0214140010b1541c15030942e40540d0300d1403c0d1250074034000d60f101c071400ba25480121001085940401c0d03080c448c0300c0c64070b4100c0e910401c6040450307010302c89584102407980707440c130715907260750456101c6191a060403c15480e4520b10041c8040017a6045465071100d810560580407080a9003400707008081601007030915480d100e0010804592240d040501a80c0e0360b0000e000001741c0420100c00b6000b4210b03100201c4580b2034140e004c0d03619026109a014980120b04043d060380078203500d000180c802c81c510038040300182 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 986815647 1250 986814397 986814401
    0xa23010e0d0f0e03120715140406050106082823040c0f031a0a06030b044b020f13061406090607020d080c01020c1c020304050d0b0901060b030a 63
    0x24210380702040500d80038032001c0e070082d40c03080c001d01001000b8005562600140e01400d0340071041c2202c0124909660419400c281e1007075118000c807001800455141a14050b01240c030180c0002d024003108500b04403202c500c400c1e054054580143c420014078110324800f00162084c0403424416420484d00c480512080707030b062500c00ea0051420300c43c0b080d0341e25881c403500889400094a14080c2c0d17815500d0303543c3d02900040d00701c00c83c0c000c0060107544c0c9407110610a401a07400702c41d00d000c1040d91401c03c2500140c54401d00000402c100181e0144000c8140601c12400303801c0456000b130f59050041d035551403850200c10402500c055941d50700741040070000d009030f0003034150307000c0c00d502c0000460919a066030101c0c01c014201500d1300160390208080031480030340c22519204100061444203100380051301400b11ba0100505c0341c0080911741041d480d020705010804c640c405c1c8000c012a98500d00d280214603007100a501458a51245182c003608e002d070030107c42d1150002c01d002500d8280c0e = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 986816897 1250 986815647 986815663
    0xe030c0111121005010906031512060f05070921020303090409080c0d08040804170106030818090c0c030307140c0106140907031517010b031203270a23010e 68
    0x42080c500541d500000710301d8050310f80c019940001c103440020700405c0d00940c001a2601c001100392480340350356464040b059001a0411030b03285890f80c4d06028503c4590140320303008012030500c0d44c0c0e101d080064201c0460b41d86120b120403054220080c00654030705204407620024060414041203400b4104828194083d408048480c440e42c0f01d06000280728454190099900c40300c0c0e545414038010b4a0b4440c81c0141d110000103540c0e508000001400c01c1004144900201141c143c40040100c2041081c106c0184040e040c0300c0304000c4c0303d800e40400300841e036020360305017051259181c03018030440306d601030214040352a6103408800f090741c0114100c02e20400400301c400c081d6540c1e1380d140407410380d170000010740340305030072100280441c00c0780b2a0300905a03001500002b0f1001c2d503501c0002e24000d481c868401d5000c1001040c04428903e03054600c10901c0100103140c1807000751151640d6030482068013612610456079011603001d01032510705c003015207001c000d1049400c400341046e11030b00c034 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 986818147 1250 986816897 986816917
    0x2060c010501060c1e030507142d160815040c030c0b0409050603030c06010603050612100f1b0c030c031110050708090c0a1e0f090903030c09030203060a0e030c0111 72
    0x2580e0455505c0001050300c40380b040e50641ea094140038543c1d81d07840148070301003d025102d000d4a0074050946449809040142c071388540841e07c040f14102e5080d0170003071203400c80e03405042c40d64424000680c1c0001c10440041c0018014070f802da80740d060502d8920350a81000301400300ba00030010700548400c001c0c205641005004100544480d8201592031043e8000d1403010381100b401004000c0c02580180d91104014105950306542c129405050840355244410120707a26079010414040303900c40c4116500309400c6040070001c140702d01400700c14061070300904000540300c10b030041500c00d051148000030110308541042e54044070f4640a014110b89640016951000280e0100170001f02d100818002521407500c3c076044c1848a014644e1110b000780415010000008401c0145440d000082c0800031000882d00503901d80242030f10760700e050070002c000a128013403015070f0f07002c180c2d16040320b80c0c2c00000030310f48601c1480c0d03400c42c040c5c110464469407801017801e8224130b407003005100241d0717 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 986819397 1250 986818147 986818163
    0x402061e1602040609052403011d010608070f06140a090f0806090c010503101a07021c03090e07080c0d060504050118110a170a1821210902060c010501060c 68
    0x502c5e03020301c80072100c040714461b034540c04901c901006c0b4158060444080c00d409000880c0303102c120314030000004103604952101d070b956600f08101c001c50900c0088050720070300c641c400103940b9280d0020055103480101e0700150300001100c2103030701c1c01056000010180e688569246550310b40450b515040c003258810783c68020450007442d190b101701c0450740715080c116190340e4414144030900302d100003101100d00d51150100240c10150b03550618881c0d8161a076005000b03445020310300107040303400039030207000e0103d03556062100464014070710070b50040e07100000039102c1c0a48208140034240c40c0d4031058005140c20f0001c55680051040031008030f8003040140100c2102070140c1d03c161046200c844001100102040d52045442c5c900390b420103a480d401080c800ca69506c00c041010400e141281d4074040d0401402a15242003100311000801c1d05002600a81200040340002202041d940c252542c0b4071508e402c55542e082510002004c440003000151713103980300034004480880d070a81d0444 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 986820647 1250 986819397 986819399
    0x190e0904031e2a020102160b0306030f0d05030105310b040e030c0a020f0105190c062301030311120c06060a051e0103020913020d051602150402061e16020406 69
    0x40c010240580494007015120100d03002403092016443c2c80345404038118010103281400003405000b50300050130051142c2070740d81c1000d800301490104036800e04800d541040a45e250030700e80040a8070b04403042a40c111042c080300003403c0b880a0b5111116801620040040240300b0002d07a001d045035035001d84041003480070000c0c2c550703928083e07552840c121340e120b82200030060070b110b042c0c059501c0c410304103241044000b210700c00700c21000c00b0980d00002c400b00002018450700e405000c2600700e03040e074100c0c01c0c1004010f0100941c4414080542400345103400708546080801c41c01d888030940356036030b035103034282d21090b942c4801c000e440d014428003050202280510f00b16001c007408510040c560070340125003c1c01540030f0342002002c1903000310074000040c68969a4001410201c08072180000d00749800201d00b800c0a064410001c215408810b20b00d4001e080b01400c5038225030125401c5444042400c44011f99110415401d9041e09010964010403100e09480398002407003120188045 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 986821897 1250 986820647 986820707
    0x90405040c09020d0b15070507140105071a04030e041b142517030f01060e030312070507030809010c02071802070f03020604030f02030306060a0509040b03070b0d0b06090105190e090403 81
    0x10f00400b68041e1660300651002c001c0022b071844441300005040c14403500b40f103801d84501c040030b54030440d07200002c05070100f00810590302280307403200d800d0100d03810040c449101040c8a0030220b055030300802d205c1845401140190711005507403a442d0b154071042c0e9100340c2d448a0780854464a00f088030b90803044184104014010400e03284a40300b19107a8001c540c0c80c0c624121052806c2044c00d81c2c050004002086440d041d0650141c8034400a8030782c6a50780c41c05142c0100304a0b00180b036510a40d1400d013081d6013103079000c0f48200403a100190494104102984414003d01c10200d00810b010a0030184004064000c102c40d0f114501a4a40b101d407059640c000317076101e20040380d9155002030200005884c2a01a80c0940710070080076000288180860010030310344541500000b0700600301080642601003a80224100044151005402c1282e10400640035008510340c1c40403990040705440c4800c0c0c403800d0100c104e03060080c8002d03c0c50500742009031421000b00c580b034446104841c0c0350506 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 986823147 1250 986821897 986821939
    0x90b090a050c1222030908061b0423040212071d01020a080a03092a0f0506073f090501080f0f09100501080c01180b090405040c09020d0b 60
    0x454003556007002e1800380082400e03603c858004012074003104075078059007292249640551016803090f141c9403556828640380780d203040c10003043c2d25541c03a8100402130601006c401518100c46400c9940f030031443d030800700010900c0079820181d4009202185040300c039804002032a0040b403181e2211007451008048070382c0e0a220704140e03540542d2180d400040002c002100400d03028650381703400070b040f0750260317152904001069503070350130480c400d500100c044440c2d003145401003500c2200d14003024078080110701540180d2001134140c100e040089903904100d048407503a07001500038440280c0c05038040c3d40d2100404808a02c00080c2d82c03260200c2c1e9940180e10032801b030040070030b44080d15070b141040c01d60b48401c0188090035a02480c5120140c1c00540d01070107010307007204805440360b00f02031000106081d6003483d828040c02c000100401881510030116200f45c1380945000c80c1641c1e544c1070543c400703c400e52140c6403441c8001540840b0050302c0d40411000113003100d0301c034085540c040e49251 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 986824397 1250 986823147 986823151
    0x22203050727020307020a1205070519050309060304050102040306050f04151a03071710020f030417271009081506040603080408031804060f03081c06090b090a05 71
    0x1003a980079010030300c200803201018101d41280c501e01c1c2e8100302e2100c0304032426600103036003000150b8032150300c07070040000003c81402918000d2030110305058140c1c840c03075511601201d40c1003c0102080c034020a201d4240219100080d002d40b02560b64206450514000c1d8400e05c0300384c030680d203003d0215501e01c40282006014982011340890f00c02c42451640d0014141d052a4002007088044001c1c080e84051094500801e0002c1d007408244601c01c00c0c2c24245400c0345c418808040c410001862403203010001d07a6005900841040e0041681d01c800036541d02c41d4003544d81034511400320030041c2c80d1101c41c2e803000d10303141510640000c400ca0305041d42c04900c207004052043e000407054100c880418814103601520042c0b010460365500d4035481d82c80d80c81904040d08541001422025042618030405883e950540d81001040e06c0d020210400e422a0b000060113104005000d45543c500ba40c042599042e036140e04026090340d840e4400000d0454041442c003e0710840c0000b0441c05481c411a8 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 986825647 1250 986824397 986824403
    0xf1704090e1c21060b0904050606070506070c05010e0304090c02011a0a18020403060507080601170f040602030a1508030c01200d0507090305101a090601090303050d110706022203 78
    0x2070b40c00300491009071100c5080750805544140405602a041c40442c0120b000074075405081d1030392440400148800e03240700405886c09070a08102000016100240b00303640301c0300920b000c65407000149049409004603440d40c01692001140215801034039920108000a0319002082410004405d0312341440640703600342e920142c0c1c1102040741450388c034503c0c4018200205c0c014541622a03803198120780b000d44a0034000344081e020000d0b1b550b008400848450440407090175a40f410905400180d98018001401c00d40c012000c1050648260000c610044c840202a07060988841c045035503500022003200c040c3d0b0a000e0b0000d081c9541c0f040c94040c0482034081d0510380100c684011001e040301810900c1040860b541c00400b02d142808050700e24500500013143c0e01003040e44c1c02c81c0c0000802d05680c4151000f4041c000c05070b8104900508403503142c01c029896582d004c10500c01009041c00e0500fa00500054280402140707900514008019101002d0005101250502d214107180401 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 986826897 1250 986825647 986825683
    0x6061e08160c08070503210c0a0e012c0a0f06120903020c090f0105031005131115040303080f07030b0a0905040c230312031504090f1704090e 62
    0x100c0c419100d600401c08008019060000c4895259900c14590758004082521907400100c0e406612044c84003d5070800c804030901d540c0c07d420a07109a880c02e101d04001c6a045c03000c4465a0311243e4042c603401140007038455148101400350325001594014909440c40c85004080c2c000300c0c40d1448042e110007591140d80d103056504c00c034141640300411080c42c040d0294480ca03a40d0480ca5a1040780c00d81c481c0da8101c0100c031181d45880181443d00c44044846040310307040001b004184a04903603020845a00100c40c0491102242c022a014911090380030804500024000c02810b8104140d1805441d0101100c02d00e5a90250201d0494401c885280e922096212042007001c1c255000590824010400307131102036990020340b001c1c0c103110100c029a04e00007240e0500d0078a400d00c03605441d0110f9000c030f40d245107000f20301c0042c0c0c611524000c0e07200700da846000c10203200a1110120141c0d9001003003410392000e0031104800380d00300b0320900105c40d041c41c2c8032400c500808161011b224124100c5 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 986828147 1250 986826897 986826901
    0x30c030e0102270d0c0f090606020615130b150c0f15241c03021009031b031e0203030912040303140a1e0905030c0405010b0706110f0703020106061e08 66
    0x44050811100100c3d07a0720030943c6108902180e8510f55000080030395510789580c541c5401140e505030b9040754000010364220f00104111005103041c0ca0406110403600c181550001840c5040149070340701026401510390590409045219070003030814041b02400c40c1c000c40c500c81f000c0c985d81e0030304e40c01c02c105a2840c00007141000d02c400c0340010f02a2401d40900c120520204046041e0a620104480f154980c03051403106058040c07050016030304020000b884a00c07030a0310f024089002c80c030b291114400341404072a051500c03c4c001644610785808003c07049802844d4000c1d540c0d081500d41c115039014a001a042c0031242001312001c481e8580c43d488002070181c200749034281c101105c20018040d0107039440d00c8030654544601c1030740e141c9072a2101050708001c2812300d004000226180114034150040c0318101c18001600c0d1f0460f8001004221b600700700300d182d00e080c0a1603002c000d00c3d60300030402c00c0030181c040d0004810341c2d0569407054280040b101d8240c0380b01c00c40c0d1004401240000c00 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 986829397 1250 986828147 986828197
    0x1051c020f010f05042c09010b01020a021c0503030c091206010608070c030908061e07030b0102100507032a030f1404200a03051b04020a050f0702040b060307030c030e0102 75
    0x20751807241071610b0a019040959441c00445860141b00190014058030f020042800781d48044154000d100d07040200700c07400c1c041e00041e64940d103014029108541480782550800f81d151040010b5070b50140c1504d49034244126055503581001da0154443c100d400c038a1817500700c00281007070407a045a40d070144541ca0303a100980c2e9175416510194101304006ca0302040711907080203a1400f414081e01021442e442c403100000008602504040070181420303801d03034050380c1c0001d001588042c1e0810001d2107488150701a0020f00c070001d880d080c1c041c01c2c2c101554120803040404e008189141d00d09000c1c403480d040d80e030b81c1200c1050382d10128046085000c50041001480e800d024034030030030000c0d800c01c900c1740000350182c840c0744d204460f141d02c100c0300c2216403840c140c00744055980c1503c080d403c10340081c90240c140c1c060b003a0442d0f81100040740031000d664503600031066644010300400d030b89091041000780603200030f9443c1030109080482020b8038810510031104481007105103007280b001451 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 986830647 1250 986829397 986829407
    0x402060d05220b040507170a02010521090a0506010f0e0c0a030f240b04030b010b030907090f0507170105030d051b010f05070f03290d06110301051c020f01 68
    0x2e070000d20424a00710301c01440c40101c0b140307010101d00518480e4030516141c5051032604002d5000524040d00b00b110403140c0500000d82d00c0c201aa09081445d00c4181c06440440400740f6416043d41542145051200c0f00700042001910302c0d010b0020745490b85c0c0c0b18090b021030030165104200c08100543d0000c3c4049550b0009090008001d14001c00d544082020500a858802c032007842941d0304061511200008000c030352000b0311041640c0ba042070310b11348400050200c14890790200340000400540d1507101801500c0142c202e8610810441c0e80e01400c94004000444525001c14540d00c06a08038629118403a4101c075001402003030000b00c0c10a04031001d0b00203071201000502d182d488100585420f000ea0003810080c00e50004091610007401440e505042c10b02c1021305203000d030001022400c0d0314003410103403400d000100342d00c0b0400011513010408010b0151969281880040d10f075500c4500660403124101c602c00c804844400d040c403042c0400210003580032002d03008000c0c0ea94010 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 986831897 1250 986830647 986830651
    0x30f050301121416030c090f09050a0b0907030519060f0e12090f091501022514060c0f15010b160210030617063c04140f0319080402060d05 61
    0x50f0701603038102c01c040e915034a00320007a0b810071540f41540f484240405022403050310584220683c00340800e0081d515042d465680c4500050a14008a000102d1019081000000031540001102d0050440c5920b808042da8009011110117080050b445290401ca0080034100306106e4003511241c0c20345140000d15901c80c0614580008001400748042e82c0c1d60750b0b00c50b10400c42c412103c142900b4580009041c0480d0009030305c0c90340641c4400d000e0308030ba1b80c02035606507400034060701c540c0780321800082d445000365202c05910348918102c034400050040745041001d1148900d41d04540d88601e406611030040030030f204034039502c1030740400240c40c01c004c10107076180c01c0b4200010b003541c0b92025400c050030303180101e6007282d0015003844643c19648800b030445850355150b2204503a0403054609848418131041400003070503030082000e2141c42003c06010040f42c00c203c4000780202c2c0c000680f20b03000703d0701114190042e000d0075079225000c0c4645034859030340100207500d03104e00c10003541d00070400 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 986833147 1250 986831897 986831933
    0x60c0f1103120415020c0709060b0310150e0405160e0324220807030f0302030c19030f0c030e0c0607030207210512070b0618060d0201031401060c030f05030112 70
    0x310307004900000d18505c0140000840f00380601249820001d05c2030039280194054a0070050400800c5001041d90f07588409840450310780c0160001c0c1c00204450800402420301d91140ca00003d01804000703400c220600307441c1ca5119a410032000d541003580350010a680745036060004481d1201003288070624981c460305801c520700d0f06003511802581d1400500c2d07411682c0d41000188207090540018000b11429582e2070103510794030700f81d80714280038040d44079626501c2c0034407134010340d2450094020060003072015804111042e03143e01d0060140000c00040e4090303002c0c4244503111030410004032803e280d01500140300702490301031890304580c43c02f00700d101d44e05000c007088000910103010b02446040301441003034a4900da0700707001200d044041c110621407010070003003080c070001380a40c0d03640c400c1003214181d00e01030031030006074050540d604c00c9100c40c51141c0004280710b500181603461040c0640d44500131030880c20415100f51000303015040b000e0310403540380d1001801c1c0c3c5039140c1c41100c0c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 986834397 1250 986833147 986833163
    0x151b200f060619180c17040c0501113a0309050c1908030a080f1e071202040801020f03010e130f0f0201050c01020a121505010804020f1804060c0f11031204 68
    0xd40c03400484441c03c042120000c031142c0b03944104005c1540000d408486041a181c40c00841c18540d854071f0a21980d031050724184140c06004800401051004481e480c0c14290900c4034602e0030650360460002a0f0600b801410168101e000c07510712034130403010b0007030340080142482100e2400b048115410700400b0034034801075003c0414102d0301030000c0c1c00b00c01500d884003603140c02c281000640c0d21a0080c2030001803004c3d2242c45c00e401410300002c0c4d402c0445400c0a520000301624030b000070f0b1080b500f04603681e40c00002c0e0030002000c0d01c00210704176103154095005988504040040d82004413074040d00d41450010000b002c20303069079010984d0340c41410017502c0d00504503c074600f6a00701101c0712002c5041c0300e41c1c404005402d4001c0f03e071541d07a100d101d002c0741800c000000e8071005015002a00810080c00c800c0c03403549031484041081034080d00c0e40041d514082c6082d2010b84403913080e54000401d05eaa0a00c00a80111401d500d0284c121020354209450b902d00014880d42c028800d640d101 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 986835647 1250 986834397 986834399
    0x90c05130923010605010e010f0f0e1008190e071419170f0d1403060f04050f04110303071104020a1206060c14120304151b200f060619 59
    0xc42550b541800508840600e2807000c2c5480c2c812821150070f644440d0502010a0302d100d001daa2100401c2411741440c280401103488096049030000c3c040407940360080f1039213002d0000c00340c010400601c40c000d8a508001100185200581540c00c2d103168031005910081e014002e10a000c0340d0848a0103015000030740d1741c01001540840b010300340d400f41e4004200786200452140043c40040d0555400b03a004080c03a00800600404980542168040c42e0b4400300c0810702e541d03106410100002da00074003d020f907050600400380c42171001d840407603042c5164018a5214100402918805500a03600140c403482490900000c1d500a081580c10040c0c0c80e02020b030114101e21404001e0607040c1d0710080070024074601100010790150503001c0c1c4d90310010041d201070808004503036025078041110030310441c103000c41d440541058140c0b20421700300406095110790348003d0344828040040c0d00c00078059003034101e50307844803888a9004a41d4110000203821030400300c01c0702c1034049506c58189141e0b = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 986836897 1250 986835647 986835653
    0x406080a0b061b0f0d0509100e03010504050c10020d08130813030c180501030b07110709050108011e0b030d20010e0303070f1409040f0626060a090c051309 68
    0x140e405403055035500714050304040c1c49003070200084203140f05034000404c0d49170700d060000340035800740600e580d2041c4203900c8040f68551003900e50103c4007038007a000744214200f600e1f10a40340c0003a00203d501841a141c161400360f031000410107a0368016858842c0740342c42c2c0c0c0a01e40c5800325a01d0043d1507000d010810441c0140014a1400c0110300414001491600f0000c2064141e18480c0d40b00340329030f00300070040c400308154854040d00315103131b402c0800c014032600708171909110181d809600507916140001501c19419044403007446248102c0040185480c2c040300111600000c41c0d980690100010545040c01000082403c0320150407886c030224000704100d09540b600080d0518a40000c4140400140c01000804409145060600d050000304040202502440b2030140c440c0307854007003444054071175920540140088180c003c1d05001c90b802900c000341888615071304144101c1002030f034140803610840010603840381ca1034407098a008100f102020702900d0311032019540c0e50001e400 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 986838147 1250 986836897 986836909
    0xa0605033d0608060111030415021906060e0a0c4a09090c09041e060603050a020a2102010e04020415210504030503041e020a1707120203030406080a0b 66
    0x12289900500071200350a05400030b10b840f101400701e506100311558109a008004002c3d038050700d64040c1d180b10030581e00303041245003103201c9070440c042d140302e010310701c05001c0150000c0c0140e40052084504680703070824a00c003203810311900d1600240b2500354941d9001198098206003380d4484443d80c200e0705420780c05118001001070041c41c81401082c10f041d4101308070000d074080e58803409001c8861201000c40d0100740001c10080c420803200c084110210141c21891601d1500b2580410140b500c903d0401da8aa5000406911441500c400090703440740700080f500a500000c08640002c003220341c0150360a4132042612540a03400344004600312130154100c45800c0f02c155212205001805080c0f4200080c60700600752285c1010300b040301081c0c20408032078101c3d91100100b40494400001c6e11818240207200035440040300d000014000c0c40402c1c500a162142c40c00c3d20701240e921000c000d1094082a002034158200307200820019001d003c044c1d03400900500b0200f46d402030390340003079a = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 986839397 1250 986838147 986838241
    0xa02040509010f15032612070c1112250806070305070f030b1c0501021e0309010e0c030a14070803040f06090503030307080609090f010e030a02010b0a060503 69
    0x24603950f4a00d0600c50200c0d0380180e0074031580381041140003e045840303e0403103800107102c0401207a40e209141150f980034004680c01005a020314180e10304100030010700c0b03007601140c04c1e100b849500c2d1a1040c01d142c0603812a6003401c1500007030003a04030301180030428195060440170451202000014000d4050288902ca004190b07400100c625124401078258200c041d0980209403514035640300316142e01058080405019024409100603850814064442c2a210714180720036224801d840803c188051406a51050000d00c00c194070444c0403aa40c0881d40051645075114030180804078210000c0075200403120000d0760000303a2551a40b0b0300c1c1d42e201d64001e00c0252000403003081105c6c0d03c0380100000d4003080b00918514184108000d1004c04050112849031081d4804111950010404182e988040400038440305202c1c0b0034940c2c50b50001903083c0055420030079500510b00d800d15000040c0c640b6516070500b0364990200c0340f6076900c41c0d401c41145035042527100c0301c0b980c451203c08031 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 986840647 1250 986839397 986839411
    0x509030903061501110d0503071b02040f1a0d02181005030604050a15110a110f07030308040204180302120a0e18041209150c020d2405010e060603180a020405 69
    0xd007038102c400d00045c04a08010350401207038020a015440386580f1070204e0342c05c0f464929100c18070040c400300300c94000c5500c40009500614000040d00b64041540110b00100e6900f2110b5041d10000c40c00d108071070031058030081d88001c45040595144a4112105802210714907420780701c05d80381c03008680f0340441540c2c20744e2664400d50312002000302c881000c0c100e14007214003d0001001c4c06410b0350031030145419040078813005890b101c2e55140300b0469aa44048003c0c101d8a0740787c1d46c1d0030040c105110985082e1301030b40c184034410421403810021400c015134140d008041401d2140c198040e1500025034810402c030a101140416541e511b41d8440c1c01806081e043c0e00c071303091500e022100c1550710501c032803d1000b088020001048540c010703080142281c01c0c0405844003d100081101c0010700e8020582001d44072401d030300070070344000c20940c0d03103003c28100031903600c502249941d0718040f60120780c004020000120000450960880c00400000464040c00600c1d80001d060312400ca500f5 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 986841897 1250 986840647 986840671
    0xf0908040b0c0105060307050a060f03090c170c0406031a0c04030c06030e060f06150c10062402011802060d0207060c030b010f0c0f0b060613030605062809050903090306 74
    0x12030600030b003e214054200c01c00f1802407036540c3c40c00022882440c1c003849540c09108502018064141c001e8101001283d400b0f040c0d154540c2c1c46126400036004c1100c101c0d0420310601401034054142840f5400540c1d401491b81d8218007464981c59801d0b1341c00601003680e15005000c00000100d0314414400a401e9940700841c58407003400b0b4075407500d44000c116a00110046040c80f9054940624641c1400f101d2409680c1e5a001c07560114a07049140d41182d0030546080d60028900341e500070755400341083d44000206880c81c2c40000c9082c3c0d031013807915208517510508030a005141ca0002818035041200c405030900589881d040c0844040548090110b81c640005120560344001080c0082440b402d000d40c1441d0203455103442c015030250001c1c02c1c98001d90200c2e0055441314103070f42008006088030054140c80b450300c2d002410f4141d44460003001170b000340c8003d001c50b2106146a14900e0b90804140c50b24004070b4902400c0050806c4450380410042c259403501c0a2140c035118944910386 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 986843147 1250 986841897 986841907
    0x30c0a110f0102040306140717130219150206010b0306010c17071401110412110316030c06030c030203090a330b130207080712090905160e0f0a090f0908040b 69
    0x6d01919408036092601d40c0300d840030000060381007820b8520088114400c0b607440d507140c10b0303411242d000310000a540103002c072003500b0310701740c00d0803524084c1c2d00b2810f01a051b41c404140182d81d20607080c06990400001400014003d501c0b803440c91380903030301a6095a0b40980c0f030910b8420b07244e01c00703001510515101b005d0300034584000d02070b604800d056003820034034140c0307000200405400040d000419400a40c507412116990801c011050100305e014204041c0c2e03170345d00e013006030f1100314401c2c0d1000c241001c00300542d1500034030a43c0e100d01e1440024040105083c0d40d1031528013440e45480c2441d81e105030007035407581c1d640307450445c0e240c0d1403100c00182c0c0d5207800100141c0308040c41c801400c00e030040020400040c500c0c0180c0c0d4200368461503c1001207074583d41a01d0964003a0844410b19260200b08048410a00310140c0c81c807409071155903903110080144410000c120722a190030584100c030405c060b410543c07109407117000c465000161824640d40d83c4c0e2080d482540f00c1c4e0b8030700c03002141e = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 986844397 1250 986843147 986843153
    0x30606090902030d08060607031803120f03060608160c231b04061d04060e060c030601030b15032206150302031504020f0112090b01030530030c0a110f01020403 70
    0x13042d4800d035a22070524484070300c4d1400024050f0710903000010100690302c0312a0915504141c60640039562000218800c0d282d0950020147c1c0c0c2250101c0d0300081c00e02d000040c2940c040c0701101d003e40001c100811a01042c00030540d03d104005504850800d0801d03500b141102005800000c0081144064800340300b00d80710307c403e401005601c0b00d2285c0d24148007081502c80002000e03501c41c03d40c050b040742903070b1941005401801d600c00c0311292030080c2d4080101400e8a0b2000b0361040e01c003601e040061940c44414084180d01c0b50b81c800303a05000820208191002113601c180010010161200442049070745600a80b182181100e140781103d541c03c0c0210700d014070050b120403400c404c40e441c1c40d19160300090324204905900c1410b205020450018000440c3c00501c401038104014101d6569240f403c01c1c1d541d08030340b040d5500103210f424080d0b040030b03c00b01440351480360382c1d02c8542181c03100c0c03c02c2e030015846098268244121403d2100d80b040044c440380c410600e825000684032403441c1 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 986845647 1250 986844397 986844403
    0xe0409032007080a2618040e0105040308070e0301110c030a0206070f0f1805180708090a08030f060307121101140702011d040e07031428150603060609090203 69
    0x20912582c1c101000a0104460000d13010042d1078100607000314585001044450084417128600c40040c0c001952160001100806040c59042568104211900e8400c050b007200d1050754010005081140452001c501c100c1810701071100c004c00010b5000b0a0181030b0300c0c542d01266400446400100b24801c2103501070210640c4582c507401c1003840d541c04620000c0050110fa8845002d01243e1f100b49041e18064a8800c00034150103004c0391203149807045416840a0103c58110000b1100c000090b54a030000c2081c0500340c0d031040101d0b080d03031100c5031045c400007001003040350180b14241001400e641013000d0344480074040e0008000145030900010019210f0903804802400c041199038010b036070120034a480f041c82202d01c001078062810015003e0b10742c04c202c0d20280e01c6803050200912441c0c281c1c43e000340d011002110046220b0304078642c0041400b00c13210318080e04d4480c6400100302c0c003160103030320f03500c602c0400100d05840e580e03410308441d0f81d40c03c40c450450790b40318142d086003410 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 986846897 1250 986845647 986845697
    0x209131e0c091503020909091c0f0c02041d030714012d0b030109080a050406030b121906180f020f091009151a091309050d08070e040903 60
    0x3400a00000c9044000944441000e20560741c0e500041c541800700d41d4440c2e8142d44442100401e41c041500f403000c101507541c0011414116141e5590100304180c5d03004117290307070541c0303826140c6500314800e40e02040010300c82c80c859001c8a840c00459920054018001010180c0c4110345110140301c141c3c3c56203003100c43d2240036201c44184030030703074464001003421000c05100c000702c1d0204403404044046801b5064a034001440ba510100310340c3c098540010107441610060754041141c40050380c00c1010b20341c03005050590a801040d40120f0060340d268000f0001805600041104060168400702500f59164181d83c0c00781c0c001000b908514040d808801c15501c00c99013101c190034412004503002e00240700320000141d0394492145015000803804004001c0c048251041d2560000c000b9050b90180e0500c9201d00e04001c1044403840b554480c0c0a8025081401000d03c01c1039400c0c15507000b032000d0042800e10000d031030340f403c03550788a0042c20061031090392458191a51740720b10549045076 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 986848147 1250 986846897 986846951
    0x306031b0b03040b06030a14011b050405060910050f040e01090f02070c0608190203010b030a0506180c0a0302160c050114040602060f0c120127020405010c02010e04020913 75
    0x165510030003001d1000400d5a4101c1e40142d000b036159115100044d107046560080103100e0b5072091000c000c410741c10b50010a0140b03007103488100d1602c49002c216000d101b18000c60303070712800a00041c002d6060140a5108100c52800c2080c0f8124008040c100c0356006a8850040c0183e403c00600102100d40294003100f04401d00640c00c12600b0750310389000d624180141c00c2009910300018004507940d070556144198030302411940c039611801051220b500895002c00403a080c0000309819042006665020107544000000291111039100a140d03120301c4022041640910450141c1012842a819a103205403074403441d02c3c2c94140050720044050140c100040000e000c200300441d00841ca581d80312020380202c030610380e12400494054060050340d880c80d0251074001141c180c0e4180c0d84240c0d050400c0442a9103246490100f0060f4031903030065a0005d4101c0d450321005500402509401c41001070002d4106000320000c12014000000d24a42c1c580e2621600740c078804448441c155a004 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 986849397 1250 986848147 986848193
    0x60c11100b1305070e150904090605180c030607031e0c02030c150c07030c08070f2a062a061b1407120809070e010e271f0e0d030603 58
    0x2600721406824445ca880c0c100d8000c91485100000c604001001c0b5114800000d0042241c2071060406038000d00c002c450390b5000e07440083d402c080c021400200c0407800320f8000d008141e141e40c2d0344d10440103056039804001c004690b00900000c51002801108d14015056000319240d000e41c1481600c1d002e0340c0c0e040080c0c407124800601c41c07600c50130320440d8189909030811250b4480da80c504403416100b18500174241d40100c2c18460108074252103200b424100c2c051010300350090042c035420010540388070f460081010028007034980701030508107009254011074150f1413041140c40e200c040c1c0c2e81081c015510304250744c1241d80510341041305c800011090405031414900d8641e9201c440306080d0801906004600c00040c0924604000600140c440c04903414801e5a40e5161402c0380d0601b40c51904006074250746401c0703030a600e100c2c1b40007120402001410804c034410b03600c1d0384a42c1701802c1c40c905c09890355602c44035508100440c050861040d600090300034518105400c25800a642c01c1404075 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 986850647 1250 986849397 986849401
    0x1e0604230a031203110706020d0b1813061a1005042105031e0705190209060103051e0903220f05030304060c03080c1216020106090b0607060c11100b1305 67
    0x40f54400a50188640703814001000320782d0120225690158a000801c020300001e428a244001381d049080c030440103175251000c0f111044100744105e01308441800035189032990180c003080f0940c02101c883d0300306100d4064644007039404689001042920180440d0001800304110359004280700103c40001141241140e403030361300c00e9264410341c94884940c1e84141030300b5030280a940300715100d8035031000840da042003900004001d0b030400e08405038802c0c829000011069402409128405c0491071b28201001742807a031034142c0b07504040c115000611050080108038101c89070071054010496003140d0358107140010300d2903600469003100b40280c106010070004036400c50b4a0040556060910704050f0352441442ea6013400784421502c01500c00e241484022009203c600c6141c0c0300e46d500034020070341c640c141c85040c2c408440d075254004608114807004174000c1c2e131281003062424540150251580e00c040c51522101040c0c0c100015a00c402900c150300c1e207500d01c0d0f4104402090300f84424 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 986851897 1250 986850647 986850653
    0x3030f05090604090e07081606090608090d0f0e100801180905100e01090206030c1e03130b060f0904050f061005150d0f02030a0e12030c03061e0604230a03 68
    0x5000e540f1410644640345da00225801c0c60a000d24000313001440c044840b40321007250a000c039080244103460102d400240702040051280300c26038410040d2074000d00319813040ea070080300c13202c5405000074100f1100446691980d580c0c10310900301c0d00c0a5680345000340d4109440c0701d84d90700300790702640726203840c4c04045000600085442c010f00d0f40318940c001007851003100c0b050b02400c45c5500096201c2c000100b00100a908a0007812640c00c3d40c11224000d502041080011032005880c0580708142e10418500011800d48001d070b401513025003000c0ea0804258041340d80005c0607038084400d85c00c208113494810f24200a01c070344c03100d11307441a891042d140c40c0100c0c542c00307074031103010100341c0e0001615001c2e14010340222281d129000401c65032841d1182d40400103160300d502700b00743e134028981e4450740303003a040080e40d0085400d002c0035450344c1c982d82c0c1041898a41482c0c40700780310201110303103185e5542e1070300a0401401541c0b03615080c007884c810400d4650070510b9040788500d186200c14008 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 986853147 1250 986851897 986851909
    0xc0d0308040305070506070302040e0a0605010509060d1d0a17040608070e0415180e0705090106080405070305070b09010908011404082101090606021501060c0605040215070b0103030f0509 82
    0x4550142000038081d111410201c41601c2074800162182c4600000d002d159540b43d40108116140328800740810307151205071200b905c206209003400a9000d0080000e82d18001004018861050800040080c00a60850980b91040038984000d8000200c04028003d04034005000400d071010028034060a004028200301c0f4003a04030010002c01900f07403015915940e100c000e8010302c01032820341407660b90300d1480d14644110269402d081c01e00d00140c000100014550058070002811035409030300b0950226080c0c40b006000ba20310303101d960310000c04150300f80086800b404400414640c2e8180300000076090b09020340c00a40185c4c9014201c0400c10804004c0641082d40043c9650303440403000f0800d407034001c0d44900405102540340000034150384c0b03940920100d5510f902030f2404031007072400702190b081c401d12490700031815285600000030400d070720031580144020001940c65510503c0c01d480360304286400c481605105006109040e003100401c002044d07145031451500e4007480200b42c03 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 986854397 1250 986853147 986853169
    0x703080a2006070e061306030c120509070303260a090501150b03040201030605060403110d05070504150e01090e0d141204200a050d0609210c06051005060412020a05061803010b030c 79
    0x10155240707c00024103100312040c0070030390092b02081c8858200400c1c41a01e900440c4070442c081100585080210030488516080c85090014528a80d0b41d0350f0b000e140c05441460001c0b0741c1c2d03550703c5420706076540091848001030b100f0403001540b207191520000d0200c454a801040c4035981c1480200b0018100341440d0005581c10340d01c490001d846458483e1802e41541c00083c3e010342850f042d8207003426100066012100c501e00c0010781643c2e1001c88401320b41c074075890303600302c2d803c420300b00035485004052040c031050042c2d0040b464015100c60300c0076442003c0d0303022181805c41000c041203408803502002d810081c21034840c3e802c42d16120000702c0140c42d40348010130301c91311405658240030a032214104405010f510162020504070030052000b11b4130300c0c0031a401840c3c080458100c003070601c0304006552010f4209880c2c5414401850844081410100da11240708600802d16881c2c0c80041c5c040d00407809424984200801c0c201400c1d1a100d000c0b0602a0f0301c40354040c04207580d40d5030652 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 986855647 1250 986854397 986854409
    0x90106150e0d02040608030c01051005030c06031f0b22150c0609020604090516030605060901030f0e100b150702090f0910020a120506030f0703080a2006070e0613 71
    0x9000d0222500810200300c100c00c0d01071350041c03822000203070b01d010100040011101c0719000304415528807064602e8600d690080c83e03056400100c100c0440d0902038000c0d41c002d100390385d2421410303140d12280004803126400c0600040400b18039802107094040120440f10b0503001c2901034a400c2803450764002050041b814100070030b4004410a00005511041b4001e402903c1d031581c55458a080c10041c00040c0c4401c21480341c1524042c46881c8240b141009842000f8441d80c0b501c60300303e0044018001c59250648400c0d0344a016041c450010001c4803840d10880e00d0119400d00d51408200c0000900e4160700710400041081da130050b07580a0180e54013201c1036000c0c418035100e194801e1301c1c1442007131050000703a1000900001c400e0300300b04400c0f81c070300c0c4604044c040c5a90710014540c65549103e03100c030956101c880103100240c40ea0000c2d000d104202d160003040816840203c0f07611400345540200c558100005002d15103510a000c840144019640a0300d00030301c85809011030741c0e25200728 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 986856897 1250 986855647 986855657
    0x5150106050a140d0e031306091a090907110d0f020111041202040911031902030c06040e040620040f0305011808040e060102013b01110405012006010f06030509010615 73
    0x130341d007203403001da021182c600c0c04c450403070340c81e0000300040c03000c04201c502604021444415001501d0b0140c080c6540765081185109810686201c003400100074000c0e110340d007480300d6002001c0f003150040003c000100456a62502c1c00640800c7c080d0840d140038000c2600741c1020042800503084011402c66003a6055500150030ba10742c0c1802100d10b600e1860a591501030041800f001c1000480c80f004800c0c001c50513101c103801d28004025040c460743c81140440d1903100002070216125912901111080d5004141c8601501c0701000c0340381c2c015040241c030b8031305508080c170a100d0b0900c940600c0328070303a4000c0107010400d600c0e03c0d4440c1c083c0b03100c0c00b510b6110101c0003815a074400e4102031506840f940c622400900c201c1c00801c1820b01280c06090881e88045201d02c0a043c14000c404952010304081403401e42004011680d1010110004228410501840c8000b210400640c4e00a142c507040d801080c5013440001415178102034500862a818204144541640c850b00f041c034400183c205 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 986858147 1250 986856897 986856907
    0x221100b09060c151501050a08010b0d15150806040c0c1407050307120210020c151b030a05070308091614010e030a0602090f15040302040207080c0a05150106050a14 72
    0x2807600d11500624000303900803880380c540100c0d13081000c00c0c02005010101603541e0302d01c8004441034003800348200000341800c0c004005240320600102144480f01901155140c0b2804032040e901c1c0c166441041d56401440900100d190701c4613401d40c21050848060001046045004007010702c0060054010313103903960700054540081012000400018007940c141075a01c10388004904446601a80a1018080584c8881e8400b20740542400f0004054140b541024602201140c01201d40c0c4c0840c000e2081700503440030020406000421442d5a4485e030390300c890700d0002e000c200083c181c85040e41c0b010082004521484244e10156180c030440f8081300c40d840700c0101c0f50020001c02d1290140202401c480038050103400500030300005458000c440078600040c03141401d8120b5540c0700c0f420041c8001d00040c40d082e001401e5490250b8001800d0229065005051a10141045401d0b0303009100399400340801c09070060040c40385080c0300b0300300010644007405440350650f15101d6120001a = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 986859397 1250 986858147 986858149
    0x6141e1e130c14150c280204060905090127030302210708010303080603070303020705040e031b0703170a050d0c1101060605040f0803090a03030c0609060e010221100b09 74
    0x2a600075203801000c2489802d40d504002c03625001c9880c0700c14028100d400b404800c076821002268242c2c6013540081883c680001d0711b00c803180120004544154036a00c02d1880035a4031405441d0140ca900040003072282011b0740217030300711810301c0b0b0012003486ca58801005030701d60031040c1061040e010304001d039035181368107040c0074084218400d000b03040a000050000850f800000c140c10307203105c0e40f03c040b8552a000105030742c07a0440d120040050303000c1c8034240700702c0c18030390800d86448128804907400c0c9018080c0e50480e01e91086201e4016034040c850400c00e2080300c80c0750703445031600003010600d0124280002801ca10404104504850300c03400c2c07010006100d0000c100c40141e8240003080780c0e5840d0b0400504035030251180c00b0040c00b00720004200c4c92004821200500d4004008460701d030301d50f5609480c50980136005071800e568039030300c3c3ca01240380c0d40150b074a0512104001030342c070080c29121500b4a40c100c0c2020f0040095001000303098100c04000c80143e4400d82e1b00c59840b0798100c8 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 986860647 1250 986859397 986859421
    0x30307050f0403120e01020120070f060b1215062403040f120c0b01050a05031f0b03011e0510181823070801051009021606141e1e 57
    0x5403004142e15813502030300c0c0100341e0050b405030815800740d00030b101a03014441119040340c804600074600325801c2041100245078140166851881070001080841c40d03080014030807000484101100e41020340c69400034040011084d6002108445001d0580002c0c950b560040c2d904090040c6001d80c00400b184c244100401010812031f0700000b40b51300d14240480c01451503081d82e104803100d5000100110766440c0c0f001094094800c06001483c0c261b0700b8018000f0044090301e80115680e954981c01c1c0030711f0b2000e005260048038040da071411180341c82d03d565412140020300c2e50782e510b00040403d10428030300c0010f05240099181b0701282d424443d0f01804090101440b0040028851000000e600d4008590240c0140f0992044e0341d84595240c424070b0a0f81c0d022140a500c40042c0030003803024102070303030180007044030780410800e2031042c41d03031024202c0b082c1120807038400c9800700030821003020035045e0b00e03c41401403500031041c1c01c00c0c40c1181c10044043c9004020510800c2c00180400102 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 986861897 1250 986860647 986860649
    0xf04050d1b0902091819090c12080301030309080a020a0b180910030614070f140d05042303070f0f0212031318050708060907021e0615010c05030307050f04 68
    0x7480a0505180d61851a40c000b503100419807030090200700d42a812207910403207400d00c1a0005500b001200d41c50311080b01c014500341c00c040301e1110010001042e01c00300c48481031702840c440c0300c885540c0e5055090140c504945a80401e07a80c2d401109403200507101c242e00c4004a83c40301c0c2b980c0342c50f10154444004400d4688004070340101e0044104000041c0a01284003102c0c0609010040c03441d401400c00c050707950440300400800d42410180c04818418036007a800d820302e12081d1800c103008032080c01c003a21410f940907242815030303050801c5100c8000b10f903900091072010040d071400785540e41e00f800d04125200d019103030384c01c0a5408020b40d01c1d10140104001441010f81c0e9035901c000c10091000b840398003a2406880d04c00180320540341642c4201ea005040f151140c030701c15600e260070020019001041c040440c0684000210030b50342c0411441d03002c0c03490b100a8400c0c0d1070f03d606035890482c81c05143c541000a0301c00020b0214401100300e9400103001d00d805559a101d6140401c0d0030310071 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 986863147 1250 986861897 986861933
    0x10060b190917030405090f07051b0327041401050d15150f0f060903110f0d050105010f1403070b040611070506030f1e0f01170f1608060702030f04050d 66
    0x2016500b0300300d401001c8014010b82d1811030f0310b040c80e615074140300301100004880920101d02d081041c40c0e039a40051015030f4080400d501101d25298030070b02d0380014040850100d0b00303181d40301c40c5611513038074044c041d50b04007021119003207855614140020702c00c078607a0600584203c20340780c100780798010241c1001c103800741a40840d96415541c1d94000207000305520a940382c10100401c0464007030300c280401d50440e50060394202c43c1d42c600004104002103c103010381d03400044643c02600041e401e00030329000308540705402e0591842c0c4202d00000c1c000080303005100ba003220740140300f00d800301000da07800ea038158980210301a0798484031600d0701d03030035410007988500c1c00b1007003011401e103104601d88105002c1100300d0140e003a82d26041050b420999240004517940e0006010041703000e4440307002c2c030a03480308071552603626603e01810329022000c00710340a18203c2003032001e0313541044850f0b0403001c1c80c802146005616641240940a2030195134401c0582d4030500d0180544030041c00301c0848 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 986864397 1250 986863147 986863169
    0xc0f05060f0c0304150503040b1b0927130308070c1109153c0a0603110c0319030e01090f031805090a1406010504150c06020d050a060906080703030c0f081204050a020310060b1909 78
    0xb84074055250002c0dd621040700050140c2c030000390094400c0703407030302143ea03408801040300400c1c0384104412400c0050003011841d0112401010ba5698040ba0100a1500b640c400c01c064034030100341c00040d186041503405ca0841101c852070240c4601120408840f0285800503c80d41e91100d035500c248196242d50210744000b084000c9001c8805203002105451354604015170b403a840c4245080c1c1d1007540d80940303015540011400402d020390100c1840d4a00310700b050000e241c0307900020307405220544412849580e9503081121a64401da2425006136090900314202454000d2810703031030321907100c81020001c66038030f0f505c1000000d4040c0c61004080030700a0086191000041000344080d01c203402d41e2a04000b000104188081500010b4942554800c0354194658841c1c0c00802119442191100420080040c007103840c0c2410700d0086100310064002020310740100b500d050980200c030190305242110405c24010a4000c84804820a9841e0481c1a1460345c2c15103490f00303640d001490380c0d0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 986865647 1250 986864397 986864401
    0xb0d230610291902070801020c0303060301050a0605030318010512010303110d030e07060305130b0403080a0e01020a05070f05010f11070c0f05060f0c0304150503040b1b0927 76
    0x880d0a0080054540311200e4500303403603540a81c42c000305458404400401c50400040c40d400700d08140c0030181401c1401200c1d04070769680d041608aa200000f1408150804020300007070f46400c0c024503420035a0240e091003902e05000020b6103074071440072000818200b0350403880040e4000c03810b44082c2003a6002101d41517940b400e020341071140b00c4903444214000d8031600c448590280c0300e054080070118008040d45410b00074203800404018010701800d41001406800107502c442d21140b1507886550b80c8082d40c2031050341d005c10342c2d110502c500f00c3c0340d0042c40001e0496030f00c102610750540e0400342c2c1404408440c01e18500400141c0840c11210303040a03014036054044000910465200300820f2101c250b031004014084100e81c058a940310008020301906081c400000d4200850320303105803450950341e0901601ea170703242c4007080d00100714007104100910080c8814160301070010394680143e0150318400c041e2512a0032501d500c1503100203001d9040080e41804c0421102c08000c10f03c07030324 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 986866897 1250 986865647 986865661
    0x3100b1c14010305010f090308060114090a06050a0f0903050a0b0c07051506030c0102060105030d0c29150f090106050c0a0b0c0c0c1e0d0312020a030b040c030b0d2306 73
    0x4070001d00081e01d940d801d100080066880b01d21520f103c0075010703a200c89079501c5050046548444025400035112011700865000d590b135820038030010109500d1361665030f40d0240014000c0040401e8040500081000c01c0000c034802140c0d035192950f1040c0103000c50b903202c103000e00c900c0c002c0746405041031003240f50010740c81c0d5000c2070f90360043c070b0110300729407241c4148401240e481809000d4150035401c1110b40c0b0501600648126101c18410f862008000880d0301440125601c00074081465036405414041408510740c40408124001d0b0b07807604410603440041038040c50180300c0d081c104040052528060282030001007400e56200042c44c0e80703410001c0c2e140049070008400c1c4000c0380071380500c605a0f40340200342c0303180340e030340403491060310307903c184100203074468003403003e4007402006200c0d54002e0b41d151008102928480e00c00003007520346c0100303102c1203070301003000402890704c0e20740702c0b0f486565a64401018168010154002d008200c1a45524607800c0c0e844004a4884e0005100d00 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 986868147 1250 986866897 986866931
    0xd0f180302070b040b0412050307050d230421050c03160e0a0b18040f0b070c05060a0528150605120c0f070f11060a1d0603100b1c 57
    0x1040c040c1d402c9800a5455440d412014815071240504080301004100041d07504403a14101244c0540b064a080c4115031303e44a08081d5080c00c4580080c083d40f09a42da00100503005000000843c81c4a03400c141c28800c807000a01c03c8045140c0d82028902004c10401034100b06a0211840107010b86441c00301d01c1010100b85c18681c001e2030300b40c2c0103900000b81600968811443c844100a208140c40d060754070840180042c080c10541e2000740104141e40440d012404c1c0034018449665510152001e5040190030100040e1900c2c08550a0a00348448504408007411a6101c80d200302100d50043c500848024036901c03062403c08000d2314000101c007500034000d49a0000d55403130f044043e90350551043e07003500c5039080d00c6034100307414484040802e091a090182e840c0c8101840150000ca88001491903003000304210002000300716416489642c00640c02403508041e200582581010a20112600418001c00869150200b000e100c100902d541c1300400c1e0300014020040e4a0b83c680502d10 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 986869397 1250 986868147 986868191
    0xf0c0213020a0518040b010806060a05090405010e0910090201020c101107120c09050915040f0c030b0601030b0d050303061207090603030f0e0603060d0212150a1b0f020303010b0d0f 79
    0x40c151240300e01c0003001d400d00380217201b144d0f841651054015504d01c1c042080030b420030154002005030510000040780c84612030a806400c2c0007a0070442d9113004041c2501c0e1000e416100c10308a4102020000143d0b0005a5284000e00450b520698a24134020880f240c0508a0182032503202d603000000d6556403802d00070b050319014039180603015840d03120001c1500c9003a116040c0d80d078804106041c2c502910100700380c08c14410b14220040c0b00079600ca4554a05480e081a0341900185041c80020f42e01481641004142038450a40c111202d40b40c071912400000c01d4140225181c4104520454046c4010b00103000301c0c810400060780c40381370060605803030052040108206048685052426009a07032045030004c10748001c0d44440c2d8203001480300b020084000d94480e401f0141c254560729544a40309090f00d84001604081d4a8441d5a00902e660000d1052103a40c80700d9800311913000c0100e0381500c0d40c0d40c0d401580c03040c04503544402440c3c0e204600500b1450445100400800207084030 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 986870503 1106 986869397 986869417
    0x1060306061d040c050409081b0d0e0f01080a050402030c100507020112060e04110109120317070503132d0b0a0507050406020c040e0703080f0a08090d0f0c0213020a05 73
    0x4100c3c0d00454065a0290400701092024a03403108102f841c1c100105c0f8209000c848107800a00007840c00380481d2446a02d400000c1c065440400901171802070103000224074443c2e1800081568002d44401c0b40003a21510240d01d80e800306010740c909480d40603007285200d403559500d5589440102c03002c035041c00460040058015182149401051f00a031581c0d00c0c0740418102c5001c0c5068000c218405100c0f0a00a120400e220095014030703190b400028110303030003007405c04031400312164451840d240c48014504410000701c08200da001c2e0f00203660500103900c80c3c072010341e03541c0034a02599005a22400e100141450a0380026049131443e00c2520540ca440c1d441c0c03200d590340041162600031200007611559990310241c25503000700e408000d0f10000c003134142c00402a000c030017182c008012451890100b99600c2840000c0018500b0204550b40e03110070344c0142c03060f04400d1320f41c = true := by decide +kernel

theorem cover : BRFrame.Cov 986690647 986870503 := by
  have h0 := BRFrame.cov_init 986690647
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986690647 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 986690647 ≤ n) (h2 : n < 986870503) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
