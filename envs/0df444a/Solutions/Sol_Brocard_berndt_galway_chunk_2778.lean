-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2778
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:43:04.873138+00:00
-- url     : https://prove2.me/submissions/6f69c800-7b0b-4f94-b5c5-ad994700fbc4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 499460431 ≤ n < 499640287 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 499461681 1250 499460431 499460441
    0x30f09010f0204080c12010501061704031205040b07081006080705220e04020a06030204080a0201030c0309050609011b030905030a0503060114040b070c061d0f0f0d051c0c030207030201051303020907080901 90
    0x100f01b4030703490400100001c0340c001580344408030503103400c0550b075500c51030144c07260302d055001e4400c0c89103800c0800080213440c075002801440e09490307002030351360380710000c80c0707101120700a00002034010000328001901400191007801c103580031917690600604d201d00400c0480703504c4103003004501700c20f00c0290f0914911b40400350030189800e614040c01d05058035625030924100904159489054000580c880ea001039141340d400b03410341d810b03414110a403034040e06d00f0f07100c0c0944d40d481c02000f0740340050280c8500044036034060b010f181064400c0c1e00c04d83c1c890700001d2805040c4680d01050506120342c810040028241015100362201305504100040300c01e245c01c40802d10207014406148002100e0007842e000c0e500710b0740d000b0001d0703800c40817804034449607140030f812081c0b0840101c100f0001060281d40b0055244030105580413110049451900c1d0960160142e089080180090f501c5100140b050031140000003c846550742e000c00c8007008100d40050025000c2c42c00d21032070020078050 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 499462931 1250 499461681 499461709
    0x40f0b3d050d052a09181020070318030c0603060b120402100e04020f04030506060a03080d020306010203090a090b0411180d05120a09030b1b030f09010f0204080c 71
    0x681541c1002a40c0301a50380c0c0f5410740c81e910740c01a00304d840816411142000041d403d02821103c0c0c141840c00fa4180119440c100c20103c0b03000746035038200c43d4021071250406090040c26494030003900400c08806a5110220075000c1003144a21214a00d80b0170007014011403296400b1524280341000c020221040b6400180320030703074100302d49480c081c8881e2015412640449400410015101050310810740c1021019041800411190742900b00000600708403401042941c90780c1c0d42e00c40c1040400b924070b010080c14020140320031b111940c2698041c580c00807043c01241c0c0741020303210001d458003503681e1003120415140c1031260300702d003854011710a4041c0880002401c015a1030034a0802aa100710202e0090031a00503032400e006003045190f2000f4000b541381e540d90241444020000c013424001580c041325080040b60901261011003100d10311840051403e40d1110341a014540c00c000e480c0c401c0564a4400c41b41c0030b99001d1000704000d14100c0d000340440304008052100c01d40c041c0d20 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 499464181 1250 499462931 499462939
    0x602060907060f05092b170f0708031b0f07030e0f010e1203120903040807060804110f01180f05010906170703021605060c03040b0a0203040f0b3d05 65
    0x800700b002e250800c00d0381c0840350035801c0290311030002201040c02e100c2609121903524101d001c0501c41d146100000c5903c41c0e0003806c413811141c211818030a214800e60002e00f0034003030f04218800100700c0c40c201840d00f1500b992440c2d03e40403040c00d101560782d004070007010351000d8005000400c05800c444105a0810207403140280252140b00207801c1d4811521043e000c0c01480c090408155010700484482802c0d0031202541418498201e560301c1e0820f00038071800d4800ca02d000b00700d4901840c1c051348200d50190015980040440038803070210400018941402907840c01c1c10380005803014904054031400c4c0b6101c3c0b001d80b802000400b0760200c1d42c40070041c802c55201c69000e090300c264000764882110704004d0303980c1001e250414034111980e04003031f2a84c0584d03000d00480c6107400004502860141544840b10785942c6044c00c12844251070007080005c54260002c00511640500ba902185c00301c001052801070b440d030405031962440c00382885868162480d030102103c410004040d241c152 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 499465431 1250 499464181 499464193
    0x5191407080a1505040c0203040b0f07060509071406090a08010e0a060c0f0203072a120b0703450c08061b0a1b1505150f0102030403110301060806040c06020609 70
    0x100c403003800f12040c0c0902c5020b6503c0e10316402e4814000c0045070010604001842d95960a00b03141409640200c48211400c50905010484041d000a4800181c0c1c0201c8440607000020800b0020f080d03010f40352168011014402c0007515440a1081f125030460f02c2010780711150311483e0181c1201d031801c44000a000c84180c464000603400819610042d501007041c4040c4900400400c07040c40001c0079140c0c454a10340e10104907440342e0095403ca0754451380c0b2148442d110004160140d44424003060012112442c0c03000c04541d40104000075480a18100c001c540754040a10b0716003620000150380090f009141007245040c100505580108050342c0c0807412001204500c55512030b6116000c2005203500b0004084102154100c43c03082d40100d0390328641203090b03c41005407104a5442d8400e1f4030b5440c604856043c2200b9013460f0600590280d0f107401c1c05c43c0e65501801d082041d5084c2c1540d81c0d01404560810104011400346019501e41d698040c03400c00d0003450800001d062a449030001 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 499466681 1250 499465431 499465451
    0x150905070e090a0e030a020d0809030324040f0213141801062615040b0d08030a09060f09060605150a020d08060310151d06030703030305191407080a 65
    0x41180c0c0c41d4040032250210180c8420340200013818081000030000e01002408001c0507800041e0381c10042505d03110710102d6611790a44503103901086591140360098161440281d500c0e20819410a0300010300000c0c0170f080f03114107142240c102c0300900501c048600c8081c03050004440c010060b0a0301210b400040500710a0403840f4000184600341c240220307486042c0022000c08000c00ca4041031003030740c1e0041c0c603010071003017124030070590340500403403034580b421441d4205081d462040035003251060340b454a9500e00c0380d0041c00704207001e80315981e803070758403034031640540c02000001e074050f0308045211428942042080ba18041d0050741c00356003042405030081d004034108041c3c000d5410040c000d6504c80d00807900744040ca9040a80da11320b4800360940321400d4455410945410f4404210240668000080351440c00d4887c076500d540070820810000b8401d0704256808143c003407600c03280201c42d0740240c080d04c011258090384440c0c048100200c103a84080105d078000100e102c144410850 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 499467931 1250 499466681 499466687
    0x603060d0b090715030501050406060e0121060305011d07210602030c0c0307060e0705061e030903040302060f09040f020306060a081503072705010612022b15090507 72
    0xe520040454202200040c0300920a0040344010688032519448020941800400900f02401501d200d1803070000302081d582d03c54280c41c0e0700c650060f114940c4400b0050209801c100090001d6094a40c0f0307204003000081007801b0381002209a60814070054540000050800c00c050304040c5c1c3d81d5141c00d240240610240486407540340e0010b84c016925110525108102d00c40c102e41c01c0302074400064240104001c661040c21307414007000c292544240c480082140f9803090072484000480d54804c20f00d50325450b1383c010742d000b140102c00c4915007030750780d808151103070003546045c1d145407800706840d2101d041a0142c0082460b038602c045295140010014029010711103100b420801100005003621500d44d181240e00c070002000c46554a6541c0d140800e10321240100c0907140513450303e013611002660040c281a03030095119804c207001ca9500d008000d4000007004a03109800a0900c0d82403402c880000501c015107070404504c46240c400300c0504e070041548034a937218035040801285941c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 499469181 1250 499467931 499467949
    0x1050c100b03031308030a0809340302150d062909010c0c0b0702180402220204030c0e04021e1011010f0f0504210507060504031b050714060306 63
    0x14012a000030a4980d00001c40d10f103020703c0701c0c4071001031110321002c20300d01d00020240c03600d294295606829940d03050000750709c510308281e83c03420304014801c003410f2981600700c000700200c5102102840351541ea4000810150000c0001e000c104000a07400704030b81f040e4080c5001400d40115620f58908019001da0320180711105042c0c55008081740b1b0001760380c03065501c00340312034000b05158141e9480d10340740314186e404054201d201c1c154406e007154000d01c240c2a05445960010850040d8a21010300000d070f5001005180c08425400c00c40400042c948a0140c4080d00350070b40b60380c0043c030309481406220319070a4024a5403154018004526070b032402101c0e626941545890800d0b1030281c040d03e03001d0442c0c0d460701d40e22a82001d80c0c61040c40080e0b400302d4400c90040d4281400c04c20903424405e2070103600c40480c00018000c0189801003901d50700f1031604284645088075114691214640b041d145060040324a034100000030001a5208000301c40381d02d0084848510f107040080004940d05 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 499470431 1250 499469181 499469203
    0x30f02071a0f28021e0706030b2101140f040b2413230f01060c2109030b160e040c020f03040e04020a0f05012f0f10050601050c 56
    0x180064a4140484200c0941e180a55032007840402c4941904840240040ca8107151006201c0c1c40f01c0c0080fa81c2003102148011440c04006d041000d050a200310003034455000c0c00b9170050300c51101d1541c43c1c0c1c1d642c180040009020300000681002000340550482400f034484910407038890142b2007c10a0740218903000000070310b242d00e0041c20741010400c68030110071034540c00611402241c0501c511900145030240280302000c000c4188481865561403041c0d80c22000c240c80d410040c001035001b0003110720200c0c002e000845480068007a03500d044410034250344001040d11204008025110040030b400c140c00c01e03400c0f0309070211418020860490000da180c8501d460f00c41000c1c030b0030b00a000d64201d5099210550b83c0d00c80d11800d40114205090310120b00400d642e44c4000382521403111440240d440507922101018100f00c414900c409030f40c0b10b0404244502c4200d0082031604101002c0540c803403602030003410842640110454034020007a80c10300c1030810403400c0020001c61001100 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 499471681 1250 499470431 499470479
    0x3210610111c02070905061009090b04090c150807090518060a0b1218120403081b06131103070302060f0a02160f140103201605060c0304030f0207 64
    0x100100364811464a1807a00c600100d0284541c0a804250342c013081280644080520503c61620f444042c88801550819010001105410140040201508a160a40d074014800b041d08001611140f040c2c40c0f180d0b220105401c03045901d1400c03103070401c01244e4000c83c0e40c10a211014a8031010912144403904818001c5c200100001d00e59582c10034a0000740042913545074440da44681c40c0460340380700f601c112480e0341220390901000e410000d01102200081c0034214240f0346113650380c0c3e210303401400728106200303545c920101e0009010400c85214005c002c9c581408074025003400c102c160154000540603402c880810300160b25680110350000301c92006455a503e400d01c0c049051130240b040c044044550620000f0b82110364900c1001034a00c01c43c9128080d904601c010340071100302000d40310021000d2080b00c0c2400b41440060184000004900300b5603d4007070355820b060000880d00048903d40c0401400241941f15580c1c0c40350890a000502030b090403e20402801030140913a404a = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 499472931 1250 499471681 499471697
    0xc0c041e0c0201140907170f07050114161b05090105181807080709050901150302010f020c032b02030f03040b0627011e0f170111030903210610 63
    0xc01c51007580140141d801054081020703041c030000003600e0b041c991041304401e50707413040c620b4840d51000c0b803200000c0c04444002c101492170720300151200341c8010f480d0071781400d0900045250618508109002071302c14a19030710801c18401270710020042036040300e80103a1008005003c0343d1902a40d8900e070800548011450303544040c269840c8802000790501c040c003502e00300060250000640c01e064426510b0103000568401e9030f0503003202c41051129100e038040107410009540a2200c0541c01d04d200e01c152100600a20301191400c40060310040400b0341c2003c0d0142032200001c883d08a0359458405035142108001840b815030001820103042150800081205a80c2e0386503208444d411401e406400842c0c8440600b070901024402c0c4030328014200c10211072100710200038003e90707100707003e40f20102c3d0503c40303035102c9560146041c0045650b03e41180d0020030758180034502c160161001180d6468000441006030011a0140d95059070044244070300c0e40d4070402142000d005500d00f41d11 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 499474181 1250 499472931 499472951
    0x10801090305091e030a11011b0b280e1b010f050403060f0b04050705090f011107060804050c120313150801030b0411120708060606030402210319050c0c041e 69
    0x208180440c40c41c95403600c51188000100000c40c0c1f50504500026251202d07203264040040a5a5000345001854600c140000624141e0100300607141208082c02a048203900c03000e034081110031608100380c071903200c0c0c600c0c91860b03681001c15101c0c1488c2840c1848403401da0203406081c0d0f01840c0001400c0700c4d1146805501085103601c04614030000030000d001504100c4009410740e48526805400348910940b540f6103940100c0380c000107550880001d206492411504540d1910094002c94050191211f411100d42d15420700c080f880703441501555030340782204140b6030510519840710f502d148014055001e2560020f0440b4112a00710030010314554640c90052007000443c00c80360b61120060113001da000c000094040c056403c04811200e481c1c44400800200d8002102c00962082107400680602e0b0b14030080c111000d070306401203d0902051114004084988a800d0b60000d140424203030100001003200c1c0d1003140c82900d08003c4a004501d60240528488003441c0001d40ca41c40421 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 499475431 1250 499474181 499474219
    0x50607230321070810030b0604020901030204080132062119030302040f08032701021c1206050405090a0209070e06030f01050111030f030105010c15091a01080109030509 74
    0x200b50025a0308080019421101c90204400040d20304100048413007000070f07030b803110b1800140150ba8001c10b0034503041c0e90380c01c1008007940c88032049d107040507000d000c0080c0c0843c00f40600200240501d82000750a1418003140040a810328030160345d03e540d182c01d111094540c264500038641e850200500000c50440c4240c0c9404140d107039940280c45103d00310804c1c540c2c1036024009564282d29200c100c01d0303950001c10b40c0d078001e0322a03c005075400f050000b82c540c0001030107501860790600581c1c0d0f80c6103c03299018004861001d0f82c90120341c0c183e8080d281e0420501c9068003400023118200400d013803085403190745121150009025004078030220b07888602800f1503030300da100c00400d05940e07883c0c08030381800f076031a0a00c02c0e240859400100400c0701d04010040e511001000e01c07940c3d045a20340801150103452a20702034940c2c01110818200502890155010640c01807001c0701c04c80d818030b4407038201c5c000e059014100c180d14004000300000e50005c1101d840d42021128001c040303010400030 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 499476681 1250 499475431 499475437
    0x50103140f060907030615091401021f0203090c030618011d0606010f180308070b01050d081204020d140a12050408100510170d0201141b220807050a0506072303 70
    0x31900c1040b05104101480c1e231080d2804180c0b807408543e504000710347c40059950f0386074442ca1140c0c0060713a500d45d496280c425405944d03c41203040440b4100c881810100e42170200c107862400c040b034007481020703030004800d005121142d049500700c80c40c0c0c0170031020440c1c0c4422000e4100c504000c18010042c0b00c0c01d11464021031400001c225850303415507203180c082c0180c0d01010707048949003145030000440345000d4120552050b0030410b403925091004e092210181c0e4000c10032a8404001000100460341540c0102000500e4200400300080d0034201180d146100f0010380b07042000c2004280080380d4082101c902c43c4900e0b22010803251540441c50011000941203180600000c40d2105129040010000a690140e8008120480c81000040411a000c42d00c80a401d4803111403104406c0303641000341102ca50407503600d00901c10190001d0080601a4003d5502da40000001d01c15882c1900001e40200b904a40e002c0c50401c20f0b030349c1e0309001208192d0b00141c42c9000f440d00125501d043c011 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 499477931 1250 499476681 499476689
    0x10c05010f0c0203041712071704180b120703021309030e03060a050f09030901050702010c06020702090a020c011a0d022103030c040e0601030b1e210106050103140f0609070306 77
    0x414000915a02c20082d0b698205100d4039031440c42c50300e00115200404250030700105610083c05140110a1326040c810001049400c102017900300000184801035001e086100c140c5640045116641a41080307940c40c101403500207035800c40c0d80e04200690b00d49803a52403d000c1200049000d09803404d098805141c03160343c0c160540940c504000300d2120a501907032141c0c2900b02c0340c10607925428000c0790740740510b88106001c2201003103914027560154030101d4501d403040700702600e8009540e012400740030054442e40842e58000c01e07010324200003030059210698170300da061001c09026400250740000c0c0034a019026600c01084101404035011246808200761400c403960307170500e0924000305034031074400c062143c000d000204003550b03c203002d100381da070100911500c6244003810110f00c42e50031000c400ea0740003150031142115140341e00d801c243c00694240c000a40d0310301e004005002c0c0c4280034460080740303409408001030440c8644130b0f9504100d06585400140d541d18a0a4009101c9504 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 499479181 1250 499477931 499477961
    0xf1a0306131e17091c3309030201060f08010c1b020f0607050f010b0f0303031501091203020105060a0b07050a140a140105100501020102040b041814070c0303060f050a05010c0501 78
    0x401100b900107480081000e034030107131a01d07002031526517802003585c0e000341001042d4070641c8000506039801e017882810307a405401a00e4065203100000002102c280d50011400740c1d46950042100120310b52034030000305614070091000580900000b09829040351010001204054034101035450f0034013081c10610000d4003007542e41855007440740c0d80301565800c48000c3e60800c9800c04050905441032610b1100140055007140c564900b10800b0103e0040c0c1e00381041204d440000ba5030b0081c205034955240683c0000910742400b1007801a10002600082c010442c10000c00e00040c07000211344d1081500301d807052000e01007601c0316034240000d6103400b5103100c030b01040101111b40194482c0d03008005482565030a44c0d039410069090f8002d03885841007032801801b0800c030304410410050150784410b20f00099145040f21445507800083d500000020480d078900c0301050340606c00d01e00541710005024035664a0400022000e86a0780120b90420075480b90040030058250000c0004900401c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 499480431 1250 499479181 499479203
    0x9060c080d020f0412061118280f0603050c03090a08070c0f030b24100309021206090d080c1806091306060203091005131e090f1a0306131e 61
    0xe07108004806101d05c1c02e940071483d0400d0945e248000300110741c004070346c141e000025910101e04010b060f0035208002caaa40d1a50701ca900d00070110b01c11110301070042c080180a03404d00380300c0000c3c01c40300c000b80980c0c4542000c005002090500080f80f0f83c200e5031014505688180743c0c900712010113079551200070040b98001d008803c01000c040300902c030302e4110100c8248024100300300d86442a00c0010300e6001451a000300d00e20358866001619014009000c7c641c1c000500e980d040d140090031141a002c0307400c05401116480e81c016103158000d108401554104503406440c0c2c051080b014045501c0b80c2c1d00080c40d030303201ea02d035001c4080c5601c040020030088a640c2e40006500caa0241000900c141c60784203031002054065003e03120301c600b00120031003074a800c02c0c402d0b203513030250140740035102c01c13014000042911b0280070f95005080c090b0300100740d01c103d101020301e11150b01e1404034460341140b000c0103001459840342080c1150408034441c5040c182001c00f000025903060043c182e1242c1ca = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 499481681 1250 499480431 499480439
    0xe0f2a03040501020d1b0e12010b030316060b0a08100203070309050f1f14060f01051c0e0607080108060604200d060f0504020301030803150402160f1209060c080d020f04 74
    0x40d405448120100d5000b4014506c0f100340c0c04040414500151010641143d0750301c400741010080a6031842403000001070400d0501c0c0046d1540d0030054003210724080c0c10a113102000b0b03041c080c0003c501c4050700c80108031800c01d48000d84134144024491130742e0343d01100013400c1c14820780000c24a19040015034441000019080d903c642485021212a680c00c0405031003c4200780b00c0c040700501c502000083d2501e81d0410040f0281d01000d0040c1048800c2c403da2080d41913060b550512030898103000100c0362803006400341030040082190050110f210010400d4100108500f42e0050302107400050600801010041146500c11400c1500c0c102152403200d4050592142c1c091310288107030101190f0b0340e001040180d1009000003808003c0038408203141c0f9401d806109402000200050309000748010b5246e40703041080310a8580c02c03c44401d403010b202c5200a60030303401c0c4461400861103130510201400c0702c040454010104000081c000941488aa05648240115822081c1d03181c0c4c0e2 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 499482931 1250 499481681 499481683
    0x307031703040507120803150f060703120f050c04080c041b030b0120161505071b0503030f07021003090302120c03040312110f060123030c030a05010203100e0f2a030405 74
    0x80760210b50000001007081238500c0d01000f40103030200002c180520384045940c088030052084554481203e880384801107a00180380038061282000301d2646841d149042c0d0700c00d1800d44000401d03030140b03141501020800c07040410490f1882c0c2181004180c05d031b04440102c0700d0701110a401b03003c0002c141c0b03c0c00340f01c0740086035100141d02061104840c5036260341320080314a9061000e0340c0480c00407c00440060350075401d4280011224203a21f203000c1c0d840000c242154002820b032a00a10300050600031450010b504801c2c10025240410140b040e0341d074041c0da64200c0c0710781d18005000108100c80385a008008076406981e00183d2607070090070514014026420304100806179000e0910050511640052140e04840c5000c11454000394902e200c81121004503400c0da0b058028500070b092603031000c000e0042e40d0b511403070005a607403601c100304e003900f0012500180000910740c01800603485010308032540004940c0c58a02110f02d180c032807403420401a00804101032800300403c01400340c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 499484181 1250 499482931 499482937
    0x1b03080921060910060512062e030b04020126040204020d0e1b150705070504090311010c0e010905030c030a0b071107030c0504140f070f020304120f050c03070317030405071208 77
    0x1302100d8248102030b1900c00b000b8455810795170102a60b030019000445000d201c505950708000d00c00c4401c80405140610541ca40d102c642080c3c3d142603000e1b05120031940d004035208804000b02041c0034003c611a82d0075155030b8070141000e4070441c1c0204a1100d010310341d0303100d22044100c24045414040055055047c003110307042d040c0c3d100302c083d8104000410303c408200c42c1f966602c80060030711203061130104401404c1d280c9043e003c21035000c1c020070b24540244240154000306444004034425198001000240650800da000c0d400c00d000742c1d003a030341700000e2212842d6032100d410040d03075843d400103c90204c1c05071125050380c80303004800810712030361000c03c40c240d602c06d503000c2c480203501c0040d21400000982d120700001c08042c0020340414880c0c200040c03c0300c0c10b032064920389691070030510354083c3c410301d050b034101200710f90754020440c04208105c4401e43c142c020341003042c0346071240144111810100c0c0c1c0301c44000000135081120611511019082c00808101c1c1c41c00385007080220b0b03030 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 499485431 1250 499484181 499484203
    0x1006080c310b04140603030d05070c080301080c040e0705060901051b19140c1503040204091401020a090f030b0403110106260c010905210309030d020a1b030809210609 73
    0x510740302c3c130120842d24000d0315a1003400040d000750328003a588802c075801090024221800c0211043c8a8000540b20b00000c0d0f000f40f000e5401402c5c051100b00401c012100b11603140d840980c0b00c40c50030403145d1505000e9686400007404c180e0344812034800c40e40035030f8181141c00f4103140140c1c5045030456180c19481c204140c040c0c03e51104101052031001c0d5180907408034564421641d1060444103c440c00003140e1251001d031001c1461a043c1e03640c042c032104580380100385a500071801c0200d00da4410300040060501c180f01c01038091075511101c41c0084040c001401300821115001000390382500028000c00c1410b200342c0d00000c040d09810308504000d1400f41043c010030b050f00c0307010740c8901400015244020701c800100524940c04443c21071521211032154002848001c1c500e5605000e18036400320160090f082500707503480c00754a501008410505404103100b000c0c00443d000304103486c040141600c443c10708140a1004178041401851542e800d0310810341040001800414600080 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 499486681 1250 499485431 499485439
    0xf070b0405070b030f010b0901050c0a0b16140d02031e010f0e010909030e060306190803031015052a0303180d091827080c1006080c310b 60
    0x20b640798032080c0d065100c25185c0548680c030a20050003440e5420005040041c014142140317085250710b4081c0c10028110402c3e00d81920310400c0088001412207030854900c3d003440c0c4021017091042c0411101d01600d4500c032000307603003c00040c072219840403548541c00e2084c428043c2560750f8540c0e808034940180261600411500000100c03024640192641c459160702c45482400c000024403415400051140d80c0c04566071403454184550810501c0c0034040e030f42c016543d17a2803c84180542e1054a90040544c0150960058507050f071020036508400f00b40071108020f80f1440c0a401040e038482c000229207800000280b000c0385100090800684019205403803140d490420250b407545550703c68104946000312500030310200b1644545000500300c101c107040005120741c48000d42007094070441e50f210001071400150181001000c000c00080c007010300929040100b05a1242c2e03294501c0d034002c881d064030a4400c4101e480007112070040440035803040042140551b406083c2c000031807801 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 499487931 1250 499486681 499486693
    0x9070f090b030a02040902040605060a17062407050319020d0e060a0c08032212020f070f06050a1110060302090105032107080d1103010305240114060f070b0405 70
    0x31401503000d2001a24002005054071000c0794080c4806000e445004a034002d80c0e40c0804201582e980010345440c001694400500c0c03071030140940401c2001030032903031060116050344140d81c511314004040c222000c03494682c075a0390368a00141303035024546680c41105624107001500b01e17400504a00ea40803103179a00251b200300c51082c8035480c811121040c00054907081e0315404208028000c50b00a10180e840f101d404010440222100c226a0383c104c80c00780084a00140290341044070080c07004006001d000220b02d480304100302401c06d07200318400d01c1000700d094210140500100c2501d0040201914640010550080c00400b181e00081344600b04520010621b8100011140c01c88a90a040003451145103401d00040d0f400c0400c0403101440d003005001d51a1380f0500505000c0d01ca03540c40d03d600c950540c50468102100c65080c9a0510005400024018240c50361141140c1a0403070141e00390f15654003023200d600c90305051140c442c40010348101000080c415651156020b1402e81c0c0d4 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 499489181 1250 499487931 499487939
    0xc0c1807080f010b04150c0606090c11010501080c0405060f040c0905240406050705160e0f220809030a08031003060b031b011805040e0703060b030a05100507050405030609070f 77
    0x2d0741c1d400a0280721110b61003407200b40400e0114240b00082401103041c440700c150010365600c0d0980e07140390442e0086540f25900000307400d4000d05106940311030342000b40410741c10189100d5a851100345a83d03c2a17843c0d101194550f11040d000c13080d0400082d101340103050358036001030010640c80c400c0501070303001140880c004001440c4009940100c122003a4501854060700b10f81640009a054405020b94150100400420000300f80240344600120741c40b4584426003503010030f001172549407450040725070514244c0e0005820f80e10250300a9525850b0380b00100400e181846c003170300042ca4103000105004800071000304441c101c030f2140500b031046203110014152074400000001041040d641c203492110360088407840c018682000440407d0356442c070000d815188001045545a00850402d0041c0101401600c60b41030054005104403003080d80c1d01c4e6940c03030103554001900c503516000309040d6032240c0100c4006100c014100c81482c100014143c1d1580803602ca06060307030400200c00a = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 499490431 1250 499489181 499489201
    0x303040609050f031314040e0319140a2304170606040b010e06041215020703110609070617090102070803090d08010614040303360f0f03020d080c0c180708 68
    0x464854001e940d6520079864008406116880b28220b1648546c0300c075001323000c0441c20006001d0440c0c06c81700e40c04280140c164080c0c038004060035918800c000030494107190640198034113180001603c25007c90307070001c00303031660280201d800080c485c40402070400b400c04c1d1300160306801540211410005190f0002c010341e5140d04640480780c1054040c002040030456419084412a0140c0c8008080c441c80c0c075401400c3f603100341c0080f401f0a800c2c242030783d5001c1041020302d6000c1c0d02c031401401111308003400034000c171101c408002b601e00c42d41400911109030139011340e0081c5030f100300901e8407130800030306180c0c03a07a55118403100080e40400001072468402c907042d01d004100317181c5c2c0740d180501b10b407001c4a62070504044080c029010f0200d00085940300c0f1840c00b003031805109100c1d0132600f0721342e00c0f00800c0d00301c2d400f500103d00c00c101c051026984118040c6079030b5500550081c0d940914003ea5824169101c224584c0304241c2e003c107071a010107800650f481000240e641e00403d50750300800d0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 499491681 1250 499490431 499490437
    0x105060301060f080702013c15091d0a0c15020c0114070201020a0f1202070803090a06030203060a09090b06041128020c0303070c050301052a0307110303040609050f03 73
    0x2000051420303510b0f052154014200250010254800440c41c00e50312180842901c0c05405154180f500800c00c10540f140b00c519810311220312480184040c0d00c0040d4070401c0fa80749070044105581ea640c0c2c6400360224080540c000d01858103041d54040512400c0c00004840e00e4411544a030213031041640361144081011888550142c56880c40040c1d40304d1040c400c0e81104004030705601c100d42000c008142e16840034121207116581e41ca0509130415402400c01141d50312414a59105010740c940c181c4e980a2440c3c00e45400b460016200e60340d040c00101c3c0359805500180c0141e1610510106001c2c88502c0544034031001d503828810076203400d0b0b0515951240d003208503005030039000c0c03000086140b9180d01c10422041c0c411103c0c0105c9000009056a1081c6401c488600444e5001c1045040078043d09a0124850070221003c0d682282e031000c8014204207003a0102740d0000019103000e010b00000030783e00b501c1c1c4c01126101e103045c3c43d004005000043c0300307a400e4403c0341e03001d6030303040400012 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 499492931 1250 499491681 499491689
    0x604181112100e0c0916030513060e010b01020d0201110702270103140712080d0f06260d05040608070f050403060c0c05011413020f03010908030f010303090b040b040501050915030a0906050105060301 87
    0x1448043c40d006c004d04900610003e40345410500c5840d14440101e40c42e8003d03c28500c603403800000c3c803d41c111700003900d0550800c0d801d50959051040c40d031940401101a140901e4040d60001000184000f0303d240e0b5501807440412600c04180c0040103020f02507040c82c3c4c05c1d5900750102c64559498580030040c2c00c180c00070040500b4010800f5600b140c4c029003014002e056035210110300c3d10348403a201402000e100080405003c82c050300f11845c084104101c0b041807155041c8585880d0a080d03001b00806d40050a160910450005030f003001ca01c2941101d0085401040401009249000080004919500546a540c28441c903248004007810440340a845840c6290240042a50030300406030001c1c0030495245d540e80e0780010201c0e6045008500c96802480f42003059810f502d0080d201c02c90a0304400344d245414407061042062510484041d079600b401c00079158405480054081208281040031200010051002401d800d0300521182407048805001603a05d41062082500091203 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 499494181 1250 499492931 499492951
    0x6030c061404270b1e0a0b0313140a050a0c1509210503091207051e0105030105041109041b030b010c0b0403050310030b070f080604181112100e0c09 65
    0x44050780709072142d440a030003003290343d001040c1d140d0501300081e42001c11000c00b168602078541070342101d01d8004201c2c0003601200215500b1410819040c80c5020f1160703900400c088101e9200d000100c03420070210b000d035079110040b15000319482c40c01400c19061407054108500d030130f41c8641c00950080c000101541c86240114019108240711b40460820210090301c02c0c0c0030811010a29864041c42480116090382c010181680380005201d92411130000c1d803c072000300000380c0c410b1070380d125080b2030444030102c0d008500b100c1800301604891144800861b0b00c0780c9090488602146021803080039000552000c10505008000546680e040b1800092814404000007400640030704091a0000b49180c0210707101622030381c4034019903c0c151b032a080460ba0015200382c04030782c0b1a00e002c0e0b00107030940e814802000b07644a400c41d14207034900000c1010200c5036a03a00251250074508c1c59a10440e412070350000e1007000c028000307050308080000c0a00450052462a081c0f07460068000c00400e8 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 499495431 1250 499494181 499494209
    0x10b01020c060a1101060b040806060109030b010905040218040b01060e010203090604150c0c0f0504050604111606021c0b1c0803070c02040204051f080f13020603091006030c061404 79
    0x303010882c85510100900301407203000003a03c00c0c04a402d01c43c5101408080f40960f58179418082080c0c03400a00611036030400041c4201840041d100352901e0381140c66002011030151603920001e8610f0140a540184583e100e8040005000b4003900b0b0504131030480e1220316550000500480c1c0301d1046240c45034101208002c20000805640c0d000343e0300111b6850705268000c1c0c26a00c0042c1441a41d02c12100d03071290603000c0c012803800340325450300300a00f1241001010980c2035540458020000c1d80240e01010080c24028892350b0340443d00c0c441c0d41c2e40c00304401c08404603a210300808001d5181806009451070181c201000411a80006504003840500b90754842c14211a060300c001412600240c082c400010140c0781c00744000044140b8501015031200240310041882000800d445040b0784c0341001d0000301c400a000900009805984855481d81c0d950342841c584a444124074503654500310b00002403040401d000d0301a11850707900c5040200801c5220340d900d01913801038030102c8000c4 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 499496681 1250 499495431 499495453
    0x11a010806030c030d18150903080c073b04030503012702030f0a0c020a080412140303010e040201170907120f060c0203130b070b040206030907080a05031b010b0102 72
    0xc022050780040010100c81c83c003103d44004c203040841c0c80125501040c0e1907a0b180400f0b45000041c003010b80450a12821040201c4000401c016110320011b00928000995110625414030180b00505403a0b6041d031039018148410042c0d201d000300f40354628454440d108642c2e240e1207444980140e4040c1d4415085909100168040c4604d401c0c15209210016855070810000c500140d032003000b100b603026440d0700d07000d0a01425910040140070440d04101400c0c000a20b03800c042e6000e9682c402d4403549012158035028040b1181c1d01800c40c0580b0011000080300014501100e01c114800e90328070345010b100003000810a50140c80040720ba4102c903009110041d508100c4011090141440141c1501c1036140c101c2103448001703400d00180c2000449000d00703d000079205000300300100c001803420b0040d407034444140d40f020380001d20400d000004100020010080c07480504162000d84105030a070707140840c0e07641c0c030004982511011901d846420481d06104401c890b80d81a00608086190 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 499497931 1250 499496681 499496687
    0xb0a0f0207230612131106070302070b0d0e07141503160806040b0402070302010902010e010918020f040305060f0619030b04030c081e0919241707031409011a01 70
    0x4102d401c0c1e03045101030001c0a150552003d00c80e00560300004040692400e40c10074049441e1110240c0e030040fa0100305000000c2e90020346503003140c0d15001865140c414000882020304084650f440992007140d0020501300001503805000c1602180c805026560402130444603010848105403100041c9070082c1c0c201c1c0c01400c045500150040001030a1180100080c04a8004000a80c01030703549031030f11000c6503000016080b50310800d0030008040c07031420300c0e1407580030510a0071140790b9402203034840013080040140e901550f440b4007903801d20b103400d20790171262020889083d4881c6584122503241480201030171000d894100900300d120ba80c0e1a1403d540480e80004211140a0108a007070498041001c6403122800c40f407805659a00c9130b001040b40300511401c09841c0b4010411007045803411922410b03040d610b40100402e80b003a60882d05a80d45243d2000f05119140090208403481c1e525a21131482030002101c0d001081e1126450b0720b00b21041d500d0320b445030240b00d51210b0001e42c0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 499499181 1250 499497931 499497989
    0x1c0612050d05090a031e0201030506031f090c080733120c1101020313050f1b1003020c030f0a272303030c0109051e0d051804060b0a0f0207 61
    0x30013900b844001e640e2980c03810015078030f0808030302d4880f40300441181103607410301900d500300d80210020481e201400c56001c0c2007201e0358684d07a070640c0c4d40d125507100300840144403c1c014285803041d41c0050755960510100c021800303d00180c07017900e0309091841001c03000059410000c0c0c0b99640105140102d0718800105005408001449480303181003011010034001144100c51035443c000b600c020a2801c3c07403901c140101c5d4a1120b070424281d1490910515a05000c100e034212446020080c0b68201a00288200084010140000200300810121050003001c1f00b004d503648022004030340400c1c6482141d03055108074458043c0c4078040008980d420041210514950b0071039400c4107100c400249035074030038105040c075030f5100c00e0303820140041446442c000c0031490504100c4070400d046920384900c0d1060700c50b821300c1004140c0303046865640701c0322900e029000d4070401489840715220060340c0c1000b03924100141400080e4001140b011441d202161000110700c82511203410224420341 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 499500431 1250 499499181 499499197
    0xc06011703040b04031e062d111602060f0309060f0105060c0d12060803040f09061509060804060f0c080a0c0302041a070204020c03040b0304060f05040203301c0612050d05 75
    0x314001407081b012607080d00c20701410000b042d04a051150203900a03498200b6010b0180098a1400032020a0304d0b01d004111200f541c508a01100d07040030610001d4018040c3c0740440c100b014001c0200b2444020014803c1d0103088100300b10b001c180c1e03a61081100718400e0362841d04040e0415182602503a0181c0070300e10b003400c0d01c1c1c50301240c0c0d507031214081499600700358003503003d00b142c00b042000070320600c0c0f2404c0041c0c00441603205100c0b1804001a001391414801c1104201810b80081c05004446d8845600004141010b00080038603150081808078281c1d401c10540b4a81051440a94040e05c212402c0300c06025400741803140500414015420440d03090343c11a4080118111a25003800100058009417081d039031241464104581240c1c020060100c00703d1030401400096980003c07050000c3c02c041c2c0740025103602501c1044075101011703079802c12441011503515242503405601151513504d500c4208900d9aa81c40d0100a01e549980098001e8010f802e050003103e101d00000c4c4400 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 499501681 1250 499500431 499500473
    0x30902060910092d3305030f100503190f05120d060503191e140c040510060f080c04050907050d0513031d030c060c06011703040b0403 59
    0x4107000e01007072010b655290041c0000d8803542003030203921513541072040c003403140b00c43d2811034003849070311a541c2c2c0c51180a038003060501c4a40d0303201e40040704c0900842d201d0401c18119401c01c60800013404580003a605003489202800c009080c24000341115021204010010003443d580d64000782c00c07201c0c68400c151003c001e40303c070807000300d44100030042140e0060450030f9035451a1000c0403080340d07000c4e001540300ea0880540c0c8515400c2400740c4204164000074510900c09650035440c800d40e01802004014100144140039010000705448060b20400d0320140080d9840c05100c9142809071302901c2c010880f43c1e40110b030709512800074140e1040545071810b241079215400542482c1d81100c07840000b03280040c8950007940035014480d001083c10121415801c2c265501514104141c80c1d060680e1510104080440d501040858900107001d4505c55030744442c805125180c0384240504071001001d131a041100c032100000312000c44134801c0d509030404d820359070b40301380048121544017070b1 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 499502931 1250 499501681 499501687
    0x40302010e1801151403090f0609070303020c0103020a050d0906020d0605062d0705151e060d0210030609090c05040b06120a2c0a0302010506030304180f0908030a09021f050a03090206 80
    0x5c801404002140070f0880c0000400181d2401c3c4041d91410354010007407504d6411064040001a0300041c00340d91482c02409c0150b29491030060071100d50140d484482146410700b0108014048a44e0080039014044d10080c03020f43e4032401401501d105182040c0c000580c0820700502c41c58030ac181c0c00f01d11110001c80c1c00e241400f1503e41602d80703452034059080003513280c3e060126119048a100d440c0510b0355500340700b00c0c80c2120010302002d10305807000e0b008084201c2510409413090380a4400340180000401500d540743c108150b00c403449001e518052450650900c440b4a4104c00344c4c0c5160f114808a100180d441c039040c2406413111000b4990b440050142030f24000c140603440007615100c1d007005000208450074001c1c00e640c1c018107070300d0181c1c10812003484800300b00303250020880b40030003002c680102e142031140002e000c0785c413001e42001004014810211001e80113550002e008481c00d43c84400941c1d00c0b144494502840d80700800e008104102d1201e00a8002e02c10550000b854182 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 499504181 1250 499502931 499502957
    0x807031805060c03280606033206010201020c030f03060f0405010e04080705121b01051018020304140111120703020906091201061511060108070501080c0d09080708040302010e180115 80
    0x1701103221410713008003140d1603c03420712010380d261140c45445c0c108483c00700380039400128011001110140c1007807a1500384030008020364001d404841200103100f080f01d80e01d040010b00302541e81c00a075a01845800030a80707524091900f402907505075401113076190241d440741c0d95010110760000004480900401d500a10080c044802a084001a6520f14010092401c1480b030864100925103143d402c0303500c0042c0f26a4600105030240352000200c0143e580e151403e1a03014000348026425496003054800d01c04881954040d0032460803c0c54050300507281c4003c20340c103038002e8803140da0308031a090101d0301451604a00d001d030000b400900001e40d264507001031a15000c805040d4602103280f80034005107a5101700a01401004140c029021080c149800208440300c0034140c187c0e05440450b9207204940d090740b05002031544001001d964150925106c160740d0410b01c0706a01040f0b496441c10110308140c03100491000310804001c195030f09148608010401903800f903410410302500100c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 499505431 1250 499504181 499504231
    0xa08090a0c090f0e0604211106010605040510050424050c101505011b06091a010306140108030a0e19120813080f0a02040c1b030807031805060c03 64
    0x24050b054801000c10b40c1201c80d000d0718290796100d600c07a411544100100004a9898000000404000760400d91340c0c1c2011401291908030710106d058182c054140005005c0b40c0100c01030084400079103c0c6204664510004c2d943c41c041c074406c08400000078000c5048484011110003199003282c18040d0901000003c4035140c01410418050036558918110701c080204c00480d6001300003d10b86142e0456002d00c2080c080030002c82c0080c9010b846800d6102004036005042c145070202258808036580d4a0070306c00c0c068490580402d9102c202c90380049101c84003c03046555192650300c55a0408100d402845455140002016000a071329400881e04450b66442c00c070740d0900941060780c503460903686000c980003050b884540150b100c2a1503240140001c03400e03d9030142c044900082c0c880508500382d48400b40e0a4511300e000c45800888001c1613000420f6901a10050380d04018031400c403540748040042c0054047c00b01d5200000203912007000b40d0055a100c0c24a502c0e400c1800396058040c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 499506681 1250 499505431 499505453
    0x806070201060315020702010509061e0a0509090f0126010608030d090b06010c0308010b0d06090c0309060507020c0a03060b030106030f0804061d06030415140a06030b010e0c0a08090a 80
    0x1910050b51a100100107124648441c5010108a40000c618151841d03001034950f10803101c14600601000c2032001d01014400e104c01d5448006034007440da50005050001e0003036010603282c521500e140d00c007003a04408a136041074142c44600032094509600c2c811a054040050503180d6241e64030ba11000c52074240600180c2501e10010340085040d19140c42d140201c000010034440c1000011082040800e50022440b41184c03484090350b43d41e6907c444004008e000ca82d04540c2d220707401c0203001c106081c0d00d5408241000c1c081d00040004c0d8448800803030300c80302841049a8004040e80007840400c2e02a0310000c4000e0004000054a5540380e8514041e03151041042d5692840810108541500407482e10404031184188142c20141200041c0450101800113403d515010080118410740340e0b001e4000307501c0640d400185480c207181ea400107000315000c01c0b1543c41c0803400000391001c5040466004500314000d080c106880c0d02e000301c1c3c180354001c08800b01c500c901402800450050202 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 499507931 1250 499506681 499506691
    0x510050a06121d0303070c0606031b0305210a052104030917070f14060d0f050a06170a06050606070c0306141303020a11130f0504060e1b06090a0806 65
    0x260600c0060b03491800c021103441c18860b01e103585a2640d8a00030316000700449a00c00400e00b40052401d60504004005220a0300004d160040e03000c41e8002c030689041031744080317071700c0340c411160800504400c1401d22001d01d10b031000098024008010480e026002038441d0f83c4401340010300c1401c014081306810360090700c1c01c0e07001c04e500080501151014444070302c04444210001d0000314540840300c8086000c5204402c00d0701111802104d903592500c0072036140054040c0c4c02c2c001d147c002c8480300004d080a440a16202c1d107400d20000e441404920003c90091658000e448003c0c09621901d0182c0401071150340d112030704008260009211407659806103020b43c4000849241c0083d462500c1c10021b490598024508103005000940c00580b00c0c845a5200c640389410841910104040f4111902031400301c9042c2120144580440d5103c0380c400e0780281014001e110300801da980e2241c4441401c12031400c8204075800080c1003d90082c0300c03000c0044c09070b10910ba51141040d05210302510 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 499509181 1250 499507931 499507937
    0x71e020321281107080a06050a0b030319020f0c06030402040b0406030f060b010f0813032f01050916031a130606080109021201050c1e0c0109050307060e070e01090510050a06 76
    0x41c01c442c2d40e403100010305102602c2d0010840b0b2420000860f40e07440075010011329103030310b842c0054110304540e0001101031390003a08890300d511030044018000480054030a00510450740951300c0c81030300261340240c40101400841c55516a0740a10000d40400e680c241d402548410001000a10158155910602030040015524020f6000401c640140308240040040d80c0050020a42310680751f07114050b070609003804610500306044800200607030b00c500790101185a40303004150190400d901c604105800c0e81c0010100d0000c03070b0140d150a00000d07003080f45454a440300c0100c0c03000341c0c2e82c010082c444841c003443c00a5036048151156a00300ba0307810307519030034070104500301301c0011020311220900030f10040c90083d8014005001325044c80d40800c0105000f41c81d55484441114881d4902000a0100c2110b074240240c0c0d0b039220070b0b4101c80e00c81c074180002681c3c1402081d00011b03540341108002180c0d1070000301c2d0015200c040c0c14540407900c050f00c009040d54401c0741603401000c0c151 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 499510431 1250 499509181 499509247
    0x90d0c030f170405012a15020d1b020c0607060603021c020f01030c081302062701110a05060402010e04021c06060e0d0b0f091e0102071e020321 63
    0x8a0b000011614440b200480341505210900c041d0b0f81101b890350711900f000155800c950030f50303403034801d080005600c090844400d01020305000c1a42d500184200302007000280951446250380d0706010350718804007001600034003407002052500200800b240340c01640049020781c1c594001640140002204000d1180a1005442141411003e8501d0b860302402c2c00c10424842140191001c0d000426212003a8140804c503403c556840003540e502140005081e100c01210002d0010014100c11505011440300940c050300004000742140c0c00687c400040d116640703403a4010b49001031203003030503981b0a8084c091211000da40c1d03003c0c1d040002080310085035940c0740000281c41d00c0c2c008402103015004801c4080c0215032130341d445542040f00d06180043c00e680d1052400c0c00d0031110b204030050300380000760b40344082a0540152620500604102d155011040904541c5074100c800c02905078011403c1040320a84c40103201040c00c000106007440c000c0010340005040b03089a408510140d840 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 499511681 1250 499510431 499510433
    0xe0d0306050d0b3904090e030328420509040b0601021906320f071404080718020304240605040509061608130305090d0c030f 55
    0x540200d00080c0400d0b2000d200885043c0c030380b07064680c001407081c44032020404041801d807134400c1480c0105110010000202c039480500140c265001b1300c128075407907040c80000030700d440c0044100c90003101c01c80240c10124400a840b66410700c0103080c3d50700000e5807904940b107440c0d504842000d04100c8090400c0f900509201c4a140000c28409011904c000109003441036441e02d0002a80041c3c00201201c82a6140702c0101c2c0f500914003030219031048100f000c5000c1000b02d81207200b80d6040d0016169000503460321049072400454070303402c507080303150300032980a0024915060300405113183c80d90109041665692a07036009602820340396010050400142c01d807000d01d0307041510b0320130382581f440c00e00ea06c80540040011820b0114151400c59081e1000500e0780003600521001d0410702080c40c00d0039506440d01411102d003002082d40c0401d0038001442100b03881c1c85880607009070080c400413910f0484441e00f201c60701d81c1d04811450f06060214031a03115220086218011a036082c1c906 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 499512931 1250 499511681 499511687
    0x50703080703050c160c03080412060506011403011e0e07090512120a08070c05060412030b040b03075f0906060f12150316050a0302060318010e0d 64
    0x100034281c0c02014503240a0101940c400310444d6186481d0424607045840c050803c00c4620607591b01c0200114800140007039001604903500f104180603410801c0a60707595001034480403110100141c1b8054200014002810004088803c00d00e2800f422030015031a91a42194000191422400b051503400104010303e003c0e00c0c0c4204084400c00078115084481c0703060f03c01d07802080c01141c28441284005400340c1c0c400c040003400d960b08a03084031600e00701810840315001c4100d0f44800000d04006281034281403038020605003d0380036000b01303042031800c0311400c0281c802010070f400c20064846011509402600384074007000f40c00840d00d04011580320441441d075140c01401d2082c16410300ca400c07055844610030355100704140d40346070f03540c060150102600d12600d1090744040003074509000300030204403102202e500c001d0301242c0485a0a00f4036843c901c502c3e00c034155000421041c10f00c0141007080145401c1002c4c0750941000040140e50b030340c25103008004008a139808600300e6019194 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 499514181 1250 499512931 499512947
    0x2090a08070b03280c050d050c090d0b0a0f05012303070b0d2a0f0806040b0607020d0201180312081503030a030c0e03120408060f010518091507050703 66
    0x10100040007410b10700503064801e07000040c86203200c0d1243d140000c2001c1054108000d8011601c1020025020b01690190468100c0307071101aa032450000000c01003180b10303044a090007002440740c90742030070766500d844501e44000c000c050306a4441071001403174001d500a8034080d08411103005030303800000012000e54038540d0329080c802e03070010f4800c200c4588420116900c0039003510020504600c00c013141c89544c0c400c2d09070075801503c403109031541e80c1c0c0c1c89a02c1c0d821240241d0340d450510740715401003200741e4100b0071180f907105904118420042c50903220200071140306042c402c4004035600350032800070400b0361040d2441d915600449403001e41c0080040e5006c80140031341d9246000d8407004c25900d005810050301415902c0c0e4003800d81d980200601600100010101c0700a000c141998805640062040007000c1c81190b003c00c0100302c0e10100e00c0d05850028011843c2a104c200e155218000b010701190309500965141024825285203094440c84194030382c1a520402d9290007040743c2 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 499515431 1250 499514181 499514189
    0x200301030203010e0c0d0f020105070218090105062209020a050301110c010c05030f040305030405120d020711030a050a03050d020f0403060b090601020d0522090501060e1c0b010306020705010b0d050102090a 90
    0x60044815603c050b42d901140540e030303d0b008082603180030250b10050742c09110345213020b54000d902e220b50102c070792105374a071807040c02c40300000c2c4103a07100d00b0f05100c62170402091006010107032030313500f003c010429403104004500081c60108030316175600200307084030892402408a0800021080d02c0a0f00034051500403441603d4080d1440c601821660081000a0001070801c400040810b050140030007020b0b5042c2101641956079440072807512000358001c40b000ca500365030b000900105807401107488141160010007604001000e41c1e0112001d52000743e20705003099007031100c11031074070000000c0e00286100b5100014211200020051511340007400a411903001c1e030074101c55140d0100551b03400d160428440309520701e00380e25255035200160402e00c0300614041c0000b50040c0d0210408004040540b410304d03004084195556a100404c000581000148001040001c0b070582c01800c0080c020000040c80b1402c990008281c19845403041d200c60b900803503000700c14034180400500034 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 499516681 1250 499515431 499515433
    0x80a030e0c0a061107060c050c0913021207050307061d01050901020f0304030609020f0906010903030302090102032203140d0e0f01090e1008010c030e120304030e030303100303200c090901200301030203010e 90
    0x12031f8295a6076685000c0c803c080c5010b080b030400410740c2090040d42c0c01c102c095004089050442c0150180f5036544054824140705e4030800c0d00004a2500401d10104c6460011900800400914006403007075805040140d0461058810981040c003060002d00301462007070398081008000b60042009641d10f12160318464040d41c0103005490380c0003410a03007265458180980c4400081c0c0050b4150300a455045c1825180d070201d0b0341b0580300f2049850250b034403400184a0209010102691395000c04200e80081342d100c0803090514074046511600c032a0381490000060b944541142048030019203400000c104450011f202c051801e011b9410154a41e01c0c0410244c100400701e1544c40c550410300940103a40000400c0500d0311031030203d4014003018044943c0d03402c0006068200300741c0ca10043d030001d00740c61140b004d031002020350004089442030041c81c000500e20300b0032008a50260001106640c1c455600068801c480d43c010381b8000e90283d019100d40c518010305007980c03205c8a0701066 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 499517931 1250 499516681 499516697
    0x3071709033a05130609080d05041203081f060e04060602010507020c0d02040b03070e0a0b010c03080f100806070c11060906030c07240621080a030e0c0a06110706 71
    0x224000d401d032000070203120111009440002901c20340e841c3c4aa5181000c076904c200070f02150007034020302c4281c00c9038079410444a9009070004225910f003c0c2e0700854030008408401800440e20450311030790030000801031420103418050031a00c3c0640740c1d90100d40401d1024801010f1441c042c8125401030040d40024485460304280080d00d40c40750080071445440540041c00a540741ca5201c0000c008000c3c01f110314a94448000680002c03080300c0f0600260b0428500700304951042442c490425495203e4200c0c540700d01510b1000d1800050040c1150103003001d00264641041051030f02622440d120304a40710124105840344c207010040840c0615000c000410b41601c8250489034412031a580aa480b602c852030a1038200c0020030001c0f1104a54002c240c401082943c402000c8510745080c52031645507003014000c40c0c0c40c0d9210041d0903450300348458803582c1d0294001c1107640640d201070314030009503500060440340103601728900045804c6100418110304000040190000c0d04010315 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 499519181 1250 499517931 499517983
    0x314190c0509060a06090510020f1b090a0b0a0b2d090117150402131a0913050403080a0203061903061407020a0c060f0c0f140616020601090b01020307170903 69
    0x107201d8681c41f410f400341044200c0240c0c043d00c280244090365a0600968403072822824800d900c114504020703d01c124807120116a982442d0b102d02c1d50364500140540c1d0446103004585030341c82c1c11266100c2403009100303d02c42c0703c80300c00e010000b95418045980d15100c1ca0807074001401040980e00701c0801a400d8410301c100020301c5024442c50322401c590241c0d444545803144186020303140d00034034030407070240e204055510100300504030094041d5080e02c400c4045105076401d940741036030302030086207070000032440b00034968004580c0000098101c0d4001c3c100c2c103134560b01000059109803180c03035903203156410307050307c003644035402a102d4402404d45029a488160013501588244414000c4000112401a010300b001034150341d04502d1740c880100d440d0519114480c0d940b80741280901904002801d000b4000c400003441344502d41c000c1c60561300701b000c804000c02c1000360b004d0641c03005211000014100000402e01c2020700e0290a8980ca220428075107845059001526882c0e64046040 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 499520431 1250 499519181 499519187
    0x60a050d02070c1a090f060f040b03070c170f0d0e071205031902070509010b030a0b060408030d0c020613060b0d05030a122f1309020a0c05150c040314190c0509060a06 73
    0xd0a1346d900b10303111a510390000024000c070740b0855010303907440302d404801c10510030740107000c18011a004504004031080320425000080c42442000d41050a083c81000c1d00b400595021400002c040001c4981d00b43d00d805030b62111070b43c8403408a500c0d03071002480d45100072650802d10072a2807a400209405400c001c0040c00c150014010025031030001310000f00e001d8100d4010481c0b554000c1c181c01ea4032900d03266903c1d2070794441110315007040d0814040f8403580340700003611032040141c24810501c00d0b40d42d684960250984503101c075400700d5640403c80100c0c02c18802400802c0198550526030245803081009940c02c0344294000490100c00c1800d40c09017401c0100743c100c0400002a648004102006c01040308581000c41c4051011800c03104240e00310030100400d600600072030703505405001028a5410003284c088140d040c040c0420000501401091a403009000c01500d10043c1810401036211920500c1a03030070010b011020001401c100d510103400520964802040904100000d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 499521681 1250 499520431 499520449
    0x303040212150106050909070816030c03020d060603140115080f090f06010b1c0207020a0515120a06060914010f0f09050a0807060e010c030c02060a050d02070c1a09 72
    0x1a0092507040000c840c01c080c18042100b80ca01108a4900d5a50b140e14006001d0703040003101e50702800408001c5100a8001c004c040e12802d01e2000360b60210394510412800303404418000c6040c140c003031000d0004030758140070305006030000703980006141070a1406a0340f041c1c0180e0045580c002d00c203a1894111b54070500040d07102882e6803a0b02655150050043d240980414941c922801650000300303592440f1170003403100c40c0158681c625540d4002c00c10401300d100e00d0100a51094181100304014203120b40c0c03102e0441c040d442c1103810a6807594038051135280c01c4a04014090f80c49805000f60754001c0700310b030040c104440c00c0f400701204040000c3d00720860070075003030306000c8000b2023091400d200e440380d1009000050103084055507902503840d41c1e41954080c10700825082075954103035520540c0c8040c61150103940c0c10603545075507003d00c07619034000078000c020800100310031807151010f8001840d006218250161400340b402c40c0580d8410505580014104010403002e00c003a990910700b = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 499522931 1250 499521681 499521683
    0x60a0b0f07170909070e04060503070f050d061107030216090903080f0a1d010f0507020d0206070f050405121b040e0d080c0d24060c1a060d0512090f09040203030304 72
    0x34603121250a01100006002d00003041303520400f280700700000181c3c84007010b0780d040c2c8155024000e2a483c0d108258454034a40100040740020100400c414508040000000c80c0100380000b000c030300c1408501c0c0180e005000580150b0300030f142c100862051721803071000402d01e0010403c401c3c3e003213030744c000c009000150840d1310500c407410206801104c140c0c441c0d99081c8480141d02881642920040d004e05503040e040d41100789800c00146126001244483d00441c3c00e50141085a9500d0001c0c0d88140c0f00020903000c0000901000c1001d4461559980018101d20010030780504420800b001840405038414002d03400c00748100c0d46a040083d401542100b5400e004445949020520f8100c6c055012295000c0d801e15018880800200c0840c04086020b40b81e48a030003519030000380c0712031200c4000101034031508000c141c500040802d850b500010002c0c6111200111916160316010001e40c448200c0703800000d5800451400a0402444c4002520315140518145e00042d03264000100 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 499524181 1250 499522931 499522943
    0x60c031302060a272405191701091e0b0f010e040906020d050103050d0509060304140a0606032003151b220608090102070b061203040914060a0b0f07 65
    0x1d8625840da00460001002030408410030390381410004d03000f4000c441e144500c04420000c24911a9a200c3c20002590445456265a441c1c020f004204102c0b140c00d40150208018140034100b580c20050b200c1180205000c0002140301020f0b013000686441c00500c00c2100c0300d03e40322155030341d40c88000a42070726100c2428100303001404040820060305166000034400ba01c0020720048010395507201905980c000d408446094141d801c09480307501c41c41c0a20f0351f0018041c0009000102d841948056a500c20703019074520001690300e50068500e07a0f00116404403c03420001440c165000300120701220840007004200095200e1040c915406400c04505586001a540920003002c048030304182030480105d110100c80c1d8901880d9400e980504400200880003107031001405000351030310b440d08101040c406449140c10070490400309960319485000601c80025681c003903205a812000002100040760b103015402c0100743d0305150001d2402200900c180310410303581d401600c0c01107a005e0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 499525431 1250 499524181 499524187
    0x30b10022409010e0304080d0f020d0e06031503341206050a021c0501150903080909150d0b0f0c0a081501030204030b01091a1f050d02160b0405060c03130206 69
    0xb80d014043c181c80b0041130784400580003a04060011b07482200845640e01d40440c2400704404903120050005040d00003084284d080555141010040d80c01100d00702c000440c94155201085c11710a0090340980001da0100b05440c1103003010303004c141c5c00031048241c10b40a40c10030a0300313144000995000b603c447d503110005a030100c2c55604a1308200701d240c0180c42d00030600850000a00300900408070711480d9038800c0d40d100c80c01903401c0d4040e40d5122811a0400504030700303208201c00010501c08261210340034544164842c81a040003072070007940049140d10300070b070700c10740d442c0806000c1c526180010084098955888007100307070040c121807c00d80095400000480c040c2c040c0340c002500c800c04150000500003060b50164114020885c110740d44461494100911220324a4100f048400340b401b8002c001c038400c000030540580720302e40060510180c0019200800e10b01201202e0780c40402e002c0c0700900030100a995445200c00c00303803502d503107012000c03000004c0c071050000380612004 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 499526681 1250 499525431 499525441
    0x100c0507080d1103040c0f0501081b070303061a0c120313020111150c121f050609061306020102030f0a0c1b05100f0507180e011e15030b100224 63
    0x41d03004020350f1003024142540b40d0074241001d171003081e0a0312508010115845000030954000c0c80c0181c892000d00d0b0b02c1c510703c40301da00020581944140c7c8110b003059540c0001080500d0381d50f8004aa040200b0f0800d9101e04900040c98600415401005034a000510410900d044002c8282400356428a8a01216406c00c0c0f00e040c540980e05003c40c86e056000c8081182c4101100d016014810707080d17900c0a140e03103513424104444a1420481c03090012074000c140005d0134204010403900002800540c5885066042c1d529150300d00d42010300141d400105124081d0005500c4581022050a00700201d0035040700141000d0703001000d071104980c90558250a1040502045d1090040180207004114a9400c120000c1c90111103005c0800c20ba4030480405d40d04100102c025152840e805940036400d1800d42411b040c2c1031041d005130011040c90100d2401c1900001c20602561a24041580014030040080004144400c14110350004842c1c10b01c4d0812040c941c4071000c10103030600000d482d8 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 499527931 1250 499526681 499526707
    0x11505243604111908090c0d0b01030308010b0f0d0c111507020f0703051009060b130b2106070f0e15070203070e10090213050a17100c050708 62
    0x86014000460844618011559100d2200d0201c0540e0101c42c01c0200e0411603403184654061503401004c510003442000c48003501460a2039044241c4404880c0066200800038240c0146003a003102c040e17040000400415410644150141c0381143d0740c035080c00002d00744000203004d4015520b00320380e00c80049105c2c85003d41401486030320544260303014071192144104d00104181e910f40f00520414480e0207109101007141c030140c039800070181201c40e2079070740418094117014038207848842d9542880d520b155140d40700481503208900c4080741e060750a104101c2a117594802c10409441b03000e0210068540c00306000c0c1d884201d609104901c030300c1d80d0001300c9000b100c441d40f40e900800441a0020100c1d03158002d8051240b00b10102c43c1ea007611a1648564a078042c0c4a40d10001041c5000703202052a07900540441c00001a2450342c150382ca0300064040941c40e4012605c090b28100d40d404500700a004413003061143c00c00c140001c2c404000300500364400c101000e40011004280c40040c40c130 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 499529181 1250 499527931 499527967
    0x1020c1003091e1a280207170903070303030e1221010f05010e09042102030d0b04060e010b0a0c061505041a0303040b1614010e0d0c0302060109020f1b01150524 70
    0x40d4405c004104108100c110000c0d8810b41c816150714001c2d100e6514120b0035803040303c03910003010300900082403641e41d05a01030401d0032128800d5005001d4207048521551010701000002c1c0440c40360f0005501009800c1c906040c0c00850840f40951824059643c105030381074003000d0169241d1007a0b0756241440c03c0030709110180c2941c0058614041c030543c40e4000050300d11080505820064200440208000c41e100ca2007112425117099004209a5060b44040e010344c031100c0c201100755039410782e103600461315021340104884640b40d40038000b40c20f00b841843c0f002011500c0b65000808a040000d41c1c9014501c40c030600040000352080d45410011480010741d5840956107180300c5035030050b280a40440c408041146c0708400703810595a02c9104548480d507015006002d0b581d080c105424040d51000304240203161041101400600c1046481c0007885900000050701480300c510108001403140d1043e449201e4580c1c0a00d150211400074180d08a40c020105a03500350488041a00c19 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 499530431 1250 499529181 499529221
    0xf020c150d02090d150f0b0901060c03020f03070b15010c03090b131205031b150105010302250b070809030a121a06040308070605010501050a0c030e01020c1003091e1a 73
    0x80e580000700800c00080b44460714101c00c17004018840301140e0204481213840050703195500002e818010000d0710301a00c545c0308110f000344181d80070900703950040c0e0b1440e0b0050701c080310b00131440c00c01c200d1450b040f9000c41c90004000d00c0c0624160410361002440740039140038250001e04002100c00e25030350890442402412112200c541101803400e1403512500004800902c0c2145511222110400400e4403211401a400d00320380a9080000440094008541d1900d603110144074a03420040a840511a518800c0c0300045291070108001404140081c050040e160b00500412030015000745200e20695512072000545a56008114402b110960750940d0001000180801400b03801c03001844c0d0507006804c240441d9a9981c011a001d208894503c1c001540c03245041c40041d2062203c80b001e01c0052049078244100a070000b08814040101800405d0b83c8000d9401000940521000710140d401c01d1501b00001e11307218070302c0d544c0008140d2030303205881c0400101203500005100201c0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 499531681 1250 499530431 499530439
    0x639010f1e1e0e030405031b060a0507030c08040e06030c0420070c03170a090f12060f0b090115030f060303090620030f2511042304060209010f020c150d0209 69
    0xc43c0c4401c15141d2281e1190091600034000c02103120500101825140c400110280800b840d203603c103141102c0603002044103d0401441907118004140140007600140002c0300f445d40c1355007001d03000c03d46040c15910710705000313900305a0400d101d11503205645003040d00030300c501907545000d85049615041190001492100140900022014080058020030401e0340b0785103822529551030044c552820300c40d018000c1c014050001c0060215004020381c4044a000841c07031052490001f81091002d03000314986c0d01c144030a0701882c0750f26000f40304511a01c044204401c50450318001e0640c880c5000c1d0f5400e0158400d030352603484050799001c020303c41240003907988800a01148040680c403d55182d0018058426444010401101000d010603030003200060444503880c10700029040600b40c0404418550358510451003801c4200762040c0d10441b40103a41c0c084d07050014007040041d40c501011580034903005003543d1280030f1403038588500d40614036104c15884500c407019209242440b600 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 499532931 1250 499531681 499531691
    0x101e090201121406101d1c020d030203090112020f03011e0e01030308010e010e101806050303070f2303030408090a030203150907080d020703020639010f1e1e 69
    0x10f4803802e0071181c00780d241259a2910524220000c6030440603041d0000110805031610604520f01000000c11401d0203d0320380c482030419400240e001600d210080d800358000013806440c0e587e01a210300d046001c102c5007141069540f03003003440280014094002040b030011650035010b8031141b0300c030004011641c000c0401d5a16481d00400e0400c0030303c6001c000b03a60010000c5000c1c407801040e0b500c03410031140c920040303518000d54011640d070104c26062102e03684400204951b102800201181801100e0010200713096180c000501c0050703010710130b051030f485400d804075500044120b981180c0c000321580c0e00c400201c0000f41c0c2516481c0d0000754948141ca00301c5641040c0088010310401071603054a40b129682d080c1103031901c00348010840182c104070421f01c014030780000074011314844090550320703454185004500e50020942c0300319140c0c2000315840b5141d08240542420440403803070501215503030703180d8800401038030300340e10841c07644545008142038441d000c05c9683c0c069211042c82 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 499534181 1250 499532931 499532951
    0x308040902070b15010807080c1c1b080f010b070c1d0601170601050706050a0e0d05040f050f0109030b070c06020307030606030e030a050a1206150809101e09020112 72
    0x2009600c99401100c2407040c441c00600403404d0794604181205042e113a6a1451307030b514404994844000744104180c0c002031184d400c401010030400031906404a800003000c480a9141441402c1d1504100c410000742c81c017000101c0c0900c1c2042030448a0018980e07071100001d10380010183c0003031300310140c156004646449550520302806008420a80700c10030031028031000c0c00000c0c14119030940c0411020080d400000e045940311503400801940300003002c691003000350381008034000c4140000f5901080900c000003000d2144801400704980040f2030200707040020305100710f64440600350100307030030008004502481030486465403000086650b8a040c0c0700c040c00600b094014100003906d44034090b1f02c400b44c004200c80300020640c481c40d0401c00e40030b4048807081c001580da9041c00c0e448000c0029000110540000808034039100c0a0080c6400f903901072030030b01e0340c0341c20f4003030b036410285540300c806040c00e80200c101a01400c0403a4071007280c00180d070f84c441050b4107004030f18540202d010f = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 499535431 1250 499534181 499534199
    0x80307031d030106030b060d0804171614100302070302010b04090b09070509010b030c0a1b050304031502090a090e070b0301091a090403120c1124011706010b090604030804 75
    0x461076907500e80a030740a01810706007260441d000003068603810b040890764601e4030038a0182d0700e6105600b1145001d403503004c0704210035050f070003084141e07211800d55407484680011410140c6680b56400d80002c030b8813000107030700109642c08075060560000702003040c11300c01e412040144102920074024070700c04d40352551400404548007021030143e401c000c02c1c5403a184003c0c038100c413030500b040e60454035080c121000c1036004001e1201404408044600703600c80540304189464051405107840ea8036504000c49035a250401c00501c2a10401c8407403095a02c1500e8007080c0d881440002950342c00c1001500e141a0160f01725480a0401100001c1c1040080d0407407150303020100404d401c4180950b060104052050324010007107040d4441c044078107200350303004003051142885e102c03030401001241d20307040140c4181103540260300960365540e05264014200e0041040a2074280048204104551143c1041c05220100720001400d83d00648e146405c0e035000d5038020304200d549a544254135 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 499536681 1250 499535431 499535447
    0x90e0a02030706031a0616140105060906041803080a0209040207050f0d03110403060e01020d050406050702070602070b07110a0308040b03040c0605041521050a0605010909020408070e0702010608030703 88
    0x4a110307102d0040007080300c61003401800b2600c00340d041e801c01c4922031181080f28a810100d20807501700202840710300410041c081200840000c240006040d0030a032042c80100d000c01001180a2401d103541c12000c03c89030240c900019415143c5084541c580300754036000b920403904180c0d4424008140901072000c08a6141d001c00301200882d07100040b0070000754156207000d0f0022040c400d05000800100d0940c3d04030700ea9a0440c0c4000520302500c0c41450002c4820549003a40c1da240c0d20410403c1480c3c041060002400303079030008150706403a006440c6258843c0c0c003c000c201242c80005246135441e03c1255102450b071244107203071141e899418154454004440946904048001c00903680340601704480542d00054000c0040007200c102c1070f184080400303110040d504c0c0321603074201ca4030790340e1040c00c0c0a608101e40100c0e001340b800e40014647c019a0708040c2c00c2501c1000304001030400010450121150b00c00c0841881d61100c1040c0c5c014419540001c00760b002c009520320805078003440d4 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 499537931 1250 499536681 499536683
    0x1020f060c0c10060b0304022206031a0a0b2107030804030311190f02011b020409110a081912180801060f06050c0601090f0e160e130314070201030204090e0a 69
    0x2281d142c0b854140d440f00654407503216114203081c003000410013608100300b092055000e020003801c421840d2449000448005500c00ea40c8468094200c80d040041c04402a8201407101020701c0246201c00c00130708542d031401001c1c15403003603c1003441c40e0700c41c0900c9200700558010100780e4403645c0c0c0c0c0c10003609825040b040d048141c010307594524851001c494000c480360f5001600c40301d454481d9030044d43c1084107400b9501007080c444401c1c1c40181e845005156260748102c0201c1d031400c94110900c041501260801480344d04180038080c2000c0d00c041b4844a0030390003500c0701d408a260748506a62109280035400103070703400c2d41c8000ca20030b074054100b0400c03110400b01c807800c1c450362200e0403100e60240f0340d1803909580141c80104864072050300666030070980480001050b8401004092900d1503000c0c6900100720001c6007001044d400103805076008200030099543d180362a07030f0040504141c40c1e00d0302070320140820b0b034030151392195040d1005045e04040401084100c01c1c3c0865988860400c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 499539181 1250 499537931 499537933
    0x10b1201050a180309030f0611160b01080136021203130509091c05040f0303020a05070603020c10020f0708070f02150f040504020f070c0f141017040201020f060c0c 72
    0x940703280342800381c0c80f12941d0a07800d83e451040d054115540c54031f42d4901c0c85401d07141c6907101d020314010030300e07500c00416038001004407400f0b0000c241e103132130001030700140d101d1a820303450200c1098103000205e400e0f220703800d061003003086409500c0758020403014500744060b411920110406c3e00450000000708000b07010901d03c03540c0580d45408003c03190b88100e6602403240c01180312038514040740b0031100e09a1000c1c3c1003150900761250310340d41c803020090f40140d005a002c1e513254801d119090012802400f8140350652030451501441e81c2d0344c0e0404034202d01110340c0000e18400c0500c40500340c940069000c91019501e50150911900f4100d002c0d1003a4400c071040d58000c40c40000003001c4501c90100c1021080c06c0a28090400009400020246c208103c082003500002410304801d90090000c500c0d486d00c009040004241082105034082ca008007a030b0901895607a80100001c00401100f00440039a65113034070040b810101708005500f0b561040381c0a000d0315141d07840182483c845428 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 499540431 1250 499539181 499539191
    0x10b040828020f031c02070611030403080a1d04051303031d072d0602010c12060515160605040b060f040501030b01060507020d2f0906030705040e010b1201050a 70
    0x920724804500240c0030341514080290100c40142403030304460a822500600395080c03602e1041c141d080c2a50b1000c3c1c0000180c00064080c40300d2070b0481c03004441c241c107800c000c505050550380e0300c4c0c0c214400d00c60302e4414441d030381c62000780f04c001d0001a41d54034400270703005005a044c55180741c00030240b94002103011900b0844c06603c90000005c0c40c00342071020a0041080d2441c1c03102510f040440f07010070b4031003110780c10394022601c00c880080030001c04d1542c1c0006040c04174888010005120340e5007403da03aa040c0703881001240e4980302141030000c032301c0b01c010f5902c104d42d40801040410304540209000c0c2400c0800c030503ca541440c451060388240c48404084c2142030422044441c2400001d200154400041c808140305601503c119480a0001c105003130aa03204c09003074148035001c580c03041440b0100700b0f48007034507007404c00c150390f00070785500055050100009859408a0103100c0c0a20368811800c0c10421f000d4101c1501080b02400b003c1c1d419070069004d502074032044950382c3c020b500700 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 499541681 1250 499540431 499540453
    0x20a050a0e06130509061c0c0e0f01030b0f07111f060b0408120a0e060304050d020d170601080417040603060504180201020a080705011b020a03090f060f05160803010b0408 75
    0x5108480700c19005401c40741d0020306000801c203020360b0140402ea00500310202c08251f20140300300c9050040d0044c10103411701440c0040390010302200078151481c065650f8010000580301046c62500040140b1a0415987d9441012107881526054a244034403615400c2c0d02041084030070407031003406210052007529100c2d000d640251003079120708180d5a100e04d0f0a0b0051248131805805107020501c0c2c5686440304003000581035030030545040d15907401011040b000ea9404103c060a01d405c9820000c80c11424a03c01225940f0010020b50500108000060801103901002c441050b079440d480f135180c585030200107004255601803907010f607117000403101412048101030000707154168020003198074255110034a50b000390104403455034075040342000805003080d03a820b184100c5d50051595480d17508000b0072400d036903403028800e420b5458041c09095408115640c5000301800d0550703403242e80c0c0800511208440d8800703420389070080004100c0c0c8030300c40300410468010320304460f80c1d8444 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 499542931 1250 499541681 499541689
    0x3061a060a0504140a24030e0109030507140c0a1409060d02150f161101030f050114061b0f0f0d020102040b0a080a020c06040803061e09060121020a050a0e 68
    0x24011070080821400e210400c40c1100e40701e040109120068000d115140da00e00b14041d02120310003d800304002c001c40f01c40c0c0b030306600d4401d010420701e11000074001540c40b0342f0702804a00c12000082d0640011180d4100b0400d001c221000c0f8040010b089440320998403502c080510640c200c01c00d1180c02d200021804a00c4c1a580344c040b42030f0014240550f140d03c0c4081d0203070a030b20452600424601c103100040c030780c10f03110310001d0307155018003110045151024001030480d2001d03560088034525120043c0541c80d609503180d2000c02042c1c501c1503850344860344910400e2105c080b0b0b5101441500e1501e2440880814190300c1143d070381c400c0358a40307081400280c1c244d00030340c05165408402403001d50030907032242d6003a54003c0b008001c014070304008041c40ea41400000c0b9002c2c0c500e80400801d006141c20080c0c80c014007c89800d40620040035100d000511000c00605031070304000c1e10341600c501416144001c41d954500b500811992540c61000141040d049044101c01250945d000421300b810 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 499544181 1250 499542931 499542937
    0x909100815090d110a0f06060f0b131a0f0c0c0a050a0602280501090f0b13030509121e0705100906020c040c180f0e06030c010206040b0603010b0a03061a06 68
    0x1c0c00b00081d08800034010000c980c40300b040e283c541e5840c42142140808140e03541a60391038640114804102941401a52003c0c1304d820340c071652101c9000c004100c440c1041081c05015900c0181c07083c920442c4161500c042c600620320b138019007410004c0c411407902400a8100403059040c4e40301e5025560b514100800a280c0c1c1c410b080c0580c11800c881c418448600f03055050b00103491203d141c5050301d64844500311035208804a40440d2030180c1002071141c010500c550140503c003561010100c40e40d8001c10038000c08110030700403040c100500b5401079090100203000d16200315010411a41c100040303640303003918402d85005038038403004030107514421134010040e80e00d2500101100c440c2002440300811502c41004100481c03541c29491803c140504034009221842c0074140b220300b80441030f200640060b000c41e10962081c8034141c2c55903008038006500a400142619040d926100030a01604c46c66100980c854505103011040280720f03400b0403440c40041c4066114041c5040030310400f44 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 499545431 1250 499544181 499544191
    0xb0a0f0e07030e0304030f2105031f0b0406180302091311010521070c0b07030c1d091801020723010c0c030801151202070f02090705070222020909100815 67
    0xa0400c2001b400814110040782c00564450806140350b140c0c0340d100d444590100c076215000140d0000203000c1d50000065a001000084130301c03c1d100c1700d14090001c00248100d100c0e41051040100900040b5044440071000554010384540c9030751404560600c95000110000c640203e0080c2c07100085511800c2600d100d1601592904881140c01c041003074545c0c4014030701d2003000090340003600002d240c80c07c0c0f18029a05910007243c07550b059031000d0030102c556084840c031406c120203c0001e80e9106000550018038001041d818900200d1045000e8814100e000e41142d02e5506000b05031400b400c01e588031803102030000c114042c550381c0c00321208100c0a0000d0001250040184140c210139032010080340d04500f8401040100d4100489c2039802c801d90075101c150f21000c00303009608010ba003165201f001d03440c2052801020307500042e00808403001496001c400c0e0380c1c0007110110154111400d442005005d021189006004140390444e00c0c00b409540b0f008040e40c024903c180048400d02603 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 499546681 1250 499545431 499545433
    0x30106200d0c02060c150907170706050703050708030c0d05010902070209062b0f0b1f12151805010e01140a0207030903080c0601030309050604050d11040b0a0f0e07030e 74
    0xc40c0307400c0ba2140c42c0312000b80d900c41c2081142e480c0420040007801080e40041c0a00350f142d1804495590400130700b07510100640620f44c4c0710005043d00850344100b52441428541c0e2107003164201150700c1e0140d110002d160740400010710803d81c28440c00741801004540302444542e0303d959110003607000748072000303400c00740620100da164580002c2c42c200d046038029421031041d007050103d400303c4985400076070301c00744035501c1081401010f03000c495002c0c040c1342c9009d010003c40c41d542032190740039108210145002d90b20b9881000390741414444a00758140b402c3c0300b074044410319000081580e42040780e44d58600081a0300320301d0103010f41c280600c10021a0a401d40d1615108406580035003411000c0200761807000c00011010f6010300a80c1c0b604000401c519030540c90007a055446980209100e0f68050004011070b1f40c4a10350088031661000580c1907602d07040b000300b070281054410950b8040011031000ca442590304a10030121000c5604c0010a034071154401d404841003c0ba0305622 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 499547931 1250 499546681 499546693
    0x10150905030319050c121b0706021b031e060603101104050111101407080f0c0301271a0310020315060309030706020d0c0201050709080d200a0803010620 67
    0x40c0d5800e003040e80e820101c4506010307103410005140b640c145120201500600540460404107643c0290000000281c10b0f10023002424180741e0080c2d6141c0064804e03c0340010011850b01c0907850500c207900c1581e502400c2100905a1030078002c0d01d0b0002110300e24002d10030101e82c250703096118020803100d2104110282e1400d03086c2001101d80000c104500e038070500c10b420f0b85c20351540041c802c1c00b89101542d02e401016041c1004020300344000a8201c1c480c50034504148503a00c1d10b02c40459046410a0300300e50f0b80c1e1000040d10782800501c80c141101c40d5031030a016241c080d510100710311840e0300c0c200e090340d085800d0584c3e001c080703000a4901100138114181030581c1c6003002001148c210f10001e0807a401c2c030700540da030f0206903481701c00408042034550807050000c0741c090081a401c043c442c200201c0181c180b03042e46030381d61000303002c3d8802c00c0581c10307600350782420400a01d40480b40810039540440b002c0c1c2408031b0158028803440340050161010084040c074095090f02ca22285c0d140a094 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 499549181 1250 499547931 499547947
    0xc08070c0f05060108030a080a020c1207020409050706210e0606040e10110405040c0201200a0c05240709180b1c0b040312090f120905030303101509050303 68
    0x20340608181000c58040d4400820840418010012180205403840c011691180e42400060201300c0142850788030600521944021040214040490300c81a4403819101c0226000081c040c0500100240203400344aa021070003a500074408100304d000c91140005541418038020100c90003020741c9846500040d010030703841e01e059005500c1852040d0304940302000904017040480d10f50000c0140110360008040019003410300031194402140e000030030400c003129541c042e46c445508a1301000e1800061907005440c01413001d0100181c2200452b080c00726801c0102d41240760303149020b8007100d604400a0000c0c1d200d10a600d040d107004000040c00402d1190003070001d031a21030400ca9000d0f14500026a04d80070748060400c005000c0d0311845c04130705050902814054411703210030382050802c5908404144a40317800c8200d564858a08903004d80c50031750480300f00c2500e400060741800300006215506201016810031381c0c8139802581046450001c040d0364007002442603039016042408082 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 499550431 1250 499549181 499549187
    0x20411180f12060a05071d01050702011404081504050709091703040302150a020a03050a11091c050604120e0303040513150302060406020a060f0e0613030521190c0807 73
    0x14045074018006080a014020440c1d0409004440780e10f142913962040000055101c059854004204400c010140100c1000206184203140020781405000e403001e80c11450260100c03001080e4000070342e07901e010041c1e03110780c035158151426600e030707c50b0350341c003044002d203074822510300c5a4030660b0440208000c1d01110a240c000400580942c05100c400525444602a0942c0715024404c001030f61500c070180040c0c201c40014092610300c0707107090312081c505060a01281c1d401c640450316501c43c142c403420444000414918000c115000e8141444100480345076074140c0c0819648130158904816024103551707000d0f5101d070550060701880e0051401c8003648c4484554003078075000449103a140d0300403c7c607a0780181d0142c801644442c00d80320520407a4843c200b822034500c1424880100d01a203040d07600c00010f05500301e0b5a0701e06803010201750180046078080d00c102104000d80102020101040c11404c03078581c1c03442d4000100d42c0ea40b08080348144910f031800c548031600d40d03881e000f10803 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 499551681 1250 499550431 499550449
    0x14010804030f030f09030f030f0b060f070c090216020a0e1902091f1206050a0f030b0702160b04260607080709050d0503090f0d0c03020d0204020f0a0c02041118 70
    0x710050503030351301840b21001014081c0c840b001c1d01946840c801302c150190000d0843d00f01c40d0741181c203640390400d0f9003c290b0b2600c0c210341814a4076a81d01e5120081400c003040c94100a521041c0e0192002500e18410400300121480d401e00889502800310768030103c000f11801c0071a00030b22202c1c080c000c3c0460342d4240b64042e040108010309020401d0f9030420600901c1030703c0c0c0b240b034008180d40d401c003030800d0182070103240090b100940383c01c201145458004400c7c50340f0f5000080c5075429503000a0050383c401c000364090400d00b01704840e0550343c2c0d5111950254050b001e11504a1034010412140b0442d0440380c440e050060b200501142d43c8020003117440060150007001008032240d070010b050b07a2441020300c50300f402400a940e403074203a8000c2003c12008052000e01403c0420104030103c1c07920260350080301c5d010b8031412106105840003074020b102e0003000400f80039010400104084d40984080b4406200382c40c10002c82eaa02c1c3c400c0c2801c0d015103642d0071950918014000b006d801c000c590 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 499552931 1250 499551681 499551707
    0x5030303092a09071205150d0209070201110409140a06031e050c15030108060f0c07030f03020f07030e040c0306080d0c05010e0109050d02060615120417030709030303061401080403 79
    0x5081201c0c5210000f0810602690004001030001020106180e0b040c41081d070080451852160000c202d84080340f0008820003020f803052600c0400551154000e41109100000d48140c0a82c0c4984074000390740208450381102d200202e0840014088030110721030082600d0b00034a000c0c0c24010109201410303003009400840b600d0241207200061a22803881001e2185c0d50650320640325810803185502c2c010008000405200031325060054030150b2404032000d45815141031b102100500c2e00950183c800c07240d444080d220002220018168041d000c1440142c04490601c11541040c1d0100d0585880d80100f6841c5e801006444500718007929070562503600ca0000494900010f025043c2185c584200036202c980002c8824200154148010381d03100b401101d180110044004000c4000c2c0203031305000c101d0b50307820400700c0c090107401400c03051f50546001c42a0350701d02c0c213030300300800e06143d6102c12000710381401d5000c42c0d0450200b1802d00180c02c1a5954903140e079481c3c0342242d00c07a110a01d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 499554181 1250 499552931 499552993
    0x601050d021306030b01180b060703080f07031b0305070e03011b030f0b0a030b0f13080403020111030c0709020a0f0201180f1b080d0f0f020a0b0a0204081905070503030309 75
    0x3c000001098481d62500030841c3c91184107900d21350780d4010040d55210000c00d440f60f80d04000341e10019400c5a05a038006001000520707050b52440ca040d80100200044400240c44007a82004810f9040c1c1000f4800e081c00d41d41e15551980141c140b50980344c1c1c00c0c3e40c0c1007142c0382030a03011007414403d074000c0c4420356182d04042039010440c0081155160345d0b4009075058883d010030002d606043c0d08600e500302041e40b80c41ca201c0d81c1c0589400a0794012800000c1c1045071501594800d0481001940e20100070042500c0c902956800c2c214000e40c0918141e401081c41005440c2c45039006102c0c84a1100b840700022002c12520751703407070007201030b4507500710340354400d14007082c98a0054401c00800342c0600e0b002004102c8200703e02030520254000c4010400c0040349403078100b80e601198032241b5031341c0a00441c60355100d0400d48400390040b90009102c0b0700c10618540c01520f401200003100502810039191410b0f20340c02403642340d11003180d92000952010454110340340303d01ca80e854411280c03071 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 499555431 1250 499554181 499554191
    0x909020c0313150801120c0b0306060705030a0e100903150f110a03060905010e06030d030c02030d240803190f03060b0f030f061905090c0d0501060504170601050d0213 73
    0x14081d2046050b25800280402d0702c645041541c040c2c000c01450301500296030341d0003411007140c1c0e90104040c9107010356010010302002080c800d0f00e5004c20b1b070303411642c00703c00d4980f14000c2c15001041c3c140c0c1e081d203443c85006c2d441d0800e4091401034000e0415281c02c180c0403940b01500200c2d01026000c0651150b00e0183d8910448a0041d140000727440007460a64000c1070092500a2181c1600c0c0182c204d122441114824002a03a80c0001c992106600034100403c0031000500c0076821801349102815002e41014010a10303206540224002c80180360007036003d094580e40714545c2c030b001e03002da90007000d0105060b45071900d01408450902c240c880c03502180f01515200b185142c1c0e00001c03d0150380213004020b110b803031141d06c20410350140040d01d034600b45180e0880080f541c00d0307181c420705001d01c9034240492024002c00e01241d101180c200400c0c042d950390707230000070002d030f20910841c0c507100c5000240c20074282c0086031150481da00100108a40c0443d5001c010100001e103820400070740d620 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 499556681 1250 499555431 499555447
    0x315090c051206211f0c09150e28081212090307080d060611010b06180d170c0f0309090412170c04090c0203190804050f1207030914010909020c03 64
    0x4c90144940301d0403d40074200d1800304c503000e2200e030070003020155449401d11490403121303a4400d490134102c0d501d0050380001149017510540305a5450107003541c00002e001250000204c0d11011140c040115140c5078444540d181000f549900074044403015580c0c0c01c01c0a20310010980811640041224041d24980003465039500019408040d5510505448800801082c0e4202004c4414018020024052000070000060152144002c101c0302c2161101400d00644c840400198140c1d40c0040800740c0c012084084881c260840103204400303114074041e004000030080f003560300c031101c050082046038a0f517544419801c1c04d41e060070f608120080c000441c4541c10a510305003d201120703982c903a00c034100800901503520501c4500700355802002500101200c109074043c000f0603130300d00341415449600e0410b042110301c82c3d0034000340c1b08400000f45541d540e0001082640c0c46529162086662001c82e08040240f00f0062030215260000820410350690000c10030102c0304400c1d2881c280ca8 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 499557931 1250 499556681 499556719
    0xf07030504120f0605131205160206070803100512060411060f072001020708150a0b18190b0108130503040512060a0e0609070315090b01060315090c051206 68
    0x241d4031040d11841ca80210303903c00e0001078420a134200618000401c1c60400b103403076801c0341d003024000c0c3d001001000500ba200c075426481d10707450703140c5d401806290703500c501e41000d0899800c155051040c41d10484400107440c508401d82c080d10030108405040107a07103a031035039104940300705032940d00402c04006140010404100402c40284580004c030010449801c041000400c01610107040d076000c02d174144170508002441d80e080c034440600c8049183e0f100140c2e14090325400c0e00390f50300803075445440c240f070140b0f40d5080c038490240404004c10701d8418104100645402e0709003075001c19101c0e0080396180b0700c0d90110556107070250003260319041c1c0d564007043d68030f9283c10105045801100610002c028907002c4c01c0710611401d0003d00c010708043c804107813114210b2200804540e00358600c112403144a810000d18107400030b08401d56580d66800240c00341400e0008080d080d4200c1202090001039845054240c111586c1ca607400e000030152002105800513114640c48441c401d141290803007 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 499559181 1250 499557931 499557959
    0x90303070f05010c020606040c1205040507030b07110606030c0108044d060a1b06110307030605040b031c0302070f05010e01021c0605060703140c07090209030d0903080f07030504 78
    0x301c42d4000090030418000c0080c00d240025015512480c2802901c0703500684c0007005454131458540300080e20b84aa190480c43c0140c2c0d940700800240d581e004000c581600700710301030171504241054480d10380d1003004145d110f0031140d5045011074040303000b09001c1421003451702c8032031290000a0006181c0c2121882c2c0c0300200303180c180c09802881c0d54003c07100d9000b9400346414401074507100c0c145a52000e010341070000140e00245c1740415050400180100d03a084030b00d0f200c40c1400c41c503503603080100c0c0c01000343c075a60090a0059007011480781440c00c000072003206d1001c1201da00401c06204d610114040d6001440076220400050764040c0811003c1c86090784030841ca40005a5a50701d600d11503045102c15104900d6240c60044e0400ca20f407141401c5450f442d0f494a4400c159501c0c0c00f000c0d2449010b480c02c4541c0b075105103c2c0101d0600e080e68020248240118111010343c0b090b14801c4494a246000c003c10700002407200b1240d2880e1540500116486400c1060030b00303889851840c6041 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 499560431 1250 499559181 499559183
    0x305030a0f0e010f11030c0706021606062405120f0c07050111030106031805150c0d1404031107061e03060812070b0709060507030e04110703020304030605060a1a090303070f 76
    0x2940d40c00744d0049680080c41030703c3e04101c1d01e4021074254038150450240b5406400704c0036001d1340e0001840d801c0108041841c0151076031004e0700b0004a510340c80721080504480310030b92000c01507680d060442902500664061506403022400203507111865003101000150055200f001d0512411002503028050a42c02c100e6020344035460f03615000380103060720030055200d040b404c81d9284020125002003070f043d5a850f6080c00740307415901c0b03c9010040e60b100d001a210400762901c0c504840d0740403145802401603010359250140d03095003000c1540c5580031849480c011408a10500c503088007a0a044111100707141070016000e030f038500d0f507141031040d840c04050301ea410000304001045494418590071402070b1030f1440070740b8203041c80075200e40706800c00038084c00400c400250095940d600020030745050940301545030100c030310700a541c83c0c0043c08110b60b03d60074400090690b040100303101e01100c00380104460010b0300000545002e038099400ca540501040000001103109089042609 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 499561681 1250 499560431 499560433
    0xd05060a050a1a012d0e09011d1f034805090603010f0501080a03030c050f030f0a0632090408070807030e09011701150e0a0f0605040c0e09010b030c070305030a0f0e 72
    0x4035a20720100200c0c28016000f90100110540012802c182035200e005d43c0008884c0564013001140320020150203010f1f8001331414002221582000c4420409030517032001310902001c99417500d0800880d60701d20b0201280c0b040001c03000800c83c603c0c0c134100494009a0190001500d08038034030f84081602d03026000040c0c0b030791081080d102090341c14800c0745802c09041c58120305042c0c40c0102c6c06034a100162808000080740c0c0042403030a100c40e441350700102030b49030b1100022080305120b00e592340e010301500354942811a000c4155070824600e06481780d5400244940341c21290303034510380ca5030410760051302003200641030b2031010344030b00300100c0c0600b441d144024284520b501c9003030300b518020018441c0f0b059070090100984006130204a40002d240000401c106030b0304401d20000306983d82c0f01d5a4420309060610b21859040300c0400310384182540c0c6059230340e0b2100141c8a4034030044c0c5964241c0c4004010140c0030034425809103030008010381c070106030303036101c0356110080d01d81c0000000c4c05 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 499562931 1250 499561681 499561697
    0x414010303080702060c030c09060d09110a0b1603032703021e030c060a021c110c010510030530030f090f0c0315040807020d05060a050a1a012d 63
    0x1070541100782d40340e000d00d5078401032805150004c200101804098000920098003140400f02d60380c40f078096420108010100304098400c50078a103180120300a403660050341e84402c00304003d41c180c41124109904414100404049654100c0c000e01e4502c0c240d14040082000c2d40c1d000d11075420189000c64040d80c010f20b0205c00c5601074020f94400d03408445805e600810401d8811030000c11800d9000700c07103074401a140c404025050500c3c1400c07050840e809450054001500000040030749080304d1040c000700020342e0b81c015440520045400064543d5100704040f00d1054000140d40340c640c00355068000071807842542c098019041641c9803016402c021042107950b050402180750310504010040c41442000710200341c50b0f0302c04546462021101030700240500001c0000c03a034400d940604107421b10550b600307049840303003025514407500c1810b240200f06105850b008888800d42c40801981200300341d040155074010f1105807050f5400032503183c144080700403a0307512004511540755110 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 499564181 1250 499562931 499562933
    0x70609080d0504033908030d1802011b171225050d0f0605060c1f06050612090a061a01031d1c09051504182f0904140103 53
    0x10604901e00402000c0200600003000407072a00c0c0400380946a01c03813100c842011440c8080000083d0607040c06102c0d06880100060550b0300200420641e4035412081051200314540c0400d40c4444c034001030700040c101c91189085c1a80b05a006a1441c40385684411050404500354901e030461400d0105c900c01d6982000b103d01c44000c000307800082106030309200c0c86243c0001a045004e10341c0c405017101d50ba055819801180741d07001d0f10180400a120a441d50345108650307a9031250203008040d0ba040e1079807a08000c0b40640124001e842e00144032a050020782003041e0440c1e070006110608c24440c558035440410168424a9101c00c440d05030700307585c28030010014068419440c0d90011a20340d0807100b500144d0b002c20b0800920701e03005d80810b0488074121048418002c03a07000b190f4020758980010705103144680c010f0007120140c40401c0510714580811408403031601c1c004049110442c1c144e041d14942c401e01d4150700e80703c40f002c2e143c1041001c2c0c0204d411541081c1000c2d91815101c0300500c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 499565431 1250 499564181 499564183
    0x6030c030e0109030504140103021e030601090905010e04030c1b0605041401020a080901111e060f06100f11010917030103030e03060c0a0f1b0309051e010c02060a05090307060908 78
    0x44401d540c4800900c03081c1a2070fa4018154803a9205402040c00c0c061400000750b031081e01207c03060000302d4481450f90f0300c40a1000780d540d205603034882c04030b5080b030000949203550713003c2c1c98102c40200e50400e80e00e95407518262285144084100c41c030f61948009000b5503c0701803e042e000e80030955071503842c2d80c1058002d5002c511560249419944030840140001d0701c07030012140c0c141401c0c60b16241040b8a074446c0b503d0f044010840014110f40002f0181c200280003030729078402c0f949480c00920a4a0b078005000301d911040c54107400041c07080154000d218040d403d00c06090221000019013071140343c503408031760b0000c1d100300c0411081c0000100103240e03115014010b102011400381c0140d04080c00d52000714818900c0480501007000515420f10b1701a08912100902060304c0504982607446e00a0103000381e4041d403441010710a80441c105001000c00e1407a0326010f848814407401240c00b001040c0c0c11280e1034070b00700b04007044514020b44040c451680104004e842ea0180181415051 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 499566681 1250 499565431 499565441
    0x81606091215150803030c0c060a05060d02011404170f01060b12040f0f140d030e030c071a070f0813050603060604050919020c0c09100303020606060c0c040606030c03 73
    0x25034003003981d60744038081000c0803220980d21859000c0001d8036100140210000482a403041885000200402040c202190300038441241e800c01510265a0780e4221403084507001d40e103171074000c2c0d0f40c1c1e00000015400b4860070b48502a141500303a041079a20f040c2070404802c60740840304660080162050a803109025680c00360108260060501040d6a4940d00c803213001040030b048100c20441d04000d100c0144038038554290001c01510100d000c0c510f0407581c542c1d02c5041d80d40064a8150004031107000403080d900402d15a201030480303d171901c050018480e030310480c0720303066800420524001400b1107141180c802d114911030f6454034076418526040004c56805140141810020000256545000c0b28243c4204540d05406a115a001141c00c071100310b0910101c2840000d504608010001e080510303420100c410300050360f101000d03185072841910000300540c1c0b042000c20300d5840c01c140503003d010410801c076100d02c4154000142502d00355400300c0046503071905114010340e0b16000d0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 499567931 1250 499566681 499566689
    0x60e030c011407140703120501260708030306130e190b150a1a070b0c030603010609020702060301211208060f010f0c0204020906090402030f07030b0307080601061808160609 76
    0x30180c0e850f121102034142070100e130100d500b50308006100c03420180243d05c089101c001e03401c02000f0b20f41c0c40344c515070740002c00503000c45980604001c034002e034114000759070425105400040d6040d0b0f00e6035010b0002400910701c6002c80d403510382d04032003150a03041040a20030480c03115400d8010a113824040000e242c00307844041c0482040411440d81d4860400c480d04a030342a241c840690003041cac00130461402204030040c800f0400070180000d0145001c0a10702038030045000f004002c3d911340b800c0c4101d02c80d9850082d080760040c80104601d0310700d40c40e0100201508414094518050394503000e180960000350008940341406100c4581485641d40c41542000e08100301464008a00034060341c4e0900c200a1041e0340001d02202180c4a80342600d032000320103001136459003402c03124031a0104045407442d0010b840c00300585050728001400408484046014124036404c4c0031084a81c00e800f03840da10b400d10307008003000400034020056808504400c070b000383c1c2e0007820010b00030462601940 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 499569181 1250 499567931 499567961
    0x350609100e06090c0c03070f021e0d02040b240a0201150b2b0e070302040b18010b0304110d060902030d050a020c040b0415032a120609050a060e030c01 66
    0x210601a070495814810380205044403d0b0030f4640d80d030021103101c0d12070101104181c0c04081600000c110526100c0c11629108a8100c40f500c1800c20400310904200c600503584170348140421009420160701c000e0300d149010b414171250441349403032508000c2a0100200124900140312602658280310b5140254400f02c0b400342105d251940790b603980d014041c7c0b80028071440b0700745001d00d20900404c000300d0001150b0103002100c0841009511906144016401030f801d2011a02003881c000402c0d6400c00341c3d04058811076402c0c030540c1794181e000180201e610700f0703400001c0c490a40e501211485491310842c0c0c0801c202d603051041c14102100714080b0801d000052000f802d0094002c03031807692140081d940002e0303207907080b00010044e0000425541c441c118040c8040148014076001607900300c0d09046540001307096030040711003987c0910070203178108021044030000543d2600000042401b038011285491031755207c070780c202d40c82040144001d034030006078108560380a014124421500c08 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 499570431 1250 499569181 499569211
    0x1080102030705180109051002071a0405031f1e09050f0a12030c120507030c08070219031b0210080105010f030209030c0f060d050115030e03030412350609 68
    0xc000500140a05000c00661140b204e500c55256481103941c0002440d005255804014044102940f1070840e40500c26980c1b2400821016083c446000ca80444c0c0c0081c0081c4600d062076503040300c541c0d42010442d80c0107621296448035911850070081c03680c440150b400262810b00d45011840c29049402524054100401c408007040414104189500580c01c022850103d6920100c0354000d0b45d99410035010324090070301200c0c644c554000002d0400b10344580c0361a40360030000741d9032503092102e84204000c800800b00c0c0002d1045d030050004402820386031000c0003156001074002c240c250000780020f08980010426582e000d80340741d02c1c4c0285800c0c01c6180c2600e800101e6122061000c0d910f004075150156000c55868400c00c035010f98003030400030005561201c01d6507420210941c0c08800107818040d12200392280841120b0166030f100b04041d101e000842000d0b11400c4000003420070401082c0d102280041b256040d4100b40c1000c07081543c0140342401c02c2060700d910240c40035132420780d2a = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 499571681 1250 499570431 499570441
    0x90507080402060307020120090f09040b04110a0801140702070b0c0c060304050c03032206210b0103020408070b04032102030a0804050304030614062b0602091503010b040e0108010203 80
    0x425401d400a030140c3e012592a13079121380580c0509003208204c03400f1200c0d04401d1b62004464806804007040440b01100480b0700340c000c02c1081c0c42c040c3c0f0003a00101100b004940000c403411503110301408042e10119200d035560500360f0131101d80d00e668503580e180c680204035030503a050100e80301812950303044ea406d100e04810f900f0740e20003810140d0b42c05004000042024014100540740c176622009046980d82d48510407004181c82e85400840001f00105501290081c05000170180e01302e003032600700d014940030038211030140241c104003e05040d4200030100300c48000348060780180106030b085664a624601e06503640107070440c1260026240b07804810032860b4044201c030148420b9203003902c047d4841e400d003541584919440103101c1d910380b0400411030041030b00790742e12410003280c04d81d012030220400081c0d40c42e070132040741c01040d03400d9070b20030006203459000e000c00100c05007030071411b04101003408107264401e1700070f41c10380000407d041281c2480d4003556405044001e009600b14281 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 499572931 1250 499571681 499571687
    0x60109080c060f120c071109060907080402010e0a0f08100c0c0210050c03040f03050c120d11071d061003060b03060906030a0c0905090c0a0e010510050c010908090a090507 75
    0x1121080a1260400103a485603400c00740084c0c2c0c140901844100002c1d06003625410420b601207902210400224905100245032001141e0b220301c4014048014076600d43c8800c50b21200001d004074188031070703980545032903252106c00c5130280100c22235400480b414040c100e032800c0c2586200054140c200036000b4602540544c481040b680c1c1a1100304a13588050410b686600841714145204e10020500080783c0f441c0f860036504480c012816500e000c652802031098005041c1400340142c0d01c0007220544161140c000c002d95191007501750341c1e00302d0316005150140c800000d5800c400c4403946052001918182480c880460382d103040c00c102c040e00e801181c0701c1d5400001d00702c5101e1080d1000040c1035807414410407840039800703030102d0321581d21020103100802081d54203010a1103450003680c3c5038100100c0e40400d40d0240b00e42010790783c1c40c2004001c0c901d8200c01e10103042000901c01c00c044102c0034003130341c0083c40c8502c08464540a5000901201000b50780c080d1010a0618007413003070041d0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 499574181 1250 499572931 499572943
    0x307090b0f0f03072c04053907050609060f070921020411030a1410050a03060509010603050d0903020915060a1d0303040e06100c03050a110a080d0c0806010908 70
    0x3840c2da2081d141d94520314259102c903e4029880c9003d068a082c070901d24000b44003038007075100d049030204003070f40b5180804001d0144c070608046010f02291a540720030b00c00d10007144940e10340c10a400c3d1138030045603101400c1c0542612181c0c00369000d00207024540801190307182d445200d61508040a519201982c1c803034000300300b8001500381010004600303544580d0400e0800d4003001042c4ca9480c00c0800004000f0200032140300019000700010801da81c1070070004104a4000414848401c1d095449174001407030042c000c12429075035950004002903040c8003410150145490303648480e4610b0042c0f0001e02d10050004508805105c0000384031303510502034401003042c9181007865001c90211428030907081d003c0c600e03494440410002010201007c41030321404068502c400c6d13100000e80203890043d80001d000300030030070921044400b6441070a017400001502002c450341520b094590841030383c0b1002044410946034450010303041d80104450750031000138038141c81c030341e40b40c00c07041031b103c0c9 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 499575431 1250 499574181 499574197
    0xf1107020306070e0a0f080606090709050a05090c16050303091501030317040c08061f0b09010807110a0602041508130506131b0605190c02090c28050307090b0f 70
    0x10f500e103880007940c40c1c1501d005e02400303a408110200c82d40315070711659034250480d0380a100c1d80d69100000c80103842948071104454010342040300c840c1c2000100215040020001803950806105d54140010030340e0b0a0701c020350080c0c015550f00d00741001280e00381005090318001c1c244031400100b00003944001ccc10600c80003490501480c44d2600e01d4401131002e6035512901c003501c5400140315141c1c603070309010040a604c01c60000c0950384c1d11891304149000e010f0100e4045622900000d411500445180302c40350203030380a4591028080d42e551080340c100344c112440d050180200d09505135000b046183d0000b84074190f80782450b9640da141c0d23580e22801801c1c8862045d04044560030491007501c5050b404001640c0450020344684004140350800d0600b40c0c0d4140b031030640b1409150141401000142e0045c01c003803926690050014465442924054a80d40a00c0c00c4181100848000802210016600c107942d0b403c11031001030009002d9007050841c01c00800042001c5c804403000c80c0d600c5 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 499576681 1250 499575431 499575437
    0x306040c020a020a090c020d081b0c101118030316060f0902030613020405160804170c010c2316330504060c09080a060509100207060f110702030607 65
    0xa011014003242800c07003540009404c4040c920010070407519030f0b0882e030300008280d400c0324481070210a003142c0c03103a0103841e43c0700c42140c880800704444011400514480301c0031000c13500c080c0000340700c2c04120380084907c10b086400c0810010000070301c109140644100c120019401d014000c4103400420030081c07401005103075600030b0144400b03919000f4081460700203003518454605030b48898100c00300c1c0360040388590700c1e01c0006480702c01003141c1552041b24640e2410040d03940c1c0c0d84e50520ba00f030256101403442a052004499208013401508400c05c0c0c682c1c0c40c0c6868130841c600316115034603401d0000317000c0c11090015454100a42008071074aa4100c8100100f081c2690303140e000224902c0000d40540040e0700c0c012403821040e400c0740e0b0245102d50410000c1540c607403000c40f80042203004400054004202000c00b25601380c100c1508003070264107580019100100e100c0c00ca0388540780c1191900d0316005c01007542c94083c0f0031541e0004291240a1414009600080d11680010500703018 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 499577931 1250 499576681 499576691
    0x4021c050a0e0109080705011401120b0709090204080d090b0a120b120d020a050f0c010801180b03010c030f0501080303040f15060e0a1a1203040b0d0e0d11071208030604 74
    0xd0702681e4000b03801010080000304241c500d039003407950880e802520140c0341913003802d0484503002c562203451340c1250007079032000c49040a155185419100082d2490701003145c0405d010605079140d10040c4018002e000c0103044190391a000980001c0c400c0e4007000c4808000e02800d59010b820814a1350501e9190f0310010300d45481c1000500c49510558002d81e09100703c012089501c0d4000541d003d846020b841182c051940340320500f5a00c114081c28580010079003c01000101c20300031810507101d0004070041245414140800c2c21691104540400a40c50303074240307a6081c86911429024000c400c01462640c0740980b1003103002c0441540080c580c5500007410b50100c2556403004020b001c04030031200b05404c0030103440c005400c20030110803140306a90040c621603e00182920b5000d1a100040c504080c601586610550404181040312540f074424402155405029480504400f9101c41c0300e405810a041031030318010703400803218402b4a660070000308507a101626070048080b100415 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 499579181 1250 499577931 499577941
    0x3011e020f04090c021f0606170c16030906090e09030f25030305040c0b3108060c040608070c2d0f110301050a02090a03060506010e030708060106090504021c05 70
    0x1440303208030303800f48140300d1610b0052039010f40e01003140d841050030703100d40c03000c0d82407504e0700601107031018401c0c1c40c00308000c0c0c410180c5144040112507400840307146070904205070184090000d102c00c000c200c0000380070180c140038003034000c60305102500c2440164006031808100840d903a108811826010b404045101d031146104c81500007840c500701032411070104a5031801401518040c0e0f4104d498500540d03010410340e1600d03003600d51400100500b400e01c420186000c401c400413410050105036140b103030201b4010740400445014000c2d0020032541d072440c0c800b00400300000942800c0c10081806011004200b001100c803c000b15030440681c040c036403030300c401d41c82d03c07204090051184840380c2c20101445490f00450200f1003040d0002e0105503036141214081f807003445540b961040c5906000d00c0450704a03070105500c61010304001c6c42814001001902e80b800941c0103481c240d01000041c03050540c44442c8000402090340c0c00d500303282c0c4100b00e11440002811658403040c0d91007000031 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 499580431 1250 499579181 499579207
    0x9030a0212130807080105040204060e07050706050907090c11010507020a020102030f030c040e19060501020d09030809040b0904050303150f0604090203090a1407090612050c09070210060609031103011e02 89
    0x180082c20f0000841d45116039804406028002c1254141d10482c5002c00019040704010701c0a0f101d040203588640c83c200580d512800145070207800880a80700b1b480020684900c03501c21115072400c6500c0310080c08219460b080c0c20344400600f91030840d08800d41140041c1d80001c19200c104481040e019201c0e9918012051107018503800824105c0c0c0010504c0034142014452400307c7d5644502030244c01c1d11000113a07951070b041809580000c88482c400c201060744200134100144000340045a02d82c41e4000040c41c07a001524241c0d9140c0000052049100a030420018030600907589002d40c7e65010300025924002d82c8158200750340c0010005008040510200300159400942410206103405681d90b468050380070707008c1c0003885c0800c04200d080c5411008408190321070001d00d02800d0352014048441c6002c0c0011f420f500c600b010240400a26004d944003134030780da03510309000f60b1071818014024007402c21178600991401e554501410030720b0300c002e504c0c0782d4043d0b00565a07240c02c540300 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 499581681 1250 499580431 499580467
    0xe04060801020406141c18031707080c1e0f0c060f010510081509010803130b09100c0302160b0d0b01030b1e0102070801020c0105090610080606190306180b09030a0212 73
    0x352500e4904240060801f140c904582d01a9000740d84c0c04e00c1040501c3c09413000c48105550b4200801c0b1008000f441c054142c80040041d9030417401c03440c1403544030030306e005200e070029207001d40c1d015404200c900c1c14107020015681d00415a1101103180e503d010003007541000e0240c441d204200310600001e42d19810031680d848c2500c40500003000c20769560030381075141d400099410000020713400740019071140d60790503034100f41c800401c0c02c0405540340c2c10580700d6142402c0d04400f540503040e04076040f581e44254020091000407070107941c840c9001481c40c12100700712a480e046c0362030100c050340580c0302e041c400c1e02c0218001c00010386604a01d40184d1500300309900c004a00d44c000590390345132280c19005103001d0580442200c0150f142c00703192902c820ad00b40a00c0403990f0154000400300c1c601700360582040300a41c00d809880c02c0d129122030341907500c0e04860b1242c245001d410701c0e0030402d03a4074021303520503444000b6505101600100a440c2c80e088040651503403c00700d00032510840d02080 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 499582931 1250 499581681 499581727
    0x1903030c0308040206091807030f060f0b031f0303030903030f02270a150903020f01020a05060403031109060a110618070b2227150b07060603050d0e0406080102040614 73
    0x1f1745100a0001900300600ca04448280009003404050204a8403030700a49040d80c14802046403110308107518006180c000400311481d044a90003450b036100e81070f1001e64013441c00303550007040000c0c142c1005020b40d01c1d00d2850790645403041145080d190041388401c0310745c032001007042e403105603a00c0000e03c120780c1e070b130700018000d018040341c0c4070300c5a8005034040110b03442641d084100b141c2c55001079869030342003079010702550880000140082c2c425485000d9141040028500701a0484042035050b0030803014800820898106000b4005082010f15801148a1091140e281e4044c07802511100603220341103803d0300101d043d40080c1c240c1024042e0302d01c48000000c200564a0745c2c580340d481d5048064607420700c103510350f50301488894002d10740c14429840d124240103103040c280808070350000c80d054504030b03030b590780200000340140992094103070a0307500d007842021440d040204664a0344e008060710782c4104020040345e900b0501c0360b0b0519600c482025124a406454081c1240a4481d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 499584181 1250 499582931 499582939
    0xa03140a020307090608061e0f0a1103010f21030909090302030d24060513270905071a0c0606040207030c0b07091d100e070203070c0807051903030c030804020609 71
    0x80e001c90703a9030285c4e01c00800c407072558007160110303100e00060380d02400100c41c0703424120b00120300068014010034805a08880c0091000800b0444014a01c80c150001c1e0850100405151002c001c0c00c02c200c405019241c400c64140c40303040c0e9050b500548040990300c81c080000d5103035110700c0c3c203050080c01550004d0080d40828401a10320700b00b2812b41032442c985005c00081000004200180f05001303036140c45080201507415141000c00e507a03080c420b10008a000e250304240c0445c1390011501640040e14480c000510010342044903d110090a07225151201c0c5024070500c81c10b1600050901d4210409a0380182d50300d0701d50a04946004030040b0207000c2502020900660300d9000d01c11404490a54841c004255a9107401c10702c400d00070f80b082d14141d5a4801c052190599461030140c1241d4540112481d01c400c80e0b40d03034040c034000e59012071710075000340c1d000b0801c50814041000a40350003516a0740e030981556006404000203803805001c0140310000a0115125482211a0098020 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 499585431 1250 499584181 499584193
    0xa0e270f030c0a0308010e2202060f13030c1d01181b020a050d03110901030f020d0f0501030b0702061611120c0a0c09020301060c020906030106091107051b0a03140a0203 74
    0x9071043d65845611030102c002400500000410100860800c1e0156900c001c80f4940300001924405624202000a980c40300c01000121815410310004010505202c1090607100f40703941445400c18565602c0f101c7c1c0801130507460a18180f44030011819030300c00d02000c0001d2800480281c0040141001c0300003241113001c1028202500000c610301041c0c0314030704079a09482c07014400c506640d1f0359002c500180c03c047c0007035451503000ba007001c100a4080c031401405c14032038a042e5025503103c0b0781220360140d6181e0044c81400991036045034080d24038001086a406c02d074401070380043e0804051000c1010125044001010621035900140c40443c116922626034882c000c0d141c45036034030101c40090390070100007502e500a0080d2812200b040c0c842001c202c10a400f44801c02000804a075459540d0760000304000b4050310619882140400329103445014914081c0d103400440382030b83c0703040c081c0c000750111180d030f42000c400103980d070054031030402c26002d5400b10f161501c201d800941c54040d10b = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 499586681 1250 499585431 499585447
    0x10080703140115060c0602091815090603030a2703060921020a020a06030b13090507210c06050a1e030b0a05040522020d05070608060a0e270f03 63
    0x6400003407225039140000c1146000200c0344441c0d44040e446036601052664200ca800f0400e9030380034001103800a0406040d11b4240b0100030b4406104841b101c0700a16103240c1c2281c2c9062406840d644204140c00461901c58801c80240000001c502c400701b480c140e0301000010820001645001194051810b2200d880c641ca00581580115222648000d45641c442c18030035200040d588070305500607044001c1c85d41404c07401ca000c1c100b51422180c01003d401e28034410814035114080009000718058a0040d062130140070310b850150101e000000c01c620904000710314180d502404460450a10039690007076042d0a54100e26030011002e00c50688034100d0080300d8041d044600115000c65212a0b906e46031070401003198010b0320100c81d040b0108104070b45088040d40c1040035140004e0440100210a5403201d2400d22550400d0300041c03d881c1c140019800c140306500003510340a814a0583c0c94031700d51000400c01240d0202040310320070498854260303018010000e801081c0340a4039a59001 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 499587931 1250 499586681 499586693
    0x90c120803011a0306090a02030603070305070f090b0613060e0d020d0c030b01060311160804030c06180f0803070209071206031110051201090e0c0405040605180102160b10080703 78
    0xc03d101d020a4000c544a40c51041800c04003202c0c8500401041c203042a1150b803030301002074000400d030300d0709031150b03a20200c086081008480c00415150100d191032606104030031007680d42c0e22100502540c020320a4221460803d80d8010584600e80ba240c5e51103035640000650718126920013035003118100d5003007030910070341038061720580380210b03045036581e44e9030f400480496826210100d1060003c0c800407402c0c000600502e24407900801c4c105007420303143e443d02c020341116644500d01140070380f221040c41d400940b60100c024500b0241c408841d6181134181c607124451500c0c02445030b000240020200f42c003414240ca80500301810803c10740b5200e1400182d0b040401900d1449400e1407505000940d01c03d80c202c076030102018900566907440c10213000090209660443c585004243c017503c1152201d10450b80300314014107000c140d03400c050550074228041c9104c400116401000103031540031440c10305441c902d5100c0c2074160070f551481000e45452046411649850045603000018851 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 499589181 1250 499587931 499587937
    0x2040f0b040b0d0c03023c0a20070302030f0d0905010c1707020d12031a0906030c01110304230f0103050103080313111302031e0402010c06020a05221406040b040306090c1208 76
    0x1020211134280407c10180315202070195000d0240050301d214142417507801400e440740c0c840748200c400c807480e4548070360010f03050000c101c94000056100701b61940c04240e0040740341c40140000c0c2040c909914039601c40ca5111455405800580203000401c00215200c0310f41c002e41442d008003040020800410000f000703408035601800e071034508182280140e2402d01600d80c0140001001400b040d24140010b5071140484030080030b450000344030000e0f02d19041041111180e0396009a2400c0000c0d40c0208049030a2400d03000f0f04240c5054014000a1078050442e41c000074404c1542a00d2049407420310f00c1d00030081050780d000482d000070b4032854103084d006103006049003140c0c1821002080207400c10710b003048070080c1c0051000088400402c0f1141d004100b0041b00e1b141c401d00e0000580806a400e04107041e089900010702d07001000409180982d400980b00c040310401d1820b03140c41c0c0030105501460002174001d55560178003004000c00400004004c0c00030700c1c004c000042031402c000203590 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 499590431 1250 499589181 499589257
    0x316030e010201061406030f04140102040e010f090c1205090f010603080d05130b132d0201030507050a0509040b0102030c0d050c060105010306051011011e02040f0b040b0d0c0302 78
    0x1d803d014001c51700c00c9030404540d10780000035200900310b45c0c0c0c0310694028500064402d6600000a00b06101c04043c01c1c00100080d01202c00d0b2340c15039500d00300c104894880241d110a00c1146420846040345074050300f04a6004003110021400340c4601c0034844c2082c9040607484007a61070100008100482c50001e407050002030b00d020411a81c4498411400c42064035005141132145000620000410540b210469019007140100002c03607000480700c0c0344060701d038802801500c0403040c1c05c660349405816403240c01d40c68906e05002d02e9a50140c41c6000f100243c6110b0340c0c503002d00d01c3e1581d02c00c00542c0c4100120760101c8080d011102e0024040d0b03031140d00046640d014220010441c1d50281c0583d80031100080c040b81140c200c102c1040310101040d03080944295281c0d0b500c2608010403521140e0a501103007401a50740d490b044200d4144101d50348604040380007800200803903501e28041d03610044040d01c01060b1108071182c128020310610346804803c0c0c940d1035500c110302c0d100500c20107441d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 499591681 1250 499590431 499590433
    0x3030d022205040b0604061b12020114180c01053403090b040f0b13051e1c0308010501080a06051011010c0c2001020f030a0c03090b0a0804060c020316030e0102 70
    0x890780319020302040c1d0344005002c45c2c000c1d004000800c030007031141c3c000400c3e11541c11a11400c0302c940350388001c00783c4554645000181c3d100d00729081900252020981c101e0280060b81b00d1032980940d1460300d5051011185051020210314240f00090b814a078101c61051641311203d074041d4000c04050403007452100780e001611a1501007040d500703403021201900d5002c142003207418500b003a030407105d50120038981000000c1d00c0c0005426141c60902d842d4021784d2807a01c4d014440d440051118070303401451441c6200e80c41c82d9510020a030000c00d80b50540e4400c0c60684003990701c06009501400c803a80c0302e00e8000420605205a03641d02c036810000a0b5000c1d002480b211540c05001c41e1803202d0440e01500a04400160310701241c5100e00f036000c00c80f0180140c0703a03500c070140c01003810358000141500c0407070201040c041c100350340603000307101802030910030a0402020420041c00000018401003800740e55903001500b031802001a6803c280c4103038000b0501c1312a40c60300900078a241e00405000d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 499592931 1250 499591681 499591747
    0x507080c1c0503010b04090506240d0e070b0f0304020a0e04030c0c1d0c0d11030c1801021c0302030a0b03061801050a0b0607060908041e2306090f03030d02 68
    0x80c1c644076404403412102c00780c003041c1c105428074080000a00000d051558004a580c10f080f0301ea010f80e2900000000d420280180c030360080c044205c041d5044841310340c101d600450070030322884200809440001071002d1034640c40b0707516480841c4c4045525001701c22020104400c100030980e20a1a1102c01407003080391603681070341e501505603081c5091481c551507000440000356011410b001400085100d8000403c0c065416a07c101c082d40c015504181202c200090140c101c1d4401e14055103800d0080c402403000e0080ca2043c80c0b840c02c500120b00c03080580000103d0602d000796041074503022001003d4402d607041040b0075151418800c1c010159030b5080c4000180361903401c0c41013011200006c1e101c0d0b480c02046590b02c0c001084030410031a150802800082281c01251040800b01c1c20342c582174052840c1005181143c0d0680040200448648010307400b010303450b84070940c0c2007004140d55500040c20a600040c0c11070082c0001041e0721480811000002200e00d00040a103501800081c08 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 499594181 1250 499592931 499592983
    0x3030c1023060904170d0906110406050406030e010207060c0809010608070b07080f130314121c050a060302121005060604080706080702160605180a0305120a0507080c 73
    0x110a210003122403080316188002036a00d007005100240d00c144504d0014041201c0380800c9000c0da08481c01b40356060744e40d0704440e81040480d01c2000e000180c050510703401c2ca840d2410060452040703000c4d040405072640324030303426541c0940598041590241c801c1c001d04408000041103c007044a80900719030030100001034882e0b01280001c1914000c070200c9107041103a440c0c3c001c0e15440250f03055011541080004800500c49038018069071090070b00700c140800a01c0914542104010960310380d0030200070312801858617012007010462040c001203059910b00280701c00600300e680c4042d4100e00c0707200200b103103210b011902d4112140354076010045510341c0014000540100d0043c5280b65200100c248070442c095000306500038590300c11035003030014400d03c0c24603a05069108801043c004940c40003c4d140304181021b0340d035815603960807681c0c9151242170303032107000e00081f05510100054402e0b0030b9201d40c0803a404581c125680b40d58a1003107000543da0340c0e50fa40b0700214a01d000900c104 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 499595431 1250 499594181 499594211
    0x110414090607050a0203130f031401050c0301030f050109061109130b0f0906150409020d061415130e040b011706190c0516030e0406050409020d170903030c10 69
    0x103400303049200020882940c03000d40030b031030360f9021200d0402540f00900c1004011030000344404040c250096000484910354a06000d40d5502904020384c0d90741401c003000b04a8041005980c1107980080845044c0201400c0031801403441680283c4064202031507041079001600081042510a40d210000383c41201c00b024100e5203020141c603400710366000320340e40c80e203010114550410320090031035088944691364040c169100c0e50010820076000704024000101ca807103000c0051460400d544001c000885c005510b400f80c0103910310241c1e00115000000b601a2501100641070500e0700c0105400c07d41421489003a0912074202c003114844034a2000b0300300420840c0c025881240ea0b14070401070207220401400185004204002040c007444400c80c8200d0000c00d44540a602c43e446102c02480910003550a107410260095081403280c50060b110380491400ca6a0000c082c1400d1996281d41d4034100d1243c1404551f0500c40401c01030a03600c0082040200b1030703000d58003003003041c5081641d0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 499596681 1250 499595431 499595471
    0x907141206101b0b1b0403030e030c0d1e0303020904020a09050901090207020a0320061606140618060f0301090507060e0906090106080901090c060c050f340902071104 73
    0x1d035000d02c00c041104000601c03a0044c10340005102c488030400c04020105007289811036401500002d40c0c04e0269502418107014250405609544020307401102d611201402e1141c00d8484900b00392104032201854800d031706442d10000014015035485a944a0007004210349002e80d9120303202017000001c803803055100312443e071507003d040030606c0d601e56115039650180b5004524a42005295603558a6984c02c005001c006102c882d0400d00034010308001c1c0441c4c010b0710040d05ca41000e4418000c1381e580b146009004194010018100382e582c0074045a01d0031203003044550590b0a01c0c00328410450302195880507241b86988011450b24054100078040c4400da0710503402c00e40000050107440c3c0300307011482d8800640310010038940a5603951440c0307214030b6400800010f03042081720003000310a00824001d840d40da402800003044c25800f003540d21f01d422500d0300100194640802501020100b003500800c8403030001c64449030242020328240c00400e004510551a01000a102103a01801 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 499597931 1250 499596681 499596707
    0x1f08030a09050d0804050315090c09010e0604020d0e0a060608060a020a09090e0c13020405100305040c050d29060f0103140a02130509040507080f0318090714120610 72
    0x501e144103450a800c3c0301c0000303aa918160b962040c10000851962010042c885c10000f00382e90300304841c070742041410705180701228118410300c14000100310341c10341ea10825030010021140140d032001e603078220302c008010803184520503020f0740c2c10760020320016610034408c0302c11010940d141c503660000548100c0c841d800110b400300380b810342e00b03100c02889644503540c800c0081c4120f80c0740c0c502c1840043ca5030341e020b09009403000c1e0002828071290404500507609106181014000f50409940300302021005000704da000e425070b1003640e42401140590f43c402005950f000c8184c0070500d034001d8401c020111002030040881c160980040e5100e4801c60001d07102000c46543d02d520f4000004000c0c0d072020302104035148607090f02003070781d41d5160604d030300841c41800140715a80c503140d0658144240c0c0c103150469500180001c11030a48040c0340b0b0440750804813101c015541d2402c0040d1101084014040c0d41c160004c1420240003030001003440c0111006c0303441c071018441c030720302c112030500b20310903 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 499599181 1250 499597931 499597937
    0xe0d0e0a0b030f15130c0906030b010806040b01090312080a060f05180702030d020f070c0b280210050103060e0c150a03110405090f10080a020603150301060503061f08030a 75
    0x103e4404002c9880d541040a0106510001103640005034000d150011a0281c450b81c0c1e1001020a0380c002580314020300e068103081c44003c0600c40080c241007401800180500c0d21004404070980c46086070740013035548821001c00c4a00e814000506291044138980350080c5082c00110746a200c0740c510f00103c413001000d40d14085410390100d100f07640d015020a0540c80140616000310209001510f00da50400035080d864400302d040110300c0d00e40c0c50f480010721000400804102c8e64110000400034041004002008201203000300d107402031500c0c840c51500e260000200030402290040550034403004116059540450108840030945e04c007c07801000007000129a01802900701d4180504a40c0c503075070074140c1e51004038109060840b050356400f50100200200c11043ca1140740c00b9003540001484141b0b42d0b50302150092102500b0a48842e180084003a107540e000d401480c06072001509a82d61800c1400c02d0000d1090a403c0f43c402c0034050000100d44404000103030b4240c010703e03075 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 499600431 1250 499599181 499599187
    0x91f0801200a03151d1305151b0d0605180c03061012050403020601150e0303070f020f041a031b0901030f0c090c08060f040e0d050c0109060e0d0e0a0b 66
    0x101601d1410360089203008103164a0740c110050a0108501c144014113070394100100201c0081059a05a00c0c0240202c414886440507040410000a04031101054103403051040e5242c50395010b080301010f103150008a01c0c00900c203141342001f03402610480d1810364008030080d0107401800e0b0940d104451100c5400400c3c4001001032524441d555003003141c5052044044080b42c1c0c05505a80301203c0170740150344800010000680e002c0920ba80901c1a46403a054105401e00066201c2c0300d58107000e494821800d0050003590388031030240b00c1c0e0100003002040131610740140d6130790020107036040c14420f000720141640b4240000000441d4001e004021038000da080d0359076010441f0015100340e0b0440010b102c0414001004e01c41e599408030a6203543d061450f0440c1049040c1d0226407589010b02d081502e010521040040e40201004c0c850030207985a07a007148180340100401c501c0503010710304281d589080d8140209131000d05421a42d900c43c01170341d40c2018006045160310580210031420 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 499601681 1250 499600431 499600481
    0x17010e06011403060d06150e091f051005030d020f07050a1805041106041409010f0e1303030b1509090a0915090305130602030a11070b0a05090a0302091f0801 69
    0xb0000640c1d2000700104107040034110303611150f0031201e01d5440460307080e14500f824441c6150820182d81d02000c018014241c041e05c0300d03007500b5200305c0246107889043e110307008190200c1905800780040c2034003038111200340001810082d038664094450030240c0c041c81601181e10f04094010000761100c5c2444d8031000840c1040b01030081200800a688808000750b1880039695000004c01c02482541480c6c1c034070b0347c4110700300a01c0c01410707880031000718821351007004500340c200c80751980800d03040e0f041588121241019005000909112a44050b5205540e08404600006800340758029600c48409035143e9024804035201d0140142400b540340011807045401a041a48540c0c868034069091654080800303036011402c0c0c100070302507000841c1100345551b0020b16440321584620050036214038040c1004060300c03c8601010812400007803141d40c0341ca0f210740c0c0d0002144d004d41070f10501d15210343c4081c40750030b0703003182c04401a001e100c00042c20b071414050340801c582c80b5040f220000140b = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 499602931 1250 499601681 499601717
    0x15060216210812190203061c030c14030a140708070f030e06040f03140606010806150c1204082401090f14090309040c02012f041517010e0601 62
    0x1100201c9204001e50118690001e0811030140c25400d41078109141181000d244040c00030305031540650480344144100113165075034030305803000740084401e81c10b14102c090600322880300c4610b0020340844c46c40c1b003d245011340300000800307680d8140e6881008109040316004d0f450f00c80d007103001e0101c090608c10140400d151000343e41071103229042c4016280c0c5968041040743e000340d03009140844030204100148200d040c0101850414580503148514003e400038000e0480500058041c1c5461745005840030b88140881c0c28201000c03003126030b80c009680103144580c1c4507026003225030062070444020075940100313001c0059403100d00000035078284407035032005000301d5506405850319010f40301c501901501c6028010700d42440615690213804c000e12055410b44101981117a15000c0c68601c680002c000407211407500c0342410a080c010711741307060b10a0180f03802000307211883c1c0044c0c0500542041c0102007072003c6001d6052260398403009402d10a60442c0c0882c08190498040508400 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 499604181 1250 499602931 499602959
    0x108030a05090303190807122c0a0b010e0106170103030203030c030403120c022b080c070c080f2103060306070f020f0304060e13020406050f0702150c0115060216 71
    0x9405011a402d0402200d175031000b40c41c01c0101c4601052180c000d210a181d400140b1003010f9203407900901c030314005030f1800701c4100c4100079010740e0301400489059072100c003404414070b825008001c40c4400d5846415441900e1070078421003020412900a054010800c0d5520340d0490b5010780186003540d81d952003004082c0c2c0000c01c102c00304403910590159100700c2d44554848052550b004000e81c492500203c25402c802c1c2e992580950f0620342c000310016804508540c0c4001403180403034480200d443c10b240c0e8107230f07030fa080105540a07040c0c40c0805030800140400c0000c0722010b46103c8a9496036000000c0d20065400e80c2e00f54000c60002503130305010340380180d00115a4411582040280408103080d80c21503000750000404012000702c01d80340018180b8111184150114a0300b464080c1c050454131681b0161a1410f078049014015981e45540f180c098800048000b0b80c2d6504201e60180200340d8004042c804c40104000800e00d1031000954801d4030038041c0d018400d4074148241101211 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 499605431 1250 499604181 499604197
    0x423100801090b1801080c10050c0a06110f0f030f06010e0d080721050705010e060f060d06140f040302160b1b010b0406060207031502130510020c030a0c1401080108030a05 75
    0x10040004030403132282d008080d008183c204060300aa46c440020404410002c01c245401c1010030b10500d00d4442000c0303401c800ca150301a50000740c01e0305000008401d030180f068000f02c40b080218101040001100c0114440d4000c2190548259641001036070380309600070f1010b4001d042640040c00203603074040101015801a1100204600c222403541d4a2211076807401d80001c00104241e0100300d802d000d09007001c403515015080502d803240d81040d0000000381060f10032496881c00d0814040c00f5440b00703c2c00303980700f04000780502c6c00891100282005880c100c0051048000c8030a013810102440b109469030b001340c1030300d010b4802e803000c0c05810302000413810555a444445201d07a0302c6d0710840b00180102e40240c054585541801450b00381c1c150135031310180340100481c500700c5003034002e18070031340f481140c4a555103190075000324034228500c020309400d0b1050b02c4102061041020000c070448403054089050380340780400440d8007150a1081d42d240754428000d4100580c00352018011403 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 499606681 1250 499605431 499605439
    0x41a03060f0a03110a120503161401050108031809160818062d010e040f06060e1008010501060203090603150f2206050103051e0910020423100801090b 66
    0x54030705200041c1d1400391540102ca8150b500410302d101424644c0d00c1318020045440c170b414210705242c407519200c1c4249040a0009484088100200f040c100781e04004042e203070340200000e40c1c41e9581c05a880d03118000300780d60303600000c0c40002c0343d18013182e0141c82549610281414103d80d01420368550340c02034080c2c005039017000b0841940400400c40301e4810202c40c4e0282010510b001c800c03842190128200011048001006003c49140003840540080c0d01c1314501500c0301050400e08001d003c280c009240088460080c4210101e28588260a0340c80c080004c00c180d0340c0e201d034244e0b034030300c036919801d03411100900004942c8510111900b030310b010080c1606050704402d81c0025000c0c0200c0c04251198ac5840200f29869200b5101e842c014000031b08040055081c10581c580b003090380300440411030780b2188001000c600d4140401c2c040805454001d6441c0d544418000400c07004a0380c0b2241103030f10aa15803192813401426021207030360151504a0b00341d00b01848207028240004000d030704 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 499607931 1250 499606681 499606699
    0x2040315052206050f090609070b03131401050405010e0c010c0206090406170f06070c170c10060b04090f02070206090d21050912070f06051c06060503100b041a0306 72
    0x60518940c02c0a00c0e15100300f4000030f85140200500d00700c4000540381a0311980580c1c100b040843c00050180240c0c0c181c0385d6560348a98451041224291311107100901c1c0d0011800409c4941005420160003503114030000d024002c0f200d51007903910f142d20703e81940082c0c031304481c07074002d810907000034000701c540500042007890719481441a030b2000041e0f6401d40c3c0e806000c206d08404024440250840710920b840c1500c0f1400b52101232042c0009800214580c5c40024054000e14041102c200185141c00c02405041e6031080309036091307041031040c1e000c4142040c0781c490072103240341308031640198000d050504100c052024400e60300d45a07441102ca084000002c000880112512001c1990140d030300c0a03500c0106005018081e07640700065820b5034090784081c040441c41000510681c4c0144c07a0a80e2141c41070700e000707180115070a1030282e500389084004103080c0c0d84040154414030754441c4000705c0c40c0c0e07102d400c0d242a1003644100d03104441c4800481e500020240020740d0003540007418104 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 499609181 1250 499607931 499607971
    0x101a010e0316060c171606021b0618011a0607030f12020313120804051c021203040503070c080607090311180a05040c08010c0e043201180204031505 65
    0x2e0800019040398001c5101002c1400420003601d44404020004a8469040c0f2004120810303003807048a9000340f0890300031134600c0d1802e501f0007070002800d4460b8100d0700b0a0400305d142c0ba03400006000c0440d8603500300034005400c2c0c50700d00c000311001c13000942503034601042d41e02d0484105c1210b403801410880310740191540c08165001441c09003441640e0105500090314081c0401c1e042110110305100c042d0b410440451400310319081c0f040b1007941c0d001d646040b00340c0102e082c440041c4584000308004000e0005208c000800303814150301c154a00d241160b11f031151550340341802c6401d00c0000d00c00700014000a107524400c02400c8001400328030800d0300c04020102c4c40f04081380c1640b4031715030340e06c108010301c0300e850740c0350740244248002003011072110307400200003050b2071001501071030300c88019041d403000101044030740c10340c4408502050604009008900e036828418051600c9401695610024107442241c007100e40c0100340081400102c00440003404000b00f14089050a060481d0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 499610431 1250 499609181 499609213
    0x903031d0f0c210312060103060510020a0b040809030a030c02100c02030304060315090501030f060605040c14030c070b090d0905061321050f01020c10140f3303101a010e03 75
    0x4030004000c264148601d1174111b000500b2540711380e05c0244500c0d0228054940c064000c11103d00c0c458212542c25029036560400e18844c4c480d071104603406214140958050541c09808109103134400c48205008802c4000c0803144408100006941900208010002d050081d840010710183c0c0090350703010582d840341094100d440982c0150399003d1020542c80401000344900d0000d8403003101c0401283d030828a0042085032900e03040f2802090000101c0d20040340700c2c0c01e4500281e032088400805151032155552102804d0b040d1001080c05000081558605101a601d911074000a00c4503020b25101d03540b20034599203140d091603008035004c0ca101044080c045941d140e9041000588d0f22400e55040d00d03d049120300c070140e4031615040c00c04000803950840d49801441c82d200717009582d01c80c0300926512250703111010228030080c12400400b14900320b11500d10103001c4041d991400076074202c1c04151440404003400c8110303008007060080d802901c1455206a003d0203d80d542c4800310703002 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 499611681 1250 499610431 499610437
    0x507110a030305031e0903180a050d03111c020a020f0d0b04030f1b020303040504020c100623040c08010504110c1506090612030403060b01120903031d0f0c2103 70
    0x340c00040d0b0002c1001940202c204a075501c02418007002c3c405845c00790111a01c9015003009202023405125082240d40d441c20540c00103040028110b260500031490050a81d03c41c0b8060b030b01a034001c080b43c400c1084402c01c1d04010984540d009000c48401990800041d42100d40000f5442130700c2d410003102084441c100540720343d212351940102c41e501c1032030250181070405c1d0a568442c0ba900c24000050704c0200658003203135002d0780d0150f100e1041c0111a4102040300c00390315006803030404001100000b81c403031000000c0a10005107050107204c410701040d10020308007000480d4071600100100d0500c0d81c001d506081503480b0080c10a040111058148a2007003449806900c4d60002d110722480c080e41c91582210046030ba00c098013003510046600e13800389100c0a0f00741c5a5400495809900403c101c4d00482c3c0300550412114603503140180c002d210380032501182100c40d180c0110b000c8400160550b03080c081c1344c0201342c0340010070100181c440b48500400e03100714401402d05040c007010406 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 499612931 1250 499611681 499611683
    0xe0103050d2d0f11070b0d0f14160305161b051218030705030a03080f0a06090c05190801180b18040506180a0c0b0313081303031803080a0507110a03 65
    0x5543c60260300395400070040d045080406031150004501001416022001c84001e01140180801d0780a092400c5c40010009001d090001ca9200b41c10040400c1850b1444d01091070a91004c200e00d0b294580c5144030040c175681b000000c52850990240418000106150041c1c03144044400c017107001c20503080c90317800190314241c0101c1e030020b0034041850b003880510050541900140704030180c94074002c0403410003404011000903200c02090880e402908560040d0406040620090940d42001072044d40a40d00d020258061035005a108a204554a5040300d031700000340120301045c012150000d0403e002ca8a0740320800d8807441c040b400f54001c0462045002c2c6021b070000e441c203ca2116040c07240d100a2881c6500701903120000035000c0c0410f0010b49903480c40c0240c603507441c08001e1441d9000403202400d5900c000c41c00480f02c4540e07000c1d0b54103680c0f203950b440c13007201441c00000007100070310b010040c4240800e11200600b02e10841c050800d2500038140858200350f440c1c0401e00b07107012500 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 499614181 1250 499612931 499612937
    0x120f061701110705190f0f14010c030917090d0b090604020126130539010302040b030a240b0703080603030c0d0e0103022506060e0103050d2d 62
    0x486020010284200d04080e0b0142c2d08452804000e5079031030b600d503800d4540040491915071014010b02112400075086d843e0312010f40c0e0421002424007584da03d8002003d6110740d03081c0241192054172a01800b524158446203000400198050400c00c98104408498100d65110503140204a1641d02c89008241e0b150190017036007417a0000520b00d0448070311400515002850811255950528255100d00c0c4020324510300c02c0c03545855800c000560b882101000c1c0c241c08a400d082025030048410030401502c01001c42029070010740a0f401640302c1d010700d540061000440e50b60040d0030802c1034808090000f0400c01c202da00786540036115401c04400f200011801104254024110035000700707044000b1410000c000408590350b181303100c04801040807091394102e007a4000c0c0c05942d90039640006203005003501c40700c404d000d849014000c0d581c403824820009603180c0480c400b18140c0750000300cc0d00c1021803031402582e0070300302c030701e80100e0b981c130f104840217242c0760045400d000c100d081341d07 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 499615431 1250 499614181 499614209
    0x103020d0b15280504140103020403050a03020609010c090303120b030f0a08030106140316030e032512140414030709060801020a17010609060c08211e0610120f06 71
    0x160040b0003000e60f00203c3d501c0340c03a01148002c00740303420200351411545070714241d1003618410300c01203002e4041d940c0000c00f188120324a0000701030300403401a00c9500c220000300709500c4203c0086902e9a0f441c4009004208001e410625442290b0007003103440d90090f0454000030048610245001c030300c00f6040c4c1e412000800140041503005e05490120110340c45810309506180c00d40c1d009036406550314105240e560306c81a42008820b00964400745c5101d04613910903061110000e000910b8442c0407504841106020610980a60f960703801380d4042074201345c10309062030403810740002160f0980740d0621800000086822480c01480003403c2c0b080300260300c81a21100103030556a03444a50090740d808040184555684404801c0032502c0b40d00e0628802c1c1c1d4141440707007e92203903940e10380003224003d140481c105070912019001d00074940c130025202d00e2000d003250303403d04180c0d540380e40f24030744802c1501e03540c1c0300e0703001f00602c03426a40f00044c4a441e180501d4044554aa10080346030100c2 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 499616681 1250 499615431 499615447
    0x2a07050c1f1b1e030e120304060306120f02100504080601180b0f010522030b070e090a021e030a14010e011a030405030403032001060b0910020c0d020103020d0b15 71
    0x810444680070044002e05100301c00940e8803502d10050a104080b03070990100041410b0500c54070000c044040c0c098410091030103048580d64482d80507000316400b0170b0030502d00107071150300342000c48092a0003454901048a841d400c010b51900140921401c02c0014000031803110790a00480c0d0090986074042005000d0b5014500152680314180b584540d0900ca12017200d030b40c200040340c86903115a901e00890f555480c030714031400b55441d00007500d08401c1e40104440c5c2a0400740103014050120751001540d5222034007401684035800c00303c1c5038030f010340030400084100003001d160044038424001c20364191042a01e203440c90240e2085005400e80c100400844408160860607107030700494551441c54036407182d503a28404d80c40010100b0210300f01d0159100e4000088501c040c2c01400280000b564038520401d17643c1000d00e889100303c544d030800600141c000202d0100800c0c1c0a080030a8403211a001540207402080e0000413094941c3c8841d45103507550341d6800701d0091307007030300e4651280c0301 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 499617931 1250 499616681 499616687
    0xc010216050906090c1c2702090106031e060801020c060f0c04030201200f012406020c0616051b0114042111030703030503040b07030204180f06030f08070b2a07050c1f 73
    0x805103030900f90400c1174100031f01603100c40d803609066820509022888000344245441040800868840400d25080011400355010b4000380f4804500804440d407030744807031a03034903c4400d0580d01a03103410b00030002000194022885a50031207440d1f0700d001c0503207540b00742c16800c02e10702c1e06001059941d0359461014584c480c4079542c075100c010551010b02d15090510107075a40760200e500c24481d8001160381c00f0304070341a54080c0211580642610b100c010320b445058005030f100e000045c0429100d0498102c0c0100381410360b4201c0b60101c0c4610a1000195580d15007101100c2c2c0030786e03082d480301e111940161010401040103511039030366580d492038241032090342c041d809800e0108041c010401000f50417114000d03049804a003403000100c1c040c05014100040c421588003c2c29007a903004031009016a5402411040d4000e00c2480055904c0c42d1440909014040d2180807090700c0c082d68001450f10700c0c0242058a01c00d000303c4403005210030024080b1000340301802100121220701c603925641c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 499619181 1250 499617931 499617971
    0x507030c020118140a0b130e1305070e01080609030702090f071218050c0901060c03050c07080d0908011a130b0609040e0d200307062c0c010216050906090c1c 69
    0x480f071906c00c1e051402401649040709842e20414840e8400540801c014124000c002c0c00c501c1d600c0310444012565400c0040c0c650482417181c03a05500940001900c86240481140d080c030358000c0c4906e8055840d5000d00d80c0c900c601a041d1020804405003581c1c0743c40c401e12032100c000040907000c2105201c9445d000b45405041144140110b040800401c01507812500c03481d041b5615040a5480d21501c4021501d44a06032380705101a114000c1002e0f401900004036209580c0306800a211418a07002c0328460030901001568011040c5800c4016032425940f040d215890014002c5241081820018040da428121030900c140c000d0500300c2c8905400c89039901145090024144084800c07811444e00d174011820060075250300c03402d02d05007085801510055480100e03125551a4010b568550395400c1e4030301446002d4440c3c0603006901c0840724507007200300c0d00020a0442a90758020074090f000fa0090400c00300c0a50600c144803601440c64458007141054140015605200f01000ea01e815 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 499620431 1250 499619181 499619189
    0xa1824020c060136150602030a0e09100506120a0b0a0b090d02010c0f1208010609080a060c020a020d030c1a0c0909151302070b0c04060507030c020118140a 68
    0x24410060201041d10100e051030440702800d011052030320802c42e0109078141224544403562400d06040c01c9800c20715030044010708030340720740c040c0c4068481d082a43c0da441440c54010100f40c912a0012140c5010120603a02c281a002e01c240f169580c1c00c0812502d8101000c2c00380d08118020030498028260300c00d40c0c40c006002c4450b04289407414944650501c03621356818012044280b83c0d50a690180300035a0540d58403100e41c40d03200300e0f05d0412005102c800b01450001842c20b000001c2d44620a070710020640c3d0aa002800c0c1200c426130ba280000d024000a00b415802070742c49070301c05aa03544000041103400b0740c60340b044400291500780d000d2540341403000f46500708041800038000401c026210b00180586603a403007a1240740304900b45200d081d80340c3c0d80c0150003000c01c926420054000d803c090f0720440b000d20303958940d00410038942c007690040d800002c00174452480030074400d420078003c0301e0040c1001480c00884194490313a160031a00300007200c0c9004041f4034900d00349050403000070 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 499621681 1250 499620431 499620503
    0xa0506160314041704030b01080a02100e010f0c050a1b240503280e03071103010c020a022407060b010e040b0913030e09100611060402060a080a18 64
    0x10680c4402c2c02d6038800015001400d81c040c4d4250351841c200190088501854010107405030b15a542c400855540d840c90000328000c60181110070141b601500012200100584807450140c01080c011158042c001d4020f9440e849203124020104410000354101e135026010203d0089041c2003400340702e040705110030b080d601c018040340c540143e4071a05481e005002290a020700010102901e4051120030a48910692130203018001852000008060b130f188904010020b1711458000c2600f01c60b003a211007409600507980010061400202440314203080c482100306035441c403c4403411540001400301c481c10f981d01c4c481012585c01c091501d03c2c1034001c42e805c6c8a03048401e000b040180c0e20141890318a400e01c0d5400400b09400b640902d001003a000c0c00c1c0351030501e01f0076607240601981d0f12400000c0303141501c000b14540b001060b041d104640140140c2e140202c00001201c1e0741038010100c1082540d03840070f10300646d089000d0049501d0040b00b01e0f035a00001c0c42e191f8807040071000202901 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 499622931 1250 499621681 499621691
    0x80a0f022506050309031c3c02030c120c041701051006030c0306120c0f0605070308041b03020d0c1701020403031d0411040305010203040b01090b0303090f0a080a05061603 75
    0x1404102040398019191140f03811612500da007444949540504103801c1d0200b1303d01201040f212202c2c0d40700710a181040040e42024800c1011303450314180d541c45521484481d242c01c5c0e07004145141c3c0003180c105249805c01442d007000c41c041840d84200c280c40343c88841000060421441031007241d00380e24004180d000b0003603414400e081d802da0490f83d00c912400d064850348400f8465000b6407001000700460010301500080c14500300a04280d240599008298088004141c2611800645405a80c107803500c1841c0d813506c7d241d0780d50020006081810343c03a482c140210050f00c1d001c4400c1122403140850402071800d0407880904102000008242a031040c0420408a1340c41449120b04c03014400700b000e064000c040100d0060280003004030780b044c00000d0008100081503000b180b1843c001c403400001030340c0b1803880c0701c01c3c1e51020702d0540c0c7c19402030010603030350303c0e1440c0008500e01e030092410000c682d07206a06401c2c0407070b411017554107402c60000c00c010100b065403070041d203140c0c600d81086 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 499624181 1250 499622931 499622983
    0x10e04050d09230a09060e0406180203030706020d0f020a020a0c0e100314010204260706090e0415090b071205100501020303180a0c0e04030f030e0601050f03010207080a0f02 76
    0x11030064200b1071800b89460300f00c80ca482e5200c0c00302c1c03d009081c2803113060002584800c071200e0300700b0041c0c40440d0300c0c070315242c441e40c2c1c1c40d01302d15040c0c0030701d83c0e0080103035240c000f03c0c5e00c4490203504980304c1c540703815030358184034018100c0b01d20040203204115009006a0610750800350800c181c298030184030782c02d0740401c10035041220b00c0114152a800b070038001a20040001d06402406540c00160043ca8070000c04090280c9020700d1001c502460070440d154580c4410f000c440300e60042c1301e642c010241140100d0001196400d108005040540c40003c004020752602400d800c415a03030799010801ca034501d010b01103001d01030b80750303c04090068900020701d0500000d5a03884028548041120a241d188400036400d00c1466461a0020707100180940c41d01c1d07040125400541342117001c280c0602403144014000e000fa20101a00d150280c0300341da203464144107241500090917681954200042000510000c018015035095035403005e0598402c0c9102070715003008a9000c00d844100320401e00 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 499625431 1250 499624181 499624199
    0xa060e0a0903320c030706090812011a0d090203030c010f15050f100320040305011508010902030a08030a09170901030b011106130201050d020703110111120105091e010e04050d09 78
    0x40d8104211050113981e601c402e10f80c0c10f0a500512a00804550030000348000748000c000240480100c0c4028401007a40c0c0d0340004c04584000300340e0810002414400113a640034554407421100b40040c1c10b5070b140041c20f0504900711050032008800490f641c0b0113000307a0284032041003001d00016149100c2c000c01820004481b42c101c01e03455000c064036544500c02140480c2c000300307201c072068034445866036100d1418501030500074290711603690800d54005142c8005004030602150062f0151030050f143c2d0300c4070b0445d540005d000046080d1144154070005244241d40c01c0c03070701004800640c031903049000040c143e0307200410035030401c5206040300404100c00b0500d00d401c035a07910a1f4034142ca10510050f42d542c0140c840f10351103144046401d1060603048500c100640169900070414901c210b00c07580a5401501c040502040304d040051000382000d110480d04140b011a8a40310600000f101e0a17041100360003d101000c11702050004003c810407040030f482c08a0304000c02007506000c490 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 499626681 1250 499625431 499625507
    0x3210c09080c130902030c030a1101170c0a0c050c0d03091d3304110901030608120a0e040603020a08030a02010b01090315020315030708010902120102040e010b030a060e0a0903 77
    0x241001c10340d2a00c584c0c085542c104003c4001080240c160340c0318980e00d0a044124100300c1007050b001c648403c490444000740ca5407a0351280f62109581c50904501e102c08071004a011841100d0310301c07800940803d0b90b6035140381c03c3e903068440d55514220354144003002e10b4030319040c0580385082e4480c0c010701c8130b60f40b80b005031a0740d206907800c4090000703031880141042d0204c0c02c5190303030f402500d00091104075009030300080c07034580000c0e201888a90381c0c41e052103549102084003907201e25014001440128842e0040e4600418024004035900c1d80b44c2d00000c0140f540c1e544000070503880013401014550702030040d40030034882420326109a40c07a41e01c2d01182500c21305c14604040b640000003452003070300e18280711904100502103500c0c2c01c1c0c41e0a28140200024442644074038242400381000742014001c44090318081c8441c1d240f03a901c1c10320145259040a080414010341700c803c00300d40007602d422241e20400c148200446c43c2c1c0858240901102e4182113003d4a1381e6403948141d031241c821000d0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 499627931 1250 499626681 499626709
    0xe0f07050d1a10030614071b06150b1c020c0c040905011e020315060306060703031122150e030c060a0e12070504050c1303030c03210c09080c 62
    0x101414403525280000c0d8800002e006040510882c500740142c54003007900394016a80f05030400c11081107107411054120001300d911100194040510704032615a20860141041c410580030514158000c0800880c81c080d40050201f400e001c074802002080da0024040d03049006001180740004540c6050b81742d985008a2a002d1601c980100080140175801080c401150400900205608a041d90041d52054076001005051107199080e945802130407240150380050880f49000c1880d9416030191814001c040c000d48401d02203c040ba000d101209140c460700c1940e209040c078203100d218401031959400700002c02c40c58426884c0941c03070004051725403240c00c55000351100064030007202c4880000000c545c03c5070781c00003621204000041c510341940c408480a124941da148054602c9020300c0c00d2429a847d40300404001207802044180c080501900d802c6c10902103911071500d0b0b1390712805550019594625000c95140d038003602d40700152203060b020b00682c5501c100054002070212034 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 499629181 1250 499627931 499627939
    0x51b090d170c0c151c050711120909071e11100e0106030c09091a06040207080406170c0414090603010f0c120e0a08190c0c080706030e0f0705 62
    0x264020701c4079102021014640e08900c190ba00d071105440581c6501e90289410f005103100c1689407039001c02c450a40d14042140700e8207000c000d5408695002621002d0084418403020003070300f0141d07100901c181c01e00b00c1050401c03036039210781140c2440310502d4020550020440702c0b800000d0b2050342c02002100301001441e040b4201001040c00500b40a560010801481e147c08032001d0b42042c190069412240591980ca1903c0d66910400c410740d505071000800b00d0400ca04400d9030200c4010340c1c0c0d60056005000141001d010b560340c100c2550ac0b45c0c110b000458200d46030071640a504caa90f456000d02e40c000f40c40c0c00c0500e05201c800c1403504200845120b8508400090307215202503001a02c1000300d150103012a00c074140025044118801c03150740a0b500341030404408110004520504592110086290104506409506448100300001000075500c07018000c204034180041c007038a480c0016008142c07616901400b10369201a5044c802d401c8081c00f8403103100c000c202407044800079a = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 499630431 1250 499629181 499629199
    0xb1c02090102010b100c15090203072d1d13051e030906030103082502030c0d0204091a070201240611031e070c05040e0706030b0d02150706051b09 64
    0x40c005030f0140075100c0c0042d8002c06118481c1d105981d005581d003111038001d040d1851542d280308840001c6e1900500040c0d09079002c44403c01210b4040300070014401c4106120f62804030168902403515441c076403109a60300061801081c0001e007550300c85401c400b040c1c094402c0f880d0280da900e81c0b80c400c003c4014000000c8040150b43d000021703c12941908002448181d4075a100c1c50410096000b5020420f5200e000c0850382e03902c000480004518503400030010082c2d419904204000482c03180ea040380c006842c2c0304174900241201c058120b941084541001080c1781c0003400901b1992400380c203400a110110700c3c07603c014603410464095400368505800c40203660701742c4515604c2540d5400c41c404c1ea1b0121181800346a01c0060203020b0b20484203100072507982c108010550b103802811000715085004200502030082c0d0120034441c0000e400c41c000da15064000852101140d18810b040500020318441000000d100705984108070001040c00314491184150042c0540140140220001 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 499631681 1250 499630431 499630447
    0x903070c1d01050405070531060206090601091a03030a09031104020906030c09030a0b01120201080f01080c0f040b04140f010e01080607030b1c030e010206150d030302090a03060903180b1c02 83
    0x20740c08403005040900d0722410540440c1504423045900080c0018000000a0000c55100d10220382d550243d10141c008060613400c0005660040c00c1c0e0500b10a01c08140141008090b18144040c0c0a03000e03031610b58202880c690308021070303560040f5660610492040154400c5562550183c80d04045e20b40080ca4858500d50302291900c600450081d1131001d500f000062006407410b00d11003482e02c02e0343c07030004507100e40c01410507100080c042c1c1001e503048051044024200311128250000d001040821700203160400308080380e58124000344000210420005000c00c3c0443d114018000280c1c0b103503440d894110410780314600503100c2c1c0c040585801d41c00129554401100088040789002090148981c0c03a020f08042e196000d414058003e0034009015607003050040c01d02c42102610a0b07940700d0329654200d000f9401036802d00c2d40411746200110200790244546091a482502c1d030418400900041030b00d21101d030351054411100402c81c0c55840304e80100c071000821a403000150300c60f000 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 499632931 1250 499631681 499631687
    0x803031603180209180c0603132a090b12070302010c1b0911040305060702010501061d0a09020a080603070b03040305040e0a0902030d120c020f0d0c0510050903070c1d0105040507 78
    0x20b60101941c400328850030310201d020220b03814002c0d000c207801210030544218003403040d01d0208030341a00d066031415038041d0100b11901c3c8050681c2c520700020804030985075044d00c40e20341460b001000c004d9921808000c503420000100c060396001d02008000c147d1565000074411402020002c0c40d1050f599032102a440107049580d000d48070a20f800d10241c440c812003403d42e504148000c1e07480c1e204840100d500c045c01031103203505a50041c0d9072016404608500040341c51000c0303900c00e0b003040404c030b070005030000c080c8047e00ba401c040e55600d1405040800070980341ca5440c0d081203240350000c01c1400006a00401141c044488000481e112542c0340c3c5882d00c001c004002c0083d4250058280c0d015155038029081d40b441d80c0c82c05030401c40310700c65920480c2d99503094002c0001d02c0c3d00c9180000380482c01840d01016692180c000c80d00442c01c040001800c0e248144c0742400181c1c800300341c442c00c005008070600081c02142c074001458040102c582c0c440010706204113400785d40e0f20404a24041c1c8 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 499634181 1250 499632931 499632971
    0x30322030f0302010903120b030d0f020c030609210a021504080705061f140120070503070806091b01020604150e0d09031509032001181b0803031603 65
    0x182100c1c0c00c415440305401c01902800a00000f10001440c00448120041c840d03c15181824005001042d115070088010758121811190311010343c4240c0340700500940e810448107118541c958040d0603100c41891030542c50b10040d80902050200c01d1180d14110380e80041c4142640319001d86405407034803681440a428440e0103c007401034010322080000040c0500c450920401c219007131003080076680d00c69508260034141c15680040c0069014840310717400082d1404604005000b6104800e031342c2c000080c0340c01046d83c09000150082001c00c12840c0d414001002c0c4005d421844994013691040002d480c4c140040004008681c0c1c40000e0014514541c400507e4800d00d0085a455522440014000e443c0603c1f08550f51000003003440768aa541d0700070380c1002641030311415013240c0c40d40c1d040000b40c04152a514010f40da0358080c0740d0310030b2144034901ba070f481c0a482c6c2016546040c80070326070101031941020025900030424808071308a04e2441380e664030401d280000744401100203264402c0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 499635431 1250 499634181 499634183
    0x40b04031209080306010f03020901020c090a020c0d020d0f02010c140a120204060504080c030109050d050d0915020a031b0203030c07050f0d0f18030c140f040f0c030c0e03032203 78
    0xd00e006442c50400040c3c000440c081e000988034014466408041241230b0f204042c82c480c0140c0140300c0c2d100786402c0c60b0402ca600030341c000c44058105008066000c1c98441d60061801c0113030300c10310060100d1500130302c1601e100406480284034031554400042c0440160448440b402c01340040c00001442c40bc0c1000040040b080c04255501c40d40c07904008c00903003140c01181c400d8000c160000180313190510500b05070303a500102500d840d0f5451401a1907503081001401030407911400f10703800246e41c111444001c29110400182c450900a20050441e28452081540100400c8000e61115000410350340d103d07000151640c0c3d18a264941281041c1c02200017151030b12498030203c4006400c040c4c1b4030100c40725a03a4882c4040907001c10b00c0d5500409200280c00c661100906000284981d81608240400900b080c0101002c50b800309007250b200d09600c4201c42c1d07642c02c00c0fa90480d41801200000050b500d0308a070f850300c4203c0040e49134454101d00040b00074085076006404619420014025 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 499636681 1250 499635431 499635467
    0x11205030c011a01020c09010305060a05040206040905010806040b0c030906010509150901080601030521191704031d01030c120c17040614010b040b120703020d0204030c05041a010503040b0403 84
    0x110003c2c03414680707070842c0c0c0340e1202c1c00742c081e14048040906084d22101d0480c2e401100922003525983c0c5e00b18005d1801030010780c0c00031030410002c5146296070040c0c80c002c200307010041c03075140b40c682000f000c1c092014000d007401020403c02d1045074900010702c6415036600f04c6603030b0b40544035425060030b158410170807582c105031060b0000030284070205486049900550564140d1800c000110048002026165000d12801d0006550900103001c4c0ca010059090404004900b031796008151006021107040700001e000c0f070110503d140051840424401080c02c05100f80c201a40c0d0140041f90743c031051110403550380c031041c011184034844641a4183c5039040e15424100303810480c012b00014030740c0e02190340c80c410000520040c5203003102c0884160610b01c1f4100400000c034a07003c0381c00034241d0020140c00780040003010b4442c0c0700510081d07101c0d8003945079961500d0b05120603038240604080c661060300d684481e450343c1110840368410340c0900d01c114142d83e140b4040d41c0031040c82c0303415444 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 499637931 1250 499636681 499636691
    0x6050d05030301180e1b130e0309041104061b0203120c0a110d020109031401150f05090a0203130227040305070204180309090e0307080a08010e0f0f011205030c01 71
    0x1444808001581130b1200407161900a07107103d048081581d2807580600000c1d4031290781040b41000d410740728003410400a05018030320241440c40c0d0192030669499185942001648480518052081e4a6031181555a040c00c2914140014103094200d50f10000c04042e01050401190390520049080c00c004840c0785071556449108aa5140e1400c0c0c1e04440758460095140c600b4941b505a080e40603034165100c1d8150340c1555a00c00010f03452541c181c00964a80750040c00ca40c2d011300b0540301411b01103081c4c002082c9410100542080c1c080e02c00e0701054810001d100c00c40c44843c6400c0d17000c83e01501c41c4420341100078040c841d070b02c10401c3c440a010000e02c00344410075611400404045000311020b100c1c0c0380900c6416035100240c000002c020031410f10041101040703503004600c41c1ca01c94010742e4140400c5413550341543d48a1680c600000341e001c00103120b82e0240001c040c1c0c10010290160b0f401b0b1411030713100c03402c0c2c80041c09131811000390352200c50204142041281c1e070714440a4002c3c42 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 499639181 1250 499637931 499637933
    0x50f1e0601050904020f070b010f12080711011806180902030f0a0b0a0305060406021b0606010f270803040e161d04022206030e010213121a010b04150c08030411010306050d 75
    0xc0782e15400e0140e1203510010301c00012f6401100c0c200141080d40203041d080c50410b00356590128108420fa0660500180c0d1858290302030140c1c860318000d1855449a401e900c14a40030f00d800f050b644d80142d8041407041c000d2003942300341c20f0742d11903220100000000d16181d100e000074074000203c1c0c0c40100980702e83e0081008001c100d030081c000f0b021b02502803c4402a4110140c0d446000445120340003038905070321803182512440414481c1200d1405000241000a203035510411058000c40310365400010100480c01c0801c020660101e036400b141c02c074220f0403641c01400e9014a0201c004000800c00900c83e80d03a40796070450342c0c2c3d607007101d4024410205041c0a81a0a00d46100e000080780c0707030015415801d103040c001c40b540041503c0d40c000702d55046c40d06c0c400000907655003d9400d619070440340c1d0060750000200c18040d0000504094849150103040035050f80c010011100f00b000d184803c0340003480c0039081d40d030081e52051060a041020000407801440c2d544d11082c2d225103507102d1030b0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 499640287 1106 499639181 499639193
    0x4080a0c0606050d0f0b130f061a1002010f0c0206070c020409052103011e0501080a0b1915021b09071b0203010f050f1e0601050904020f07 61
    0x10341507210000b00b070f00281c00b03100494130a1005c00030030050200741c42c0195401800f8900306000b012207035a40c1e64002ca00c803c001001079884a2413a0354407120188845000300c00500b074404201d03100310000b40a80400c0304403607040b518141040c81802c3c40444e00c20711031645902c40c603400c0d41e641d900b4840100010481640c06004590391030801d0324080c4400c0612030000000140c44e54117141080c4410502c4403403002c000307400003508002e1070340c20481d029402844110001003001d1f90501103140e204902c3c01250342c0910201010500b41110781c89440c00b04080e5080722104420380e04650740b41070b004180d180e07203c91560300040480c2d2080d03224403541107804210044046441e8046800d403000c0551454645403075504112884080c00d196503808441c40e01240754509017002414041c0e00086c4c0315504205002441e04451345694040b030300100e80341400c6690300c0350340e41800 = true := by decide +kernel

theorem cover : BRFrame.Cov 499460431 499640287 := by
  have h0 := BRFrame.cov_init 499460431
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499460431 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 499460431 ≤ n) (h2 : n < 499640287) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
